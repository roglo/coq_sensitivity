(* Sensitivity Theorem proved by Hao Huang.
   https://arxiv.org/pdf/1907.00847.pdf
   https://eccc.weizmann.ac.il/report/2020/002/
     ?fbclid=IwAR19mpxfIuoSaWq3HO8MdV8i8x_xlvwMKHjfElzBUK0GditlyaLeJiC8gJY *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations.
Require Import Init.Nat.
Require Import Misc SortingFun IterAdd.
Require Import NatRingLike.

(* adjacent vertices of a cube graph in any dimension;
   a vertex is represented by a natural number. *)

Fixpoint are_adj_vert_loop it a b :=
  match it with
  | 0 => false
  | S it' =>
      if Nat.eq_dec (a mod 2) (b mod 2) then
        are_adj_vert_loop it' (a / 2) (b / 2)
      else
        if Nat.eq_dec (a / 2) (b / 2) then true else false
  end.

Definition are_adjacent_vertices a b :=
  are_adj_vert_loop (max a b) a b.

(*
Compute
  (let n := 3 in
   map (λ a, (a, filter (are_adjacent_vertices a) (seq 0 (2^n))))
     (seq 0 (2^n))).
*)

(* subgraph of the n-dimensional cube graph *)

Record subgraph := mksg { sg_vert : list nat }.

Definition edges vl :=
  List.fold_right
    (λ a l,
     List.fold_right
       (λ b l,
        if lt_dec a b then
          if are_adjacent_vertices a b then (a, b) :: l else l
        else l) l vl)
    [] (List.nodup Nat.eq_dec vl).

(*
Compute (edges [1; 2; 7; 4]).
*)

Definition sg_edges sg := edges (sg_vert sg).

(* Example *)

Definition cube_vert := List.seq 0 (2 ^ 3).
Definition full_cube := mksg cube_vert.

(* edges and vertices count *)

Definition number_of_edges sg := length (sg_edges sg).
Definition number_of_vertices sg := length (sg_vert sg).
(*
Compute (number_of_edges full_cube).
Compute (number_of_vertices full_cube).
*)

(* degree of a vertex = number of edges adjacents to the vertex *)

Definition vdeg el v :=
  List.count_occ Bool.bool_dec (List.map (λ '(a, b), Nat.eqb a v) el) true +
  List.count_occ Bool.bool_dec (List.map (λ '(a, b), Nat.eqb v b) el) true.

Definition deg sg v := vdeg (sg_edges sg) v.

(* Δ : maximum degree of a subgraph *)

Definition vΔ vl :=
  let el := edges vl in
  List.fold_left (λ m v, max m (vdeg el v)) vl 0.

(*
Compute (vΔ [0; 1; 0]).
Compute (edges [0; 1; 0]).

Compute (vΔ [0; 1; 2; 4; 0]).
Compute (vdeg (edges [0; 1; 2; 4]) 0).
*)

Definition Δ sg := vΔ (sg_vert sg).

(* sensitivity *)

Definition Nat_togglebit x i :=
  if Nat.testbit x i then Nat.clearbit x i else Nat.setbit x i.

Definition flip x S := List.fold_right Nat_togglebit x S.

Notation "x ^^ S" := (flip x S) (at level 30).

Definition loc_sens_list n (f : nat → bool) x :=
  List.filter (λ i, negb (Bool.eqb (f x) (f (x ^^ [i])))) (List.seq 0 n).

Definition local_sensitivity (n : nat) (f : nat → bool) (x : nat) :=
  length (loc_sens_list n f x).

Definition sensitivity n f :=
  List.fold_right max 0
    (List.map (local_sensitivity n f) (List.seq 0 (2 ^ n))).

(* Hamming distance *)

Fixpoint cnt_1_loop it n :=
  match it with
  | 0 => 0
  | S it' =>
      if Nat.eq_dec (n mod 2) 1 then 1 + cnt_1_loop it' (n / 2)
      else cnt_1_loop it' (n / 2)
  end.

Definition count_ones n := cnt_1_loop n n.

Definition Hamming_distance x y := count_ones (Nat.lxor x y).

(* pre-partitions
   A pre-partition (my naming) of a finite set of n elements is a set
   of n subsets such that
   - the union of all these subsets is the initial set
   - the intersection of two subsets is the empty set
   It has always n subsets, some of them can be empty.
   A partition is a pre-partition where empty sets have been eliminated.
   There are exactly n^n pre-partitions of a set of cardinal n.
   Each pre-partition can be associated (bijection) with a number
   between 0 and n^n-1.
   Actually, we implemented the sets as lists, and a finite set of
   cardinal n as the natural numbers between 0 and n-1.
   Below, the definitions of the functions
     dispatch : number → pre-partition
     locate : pre-partition → number
*)

(* To define local_block_sensitivity later, we need an algorithm to
   generate all lists of disjoint blocks *)

Fixpoint next_in_radix n dl :=
  match dl with
  | [] => [1]
  | d :: dl' =>
      if lt_dec (d + 1) n then (d + 1) :: dl'
      else 0 :: next_in_radix n dl'
  end.

Fixpoint count_in_radix n start len :=
  match len with
  | 0 => []
  | S len' => start :: count_in_radix n (next_in_radix n start) len'
  end.

Definition count_upto_n_to_n n :=
  List.map (@List.rev nat) (count_in_radix n (List.repeat 0 n) (n ^ n)).

(*
Compute (count_upto_n_to_n 3).
*)

Definition is_nil {A} (l : list A) :=
  match l with
  | [] => true
  | _ => false
  end.

(**)

Fixpoint nth_find_all_loop {A} (f : A → bool) l i :=
  match l with
  | [] => []
  | a :: l' =>
      if f a then i :: nth_find_all_loop f l' (i + 1)
      else nth_find_all_loop f l' (i + 1)
  end.

Definition nth_find_all {A} f l := @nth_find_all_loop A f l 0.

(**)

Fixpoint nth_find_loop {A} (f : A → bool) l i :=
  match l with
  | [] => i
  | a :: l' => if f a then i else nth_find_loop f l' (i + 1)
  end.

Definition nth_find {A} f l := @nth_find_loop A f l 0.

(**)

Theorem nth_find_nth_find_all_loop : ∀ A (f : A → bool) l i,
  nth_find_loop f l i =
    match nth_find_all_loop f l i with
    | [] => i + length l
    | a :: _ => a
    end.
Proof.
intros.
revert i.
induction l as [| a]; intros; [ now rewrite Nat.add_0_r | cbn ].
destruct (f a); [ easy | ].
rewrite <- (Nat.add_succ_comm _ (length l)), Nat.add_1_r.
apply IHl.
Qed.

Theorem nth_find_nth_find_all : ∀ A (f : A → bool) l,
  nth_find f l =
    match nth_find_all f l with
    | [] => length l
    | a :: _ => a
    end.
Proof.
intros.
apply nth_find_nth_find_all_loop.
Qed.

(**)

Definition dispatch_list l :=
  List.map (λ j, nth_find_all (Nat.eqb j) l) (List.seq 0 (length l)).

Definition dispatch n i := dispatch_list (List.rev (to_radix n i)).

Definition pre_partitions n := List.map (dispatch n) (List.seq 0 (n ^ n)).

(*
Compute (let l := [3; 2; 1; 1] in dispatch_list l).
*)

(* *)

Fixpoint list_nat_le la lb :=
  match (la, lb) with
  | ([], _) => true
  | (_, []) => false
  | (a :: la', b :: lb') =>
      match a ?= b with
      | Eq => list_nat_le la' lb'
      | Lt => true
      | Gt => false
      end
  end.

Fixpoint list_list_nat_leb lla llb :=
  match (lla, llb) with
  | ([], _) => true
  | (_, []) => false
  | (la :: lla', lb :: llb') =>
      if list_nat_le la lb then
        if list_nat_le lb la then list_list_nat_leb lla' llb'
        else true
      else false
  end.

Definition all_partitions n :=
  isort list_list_nat_leb
    (List.nodup (List.list_eq_dec (List.list_eq_dec Nat.eq_dec))
       (List.map (isort list_nat_le)
          (List.map (List.filter (λ s, negb (is_nil s)))
             (pre_partitions n)))).

(*
Compute (List.map (isort list_nat_le) (pre_partitions 4)).
Compute
  (List.nodup (List.list_eq_dec (List.list_eq_dec Nat.eq_dec))
     (List.map (isort list_nat_le) (pre_partitions 4))).
Compute (all_partitions 4).
*)

(* Local block sensitivity *)

Definition loc_bl_sens_list Bl f x :=
  List.filter (λ Bi, negb (Bool.eqb (f x) (f (x ^^ Bi)))) Bl.

Definition local_block_sensitivity n f x :=
  List.fold_right max 0
    (List.map (λ Bl, length (loc_bl_sens_list Bl f x)) (pre_partitions n)).

Definition block_sensitivity n f :=
  List.fold_right max 0
    (List.map (local_block_sensitivity n f) (List.seq 0 (2 ^ n))).

(* Proving Theorem: bs(f) ≥ s(f) *)

Require Import Sorting.

(* property of partitions of {0,1,..,n-1} returned by pre_partitions *)

Definition is_pre_partition ll :=
  (∀ l, l ∈ ll → ∀ i, i ∈ l → i < length ll) ∧
  (∀ i, i < length ll → ∃ l, l ∈ ll ∧ i ∈ l) ∧
  List.NoDup (List.concat ll) ∧
  (∀ l, l ∈ ll → Sorted lt l).

(* locate: inverse of "dispatch" *)

Fixpoint nat_in_list i l :=
  match l with
  | [] => false
  | j :: l' => if Nat.eq_dec i j then true else nat_in_list i l'
  end.

Definition locate_list ll :=
  List.map (λ i, nth_find (nat_in_list i) ll) (List.seq 0 (length ll)).

Definition locate ll :=
  List.fold_left (λ a i, a * length ll + i) (locate_list ll) 0.

(*
Compute (locate [[2]; []; [0; 1]]).
Compute (dispatch 3 24).
Compute (locate [[]; [0; 2]; [1]]).
Compute (dispatch 3 16).
Compute (dispatch 4 23).
Compute (locate [[0]; [1; 2]; []; [3]]).
*)

Definition sub_list {A} (l : list A) start len :=
  List.firstn len (List.skipn start l).

Theorem seq_app_last : ∀ start len,
  List.seq start len ++ [start + len] = start :: List.seq (start + 1) len.
Proof.
intros.
revert start.
induction len; intros; cbn; [ now rewrite Nat.add_0_r | f_equal ].
rewrite <- Nat.add_succ_comm.
rewrite Nat.add_1_r.
rewrite <- (Nat.add_1_r (S start)).
apply IHlen.
Qed.

Theorem nth_find_loop_app_2 : ∀ A f (l1 l2 : list A) i,
  (∀ j, j ∈ l1 → f j = false)
  → nth_find_loop f (l1 ++ l2) i = nth_find_loop f l2 (i + length l1).
intros * Hl1.
revert l2 i.
induction l1 as [| a1]; intros; cbn; [ now rewrite Nat.add_0_r | ].
rewrite Hl1; [ | now left ].
rewrite Nat.add_1_r.
rewrite <- Nat.add_succ_comm.
apply IHl1.
intros j Hj.
apply Hl1.
now right.
Qed.

(*
Compute (let ll := [[1; 2]; []; [0]] in locate_list ll).
Compute (let l := [2; 0; 0] in dispatch_list l).

Compute (locate_list (dispatch_list [2; 0; 0])).
Compute (locate_list (dispatch_list [1; 2; 0])).
*)

(* return the rank (from 0) in the pre-partition i where we j is found
   (j < n) *)
Definition in_nth_list_of_pre_part n j i :=
  i mod n ^ (n - j) / n ^ (n - j - 1).

Theorem not_in_nth_find_loop : ∀ A f (l : list A) i j,
  i < j → i ≠ nth_find_loop f l j.
Proof.
intros * Hij.
revert i j Hij.
induction l as [| a]; intros; [ cbn; flia Hij | ].
cbn; intros H1.
assert (Hij1 : i < j + 1) by flia Hij.
destruct (f a); [ flia Hij H1 | ].
now specialize (IHl i (j + 1) Hij1).
Qed.

Theorem not_in_nth_find_all_loop : ∀ {A} f (l : list A) {i j},
  i < j → i ∉ nth_find_all_loop f l j.
Proof.
intros * Hij.
revert i j Hij.
induction l as [| a]; intros; [ easy | ].
cbn; intros H1.
assert (Hij1 : i < j + 1) by flia Hij.
destruct (f a). {
  destruct H1 as [H1| H1]; [ flia Hij H1 | ].
  now specialize (IHl i (j + 1) Hij1).
}
now specialize (IHl i (j + 1) Hij1).
Qed.

Theorem in_nth_find_all_loop_eqb : ∀ l i k b,
  b ∈ nth_find_all_loop (Nat.eqb i) l k
  → k ≤ b
  → List.nth (b - k) l 0 = i.
Proof.
intros * Hb1 Hbk.
revert i k b Hb1 Hbk.
induction l as [| a]; intros; [ easy | ].
cbn.
remember (b - k) as bk eqn:Hbk1; symmetry in Hbk1.
destruct bk. {
  cbn in Hb1.
  remember (i =? a) as ia eqn:Hia; symmetry in Hia.
  destruct ia; [ now apply Nat.eqb_eq in Hia | ].
  replace k with b in Hb1 by flia Hbk Hbk1.
  exfalso.
  revert Hb1.
  apply not_in_nth_find_all_loop; flia.
}
cbn in Hb1.
remember (i =? a) as ia eqn:Hia; symmetry in Hia.
destruct ia. {
  apply Nat.eqb_eq in Hia; subst a.
  destruct Hb1 as [Hb1| Hb1]; [ flia Hb1 Hbk1 | ].
  specialize (IHl i (k + 1) b Hb1) as H1.
  assert (H : k + 1 ≤ b) by flia Hbk1.
  specialize (H1 H); clear H.
  now replace (b - (k + 1)) with bk in H1 by flia Hbk1.
}
specialize (IHl i (k + 1) b Hb1) as H1.
assert (H : k + 1 ≤ b) by flia Hbk1.
specialize (H1 H); clear H.
now replace (b - (k + 1)) with bk in H1 by flia Hbk1.
Qed.

Theorem in_nth_find_all_loop_eqb_if : ∀ {a} l d,
  a < length l
  → a + d ∈ nth_find_all_loop (Nat.eqb (List.nth a l 0)) l d.
Proof.
intros * Hal.
revert d a Hal.
induction l as [| b]; intros; [ easy | ].
cbn.
destruct a; [ now rewrite Nat.eqb_refl; left | ].
remember (List.nth a l 0 =? b) as c eqn:Hc; symmetry in Hc.
destruct c. {
  right.
  rewrite Nat.add_succ_comm, Nat.add_1_r.
  cbn in Hal.
  apply Nat.succ_lt_mono in Hal.
  now apply IHl.
}
rewrite Nat.add_succ_comm, Nat.add_1_r.
cbn in Hal.
apply Nat.succ_lt_mono in Hal.
now apply IHl.
Qed.

Theorem in_flat_map_nth_find_all_loop_eq : ∀ l j k len b,
  b ∈ List.flat_map (λ i, nth_find_all_loop (Nat.eqb i) l k) (List.seq j len)
  → k ≤ b
  → j ≤ List.nth (b - k) l 0 < j + len.
Proof.
intros * Hbf Hkb.
apply List.in_flat_map in Hbf.
destruct Hbf as (i & Hi & Hik).
apply in_nth_find_all_loop_eqb in Hik; [ | easy ].
rewrite Hik.
now apply List.in_seq in Hi.
Qed.

Theorem flat_map_nth_find_all_loop_cons : ∀ a l k i len,
  a < i ∨ i + len ≤ a
  → List.flat_map (λ j, nth_find_all_loop (Nat.eqb j) (a :: l) k)
       (List.seq i len) =
    List.flat_map (λ j, nth_find_all_loop (Nat.eqb j) l (k + 1))
      (List.seq i len).
Proof.
intros * Hai.
do 2 rewrite List.flat_map_concat_map; f_equal; cbn.
apply List.map_ext_in_iff.
intros b Hb.
apply List.in_seq in Hb.
remember (b =? a) as c eqn:Hc; symmetry in Hc.
destruct c; [ | easy ].
apply Nat.eqb_eq in Hc; subst b.
flia Hai Hb.
Qed.

Theorem dispatch_list_length : ∀ l, length (dispatch_list l) = length l.
Proof.
intros.
unfold dispatch_list.
now rewrite List.length_map, List.length_seq.
Qed.

Theorem dispatch_list_is_pre_partition : ∀ l,
  (∀ a, a ∈ l → a < List.length l)
  → is_pre_partition (dispatch_list l).
Proof.
intros * Hl.
split. {
  intros l1 Hl1 i Hi.
  unfold dispatch_list in Hl1.
  move i at top.
  move l1 before l.
  apply List.in_map_iff in Hl1.
  destruct Hl1 as (b & Hb & Hbs).
  subst l1; move b before i.
  unfold nth_find_all in Hi.
  assert
    (H : ∀ A f (l : list A) i j,
     j < List.length (nth_find_all_loop f l i)
     → List.nth j (nth_find_all_loop f l i) 0 < i + List.length l). {
    clear.
    intros * Hj.
    revert i j Hj.
    induction l as [| a]; intros; [ easy | ].
    cbn in Hj; cbn.
    destruct (f a). {
      cbn in Hj; cbn.
      destruct j; [ flia | ].
      apply Nat.succ_lt_mono in Hj.
      rewrite Nat.add_1_r in Hj.
      rewrite Nat.add_1_r.
      rewrite <- Nat.add_succ_comm.
      now apply IHl.
    } {
      rewrite Nat.add_1_r in Hj.
      rewrite Nat.add_1_r.
      rewrite <- Nat.add_succ_comm.
      now apply IHl.
    }
  }
  apply List.in_split in Hi.
  destruct Hi as (l1 & l2 & Hi).
  specialize (H nat (Nat.eqb b) l 0 (List.length l1)) as H1.
  rewrite Hi in H1.
  rewrite List.app_nth2 in H1; [ | now unfold "≥" ].
  rewrite Nat.sub_diag in H1; cbn in H1.
  rewrite dispatch_list_length.
  apply H1.
  rewrite List.length_app; cbn; flia.
}
split. {
  intros i Hi.
  rewrite dispatch_list_length in Hi.
  exists (List.nth (List.nth i l 0) (dispatch_list l) []).
  split. {
    apply List.nth_In.
    unfold dispatch_list.
    rewrite List.length_map.
    rewrite List.length_seq.
    apply Hl.
    now apply List.nth_In.
  }
  unfold dispatch_list.
  rewrite (List_map_nth' 0). 2: {
    rewrite List.length_seq.
    apply Hl.
    now apply List.nth_In.
  }
  rewrite List.seq_nth. 2: {
    apply Hl.
    now apply List.nth_In.
  }
  cbn.
  unfold nth_find_all.
  assert
      (H : ∀ d, i + d ∈ nth_find_all_loop (Nat.eqb (List.nth i l 0)) l d). {
    revert i Hi.
    clear Hl.
    induction l as [| a]; intros; [ easy | ].
    destruct i; [ now cbn; rewrite Nat.eqb_refl; left | cbn ].
    enough
        (S i + d ∈ nth_find_all_loop (Nat.eqb (List.nth i l 0)) l (d + 1)). {
      destruct (List.nth i l 0 =? a); [ now right | easy ].
    }
    cbn in Hi; apply Nat.succ_lt_mono in Hi.
    rewrite Nat.add_succ_comm, Nat.add_1_r.
    now apply IHl.
  }
  replace i with (i + 0) at 1 by apply Nat.add_0_r.
  apply H.
}
split. {
  unfold dispatch_list.
  rewrite <- List.flat_map_concat_map.
  assert (Hnd : ∀ l i j, List.NoDup (nth_find_all_loop (Nat.eqb i) l j)). {
    clear.
    intros.
    revert i j.
    induction l as [| a]; intros; [ constructor | ].
    cbn - [ Nat.eqb ].
    remember (i =? a) as ia eqn:Hia; symmetry in Hia.
    destruct ia. {
      constructor; [ apply not_in_nth_find_all_loop; flia | ].
      apply IHl.
    }
    apply IHl.
  }
  assert
  (H : ∀ i k len,
      List.NoDup
        (List.flat_map (λ j, nth_find_all_loop (Nat.eqb j) l k)
                  (List.seq i len))). {
    clear Hl.
    induction l as [| a]; intros. {
      cbn; clear.
      revert i.
      induction len; intros; [ constructor | apply IHlen ].
    }
    destruct (lt_dec a i) as [Hai| Hai]. {
      rewrite flat_map_nth_find_all_loop_cons; [ | now left ].
      apply IHl.
    }
    apply Nat.nlt_ge in Hai.
    destruct (le_dec (i + len) a) as [Hila| Hila]. {
      rewrite flat_map_nth_find_all_loop_cons; [ | now right ].
      apply IHl.
    }
    apply Nat.nle_gt in Hila.
    rewrite List.flat_map_concat_map.
    replace len with (a - i + (len - (a - i))) by flia Hila.
    rewrite List.seq_app.
    rewrite List.map_app.
    rewrite List.concat_app.
    do 2 rewrite <- List.flat_map_concat_map.
    rewrite flat_map_nth_find_all_loop_cons; [ | right; flia Hai ].
    rewrite (Nat.add_comm i), Nat.sub_add; [ | easy ].
    replace (len - (a - i)) with (1 + (len - (a - i) - 1)) by flia Hai Hila.
    rewrite List.seq_app.
    do 2 rewrite List.flat_map_concat_map.
    rewrite List.map_app, List.concat_app.
    unfold List.seq at 2, List.map at 2, List.concat at 2.
    rewrite List.app_nil_r.
    remember (nth_find_all_loop (Nat.eqb a) _ _) as x; cbn in Heqx; subst x.
    rewrite Nat.eqb_refl.
    do 2 rewrite <- List.flat_map_concat_map.
    apply NoDup_app_iff.
    split; [ apply IHl | ].
    split. {
      apply NoDup_app_iff.
      split. {
        constructor; [ | apply Hnd ].
        apply not_in_nth_find_all_loop; flia.
      }
      split. {
        rewrite flat_map_nth_find_all_loop_cons; [ | left; flia ].
        apply IHl.
      }
      intros b Hb Hbf.
      apply in_flat_map_nth_find_all_loop_eq in Hbf. 2: {
        destruct Hb as [Hb| Hb]; [ now subst b | ].
        apply Nat.nlt_ge; intros H; revert Hb.
        apply not_in_nth_find_all_loop; flia H.
      }
      destruct Hb as [Hb| Hb]. {
        subst k.
        rewrite Nat.sub_diag in Hbf; cbn in Hbf; flia Hbf.
      }
      remember (b - k) as bk eqn:Hbk; symmetry in Hbk.
      destruct bk; [ cbn in Hbf; flia Hbf | ].
      cbn in Hbf.
      apply in_nth_find_all_loop_eqb in Hb; [ | flia Hbk ].
      replace (b - (k + 1)) with bk in Hb by flia Hbk.
      flia Hb Hbf.
    }
    intros b Hb1 Hb2.
    destruct Hb2 as [Hb2| Hb2]. {
      subst k.
      apply List.in_flat_map in Hb1.
      destruct Hb1 as (j & Hj & Hjb).
      revert Hjb.
      apply not_in_nth_find_all_loop; flia.
    }
    apply List.in_app_iff in Hb2.
    destruct Hb2 as [Hb2| Hb2]. {
      destruct (le_dec (k + 1) b) as [Hkb| Hkb]. {
        apply in_flat_map_nth_find_all_loop_eq in Hb1; [ | easy ].
        apply in_nth_find_all_loop_eqb in Hb2; [ | easy ].
        rewrite Hb2 in Hb1.
        flia Hb1.
      }
      apply Nat.nle_gt in Hkb.
      revert Hb2.
      now apply not_in_nth_find_all_loop.
    }
    rewrite flat_map_nth_find_all_loop_cons in Hb2; [ | left; flia ].
    destruct (le_dec (k + 1) b) as [Hkb| Hkb]. {
      apply in_flat_map_nth_find_all_loop_eq in Hb1; [ | easy ].
      apply in_flat_map_nth_find_all_loop_eq in Hb2; [ | easy ].
      flia Hb1 Hb2.
    }
    apply Nat.nle_gt in Hkb.
    apply List.in_flat_map in Hb1.
    destruct Hb1 as (x & Hx & Hxl).
    revert Hxl.
    now apply not_in_nth_find_all_loop.
  }
  apply H.
} {
  intros l1 Hl1.
  unfold dispatch_list in Hl1.
  apply List.in_map_iff in Hl1.
  destruct Hl1 as (i & Hill & Hil); subst l1.
  apply List.in_seq in Hil; destruct Hil as (_, Hil); cbn in Hil.
  unfold nth_find_all.
  remember 0 as j; clear Heqj.
  clear Hl Hil.
  revert i j.
  induction l as [| k]; intros; [ constructor | cbn ].
  remember (i =? k) as b eqn:Hb; symmetry in Hb.
  destruct b; [ | apply IHl ].
  apply Nat.eqb_eq in Hb; subst k.
  constructor; [ apply IHl | clear ].
  remember 0 as d.
  clear Heqd.
  revert i j d.
  induction l as [| k]; intros; [ constructor | cbn ].
  remember (i =? k) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    apply Nat.eqb_eq in Hb; subst k.
    constructor; flia.
  }
  replace (j + S d + 1) with (j + S (S d)) by flia.
  apply IHl.
}
Qed.

Theorem nth_find_loop_map : ∀ A B f (g : A → B) i l,
  nth_find_loop f (List.map g l) i =
  nth_find_loop (λ a, f (g a)) l i.
Proof.
intros.
revert f g i.
induction l as [| a]; intros; [ easy | cbn ].
destruct (f (g a)); [ easy | ].
apply IHl.
Qed.

Theorem nth_find_all_loop_map : ∀ A B (f : B → bool) g i (l : list A),
  nth_find_all_loop f (List.map g l) i = nth_find_all_loop (λ a, f (g a)) l i.
Proof.
intros.
revert i.
induction l as [| a]; intros; [ easy | cbn ].
destruct (f (g a)); [ now rewrite IHl | ].
apply IHl.
Qed.

Theorem nth_find_all_map : ∀ A B (f : B → bool) g (l : list A),
  nth_find_all f (List.map g l) = nth_find_all (λ a, f (g a)) l.
Proof.
intros.
apply nth_find_all_loop_map.
Qed.

Theorem nat_in_list_true_iff : ∀ i l,
  nat_in_list i l = true ↔ i ∈ l.
Proof.
intros.
induction l as [| j]; [ easy | cbn ].
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  split; [ now intros; left | easy ].
}
split; [ now intros; right; apply IHl | ].
intros [H| H]; [ now subst j | now apply IHl ].
Qed.

Theorem nat_in_list_false_iff : ∀ i l,
  nat_in_list i l = false ↔ ∀ j, j ∈ l → i ≠ j.
Proof.
intros.
split. {
  intros Hil j Hjl Hij.
  subst j.
  revert i Hil Hjl.
  induction l as [| a]; intros; [ easy | ].
  cbn in Hil, Hjl.
  destruct Hjl as [Hjl| Hjl]. {
    subst a.
    now destruct (Nat.eq_dec i i).
  }
  destruct (Nat.eq_dec i a) as [Hia| Hia]; [ easy | ].
  now apply (IHl i).
} {
  intros Hil.
  revert i Hil.
  induction l as [| a]; intros; [ easy | cbn ].
  destruct (Nat.eq_dec i a) as [Hia| Hia]. {
    subst i.
    now specialize (Hil a (or_introl eq_refl)).
  }
  apply IHl.
  intros j Hj.
  now apply Hil; right.
}
Qed.

Theorem locate_dispatch_list : ∀ l,
  (∀ a : nat, a ∈ l → a < List.length l)
  → locate_list (dispatch_list l) = l.
Proof.
intros * Hl.
specialize (dispatch_list_is_pre_partition l Hl) as H1.
unfold is_pre_partition in H1.
destruct H1 as (Hin & Huni & Hint & Hsort).
remember (dispatch_list l) as ll.
unfold dispatch_list in Heqll.
rewrite Heqll.
unfold locate_list.
rewrite List.length_map, List.length_seq.
replace l with
    (List.map (λ i, List.nth i l 0) (List.seq 0 (List.length l))) at 2. 2: {
  clear.
  induction l as [| a]; [ easy | ].
  f_equal; cbn; f_equal.
  rewrite <- List.seq_shift.
  now rewrite List.map_map.
}
apply List.map_ext_in_iff.
intros a Ha.
unfold nth_find.
unfold nth_find_all.
replace (List.length l) with
    (List.nth a l 0 + 1 + (List.length l - (List.nth a l 0 + 1))). 2: {
  apply List.in_seq in Ha; cbn in Ha.
  destruct Ha as (_, Ha).
  specialize (Hl (List.nth a l 0) (List.nth_In l 0 Ha)) as H1.
  flia H1.
}
do 2 rewrite List.seq_app.
do 2 rewrite Nat.add_0_l.
replace (List.seq _ 1) with [List.nth a l 0] by easy.
do 2 rewrite List.map_app.
rewrite <- List.app_assoc.
rewrite nth_find_loop_app_2. 2: {
  intros l1 Hl1.
  apply nat_in_list_false_iff.
  intros j Hj Haj; subst j.
  apply List.in_map_iff in Hl1.
  destruct Hl1 as (k & Hkl & Hka); subst l1.
  apply List.in_seq in Hka; destruct Hka as (_, Hka); cbn in Hka.
  apply in_nth_find_all_loop_eqb in Hj; [ | flia ].
  rewrite Nat.sub_0_r in Hj; subst k.
  flia Hka.
}
rewrite List.length_map, List.length_seq, Nat.add_0_l; cbn.
remember (nat_in_list a _) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
specialize ((proj1 (nat_in_list_false_iff _ _)) Hb a) as H1.
exfalso; apply H1; clear H1; [ | easy ].
apply List.in_seq in Ha; destruct Ha as (_, Ha); cbn in Ha.
specialize (in_nth_find_all_loop_eqb_if l 0 Ha) as H1.
now rewrite Nat.add_0_r in H1.
Qed.

Theorem in_to_radix_loop : ∀ it n i a,
  n ≠ 0
  → a ∈ to_radix_loop it n i
  → a < n.
Proof.
intros * Hnz Han.
revert a n i Hnz Han.
induction it; intros; [ easy | ].
cbn - [ "/" "mod" ] in Han |-*.
destruct Han as [Han| Han]. {
  rewrite <- Han.
  now apply Nat.mod_upper_bound.
}
now apply (IHit _ _ (i / n)).
Qed.

Theorem fold_left_to_radix : ∀ n i,
  i < n ^ n
  → List.fold_left (λ a j : nat, a * n + j) (List.rev (to_radix n i)) 0 = i.
Proof.
intros * Hin.
assert
  (H : ∀ it n i,
   i < n ^ it
   → List.fold_left (λ a j, a * n + j)
       (List.rev (to_radix_loop it n i)) 0 = i). {
  clear.
  intros * Hin.
  revert n i Hin.
  induction it; intros; [ now apply Nat.lt_1_r in Hin; subst i | ].
  cbn.
  rewrite List.fold_left_app; cbn.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
  specialize (Nat.div_mod i n Hnz) as H1.
  rewrite H1 at 3; f_equal.
  rewrite Nat.mul_comm; f_equal.
  apply IHit.
  apply (Nat.mul_lt_mono_pos_r (n ^ 1)); [ rewrite Nat.pow_1_r; flia Hnz | ].
  rewrite <- Nat.pow_add_r, Nat.add_1_r, Nat.pow_1_r.
  apply (Nat.le_lt_trans _ i); [ | easy ].
  rewrite Nat.mul_comm.
  apply Nat.Div0.mul_div_le.
}
now apply H.
Qed.

(*
Compute (let n := 4 in let i := 255 in locate (dispatch n i)).
*)

Theorem locate_dispatch : ∀ n i, i < n ^ n → locate (dispatch n i) = i.
Proof.
intros * Hin.
unfold locate, dispatch.
rewrite locate_dispatch_list. 2: {
  intros a Ha.
  apply List.in_rev in Ha.
  rewrite List.length_rev.
  unfold to_radix in Ha |-*.
  rewrite to_radix_loop_length.
  apply in_to_radix_loop in Ha; [ easy | ].
  now intros H; subst n.
}
rewrite dispatch_list_length.
rewrite List.length_rev.
assert
  (H : ∀ i b l,
   List.fold_left (λ a j, a * List.length (to_radix n i) + j) l b =
   List.fold_left (λ a j, a * n + j) l b). {
  clear.
  intros.
  unfold to_radix.
  destruct l as [| a]; [ easy | cbn ].
  unfold to_radix.
  now rewrite to_radix_loop_length.
}
rewrite H; clear H.
now apply fold_left_to_radix.
Qed.

(* pre_partition_in n j k i = true ↔ pre-partition i has the j in k-th set
        0 ≤ i < n^n
        0 ≤ j < n
        0 ≤ k < n
   e.g.
      dispatch n i = [_; _; [...; j; ...]; _; ...]  (* some pre-partition *)
                      <----> <--------->
                         k      k-th
                      <------------------------->
                                  n
   then
     pre_partition_in n j k i = true
 *)

Definition pre_partition_in n j k i :=
  (i + n ^ n - k * n ^ (n - j - 1)) mod (n ^ (n - j)) <? n ^ (n - j - 1).

(* example: all pre-partitions that have the j in k-th set *)
(*
Compute
  (let n := 3 in let j := 1 in let k := 2 in
   List.map (λ i, (i, dispatch n i))
    (List.filter (pre_partition_in n j k) (List.seq 0 (n ^ n)))).
*)

Theorem nth_find_all_loop_app : ∀ A f (l1 l2 : list A) i,
  nth_find_all_loop f (l1 ++ l2) i =
  nth_find_all_loop f l1 i ++ nth_find_all_loop f l2 (i + List.length l1).
Proof.
intros.
revert i l2.
induction l1 as [| a1]; intros. {
  now cbn; rewrite Nat.add_0_r.
}
cbn.
destruct (f a1). {
  cbn; f_equal.
  rewrite <- (Nat.add_succ_comm _ (List.length l1)).
  rewrite Nat.add_1_r.
  apply IHl1.
}
rewrite <- (Nat.add_succ_comm _ (List.length l1)).
rewrite Nat.add_1_r.
apply IHl1.
Qed.

Theorem fold_left_mul_add_mod : ∀ n j l,
  List.fold_left (λ a i, a * n + i) l j mod n = List.last (j :: l) 0 mod n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  cbn - [ List.last ].
  erewrite List_fold_left_ext_in. 2: {
    intros * Hb.
    now rewrite Nat.mul_0_r, Nat.add_0_l.
  }
  revert j.
  induction l as [| i]; intros; [ easy | ].
  remember (i :: l) as l'; cbn; subst l'.
  apply IHl.
}
revert n j Hnz.
induction l as [| b]; intros; [ easy | ].
cbn - [ List.last ].
remember (b :: l) as l'; cbn; subst l'.
transitivity (List.fold_left (λ a i : nat, a * n + i) l b mod n). 2: {
  now apply IHl.
}
clear - Hnz.
revert b n j Hnz.
induction l as [| a]; intros; [ apply Nat_mod_add_l_mul_r | cbn ].
rewrite IHl; [ | easy ].
now rewrite IHl.
Qed.

Theorem fold_left_mul_add_div : ∀ n j l,
  (∀ i, i ∈ l → i < n)
  → l ≠ []
  → List.fold_left (λ a i, a * n + i) l j / n =
     List.fold_left (λ a i, a * n + i) (List.removelast l) j.
Proof.
intros * Hin Hln.
destruct l as [| b]; [ easy | clear Hln ].
cbn - [ List.removelast ].
revert n j b Hin.
induction l as [| a]; intros. {
  cbn.
  rewrite Nat.div_add_l. 2: {
    intros H; subst n.
    now specialize (Hin b (or_introl eq_refl)).
  }
  rewrite Nat.div_small; [ | now apply Hin; left ].
  now rewrite Nat.add_0_r.
}
cbn - [ List.removelast ].
remember (a :: l) as l'; cbn; subst l'.
rewrite IHl; [ easy | ].
intros i Hl.
now apply Hin; right.
Qed.

Theorem locate_list_length :
  ∀ ll, List.length (locate_list ll) = List.length ll.
Proof.
intros.
unfold locate_list.
now rewrite List.length_map, List.length_seq.
Qed.

Theorem eq_nth_find_all_loop_nil : ∀ A f (l : list A) i,
  nth_find_all_loop f l i = [] ↔ ∀ j, j ∈ l → f j = false.
Proof.
intros.
split. {
  intros Hfl * Hj.
  revert i j Hj Hfl.
  induction l as [| k]; intros; [ easy | ].
  cbn in Hfl.
  remember (f k) as b eqn:Hb; symmetry in Hb.
  destruct b; [ easy | ].
  destruct Hj as [Hj| Hj]; [ now subst k | ].
  now apply (IHl (i + 1)).
} {
  intros Hlf.
  revert i.
  induction l as [| k]; intros; [ easy | cbn ].
  remember (f k) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    specialize (Hlf k (or_introl eq_refl)).
    now rewrite Hlf in Hb.
  }
  apply IHl.
  intros j Hj.
  now apply Hlf; right.
}
Qed.

Theorem eq_nth_find_all_nil : ∀ A f (l : list A),
  nth_find_all f l = [] ↔ ∀ i, i ∈ l → f i = false.
Proof. intros; apply eq_nth_find_all_loop_nil. Qed.

Theorem eq_nth_find_all_loop_cons : ∀ {A} f j (d : A) l l' i,
  nth_find_all_loop f l i = j :: l' ↔
    i ≤ j < i + List.length l ∧
    (∀ k, i + k < j → f (List.nth k l d) = false) ∧
    f (List.nth (j - i) l d) = true ∧
    nth_find_all_loop f (List.skipn (j + 1 - i) l) (j + 1) = l'.
Proof.
intros.
split. {
  intros Hfl.
  split. {
    split. {
      apply Nat.nlt_ge; intros Hij.
      specialize (not_in_nth_find_all_loop f l Hij) as H1.
      now apply H1; rewrite Hfl; left.
    }
    revert i j Hfl.
    induction l as [| a]; intros; [ easy | ].
    cbn in Hfl |-*.
    remember (f a) as b eqn:Hb; symmetry in Hb.
    destruct b. {
      injection Hfl; clear Hfl; intros Hfl H; subst j; flia.
    }
    rewrite <- Nat.add_succ_comm, <- Nat.add_1_r.
    now apply IHl.
  }
  split. {
    intros k Hkj.
    revert i k Hfl Hkj.
    induction l as [| b]; intros; [ easy | ].
    cbn in Hfl.
    remember (f b) as b1 eqn:Hb1; symmetry in Hb1.
    destruct b1. {
      injection Hfl; clear Hfl; intros Hfl H; subst j.
      flia Hkj.
    }
    cbn.
    destruct k; [ easy | ].
    apply (IHl (i + 1)); [ easy | ].
    flia Hkj.
  }
  split. {
    revert i Hfl.
    induction l as [| b]; intros; [ easy | ].
    cbn in Hfl.
    remember (f b) as b1 eqn:Hb1; symmetry in Hb1.
    destruct b1. {
      injection Hfl; clear Hfl; intros Hfl H; subst j.
      now rewrite Nat.sub_diag; cbn.
    }
    cbn.
    remember (j - i) as ji eqn:Hji; symmetry in Hji.
    destruct ji. {
      apply Nat.sub_0_le in Hji.
      assert (H : j < i + 1) by flia Hji.
      specialize (not_in_nth_find_all_loop f l H) as H1; clear H.
      rewrite Hfl in H1.
      now exfalso; apply H1; left.
    }
    replace ji with (j - (i + 1)) by flia Hji.
    now apply IHl.
  } {
    revert i Hfl.
    induction l as [| b]; intros; [ easy | ].
    cbn in Hfl.
    remember (f b) as b1 eqn:Hb1; symmetry in Hb1.
    destruct b1. {
      injection Hfl; clear Hfl; intros Hfl H; subst j.
      rewrite Nat.add_comm at 1.
      now rewrite Nat.add_sub.
    }
    specialize (IHl (i + 1) Hfl).
    assert (Hij : i + 1 ≤ j). {
      apply Nat.nlt_ge; intros Hij.
      specialize (not_in_nth_find_all_loop f l Hij) as H1.
      now apply H1; rewrite Hfl; left.
    }
    replace (j + 1 - (i + 1)) with (j - i) in IHl by flia Hij.
    replace (j + 1 - i) with (S (j - i)) by flia Hij.
    now rewrite List.skipn_cons.
  }
} {
  intros ((Hij, Hjil) & Hikj & Hfji & Hsk).
  subst l'.
  revert j i Hij Hjil Hikj Hfji.
  induction l as [| b]; intros. {
    cbn in Hjil.
    flia Hij Hjil.
  }
  cbn.
  remember (f b) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1. {
    f_equal. {
      cbn in Hfji.
      remember (j - i) as ji eqn:Hji; symmetry in Hji.
      destruct ji; [ flia Hij Hji | exfalso ].
      specialize (Hikj 0); cbn in Hikj.
      rewrite Hikj in Hb1; [ easy | ].
      flia Hji.
    }
    destruct (Nat.eq_dec i j) as [Hiej| Hiej]. {
      subst j.
      now replace (i + 1 - i) with 1 by flia.
    }
    specialize (Hikj 0).
    assert (H : i + 0 < j) by flia Hij Hiej.
    specialize (Hikj H); cbn in Hikj.
    now rewrite Hikj in Hb1.
  }
  replace (j + 1 - i) with (S (j - i)) by flia Hij.
  rewrite List.skipn_cons.
  destruct (Nat.eq_dec i j) as [Hiej| Hiej]. {
    subst j; rewrite Nat.sub_diag in Hfji; cbn in Hfji.
    now rewrite Hfji in Hb1.
  }
  replace (j - i) with (j + 1 - (i + 1)) by flia.
  replace (j - i) with (S (j - (i + 1))) in Hfji by flia Hij Hiej.
  cbn in Hfji, Hjil.
  rewrite <- Nat.add_succ_comm, <- Nat.add_1_r in Hjil.
  apply IHl; [ flia Hij Hiej | easy | | easy ].
  intros k Hk.
  rewrite Nat.add_1_r, Nat.add_succ_comm in Hk.
  now specialize (Hikj _ Hk).
}
Qed.

Theorem eq_nth_find_all_cons : ∀ A f j (d : A) l l',
  nth_find_all f l = j :: l' ↔
    j < List.length l ∧
    (∀ k : nat, k < j → f (List.nth k l d) = false) ∧
    f (List.nth j l d) = true ∧
    nth_find_all_loop f (List.skipn (j + 1) l) (j + 1) = l'.
Proof.
intros.
specialize (eq_nth_find_all_loop_cons f j d l l' 0) as H1.
cbn in H1.
do 2 rewrite Nat.sub_0_r in H1.
unfold nth_find_all.
split. {
  intros H.
  specialize (proj1 H1 H) as H2.
  now destruct H2 as ((_, H3), H2).
} {
  intros H.
  destruct H as (H2, H3).
  apply H1.
  split; [ | easy ].
  split; [ flia | easy ].
}
Qed.

Theorem in_nth_nth_find_loop : ∀ ll {i} d,
  (∀ i, i < List.length ll → ∃ l : list nat, l ∈ ll ∧ i ∈ l)
  → i < List.length ll
  → i ∈ List.nth (nth_find_loop (nat_in_list i) ll d - d) ll [].
Proof.
intros * Huni Hi.
specialize (Huni _ Hi).
destruct Huni as (l & Hlll & Hil).
clear - Hlll Hil.
revert d l Hlll Hil.
induction ll as [| l1]; intros; [ easy | ].
cbn - [ List.nth ].
remember (nat_in_list i l1) as b eqn:Hb; symmetry in Hb.
destruct b. {
  rewrite Nat.sub_diag; cbn.
  now apply nat_in_list_true_iff in Hb.
}
destruct Hlll as [Hlll| Hlll]. {
  subst l1.
  apply nat_in_list_true_iff in Hil.
  now rewrite Hil in Hb.
}
cbn.
remember (nth_find_loop (nat_in_list i) ll (d + 1) - d) as b eqn:Hb1.
symmetry in Hb1.
destruct b. {
  apply Nat.sub_0_le in Hb1.
  apply Nat.nlt_ge in Hb1.
  exfalso; apply Hb1; clear Hb1.
  clear.
  revert d.
  induction ll as [| l]; intros; cbn; [ flia | ].
  remember (nat_in_list i l) as b eqn:Hb; symmetry in Hb.
  destruct b; [ flia | ].
  transitivity (d + 1); [ flia | apply IHll ].
}
specialize (IHll (d + 1) l Hlll Hil).
rewrite Nat.sub_add_distr in IHll.
rewrite Hb1 in IHll.
now rewrite Nat_sub_succ_1 in IHll.
Qed.

Theorem in_nth_nth_find : ∀ ll j,
  (∀ i, i < List.length ll → ∃ l : list nat, l ∈ ll ∧ i ∈ l)
  → j < List.length ll
  → j ∈ List.nth (nth_find (nat_in_list j) ll) ll [].
Proof.
intros * Huni Hi.
specialize (in_nth_nth_find_loop ll 0 Huni Hi) as H1.
now rewrite Nat.sub_0_r in H1.
Qed.

Theorem eq_nth_find_all_loop_iff : ∀ A f (d : A) l l1 i,
  nth_find_all_loop f l i = l1 ↔
    match l1 with
    | [] => (∀ j, j ∈ l → f j = false)
    | j :: l2 =>
        i ≤ j < i + List.length l ∧
        (∀ k, i + k < j → f (List.nth k l d) = false) ∧
        f (List.nth (j - i) l d) = true ∧
        nth_find_all_loop f (List.skipn (j + 1 - i) l) (j + 1) = l2
end.
Proof.
intros.
destruct l1 as [| b]; [ apply eq_nth_find_all_loop_nil | ].
apply eq_nth_find_all_loop_cons.
Qed.

Theorem length_loc_loc_bl_sens_list : ∀ n f x,
  List.length (loc_sens_list n f x) =
  List.length (loc_bl_sens_list (List.map (λ i, [i]) (List.seq 0 n)) f x).
Proof.
intros.
unfold loc_sens_list.
unfold loc_bl_sens_list.
cbn; unfold "^^"; cbn.
remember 0 as s eqn:Hs; clear Hs.
revert s.
induction n; intros s; cbn; [ easy | ].
remember (negb (Bool.eqb (f x) (f (Nat_togglebit s x)))) as b eqn:Hb.
symmetry in Hb.
destruct b; [ cbn; f_equal; apply IHn | apply IHn ].
Qed.

Theorem loc_length_loc_bl_sens_list : ∀ n f x,
  local_sensitivity n f x =
  List.length (loc_bl_sens_list (List.map (λ i, [i]) (List.seq 0 n)) f x).
Proof.
intros.
apply length_loc_loc_bl_sens_list.
Qed.

Theorem map_loc_sens : ∀ n f l,
  List.map (local_sensitivity n f) l =
  List.map
    (λ x,
       List.length
         (loc_bl_sens_list (List.map (λ i, [i]) (List.seq 0 n)) f x))
    l.
Proof.
intros.
induction l; cbn; [ easy | ].
rewrite <- loc_length_loc_bl_sens_list; f_equal.
apply IHl.
Qed.

Theorem Nat_pow_from_sum :
  let ro := nat_ring_like_op in
  ∀ a n, a * n ≠ 0 →
  n ^ a = (n - 1) * (∑ (i = 0, a - 1), n ^ i) + 1.
Proof.
intros * Hanz.
destruct a; [ easy | ].
replace (S a - 1) with a by flia.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  now rewrite Hnz, Nat.mul_comm in Hanz.
}
clear Hanz.
revert n Hnz.
induction a; intros. {
  unfold iter_seq, iter_list; cbn.
  do 2 rewrite Nat.mul_1_r.
  symmetry; apply Nat.sub_add.
  now apply Nat.neq_0_lt_0.
}
rewrite iter_seq_split_last; [ | easy ].
rewrite (iter_shift 1). 2: {
  split; [ easy | ].
  now apply -> Nat.succ_le_mono.
}
rewrite Nat.sub_diag.
rewrite Nat_sub_succ_1.
rewrite Nat.mul_add_distr_l, Nat.add_shuffle0.
erewrite iter_seq_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat.add_comm, Nat.add_sub.
}
rewrite <- IHa; [ | easy ].
replace (n ^ S a) with (1 * n ^ S a) at 1 by flia.
rewrite <- Nat.mul_add_distr_r.
now replace (1 + (n - 1)) with n by flia Hnz.
Qed.

Theorem fold_left_horner_eval_sum :
  let ro := nat_ring_like_op in
  ∀ k n a x,
  List.fold_left (λ acc i : nat, acc * x + a (n + k - i))
    (List.seq (S k) n) (∑ (i = 0, k), a (n + i) * x ^ i) =
  List.fold_left (λ c i : nat, c + a (n + k - i) * x ^ (n + k - i))
    (List.seq (S k) n) (∑ (i = 0, k), a (n + i) * x ^ (n + i)).
Proof.
intros.
revert k.
induction n; intros; [ easy | ].
specialize (IHn (S k)).
replace (n + S k) with (S n + k) in IHn by flia.
replace (List.seq (S k) (S n)) with (S k :: List.seq (S (S k)) n) by easy.
cbn - [ "-" "+" ].
replace (S n + k - S k) with n by flia.
rewrite iter_seq_split_first in IHn; [ | easy | | | easy ]; cycle 1. {
  apply Nat.add_0_r.
} {
  apply Nat.add_assoc.
}
rewrite Nat.pow_0_r, Nat.add_0_r, Nat.mul_1_r in IHn.
rewrite (Nat.add_comm (a n)) in IHn.
rewrite iter_seq_succ_succ in IHn.
rewrite iter_seq_eq_compat with (h := λ i, a (S n + i) * x ^ i * x)
  in IHn. 2: {
  intros i Hi.
  rewrite Nat.add_succ_comm.
  now cbn; rewrite Nat.mul_assoc, Nat.mul_shuffle0.
}
remember (∑ (i = 0, k), a (S n + i) * x ^ i * x) as y.
unfold iter_seq in Heqy.
rewrite Nat.sub_0_r in Heqy.
specialize mul_iter_list_distr_r as H1.
specialize (H1 nat nat x (List.seq 0 (S k))).
specialize (H1 (λ i, a (S n + i) * x ^ i)).
specialize (H1 Nat.add Nat.mul 0).
cbn - [ List.seq "+" ] in H1.
cbn - [ List.seq "+" ] in Heqy.
rewrite <- H1 in Heqy. 2: {
  intros; apply Nat.mul_add_distr_r.
}
subst y; clear H1.
symmetry in IHn; symmetry.
rewrite iter_seq_split_first in IHn; [ | easy | | | easy ]; cycle 1. {
  apply Nat.add_0_r.
} {
  apply Nat.add_assoc.
}
rewrite Nat.add_0_r in IHn.
rewrite (Nat.add_comm (a n * x ^ n)) in IHn.
rewrite iter_seq_succ_succ in IHn.
rewrite iter_seq_eq_compat with (h := λ i, a (S n + i) * x ^ (S n + i))
  in IHn. 2: {
  intros i Hi.
  now rewrite Nat.add_succ_comm.
}
apply IHn.
Qed.

Theorem horner_is_eval_polyn :
  let ro := nat_ring_like_op in
  let rp := nat_ring_like_prop in
  ∀ n a x,
  List.fold_left (λ acc i, acc * x + a (n - i)) (List.seq 0 (S n)) 0 =
  ∑ (i = 0, n), a i * x ^ i.
Proof.
intros.
rewrite rngl_summation_rtl.
rewrite Nat.add_0_r.
specialize (fold_left_horner_eval_sum 0 n a x) as H1.
rewrite Nat.add_0_r in H1.
do 2 rewrite rngl_summation_only_one, Nat.add_0_r in H1.
rewrite Nat.pow_0_r, Nat.mul_1_r in H1; cbn.
rewrite Nat.sub_0_r, H1.
unfold iter_seq, iter_list.
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem horner_is_eval_polyn2 :
  let ro := nat_ring_like_op in
  ∀ n a x,
  List.fold_left (λ acc i, acc * x + a i) (List.seq 0 (S n)) 0 =
  ∑ (i = 0, n), a (n - i) * x ^ i.
Proof.
intros.
specialize (horner_is_eval_polyn n (λ i, a (n - i)) x) as H1.
cbn - [ "-" List.fold_left List.seq ] in H1.
cbn.
rewrite <- H1; cbn.
rewrite Nat.sub_0_r, Nat.sub_diag.
apply List_fold_left_ext_in.
intros b c Hb; f_equal; f_equal.
apply List.in_seq in Hb.
flia Hb.
Qed.

Theorem to_radix_fold_left : ∀ n,
  to_radix n (List.fold_left (λ a i, a * n + i) (List.seq 0 n) 0) =
  List.rev (List.seq 0 n).
Proof.
intros.
assert
  (Hft : ∀ it n l d,
   n = List.length l
   → n ≤ it
   → (∀ i, i ∈ l → i < n + d)
   → List.firstn n
        (to_radix_loop it (n + d)
           (List.fold_left (λ a j, a * (n + d) + j) l 0)) =
        List.rev l). {
  clear.
  intros * Hnl Hit Hil.
  revert n d l Hnl Hit Hil.
  induction it; intros. {
    apply Nat.le_0_r in Hit; subst n.
    apply List.length_zero_iff_nil in Hit.
    now subst l.
  }
  cbn.
  rewrite fold_left_mul_add_mod.
  destruct l as [| a]. {
    now cbn in Hnl; subst n; cbn.
  }
  remember (a :: l) as l' eqn:Hl'; symmetry in Hl'.
  rewrite fold_left_mul_add_div; [ | easy | ]. 2: {
    now subst l'.
  }
  clear a l Hl'.
  rename l' into l.
  destruct n. {
    symmetry in Hnl.
    now apply List.length_zero_iff_nil in Hnl; subst l.
  }
  cbn - [ List.last "mod" ].
  remember (List.rev l) as rl eqn:Hrl; symmetry in Hrl.
  destruct rl as [| a]. {
    now apply List_eq_rev_nil in Hrl; subst l.
  }
  assert (Hlr : l = List.rev (a :: rl)). {
    rewrite <- Hrl; symmetry; apply List.rev_involutive.
  }
  rewrite Hlr.
  cbn - [ List.last "mod" ].
  rewrite List.app_comm_cons, List.last_last.
  rewrite Nat.mod_small. 2: {
    apply Hil; rewrite Hlr; cbn.
    now apply List.in_or_app; right; left.
  }
  f_equal.
  rewrite List.removelast_app; [ | easy ].
  rewrite List.app_nil_r.
  replace rl with (List.tl (List.rev l)) by now rewrite Hrl.
  cbn in Hil.
  replace (S (n + d)) with (n + S d) in Hil |-* by flia.
  apply Nat.succ_le_mono in Hit.
  rewrite IHit; [ apply List.rev_involutive | | easy | ]. 2: {
    intros i Hi.
    apply Hil.
    apply List.in_rev in Hi.
    apply List.in_rev.
    remember (List.rev l) as l'.
    clear - Hi; rename l' into l.
    induction l as [| a]; [ easy | ].
    cbn in Hi.
    destruct l as [| b]; [ easy | ].
    destruct Hi as [Hi| Hi]. {
      subst b.
      now right; left.
    }
    now right; apply IHl.
  }
  rewrite List.length_rev.
  apply Nat.succ_inj.
  rewrite Hnl, Hrl; cbn.
  rewrite Hlr.
  now rewrite List.length_rev.
}
specialize (Hft n n (List.seq 0 n) 0) as H1.
rewrite List.length_seq in H1.
specialize (H1 eq_refl (Nat.le_refl _)).
rewrite Nat.add_0_r in H1.
assert (H : ∀ i, i ∈ List.seq 0 n → i < n). {
  now intros i Hi; apply List.in_seq in Hi.
}
specialize (H1 H); clear H.
unfold to_radix.
remember (to_radix_loop _ _ _) as l.
rewrite <- H1; symmetry.
replace n with (List.length l). 2: {
  rewrite Heql.
  apply to_radix_loop_length.
}
apply List.firstn_all.
Qed.

Theorem fold_left_mul_seq_lt : ∀ n,
  List.fold_left (λ a i, a * n + i) (List.seq 0 n) 0 < n ^ n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ subst n; cbn; flia | ].
rewrite Nat_pow_from_sum. 2: {
  intros H; apply Hnz.
  apply Nat.eq_mul_0 in H.
  now destruct H.
}
rewrite Nat.add_1_r.
apply Nat.lt_succ_r.
unfold iter_seq.
rewrite mul_iter_list_distr_l; [ | apply Nat.mul_add_distr_l ].
cbn - [ List.seq ].
specialize (horner_is_eval_polyn (n - 1)) as H2.
specialize (H2 (λ i, n - 1 - i) n).
cbn - [ "-" List.fold_left List.seq ] in H2.
rewrite List_fold_left_ext_in with (g := λ acc i, acc * n + i) in H2. 2: {
  intros acc i Hacc.
  apply List.in_seq in Hacc.
  flia Hacc.
}
replace (S (n - 1)) with n in H2 at 1 by flia Hnz.
replace (S (n - 1)) with (S (n - 1) - 0) by flia Hnz.
rewrite H2.
rewrite Nat.mul_0_r, fold_iter_seq.
specialize @rngl_summation_le_compat as H1.
specialize (H1 nat).
specialize (H1 nat_ring_like_op nat_ring_like_prop).
cbn in H1.
specialize (H1 eq_refl).
apply Nat.leb_le.
apply H1.
intros i Hi.
apply Nat.leb_le.
apply Nat.mul_le_mono_r; flia.
Qed.

Theorem x_bs_ge_s : ∀ n f x,
  local_block_sensitivity n f x ≥ local_sensitivity n f x.
Proof.
intros.
rewrite loc_length_loc_bl_sens_list.
unfold local_block_sensitivity.
remember (pre_partitions n) as ll eqn:Hll.
remember (locate (dispatch_list (List.seq 0 n))) as j eqn:Hj.
specialize (@List.nth_split _ j ll []) as H1.
assert (H : j < List.length ll). {
  rewrite Hj, Hll.
  unfold pre_partitions.
  rewrite List.length_map, List.length_seq.
  unfold locate.
  rewrite locate_dispatch_list. 2: {
    intros a Ha.
    rewrite List.length_seq.
    now apply List.in_seq in Ha.
  }
  rewrite dispatch_list_length, List.length_seq.
  apply fold_left_mul_seq_lt.
}
specialize (H1 H); clear H.
destruct H1 as (l1 & l2 & Hll12 & Hl1).
unfold locate in Hj.
rewrite locate_dispatch_list in Hj. 2: {
  intros a Ha.
  apply List.in_seq in Ha.
  now rewrite List.length_seq.
}
rewrite dispatch_list_length in Hj.
rewrite List.length_seq in Hj.
rewrite Hll12.
rewrite List.map_app.
rewrite List.fold_right_app; cbn.
assert (Hjll : List.nth j ll [] = List.map (λ i, [i]) (List.seq 0 n)). {
  rewrite Hll.
  unfold pre_partitions.
  assert (Hjnn : j < n ^ n). {
    rewrite Hj.
    apply fold_left_mul_seq_lt.
  }
  rewrite (List_map_nth' 0) by now rewrite List.length_seq.
  rewrite List.seq_nth; [ cbn | easy ].
  unfold dispatch.
  rewrite Hj.
  rewrite to_radix_fold_left.
  rewrite List.rev_involutive.
  clear.
  unfold dispatch_list.
  rewrite List.length_seq.
  apply List.map_ext_in_iff.
  intros a Ha.
  unfold nth_find_all.
  apply (eq_nth_find_all_loop_cons _ _ 0).
  rewrite List.length_seq, Nat.sub_0_r, Nat.sub_0_r; cbn.
  apply List.in_seq in Ha.
  split; [ easy | ]; destruct Ha as (_, Ha); cbn in Ha.
  rewrite List.seq_nth; [ | easy ].
  split. {
    intros k Hk.
    rewrite List.seq_nth; [ | flia Ha Hk ].
    apply Bool.not_true_iff_false; intros Hak.
    apply Nat.eqb_eq in Hak.
    rewrite Hak in Hk; flia Hk.
  }
  split; [ now apply Nat.eqb_eq | ].
  apply eq_nth_find_all_loop_nil.
  intros j Hj.
  apply Bool.not_true_iff_false; intros Haj.
  apply Nat.eqb_eq in Haj; subst j.
  rewrite List_skipn_seq in Hj; [ | flia Ha ].
  cbn in Hj.
  apply List.in_seq in Hj; flia Hj.
}
rewrite Hjll.
rewrite <- loc_length_loc_bl_sens_list.
unfold "≥".
etransitivity; [ | apply List_fold_right_max_ge ].
apply Nat.le_max_l.
Qed.

(* "Obviously, bs(f) ≥ s(f)" *)

Theorem bs_ge_s : ∀ n f, block_sensitivity n f ≥ sensitivity n f.
Proof.
intros.
unfold block_sensitivity, sensitivity.
unfold "≥".
remember (List.seq 0 (2 ^ n)) as l; clear Heql.
induction l as [| a]; [ easy | cbn ].
etransitivity. {
  apply Nat.max_le_compat_l.
  apply IHl.
} {
  apply Nat.max_le_compat_r.
  apply x_bs_ge_s.
}
Qed.

(* "Given a n×n matrix A, a principal submatrix of A is obtained by deleting
    the same set of rows and columns from A.

   Theorem 2.1. (Cauchy’s Interlace Theorem) Let A be a symmetric n×n matrix,
      and B be a m×m principal submatrix of A, for some m < n. If the
      eigenvalues of A are λ₁ ≥ λ₂ ≥ … ≥ λ_n, and the eigenvalues of B
      are µ₁ ≥ µ₂ ≥ … ≥ µ_m, then for all 1 ≤ i ≤ m,
              λ_i ≥ µ_i ≥ λ_{i+n-m}."
*)

(* testing... *)

(*
Compute (Δ full_cube, Nat.sqrt 3).
Compute (2 ^ (3 - 1) + 1).

Compute (List.length (sg_edges full_cube)).
Compute (vdeg (edges cube_vert) 0).

Compute (edges [1; 2; 4; 7]).
Compute (List.length (edges [1; 2; 4; 7])).
Compute (2 ^ (3 - 1) + 1).

Compute (vΔ [0; 1; 4; 5; 7]).
Compute (edges [0; 1; 4; 5; 7]).

Compute (edges [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (vΔ [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (2 ^ (4 - 1) + 1).
Compute (Nat.sqrt 4).
Compute (let n := 4 in 2 ^ (n - 1) + 1).
Compute (List.map (λ i, vΔ [0; 3; 5; 6; 9; 10; 12; 15; i]) (List.seq 0 16)).
Compute (let n := 4 in Nat.sqrt n).
Compute (let n := 3 in 2 ^ (n - 1) + 1).
Compute (List.map (λ i, (i, vΔ [0; 3; 5; 6; i])) (List.seq 0 8)).
Compute (let n := 3 in Nat.sqrt n).

Compute (edges [0; 3; 5; 6]).
Compute (edges [0; 3; 5; 6; 2]).
Compute (vdeg (edges [0; 3; 5; 6; 1])) 1.

Compute (Nat.sqrt 5).
Compute (let n := 5 in 2 ^ (n - 1) + 1).
Compute (edges [0; 3; 5; 6; 9; 10; 12; 15; 17; 18; 20; 23; 24; 27; 29; 30]).
Compute
   (List.map
     (λ i, vΔ [0; 3; 5; 6; 9; 10; 12; 15; 17; 18; 20; 23; 24; 27; 29; 30; i])
     (List.seq 0 32)).

Compute (Nat.sqrt 4).
Compute (let n := 4 in 2 ^ (n - 1) + 1). (* 9 *)
Compute (List.length [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (edges [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (List.map (λ i, vΔ [0; 3; 5; 6; 9; 10; 12; 15; i]) (List.seq 0 16)).

Compute (vΔ [0; 1; 6; 7; 10; 11; 12; 13]).
Compute (List.map (λ i, vΔ [0; 1; 6; 7; 10; 11; 12; 13; i]) (List.seq 0 16)).

Compute (Nat.sqrt 2).
Compute (let n := 2 in 2 ^ (n - 1) + 1).
Compute (List.length [0; 3]).

Compute (Nat.sqrt 3).
Compute (let n := 3 in 2 ^ (n - 1) + 1).
Compute (List.length [0; 3; 5; 6]).
Compute (edges [0; 3; 5; 6]).
Compute (List.map (λ i, vΔ [0; 3; 5; 6; i]) (List.seq 0 8)).
Compute (List.map (λ i, vΔ [0; 1; 2; 4; i]) (List.seq 0 8)).

Compute (List.map (λ i, vΔ [0; 1; 6; 7; i]) (List.seq 0 8)).
Compute (vΔ [0; 1; 6; 7]).
Compute (edges [0; 1; 2; 4]).
*)

(* The theorem *)

(* to be completed
Theorem sensitivity_th : ∀ sg n,
  number_of_vertices sg = 2 ^ (n - 1) + 1
  → Δ sg ≥ Nat.sqrt n.
Proof.
...
*)
