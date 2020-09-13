(* Sensitivity Theorem proved by Hao Huang.
   https://arxiv.org/pdf/1907.00847.pdf
   https://eccc.weizmann.ac.il/report/2020/002/?fbclid=IwAR19mpxfIuoSaWq3HO8MdV8i8x_xlvwMKHjfElzBUK0GditlyaLeJiC8gJY *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Init.Nat.
Require Import Misc.

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

Compute (let n := 3 in map (λ a, (a, filter (are_adjacent_vertices a) (seq 0 (2^n)))) (seq 0 (2^n))).

(* subgraph of the n-dimensional cube graph *)

Record subgraph := mksg { sg_vert : list nat }.

Definition edges vl :=
  fold_right
    (λ a l,
     fold_right
       (λ b l,
        if lt_dec a b then
          if are_adjacent_vertices a b then (a, b) :: l else l
        else l) l vl)
    [] (nodup Nat.eq_dec vl).

Compute (edges [1; 2; 7; 4]).

Definition sg_edges sg := edges (sg_vert sg).

(* Example *)

Definition cube_vert := seq 0 (2 ^ 3).
Definition full_cube := mksg cube_vert.

(* edges and vertices count *)

Definition number_of_edges sg := length (sg_edges sg).
Definition number_of_vertices sg := length (sg_vert sg).
Compute (number_of_edges full_cube).
Compute (number_of_vertices full_cube).

(* degree of a vertex = number of edges adjacents to the vertex *)

Definition vdeg el v :=
  count_occ Bool.bool_dec (map (λ '(a, b), Nat.eqb a v) el) true +
  count_occ Bool.bool_dec (map (λ '(a, b), Nat.eqb v b) el) true.

Definition deg sg v := vdeg (sg_edges sg) v.

(* Δ : maximum degree of a subgraph *)

Definition vΔ vl :=
  let el := edges vl in
  fold_left (λ m v, max m (vdeg el v)) vl 0.

Compute (vΔ [0; 1; 0]).
Compute (edges [0; 1; 0]).

Compute (vΔ [0; 1; 2; 4; 0]).
Compute (vdeg (edges [0; 1; 2; 4]) 0).

Definition Δ sg := vΔ (sg_vert sg).

(* sensitivity *)

Definition Nat_togglebit x i :=
  if Nat.testbit x i then Nat.clearbit x i else Nat.setbit x i.

Definition flip x S := fold_right Nat_togglebit x S.

Notation "x ^^ S" := (flip x S) (at level 30).

Definition loc_sens_list n (f : nat → bool) x :=
  filter (λ i, negb (Bool.eqb (f x) (f (x ^^ [i])))) (seq 0 n).

Definition local_sensitivity (n : nat) (f : nat → bool) (x : nat) :=
  length (loc_sens_list n f x).

Definition sensitivity n f :=
  fold_right max 0 (map (local_sensitivity n f) (seq 0 (2 ^ n))).

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
  map (@rev nat) (count_in_radix n (repeat 0 n) (n ^ n)).

Compute (count_upto_n_to_n 3).

Definition cons_nth {A} i (a : A) ll :=
  firstn i ll ++  (a :: nth i ll []) :: skipn (i + 1) ll.

Definition is_nil {A} (l : list A) :=
  match l with
  | [] => true
  | _ => false
  end.

(* conversion natural into radix n as a list of digits; i must be
   less than n^n; always return n digits; e.g. radix 10 37 =
   7; 3; 0 ... (eight 0s) *)

Fixpoint to_radix_loop it n i :=
  match it with
  | 0 => []
  | S it' => i mod n :: to_radix_loop it' n (i / n)
  end.

Definition to_radix n i := to_radix_loop n n i.

(**)

Fixpoint nth_find_all_loop {A} (f : A → bool) l i :=
  match l with
  | [] => []
  | a :: l' =>
      if f a then i :: nth_find_all_loop f l' (i + 1)
      else nth_find_all_loop f l' (i + 1)
  end.

Definition nth_find_all A f l := @nth_find_all_loop A f l 0.
Arguments nth_find_all [A]%type_scope _%function_scope _%list_scope.

(**)

Fixpoint nth_find_loop {A} (f : A → bool) l i :=
  match l with
  | [] => i
  | a :: l' => if f a then i else nth_find_loop f l' (i + 1)
  end.

Definition nth_find A f l := @nth_find_loop A f l 0.
Arguments nth_find [A]%type_scope _%function_scope _%list_scope.

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
  map (λ j, nth_find_all (Nat.eqb j) l) (seq 0 (length l)).

Definition dispatch n i := dispatch_list (rev (to_radix n i)).

Definition pre_partitions n := map (dispatch n) (seq 0 (n ^ n)).

Compute (let l := [3; 2; 1; 1] in dispatch_list l).

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

Fixpoint list_list_nat_le lla llb :=
  match (lla, llb) with
  | ([], _) => true
  | (_, []) => false
  | (la :: lla', lb :: llb') =>
      if list_nat_le la lb then
        if list_nat_le lb la then list_list_nat_le lla' llb'
        else true
      else false
  end.

Definition all_partitions n :=
  bsort list_list_nat_le
    (nodup (list_eq_dec (list_eq_dec Nat.eq_dec))
       (map (bsort list_nat_le)
          (map (filter (λ s, negb (is_nil s))) (pre_partitions n)))).

Compute (map (bsort list_nat_le) (pre_partitions 4)).
Compute (nodup (list_eq_dec (list_eq_dec Nat.eq_dec)) (map (bsort list_nat_le) (pre_partitions 4))).
Compute (all_partitions 4).

(* Local block sensitivity *)

Definition loc_bl_sens_list Bl f x :=
  filter (λ Bi, negb (Bool.eqb (f x) (f (x ^^ Bi)))) Bl.

Definition local_block_sensitivity n f x :=
  fold_right max 0
    (map (λ Bl, length (loc_bl_sens_list Bl f x)) (pre_partitions n)).

Definition block_sensitivity n f :=
  fold_right max 0 (map (local_block_sensitivity n f) (seq 0 (2 ^ n))).

(* Proving Theorem: bs(f) ≥ s(f) *)

Require Import Sorting.

(* property of partitions of {0,1,..,n-1} returned by pre_partitions *)

Definition is_pre_partition ll :=
  (∀ l, l ∈ ll → ∀ i, i ∈ l → i < length ll) ∧
  (∀ i, i < length ll → ∃ l, l ∈ ll ∧ i ∈ l) ∧
  NoDup (concat ll) ∧
  (∀ l, l ∈ ll → Sorted lt l).

(* locate: inverse of "dispatch" *)

Fixpoint nat_in_list i l :=
  match l with
  | [] => false
  | j :: l' => if Nat.eq_dec i j then true else nat_in_list i l'
  end.

Definition locate_list ll :=
  map (λ i, nth_find (nat_in_list i) ll) (seq 0 (length ll)).

Definition locate ll :=
  fold_left (λ a i, a * length ll + i) (locate_list ll) 0.

Compute (locate [[2]; []; [0; 1]]).
Compute (dispatch 3 24).
Compute (locate [[]; [0; 2]; [1]]).
Compute (dispatch 3 16).
Compute (dispatch 4 23).
Compute (locate [[0]; [1; 2]; []; [3]]).

Theorem cons_nth_length : ∀ {A} i ll (v : A),
  i < length ll → length (cons_nth i v ll) = length ll.
Proof.
intros * Hi.
revert i v Hi.
induction ll as [| l]; intros; cbn in Hi; [ flia Hi | ].
destruct i; [ easy | cbn ].
apply Nat.succ_lt_mono in Hi.
f_equal.
now apply IHll.
Qed.

Definition sub_list {A} (l : list A) start len :=
  firstn len (skipn start l).

Theorem seq_app_last : ∀ start len,
  seq start len ++ [start + len] = start :: seq (start + 1) len.
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

Compute (let ll := [[1; 2]; []; [0]] in locate_list ll).
Compute (let l := [2; 0; 0] in dispatch_list l).

Compute (locate_list (dispatch_list [2; 0; 0])).
Compute (locate_list (dispatch_list [1; 2; 0])).

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

Theorem not_in_nth_find_all_loop : ∀ A f (l : list A) i j,
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
  → nth (b - k) l 0 = i.
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

Theorem in_nth_find_all_loop_eqb_if : ∀ a l d,
  a < length l
  → a + d ∈ nth_find_all_loop (Nat.eqb (nth a l 0)) l d.
Proof.
intros * Hal.
revert d a Hal.
induction l as [| b]; intros; [ easy | ].
cbn.
destruct a; [ now rewrite Nat.eqb_refl; left | ].
remember (nth a l 0 =? b) as c eqn:Hc; symmetry in Hc.
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
  b ∈ flat_map (λ i, nth_find_all_loop (Nat.eqb i) l k) (seq j len)
  → k ≤ b
  → j ≤ nth (b - k) l 0 < j + len.
Proof.
intros * Hbf Hkb.
apply in_flat_map in Hbf.
destruct Hbf as (i & Hi & Hik).
apply in_nth_find_all_loop_eqb in Hik; [ | easy ].
rewrite Hik.
now apply in_seq in Hi.
Qed.

Theorem flat_map_nth_find_all_loop_cons : ∀ a l k i len,
  a < i ∨ i + len ≤ a
  → flat_map (λ j, nth_find_all_loop (Nat.eqb j) (a :: l) k) (seq i len) =
    flat_map (λ j, nth_find_all_loop (Nat.eqb j) l (k + 1)) (seq i len).
Proof.
intros * Hai.
do 2 rewrite flat_map_concat_map; f_equal; cbn.
apply map_ext_in_iff.
intros b Hb.
apply in_seq in Hb.
remember (b =? a) as c eqn:Hc; symmetry in Hc.
destruct c; [ | easy ].
apply Nat.eqb_eq in Hc; subst b.
flia Hai Hb.
Qed.

Theorem dispatch_list_length : ∀ l, length (dispatch_list l) = length l.
Proof.
intros.
unfold dispatch_list.
now rewrite map_length, seq_length.
Qed.

Theorem dispatch_list_is_pre_partition : ∀ l,
  (∀ a, a ∈ l → a < length l)
  → is_pre_partition (dispatch_list l).
Proof.
intros * Hl.
split. {
  intros l1 Hl1 i Hi.
  unfold dispatch_list in Hl1.
  move i at top.
  move l1 before l.
  apply in_map_iff in Hl1.
  destruct Hl1 as (b & Hb & Hbs).
  subst l1; move b before i.
  unfold nth_find_all in Hi.
  assert
    (H : ∀ A f (l : list A) i j,
     j < length (nth_find_all_loop f l i)
     → nth j (nth_find_all_loop f l i) 0 < i + length l). {
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
  apply in_split in Hi.
  destruct Hi as (l1 & l2 & Hi).
  specialize (H nat (Nat.eqb b) l 0 (length l1)) as H1.
  rewrite Hi in H1.
  rewrite app_nth2 in H1; [ | now unfold "≥" ].
  rewrite Nat.sub_diag in H1; cbn in H1.
  rewrite dispatch_list_length.
  apply H1.
  rewrite app_length; cbn; flia.
}
split. {
  intros i Hi.
  rewrite dispatch_list_length in Hi.
  exists (nth (nth i l 0) (dispatch_list l) []).
  split. {
    apply nth_In.
    unfold dispatch_list.
    rewrite map_length.
    rewrite seq_length.
    apply Hl.
    now apply nth_In.
  }
  unfold dispatch_list.
  rewrite List_map_nth_in with (a := 0). 2: {
    rewrite seq_length.
    apply Hl.
    now apply nth_In.
  }
  rewrite seq_nth. 2: {
    apply Hl.
    now apply nth_In.
  }
  cbn.
  unfold nth_find_all.
  assert (H : ∀ d, i + d ∈ nth_find_all_loop (Nat.eqb (nth i l 0)) l d). {
    revert i Hi.
    clear Hl.
    induction l as [| a]; intros; [ easy | ].
    destruct i; [ now cbn; rewrite Nat.eqb_refl; left | cbn ].
    enough (S i + d ∈ nth_find_all_loop (Nat.eqb (nth i l 0)) l (d + 1)). {
      destruct (nth i l 0 =? a); [ now right | easy ].
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
  rewrite <- flat_map_concat_map.
  assert (Hnd : ∀ l i j, NoDup (nth_find_all_loop (Nat.eqb i) l j)). {
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
      NoDup
        (flat_map (λ j, nth_find_all_loop (Nat.eqb j) l k)
                  (seq i len))). {
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
    rewrite flat_map_concat_map.
    replace len with (a - i + (len - (a - i))) by flia Hila.
    rewrite seq_app.
    rewrite map_app.
    rewrite concat_app.
    do 2 rewrite <- flat_map_concat_map.
    rewrite flat_map_nth_find_all_loop_cons; [ | right; flia Hai ].
    rewrite (Nat.add_comm i), Nat.sub_add; [ | easy ].
    replace (len - (a - i)) with (1 + (len - (a - i) - 1)) by flia Hai Hila.
    rewrite seq_app.
    do 2 rewrite flat_map_concat_map.
    rewrite map_app, concat_app.
    unfold seq at 2, map at 2, concat at 2.
    rewrite app_nil_r.
    remember (nth_find_all_loop (Nat.eqb a) _ _) as x; cbn in Heqx; subst x.
    rewrite Nat.eqb_refl.
    do 2 rewrite <- flat_map_concat_map.
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
      apply in_flat_map in Hb1.
      destruct Hb1 as (j & Hj & Hjb).
      revert Hjb.
      apply not_in_nth_find_all_loop; flia.
    }
    apply in_app_iff in Hb2.
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
    apply in_flat_map in Hb1.
    destruct Hb1 as (x & Hx & Hxl).
    revert Hxl.
    now apply not_in_nth_find_all_loop.
  }
  apply H.
} {
  intros l1 Hl1.
  unfold dispatch_list in Hl1.
  apply in_map_iff in Hl1.
  destruct Hl1 as (i & Hill & Hil); subst l1.
  apply in_seq in Hil; destruct Hil as (_, Hil); cbn in Hil.
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
  nth_find_loop f (map g l) i =
  nth_find_loop (λ a, f (g a)) l i.
Proof.
intros.
revert f g i.
induction l as [| a]; intros; [ easy | cbn ].
destruct (f (g a)); [ easy | ].
apply IHl.
Qed.

Theorem nth_find_all_loop_map : ∀ A B (f : B → bool) g i (l : list A),
    nth_find_all_loop f (map g l) i = nth_find_all_loop (λ a, f (g a)) l i.
Proof.
intros.
revert i.
induction l as [| a]; intros; [ easy | cbn ].
destruct (f (g a)); [ now rewrite IHl | ].
apply IHl.
Qed.

Theorem nth_find_all_map : ∀ A B (f : B → bool) g (l : list A),
    nth_find_all f (map g l) = nth_find_all (λ a, f (g a)) l.
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
  (∀ a : nat, a ∈ l → a < length l)
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
rewrite map_length, seq_length.
replace l with (map (λ i, nth i l 0) (seq 0 (length l))) at 2. 2: {
  clear.
  induction l as [| a]; [ easy | ].
  f_equal; cbn; f_equal.
  rewrite <- seq_shift.
  now rewrite map_map.
}
apply map_ext_in_iff.
intros a Ha.
unfold nth_find.
unfold nth_find_all.
replace (length l) with (nth a l 0 + 1 + (length l - (nth a l 0 + 1))). 2: {
  apply in_seq in Ha; cbn in Ha.
  destruct Ha as (_, Ha).
  specialize (Hl (nth a l 0) (nth_In l 0 Ha)) as H1.
  flia H1.
}
do 2 rewrite seq_app.
do 2 rewrite Nat.add_0_l.
replace (seq _ 1) with [nth a l 0] by easy.
do 2 rewrite map_app.
rewrite <- app_assoc.
rewrite nth_find_loop_app_2. 2: {
  intros l1 Hl1.
  apply nat_in_list_false_iff.
  intros j Hj Haj; subst j.
  apply in_map_iff in Hl1.
  destruct Hl1 as (k & Hkl & Hka); subst l1.
  apply in_seq in Hka; destruct Hka as (_, Hka); cbn in Hka.
  apply in_nth_find_all_loop_eqb in Hj; [ | flia ].
  rewrite Nat.sub_0_r in Hj; subst k.
  flia Hka.
}
rewrite map_length, seq_length, Nat.add_0_l; cbn.
remember (nat_in_list a _) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
specialize ((proj1 (nat_in_list_false_iff _ _)) Hb a) as H1.
exfalso; apply H1; clear H1; [ | easy ].
apply in_seq in Ha; destruct Ha as (_, Ha); cbn in Ha.
specialize (in_nth_find_all_loop_eqb_if l 0 Ha) as H1.
now rewrite Nat.add_0_r in H1.
Qed.

Theorem to_radix_loop_length : ∀ it n i, length (to_radix_loop it n i) = it.
Proof.
intros.
revert n i.
induction it; intros; [ easy | cbn ].
now rewrite IHit.
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
  → fold_left (λ a j : nat, a * n + j) (rev (to_radix n i)) 0 = i.
Proof.
intros * Hin.
assert
  (H : ∀ it n i,
   i < n ^ it
   → fold_left (λ a j, a * n + j) (rev (to_radix_loop it n i)) 0 = i). {
  clear.
  intros * Hin.
  revert n i Hin.
  induction it; intros; [ now apply Nat.lt_1_r in Hin; subst i | ].
  cbn.
  rewrite fold_left_app; cbn.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
  specialize (Nat.div_mod i n Hnz) as H1.
  rewrite H1 at 3; f_equal.
  rewrite Nat.mul_comm; f_equal.
  apply IHit.
  apply (Nat.mul_lt_mono_pos_r (n ^ 1)); [ rewrite Nat.pow_1_r; flia Hnz | ].
  rewrite <- Nat.pow_add_r, Nat.add_1_r, Nat.pow_1_r.
  apply (le_lt_trans _ i); [ | easy ].
  rewrite Nat.mul_comm.
  now apply Nat.mul_div_le.
}
now apply H.
Qed.

Compute (let n := 4 in let i := 255 in locate (dispatch n i)).

Theorem locate_dispatch : ∀ n i, i < n ^ n → locate (dispatch n i) = i.
Proof.
intros * Hin.
unfold locate, dispatch.
rewrite locate_dispatch_list. 2: {
  intros a Ha.
  apply in_rev in Ha.
  rewrite rev_length.
  unfold to_radix in Ha |-*.
  rewrite to_radix_loop_length.
  apply in_to_radix_loop in Ha; [ easy | ].
  now intros H; subst n.
}
rewrite dispatch_list_length.
rewrite rev_length.
assert
  (H : ∀ i b l,
   fold_left (λ a j, a * length (to_radix n i) + j) l b =
   fold_left (λ a j, a * n + j) l b). {
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
Compute (let n := 3 in let j := 1 in let k := 2 in map (λ i, (i, dispatch n i))
(filter (pre_partition_in n j k) (seq 0 (n ^ n)))).

Theorem nth_find_all_loop_app : ∀ A f (l1 l2 : list A) i,
  nth_find_all_loop f (l1 ++ l2) i =
  nth_find_all_loop f l1 i ++ nth_find_all_loop f l2 (i + length l1).
Proof.
intros.
revert i l2.
induction l1 as [| a1]; intros. {
  now cbn; rewrite Nat.add_0_r.
}
cbn.
destruct (f a1). {
  cbn; f_equal.
  rewrite <- (Nat.add_succ_comm _ (length l1)).
  rewrite Nat.add_1_r.
  apply IHl1.
}
rewrite <- (Nat.add_succ_comm _ (length l1)).
rewrite Nat.add_1_r.
apply IHl1.
Qed.

Theorem fold_left_mul_add_mod : ∀ n j l,
  fold_left (λ a i, a * n + i) l j mod n = last (j :: l) 0 mod n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
revert n j Hnz.
induction l as [| b]; intros; [ easy | ].
cbn - [ last ].
remember (b :: l) as l'; cbn; subst l'.
transitivity (fold_left (λ a i : nat, a * n + i) l b mod n). 2: {
  now apply IHl.
}
clear - Hnz.
revert b n j Hnz.
induction l as [| a]; intros. {
  now apply Nat_mod_add_l_mul_r.
}
cbn.
rewrite IHl; [ | easy ].
now rewrite IHl.
Qed.

Theorem fold_left_mul_add_div : ∀ n j l,
  (∀ i, i ∈ l → i < n)
  → l ≠ []
  → fold_left (λ a i, a * n + i) l j / n =
     fold_left (λ a i, a * n + i) (removelast l) j.
Proof.
intros * Hin Hln.
destruct l as [| b]; [ easy | clear Hln ].
cbn - [ removelast ].
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
cbn - [ removelast ].
remember (a :: l) as l'; cbn; subst l'.
rewrite IHl; [ easy | ].
intros i Hl.
now apply Hin; right.
Qed.

Theorem locate_list_length : ∀ ll, length (locate_list ll) = length ll.
Proof.
intros.
unfold locate_list.
now rewrite map_length, seq_length.
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

Theorem eq_nth_find_all_loop_cons : ∀ A f j (d : A) l l' i,
  nth_find_all_loop f l i = j :: l' ↔
    i ≤ j < i + length l ∧
    (∀ k, i + k < j → f (nth k l d) = false) ∧
    f (nth (j - i) l d) = true ∧
    nth_find_all_loop f (skipn (j + 1 - i) l) (j + 1) = l'.
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
    now rewrite skipn_cons.
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
  rewrite skipn_cons.
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
    j < length l ∧
    (∀ k : nat, k < j → f (nth k l d) = false) ∧
    f (nth j l d) = true ∧
    nth_find_all_loop f (skipn (j + 1) l) (j + 1) = l'.
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

Theorem in_nth_nth_find_loop : ∀ ll i d,
  (∀ i, i < length ll → ∃ l : list nat, l ∈ ll ∧ i ∈ l)
  → i < length ll
  → i ∈ nth (nth_find_loop (nat_in_list i) ll d - d) ll [].
Proof.
intros * Huni Hi.
specialize (Huni _ Hi).
destruct Huni as (l & Hlll & Hil).
clear - Hlll Hil.
revert d l Hlll Hil.
induction ll as [| l1]; intros; [ easy | ].
cbn - [ nth ].
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
now rewrite Nat.sub_succ, Nat.sub_0_r in IHll.
Qed.

Theorem in_nth_nth_find : ∀ ll j,
  (∀ i, i < length ll → ∃ l : list nat, l ∈ ll ∧ i ∈ l)
  → j < length ll
  → j ∈ nth (nth_find (nat_in_list j) ll) ll [].
Proof.
intros * Huni Hi.
specialize (in_nth_nth_find_loop ll 0 Huni Hi) as H1.
now rewrite Nat.sub_0_r in H1.
Qed.

Theorem NoDup_concat_in_in : ∀ A ll (a : A) b c,
  NoDup (concat ll)
  → a ∈ nth b ll []
  → a ∈ nth c ll []
  → b = c.
Proof.
intros * Hnd Hb Hc.
revert b c Hb Hc.
induction ll as [| l]; intros. {
  cbn in Hb.
  now rewrite match_id in Hb.
}
cbn in Hnd.
apply NoDup_app_iff in Hnd.
destruct Hnd as (Hnd & Hndc & Hll).
specialize (IHll Hndc).
cbn in Hb, Hc.
destruct b. {
  destruct c; [ easy | exfalso ].
  specialize (Hll _ Hb) as H1.
  apply H1; clear H1.
  clear - Hc.
  revert c a Hc.
  induction ll as [| l]; intros. {
    rewrite nth_overflow in Hc; [ easy | cbn; flia ].
  }
  cbn in Hc; cbn.
  destruct c; [ now apply in_or_app; left | ].
  apply in_or_app; right.
  now apply (IHll c).
}
destruct c. {
  exfalso.
  specialize (Hll _ Hc) as H1.
  apply H1; clear H1.
  clear - Hb.
  revert b Hb.
  induction ll as [| l]; intros. {
    rewrite nth_overflow in Hb; [ easy | cbn; flia ].
  }
  cbn in Hb; cbn.
  destruct b; [ now apply in_or_app; left | ].
  apply in_or_app; right.
  now apply (IHll b).
}
f_equal.
now apply IHll.
Qed.

Theorem eq_nth_find_all_loop_iff : ∀ A f (d : A) l l1 i,
  nth_find_all_loop f l i = l1 ↔
    match l1 with
    | [] => (∀ j, j ∈ l → f j = false)
    | j :: l2 =>
        i ≤ j < i + length l ∧
        (∀ k, i + k < j → f (nth k l d) = false) ∧
        f (nth (j - i) l d) = true ∧
        nth_find_all_loop f (skipn (j + 1 - i) l) (j + 1) = l2
end.
Proof.
intros.
destruct l1 as [| b]; [ apply eq_nth_find_all_loop_nil | ].
apply eq_nth_find_all_loop_cons.
Qed.

Theorem length_loc_loc_bl_sens_list : ∀ n f x,
  length (loc_sens_list n f x) =
  length (loc_bl_sens_list (map (λ i, [i]) (seq 0 n)) f x).
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
  length (loc_bl_sens_list (map (λ i, [i]) (seq 0 n)) f x).
Proof.
intros.
apply length_loc_loc_bl_sens_list.
Qed.

Theorem map_loc_sens : ∀ n f l,
  map (local_sensitivity n f) l =
  map (λ x, length (loc_bl_sens_list (map (λ i, [i]) (seq 0 n)) f x)) l.
Proof.
intros.
induction l; cbn; [ easy | ].
rewrite <- loc_length_loc_bl_sens_list; f_equal.
apply IHl.
Qed.

Theorem Nat_pow_from_sum : ∀ a n, a * n ≠ 0 →
  n ^ a = (n - 1) * (Σ (i = 0, a - 1), n ^ i) + 1.
Proof.
intros * Hanz.
destruct a; [ easy | ].
replace (S a - 1) with a by flia.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  now rewrite Hnz, Nat.mul_comm in Hanz.
}
clear Hanz.
revert n Hnz.
induction a; intros; [ cbn; flia Hnz | ].
rewrite summation_split_last; [ | flia | flia ].
replace (S a - 1) with a by flia.
rewrite Nat.mul_add_distr_l, Nat.add_shuffle0.
rewrite <- IHa; [ | easy ].
replace (n ^ S a) with (1 * n ^ S a) at 1 by flia.
rewrite <- Nat.mul_add_distr_r.
now replace (1 + (n - 1)) with n by flia Hnz.
Qed.

Theorem fold_left_horner_eval_sum : ∀ k n a x,
  fold_left (λ acc i : nat, acc * x + a (n + k - i))
    (seq (S k) n) (Σ (i = 0, k), a (n + i) * x ^ i) =
  fold_left (λ c i : nat, c + a (n + k - i) * x ^ (n + k - i))
    (seq (S k) n) (Σ (i = 0, k), a (n + i) * x ^ (n + i)).
Proof.
intros.
revert k.
induction n; intros; [ easy | ].
specialize (IHn (S k)).
replace (n + S k) with (S n + k) in IHn by flia.
replace (seq (S k) (S n)) with (S k :: seq (S (S k)) n) by easy.
cbn - [ "-" "+" ].
replace (S n + k - S k) with n by flia.
rewrite summation_split_first in IHn; [ | flia ].
rewrite Nat.pow_0_r, Nat.add_0_r, Nat.mul_1_r in IHn.
rewrite (Nat.add_comm (a n)) in IHn.
rewrite summation_succ_succ in IHn.
rewrite summation_eq_compat with (h := λ i, a (S n + i) * x ^ i * x)
  in IHn. 2: {
  intros i Hi.
  rewrite Nat.add_succ_comm.
  now cbn; rewrite Nat.mul_assoc, Nat.mul_shuffle0.
}
rewrite <- mul_summation_distr_r in IHn.
symmetry in IHn; symmetry.
rewrite summation_split_first in IHn; [ | flia ].
rewrite Nat.add_0_r in IHn.
rewrite (Nat.add_comm (a n * x ^ n)) in IHn.
rewrite summation_succ_succ in IHn.
rewrite summation_eq_compat with (h := λ i, a (S n + i) * x ^ (S n + i))
  in IHn. 2: {
  intros i Hi.
  now rewrite Nat.add_succ_comm.
}
apply IHn.
Qed.

Theorem horner_is_eval_polyn : ∀ n a x,
  fold_left (λ acc i, acc * x + a (n - i)) (seq 0 (S n)) 0 =
  Σ (i = 0, n), a i * x ^ i.
Proof.
intros.
rewrite summation_rtl.
rewrite Nat.add_0_r; cbn.
rewrite Nat.sub_0_r.
specialize (fold_left_horner_eval_sum 0 n a x) as H1.
cbn in H1.
now rewrite Nat.add_0_r, Nat.mul_1_r in H1.
Qed.

Theorem horner_is_eval_polyn2 : ∀ n a x,
  fold_left (λ acc i, acc * x + a i) (seq 0 (S n)) 0 =
  Σ (i = 0, n), a (n - i) * x ^ i.
Proof.
intros.
specialize (horner_is_eval_polyn n (λ i, a (n - i)) x) as H1.
cbn - [ "-" fold_left seq ] in H1.
rewrite <- H1.
apply List_fold_left_ext_in.
intros b c Hb; f_equal; f_equal.
apply in_seq in Hb.
flia Hb.
Qed.

Theorem to_radix_fold_left : ∀ n,
  to_radix n (fold_left (λ a i, a * n + i) (seq 0 n) 0) = rev (seq 0 n).
Proof.
intros.
assert
  (Hft : ∀ it n l d,
   n = length l
   → n ≤ it
   → (∀ i, i ∈ l → i < n + d)
   → firstn n
        (to_radix_loop it (n + d) (fold_left (λ a j, a * (n + d) + j) l 0)) =
        rev l). {
  clear.
  intros * Hnl Hit Hil.
  revert n d l Hnl Hit Hil.
  induction it; intros. {
    apply Nat.le_0_r in Hit; subst n.
    apply length_zero_iff_nil in Hit.
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
    now apply length_zero_iff_nil in Hnl; subst l.
  }
  cbn - [ last "mod" ].
  remember (rev l) as rl eqn:Hrl; symmetry in Hrl.
  destruct rl as [| a]. {
    now apply List_eq_rev_nil in Hrl; subst l.
  }
  assert (Hlr : l = rev (a :: rl)). {
    rewrite <- Hrl; symmetry; apply rev_involutive.
  }
  rewrite Hlr.
  cbn - [ last "mod" ].
  rewrite app_comm_cons, List_last_app.
  rewrite Nat.mod_small. 2: {
    apply Hil; rewrite Hlr; cbn.
    now apply in_or_app; right; left.
  }
  f_equal.
  rewrite removelast_app; [ | easy ].
  rewrite app_nil_r.
  replace rl with (tl (rev l)) by now rewrite Hrl.
  cbn in Hil.
  replace (S (n + d)) with (n + S d) in Hil |-* by flia.
  apply Nat.succ_le_mono in Hit.
  rewrite IHit; [ apply rev_involutive | | easy | ]. 2: {
    intros i Hi.
    apply Hil.
    apply in_rev in Hi.
    apply in_rev.
    remember (rev l) as l'.
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
  rewrite rev_length.
  apply Nat.succ_inj.
  rewrite Hnl, Hrl; cbn.
  rewrite Hlr.
  now rewrite rev_length.
}
specialize (Hft n n (seq 0 n) 0) as H1.
rewrite seq_length in H1.
specialize (H1 eq_refl (le_refl _)).
rewrite Nat.add_0_r in H1.
assert (H : ∀ i, i ∈ seq 0 n → i < n). {
  now intros i Hi; apply in_seq in Hi.
}
specialize (H1 H); clear H.
unfold to_radix.
remember (to_radix_loop _ _ _) as l.
rewrite <- H1; symmetry.
replace n with (length l). 2: {
  rewrite Heql.
  apply to_radix_loop_length.
}
apply firstn_all.
Qed.

Theorem fold_left_mul_seq_lt : ∀ n,
  fold_left (λ a i, a * n + i) (seq 0 n) 0 < n ^ n.
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
rewrite mul_summation_distr_l.
cbn - [ seq ].
specialize (horner_is_eval_polyn (n - 1)) as H2.
specialize (H2 (λ i, n - 1 - i) n).
cbn - [ "-" fold_left seq ] in H2.
rewrite List_fold_left_ext_in with (g := λ acc i, acc * n + i) in H2. 2: {
  intros acc i Hacc.
  apply in_seq in Hacc.
  flia Hacc.
}
replace (S (n - 1)) with n in H2 at 1 by flia Hnz.
replace (S (n - 1)) with (S (n - 1) - 0) by flia Hnz.
rewrite H2.
apply summation_le_compat.
intros i Hi.
apply Nat.mul_le_mono_r; flia.
Qed.

Theorem x_bs_ge_s : ∀ n f x,
  local_block_sensitivity n f x ≥ local_sensitivity n f x.
Proof.
intros.
rewrite loc_length_loc_bl_sens_list.
unfold local_block_sensitivity.
remember (pre_partitions n) as ll eqn:Hll.
remember (locate (dispatch_list (seq 0 n))) as j eqn:Hj.
specialize (@nth_split _ j ll []) as H1.
assert (H : j < length ll). {
  rewrite Hj, Hll.
  unfold pre_partitions.
  rewrite map_length, seq_length.
  unfold locate.
  rewrite locate_dispatch_list. 2: {
    intros a Ha.
    rewrite seq_length.
    now apply in_seq in Ha.
  }
  rewrite dispatch_list_length, seq_length.
  apply fold_left_mul_seq_lt.
}
specialize (H1 H); clear H.
destruct H1 as (l1 & l2 & Hll12 & Hl1).
unfold locate in Hj.
rewrite locate_dispatch_list in Hj. 2: {
  intros a Ha.
  apply in_seq in Ha.
  now rewrite seq_length.
}
rewrite dispatch_list_length in Hj.
rewrite seq_length in Hj.
rewrite Hll12.
rewrite map_app.
rewrite fold_right_app; cbn.
assert (Hjll : nth j ll [] = map (λ i, [i]) (seq 0 n)). {
  rewrite Hll.
  unfold pre_partitions.
  assert (Hjnn : j < n ^ n). {
    rewrite Hj.
    apply fold_left_mul_seq_lt.
  }
  rewrite (List_map_nth_in _ 0) by now rewrite seq_length.
  rewrite seq_nth; [ cbn | easy ].
  unfold dispatch.
  rewrite Hj.
  rewrite to_radix_fold_left.
  rewrite rev_involutive.
  clear.
  unfold dispatch_list.
  rewrite seq_length.
  apply map_ext_in_iff.
  intros a Ha.
  unfold nth_find_all.
  apply (eq_nth_find_all_loop_cons _ _ 0).
  rewrite seq_length, Nat.sub_0_r, Nat.sub_0_r; cbn.
  apply in_seq in Ha.
  split; [ easy | ]; destruct Ha as (_, Ha); cbn in Ha.
  rewrite seq_nth; [ | easy ].
  split. {
    intros k Hk.
    rewrite seq_nth; [ | flia Ha Hk ].
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
  apply in_seq in Hj; flia Hj.
}
rewrite Hjll.
rewrite <- loc_length_loc_bl_sens_list.
unfold "≥".
etransitivity; [ | apply fold_right_max_ge ].
apply Nat.le_max_l.
Qed.

(* "Obviously, bs(f) ≥ s(f)" *)

Theorem bs_ge_s : ∀ n f, block_sensitivity n f ≥ sensitivity n f.
Proof.
intros.
unfold block_sensitivity, sensitivity.
unfold "≥".
remember (seq 0 (2 ^ n)) as l; clear Heql.
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

Require Import Semiring SRsummation.

(* matrices *)

Record matrix T := mk_mat
  { mat_el : nat → nat → T;
    mat_nrows : nat;
    mat_ncols : nat }.

(* function extensionality required for matrices *)
Axiom matrix_eq : ∀ T (MA MB : matrix T),
  mat_nrows MA = mat_nrows MB
  → mat_ncols MA = mat_ncols MB
  → (∀ i j, i < mat_nrows MA → j < mat_ncols MB →
      mat_el MA i j = mat_el MB i j)
  → MA = MB.

Definition list_list_nrows T (ll : list (list T)) :=
  length ll.

Definition list_list_ncols T (ll : list (list T)) :=
  length (hd [] ll).

Definition list_list_of_mat T (M : matrix T) : list (list T) :=
  map (λ i, map (mat_el M i) (seq 0 (mat_ncols M))) (seq 0 (mat_nrows M)).

Definition list_list_el T d (ll : list (list T)) i j : T :=
  nth j (nth i ll []) d.

Definition mat_of_list_list T d (ll : list (list T)) :=
  mk_mat (list_list_el d ll) (list_list_nrows ll) (list_list_ncols ll).

(*
Compute (let (i, j) := (2, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (let (i, j) := (7, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (let (i, j) := (1, 3) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (list_list_of_mat (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]])).
*)

(* block matrices *)

Inductive bmatrix T :=
  | BM_1 : T → bmatrix T
  | BM_M : matrix (bmatrix T) → bmatrix T.

Theorem bmatrix_ind2 : ∀ T (P : bmatrix T → Prop),
  (∀ t, P (BM_1 t))
  → (∀ M, (∀ i j, i < mat_nrows M → j < mat_ncols M → P (mat_el M i j))
      → P (BM_M M))
  → ∀ BM, P BM.
Proof.
fix IHB 5.
intros * H1 HM *.
destruct BM as [x| M]; [ apply H1 | ].
apply HM.
intros.
destruct M as (f, r, c); cbn.
remember (f i j) as BM eqn:HBM.
symmetry in HBM.
destruct BM as [x| M]; [ apply H1 | ].
apply HM.
intros k l Hk Hl.
now apply IHB.
Qed.

Fixpoint concat_list_in_list T (ll1 ll2 : list (list T)) :=
  match ll1 with
  | [] => ll2
  | l1 :: ll1' =>
       match ll2 with
       | [] => ll1
       | l2 :: ll2' => app l1 l2 :: concat_list_in_list ll1' ll2'
       end
  end.

Definition concat_list_list_list T (lll : list (list (list T))) :=
  fold_left (@concat_list_in_list T) lll [].

Fixpoint list_list_of_bmat T (MM : bmatrix T) : list (list T) :=
  match MM with
  | BM_1 x => [[x]]
  | BM_M MMM =>
      let ll :=
        map
          (λ i,
             concat_list_list_list
               (map (λ j, list_list_of_bmat (mat_el MMM i j))
                  (seq 0 (mat_ncols MMM))))
          (seq 0 (mat_nrows MMM))
      in
      List.concat ll
  end.

(* addition *)

Definition mat_add T (add : T → T → T) (M1 M2 : matrix T) :
    matrix T :=
  {| mat_el i j := add (mat_el M1 i j) (mat_el M2 i j);
     mat_nrows := mat_nrows M1;
     mat_ncols := mat_ncols M1 |}.

(* addition of block matrices *)

Fixpoint bmat_add T {so : semiring_op T} (MM1 MM2 : bmatrix T) :=
  match MM1 with
  | BM_1 xa =>
      match MM2 with
      | BM_1 xb => BM_1 (xa + xb)%Srng
      | BM_M MMB => BM_1 0%Srng
      end
  | BM_M MMA =>
      match MM2 with
      | BM_1 xb => BM_1 0%Srng
      | BM_M MMB =>
          let r :=
            {| mat_el i j := bmat_add (mat_el MMA i j) (mat_el MMB i j);
               mat_nrows := mat_nrows MMA;
               mat_ncols := mat_ncols MMA |}
          in
          BM_M r
      end
  end.

Definition nat_semiring_op : semiring_op nat :=
  {| srng_zero := 0;
     srng_one := 1;
     srng_add := Nat.add;
     srng_mul := Nat.mul |}.

(*
Compute (let _ := nat_semiring_op in list_list_of_mat (mat_add add (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
*)

(* multiplication *)

Definition mat_mul T {so : semiring_op T} (MA MB : matrix T) :=
  {| mat_el i k := (Σ (j = 0, mat_ncols MA), mat_el MA i j * mat_el MB j k)%Srng;
     mat_nrows := mat_nrows MA;
     mat_ncols := mat_ncols MB |}.

(*
Compute (let _ := nat_semiring_op in list_list_of_mat (mat_mul (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
*)

(* multiplication of block matrices *)

Fixpoint bmat_mul T {so : semiring_op T} (MM1 MM2 : bmatrix T) :=
  match MM1 with
  | BM_1 xa =>
      match MM2 with
      | BM_1 xb => BM_1 (xa * xb)%Srng
      | BM_M _ => BM_1 0%Srng
      end
  | BM_M MMA =>
      match MM2 with
      | BM_1 _ => BM_1 0%Srng
      | BM_M MMB =>
          let mat_el_mul i k :=
            fold_left
              (λ acc j,
                 bmat_add acc
                   (bmat_mul (mat_el MMA i (j + 1)) (mat_el MMB (j + 1) k)))
              (seq 0 (mat_ncols MMA - 1))
              (bmat_mul (mat_el MMA i 0) (mat_el MMB 0 k))
          in
          let r :=
            {| mat_el i k := mat_el_mul i k;
               mat_nrows := mat_nrows MMA;
               mat_ncols := mat_ncols MMB |}
          in
          BM_M r
      end
  end.

(* opposite *)

Fixpoint bmat_opp T {ro : ring_op T} BM : bmatrix T :=
  match BM with
  | BM_1 x => BM_1 (- x)%Rng
  | BM_M MMM =>
      let M :=
         {| mat_el i j := bmat_opp (mat_el MMM i j);
            mat_nrows := mat_nrows MMM;
            mat_ncols := mat_ncols MMM |}
      in
      BM_M M
  end.

Theorem bmat_opp_involutive : ∀ T {ro : ring_op T} {rp : ring_prop T}
  (so := @rng_semiring T ro) {sp : semiring_prop T} BM,
  bmat_opp (bmat_opp BM) = BM.
Proof.
intros.
induction BM as [x| M IHBM] using bmatrix_ind2. {
  now cbn; rewrite rng_opp_involutive.
} {
  destruct M as (f, r, c).
  cbn in IHBM |-*.
  f_equal.
  apply matrix_eq; cbn; [ easy | easy | ].
  intros * Hi Hj.
  now apply IHBM.
}
Qed.

Definition bmat_sub T {ro : ring_op T} (so := rng_semiring) BMA BMB :=
  bmat_add BMA (bmat_opp BMB).

Declare Scope BM_scope.
Delimit Scope BM_scope with BM.

Module bmatrix_Notations.

Notation "a + b" := (bmat_add a b) : BM_scope.
Notation "a - b" := (bmat_sub a b) : BM_scope.
Notation "a * b" := (bmat_mul a b) : BM_scope.
Notation "- a" := (bmat_opp a) : BM_scope.

End bmatrix_Notations.

Import bmatrix_Notations.

(* sequence "An" *)

Fixpoint IZ_2_pow T {so : semiring_op T} (u : T) n :=
  match n with
  | 0 => BM_1 u
  | S n' =>
      BM_M
        (mat_of_list_list (BM_1 u)
           [[IZ_2_pow u n'; IZ_2_pow 0%Srng n'];
            [IZ_2_pow 0%Srng n'; IZ_2_pow u n']])
  end.

Definition I_2_pow T {so : semiring_op T} := IZ_2_pow 1%Srng.
Definition Z_2_pow T {so : semiring_op T} := IZ_2_pow 0%Srng.

Theorem fold_Z_2_pow : ∀ T {so : semiring_op T} n,
  IZ_2_pow 0%Srng n = Z_2_pow n.
Proof. easy. Qed.

Fixpoint A T {ro : ring_op T} (so := rng_semiring) n : bmatrix T :=
  match n with
  | 0 => BM_1 0%Srng
  | S n' =>
       BM_M
         (mat_of_list_list (BM_1 0%Srng)
            [[A n'; I_2_pow n'];
             [I_2_pow n'; bmat_opp (A n')]])
  end.

(*
Require Import ZArith.

About Z_ring_op.
Compute (let n := 2%nat in let _ := Z_ring_op in let _ := rng_semiring in A n).

Compute (let n := 3%nat in let _ := Z_ring_op in let _ := rng_semiring in list_list_of_bmat (I_2_pow n)).
Compute (let n := 3%nat in let _ := Z_ring_op in let _ := rng_semiring in list_list_of_bmat (A n)).
Compute (let n := 3%nat in let _ := Z_ring_op in let _ := rng_semiring in list_list_of_bmat (bmat_mul (A n) (A n))).
*)

Definition rng_mul_nat_l T {so : semiring_op T} n v :=
  match n with
  | 0 => 0%Srng
  | S n' => (Σ (_ = 0, n'), v)%Srng
  end.

Fixpoint bmat_nat_mul_l T {so : semiring_op T} n BM :=
  match BM with
  | BM_1 x => BM_1 (rng_mul_nat_l n x)
  | BM_M M =>
      BM_M
        {| mat_el i j := bmat_nat_mul_l n (mat_el M i j);
           mat_nrows := mat_nrows M;
           mat_ncols := mat_ncols M |}
  end.

Fixpoint bmat_fit_for_add T (MA MB : bmatrix T) :=
  match MA with
  | BM_1 xa =>
      match MB with
      | BM_1 xb => True
      | BM_M MMB => False
      end
  | BM_M MMA =>
      match MB with
      | BM_1 xb => False
      | BM_M MMB =>
          mat_nrows MMA = mat_nrows MMB ∧
          mat_ncols MMA = mat_ncols MMB ∧
          ∀ i j, i < mat_nrows MMA → j < mat_ncols MMA →
          bmat_fit_for_add (mat_el MMA i j) (mat_el MMB i j)
      end
  end.

Require Import Relations.

Theorem bmat_fit_for_add_refl : ∀ T,
  reflexive _ (@bmat_fit_for_add T).
Proof.
intros * M.
induction M as [x| M IHM] using bmatrix_ind2; [ easy | cbn ].
destruct M as (ll, r, c); cbn in IHM |-*.
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
now apply IHM.
Qed.

Theorem bmat_fit_for_add_symm : ∀ T,
  symmetric _ (@bmat_fit_for_add T).
Proof.
intros * MA MB HMM.
revert MB HMM.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  now destruct MB.
}
destruct MB as [xb| mb]; [ easy | ].
cbn in HMM |-*.
destruct ma as (lla, ra, ca); destruct mb as (llb, rb, cb).
cbn in IHMA, HMM |-*.
destruct HMM as (Hrr & Hcc & Hss).
subst rb cb.
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
now apply IHMA, Hss.
Qed.

Theorem bmat_fit_for_add_trans : ∀ T,
  transitive _ (@bmat_fit_for_add T).
Proof.
intros * MA MB MC HAB HBC.
revert MB MC HAB HBC.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  now destruct MB.
}
destruct MB as [xb| mb]; [ easy | ].
destruct MC as [xc| mc]; [ easy | ].
cbn in HAB, HBC |-*.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
destruct mc as (fc, rc, cc).
cbn in IHMA, HAB, HBC |-*.
destruct HAB as (Hrr & Hcc & Hab); subst rb cb.
destruct HBC as (Hrr & Hcc & Hbc); subst rc cc.
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
now apply IHMA with (MB := fb i j); [ | | apply Hab | apply Hbc ].
Qed.

Add Parametric Relation T : _ (@bmat_fit_for_add T)
 reflexivity proved by (@bmat_fit_for_add_refl T)
 symmetry proved by (@bmat_fit_for_add_symm T)
 transitivity proved by (@bmat_fit_for_add_trans T)
 as bmat_fit_for_add_equivalence.

Theorem bmat_add_comm :
    ∀ T {so : semiring_op T } {sp : semiring_prop T} MA MB,
  bmat_fit_for_add MA MB
  → bmat_add MA MB = bmat_add MB MA.
Proof.
intros * sp * Hss.
revert MB Hss.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  destruct MB as [xb| mb]; [ | easy ].
  now cbn; rewrite srng_add_comm.
}
destruct MB as [xb| mb]; [ easy | ].
cbn in Hss.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in IHMA, Hss |-*.
destruct Hss as (Hrr & Hcc & Hss); subst rb cb.
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
apply IHMA; [ easy | easy | ].
now apply Hss.
Qed.

Theorem old_bmat_add_0_l : ∀ T {so : semiring_op T } {sp : semiring_prop T} n M,
  bmat_fit_for_add (Z_2_pow n) M
  → bmat_add (Z_2_pow n) M = M.
Proof.
intros * sp * Hss.
revert M Hss.
induction n; intros. {
  cbn.
  destruct M as [x| M]; [ now rewrite srng_add_0_l | easy ].
}
cbn in Hss |-*.
destruct M as [x| M]; [ easy | f_equal ].
destruct Hss as (Hr & Hc & Hss).
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
rewrite <- Hc in Hj.
specialize (Hss _ _ Hi Hj) as H1.
destruct i. {
  destruct j; [ now apply IHn | cbn ].
  destruct j; [ now apply IHn | flia Hj ].
}
destruct i; [ cbn | flia Hi ].
destruct j; [ now apply IHn | cbn ].
destruct j; [ now apply IHn | flia Hj ].
Qed.

Theorem bmat_add_0_r : ∀ T {so : semiring_op T } {sp : semiring_prop T} n M,
  bmat_fit_for_add (Z_2_pow n) M
  → bmat_add M (Z_2_pow n) = M.
Proof.
intros * sp * Hss.
rewrite bmat_add_comm; [ | easy | easy ].
now apply old_bmat_add_0_l.
Qed.

Theorem bmat_fit_for_add_IZ_IZ : ∀ T {so : semiring_op T} u v n,
  bmat_fit_for_add (IZ_2_pow u n) (IZ_2_pow v n).
Proof.
intros.
revert u v.
induction n; intros; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
destruct i. {
  destruct j; [ apply IHn | ].
  destruct j; [ apply IHn | flia Hj ].
}
destruct i; [ | flia Hi ].
destruct j; [ apply IHn | ].
destruct j; [ apply IHn | flia Hj ].
Qed.

Theorem bmat_fit_for_add_opp_r : ∀ T {ro : ring_op T} M,
  bmat_fit_for_add M (bmat_opp M).
Proof.
intros.
induction M as [| M IHM] using bmatrix_ind2; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros * Hi Hj.
now apply IHM.
Qed.

Theorem bmat_fit_for_add_IZ_A : ∀ T {ro : ring_op T} (so := rng_semiring)
    u n,
  bmat_fit_for_add (IZ_2_pow u n) (A n).
Proof.
intros.
revert u.
induction n; intros; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros * Hi Hj.
destruct i. {
  destruct j; [ apply IHn | ].
  destruct j; [ cbn | flia Hj ].
  apply bmat_fit_for_add_IZ_IZ.
}
destruct i; [ | flia Hi ].
destruct j; [ apply bmat_fit_for_add_IZ_IZ | ].
destruct j; [ cbn | flia Hj ].
transitivity (A n); [ easy | ].
apply bmat_fit_for_add_opp_r.
Qed.

Fixpoint is_square_bmat_loop T sizes (M : bmatrix T) {struct sizes} :=
  match M with
  | BM_1 _ => sizes = []
  | BM_M MM =>
      match sizes with
      | size :: sizes' =>
          mat_nrows MM = size ∧
          mat_ncols MM = size ∧
          (∀ i j, i < size → j < size →
           is_square_bmat_loop sizes' (mat_el MM i j))
      | [] => False
      end
  end.

Fixpoint sizes_of_bmatrix T (BM : bmatrix T) :=
  match BM with
  | BM_1 _ => []
  | BM_M M =>
      if zerop (mat_nrows M) ∨∨ zerop (mat_ncols M) then []
      else mat_nrows M :: sizes_of_bmatrix (mat_el M 0 0)
  end.

Definition is_square_bmat T (BM : bmatrix T) :=
  is_square_bmat_loop (sizes_of_bmatrix BM) BM.

Fixpoint bmat_zero_like T {so : semiring_op T} (BM : bmatrix T) :=
  match BM with
  | BM_1 _ => BM_1 0%Srng
  | BM_M M =>
      let M' :=
        mk_mat (λ i j, bmat_zero_like (mat_el M i j))
          (mat_nrows M) (mat_ncols M)
      in
      BM_M M'
  end.

Theorem sizes_of_bmat_zero_like : ∀ T {so : semiring_op T} (BM : bmatrix T),
  sizes_of_bmatrix (bmat_zero_like BM) = sizes_of_bmatrix BM.
Proof.
intros.
induction BM as [x| M IHBM] using bmatrix_ind2; [ easy | cbn ].
destruct (zerop (mat_nrows M)) as [Hr| Hr]; [ easy | ].
destruct (zerop (mat_ncols M)) as [Hc| Hc]; [ easy | ].
cbn; f_equal.
now apply IHBM.
Qed.

Theorem square_bmat_zero_like : ∀ T {so : semiring_op T} (BM : bmatrix T),
  is_square_bmat BM
  → is_square_bmat (bmat_zero_like BM).
Proof.
intros * HBM.
unfold is_square_bmat in HBM |-*.
rewrite sizes_of_bmat_zero_like.
remember (sizes_of_bmatrix BM) as sizes; clear Heqsizes.
revert BM HBM.
induction sizes as [| size]; intros; [ now destruct BM | ].
cbn in HBM |-*.
destruct BM as [x| M]; [ easy | cbn ].
destruct HBM as (Hr & Hc & HBM).
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
apply IHsizes.
now apply HBM.
Qed.

Theorem no_zero_bmat_size : ∀ T (BM : bmatrix T), 0 ∉ sizes_of_bmatrix BM.
Proof.
intros * Hs.
induction BM as [x| M IHBM] using bmatrix_ind2; [ easy | ].
cbn in Hs.
destruct (zerop (mat_nrows M)) as [Hrz| Hrz]; [ easy | ].
destruct (zerop (mat_ncols M)) as [Hcz| Hcz]; [ easy | ].
cbn - [ In ] in Hs.
destruct Hs as [Hs| Hs]; [ now rewrite Hs in Hrz | ].
now apply (IHBM 0 0).
Qed.

Theorem sizes_of_bmatrix_mat_el :
  ∀ T {so : semiring_op T} {sp : semiring_prop T},
  ∀ (M : matrix (bmatrix T)),
  is_square_bmat (BM_M M)
  → ∀ i j,
     i < mat_nrows M → j < mat_ncols M →
     sizes_of_bmatrix (mat_el M i j) = sizes_of_bmatrix (mat_el M 0 0).
Proof.
intros * sp * Ha * Hi Hj.
cbn in Ha.
destruct (zerop (mat_nrows M)) as [Hrz| Hrz]; [ easy | ].
destruct (zerop (mat_ncols M)) as [Hcz| Hcz]; [ easy | cbn in Ha ].
destruct Ha as (_ & Hcr & Ha).
destruct M as (fa, ra, ca); cbn in *.
subst ca; clear Hrz Hcz.
remember (sizes_of_bmatrix (fa 0 0)) as sizes eqn:Hsizes.
specialize (Ha _ _ Hi Hj) as H1.
destruct sizes as [| size]; [ now destruct (fa i j) | cbn in H1 ].
remember (fa i j) as M eqn:Hm; symmetry in Hm.
destruct M as [x| M]; [ easy | ].
destruct H1 as (Hr & Hc & H1); cbn.
rewrite Hr, Hc.
destruct (zerop size) as [Hzs| Hzs]. {
  move Hzs at top; subst size; exfalso.
  specialize (no_zero_bmat_size (fa 0 0)) as H2.
  rewrite <- Hsizes in H2.
  now apply H2; left.
}
cbn; f_equal.
specialize (H1 0 0 Hzs Hzs) as H2.
specialize (no_zero_bmat_size (fa 0 0)) as H3.
rewrite <- Hsizes in H3.
clear Hsizes Hm Ha Hzs Hr Hc.
clear i j Hi Hj fa ra sp.
revert M size H1 H2 H3.
induction sizes as [| size1]; intros; [ now destruct (mat_el M 0 0) | ].
cbn in H2.
remember (mat_el M 0 0) as BM eqn:HBM; symmetry in HBM.
destruct BM as [x| M']; [ easy | ].
destruct H2 as (Hr' & Hc' & Hss); cbn.
rewrite Hr', Hc'.
destruct (zerop size1) as [Hs1| Hs1]. {
  exfalso.
  now apply H3; rewrite Hs1; right; left.
}
cbn; f_equal.
apply (IHsizes _ size1); [ easy | now apply Hss | ]. {
  intros H; apply H3.
  destruct H as [H| H]; [ now right; left | now right; right ].
}
Qed.

Theorem sizes_of_bmatrix_at_0_0 :
  ∀ T {so : semiring_op T} {sp : semiring_prop T},
  ∀ (f : _ → _ → bmatrix T) r,
  (∀ i j, i < r → j < r →
      is_square_bmat_loop (sizes_of_bmatrix (f 0 0)) (f i j))
  → ∀ i j, i < r → j < r →
  sizes_of_bmatrix (f i j) = sizes_of_bmatrix (f 0 0).
Proof.
intros * sp * Hf * Hi Hj.
apply (sizes_of_bmatrix_mat_el (mk_mat f r r)); cbn; [ | easy | easy ].
destruct (zerop r) as [Hrz| Hrz]; [ flia Hi Hrz | easy ].
Qed.

Theorem bmat_zero_like_add_distr :
  ∀ T {so : semiring_op T} {sp : semiring_prop T},
  ∀ BMA BMB,
  bmat_zero_like (BMA + BMB)%BM =
  (bmat_zero_like BMA + bmat_zero_like BMB)%BM.
Proof.
intros.
revert BMB.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros; cbn. {
  destruct BMB as [xb| mb]; [ cbn | easy ].
  now rewrite srng_add_0_l.
}
destruct BMB as [xb| mb]; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
now apply IHBMA.
Qed.

Theorem bmat_zero_like_mul_distr_l :
  ∀ T {so : semiring_op T} {sp : semiring_prop T} BMA BMB,
  is_square_bmat BMA
  → bmat_zero_like (BMA * BMB)%BM = (bmat_zero_like BMA * BMB)%BM.
Proof.
intros * sp * Ha.
symmetry.
revert BMB.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros; cbn. {
  destruct BMB as [xb| mb]; [ | easy ].
  now rewrite srng_mul_0_l.
}
destruct BMB as [xb| mb]; [ easy | ].
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
specialize (sizes_of_bmatrix_mat_el _ Ha) as Haa.
cbn in Ha.
destruct (zerop (mat_nrows ma)) as [Hzra| Hzra]; [ easy | ].
destruct (zerop (mat_ncols ma)) as [Hzca| Hzca]; [ easy | ].
cbn in Ha.
destruct Ha as (Hrr & Hcr & Ha).
rewrite Hcr in Haa.
rewrite IHBMA; [ | easy | easy | ]. 2: {
  specialize (Ha i 0 Hi Hzra) as H2.
  unfold is_square_bmat.
  now rewrite Haa.
}
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *.
subst ca; clear Hrr Hzra Hzca.
destruct ra; [ easy | cbn ].
rewrite Nat.sub_0_r.
replace
  (fold_left (λ a k, a + bmat_zero_like (fa i (k + 1)%nat) * fb (k + 1)%nat j)
    (seq 0 ra) (bmat_zero_like (fa i 0 * fb 0 j)))%BM
with
  (fold_left (λ a k, a + bmat_zero_like (fa i (k + 1)%nat * fb (k + 1)%nat j))
    (seq 0 ra) (bmat_zero_like (fa i 0 * fb 0 j)))%BM. 2: {
  apply List_fold_left_ext_in.
  intros k BM Hk; f_equal.
  apply in_seq in Hk.
  clear BM.
  symmetry; apply IHBMA; [ easy | flia Hk | ].
  rewrite Haa; [ | easy | flia Hk ].
  apply Ha; [ easy | flia Hk ].
}
clear Hi IHBMA.
induction ra; [ easy | ].
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite fold_left_app; cbn.
rewrite bmat_zero_like_add_distr; [ | easy ].
f_equal.
apply IHra. {
  intros i1 j1 Hi1 Hj1.
  apply Ha; [ flia Hi1 | flia Hj1 ].
} {
  intros i1 j1 Hi1 Hj1.
  apply Haa; [ flia Hi1 | flia Hj1 ].
}
Qed.

Definition compatible_square_bmatrices T (BML : list (bmatrix T)) :=
  ∃ sizes,
   (∀ BM, BM ∈ BML → is_square_bmat BM) ∧
   (∀ BM, BM ∈ BML → sizes_of_bmatrix BM = sizes).

Theorem bmat_zero_like_mul_distr_r :
  ∀ T {so : semiring_op T} {sp : semiring_prop T} BMA BMB,
  compatible_square_bmatrices [BMA; BMB]
  → bmat_zero_like (BMA * BMB)%BM = (BMA * bmat_zero_like BMB)%BM.
Proof.
intros * sp * Hcsb.
revert BMB Hcsb.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros; cbn. {
  destruct BMB as [xb| mb]; [ cbn | easy ].
  now rewrite srng_mul_0_r.
}
destruct BMB as [xb| mb]; [ easy | ].
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
destruct Hcsb as (sizes & Hsq & Hsz).
specialize (Hsq _ (or_introl eq_refl)) as Ha.
specialize (Hsq _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hsz _ (or_introl eq_refl)) as Has.
specialize (Hsz _ (or_intror (or_introl eq_refl))) as Hbs.
clear Hsq Hsz.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *.
destruct (zerop ra) as [Hraz| Hraz]; [ easy | ].
destruct (zerop ca) as [Hcaz| Hcaz]; [ easy | ].
destruct (zerop rb) as [Hrbz| Hrbz]; [ easy | ].
destruct (zerop cb) as [Hcbz| Hcbz]; [ easy | ].
cbn in Ha, Has, Hb, Hbs.
destruct Ha as (_ & H & Ha); subst ca.
destruct Hb as (_ & H & Hb); subst cb.
rewrite <- Has in Hbs.
injection Hbs; clear Hbs; intros Hab H; subst rb.
clear Hraz Hcaz Hcbz Hrbz.
destruct ra; [ easy | cbn ].
rewrite Nat.sub_0_r.
destruct sizes as [| size]; [ easy | ].
injection Has; clear Has; intros Has H.
clear size H.
replace
  (fold_left (λ a k, a + fa i (k + 1)%nat * bmat_zero_like (fb (k + 1)%nat j))
     (seq 0 ra) (fa i 0 * bmat_zero_like (fb 0 j)))%BM
with
  (fold_left (λ a k, a + bmat_zero_like (fa i (k + 1)%nat * fb (k + 1)%nat j))
     (seq 0 ra) (bmat_zero_like (fa i 0 * fb 0 j)))%BM. 2: {
  rewrite <- IHBMA; [ | easy | flia | ]. 2: {
    exists sizes.
    split; intros BM HBM. {
      destruct HBM as [HBM| HBM]; [ subst BM | ]. {
        unfold is_square_bmat.
        rewrite (@sizes_of_bmatrix_at_0_0 _ _ _ _ (S ra));
          [ | easy | easy | flia ].
        apply Ha; [ easy | flia ].
      } {
        destruct HBM as [HBM| HBM]; [ subst BM | easy ].
        unfold is_square_bmat.
        rewrite (@sizes_of_bmatrix_at_0_0 _ _ _ _ (S ra));
          [ | easy | flia | easy ].
        apply Hb; [ flia | easy ].
      }
    } {
      destruct HBM as [HBM| HBM]; [ subst BM | ]. {
        rewrite (@sizes_of_bmatrix_at_0_0 _ _ _ _ (S ra));
          [ easy | easy | easy | flia ].
      } {
        destruct HBM as [HBM| HBM]; [ subst BM | easy ].
        rewrite (@sizes_of_bmatrix_at_0_0 _ _ _ _ (S ra));
          [ congruence | easy | flia | easy ].
      }
    }
  }
  apply List_fold_left_ext_in.
  intros k BM Hk; f_equal.
  apply in_seq in Hk.
  clear BM.
  apply IHBMA; [ easy | flia Hk | ].
  exists sizes.
  split; intros BM HBM. {
    destruct HBM as [HBM| HBM]; [ subst BM | ]. {
      unfold is_square_bmat.
      rewrite (@sizes_of_bmatrix_at_0_0 _ _ _ _ (S ra));
          [ | easy | easy | flia Hk ].
        apply Ha; [ easy | flia Hk ].
      } {
        destruct HBM as [HBM| HBM]; [ subst BM | easy ].
        unfold is_square_bmat.
        rewrite (@sizes_of_bmatrix_at_0_0 _ _ _ _ (S ra));
          [ | easy | flia Hk | easy ].
        apply Hb; [ flia Hk | easy ].
      }
    } {
      destruct HBM as [HBM| HBM]; [ subst BM | ]. {
        rewrite (@sizes_of_bmatrix_at_0_0 _ _ _ _ (S ra));
          [ easy | easy | easy | flia Hk ].
      } {
        destruct HBM as [HBM| HBM]; [ subst BM | easy ].
        rewrite (@sizes_of_bmatrix_at_0_0 _ _ _ _ (S ra));
          [ congruence | easy | flia Hk | easy ].
      }
  }
}
clear IHBMA.
clear Hi Hj.
induction ra; [ easy | ].
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite fold_left_app; cbn.
rewrite bmat_zero_like_add_distr; [ | easy ].
f_equal.
apply IHra. {
  intros i1 j1 Hi1 Hj1.
  apply Ha; [ flia Hi1 | flia Hj1 ].
} {
  intros i1 j1 Hi1 Hj1.
  apply Hb; [ flia Hi1 | flia Hj1 ].
}
Qed.

Theorem bmat_zero_like_eq_compat :
  ∀ T {so : semiring_op T} {sp : semiring_prop T},
  ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → bmat_zero_like BMA = bmat_zero_like BMB.
Proof.
intros * sp * Ha Hb Hab.
unfold is_square_bmat in Ha, Hb.
rewrite <- Hab in Hb.
remember (sizes_of_bmatrix BMA) as sizes; clear Heqsizes Hab.
revert BMA BMB Ha Hb.
induction sizes as [| size]; intros; [ now destruct BMA, BMB | ].
cbn in Ha, Hb.
destruct BMA as [xa| ma]; [ easy | ].
destruct BMB as [xb| mb]; [ easy | ].
destruct Ha as (Hra & Hca & Ha).
destruct Hb as (Hrb & Hcb & Hb).
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *; subst ra ca rb cb.
f_equal.
apply matrix_eq; [ easy | easy | cbn ].
intros * Hi Hj.
apply IHsizes; [ now apply Ha | now apply Hb ].
Qed.

Theorem sizes_of_bmatrix_add :
  ∀ T {so : semiring_op T} {sp : semiring_prop T},
  ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → sizes_of_bmatrix (BMA + BMB)%BM = sizes_of_bmatrix BMA.
Proof.
intros * sp * Ha Hb Hab.
revert BMB Hb Hab.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros. {
  now destruct BMB.
}
destruct BMB as [xb| mb]; [ easy | cbn ].
move mb before ma.
cbn in Ha, Hb, Hab.
destruct (zerop (mat_nrows ma)) as [Hrza| Hrza]; [ easy | ].
destruct (zerop (mat_ncols ma)) as [Hcza| Hcza]; [ easy | ].
destruct (zerop (mat_nrows mb)) as [Hrzb| Hrzb]; [ easy | ].
destruct (zerop (mat_ncols mb)) as [Hczb| Hczb]; [ easy | ].
cbn in Ha, Hb, Hab |-*.
f_equal.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *.
destruct Ha as (_ & Hrca & Ha).
destruct Hb as (_ & Hrcb & Hb).
subst ca cb.
injection Hab; clear Hab; intros Hss H2; subst rb.
apply IHBMA; [ easy | easy | | | easy ]. {
  now apply Ha.
} {
  now apply Hb.
}
Qed.

Theorem is_square_bmat_loop_add : ∀ T {so : semiring_op T} BMA BMB sizes,
  is_square_bmat_loop sizes BMA
  → is_square_bmat_loop sizes BMB
  → is_square_bmat_loop sizes (BMA + BMB)%BM.
Proof.
intros * Ha Hb.
revert BMA BMB Ha Hb.
induction sizes as [| size]; intros; cbn; [ now destruct BMA, BMB | ].
cbn in Ha, Hb.
destruct BMA as [xa| ma]; [ easy | ].
destruct BMB as [xb| mb]; [ easy | ].
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb); cbn in *.
destruct Ha as (Hra & Hca & Ha).
destruct Hb as (Hrb & Hcb & Hb).
subst ra ca rb cb.
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
apply IHsizes; [ now apply Ha | now apply Hb ].
Qed.

Theorem bmat_add_0_l : ∀ T {so : semiring_op T} {sp : semiring_prop T} BM,
  is_square_bmat BM
  → (bmat_zero_like BM + BM)%BM = BM.
Proof.
intros * sp * Hss.
induction BM as [x| M IHBM] using bmatrix_ind2. {
  now cbn; rewrite srng_add_0_l.
}
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
apply IHBM; [ easy | easy | ].
cbn in Hss.
unfold is_square_bmat.
destruct (zerop (mat_nrows M)) as [H| H]; [ flia Hi H | cbn in Hss; clear H ].
destruct (zerop (mat_ncols M)) as [H| H]; [ flia Hj H | cbn in Hss; clear H ].
destruct Hss as (_ & Hcr & Hss).
erewrite sizes_of_bmatrix_mat_el; [ | easy | | easy | easy ]. {
  rewrite Hcr in Hj.
  now apply Hss.
} {
  cbn; rewrite Hcr.
  destruct (zerop (mat_nrows M)) as [H| H]; [ flia Hi H | cbn; clear H ].
  split; [ easy | ].
  split; [ easy | ].
  clear i j Hi Hj.
  intros i j Hi Hj.
  now apply Hss.
}
Qed.

Theorem is_square_bmat_loop_mul : ∀ T {so : semiring_op T} BMA BMB sizes,
  is_square_bmat_loop sizes BMA
  → is_square_bmat_loop sizes BMB
  → is_square_bmat_loop sizes (BMA * BMB)%BM.
Proof.
intros * Ha Hb.
revert BMA BMB Ha Hb.
induction sizes as [| size]; intros; cbn; [ now destruct BMA, BMB | ].
cbn in Ha, Hb.
destruct BMA as [xa| ma]; [ easy | ].
destruct BMB as [xb| mb]; [ easy | ].
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb); cbn in *.
destruct Ha as (Hra & Hca & Ha).
destruct Hb as (Hrb & Hcb & Hb).
subst ra ca rb cb.
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
destruct size; [ easy | cbn ].
rewrite Nat.sub_0_r.
assert (H : ∀ j, j < S size → is_square_bmat_loop sizes (fa i j)). {
  intros k Hk.
  now apply Ha.
}
move H before Ha; clear Ha; rename H into Ha.
assert (H : ∀ i, i < S size → is_square_bmat_loop sizes (fb i j)). {
  intros k Hk.
  now apply Hb.
}
move H before Hb; clear Hb; rename H into Hb.
clear Hi Hj.
move j before i.
induction size. {
  apply IHsizes; [ apply Ha; flia | apply Hb; flia ].
}
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
apply is_square_bmat_loop_add. 2: {
  apply IHsizes; [ apply Ha; flia | apply Hb; flia ].
}
apply IHsize. {
  intros k Hk.
  apply Ha; flia Hk.
} {
  intros k Hk.
  apply Hb; flia Hk.
}
Qed.

Theorem sizes_of_bmatrix_fold_left :
  ∀ T {so : semiring_op T} {sp : semiring_prop T},
  ∀ BM sta len f,
  is_square_bmat BM
  → (∀ n, sta ≤ n < sta + len → is_square_bmat (f n))
  → (∀ n, sta ≤ n < sta + len → sizes_of_bmatrix BM = sizes_of_bmatrix (f n))
  → sizes_of_bmatrix (fold_left (λ acc j, (acc + f j)%BM) (seq sta len) BM) =
    sizes_of_bmatrix BM.
Proof.
intros * sp * Hb Hf Hfb.
revert sta BM Hf Hb Hfb.
induction len; intros; [ easy | cbn ].
rewrite IHlen; cycle 1. {
  intros n Hn.
  apply Hf; flia Hn.
} {
  apply is_square_bmat_loop_add. {
    rewrite sizes_of_bmatrix_add; [ easy | easy | easy | | ]. {
      apply Hf; flia.
    } {
      apply Hfb; flia.
    }
  } {
    rewrite sizes_of_bmatrix_add; [ | easy | easy | | ]. {
      rewrite (Hfb sta); [ | flia ].
      apply Hf; flia.
    } {
      apply Hf; flia.
    } {
      apply Hfb; flia.
    }
  }
} {
  intros * Hn.
  rewrite sizes_of_bmatrix_add; [ | easy | easy | | ]. {
    apply Hfb; flia Hn.
  } {
    apply Hf; flia.
  } {
    apply Hfb; flia.
  }
}
apply sizes_of_bmatrix_add; [ easy | easy | | ]. {
  apply Hf; flia.
} {
  apply Hfb; flia.
}
Qed.

Theorem sizes_of_bmatrix_mul :
  ∀ T {so : semiring_op T} {sp : semiring_prop T},
  ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → sizes_of_bmatrix (BMA * BMB)%BM = sizes_of_bmatrix BMA.
Proof.
intros * sp * Ha Hb Hab.
revert BMB Hb Hab.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros. {
  now destruct BMB.
}
destruct BMB as [xb| mb]; [ easy | cbn ].
move mb before ma.
cbn in Ha, Hb, Hab.
specialize (sizes_of_bmatrix_mat_el ma Ha) as Has.
specialize (sizes_of_bmatrix_mat_el mb Hb) as Hbs.
destruct (zerop (mat_nrows ma)) as [Hrza| Hrza]; [ easy | ].
destruct (zerop (mat_ncols ma)) as [Hcza| Hcza]; [ easy | ].
destruct (zerop (mat_nrows mb)) as [Hrzb| Hrzb]; [ easy | ].
destruct (zerop (mat_ncols mb)) as [Hczb| Hczb]; [ easy | ].
cbn in Ha, Hb, Hab, Has, Hbs |-*.
f_equal.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *.
destruct Ha as (_ & Hrca & Ha).
destruct Hb as (_ & Hrcb & Hb).
subst ca cb.
injection Hab; clear Hab; intros Hss H2; subst rb.
clear Hcza Hrzb Hczb.
specialize (IHBMA 0 0 Hrza Hrza) as Hssab.
specialize (Hssab (Ha 0 0 Hrza Hrza)).
specialize (Hssab (fb 0 0)).
specialize (Hssab (Hb 0 0 Hrza Hrza) Hss).
destruct ra; [ easy | clear Hrza; cbn ].
rewrite Nat.sub_0_r.
induction ra. {
  apply IHBMA; [ flia | flia | apply Ha; flia | apply Hb; flia | easy ].
}
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
assert (Hsm :
  sizes_of_bmatrix
    (fold_left (λ acc j, (acc + fa 0 (j + 1)%nat * fb (j + 1)%nat 0)%BM)
       (seq 0 ra) (fa 0 0 * fb 0 0)%BM) = sizes_of_bmatrix (fa 0 0)). {
  apply IHra. {
    intros i j Hi Hj H1 BMB Hbmb Hab.
    apply IHBMA; [ flia Hi | flia Hj | easy | easy | easy ].
  } {
    intros i j Hi Hj.
    apply Ha; [ flia Hi | flia Hj ].
  } {
    intros i j Hi Hj.
    apply Hb; [ flia Hi | flia Hj ].
  } {
    intros i j Hi Hj.
    apply Has; [ flia Hi | flia Hj ].
  } {
    intros i j Hi Hj.
    apply Hbs; [ flia Hi | flia Hj ].
  }
}
rewrite sizes_of_bmatrix_add; [ easy | easy | | | ]; cycle 1. {
  unfold is_square_bmat.
  rewrite IHBMA; [ | flia | flia | | | ]; cycle 1. {
    rewrite Has; [ | flia | flia ].
    apply Ha; flia.
  } {
    unfold is_square_bmat.
    rewrite Hbs; [ | flia | flia ].
    apply Hb; flia.
  } {
    rewrite Has; [ | flia | flia ].
    rewrite Hbs; [ | flia | flia ].
    easy.
  }
  rewrite Has; [ | flia | flia ].
  apply is_square_bmat_loop_mul; [ apply Ha; flia | ].
  rewrite Hss; apply Hb; flia.
} {
  rewrite IHBMA; [ | flia | flia | | | ]; cycle 1. {
    rewrite Has; [ | flia | flia ].
    apply Ha; [ flia | flia ].
  } {
    unfold is_square_bmat.
    rewrite Hbs; [ | flia | flia ].
    apply Hb; [ flia | flia ].
  } {
    rewrite Has; [ | flia | flia ].
    rewrite Hbs; [ | flia | flia ].
    easy.
  }
  rewrite Has; [ | flia | flia ].
  apply Hsm.
} {
  unfold is_square_bmat.
  rewrite Hsm.
  clear IHra.
  induction ra. {
    cbn.
    apply is_square_bmat_loop_mul; [ apply Ha; flia | ].
    rewrite Hss; apply Hb; flia.
  }
  rewrite List_seq_succ_r; cbn.
  rewrite fold_left_app; cbn.
  apply is_square_bmat_loop_add. 2: {
    apply is_square_bmat_loop_mul; [ apply Ha; flia | ].
    rewrite Hss; apply Hb; flia.
  }
  apply IHra. {
    intros i j Hi Hj H1 BMB Hbmb Hab.
    apply IHBMA; [ flia Hi | flia Hj | easy | easy | easy ].
  } {
    intros i j Hi Hj.
    apply Ha; [ flia Hi | flia Hj ].
  } {
    intros i j Hi Hj.
    apply Hb; [ flia Hi | flia Hj ].
  } {
    intros i j Hi Hj.
    apply Has; [ flia Hi | flia Hj ].
  } {
    intros i j Hi Hj.
    apply Hbs; [ flia Hi | flia Hj ].
  }
  move Hsm at bottom.
  rewrite List_seq_succ_r in Hsm; cbn in Hsm.
  rewrite fold_left_app in Hsm; cbn in Hsm.
  rewrite sizes_of_bmatrix_add in Hsm; [ easy | easy | | | ]; cycle 1. {
    unfold is_square_bmat.
    rewrite IHBMA; [ | flia | flia | | | ]; cycle 1. {
      rewrite Has; [ | flia | flia ].
      apply Ha; flia.
    } {
      unfold is_square_bmat.
      rewrite Hbs; [ | flia | flia ].
      apply Hb; flia.
    } {
      rewrite Has; [ | flia | flia ].
      rewrite Hbs; [ | flia | flia ].
      easy.
    }
    rewrite Has; [ | flia | flia ].
    apply is_square_bmat_loop_mul; [ apply Ha; flia | ].
    rewrite Hss; apply Hb; flia.
  } {
    rewrite IHBMA; [ | flia | flia | | | ]. {
      rewrite Has; [ | flia | flia ].
      rewrite <- Hssab.
      apply sizes_of_bmatrix_fold_left; [ easy | | | ]. {
        unfold is_square_bmat.
        rewrite Hssab.
        apply is_square_bmat_loop_mul; [ apply Ha; flia | ].
        rewrite Hss; apply Hb; flia.
      } {
        intros * Hn; cbn in Hn.
        unfold is_square_bmat.
        rewrite IHBMA; [ | flia | flia Hn | | | ]. {
          apply is_square_bmat_loop_mul. {
            rewrite Has; [ | flia | flia Hn ].
            apply Ha; [ flia | flia Hn ].
          } {
            rewrite Has; [ | flia | flia Hn ].
            rewrite Hss.
            apply Hb; [ flia Hn | flia ].
          }
        } {
          rewrite Has; [ | flia | flia Hn ].
          apply Ha; [ flia | flia Hn ].
        } {
          unfold is_square_bmat.
          rewrite Hbs; [ | flia Hn | flia ].
          apply Hb; [ flia Hn | flia ].
        } {
          rewrite Has; [ | flia | flia Hn ].
          rewrite Hbs; [ | flia Hn | flia ].
          easy.
        }
      } {
        intros n Hn.
        rewrite IHBMA; [ | flia | flia Hn | | | easy ]; cycle 1. {
          apply Ha; [ flia | flia Hn ].
        } {
          unfold is_square_bmat.
          apply Hb; [ flia Hn | flia ].
        }
        rewrite IHBMA; [ | flia | flia Hn | | | ]; cycle 1. {
          rewrite Has; [ | flia | flia Hn ].
          apply Ha; [ flia | flia Hn ].
        } {
          unfold is_square_bmat.
          rewrite Hbs; [ | flia Hn | flia ].
          apply Hb; [ flia Hn | flia ].
        } {
          rewrite Has; [ | flia | flia Hn ].
          rewrite Hbs; [ | flia Hn | flia ].
          easy.
        }
        symmetry; apply Has; [ flia | flia Hn ].
      }
    } {
      rewrite Has; [ | flia | flia ].
      apply Ha; flia.
    } {
      unfold is_square_bmat.
      rewrite Hbs; [ | flia | flia ].
      apply Hb; flia.
    } {
      rewrite Has; [ | flia | flia ].
      rewrite Hbs; [ | flia | flia ].
      easy.
    }
  }
  unfold is_square_bmat.
  clear - sp Hssab Ha Hss Hb IHBMA Has Hbs IHra.
  rewrite sizes_of_bmatrix_fold_left; [ | easy | | | ]; cycle 1. {
    unfold is_square_bmat.
    rewrite Hssab.
    apply is_square_bmat_loop_mul; [ apply Ha; flia | ].
    rewrite Hss; apply Hb; flia.
  } {
    intros * Hn.
    unfold is_square_bmat.
    rewrite IHBMA; [ | flia | flia Hn | | | ]; cycle 1. {
      rewrite Has; [ | flia | flia Hn ].
      apply Ha; [ flia | flia Hn ].
    } {
      unfold is_square_bmat.
      rewrite Hbs; [ | flia Hn | flia ].
      apply Hb; [ flia Hn | flia ].
    } {
      rewrite Has; [ | flia | flia Hn ].
      rewrite Hbs; [ | flia Hn | flia ].
      easy.
    }
    apply is_square_bmat_loop_mul. {
      rewrite Has; [ | flia | flia Hn ].
      apply Ha; [ flia | flia Hn ].
    } {
      rewrite Has; [ | flia | flia Hn ].
      rewrite Hss.
      apply Hb; [ flia Hn | flia ].
    }
  } {
    intros * Hn.
    rewrite Hssab.
    rewrite IHBMA; [ | flia | flia Hn | | | ]; cycle 1. {
      rewrite Has; [ | flia | flia Hn ].
      apply Ha; [ flia | flia Hn ].
    } {
      unfold is_square_bmat.
      rewrite Hbs; [ | flia Hn | flia ].
      apply Hb; [ flia Hn | flia ].
    } {
      rewrite Has; [ | flia | flia Hn ].
      rewrite Hbs; [ | flia Hn | flia ].
      easy.
    }
    symmetry.
    apply Has; [ flia | flia Hn ].
  }
  rewrite Hssab.
  apply IHra. {
    intros * Hi Hj H1 * Hbmb Hss'.
    apply IHBMA; [ flia Hi | flia Hj | easy | easy | easy ].
  } {
    intros i j Hi Hj.
    apply Ha; [ flia Hi | flia Hj ].
  } {
    intros i j Hi Hj.
    apply Hb; [ flia Hi | flia Hj ].
  } {
    intros i j Hi Hj.
    apply Has; [ flia Hi | flia Hj ].
  } {
    intros i j Hi Hj.
    apply Hbs; [ flia Hi | flia Hj ].
  }
  rewrite sizes_of_bmatrix_fold_left; [ easy | easy | | | ]. {
    unfold is_square_bmat.
    rewrite Hssab.
    apply is_square_bmat_loop_mul; [ apply Ha; flia | ].
    rewrite Hss; apply Hb; flia.
  } {
    intros * Hn.
    unfold is_square_bmat.
    rewrite IHBMA; [ | flia | flia Hn | | | ]; cycle 1. {
      rewrite Has; [ | flia | flia Hn ].
      apply Ha; [ flia | flia Hn ].
    } {
      unfold is_square_bmat.
      rewrite Hbs; [ | flia Hn | flia ].
      apply Hb; [ flia Hn | flia ].
    } {
      rewrite Has; [ | flia | flia Hn ].
      rewrite Hbs; [ | flia Hn | flia ].
      easy.
    }
    apply is_square_bmat_loop_mul. {
      rewrite Has; [ | flia | flia Hn ].
      apply Ha; [ flia | flia Hn ].
    } {
      rewrite Has; [ | flia | flia Hn ].
      rewrite Hss.
      apply Hb; [ flia Hn | flia ].
    }
  } {
    intros * Hn.
    rewrite Hssab.
    rewrite IHBMA; [ | flia | flia Hn | | | ]; cycle 1. {
      rewrite Has; [ | flia | flia Hn ].
      apply Ha; [ flia | flia Hn ].
    } {
      unfold is_square_bmat.
      rewrite Hbs; [ | flia Hn | flia ].
      apply Hb; [ flia Hn | flia ].
    } {
      rewrite Has; [ | flia | flia Hn ].
      rewrite Hbs; [ | flia Hn | flia ].
      easy.
    }
    symmetry.
    apply Has; [ flia | flia Hn ].
  }
}
Qed.

Theorem is_square_bmat_mul : ∀ T {so : semiring_op T} {sp : semiring_prop T},
  ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → is_square_bmat (BMA * BMB)%BM.
Proof.
intros * sp * Ha Hb Hab.
unfold is_square_bmat.
rewrite sizes_of_bmatrix_mul; [ | easy | easy | easy | easy ].
apply is_square_bmat_loop_mul; [ apply Ha | ].
rewrite Hab.
apply Hb.
Qed.

Theorem bmat_zero_like_mul : ∀ T {so : semiring_op T} {sp : semiring_prop T},
  ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → bmat_zero_like (BMA * BMB)%BM = bmat_zero_like BMA.
Proof.
intros * sp * Ha Hb Hab.
apply bmat_zero_like_eq_compat; [ easy | | easy | ]. {
  now apply is_square_bmat_mul.
}
now apply sizes_of_bmatrix_mul.
Qed.

Theorem bmat_zero_like_sqr : ∀ T {so : semiring_op T} {sp : semiring_prop T} BM,
  is_square_bmat BM
  → bmat_zero_like (BM * BM)%BM = bmat_zero_like BM.
Proof.
intros * sp * Hss.
now apply bmat_zero_like_mul.
Qed.

Theorem bmat_mul_0_l : ∀ T {so : semiring_op T} {sp : semiring_prop T} BM,
  is_square_bmat BM
  → (bmat_zero_like BM * BM)%BM = bmat_zero_like BM.
Proof.
intros * sp * Hss.
rewrite <- bmat_zero_like_mul_distr_l; [ | easy | easy ].
now apply bmat_zero_like_sqr.
Qed.

Theorem bmat_mul_0_r : ∀ T {so : semiring_op T} {sp : semiring_prop T} BM,
  is_square_bmat BM
  → (BM * bmat_zero_like BM)%BM = bmat_zero_like BM.
Proof.
intros * sp * Hss.
rewrite <- bmat_zero_like_mul_distr_r; [ | easy | ]. 2: {
  exists (sizes_of_bmatrix BM).
  split; intros BMA HBMA. {
    destruct HBMA as [| HBMA]; [ now subst BMA | ].
    destruct HBMA; [ now subst BMA | easy ].
  } {
    destruct HBMA as [| HBMA]; [ now subst BMA | ].
    destruct HBMA; [ now subst BMA | easy ].
  }
}
now apply bmat_zero_like_sqr.
Qed.

Theorem bmat_mul_Z_2_pow_l : ∀ T {so : semiring_op T } {sp : semiring_prop T},
  ∀ n M,
  bmat_fit_for_add (I_2_pow n) M
  → bmat_mul (Z_2_pow n) M = Z_2_pow n.
Proof.
intros * sp * Hss.
revert M Hss.
induction n; intros. {
cbn.
  destruct M as [xm| mm]; [ now cbn; rewrite srng_mul_0_l | easy ].
}
destruct M as [xm| mm]; [ easy | ].
cbn in Hss.
destruct Hss as (Hr & Hc & Hss).
cbn; f_equal.
rewrite <- Hc.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
specialize (Hss 0 0 Nat.lt_0_2 Nat.lt_0_2) as Hij00; cbn in Hij00.
specialize (Hss 0 1 Nat.lt_0_2 Nat.lt_1_2) as Hij01; cbn in Hij01.
specialize (Hss 1 0 Nat.lt_1_2 Nat.lt_0_2) as Hij10; cbn in Hij10.
specialize (Hss 1 1 Nat.lt_1_2 Nat.lt_1_2) as Hij11; cbn in Hij11.
destruct i. {
  destruct j. {
    rewrite IHn; [ cbn | easy ].
    rewrite IHn. 2: {
      transitivity (Z_2_pow n); [ | easy ].
      apply bmat_fit_for_add_IZ_IZ.
    }
    now apply old_bmat_add_0_l.
  }
  destruct j; [ cbn | flia Hj ].
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite IHn; [ | easy ].
  now apply old_bmat_add_0_l.
}
destruct i; [ cbn | flia Hi ].
destruct j. {
  rewrite IHn; [ | easy ].
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  now apply old_bmat_add_0_l.
}
destruct j; [ | flia Hj ].
rewrite IHn. 2: {
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite IHn; [ | easy ].
now apply old_bmat_add_0_l.
Qed.

Theorem bmat_mul_Z_2_pow_r : ∀ T {so : semiring_op T } {sp : semiring_prop T},
  ∀ n M,
  bmat_fit_for_add (I_2_pow n) M
  → bmat_mul M (Z_2_pow n) = Z_2_pow n.
Proof.
intros * sp * Hss.
revert M Hss.
induction n; intros. {
cbn.
  destruct M as [xm| mm]; [ now cbn; rewrite srng_mul_0_r | easy ].
}
destruct M as [xm| mm]; [ easy | ].
cbn in Hss.
destruct Hss as (Hr & Hc & Hss).
cbn; f_equal.
rewrite <- Hr, <- Hc.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
specialize (Hss 0 0 Nat.lt_0_2 Nat.lt_0_2) as Hij00; cbn in Hij00.
specialize (Hss 0 1 Nat.lt_0_2 Nat.lt_1_2) as Hij01; cbn in Hij01.
specialize (Hss 1 0 Nat.lt_1_2 Nat.lt_0_2) as Hij10; cbn in Hij10.
specialize (Hss 1 1 Nat.lt_1_2 Nat.lt_1_2) as Hij11; cbn in Hij11.
destruct i. {
  destruct j. {
    rewrite IHn; [ cbn | easy ].
    rewrite IHn. 2: {
      transitivity (Z_2_pow n); [ | easy ].
      apply bmat_fit_for_add_IZ_IZ.
    }
    now apply old_bmat_add_0_l.
  }
  destruct j; [ cbn | flia Hj ].
  rewrite IHn; [ | easy ].
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  now apply old_bmat_add_0_l.
}
destruct i; [ cbn | flia Hi ].
destruct j. {
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite IHn; [ | easy ].
  now apply old_bmat_add_0_l.
}
destruct j; [ | flia Hj ].
rewrite IHn. 2: {
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite IHn; [ | easy ].
now apply old_bmat_add_0_l.
Qed.

Theorem bmat_mul_1_l : ∀ T {so : semiring_op T } {sp : semiring_prop T} n M,
  bmat_fit_for_add (I_2_pow n) M
  → bmat_mul (I_2_pow n) M = M.
Proof.
intros * sp * Hss.
revert M Hss.
induction n; intros. {
  cbn.
  destruct M as [x| M]; [ now rewrite srng_mul_1_l | easy ].
}
cbn.
destruct M as [x| M]; [ easy | f_equal ].
cbn in Hss.
destruct Hss as (Hr & Hc & Hss).
rewrite <- Hc.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
rewrite <- Hc in Hj.
specialize (Hss 0 0 Nat.lt_0_2 Nat.lt_0_2) as Hij00; cbn in Hij00.
specialize (Hss 0 1 Nat.lt_0_2 Nat.lt_1_2) as Hij01; cbn in Hij01.
specialize (Hss 1 0 Nat.lt_1_2 Nat.lt_0_2) as Hij10; cbn in Hij10.
specialize (Hss 1 1 Nat.lt_1_2 Nat.lt_1_2) as Hij11; cbn in Hij11.
destruct i. {
  cbn.
  rewrite IHn. 2: {
    destruct j; [ easy | ].
    destruct j; [ | flia Hj ].
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite fold_Z_2_pow.
  rewrite bmat_mul_Z_2_pow_l; [ | easy | ]. 2: {
    destruct j. {
      transitivity (Z_2_pow n); [ | easy ].
      apply bmat_fit_for_add_IZ_IZ.
    }
    destruct j; [ easy | flia Hj ].
  }
  apply bmat_add_0_r; [ easy | ].
  destruct j. {
    transitivity (I_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  destruct j; [ | flia Hj ].
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
destruct i; [ cbn | flia Hi ].
rewrite fold_Z_2_pow.
rewrite bmat_mul_Z_2_pow_l; [ | easy | ]. 2: {
  destruct j; [ easy | ].
  destruct j; [ | flia Hj ].
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite IHn. 2: {
  destruct j. {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  destruct j; [ easy | flia Hj ].
}
apply old_bmat_add_0_l; [ easy | ].
destruct j; [ easy | ].
destruct j; [ | flia Hj ].
transitivity (I_2_pow n); [ | easy ].
apply bmat_fit_for_add_IZ_IZ.
Qed.

Theorem bmat_mul_1_r : ∀ T {so : semiring_op T } {sp : semiring_prop T} n M,
  bmat_fit_for_add (I_2_pow n) M
  → bmat_mul M (I_2_pow n) = M.
Proof.
intros * sp * Hss.
revert M Hss.
induction n; intros. {
  cbn.
  destruct M as [x| M]; [ now cbn; rewrite srng_mul_1_r | easy ].
}
destruct M as [x| M]; [ easy | cbn; f_equal ].
cbn in Hss.
destruct Hss as (Hr & Hc & Hss).
rewrite <- Hc; cbn.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
rewrite <- Hr in Hi.
rewrite <- Hc in Hj.
specialize (Hss 0 0 Nat.lt_0_2 Nat.lt_0_2) as Hij00; cbn in Hij00.
specialize (Hss 0 1 Nat.lt_0_2 Nat.lt_1_2) as Hij01; cbn in Hij01.
specialize (Hss 1 0 Nat.lt_1_2 Nat.lt_0_2) as Hij10; cbn in Hij10.
specialize (Hss 1 1 Nat.lt_1_2 Nat.lt_1_2) as Hij11; cbn in Hij11.
destruct i. {
  destruct j. {
    rewrite IHn; [ | easy ].
    rewrite fold_Z_2_pow.
    rewrite bmat_mul_Z_2_pow_r; [ | easy | ]. 2: {
      transitivity (Z_2_pow n); [ | easy ].
      apply bmat_fit_for_add_IZ_IZ.
    }
    apply bmat_add_0_r; [ easy | ].
    transitivity (I_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  destruct j; [ | flia Hj ].
  rewrite fold_Z_2_pow.
  rewrite bmat_mul_Z_2_pow_r; [ | easy | easy ].
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  now apply old_bmat_add_0_l.
}
destruct i; [ cbn | flia Hi ].
destruct j. {
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite fold_Z_2_pow.
  rewrite bmat_mul_Z_2_pow_r; [ | easy | easy ].
  now apply bmat_add_0_r.
}
destruct j; [ | flia Hj ].
rewrite fold_Z_2_pow.
rewrite bmat_mul_Z_2_pow_r; [ | easy | ]. 2: {
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite IHn; [ | easy ].
apply old_bmat_add_0_l; [ easy | ].
transitivity (I_2_pow n); [ | easy ].
apply bmat_fit_for_add_IZ_IZ.
Qed.

Theorem bmat_nat_mul_l_succ : ∀ T {so : semiring_op T}
    {sp : semiring_prop T} n M,
  bmat_nat_mul_l (S n) M = bmat_add (bmat_nat_mul_l n M) M.
Proof.
intros.
induction M as [x| M IHM] using bmatrix_ind2. {
  remember (S n) as sn; cbn; subst sn.
  f_equal.
  revert x.
  induction n; intros; [ easy | ].
  remember (S n) as sn; cbn; subst sn.
  rewrite <- (Nat.add_1_r n) at 1.
  rewrite seq_app; cbn.
  rewrite srng_add_0_l.
  apply fold_left_app.
}
cbn.
f_equal.
now apply matrix_eq.
Qed.

Theorem bmat_add_opp_r : ∀ T {ro : ring_op T} (so := rng_semiring)
    {rp : ring_prop T} {sp : semiring_prop T} M,
  bmat_add M (bmat_opp M) = bmat_zero_like M.
Proof.
intros * rp sp *.
induction M as [x| M IHM] using bmatrix_ind2; intros. {
  cbn.
  unfold so.
  rewrite fold_rng_sub.
  now rewrite rng_add_opp_r.
}
cbn; f_equal.
now apply matrix_eq.
Qed.

Theorem bmat_nat_mul_0_r : ∀ T {so : semiring_op T} {sp : semiring_prop T}
    k n,
  bmat_nat_mul_l k (Z_2_pow n) = Z_2_pow n.
Proof.
intros.
revert k.
induction n; intros. {
  cbn; f_equal.
  unfold rng_mul_nat_l.
  destruct k; [ easy | ].
  now apply all_0_srng_summation_0.
}
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
destruct i. {
  destruct j; [ easy | cbn ].
  destruct j; [ easy | flia Hj ].
}
destruct i; [ | flia Hi ].
destruct j; [ easy | cbn ].
destruct j; [ easy | flia Hj ].
Qed.

Theorem bmat_fit_for_add_add_l : ∀ T {so : semiring_op T} MA MB MC,
  bmat_fit_for_add MA MC
  → bmat_fit_for_add MB MC
  → bmat_fit_for_add (MA + MB)%BM MC.
Proof.
intros * Hssac Hssbc.
revert MA MB Hssac Hssbc.
induction MC as [xc| mc IHMC] using bmatrix_ind2; intros. {
  destruct MA; [ now destruct MB | easy ].
}
destruct MA as [xa| ma]; [ easy | ].
destruct MB as [xb| mb]; [ easy | ].
cbn in Hssac, Hssbc |-*.
destruct Hssac as (Hrac & Hcac & Hssac).
destruct Hssbc as (Hrbc & Hcbc & Hssbc).
split; [ easy | ].
split; [ easy | ].
intros * Hi Hj.
apply IHMC; [ | | now apply Hssac | ]. {
  now rewrite Hrac in Hi.
} {
  now rewrite Hcac in Hj.
} {
  apply Hssbc. {
    now rewrite Hrac, <- Hrbc in Hi.
  } {
    now rewrite Hcac, <- Hcbc in Hj.
  }
}
Qed.

Theorem bmat_add_add_swap :
  ∀ T (so : semiring_op T) {sp : semiring_prop T} MA MB MC,
  bmat_fit_for_add MA MB
  → bmat_fit_for_add MA MC
  → (MA + MB + MC = MA + MC + MB)%BM.
Proof.
intros * sp * Hssab Hssac.
revert MB MC Hssab Hssac.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  destruct MB as [xb| mb]; [ cbn | easy ].
  destruct MC as [xc| mc]; [ cbn | easy ].
  now rewrite srng_add_add_swap.
}
destruct MB as [xb| mb]; [ easy | ].
destruct MC as [xc| mc]; [ easy | cbn ].
f_equal.
apply matrix_eq; [ easy | easy | cbn ].
intros i j Hi Hj.
apply IHMA; [ easy | easy | now apply Hssab | now apply Hssac ].
Qed.

Theorem bmat_add_assoc :
  ∀ T (so : semiring_op T) {sp : semiring_prop T} MA MB MC,
  bmat_fit_for_add MA MB
  → bmat_fit_for_add MB MC
  → (MA + (MB + MC) = (MA + MB) + MC)%BM.
Proof.
intros * sp * Hssab Hssbc.
rewrite bmat_add_comm; [ | easy | ]. 2: {
  symmetry.
  apply bmat_fit_for_add_add_l; symmetry; [ easy | ].
  now transitivity MB.
}
rewrite (bmat_add_comm MA MB); [ | easy ].
apply bmat_add_add_swap; [ easy | easy | now symmetry ].
Qed.

Theorem square_bmat_fit_for_add : ∀ T sizes (MA MB : bmatrix T),
  is_square_bmat_loop sizes MA
  → is_square_bmat_loop sizes MB
  → bmat_fit_for_add MA MB.
Proof.
intros * Ha Hb.
revert MA MB Ha Hb.
induction sizes as [| size]; intros; [ now destruct MA, MB | ].
cbn in Ha, Hb.
destruct MA as [xa| ma]; [ easy | ].
destruct MB as [xb| mb]; [ easy | cbn ].
destruct Ha as (Hra & Hca & Ha).
destruct Hb as (Hrb & Hcb & Hb).
split; [ congruence | ].
split; [ congruence | ].
intros * Hi Hj.
apply IHsizes; [ apply Ha; congruence | apply Hb; congruence ].
Qed.

Theorem square_bmat_add : ∀ T {so : semiring_op T} MA MB sizes,
  is_square_bmat_loop sizes MA
  → is_square_bmat_loop sizes MB
  → is_square_bmat_loop sizes (MA + MB)%BM.
Proof.
intros * Ha Hb.
revert MA MB Ha Hb.
induction sizes as [| size]; intros; [ now destruct MA, MB | ].
cbn in Ha, Hb |-*.
destruct MA as [xa| ma]; [ easy | ].
destruct MB as [xb| mb]; [ easy | cbn ].
destruct Ha as (Hra & Hca & Ha).
destruct Hb as (Hrb & Hcb & Hb).
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
apply IHsizes; [ now apply Ha | now apply Hb ].
Qed.

Theorem square_bmat_fold_left : ∀ T {so : semiring_op T},
  ∀ (fa fb : nat → nat → bmatrix T) size sizes i j,
  (∀ MA MB,
   is_square_bmat_loop sizes MA
   → is_square_bmat_loop sizes MB
   → is_square_bmat_loop sizes (MA * MB)%BM)
  → (∀ j, j < S size → is_square_bmat_loop sizes (fa i j))
  → (∀ i, i < S size → is_square_bmat_loop sizes (fb i j))
  → is_square_bmat_loop sizes
       (fold_left (λ a k, (a + fa i (k + 1)%nat * fb (k + 1)%nat j)%BM) 
       (seq 0 size) (fa i 0 * fb 0 j)%BM).
Proof.
intros * IHsizes Ha Hb.
induction size. {
  apply IHsizes; [ apply Ha; flia | apply Hb; flia ].
}
rewrite <- (Nat.add_1_r size).
rewrite seq_app.
rewrite fold_left_app.
rewrite Nat.add_0_l.
unfold seq at 1.
unfold fold_left at 1.
apply square_bmat_add. 2: {
  apply IHsizes; [ apply Ha; flia | apply Hb; flia ].
}
apply IHsize. {
  intros k Hk; apply Ha; flia Hk.
} {
  intros k Hk; apply Hb; flia Hk.
}
Qed.

Theorem bmat_mul_add_distr_r :
  ∀ T (so : semiring_op T) {sp : semiring_prop T} (MA MB MC : bmatrix T),
  compatible_square_bmatrices [MA; MB; MC]
  → ((MA + MB) * MC = MA * MC + MB * MC)%BM.
Proof.
intros * sp * Hcsb.
revert MA MB Hcsb.
induction MC as [xc| mc IHMC] using bmatrix_ind2; intros. {
  destruct Hcsb as (sizes & Hsq & Hsz).
  unfold is_square_bmat in Hsq.
  destruct sizes as [| size]. 2: {
    specialize (Hsq _ (or_intror (or_intror (or_introl eq_refl)))).
    rewrite Hsz in Hsq; [ easy | now right; right; left ].
  }
  destruct MA as [xa| ma]. 2: {
    specialize (Hsq _ (or_introl eq_refl)).
    rewrite Hsz in Hsq; [ easy | now left ].
  }
  destruct MB as [xb| mb]. 2: {
    specialize (Hsq _ (or_intror (or_introl eq_refl))).
    rewrite Hsz in Hsq; [ easy | now right; left ].
  }
  now cbn; rewrite srng_mul_add_distr_r.
}
destruct Hcsb as (sizes & Hsq & Hsz).
destruct sizes as [| size]. {
  specialize (Hsq _ (or_intror (or_intror (or_introl eq_refl)))).
  unfold is_square_bmat in Hsq.
  rewrite Hsz in Hsq; [ easy | now right; right; left ].
}
destruct MA as [xa| ma]. {
  now specialize (Hsz _ (or_introl eq_refl)).
}
destruct MB as [xb| mb]; [ easy | ].
specialize (Hsq _ (or_introl eq_refl)) as Ha.
specialize (Hsq _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hsq _ (or_intror (or_intror (or_introl eq_refl)))) as Hc.
unfold is_square_bmat in Ha, Hb, Hc.
specialize (Hsz _ (or_introl eq_refl)) as Has.
specialize (Hsz _ (or_intror (or_introl eq_refl))) as Hbs.
specialize (Hsz _ (or_intror (or_intror (or_introl eq_refl)))) as Hcs.
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
destruct mc as (fc, rc, cc).
cbn - [ In ] in *.
rewrite Has in Ha; rewrite Hbs in Hb; rewrite Hcs in Hc.
cbn in Ha, Hb, Hc.
destruct Ha as (H1 & H2 & Ha); subst ra ca.
destruct Hb as (H1 & H2 & Hb); subst rb cb.
destruct Hc as (H1 & H2 & Hc); subst rc cc.
destruct size; [ easy | cbn in Has, Hbs, Hcs |-* ].
injection Has; clear Has; intros Has.
injection Hbs; clear Hbs; intros Hbs.
injection Hcs; clear Hcs; intros Hcs.
rewrite Nat.sub_0_r.
rewrite IHMC; [ | flia | easy | ]. 2: {
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  exists sizes.
  split. {
    intros BM HBM.
    unfold is_square_bmat.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia ].
      apply Ha; [ easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | flia ].
      apply Hb; [ easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia | easy ].
      apply Hc; [ flia | easy ].
    }
    easy.
  } {
    intros BM HBM.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ easy | easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ easy | easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ easy | flia | easy ].
    }
    easy.
  }
}
replace
  (fold_left
    (λ (acc : bmatrix T) (j0 : nat),
       (acc + (fa i (j0 + 1)%nat + fb i (j0 + 1)%nat) * fc (j0 + 1)%nat j)%BM)
    (seq 0 size) (fa i 0 * fc 0 j + fb i 0 * fc 0 j)%BM)
with
  (fold_left
    (λ (acc : bmatrix T) (j0 : nat),
       (acc +
        (fa i (j0 + 1)%nat * fc (j0 + 1)%nat j +
         fb i (j0 + 1)%nat * fc (j0 + 1)%nat j))%BM)
    (seq 0 size) (fa i 0 * fc 0 j + fb i 0 * fc 0 j)%BM). 2: {
  apply List_fold_left_ext_in.
  intros k M Hk.
  f_equal.
  apply in_seq in Hk.
  symmetry.
  apply IHMC; [ flia Hk | easy | ].
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  exists sizes.
  split. {
    intros BM HBM.
    unfold is_square_bmat.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia Hk ].
      apply Ha; [ easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | flia Hk ].
      apply Hb; [ easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hk | easy ].
      apply Hc; [ flia Hk | easy ].
    }
    easy.
  } {
    intros BM HBM.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ easy | easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ easy | easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ easy | flia Hk | easy ].
    }
    easy.
  }
}
assert (H : ∀ j, j < S size → is_square_bmat_loop sizes (fa i j)). {
  now intros; apply Ha.
}
move H before Ha; clear Ha; rename H into Ha.
assert (H : ∀ j, j < S size → is_square_bmat_loop sizes (fb i j)). {
  now intros; apply Hb.
}
move H before Hb; clear Hb; rename H into Hb.
assert (H : ∀ i, i < S size → is_square_bmat_loop sizes (fc i j)). {
  now intros; apply Hc.
}
move H before Hc; clear Hc; rename H into Hc.
move j before i.
clear Hi Hj IHMC Hsq Hsz.
induction size; [ easy | ].
rewrite List_seq_succ_r; cbn.
do 3 rewrite fold_left_app; cbn.
rewrite IHsize; cycle 1. {
  intros k Hk; apply Ha; flia Hk.
} {
  intros k Hk; apply Hb; flia Hk.
} {
  intros k Hk; apply Hc; flia Hk.
}
remember
  (fold_left (λ acc j0, acc + fa i (j0 + 1)%nat * fc (j0 + 1)%nat j)
     (seq 0 size) (fa i 0 * fc 0 j))%BM as x.
remember
  (fold_left (λ acc j0, acc + fb i (j0 + 1)%nat * fc (j0 + 1)%nat j)
     (seq 0 size) (fb i 0 * fc 0 j))%BM as y.
remember (fa i (size + 1)%nat) as u.
remember (fb i (size + 1)%nat) as v.
remember (fc (size + 1)%nat j) as w.
assert (Hx : is_square_bmat_loop sizes x). {
  subst x.
  apply square_bmat_fold_left; cycle 1. {
    intros k Hk; apply Ha; flia Hk.
  } {
    intros k Hk; apply Hc; flia Hk.
  }
  intros * HA HB.
  now apply is_square_bmat_loop_mul.
}
assert (Hy : is_square_bmat_loop sizes y). {
  subst y.
  apply square_bmat_fold_left; cycle 1. {
    intros k Hk; apply Hb; flia Hk.
  } {
    intros k Hk; apply Hc; flia Hk.
  }
  intros * HA HB.
  now apply is_square_bmat_loop_mul.
}
assert (Sxy : is_square_bmat_loop sizes (x + y)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Su : is_square_bmat_loop sizes u) by (subst u; apply Ha; flia).
assert (Sv : is_square_bmat_loop sizes v) by (subst v; apply Hb; flia).
assert (Sw : is_square_bmat_loop sizes w) by (subst w; apply Hc; flia).
assert (Suw : is_square_bmat_loop sizes (u * w)%BM). {
  now apply is_square_bmat_loop_mul.
}
assert (Svw : is_square_bmat_loop sizes (v * w)%BM). {
  now apply is_square_bmat_loop_mul.
}
assert (Syvw : is_square_bmat_loop sizes (y + v * w)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Hxy : bmat_fit_for_add x y). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hx_uw : bmat_fit_for_add x (u * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hx_yvw : bmat_fit_for_add x (y + v * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hy_vw : bmat_fit_for_add y (v * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hxy_vw : bmat_fit_for_add (x + y)%BM (v * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Huw_vw : bmat_fit_for_add (u * w)%BM (v * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
rewrite <- (bmat_add_add_swap _ _ (u * w)%BM); [ | easy | easy ].
rewrite (bmat_add_assoc x); [ | easy | easy ].
rewrite <- (bmat_add_assoc (x + y)%BM); [ | easy | now symmetry ].
f_equal.
now apply bmat_add_comm.
Qed.

Theorem bmat_mul_add_distr_l :
  ∀ T (so : semiring_op T) {sp : semiring_prop T} (MA MB MC : bmatrix T),
  compatible_square_bmatrices [MA; MB; MC]
  → (MA * (MB + MC) = MA * MB + MA * MC)%BM.
Proof.
intros * sp * Hcsb.
revert MB MC Hcsb.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  destruct Hcsb as (sizes & Hsq & Hsz).
  unfold is_square_bmat in Hsq.
  destruct sizes as [| size]. 2: {
    specialize (Hsq _ (or_introl eq_refl)).
    rewrite Hsz in Hsq; [ easy | now left ].
  }
  destruct MB as [xb| mb]. 2: {
    specialize (Hsq _ (or_intror (or_introl eq_refl))).
    rewrite Hsz in Hsq; [ easy | now right; left ].
  }
  destruct MC as [xc| mc]. 2: {
    specialize (Hsq _ (or_intror (or_intror (or_introl eq_refl)))).
    rewrite Hsz in Hsq; [ easy | now right; right; left ].
  }
  now cbn; rewrite srng_mul_add_distr_l.
}
destruct Hcsb as (sizes & Hsq & Hsz).
destruct sizes as [| size]. {
  specialize (Hsq _ (or_introl eq_refl)).
  unfold is_square_bmat in Hsq.
  rewrite Hsz in Hsq; [ easy | now left ].
}
destruct MB as [xb| mb]. {
  now specialize (Hsz _ (or_intror (or_introl eq_refl))).
}
destruct MC as [xc| mc]; [ easy | ].
specialize (Hsq _ (or_introl eq_refl)) as Ha.
specialize (Hsq _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hsq _ (or_intror (or_intror (or_introl eq_refl)))) as Hc.
unfold is_square_bmat in Ha, Hb, Hc.
specialize (Hsz _ (or_introl eq_refl)) as Has.
specialize (Hsz _ (or_intror (or_introl eq_refl))) as Hbs.
specialize (Hsz _ (or_intror (or_intror (or_introl eq_refl)))) as Hcs.
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
destruct mc as (fc, rc, cc).
cbn - [ In ] in *.
rewrite Has in Ha; rewrite Hbs in Hb; rewrite Hcs in Hc.
cbn in Ha, Hb, Hc.
destruct Ha as (H1 & H2 & Ha); subst ra ca.
destruct Hb as (H1 & H2 & Hb); subst rb cb.
destruct Hc as (H1 & H2 & Hc); subst rc cc.
destruct size; [ easy | cbn in Has, Hbs, Hcs |-* ].
injection Has; clear Has; intros Has.
injection Hbs; clear Hbs; intros Hbs.
injection Hcs; clear Hcs; intros Hcs.
rewrite Nat.sub_0_r.
rewrite IHMA; [ | easy | flia | ]. 2: {
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  exists sizes.
  split. {
    intros BM HBM.
    unfold is_square_bmat.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia ].
      apply Ha; [ easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | flia | easy ].
      apply Hb; [ flia | easy ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia | easy ].
      apply Hc; [ flia | easy ].
    }
    easy.
  } {
    intros BM HBM.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ easy | easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ easy | flia | easy ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ easy | flia | easy ].
    }
    easy.
  }
}
replace
  (fold_left
    (λ (acc : bmatrix T) (j0 : nat),
       (acc + fa i (j0 + 1)%nat * (fb (j0 + 1)%nat j + fc (j0 + 1)%nat j))%BM)
    (seq 0 size) (fa i 0 * fb 0 j + fa i 0 * fc 0 j)%BM)
with
  (fold_left
    (λ (acc : bmatrix T) (j0 : nat),
       (acc +
        (fa i (j0 + 1)%nat * fb (j0 + 1)%nat j +
         fa i (j0 + 1)%nat * fc (j0 + 1)%nat j))%BM)
    (seq 0 size) (fa i 0 * fb 0 j + fa i 0 * fc 0 j)%BM). 2: {
  apply List_fold_left_ext_in.
  intros k M Hk.
  f_equal.
  apply in_seq in Hk.
  symmetry.
  apply IHMA; [ easy | flia Hk | ].
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  exists sizes.
  split. {
    intros BM HBM.
    unfold is_square_bmat.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia Hk ].
      apply Ha; [ easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | flia Hk | easy ].
      apply Hb; [ flia Hk | easy ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hk | easy ].
      apply Hc; [ flia Hk | easy ].
    }
    easy.
  } {
    intros BM HBM.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ easy | easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ easy | flia Hk | easy ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ easy | flia Hk | easy ].
    }
    easy.
  }
}
assert (H : ∀ j, j < S size → is_square_bmat_loop sizes (fa i j)). {
  now intros; apply Ha.
}
move H before Ha; clear Ha; rename H into Ha.
assert (H : ∀ i, i < S size → is_square_bmat_loop sizes (fb i j)). {
  now intros; apply Hb.
}
move H before Hb; clear Hb; rename H into Hb.
assert (H : ∀ i, i < S size → is_square_bmat_loop sizes (fc i j)). {
  now intros; apply Hc.
}
move H before Hc; clear Hc; rename H into Hc.
move j before i.
clear Hi Hj IHMA Hsq Hsz.
induction size; [ easy | ].
rewrite List_seq_succ_r; cbn.
do 3 rewrite fold_left_app; cbn.
rewrite IHsize; cycle 1. {
  intros k Hk; apply Ha; flia Hk.
} {
  intros k Hk; apply Hb; flia Hk.
} {
  intros k Hk; apply Hc; flia Hk.
}
remember
  (fold_left (λ acc j0, acc + fa i (j0 + 1)%nat * fb (j0 + 1)%nat j)
     (seq 0 size) (fa i 0 * fb 0 j))%BM as x.
remember
  (fold_left (λ acc j0, acc + fa i (j0 + 1)%nat * fc (j0 + 1)%nat j)
     (seq 0 size) (fa i 0 * fc 0 j))%BM as y.
remember (fa i (size + 1)%nat) as u.
remember (fb (size + 1)%nat j) as v.
remember (fc (size + 1)%nat j) as w.
assert (Hx : is_square_bmat_loop sizes x). {
  subst x.
  apply square_bmat_fold_left; cycle 1. {
    intros k Hk; apply Ha; flia Hk.
  } {
    intros k Hk; apply Hb; flia Hk.
  }
  intros * HA HB.
  now apply is_square_bmat_loop_mul.
}
assert (Hy : is_square_bmat_loop sizes y). {
  subst y.
  apply square_bmat_fold_left; cycle 1. {
    intros k Hk; apply Ha; flia Hk.
  } {
    intros k Hk; apply Hc; flia Hk.
  }
  intros * HA HB.
  now apply is_square_bmat_loop_mul.
}
assert (Sxy : is_square_bmat_loop sizes (x + y)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Su : is_square_bmat_loop sizes u) by (subst u; apply Ha; flia).
assert (Sv : is_square_bmat_loop sizes v) by (subst v; apply Hb; flia).
assert (Sw : is_square_bmat_loop sizes w) by (subst w; apply Hc; flia).
assert (Suv : is_square_bmat_loop sizes (u * v)%BM). {
  now apply is_square_bmat_loop_mul.
}
assert (Suw : is_square_bmat_loop sizes (u * w)%BM). {
  now apply is_square_bmat_loop_mul.
}
assert (Syuw : is_square_bmat_loop sizes (y + u * w)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Hxy : bmat_fit_for_add x y). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hx_uv : bmat_fit_for_add x (u * v)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hx_yuw : bmat_fit_for_add x (y + u * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hy_uw : bmat_fit_for_add y (u * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hxy_uw : bmat_fit_for_add (x + y)%BM (u * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Huw_uv : bmat_fit_for_add (u * w)%BM (u * v)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
rewrite <- (bmat_add_add_swap _ _ (u * v)%BM); [ | easy | easy ].
rewrite (bmat_add_assoc x); [ | easy | easy ].
rewrite <- (bmat_add_assoc (x + y)%BM); [ | easy | easy ].
f_equal.
now apply bmat_add_comm.
Qed.

Theorem is_square_bmat_loop_opp : ∀ T {ro : ring_op T} (M : bmatrix T) sizes,
  is_square_bmat_loop sizes M → is_square_bmat_loop sizes (- M)%BM.
Proof.
intros * HM.
revert M HM.
induction sizes as [| size]; intros; [ now destruct M | ].
cbn in HM |-*.
destruct M as [x| M]; [ easy | cbn ].
destruct HM as (Hr & Hc & HM).
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
now apply IHsizes, HM.
Qed.

Theorem sizes_of_bmatrix_opp : ∀ T {ro : ring_op T} (M : bmatrix T),
  sizes_of_bmatrix (- M)%BM = sizes_of_bmatrix M.
Proof.
intros *.
induction M as [x| M IHBM] using bmatrix_ind2; [ easy | cbn ].
destruct (zerop (mat_nrows M)) as [Hrz| Hrz]; [ easy | cbn ].
destruct (zerop (mat_ncols M)) as [Hcz| Hcz]; [ easy | cbn ].
f_equal.
now apply IHBM.
Qed.

Theorem is_square_bmat_opp : ∀ T {ro : ring_op T} (M : bmatrix T),
  is_square_bmat M → is_square_bmat (- M)%BM.
Proof.
intros * HM.
apply is_square_bmat_loop_opp.
unfold is_square_bmat in HM.
now rewrite sizes_of_bmatrix_opp.
Qed.

Theorem bmat_add_move_l :
  ∀ T {ro : ring_op T} (so := rng_semiring) {sp : semiring_prop T}
     {rp : ring_prop T} MA MB MC,
  compatible_square_bmatrices [MA; MB; MC]
  → (MA + MB)%BM = MC
  → MB = (MC - MA)%BM.
Proof.
intros * sp rp * Hcsb Hab.
rewrite <- Hab.
unfold bmat_sub.
destruct Hcsb as (sizes & Hsq & Hsz).
rewrite bmat_add_add_swap; [ | easy | | ]; cycle 1. {
  apply (square_bmat_fit_for_add (sizes_of_bmatrix MA)). {
    now apply Hsq; left.
  } {
    specialize (Hsq _ (or_intror (or_introl eq_refl))) as H.
    rewrite Hsz; [ | now left ].
    rewrite <- (Hsz MB); [ | now right; left ].
    now apply Hsq; right; left.
  }
} {
  apply (square_bmat_fit_for_add (sizes_of_bmatrix MA)). {
    now apply Hsq; left.
  } {
    specialize (Hsq _ (or_introl eq_refl)) as H.
    apply is_square_bmat_loop_opp.
    now apply Hsq; left.
  }
}
unfold so.
rewrite bmat_add_opp_r; [ | easy | easy ].
symmetry.
rewrite (bmat_zero_like_eq_compat _ MB); cycle 1. {
  now apply Hsq; left.
} {
  now apply Hsq; right; left.
} {
  rewrite Hsz; [ | now left ].
  rewrite Hsz; [ | now right; left ].
  easy.
}
apply bmat_add_0_l; [ easy | ].
now apply Hsq; right; left.
Qed.

Theorem bmat_zero_like_opp :
  ∀ T {ro : ring_op T} (so := rng_semiring) {sp : semiring_prop T}
     {rp : ring_prop T} MA,
  is_square_bmat MA
  → bmat_zero_like (- MA)%BM = bmat_zero_like MA.
Proof.
intros * sp rp * Ha.
induction MA as [xa| ma IHMA] using bmatrix_ind2; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
apply IHMA; [ easy | easy | ].
cbn in Ha.
destruct (zerop (mat_nrows ma)) as [Hrz| Hrz]; [ flia Hrz Hi | ].
destruct (zerop (mat_ncols ma)) as [Hcz| Hcz]; [ flia Hcz Hj | ].
cbn in Ha.
destruct Ha as (_ & Hrc & Ha).
unfold is_square_bmat.
rewrite Hrc in Hj.
rewrite (@sizes_of_bmatrix_at_0_0 T so) with (r := mat_nrows ma); try easy.
now apply Ha.
Qed.

Theorem bmat_add_move_0_l :
  ∀ T {ro : ring_op T} (so := rng_semiring) {sp : semiring_prop T}
     {rp : ring_prop T} MA MB,
  compatible_square_bmatrices [MA; MB]
  → (MA + MB)%BM = bmat_zero_like MA
  → MB = (- MA)%BM.
Proof.
intros * sp rp * Hcsb Hab.
apply bmat_add_move_l in Hab; [ | easy | easy | ]. 2: {
  destruct Hcsb as (sizes & Hsq & Hsz).
  exists sizes.
  split. {
    intros * HBM.
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsq; left | ].
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsq; right; left | ].
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    now apply square_bmat_zero_like, Hsq; left.
  } {
    intros * HBM.
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsz; left | ].
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsz; right; left | ].
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    rewrite sizes_of_bmat_zero_like.
    now apply Hsz; left.
  }
}
unfold bmat_sub in Hab.
unfold so in Hab.
rewrite <- bmat_zero_like_opp in Hab; [ | easy | easy | ]. 2: {
  destruct Hcsb as (size & Hsq & Hsz).
  now apply Hsq; left.
}
rewrite bmat_add_0_l in Hab; [ easy | easy | ].
apply is_square_bmat_opp.
destruct Hcsb as (sizes & Hsq & Hsz).
now apply Hsq; left.
Qed.

Theorem bmat_mul_opp_l :
  ∀ T {ro : ring_op T} (so := rng_semiring) (rp : ring_prop T)
    (sp : semiring_prop T),
  ∀ MA MB,
  compatible_square_bmatrices [MA; MB]
  → ((- MA) * MB = - (MA * MB))%BM.
Proof.
intros * rp sp * Hcsb.
specialize (@bmat_mul_add_distr_r T so sp MA (bmat_opp MA) MB) as H1.
destruct Hcsb as (sizes & Hsq & Hsz).
specialize (Hsq _ (or_introl eq_refl)) as Ha.
specialize (Hsq _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hsz _ (or_introl eq_refl)) as Has.
specialize (Hsz _ (or_intror (or_introl eq_refl))) as Hbs.
generalize Ha; intros Hao.
apply (@is_square_bmat_opp _ ro) in Hao.
generalize Has; intros Haso.
rewrite <- (@sizes_of_bmatrix_opp _ ro) in Haso.
assert (H : compatible_square_bmatrices [MA; (- MA)%BM; MB]). {
  exists sizes.
  split; intros BM HBM. {
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | easy ].
  } {
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | easy ].
  }
}
specialize (H1 H); clear H.
unfold so in H1.
rewrite bmat_add_opp_r in H1; [ | easy | easy ].
assert (Hss : sizes_of_bmatrix MA = sizes_of_bmatrix MB). {
  now rewrite Has, Hbs.
}
assert (Hab : bmat_zero_like MA = bmat_zero_like MB). {
  now rewrite (bmat_zero_like_eq_compat _ MB).
}
unfold so in Hab.
rewrite Hab in H1.
rewrite bmat_mul_0_l in H1; [ | easy | easy ].
symmetry in H1.
rewrite <- Hab in H1.
rewrite (bmat_zero_like_eq_compat _ MB) in H1; [ | easy | easy | easy ].
rewrite <- Hab in H1.
rewrite <- (bmat_zero_like_mul _ MB) in H1; [ | easy | easy | easy ].
apply bmat_add_move_0_l in H1; [ easy | easy | easy | ].
exists sizes.
split; intros BM HBM. {
  destruct HBM as [HBM| HBM]; [ subst BM | ]. {
    now apply is_square_bmat_mul.
  }
  destruct HBM as [HBM| HBM]; [ subst BM | easy ].
  apply is_square_bmat_mul; [ easy | easy | easy | ].
  now rewrite Haso, Hbs.
} {
  destruct HBM as [HBM| HBM]; [ subst BM | ]. {
    now rewrite sizes_of_bmatrix_mul.
  } {
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    rewrite sizes_of_bmatrix_mul; [ easy | easy | easy | easy | ].
    now rewrite sizes_of_bmatrix_opp.
  }
}
Qed.

Theorem bmat_mul_opp_r :
  ∀ T {ro : ring_op T} (so := rng_semiring) (rp : ring_prop T)
    (sp : semiring_prop T),
  ∀ MA MB,
  compatible_square_bmatrices [MA; MB]
  → (MA * (- MB) = - (MA * MB))%BM.
Proof.
intros * rp sp * Hcsb.
specialize (@bmat_mul_add_distr_l T so sp MA MB (bmat_opp MB)) as H1.
destruct Hcsb as (sizes & Hsq & Hsz).
specialize (Hsq _ (or_introl eq_refl)) as Ha.
specialize (Hsq _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hsz _ (or_introl eq_refl)) as Has.
specialize (Hsz _ (or_intror (or_introl eq_refl))) as Hbs.
generalize Hb; intros Hbo.
apply (@is_square_bmat_opp _ ro) in Hbo.
generalize Hbs; intros Hbso.
rewrite <- (@sizes_of_bmatrix_opp _ ro) in Hbso.
assert (H : compatible_square_bmatrices [MA; MB; (- MB)%BM]). {
  exists sizes.
  split; intros BM HBM. {
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | easy ].
  } {
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | easy ].
  }
}
specialize (H1 H); clear H.
unfold so in H1.
rewrite bmat_add_opp_r in H1; [ | easy | easy ].
assert (Hss : sizes_of_bmatrix MA = sizes_of_bmatrix MB). {
  now rewrite Has, Hbs.
}
assert (Hab : bmat_zero_like MA = bmat_zero_like MB). {
  now rewrite (bmat_zero_like_eq_compat _ MB).
}
unfold so in Hab.
rewrite <- Hab in H1.
rewrite bmat_mul_0_r in H1; [ | easy | easy ].
symmetry in H1.
rewrite (bmat_zero_like_eq_compat _ MB) in H1; [ | easy | easy | easy ].
rewrite <- Hab in H1.
rewrite <- (bmat_zero_like_mul _ MB) in H1; [ | easy | easy | easy ].
apply bmat_add_move_0_l in H1; [ easy | easy | easy | ].
exists sizes.
split; intros BM HBM. {
  destruct HBM as [HBM| HBM]; [ subst BM | ]. {
    now apply is_square_bmat_mul.
  }
  destruct HBM as [HBM| HBM]; [ subst BM | easy ].
  apply is_square_bmat_mul; [ easy | easy | easy | ].
  congruence.
} {
  destruct HBM as [HBM| HBM]; [ subst BM | ]. {
    now rewrite sizes_of_bmatrix_mul.
  } {
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    rewrite sizes_of_bmatrix_mul; [ easy | easy | easy | easy | ].
    now rewrite sizes_of_bmatrix_opp.
  }
}
Qed.

Theorem bmat_mul_opp_opp :
  ∀ T {ro : ring_op T} (so := rng_semiring)
       {sp : semiring_prop T} {rp : ring_prop T} MA MB,
  compatible_square_bmatrices [MA; MB]
  → (- MA * - MB = MA * MB)%BM.
Proof.
intros * sp rp * Hab.
subst so.
rewrite bmat_mul_opp_l; [ | easy | easy | ]. 2: {
  destruct Hab as (sizes & Hsq & Hsz).
  exists sizes.
  split; intros BM HBM. {
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsq; left | ].
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    now apply is_square_bmat_opp, Hsq; right; left.
  } {
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsz; left | ].
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    now rewrite sizes_of_bmatrix_opp; apply Hsz; right; left.
  }
}
rewrite bmat_mul_opp_r; [ | easy | easy | easy ].
now rewrite bmat_opp_involutive.
Qed.

Theorem bmat_mul_sqr_opp :
  ∀ T {ro : ring_op T} (so := rng_semiring)
       {sp : semiring_prop T} {rp : ring_prop T} M,
  is_square_bmat M
  → (- M * - M = M * M)%BM.
Proof.
intros * sp rp * HM.
apply bmat_mul_opp_opp; [ easy | easy | ].
exists (sizes_of_bmatrix M).
split; intros BM HBM. {
  replace BM with M; [ easy | ].
  destruct HBM as [| HBM]; [ easy | now destruct HBM ].
} {
  replace BM with M; [ easy | ].
  destruct HBM as [| HBM]; [ easy | now destruct HBM ].
}
Qed.

Theorem bmat_fit_for_add_Z_2_pow_bmat_nat_mul_l :
  ∀ T {ro : ring_op T} (so := rng_semiring) {sp : semiring_prop T} n,
  bmat_fit_for_add (Z_2_pow n) (bmat_nat_mul_l n (Z_2_pow n)).
Proof.
intros.
induction n; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
rewrite bmat_nat_mul_l_succ; [ | easy ].
destruct i; cbn. {
  destruct j; cbn. {
    symmetry.
    now apply bmat_fit_for_add_add_l; symmetry.
  }
  destruct j; [ | flia Hj ].
  symmetry.
  now apply bmat_fit_for_add_add_l; symmetry.
}
destruct i; [ | flia Hi ].
destruct j; cbn. {
  symmetry.
  now apply bmat_fit_for_add_add_l; symmetry.
}
destruct j; [ | flia Hj ]. {
  symmetry.
  now apply bmat_fit_for_add_add_l; symmetry.
}
Qed.

Theorem bmat_zero_like_IZ_eq_Z :
  ∀ T {ro : ring_op T} (so := rng_semiring),
  ∀ u n, bmat_zero_like (IZ_2_pow u n) = Z_2_pow n.
Proof.
intros.
revert u.
induction n; intros; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
destruct i; cbn. {
  destruct j; cbn; [ easy | ].
  destruct j; [ easy | flia Hj ].
}
destruct i; [ cbn | flia Hi ].
destruct j; cbn; [ easy | ].
destruct j; [ easy | flia Hj ].
Qed.

Theorem sizes_of_bmatrix_A : ∀ T {ro : ring_op T} n,
  sizes_of_bmatrix (A n) = repeat 2 n.
Proof.
intros.
induction n; [ easy | now cbn; f_equal ].
Qed.

Theorem sizes_of_bmatrix_IZ : ∀ T {ro : ring_op T} (so := rng_semiring) n u,
  sizes_of_bmatrix (IZ_2_pow u n) = repeat 2 n.
Proof.
intros.
induction n; [ easy | now cbn; f_equal ].
Qed.

Theorem IZ_is_square_bmat : ∀ T {ro : ring_op T} (so := rng_semiring) n u,
  is_square_bmat (IZ_2_pow u n).
Proof.
intros.
revert u.
induction n; intros; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
destruct i; cbn. {
  destruct j; [ apply IHn | cbn ].
  destruct j; [ | flia Hj ].
  unfold so.
  rewrite sizes_of_bmatrix_IZ.
  rewrite <- (sizes_of_bmatrix_IZ n 0%Srng).
  apply IHn.
}
destruct i; [ | flia Hi ].
destruct j; cbn. {
  unfold so.
  rewrite sizes_of_bmatrix_IZ.
  rewrite <- (sizes_of_bmatrix_IZ n 0%Srng).
  apply IHn.
}
destruct j; [ | flia Hj ].
apply IHn.
Qed.

Theorem A_is_square_bmat : ∀ T {ro : ring_op T} (so := rng_semiring) n,
  is_square_bmat (A n).
Proof.
intros.
induction n; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
destruct i; cbn. {
  destruct j; [ easy | cbn ].
  destruct j; [ | flia Hj ].
  rewrite sizes_of_bmatrix_A.
  rewrite <- (sizes_of_bmatrix_IZ n 1%Srng).
  apply IZ_is_square_bmat.
}
destruct i; [ cbn | flia Hi ].
destruct j; cbn. {
  rewrite sizes_of_bmatrix_A.
  rewrite <- (sizes_of_bmatrix_IZ n 1%Srng).
  apply IZ_is_square_bmat.
}
destruct j; [ | flia Hj ].
apply is_square_bmat_loop_opp.
apply IHn.
Qed.

Theorem bmat_zero_like_A_eq_Z :
  ∀ T {ro : ring_op T} (so := rng_semiring)
     {rp : ring_prop T} {sp : semiring_prop T},
  ∀ n, bmat_zero_like (A n) = Z_2_pow n.
Proof.
intros.
induction n; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
destruct i; cbn. {
  destruct j; cbn; [ easy | ].
  destruct j; [ cbn | flia Hj ].
  apply bmat_zero_like_IZ_eq_Z.
}
destruct i; [ cbn | flia Hi ].
destruct j; cbn. {
  apply bmat_zero_like_IZ_eq_Z.
}
destruct j; [ | flia Hj ].
unfold so.
rewrite bmat_zero_like_opp; [ easy | easy | easy | ].
apply A_is_square_bmat.
Qed.

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I :
    ∀ T {ro : ring_op T} (so := rng_semiring),
    ∀ {rp : ring_prop T} {sp : semiring_prop T} n,
  (A n * A n = bmat_nat_mul_l n (I_2_pow n))%BM.
Proof.
intros.
induction n; intros; [ now cbn; rewrite srng_mul_0_l | ].
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
destruct i. {
  destruct j. {
    cbn; rewrite IHn; symmetry.
    rewrite bmat_nat_mul_l_succ; [ | easy ].
    now rewrite bmat_mul_1_r.
  }
  destruct j; [ cbn | flia Hj ].
  rewrite bmat_nat_mul_l_succ; [ | easy ].
  rewrite bmat_mul_1_r; [ | easy | ]. 2: {
    unfold I_2_pow.
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_mul_1_l; [ | easy | ]. 2: {
    unfold I_2_pow.
    transitivity (A n); [ apply bmat_fit_for_add_IZ_A | ].
    apply bmat_fit_for_add_opp_r.
  }
  unfold so.
  rewrite bmat_add_opp_r; [ | easy | easy ].
  rewrite fold_Z_2_pow.
  rewrite bmat_add_0_r; [ | easy | ]. 2: {
    now apply bmat_fit_for_add_Z_2_pow_bmat_nat_mul_l.
  }
  rewrite bmat_nat_mul_0_r; [ | easy ].
  now apply bmat_zero_like_A_eq_Z.
}
destruct i; [ | flia Hi ].
destruct j; cbn. {
  rewrite bmat_mul_1_l; [ | easy | ]. 2: {
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_mul_1_r; [ | easy | ]. 2: {
    transitivity (A n); [ | apply bmat_fit_for_add_opp_r ].
    apply bmat_fit_for_add_IZ_A.
  }
  unfold so.
  rewrite bmat_add_opp_r; [ | easy | easy ].
  rewrite bmat_nat_mul_l_succ; [ | easy ].
  rewrite fold_Z_2_pow.
  rewrite bmat_nat_mul_0_r; [ | easy ].
  rewrite bmat_add_0_r; [ | easy | easy ].
  now apply bmat_zero_like_A_eq_Z.
}
destruct j; [ cbn | flia Hj ].
rewrite bmat_mul_1_l; [ | easy | easy ].
unfold so.
rewrite bmat_mul_sqr_opp; [ | easy | easy | apply A_is_square_bmat ].
rewrite bmat_nat_mul_l_succ; [ | easy ].
unfold so in IHn.
rewrite <- IHn.
apply bmat_add_comm; [ easy | ].
transitivity (A n). 2: {
  apply (square_bmat_fit_for_add (sizes_of_bmatrix (A n))). {
    apply A_is_square_bmat.
  }
  apply is_square_bmat_loop_mul; apply A_is_square_bmat.
}
apply bmat_fit_for_add_IZ_A.
Qed.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
(* marche pas
Context (so := rng_semiring).
*)
Context {sp : @semiring_prop T (@rng_semiring T ro)}.
Context {rp : @ring_prop T ro}.

(* block matrix trace *)

Fixpoint Tr (so := rng_semiring) (BM : bmatrix T) :=
  match BM with
  | BM_1 x => x
  | BM_M M => (Σ (i = 0, mat_nrows M - 1), Tr (mat_el M i i))%Srng
  end.

(*
Require Import ZArith.
Compute (let ro := Z_ring_op in let so := rng_semiring in Tr (I_2_pow 3)).
Compute (let ro := Z_ring_op in let so := rng_semiring in Tr (I_2_pow 4)).
Compute (let ro := Z_ring_op in let so := rng_semiring in Tr (A 3)).
*)

Theorem Tr_opp : ∀ (so := rng_semiring) BM,
  is_square_bmat BM
  → Tr (- BM)%BM = (- Tr BM)%Rng.
Proof.
intros * so * HBM.
induction BM as [x| M IHBM] using bmatrix_ind2; [ easy | ].
cbn - [ seq "-" ].
cbn in HBM.
destruct (zerop (mat_nrows M)) as [Hrz| Hrz]; [ easy | ].
destruct (zerop (mat_ncols M)) as [Hcz| Hcz]; [ easy | ].
cbn in HBM.
rewrite rng_opp_summation; [ | easy | easy ].
cbn.
rewrite IHBM; [ | easy | easy | now apply HBM ].
rewrite srng_add_0_l.
apply List_fold_left_ext_in.
intros i x Hi.
apply in_seq in Hi.
f_equal.
destruct HBM as (_ & Hcr & HBM).
apply IHBM; [ flia Hi | flia Hi Hcr | ].
unfold is_square_bmat.
rewrite (@sizes_of_bmatrix_at_0_0 T so) with (r := mat_nrows M);
  [ | easy | easy | flia Hi | flia Hcr Hi ].
apply HBM; flia Hi.
Qed.

Theorem Tr_A : ∀ (so := rng_semiring) n, Tr (A n) = 0%Srng.
Proof.
intros.
induction n; [ easy | cbn ].
rewrite IHn.
do 2 rewrite srng_add_0_l.
unfold so.
rewrite Tr_opp; [ | apply A_is_square_bmat ].
rewrite IHn.
apply rng_opp_0.
Qed.

...

End in_ring.

...

Definition charac_polyn {A} {n : nat} (M : matrix A) := det (M - x * I).

...

(* testing... *)

Compute (Δ full_cube, Nat.sqrt 3).
Compute (2 ^ (3 - 1) + 1).

Compute (length (sg_edges full_cube)).
Compute (vdeg (edges cube_vert) 0).

Compute (edges [1; 2; 4; 7]).
Compute (length (edges [1; 2; 4; 7])).
Compute (2 ^ (3 - 1) + 1).

Compute (vΔ [0; 1; 4; 5; 7]).
Compute (edges [0; 1; 4; 5; 7]).

Compute (edges [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (vΔ [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (2 ^ (4 - 1) + 1).
Compute (Nat.sqrt 4).
Compute (let n := 4 in 2 ^ (n - 1) + 1).
Compute (map (λ i, vΔ [0; 3; 5; 6; 9; 10; 12; 15; i]) (seq 0 16)).
Compute (let n := 4 in Nat.sqrt n).
Compute (let n := 3 in 2 ^ (n - 1) + 1).
Compute (map (λ i, (i, vΔ [0; 3; 5; 6; i])) (seq 0 8)).
Compute (let n := 3 in Nat.sqrt n).

Compute (edges [0; 3; 5; 6]).
Compute (edges [0; 3; 5; 6; 2]).
Compute (vdeg (edges [0; 3; 5; 6; 1])) 1.

Compute (Nat.sqrt 5).
Compute (let n := 5 in 2 ^ (n - 1) + 1).
Compute (length [0; 3; 5; 6; 9; 10; 12; 15; 17; 18; 20; 23; 24; 27; 29; 30]).
Compute (edges [0; 3; 5; 6; 9; 10; 12; 15; 17; 18; 20; 23; 24; 27; 29; 30]).
Compute (map (λ i, vΔ [0; 3; 5; 6; 9; 10; 12; 15; 17; 18; 20; 23; 24; 27; 29; 30; i]) (seq 0 32)).

Compute (Nat.sqrt 4).
Compute (let n := 4 in 2 ^ (n - 1) + 1). (* 9 *)
Compute (length [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (edges [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (map (λ i, vΔ [0; 3; 5; 6; 9; 10; 12; 15; i]) (seq 0 16)).

Compute (vΔ [0; 1; 6; 7; 10; 11; 12; 13]).
Compute (map (λ i, vΔ [0; 1; 6; 7; 10; 11; 12; 13; i]) (seq 0 16)).

Compute (Nat.sqrt 2).
Compute (let n := 2 in 2 ^ (n - 1) + 1).
Compute (length [0; 3]).

Compute (Nat.sqrt 3).
Compute (let n := 3 in 2 ^ (n - 1) + 1).
Compute (length [0; 3; 5; 6]).
Compute (edges [0; 3; 5; 6]).
Compute (map (λ i, vΔ [0; 3; 5; 6; i]) (seq 0 8)).
Compute (map (λ i, vΔ [0; 1; 2; 4; i]) (seq 0 8)).

Compute (map (λ i, vΔ [0; 1; 6; 7; i]) (seq 0 8)).
Compute (vΔ [0; 1; 6; 7]).
Compute (edges [0; 1; 2; 4]).

(* The theorem *)

Theorem sensitivity : ∀ sg n,
  number_of_vertices sg = 2 ^ (n - 1) + 1
  → Δ sg ≥ Nat.sqrt n.
Proof.
...
