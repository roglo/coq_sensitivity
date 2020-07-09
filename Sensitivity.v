(* Sensitivity Theorem proved by Hao Huang.
   https://arxiv.org/pdf/1907.00847.pdf
   https://eccc.weizmann.ac.il/report/2020/002/?fbclid=IwAR19mpxfIuoSaWq3HO8MdV8i8x_xlvwMKHjfElzBUK0GditlyaLeJiC8gJY *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
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

(*
Add LoadPath "../../math-comp/master".
From mathcomp Require Import all_algebra.
(*
Set Implicit Arguments.
*)
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Check poly.
Print ringType.
Print GRing.Ring.type.
*)

Require Import Semiring SRsummation.

(* matrices *)

Record matrix T := mk_mat
  { mat_list : list (list T);
    mat_nrows : nat;
    mat_ncols : nat }.

Definition list_list_nrows T (ll : list (list T)) :=
  length ll.

Definition list_list_ncols T (ll : list (list T)) :=
  length (hd [] ll).

Definition mat_of_list T (ll : list (list T)) : matrix T :=
  {| mat_list := ll;
     mat_nrows := list_list_nrows ll;
     mat_ncols := list_list_ncols ll |}.

Compute (mat_of_list [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]).

Definition list_list_el T d (ll : list (list T)) i j : T :=
  nth j (nth i ll []) d.

Compute (let (i, j) := (2, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (let (i, j) := (7, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).

Definition mat_el T d (M : matrix T) i j : T :=
  list_list_el d (mat_list M) i j.

Compute (let (i, j) := (2, 1) in mat_el 42 (mat_of_list [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] : matrix nat) i j).
Compute (let (i, j) := (7, 1) in mat_el 42 (mat_of_list [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] : matrix nat) i j).

Definition list_list_transpose {T} d (ll : list (list T)) : list (list T) :=
  let r := list_list_nrows ll in
  let c := list_list_ncols ll in
  map (λ i, map (λ j, list_list_el d ll j i) (seq 0 r)) (seq 0 c).

Compute (list_list_transpose 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]).

Definition mat_transpose T (d : T) (M : matrix T) : matrix T :=
  {| mat_list := list_list_transpose d (mat_list M);
     mat_nrows := mat_ncols M;
     mat_ncols := mat_nrows M |}.

Compute (mat_transpose 0 (mat_of_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]])).

Definition list_list_add T {so : semiring_op T} r c
    (ll1 ll2 : list (list T)) :=
  map
    (λ i,
       map
         (λ j,
            (list_list_el 0 ll1 i j + list_list_el 0 ll2 i j)%Srng)
         (seq 0 c))
    (seq 0 r).

Definition list_list_mul T {ro : semiring_op T} r cr c
    (ll1 : list (list T)) (ll2 : list (list T)) :=
  map
    (λ i,
     map
       (λ k,
        let vl :=
          map
            (λ j,
             srng_mul (list_list_el srng_zero ll1 i j)
               (list_list_el srng_zero ll2 j k))
            (seq 0 cr)
        in
	match vl with
        | [] => srng_zero
        | v :: vl' => List.fold_left srng_add vl' v
        end)
       (seq 0 c))
    (seq 0 r).

Definition nat_semiring_op : semiring_op nat :=
  {| srng_zero := 0;
     srng_one := 1;
     srng_add := Nat.add;
     srng_mul := Nat.mul |}.

Compute (let _ := nat_semiring_op in list_list_mul 3 4 2 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] [[1; 2]; [3; 4]; [5; 6]; [0; 0]]).

Compute (let _ := nat_semiring_op in list_list_mul 3 3 3 [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]).

Definition void_mat {T} : matrix T :=
  {| mat_list := []; mat_nrows := 0; mat_ncols := 0 |}.

(* multiplication of matrices is always defined, even if the resp # of
   rows (columns) of the first matrix is not equal to the # of rows
   (columns) of ths second one ; in that case, the result has no sense *)

(* multiplication of matrices is always defined, even if the # of columns
   of the first matrice is not equal to the # of rows of the second one;
   in that case, the result has not sense; theorems likely have to add the
   condition among its hypotheses *)

Definition mat_add T {so : semiring_op T} (M1 M2 : matrix T) : matrix T :=
  if Nat.eq_dec (mat_nrows M1) (mat_nrows M2) then
    if Nat.eq_dec (mat_ncols M1) (mat_ncols M2) then
      {| mat_list :=
           list_list_add (mat_nrows M1) (mat_ncols M1) (mat_list M1)
             (mat_list M2);
         mat_nrows := mat_nrows M1;
         mat_ncols := mat_ncols M1 |}
    else void_mat
  else void_mat.

Definition mat_mul {T} {so : semiring_op T} (M1 M2 : matrix T) : matrix T :=
  if Nat.eq_dec (mat_ncols M1) (mat_nrows M2) then
    {| mat_list :=
         list_list_mul (mat_nrows M1) (mat_ncols M1) (mat_ncols M2)
           (mat_list M1) (mat_list M2);
       mat_nrows := mat_nrows M1;
       mat_ncols := mat_ncols M2 |}
  else void_mat.

Compute (let _ := nat_semiring_op in mat_mul (mat_of_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list [[1; 2]; [3; 4]; [5; 6]; [0; 0]])).
Compute (let _ := nat_semiring_op in mat_mul (mat_of_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list [[1; 2]; [3; 4]; [5; 6]])).
Compute (let _ := nat_semiring_op in mat_mul (mat_of_list [[1; 2]; [3; 4]; [5; 6]])
  (mat_of_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]])).

Compute (let _ := nat_semiring_op in mat_ncols (mat_mul (mat_of_list [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]) (mat_of_list [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]))).

Definition list_list_opp T {ro : ring_op T} (ll : list (list T)) :=
  map (map rng_opp) ll.

Definition mat_opp T {ro : ring_op T} (M : matrix T) :=
  {| mat_list := list_list_opp (mat_list M);
     mat_nrows := mat_nrows M;
     mat_ncols := mat_ncols M |}.

(* matrices of matrices *)

Inductive mmatrix T :=
  | MM_1 : T → mmatrix T
  | MM_M : matrix (mmatrix T) → mmatrix T.

Arguments MM_1 {_} a%Srng.
Arguments MM_M {_}.

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

Fixpoint list_list_of_mmat T (MM : mmatrix T) : list (list T) :=
  match MM with
  | MM_1 x => [[x]]
  | MM_M MMM =>
      let ll :=
        map
          (λ MMl, concat_list_list_list (map (@list_list_of_mmat T) MMl))
          (mat_list MMM)
      in
      List.concat ll
  end.

Definition mat_of_mmat T (mm : mmatrix T) : matrix T :=
  mat_of_list (list_list_of_mmat mm).

Definition void_mmat T {so : semiring_op T} : mmatrix T :=
  MM_1 0%Srng.

Fixpoint mmat_opp T {ro : ring_op T} MM : mmatrix T :=
  match MM with
  | MM_1 x => MM_1 (- x)%Rng
  | MM_M MMM =>
      MM_M
        {| mat_list := map (map (λ mm, mmat_opp mm)) (mat_list MMM);
           mat_nrows := mat_nrows MMM;
           mat_ncols := mat_ncols MMM |}
  end.

Definition mmat_of_list T (ll : list (list (mmatrix T))) :
    matrix (mmatrix T) :=
  {| mat_list := ll;
     mat_nrows := list_list_nrows ll;
     mat_ncols := list_list_ncols ll |}.

Fixpoint IZ_2_pow T {ro : ring_op T} u n :=
  match n with
  | 0 => MM_1 u
  | S n' =>
      MM_M
        {| mat_list :=
             [[IZ_2_pow u n'; IZ_2_pow 0%Rng n'];
              [IZ_2_pow 0%Rng n'; IZ_2_pow u n']];
           mat_nrows := 2; mat_ncols := 2 |}
  end.

Definition I_2_pow T {ro : ring_op T} := IZ_2_pow 1%Rng.
Definition Z_2_pow T {ro : ring_op T} := IZ_2_pow 0%Rng.

Fixpoint A T {ro : ring_op T} n :=
  match n with
  | 0 => MM_1 0%Rng
  | S n' =>
       MM_M
         (mmat_of_list
            [[A n'; I_2_pow n'];
             [I_2_pow n'; mmat_opp (A n')]])
  end.

(*
Require Import ZArith.
Search mmatrix.
Open Scope Z_scope.

Compute (mat_of_mmat (@A _ Z_ring_op 4)).
*)

Fixpoint mmat_depth T (MM : mmatrix T) :=
  match MM with
  | MM_1 _ => 1
  | MM_M MMM =>
      match MMM with
      | mk_mat [] _ _ => 0
      | mk_mat (MMl :: _) _ _ =>
          match MMl with
          | [] => 0
          | MM' :: _ => 1 + mmat_depth MM'
          end
      end
  end.

Compute (mmat_depth (A 0)).
Compute (mmat_depth (A 1)).
Compute (mmat_depth (A 2)).
Compute (mmat_depth (A 3)).
Compute (mmat_depth (A 4)).

Definition mmmat_depth T {so : semiring_op T} (MMM : matrix (mmatrix T)) :=
  mmat_depth (mat_el void_mmat MMM 0 0).

Fixpoint mmat_add_loop T {so : semiring_op T} it (MM1 MM2 : mmatrix T) :=
  match it with
  | 0 => void_mmat
  | S it' =>
      match MM1 with
      | MM_1 xa =>
          match MM2 with
          | MM_1 xb => MM_1 (xa + xb)%Srng
          | MM_M MMB => void_mmat
          end
      | MM_M MMA =>
          match MM2 with
          | MM_1 MB => void_mmat
          | MM_M MMB =>
              let sso :=
                {| srng_zero := void_mmat; srng_one := void_mmat;
                   srng_add := mmat_add_loop it';
                   srng_mul := mmat_add_loop it' |}
              in
              MM_M (mat_add MMA MMB)
          end
      end
  end.

Definition mmat_add T {so : semiring_op T} (MM1 MM2 : mmatrix T) :=
  mmat_add_loop (mmat_depth MM1) MM1 MM2.

(* problem of this implementation: the recursive call mmat_mul_loop
   is inside an implicit argument; makes induction proofs difficult
   to make *)
Fixpoint mmat_mul_loop T {so : semiring_op T} it (MM1 MM2 : mmatrix T) :=
  match it with
  | 0 => void_mmat
  | S it' =>
      match MM1 with
      | MM_1 xa =>
          match MM2 with
          | MM_1 xb => MM_1 (xa * xb)%Srng
          | MM_M MMB => void_mmat
          end
      | MM_M MMMA =>
          match MM2 with
          | MM_1 MB => void_mmat
          | MM_M MMMB =>
              let mso :=
                {| srng_zero := void_mmat;
                   srng_one := void_mmat;
                   srng_add := @mmat_add T so;
                   srng_mul := mmat_mul_loop it' |}
              in
              MM_M (mat_mul MMMA MMMB)
          end
      end
  end.

Definition mmat_mul T {so : semiring_op T} (MM1 MM2 : mmatrix T) :=
  mmat_mul_loop (mmat_depth MM1) MM1 MM2.

(*
Require Import ZArith.
Open Scope Z_scope.

Check mmat_mul.
Check mat_of_mmat.

Compute (let ro := Z_ring_op in let so := @rng_semiring Z Z_ring_op in A 0).
Compute (let ro := Z_ring_op in let so := @rng_semiring Z Z_ring_op in A 1).
Compute (let ro := Z_ring_op in let so := @rng_semiring Z Z_ring_op in mat_of_mmat (A 2)).

Compute (let ro := Z_ring_op in let so := @rng_semiring Z Z_ring_op in mat_of_mmat (mmat_mul (A 0) (A 0))).
Compute (let ro := Z_ring_op in let so := @rng_semiring Z Z_ring_op in mat_of_mmat (mmat_mul (A 1) (A 1))).
Compute (let ro := Z_ring_op in let so := @rng_semiring Z Z_ring_op in mat_of_mmat (mmat_mul (A 2) (A 2))).
Compute (let ro := Z_ring_op in let so := @rng_semiring Z Z_ring_op in mat_of_mmat (mmat_mul (A 3) (A 3))).
*)

Definition rng_mul_nat_l T {so : semiring_op T} n v :=
  match n with
  | 0 => 0%Srng
  | S n' => (Σ (_ = 0, n'), v)%Srng
  end.

(*
Require Import ZArith.
Compute (let _ := @rng_semiring Z Z_ring_op in mul_nat_l 7 (-4)%Z).
*)

Definition mat_nat_mul_l T {so : semiring_op T} n M :=
  {| mat_list := map (map (rng_mul_nat_l n)) (mat_list M);
     mat_nrows := mat_nrows M;
     mat_ncols := mat_ncols M |}.

Fixpoint mmat_nat_mul_l_loop T it {so : semiring_op T} n MM :=
  match it with
  | 0 => void_mmat
  | S it' =>
      match MM with
      | MM_1 x => MM_1 (rng_mul_nat_l n x)
      | MM_M MMM =>
          MM_M
            {| mat_list :=
                 map (map (mmat_nat_mul_l_loop it' n)) (mat_list MMM);
               mat_nrows := mat_nrows MMM;
               mat_ncols := mat_ncols MMM |}
      end
  end.

Definition mmat_nat_mul_l T {so : semiring_op T} n MMM :=
  mmat_nat_mul_l_loop (mmat_depth MMM) n MMM.

Section Sensitivity.

Context {T : Type}.
Context (ro : ring_op T).
Context (so := @rng_semiring T ro).
Context (rp : @ring_prop T ro).
Context (sp : @semiring_prop T so).

Theorem mmat_depth_A : ∀ n, mmat_depth (A n) = S n.
Proof.
intros.
induction n; [ easy | cbn ].
now rewrite IHn.
Qed.

Theorem mmat_depth_IZ_2_pow : ∀ u n, mmat_depth (IZ_2_pow u n) = S n.
Proof.
intros.
induction n; [ easy | cbn ].
now rewrite IHn.
Qed.

(*
Theorem A_MM_1_nrows : ∀ n M,
  A n = MM_1 M
  → mat_nrows M = 1.
Proof.
intros * HAn.
destruct n; [ | easy ].
cbn in HAn.
now injection HAn; clear HAn; intros; subst M.
Qed.

Theorem A_MM_1_ncols : ∀ n M,
  A n = MM_1 M
  → mat_ncols M = 1.
Proof.
intros * HAn.
destruct n; [ | easy ].
cbn in HAn.
now injection HAn; clear HAn; intros; subst M.
Qed.
*)

Theorem A_MM_M_nrows : ∀ n MMM,
  A n = MM_M MMM
  → mat_nrows MMM = 2.
Proof.
intros * HAn.
destruct n; [ easy | ].
cbn in HAn.
now injection HAn; clear HAn; intros; subst MMM.
Qed.

Theorem A_MM_M_ncols : ∀ n MMM,
  A n = MM_M MMM
  → mat_ncols MMM = 2.
Proof.
intros * HAn.
destruct n; [ easy | ].
cbn in HAn.
now injection HAn; clear HAn; intros; subst MMM.
Qed.

(*
Theorem IZ_2_pow_MM_1_nrows : ∀ u n M,
  IZ_2_pow u n = MM_1 M
  → mat_nrows M = 1.
Proof.
intros * HIM.
destruct n; [ | easy ].
cbn in HIM.
now injection HIM; clear HIM; intros; subst M.
Qed.

Theorem IZ_2_pow_MM_1_ncols : ∀ u n M,
  IZ_2_pow u n = MM_1 M
  → mat_ncols M = 1.
Proof.
intros * HIM.
destruct n; [ | easy ].
cbn in HIM.
now injection HIM; clear HIM; intros; subst M.
Qed.
*)

Theorem IZ_2_pow_MM_M_nrows : ∀ u n MMM,
  IZ_2_pow u n = MM_M MMM
  → mat_nrows MMM = 2.
Proof.
intros * HIM.
destruct n; [ easy | ].
cbn in HIM.
now injection HIM; clear HIM; intros; subst MMM.
Qed.

Theorem IZ_2_pow_MM_M_ncols : ∀ u n MMM,
  IZ_2_pow u n = MM_M MMM
  → mat_ncols MMM = 2.
Proof.
intros * HIM.
destruct n; [ easy | ].
cbn in HIM.
now injection HIM; clear HIM; intros; subst MMM.
Qed.

Theorem mat_sqr_nrows : ∀ M (s := so),
  mat_nrows M = mat_ncols M
  → mat_nrows (mat_mul M M) = mat_nrows M.
Proof.
intros * Hrc; subst s.
unfold mat_mul.
symmetry in Hrc.
now destruct (Nat.eq_dec (mat_ncols M) (mat_nrows M)).
Qed.

Theorem mat_sqr_ncols : ∀ M (s := so),
  mat_nrows M = mat_ncols M
  → mat_ncols (mat_mul M M) = mat_ncols M.
Proof.
intros * Hrc; subst s.
unfold mat_mul.
symmetry in Hrc.
now destruct (Nat.eq_dec (mat_ncols M) (mat_nrows M)).
Qed.

(*
Theorem mat_nrows_A_I_2_pow_MM_1 : ∀ n M IM,
  A n = MM_1 M
  → I_2_pow n = MM_1 IM
  → mat_nrows M = mat_nrows IM.
Proof.
intros * HAn HIn.
destruct n; [ | easy ].
cbn in HAn, HIn.
injection HAn; clear HAn; intros; subst M.
injection HIn; clear HIn; intros; subst IM; easy.
Qed.
*)

(*
Theorem mat_ncols_A_I_2_pow_MM_1 : ∀ n M IM,
  A n = MM_1 M
  → I_2_pow n = MM_1 IM
  → mat_ncols M = mat_ncols IM.
Proof.
intros * HAn HIn.
destruct n; [ | easy ].
cbn in HAn, HIn.
injection HAn; clear HAn; intros; subst M.
injection HIn; clear HIn; intros; subst IM; easy.
Qed.
*)

Theorem mat_nrows_A_I_2_pow_MM_M : ∀ n MMM IMMM,
  A n = MM_M MMM
  → I_2_pow n = MM_M IMMM
  → mat_nrows MMM = mat_nrows IMMM.
Proof.
intros * HAn HIn.
destruct n; [ easy | ].
cbn in HAn, HIn.
injection HAn; clear HAn; intros; subst MMM.
injection HIn; clear HIn; intros; subst IMMM; easy.
Qed.

Definition mmat_nrows T (MM : mmatrix T) :=
  match MM with
  | MM_1 _ => 1
  | MM_M MMM => mat_nrows MMM
  end.

Definition mmat_ncols T (MM : mmatrix T) :=
  match MM with
  | MM_1 _ => 1
  | MM_M MMM => mat_ncols MMM
  end.

Theorem fold_mmat_add (_ := so) : ∀ (MM1 MM2 : mmatrix T),
  mmat_add_loop (mmat_depth MM1) MM1 MM2 = mmat_add MM1 MM2.
Proof. easy. Qed.

Theorem list_list_add_comm (_ := so) :
  ∀ (lla llb : list (list T)) r c,
  list_list_add r c lla llb = list_list_add r c llb lla.
Proof.
intros.
apply map_ext_in.
intros i Hi.
apply map_ext_in.
intros j Hj.
apply srng_add_comm.
Qed.

Theorem mat_add_comm (_ := so) : ∀ (MA MB : matrix T),
  mat_add MA MB = mat_add MB MA.
Proof.
intros.
unfold mat_add.
destruct (Nat.eq_dec (mat_nrows MA) (mat_nrows MB)) as [RAB| RAB]. {
  symmetry in RAB.
  destruct (Nat.eq_dec (mat_nrows MB) (mat_nrows MA)) as [H| ]; [ | easy ].
  clear H.
  destruct (Nat.eq_dec (mat_ncols MA) (mat_ncols MB)) as [CAB| CAB]. {
    symmetry in CAB.
    destruct (Nat.eq_dec (mat_ncols MB) (mat_ncols MA)) as [H| ]; [ | easy ].
    clear H.
    now rewrite list_list_add_comm, RAB, CAB.
  } {
    destruct (Nat.eq_dec (mat_ncols MB) (mat_ncols MA)) as [H| ]; [ | easy ].
    now symmetry in H.
  }
} {
  destruct (Nat.eq_dec (mat_nrows MB) (mat_nrows MA)) as [H| ]; [ | easy ].
  now symmetry in H.
}
Qed.

(* trop compliqué : à voir plus tard, peut-être
Theorem mmat_add_comm : ∀ MMA MMB,
  mmat_depth MMA = mmat_depth MMB
  → @mmat_add T so MMA MMB = @mmat_add T so MMB MMA.
Proof.
intros * Hdep.
unfold mmat_add.
remember (mmat_depth MMA) as it eqn:Hit.
rewrite <- Hdep.
clear Hit Hdep.
destruct it; [ easy | cbn ].
destruct MMA as [MA| MMMA]. {
  destruct MMB as [MB| MMMB]; [ | easy ].
  f_equal.
  now apply mat_add_comm.
} {
  destruct MMB as [MB| MMMB]; [ easy | ].
  f_equal.
Print semiring_op.
Print void_mmat.
Set Printing Implicit.
  remember so as sso.
  remember
    {| srng_zero := @void_mmat T;
       srng_one := @void_mmat T;
       srng_add := @mmat_add_loop T it 0%Srng (@srng_add T so);
       srng_mul := @mmat_add_loop T it 0%Srng (@srng_add T so) |}.
Print semiring_prop.
  apply mat_add_comm.
...
}
*)

Theorem mmat_add_IZ_Z_2_pow : ∀ u n,
  @mmat_add T so (IZ_2_pow u n) (Z_2_pow n) = IZ_2_pow u n.
Proof.
intros.
unfold mmat_add.
unfold Z_2_pow.
rewrite mmat_depth_IZ_2_pow.
revert u.
induction n; intros; [ now cbn; rewrite srng_add_0_r | ].
remember (S n) as sn; cbn; subst sn.
remember (IZ_2_pow u (S n)) as MM eqn:HMM; symmetry in HMM.
destruct MM as [M| MMM]; [ easy | ].
remember (IZ_2_pow 0%Rng (S n)) as MM eqn:HMM'; symmetry in HMM'.
destruct MM as [M'| MMM']; [ easy | ].
move MMM' before MMM.
f_equal.
injection HMM; clear HMM; intros; subst MMM.
injection HMM'; clear HMM'; intros; subst MMM'.
remember (S n) as sn; cbn; subst sn.
now do 2 rewrite IHn.
Qed.

Theorem mmat_add_Z_IZ_2_pow : ∀ u n,
  @mmat_add T so (Z_2_pow n) (IZ_2_pow u n) = IZ_2_pow u n.
Proof.
intros.
unfold mmat_add.
unfold Z_2_pow.
rewrite mmat_depth_IZ_2_pow.
revert u.
induction n; intros; [ now cbn; rewrite srng_add_0_l | ].
remember (S n) as sn; cbn; subst sn.
remember (IZ_2_pow u (S n)) as MM eqn:HMM; symmetry in HMM.
destruct MM as [M| MMM]; [ easy | ].
remember (IZ_2_pow 0%Rng (S n)) as MM eqn:HMM'; symmetry in HMM'.
destruct MM as [M'| MMM']; [ easy | ].
move MMM' before MMM.
f_equal.
injection HMM; clear HMM; intros; subst MMM.
injection HMM'; clear HMM'; intros; subst MMM'.
remember (S n) as sn; cbn; subst sn.
now do 2 rewrite IHn.
Qed.

Theorem mmat_mul_loop_IZ_Z_2_pow (_ := so) : ∀ it u n,
  S n ≤ it
  → mmat_mul_loop it (IZ_2_pow u n) (Z_2_pow n) = Z_2_pow n.
Proof.
intros * Hit.
revert n u Hit.
induction it; intros; [ easy | cbn ].
remember (IZ_2_pow u n) as MZ eqn:HMZ; symmetry in HMZ.
destruct MZ as [xz| MMMZ]. {
  destruct n; [ | easy ].
  cbn in HMZ.
  injection HMZ; clear HMZ; intros; subst xz.
  cbn.
  now rewrite srng_mul_0_r.
} {
  destruct n; [ easy | ].
  apply Nat.succ_le_mono in Hit.
  f_equal.
  cbn in HMZ.
  injection HMZ; clear HMZ; intros; subst MMMZ.
  cbn; f_equal.
  do 2 rewrite fold_mmat_add.
  rewrite IHit; [ | easy ].
  rewrite IHit; [ | easy ].
  f_equal; f_equal. {
    f_equal; [ apply mmat_add_IZ_Z_2_pow | ].
    f_equal; apply mmat_add_IZ_Z_2_pow.
  } {
    unfold Z_2_pow at 1 3.
    now rewrite mmat_add_IZ_Z_2_pow.
  }
}
Qed.

Theorem mmat_mul_loop_Z_IZ_2_pow : ∀ it u n,
  S n ≤ it
  → @mmat_mul_loop T so it (Z_2_pow n) (IZ_2_pow u n) = Z_2_pow n.
Proof.
intros * Hit.
revert n u Hit.
induction it; intros; [ easy | cbn ].
remember (IZ_2_pow u n) as MZ eqn:HMZ; symmetry in HMZ.
destruct MZ as [MZ| MMMZ]. {
  destruct n; [ | easy ].
  cbn in HMZ.
  injection HMZ; clear HMZ; intros; subst MZ.
  cbn.
  now rewrite srng_mul_0_l.
} {
  destruct n; [ easy | ].
  apply Nat.succ_le_mono in Hit.
  f_equal.
  cbn in HMZ.
  injection HMZ; clear HMZ; intros; subst MMMZ.
  cbn; f_equal.
  do 2 rewrite fold_mmat_add.
  rewrite IHit; [ | easy ].
  rewrite IHit; [ | easy ].
  f_equal; f_equal. {
    f_equal; [ apply mmat_add_IZ_Z_2_pow | ].
    f_equal; apply mmat_add_IZ_Z_2_pow.
  } {
    unfold Z_2_pow at 1 3.
    now rewrite mmat_add_IZ_Z_2_pow.
  }
}
Qed.

Theorem fold_Z_2_pow : ∀ n, IZ_2_pow 0%Rng n = Z_2_pow n.
Proof. easy. Qed.

Theorem mmat_mul_loop_sqr_I_2_pow : ∀ it n,
  S n ≤ it
  → @mmat_mul_loop T so it (I_2_pow n) (I_2_pow n) = I_2_pow n.
Proof.
intros * Hit.
revert n Hit.
induction it; intros; [ easy | ].
cbn.
remember (I_2_pow n) as MI eqn:HMI; symmetry in HMI.
destruct MI as [MI| MMMI]. {
  destruct n; [ | easy ].
  cbn in HMI.
  injection HMI; clear HMI; intros; subst MI.
  cbn.
  now rewrite srng_mul_1_l.
} {
  destruct n; [ easy | ].
  apply Nat.succ_le_mono in Hit.
  f_equal.
  cbn in HMI.
  injection HMI; clear HMI; intros; subst MMMI.
  cbn; f_equal.
  rewrite IHit; [ | easy ].
  do 4 rewrite fold_mmat_add.
  rewrite fold_Z_2_pow.
  unfold Z_2_pow at 1.
  unfold I_2_pow.
  rewrite mmat_mul_loop_IZ_Z_2_pow; [ | easy ].
  rewrite mmat_mul_loop_IZ_Z_2_pow; [ | easy ].
  rewrite mmat_mul_loop_Z_IZ_2_pow; [ | easy ].
  unfold Z_2_pow at 2.
  do 2 rewrite mmat_add_IZ_Z_2_pow.
  unfold Z_2_pow at 3.
  rewrite mmat_mul_loop_IZ_Z_2_pow; [ | easy ].
  unfold Z_2_pow at 1.
  rewrite mmat_add_IZ_Z_2_pow.
  now rewrite mmat_add_Z_IZ_2_pow.
}
Qed.

Fixpoint mmat_hss (_ := so) it (MMA MMB : mmatrix T) :=
  match it with
  | 0 => False
  | S it' =>
      match MMA with
      | MM_1 xa =>
          match MMB with
          | MM_1 _ => True
          | MM_M _ => False
          end
      | MM_M MMMA =>
          match MMB with
          | MM_1 _ => False
          | MM_M MMMB =>
              ∀ i j, i < mat_nrows MMMA → j < mat_ncols MMMA →
              mmat_hss it'
                (mat_el void_mmat MMMA 0 0)
                (mat_el void_mmat MMMB 0 0)
          end
      end
  end.

Definition mmat_have_same_struct MMA MMB :=
  mmat_hss (mmat_depth MMA) MMA MMB.

Compute (mmat_have_same_struct (A 4) (I_2_pow 4)).
Compute (mmat_have_same_struct (A 4) (I_2_pow 3)).
Compute (mmat_hss 10 (A 4) (I_2_pow 4)).

Theorem glop (_ := so) : ∀ it n,
  S n < it
  → mmat_mul_loop it (A n) (A n) = mmat_nat_mul_l_loop it n (I_2_pow n).
Proof.
intros * Hit; subst s.
revert n Hit.
induction it; intros; [ easy | ].
destruct n; [ now cbn; rewrite srng_mul_0_l | ].
cbn.
do 4 rewrite fold_mmat_add.
apply Nat.succ_le_mono in Hit.
f_equal; f_equal; f_equal. {
  f_equal. {
    rewrite IHit; [ | easy ].
    rewrite mmat_mul_loop_sqr_I_2_pow; [ | flia Hit ].
    destruct it; [ easy | ].
    apply Nat.succ_le_mono in Hit.
    cbn.
    remember (I_2_pow n) as MM eqn:HMM; symmetry in HMM.
    destruct MM as [x| MMM]. {
      cbn.
      f_equal.
      rewrite srng_add_0_l.
      clear - sp.
      induction n; [ cbn; apply srng_add_0_l | ].
...

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I : ∀ n (_ := so),
  mmat_mul (A n) (A n) = mmat_nat_mul_l n (I_2_pow n).
Proof.
intros; subst s.
unfold mmat_mul, mmat_nat_mul_l.
rewrite mmat_depth_A.
unfold I_2_pow at 1.
rewrite mmat_depth_IZ_2_pow.
...
 induction n. {
  cbn; unfold mat_nat_mul_l; cbn.
  now rewrite srng_mul_0_l.
}
(**)
remember (S n) as sn eqn:Hsn; cbn; subst sn.
Print mmat_nat_mul_l.
...
remember (S n) as sn eqn:Hsn; cbn.
remember (A sn) as Asn eqn:HAsn; symmetry in HAsn.
remember (I_2_pow sn) as Isn eqn:HIsn; symmetry in HIsn.
move Isn before Asn.
destruct Asn as [MA| MMMA]; [ now subst sn | ].
destruct Isn as [MI| MMMI]; [ now subst sn | ].
f_equal.
unfold mat_mul.
rewrite (A_MM_M_nrows _ HAsn).
rewrite (A_MM_M_ncols _ HAsn).
rewrite (IZ_2_pow_MM_M_nrows _ _ HIsn).
rewrite (IZ_2_pow_MM_M_ncols _ _ HIsn).
cbn - [ list_list_mul ]; f_equal.
rewrite Hsn in HAsn; cbn in HAsn.
injection HAsn; clear HAsn; intros HA.
subst MMMA; cbn - [ list_list_mul ].
rewrite Hsn in HIsn; cbn in HIsn.
injection HIsn; clear HIsn; intros HI.
subst MMMI; cbn.
f_equal. {
  f_equal. {
    rewrite mmat_mul_loop_sqr_I_2_pow; [ | now subst sn ].
    subst sn.
    remember (mmat_depth _) as it eqn:Hit.
...
intros.
unfold mmat_mul, mmat_nat_mul_l.
rewrite mmat_depth_A, mmat_depth_I_2_pow.
cbn.
unfold mat_nat_mul_l.
remember (A n) as An eqn:HAn; symmetry in HAn.
remember (I_2_pow n) as In eqn:HIn; symmetry in HIn.
move In before An.
destruct An as [M| MMM]. {
  destruct In as [IM| IMMM]; [ f_equal | now destruct n ].
  unfold mat_nat_mul_l.
  unfold mat_mul.
  rewrite (A_MM_1_nrows _ HAn).
  rewrite (A_MM_1_ncols _ HAn).
  rewrite (IZ_2_pow_MM_1_nrows _ _ HIn).
  rewrite (IZ_2_pow_MM_1_ncols _ _ HIn).
  cbn; f_equal.
  destruct n; [ | easy ].
  cbn in HAn, HIn.
  injection HAn; clear HAn; intros; subst M.
  injection HIn; clear HIn; intros; subst IM; cbn.
  now rewrite srng_mul_0_l.
} {
  destruct In as [IM| IMMM]; [ now destruct n | f_equal ].
  unfold mat_mul.
  rewrite (A_MM_M_nrows _ HAn).
  rewrite (A_MM_M_ncols _ HAn).
  rewrite (IZ_2_pow_MM_M_nrows _ _ HIn).
  rewrite (IZ_2_pow_MM_M_ncols _ _ HIn).
  cbn - [ list_list_mul ]; f_equal.
  destruct n; [ easy | ].
  cbn in HAn, HIn.
  injection HAn; clear HAn; intros; subst MMM.
  injection HIn; clear HIn; intros; subst IMMM.
  cbn - [ list_list_mul mmat_nat_mul_l_loop ].
  cbn - [ mmat_add ].
  f_equal. {
    f_equal. {
      remember (A n) as An eqn:HAn; symmetry in HAn.
      remember (I_2_pow n) as In eqn:HIn; symmetry in HIn.
      move In before An.
      destruct An as [MA | MMMA]. {
        destruct In as [M| MMM]; [ | now destruct n ].
        destruct n; [ | easy ].
        cbn in HAn, HIn.
        injection HAn; clear HAn; intros; subst MA.
        injection HIn; clear HIn; intros; subst M.
        unfold mat_nat_mul_l.
        cbn; f_equal; f_equal.
        now rewrite srng_mul_0_l, srng_mul_1_l.
      }
      destruct n; [ easy | ].
      destruct In as [M| MMM]; [ now destruct n | ].
      cbn in HAn, HIn.
      injection HAn; clear HAn; intros; subst MMMA.
      injection HIn; clear HIn; intros; subst MMM.
      remember (S n) as sn.
      cbn; f_equal; f_equal.
      f_equal. {
        f_equal. {
          subst sn.
          remember (mmat_depth (mmat_mul_loop (S n) (A n) (A n)))
            as ma eqn:Hma.
          remember (mmat_depth (mmat_mul_loop (S n) (I_2_pow n) (I_2_pow n)))
            as mi eqn:Hmi.
          cbn in Hma, Hmi.
          move mi before ma.
          remember (A n) as An eqn:HAn; symmetry in HAn.
          remember (I_2_pow n) as In eqn:HIn; symmetry in HIn.
          move In before An; move HIn before HAn.
          remember (IZ_2_pow 0%Rng n) as Zn eqn:HZn; symmetry in HZn.
          move Zn before In; move HZn before HIn.
          destruct An as [MA| MMMA]. {
            cbn in Hma; subst ma.
            destruct n; [ | easy ].
            injection HAn; clear HAn; intros; subst MA.
            destruct In as [MI| MMMI]; [ | easy ].
            cbn in Hmi; subst mi; cbn.
            injection HIn; clear HIn; intros; subst MI.
            destruct Zn as [MZ| MMMZ]; [ | easy ].
            cbn in HZn.
            injection HZn; clear HZn; intros; subst MZ.
            cbn; f_equal.
            unfold mat_nat_mul_l; cbn; f_equal.
            rewrite srng_mul_0_l.
            rewrite srng_mul_1_l.
            now rewrite srng_add_0_r.
          } {
(**)
            destruct In as [MI| MMMI]; [ now destruct n | ].
            destruct Zn as [MZ| MMMZ]; [ now destruct n | ].
            unfold mat_mul in Hma, Hmi.
            rewrite (A_MM_M_nrows _ HAn) in Hma.
            rewrite (A_MM_M_ncols _ HAn) in Hma.
            cbn in Hma.
            rewrite (IZ_2_pow_MM_M_nrows _ _ HIn) in Hmi.
            rewrite (IZ_2_pow_MM_M_ncols _ _ HIn) in Hmi.
            cbn in Hmi.
            subst mi; cbn.
            rewrite (IZ_2_pow_MM_M_nrows _ _ HIn).
            rewrite (IZ_2_pow_MM_M_ncols _ _ HIn).
            subst ma; cbn.
...
            destruct n; [ easy | ].
            cbn in HAn.
            destruct In as [MI| MMMI]; [ easy | ].
            destruct Zn as [MZ| MMMZ]; [ easy | ].
            injection HAn; clear HAn; intros; subst MMMA.
            injection HIn; clear HIn; intros; subst MMMI.
            injection HZn; clear HZn; intros; subst MMMZ.
            cbn in Hma, Hmi.
            subst ma mi; cbn.
            f_equal; f_equal.
...
intros.
unfold mmat_mul, mmat_nat_mul_l.
rewrite mmat_depth_A, mmat_depth_I_2_pow.
destruct n. {
  cbn; f_equal.
  unfold mat_nat_mul_l; cbn; f_equal; f_equal; f_equal.
  rewrite (@srng_mul_0_l T so); [ easy | ].
  apply sp.
}
destruct n. {
  cbn; f_equal; f_equal.
  unfold mat_nat_mul_l; cbn.
  rewrite rng_opp_0.
  do 2 rewrite srng_mul_0_l.
  do 2 rewrite srng_mul_1_l.
  do 3 rewrite srng_add_0_l.
  now rewrite srng_add_0_r.
}
...
destruct n. {
  cbn.
  do 5 rewrite srng_mul_0_l.
  do 5 rewrite srng_mul_1_l.
  do 11 rewrite srng_add_0_l.
...
intros.
unfold mmat_mul, mmat_nat_mul_l.
rewrite mmat_depth_A, mmat_depth_I_2_pow.
induction n. {
  cbn; f_equal.
  unfold mat_nat_mul_l; cbn; f_equal; f_equal; f_equal.
  rewrite (@srng_mul_0_l T so); [ easy | ].
  apply rp.
}
remember (S n) as sn; cbn; subst sn.
...

intros.
induction n. {
  cbn; f_equal.
  unfold mat_nat_mul_l; cbn; f_equal; f_equal; f_equal.
  rewrite (@srng_mul_0_l T so); [ easy | ].
  apply rp.
}
cbn; f_equal; f_equal.
f_equal. {
  f_equal. {
    unfold mmat_mul in IHn.
    unfold mmat_nat_mul_l in IHn.
    rewrite IHn.
...

Fixpoint mmat_el T dmm {ro : ring_op T} (MM : mmatrix T) i j {struct MM} :=
  match MM with
  | MM_1 M => mat_el 0%Rng M i j
  | MM_M mm =>
      let (nrows_bef, im) := mmat_which_row (S i) mm i 0 in
      let (ncols_bef, jm) := mmat_which_col (S j) mm j 0 in
      mmat_el dmm (mat_el dmm mm im jm) (i - nrows_bef) (j - ncols_bef)
  end.
...

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I (ro := Z_ring_op) (mro : ring_op (mmatrix Z)) :
  ∀ n i j,
  (i < 2 ^ n)%nat → (j < 2 ^ n)%nat
  → mmat_el (mmat_mul (A' n) (A' n)) i j = mat_el (nI n) i j.
Proof.
intros * Hi Hj.

...

(* old version *)
(* the type "matrix" defines infinite sized matrices; the limited size
   is given by functions such that mat_mul which, multiplying a m×n
   matrix with a n×p matrix, n is given as parameter of mat_mul *)

Record matrix A := { matel : nat → nat → A }.

Arguments matel {_}.

Definition mat_of_list {A} (d : A) ll :=
  {| matel i j := nth i (nth j ll []) d |}.

Definition list_of_mat {A} nrow ncol (M : matrix A) :=
  map (λ row, map (λ col, matel M row col) (seq 0 ncol)) (seq 0 nrow).

Definition mat_transp T (M : matrix T) :=
  {| matel i j := matel M j i |}.

Definition mat_mul T {ro : ring_op T} n A B :=
  {| matel i k := (Σ (j = 0, n - 1), matel A i j * matel B j k)%Rng |}.

Definition mat_sqr T {ro : ring_op T} n A := mat_mul n A A.

Require Import ZArith.

Compute (let _ := Z_ring_op in list_of_mat 3 3 (mat_mul 3 (mat_of_list 0 [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]) (mat_of_list 0 [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]))%Z).
Compute (let _ := Z_ring_op in list_of_mat 4 3 (mat_transp (mat_mul 4 (mat_transp (mat_of_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]])) (mat_transp (mat_of_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]; [13; 14;15; 16]]))))%Z).

Fixpoint insert_at {A} it pos (a : A) σ σll :=
  match it with
  | 0 => []
  | S it' =>
      map
        (λ σl,
         let (σ1, l) := (σl : (bool * list A)) in
         (xorb σ σ1, firstn pos l ++ [a] ++ skipn pos l)) σll ++
      insert_at it' (S pos) a (negb σ) σll
  end.

Fixpoint all_perm {A} (l : list A) :=
  match l with
  | [] => [(false, [])]
  | a :: l =>
      let σll := all_perm l in
      insert_at (S (length l)) 0 a false σll
 end.

Compute (all_perm [1; 2; 3]).

Definition det {A} {ro : ring_op A} (n : nat) (M : matrix A) : A :=
  let allp := all_perm (seq 0 n) in
  (Σ (ip = 0, length allp - 1),
     let '(σ, l) := nth ip allp (false, []) in
     let ll := combine (seq 0 n) l in
     rng_mul
       (if σ then rng_opp 1%Rng else 1%Rng)
       (fold_left (λ a ij, rng_mul a (matel M (fst ij) (snd ij))) ll 1%Rng))%Rng.

(*
Fixpoint det {A} {R : ring A} (n : nat) (M : matrix A) : A :=
  match n with
  | 0 => 1%Rng
  | S n' => (Σ (i = 0, n'), ((- (1)) ^ i) * matel M n' i * @det A R n' M)%Rng
  end.
*)

Print det.

(*
  | 1 3 |
  | 2 4 | = -2
*)
Compute (let _ := Z_ring_op in det 2 (mat_of_list 0%Z [[1; 2]; [3; 4]]%Z)).
(* ok *)

(*
  | -1 -4 |
  | 0  4  | = -4
*)
Compute (let _ := Z_ring_op in det 2 (mat_of_list 0%Z [[-1; 0]; [-4; 4]]%Z)).
(* ok *)

(*
  | -1 -4 -1 |
  |  0  4 -5 | = -31
  | -3 -5 -4 |
*)
Compute (let _ := Z_ring_op in det 3 (mat_of_list 0%Z [[-1; 0; -3]; [-4; 4; -5]; [-1; -5; -4]])%Z).
(* ok *)

(*
  "Theorem 2.2. We define a sequence of symmetric square matrices
   iteratively as follows,
               ⌈ 0 1 ⌉          ⌈ A_{n-1}   I       ⌉
         A₁ =  ⌊ 1 0 ⌋   A_n =  ⌊ I        -A_{n-1} ⌋

    Then An is a 2^n × 2 ^n matrix whose eigenvalues are √n of
    multiplicity 2^{n-1}, and -√n of multiplicity 2^{n-1}."
*)

(**)
(* attempt to make matrices of matrices in order to be able to manipulate
   the A_n function of A_{n-1} like above... *)

Require Import Equivalence.

Definition mat_eq {T} (eqt : T → T → Prop) (M M' : matrix T) :=
  ∀ i j, eqt (matel M i j) (matel M' i j).

Definition submat {T} (M : matrix T) istart jstart :=
  {| matel i j := matel M (i + istart) (j + jstart) |}.

(* "mat_mat_of_even_mat M n" returns a matrix of sub matrices
   of M of size n×n *)

Definition mat_mat_of_even_mat {T} n (M : matrix T) :=
  {| matel i j := submat M (i * n) (j * n) |}.

Definition even_mat_of_mat_mat {T} n (MM : matrix (matrix T)) :=
  {| matel i j := matel (matel MM (i / n) (j / n)) (i mod n) (j mod n) |}.

Print mat_mat_of_even_mat.
Print even_mat_of_mat_mat.

Theorem even_mat_mat_mat : ∀ T eqt (M : matrix T) n,
  Equivalence eqt
  → n ≠ 0
  → mat_eq eqt (even_mat_of_mat_mat n (mat_mat_of_even_mat n M)) M.
Proof.
intros * Heq Hnz i j; cbn.
setoid_rewrite Nat.add_comm.
setoid_rewrite Nat.mul_comm.
rewrite <- Nat.div_mod; [ | easy ].
rewrite <- Nat.div_mod; [ | easy ].
easy.
Qed.

Definition eqmt_of_eqt T (eqt : T → T → Prop) r c M1 M2 :=
  ∀ i j, i < r → j < c → eqt (matel M1 i j) (matel M2 i j).

Theorem mat_mat_even_mat : ∀ T eqt (MM : matrix (matrix T)) n,
  Equivalence eqt
  → n ≠ 0
  → mat_eq (eqmt_of_eqt T eqt n n)
       (mat_mat_of_even_mat n (even_mat_of_mat_mat n MM)) MM.
Proof.
intros * Heq Hnz i j k l Hk Hl; cbn.
rewrite Nat.div_add; [ | easy ].
rewrite Nat.div_add; [ | easy ].
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.div_small; [ | easy ].
rewrite Nat.div_small; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
easy.
Qed.

Definition zero_mat {T} {ro : ring_op T} := {| matel _ _ := rng_zero |}.

Definition I {T} {ro : ring_op T} :=
  {| matel i j := if Nat.eq_dec i j then rng_one else rng_zero |}.

Definition mat_opp {T} {ro : ring_op T} (M : matrix T) :=
  {| matel i j := rng_opp (matel M i j) |}.

Fixpoint old_A {T} {ro : ring_op T} n :=
  match n with
  | 0 => mat_of_list 0%Rng []
  | 1 => mat_of_list 0%Rng [[0; 1]; [1; 0]]%Rng
  | S n' =>
      even_mat_of_mat_mat (2 ^ n')
        {| matel i j :=
             if Nat.eq_dec i 0 then
               if Nat.eq_dec j 0 then old_A n' else I
             else
               if Nat.eq_dec j 0 then I else mat_opp (old_A n') |}
  end.

Definition mat_add {T} {ro : ring_op T} A B :=
  {| matel i j := (matel A i j + matel B i j)%Rng |}.

(*
Definition mat_ring_op {T} {ro : ring_op T} n :=
  {| rng_zero := zero_mat;
     rng_one := I;
     rng_add := mat_add;
     rng_mul := mat_mul n;
     rng_opp := mat_opp |}.
*)

(*
(* attempt to define the ring of matrices (of size n), but I think
   I need the extensionality of the functions and, perhaps, of
   functions of a nat up to n *)

Axiom extens_eq_sqr_mat : ∀ T n (M1 M2 : matrix T),
  eqmt_of_eqt T eq n M1 M2 → M1 = M2.

Theorem glop : False.
Proof.
set (ro := Z_ring_op).
assert (H : I = zero_mat). {
  apply (extens_eq_sqr_mat Z 0).
  now intros i j Hi Hj.
}
unfold I, zero_mat in H.
apply (f_equal matel) in H.
apply (f_equal (λ f, f 0 0)) in H.
now destruct (Nat.eq_dec 0 0).
Qed.

(* oops *)
(* but this is normal: I use extens_eq_sqr_mat with n=0, which is not
   the size of I & zero_mat; if you limit their sizes to 0, it is
   normal that they are equal!
   I should find a system to prevent the (my) use of this situation. *)
...

Theorem mat_1_neq_0 {T} {ro : ring_op T} {rp : ring_prop} :
  I ≠ zero_mat.
Proof.
intros H.
assert (H1 : ∀ i j, matel I i j = matel zero_mat i j). {
  intros i j.
  now rewrite H.
}
specialize (H1 0 0).
now apply rng_1_neq_0 in H1.
Qed.

Theorem mat_eq_dec {T} (n : nat) (M1 M2 : matrix T) :
  {M1 = M2} + {M1 ≠ M2}.
Proof.
intros.
left.
apply (extens_eq_sqr_mat T 0).
now intros i j Hi Hj.
Qed.

...

Definition mat_ring_prop {T} {ro : ring_op T} {rp : ring_prop} n :=
  let mro := mat_ring_op n in
  {| rng_1_neq_0 := mat_1_neq_0;
     rng_eq_dec := mat_eq_dec n;
     rng_add_comm := Z.add_comm |}.
     rng_add_assoc := Z.add_assoc;
     rng_add_0_l := Z.add_0_l;
     rng_add_opp_l := Z.add_opp_diag_l;
     rng_mul_comm := Z.mul_comm;
     rng_mul_assoc := Z.mul_assoc;
     rng_mul_1_l := Z.mul_1_l;
     rng_mul_add_distr_l := Z.mul_add_distr_l |}.

(* end attempt *)

Canonical Structure mat_ring_op.
Canonical Structure mat_ring_prop.
*)

Open Scope Z_scope.

Compute (list_of_mat 2 2 (let _ := Z_ring_op in old_A 1)).
Compute (list_of_mat 4 4 (let _ := Z_ring_op in old_A 2)).
Compute (list_of_mat 8 8 (let _ := Z_ring_op in old_A 3)).
Compute (list_of_mat 16 16 (let _ := Z_ring_op in old_A 4)).

Close Scope Z_scope.

Section I_A_theorems.

Context {T : Type}.
Context {ro : ring_op T}.
Context {rp : ring_prop}.

Theorem I_diag : ∀ i, matel I i i = 1%Rng.
Proof.
intros; cbn.
now destruct (Nat.eq_dec i i).
Qed.

Theorem I_ndiag : ∀ i j, i ≠ j → matel I i j = 0%Rng.
Proof.
intros * Hij; cbn.
now destruct (Nat.eq_dec i j).
Qed.

Theorem A_diag : ∀ n i, matel (old_A n) i i = 0%Rng.
Proof.
intros.
revert i.
induction n; intros; cbn. {
  rewrite match_id.
  rewrite nth_overflow; [ easy | cbn; flia ].
}
destruct n. {
  cbn.
  destruct i; [ easy | cbn ].
  destruct i; [ easy | cbn ].
  rewrite match_id.
  rewrite nth_overflow; [ easy | cbn; flia ].
}
remember (S n) as n1 eqn:Hn1; cbn.
destruct (Nat.eq_dec (i / 2 ^ n1) 0) as [Hin| Hin]; [ easy | cbn ].
rewrite IHn.
apply rng_opp_0.
Qed.

Theorem I_symm : ∀ i j, matel I i j = matel I j i.
Proof.
intros; cbn.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  symmetry in Hij.
  now destruct (Nat.eq_dec j i).
} {
  apply Nat.neq_sym in Hij.
  now destruct (Nat.eq_dec j i).
}
Qed.

Theorem A_symm : ∀ n i j, matel (old_A n) i j = matel (old_A n) j i.
Proof.
intros.
revert i j.
induction n; intros; cbn. {
  do 2 rewrite match_id.
  rewrite nth_overflow; [ | cbn; flia ].
  rewrite nth_overflow; [ easy | cbn; flia ].
}
destruct n. {
  cbn.
  destruct i. {
    destruct j; [ easy | cbn ].
    destruct j; [ easy | cbn ].
    do 2 rewrite match_id.
    rewrite nth_overflow; [ easy | cbn; flia ].
  }
  destruct j. {
    cbn.
    destruct i; [ easy | cbn ].
    do 2 rewrite match_id.
    rewrite nth_overflow; [ easy | cbn; flia ].
  }
  destruct i. {
    cbn.
    destruct j; [ easy | ].
    do 2 rewrite match_id.
    rewrite nth_overflow; [ easy | cbn; flia ].
  }
  destruct j. {
    cbn.
    do 2 rewrite match_id.
    rewrite nth_overflow; [ easy | cbn; flia ].
  }
  now do 2 rewrite match_id.
}
remember (S n) as n1 eqn:Hn1; cbn.
destruct (Nat.eq_dec (i / 2 ^ n1) 0) as [Hin| Hin]. {
  destruct (Nat.eq_dec (j / 2 ^ n1) 0) as [Hjn| Hjn]; [ apply IHn | ].
  apply I_symm.
} {
  destruct (Nat.eq_dec (j / 2 ^ n1) 0) as [Hjn| Hjn]; [ apply I_symm | ].
  now cbn; rewrite IHn.
}
Qed.

Theorem mat_sqr_A_up_left : ∀ n i j,
  i < 2 ^ n
  → j < 2 ^ n
  → matel (mat_sqr (2 ^ S n) (old_A (S n))) i j =
    matel (mat_add (mat_sqr (2 ^ n) (old_A n)) I) i j.
Proof.
intros * Hin Hjn.
destruct n; intros. {
  cbn in Hin, Hjn.
  destruct i; [ | flia Hin ].
  destruct j; [ | flia Hjn ].
  cbn.
  rewrite rng_mul_0_l, rng_add_0_l.
  rewrite rng_mul_1_l, rng_add_0_r.
  now do 2 rewrite rng_add_0_l.
}
remember (S n) as sn; cbn - [ mat_sqr "^" I mat_add ]; subst sn.
unfold even_mat_of_mat_mat.
remember (S n) as sn; cbn - [ mat_sqr "/" "^" I mat_add ]; subst sn.
cbn - [ summation "^" old_A I ].
rewrite Nat.div_small; [ | easy ].
rewrite Nat.div_small; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
erewrite (summation_split (2 ^ S n - 1)). 2: {
  split; [ flia | ].
  apply -> Nat.succ_le_mono.
  apply Nat.sub_le_mono_r.
  apply Nat.pow_le_mono_r; [ easy | flia ].
}
assert (Hz : 2 ^ S n ≠ 0) by now apply Nat.pow_nonzero.
replace (Σ (_ = _, _), _)%Rng with
    (Σ (k = 0, 2 ^ S n - 1),
     (matel (old_A (S n)) i k * matel (old_A (S n)) k j))%Rng. 2: {
  apply summation_compat; intros k Hk.
  rewrite Nat.div_small; [ | flia Hz Hk ].
  rewrite Nat.mod_small; [ | flia Hz Hk ].
  now destruct (Nat.eq_dec _ _).
}
rewrite Nat.sub_add; [ | flia Hz ].
replace (Σ (_ = 2 ^ S n, _), _)%Rng with
    (Σ (k = 2 ^ S n, 2 ^ S (S n) - 1),
     matel I i (k - 2 ^ S n) * matel I j (k - 2 ^ S n))%Rng. 2: {
  apply summation_compat; intros k Hk.
  rewrite (Nat_div_less_small 1). 2: {
    rewrite Nat.mul_1_l, Nat.add_1_r.
    rewrite (Nat.pow_succ_r _ (S n)) in Hk; [ | flia ].
    flia Hz Hk.
  }
  destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H ].
  rewrite (Nat_mod_less_small 1). 2: {
    rewrite Nat.mul_1_l, Nat.add_1_r.
    rewrite (Nat.pow_succ_r _ (S n)) in Hk; [ | flia ].
    flia Hz Hk.
  }
  now rewrite Nat.mul_1_l, (I_symm _ j).
}
cbn - [ summation old_A I "^" ].
f_equal.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  rewrite I_diag.
  erewrite (summation_split (i + 2 ^ S n - 1)). 2: {
    split; [ flia | ].
    apply -> Nat.succ_le_mono.
    apply Nat.sub_le_mono_r.
    rewrite (Nat.pow_succ_r _ (S n)); [ flia Hin | flia ].
  }
  erewrite all_0_summation_0. 2: {
    intros k Hk.
    rewrite I_ndiag; [ | flia Hk Hz ].
    apply rng_mul_0_l.
  }
  rewrite Nat.sub_add; [ | flia Hz ].
  rewrite summation_split_first. 2: {
    rewrite (Nat.pow_succ_r _ (S n)); [ | flia ].
    flia Hin.
  }
  rewrite Nat.add_sub, I_diag.
  erewrite all_0_summation_0. 2: {
    intros k Hk.
    rewrite I_ndiag; [ | flia Hk Hz ].
    apply rng_mul_0_l.
  }
  now rewrite rng_add_0_l, rng_mul_1_l, rng_add_0_r.
}
rewrite I_ndiag; [ | easy ].
rewrite summation_shift; [ | rewrite (Nat.pow_succ_r _ (S n)); flia Hz ].
replace (Σ (_ = _, _), _)%Rng with
    ((Σ (k = 0, 2 ^ S (S n) - 1 - 2 ^ S n),
      matel I i k * matel I j k)%Rng). 2: {
  apply summation_compat; intros k Hk.
  now rewrite Nat.add_comm, Nat.add_sub.
}
erewrite all_0_summation_0; [ easy | ].
intros k Hk.
eapply rng_mul_eq_0.
destruct (Nat.eq_dec i k) as [Hik| Hik]. {
  destruct (Nat.eq_dec j k) as [Hjk| Hjk]; [ congruence | ].
  right.
  now apply I_ndiag.
}
left.
now apply I_ndiag.
Qed.

Theorem mat_sqr_A_up_right : ∀ n i j,
  i < 2 ^ n
  → j < 2 ^ n
  → matel (mat_sqr (2 ^ S n) (old_A (S n))) i (j + 2 ^ n) = 0%Rng.
Proof.
intros * Hin Hjn.
remember (S n) as sn; cbn - [ summation "^" ]; subst sn.
revert i j Hin Hjn.
induction n; intros. {
  cbn in Hin, Hjn.
  apply Nat.lt_1_r in Hin.
  apply Nat.lt_1_r in Hjn.
  subst i j; cbn.
  rewrite rng_mul_0_l, rng_mul_0_r.
  now do 2 rewrite rng_add_0_l.
}
remember (S n) as sn; cbn - [ summation "^" ]; subst sn.
unfold even_mat_of_mat_mat.
remember (S n) as sn; cbn - [ summation "^" ]; subst sn.
rewrite Nat.div_small; [ | easy ].
destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
assert (Hz : 2 ^ S n ≠ 0) by now apply Nat.pow_nonzero.
rewrite Nat_div_add_same_r; [ | easy ].
rewrite Nat.div_small; [ | easy ].
rewrite Nat.add_0_l.
destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H].
rewrite Nat.mod_small; [ | easy ].
rewrite Nat_mod_add_same_r; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
rewrite (summation_split (2 ^ S n - 1)). 2: {
  rewrite (Nat.pow_succ_r _ (S n)); flia.
}
replace (Σ (_ = _, _), _)%Rng with
  (Σ (k = 0, 2 ^ S n - 1), matel (old_A (S n)) i k * matel I k j)%Rng. 2: {
  apply summation_compat; intros k Hk.
  rewrite Nat.div_small; [ | flia Hz Hk ].
  rewrite Nat.mod_small; [ | flia Hz Hk ].
  now destruct (Nat.eq_dec 0 0).
}
rewrite (summation_split (j - 1)) by flia Hjn.
destruct (Nat.eq_dec j 0) as [Hjz| Hjz]. {
  subst j.
  rewrite Nat.sub_0_l, Nat.add_0_l.
  rewrite summation_only_one.
  rewrite I_diag, rng_mul_1_r.
  rewrite all_0_summation_0. 2: {
    intros k Hk.
    rewrite I_ndiag; [ | flia Hk ].
    apply rng_mul_0_r.
  }
  rewrite rng_add_0_r.
  rewrite Nat.sub_add; [ | now apply Nat.neq_0_lt_0 ].
  replace (Σ (_ = _, _), _)%Rng with
    (Σ (k = 0, 2 ^ S n - 1),
     matel I i k * matel (mat_opp (old_A (S n))) k 0)%Rng. 2: {
    rewrite (summation_shift (2 ^ S n)). 2: {
      rewrite (Nat.pow_succ_r _ (S n)); [ flia Hz | flia ].
    }
    rewrite Nat_sub_sub_swap.
    replace (2 ^ S (S n) - 2 ^ S n) with (2 ^ S n) by (cbn; flia).
    apply summation_compat; intros k Hk.
    rewrite (Nat_div_less_small 1); [ | flia Hk Hz ].
    destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H].
    rewrite (Nat_mod_less_small 1); [ | flia Hk Hz ].
    now rewrite Nat.mul_1_l, Nat.add_comm, Nat.add_sub.
  }
  destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
    subst i.
    rewrite A_diag, rng_add_0_l.
    rewrite summation_split_first; [ | flia ].
    rewrite I_diag, rng_mul_1_l.
    rewrite all_0_summation_0. 2: {
      intros k Hk.
      rewrite I_ndiag; [ | flia Hk ].
      apply rng_mul_0_l.
    }
    rewrite rng_add_0_r.
    cbn - [ old_A ].
    rewrite A_diag.
    apply rng_opp_0.
  }
  rewrite (summation_split (i - 1)). 2: {
    split; [ flia | flia Hin Hiz ].
  }
  rewrite all_0_summation_0. 2: {
    intros k Hk.
    rewrite I_ndiag; [ | flia Hiz Hk ].
    apply rng_mul_0_l.
  }
  rewrite rng_add_0_l.
  rewrite Nat.sub_add; [ | flia Hiz ].
  rewrite summation_split_first; [ | flia Hin ].
  rewrite I_diag, rng_mul_1_l, rng_add_assoc.
  unfold mat_opp at 1.
  cbn - [ old_A summation "^" ].
  rewrite fold_rng_sub, rng_add_opp_r, rng_add_0_l.
  apply all_0_summation_0.
  intros k Hk.
  destruct (Nat.eq_dec i k) as [H| H]; [ flia Hk H | ].
  apply rng_mul_0_l.
}
rewrite Nat.sub_add; [ | flia Hjz ].
rewrite all_0_summation_0. 2: {
  intros k Hk.
  rewrite I_ndiag; [ | flia Hjz Hk ].
  apply rng_mul_0_r.
}
rewrite rng_add_0_l.
rewrite summation_split_first; [ | flia Hjn ].
rewrite I_diag, rng_mul_1_r.
rewrite all_0_summation_0. 2: {
  intros k Hk.
  rewrite I_ndiag; [ | flia Hjz Hk ].
  apply rng_mul_0_r.
}
rewrite Nat.sub_add; [ | flia Hz ].
rewrite rng_add_0_r.
replace (Σ (_ = _, _), _)%Rng with
  (Σ (k = 0, 2 ^ S n - 1),
   matel I i k * matel (mat_opp (old_A (S n))) k j)%Rng. 2: {
  rewrite (summation_shift (2 ^ S n)). 2: {
    rewrite (Nat.pow_succ_r _ (S n)); [ flia Hz | flia ].
  }
  rewrite Nat_sub_sub_swap.
  replace (2 ^ S (S n) - 2 ^ S n) with (2 ^ S n) by (cbn; flia).
  apply summation_compat; intros k Hk.
  rewrite (Nat_div_less_small 1); [ | flia Hk Hz ].
  destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H].
  rewrite (Nat_mod_less_small 1); [ | flia Hk Hz ].
  now rewrite Nat.mul_1_l, Nat.add_comm, Nat.add_sub.
}
rewrite (summation_split (i - 1)) by flia Hin.
destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
  subst i.
  rewrite Nat.sub_0_l, Nat.add_0_l.
  rewrite summation_only_one.
  rewrite I_diag, rng_mul_1_l.
  rewrite rng_add_assoc.
  unfold mat_opp at 1.
  cbn - [ old_A summation "^" mat_opp I ].
  rewrite fold_rng_sub, rng_add_opp_r, rng_add_0_l.
  apply all_0_summation_0.
  intros k Hk.
  rewrite I_ndiag; [ | flia Hk ].
  apply rng_mul_0_l.
}
rewrite all_0_summation_0. 2: {
  intros k Hk.
  rewrite I_ndiag; [ | flia Hiz Hk ].
  apply rng_mul_0_l.
}
rewrite rng_add_0_l.
rewrite Nat.sub_add; [ | flia Hiz ].
rewrite summation_split_first; [ | flia Hin ].
rewrite I_diag, rng_mul_1_l, rng_add_assoc.
unfold mat_opp at 1.
cbn - [ old_A summation "^" mat_opp I ].
rewrite fold_rng_sub, rng_add_opp_r, rng_add_0_l.
apply all_0_summation_0.
intros k Hk.
rewrite I_ndiag; [ | flia Hk ].
apply rng_mul_0_l.
Qed.

Theorem A_sqr_symm : ∀ n i j,
  matel (mat_sqr (2 ^ n) (old_A n)) i j = matel (mat_sqr (2 ^ n) (old_A n)) j i.
Proof.
intros; cbn - [ summation ].
apply summation_compat; intros k Hk.
rewrite rng_mul_comm.
rewrite A_symm; f_equal.
apply A_symm.
Qed.

End I_A_theorems.

(* "We prove by induction that A_n^2 = nI" *)

Definition nI n :=
  {| matel i j := if Nat.eq_dec i j then Z.of_nat n else 0%Z |}.

Definition fin_mat_eq {T} (eqt : T → T → Prop) u v (M M' : matrix T) :=
  ∀ i j, i < u → j < v → eqt (matel M i j) (matel M' i j).

(* trying to prove
                   ⌈ (A_n)^2+I   0          ⌉
    (A_{n+1})^2 =  ⌊ 0           (A_n)^2+I  ⌋

  with matrices (and sub-matrices)
*)

Record vector A := { vecel : nat → A }.

Arguments vecel {_}.

(* matrix of sub-matrices
   - MM_1 : matrix alone
   - MM_M vnrow vncol MM :
        MM : matrix of matrices
        vnrow(i) : number of rows of the sub-matrices at row i
        vncol(i) : number of cols of the sub-matrices at col i
  so that all sub-matrices are correctement calées les unes à
  côté des autres

  e.g.

    ---------------------------------------
    |       |  |             |            |  : vnrow(0) = 1
    ---------------------------------------
    |       |  |             |            |
    |       |  |             |            |  : vnrow(1) = 3
    |       |  |             |            |
    ---------------------------------------
     <-----> <> <-----------> <---------->
        7    2       13            12

       vncol(0) = 7 ; vncol(1) = 2 ; vncol(2) = 13 ; vncol(3) = 12
*)

Inductive mmatrix T :=
  | MM_1 : matrix T → mmatrix T
  | MM_M : vector nat → vector nat → matrix (mmatrix T) → mmatrix T.

Arguments MM_1 {_}.
Arguments MM_M {_}.

Fixpoint mmat_opp {T} {ro : ring_op T} MM :=
  match MM with
  | MM_1 M => MM_1 (mat_opp M)
  | MM_M vr vc mm => MM_M vr vc {| matel i j := mmat_opp (matel mm i j) |}
  end.

Definition mmat_of_list {T} (d : T) (ll : list (list (mmatrix T))) :
    matrix (mmatrix T) :=
  {| matel i j := nth i (nth j ll []) (MM_1 {| matel i j := d |}) |}.

Fixpoint A {T} {ro : ring_op T} n :=
  match n with
  | 0 => MM_1 (mat_of_list 0%Rng [])
(*
  | 1 => MM_1 (mat_of_list 0%Rng [[0; 1]; [1; 0]]%Rng)
*)
  | S n' =>
       MM_M {| vecel _ := 2 |} {| vecel _ := 2 |}
         (mmat_of_list 0%Rng
            [[A n'; MM_1 I];
             [MM_1 I; mmat_opp (A n')]])
  end.

(**)
Fixpoint mmat_nb_of_rows_ub {T} vlen (MM : mmatrix T) :=
  match MM with
  | MM_1 _ => vlen
  | MM_M vr _ MMM =>
      Σ (i = 0, vlen - 1),
      (vecel vr i + mmat_nb_of_rows_ub (vecel vr i) (matel MMM i 0))
  end.

Fixpoint mmat_nb_of_cols_ub {T} vlen (MM : mmatrix T) :=
  match MM with
  | MM_1 _ => vlen
  | MM_M _ vc MMM =>
      Σ (i = 0, vlen - 1),
      (vecel vc i + mmat_nb_of_cols_ub (vecel vc i) (matel MMM i 0))
  end.

Compute (let n := 0 in mmat_nb_of_rows_ub 2 (A n)).
Compute (let n := 1 in mmat_nb_of_rows_ub 2 (A n)).
Compute (let n := 2 in mmat_nb_of_rows_ub 2 (A n)).
Compute (let n := 3 in mmat_nb_of_rows_ub 2 (A n)).
Compute (let n := 4 in mmat_nb_of_rows_ub 2 (A n)).

Definition mmmat_nb_of_rows_ub {T} nr (MMM : matrix (mmatrix T)) :=
  match nr with
  | 0 => 0
  | S nr' => Σ (i = 0, nr'), mmat_nb_of_rows_ub nr (matel MMM i 0)
  end.

Definition mmmat_nb_of_cols_ub {T} nc (MMM : matrix (mmatrix T)) :=
  match nc with
  | 0 => 0
  | S nc' => Σ (j = 0, nc'), mmat_nb_of_cols_ub nc (matel MMM 0 j)
  end.

Compute
  (let mmm :=
     let fm k := MM_1 {|matel i j := 100 * k + 10 * i + j|} in
     mmat_of_list 0 [[fm 0; fm 1; fm 2]; [fm 3; fm 4; fm 5]; [fm 6; fm 7; fm 8]]
   in
   mmmat_nb_of_rows_ub 3 mmm). (* 9 ≥ 7 : ok *)
Compute
  (let mmm :=
     let fm k := MM_1 {|matel i j := 100 * k + 10 * i + j|} in
     mmat_of_list 0 [[fm 0; fm 1; fm 2]; [fm 3; fm 4; fm 5]; [fm 6; fm 7; fm 8]]
   in
   mmmat_nb_of_cols_ub 3 mmm). (* 9 ≥ 9 *)
Compute
  (let mmm :=
     let fm k := MM_1 {|matel i j := 100 * k + 10 * i + j|} in
     mmat_of_list 0 [[MM_M {| vecel i := 2 |} {| vecel j := match j with 0 => 2 | _ => 1 end |} {| matel i j := match j with 0 => fm 0 | _ => fm 1 end |}; fm 1; fm 2]; [fm 3; fm 4; fm 5]; [fm 6; fm 7; fm 8]]
   in
   (mmmat_nb_of_rows_ub 3 mmm, mmmat_nb_of_cols_ub 3 mmm)).

(* with ub, it should be possible to compute the real value; but I have to
   prove that this so-called ub is indeed an upper bound *)

Fixpoint mmat_nb_of_rows_loop {T} it vlen (MM : mmatrix T) :=
  match it with
  | 0 => 42 (* should not happen *)
  | S it' =>
      match MM with
      | MM_1 _ => vlen
      | MM_M vr _ MMM =>
          Σ (i = 0, vlen - 1),
          mmat_nb_of_rows_loop it' (vecel vr i) (matel MMM i 0)
      end
  end.

Definition mmat_nb_of_rows {T} vlen (MM : mmatrix T) :=
  mmat_nb_of_rows_loop (mmat_nb_of_rows_ub vlen MM) vlen MM.

Definition mmmat_nb_of_rows {T} nr (MMM : matrix (mmatrix T)) :=
  match nr with
  | 0 => 0
  | S nr' => Σ (i = 0, nr'), mmat_nb_of_rows nr (matel MMM i 0)
  end.

Compute (let n := 0 in mmat_nb_of_rows 1 (A n)).
Compute (let n := 1 in mmat_nb_of_rows 2 (A n)).
Compute (let n := 2 in mmat_nb_of_rows 2 (A n)).

Compute (let n := 3 in mmat_nb_of_rows 2 (A n)). (* shit, 6 *)
Compute (let n := 3 in mmat_nb_of_rows_ub 2 (A n)).
  (* 14 ou 20, selon que A a le cas "1 => ..." ou non *)
...

Compute (let n := 4 in mmat_nb_of_rows 2 (A n)).
...

Definition mmmat_nb_of_rows {T} vlen vr (MMM : matrix (mmatrix T)) :=
  match vlen with
  | 0 => 0
  | S vlen' => Σ (i = 0, vlen'), mmat_nb_of_rows (vecel vr i) (matel MMM i 0)
  end.

Fixpoint mmat_nb_of_cols {T} vlen (MM : mmatrix T) :=
  match MM with
  | MM_1 _ => vlen
  | MM_M _ vc MMM =>
      Σ (j = 0, vlen - 1), mmat_nb_of_cols (vecel vc j) (matel MMM 0 j)
  end.

Definition list_of_mmat_mat {T} r c (MM : mmatrix T) :=
  match MM with
  | MM_1 M => list_of_mat r c M
  | MM_M _ _ _ => []
  end.


Definition mmmat_nb_of_cols {T} vlen vc (MMM : matrix (mmatrix T)) :=
  match vlen with
  | 0 => 0
  | S vlen' => Σ (j = 0, vlen'), mmat_nb_of_cols (vecel vc j) (matel MMM 0 j)
  end.

Compute
  (let mmm :=
     let stdm k := MM_1 {|matel i j := 100 * k + 10 * i + j|} in
     mmat_of_list 0 [[stdm 0; stdm 1; stdm 2]; [stdm 3; stdm 4; stdm 5]; [stdm 6; stdm 7; stdm 8]]
   in
   let mml := list_of_mat 3 3 mmm in
   let f r c i j := list_of_mmat_mat r c (nth i (nth j mml []) (MM_1 {|matel _ _ := 0|})) in
   [[f 2 3 0 0; f 2 2 0 1; f 2 4 0 2];
    [f 4 3 1 0; f 4 2 1 1; f 4 4 1 2];
    [f 1 3 2 0; f 1 2 2 1; f 1 4 2 2]]).
(* mmm : matrix (mmatrix nat) *)
Compute
  (let mmm :=
     let fm k := MM_1 {|matel i j := 100 * k + 10 * i + j|} in
     mmat_of_list 0 [[fm 0; fm 1; fm 2]; [fm 3; fm 4; fm 5]; [fm 6; fm 7; fm 8]]
   in
   (mmmat_nb_of_rows 3 {| vecel i := match i with 0 => 2 | 1 => 4 | _ => 1 end |} mmm,
    mmmat_nb_of_cols 3 {| vecel i := match i with 0 => 3 | 1 => 2 | _ => 4 end |} mmm)).
Compute
  (let mmm :=
     let fm k := MM_1 {|matel i j := 100 * k + 10 * i + j|} in
     mmat_of_list 0 [[MM_M {| vecel i := 2 |} {| vecel j := match j with 0 => 2 | _ => 1 end |} {| matel i j := match j with 0 => fm 0 | _ => fm 1 end |}; fm 1; fm 2]; [fm 3; fm 4; fm 5]; [fm 6; fm 7; fm 8]]
   in
   (mmmat_nb_of_rows 3 {| vecel i := match i with 0 => 2 | 1 => 4 | _ => 1 end |} mmm,
    mmmat_nb_of_cols 3 {| vecel i := match i with 0 => 3 | 1 => 2 | _ => 4 end |} mmm)).

(* pfff... même l'exemple, c'est compliqué *)
...

Fixpoint number_of_rows_upto {T} it im vr (MMM : matrix (mmatrix T)) :=
  match it with
  | 0 => 0
  | S it' =>
      match im with
      | 0 => 0
      | S im' =>
          match matel MMM im' 0 with
          | MM_1 _ => vecel vr im
          | MM_M vr' _ MMM' => number_of_rows_upto it' (vecel vr im) vr' MMM'
          end +
          number_of_rows_upto it' im' vr MMM
      end
  end.

...

Fixpoint mmat_nb_of_rows_ub {T} vlen (MM : mmatrix T) :=
  vlen +
  match MM with
  | MM_1 _ => 0
  | MM_M vr _ MMM =>
      Σ (i = 0, vlen - 1), mmat_nb_of_rows_ub (vecel vr i) (matel MMM i 0)
  end.
...
(* "Recursive definition of nb_of_rows_ub is ill-formed." *)
...
Fixpoint nb_of_rows_ub {T} vlen vr (MMM : matrix (mmatrix T)) {struct MMM} :=
  vlen +
  Σ (i = 0, vlen - 1),
    match matel MMM i 0 with
    | MM_1 _ => vecel vr i
    | MM_M vr' _ MMM' => nb_of_rows_ub (vecel vr i) vr' MMM'
    end.
...

Fixpoint mmat_which_row {T} it vlen (vr : vector nat) (MMM : matrix (mmatrix T)) (i im : nat) :=
  match it with
  | 0 => (0, 0)
  | S it' =>
      let nr := number_of_rows_upto (nb_of_rows_ub vlen vr MMM) im vr MMM in
      (0, 0)
  end.
...
      match matel MMM im 0 with
      | MM_1 M =>
          let nr := vecel vr im in
          if lt_dec i nr then (0, im)
          else
            let (nr_bef, ir) := mmat_which_row it' vr MMM (i - nr) (im + 1) in
            (nr + nr_bef, ir)
      | MM_M vr' _ mmm => (0, 0)
      end
  end.
...

(*
Definition mmat_which_row {T} it (nc : vector nat) (mm : matrix (mmatrix T)) (i im : nat) := (0, 0).
*)
Definition mmat_which_col {T} it (nc : vector nat) (mm : matrix (mmatrix T)) (j jm : nat) := (0, 0).

Fixpoint mmatel' {T} {ro : ring_op T} (MM : mmatrix T) i j :=
  match MM with
  | MM_1 M => matel M i j
  | MM_M vr vc mm =>
      let (nrows_bef, im) := mmat_which_row (S i) vr mm i 0 in
      let (ncols_bef, jm) := mmat_which_col (S j) vc mm j 0 in
      mmatel' (matel mm im jm) (i - nrows_bef) (j - ncols_bef)
  end.
...

Definition mat_horiz_concat {T} '(r1, c1, m1) '(r2, c2, m2) :
    (nat * nat * matrix T) :=
  (max r1 r2, c1 + c2,
   {| matel i j :=
       if lt_dec j c1 then matel m1 i j else matel m2 i (j - c1) |}).

Definition mat_vertic_concat {T} '(r1, c1, m1) '(r2, c2, m2) :
    (nat * nat * matrix T) :=
  (r1 + r2, max c1 c2,
   {| matel i j :=
       if lt_dec i r1 then matel m1 i j else matel m2 (i - r1) j |}).

Fixpoint mat_of_mmat {T} (d : T) MM :=
  match MM with
  | MM_1 r c M => (r, c, M)
  | MM_M nr nc mm =>
      List.fold_left
        (λ acc r,
	   mat_vertic_concat acc
             (List.fold_left
                 (λ acc c,
                    mat_horiz_concat acc (mat_of_mmat d (matel mm r c)))
                 (seq 0 nc) (0, 0, {| matel _ _ := d |})))
        (seq 0 nr) (0, 0, {| matel _ _ := d |})
  end.

Definition list_of_mat2 {T} '(n, c, M) : list (list (matrix T)) :=
  list_of_mat n c M.

Definition list_of_mmat {T} d (MM : mmatrix T) :=
  let '(r, c, M) := mat_of_mmat d MM in
  list_of_mat r c M.

Definition mmatel {T} {ro : ring_op T} MM i j :=
  matel (snd (mat_of_mmat 0%Z MM)) i j.

(**)
Fixpoint mmat_nrows {T} {ro : ring_op T} (MM : mmatrix T) :=
  match MM with
  | MM_1 nr _ _ => nr
  | MM_M nr _ mm => Σ (i = 0, nr - 1), mmat_nrows (matel mm i 0)
  end.

Fixpoint mmat_ncols {T} {ro : ring_op T} (MM : mmatrix T) :=
  match MM with
  | MM_1 _ nc _ => nc
  | MM_M _ nc mm => Σ (j = 0, nc - 1), mmat_ncols (matel mm 0 j)
  end.

(**)
...

Compute (let n := 1 in list_of_mat (2 ^ n) (2 ^ n) (let _ := Z_ring_op in A n)).
Compute (let n := 1 in list_of_mmat 0%Z (let _ := Z_ring_op in A' n)).
Compute (let n := 2 in list_of_mat (2 ^ n) (2 ^ n) (let _ := Z_ring_op in A n)).
Compute (let n := 2 in list_of_mmat 0%Z (let _ := Z_ring_op in A' n)).
Compute (let n := 3 in list_of_mat (2 ^ n) (2 ^ n) (let _ := Z_ring_op in A n)).
Compute (let n := 3 in list_of_mmat 0%Z (let _ := Z_ring_op in A' n)).
Open Scope Z_scope.
Compute (let n := 4%nat in list_of_mat (2 ^ n) (2 ^ n) (let _ := Z_ring_op in A n)).
Compute (let n := 4%nat in list_of_mmat 0%Z (let _ := Z_ring_op in A' n)).
Close Scope Z_scope.

Definition mmat_mul {T} {ro : ring_op T} {mro : ring_op (mmatrix T)}
    (A B : mmatrix T) :=
  match A with
  | MM_1 ra ca MA =>
      match B with
      | MM_1 rb cb MB =>
          if Nat.eq_dec ca rb then MM_1 ra cb (mat_mul ca MA MB)
          else MM_1 0 0 zero_mat
      | MM_M rb cb MMB => MM_1 0 0 zero_mat
      end
  | MM_M ra ca MMA =>
      match B with
      | MM_1 rb cb MB => MM_1 0 0 zero_mat
      | MM_M rb cb MMB =>
          if Nat.eq_dec ca rb then MM_M ra cb (mat_mul ca MMA MMB)
          else MM_1 0 0 zero_mat
      end
  end.

Theorem A'_is_MM_1 (ro := Z_ring_op) : ∀ n r c M,
  A' n = MM_1 r c M → n = 0 ∧ r = 1 ∧ c = 1 ∧
  M = zero_mat.
Proof.
intros * HA.
destruct n; [ | easy ].
cbn in HA.
now injection HA; clear HA; intros; subst.
Qed.

Theorem A'_is_MM_M (ro := Z_ring_op) : ∀ n r c MM,
  A' n = MM_M r c MM → n ≠ 0 ∧ r = 2 ∧ c = 2 ∧
  MM =
    mmat_of_list 0%Rng
      [[A' (n - 1); MM_1 (2 ^ (n - 1)) (2 ^ (n - 1)) I];
      [MM_1 (2 ^ (n - 1)) (2 ^ (n - 1)) I; mmat_opp (A' (n - 1))]].
Proof.
intros * HA.
destruct n; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r.
cbn in HA.
now injection HA; clear HA; intros; subst.
Qed.

Fixpoint mmat_eq {T} eqt (MM1 MM2 : mmatrix T) :=
  match MM1 with
  | MM_1 r1 c1 M1 =>
      match MM2 with
      | MM_1 r2 c2 M2 =>
          ∀ i j, i < min r1 r2 → j < min c1 c2 → eqt (matel M1 i j) (matel M2 i j)
      | MM_M r2 c2 MM'2 =>
          False
      end
  | MM_M r1 c1 MM'1 =>
      match MM2 with
      | MM_1 r2 c2 M2 =>
          False
      | MM_M r2 c2 MM'2 =>
          ∀ i j, mmat_eq eqt (matel MM'1 i j) (matel MM'2 i j)
      end
  end.

(*
Theorem mmat_eq_matel (ro := Z_ring_op) : ∀ MMM1 MMM2 r c,
  (∀ i j, i < r → j < c → mmat_eq eq (matel MMM1 i j) (matel MMM2 i j))
  → ∀ im jm, mmatel (MM_M r c MMM1) im jm = mmatel (MM_M r c MMM2) im jm.
Proof.
intros * HMM *.
unfold mmatel.
Print mat_of_mmat.
(* ah la la... j'aime pas ces mat_vertic_concat et mat_horiz_concat ;
   comment raisonner avec ces trucs-là ? *)
...
*)

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I (ro := Z_ring_op) (mro : ring_op (mmatrix Z)) :
  ∀ n i j,
  (i < 2 ^ n)%nat → (j < 2 ^ n)%nat
  → mmatel (mmat_mul (A' n) (A' n)) i j = matel (nI n) i j.
Proof.
intros * Hi Hj.
unfold mmat_mul.
remember (A' n) as an eqn:Han; symmetry in Han.
destruct an as [ra ca MA| ra ca MMA]. {
  apply A'_is_MM_1 in Han.
  destruct Han as (Hn & Hra & Hca & HMA).
  subst; cbn.
  now destruct (Nat.eq_dec i j).
}
apply A'_is_MM_M in Han.
destruct Han as (Hnz & Hra & Hca & HMMA).
subst ra ca; cbn - [ nI ].
subst MMA.
unfold mat_mul.
cbn - [ nI mmat_of_list ].
rename i into im; rename j into jm.
rename Hi into Him; rename Hj into Hjm.
Check mmatel.
Print MM_M.
(*
...
etransitivity.
apply mmat_eq_matel.
intros * Hi Hj.
cbn - [ mmat_of_list ].
Print mmat_eq.
...
*)
transitivity
  (mmatel
    (MM_M 2 2
       {|
       matel := λ i k : nat,
                  ((if Nat.eq_dec i 0 then A' (n - 1)
                    else
                      matel
                        (mmat_of_list 0%Z
                           [[A' (n - 1); MM_1 (2 ^ (n - 1)) (2 ^ (n - 1)) I];
                           [MM_1 (2 ^ (n - 1)) (2 ^ (n - 1)) I; mmat_opp (A' (n - 1))]])
                        i 0) *
                   matel
                     (mmat_of_list 0%Z
                        [[A' (n - 1); MM_1 (2 ^ (n - 1)) (2 ^ (n - 1)) I];
                        [MM_1 (2 ^ (n - 1)) (2 ^ (n - 1)) I; mmat_opp (A' (n - 1))]]) 0 k +
                   (matel
                      (mmat_of_list 0%Z
                         [[A' (n - 1); MM_1 (2 ^ (n - 1)) (2 ^ (n - 1)) I];
                         [MM_1 (2 ^ (n - 1)) (2 ^ (n - 1)) I; mmat_opp (A' (n - 1))]]) i 1 *
                    matel
                      (mmat_of_list 0%Z
                         [[A' (n - 1); MM_1 (2 ^ (n - 1)) (2 ^ (n - 1)) I];
                         [MM_1 (2 ^ (n - 1)) (2 ^ (n - 1)) I; mmat_opp (A' (n - 1))]]) 1 k + 0))%Rng |}) im jm).
(* essayons déjà avec ça : vais-je y arriver ? *)
unfold mmatel; cbn.
(* c'est pas le pied, comme on disait à l'époque ;
   encore à cause ce ce mat_vertic_concat, pas bien facile à utiliser ;
   faudrait une autre définition de mmatel *)
...
destruct n; [ easy | clear Hnz ].
cbn - [ nI ].
rewrite Nat.sub_0_r.
induction n. {
  cbn in Hi, Hj.
  destruct i. {
    destruct j. {
...
intros * Hi Hj.
unfold mmatel.
induction n; [ now cbn; destruct (Nat.eq_dec i j) | ].
cbn - [ nI mmat_mul ].
unfold mmat_mul.
destruct (Nat.eq_dec 2 2) as [H| H]; [ clear H | easy ].
...

Theorem sqr_An1_from_sqr_An (ro := Z_ring_op) (rp := Z_ring_prop) : ∀ n,
  fin_mat_eq eq (2 ^ S n) (2 ^ S n)
    (mat_sqr (2 ^ S n) (A (S n)))
    (even_mat_of_mat_mat (2 ^ n)
       {| matel i j :=
           if Nat.eq_dec i 0 then
             if Nat.eq_dec j 0 then mat_add (mat_sqr (2 ^ n) (A n)) I
             else zero_mat
           else
             if Nat.eq_dec j 0 then zero_mat
             else mat_add (mat_sqr (2 ^ n) (A n)) I |}).
Proof.
intros * i j Hi Hj.
unfold even_mat_of_mat_mat.
remember (S n) as sn.
cbn - [ mat_sqr "/" ]; subst sn.
destruct (lt_dec i (2 ^ n)) as [Hin| Hin]. {
  destruct (Nat.eq_dec (i / 2 ^ n) 0) as [H| H]. 2: {
    now rewrite Nat.div_small in H.
  }
  clear H.
  rewrite Nat.mod_small; [ | easy ].
(**)
  destruct (lt_dec j (2 ^ n)) as [Hjn| Hjn]. {
    destruct (Nat.eq_dec (j / 2 ^ n) 0) as [H| H]. 2: {
      now rewrite Nat.div_small in H.
    }
    clear H.
    rewrite Nat.mod_small; [ | easy ].
    now apply mat_sqr_A_up_left.
  }
  apply Nat.nlt_ge in Hjn.
  rewrite (Nat_div_less_small 1) by now rewrite Nat.mul_1_l.
  rewrite (Nat_mod_less_small 1) by now rewrite Nat.mul_1_l.
  destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H].
  unfold zero_mat.
  cbn - [ A mat_sqr "^" ].
  assert (Hz : 2 ^ n ≠ 0) by now apply Nat.pow_nonzero.
  replace j with (j - 2 ^ n + 2 ^ n) by now apply Nat.sub_add.
  remember (j - 2 ^ n) as k eqn:Hk.
  assert (H : k < 2 ^ n) by (cbn in Hj; flia Hj Hk).
  clear j Hj Hjn Hk.
  rename k into j; rename H into Hjn.
  move j before i.
  move Hjn before Hin; clear Hi Hz.
  now rewrite mat_sqr_A_up_right.
}
apply Nat.nlt_ge in Hin.
rewrite (Nat_div_less_small 1) by now rewrite Nat.mul_1_l.
rewrite (Nat_mod_less_small 1) by now rewrite Nat.mul_1_l.
destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H ].
rewrite Nat.mul_1_l.
destruct (lt_dec j (2 ^ n)) as [Hjn| Hjn]. {
  destruct (Nat.eq_dec (j / 2 ^ n) 0) as [H| H]. 2: {
    now rewrite Nat.div_small in H.
  }
  clear H.
  unfold zero_mat.
  cbn - [ A mat_sqr "^" ].
  assert (Hz : 2 ^ n ≠ 0) by now apply Nat.pow_nonzero.
  replace i with (i - 2 ^ n + 2 ^ n) by now apply Nat.sub_add.
  remember (i - 2 ^ n) as k eqn:Hk.
  assert (H : k < 2 ^ n) by (cbn in Hi; flia Hi Hk).
  clear i Hi Hin Hk.
  rename k into i; rename H into Hin.
  move i after j.
  move Hin after Hjn; clear Hj Hz.
  rewrite A_sqr_symm.
  now rewrite mat_sqr_A_up_right.
}
apply Nat.nlt_ge in Hjn.
rewrite (Nat_div_less_small 1). 2: {
  rewrite Nat.pow_succ_r in Hj; [ | flia ].
  rewrite Nat.mul_1_l; flia Hj Hjn.
}
rewrite (Nat_mod_less_small 1). 2: {
  rewrite Nat.pow_succ_r in Hj; [ | flia ].
  rewrite Nat.mul_1_l; flia Hj Hjn.
}
rewrite Nat.mul_1_l.
destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H ].
rewrite Nat.pow_succ_r in Hi; [ | flia ].
rewrite Nat.pow_succ_r in Hj; [ | flia ].
rewrite <- mat_sqr_A_up_left; [ | flia Hi | flia Hj ].
cbn - [ summation "^" A ].
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  rewrite (summation_split (2 ^ n - 1)). 2: {
    split; [ flia | cbn; flia ].
  }
  rewrite Nat.sub_add. 2: {
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    subst n.
    cbn in Hi, Hin.
    now replace i with 1 by flia Hi Hin.
  }
  assert (Hz : 2 ^ n ≠ 0) by now apply Nat.pow_nonzero.
  replace (Σ (_ = _, _), _)%Rng with 1%Rng. 2: {
    rewrite (summation_split (i - 2 ^ n)) by flia Hi.
    destruct (Nat.eq_dec i (2 ^ n)) as [Hien| Hien]. {
      replace (i - 2 ^ n) with 0 by flia Hien.
      rewrite Nat.add_0_l.
      rewrite summation_only_one.
      rewrite all_0_summation_0. 2: {
        intros k Hk.
        cbn - [ A ].
        apply Z.mul_eq_0; left.
        cbn.
        destruct n; [ easy | ].
        unfold even_mat_of_mat_mat.
        cbn - [ A "^" ].
        rewrite Hien.
        rewrite Nat.div_same; [ | easy ].
        rewrite Nat.mod_same; [ | easy ].
        destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H ].
        rewrite Nat.div_small; [ | flia Hk ].
        rewrite Nat.mod_small; [ | flia Hk ].
        destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
        rewrite I_ndiag; [ easy | flia Hk ].
      }
      rewrite rng_add_0_r.
      cbn.
      destruct n; [ easy | ].
      unfold even_mat_of_mat_mat.
      cbn - [ A "^" ].
      rewrite Hien.
      rewrite Nat.div_same; [ | easy ].
      rewrite Nat.mod_same; [ | easy ].
      destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H ].
      rewrite Nat.div_0_l; [ | easy ].
      rewrite Nat.mod_0_l; [ | easy ].
      now destruct (Nat.eq_dec 0 0).
    }
    replace (i - 2 ^ n) with (S (i - 2 ^ n - 1)) at 1 by flia Hin Hien.
    rewrite summation_split_last by flia Hin Hz.
    replace (S (i - 2 ^ n - 1)) with (i - 2 ^ n) by flia Hin Hien.
    rewrite (A_symm _ _ i).
    replace (matel (A (S n)) i (i - 2 ^ n)) with 1%Rng. 2: {
      cbn.
      destruct n; [ easy | ].
      unfold even_mat_of_mat_mat.
      cbn - [ A "mod" "/" "^" ].
      rewrite (Nat_div_less_small 1). 2: {
        split; [ flia Hin | ].
        now cbn in Hi; cbn.
      }
      destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H ].
      rewrite Nat.div_small by flia Hi.
      destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
      rewrite (Nat_mod_less_small 1). 2: {
        split; [ flia Hin | ].
        now cbn in Hi; cbn.
      }
      rewrite Nat.mod_small by flia Hi.
      now rewrite Nat.mul_1_l, I_diag.
    }
    rewrite Z.mul_1_l.
    rewrite all_0_summation_0. 2: {
      intros k Hk.
      cbn - [ A ].
      apply Z.mul_eq_0; left.
      cbn.
      destruct n; [ easy | ].
      unfold even_mat_of_mat_mat.
      cbn - [ A "^" ].
      rewrite (Nat_div_less_small 1). 2: {
        split; [ flia Hin | easy ].
      }
      destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H ].
      rewrite Nat.div_small by flia Hi Hk.
      destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
      rewrite (Nat_mod_less_small 1). 2: {
        split; [ flia Hin | easy ].
      }
      rewrite Nat.mul_1_l.
      rewrite Nat.mod_small by flia Hi Hk.
      rewrite I_ndiag; [ easy | ].
      flia Hk Hin Hien.
    }
    rewrite rng_add_0_l.
    rewrite all_0_summation_0. 2: {
      intros k Hk; cbn.
      replace n with (S (n - 1)) at 1 2 by flia Hnz.
      unfold even_mat_of_mat_mat; cbn.
      rewrite (Nat_div_less_small 1). 2: {
        split; [ flia Hin | easy ].
      }
      rewrite Nat.div_small; [ | flia Hk ].
      destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H ].
      destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
      rewrite (Nat_mod_less_small 1). 2: {
        split; [ flia Hin | easy ].
      }
      rewrite Nat.mod_small; [ | flia Hk ].
      rewrite I_ndiag; [ | flia Hk ].
      apply rng_mul_0_l.
    }
    now rewrite rng_add_0_r.
  }
Compute (let n := 5 in let i := 2 ^ n + 2 ^ n - 3 in (Σ (i0 = 2 ^ n, 2 ^ S n - 1), (matel (A (S n)) i i0 * matel (A (S n)) i0 i))%Rng).
Compute (let n := 5 in let i := 2 ^ n in (Σ (j = 0, 2 ^ S n - 1),
   (matel (A (S n)) (i - 2 ^ n) j * matel (A (S n)) j (i - 2 ^ n))%Z)%Rng).
  rewrite summation_shift.
  replace (2 ^ S n - 1 - 2 ^ n) with (2 ^ n - 1) by (cbn; flia).
  replace (Σ (_ = _, _), _)%Rng with
     (Σ (j = 0, 2 ^ n - 1),
     (matel (A (S n)) i (j + 2 ^ n) * matel (A (S n)) (j + 2 ^ n) i))%Rng. 2: {
    apply summation_compat; intros k Hk.
    now rewrite (Nat.add_comm k).
  }
(* ah, putain, c'est décourageant... j'ai exploré plein de pistes qui n'ont pas
   l'air de fonctionner bien ; il reste celle-là, mais faut encore pas mal
   réfléchir et, en plus, je ne suis même pas sûr que ce théorème va bien
   fonctionner par la suite ; et ne suis pas content de son énoncé, pas facile
   à lire ; mon code est un peu en bordel en plus (mardi 2 juin 2020 10h51 *)
...
  replace (Σ (_ = _, _), _)%Rng with (Z.of_nat n). 2: {
...
  rewrite Nat.mul_1_l.
  cbn - [ A summation "^" ].
  erewrite (summation_split i).
  destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
    subst i.
    erewrite summation_only_one.
    erewrite A_diag.
    rewrite Z.mul_0_l, Nat.add_0_l.
    erewrite (summation_split j).
    replace j with (S (j - 1)) at 1 by flia Hz Hjn.
    erewrite summation_split_last.
...
  erewrite all_0_summation_0; [ easy | ].
  intros k Hk.
  cbn - [ A ].
  apply Z.mul_eq_0.
  destruct (Nat.eq_dec i k) as [Hik| Hik]. {
    subst k; left.
    now erewrite A_diag.
  }
Compute (list_of_mat 8 8 (let _ := Z_ring_op in A 3)).
...
intros * i j Hi Hj.
destruct n. {
  cbn in Hi, Hj.
  rewrite Nat.pow_0_r, Nat.pow_1_r.
  cbn - [even_mat_of_mat_mat ].
  destruct i. {
    destruct j; [ easy | ].
    destruct j; [ easy | flia Hj ].
  }
  destruct i; [ | flia Hi ].
  destruct j; [ easy | ].
  destruct j; [ easy | flia Hj ].
}
(**)
unfold even_mat_of_mat_mat.
remember (S (S n)) as ssn.
remember (S n) as sn.
cbn - [ mat_sqr "/" ]; subst sn ssn.
destruct (lt_dec i (2 ^ S n)) as [Hin| Hin]. {
  destruct (Nat.eq_dec (i / 2 ^ S n) 0) as [H| H]. 2: {
    now rewrite Nat.div_small in H.
  }
  clear H.
  rewrite Nat.mod_small; [ | easy ].
  destruct (lt_dec j (2 ^ S n)) as [Hjn| Hjn]. {
    destruct (Nat.eq_dec (j / 2 ^ S n) 0) as [H| H]. 2: {
      now rewrite Nat.div_small in H.
    }
    clear H.
    rewrite Nat.mod_small; [ | easy ].
...
destruct n. {
  cbn in Hi, Hj.
  destruct i. {
    destruct j; [ easy | ].
    destruct j; [ easy | ].
    destruct j; [ easy | ].
    destruct j; [ easy | flia Hj ].
  }
  destruct i. {
    destruct j; [ easy | ].
    destruct j; [ easy | ].
    destruct j; [ easy | ].
    destruct j; [ easy | flia Hj ].
  }
  destruct i. {
    destruct j; [ easy | ].
    destruct j; [ easy | ].
    destruct j; [ easy | ].
    destruct j; [ easy | flia Hj ].
  }
  destruct i; [ | flia Hi ].
  destruct j; [ easy | ].
  destruct j; [ easy | ].
  destruct j; [ easy | ].
  destruct j; [ easy | flia Hj ].
}
...

Theorem lemma_2_A_n_2_eq_n_I (R := Z_ring_op) : ∀ n,
  fin_mat_eq eq (2 ^ n) (2 ^ n)
    (mat_mul (2 ^ n) (A n) (A n)) (nI n).
Proof.
intros * i j Hi Hj.
destruct n. {
  cbn.
  do 2 rewrite match_id; cbn.
  now destruct (Nat.eq_dec i j).
}
remember (A (S n)) as asn eqn:Hasn.
revert asn i j Hasn Hi Hj.
induction n; intros. {
  subst asn.
  cbn in Hi, Hj |-*.
  destruct i. {
    destruct j; [ easy | ].
    destruct j; [ easy | flia Hj ].
  }
  destruct i; [ | flia Hi ].
  destruct j; [ easy | ].
  destruct j; [ easy | flia Hj ].
}
remember (2 ^ S (S n)) as ssn.
remember (S n) as sn.
cbn - [ mat_mul nI ].
cbn in Hasn.
subst sn ssn.
...
Print mat_mul.
Theorem glop {ro : ring_op Z} : ∀ n (rro := mat_ring_op n),
  ∀ MM1 MM2,
  mat_eq eq
    (mat_mul (2 * n)
       (even_mat_of_mat_mat n MM1)
       (even_mat_of_mat_mat n MM2))
    (even_mat_of_mat_mat n (mat_mul 1 MM1 MM2)).
Proof.
intros * i j.
remember (2 * n) as n2; cbn - [ summation ]; subst n2.
...
rewrite Nat.pow_succ_r.
rewrite glop.
remember (2 * S n) as n2; cbn - [ summation ]; subst n2.
...
unfold even_mat_of_mat_mat.
remember (2 ^ S (S n)) as ssn; remember (S n) as sn; cbn - [ mat_mul nI ]; subst sn ssn.
Print mat_mul.
(* mouais... c'est pas si évident... *)
...
*)

(* previous version: worked, but had to be terminated *)

Print A.
...

Fixpoint old_A n :=
  match n with
  | 0 => mat_of_list 0%Z []
  | 1 => mat_of_list 0%Z [[0; 1]; [1; 0]]%Z
  | S n' =>
      {| matel i j :=
           if lt_dec i (2 ^ n') then
             if lt_dec j (2 ^ n') then matel (old_A n') i j
             else if Nat.eq_dec i (j - 2 ^ n') then 1%Z else 0%Z
           else
             if lt_dec j (2 ^ n') then
               if Nat.eq_dec (i - 2 ^ n') j then 1%Z else 0%Z
             else (- matel (old_A n') (i - 2 ^ n') (j - 2 ^ n'))%Z |}
  end.

Open Scope Z.

Compute (list_of_mat 2 2 (old_A 1)).
Compute (list_of_mat 2 2 (let _ := Z_ring_op in A 1)).
Compute (list_of_mat 4 4 (old_A 2)).
Compute (list_of_mat 4 4 (let _ := Z_ring_op in A 2)).
Compute (list_of_mat 8 8 (old_A 3)).
Compute (list_of_mat 8 8 (let _ := Z_ring_op in A 3)).
Compute (list_of_mat 16 16 (old_A 4)).
Compute (list_of_mat 16 16 (let _ := Z_ring_op in A 4)).

Close Scope Z.

Theorem A_diag : ∀ n i, matel (A n) i i = 0%Z.
Proof.
intros.
revert i.
induction n; intros; cbn. {
  rewrite match_id.
  rewrite nth_overflow; [ easy | cbn; flia ].
}
destruct n. {
  cbn.
  destruct i; [ easy | cbn ].
  destruct i; [ easy | cbn ].
  rewrite match_id.
  rewrite nth_overflow; [ easy | cbn; flia ].
}
remember (S n) as n1 eqn:Hn1; cbn.
destruct (lt_dec i (2 ^ n1)) as [Hin| Hin]; [ easy | ].
apply Nat.nlt_ge in Hin.
now rewrite IHn.
Qed.

Theorem A_symm : ∀ n i j, matel (A n) i j = matel (A n) j i.
Proof.
intros.
revert i j.
induction n; intros; cbn. {
  do 2 rewrite match_id.
  rewrite nth_overflow; [ | cbn; flia ].
  rewrite nth_overflow; [ easy | cbn; flia ].
}
destruct n. {
  cbn.
  destruct i. {
    destruct j; [ easy | cbn ].
    destruct j; [ easy | cbn ].
    do 2 rewrite match_id.
    rewrite nth_overflow; [ easy | cbn; flia ].
  }
  destruct j. {
    cbn.
    destruct i; [ easy | cbn ].
    do 2 rewrite match_id.
    rewrite nth_overflow; [ easy | cbn; flia ].
  }
  destruct i. {
    cbn.
    destruct j; [ easy | ].
    do 2 rewrite match_id.
    rewrite nth_overflow; [ easy | cbn; flia ].
  }
  destruct j. {
    cbn.
    do 2 rewrite match_id.
    rewrite nth_overflow; [ easy | cbn; flia ].
  }
  now do 2 rewrite match_id.
}
remember (S n) as n1 eqn:Hn1; cbn.
destruct (lt_dec i (2 ^ n1)) as [Hin| Hin]. {
  rewrite IHn.
  destruct (lt_dec j (2 ^ n1)) as [Hjn| Hn]; [ easy | ].
  destruct (Nat.eq_dec i (j - 2 ^ n1)) as [Hij| Hij]. {
    rewrite <- Hij; cbn.
    now destruct (Nat.eq_dec i i).
  }
  destruct (Nat.eq_dec (j - 2 ^ n1) i) as [Hji| Hji]; [ | easy ].
  now symmetry in Hji.
}
rewrite IHn.
destruct (lt_dec j (2 ^ n1)) as [Hjn| Hjn]; [ | easy ].
destruct (Nat.eq_dec (i - 2 ^ n1) j) as [Hij| Hij]. {
  rewrite Hij; cbn.
  now destruct (Nat.eq_dec j j).
}
destruct (Nat.eq_dec j (i - 2 ^ n1)) as [Hji| Hji]; [ | easy ].
now symmetry in Hji.
Qed.

(* "We prove by induction that A_n^2 = nI" *)

Definition nI n :=
  {| matel i j := if Nat.eq_dec i j then Z.of_nat n else 0%Z |}.

Theorem lemma_2_A_n_2_eq_n_I (R := Z_ring) : ∀ n i j,
  (i < 2 ^ n)%nat → (j < 2 ^ n)%nat
  → matel (mat_mul (2 ^ n) (A n) (A n)) i j = matel (nI n) i j.
Proof.
intros * Hi Hj.
destruct n. {
  cbn in Hi, Hj; cbn.
  destruct i; [ now destruct j | ].
  destruct i; [ cbn | flia Hi ].
  destruct j; [ easy | ].
  destruct j; [ easy | flia Hj ].
}
remember (A (S n)) as a eqn:Ha.
remember (S n) as sn; cbn - [ summation ]; subst sn.
rewrite (summation_split (2 ^ n - 1)). 2: {
  split; [ flia | ].
  cbn; flia.
}
rewrite Nat.sub_add. 2: {
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
change
  ((Σ (k = 0, 2 ^ n - 1), (matel a i k * matel a k j) +
   Σ (k = 2 ^ n, 2 ^ S n), (matel a i k * matel a k j)) =
   if Nat.eq_dec i j then Z.of_nat (S n) else 0)%Rng.
remember (matel a) as f eqn:Hf.
subst a.
cbn in Hf.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n f.
  cbn in Hi, Hj; cbn.
  destruct i. {
    destruct j; [ easy | ].
    destruct j; [ easy | flia Hj ].
  }
  destruct i; [ | flia Hi ].
  destruct j; [ easy | ].
  destruct j; [ easy | flia Hj ].
}
replace n with (S (n - 1)) in Hf at 1 by flia Hnz.
cbn in Hf.
destruct (lt_dec j (2 ^ n)) as [Hjn| Hjn]. {
  replace (Σ (k = 0, 2 ^ n - 1), f i k * f k j)%Rng with
      (Σ (k = 0, 2 ^ n - 1),
       (if lt_dec i (2 ^ n) then matel (A n) i k
        else if Nat.eq_dec (i - 2 ^ n) k then 1%Z else 0%Z) *
       matel (A n) k j)%Rng. 2: {
    apply summation_compat.
    intros k Hk; cbn; subst f.
    destruct (lt_dec k (2 ^ n)) as [H| H]. 2: {
      assert (Hz : 2 ^ n ≠ 0) by now apply Nat.pow_nonzero.
      flia Hk H Hz.
    }
    clear H.
    destruct (lt_dec j (2 ^ n)) as [H| H]; [ easy | flia Hjn H].
  }
  rewrite (summation_shift (2 ^ n)); [ | cbn; flia ].
  replace (2 ^ S n - 2 ^ n) with (2 ^ n) by (cbn; flia).
  replace
    (Σ (i0 = 0, 2 ^ n), f i (2 ^ n + i0)%nat * f (2 ^ n + i0)%nat j)%Rng
  with
    (Σ (k = 0, 2 ^ n),
     (if lt_dec i (2 ^ n) then if Nat.eq_dec i k then 1%Z else 0%Z
      else (- matel (A n) (i - 2 ^ n) k)%Z) *
     (if Nat.eq_dec k j then 1%Z else 0%Z))%Rng. 2: {
    apply summation_compat.
    intros k Hk; cbn; subst f.
    destruct (lt_dec (2 ^ n + k) (2 ^ n)) as [H| H]; [ flia Hk H | clear H ].
    rewrite Nat.add_comm, Nat.add_sub.
    destruct (lt_dec j (2 ^ n)) as [H| H]; [ easy | flia Hjn H].
  }
  clear f Hf.
  destruct (lt_dec i (2 ^ n)) as [Hin| Hin]. {
    destruct (Nat.eq_dec i j) as [Hij| Hij]. {
      subst j; clear Hj Hjn.
      replace
        (Σ (k = 0, 2 ^ n),
         (if Nat.eq_dec i k then 1%Z else 0%Z) *
         (if Nat.eq_dec k i then 1%Z else 0%Z))%Rng with 1%Z. 2: {
        rewrite (summation_split i). 2: {
          split; [ flia | ].
          apply -> Nat.succ_le_mono.
          now apply Nat.lt_le_incl.
        }
        destruct i. {
          rewrite summation_only_one, Nat.add_0_l.
          rewrite all_0_summation_0; [ easy | ].
          intros j Hj.
          destruct (Nat.eq_dec 0 j) as [H| H]; [ flia Hj H | easy ].
        }
        rewrite summation_split_last; [ | flia ].
        rewrite all_0_summation_0. 2: {
          intros j Hj.
          destruct (Nat.eq_dec (S i) j) as [H| H]; [ flia Hj H | clear H ].
          destruct (Nat.eq_dec j (S i)) as [H| H]; [ flia Hj H | easy ].
        }
        rewrite all_0_summation_0. 2: {
          intros j Hj.
          destruct (Nat.eq_dec (S i) j) as [H| H]; [ flia Hj H | clear H ].
          destruct (Nat.eq_dec j (S i)) as [H| H]; [ flia Hj H | easy ].
        }
        now destruct (Nat.eq_dec (S i) (S i)).
      }
      rewrite Z.add_1_r.
      rewrite Nat2Z.inj_succ; f_equal.
      clear Hi.
Compute (let (n, i) := (3, 7) in (Σ (k = 0, 2 ^ n - 1), matel (A n) i k * matel (A n) k i)%Rng = Z.of_nat n).
Compute (let (n, i) := (3, 7) in map (λ k, (matel (A n) i k * matel (A n) k i)%Rng) (seq 0 (2 ^ n))).
Compute (let (n, i) := (3, 6) in map (λ k, (matel (A n) i k * matel (A n) k i)%Rng) (seq 0 (2 ^ n))).
Compute (let (n, i) := (3, 5) in map (λ k, (matel (A n) i k * matel (A n) k i)%Rng) (seq 0 (2 ^ n))).
       replace
         ((Σ (k = 0, 2 ^ n - 1), matel (A n) i k * matel (A n) k i)%Rng)
       with
         ((Σ (k = 0, 2 ^ n - 1), matel (A n) i k * matel (A n) i k)%Rng). 2: {
         apply summation_compat.
         intros j Hj.
         now rewrite A_symm.
       }
       destruct n; [ easy | clear Hnz ].
       revert i Hin.
       induction n; intros. {
         cbn in Hin.
         destruct i; [ easy | ].
         destruct i; [ easy | flia Hin ].
       }
       remember (2 ^ S (S n)) as n1; remember (S n) as n2.
       cbn - [ summation ]; subst.
       remember (2 ^ S (S n)) as n1; remember (S n) as n2.
       cbn - [ summation ]; subst.
       destruct (lt_dec i (2 ^ S n)) as [Hisn| Hisn]. {
         rewrite (summation_split (2 ^ S n - 1)). 2: {
           split; [ flia | cbn; flia ].
         }
         rewrite Nat.sub_add. 2: {
           now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
         }
         replace (Σ (_ = _, _), _)%Rng with
             (Σ (k = 0, 2 ^ S n - 1),
              matel (A (S n)) i k * matel (A (S n)) i k)%Rng. 2: {
           apply summation_compat.
           intros k Hk.
           assert (Hz : 2 ^ S n ≠ 0) by now apply Nat.pow_nonzero.
           destruct (lt_dec k (2 ^ S n)) as [H| H]; [ easy | flia Hk H Hz ].
         }
         rewrite IHn; [ | easy ].
         replace (Σ (_ = _, _), _)%Rng with
             (Σ (k = 2 ^ S n, 2 ^ S (S n) - 1),
              ((if Nat.eq_dec i (k - 2 ^ S n) then 1 else 0) *
               (if Nat.eq_dec i (k - 2 ^ S n) then 1 else 0)))%Rng. 2: {
           apply summation_compat.
           intros k Hk.
           destruct (lt_dec k (2 ^ S n)) as [H| H]; [ flia Hk H | easy ].
         }
         rewrite (summation_split (i + 2 ^ S n - 1)). 2: {
           split; [ flia | ].
           apply -> Nat.succ_le_mono.
           apply Nat.sub_le_mono_r.
           remember (S n) as sn; cbn; subst sn.
           flia Hisn.
         }
         rewrite all_0_summation_0. 2: {
           intros k Hk.
           destruct (Nat.eq_dec i (k - 2 ^ S n)) as [Hik| Hik]; [ | easy ].
           flia Hk Hik Hisn.
         }
         rewrite Nat.sub_add; [ | flia Hisn ].
         rewrite summation_split_first. 2: {
           cbn; cbn in Hisn; flia Hisn.
         }
         rewrite Nat.add_sub.
         destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
         rewrite all_0_summation_0. 2: {
           intros k Hk.
           destruct (Nat.eq_dec i (k - 2 ^ S n)) as [Hik| Hik]; [ | easy ].
           flia Hk Hik Hisn.
         }
         cbn.
         now rewrite Pos.add_1_r.
       } {
         apply Nat.nlt_ge in Hisn.
         rewrite (summation_split (2 ^ S n - 1)). 2: {
           split; [ flia | cbn; flia ].
         }
         rewrite Nat.sub_add. 2: {
           now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
         }
         replace (Σ (_ = _, _), _)%Rng with
             (Σ (k = 0, 2 ^ S n - 1),
              (if Nat.eq_dec (i - 2 ^ S n) k then 1 else 0) *
              (if Nat.eq_dec (i - 2 ^ S n) k then 1 else 0))%Rng. 2: {
           apply summation_compat.
           intros k Hk.
           assert (Hz : 2 ^ S n ≠ 0) by now apply Nat.pow_nonzero.
           destruct (lt_dec k (2 ^ S n)) as [H| H]; [ easy | flia Hk H Hz ].
         }
         destruct (Nat.eq_dec i (2 ^ S n)) as [Hiz| Hiz]. {
           rewrite Hiz, Nat.sub_diag.
           rewrite summation_split_first; [ | flia ].
           destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
           rewrite all_0_summation_0. 2: {
             intros k Hk.
             destruct (Nat.eq_dec 0 k) as [H| H]; [ flia Hk H | easy ].
           }
           replace (Σ (_ = _, _), _)%Rng with
               (Σ (k = 2 ^ S n, 2 ^ S (S n) - 1),
                ((matel (A (S n)) 0 (k - 2 ^ S n)) *
                 (matel (A (S n)) 0 (k - 2 ^ S n))))%Rng. 2: {
             apply summation_compat.
             intros k Hk.
             destruct (lt_dec k (2 ^ S n)) as [H| H]; [ flia Hk H | ].
             rewrite rng_mul_opp_l, rng_mul_opp_r.
             now rewrite rng_opp_involutive.
           }
           rewrite summation_shift; [ | cbn; flia ].
           replace (2 ^ S (S n) - 1 - 2 ^ S n) with (2 ^ S n - 1). 2: {
             cbn; flia.
           }
           replace (Σ (_ = _, _), _)%Rng with
             (Σ (k = 0, 2 ^ S n - 1),
              matel (A (S n)) 0 k * matel (A (S n)) 0 k)%Rng. 2: {
             apply summation_compat.
             intros k Hk.
             now rewrite Nat.add_comm, Nat.add_sub.
           }
           rewrite Z.mul_1_l, Z.add_0_r, Z.add_1_l.
           rewrite IHn; [ | now apply Nat.neq_0_lt_0, Nat.pow_nonzero ].
           symmetry; apply Zpos_P_of_succ_nat.
         }
         remember (S n) as sn; cbn in Hin; subst sn.
         rewrite (summation_split (i - 2 ^ S (n) - 1)). 2: {
           split; [ flia | flia Hin ].
         }
         rewrite all_0_summation_0. 2: {
           intros k Hk.
           destruct (Nat.eq_dec (i - 2 ^ S n) k) as [H| H]; [ | easy ].
           flia Hisn Hiz Hk H.
         }
         rewrite Nat.sub_add; [ | flia Hisn Hiz ].
         rewrite summation_split_first; [ | flia Hin ].
         destruct (Nat.eq_dec (i - 2 ^ S n) (i - 2 ^ S n)) as [H| H]. 2: {
           easy.
         }
         clear H.
         rewrite all_0_summation_0. 2: {
           intros k Hk.
           destruct (Nat.eq_dec (i - 2 ^ S n) k) as [H| H]; [ | easy ].
           flia Hisn Hiz Hk H.
         }
         replace (Σ (_ = _, _), _)%Rng with
             (Σ (k = 2 ^ S n, 2 ^ S (S n) - 1),
              ((matel (A (S n)) (i - 2 ^ S n) (k - 2 ^ S n)) *
               (matel (A (S n)) (i - 2 ^ S n) (k - 2 ^ S n))))%Rng. 2: {
           apply summation_compat.
           intros k Hk.
           destruct (lt_dec k (2 ^ S n)) as [H| H]; [ flia Hk H | ].
           rewrite rng_mul_opp_l, rng_mul_opp_r.
           now rewrite rng_opp_involutive.
         }
         rewrite summation_shift; [ | cbn; flia ].
         replace (2 ^ S (S n) - 1 - 2 ^ S n) with (2 ^ S n - 1). 2: {
           cbn; flia.
         }
         replace (Σ (_ = _, _), _)%Rng with
           (Σ (k = 0, 2 ^ S n - 1),
            matel (A (S n)) (i - 2 ^ S n) k *
            matel (A (S n)) (i - 2 ^ S n) k)%Rng. 2: {
           apply summation_compat.
           intros k Hk.
           now rewrite Nat.add_comm, Nat.add_sub.
         }
         rewrite IHn; [ | flia Hin ].
         rewrite Z.mul_1_l, Z.add_0_r, Z.add_1_l.
         symmetry; apply Zpos_P_of_succ_nat.
       }
    }
    replace (2 ^ n) with (S (2 ^ n - 1)) at 2. 2: {
      assert (H : 2 ^ n ≠ 0) by now apply Nat.pow_nonzero.
      flia H.
    }
    rewrite summation_split_last, rng_add_assoc; [ | flia ].
    rewrite <- summation_add_distr.
    destruct (Nat.eq_dec i (S (2 ^ n - 1))) as [H| H]; [ flia Hin H | ].
    clear H.
    rewrite rng_mul_0_l, rng_add_0_r.
Compute (let '(i, j, n) := (1, 2, 3) in map (λ k, (matel (A n) i k * matel (A n) k j)%Rng) (seq 0 8)).
Compute (let '(i, j, n) := (2, 1, 3) in map (λ k, (matel (A n) i k * matel (A n) k j)%Rng) (seq 0 8)).
Compute (let '(i, j, n) := (0, 1, 3) in map (λ k, (matel (A n) i k * matel (A n) k j)%Rng) (seq 0 8)).
    replace (Σ (_ = _, _), _)%Rng with
      (Σ (k = 0, 2 ^ n - 1), matel (A n) i k * matel (A n) j k)%Rng. 2: {
      apply summation_compat.
      intros k Hk.
      destruct (Nat.eq_dec i k) as [Hik| Hik]. {
        destruct (Nat.eq_dec k j) as [Hkj| Hkj]. {
          now rewrite Hik in Hij.
        }
        rewrite rng_mul_0_r, rng_add_0_r.
        now rewrite (A_symm _ k).
      }
      rewrite rng_mul_0_l, rng_add_0_r.
      now rewrite (A_symm _ k).
    }
    clear Hi Hj.
    destruct n; [ easy | clear Hnz ].
    revert i j Hin Hjn Hij.
    induction n; intros. {
      cbn in Hin, Hjn.
      destruct i. {
        destruct j; [ easy | ].
        destruct j; [ easy | flia Hjn ].
      }
      destruct i; [ | flia Hin ].
      destruct j; [ easy | ].
      destruct j; [ easy | flia Hjn ].
    }
    remember (S n) as sn; cbn - [ summation ]; subst sn.
    remember (S n) as sn; cbn - [ summation ]; subst sn.
    rewrite Nat.add_0_r.
    destruct (lt_dec i (2 ^ S n)) as [Hisn| Hisn]. {
      destruct (lt_dec j (2 ^ S n)) as [Hjsn| Hjsn]. {
        rewrite (summation_split (2 ^ S n - 1)) by flia.
        assert (Hz : 2 ^ S n ≠ 0) by now apply Nat.pow_nonzero.
        replace (Σ (_ = _, _), _)%Rng with
          (Σ (k = 0, 2 ^ S n - 1),
           ((matel (A (S n)) i k) * (matel (A (S n)) j k)))%Rng. 2: {
          apply summation_compat; intros k Hk.
          destruct (lt_dec k (2 ^ S n)) as [H| H]; [ easy | flia Hk Hz H ].
        }
        rewrite IHn; [ | easy | easy | easy ].
        rewrite Nat.sub_add; [ | flia Hz ].
        replace (Σ (_ = _, _), _)%Rng with
          (Σ (k = 2 ^ S n, 2 ^ S n + 2 ^ S n - 1),
           ((if Nat.eq_dec i (k - 2 ^ S n) then 1 else 0) *
            (if Nat.eq_dec j (k - 2 ^ S n) then 1 else 0)))%Rng. 2: {
          apply summation_compat; intros k Hk.
          destruct (lt_dec k (2 ^ S n)) as [H| H]; [ flia Hk H | easy ].
        }
        rewrite all_0_summation_0; [ easy | ].
        intros k Hk.
        destruct (Nat.eq_dec i (k - 2 ^ S n)) as [Hikn| Hikn]; [ | easy ].
        destruct (Nat.eq_dec j (k - 2 ^ S n)) as [Hjkn| Hjkn]; [ | easy ].
        now rewrite <- Hjkn in Hikn.
      } {
        apply Nat.nlt_ge in Hjsn.
        rewrite (summation_split (2 ^ S n - 1)) by flia.
        assert (Hz : 2 ^ S n ≠ 0) by now apply Nat.pow_nonzero.
        replace (Σ (_ = _, _), _)%Rng with
          (Σ (k = 0, 2 ^ S n - 1),
           ((matel (A (S n)) i k) *
            (if Nat.eq_dec (j - 2 ^ S n) k then 1 else 0)))%Rng. 2: {
          apply summation_compat; intros k Hk.
          destruct (lt_dec k (2 ^ S n)) as [H| H]; [ easy | flia Hk Hz H ].
        }
        rewrite Nat.sub_add; [ | flia Hz ].
        replace (Σ (_ = 2 ^ S n, _), _)%Rng with
          (Σ (k = 2 ^ S n, 2 ^ S n + 2 ^ S n - 1),
           ((if Nat.eq_dec i (k - 2 ^ S n) then 1 else 0) *
            (- matel (A (S n)) (j - 2 ^ S n) (k - 2 ^ S n))))%Rng. 2: {
          apply summation_compat; intros k Hk.
          destruct (lt_dec k (2 ^ S n)) as [H| H]; [ flia Hk H | easy ].
        }
        rewrite (summation_shift (2 ^ S n)); [ | flia ].
        rewrite Nat_sub_sub_swap, Nat.add_sub.
        rewrite <- summation_add_distr.
        replace (Σ (_ = _, _), _)%Rng with
          (Σ (k = 0, 2 ^ S n - 1),
           (matel (A (S n)) i k *
            (if Nat.eq_dec (j - 2 ^ S n) k then 1 else 0) -
           (matel (A (S n)) (j - 2 ^ S n) k *
            (if Nat.eq_dec i k then 1 else 0))))%Rng. 2: {
          apply summation_compat; intros k Hk.
          rewrite rng_mul_opp_r, fold_rng_sub.
          rewrite Nat.add_comm, Nat.add_sub.
          now rewrite (rng_mul_comm (matel _ (j - _) _)).
        }
        remember (j - 2 ^ S n) as l eqn:Hl.
        assert (Hlsn : l < 2 ^ S n). {
          remember (S n) as sn; cbn in Hjn; subst sn.
          flia Hl Hjn.
        }
        move l before j.
        clear j Hjn Hij Hjsn Hl.
        rename l into j; rename Hlsn into Hjsn.
        move Hjsn before Hisn.
        destruct (Nat.eq_dec i j) as [Hij| Hij]. {
          subst j.
          apply all_0_summation_0.
          intros k Hk.
          apply Z.sub_diag.
        }
        destruct (lt_dec i j) as [Hlij| Hlij]. {
          destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
            subst i.
            rewrite summation_split_first; [ | flia ].
            rewrite A_diag, rng_mul_0_l, Z.sub_0_l.
            destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
            rewrite rng_mul_1_r.
            rewrite (summation_split (j - 1)) by flia Hjsn.
            rewrite all_0_summation_0. 2: {
              intros k Hk.
              destruct (Nat.eq_dec j k) as [H| Hjk]; [ flia H Hk | ].
              destruct (Nat.eq_dec 0 k) as [H| H]; [ flia H Hk | ].
              now rewrite <- rng_mul_sub_distr_r, rng_mul_0_r.
            }
            rewrite Nat.sub_add; [ | easy ].
            rewrite summation_split_first; [ | flia Hjsn ].
            destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
            rewrite A_diag, rng_mul_0_l, rng_sub_0_r.
            rewrite all_0_summation_0. 2: {
              intros k Hk.
              destruct (Nat.eq_dec j k) as [H| H]; [ flia Hk H | clear H ].
              destruct (Nat.eq_dec 0 k) as [H| H]; [ flia Hk H | clear H ].
              now rewrite <- rng_mul_sub_distr_r, rng_mul_0_r.
            }
            rewrite rng_add_0_l, rng_mul_1_r, rng_add_0_r.
            rewrite A_symm.
            apply rng_add_opp_l.
          } {
            rewrite (summation_split (i - 1)).
(* terminable... mais interminable... *)
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
