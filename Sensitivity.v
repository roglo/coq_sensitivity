(* Sensitivity Theorem proved by Hao Huang.
   https://arxiv.org/pdf/1907.00847.pdf
   https://eccc.weizmann.ac.il/report/2020/002/?fbclid=IwAR19mpxfIuoSaWq3HO8MdV8i8x_xlvwMKHjfElzBUK0GditlyaLeJiC8gJY *)

Set Nested Proofs Allowed.
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

Lemma nth_find_nth_find_all_loop : ∀ A (f : A → bool) l i,
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

Lemma not_in_nth_find_loop : ∀ A f (l : list A) i j,
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

Lemma not_in_nth_find_all_loop : ∀ A f (l : list A) i j,
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

Lemma in_nth_find_all_loop_eqb : ∀ l i k b,
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

Lemma in_nth_find_all_loop_eqb_if : ∀ a l d,
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

Lemma in_flat_map_nth_find_all_loop_eq : ∀ l j k len b,
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

Lemma flat_map_nth_find_all_loop_cons : ∀ a l k i len,
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

Lemma nth_find_loop_map : ∀ A B f (g : A → B) i l,
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
specialize (in_nth_find_all_loop_eqb_if a l 0 Ha) as H1.
now rewrite Nat.add_0_r in H1.
Qed.

Lemma to_radix_loop_length : ∀ it n i, length (to_radix_loop it n i) = it.
Proof.
intros.
revert n i.
induction it; intros; [ easy | cbn ].
now rewrite IHit.
Qed.

Lemma in_to_radix_loop : ∀ it n i a,
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

Lemma nth_find_all_loop_app : ∀ A f (l1 l2 : list A) i,
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

Lemma eq_nth_find_all_loop_cons : ∀ A f j (d : A) l l' i,
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
      specialize (not_in_nth_find_all_loop _ f l _ _ Hij) as H1.
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
      specialize (not_in_nth_find_all_loop _ f l j (i + 1)) as H1.
      assert (H : j < i + 1) by flia Hji.
      specialize (H1 H); clear H.
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
      specialize (not_in_nth_find_all_loop _ f l _ _ Hij) as H1.
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
specialize (eq_nth_find_all_loop_cons _ f j d l l' 0) as H1.
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

Lemma in_nth_nth_find_loop : ∀ ll i d,
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
specialize (in_nth_nth_find_loop ll j 0 Huni Hi) as H1.
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

Lemma eq_nth_find_all_loop_iff : ∀ A f (d : A) l l1 i,
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

Lemma fold_left_horner_eval_sum : ∀ k n a x,
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
  apply (eq_nth_find_all_loop_cons _ _ _ 0).
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

   Lemma 2.1. (Cauchy’s Interlace Theorem) Let A be a symmetric n×n matrix,
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

Require Import Ring2 Rsummation Rpolynomial2.

(* the type "matrix" defines infinite sized matrices; the limited size
   is given by functions such that mat_mul which, multiplying a m×n
   matrix with a n×p matrix, n is given as parameter of mat_mul *)

Record matrix A := { matel : nat → nat → A }.

Arguments matel {_}.

Definition mat_of_list {A} (d : A) ll :=
  {| matel i j := nth i (nth j ll []) d |}.

Definition list_of_mat {A} nrow ncol (M : matrix A) :=
  map (λ row, map (λ col, matel M row col) (seq 0 ncol)) (seq 0 nrow).

Definition mat_transp {T} (M : matrix T) :=
  {| matel i j := matel M j i |}.

Definition mat_mul {T} {ro : ring_op T} n A B :=
  {| matel i k := (Σ (j = 0, n - 1), matel A i j * matel B j k)%Rng |}.

Definition mat_sqr {T} {ro : ring_op T} n A := mat_mul n A A.

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
  "Lemma 2.2. We define a sequence of symmetric square matrices
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

Definition eqmt_of_eqt T (eqt : T → T → Prop) n M1 M2 :=
  ∀ i j, i < n → j < n → eqt (matel M1 i j) (matel M2 i j).

Theorem mat_mat_even_mat : ∀ T eqt (MM : matrix (matrix T)) n,
  Equivalence eqt
  → n ≠ 0
  → mat_eq (eqmt_of_eqt T eqt n)
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

Fixpoint A {T} {ro : ring_op T} n :=
  match n with
  | 0 => mat_of_list 0%Rng []
  | 1 => mat_of_list 0%Rng [[0; 1]; [1; 0]]%Rng
  | S n' =>
      even_mat_of_mat_mat (2 ^ n')
        {| matel i j :=
             if Nat.eq_dec i 0 then
               if Nat.eq_dec j 0 then A n' else I
             else
               if Nat.eq_dec j 0 then I else mat_opp (A n') |}
  end.

Definition mat_add {T} {ro : ring_op T} A B :=
  {| matel i j := (matel A i j + matel B i j)%Rng |}.

Definition mat_ring_op {T} {ro : ring_op T} n :=
  {| rng_zero := zero_mat;
     rng_one := I;
     rng_add := mat_add;
     rng_mul := mat_mul n;
     rng_opp := mat_opp |}.

Open Scope Z_scope.

Compute (list_of_mat 2 2 (let _ := Z_ring_op in A 1)).
Compute (list_of_mat 4 4 (let _ := Z_ring_op in A 2)).
Compute (list_of_mat 8 8 (let _ := Z_ring_op in A 3)).
Compute (list_of_mat 16 16 (let _ := Z_ring_op in A 4)).

Close Scope Z_scope.

Section glop.

Context {T : Type}.
Context {ro : ring_op T}.
Context {rp : ring_prop}.

Theorem I_i_i : ∀ i, matel I i i = 1%Rng.
Proof.
intros; cbn.
now destruct (Nat.eq_dec i i).
Qed.

Theorem I_i_j : ∀ i j, i ≠ j → matel I i j = 0%Rng.
Proof.
intros * Hij; cbn.
now destruct (Nat.eq_dec i j).
Qed.

Theorem A_i_i : ∀ n i, matel (A n) i i = 0%Rng.
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
destruct (Nat.eq_dec (i / 2 ^ n1) 0) as [Hin| Hin]. {
  destruct (Nat.eq_dec (j / 2 ^ n1) 0) as [Hjn| Hjn]; [ apply IHn | ].
  apply I_symm.
} {
  destruct (Nat.eq_dec (j / 2 ^ n1) 0) as [Hjn| Hjn]; [ apply I_symm | ].
  now cbn; rewrite IHn.
}
Qed.

End glop.

(* "We prove by induction that A_n^2 = nI" *)

Definition nI n :=
  {| matel i j := if Nat.eq_dec i j then Z.of_nat n else 0%Z |}.

Definition fin_mat_eq {T} (eqt : T → T → Prop) u v (M M' : matrix T) :=
  ∀ i j, i < u → j < v → eqt (matel M i j) (matel M' i j).

(*
                   ⌈ (A_n)^2+I   0          ⌉
    (A_{n+1})^2 =  ⌊ 0           (A_n)^2+I  ⌋
*)

Lemma sqr_An1_from_sqr_An (R := Z_ring_op) : ∀ n,
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
  destruct (lt_dec j (2 ^ n)) as [Hjn| Hjn]. {
    destruct (Nat.eq_dec (j / 2 ^ n) 0) as [H| H]. 2: {
      now rewrite Nat.div_small in H.
    }
    clear H.
    rewrite Nat.mod_small; [ | easy ].
    clear Hi Hj.
(*
    revert i j Hin Hjn.
    induction n; intros. {
*)
    destruct n; intros. {
      cbn in Hin, Hjn.
      destruct i; [ | flia Hin ].
      destruct j; [ easy | flia Hjn ].
    }
    remember (S n) as sn; cbn - [ mat_sqr "^" I mat_add ]; subst sn.
    unfold even_mat_of_mat_mat.
    remember (S n) as sn; cbn - [ mat_sqr "/" "^" I mat_add ]; subst sn.
(**)
    cbn - [ summation "^" A I ].
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
         (matel (A (S n)) i k * matel (A (S n)) k j))%Rng. 2: {
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
    cbn - [ summation A I "^" ].
    f_equal.
    destruct (Nat.eq_dec i j) as [Hij| Hij]. {
      subst j.
      rewrite I_i_i.
      erewrite (summation_split (i + 2 ^ S n - 1)). 2: {
        split; [ flia | ].
        apply -> Nat.succ_le_mono.
        apply Nat.sub_le_mono_r.
        rewrite (Nat.pow_succ_r _ (S n)); [ flia Hin | flia ].
      }
      erewrite all_0_summation_0. 2: {
        intros k Hk.
        rewrite I_i_j; [ easy | flia Hk Hz ].
      }
      rewrite Nat.sub_add; [ | flia Hz ].
      rewrite summation_split_first. 2: {
        rewrite (Nat.pow_succ_r _ (S n)); [ | flia ].
        flia Hin.
      }
      rewrite Nat.add_sub, I_i_i.
      erewrite all_0_summation_0. 2: {
        intros k Hk.
        rewrite I_i_j; [ easy | flia Hk Hz ].
      }
      easy.
    }
    rewrite I_i_j; [ | easy ].
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
      now apply I_i_j.
    }
    left.
    now apply I_i_j.
  }
  apply Nat.nlt_ge in Hjn.
  rewrite (Nat_div_less_small 1) by now rewrite Nat.mul_1_l.
  destruct (Nat.eq_dec 1 0) as [H| H]; [ easy | clear H].
  cbn - [ A summation "^" ].
...
  erewrite all_0_summation_0; [ easy | ].
  intros k Hk.
  cbn - [ A ].
  apply Z.mul_eq_0.
  destruct (Nat.eq_dec i k) as [Hik| Hik]. {
    subst k; left.
    now erewrite A_i_i.
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

Lemma lemma_2_A_n_2_eq_n_I (R := Z_ring_op) : ∀ n,
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

(* previous version: worked, but had to be terminated *)

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

Theorem A_i_i : ∀ n i, matel (A n) i i = 0%Z.
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

Lemma lemma_2_A_n_2_eq_n_I (R := Z_ring) : ∀ n i j,
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
            rewrite A_i_i, rng_mul_0_l, Z.sub_0_l.
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
            rewrite A_i_i, rng_mul_0_l, rng_sub_0_r.
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
