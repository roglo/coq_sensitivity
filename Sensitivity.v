(* Sensitivity Theorem.
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

Search (nat → nat → nat).

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
  replace i with (i + 0) at 1 by easy.
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

(*
Lemma to_radix_loop_fold_left : ∀ it l n,
  n ≤ it
  → (∀ i, i ∈ l → i < n)
  → to_radix_loop it n (fold_left (λ a i, a * n + i) l 0) =
     rev l ++ repeat 0 (it - n).
Proof.
intros * Hlit Hil.
Compute (let l := [3; 2; 0] in let n := 4 in let it := 4 in (to_radix_loop it n (fold_left (λ a i, a * n + i) l 0), rev l ++ repeat 0 (it - n))).
...
revert n l Hlit Hil.
induction it; intros. {
  apply Nat.le_0_r in Hlit; subst n; cbn.
  destruct l as [| a]; [ easy | cbn ].
  now specialize (Hil a (or_introl eq_refl)).
}
destruct n. {
  clear; cbn; f_equal.
...
  clear; cbn; f_equal; rewrite app_nil_r.
  induction it; [ easy | now cbn; f_equal ].
}
cbn - [ "/" "mod" ].
rewrite Nat.sub_succ.
...
*)

(*
Lemma to_radix_loop_fold_left : ∀ it l,
  length l ≤ it
  → (∀ i, i ∈ l → i < length l)
  → to_radix_loop it (length l) (fold_left (λ a i, a * length l + i) l 0) =
     repeat 0 (it - length l) ++ l.
Proof.
intros * Hlit Hil.
revert l Hlit Hil.
induction it; intros. {
  apply Nat.le_0_r in Hlit.
  apply length_zero_iff_nil in Hlit.
  now subst l.
}
destruct l as [| a]. {
  clear; cbn; f_equal; rewrite app_nil_r.
  induction it; [ easy | now cbn; f_equal ].
}
cbn - [ "/" "mod" ].
rewrite Nat.sub_succ.


Print to_radix_loop.
Print locate.
Print locate_list.
(* ouais bon, faut voir ; peut-être généraliser ce lemme *)
...
*)

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

(*
Theorem fold_left_mul_add_mod_r : ∀ n j k l,
  fold_left (λ a i : nat, a * n + i) l (j * n + k) ≡ last (k :: l) 0 mod n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
rewrite fold_left_mul_add_mod.
destruct l as [| b]; [ cbn | easy ].
now apply Nat_mod_add_l_mul_r.
Qed.
*)

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

(*
Theorem to_radix_fold_left : ∀ l,
  (∀ i, i ∈ l → i < length l)
  → to_radix (length l) (fold_left (λ a i, a * length l + i) l 0) = rev l.
Proof.
intros * Hil.
unfold to_radix.
remember (length l) as n eqn:Hn.
destruct l as [| a1]; [ now subst n | ].
cbn - [ "/" "mod" rev ].
Print to_radix_loop.
...
intros * Hil.
unfold to_radix.
destruct l as [| a1]; [ easy | ].
cbn - [ "/" "mod" rev ].
rewrite (@app_removelast_last nat (a1 :: l) 0); [ | easy ].
rewrite rev_app_distr.
cbn - [ "/" "mod" last removelast ].
f_equal. {
  rewrite fold_left_mul_add_mod.
  apply Nat.mod_small.
  apply Hil.
  clear.
  revert a1.
  induction l as [| a2]; intros; [ now left | right ].
  apply IHl.
}
destruct l as [| a2]; [ easy | ].
remember (rev (removelast _)) as l'.
cbn - [ "/" "mod" rev ].
subst l'.
rewrite (@app_removelast_last nat (removelast _) 0); [ | easy ].
rewrite rev_app_distr.
cbn - [ "/" "mod" last removelast ].
f_equal. {
  remember (S (S (length l))) as len eqn:Hlen.
  clear - Hil Hlen.
  remember (a2 :: l) as l'; cbn; subst l'.
  remember (length (a1 :: a2 :: l)) as len'; cbn in Heqlen'; subst len'.
  rewrite <- Hlen in Hil.
  clear Hlen.
  destruct l as [| a3]. {
    cbn.
    rewrite Nat.div_add_l. 2: {
      intros H; subst len.
      now specialize (Hil a1 (or_introl eq_refl)).
    }
    rewrite Nat.div_small; [ | now apply Hil; right; left ].
    rewrite Nat.add_0_r.
    now apply Nat.mod_small, Hil; left.
  }
  rewrite fold_left_mul_add_div; [ | | easy ]. 2: {
    intros i Hi.
    now apply Hil; right; right.
  }
  cbn - [ removelast ].
  remember (a3 :: l) as l'; cbn; subst l'.
...
  ============================
  fold_left (λ a i : nat, a * len + i) (removelast (a3 :: l)) (a1 * len + a2)
  mod len = last (a2 :: removelast (a3 :: l)) 0
...
*)

(*
Theorem locate_list_to_radix_locate : ∀ ll,
  locate_list ll = rev (to_radix (length ll) (locate ll)).
Proof.
intros.
unfold locate.
Compute (let l := [1; 2; 2] in rev (to_radix (length l) (fold_left (λ a i : nat, a * length l + i) l 0))).
Search to_radix_loop.
...
intros.
unfold to_radix.
induction ll as [| l]; [ easy | ].
Print locate_list.
Print locate.
...

locate_list = 
λ ll : list (list nat),
  map (λ i : nat, nth_find (nat_in_list i) ll) (seq 0 (length ll))

locate = 
λ ll : list (list nat),
  fold_left (λ a i : nat, a * length ll + i) (locate_list ll) 0
     : list (list nat) → nat
...
cbn - [ "/" "mod" ].
...
*)

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

(*
Lemma nth_find_all_loop_map_seq : ∀ a ll,
  (∀ l, l ∈ ll → ∀ i, i ∈ l → i < length ll)
  → (∀ i, i < length ll → ∃ l : list nat, l ∈ ll ∧ i ∈ l)
  → NoDup (concat ll)
  → (∀ l, l ∈ ll → Sorted lt l)
  → nth_find_all_loop (Nat.eqb a)
       (map (λ i, nth_find (nat_in_list i) ll)
          (seq (hd 0 (nth a ll []) + 1)
             (length ll - (hd 0 (nth a ll []) + 1))))
       (hd 0 (nth a ll []) + 1) = tl (nth a ll []).
Proof.
intros * Hin Huni Hint Hsort.
remember (nth a ll []) as l eqn:Hl; symmetry in Hl.
(*1*)
induction l as [| b]. {
  cbn.
  apply eq_nth_find_all_loop_nil.
  intros j Hj.
  apply in_map_iff in Hj.
  destruct Hj as (i & Hli & Hil).
  apply Bool.not_true_iff_false.
  intros H.
  apply Nat.eqb_eq in H; subst j a.
  apply in_seq in Hil.
  specialize (in_nth_nth_find ll i Huni) as H1.
  assert (H : i < length ll) by flia Hil.
  specialize (H1 H); clear H.
  now rewrite Hl in H1.
}
cbn.
(*2*)
destruct l as [| b1]. {
  apply eq_nth_find_all_loop_nil.
  intros j Hj.
  apply in_map_iff in Hj.
  destruct Hj as (i & Hli & Hil).
  apply Bool.not_true_iff_false.
  intros Haj.
  apply Nat.eqb_eq in Haj.
  apply in_seq in Hil.
  specialize (in_nth_nth_find ll i Huni) as H1.
  assert (H : i < length ll) by flia Hil.
  specialize (H1 H); clear H.
  rewrite Hli, <- Haj, Hl in H1.
  destruct H1 as [H1| H1]; [ | easy ].
  rewrite H1 in Hil.
  flia Hil.
}
(*3*)
destruct l as [| b2]. {
(*
replace [b1] with (tl (nth a ll [])) by now rewrite Hl.
replace b with (hd 0 (nth a ll [])) by now rewrite Hl.
remember (nth a ll []) as l.
clear Heql Hl.
apply (proj2 (@eq_nth_find_all_loop_iff nat (Nat.eqb a) 0 _ _ _)).
...
*)
  apply (proj2 (eq_nth_find_all_loop_cons _ _ b1 0 _ [] (b + 1))).
  rewrite map_length, seq_length.
  assert (Halt : a < length ll). {
    apply Nat.nle_gt; intros H.
    now rewrite nth_overflow in Hl.
  }
  assert (Hb1 : b1 < length ll). {
    apply (Hin [b; b1]); [ | now right; left ].
    rewrite <- Hl.
    now apply nth_In.
  }
  assert (Hbb1 : b < b1). {
    specialize (Hsort (nth a ll [])) as H1.
    specialize (@nth_In _ a ll [] Halt) as H2.
    specialize (H1 H2); clear H2.
    rewrite Hl in H1.
    cbn in H1.
    apply Sorted_inv in H1.
    destruct H1 as (_, H1).
    now apply HdRel_inv in H1.
  }
  split; [ flia Hb1 Hbb1 | ].
  split. {
    intros k Hk.
    apply Bool.not_true_iff_false.
    intros Ha.
    apply Nat.eqb_eq in Ha.
    rewrite (List_map_nth_in _ 0) in Ha. 2: {
      rewrite seq_length.
      flia Hk Hb1.
    }
    rewrite seq_nth in Ha; [ | flia Hk Hb1 ].
    specialize (in_nth_nth_find ll (b + 1 + k) Huni) as H1.
    assert (H : b + 1 + k < length ll) by flia Hk Hb1.
    specialize (H1 H); clear H.
    rewrite <- Ha, Hl in H1.
    destruct H1 as [H1| H1]; [ flia H1 | ].
    destruct H1 as [H1| H1]; [ | easy ].
    flia Hk H1.
  }
  split. {
    apply Nat.eqb_eq.
    rewrite (List_map_nth_in _ 0). 2: {
      rewrite seq_length.
      flia Hb1 Hbb1.
    }
    rewrite seq_nth; [ | flia Hb1 Hbb1 ].
    rewrite Nat.add_sub_assoc; [ | flia Hbb1 ].
    rewrite Nat.add_comm, Nat.add_sub.
    specialize (in_nth_nth_find ll b1 Huni Hb1) as H1.
    remember (nth_find (nat_in_list b1) ll) as c eqn:Hc.
    move Hl before H1.
    assert (H2 : b1 ∈ nth a ll []) by now rewrite Hl; right; left.
    now apply (NoDup_concat_in_in _ ll b1).
  }
  apply eq_nth_find_all_loop_nil.
  intros j Hj.
  apply Nat.eqb_neq; intros H; subst j.
  rewrite List_skipn_map in Hj.
  rewrite List_skipn_seq in Hj; [ | flia Hb1 Hbb1 ].
  replace (b + 1 + (b1 + 1 - (b + 1))) with (b1 + 1) in Hj by flia Hbb1.
  replace (length ll - (b + 1) - (b1 + 1 - (b + 1))) with
    (length ll - (b1 + 1)) in Hj by flia Hbb1.
  apply in_map_iff in Hj.
  destruct Hj as (i & Hli & Hil).
  apply in_seq in Hil.
  specialize (in_nth_nth_find ll i Huni) as H1.
  assert (H : i < length ll) by flia Hil.
  specialize (H1 H); clear H.
  rewrite Hli, Hl in H1.
  destruct H1 as [H1| H1]; [ flia Hbb1 H1 Hil | ].
  destruct H1 as [H1| H1]; [ flia H1 Hil | easy ].
}
...
  Hl : nth a ll [] = b :: b1 :: b2 :: l
  ============================
  nth_find_all_loop (Nat.eqb a)
    (map (λ i : nat, nth_find (nat_in_list i) ll)
       (seq (b + 1) (length ll - (b + 1)))) (b + 1) = 
  b1 :: b2 :: l
...
  Hl : nth a ll [] = b :: b1 :: l
  ============================
  nth_find_all_loop (Nat.eqb a)
    (map (λ i : nat, nth_find (nat_in_list i) ll)
       (seq (b + 1) (length ll - (b + 1)))) (b + 1) = 
  b1 :: l
...
  Hl : nth a ll [] = b :: l
  ============================
  nth_find_all_loop (Nat.eqb a)
    (map (λ i : nat, nth_find (nat_in_list i) ll)
       (seq (b + 1) (length ll - (b + 1)))) (b + 1) = l
...
  Hl : nth a ll [] = l
  ============================
  nth_find_all_loop (Nat.eqb a)
    (map (λ i : nat, nth_find (nat_in_list i) ll)
       (seq (hd 0 l + 1) (length ll - (hd 0 l + 1)))) 
    (hd 0 l + 1) = tl l
...
*)

(*
Theorem dispatch_locate_list : ∀ ll,
  is_pre_partition ll
  → dispatch_list (locate_list ll) = ll.
Proof.
intros * Hll.
unfold dispatch_list.
rewrite locate_list_length.
replace ll with (map (λ i, nth i ll []) (seq 0 (length ll))) at 2. 2: {
  clear.
  induction ll as [| l]; [ easy | ].
  f_equal; cbn; f_equal.
  rewrite <- seq_shift.
  now rewrite map_map.
}
apply map_ext_in_iff.
intros a Ha.
apply in_seq in Ha; destruct Ha as (_, Ha); cbn in Ha.
destruct Hll as (Hin & Huni & Hint & Hsort).
(*
clear Huni.
*)
unfold locate_list.
unfold nth_find_all.
revert a Ha.
induction ll as [| l1]; intros; [ easy | ].
cbn - [ nth ].
remember (nat_in_list 0 l1) as b1 eqn:Hb1; symmetry in Hb1.
destruct b1. {
  remember (a =? 0) as az eqn:Haz; symmetry in Haz.
  destruct az. {
    apply Nat.eqb_eq in Haz; subst a.
    clear Ha.
    cbn - [ Nat.eqb ].
    apply nat_in_list_true_iff in Hb1.
    destruct l1 as [| a1]; [ easy | ].
    destruct Hb1 as [Hb1| Hb1]. {
      subst a1; f_equal.
      cbn in Hint.
      replace (map _ _) with
        (map
           (λ i,
            if nat_in_list i l1 then 0
            else
              nth_find_loop (nat_in_list i) ll 1) (seq 1 (length ll))). 2: {
        apply map_ext_in_iff.
        intros a Ha.
        apply in_seq in Ha; cbn.
        destruct (Nat.eq_dec a 0) as [Haz| Haz]; [ flia Ha Haz | easy ].
      }
      remember (map _ _) as m eqn:Hm in |-*.
      apply (proj2 (@eq_nth_find_all_loop_iff nat (Nat.eqb 0) 0 _ _ _)).
      destruct l1 as [| a1]. {
        intros j Hj.
        subst m.
        apply in_map_iff in Hj.
        destruct Hj as (i & Hij & Hi).
        cbn in Hij.
        apply Bool.not_true_iff_false; intros Hj.
        apply Nat.eqb_eq in Hj; move Hj at top; subst j.
        apply in_seq in Hi.
        specialize (not_in_nth_find_loop _ (nat_in_list i) ll 0 1) as H1.
        apply H1; [ flia | easy ].
      }
      split. {
        split. {
          apply Nat.neq_0_lt_0.
          intros H; subst a1.
          cbn in Hint.
          apply NoDup_cons_iff in Hint.
          destruct Hint as (H, _); apply H.
          now left.
        }
        rewrite Hm, map_length, seq_length.
        specialize (Hin _ (or_introl eq_refl) a1).
        specialize (Hin (or_intror (or_introl eq_refl))).
        now cbn in Hin.
      }
      split. {
        intros i Hi.
        apply Nat.eqb_neq; intros Him.
        symmetry in Him.
        assert (Hill : i < length ll). {
          specialize (Hin _ (or_introl eq_refl) a1).
          specialize (Hin (or_intror (or_introl eq_refl))).
          cbn in Hin.
          flia Hin Hi.
        }
        rewrite Hm, (List_map_nth_in _ 0) in Him; [ | now rewrite seq_length ].
        rewrite seq_nth in Him; [ | easy ].
        remember (nat_in_list (1 + i) (a1 :: l1)) as b eqn:Hb; symmetry in Hb.
        destruct b. {
          apply nat_in_list_true_iff in Hb; clear Him.
          destruct Hb as [Hb| Hb]; [ flia Hi Hb | ].
          specialize (Hsort _ (or_introl eq_refl)).
          apply Sorted_inv in Hsort.
          destruct Hsort as (Hsort, _).
          apply Sorted_extends in Hsort. 2: {
            intros x y z Hxy Hyz.
            now transitivity y.
          }
          specialize (proj1 (Forall_forall _ _) Hsort _ Hb) as H1.
          flia Hi H1.
        }
        symmetry in Him; revert Him.
        apply not_in_nth_find_loop; flia.
      }
      assert (Ha1 : a1 ≤ length ll). {
        specialize (Hin _ (or_introl eq_refl) a1).
        specialize (Hin (or_intror (or_introl eq_refl))).
        cbn in Hin; flia Hin.
      }
      split. {
        apply Nat.eqb_eq; symmetry.
        subst m.
        destruct (Nat.eq_dec a1 0) as [Ha1z| Ha1z]. {
          exfalso.
          subst a1.
          apply NoDup_cons_iff in Hint.
          destruct Hint as (H, _); apply H.
          now left.
        }
        rewrite (List_map_nth_in _ 0). 2: {
          rewrite seq_length.
          flia Ha1z Ha1.
        }
        rewrite seq_nth; [ | flia Ha1z Ha1 ].
        replace (1 + (a1 - 1)) with a1 by flia Ha1z; cbn.
        now destruct (Nat.eq_dec a1 a1).
      }
      rewrite Nat.add_sub.
      subst m.
      rewrite List_skipn_map.
      rewrite List_skipn_seq; [ | easy ].
      replace (map _ _) with
        (map
           (λ i,
            if nat_in_list i l1 then 0
            else
              nth_find_loop (nat_in_list i) ll 1)
                (seq (1 + a1) (length ll - a1))). 2: {
        apply map_ext_in_iff.
        intros a Ha.
        apply in_seq in Ha; cbn.
        destruct (Nat.eq_dec a a1) as [Haz| Haz]; [ flia Ha Haz | easy ].
      }
      apply (proj2 (@eq_nth_find_all_loop_iff nat (Nat.eqb 0) 0 _ _ _)).
      destruct l1 as [| b1]. {
        intros j Hj.
        apply Nat.eqb_neq; intros H; subst j.
        apply in_map_iff in Hj.
        destruct Hj as (j & Hjl & Hj).
        cbn in Hjl.
        symmetry in Hjl; revert Hjl.
        apply not_in_nth_find_loop; flia.
      }
      rewrite map_length, seq_length.
      remember (map _ _) as m eqn:Hm in |-*.
...
intros * Hll.
unfold dispatch_list.
rewrite locate_list_length.
replace ll with (map (λ i, nth i ll []) (seq 0 (length ll))) at 2. 2: {
  clear.
  induction ll as [| l]; [ easy | ].
  f_equal; cbn; f_equal.
  rewrite <- seq_shift.
  now rewrite map_map.
}
apply map_ext_in_iff.
intros a Ha.
remember (nth a ll []) as l eqn:Hl.
symmetry in Hl.
apply in_seq in Ha; destruct Ha as (_, Ha); cbn in Ha.
revert a Ha Hl.
induction l as [| b]; intros. {
  cbn.
  apply eq_nth_find_all_nil.
  intros i Hi.
  apply Nat.eqb_neq.
  intros H; subst i.
  apply in_map_iff in Hi.
  destruct Hi as (i & Hia & Hi).
  move i before a; move Hi before Ha.
  rewrite <- Hia in Hl.
  clear a Ha Hia.
  destruct Hll as (Hin & Huni & Hint & Hsort).
  clear Hint.
  apply in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
  specialize (in_nth_nth_find _ _ Huni Hi) as H1.
  now rewrite Hl in H1.
}
apply (proj2 (eq_nth_find_all_cons _ _ _ 0 _ _)).
destruct Hll as (Hin & Huni & Hint & Hsort).
assert (Hbl : b < length ll). {
  apply (Hin (b :: l)); [ | now left ].
  rewrite <- Hl.
  now apply nth_In.
}
assert (Hab : a = nth b (locate_list ll) 0). {
  unfold locate_list.
  rewrite (List_map_nth_in _ 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ cbn | easy ].
  specialize (in_nth_nth_find ll b Huni Hbl) as H1.
  assert (H2 : b ∈ nth a ll []) by now rewrite Hl; left.
  remember (nth_find (nat_in_list b) ll) as c eqn:Hc.
  now apply (NoDup_concat_in_in _ ll b).
}
split; [ now rewrite locate_list_length | ].
split. {
  intros k Hkb.
  apply Nat.eqb_neq; intros Hanl.
  unfold locate_list in Hanl.
  rewrite (List_map_nth_in _ 0) in Hanl. 2: {
    rewrite seq_length.
    now transitivity b.
  }
  rewrite seq_nth in Hanl; cbn in Hanl; [ | now transitivity b ].
  specialize (in_nth_nth_find ll k Huni) as H1.
  assert (H : k < length ll) by now transitivity b.
  specialize (H1 H); clear H.
  rewrite <- Hanl, Hl in H1.
  destruct H1 as [H1| H1]; [ subst k; flia Hkb | ].
  assert (H : b :: l ∈ ll). {
    rewrite <- Hl.
    now apply nth_In.
  }
  specialize (Hsort _ H) as H2; clear H.
  clear - H1 H2 Hkb.
  apply Sorted_LocallySorted_iff in H2.
  revert b k Hkb H1 H2.
  induction l as [| a]; intros; [ easy | ].
  destruct H1 as [H1| H1]. {
    subst a.
    inversion H2; subst.
    flia Hkb H4.
  }
  inversion H2; subst.
  apply (IHl a k); [ | easy | easy ].
  now transitivity b.
}
split. {
  now apply Nat.eqb_eq.
} {
  unfold locate_list.
  rewrite List_skipn_map.
  rewrite List_skipn_seq; [ cbn | flia Hbl ].
...
  unfold locate_list in Hab.
  rewrite (List_map_nth_in _ 0) in Hab; [ | now rewrite seq_length ].
  rewrite seq_nth in Hab; [ cbn in Hab | easy ].
  rewrite Hab in Hl.
  apply (proj2 (@eq_nth_find_all_loop_iff nat (Nat.eqb a) 0 _ _ _)).
  destruct l as [| b2]. {
    intros j Hj.
    apply Bool.not_true_iff_false; intros Hja.
    apply Nat.eqb_eq in Hja.
    subst j.
    apply in_map_iff in Hj.
    destruct Hj as (j & Hja & Hj).
...
(*
  clear - Hl Hbl.
  revert a b ll Hl Hbl.
  induction l as [| c]; intros. {
    destruct ll as [| l1]; [ easy | cbn in Hbl; cbn ].
    rewrite Nat.add_1_r.
    rewrite <- (Nat.add_1_r b).
    destruct a. {
      cbn in Hl; subst l1.
*)
...
*)

(*
Theorem dispatch_locate : ∀ ll,
  is_pre_partition ll
  → dispatch (length ll) (locate ll) = ll.
Proof.
intros * Hll.
Inspect 7.
Search dispatch_list.
...
unfold dispatch.
unfold dispatch_list.
rewrite rev_length.
unfold to_radix at 2.
rewrite to_radix_loop_length.
...
rewrite <- locate_list_to_radix_locate.
Compute (let ll := [[2]; []; [0; 1]] in locate ll).
Compute (let ll := [[2]; []; [0; 1]] in rev (to_radix (length ll) (locate ll))).
Compute (let ll := [[2]; []; [0; 1]] in to_radix (length ll) (locate ll)).
Compute (let ll := [[2]; []; [0; 1]] in map (λ j : nat, nth_find_all (Nat.eqb j) (rev (to_radix (length ll) (locate ll)))) (seq 0 (length ll))).
destruct Hll as (Hall & Huni & Hint).
replace ll with (map (λ i, nth i ll []) (seq 0 (length ll))) at 2. 2: {
  clear.
  induction ll as [| l]; [ easy | cbn ].
  f_equal.
  rewrite <- seq_shift.
  now rewrite map_map.
}
apply map_ext_in.
intros i Hi.
apply in_seq in Hi; cbn in Hi; destruct Hi as (_, Hi).
unfold nth_find_all.
(**)
Compute (let ll := [[2]; []; [0; 1]] in rev (to_radix_loop (length ll) (length ll) (locate ll))).
Compute (let ll := [[2]; []; [0; 1]] in rev (to_radix (length ll) (locate ll))).
Compute (let ll := [[2]; []; [0; 1]] in locate_list ll).
...
rewrite <- locate_list_to_radix_locate.
  nth_find_all_loop (Nat.eqb i) (locate_list ll) 0 = nth i ll []
...
Print locate.
Search locate_list.
...
unfold to_radix.
destruct ll as [| l]; [ easy | ].
cbn - [ "/" "mod" Nat.eqb locate nth ].
cbn in Hi, Hall, Huni.
remember (length ll) as n eqn:Hn.
rewrite nth_find_all_loop_app.
rewrite Nat.add_0_l, rev_length.
rewrite to_radix_loop_length.
cbn - [ "/" "mod" Nat.eqb locate nth ].
remember (i =? locate (l :: ll) mod S n) as b eqn:Hb.
symmetry in Hb.
destruct b. {
  apply Nat.eqb_eq in Hb.
(**)
  revert l n Hn Hall Huni Hint i Hi Hb.
  induction ll as [| l2]; intros. {
    subst n; cbn.
    apply Nat.lt_1_r in Hi; rewrite Hi; clear i Hi Hb.
    specialize (Huni 0 (Nat.lt_0_succ _)).
    destruct Huni as (l1 & Hl1 & Hzl1).
    destruct Hl1 as [Hl1| Hl1]; [ | easy ].
    subst l1.
    specialize (Hall l (or_introl eq_refl)).
    cbn in Hall.
    induction l as [| a]; [ easy | ].
    destruct Hzl1 as [Hzl1| Hzl1]. {
      subst a; f_equal.
      cbn in Hint; rewrite app_nil_r in Hint.
      apply NoDup_cons_iff in Hint.
      destruct l as [| a]; [ easy | exfalso ].
      specialize (Hall a (or_intror (or_introl eq_refl))) as H1.
      apply Nat.lt_1_r in H1; subst a.
      now destruct Hint as (H, _); apply H; left.
    }
    specialize (IHl Hzl1).
    cbn in IHl, Hint; rewrite app_nil_r in Hint, IHl.
    assert (H : ∀ i : nat, i ∈ l → i < 1). {
      intros i Hi.
      now apply Hall; right.
    }
    apply NoDup_cons_iff in Hint.
    specialize (IHl H (proj2 Hint)); clear H; subst l.
    specialize (Hall a (or_introl eq_refl)).
    apply Nat.lt_1_r in Hall.
    now subst a.
  }
...
  Hn : n = length ll
  Hi : i < S n
  Hb : i = locate (l :: ll) mod S n
  ============================
  nth_find_all_loop (Nat.eqb i)
    (rev (to_radix_loop n (S n) (locate (l :: ll) / S n))) 0 ++ [n] =
  nth i (l :: ll) []
...
  Hn : n = length (l2 :: ll)
  Hi : i < S n
  Hb : i = locate (l :: l2 :: ll) mod S n
  ============================
  nth_find_all_loop (Nat.eqb i)
    (rev (to_radix_loop n (S n) (locate (l :: l2 :: ll) / S n))) 0 ++ [n] =
  nth i (l :: l2 :: ll) []
...
unfold locate.
unfold locate_list.
Search to_radix.
unfold nth_find_all.
...
*)

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

(*
Theorem trivial_partition : ∀ n,
  nth (Σ (j = 1, n - 1), j * n ^ (n - 1 - j)) (pre_partitions n) [] =
  map (λ i, [i]) (seq 0 n).
Proof.
intros.
cbn; rewrite Nat.sub_0_r.
induction n; [ easy | cbn ].
rewrite Nat.sub_0_r.
unfold dispatch.
rewrite (List_map_nth_in _ 0). 2: {
  rewrite seq_length.
  replace n with (S n - 1) at 1; [ | flia ].
  (* pffff... compliqué *)
*)

(*
Theorem trivial_partition : ∀ n,
   dispatch_list (seq 0 n) = map (λ i, [i]) (seq 0 n).
*)

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
(*
Compute (let n:= 3 in to_radix n (fold_left (λ a i, a * n + i) (seq 0 n) 0) = rev (seq 0 n)).
Compute (let l := [2; 2; 0] in let n := length l in let d := 4 in let it := 7 in firstn n (to_radix_loop it (n + d) (fold_left (λ a j, a * (n + d) + j) l 0))).
*)
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
(*
Compute (let n := 4 in let j := fold_left (λ a i : nat, a * n + i) (seq 0 n) 0 in nth j (pre_partitions n) []).
*)
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

Theorem bs_ge_s : ∀ n f, block_sensitivity n f ≥ sensitivity n f.
Proof.
intros.
Inspect 1.
...
unfold block_sensitivity, sensitivity.
rewrite map_loc_sens.
unfold local_block_sensitivity.
unfold pre_partitions.
unfold dispatch.
Print loc_bl_sens_list.
...
unfold local_block_sensitivity, local_sensitivity.
...
1→0 = 0 radix 1
2→1 = 01 radix 2
3→5 = 012 radix 3
4→27 = 0123 radix 4
1*n^2 + 2*n^1 + 3*n^0
(n-1)n^0+(n-2)n^1+(n-3)^n^2+...+1*n^(n-2)+0*n^(n-1)
  Σ (i=0,n-1) i*n^(n-1-i)
= Σ (i=0,n-1) (n-1-i)*n^i

map (λ i, [i]) (seq 0 n) = nth ... (pre_partitions n) []
...
}
apply in_split in H.
destruct H as (l1 & l2 & Hll).
rewrite Hll.
(* prove that the "map (λ i, [i]) (seq 0 n)" has the maximum length *)
...
(* previous attempt to prove
    map (λ i, [i]) (seq 0 n) ∈ pre_partitions n *)
  unfold pre_partitions.
  assert (H : map (λ i, [i]) (seq 0 n) = dispatch n (seq 0 n)). {
    unfold dispatch.
    rewrite List_filter_all_true. 2: {
      intros a Ha.
      clear - Ha.
      destruct a; [ exfalso | easy ].
      assert (H : ∀ i s n r, length r = n → [] ∉ disp_loop i (seq s n) r). {
        clear.
        intros i s n r Hr Ha.
        revert i s r Hr Ha.
        induction n; intros i s r Hr Ha. {
          now apply length_zero_iff_nil in Hr; subst r.
        }
        cbn in Ha.
...
destruct n. {
  cbn in Ha.
  destruct r as [| r1]; [ easy | ].
  destruct r; [ | easy ].
  cbn in Ha.
  destruct s. {
    cbn in Ha.
    now destruct Ha.
  }
  cbn in Ha.
  destruct Ha as [Ha| Ha]. {
...
  unfold set_nth in Ha.
...
        specialize (IHn (i + 1) (S s)) as H1.
        specialize (H1 (set_nth s r (i :: nth s r []))).
...
        assert (H : length (set_nth s r (i :: nth s r [])) = n). {
Print set_nth.
Theorem glop {A} : ∀ i (l : list A) v, length (set_nth i l v) = length l.
Proof.
intros.
revert i v.
induction l as [| a]; intros. {
  cbn.
  unfold set_nth.
(* ouais non c'est faux *)
...
rewrite glop.
...

        destruct r as [| a]; [ easy | ].
        cbn in Hr.
        apply Nat.succ_inj in Hr.
        specialize (IHn (i + 1) (S s) r Hr) as H1.
Print set_nth.
...
      assert
        (H : ∀ s n r1 r2,
         (∀ l, l ∈ r1 → l ≠ [])
         → length r2 = n
         → [] ∉ disp_loop s (seq s n) (r1 ++ r2)). {
        clear.
        intros s * Hr1 Hr2 Ha.
        revert s r1 r2 Hr1 Hr2 Ha.
        induction n; intros s *; intros. {
          cbn in Ha.
          apply length_zero_iff_nil in Hr2; subst r2.
          rewrite app_nil_r in Ha.
          now specialize (Hr1 _ Ha).
        }
        cbn in Ha.
        destruct r2 as [| a r2]; [ easy | ].
        cbn in Hr2.
        apply Nat.succ_inj in Hr2.
        specialize (IHn (S n) r1 r2 Hr1 Hr2) as H1.
...
      destruct n; [ easy | ].
      cbn in Ha.
      destruct n; [ now destruct Ha | ].
      cbn in Ha.
  Ha : [] ∈ disp_loop 0 (seq 0 n) (repeat [] n)
  Ha : [] ∈ disp_loop 1 (seq 1 n) ([0] :: repeat [] n)
  Ha : [] ∈ disp_loop 2 (seq 2 n) ([0] :: [1] :: repeat [] n)
      destruct n. {
        cbn in Ha.

      cbn in Ha.
...
      assert (H : ∀ i l a r, [] ∉ disp_loop i l (a :: r)). {
        clear.
        intros * Ha.
        revert i a r Ha.
        induction l as [| b l]; intros.
cbn in Ha.

    induction n; [ easy | ].
    rewrite <- Nat.add_1_r.
    rewrite seq_app.
    rewrite map_app.
    rewrite IHn.
    rewrite Nat.add_0_l.
    rewrite disp_loop_app.
    rewrite seq_length, Nat.add_0_l.
Print dispatch.
...
    replace (repeat [] (n + 1)) with (repeat ([] : list nat) n ++ [[]]). 2: {
      clear.
      induction n; [ easy | cbn ].
      now rewrite IHn.
    }
    cbn.
Print disp_loop.
...
    rewrite disp_loop_app.
...

Theorem bs_ge_s : ∀ n f, bs n f ≥ s n f.
Proof.
intros.
unfold bs, s.
unfold block_sensitivity, sensitivity.
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
