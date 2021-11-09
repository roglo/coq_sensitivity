(* permutations of sequences of natural numbers between 1 and n *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.

Require Import Misc.
Require Import IterAnd.
Require Import Pigeonhole.

Definition comp {A B C} (f : B → C) (g : A → B) x := f (g x).

Definition comp_list (la lb : list nat) :=
  map (λ i, nth i la 0) lb.

(*
Compute (comp_list [0;2;1] [2;1;0]).
Compute (map (comp (λ i, nth i [0;2;1] 0) (λ i, nth i [2;1;0] 0)) [0;1;2]).
*)

Notation "σ₁ ° σ₂" := (comp_list σ₁ σ₂) (at level 40).

Notation "'Comp' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, comp c g) (λ i, i))
  (at level 35, i at level 0, l at level 60).

(* Permutations of {0, 1, 2, ... n-1} *)

Definition is_permut_list l :=
  (∀ x, x ∈ l → x < length l) ∧
  (∀ i j, i < length l → j < length l → nth i l 0 = nth j l 0 → i = j).

Definition is_permut_list_bool l :=
  (⋀ (a ∈ l), (a <? length l)) &&
  (⋀ (i = 1, length l),
     (⋀ (j = 1, length l),
        ((nth (i - 1) l 0 ≠? nth (j - 1) l 0) || (i =? j)))).

Theorem is_permut_list_is_permut_list_bool : ∀ l,
  is_permut_list l ↔ is_permut_list_bool l = true.
Proof.
intros.
split. {
  intros (H1, H2).
  unfold is_permut_list_bool.
  apply andb_true_iff.
  split. {
    apply all_true_and_list_true_iff.
    intros i Hi.
    apply Nat.ltb_lt.
    now apply H1.
  } {
    apply all_true_and_seq_true_iff.
    intros i Hi.
    apply all_true_and_seq_true_iff.
    intros j Hj.
    apply orb_true_iff.
    specialize (H2 (i - 1) (j - 1)) as H3.
    assert (H : i - 1 < length l) by flia Hi.
    specialize (H3 H); clear H.
    assert (H : j - 1 < length l) by flia Hj.
    specialize (H3 H); clear H.
    destruct (Nat.eq_dec i j) as [Hij| Hij]. {
      subst j.
      now right; rewrite Nat.eqb_eq.
    }
    left.
    apply negb_true_iff.
    apply Nat.eqb_neq.
    intros H.
    specialize (H3 H).
    flia Hi Hj H3 Hij.
  }
} {
  intros Hb.
  unfold is_permut_list_bool in Hb.
  apply andb_true_iff in Hb.
  destruct Hb as (H1, H2).
  split. {
    intros i Hi.
    specialize (proj2 (all_true_and_list_true_iff _ _ _) H1) as H3.
    specialize (H3 _ Hi).
    now apply Nat.ltb_lt.
  } {
    clear H1.
    intros i j Hi Hj Hij.
    specialize (proj2 (all_true_and_list_true_iff _ _ _) H2) as H3.
    rewrite Nat_sub_succ_1 in H3.
    specialize (H3 (S i)).
    rewrite Nat_sub_succ_1 in H3.
    assert (H : S i ∈ seq 1 (length l)) by (apply in_seq; flia Hi).
    specialize (H3 H); clear H.
    specialize (proj2 (all_true_and_list_true_iff _ _ _) H3) as H4.
    rewrite Nat_sub_succ_1 in H4.
    specialize (H4 (S j)).
    rewrite Nat_sub_succ_1 in H4; cbn in H4.
    assert (H : S j ∈ seq 1 (length l)) by (apply in_seq; flia Hj).
    specialize (H4 H); clear H.
    apply orb_true_iff in H4.
    rewrite Nat.eqb_eq in H4.
    destruct H4 as [H4| H4]; [ | easy ].
    apply negb_true_iff in H4.
    now apply Nat.eqb_neq in H4.
  }
}
Qed.

(*
   Canonical Symmetric Group.

   In set theory, there is one only symmetric group of order n.

   Here, a symmetric group (of order n) is a list of n! permutations,
   which can be ordered in any order. There are actually n!! (factorial
   of factorial n) possible orders.

   There is one that we call "canonical" because the generated permutation
   are in alphabetic order.

   The canonical symmetric group is built this way. The k-th permutation
   is a vector of size n where
   - the first value is k/fact(n-1)
   - the rest is the (k mod fact(n-1))-th permutation of n-1 values
     (from 0 to n-2) where
     * all values less than the first value (k/fact(n-1)) are unchanged
     * all values greater or equal to it are increased by 1
   Example. For n=4 and k=0
   - first value: 0
   - rest: shift of 0;1;2 by 1, i.e. 1;2;3
   Result : 0;1;2;3
   Other example. For n=4 and k=13
   - first value: 13/3! = 13/6 = 2
   - rest: k' = 13 mod 3! = 13 mod 6 = 1 for n'=3, resulting 0;2;1
     0 and 1 are not shifted (both < 2), 2 is shifted, resulting 0;3;1
     final result: 2;0;3;1
  *)

(*
Definition canon_sym_gr_fun n (σ_n : nat → nat → nat) k j : nat :=
  match j with
  | 0 => k / n!
  | S j' => σ_n (k mod n!) j' + Nat.b2n (k / n! <=? σ_n (k mod n!) j')
  end.

Fixpoint canon_sym_gr_elem n : nat → nat → nat :=
  match n with
  | 0 => λ _ _, 0
  | S n' => canon_sym_gr_fun n' (canon_sym_gr_elem n')
  end.

Definition canon_sym_gr n : vector (vector nat) :=
  mk_vect
    (map (λ k, mk_vect (map (canon_sym_gr_elem n k) (seq 0 n))) (seq 0 n!)).
*)

Definition succ_when_ge k a := a + Nat.b2n (k <=? a).

(* k-th canonic permutation of order n *)
Fixpoint canon_sym_gr_list n k : list nat :=
  match n with
  | 0 => []
  | S n' =>
      k / n'! ::
      map (succ_when_ge (k / n'!)) (canon_sym_gr_list n' (k mod n'!))
  end.

(* all canonic permutations *)
Definition canon_sym_gr_list_list n : list (list nat) :=
  map (canon_sym_gr_list n) (seq 0 n!).

(*
Compute (let n := 4 in map (canon_sym_gr_list n) (seq 0 n!)).
Compute (let n := 3 in ((*canon_sym_gr n,*) canon_sym_gr_vect n)).
*)

Definition is_sym_gr_list n (ll : list (list nat)) :=
  (∀ i, i < length ll →
   length (nth i ll []) = n ∧
   is_permut_list (nth i ll [])) ∧
  (∀ i j, i < length ll → j < length ll →
   nth i ll [] = nth j ll [] → i = j) ∧
  (∀ l, length l = n → is_permut_list l → l ∈ ll).

(*
Definition vect_vect_nat_el (V : vector (vector nat)) i : vector nat :=
  nth i (vect_list V) empty_vect.
*)

(*
Fixpoint permut_fun_inv_loop f i j :=
  match i with
  | 0 => 42
  | S i' => if Nat.eq_dec (f i') j then i' else permut_fun_inv_loop f i' j
  end.

Definition permut_vect_inv (σ : vector nat) :=
  mk_vect
    (map (permut_fun_inv_loop (vect_el 0 σ) (vect_size σ))
       (seq 0 (vect_size σ))).
*)

Definition permut_list_inv l :=
  map (λ i, unsome 0 (List_find_nth (Nat.eqb i) l)) (seq 0 (length l)).

(**)

(*
Compute (let n := 4 in canon_sym_gr_vect 3).
Compute (let n := 4 in map (λ i, let v := vect_el empty_vect (canon_sym_gr_vect n) i in (v, permut_vect_inv v)) (seq 0 n!)).
Compute (let n := 5 in map (λ i, let v := vect_el empty_vect (canon_sym_gr_vect n) i in vect_eqb Nat.eqb (permut_vect_inv v) (permut_vect_inv' v)) (seq 0 n!)).
*)

(* transposition *)

Definition transposition i j k :=
  if k =? i then j else if k =? j then i else k.

Definition swap_elem (f : nat → nat) i j k :=
  f (transposition i j k).

Definition list_swap_elem {A} d (l : list A) i j :=
  map (λ k, nth (transposition i j k) l d) (seq 0 (length l)).

(*
Theorem permut_fun_inv_loop_ext_in : ∀ f g i j,
  (∀ k, k < i → f k = g k)
  → permut_fun_inv_loop f i j = permut_fun_inv_loop g i j.
Proof.
intros * Hfg.
revert j.
induction i; intros; [ easy | cbn ].
destruct (Nat.eq_dec (f i) j) as [Hf| Hf]. {
  destruct (Nat.eq_dec (g i) j) as [Hg| Hg]; [ easy | ].
  specialize (Hfg i (Nat.lt_succ_diag_r _)); congruence.
}
destruct (Nat.eq_dec (g i) j) as [Hg| Hg]. {
  specialize (Hfg i (Nat.lt_succ_diag_r _)); congruence.
}
apply IHi.
intros k Hk.
apply Hfg; flia Hk.
Qed.
*)

Theorem permut_list_ub : ∀ l i,
  is_permut_list l → i < length l → nth i l 0 < length l.
Proof.
intros * Hp Hin.
now apply Hp, nth_In.
Qed.

Theorem transposition_lt : ∀ i j k n,
  i < n
  → j < n
  → k < n
  → transposition i j k < n.
Proof.
intros * Hi Hj Hk.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i); [ easy | ].
now destruct (Nat.eq_dec k j).
Qed.

Theorem transposition_out : ∀ i j k, k ≠ i → k ≠ j → transposition i j k = k.
Proof.
intros * Hi Hj.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i) as [H| H]; [ easy | clear H ].
now destruct (Nat.eq_dec k j).
Qed.

Theorem transposition_id : ∀ i k, transposition i i k = k.
Proof.
intros.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
now destruct (Nat.eq_dec k i).
Qed.

Theorem transposition_1 : ∀ i j, transposition i j i = j.
Proof.
intros.
unfold transposition.
now rewrite Nat.eqb_refl.
Qed.

Theorem transposition_2 : ∀ i j, transposition i j j = i.
Proof.
intros.
unfold transposition.
rewrite Nat.eqb_refl.
rewrite if_eqb_eq_dec.
now destruct (Nat.eq_dec j i).
Qed.

Theorem transposition_comm : ∀ i j k, transposition i j k = transposition j i k.
Proof.
intros.
unfold transposition.
do 4 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i) as [Hki| Hki]. {
  destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ congruence | easy ].
} {
  destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ congruence | easy ].
}
Qed.

Theorem list_swap_elem_is_permut : ∀ σ p q,
  p < length σ
  → q < length σ
  → is_permut_list σ
  → is_permut_list (list_swap_elem 0 σ p q).
Proof.
intros * Hp Hq Hσ.
unfold is_permut_list, list_swap_elem.
rewrite map_length, seq_length.
split; cbn. {
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  rewrite <- Hji.
  apply permut_list_ub; [ easy | ].
  now apply transposition_lt.
} {
  intros i j Hi Hj Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  unfold transposition in Hij.
  do 4 rewrite if_eqb_eq_dec in Hij.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    subst i.
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ now subst j; apply Hσ | ].
    apply Nat.neq_sym in Hjq.
    now exfalso; apply Hjq, Hσ.
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ now subst i j; apply Hσ | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ congruence | ].
    now apply Nat.neq_sym in Hjp; exfalso; apply Hjp; apply Hσ.
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ now exfalso; apply Hiq, Hσ | ].
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ now exfalso; apply Hip, Hσ | ].
  now apply Hσ.
}
Qed.

(* *)

Definition rank_of_permut_in_sym_gr (sg : list (list nat)) σ :=
  unsome 0 (List_find_nth (list_eqb Nat.eqb σ) sg).

Theorem rank_of_permut_in_sym_gr_lt : ∀ n sg v,
  n ≠ 0
  → is_sym_gr_list n sg
  → rank_of_permut_in_sym_gr sg v < length sg.
Proof.
intros * Hnz Hsg.
unfold rank_of_permut_in_sym_gr.
unfold unsome.
remember (List_find_nth _ _) as i eqn:Hi; symmetry in Hi.
destruct i as [i| ]; [ now apply List_find_nth_Some_lt in Hi | ].
clear Hi.
destruct (lt_dec 0 (length sg)) as [Hs| Hs]; [ easy | ].
apply Nat.nlt_ge in Hs; exfalso.
apply Nat.le_0_r in Hs.
apply length_zero_iff_nil in Hs; subst sg.
destruct Hsg as (_ & _ & Hsurj).
cbn in Hsurj.
specialize (Hsurj (seq 0 n)) as H1.
rewrite seq_length in H1.
specialize (H1 eq_refl).
assert (H : is_permut_list (seq 0 n)). {
  split. {
    cbn; rewrite seq_length.
    intros i Hin.
    now rewrite in_seq in Hin.
  } {
    cbn; rewrite seq_length.
    intros i j Hi Hj Hij.
    rewrite seq_nth in Hij; [ | easy ].
    rewrite seq_nth in Hij; [ | easy ].
    easy.
  }
}
congruence.
Qed.

Theorem nth_rank_of_permut_in_sym_gr : ∀ sg l n,
  is_sym_gr_list n sg
  → is_permut_list l
  → length l = n
  → nth (rank_of_permut_in_sym_gr sg l) sg [] = l.
Proof.
intros * Hsg Hp Hs.
unfold rank_of_permut_in_sym_gr, unsome.
remember (List_find_nth _ _) as i eqn:Hi; symmetry in Hi.
destruct i as [i| ]. {
  apply List_find_nth_Some with (d := []) in Hi.
  destruct Hi as (Hji, Hi).
  now apply list_eqb_eq in Hi.
}
assert (H : l ∉ sg). {
  intros H.
  apply In_nth with (d := []) in H.
  destruct H as (j & Hj & Hjv).
  specialize (List_find_nth_None [] _ _ Hi Hj) as H.
  apply list_eqb_neq in H.
  now symmetry in Hjv.
}
exfalso; apply H; clear H.
now apply Hsg.
Qed.

Theorem rank_of_permut_in_sym_gr_list_el : ∀ n sg i,
  n ≠ 0
  → is_sym_gr_list n sg
  → i < length sg
  → rank_of_permut_in_sym_gr sg (nth i sg []) = i.
Proof.
intros * Hnz Hsg Hi.
unfold rank_of_permut_in_sym_gr, unsome.
remember (List_find_nth _ _) as j eqn:Hj; symmetry in Hj.
destruct j as [j| ]. {
  apply List_find_nth_Some with (d := []) in Hj.
  destruct Hj as (Hji, Hj).
  apply list_eqb_eq in Hj.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  assert (Hjs : j < length sg). {
    destruct (lt_dec j (length sg)) as [Hjs| Hjs]; [ easy | exfalso ].
    apply Nat.nlt_ge in Hjs.
    rewrite (@nth_overflow _ _ j) in Hj; [ | easy ].
    specialize (Hsg i Hi) as H1.
    destruct H1 as (H1, H2).
    now rewrite Hj in H1; cbn in H1; subst n.
  }
  now apply Hinj.
}
specialize (List_find_nth_None [] _ _ Hj Hi) as H1.
now apply list_eqb_neq in H1.
Qed.

Theorem length_of_empty_sym_gr : ∀ sg,
  is_sym_gr_list 0 sg → length sg = 1.
Proof.
intros * Hsg.
destruct Hsg as (Hsg & Hinj & Hsurj).
specialize (Hsurj [] eq_refl) as H1.
assert (H : is_permut_list []). {
  now apply is_permut_list_is_permut_list_bool.
}
specialize (H1 H); clear H.
apply (In_nth _ _ []) in H1.
destruct H1 as (i & Hil & Hi).
destruct (Nat.eq_dec (length sg) 0) as [Hvz| Hvz]. {
  now rewrite Hvz in Hil.
}
destruct (Nat.eq_dec (length sg) 1) as [Hv1| Hv1]; [ easy | ].
specialize (Hsg 0) as H1.
specialize (Hsg 1) as H2.
specialize (Hinj 0 1) as H3.
assert (H : 0 < length sg) by flia Hvz.
specialize (H1 H); specialize (H3 H); clear H.
assert (H : 1 < length sg) by flia Hvz Hv1.
specialize (H2 H); specialize (H3 H); clear H.
destruct H1 as (H4, H5).
destruct H2 as (H6, H7).
enough (H : nth 0 sg [] = nth 1 sg []). {
  rewrite H in H3.
  now specialize (H3 eq_refl).
}
apply length_zero_iff_nil in H4, H6.
congruence.
Qed.

Fixpoint canon_sym_gr_inv_elem n k (j : nat) :=
  match n with
  | 0 => 0
  | S n' =>
      if lt_dec j (k / n'!) then
        S (canon_sym_gr_inv_elem n' (k mod n'!) j)
      else if lt_dec (k / n'!) j then
        S (canon_sym_gr_inv_elem n' (k mod n'!) (j - 1))
      else 0
  end.

Definition canon_sym_gr_inv_list n k : list nat :=
  map (canon_sym_gr_inv_elem n k) (seq 0 n).

Theorem length_canon_sym_gr_list_list : ∀ n,
  length (canon_sym_gr_list_list n) = n!.
Proof.
intros.
unfold canon_sym_gr_list_list.
now rewrite map_length, seq_length.
Qed.

Theorem length_canon_sym_gr_list : ∀ k n,
  length (canon_sym_gr_list n k) = n.
Proof.
intros.
revert k.
induction n; intros; [ easy | cbn ].
f_equal; rewrite map_length.
apply IHn.
Qed.

Theorem canon_sym_gr_list_ub : ∀ n k i,
  k < n!
  → i < n
  → nth i (canon_sym_gr_list n k) 0 < n.
Proof.
intros * Hkn Hi.
revert i k Hkn Hi.
induction n; intros; [ easy | cbn ].
destruct i. {
  apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
  now rewrite Nat.mul_succ_r, Nat.add_comm, Nat.mul_comm.
}
apply Nat.succ_lt_mono in Hi.
rewrite (List_map_nth' 0); [ | now rewrite length_canon_sym_gr_list ].
unfold succ_when_ge.
rewrite <- Nat.add_1_r.
apply Nat.add_lt_le_mono; [ | apply Nat_b2n_upper_bound ].
apply IHn; [ | easy ].
apply Nat.mod_upper_bound, fact_neq_0.
Qed.

Theorem canon_sym_gr_inv_sym_gr : ∀ n k i,
  i < n
  → k < n!
  → nth ((nth i (canon_sym_gr_list n k) 0)) (canon_sym_gr_inv_list n k) 0 = i.
Proof.
intros * Hi Hkn.
unfold canon_sym_gr_inv_list.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now apply canon_sym_gr_list_ub.
}
rewrite seq_nth; [ | now apply canon_sym_gr_list_ub ].
rewrite Nat.add_0_l.
revert k i Hi Hkn.
induction n; intros; [ easy | ].
cbn.
destruct i. {
  do 2 rewrite <- if_ltb_lt_dec.
  now rewrite Nat.ltb_irrefl.
}
apply Nat.succ_lt_mono in Hi.
rewrite (List_map_nth' 0); [ | now rewrite length_canon_sym_gr_list ].
unfold succ_when_ge.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec (k / n!) _) as [H1| H1]. {
  destruct (lt_dec _ (k / n!)) as [H| H]; [ flia H1 H | clear H ].
  destruct (lt_dec (k / n!) _) as [H| H]; [ clear H | flia H1 H ].
  f_equal; rewrite Nat.add_sub.
  apply IHn; [ easy | apply Nat.mod_upper_bound, fact_neq_0 ].
} {
  rewrite Nat.add_0_r.
  destruct (lt_dec _ (k / n!)) as [H| H]; [ clear H | flia H1 H ].
  f_equal.
  apply IHn; [ easy | apply Nat.mod_upper_bound, fact_neq_0 ].
}
Qed.

Theorem nth_canon_sym_gr_list_inj1 : ∀ n k i j,
  k < fact n
  → i < n
  → j < n
  → nth i (canon_sym_gr_list n k) 0 = nth j (canon_sym_gr_list n k) 0
  → i = j.
Proof.
intros * Hk Hi Hj Hij.
rewrite <- canon_sym_gr_inv_sym_gr with (n := n) (k := k); [ | easy | easy ].
symmetry.
rewrite <- canon_sym_gr_inv_sym_gr with (n := n) (k := k); [ | easy | easy ].
symmetry.
now rewrite Hij.
Qed.

(* rank in canon symmetric group *)

(*
Definition sub_canon_permut_fun (f : nat → nat) i :=
  f (S i) - Nat.b2n (f 0 <? f (S i)).

Fixpoint rank_of_permut_in_canon_sym_gr n (f : nat → nat) : nat :=
  match n with
  | 0 => 0
  | S n' => f 0 * n'! + rank_of_permut_in_canon_sym_gr n' (sub_canon_permut_fun f)
  end.

Definition rank_of_permut_in_canon_sym_gr_vect n (v : vector nat) : nat :=
  rank_of_permut_in_canon_sym_gr n (vect_el 0 v).
*)

(* *)

Definition sub_canon_permut_list (l : list nat) :=
  map (λ a, a - Nat.b2n (hd 0 l <? a)) (tl l).

Fixpoint rank_of_permut_in_canon_sym_gr_list n (l : list nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      hd 0 l * n'! +
      rank_of_permut_in_canon_sym_gr_list n' (sub_canon_permut_list l)
  end.

(*
Compute (let n := 4 in map (λ i, let v := vect_el empty_vect (canon_sym_gr n) i in (rank_of_permut_in_canon_sym_gr_vect n v, rank_of_permut_in_canon_sym_gr_vect n v)) (seq 0 (n! + 10))).
*)

Theorem sub_canon_permut_list_elem_ub : ∀ l i,
  is_permut_list l
  → S i < length l
  → nth i (sub_canon_permut_list l) 0 < length l - 1.
Proof.
intros * (Hvn, Hn) Hin.
destruct l as [| a]; [ easy | ].
cbn - [ "<?" ] in Hin |-*.
rewrite Nat.sub_0_r.
apply Nat.succ_lt_mono in Hin.
rewrite (List_map_nth' 0); [ | easy ].
unfold Nat.b2n.
rewrite if_ltb_lt_dec.
destruct (lt_dec a (nth i l 0)) as [Hal| Hal]. {
  enough (H : nth i l 0 < S (length l)) by flia Hal H.
  now apply Hvn; right; apply nth_In.
}
apply Nat.nlt_ge in Hal.
rewrite Nat.sub_0_r.
destruct (Nat.eq_dec (nth i l 0) a) as [Hia| Hia]. {
  rewrite Hia.
  apply Nat.succ_lt_mono in Hin.
  symmetry in Hia.
  now specialize (Hn 0 (S i) (Nat.lt_0_succ _) Hin Hia).
}
specialize (Hvn a (or_introl eq_refl)); cbn in Hvn.
flia Hvn Hal Hia.
Qed.

Theorem sub_canon_sym_gr_elem_inj1 : ∀ l i j,
  is_permut_list l
  → S i < length l
  → S j < length l
  → nth i (sub_canon_permut_list l) 0 = nth j (sub_canon_permut_list l) 0
  → i = j.
Proof.
intros * (Hvn, Hn) Hin Hjn Hij.
destruct l as [| a]; [ easy | ].
cbn - [ "<?" ] in Hin, Hjn, Hij.
apply Nat.succ_lt_mono in Hin, Hjn.
rewrite (List_map_nth' 0) in Hij; [ | easy ].
rewrite (List_map_nth' 0) in Hij; [ | easy ].
unfold Nat.b2n in Hij.
do 2 rewrite if_ltb_lt_dec in Hij.
destruct (lt_dec a (nth i l 0)) as [Hai| Hai]. {
  destruct (lt_dec a (nth j l 0)) as [Haj| Haj]. {
    apply Nat.succ_inj.
    apply Nat.succ_lt_mono in Hin, Hjn.
    apply Hn; [ easy | easy | ].
    cbn; flia Hai Haj Hij.
  }
  apply Nat.nlt_ge in Haj.
  rewrite Nat.sub_0_r in Hij.
  apply Nat.succ_lt_mono in Hjn.
  specialize (Hn 0 (S j) (Nat.lt_0_succ _) Hjn) as H1.
  cbn in H1.
  replace (nth j l 0) with a in H1 by flia Hai Haj Hij.
  now specialize (H1 eq_refl).
}
apply Nat.nlt_ge in Hai.
rewrite Nat.sub_0_r in Hij.
destruct (lt_dec a (nth j l 0)) as [Haj| Haj]. {
  apply Nat.succ_lt_mono in Hin.
  specialize (Hn (S i) 0 Hin (Nat.lt_0_succ _)) as H1.
  cbn in H1.
  replace (nth i l 0) with a in H1 by flia Hai Haj Hij.
  now specialize (H1 eq_refl).
}
rewrite Nat.sub_0_r in Hij.
apply Nat.succ_inj.
apply Nat.succ_lt_mono in Hin, Hjn.
now apply Hn.
Qed.

Theorem length_sub_canon_permut_list : ∀ l,
  length (sub_canon_permut_list l) = length l - 1.
Proof.
intros.
destruct l as [| a]; [ easy | ].
now cbn; rewrite map_length, Nat.sub_0_r.
Qed.

Theorem rank_of_canon_permut_ub : ∀ n l,
  is_permut_list l
  → length l = n
  → rank_of_permut_in_canon_sym_gr_list n l < n!.
Proof.
intros * (Hvn, Hn) Hln.
revert l Hvn Hn Hln.
induction n; intros; cbn; [ flia | ].
rewrite Nat.add_comm.
apply Nat.add_lt_le_mono. {
  apply IHn. {
    intros i Hi.
    apply (In_nth _ _ 0) in Hi.
    destruct Hi as (j & Hj & Hji).
    rewrite <- Hji.
    rewrite length_sub_canon_permut_list in Hj |-*.
    apply sub_canon_permut_list_elem_ub; [ easy | flia Hj ].
  } {
    intros i j Hi Hj.
    rewrite length_sub_canon_permut_list in Hi, Hj.
    apply sub_canon_sym_gr_elem_inj1; [ easy | flia Hi | flia Hj ].
  }
  now rewrite length_sub_canon_permut_list, Hln, Nat_sub_succ_1.
}
apply Nat.mul_le_mono_r.
specialize (Hvn (hd 0 l)).
assert (H : hd 0 l ∈ l). {
  rewrite List_hd_nth_0; apply nth_In; rewrite Hln; flia.
}
specialize (Hvn H); clear H.
rewrite Hln in Hvn.
now apply Nat.succ_le_mono in Hvn.
Qed.

Theorem sub_canon_permut_list_is_permut : ∀ l,
  is_permut_list l
  → is_permut_list (sub_canon_permut_list l).
Proof.
intros * Hl.
split. {
  intros i Hi.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (j & Hj & Hji).
  rewrite <- Hji.
  rewrite length_sub_canon_permut_list in Hj |-*.
  apply sub_canon_permut_list_elem_ub; [ easy | flia Hj ].
} {
  intros i j Hi Hj Hij.
  rewrite length_sub_canon_permut_list in Hi, Hj.
  apply sub_canon_sym_gr_elem_inj1 in Hij; [ easy | easy | | ]. {
    flia Hi.
  } {
    flia Hj.
  }
}
Qed.

(*
Theorem permut_in_canon_sym_gr_of_its_rank : ∀ n f,
  is_permut_fun f n
  → ∀ i, i < n
  → canon_sym_gr_elem n (rank_of_permut_in_canon_sym_gr n f) i = f i.
*)
Theorem permut_in_canon_sym_gr_of_its_rank : ∀ n l,
  is_permut_list l
  → length l = n
  → canon_sym_gr_list n (rank_of_permut_in_canon_sym_gr_list n l) = l.
Proof.
intros * (Hvn, Hn) Hln.
revert l Hvn Hn Hln.
induction n; intros; [ now apply length_zero_iff_nil in Hln | cbn ].
destruct l as [| a]; [ easy | ].
f_equal. {
  cbn - [ sub_canon_permut_list ].
  rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
  rewrite <- Nat.add_0_r; f_equal.
  apply Nat.div_small.
  apply rank_of_canon_permut_ub. 2: {
    cbn; rewrite map_length.
    now cbn in Hln; apply Nat.succ_inj in Hln.
  }
  now apply sub_canon_permut_list_is_permut.
} {
  cbn in Hln.
  apply Nat.succ_inj in Hln.
  rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
  rewrite Nat_mod_add_l_mul_r; [ | apply fact_neq_0 ].
  rewrite Nat.mod_small. 2: {
    apply rank_of_canon_permut_ub. 2: {
      rewrite length_sub_canon_permut_list; cbn.
      now rewrite Hln, Nat.sub_0_r.
    }
    now apply sub_canon_permut_list_is_permut.
  }
  rewrite IHn; cycle 1. {
    intros i Hi.
    apply (In_nth _ _ 0) in Hi.
    destruct Hi as (j & Hj & Hji).
    rewrite <- Hji.
    apply permut_list_ub; [ | easy ].
    now apply sub_canon_permut_list_is_permut.
  } {
    intros i j Hi Hj.
    rewrite length_sub_canon_permut_list in Hi, Hj.
    cbn in Hi, Hj.
    rewrite Nat.sub_0_r in Hi, Hj.
    apply sub_canon_sym_gr_elem_inj1; [ easy | cbn; flia Hi | cbn; flia Hj ].
  } {
    rewrite length_sub_canon_permut_list; cbn.
    now rewrite Nat.sub_0_r.
  }
  cbn - [ sub_canon_permut_list ].
  unfold succ_when_ge.
  remember (rank_of_permut_in_canon_sym_gr_list _ _) as x.
  cbn - [ "<=?" ]; subst x.
  rewrite map_map.
  rewrite List_map_map_seq with (d := 0).
  rewrite List_map_nth_seq with (d := 0).
  apply map_ext_in_iff.
  intros i Hi; apply in_seq in Hi.
  unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec a (nth i l 0)) as [Hai| Hai]. {
    rewrite if_leb_le_dec.
    destruct (le_dec _ _) as [H1| H1]; [ apply Nat.sub_add; flia Hai | ].
    exfalso.
    apply H1; clear H1.
    rewrite Nat.div_small; [ flia Hai | ].
    apply rank_of_canon_permut_ub; [ | now cbn; rewrite map_length ].
    now apply sub_canon_permut_list_is_permut.
  }
  apply Nat.nlt_ge in Hai.
  rewrite Nat.sub_0_r.
  rewrite Nat.div_small. 2: {
    apply rank_of_canon_permut_ub. 2: {
      rewrite length_sub_canon_permut_list; cbn; rewrite Hln.
      apply Nat.sub_0_r.
    }
    now apply sub_canon_permut_list_is_permut.
  }
  rewrite Nat.add_0_r, if_leb_le_dec.
  destruct (le_dec _ _) as [H1| H1]; [ | apply Nat.add_0_r ].
  exfalso.
  apply Nat.le_antisymm in H1; [ symmetry in H1 | easy ].
  specialize (Hn 0 (S i) (Nat.lt_0_succ _)) as H2.
  assert (H : S i < length (a :: l)) by (cbn; flia Hi).
  now specialize (H2 H H1); clear H.
}
Qed.

Theorem canon_sym_gr_list_is_permut : ∀ n k,
  k < n!
  → is_permut_list (canon_sym_gr_list n k).
Proof.
intros * Hkn.
split. {
  intros i Hi.
  rewrite length_canon_sym_gr_list.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (j & Hj & Hji).
  rewrite length_canon_sym_gr_list in Hj.
  rewrite <- Hji.
  now apply canon_sym_gr_list_ub.
} {
  intros * Hi Hj Hij.
  rewrite length_canon_sym_gr_list in Hi, Hj.
  now apply nth_canon_sym_gr_list_inj1 in Hij.
}
Qed.

(*
ouais, bon, c'est la=lb, donc c'est trivial
Theorem rank_of_permut_in_canon_sym_gr_eq_compat : ∀ n f g,
  (∀ i, i < n → f i = g i)
  → rank_of_permut_in_canon_sym_gr n f = rank_of_permut_in_canon_sym_gr n g.
Proof.
intros * Hfg.
revert f g Hfg.
induction n; intros; [ easy | cbn ].
rewrite Hfg; [ f_equal | flia ].
apply IHn.
intros i Hi.
unfold sub_canon_permut_fun.
rewrite Hfg; [ f_equal | flia Hi ].
rewrite Hfg; [ f_equal | flia Hi ].
Qed.
*)

Theorem canon_sym_gr_sub_canon_permut_list : ∀ n k,
  canon_sym_gr_list n (k mod n!) =
  sub_canon_permut_list (canon_sym_gr_list (S n) k).
Proof.
intros.
destruct n; intros; [ easy | ].
cbn - [ "<?" fact ].
f_equal. {
  unfold succ_when_ge.
  rewrite <- Nat.add_sub_assoc. 2: {
    unfold Nat.b2n.
    rewrite if_leb_le_dec, if_ltb_lt_dec.
    destruct (le_dec _ _) as [H| H]; [ destruct (lt_dec _ _); cbn; flia | ].
    rewrite Nat.add_0_r.
    apply Nat.nle_gt in H.
    destruct (lt_dec _ _) as [Hqr| Hqr]; [ flia H Hqr | easy ].
  }
  symmetry; rewrite <- Nat.add_0_r; f_equal.
  unfold Nat.b2n.
  rewrite if_leb_le_dec, if_ltb_lt_dec.
  destruct (le_dec _ _) as [H1| H1]; [ | easy ].
  destruct (lt_dec _ _) as [H2| H2]; [ easy | flia H1 H2 ].
}
rewrite map_map.
rewrite map_map.
apply map_ext_in.
intros i Hi.
remember (succ_when_ge (_ mod _ / _) _) as x eqn:Hx.
unfold succ_when_ge, Nat.b2n.
rewrite if_leb_le_dec, if_ltb_lt_dec.
rewrite <- Nat.add_sub_assoc. 2: {
  destruct (le_dec _ _) as [H| H]; [ destruct (lt_dec _ _); cbn; flia | ].
  rewrite Nat.add_0_r.
  apply Nat.nle_gt in H.
  destruct (lt_dec _ _) as [Hqr| Hqr]; [ flia H Hqr | easy ].
}
symmetry; rewrite <- Nat.add_0_r; f_equal.
destruct (le_dec _ _) as [H1| H1]; [ | easy ].
destruct (lt_dec _ _) as [H2| H2]; [ easy | flia H1 H2 ].
Qed.

Theorem rank_of_canon_permut_of_canon_rank : ∀ n k,
  k < n!
  → rank_of_permut_in_canon_sym_gr_list n (canon_sym_gr_list n k) = k.
Proof.
intros * Hkn.
revert k Hkn.
induction n; intros; [ now apply Nat.lt_1_r in Hkn | ].
cbn - [ canon_sym_gr_list ].
remember (sub_canon_permut_list _) as x; cbn; subst x.
specialize (Nat.div_mod k (fact n) (fact_neq_0 _)) as H1.
rewrite Nat.mul_comm in H1.
replace (k / fact n * fact n) with (k - k mod fact n) by flia H1.
rewrite <- Nat.add_sub_swap; [ | apply Nat.mod_le, fact_neq_0 ].
apply Nat.add_sub_eq_r; f_equal.
clear H1.
rewrite <- (IHn (k mod fact n)) at 1. 2: {
  apply Nat.mod_upper_bound, fact_neq_0.
}
f_equal.
apply canon_sym_gr_sub_canon_permut_list.
Qed.

Theorem rank_in_sym_gr_of_rank_in_canon_sym_gr_prop : ∀ n sg,
  is_sym_gr_list n sg
  → ∀ k : fin_t n!,
      (rank_of_permut_in_sym_gr sg
         (nth (proj1_sig k) (canon_sym_gr_list_list n) []) <? length sg) =
      true.
Proof.
intros * Hsg k.
apply Nat.ltb_lt.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  destruct k as (k, pk); cbn.
  apply Nat.ltb_lt, Nat.lt_1_r in pk; subst k.
  specialize (length_of_empty_sym_gr Hsg) as Hs.
  destruct sg as [| v]; [ easy | ].
  destruct sg; [ clear Hs | easy ].
  destruct Hsg as (Hsg & _ & _).
  specialize (Hsg 0 Nat.lt_0_1); cbn in Hsg.
  destruct Hsg as (H1, H2).
  apply length_zero_iff_nil in H1; subst v.
  apply Nat.lt_0_1.
}
now apply rank_of_permut_in_sym_gr_lt with (n := n).
Qed.

Theorem rank_in_canon_sym_gr_of_rank_in_sym_gr_prop : ∀ n sg,
  is_sym_gr_list n sg
  → ∀ k : fin_t (length sg),
      (rank_of_permut_in_canon_sym_gr_list n (nth (proj1_sig k) sg []) <? n!)
      = true.
Proof.
intros * Hsg k.
destruct Hsg as (Hsg & Hinj & Hsurj).
apply Nat.ltb_lt.
destruct k as (k, pk); cbn.
apply Nat.ltb_lt in pk.
specialize (Hsg k pk).
now apply rank_of_canon_permut_ub.
Qed.

Definition rank_in_sym_gr_of_rank_in_canon_sym_gr n sg
    (Hsg : is_sym_gr_list n sg) (k : fin_t n!) : fin_t (length sg) :=
  exist (λ a : nat, (a <? length sg) = true)
    (rank_of_permut_in_sym_gr sg
      (nth (proj1_sig k) (canon_sym_gr_list_list n) []))
    (rank_in_sym_gr_of_rank_in_canon_sym_gr_prop Hsg k).

Definition rank_in_canon_sym_gr_of_rank_in_sym_gr  n sg
    (Hsg : is_sym_gr_list n sg) (k : fin_t (length sg)) : fin_t n! :=
  exist (λ a : nat, (a <? n!) = true)
    (rank_of_permut_in_canon_sym_gr_list n (nth (proj1_sig k) sg []))
    (rank_in_canon_sym_gr_of_rank_in_sym_gr_prop Hsg k).

Theorem rank_in_sym_gr_of_rank_in_canon_sym_gr_of_its_inverse : ∀ n sg
    (Hsg : is_sym_gr_list n sg) k,
  rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg
    (rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg k) = k.
Proof.
intros.
destruct k as (k, pk); cbn - [ "<?" ].
apply eq_exist_uncurried.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  specialize (length_of_empty_sym_gr Hsg) as Hs.
  specialize (proj1 (Nat.ltb_lt _ _) pk) as Hk.
  rewrite Hs in Hk.
  apply Nat.lt_1_r in Hk; subst k.
  assert (p : rank_of_permut_in_sym_gr sg [] = 0). {
    unfold rank_of_permut_in_sym_gr, unsome; cbn.
    destruct sg as [| v]; [ easy | ].
    destruct sg; [ cbn | easy ].
    destruct Hsg as (Hsg & _ & _).
    specialize (Hsg 0 Nat.lt_0_1); cbn in Hsg.
    destruct Hsg as (H1, H2).
    now apply length_zero_iff_nil in H1; subst v.
  }
  exists p.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
}  
cbn.
assert
  (p :
   rank_of_permut_in_sym_gr sg
     (nth (rank_of_permut_in_canon_sym_gr_list n (nth k sg []))
        (canon_sym_gr_list_list n) []) = k). {
  apply Nat.ltb_lt in pk.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  specialize (Hsg k pk) as H1.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply rank_of_canon_permut_ub.
  }
  rewrite seq_nth; [ | now apply rank_of_canon_permut_ub ].
  rewrite Nat.add_0_l.
  rewrite permut_in_canon_sym_gr_of_its_rank; [ | easy | easy ].
  now apply rank_of_permut_in_sym_gr_list_el with (n := n).
}
exists p.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem rank_in_canon_sym_gr_of_rank_in_sym_gr_of_its_inverse : ∀ n sg
    (Hsg : is_sym_gr_list n sg) k,
  rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg
    (rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg k) = k.
Proof.
intros.
destruct k as (k, pk); cbn - [ "<?" ].
apply eq_exist_uncurried; cbn.
assert
  (p :
   rank_of_permut_in_canon_sym_gr_list n
     (nth (rank_of_permut_in_sym_gr sg (nth k (canon_sym_gr_list_list n) []))
        sg []) = k). {
  specialize (proj1 (Nat.ltb_lt _ _) pk) as Hkn.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ cbn | easy ].
  rewrite (@nth_rank_of_permut_in_sym_gr _ _ n); cycle 1. {
    easy.
  } {
    now apply canon_sym_gr_list_is_permut.
  } {
    apply length_canon_sym_gr_list.
  }
  now apply rank_of_canon_permut_of_canon_rank.
}
exists p.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem sym_gr_size : ∀ n sg, is_sym_gr_list n sg → length sg = n!.
Proof.
intros * Hsg.
apply (bijective_fin_t _ _ (rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg)).
exists (rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg).
split. {
  intros x.
  apply rank_in_sym_gr_of_rank_in_canon_sym_gr_of_its_inverse.
} {
  intros y.
  apply rank_in_canon_sym_gr_of_rank_in_sym_gr_of_its_inverse.
}
Qed.

(* *)

Record sym_gr_list n :=
  { sg_list : list (list nat);
    sg_prop : is_sym_gr_list n sg_list }.

Theorem canon_sym_gr_vect_is_permut : ∀ n k,
  k < n!
  → is_permut_list (nth k (canon_sym_gr_list_list n) []).
Proof.
intros * Hkn.
unfold is_permut_list.
cbn; unfold canon_sym_gr_list_list.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
now apply canon_sym_gr_list_is_permut.
Qed.

Theorem canon_sym_gr_list_inj : ∀ n i j,
  i < fact n
  → j < fact n
  → canon_sym_gr_list n i = canon_sym_gr_list n j
  → i = j.
Proof.
intros * Hi Hj Hij.
apply (f_equal (@rank_of_permut_in_canon_sym_gr_list n)) in Hij.
rewrite rank_of_canon_permut_of_canon_rank in Hij; [ | easy ].
rewrite rank_of_canon_permut_of_canon_rank in Hij; [ | easy ].
easy.
Qed.

Theorem canon_sym_gr_is_sym_gr_list : ∀ n,
  is_sym_gr_list n (canon_sym_gr_list_list n).
Proof.
intros.
split. {
  rewrite length_canon_sym_gr_list_list.
  intros i Hi.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite length_canon_sym_gr_list.
  split; [ easy | ].
  now apply canon_sym_gr_list_is_permut.
}
split. {
  rewrite length_canon_sym_gr_list_list.
  intros i j Hi Hj Hij.
  unfold canon_sym_gr_list_list in Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  now apply canon_sym_gr_list_inj in Hij.
} {
  intros l Hl Hp.
  unfold canon_sym_gr_list_list.
  apply in_map_iff.
  exists (rank_of_permut_in_canon_sym_gr_list n l).
  rewrite permut_in_canon_sym_gr_of_its_rank; [ | easy | easy ].
  split; [ easy | ].
  apply in_seq.
  split; [ flia | ].
  now apply rank_of_canon_permut_ub.
}
Qed.

Theorem rank_of_permut_in_canon_gr_list_inj : ∀ n la lb,
  is_permut_list la
  → is_permut_list lb
  → length la = n
  → length lb = n
  → rank_of_permut_in_canon_sym_gr_list n la =
    rank_of_permut_in_canon_sym_gr_list n lb
  → la = lb.
Proof.
intros * Hla Hlb Han Hbn Hrr.
apply (f_equal (canon_sym_gr_list n)) in Hrr.
rewrite permut_in_canon_sym_gr_of_its_rank in Hrr; [ | easy | easy ].
rewrite permut_in_canon_sym_gr_of_its_rank in Hrr; [ | easy | easy ].
easy.
Qed.
