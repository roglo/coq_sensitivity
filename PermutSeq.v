(* permutations of sequences of natural numbers between 1 and n *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Require Import Permutation.
Import List List.ListNotations.

Require Import Misc RingLike MyVector.
Require Import IterMul IterAnd.
Require Import Pigeonhole.

Definition comp {A B C} (f : B → C) (g : A → B) x := f (g x).

Definition comp_list (la lb : list nat) :=
  map (λ i, nth i la 0) lb.

Definition permut_comp (σ₁ σ₂ : vector nat) :=
  mk_vect (comp_list (vect_list σ₁) (vect_list σ₂)).

(*
Compute (comp_list [0;2;1] [2;1;0]).
Compute (map (comp (λ i, nth i [0;2;1] 0) (λ i, nth i [2;1;0] 0)) [0;1;2]).
*)

Notation "σ₁ ° σ₂" := (permut_comp σ₁ σ₂) (at level 40).

Notation "'Comp' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, comp c g) (λ i, i))
  (at level 35, i at level 0, l at level 60).

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

(* Permutations of {0, 1, 2, ... n-1} *)

Definition is_permut_list l :=
  (∀ x, x ∈ l → x < length l) ∧
  (∀ i j, i < length l → j < length l → nth i l 0 = nth j l 0 → i = j).
Definition is_permut_vect (p : vector nat) := is_permut_list (vect_list p).

Definition is_permut_list_bool l :=
  (⋀ (a ∈ l), (a <? length l)) &&
  (⋀ (i = 1, length l),
     (⋀ (j = 1, length l),
        ((nth (i - 1) l 0 ≠? nth (j - 1) l 0) || (i =? j)))).

Definition is_permut_vect_bool (p : vector nat) :=
  is_permut_list_bool (vect_list p).

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

Theorem is_permut_vect_is_permut_vect_bool : ∀ v,
  is_permut_vect v ↔ is_permut_vect_bool v = true.
Proof.
intros.
unfold is_permut_vect.
apply is_permut_list_is_permut_list_bool.
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

(* vector of all canonic permutations vectors *)
Definition canon_sym_gr_vect n : vector (vector nat) :=
  mk_vect (map (mk_vect (T := nat)) (canon_sym_gr_list_list n)).

(*
Compute (let n := 4 in map (canon_sym_gr_list n) (seq 0 n!)).
Compute (let n := 3 in ((*canon_sym_gr n,*) canon_sym_gr_vect n)).
*)

Definition is_sym_gr n (vv : vector (vector nat)) :=
  (∀ i, i < vect_size vv →
   vect_size (vect_el empty_vect vv i) = n ∧
   is_permut_vect (vect_el empty_vect vv i)) ∧
  (∀ i j, i < vect_size vv → j < vect_size vv →
   vect_el empty_vect vv i = vect_el empty_vect vv j → i = j) ∧
  (∀ v, vect_size v = n → is_permut_vect v → v ∈ vect_list vv).

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

Definition permut_vect_inv (v : vector nat) :=
  mk_vect (permut_list_inv (vect_list v)).

(**)

Definition vect_eqb A eqb (u v : vector A) :=
  list_eqb eqb (vect_list u) (vect_list v).

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

Definition vect_swap_elem {A} d (v : vector A) i j :=
  mk_vect
    (map (λ k, vect_el d v (transposition i j k))
       (seq 0 (length (vect_list v)))).

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

Theorem permut_vect_ub : ∀ v i,
  is_permut_vect v → i < vect_size v → vect_el 0 v i < vect_size v.
Proof.
intros (l); cbn; intros * Hp Hin.
now apply permut_list_ub.
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

Theorem vect_swap_elem_is_permut : ∀ σ p q,
  p < vect_size σ
  → q < vect_size σ
  → is_permut_vect σ
  → is_permut_vect (vect_swap_elem 0 σ p q).
Proof.
intros * Hp Hq Hσ.
split; cbn. {
  intros i Hi.
  rewrite map_length, seq_length.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  rewrite <- Hji.
  apply permut_vect_ub; [ easy | ].
  now apply transposition_lt.
} {
  rewrite map_length, seq_length, fold_vect_size.
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

Definition rank_of_permut_in_sym_gr (sg : vector (vector nat)) σ :=
  unsome 0 (List_find_nth (vect_eqb Nat.eqb σ) (vect_list sg)).

Theorem vect_eqb_eq : ∀ u v, vect_eqb Nat.eqb u v = true → u = v.
Proof.
intros * Huv.
unfold vect_eqb in Huv.
destruct u as (u).
destruct v as (v).
cbn in Huv; f_equal.
now apply list_eqb_eq.
Qed.

Theorem vect_eqb_neq : ∀ u v, vect_eqb Nat.eqb u v = false → u ≠ v.
Proof.
intros * Huv.
destruct u as (u).
destruct v as (v).
intros H.
injection H; clear H; intros H.
revert H.
now apply list_eqb_neq.
Qed.

Theorem rank_of_permut_in_sym_gr_lt : ∀ n sg v,
  n ≠ 0
  → is_sym_gr n sg
  → rank_of_permut_in_sym_gr sg v < vect_size sg.
Proof.
intros * Hnz Hsg.
unfold rank_of_permut_in_sym_gr.
unfold unsome.
remember (List_find_nth _ _) as i eqn:Hi; symmetry in Hi.
destruct i as [i| ]; [ now apply List_find_nth_Some_lt in Hi | ].
clear Hi.
destruct (lt_dec 0 (vect_size sg)) as [Hs| Hs]; [ easy | ].
apply Nat.nlt_ge in Hs; exfalso.
apply Nat.le_0_r in Hs.
destruct Hsg as (Hsg & Hinj & Hsurj).
specialize (Hsurj (mk_vect (seq 0 n))) as H1.
cbn in H1; rewrite seq_length in H1.
specialize (H1 eq_refl).
assert (H : is_permut_vect (mk_vect (seq 0 n))). {
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
specialize (H1 H); clear H.
apply length_zero_iff_nil in Hs.
now rewrite Hs in H1.
Qed.

Theorem vect_el_rank_of_permut_in_sym_gr : ∀ sg v n,
  is_sym_gr n sg
  → is_permut_vect v
  → vect_size v = n
  → vect_el empty_vect sg (rank_of_permut_in_sym_gr sg v) = v.
Proof.
intros * Hsg Hp Hs.
unfold rank_of_permut_in_sym_gr, unsome.
remember (List_find_nth _ _) as i eqn:Hi; symmetry in Hi.
destruct i as [i| ]. {
  apply List_find_nth_Some with (d := empty_vect) in Hi.
  destruct Hi as (Hji, Hi).
  now apply vect_eqb_eq in Hi.
}
assert (H : v ∉ vect_list sg). {
  intros H.
  apply In_nth with (d := empty_vect) in H.
  destruct H as (j & Hj & Hjv).
  specialize (List_find_nth_None empty_vect _ _ Hi Hj) as H.
  apply vect_eqb_neq in H.
  now symmetry in Hjv.
}
exfalso; apply H.
now apply Hsg.
Qed.

Theorem rank_of_permut_in_sym_gr_vect_el : ∀ n sg i,
  n ≠ 0
  → is_sym_gr n sg
  → i < vect_size sg
  → rank_of_permut_in_sym_gr sg (vect_el empty_vect sg i) = i.
Proof.
intros * Hnz Hsg Hi.
unfold rank_of_permut_in_sym_gr, unsome.
remember (List_find_nth _ _) as j eqn:Hj; symmetry in Hj.
destruct j as [j| ]. {
  apply List_find_nth_Some with (d := empty_vect) in Hj.
  destruct Hj as (Hji, Hj).
  apply vect_eqb_eq in Hj.
  rewrite fold_vect_el in Hj.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  apply Hinj; [ | easy | easy ].
  destruct (lt_dec j (vect_size sg)) as [Hjs| Hjs]; [ easy | exfalso ].
  apply Nat.nlt_ge in Hjs.
  unfold vect_el in Hj at 2.
  rewrite nth_overflow in Hj; [ | easy ].
  specialize (Hsg i Hi) as H1.
  destruct H1 as (H1, H2).
  now rewrite Hj in H1; cbn in H1; subst n.
}
specialize (List_find_nth_None empty_vect _ _ Hj Hi) as H1.
now apply vect_eqb_neq in H1.
Qed.

Theorem vect_size_of_empty_sym_gr : ∀ sg,
  is_sym_gr 0 sg → vect_size sg = 1.
Proof.
intros * Hsg.
destruct Hsg as (Hsg & Hinj & Hsurj).
specialize (Hsurj empty_vect eq_refl) as H1.
assert (H : is_permut_vect empty_vect). {
  now apply is_permut_vect_is_permut_vect_bool.
}
specialize (H1 H); clear H.
apply (In_nth _ _ empty_vect) in H1.
destruct H1 as (i & Hil & Hi).
unfold vect_el in Hi.
rewrite fold_vect_size in Hil.
destruct (Nat.eq_dec (vect_size sg) 0) as [Hvz| Hvz]. {
  now rewrite Hvz in Hil.
}
destruct (Nat.eq_dec (vect_size sg) 1) as [Hv1| Hv1]; [ easy | ].
specialize (Hsg 0) as H1.
specialize (Hsg 1) as H2.
specialize (Hinj 0 1) as H3.
assert (H : 0 < vect_size sg) by flia Hvz.
specialize (H1 H); specialize (H3 H); clear H.
assert (H : 1 < vect_size sg) by flia Hvz Hv1.
specialize (H2 H); specialize (H3 H); clear H.
destruct H1 as (H4, H5).
destruct H2 as (H6, H7).
enough (H : vect_el empty_vect sg 0 = vect_el empty_vect sg 1). {
  now apply H3 in H.
}
unfold vect_size in H4, H6.
apply length_zero_iff_nil in H4, H6.
unfold vect_el in H4, H6 |-*.
remember (nth 0 (vect_list sg) empty_vect) as x eqn:Hx.
remember (nth 1 (vect_list sg) empty_vect) as y eqn:Hy.
symmetry in Hx, Hy.
destruct x as (x).
destruct y as (y).
cbn in H4, H6.
now subst x y.
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

(*
Theorem canon_sym_gr_inv_sym_gr : ∀ n k i,
  i < n
  → k < fact n
  → canon_sym_gr_inv n k (canon_sym_gr_elem n k i) = i.
*)
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

(*
Theorem nth_canon_sym_gr_list_inj2 : ∀ n i j,
  i < n!
  → j < n!
  → (∀ k, k < n →
     nth k (canon_sym_gr_list n i) 0 = nth k (canon_sym_gr_list n j) 0)
  → i = j.
Proof.
intros * Hin Hjn Hij.
revert i j Hin Hjn Hij.
induction n; intros; [ apply Nat.lt_1_r in Hin, Hjn; congruence | ].
destruct (Nat.eq_dec (i / n!) (j / n!)) as [Hijd| Hijd]. 2: {
  now specialize (Hij 0 (Nat.lt_0_succ _)).
}
destruct (Nat.eq_dec (i mod n!) (j mod n!)) as [Hijm| Hijm]. {
  specialize (Nat.div_mod i n! (fact_neq_0 _)) as Hi.
  specialize (Nat.div_mod j n! (fact_neq_0 _)) as Hj.
  congruence.
}
exfalso; apply Hijm; clear Hijm.
apply IHn. {
  apply Nat.mod_upper_bound, fact_neq_0.
} {
  apply Nat.mod_upper_bound, fact_neq_0.
}
intros k Hk.
cbn - [ fact nth ] in Hij |-*.
specialize (Hij (S k)) as H1.
assert (H : S k < S n) by flia Hk.
specialize (H1 H); clear H.
cbn - [ fact ] in H1.
rewrite Hijd in H1.
rewrite (List_map_nth' 0) in H1; [ | now rewrite length_canon_sym_gr_list ].
rewrite (List_map_nth' 0) in H1; [ | now rewrite length_canon_sym_gr_list ].
unfold succ_when_ge, Nat.b2n in H1.
do 2 rewrite if_leb_le_dec in H1.
destruct (le_dec (j / n!) _) as [H2| H2]. {
  destruct (le_dec (j / n!) _) as [H3| H3]; [ | flia H1 H2 H3 ].
  now apply Nat.add_cancel_r in H1.
}
destruct (le_dec (j / n!) _) as [H3| H3]; [ flia H1 H2 H3 | flia H1 ].
Qed.
*)

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

Definition rank_of_permut_in_canon_sym_gr_vect n v :=
  rank_of_permut_in_canon_sym_gr_list n (vect_list v).

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
  }.
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
  is_sym_gr n sg
  → ∀ k : fin_t n!,
      (rank_of_permut_in_sym_gr sg
         (vect_el empty_vect (canon_sym_gr_vect n) (proj1_sig k)) <?
       vect_size sg) = true.
Proof.
intros * Hsg k.
apply Nat.ltb_lt.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  destruct k as (k, pk); cbn.
  apply Nat.ltb_lt, Nat.lt_1_r in pk; subst k.
  specialize (vect_size_of_empty_sym_gr Hsg) as Hs.
  destruct sg as (lv); cbn in Hs.
  destruct lv as [| v]; [ easy | ].
  destruct lv; [ clear Hs | easy ].
  destruct Hsg as (Hsg & _ & _).
  specialize (Hsg 0 Nat.lt_0_1); cbn in Hsg.
  destruct Hsg as (H1, H2).
  destruct v as (l); cbn in H1 |-*.
  apply length_zero_iff_nil in H1; subst l.
  apply Nat.lt_0_1.
}
now apply rank_of_permut_in_sym_gr_lt with (n := n).
Qed.

Theorem rank_in_canon_sym_gr_of_rank_in_sym_gr_prop : ∀ n sg,
  is_sym_gr n sg
  → ∀ k : fin_t (vect_size sg),
      (rank_of_permut_in_canon_sym_gr_vect n
         (vect_el empty_vect sg (proj1_sig k)) <? n!) = true.
Proof.
intros * Hsg k.
destruct Hsg as (Hsg & Hinj & Hsurj).
apply Nat.ltb_lt.
destruct k as (k, pk); cbn.
apply Nat.ltb_lt in pk.
now apply rank_of_canon_permut_ub; apply Hsg.
Qed.

Definition rank_in_sym_gr_of_rank_in_canon_sym_gr n sg
    (Hsg : is_sym_gr n sg) (k : fin_t n!) : fin_t (vect_size sg) :=
  exist (λ a : nat, (a <? vect_size sg) = true)
    (rank_of_permut_in_sym_gr sg
      (vect_el empty_vect (canon_sym_gr_vect n) (proj1_sig k)))
    (rank_in_sym_gr_of_rank_in_canon_sym_gr_prop Hsg k).

Definition rank_in_canon_sym_gr_of_rank_in_sym_gr  n sg
    (Hsg : is_sym_gr n sg) (k : fin_t (vect_size sg)) : fin_t n! :=
  exist (λ a : nat, (a <? n!) = true)
    (rank_of_permut_in_canon_sym_gr_vect n
       (vect_el empty_vect sg (proj1_sig k)))
    (rank_in_canon_sym_gr_of_rank_in_sym_gr_prop Hsg k).

Theorem rank_in_sym_gr_of_rank_in_canon_sym_gr_of_its_inverse : ∀ n sg
    (Hsg : is_sym_gr n sg) k,
  rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg
    (rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg k) = k.
Proof.
intros.
destruct k as (k, pk); cbn - [ "<?" ].
apply eq_exist_uncurried.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  specialize (vect_size_of_empty_sym_gr Hsg) as Hs.
  specialize (proj1 (Nat.ltb_lt _ _) pk) as Hk.
  rewrite Hs in Hk.
  apply Nat.lt_1_r in Hk; subst k.
  assert (p : rank_of_permut_in_sym_gr sg {| vect_list := [] |} = 0). {
    unfold rank_of_permut_in_sym_gr, unsome, vect_eqb; cbn.
    destruct sg as (lv); cbn in Hs |-*.
    destruct lv as [| v]; [ easy | ].
    destruct lv; [ cbn | easy ].
    cbn in Hsg.
    destruct Hsg as (Hsg & _ & _).
    specialize (Hsg 0 Nat.lt_0_1); cbn in Hsg.
    destruct Hsg as (H1, H2).
    destruct v as (l); cbn in H1 |-*.
    now apply length_zero_iff_nil in H1; subst l.
  }
  exists p.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
}  
assert
  (p :
   rank_of_permut_in_sym_gr sg
     (vect_el empty_vect (canon_sym_gr_vect n)
        (proj1_sig
           (rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg (exist _ k pk)))) =
    k). {
  cbn.
  apply Nat.ltb_lt in pk.
  unfold rank_of_permut_in_canon_sym_gr_vect.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  rewrite (List_map_nth' []). 2: {
    rewrite length_canon_sym_gr_list_list.
    now apply rank_of_canon_permut_ub; apply Hsg.
  }
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply rank_of_canon_permut_ub; apply Hsg.
  }
  rewrite seq_nth. 2: {
    now apply rank_of_canon_permut_ub; apply Hsg.
  }
  rewrite Nat.add_0_l.
  rewrite permut_in_canon_sym_gr_of_its_rank; cycle 1. {
    now apply Hsg.
  } {
    now apply Hsg.
  }
  rewrite mk_vect_vect_list.
  now apply rank_of_permut_in_sym_gr_vect_el with (n := n).
}
exists p.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem rank_in_canon_sym_gr_of_rank_in_sym_gr_of_its_inverse : ∀ n sg
    (Hsg : is_sym_gr n sg) k,
  rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg
    (rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg k) = k.
Proof.
intros.
destruct k as (k, pk); cbn - [ "<?" ].
apply eq_exist_uncurried.
assert
  (p :
   rank_of_permut_in_canon_sym_gr_vect n
     (vect_el empty_vect sg
       (proj1_sig
          (rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg (exist _ k pk)))) =
    k). {
  specialize (proj1 (Nat.ltb_lt _ _) pk) as Hkn.
  unfold rank_in_sym_gr_of_rank_in_canon_sym_gr.
  unfold rank_of_permut_in_canon_sym_gr_vect; cbn.
  rewrite (List_map_nth' []); [ | now rewrite length_canon_sym_gr_list_list ].
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ cbn | easy ].
  rewrite (@vect_el_rank_of_permut_in_sym_gr _ _ n); cycle 1. {
    easy.
  } {
    unfold is_permut_vect; cbn.
    now apply canon_sym_gr_list_is_permut.
  } {
    apply length_canon_sym_gr_list.
  }
  unfold vect_el; cbn.
  now apply rank_of_canon_permut_of_canon_rank.
}
exists p.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem sym_gr_size : ∀ n sg, is_sym_gr n sg → vect_size sg = n!.
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

Record sym_gr_vect n :=
  { sg_vect : vector (vector nat);
    sg_prop : is_sym_gr n sg_vect }.

(*
Theorem canon_is_permut_vect : ∀ n k,
  k < n!
  → is_permut_vect (vect_vect_nat_el (canon_sym_gr n) k).
*)
Theorem canon_sym_gr_vect_is_permut : ∀ n k,
  k < n!
  → is_permut_vect (vect_el empty_vect (canon_sym_gr_vect n) k).
Proof.
intros * Hkn.
unfold is_permut_vect; cbn.
rewrite (List_map_nth' []); [ | now rewrite length_canon_sym_gr_list_list ].
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

Theorem canon_sym_gr_size : ∀ n, vect_size (canon_sym_gr_vect n) = n!.
Proof.
intros; cbn.
now rewrite map_length, length_canon_sym_gr_list_list.
Qed.

Theorem vect_el_mk_vect : ∀ A i d (l : list A),
  vect_el d (mk_vect l) i = nth i l d.
Proof. easy. Qed.

Theorem canon_sym_gr_is_sym_gr : ∀ n, is_sym_gr n (canon_sym_gr_vect n).
Proof.
intros.
split. {
  intros i Hi; cbn.
  rewrite canon_sym_gr_size in Hi.
  rewrite (List_map_nth' []); [ | now rewrite length_canon_sym_gr_list_list ].
  cbn; unfold is_permut_vect; cbn.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ cbn | easy ].
  rewrite length_canon_sym_gr_list.
  split; [ easy | ].
  now apply canon_sym_gr_list_is_permut.
}
split. {
  intros i j Hi Hj Hij.
  rewrite canon_sym_gr_size in Hi, Hj.
  cbn in Hij.
  rewrite (List_map_nth' []) in Hij. 2: {
    now rewrite length_canon_sym_gr_list_list.
  }
  rewrite (List_map_nth' []) in Hij. 2: {
    now rewrite length_canon_sym_gr_list_list.
  }
  injection Hij; clear Hij; intros Hij.
  unfold canon_sym_gr_list_list in Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  now apply canon_sym_gr_list_inj in Hij.
} {
  intros (l) Hv Hp.
  cbn in Hv, Hp |-*.
  unfold is_permut_vect in Hp; cbn in Hp.
  apply in_map.
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

Inspect 1.

...

Theorem rank_of_permut_injective : ∀ n f g,
  is_permut_fun f n
  → is_permut_fun g n
  → rank_of_permut_in_canon_sym_gr n f = rank_of_permut_in_canon_sym_gr n g
  → ∀ i, i < n → f i = g i.
Proof.
intros * Hσ₁ Hσ₂ Hσσ i Hi.
apply (f_equal (canon_sym_gr_elem n)) in Hσσ.
apply (f_equal (λ f, f i)) in Hσσ.
rewrite permut_in_canon_sym_gr_of_its_rank in Hσσ; [ | easy | easy ].
rewrite permut_in_canon_sym_gr_of_its_rank in Hσσ; [ | easy | easy ].
easy.
Qed.

Theorem canon_sym_gr_vect_prop : ∀ n,
  is_sym_gr n (canon_sym_gr n).
Proof.
intros.
split. {
  now cbn; rewrite map_length, seq_length.
}
split. {
  intros i Hi; cbn.
  rewrite (List_map_nth' 0); [ cbn | now rewrite seq_length ].
  now rewrite map_length, seq_length.
}
split. {
  intros i j Hi Hj Hij.
  cbn in Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  apply (f_equal (@rank_of_permut_in_canon_sym_gr n)) in Hij.
  unfold vect_el in Hij.
  cbn in Hij.
  erewrite rank_of_permut_in_canon_sym_gr_eq_compat in Hij. 2: {
    intros k Hk.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    now rewrite seq_nth.
  }
  symmetry in Hij.
  erewrite rank_of_permut_in_canon_sym_gr_eq_compat in Hij. 2: {
    intros k Hk.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    now rewrite seq_nth.
  }
  symmetry in Hij.
  rewrite rank_of_permut_of_rank in Hij; [ | easy ].
  rewrite rank_of_permut_of_rank in Hij; [ | easy ].
  easy.
} {
  intros i Hi.
  eapply is_permut_eq_compat. {
    intros k Hk.
    symmetry.
    unfold vect_el; cbn.
    rewrite (List_map_nth' 0); [ cbn | now rewrite seq_length ].
    rewrite (List_map_nth' 0); [ cbn | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite seq_nth; [ | easy ].
    now do 2 rewrite Nat.add_0_l.
  }
  now apply sym_gr_elem_is_permut.
}
Qed.

(* signatures *)

Definition δ i j u v :=
  if i <? j then (rngl_of_nat v - rngl_of_nat u)%F else 1%F.

Definition ε_fun f n :=
  ((∏ (i = 1, n), ∏ (j = 1, n), δ i j (f (i - 1)%nat) (f (j - 1)%nat)) /
   (∏ (i = 1, n), ∏ (j = 1, n), δ i j i j))%F.

Definition ε n (p : vector nat) := ε_fun (vect_el 0 p) n.

(* signature of the k-th permutation of the symmetric group *)

Fixpoint ε_permut n k :=
  match n with
  | 0 => 1%F
  | S n' => (minus_one_pow (k / fact n') * ε_permut n' (k mod fact n'))%F
  end.

(* alternative version of signature of a permutation
   using only signs: ws = with sign *)

Definition sign_diff u v := if v <? u then 1%F else (-1)%F.
Definition abs_diff u v := if v <? u then u - v else v - u.

Definition ε_fun_ws f n :=
  (∏ (i = 1, n), ∏ (j = 1, n),
   if i <? j then sign_diff (f (j - 1)%nat) (f (i - 1)%nat) else 1)%F.

Definition ε_ws n (p : vector nat) := ε_fun_ws (vect_el 0 p) n.

(* equality of both definitions of ε: ε and ε_ws *)

Theorem rngl_product_product_if : ∀ b e f,
  (∏ (i = b, e), ∏ (j = b, e), if i <? j then f i j else 1)%F =
  (∏ (i = b, e), ∏ (j = i + 1, e), f i j)%F.
Proof.
intros.
apply rngl_product_eq_compat.
intros i Hi.
rewrite (rngl_product_split i); [ | flia Hi ].
rewrite all_1_rngl_product_1. 2: {
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [H| H]; [ flia Hj H | easy ].
}
rewrite rngl_mul_1_l.
apply rngl_product_eq_compat.
intros j Hj.
rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [H| H]; [ easy | flia Hj H ].
Qed.

Theorem rngl_of_nat_sub :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ i j,
  i < j
  → (rngl_of_nat j - rngl_of_nat i)%F = rngl_of_nat (j - i).
Proof.
intros Hom * Hij.
revert j Hij.
induction i; intros; cbn. {
  rewrite rngl_sub_0_r; f_equal; [ | easy ].
  now destruct j.
}
destruct j; [ easy | cbn ].
rewrite rngl_add_sub_simpl_l; [ | easy ].
apply IHi.
now apply Nat.succ_lt_mono in Hij.
Qed.

Theorem rngl_of_nat_add : ∀ a b,
  (rngl_of_nat a + rngl_of_nat b)%F = rngl_of_nat (a + b).
Proof.
intros.
induction a; [ apply rngl_add_0_l | ].
now cbn; rewrite <- rngl_add_assoc; f_equal.
Qed.

Theorem rngl_of_nat_mul :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b, (rngl_of_nat a * rngl_of_nat b)%F = rngl_of_nat (a * b).
Proof.
intros Hom *.
induction a; [ now apply rngl_mul_0_l | cbn ].
rewrite rngl_mul_add_distr_r.
rewrite rngl_mul_1_l.
rewrite IHa.
apply rngl_of_nat_add.
Qed.

Theorem rngl_product_rngl_of_nat :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ n, (∏ (i = 1, n), rngl_of_nat i)%F = rngl_of_nat (fact n).
Proof.
intros Hom *.
induction n. {
  rewrite rngl_product_empty; [ | flia ].
  symmetry; apply rngl_add_0_r.
}
rewrite rngl_product_split_last; [ | flia ].
rewrite rngl_product_succ_succ.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat_sub_succ_1.
}
rewrite IHn.
rewrite Nat_fact_succ.
rewrite Nat.mul_comm.
now apply rngl_of_nat_mul.
Qed.

Theorem rngl_sub_is_mul_sign_abs :
  rngl_has_opp = true →
  ∀ a b,
  (rngl_of_nat a - rngl_of_nat b)%F =
  (sign_diff a b * rngl_of_nat (abs_diff a b))%F.
Proof.
intros Hop *.
unfold sign_diff, abs_diff.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec b a) as [Hba| Hba]. {
  rewrite rngl_mul_1_l.
  apply rngl_of_nat_sub; [ now left | easy ].
} {
  apply Nat.nlt_ge in Hba.
  destruct (Nat.eq_dec a b) as [Hab| Hab]. {
    subst b.
    rewrite rngl_sub_diag, Nat.sub_diag; cbn; [ | now left ].
    symmetry.
    now apply rngl_mul_0_r; left.
  }
  rewrite <- rngl_opp_sub_distr; [ | easy ].
  rewrite rngl_of_nat_sub; [ | now left | flia Hba Hab ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
}
Qed.

Theorem rngl_product_change_var : ∀ A b e f g (h : _ → A),
  (∀ i, b ≤ i ≤ e → g (h i) = i)
  → (∏ (i = b, e), f i = ∏ (i ∈ map h (seq b (S e - b))), f (g i))%F.
Proof.
intros * Hgh.
unfold iter_seq, iter_list.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros i c Hi.
f_equal; f_equal; symmetry.
apply Hgh.
apply in_seq in Hi.
flia Hi.
Qed.

Theorem fun_find_prop : ∀ f n i,
  (∀ i j, i < n → j < n → f i = f j → i = j)
  → i < n
  → permut_fun_inv_loop f n (f i) = i.
Proof.
intros * Hp2 Hin.
revert i Hin.
induction n; intros; [ easy | cbn ].
destruct (Nat.eq_dec (f n) (f i)) as [Hfni| Hfni]. {
  apply Hp2; [ flia | easy | easy ].
}
rename Hin into Hisn.
assert (Hin : i < n). {
  destruct (Nat.eq_dec n i) as [H| H]; [ now subst n | ].
  flia Hisn H.
}
clear Hisn.
apply IHn; [ | easy ].
intros j k Hj Hk Hjk.
apply Hp2; [ flia Hj | flia Hk | easy ].
Qed.

Theorem permut_fun_inv_loop_fun : ∀ f n,
  is_permut_fun f n
  → ∀ i, i < n
  → permut_fun_inv_loop f n (f i) = i.
Proof.
intros * (Hp1, Hp2) * Hin.
apply fun_find_prop; [ | easy ].
intros j k Hj Hk Hjk.
now apply Hp2.
Qed.

Theorem permut_fun_inv_loop_fun' : ∀ f n,
  (∀ i j, i < n → j < n → f i = f j → i = j)
  → ∀ i, i < n
  → permut_fun_inv_loop f n (f i) = i.
Proof.
intros * Hp2 * Hin.
apply fun_find_prop; [ | easy ].
intros j k Hj Hk Hjk.
now apply Hp2.
Qed.

Definition permut_fun_inv_loop' f n i :=
  let '(x, x') :=
    pigeonhole_fun (S n) (λ j, if Nat.eq_dec j n then i else f j)
  in
  if Nat.eq_dec x n then x' else x.

Theorem fun_find_permut_fun_inv_loop' : ∀ f n,
  is_permut_fun f n
  → ∀ i, i < n
  → permut_fun_inv_loop f n i = permut_fun_inv_loop' f n i.
Proof.
intros * (Hfub, Hinj) * Hin.
unfold permut_fun_inv_loop'.
remember (pigeonhole_fun _ _) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (j, j').
unfold pigeonhole_fun in Hxx.
remember (find_dup _ _) as fd eqn:Hfd.
symmetry in Hfd.
destruct fd as [(x, x')| ]. {
  injection Hxx; clear Hxx; intros; subst x x'.
  apply find_dup_some in Hfd.
  destruct Hfd as (Hij & la1 & la2 & la3 & Hfd).
  destruct (Nat.eq_dec j n) as [Hjn| Hjn]. {
    subst j.
    destruct (Nat.eq_dec j' n) as [Hin'| Hin']. {
      subst j'; clear Hij.
      exfalso.
      revert Hfd.
      apply List_seq_nothing_after_last.
    }
    subst i.
    apply fun_find_prop; [ easy | ].
    assert (H : j' ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right; right.
      now apply in_app_iff; right; left.
    }
    apply in_seq in H.
    flia Hin' H.
  }
  destruct (Nat.eq_dec j' n) as [Hjn'| Hjn']. {
    subst j' i.
    apply fun_find_prop; [ easy | ].
    assert (H : j ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right.
      now left.
    }
    apply in_seq in H.
    flia Hjn H.
  }
  apply Hinj in Hij; cycle 1. {
    assert (H : j ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right.
      now left.
    }
    apply in_seq in H.
    flia Hjn H.
  } {
    assert (H : j' ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right; right.
      now apply in_app_iff; right; left.
    }
    apply in_seq in H.
    flia Hjn' H.
  }
  subst j'.
  exfalso.
  specialize (seq_NoDup (S n) 0) as H1.
  rewrite Hfd in H1.
  apply NoDup_app_remove_l in H1.
  rewrite app_comm_cons in H1.
  specialize (proj1 (NoDup_app_iff _ _) H1) as (_ & _ & H2).
  specialize (H2 j (or_introl eq_refl)).
  apply H2.
  now left.
}
injection Hxx; clear Hxx; intros; subst j j'.
apply find_dup_none in Hfd.
replace (if Nat.eq_dec _ _ then _ else _) with 0. 2: {
  now destruct (Nat.eq_dec 0 n).
}
specialize (proj1 (NoDup_map_iff 0 _ _) Hfd) as H1.
rewrite seq_length in H1.
assert
  (H2 : ∀ j k,
   j < S n
   → k < S n
   → (if Nat.eq_dec j n then i else f j) = (if Nat.eq_dec k n then i else f k)
   → j = k). {
  intros j k Hj Hk.
  specialize (H1 j k Hj Hk).
  now do 2 rewrite seq_nth in H1.
}
clear H1; rename H2 into H1.
apply not_NoDup_map_f_seq with (b := n) in Hfd; [ easy | flia | ].
intros j Hj.
destruct (Nat.eq_dec j n) as [Hjn| Hjn]; [ easy | ].
apply Hfub.
flia Hj Hjn.
Qed.

(* the proof that "vect_el σ (vect_el (permut_vect_inv σ) i) = i"
   is proven by the pigeonhole principle *)

Theorem pigeonhole' : ∀ f n,
  (∀ i, i < n → f i < n)
  → (∀ i j, i < n → j < n → f i = f j → i = j)
  → ∀ i, i < n
  → ∀ j, j = permut_fun_inv_loop' f n i
  → j < n ∧ f j = i.
Proof.
intros * Hp1 Hp2 * Hin * Hj.
subst j.
unfold permut_fun_inv_loop'.
remember (pigeonhole_fun _ _) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (x, x').
specialize pigeonhole as H1.
specialize (H1 (S n) n).
specialize (H1 (λ j, if Nat.eq_dec j n then i else f j)).
specialize (H1 (Nat.lt_succ_diag_r n)).
cbn in H1.
assert (H : ∀ j, j < S n → (if Nat.eq_dec j n then i else f j) < n). {
  intros j Hj.
  destruct (Nat.eq_dec j n) as [Hjn| Hjn]; [ now subst j | ].
  apply Hp1; flia Hj Hjn.
}
specialize (H1 H x x' Hxx); clear H.
destruct H1 as (Hxn & Hx'n & Hxx' & H1).
destruct (Nat.eq_dec x n) as [H2| H2]. {
  subst x.
  destruct (Nat.eq_dec x' n) as [H2| H2]; [ now subst x' | ].
  split; [ flia Hx'n H2 | easy ].
} {
  destruct (Nat.eq_dec x' n) as [H3| H3]. {
    split; [ flia Hxn H2 | easy ].
  }
  apply Hp2 in H1; [ easy | flia Hxn H2 | flia Hx'n H3 ].
}
Qed.

Theorem fun_permut_fun_inv_loop : ∀ f n,
  is_permut_fun f n
  → ∀ i, i < n
  → f (permut_fun_inv_loop f n i) = i.
Proof.
intros * (Hp1, Hp2) * Hin.
rewrite fun_find_permut_fun_inv_loop'; [ | easy | easy ].
apply (proj2 (pigeonhole' f Hp1 Hp2 Hin eq_refl)).
Qed.

Theorem permut_fun_inv_loop_is_permut : ∀ n f,
  is_permut_fun f n
  → is_permut_fun (permut_fun_inv_loop f n) n.
Proof.
intros * Hp.
destruct Hp as (Hp1, Hp2).
split. {
  intros i Hin; cbn.
  rewrite fun_find_permut_fun_inv_loop'; [ | easy | easy ].
  unfold permut_fun_inv_loop'.
  remember (pigeonhole_fun _ _) as xx eqn:Hxx.
  symmetry in Hxx; destruct xx as (x, x').
  destruct (Nat.eq_dec x n) as [Hxn| Hxn]. {
    subst x.
    unfold pigeonhole_fun in Hxx.
    remember (find_dup _ _) as fd eqn:Hfd; symmetry in Hfd.
    destruct fd as [(x, n')| ]. {
      injection Hxx; clear Hxx; intros; subst x x'.
      apply find_dup_some in Hfd.
      destruct Hfd as (Hij & la1 & la2 & la3 & Hfd).
      exfalso.
      revert Hfd.
      apply List_seq_nothing_after_last.
    }
    now injection Hxx; clear Hxx; intros; subst n x'.
  } {
    unfold pigeonhole_fun in Hxx.
    remember (find_dup _ _) as fd eqn:Hfd; symmetry in Hfd.
    destruct fd as [(n'', n')| ]. {
      injection Hxx; clear Hxx; intros; subst x x'.
      apply find_dup_some in Hfd.
      destruct Hfd as (Hij & la1 & la2 & la3 & Hfd).
      destruct (Nat.eq_dec n'' n) as [Hn''n| Hn''n]; [ now subst n'' | ].
      destruct (Nat.eq_dec n' n) as [Hn'n| Hn'n]. {
        subst n'.
        now apply List_sorted_in_seq in Hfd.
      }
      assert (H : n' ∈ seq 0 (S n)). {
        rewrite Hfd.
        apply in_app_iff; right; right.
        now apply in_app_iff; right; left.
      }
      apply in_seq in H.
      apply List_sorted_in_seq in Hfd.
      apply (Nat.lt_le_trans _ n'); [ easy | flia H ].
    }
    injection Hxx; clear Hxx; intros; subst x x'.
    flia Hin.
  }
}
intros i j Hi Hj Hij.
cbn in Hij.
rewrite fun_find_permut_fun_inv_loop' in Hij; [ | easy | easy ].
rewrite fun_find_permut_fun_inv_loop' in Hij; [ | easy | easy ].
unfold permut_fun_inv_loop' in Hij.
remember (pigeonhole_fun _ _) as xx eqn:Hxx in Hij.
remember (pigeonhole_fun _ _) as yy eqn:Hyy in Hij.
symmetry in Hxx; destruct xx as (x, x').
symmetry in Hyy; destruct yy as (y, y').
move y before x; move y' before x'.
unfold pigeonhole_fun in Hxx, Hyy.
remember (find_dup _ _) as fdi eqn:Hfdi in Hxx.
remember (find_dup _ _) as fdj eqn:Hfdj in Hyy.
symmetry in Hfdi, Hfdj.
move fdj before fdi.
move Hfdj before Hfdi.
destruct fdi as [(x1, x2)| ]. {
  injection Hxx; clear Hxx; intros; subst x1 x2.
  apply find_dup_some in Hfdi.
  destruct Hfdi as (Hij1 & la1 & la2 & la3 & Hfdi).
  destruct (Nat.eq_dec x n) as [Hxn| Hxn]. {
    subst x.
    now apply List_seq_nothing_after_last in Hfdi.
  }
  destruct fdj as [(x1, x2)| ]. {
    injection Hyy; clear Hyy; intros; subst x1 x2.
    apply find_dup_some in Hfdj.
    destruct Hfdj as (Hij2 & lb1 & lb2 & lb3 & Hfdj).
    destruct (Nat.eq_dec y n) as [Hyn| Hyn]; subst y. {
      now apply List_seq_nothing_after_last in Hfdj.
    }
    clear Hyn.
    destruct (Nat.eq_dec x' n) as [Hx'n| Hx'n]. {
      subst x'.
      destruct (Nat.eq_dec y' n) as [Hy'n| Hy'n]; [ congruence | ].
      apply Hp2 in Hij2; cycle 1. {
        assert (H : x ∈ seq 0 (S n)). {
          rewrite Hfdi.
          now apply in_app_iff; right; left.
        }
        apply in_seq in H; cbn in H; flia Hxn H.
      } {
        assert (H : y' ∈ seq 0 (S n)). {
          rewrite Hfdj.
          apply in_app_iff; right; right.
          now apply in_app_iff; right; left.
        }
        apply in_seq in H; cbn in H; flia Hy'n H.
      }
      subst y'.
      apply List_sorted_in_seq in Hfdj.
      now apply Nat.lt_irrefl in Hfdj.
    }
    apply Hp2 in Hij1; cycle 1. {
      assert (H : x ∈ seq 0 (S n)). {
        rewrite Hfdi.
        now apply in_app_iff; right; left.
      }
      apply in_seq in H; cbn in H; flia Hxn H.
    } {
      assert (H : x' ∈ seq 0 (S n)). {
        rewrite Hfdi.
        apply in_app_iff; right; right.
        now apply in_app_iff; right; left.
      }
      apply in_seq in H; cbn in H; flia Hx'n H.
    }
    subst x'.
    apply List_sorted_in_seq in Hfdi.
    now apply Nat.lt_irrefl in Hfdi.
  }
  apply find_dup_none in Hfdj.
  exfalso; revert Hfdj.
  apply not_NoDup_map_f_seq with (b := n); [ flia | ].
  intros k Hk.
  destruct (Nat.eq_dec k n) as [Hkn| Hkn]; [ easy | ].
  apply Hp1; flia Hk Hkn.
}
apply find_dup_none in Hfdi.
exfalso; revert Hfdi.
apply not_NoDup_map_f_seq with (b := n); [ flia | ].
intros k Hk.
destruct (Nat.eq_dec k n) as [Hkn| Hkn]; [ easy | ].
apply Hp1; flia Hk Hkn.
Qed.

Theorem permut_fun_without_last : ∀ n i (a : _ → nat),
  is_permut_fun a (S n)
  → i = permut_fun_inv_loop a (S n) n
  → ∃ b,
     is_permut_fun b n ∧
     map a (seq 0 i ++ seq (S i) (n - i)) = map b (seq 0 n).
Proof.
intros * Hp Hi.
exists (λ j, if lt_dec j i then a j else a (j + 1)).
split. 2: {
  destruct n. {
    cbn in Hi; cbn.
    destruct (Nat.eq_dec (a 0) 0) as [Haz| Haz]; [ now subst i | exfalso ].
    apply Haz.
    destruct Hp as (Hp1, Hp2).
    enough (H : a 0 < 1) by flia H.
    apply Hp1; flia.
  }
  destruct (Nat.eq_dec (a (S n)) (S n)) as [Han| Han]. {
    remember (S n) as sn; cbn in Hi; subst sn.
    rewrite Han in Hi.
    destruct (Nat.eq_dec (S n) (S n)) as [H| H]; [ clear H | easy ].
    subst i.
    rewrite Nat.sub_diag; cbn.
    f_equal.
    rewrite app_nil_r.
    apply map_ext_in.
    intros i Hi.
    apply in_seq in Hi.
    now destruct (lt_dec i (S n)).
  }
  destruct (Nat.eq_dec i (S n)) as [Hsni| Hsni]. {
    rewrite Hsni, Nat.sub_diag.
    cbn; f_equal.
    rewrite app_nil_r.
    apply map_ext_in.
    intros j Hj.
    destruct (lt_dec j (S n)) as [Hjsn| Hjsn]; [ easy | ].
    exfalso; apply Hjsn; clear Hjsn.
    now apply in_seq in Hj.
  }
  symmetry.
  rewrite (List_seq_cut i). 2: {
    apply in_seq.
    split; [ flia | cbn ].
    enough (H : i < S (S n)) by flia Hsni H.
    rewrite Hi.
    apply permut_ub; [ | flia ].
    now apply permut_fun_inv_loop_is_permut.
  }
  symmetry; cbn - [ "-" ].
  rewrite Nat.sub_0_r, Nat.sub_succ.
  rewrite Nat.sub_succ_l. 2: {
    assert (H : i < S (S n)). {
      rewrite Hi.
      apply permut_ub; [ | flia ].
      now apply permut_fun_inv_loop_is_permut.
    }
    flia Hsni H.
  }
  do 2 rewrite map_app.
  f_equal. {
    apply map_ext_in_iff.
    intros j Hj.
    destruct (lt_dec j i) as [Hji| Hji]; [ easy | ].
    now apply in_seq in Hj.
  }
  cbn.
  destruct (lt_dec i i) as [H| H]; [ now apply lt_irrefl in H | clear H ].
  rewrite Nat.add_1_r; f_equal.
  rewrite <- seq_shift.
  rewrite map_map.
  apply map_ext_in_iff.
  intros j Hj.
  rewrite Nat.add_1_r.
  destruct (lt_dec j i) as [Hji| Hji]; [ | easy ].
  apply in_seq in Hj.
  flia Hj Hji.
}
split. {
  intros j Hj.
  assert (Hin : a i = n). {
    rewrite Hi.
    apply fun_permut_fun_inv_loop; [ easy | flia ].
  }
  destruct (lt_dec j i) as [Hji| Hji]. {
    destruct (Nat.eq_dec (a j) n) as [Hajn| Hajn]. {
      rewrite <- Hajn in Hin.
      apply Hp in Hin; [ flia Hji Hin | | flia Hj ].
      rewrite Hi.
      apply permut_ub; [ | flia ].
      now apply permut_fun_inv_loop_is_permut.
    }
    enough (H : a j < S n) by flia Hajn H.
    apply Hp; flia Hj.
  }
  apply Nat.nlt_ge in Hji.
  destruct Hp as (Hp1, Hp2).
  apply Nat.succ_lt_mono in Hj.
  specialize (Hp1 _ Hj) as H1.
  rewrite Nat.add_1_r.
  destruct (Nat.eq_dec (a (S j)) n) as [Hajn| Hajn]. {
    rewrite <- Hajn in Hin.
    apply Hp2 in Hin; [ flia Hin Hji | flia Hj Hji | easy ].
  }
  flia H1 Hajn.
}
intros j k Hj Hk Hjk.
destruct (lt_dec j i) as [Hji| Hji]. {
  destruct (lt_dec k i) as [Hki| Hki]. {
    apply Hp in Hjk; [ easy | flia Hj | flia Hk ].
  }
  apply Nat.nlt_ge in Hki.
  apply Hp in Hjk; [ flia Hji Hki Hjk | flia Hj | flia Hk ].
}
destruct (lt_dec k i) as [Hki| Hki]. {
  apply Hp in Hjk; [ | flia Hj | flia Hk ].
  apply Nat.nlt_ge in Hji.
  flia Hji Hki Hjk.
}
apply Hp in Hjk; [ flia Hjk | flia Hj | flia Hk ].
Qed.

Theorem permut_fun_Permutation : ∀ f n,
  is_permut_fun f n
  → Permutation (map f (seq 0 n)) (seq 0 n).
Proof.
intros a n * Hp.
symmetry.
revert a Hp.
induction n; intros; [ easy | ].
rewrite seq_S at 1.
remember (permut_fun_inv_loop a (S n) n) as i eqn:Hi.
remember (seq 0 n) as s eqn:Hs.
rewrite (List_seq_cut i); subst s. 2: {
  subst i.
  apply in_seq.
  split; [ flia | ].
  apply permut_ub; [ | flia ].
  now apply permut_fun_inv_loop_is_permut.
}
rewrite Nat.sub_0_r; cbn.
rewrite map_app; cbn.
rewrite Hi at 2.
rewrite fun_permut_fun_inv_loop; [ | easy | flia ].
apply Permutation_elt.
rewrite app_nil_r.
rewrite <- map_app.
destruct (permut_fun_without_last Hp Hi) as (g & Hpg & Hg).
rewrite Hg.
now apply IHn.
Qed.

Theorem rngl_product_change_list :
  rngl_is_comm = true →
  ∀ A (la lb : list A) f,
  Permutation la lb
  → (∏ (i ∈ la), f i = ∏ (i ∈ lb), f i)%F.
Proof.
intros Hic * P.
induction P; [ easy | | | ]. {
  rewrite rngl_product_list_cons; [ | easy ].
  rewrite rngl_product_list_cons; [ | easy ].
  now rewrite IHP.
} {
  do 4 (rewrite rngl_product_list_cons; [ | easy ]).
  do 2 rewrite rngl_mul_assoc.
  f_equal.
  now apply rngl_mul_comm.
} {
  etransitivity; [ apply IHP1 | apply IHP2 ].
}
Qed.

Theorem rngl_product_product_div_eq_1 :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  rngl_has_dec_eq = true →
  ∀ n f g,
  (∀ i j, i < n → j < n → g i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), (f i j / g i j)))%F = 1%F
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), f i j))%F =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), g i j))%F.
Proof.
intros Hom Hic Hid Hin H10 Hde * Hg Hs.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
remember (∏ (i ∈ _), _)%F as a eqn:Ha in |-*.
remember (∏ (i ∈ _), _)%F as b eqn:Hb in |-*.
destruct (rngl_eq_dec Hde b 0%F) as [Hbz| Hbz]. {
  rewrite Hbz in Hb |-*; clear Hbz; subst a; symmetry in Hb.
  apply rngl_product_list_integral in Hb; [ | easy | easy | easy ].
  destruct Hb as (i & His & Hb).
  apply rngl_product_list_integral in Hb; [ | easy | easy | easy ].
  destruct Hb as (j & Hjs & Hb).
  move j before i.
  exfalso; revert Hb.
  apply in_seq in His.
  apply in_seq in Hjs.
  now apply Hg.
}
apply rngl_mul_cancel_r with (c := (b⁻¹)%F); [ now left | | ]. {
  intros Hbiz.
  apply (f_equal (rngl_mul b)) in Hbiz.
  rewrite fold_rngl_div in Hbiz; [ | easy ].
  rewrite rngl_mul_inv_r in Hbiz; [ | now left | easy ].
  rewrite rngl_mul_0_r in Hbiz; [ | easy ].
  now apply rngl_1_neq_0 in Hbiz.
}
remember (_ * _)%F as c.
rewrite fold_rngl_div; [ | easy ].
rewrite rngl_mul_inv_r; [ | now left | easy ].
subst c b.
rewrite rngl_inv_product_list; [ | easy | easy | easy | easy | ]. 2: {
  intros i Hi H1.
  apply rngl_product_list_integral in H1; [ | easy | easy | easy ].
  destruct H1 as (j & Hjs & Hijz).
  exfalso.
  revert Hijz.
  apply in_seq in Hi.
  apply in_seq in Hjs.
  now apply Hg.
}
subst a.
erewrite rngl_product_list_permut with (l1 := rev _); [ | easy | ]. 2: {
  symmetry; apply Permutation_rev.
}
rewrite <- rngl_product_list_mul_distr; [ | easy ].
erewrite rngl_product_list_eq_compat. 2 :{
  intros i Hi.
  rewrite rngl_inv_product_list; [ | easy | easy | easy | easy | ]. 2: {
    intros j Hj.
    apply in_seq in Hi.
    apply in_seq in Hj.
    now apply Hg.
  }
  erewrite rngl_product_list_permut with (l1 := rev _); [ | easy | ]. 2: {
    symmetry; apply Permutation_rev.
  }
  rewrite <- rngl_product_list_mul_distr; [ | easy ].
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    rewrite fold_rngl_div; [ | easy ].
    easy.
  }
  easy.
}
easy.
Qed.

Theorem rngl_product_product_by_swap :
  rngl_is_comm = true →
  ∀ n f,
  (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n), f i j)%F =
  ((∏ (i ∈ seq 0 n), f i i) *
   (∏ (i ∈ seq 0 (n - 1)), ∏ (j = i + 1, n - 1), (f i j * f j i)))%F.
Proof.
intros Hic *.
induction n. {
  unfold iter_seq, iter_list; cbn.
  now rewrite rngl_mul_1_l.
}
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; unfold iter_list; cbn.
  now rewrite rngl_mul_1_l, rngl_mul_1_r.
}
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n; unfold iter_seq, iter_list; cbn.
  do 5 rewrite rngl_mul_1_l.
  repeat rewrite <- rngl_mul_assoc.
  f_equal; symmetry.
  rewrite rngl_mul_comm; [ | easy ].
  now rewrite rngl_mul_assoc.
}
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite seq_S.
  rewrite iter_list_app.
  unfold iter_list at 1; cbn.
  easy.
}
cbn - [ seq ].
rewrite Nat.sub_0_r.
rewrite rngl_product_list_mul_distr; [ | easy ].
rewrite seq_S.
rewrite iter_list_app.
unfold iter_list at 1; cbn.
rewrite IHn.
rewrite iter_list_app; cbn.
rewrite iter_list_app; cbn.
unfold iter_list at 4 6; cbn.
do 3 rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_mul_comm Hic (f n n)).
do 2 rewrite rngl_mul_assoc.
f_equal.
symmetry.
rewrite rngl_product_seq_product; [ | easy ].
cbn - [ seq ].
rewrite rngl_product_split_last; [ | flia Hnz ].
rewrite rngl_product_shift; [ | flia Hnz Hn1 ].
rewrite Nat.sub_add; [ | flia Hnz ].
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz Hn1 ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1), Nat.add_sub.
  rewrite Nat.add_1_r.
  rewrite Nat.sub_succ.
  apply in_seq in Hi.
  replace (n - i) with (S (n - i - 1)) by flia Hnz Hn1 Hi.
  rewrite seq_S.
  replace (S i + (n - i - 1)) with n by flia Hnz Hn1 Hi.
  unfold iter_list.
  rewrite fold_left_app.
  cbn - [ seq ].
  rewrite fold_iter_list.
  easy.
}
cbn - [ seq "-" ].
symmetry.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite Nat.add_1_r.
  rewrite Nat.sub_succ.
  now rewrite Nat_sub_sub_swap.
}
cbn - [ seq "-" ].
rewrite rngl_product_list_mul_distr; [ | easy ].
do 2 rewrite <- rngl_mul_assoc.
f_equal.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.sub_diag.
unfold iter_list at 4; cbn.
rewrite rngl_mul_1_l.
rewrite rngl_product_seq_product; [ | easy ].
cbn - [ seq ].
rewrite rngl_product_split_last; [ | flia Hnz ].
rewrite rngl_product_shift; [ | flia Hnz Hn1 ].
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz Hn1 ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1), Nat.add_sub.
  easy.
}
rewrite rngl_product_list_mul_distr; [ | easy ].
symmetry.
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
do 3 rewrite <- rngl_mul_assoc.
f_equal.
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
f_equal.
symmetry.
rewrite rngl_product_seq_product; [ | easy ].
cbn - [ seq ].
rewrite rngl_product_split_last; [ | flia Hnz ].
rewrite rngl_product_shift; [ | flia Hnz Hn1 ].
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz Hn1 ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1), Nat.add_sub.
  easy.
}
easy.
Qed.

Theorem permut_swap_mul_cancel : ∀ n σ f,
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  is_permut_fun σ n
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → ∀ i j, i < n → j < n →
    (((if σ i <? σ j then f i j else 1) / (if i <? j then f i j else 1)) *
     ((if σ j <? σ i then f j i else 1) / (if j <? i then f j i else 1)))%F =
    1%F.
Proof.
intros * Hic Hin H10 Hp Hfij Hfijnz * Hlin Hljn.
do 4 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ i) (σ j)) as [H1| H1]. {
  destruct (lt_dec (σ j) (σ i)) as [H| H]; [ flia H1 H | clear H ].
  destruct (lt_dec i j) as [H3| H3]. {
    destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
    rewrite Hfij.
    rewrite rngl_mul_inv_r; [ | now left | ]. 2: {
      apply Hfijnz; [ easy | easy | flia H3 ].
    }
    rewrite rngl_mul_1_l.
    apply rngl_mul_inv_r; [ now left | now apply rngl_1_neq_0 ].
  }
  destruct (lt_dec j i) as [H4| H4]. {
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | now left | easy ].
    rewrite rngl_div_1_l; [ | easy ].
    rewrite fold_rngl_div; [ | easy ].
    apply rngl_mul_inv_r; [ now left | ].
    apply Hfijnz; [ easy | easy | flia H4 ].
  }
  exfalso.
  apply Nat.nlt_ge in H3.
  apply Nat.nlt_ge in H4.
  apply Nat.le_antisymm in H3; [ | easy ].
  subst j; flia H1.
}
destruct (lt_dec (σ j) (σ i)) as [H2| H2]. {
  destruct (lt_dec i j) as [H3| H3]. {
    destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | now left | easy ].
    rewrite rngl_div_1_l; [ | easy ].
    rewrite rngl_mul_comm; [ | easy ].
    rewrite fold_rngl_div; [ | easy ].
    apply rngl_mul_inv_r; [ now left | ].
    apply Hfijnz; [ easy | easy | flia H3 ].
  }
  destruct (lt_dec j i) as [H4| H4]. {
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | now left | easy ].
    rewrite rngl_mul_1_l.
    apply rngl_mul_inv_r; [ now left | ].
    apply Hfijnz; [ easy | easy | flia H4 ].
  }
  exfalso.
  apply Nat.nlt_ge in H3.
  apply Nat.nlt_ge in H4.
  apply Nat.le_antisymm in H3; [ | easy ].
  subst j; flia H2.
}
apply Nat.nlt_ge in H1.
apply Nat.nlt_ge in H2.
apply Nat.le_antisymm in H1; [ | easy ].
destruct (lt_dec i j) as [H3| H3]. {
  destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
  apply Hp in H1; [ flia H1 H3 | easy | easy ].
}
destruct (lt_dec j i) as [H4| H4]. {
  apply Hp in H1; [ flia H1 H4 | easy | easy ].
}
rewrite rngl_div_1_r; [ | now left | easy ].
apply rngl_mul_1_l.
Qed.

Theorem product_product_if_permut_div :
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_has_inv = true →
  ∀ n σ f,
  is_permut_fun σ n
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n),
      ((if σ i <? σ j then f i j else 1) / (if i <? j then f i j else 1)))%F =
     1%F.
Proof.
intros Hic H10 Hin * Hp Hfij Hfijnz.
rewrite rngl_product_product_by_swap; [ | easy ].
rewrite all_1_rngl_product_list_1; [ | easy | ]. 2: {
  intros i Hi.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec _ _) as [H| H]; [ flia H | clear H ].
  destruct (lt_dec _ _) as [H| H]; [ flia H | clear H ].
  apply rngl_div_1_r; [ now left | easy ].
}
rewrite rngl_mul_1_l.
apply all_1_rngl_product_list_1; [ easy | ].
intros i Hi.
apply all_1_rngl_product_list_1; [ easy | ].
intros j Hj.
apply in_seq in Hi.
apply in_seq in Hj.
apply (@permut_swap_mul_cancel n); try easy; [ flia Hi | flia Hj ].
Qed.

Theorem product_product_if_permut :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  rngl_has_dec_eq = true →
  ∀ n σ f,
  is_permut_fun σ n
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), if σ i <? σ j then f i j else 1))%F =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), if i <? j then f i j else 1))%F.
Proof.
intros Hom Hic Hid Hin H10 Hed * Hp Hfij Hfijnz.
apply rngl_product_product_div_eq_1; try easy. {
  intros i j Hi Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | now apply rngl_1_neq_0 ].
  apply Hfijnz; [ easy | easy | flia Hij ].
}
now apply product_product_if_permut_div.
Qed.

Theorem ε_ws_ε_fun :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ σ n,
  is_permut_fun σ n
  → ε_fun σ n = ε_fun_ws σ n.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hp.
unfold ε_fun, ε_fun_ws, δ.
rewrite rngl_product_product_if.
rewrite rngl_product_product_if.
rewrite rngl_product_product_if.
rewrite <- rngl_product_div_distr; try easy; [ | now left | ]. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_of_nat_sub; [ | now left | flia Hj ].
    easy.
  }
  cbn.
  destruct (Nat.eq_dec i n) as [Hein| Hein]. {
    subst i.
    rewrite rngl_product_empty; [ now apply rngl_1_neq_0 | flia ].
  }
  rewrite rngl_product_shift; [ | flia Hi Hein ].
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    replace (i + 1 + j - i) with (S j) by flia.
    easy.
  }
  cbn - [ rngl_of_nat ].
  erewrite <- rngl_product_succ_succ.
  replace (S (n - (i + 1))) with (n - i) by flia Hi Hein.
  rewrite rngl_product_rngl_of_nat; [ | now left ].
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  now apply fact_neq_0 in H.
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite <- rngl_product_div_distr; try easy; [ now left | ].
  intros j Hj.
  intros H.
  apply rngl_sub_move_0_r in H; [ | easy ].
  apply rngl_of_nat_inj in H; [ | now left | easy ].
  flia Hj H.
}
cbn.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_sub_is_mul_sign_abs; [ | easy ].
    rewrite rngl_sub_is_mul_sign_abs; [ | easy ].
    replace (sign_diff j i) with 1%F. 2: {
      unfold sign_diff.
      rewrite if_ltb_lt_dec.
      destruct (lt_dec i j) as [H| H]; [ easy | flia Hj H ].
    }
    rewrite rngl_mul_1_l.
    replace (rngl_of_nat (abs_diff j i)) with (rngl_of_nat (j - i)). 2: {
      unfold abs_diff.
      rewrite if_ltb_lt_dec.
      destruct (lt_dec i j) as [H| H]; [ easy | flia Hj H ].
    }
    easy.
  }
  easy.
}
cbn.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    unfold rngl_div.
    rewrite Hin.
    rewrite <- rngl_mul_assoc.
    easy.
  }
  cbn.
  rewrite rngl_product_mul_distr; [ | easy ].
  easy.
}
cbn.
rewrite rngl_product_mul_distr; [ | easy ].
rewrite <- rngl_mul_1_r; f_equal.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite fold_rngl_div; [ | easy ].
    easy.
  }
  cbn.
  rewrite rngl_product_div_distr; try easy; [ now left | ].
  intros j Hj.
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
cbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  rewrite rngl_product_empty; [ easy | flia ].
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  replace n with (S (n - 1)) at 1 2 by flia Hnz.
  rewrite Nat.add_1_r at 1 2.
  rewrite rngl_product_succ_succ.
  rewrite rngl_product_succ_succ.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat_sub_succ_1.
  }
  cbn - [ "-" ].
  easy.
}
cbn - [ "-" ].
erewrite rngl_product_shift; [ | flia Hnz ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1).
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite Nat.add_sub.
    easy.
  }
  remember (iter_seq _ _ _ _) as x.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat.add_1_r, Nat.sub_succ.
  }
  subst x.
  easy.
}
cbn.
rewrite rngl_product_div_distr; try easy; [ | now left | ]. 2: {
  intros i Hi H.
  apply (rngl_product_integral (or_introl Hop) Hit H10) in H.
  destruct H as (j & Hj & Hji).
  apply eq_rngl_of_nat_0 in Hji; [ | easy ].
  flia Hj Hji.
}
apply eq_rngl_div_1; [ now left | | ]. {
  intros H.
  apply (rngl_product_integral (or_introl Hop) Hit H10) in H.
  destruct H as (i & Hi & H).
  apply (rngl_product_integral (or_introl Hop) Hit H10) in H.
  destruct H as (j & Hj & H).
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
rewrite <- rngl_product_product_if; symmetry.
rewrite <- rngl_product_product_if; symmetry.
(* changt de var *)
rewrite rngl_product_change_var with (g := permut_fun_inv_loop σ n) (h := σ). 2: {
  intros i Hi.
  destruct Hp as (Hp1, Hp2).
  rewrite fun_find_prop; [ easy | easy | flia Hi Hnz ].
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_var with (g := permut_fun_inv_loop σ n) (h := σ). 2: {
    intros j Hj.
    destruct Hp as (Hp1, Hp2).
    rewrite fun_find_prop; [ easy | easy | flia Hj Hnz ].
  }
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    apply in_map_iff in Hj.
    destruct Hj as (k & Hk & Hsk).
    apply in_seq in Hsk.
    rewrite fun_permut_fun_inv_loop; [ | easy | ]. 2: {
      destruct Hp as (Hp1, Hp2).
      rewrite <- Hk.
      apply Hp1.
      flia Hsk Hi Hnz.
    }
    apply in_map_iff in Hi.
    destruct Hi as (l & Hl & Hsl).
    apply in_seq in Hsl.
    rewrite fun_permut_fun_inv_loop; [ | easy | ]. 2: {
      destruct Hp as (Hp1, Hp2).
      rewrite <- Hl.
      apply Hp1.
      easy.
    }
    easy.
  }
  cbn - [ "-" "<?" ].
  easy.
}
cbn - [ "-" "<?" ].
rewrite Nat.sub_0_r.
rewrite rngl_product_list_permut with (l2 := seq 0 n); [ | easy | ]. 2: {
  now apply permut_fun_Permutation.
}
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_list with (lb := seq 0 n); [ | easy | ]. 2: {
    now apply permut_fun_Permutation.
  }
  easy.
}
cbn - [ "<?" ].
rewrite product_product_if_permut; try easy; cycle 1. {
  now left.
} {
  now apply permut_fun_inv_loop_is_permut.
} {
  intros.
  unfold abs_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]. {
    destruct (lt_dec j i) as [Hji| Hji]; [ flia Hij Hji | easy ].
  } {
    destruct (lt_dec j i) as [Hji| Hji]; [ easy | ].
    now replace i with j by flia Hij Hji.
  }
} {
  intros * Hi Hj Hij H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  unfold abs_diff in H.
  rewrite if_ltb_lt_dec in H.
  destruct (lt_dec i j) as [Hlij| Hlij]; flia Hij Hlij H.
}
rewrite rngl_product_seq_product; [ | easy ].
rewrite Nat.add_0_l.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_seq_product; [ | easy ].
  rewrite Nat.add_0_l.
  easy.
}
cbn - [ "<?" ].
unfold abs_diff.
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
do 3 rewrite if_ltb_lt_dec.
now destruct (lt_dec i j).
Qed.

Theorem ε_ws_ε :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n (p : vector nat),
  is_permut_vect n p
  → ε n p = ε_ws n p.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hp.
apply ε_ws_ε_fun; try easy.
now destruct Hp as (Hp1, Hp2).
Qed.

Definition permut_fun_swap (p q : nat) (σ : nat → nat) :=
  λ i, σ (transposition p q i).

(*
Definition permut_swap {n} (p q : nat) (σ : vector nat) :=
  mk_vect n (permut_fun_swap p q (vect_el σ)).
*)

Theorem permut_swap_fun_is_permut : ∀ p q σ n,
  p < n
  → q < n
  → is_permut_fun σ n
  → is_permut_fun (permut_fun_swap p q σ) n.
Proof.
intros * Hp Hq Hσ.
unfold permut_fun_swap.
split. {
  intros i Hi.
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i p) as [Hip| Hip]; [ now apply Hσ | ].
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]; [ now apply Hσ | ].
  now apply Hσ.
} {
  intros i j Hi Hj Hs.
  unfold transposition in Hs.
  do 4 rewrite if_eqb_eq_dec in Hs.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
      apply Hσ in Hs; [ congruence | easy | easy ].
    } {
      apply Hσ in Hs; [ congruence | easy | easy ].
    }
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
      apply Hσ in Hs; [ congruence | easy | easy ].
    }
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
      apply Hσ in Hs; [ congruence | easy | easy ].
    }
    apply Hσ in Hs; [ congruence | easy | easy ].
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
    apply Hσ in Hs; [ congruence | easy | easy ].
  }
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
    apply Hσ in Hs; [ congruence | easy | easy ].
  }
  apply Hσ in Hs; [ congruence | easy | easy ].
}
Qed.

Theorem transposition_is_permut : ∀ p q n,
  p < n → q < n → is_permut_fun (transposition p q) n.
Proof.
intros * Hp Hq.
split. {
  intros i Hi.
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i p) as [Hip| Hip]; [ easy | ].
  now destruct (Nat.eq_dec i q).
} {
  intros i j Hi Hj Hs.
  unfold transposition in Hs.
  do 4 rewrite if_eqb_eq_dec in Hs.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; congruence.
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; congruence.
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ easy | ].
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ easy | ].
  easy.
}
Qed.

(*
Theorem transposition_is_permut_vect : ∀ n p q,
  p < n
  → q < n
  → is_permut_vect (mk_vect (transposition p q)).
Proof.
intros.
now apply transposition_is_permut.
Qed.
*)

Theorem is_permut_map : ∀ f n,
  is_permut_fun f n
  → is_permut_fun (λ i, nth i (map f (seq 0 n)) 0) n.
Proof.
intros * Hf.
destruct Hf as (Hf, Hff).
split. {
  intros i Hi.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  now apply Hf.
} {
  intros i j Hi Hj Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  now apply Hff.
}
Qed.

Theorem transposition_signature_lt :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n p q,
  p < q
  → q < n
  → ε n (mk_vect (map (transposition p q) (seq 0 n))) = (-1)%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hpq Hq.
rewrite ε_ws_ε; try easy. 2: {
  split; cbn; [ now rewrite map_length, seq_length | ].
  unfold vect_el; cbn.
  apply is_permut_map.
  apply transposition_is_permut; [ | easy ].
  now transitivity q.
}
unfold ε_ws; cbn.
unfold ε_fun_ws.
cbn - [ "<?" ].
unfold sign_diff.
rewrite rngl_product_shift; [ | flia Hq ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hq ].
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite (Nat.add_comm 1 j), Nat.add_sub.
    rewrite (Nat.add_comm 1 i), Nat.add_sub.
    rewrite Nat_ltb_mono_r.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi Hq ].
    rewrite seq_nth; [ | flia Hi Hq ].
    rewrite Nat.add_0_l.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj Hq ].
    rewrite seq_nth; [ | flia Hj Hq ].
    rewrite Nat.add_0_l.
    easy.
  }
  easy.
}
cbn - [ "<?" ].
rewrite (rngl_product_split3 p); [ | flia Hpq Hq ].
cbn - [ "<?" ].
assert (Hp : p < n) by now transitivity q.
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  apply all_1_rngl_product_1.
  intros j Hj.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) j) as [Hij| Hij]; [ | easy ].
  destruct (lt_dec (transposition p q (i - 1)) (transposition p q j))
    as [Htij| Htij]; [ easy | ].
  exfalso; apply Htij; clear Htij.
  rewrite transposition_out; [ | flia Hi | flia Hpq Hi ].
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ flia Hpq Hi | ].
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ flia Hpq Hi | easy ].
}
rewrite rngl_mul_1_l.
rewrite transposition_1.
rewrite (rngl_product_split3 p); [ | flia Hpq Hq ].
rewrite if_ltb_lt_dec.
destruct (lt_dec p p) as [H| H]; [ flia H | clear H ].
rewrite rngl_mul_1_r.
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec p (i - 1)) as [H| H]; [ flia Hi H | easy ].
}
rewrite rngl_mul_1_l.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec p i) as [H| H]; [ clear H | flia Hi H ].
  easy.
}
cbn - [ "<?" ].
rewrite <- rngl_product_mul_distr; [ | easy ].
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite transposition_2.
rewrite if_ltb_lt_dec.
destruct (lt_dec q p) as [H| H]; [ flia Hpq H | clear H ].
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite if_ltb_lt_dec.
destruct (lt_dec q q) as [H| H]; [ flia H | clear H ].
rewrite rngl_mul_1_r.
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec q (i - 1)) as [H| H]; [ flia Hi H | easy ].
}
rewrite rngl_mul_1_l.
do 2 rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
rewrite rngl_mul_assoc.
rewrite <- rngl_product_mul_distr; [ | easy ].
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec q i) as [H| H]; [ clear H | flia Hi H ].
  rewrite rngl_mul_assoc.
  rewrite transposition_out; [ | flia Hpq Hi | flia Hi ].
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec p i) as [H| H]; [ clear H | flia Hpq Hi H ].
  rewrite rngl_mul_1_l.
  destruct (lt_dec q i) as [H| H]; [ clear H | flia Hi H ].
  rewrite rngl_mul_1_l.
  apply all_1_rngl_product_1.
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
  rewrite transposition_out; [ | flia Hpq Hi Hij | flia Hi Hij ].
  rewrite if_ltb_lt_dec.
  now destruct (lt_dec i j).
}
rewrite rngl_mul_1_l.
rewrite all_1_rngl_product_1; [ apply rngl_mul_1_l | ].
intros i Hi.
rewrite transposition_out; [ | flia Hi | flia Hi ].
rewrite if_ltb_lt_dec.
destruct (lt_dec q (i - 1)) as [H| H]; [ flia Hi H | clear H ].
rewrite (rngl_product_split3 p); [ | flia Hp ].
rewrite transposition_1.
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) p) as [H| H]; [ flia Hi H | clear H ].
rewrite rngl_mul_1_r.
rewrite all_1_rngl_product_1. 2: {
  intros j Hj.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) (j - 1)) as [H| H]; [ flia Hi Hj H | easy ].
}
rewrite rngl_mul_1_l.
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) q) as [H| H]; [ clear H | flia Hi H ].
rewrite transposition_2.
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) p) as [H| H]; [ flia Hi H | clear H ].
rewrite rngl_mul_mul_swap; [ | easy ].
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
rewrite rngl_sqr_opp_1; [ | easy ].
rewrite rngl_mul_1_r.
rewrite (all_1_rngl_product_1 (q + 1)). 2: {
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) j) as [H| H]; [ clear H | flia Hi Hj H ].
  rewrite transposition_out; [ | flia Hpq Hj | flia Hj ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) j) as [H| H]; [ easy | flia Hi Hj H ].
}
rewrite rngl_mul_1_r.
apply all_1_rngl_product_1.
intros j Hj.
rewrite transposition_out; [ | flia Hj | flia Hj ].
do 2 rewrite if_ltb_lt_dec.
now destruct (lt_dec (i - 1) (j - 1)).
Qed.

Theorem transposition_signature :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n p q,
  p ≠ q
  → p < n
  → q < n
  → ε n (mk_vect (map (transposition p q) (seq 0 n))) = (-1)%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hpq Hp Hq.
destruct (lt_dec p q) as [Hpq'| Hpq']. {
  now apply transposition_signature_lt.
}
apply Nat.nlt_ge in Hpq'.
assert (H : q < p) by flia Hpq Hpq'.
rewrite <- transposition_signature_lt with (p := q) (q := p) (n := n); try easy.
f_equal; f_equal.
apply map_ext_in.
intros i Hi.
apply transposition_comm.
Qed.

(* ε (σ₁ ° σ₂) = ε σ₁ * ε σ₂ *)

Theorem signature_comp_fun_expand_1 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_fun g n
  → (∏ (i = 1, n),
        (∏ (j = 1, n), δ i j (f (g (i - 1)%nat)) (f (g (j - 1)%nat))) /
      ∏ (i = 1, n), (∏ (j = 1, n), δ i j (g (i - 1)%nat) (g (j - 1)%nat)))%F =
    (∏ (i = 1, n), (∏ (j = 1, n), δ i j (f (i - 1)%nat) (f (j - 1)%nat)) /
      ∏ (i = 1, n), (∏ (j = 1, n), δ i j i j))%F
  → ε_fun (comp f g) n = (ε_fun f n * ε_fun g n)%F.
Proof.
intros Hop Hin H10 Hit Hch * Hp2 Hs.
unfold ε_fun, comp; cbn.
rewrite <- Hs; symmetry.
apply rngl_div_mul_div; [ easy | ].
intros Hij.
apply rngl_product_integral in Hij; [ | now left | easy | easy ].
destruct Hij as (i & Hi & Hij).
apply rngl_product_integral in Hij; [ | now left | easy | easy ].
destruct Hij as (j & Hj & Hij).
unfold δ in Hij.
rewrite if_ltb_lt_dec in Hij.
destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 ].
apply rngl_sub_move_0_r in Hij; [ | easy ].
apply rngl_of_nat_inj in Hij; [ | now left | easy ].
destruct Hp2 as (Hp21, Hp22).
apply Hp22 in Hij; [ flia Hi Hj Hlij Hij | flia Hj | flia Hi ].
Qed.

Theorem signature_comp_fun_expand_2_1 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_fun g n
  → (∏ (i = 1, n),
      (∏ (j = 1, n), δ i j (f (g (i - 1)%nat)) (f (g (j - 1)%nat))) /
     ∏ (i = 1, n), (∏ (j = 1, n), δ i j (g (i - 1)%nat) (g (j - 1)%nat)))%F =
    (∏ (i = 1, n),
      (∏ (j = 1, n),
       (if i <? j then
         (rngl_of_nat (f (g (j - 1)%nat)) - rngl_of_nat (f (g (i - 1)%nat))) /
         (rngl_of_nat (g (j - 1)%nat) - rngl_of_nat (g (i - 1)%nat))
       else 1)))%F.
Proof.
intros Hop Hin Hic H10 Hit Hch * Hp2.
unfold rngl_div; rewrite Hin.
rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
  intros i Hi Hij.
  apply rngl_product_integral in Hij; [ | now left | easy | easy ].
  destruct Hij as (j & Hj & Hij).
  unfold δ in Hij.
  rewrite if_ltb_lt_dec in Hij.
  destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
  apply rngl_sub_move_0_r in Hij; [ | easy ].
  apply rngl_of_nat_inj in Hij; [ | now left | easy ].
  apply Hp2 in Hij; [ flia Hi Hj Hlij Hij | flia Hj | flia Hi ].
}
erewrite <- rngl_product_mul_distr; [ | easy ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
    intros j Hj Hij.
    unfold δ in Hij.
    rewrite if_ltb_lt_dec in Hij.
    destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
    apply rngl_sub_move_0_r in Hij; [ | easy ].
    apply rngl_of_nat_inj in Hij; [ | now left | easy ].
    apply Hp2 in Hij; [ flia Hi Hj Hlij Hij | flia Hj | flia Hi ].
  }
  erewrite <- rngl_product_mul_distr; [ | easy ].
  easy.
}
cbn - [ "<?" ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    move j before i.
    unfold δ.
    rewrite rngl_inv_if_then_else_distr.
    rewrite rngl_mul_if_then_else_distr.
    rewrite fold_rngl_div; [ | easy ].
    rewrite rngl_inv_1; [ | easy | easy ].
    rewrite rngl_mul_1_l.
    easy.
  }
  easy.
}
cbn - [ "<?" ].
unfold rngl_div; rewrite Hin.
easy.
Qed.

Theorem signature_comp_fun_expand_2_2 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f,
  (∏ (i = 1, n), (∏ (j = 1, n), δ i j (f (i - 1)%nat) (f (j - 1)%nat)) /
   ∏ (i = 1, n), (∏ (j = 1, n), δ i j i j))%F =
  (∏ (i = 1, n),
   (∏ (j = 1, n),
    (if i <? j then
      (rngl_of_nat (f (j - 1)%nat) - rngl_of_nat (f (i - 1)%nat)) /
      rngl_of_nat (j - i)
     else 1)))%F.
Proof.
intros Hop Hin Hic H10 Hit Hch *.
unfold rngl_div; rewrite Hin.
rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
  intros i Hi Hij.
  apply rngl_product_integral in Hij; [ | now left | easy | easy ].
  destruct Hij as (j & Hj & Hij).
  unfold δ in Hij.
  rewrite if_ltb_lt_dec in Hij.
  destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
  apply rngl_sub_move_0_r in Hij; [ | easy ].
  apply rngl_of_nat_inj in Hij; [ | now left | easy ].
  flia Hlij Hij.
}
erewrite <- rngl_product_mul_distr; [ | easy ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
    intros j Hj Hij.
    unfold δ in Hij.
    rewrite if_ltb_lt_dec in Hij.
    destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
    apply rngl_sub_move_0_r in Hij; [ | easy ].
    apply rngl_of_nat_inj in Hij; [ | now left | easy ].
    flia Hlij Hij.
  }
  erewrite <- rngl_product_mul_distr; [ | easy ].
  easy.
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    move j before i.
    unfold δ.
    rewrite rngl_inv_if_then_else_distr.
    rewrite rngl_mul_if_then_else_distr.
    rewrite fold_rngl_div; [ | easy ].
    rewrite rngl_inv_1; [ | easy | easy ].
    rewrite rngl_mul_1_l.
    easy.
  }
  easy.
}
unfold rngl_div; rewrite Hin.
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
f_equal; f_equal.
apply rngl_of_nat_sub; [ now left | easy ].
Qed.

Theorem signature_comp_fun_changement_of_variable :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_fun f n
  → is_permut_fun g n
  → (∏ (i = 1, n),
     (∏ (j = 1, n),
      (if i <? j then
         (rngl_of_nat (f (g (j - 1)%nat)) - rngl_of_nat (f (g (i - 1)%nat))) /
         (rngl_of_nat (g (j - 1)%nat) - rngl_of_nat (g (i - 1)%nat))
       else 1)))%F =
    (∏ (i = 1, n),
     (∏ (j = 1, n),
      (if i <? j then
         (rngl_of_nat (f (j - 1)%nat) - rngl_of_nat (f (i - 1)%nat)) /
         rngl_of_nat (j - i)
       else 1)))%F.
Proof.
intros Hop Hin Hic Hde H10 Hit Hch * Hp1 Hp2.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
rewrite rngl_product_shift; [ | flia Hnz ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    now rewrite (Nat.add_comm 1), Nat.add_sub.
  }
  easy.
}
cbn - [ "<?" ].
rewrite rngl_product_change_var with (g := permut_fun_inv_loop g n) (h := g). 2: {
  intros i Hi.
  rewrite fun_find_prop; [ easy | apply Hp2 | flia Hi Hnz ].
}
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1, Nat.sub_0_r.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hnz ].
  rewrite rngl_product_change_var with
      (g := permut_fun_inv_loop g n) (h := g). 2: {
    intros j Hj.
    rewrite fun_find_prop; [ easy | apply Hp2 | flia Hj Hnz ].
  }
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1, Nat.sub_0_r.
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    rewrite (Nat.add_comm _ 1).
    rewrite Nat_ltb_mono_l.
    rewrite fun_permut_fun_inv_loop; [ | apply Hp2 | ]. 2: {
      apply in_map_iff in Hi.
      destruct Hi as (k & Hk & Hkn).
      apply in_seq in Hkn.
      rewrite <- Hk.
      now apply Hp2.
    }
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite fun_permut_fun_inv_loop; [ | apply Hp2 | ]. 2: {
      apply in_map_iff in Hj.
      destruct Hj as (k & Hk & Hkn).
      apply in_seq in Hkn.
      rewrite <- Hk.
      now apply Hp2.
    }
    easy.
  }
  easy.
}
cbn - [ "<?" ].
erewrite rngl_product_list_eq_compat. 2: {
  intros j Hj.
  erewrite rngl_product_change_list; [ | easy | ]. 2: {
    now apply permut_fun_Permutation.
  }
  easy.
}
cbn - [ "<?" ].
erewrite rngl_product_change_list; [ | easy | ]. 2: {
  now apply permut_fun_Permutation.
}
symmetry.
rewrite rngl_product_shift; [ | flia Hnz ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite Nat_ltb_mono_l.
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite Nat.add_comm, Nat.add_sub.
    do 2 rewrite Nat.add_1_r.
    cbn - [ "<?" ].
    easy.
  }
  easy.
}
unfold iter_seq.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1, Nat.sub_0_r.
symmetry.
rewrite product_product_if_permut; try easy. {
  apply rngl_product_list_eq_compat.
  intros i Hi.
  apply rngl_product_list_eq_compat.
  intros j Hj.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
  f_equal.
  apply rngl_of_nat_sub; [ now left | easy ].
} {
  now left.
} {
  now apply permut_fun_inv_loop_is_permut.
} {
  intros i j.
  destruct (Nat.eq_dec i j) as [Hij| Hij]; [ now subst j | ].
  rewrite <- rngl_opp_sub_distr; [ | easy ].
  unfold rngl_div.
  rewrite Hin.
  rewrite rngl_mul_opp_l; [ | easy ].
  rewrite <- rngl_mul_opp_r; [ | easy ].
  f_equal.
  rewrite rngl_opp_inv; [ | easy | easy | easy | ]. 2: {
    intros H.
    apply rngl_sub_move_0_r in H; [ | easy ].
    apply Hij; symmetry.
    apply rngl_of_nat_inj in H; [ easy | now left | easy ].
  }
  now rewrite rngl_opp_sub_distr.
} {
  intros * Hi Hj Hij.
  unfold rngl_div.
  rewrite Hin.
  intros H.
  apply rngl_integral in H; [ | now left | now rewrite Hit ].
  destruct H as [H| H]. {
    apply rngl_sub_move_0_r in H; [ | easy ].
    apply rngl_of_nat_inj in H; [ | now left | easy ].
    apply Hij; symmetry.
    now apply Hp1 in H.
  } {
    revert H.
    apply rngl_inv_neq_0; [ now left | easy | easy | ].
    intros H.
    apply rngl_sub_move_0_r in H; [ | easy ].
    apply rngl_of_nat_inj in H; [ | now left | easy ].
    now apply Hij; symmetry.
  }
}
Qed.

Theorem signature_comp_fun :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_fun f n
  → is_permut_fun g n
  → ε_fun (comp f g) n = (ε_fun f n * ε_fun g n)%F.
Proof.
intros Hop Hin Hic Hde H10 Hit Hch * Hp1 Hp2.
apply signature_comp_fun_expand_1; try easy.
rewrite signature_comp_fun_expand_2_1; try easy.
rewrite signature_comp_fun_expand_2_2; try easy.
now apply signature_comp_fun_changement_of_variable.
Qed.

Theorem signature_comp :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n (σ₁ σ₂ : vector nat),
  is_permut_vect n σ₁
  → is_permut_vect n σ₂
  → ε n (σ₁ ° σ₂) = (ε n σ₁ * ε n σ₂)%F.
Proof.
intros Hop Hin Hic Hde H10 Hit Hch * Hp1 Hp2.
unfold ε.
destruct Hp1 as (Hp1, Hp'1).
destruct Hp2 as (Hp2, Hp'2).
rewrite <- signature_comp_fun; try easy.
unfold comp, "°".
unfold ε_fun; f_equal.
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
cbn; unfold comp_list.
rewrite (List_map_nth' 0); [ | rewrite fold_vect_size; flia Hp2 Hi ].
rewrite (List_map_nth' 0); [ | rewrite fold_vect_size; flia Hp2 Hj ].
easy.
Qed.

Theorem transposition_involutive : ∀ p q i,
  transposition p q (transposition p q i) = i.
Proof.
intros.
unfold transposition.
do 4 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i p) as [Hip| Hip]. {
  destruct (Nat.eq_dec q p) as [Hqp| Hqp]; [ congruence | ].
  destruct (Nat.eq_dec q q) as [H| H]; [ congruence | easy ].
}
destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
  destruct (Nat.eq_dec p p) as [H| H]; [ congruence | easy ].
}
destruct (Nat.eq_dec i p) as [H| H]; [ easy | clear H ].
destruct (Nat.eq_dec i q) as [H| H]; [ easy | clear H ].
easy.
Qed.

Theorem transposition_injective : ∀ p q i j,
  transposition p q i = transposition p q j
  → i = j.
Proof.
intros * Hpq.
apply (f_equal (transposition p q)) in Hpq.
now do 2 rewrite transposition_involutive in Hpq.
Qed.

(*
Theorem swap_elem_involutive : ∀ f p q,
  swap_elem (swap_elem f p q) p q = f.
Proof.
intros.
Print fin_fun_ext.
Theorem my_false : ∀ A (f g : nat → A), f = g.
Proof.
intros.
apply fin_fun_ext with (n := 0).
easy.
Print fin_fun_ext.
...
apply fin_fun_ext with (n := n).
intros i Hi.
unfold swap_elem.
rewrite transposition_involutive.
...
apply vector_eq.
intros i Hi; cbn.
unfold swap_elem.
now rewrite transposition_involutive.
Qed.
*)

(*
Theorem vect_swap_elem_injective : ∀ (u v : vector nat) p q,
  vect_swap_elem u p q = vect_swap_elem v p q
  → u = v.
Proof.
intros * Huv.
apply (f_equal (λ u, vect_swap_elem u p q)) in Huv.
now do 2 rewrite vect_swap_elem_involutive in Huv.
Qed.
*)

(* i such that vect_el (permut n k) i = j *)

(*
Definition sym_gr_elem_swap_with_0 p n k :=
  vect_swap_elem (vect_el (canon_sym_gr n) k) 0 p.
*)

(* k' such that permut_swap_with_0 p n k = permut n k' *)

Definition sym_gr_elem_swap_last (p q : nat) n k :=
  vect_swap_elem 0
    (vect_swap_elem 0 (vect_vect_nat_el (canon_sym_gr n) k) p (n - 2))
    q (n - 1).

(* *)

Theorem ε_permut_succ : ∀ n k,
  k < fact (S n)
  → ε_permut (S n) k =
     (minus_one_pow (k / fact n) * ε_permut n (k mod fact n))%F.
Proof. easy. Qed.

Theorem sym_gr_succ_values : ∀ n k σ σ',
  σ = canon_sym_gr_fun n (canon_sym_gr_elem n) k
  → σ' = canon_sym_gr_elem n (k mod n!)
  → ∀ i,
    σ i =
    match i with
    | 0 => k / fact n
    | S i' => if σ' i' <? k / fact n then σ' i' else σ' i' + 1
    end.
Proof.
intros * Hσ Hσ' i.
destruct i; [ now subst σ | ].
subst σ; cbn - [ "<?" ].
subst σ'; cbn - [ "<?" ].
rewrite Nat.leb_antisym.
unfold Nat.b2n.
rewrite if_ltb_lt_dec.
rewrite negb_if.
rewrite if_ltb_lt_dec.
destruct (lt_dec _ _) as [H1| H1]; [ | easy ].
apply Nat.add_0_r.
Qed.

Theorem sym_gr_vect_succ_values : ∀ (n k : nat) (σ σ' : nat → nat),
  k < (S n)!
  → σ = vect_el 0 (vect_vect_nat_el (canon_sym_gr (S n)) k)
  → σ' = vect_el 0 (vect_vect_nat_el (canon_sym_gr n) (k mod n!))
  → ∀ i : nat, i < S n →
    σ i =
      match i with
      | 0 => k / n!
      | S i' => if σ' i' <? k / n! then σ' i' else σ' i' + 1
      end.
Proof.
intros * Hkn Hσ Hσ' i Hin.
unfold canon_sym_gr in Hσ.
cbn - [ map fact seq ] in Hσ.
rewrite (List_map_nth' 0) in Hσ; [ | now rewrite seq_length ].
rewrite seq_nth in Hσ; [ | easy ].
rewrite Nat.add_0_l in Hσ.
rewrite Hσ.
unfold vect_el.
cbn - [ "<?" nth seq ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite Nat.add_0_l.
destruct i; [ easy | ].
subst σ; cbn - [ "<?" ].
subst σ'; cbn - [ "<?" ].
rewrite Nat.leb_antisym.
unfold Nat.b2n.
rewrite if_ltb_lt_dec.
rewrite negb_if.
rewrite if_ltb_lt_dec.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  apply Nat.mod_upper_bound, fact_neq_0.
}
cbn - [ fact map seq "<?" ].
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hin ].
rewrite seq_nth; [ | apply Nat.mod_upper_bound, fact_neq_0 ].
rewrite seq_nth; [ | flia Hin ].
do 2 rewrite Nat.add_0_l.
destruct (lt_dec _ _); [ apply Nat.add_0_r | easy ].
Qed.

(* equality of ε of sym_gr elem and ε_permut *)

Theorem ε_of_sym_gr_permut_succ :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n k,
  k < (S n)!
  → ε (S n) (vect_vect_nat_el (canon_sym_gr (S n)) k) =
    (minus_one_pow (k / n!) *
     ε n (vect_vect_nat_el (canon_sym_gr n) (k mod n!)))%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hkn.
rewrite ε_ws_ε; try easy; [ | now apply mk_canon_is_permut_vect ].
unfold ε_ws, ε_fun_ws.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold ε, ε_fun.
  subst n.
  apply Nat.lt_1_r in Hkn.
  subst k; cbn.
  unfold iter_seq, iter_list; cbn.
  repeat rewrite rngl_mul_1_l.
  rewrite rngl_div_1_l; [ | easy ].
  now symmetry; apply rngl_inv_1.
}
rewrite rngl_product_succ_succ.
rewrite rngl_product_split_first; [ | flia ].
rewrite Nat.sub_diag.
f_equal. {
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    replace (1 <? 1 + i) with (0 <? i) by easy.
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  cbn - [ "<?" canon_sym_gr ].
  rewrite rngl_product_split_first; [ | flia ].
  replace (0 <? 0) with false by easy.
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec 0 i) as [H| H]; [ clear H | flia Hi H ].
    easy.
  }
  cbn - [ canon_sym_gr ].
  remember (vect_el 0 (vect_vect_nat_el (canon_sym_gr (S n)) k))
    as σ eqn:Hσ.
  remember
    (vect_el 0 (vect_vect_nat_el (canon_sym_gr n) (k mod n!)))
    as σ' eqn:Hσ'.
  specialize (sym_gr_vect_succ_values Hkn Hσ Hσ') as H1.
  unfold sign_diff.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite H1; [ | flia ].
    easy.
  }
  cbn - [ "<?" ].
  rewrite rngl_product_shift; [ | flia Hnz ].
  remember (k / fact n) as x eqn:Hx.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? _ then _ else _) with
      (if x <? σ' i + 1 then 1%F else (-1)%F). 2: {
      rewrite (Nat.add_1_l i).
      rewrite H1; [ | flia Hi Hnz ].
      do 3 rewrite if_ltb_lt_dec.
      destruct (lt_dec (σ' i) x) as [H2| H2]; [ | easy ].
      destruct (lt_dec x (σ' i)) as [H| H]; [ flia H H2 | clear H ].
      destruct (lt_dec x (σ' i + 1)) as [H3| H3]; [ | easy ].
      flia H2 H3.
    }
    easy.
  }
  cbn - [ "<?" ].
  assert (Hp' : is_permut_fun σ' n). {
    rewrite Hσ'.
    apply mk_canon_is_permut_vect.
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  assert (Hp : is_permut_fun σ (S n)). {
    rewrite Hσ.
    now apply mk_canon_is_permut_vect.
  }
  rewrite rngl_product_change_var with (g := permut_fun_inv_loop σ' n) (h := σ').
  2: {
    intros i (_, Hi).
    apply fun_find_prop; [ | flia Hnz Hi ].
    apply Hp'.
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_list_eq_compat. 2: {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite fun_permut_fun_inv_loop; [ easy | easy | ].
    now rewrite <- Hji; apply Hp'.
  }
  cbn - [ "<?" seq ].
  rewrite rngl_product_change_list with (lb := seq 0 n); [ | easy | ]. 2: {
    now apply permut_fun_Permutation.
  }
  rewrite rngl_product_seq_product; [ | easy ].
  rewrite Nat.add_0_l.
  destruct (Nat.eq_dec x 0) as [Hxz| Hxz]. {
    move Hxz at top; subst x.
    cbn - [ "<?" ].
    apply all_1_rngl_product_1.
    intros i (_, Hi).
    now rewrite Nat.add_comm.
  }
  rewrite (rngl_product_split (x - 1)). 2: {
    split; [ flia | ].
    apply -> Nat.succ_le_mono.
    enough (H : x < S n) by flia H Hnz.
    replace x with (σ 0). 2: {
      rewrite H1; [ easy | flia ].
    }
    apply Hp; flia.
  }
  remember (∏ (i = _, _), _)%F as y eqn:Hy.
  rewrite all_1_rngl_product_1. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec x (i + 1)) as [H2| H2]; [ easy | ].
    flia Hi H2.
  }
  subst y; rewrite rngl_mul_1_r.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? i + 1 then 1%F else _) with (-1)%F. 2: {
      rewrite if_ltb_lt_dec.
      destruct (lt_dec x (i + 1)) as [H| H]; [ | easy ].
      flia Hi H Hxz.
    }
    easy.
  }
  cbn.
  destruct x; [ easy | clear Hxz ].
  rewrite Nat_sub_succ_1.
  clear Hx H1.
  induction x; cbn. {
    unfold iter_seq, iter_list; cbn.
    apply rngl_mul_1_l.
  }
  rewrite rngl_product_split_last; [ | flia ].
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  rewrite IHx.
  symmetry.
  rewrite minus_one_pow_succ; [ | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
}
rewrite ε_ws_ε; try easy. 2: {
  apply mk_canon_is_permut_vect.
  apply Nat.mod_upper_bound.
  apply fact_neq_0.
}
unfold ε_ws, ε_fun_ws.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_succ_succ.
  rewrite rngl_product_split_first; [ | flia ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (S i) 1) as [H| H]; [ flia H | clear H ].
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    replace (S i <? S j) with (i <? j) by easy.
    now do 2 rewrite Nat_sub_succ_1.
  }
  easy.
}
cbn - [ canon_sym_gr_elem "<?" fact map vect_vect_nat_el ].
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
move j before i.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
remember (vect_el 0 (vect_vect_nat_el (canon_sym_gr (S n)) k))
  as σ eqn:Hσ.
remember (vect_el 0 (vect_vect_nat_el (canon_sym_gr n) (k mod n!)))
  as σ' eqn:Hσ'.
rewrite (sym_gr_vect_succ_values Hkn Hσ Hσ'); [ | flia Hj ].
rewrite (sym_gr_vect_succ_values Hkn Hσ Hσ'); [ | flia Hi ].
destruct j; [ flia Hj | ].
destruct i; [ flia Hi | ].
rewrite Nat_sub_succ_1.
rewrite Nat_sub_succ_1.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' j) (k / fact n)) as [Hsfj| Hsfj]. {
  destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]; [ easy | ].
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i + 1) (σ' j)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsi1j Hsij.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsij Hsfj Hsfi.
}
destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]. {
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsij Hsfj Hsfi.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsi1j Hsij.
}
unfold sign_diff.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' i + 1) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
  flia Hsi1j Hsij.
}
destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
flia Hsi1j Hsij.
Qed.

(*
Theorem ε_of_sym_gr_permut_succ :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n k,
  k < (S n)!
  → ε (vect_el (canon_sym_gr (S n)) k) =
    (minus_one_pow (k / n!) *
     ε (vect_el (canon_sym_gr n) (k mod n!)))%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hkn.
rewrite ε_ws_ε; try easy; [ | now apply sym_gr_elem_is_permut ].
unfold ε_ws, ε_fun_ws.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold ε, ε_fun.
  subst n.
  apply Nat.lt_1_r in Hkn.
  subst k; cbn.
  unfold iter_seq, iter_list; cbn.
  repeat rewrite rngl_mul_1_l.
  rewrite rngl_div_1_l; [ | easy ].
  now symmetry; apply rngl_inv_1.
}
rewrite rngl_product_succ_succ.
rewrite rngl_product_split_first; [ | flia ].
rewrite Nat.sub_diag.
f_equal. {
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    replace (1 <? 1 + i) with (0 <? i) by easy.
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  cbn - [ "<?" canon_sym_gr_elem ].
  rewrite rngl_product_split_first; [ | flia ].
  replace (0 <? 0) with false by easy.
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec 0 i) as [H| H]; [ clear H | flia Hi H ].
    easy.
  }
  cbn - [ canon_sym_gr_elem ].
  remember (canon_sym_gr_elem (S n) k) as σ eqn:Hσ.
  remember (canon_sym_gr_elem n (k mod fact n)) as σ' eqn:Hσ'.
  specialize (sym_gr_succ_values Hσ Hσ') as H1.
  unfold sign_diff.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite H1.
    replace i with (S (i - 1)) at 1 by flia Hi.
    easy.
  }
  cbn - [ "<?" ].
  remember (k / fact n) as x eqn:Hx.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite <- Nat.sub_succ_l; [ | easy ].
    rewrite Nat_sub_succ_1.
    rewrite H1.
    replace i with (S (i - 1)) at 1 by flia Hi.
    easy.
  }
  cbn - [ "<?" ].
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  cbn - [ "<?" ].
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? _ then _ else _) with
      (if x <? σ' i + 1 then 1%F else (-1)%F). 2: {
      do 3 rewrite if_ltb_lt_dec.
      destruct (lt_dec (σ' i) x) as [H2| H2]; [ | easy ].
      destruct (lt_dec x (σ' i)) as [H| H]; [ flia H H2 | clear H ].
      destruct (lt_dec x (σ' i + 1)) as [H3| H3]; [ | easy ].
      flia H2 H3.
    }
    easy.
  }
  cbn - [ "<?" ].
  assert (Hp' : is_permut_fun σ' n). {
    rewrite Hσ'.
    apply sym_gr_elem_is_permut.
    apply Nat.mod_upper_bound.
    apply fact_neq_0.
  }
  assert (Hp : is_permut_fun σ (S n)). {
    rewrite Hσ.
    now apply sym_gr_elem_is_permut.
  }
  rewrite rngl_product_change_var with (g := permut_fun_inv_loop σ' n) (h := σ').
  2: {
    intros i (_, Hi).
    apply fun_find_prop; [ | flia Hnz Hi ].
    apply Hp'.
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_list_eq_compat. 2: {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite fun_permut_fun_inv_loop; [ easy | easy | ].
    now rewrite <- Hji; apply Hp'.
  }
  cbn - [ "<?" seq ].
  rewrite rngl_product_change_list with (lb := seq 0 n); [ | easy | ]. 2: {
    now apply permut_fun_Permutation.
  }
  rewrite rngl_product_seq_product; [ | easy ].
  rewrite Nat.add_0_l.
  destruct (Nat.eq_dec x 0) as [Hxz| Hxz]. {
    move Hxz at top; subst x.
    cbn - [ "<?" ].
    apply all_1_rngl_product_1; [ easy | ].
    intros i (_, Hi).
    now rewrite Nat.add_comm.
  }
  rewrite (rngl_product_split (x - 1)). 2: {
    split; [ flia | ].
    apply -> Nat.succ_le_mono.
    enough (H : x < S n) by flia H Hnz.
    replace x with (σ 0) by now rewrite H1.
    apply Hp; flia.
  }
  remember (∏ (i = _, _), _)%F as y eqn:Hy.
  rewrite all_1_rngl_product_1; [ | easy | ]. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec x (i + 1)) as [H2| H2]; [ easy | ].
    flia Hi H2.
  }
  subst y; rewrite rngl_mul_1_r.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? i + 1 then 1%F else _) with (-1)%F. 2: {
      rewrite if_ltb_lt_dec.
      destruct (lt_dec x (i + 1)) as [H| H]; [ | easy ].
      flia Hi H Hxz.
    }
    easy.
  }
  cbn.
  destruct x; [ easy | clear Hxz ].
  rewrite Nat_sub_succ_1.
  clear Hx H1.
  induction x; cbn. {
    unfold iter_seq, iter_list; cbn.
    apply rngl_mul_1_l.
  }
  rewrite rngl_product_split_last; [ | flia ].
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  rewrite IHx.
  symmetry.
  rewrite minus_one_pow_succ; [ | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
}
rewrite ε_ws_ε; try easy. 2: {
  apply sym_gr_elem_is_permut.
  apply Nat.mod_upper_bound.
  apply fact_neq_0.
}
unfold ε_ws, ε_fun_ws.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_succ_succ.
  rewrite rngl_product_split_first; [ | flia ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (S i) 1) as [H| H]; [ flia H | clear H ].
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    replace (S i <? S j) with (i <? j) by easy.
    now do 2 rewrite Nat_sub_succ_1.
  }
  easy.
}
cbn - [ canon_sym_gr_elem "<?" ].
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
move j before i.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
remember (canon_sym_gr_elem (S n) k) as σ eqn:Hσ.
remember (canon_sym_gr_elem n (k mod n!)) as σ' eqn:Hσ'.
move σ' before σ.
do 2 rewrite (sym_gr_succ_values Hσ Hσ').
destruct j; [ flia Hj | ].
destruct i; [ flia Hi | ].
rewrite Nat_sub_succ_1.
rewrite Nat_sub_succ_1.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' j) (k / fact n)) as [Hsfj| Hsfj]. {
  destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]; [ easy | ].
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i + 1) (σ' j)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsi1j Hsij.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsij Hsfj Hsfi.
}
destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]. {
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsij Hsfj Hsfi.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsi1j Hsij.
}
unfold sign_diff.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' i + 1) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
  flia Hsi1j Hsij.
}
destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
flia Hsi1j Hsij.
Qed.
*)

Theorem ε_of_permut_ε :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n k,
  k < fact n
  → ε n (vect_vect_nat_el (canon_sym_gr n) k) = ε_permut n k.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hkn.
revert k Hkn.
induction n; intros. {
  cbn; unfold ε, ε_fun; cbn.
  unfold iter_seq, iter_list; cbn.
  apply rngl_div_1_r; [ now left | easy ].
}
rewrite ε_of_sym_gr_permut_succ; try easy.
cbn.
f_equal.
apply IHn.
apply Nat.mod_upper_bound.
apply fact_neq_0.
Qed.

Theorem permut_vect_inv_is_permut : ∀ n (σ : vector nat),
  is_permut_vect n σ
  → is_permut_vect n (permut_vect_inv n σ).
Proof.
intros * (Hp1, Hp2).
specialize (permut_fun_inv_loop_is_permut Hp2) as H1.
split; [ now cbn; rewrite map_length, seq_length | ].
unfold permut_vect_inv, vect_el; cbn.
eapply is_permut_eq_compat. {
  intros i Hi.
  symmetry.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  easy.
}
easy.
Qed.

Theorem canon_sym_gr_inv_ub : ∀ n k j,
  k < fact n
  → j < n
  → canon_sym_gr_inv n k j < n.
Proof.
intros * Hkn Hjn.
revert k j Hkn Hjn.
induction n; intros; [ easy | ].
cbn.
destruct (lt_dec j (k / fact n)) as [Hjkn| Hjkn]. {
  apply -> Nat.succ_lt_mono.
  destruct n. {
    cbn in Hkn.
    apply Nat.lt_1_r in Hkn; subst k.
    now cbn in Hjkn.
  }
  destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
    subst j.
    clear Hjn.
    exfalso; apply Nat.nle_gt in Hjkn; apply Hjkn; clear Hjkn.
    rewrite Nat_fact_succ in Hkn.
    rewrite Nat.mul_comm in Hkn.
    apply Nat.lt_succ_r.
    apply Nat.div_lt_upper_bound; [ | easy ].
    apply fact_neq_0.
  } {
    apply IHn; [ | flia Hjn Hjsn ].
    apply Nat.mod_upper_bound, fact_neq_0.
  }
} {
  apply Nat.nlt_ge in Hjkn.
  destruct (lt_dec (k / fact n) j) as [Hknj| Hknj]; [ | flia ].
  apply -> Nat.succ_lt_mono.
  destruct n. {
    now apply Nat.lt_1_r in Hjn; subst j.
  }
  apply IHn; [ | flia Hjn Hknj ].
  apply Nat.mod_upper_bound, fact_neq_0.
}
Qed.

Theorem sym_gr_sym_gr_inv : ∀ n k j,
  j < n
  → k < fact n
  → canon_sym_gr_elem n k (canon_sym_gr_inv n k j) = j.
Proof.
intros * Hjn Hkn.
revert j k Hjn Hkn.
induction n; intros; [ easy | cbn ].
destruct (lt_dec j (k / fact n)) as [Hjkn| Hjkn]. {
  cbn.
  destruct n. {
    rewrite Nat.div_1_r in Hjkn; cbn in Hkn.
    flia Hkn Hjkn.
  }
  destruct (lt_dec k (fact (S n))) as [Hksn| Hksn]. {
    now rewrite Nat.div_small in Hjkn.
  }
  apply Nat.nlt_ge in Hksn.
  destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
    subst j.
    clear Hjn.
    exfalso; apply Nat.nle_gt in Hjkn; apply Hjkn; clear Hjkn.
    rewrite Nat_fact_succ in Hkn.
    rewrite Nat.mul_comm in Hkn.
    apply Nat.lt_succ_r.
    apply Nat.div_lt_upper_bound; [ | easy ].
    apply fact_neq_0.
  }
  rewrite IHn; [ | flia Hjn Hjsn | ]. 2: {
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  remember (k / fact (S n) <=? j) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ exfalso | apply Nat.add_0_r ].
  apply Nat.leb_le in Hb.
  flia Hjkn Hb.
} {
  apply Nat.nlt_ge in Hjkn.
  destruct (lt_dec (k / fact n) j) as [Hkj| Hkj]. 2: {
    apply Nat.nlt_ge in Hkj; cbn.
    now apply Nat.le_antisymm.
  }
  clear Hjkn.
  destruct j; [ easy | ].
  rewrite Nat_sub_succ_1; cbn.
  destruct n; [ flia Hjn | ].
  apply Nat.succ_lt_mono in Hjn.
  rewrite IHn; [ | easy | ]. 2: {
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  remember (k / fact (S n) <=? j) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ apply Nat.add_1_r | exfalso ].
  apply Nat.leb_nle in Hb.
  now apply Nat.succ_le_mono in Hkj.
}
Qed.

Theorem canon_sym_gr_surjective : ∀ n k j,
  k < fact n
  → j < n
  → ∃ i : nat, i < n ∧ canon_sym_gr_elem n k i = j.
Proof.
intros * Hkn Hjn.
exists (canon_sym_gr_inv n k j).
destruct n; [ easy | ].
split. {
  cbn.
  destruct (lt_dec j (k / fact n)) as [Hjk| Hjk]. {
    apply -> Nat.succ_lt_mono.
    destruct n. {
      now apply Nat.lt_1_r in Hkn; subst k.
    }
    destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
      subst j; clear Hjn.
      apply Nat.nle_gt in Hjk.
      exfalso; apply Hjk; clear Hjk.
      rewrite Nat_fact_succ in Hkn.
      rewrite Nat.mul_comm in Hkn.
      apply Nat.lt_succ_r.
      apply Nat.div_lt_upper_bound; [ | easy ].
      apply fact_neq_0.
    }
    apply canon_sym_gr_inv_upper_bound; [ | flia Hjn Hjsn ].
    apply Nat.mod_upper_bound, fact_neq_0.
  } {
    apply Nat.nlt_ge in Hjk.
    destruct (lt_dec (k / fact n) j) as [Hkj| Hkj]; [ | flia ].
    apply -> Nat.succ_lt_mono.
    destruct n. {
      apply Nat.lt_1_r in Hkn; subst k.
      flia Hjn Hkj.
    }
    apply canon_sym_gr_inv_ub; [ | flia Hjn Hkj ].
    apply Nat.mod_upper_bound, fact_neq_0.
  }
}
now apply sym_gr_sym_gr_inv.
Qed.

Theorem comp_is_permut : ∀ n (σ₁ σ₂ : nat → nat),
  is_permut_fun σ₁ n
  → is_permut_fun σ₂ n
  → is_permut_fun (comp σ₁ σ₂) n.
Proof.
intros * Hp1 Hp2.
split. {
  intros i Hi.
  now apply Hp1, Hp2.
} {
  intros i j Hi Hj Hc.
  apply Hp2; [ easy | easy | ].
  apply Hp1; [ now apply Hp2 | now apply Hp2 | easy ].
}
Qed.

Theorem comp_list_is_permut : ∀ n l,
  (∀ σ, σ ∈ l → is_permut_fun σ n)
  → is_permut_fun (Comp (σ ∈ l), σ) n.
Proof.
intros * Hl.
induction l as [| σ]; [ easy | ].
rewrite iter_list_cons; [ | easy | easy | easy ].
apply comp_is_permut. 2: {
  apply IHl.
  intros σ' Hσ'.
  now apply Hl; right.
}
now apply Hl; left.
Qed.

(*
Theorem is_permut_comp : ∀ n (u v : vector nat),
  is_permut_vect u → is_permut_vect v → is_permut_vect (u ° v).
Proof.
intros * Hu Hv.
split. {
  intros i Hi.
  cbn; unfold comp.
  now apply Hu, Hv.
} {
  intros i j Hi Hj Huv.
  apply Hu in Huv; [ | now apply Hv | now apply Hv ].
  now apply Hv in Huv.
}
Qed.
*)

(*
Theorem ε_1_opp_1 :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n (σ : vector n nat), is_permut_vect σ → ε σ = 1%F ∨ ε σ = (-1)%F.
Proof.
intros Hic Hop Hiv H10 Hit Hed Hch * Hσ.
rewrite ε_ws_ε; try easy.
unfold ε_ws.
unfold ε_fun_ws.
apply rngl_product_1_opp_1; [ easy | ].
intros i Hi.
apply rngl_product_1_opp_1; [ easy | ].
intros j Hj.
unfold sign_diff.
rewrite if_ltb_lt_dec.
rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]. {
  now destruct (lt_dec _ _) as [Hvv| Hvv]; [ left | right ].
}
now left.
Qed.
*)

(*
Theorem ε_square :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n (σ : vector n nat), is_permut_vect σ → (ε σ * ε σ = 1)%F.
Proof.
intros Hic Hop Hiv H10 Hit Hed Hch * Hσ.
specialize (ε_1_opp_1) as H1.
specialize (H1 Hic Hop Hiv H10 Hit Hed Hch).
specialize (H1 n σ Hσ).
destruct H1 as [H1| H1]; rewrite H1. {
  apply rngl_mul_1_l.
} {
  rewrite rngl_mul_opp_opp; [ | easy ].
  apply rngl_mul_1_l.
}
Qed.
*)

End a.

Arguments δ {T}%type {ro} (i j u v)%nat.
Arguments ε {T}%type {ro} n%nat p%V.
Arguments ε_fun {T}%type {ro} f%function n%nat.
Arguments ε_ws {T}%type {ro} n.
Arguments ε_fun_ws {T}%type {ro} f%function n%nat.
Arguments sign_diff {T}%type {ro} (u v)%nat.

Arguments ε_permut {T}%type {ro} (n k)%nat.
Arguments ε_of_sym_gr_permut_succ {T}%type {ro rp} _ _ _ _ _ _ _ (n k)%nat.
Arguments ε_of_permut_ε {T}%type {ro rp} _ _ _ _ _ _ _ n%nat [k]%nat.
Arguments ε_ws_ε {T}%type {ro rp} _ _ _ _ _ _ _ n%nat p%V.
Arguments ε_ws_ε_fun {T}%type {ro rp} _ _ _ _ _ _ _ [σ]%function [n]%nat.
Arguments rngl_product_change_list {T}%type {ro rp} _ [A]%type [la lb]%list
  f%function.
Arguments signature_comp {T}%type {ro rp} _ _ _ _ _ _ _ [n]%nat [σ₁ σ₂].
Arguments transposition_signature {T}%type {ro rp} _ _ _ _ _ _ _ (n p q)%nat.
(*
Arguments ε_1_opp_1 {T}%type {ro rp} _ _ _ _ _ _ _ [n]%nat [σ].
Arguments ε_square {T}%type {ro rp} _ _ _ _ _ _ _ [n]%nat [σ].
*)
