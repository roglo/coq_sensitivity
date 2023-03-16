(* permutations of sequences of natural numbers between 0 and n-1 *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.
Import Init.Nat.

Require Import Misc PermutationFun SortingFun SortRank.
Require Import IterAnd.
Require Import Pigeonhole.

Definition comp {A B C} (f : B → C) (g : A → B) x := f (g x).
Definition comp_list (la lb : list nat) := map (λ i, nth i la 0) lb.

Notation "σ₁ ° σ₂" := (comp_list σ₁ σ₂) (at level 40, left associativity).

(* Permutations of {0, 1, 2, ... n-1} *)

Definition permut_seq l := permutation Nat.eqb l (seq 0 (length l)).
Definition permut_seq_with_len n f := permut_seq f ∧ length f = n.

Theorem permut_seq_NoDup : ∀ l, permut_seq l → NoDup l.
Proof.
intros * Hp.
unfold permut_seq in Hp.
apply (permutation_sym Nat.eqb_eq) in Hp.
apply (permutation_NoDup Nat.eqb_eq Hp (seq_NoDup _ _)).
Qed.

Theorem permut_seq_ub : ∀ l, permut_seq l → AllLt l (length l).
Proof.
intros * Hp.
unfold permut_seq in Hp.
specialize (permutation_in_iff Nat.eqb_eq Hp) as H1.
intros i Hi.
apply H1 in Hi.
now apply in_seq in Hi.
Qed.

Theorem permut_seq_iff : ∀ l,
  permut_seq l ↔ AllLt l (length l) ∧ NoDup l.
Proof.
intros.
split; intros Hl. {
  now split; [ apply permut_seq_ub | apply permut_seq_NoDup ].
}
destruct Hl as (Hp1, Hp2).
unfold permut_seq.
remember (length l) as len eqn:Hlen; symmetry in Hlen.
revert l Hlen Hp1 Hp2.
induction len; intros. {
  now apply length_zero_iff_nil in Hlen; subst l.
}
rewrite seq_S; cbn.
unfold AllLt in Hp1.
assert (H : len ∈ l). {
  destruct (equality_in_dec Nat.eqb_eq len l) as [H1| H1]; [ easy | exfalso ].
  specialize (pigeonhole_list len l) as H2.
  rewrite Hlen in H2.
  assert (H : len < S len) by easy.
  specialize (H2 H); clear H.
  assert (H : ∀ i, i ∈ l → i < len). {
    intros i Hi.
    specialize (Hp1 _ Hi).
    destruct (Nat.eq_dec i len) as [Hil| Hil]; [ | flia Hp1 Hil ].
    now subst i.
  }
  specialize (H2 H); clear H.
  remember (pigeonhole_comp_list l) as xx eqn:Hxx.
  symmetry in Hxx.
  destruct xx as (i, j).
  specialize (H2 _ _ eq_refl).
  destruct H2 as (Hil & Hj & H & Hij).
  apply H; clear H.
  rewrite <- Hlen in Hil, Hj.
  now apply (NoDup_nth l 0).
}
apply in_split in H.
destruct H as (l1 & l2 & Hl); subst l.
apply (permutation_elt Nat.eqb_eq).
rewrite app_nil_r.
apply IHlen. {
  rewrite app_length in Hlen; cbn in Hlen.
  rewrite Nat.add_succ_r in Hlen.
  apply Nat.succ_inj in Hlen.
  now rewrite <- app_length in Hlen.
} {
  intros i Hi.
  specialize (Hp1 i) as H1.
  assert (H : i ∈ l1 ++ len :: l2). {
    apply in_app_or in Hi; apply in_or_app.
    destruct Hi as [Hi| Hi]; [ now left | now right; right ].
  }
  specialize (H1 H); clear H.
  destruct (Nat.eq_dec i len) as [H2| H2]; [ | flia H1 H2 ].
  subst i; clear H1.
  apply NoDup_app_iff in Hp2.
  destruct Hp2 as (H1 & H2 & H4).
  apply NoDup_cons_iff in H2.
  destruct H2 as (H2 & H3).
  apply in_app_or in Hi.
  destruct Hi as [Hi| Hi]; [ | easy ].
  specialize (H4 _ Hi).
  now exfalso; apply H4; left.
} {
  apply NoDup_app_iff in Hp2.
  apply NoDup_app_iff.
  destruct Hp2 as (H1 & H2 & H3).
  apply NoDup_cons_iff in H2.
  split; [ easy | ].
  split; [ easy | ].
  intros i Hi.
  specialize (H3 _ Hi).
  intros H4; apply H3.
  now right.
}
Qed.

Theorem comp_list_app_distr_l : ∀ la lb lc,
  la ° (lb ++ lc) = la ° lb ++ la ° lc.
Proof.
intros.
unfold "°".
now rewrite map_app.
Qed.

(* *)

Theorem NoDup_nat : ∀ l,
  NoDup l
  → (∀ i j, i < length l → j < length l → nth i l 0 = nth j l 0 → i = j).
Proof.
intros * Hnd.
now apply NoDup_nth.
Qed.
Arguments NoDup_nat : clear implicits.

Theorem nat_NoDup : ∀ l,
  (∀ i j, i < length l → j < length l → nth i l 0 = nth j l 0 → i = j)
  → NoDup l.
Proof.
intros * Hnd.
now apply NoDup_nth in Hnd.
Qed.

Theorem permut_list_without : ∀ n l,
  permut_seq l
  → n < length l
  → (∀ i, i < length l → nth i l 0 ≠ n)
  → False.
Proof.
intros * Hp Hn Hnn.
specialize (pigeonhole_list (length l) (n :: l)) as H1.
specialize (H1 (Nat.lt_succ_diag_r _)).
assert (H : ∀ x, x ∈ n :: l → x < length l). {
  intros z Hz.
  destruct Hz as [Hz| Hz]; [ now subst z | now apply permut_seq_ub ].
}
specialize (H1 H); clear H.
remember (pigeonhole_comp_list (n :: l)) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (x, x').
specialize (H1 x x' eq_refl).
destruct H1 as (Hxl & Hx'l & Hxx' & Hnxx).
destruct x. {
  destruct x'; [ easy | cbn in Hnxx ].
  cbn in Hx'l; apply Nat.succ_lt_mono in Hx'l.
  specialize (Hnn x' Hx'l).
  now symmetry in Hnxx.
} {
  cbn in Hxl; apply Nat.succ_lt_mono in Hxl.
  destruct x'. {
    cbn in Hnxx.
    now specialize (Hnn x Hxl).
  }
  cbn in Hnxx.
  cbn in Hx'l; apply Nat.succ_lt_mono in Hx'l.
  specialize (permut_seq_NoDup Hp) as Hp2.
  specialize (NoDup_nat _ Hp2 x x' Hxl Hx'l Hnxx) as H1.
  now destruct H1.
}
Qed.

Theorem nat_decidable_not_forall_exists_not : ∀ (P : nat → _) n,
  (∀ i, Decidable.decidable (P i))
  → ¬ (∀ i, i < n → P i)
  → ∃ i, i < n ∧ ¬ P i.
Proof.
intros * Hdec Hin.
induction n; [ now exfalso; apply Hin | ].
destruct (Hdec n) as [Hn| Hn]; [ | now exists n ].
assert (H : ¬ (∀ i, i < n → P i)). {
  intros H2.
  apply Hin.
  intros k Hk.
  destruct (Nat.eq_dec k n) as [Hkn| Hkn]; [ now subst k | ].
  apply H2.
  flia Hk Hkn.
}
specialize (IHn H); clear H.
destruct IHn as (k & Hkn & Hpk).
exists k.
split; [ | easy ].
flia Hkn.
Qed.

Theorem permut_list_surj : ∀ n l,
  permut_seq l
  → n < length l
  → ∃ i, i < length l ∧ nth i l 0 = n.
Proof.
intros * Hp Hn.
specialize (permut_list_without Hp Hn) as H1.
specialize nat_decidable_not_forall_exists_not as H2.
specialize (H2 (λ i, nth i l 0 ≠ n)).
cbn in H2.
enough (H : ∃ i, i < length l ∧ ¬ nth i l 0 ≠ n). {
  destruct H as (i & Hil & Hni).
  exists i; split; [ easy | ].
  now destruct (Nat.eq_dec (nth i l 0) n).
}
apply H2; [ | easy ].
intros i.
now destruct (Nat.eq_dec (nth i l 0) n) as [H| H]; [ right | left ].
Qed.

Theorem permut_comp_assoc : ∀ n f g h,
  length g = n
  → length h = n
  → permut_seq h
  → f ° (g ° h) = (f ° g) ° h.
Proof.
intros * Hg Hh Hph.
unfold "°", comp_list; cbn.
rewrite map_map.
apply map_ext_in.
intros i Hi.
rewrite (List_map_nth' 0); [ easy | ].
rewrite Hg, <- Hh.
now apply permut_seq_ub.
Qed.

Arguments permut_comp_assoc n%nat [f g h]%list.

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

Definition succ_when_ge k a := a + Nat.b2n (k <=? a).

(* k-th canonic permutation of order n *)
Fixpoint canon_sym_gr_list n k : list nat :=
  match n with
  | 0 => []
  | S n' =>
      k / n'! ::
      map (succ_when_ge (k / n'!)) (canon_sym_gr_list n' (k mod n'!))
  end.

(* all canonic permutations of "seq 0 n" *)
Definition canon_sym_gr_list_list n : list (list nat) :=
  map (canon_sym_gr_list n) (seq 0 n!).

(* all permutations of a list of anything *)
Definition all_permut {A} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | d :: _ =>
      map (λ p, map (λ i, nth i l d) p) (canon_sym_gr_list_list (length l))
  end.

Definition is_sym_gr_list n (ll : list (list nat)) :=
  (∀ i, i < length ll →
   length (nth i ll []) = n ∧
   permut_seq (nth i ll [])) ∧
  (∀ i j, i < length ll → j < length ll →
   nth i ll [] = nth j ll [] → i = j) ∧
  (∀ l, permut_seq_with_len n l → l ∈ ll).

Theorem comp_length : ∀ la lb,
  length (la ° lb) = length lb.
Proof.
intros.
unfold "°"; cbn.
now rewrite map_length.
Qed.

Theorem comp_isort_rank_r : ∀ rel l,
  l ° isort_rank rel l = isort rel l.
Proof.
intros.
apply List_eq_iff.
rewrite comp_length, isort_rank_length, isort_length.
split; [ easy | ].
intros d i.
destruct (lt_dec i (length l)) as [Hil| Hil]. 2: {
  apply Nat.nlt_ge in Hil.
  rewrite nth_overflow; [ | now rewrite comp_length, isort_rank_length ].
  rewrite nth_overflow; [ easy | now rewrite isort_length ].
}
rewrite nth_indep with (d' := 0). 2: {
  now rewrite comp_length, isort_rank_length.
}
symmetry.
rewrite nth_indep with (d' := 0); [ | now rewrite isort_length ].
symmetry.
unfold "°".
rewrite (List_map_nth' 0); [ | now rewrite isort_rank_length ].
specialize (isort_isort_rank rel 0 l) as H1.
apply (f_equal (λ l, nth i l 0)) in H1.
rewrite (List_map_nth' 0) in H1; [ | now rewrite isort_rank_length ].
easy.
Qed.

(* *)

Theorem perm_assoc_permut_seq : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  permutation eqb la lb
  → permut_seq (permutation_assoc eqb la lb).
Proof.
intros * Heqb * Hpab.
unfold permut_seq.
rewrite (permutation_assoc_length Heqb); [ | easy ].
now apply (permutation_permutation_assoc Heqb).
Qed.

Theorem permut_seq_permutation : ∀ n la lb,
  permut_seq_with_len n la
  → permut_seq_with_len n lb
  → permutation Nat.eqb la lb.
Proof.
intros * Ha Hb.
destruct Ha as (Ha, Hal).
destruct Hb as (Hb, Hbl).
unfold permut_seq in Ha, Hb.
eapply (permutation_trans Nat.eqb_eq); [ apply Ha | ].
rewrite Hal, <- Hbl.
now apply (permutation_sym Nat.eqb_eq).
Qed.

Theorem permutation_permut : ∀ la lb,
  permutation Nat.eqb la lb
  → permut_seq la
  → permut_seq lb.
Proof.
intros * Hpab Ha.
unfold permut_seq in Ha |-*.
eapply (permutation_trans Nat.eqb_eq). {
  apply (permutation_sym Nat.eqb_eq), Hpab.
}
now rewrite (permutation_length Hpab) in Ha.
Qed.

(* *)

Theorem permut_seq_app_max : ∀ l,
  permut_seq (l ++ [length l])
  → permut_seq l.
Proof.
intros * Hp.
unfold permut_seq in Hp |-*.
rewrite app_length in Hp; cbn in Hp.
rewrite Nat.add_1_r, seq_S in Hp; cbn in Hp.
apply (permutation_app_inv Nat.eqb_eq) in Hp.
now do 2 rewrite app_nil_r in Hp.
Qed.

Theorem sorted_permut : ∀ l,
  permut_seq l
  → sorted Nat.leb l
  → l = seq 0 (length l).
Proof.
intros * Hl Hs.
unfold permut_seq in Hl.
apply (sorted_sorted_permuted Nat.eqb_eq Nat_leb_antisym); [ | easy | | ]. {
  apply Nat_leb_trans.
} {
  apply sorted_nat_ltb_leb_incl, sorted_seq.
}
easy.
Qed.

(* *)

Theorem permut_isort_leb : ∀ l,
  permut_seq l
  → isort Nat.leb l = seq 0 (length l).
Proof.
intros * Hp.
specialize (sorted_isort Nat_leb_total_relation l) as Hbs.
specialize (permuted_isort Nat.leb Nat.eqb_eq l) as Hps.
remember (isort Nat.leb l) as l'; clear Heql'.
specialize permutation_permut as Hpl'.
specialize (Hpl' l l' Hps Hp).
move l' before l; move Hpl' before Hp.
replace (length l) with (length l'). 2: {
  now apply permutation_length in Hps.
}
clear l Hp Hps.
rename l' into l.
now apply sorted_permut.
Qed.

Theorem permut_comp_isort_rank_r : ∀ l,
  permut_seq l
  → l ° isort_rank Nat.leb l = seq 0 (length l).
Proof.
intros * Hp.
rewrite comp_isort_rank_r.
now apply permut_isort_leb.
Qed.

Theorem permut_isort_permut : ∀ i l,
  permut_seq l
  → i < length l
  → nth (nth i l 0) (isort_rank Nat.leb l) 0 = i.
Proof.
intros * Hp Hil.
specialize (permut_comp_isort_rank_r Hp) as H1.
apply List_eq_iff in H1.
destruct H1 as (_, H1).
specialize (H1 0).
unfold "°" in H1.
assert
  (H2 : ∀ j, j < length l → nth (nth j (isort_rank Nat.leb l) 0) l 0 = j). {
  intros j Hj.
  specialize (H1 j).
  rewrite (List_map_nth' 0) in H1; [ | now rewrite isort_rank_length ].
  now rewrite seq_nth in H1.
}
clear H1.
specialize (H2 (nth i l 0)) as H2.
assert (H : nth i l 0 < length l). {
  apply permut_seq_ub; [ easy | now apply nth_In ].
}
specialize (H2 H); clear H.
apply NoDup_nat in H2; [ easy | now apply permut_seq_NoDup | | easy ].
apply isort_rank_ub.
now intros H; subst l.
Qed.

Theorem permut_comp_isort_rank_l : ∀ l,
  permut_seq l
  → isort_rank Nat.leb l ° l = seq 0 (length l).
Proof.
intros * Hp.
apply List_eq_iff.
rewrite comp_length, seq_length.
split; [ easy | ].
intros d i.
destruct (lt_dec i (length l)) as [Hil| Hil]. 2: {
  apply Nat.nlt_ge in Hil.
  rewrite nth_overflow; [ | now rewrite comp_length ].
  rewrite nth_overflow; [ easy | now rewrite seq_length ].
}
rewrite seq_nth; [ | easy ].
rewrite nth_indep with (d' := 0); [ | now rewrite comp_length ].
clear d.
unfold "°".
rewrite (List_map_nth' 0); [ | easy ].
now apply permut_isort_permut.
Qed.

Theorem permut_permut_isort : ∀ i l,
  permut_seq l
  → i < length l
  → nth (nth i (isort_rank Nat.leb l) 0) l 0 = i.
Proof.
intros * Hp Hil.
specialize (permut_comp_isort_rank_l Hp) as H1.
apply List_eq_iff in H1.
destruct H1 as (_, H1).
specialize (H1 0).
unfold "°" in H1.
assert
  (H2 : ∀ j, j < length l → nth (nth j l 0) (isort_rank Nat.leb l) 0 = j). {
  intros j Hj.
  specialize (H1 j).
  rewrite (List_map_nth' 0) in H1; [ | easy ].
  now rewrite seq_nth in H1.
}
clear H1.
specialize (H2 (nth i (isort_rank Nat.leb l) 0)) as H2.
assert (H : nth i (isort_rank Nat.leb l) 0 < length l). {
  apply isort_rank_ub.
  now intros H; subst l.
}
specialize (H2 H); clear H.
specialize (NoDup_isort_rank Nat.leb l) as H3.
apply (NoDup_nat _ H3) in H2; [ easy | | ]. 2: {
  now rewrite isort_rank_length.
}
rewrite isort_rank_length.
apply permut_seq_ub; [ easy | ].
apply nth_In.
apply isort_rank_ub.
now intros H; subst l.
Qed.

(* transposition *)

Definition transposition i j k :=
  if k =? i then j else if k =? j then i else k.

Definition list_swap_elem {A} d (l : list A) i j :=
  map (λ k, nth (transposition i j k) l d) (seq 0 (length l)).

Theorem fold_transposition : ∀ i j k,
  (if k =? i then j else if k =? j then i else k) = transposition i j k.
Proof. easy. Qed.

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

Theorem list_swap_elem_length : ∀ A (d : A) l p q,
  length (list_swap_elem d l p q) = length l.
Proof.
intros.
unfold list_swap_elem.
now rewrite map_length, seq_length.
Qed.

Theorem list_swap_elem_involutive : ∀ A (d : A) l i j,
  i < length l
  → j < length l
  → list_swap_elem d (list_swap_elem d l i j) i j = l.
Proof.
intros * Hi Hj.
unfold list_swap_elem.
rewrite map_length, seq_length.
erewrite map_ext_in. 2: {
  intros k Hk; apply in_seq in Hk.
  rewrite (List_map_nth' 0). 2: {
    now rewrite seq_length; apply transposition_lt.
  }
  rewrite seq_nth; [ | now apply transposition_lt ].
  rewrite Nat.add_0_l.
  now rewrite transposition_involutive.
}
symmetry.
apply List_map_nth_seq.
Qed.

Theorem transposition_out : ∀ i j k, k ≠ i → k ≠ j → transposition i j k = k.
Proof.
intros * Hi Hj.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i) as [H| H]; [ easy | clear H ].
now destruct (Nat.eq_dec k j).
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

Theorem transposition_id : ∀ i j, transposition i i j = j.
Proof.
intros.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
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

Theorem list_swap_elem_permut_seq : ∀ σ p q,
  p < length σ
  → q < length σ
  → permut_seq σ
  → permut_seq (list_swap_elem 0 σ p q).
Proof.
intros * Hp Hq Hσ.
apply permut_seq_iff.
unfold list_swap_elem.
rewrite map_length, seq_length.
split; cbn. {
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  rewrite <- Hji.
  apply permut_seq_ub; [ easy | ].
  apply nth_In.
  now apply transposition_lt.
} {
  apply nat_NoDup.
  rewrite List_map_seq_length.
  intros i j Hi Hj Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  unfold transposition in Hij.
  do 4 rewrite if_eqb_eq_dec in Hij.
  apply permut_seq_NoDup in Hσ.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    subst i.
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
      now subst j; apply (NoDup_nat σ).
    }
    apply Nat.neq_sym in Hjq.
    now exfalso; apply Hjq, (NoDup_nat σ).
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
      now subst i j; apply (NoDup_nat σ).
    }
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ congruence | ].
    apply Nat.neq_sym in Hjp; exfalso; apply Hjp.
    now apply (NoDup_nat σ).
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
    now exfalso; apply Hiq, (NoDup_nat σ).
  }
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
    now exfalso; apply Hip, (NoDup_nat σ).
  }
  now apply (NoDup_nat σ).
}
Qed.

Theorem list_swap_elem_permut_seq_with_len : ∀ n σ p q,
  p < n
  → q < n
  → permut_seq_with_len n σ
  → permut_seq_with_len n (list_swap_elem 0 σ p q).
Proof.
intros * Hp Hq Hσ.
split; [ | now rewrite list_swap_elem_length; destruct Hσ ].
destruct Hσ as (H1, H2).
rewrite <- H2 in Hp, Hq.
now apply list_swap_elem_permut_seq.
Qed.

(* *)

Definition sym_gr_inv (sg : list (list nat)) σ :=
  let j := List_rank (list_eqv Nat.eqb σ) sg in
  if j =? length sg then 0 else j.

Theorem sym_gr_inv_inj : ∀ n sg la lb,
  is_sym_gr_list n sg
  → permut_seq_with_len n la
  → permut_seq_with_len n lb
  → sym_gr_inv sg la = sym_gr_inv sg lb
  → la = lb.
Proof.
intros * Hsg Hna Hnb Hab.
unfold sym_gr_inv, unsome in Hab.
remember (List_rank (list_eqv Nat.eqb la) sg) as x eqn:Hx.
remember (List_rank (list_eqv Nat.eqb lb) sg) as y eqn:Hy.
move y before x.
symmetry in Hx, Hy.
rewrite if_eqb_eq_dec in Hab.
destruct (Nat.eq_dec x (length sg)) as [Hxg| Hxg]. 2: {
  apply (List_rank_if []) in Hx.
  destruct Hx as (Hbefx, Hx).
  destruct Hx as [Hx| Hx]; [ | easy ].
  destruct Hx as (Hxs & Hx).
  apply (list_eqb_eq Nat.eqb_eq) in Hx.
  rewrite if_eqb_eq_dec in Hab.
  destruct (Nat.eq_dec y (length sg)) as [Hyg| Hyg]. 2: {
    apply (List_rank_if []) in Hy.
    destruct Hy as (Hbefy & Hy).
    destruct Hy as [Hy| Hy]; [ | easy ].
    destruct Hy as (Hys & Hy).
    apply (list_eqb_eq Nat.eqb_eq) in Hy.
    congruence.
  }
  specialize (List_rank_if [] _ _ Hy) as H1.
  destruct H1 as (H1, _).
  rewrite Hyg in H1.
  destruct Hsg as (Hsg & Hsg_inj & Hsg_surj).
  specialize (Hsg_surj lb Hnb) as H2.
  apply In_nth with (d := []) in H2.
  destruct H2 as (k & Hk & Hkb).
  specialize (H1 k Hk).
  apply (list_eqb_neq Nat.eqb_eq) in H1.
  now symmetry in Hkb.
}
specialize (List_rank_if [] _ _ Hx) as H1; cbn.
destruct H1 as (H1, _).
rewrite Hxg in H1.
destruct Hsg as (Hsg & Hsg_inj & Hsg_surj).
specialize (Hsg_surj la Hna) as H2.
apply In_nth with (d := []) in H2.
destruct H2 as (k & Hk & Hka).
specialize (H1 k Hk).
apply (list_eqb_neq Nat.eqb_eq) in H1.
now symmetry in Hka.
Qed.

Theorem seq_permut_seq : ∀ n, permut_seq (seq 0 n).
Proof.
intros.
unfold permut_seq.
rewrite seq_length.
apply (permutation_refl Nat.eqb_eq).
Qed.

Theorem seq_permut_seq_with_len : ∀ n, permut_seq_with_len n (seq 0 n).
Proof.
intros.
split; [ | apply seq_length ].
apply seq_permut_seq.
Qed.

Theorem sym_gr_inv_lt : ∀ n sg v,
  n ≠ 0
  → is_sym_gr_list n sg
  → sym_gr_inv sg v < length sg.
Proof.
intros * Hnz Hsg.
unfold sym_gr_inv.
rewrite if_eqb_eq_dec.
remember (List_rank _ _) as i eqn:Hi; symmetry in Hi.
destruct (Nat.eq_dec _ _) as [Hrl| Hrl]. 2: {
  apply (List_rank_if []) in Hi.
  destruct Hi as (_, H1).
  now destruct H1.
}
destruct (lt_dec 0 (length sg)) as [Hs| Hs]; [ easy | ].
apply Nat.nlt_ge in Hs; exfalso.
apply Nat.le_0_r in Hs.
apply length_zero_iff_nil in Hs; subst sg.
destruct Hsg as (_ & _ & Hsurj).
cbn in Hsurj.
apply (Hsurj (seq 0 n)).
apply seq_permut_seq_with_len.
Qed.

Theorem nth_sym_gr_inv_sym_gr : ∀ sg l n,
  is_sym_gr_list n sg
  → permut_seq_with_len n l
  → nth (sym_gr_inv sg l) sg [] = l.
Proof.
intros * Hsg (Hp, Hs).
unfold sym_gr_inv, unsome.
rewrite if_eqb_eq_dec.
remember (List_rank _ _) as i eqn:Hi; symmetry in Hi.
destruct (Nat.eq_dec _ _) as [His| His]. 2: {
  apply (List_rank_if []) in Hi.
  destruct Hi as (Hji, H1).
  destruct H1 as [H1| H1]; [ | easy ].
  clear His.
  destruct H1 as (His & Hi).
  now apply (list_eqb_eq Nat.eqb_eq) in Hi.
}
assert (H : l ∉ sg). {
  intros H.
  apply In_nth with (d := []) in H.
  destruct H as (j & Hj & Hjv).
  specialize (List_rank_if [] _ _ Hi) as H.
  rewrite His in H.
  destruct H as (H, _).
  specialize (H _ Hj).
  apply (list_eqb_neq Nat.eqb_eq) in H.
  now symmetry in Hjv.
}
exfalso; apply H; clear H.
now apply Hsg.
Qed.

Theorem sym_gr_inv_list_el : ∀ n sg i,
  n ≠ 0
  → is_sym_gr_list n sg
  → i < length sg
  → sym_gr_inv sg (nth i sg []) = i.
Proof.
intros * Hnz Hsg Hi.
unfold sym_gr_inv, unsome.
remember (List_rank _ _) as j eqn:Hj; symmetry in Hj.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec j (length sg)) as [Hjs| Hjs]. 2: {
  apply (List_rank_if []) in Hj.
  destruct Hj as (Hji, Hj).
  destruct Hj as [Hj| Hj]; [ clear Hjs | easy ].
  destruct Hj as (Hjs, Hj).
  apply (list_eqb_eq Nat.eqb_eq) in Hj.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  now apply Hinj.
}
specialize (List_rank_if [] _ _ Hj) as H1.
destruct H1 as (H1, _).
rewrite Hjs in H1.
specialize (H1 _ Hi).
now apply (list_eqb_neq Nat.eqb_eq) in H1.
Qed.

Theorem length_of_empty_sym_gr : ∀ sg,
  is_sym_gr_list 0 sg → length sg = 1.
Proof.
intros * Hsg.
destruct Hsg as (Hsg & Hinj & Hsurj).
assert (H : permut_seq_with_len 0 []) by easy.
specialize (Hsurj _ H) as H1; clear H.
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

Theorem canon_sym_gr_list_length : ∀ k n,
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
rewrite (List_map_nth' 0); [ | now rewrite canon_sym_gr_list_length ].
unfold succ_when_ge.
rewrite <- Nat.add_1_r.
apply Nat.add_lt_le_mono; [ | apply Nat_b2n_upper_bound ].
now apply IHn.
Qed.

Theorem canon_sym_gr_inv_list_ub : ∀ n k j,
  k < n!
  → j < n
  → nth j (canon_sym_gr_inv_list n k) 0 < n.
Proof.
intros * Hkn Hjn.
unfold canon_sym_gr_inv_list.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ cbn | easy ].
revert k j Hkn Hjn.
induction n; intros; [ easy | cbn ].
destruct (lt_dec j (k / fact n)) as [Hjkn| Hjkn]. {
  apply -> Nat.succ_lt_mono.
  destruct n. {
    cbn in Hkn.
    apply Nat.lt_1_r in Hkn; subst k.
    easy.
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
    apply IHn; [ easy | flia Hjn Hjsn ].
  }
} {
  apply Nat.nlt_ge in Hjkn.
  destruct (lt_dec (k / fact n) j) as [Hknj| Hknj]; [ | easy ].
  apply -> Nat.succ_lt_mono.
  destruct n. {
    now apply Nat.lt_1_r in Hjn; subst j.
  }
  apply IHn; [ easy | flia Hjn Hknj ].
}
Qed.

Theorem canon_sym_gr_inv_sym_gr : ∀ n k i,
  k < n!
  → i < n
  → nth (nth i (canon_sym_gr_list n k) 0)  (canon_sym_gr_inv_list n k) 0 = i.
Proof.
intros * Hkn Hi.
unfold canon_sym_gr_inv_list.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now apply canon_sym_gr_list_ub.
}
rewrite seq_nth; [ | now apply canon_sym_gr_list_ub ].
rewrite Nat.add_0_l.
revert k i Hi Hkn.
induction n; intros; [ easy | cbn ].
destruct i. {
  do 2 rewrite <- if_ltb_lt_dec.
  now rewrite Nat.ltb_irrefl.
}
apply Nat.succ_lt_mono in Hi.
rewrite (List_map_nth' 0); [ | now rewrite canon_sym_gr_list_length ].
unfold succ_when_ge.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec (k / n!) _) as [H1| H1]. {
  destruct (lt_dec _ (k / n!)) as [H| H]; [ flia H1 H | clear H ].
  destruct (lt_dec (k / n!) _) as [H| H]; [ clear H | flia H1 H ].
  f_equal; rewrite Nat.add_sub.
  now apply IHn.
} {
  rewrite Nat.add_0_r.
  destruct (lt_dec _ (k / n!)) as [H| H]; [ clear H | flia H1 H ].
  f_equal.
  now apply IHn.
}
Qed.

Theorem canon_sym_gr_inv_elem_ub : ∀ n k i,
  k < n!
  → i < n
  → canon_sym_gr_inv_elem n k i < n.
Proof.
intros * Hkn Hi.
revert i k Hkn Hi.
induction n; intros; [ easy | cbn ].
destruct (lt_dec i (k / n!)) as [Hikn| Hikn]. {
  apply -> Nat.succ_lt_mono.
  destruct (Nat.eq_dec i n) as [Hin| Hin]. {
    exfalso.
    subst i; clear Hi.
    rewrite Nat_fact_succ in Hkn.
    assert (Hkns : k / n! < S n). {
      apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
      now rewrite Nat.mul_comm.
    }
    flia Hikn Hkns.
  }
  apply IHn; [ easy | flia Hi Hin ].
}
destruct (lt_dec (k / n!) i) as [Hkni| Hkni]; [ | easy ].
apply -> Nat.succ_lt_mono.
apply IHn; [ easy | flia Hi Hkni ].
Qed.

Theorem canon_sym_gr_sym_gr_inv : ∀ n k i,
  k < n!
  → i < n
  → nth (nth i (canon_sym_gr_inv_list n k) 0) (canon_sym_gr_list n k) 0 = i.
Proof.
intros * Hkn Hi.
unfold canon_sym_gr_inv_list.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite Nat.add_0_l.
revert k i Hi Hkn.
induction n; intros; [ easy | cbn ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  now apply Nat.lt_1_r in Hkn, Hi; subst k i.
}
apply Nat.neq_0_lt_0 in Hnz.
destruct i. {
  destruct (lt_dec 0 (k / n!)) as [Hzkn| Hzkn]. {
    unfold succ_when_ge.
    rewrite (List_map_nth' 0). 2: {
      rewrite canon_sym_gr_list_length.
      now apply canon_sym_gr_inv_elem_ub.
    }
    rewrite IHn; [ | easy | easy ].
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec (k / n!) 0) as [Hknz| Hknz]; [ | easy ].
    now apply Nat.nlt_ge in Hknz.
  }
  apply Nat.nlt_ge in Hzkn.
  apply Nat.le_0_r in Hzkn.
  now rewrite Hzkn; cbn.
}
apply Nat.succ_lt_mono in Hi.
destruct (lt_dec (S i) (k / n!)) as [Hsikn| Hsikn]. {
  destruct (Nat.eq_dec (S i) n) as [Hsin| Hsin]. {
    rewrite Hsin in Hsikn.
    rewrite Nat_fact_succ in Hkn.
    assert (Hkns : k / n! < S n). {
      apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
      now rewrite Nat.mul_comm.
    }
    flia Hsikn Hkns.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite canon_sym_gr_list_length.
    apply canon_sym_gr_inv_elem_ub; [ easy | flia Hi Hsin ].
  }
  rewrite IHn; [ | flia Hi Hsin | easy ].
  unfold succ_when_ge, Nat.b2n.
  apply Nat.nle_gt in Hsikn.
  apply Nat.leb_nle in Hsikn.
  now rewrite Hsikn, Nat.add_0_r.
}
apply Nat.nlt_ge in Hsikn.
destruct (lt_dec (k / n!) (S i)) as [Hknsi| Hknsi]; [ | flia Hsikn Hknsi ].
rewrite Nat_sub_succ_1.
rewrite (List_map_nth' 0).  2: {
  rewrite canon_sym_gr_list_length.
  now apply canon_sym_gr_inv_elem_ub.
}
rewrite IHn; [ | easy | easy ].
unfold succ_when_ge.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec (k / n!) i) as [Hkni| Hkni]; [ apply Nat.add_1_r | ].
now apply Nat.succ_le_mono in Hknsi.
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
rewrite (List_map_nth' 0) in H1; [ | now rewrite canon_sym_gr_list_length ].
rewrite (List_map_nth' 0) in H1; [ | now rewrite canon_sym_gr_list_length ].
unfold succ_when_ge, Nat.b2n in H1.
do 2 rewrite if_leb_le_dec in H1.
destruct (le_dec (j / n!) _) as [H2| H2]. {
  destruct (le_dec (j / n!) _) as [H3| H3]; [ | flia H1 H2 H3 ].
  now apply Nat.add_cancel_r in H1.
}
destruct (le_dec (j / n!) _) as [H3| H3]; [ flia H1 H2 H3 | flia H1 ].
Qed.

Theorem canon_sym_gr_inv_list_length : ∀ n i,
  length (canon_sym_gr_inv_list n i) = n.
Proof.
intros.
unfold canon_sym_gr_inv_list.
apply List_map_seq_length.
Qed.

Theorem NoDup_canon_sym_gr_inv_list : ∀ n i,
  i < n!
  → NoDup (canon_sym_gr_inv_list n i).
Proof.
intros * Hi.
apply nat_NoDup.
rewrite canon_sym_gr_inv_list_length.
intros j k Hj Hk Hjk.
apply (f_equal (λ m, nth m (canon_sym_gr_list n i) 0)) in Hjk.
rewrite canon_sym_gr_sym_gr_inv in Hjk; [ | easy | easy ].
rewrite canon_sym_gr_sym_gr_inv in Hjk; [ | easy | easy ].
easy.
Qed.

Theorem in_canon_sym_gr_list : ∀ n k i,
  k < n! → i ∈ canon_sym_gr_list n k → i < n.
Proof.
intros * Hkn Hi.
apply (In_nth _ _ 0) in Hi.
destruct Hi as (j & Hj & Hi); subst i.
rewrite canon_sym_gr_list_length in Hj.
now apply canon_sym_gr_list_ub.
Qed.

(* *)

Definition sub_canon_permut_list (l : list nat) :=
  map (λ a, a - Nat.b2n (hd 0 l <? a)) (tl l).

Fixpoint canon_sym_gr_list_inv n (l : list nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      hd 0 l * n'! +
      canon_sym_gr_list_inv n' (sub_canon_permut_list l)
  end.

Theorem sub_canon_permut_list_elem_ub : ∀ l i,
  permut_seq l
  → S i < length l
  → nth i (sub_canon_permut_list l) 0 < length l - 1.
Proof.
intros * Hp Hin.
apply permut_seq_iff in Hp.
destruct Hp as (Hvn, Hn).
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
  now specialize (NoDup_nat _ Hn 0 (S i) (Nat.lt_0_succ _) Hin Hia).
}
specialize (Hvn a (or_introl eq_refl)); cbn in Hvn.
flia Hvn Hal Hia.
Qed.

Theorem sub_canon_sym_gr_elem_inj1 : ∀ l i j,
  permut_seq l
  → S i < length l
  → S j < length l
  → nth i (sub_canon_permut_list l) 0 = nth j (sub_canon_permut_list l) 0
  → i = j.
Proof.
intros * Hp Hin Hjn Hij.
apply permut_seq_iff in Hp.
destruct Hp as (Hvn, Hn).
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
    apply (NoDup_nat _ Hn); [ easy | easy | ].
    cbn; flia Hai Haj Hij.
  }
  apply Nat.nlt_ge in Haj.
  rewrite Nat.sub_0_r in Hij.
  apply Nat.succ_lt_mono in Hjn.
  specialize (NoDup_nat _ Hn 0 (S j) (Nat.lt_0_succ _) Hjn) as H1.
  cbn in H1.
  replace (nth j l 0) with a in H1 by flia Hai Haj Hij.
  now specialize (H1 eq_refl).
}
apply Nat.nlt_ge in Hai.
rewrite Nat.sub_0_r in Hij.
destruct (lt_dec a (nth j l 0)) as [Haj| Haj]. {
  apply Nat.succ_lt_mono in Hin.
  specialize (NoDup_nat _ Hn (S i) 0 Hin (Nat.lt_0_succ _)) as H1.
  cbn in H1.
  replace (nth i l 0) with a in H1 by flia Hai Haj Hij.
  now specialize (H1 eq_refl).
}
rewrite Nat.sub_0_r in Hij.
apply Nat.succ_inj.
apply Nat.succ_lt_mono in Hin, Hjn.
now apply (NoDup_nat _ Hn).
Qed.

Theorem sub_canon_permut_list_length : ∀ l,
  length (sub_canon_permut_list l) = length l - 1.
Proof.
intros.
destruct l as [| a]; [ easy | ].
now cbn; rewrite map_length, Nat.sub_0_r.
Qed.

Theorem canon_sym_gr_list_inv_ub : ∀ n l,
  permut_seq_with_len n l
  → canon_sym_gr_list_inv n l < n!.
Proof.
intros * (Hp, Hln).
apply permut_seq_iff in Hp.
destruct Hp as (Hvn, Hn).
revert l Hvn Hn Hln.
induction n; intros; cbn; [ easy | ].
rewrite Nat.add_comm.
apply Nat.add_lt_le_mono. {
  apply IHn. {
    intros i Hi.
    apply (In_nth _ _ 0) in Hi.
    destruct Hi as (j & Hj & Hji).
    rewrite <- Hji.
    rewrite sub_canon_permut_list_length in Hj |-*.
    apply sub_canon_permut_list_elem_ub; [ | flia Hj ].
    now apply permut_seq_iff.
  } {
    apply nat_NoDup.
    intros i j Hi Hj.
    rewrite sub_canon_permut_list_length in Hi, Hj.
    apply sub_canon_sym_gr_elem_inj1; [ | flia Hi | flia Hj ].
    now apply permut_seq_iff.
  }
  now rewrite sub_canon_permut_list_length, Hln, Nat_sub_succ_1.
}
apply Nat.mul_le_mono_r.
specialize (Hvn (hd 0 l)).
assert (H : hd 0 l ∈ l) by now apply List_hd_in; rewrite Hln.
specialize (Hvn H); clear H.
rewrite Hln in Hvn.
now apply Nat.succ_le_mono in Hvn.
Qed.

Theorem sub_canon_permut_list_permut_seq_with_len : ∀ l,
  permut_seq l
  → permut_seq (sub_canon_permut_list l).
Proof.
intros * Hl.
apply permut_seq_iff.
split. {
  intros i Hi.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (j & Hj & Hji).
  rewrite <- Hji.
  rewrite sub_canon_permut_list_length in Hj |-*.
  apply sub_canon_permut_list_elem_ub; [ easy | flia Hj ].
} {
  apply nat_NoDup.
  intros i j Hi Hj Hij.
  rewrite sub_canon_permut_list_length in Hi, Hj.
  apply sub_canon_sym_gr_elem_inj1 in Hij; [ easy | easy | | ]. {
    flia Hi.
  } {
    flia Hj.
  }
}
Qed.

Theorem canon_sym_gr_list_canon_sym_gr_list_inv : ∀ n l,
  permut_seq_with_len n l
  → canon_sym_gr_list n (canon_sym_gr_list_inv n l) = l.
Proof.
intros * (Hp, Hln).
apply permut_seq_iff in Hp.
destruct Hp as (Hvn, Hn).
revert l Hvn Hn Hln.
induction n; intros; [ now apply length_zero_iff_nil in Hln | cbn ].
destruct l as [| a]; [ easy | ].
f_equal. {
  cbn - [ sub_canon_permut_list ].
  rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
  rewrite <- Nat.add_0_r; f_equal.
  apply Nat.div_small.
  apply canon_sym_gr_list_inv_ub.
  split. {
    apply sub_canon_permut_list_permut_seq_with_len.
    now apply permut_seq_iff.
  } {
    cbn; rewrite map_length.
    now cbn in Hln; apply Nat.succ_inj in Hln.
  }
} {
  cbn in Hln.
  apply Nat.succ_inj in Hln.
  rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
  rewrite Nat_mod_add_l_mul_r; [ | apply fact_neq_0 ].
  rewrite Nat.mod_small. 2: {
    apply canon_sym_gr_list_inv_ub.
    split. {
      apply sub_canon_permut_list_permut_seq_with_len.
      now apply permut_seq_iff.
    } {
      rewrite sub_canon_permut_list_length; cbn.
      now rewrite Hln, Nat.sub_0_r.
    }
  }
  rewrite IHn; cycle 1. {
    intros i Hi.
    apply (In_nth _ _ 0) in Hi.
    destruct Hi as (j & Hj & Hji).
    rewrite <- Hji.
    apply permut_seq_ub; [ | now apply nth_In ].
    apply sub_canon_permut_list_permut_seq_with_len.
    now apply permut_seq_iff.
  } {
    apply nat_NoDup.
    intros i j Hi Hj.
    rewrite sub_canon_permut_list_length in Hi, Hj.
    cbn in Hi, Hj.
    rewrite Nat.sub_0_r in Hi, Hj.
    apply sub_canon_sym_gr_elem_inj1; [ | cbn; flia Hi | cbn; flia Hj ].
    now apply permut_seq_iff.
  } {
    rewrite sub_canon_permut_list_length; cbn.
    now rewrite Nat.sub_0_r.
  }
  cbn - [ sub_canon_permut_list ].
  unfold succ_when_ge.
  remember (canon_sym_gr_list_inv _ _) as x.
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
    apply canon_sym_gr_list_inv_ub.
    split; [ | now cbn; rewrite map_length ].
    apply sub_canon_permut_list_permut_seq_with_len.
    now apply permut_seq_iff.
  }
  apply Nat.nlt_ge in Hai.
  rewrite Nat.sub_0_r.
  rewrite Nat.div_small. 2: {
    apply canon_sym_gr_list_inv_ub.
    split. {
      apply sub_canon_permut_list_permut_seq_with_len.
      now apply permut_seq_iff.
    } {
      rewrite sub_canon_permut_list_length; cbn; rewrite Hln.
      apply Nat.sub_0_r.
    }
  }
  rewrite Nat.add_0_r, if_leb_le_dec.
  destruct (le_dec _ _) as [H1| H1]; [ | apply Nat.add_0_r ].
  exfalso.
  apply Nat.le_antisymm in H1; [ symmetry in H1 | easy ].
  specialize (NoDup_nat _ Hn 0 (S i) (Nat.lt_0_succ _)) as H2.
  assert (H : S i < length (a :: l)) by (cbn; flia Hi).
  now specialize (H2 H H1); clear H.
}
Qed.

Theorem canon_sym_gr_list_permut_seq : ∀ n k,
  k < n!
  → permut_seq (canon_sym_gr_list n k).
Proof.
intros * Hkn.
apply permut_seq_iff.
split. {
  intros i Hi.
  rewrite canon_sym_gr_list_length.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (j & Hj & Hji).
  rewrite canon_sym_gr_list_length in Hj.
  rewrite <- Hji.
  now apply canon_sym_gr_list_ub.
} {
  apply nat_NoDup.
  intros * Hi Hj Hij.
  rewrite canon_sym_gr_list_length in Hi, Hj.
  now apply nth_canon_sym_gr_list_inj1 in Hij.
}
Qed.

Theorem canon_sym_gr_list_permut_seq_with_len : ∀ n k,
  k < n!
  → permut_seq_with_len n (canon_sym_gr_list n k).
Proof.
intros * Hkn.
split; [ now apply canon_sym_gr_list_permut_seq | ].
apply canon_sym_gr_list_length.
Qed.

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

Theorem canon_sym_gr_list_inv_canon_sym_gr_list : ∀ n k,
  k < n!
  → canon_sym_gr_list_inv n (canon_sym_gr_list n k) = k.
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
rewrite <- (IHn (k mod fact n)) at 1; [ | easy ].
f_equal.
apply canon_sym_gr_sub_canon_permut_list.
Qed.

Theorem rank_in_sym_gr_of_rank_in_canon_sym_gr_prop : ∀ n sg,
  is_sym_gr_list n sg
  → ∀ k : fin_t n!,
      (sym_gr_inv sg
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
now apply sym_gr_inv_lt with (n := n).
Qed.

Theorem rank_in_canon_sym_gr_of_rank_in_sym_gr_prop : ∀ n sg,
  is_sym_gr_list n sg
  → ∀ k : fin_t (length sg),
      (canon_sym_gr_list_inv n (nth (proj1_sig k) sg []) <? n!)
      = true.
Proof.
intros * Hsg k.
destruct Hsg as (Hsg & Hinj & Hsurj).
apply Nat.ltb_lt.
destruct k as (k, pk); cbn.
apply Nat.ltb_lt in pk.
specialize (Hsg k pk).
now apply canon_sym_gr_list_inv_ub.
Qed.

Definition rank_in_sym_gr_of_rank_in_canon_sym_gr n sg
    (Hsg : is_sym_gr_list n sg) (k : fin_t n!) : fin_t (length sg) :=
  exist (λ a : nat, (a <? length sg) = true)
    (sym_gr_inv sg
      (nth (proj1_sig k) (canon_sym_gr_list_list n) []))
    (rank_in_sym_gr_of_rank_in_canon_sym_gr_prop Hsg k).

Definition rank_in_canon_sym_gr_of_rank_in_sym_gr  n sg
    (Hsg : is_sym_gr_list n sg) (k : fin_t (length sg)) : fin_t n! :=
  exist (λ a : nat, (a <? n!) = true)
    (canon_sym_gr_list_inv n (nth (proj1_sig k) sg []))
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
  assert (p : sym_gr_inv sg [] = 0). {
    unfold sym_gr_inv, unsome; cbn.
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
   sym_gr_inv sg
     (nth (canon_sym_gr_list_inv n (nth k sg []))
        (canon_sym_gr_list_list n) []) = k). {
  apply Nat.ltb_lt in pk.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  specialize (Hsg k pk) as H1.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply canon_sym_gr_list_inv_ub.
  }
  rewrite seq_nth; [ | now apply canon_sym_gr_list_inv_ub ].
  rewrite Nat.add_0_l.
  rewrite canon_sym_gr_list_canon_sym_gr_list_inv; [ | easy ].
  now apply sym_gr_inv_list_el with (n := n).
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
   canon_sym_gr_list_inv n
     (nth (sym_gr_inv sg (nth k (canon_sym_gr_list_list n) []))
        sg []) = k). {
  specialize (proj1 (Nat.ltb_lt _ _) pk) as Hkn.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ cbn | easy ].
  rewrite (@nth_sym_gr_inv_sym_gr _ _ n); cycle 1. {
    easy.
  } {
    now apply canon_sym_gr_list_permut_seq_with_len.
  }
  now apply canon_sym_gr_list_inv_canon_sym_gr_list.
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

Theorem canon_sym_gr_list_inj : ∀ n i j,
  i < fact n
  → j < fact n
  → canon_sym_gr_list n i = canon_sym_gr_list n j
  → i = j.
Proof.
intros * Hi Hj Hij.
apply (f_equal (@canon_sym_gr_list_inv n)) in Hij.
rewrite canon_sym_gr_list_inv_canon_sym_gr_list in Hij; [ | easy ].
rewrite canon_sym_gr_list_inv_canon_sym_gr_list in Hij; [ | easy ].
easy.
Qed.

Theorem rank_of_permut_in_canon_gr_list_inj : ∀ n la lb,
  permut_seq_with_len n la
  → permut_seq_with_len n lb
  → canon_sym_gr_list_inv n la =
    canon_sym_gr_list_inv n lb
  → la = lb.
Proof.
intros * (Hla, Han) (Hlb, Hbn) Hrr.
apply (f_equal (canon_sym_gr_list n)) in Hrr.
rewrite canon_sym_gr_list_canon_sym_gr_list_inv in Hrr; [ | easy ].
rewrite canon_sym_gr_list_canon_sym_gr_list_inv in Hrr; [ | easy ].
easy.
Qed.

Theorem isort_rank_inj : ∀ l,
  permut_seq l
  → ∀ i j, i < length l → j < length l
  → nth i (isort_rank Nat.leb l) 0 = nth j (isort_rank Nat.leb l) 0
  → i = j.
Proof.
intros * Hp * Hi Hj Hij.
rewrite <- (isort_rank_length Nat.leb) in Hi, Hj.
now apply (NoDup_nat _ (NoDup_isort_rank _ _)) in Hij.
Qed.

Theorem isort_rank_leb_seq : ∀ n, isort_rank Nat.leb (seq 0 n) = seq 0 n.
Proof.
intros.
rewrite (eq_sorted_isort_rank_seq Nat_leb_trans). {
  now rewrite seq_length.
}
apply sorted_nat_ltb_leb_incl.
apply sorted_seq.
Qed.

Theorem isort_rank_ltb_seq : ∀ n, isort_rank Nat.ltb (seq 0 n) = seq 0 n.
Proof.
intros.
rewrite (eq_sorted_isort_rank_seq Nat_ltb_trans). {
  now rewrite seq_length.
}
apply sorted_seq.
Qed.

(* to be completed
   and put in SortRank.v
   and prove isort_rank_permut_seq_with_len with that
Theorem permutation_isort_rank : ∀ A (rel : A → _) la,
  permutation Nat.eqb (isort_rank rel la) (seq 0 (length la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn - [ nth seq ].
Search (permutation _ (isort_insert _ _ _)).
Search (permutation _ (isort_rank_insert _ _ _ _)).
Print isort_rank_insert.
...
intros.
apply (permut_if_isort Nat.ltb Nat.eqb_eq).
rewrite isort_isort_rank with (d := 0).
rewrite isort_isort_rank with (d := 0).
apply List_eq_iff.
do 2 rewrite map_length.
do 3 rewrite isort_rank_length.
rewrite seq_length.
split; [ easy | ].
intros d i.
destruct (lt_dec i (length la)) as [Hila| Hila]. 2: {
  apply Nat.nlt_ge in Hila.
  rewrite nth_overflow. 2: {
    rewrite map_length.
    now do 2 rewrite isort_rank_length.
  }
  rewrite nth_overflow. 2: {
    now rewrite map_length, isort_rank_length, seq_length.
  }
  easy.
}
rewrite (List_map_nth' 0); [ | now do 2 rewrite isort_rank_length ].
rewrite (List_map_nth' 0); [ | now rewrite isort_rank_length, seq_length ].
rewrite seq_nth. 2: {
  specialize (isort_rank_ub Nat.ltb) as H1.
  specialize (H1 (seq 0 (length la)) i).
  rewrite seq_length in H1.
  apply H1; intros H2.
  apply List_seq_eq_nil in H2.
  now rewrite H2 in Hila.
}
cbn.
(**)
Compute (
let la := [3;9;7;9;5;5;2] in
let rel := Nat.ltb in
map (λ i,
  nth (nth i (isort_rank Nat.ltb (isort_rank rel la)) 0) (isort_rank rel la) 0 =
  nth i (isort_rank Nat.ltb (seq 0 (length la))) 0) (seq 0 (length la))
).
(**)
rewrite isort_rank_ltb_seq.
rewrite seq_nth; [ | easy ].
Compute (
let la := [3;9;7;9;5;5;2] in
let rel := λ i j, false in
map (λ i,
  nth (nth i (isort_rank Nat.ltb (isort_rank rel la)) 0) (isort_rank rel la) 0 = 0 + i
) (seq 0 (length la))
).
remember (isort_rank rel la) as lb eqn:Hlb.
assert (H : i < length lb) by now rewrite Hlb, isort_rank_length.
assert (Hp : permutation Nat.ltb lb (seq 0 (length lb))).
rewrite Hlb.
rewrite isort_rank_length.
Search (permutation _ _ (isort_rank _ _)).
Search (permutation _ (isort_rank _ _)).
...
clear d la Hila Hlb.
rename lb into la; rename H into Hla; cbn.
Search (nth _ (isort_rank _ _)).
Compute (
map (λ la,
map (λ i,
  nth (nth i (isort_rank Nat.ltb la) 0) la 0 = i
) (seq 0 (length la))
) (all_permut (seq 0 4))
).
rewrite nth_nth_isort_rank; [ | now rewrite isort_rank_length ].
Search (nth _ (isort _ _)).
Search (isort _ _ = seq _ _).
rewrite permut_isort_leb.
...
rewrite isort_isort_rank with (d := 0).
rewrite (List_map_nth' 0); [ | now do 2 rewrite isort_rank_length ].
...
Compute (
let la := [3;9;7;9;5;5;2] in
let rel := λ i j, Nat.leb j i in
map (λ i,
  nth i (isort Nat.ltb (isort_rank rel la)) 0 = 0 + i
) (seq 0 (length la))
).
rewrite isort_isort_rank with (d := 0).
rewrite (List_map_nth' 0); [ | now do 2 rewrite isort_rank_length ].
rewrite nth_nth_isort_rank.
  ============================
  nth i (isort Nat.ltb (isort_rank rel la)) 0 = 0 + i

...
rewrite nth_nth_isort_rank.
...
rewrite isort_rank_seq.
...
rewrite isort_rank_seq.
now rewrite seq_nth.
...
intros.
remember (length la) as len eqn:Hlen; symmetry in Hlen.
revert la Hlen.
induction len; intros; [ now apply length_zero_iff_nil in Hlen; subst la | ].
rewrite seq_S; cbn.
eapply (permutation_trans Nat.eqb_eq). 2: {
  apply (permutation_cons_append Nat.eqb_eq).
}
apply (permutation_sym Nat.eqb_eq).
apply permutation_cons_l_iff.
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (pigeonhole_list len (isort_rank rel la)) as H2.
  rewrite isort_rank_length, Hlen in H2.
  assert (H : len < S len) by easy.
  specialize (H2 H); clear H.
  assert (H : ∀ i, i ∈ isort_rank rel la → i < len). {
    intros i Hi.
    destruct (Nat.eq_dec i len) as [Hil| Hil]. {
      subst i; apply H1 in Hi.
      now rewrite Nat.eqb_refl in Hi.
    }
    apply in_isort_rank in Hi; rewrite Hlen in Hi.
    flia Hi Hil.
  }
  specialize (H2 H); clear H.
  remember (pigeonhole_comp_list (isort_rank rel la)) as xx eqn:Hxx.
  symmetry in Hxx.
  destruct xx as (i, j).
  specialize (H2 _ _ eq_refl).
  destruct H2 as (Hil & Hjl & H & Hij).
  apply H; clear H.
  rewrite <- Hlen in Hil, Hjl.
  apply (NoDup_nth (isort_rank rel la) 0); [ | | | easy ]. {
    apply NoDup_isort_rank.
  } {
    now rewrite isort_rank_length.
  } {
    now rewrite isort_rank_length.
  }
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Haft).
apply Nat.eqb_eq in H; subst x.
Check permutation_elt.
...
  destruct la as [| a]; [ easy | ].
  cbn in Hlen.
...
  assert (H : len ∈ isort_rank rel la). {
Search (_ ∈ isort_rank _ _).
...
Check permut_seq_iff.
Print permut_seq.
...
*)

Theorem isort_rank_permut_seq_with_len : ∀ A (rel : A → _) n l,
  length l = n
  → permut_seq_with_len n (isort_rank rel l).
Proof.
intros.
subst n.
split. {
  apply permut_seq_iff.
  split. {
    intros i Hi.
    rewrite isort_rank_length.
    apply (In_nth _ _ 0) in Hi.
    rewrite isort_rank_length in Hi.
    destruct Hi as (ia & Hial & Hia).
    rewrite <- Hia.
    apply isort_rank_ub.
    now intros H; rewrite H in Hial.
  } {
    apply NoDup_isort_rank.
  }
}
apply isort_rank_length.
Qed.

Arguments isort_rank_permut_seq_with_len {A} rel n%nat [l]%list.

Theorem isort_rank_permut_seq : ∀ A (rel : A → _) l,
  permut_seq (isort_rank rel l).
Proof.
intros.
now apply (isort_rank_permut_seq_with_len _ (length l)).
Qed.

Theorem permutation_isort_rank : ∀ A (rel : A → _) la,
  permutation Nat.eqb (isort_rank rel la) (seq 0 (length la)).
Proof.
intros.
specialize (isort_rank_permut_seq rel la) as H1.
unfold permut_seq in H1.
now rewrite isort_rank_length in H1.
Qed.

(* *)

Theorem nth_canon_sym_gr_list_ub : ∀ d i n k,
  i < n
  → k < n!
  → nth i (canon_sym_gr_list n k) d < n.
Proof.
intros * Hin Hkn.
revert i k Hin Hkn.
induction n; intros; [ easy | cbn ].
destruct i. {
  apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
  rewrite Nat.mul_comm.
  now rewrite <- Nat_fact_succ.
}
apply Nat.succ_lt_mono in Hin.
rewrite (List_map_nth' 0); [ | now rewrite canon_sym_gr_list_length ].
unfold succ_when_ge.
specialize (IHn i (k mod n!) Hin) as H1.
assert (H : k mod n! < n!) by apply Nat.mod_upper_bound, fact_neq_0.
specialize (H1 H); clear H.
rewrite <- Nat.add_1_l, Nat.add_comm.
rewrite nth_indep with (d' := 0) in H1. 2: {
  now rewrite canon_sym_gr_list_length.
}
apply Nat.add_le_lt_mono; [ | easy ].
apply Nat_b2n_upper_bound.
Qed.

Theorem permutation_in_all_permut : ∀ la lb,
  permutation eqb la lb → la ∈ all_permut lb.
Proof.
intros * Hpab.
destruct lb as [| d]. {
  apply permutation_nil_r in Hpab; subst la.
  now left.
}
unfold all_permut.
remember (d :: lb) as l eqn:Hl.
clear lb Hl.
rename l into lb.
erewrite map_ext_in. 2: {
  intros lc Hlc.
  erewrite map_ext_in. 2: {
    intros i Hi.
    rewrite nth_indep with (d' := 0). 2: {
      apply in_map_iff in Hlc.
      destruct Hlc as (b & H & Hlc); subst lc.
      apply (In_nth _ _ 0) in Hi.
      rewrite canon_sym_gr_list_length in Hi.
      destruct Hi as (j & Hjb & Hi).
      subst i.
      apply in_seq in Hlc.
      now apply nth_canon_sym_gr_list_ub.
    }
    easy.
  }
  easy.
}
clear d.
apply in_map_iff.
unfold canon_sym_gr_list_list.
exists (permutation_assoc eqb la lb).
split. {
  symmetry.
  now apply (map_permutation_assoc Nat.eqb_eq).
}
apply in_map_iff.
remember (length lb) as n eqn:Hlb; symmetry in Hlb.
remember (permutation_assoc eqb la lb) as p eqn:Hp.
exists (canon_sym_gr_list_inv n p).
rewrite canon_sym_gr_list_canon_sym_gr_list_inv. 2: {
  subst p.
  split; [ now apply (perm_assoc_permut_seq Nat.eqb_eq) | ].
  generalize Hpab; intros H.
  apply permutation_length in H.
  rewrite <- Hlb, <- H.
  now apply (permutation_assoc_length Nat.eqb_eq).
}
split; [ easy | ].
apply in_seq.
split; [ easy | ].
apply canon_sym_gr_list_inv_ub.
rewrite Hp.
split; [ now apply (perm_assoc_permut_seq Nat.eqb_eq) | ].
generalize Hpab; intros H.
apply permutation_length in H.
rewrite <- Hlb, <- H.
now apply (permutation_assoc_length Nat.eqb_eq).
Qed.

Theorem in_all_permut_permutation : ∀ la lb,
  la ∈ all_permut lb → permutation eqb la lb.
Proof.
intros * Hla.
revert la Hla.
induction lb as [| b]; intros. {
  destruct la; [ easy | now destruct Hla ].
}
cbn - [ canon_sym_gr_list nth fact ] in Hla.
apply in_map_iff in Hla.
destruct Hla as (lc & Hla & H).
unfold canon_sym_gr_list_list in H.
apply in_map_iff in H.
destruct H as (d & Hlc & Hd).
apply in_seq in Hd.
destruct Hd as (_, Hd); rewrite Nat.add_0_l in Hd.
cbn in Hlc.
remember (d / (length lb)!) as a eqn:Ha.
remember (map (succ_when_ge a) _) as le eqn:Hle.
subst lc; rename le into lc.
cbn - [ nth ] in Hla.
destruct (lt_dec d (length lb)!) as [Hdb| Hdb]. {
  rewrite Nat.div_small in Ha; [ | easy ].
  rewrite Nat.mod_small in Hle; [ | easy ].
  subst a.
  rewrite List_nth_0_cons in Hla.
  subst la.
  apply permutation_skip; [ now intros a; apply Nat.eqb_eq | ].
  apply IHlb.
  unfold succ_when_ge in Hle.
  erewrite map_ext_in in Hle. 2: {
    intros a Ha.
    now cbn; rewrite Nat.add_1_r.
  }
  subst lc.
  rewrite map_map.
  erewrite map_ext_in; [ | now intros; cbn ].
  apply permutation_in_all_permut.
  apply (permutation_sym Nat.eqb_eq).
  specialize (permutation_refl Nat.eqb_eq lb) as H.
  rewrite (map_permutation_assoc Nat.eqb_eq b H) at 1.
  apply (permutation_map Nat.eqb_eq Nat.eqb_eq); clear H.
  eapply (permutation_trans Nat.eqb_eq). {
    apply (permutation_permutation_assoc Nat.eqb_eq).
    apply (permutation_refl Nat.eqb_eq).
  }
  specialize (canon_sym_gr_list_length d (length lb)) as H1.
  rewrite <- H1 at 1.
  apply (permutation_sym Nat.eqb_eq).
  now apply canon_sym_gr_list_permut_seq.
}
apply Nat.nlt_ge in Hdb.
rename a into i.
apply (permutation_sym Nat.eqb_eq).
apply permutation_cons_l_iff.
remember (extract (Nat.eqb b) la) as lxl eqn:Hlxl.
symmetry in Hlxl.
remember (length lb) as n eqn:Hn.
assert (Hdm : d mod n! < n!) by (apply Nat.mod_upper_bound, fact_neq_0).
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  rewrite <- Hla in H1.
  destruct i. {
    rewrite List_nth_0_cons in H1.
    specialize (H1 _ (or_introl eq_refl)).
    now rewrite Nat.eqb_refl in H1.
  }
  rewrite List_nth_succ_cons in H1.
  destruct (lt_dec i n) as [Hilb| Hilb]. 2: {
    apply Nat.nlt_ge in Hilb.
    specialize (H1 b).
    rewrite nth_overflow in H1; [ | now rewrite <- Hn ].
    specialize (H1 (or_introl eq_refl)).
    now rewrite (equality_refl Nat.eqb_eq) in H1.
  }
  specialize (H1 b).
  assert (H : b ∈ map (λ i, nth i (b :: lb) b) lc). {
    apply in_map_iff.
    exists 0.
    split; [ easy | ].
    rewrite Hle.
    apply in_map_iff.
    exists 0.
    unfold succ_when_ge.
    split; [ easy | ].
    specialize canon_sym_gr_list_permut_seq as H2.
    specialize (H2 n (d mod n!) Hdm).
    specialize permut_list_surj as H3.
    specialize (H3 0 _ H2).
    rewrite canon_sym_gr_list_length in H3.
    assert (H : 0 < n) by flia Hilb.
    specialize (H3 H); clear H.
    destruct H3 as (j & Hjn & Hj).
    rewrite <- Hj.
    apply nth_In.
    now rewrite canon_sym_gr_list_length.
  }
  specialize (H1 (or_intror H)).
  now rewrite (equality_refl Nat.eqb_eq) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Nat.eqb_eq in H; subst x.
apply (permutation_sym Nat.eqb_eq).
rewrite <- Hla in Hlb.
destruct i. {
  symmetry in Ha.
  apply Nat.div_small_iff in Ha; [ | apply fact_neq_0 ].
  now apply Nat.nle_gt in Ha.
}
rewrite List_nth_succ_cons in Hlb.
clear la Hla.
assert (Hin : i < n). {
  apply Nat.succ_lt_mono.
  rewrite Ha.
  apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
  now rewrite Nat.mul_comm, <- Nat_fact_succ.
}
subst lc.
rewrite nth_indep with (d' := 0) in Hlb; [ | now rewrite <- Hn ].
erewrite map_ext_in in Hlb. 2: {
  intros j Hj.
  apply in_map_iff in Hj.
  destruct Hj as (k & Hk & Hj).
  rewrite nth_indep with (d' := 0). 2: {
    rewrite <- Hk.
    unfold succ_when_ge.
    apply in_canon_sym_gr_list in Hj; [ | easy ].
    cbn - [ "<=?" ].
    rewrite Nat.add_comm.
    unfold Nat.b2n.
    destruct (S i <=? k); flia Hn Hj.
  }
  easy.
}
rewrite map_map in Hlb.
erewrite map_ext_in in Hlb. 2: {
  intros j Hj.
  replace (nth _ _ _) with (nth j (b :: butn i lb) 0). 2: {
    destruct j; [ easy | cbn ].
    now rewrite nth_butn.
  }
  easy.
}
apply (permutation_cons_inv Nat.eqb_eq) with (a := b).
eapply (permutation_trans Nat.eqb_eq). {
  apply (permutation_middle Nat.eqb_eq).
}
rewrite <- Hlb.
assert (H : lb = firstn i lb ++ nth i lb 0 :: skipn (S i) lb). {
  rewrite <- (firstn_skipn i lb) at 1.
  f_equal.
  apply List_skipn_is_cons.
  now rewrite <- Hn.
}
apply (permutation_sym Nat.eqb_eq).
rewrite H at 1; clear H.
apply (permutation_sym Nat.eqb_eq).
rewrite app_comm_cons.
eapply (permutation_trans Nat.eqb_eq). 2: {
  apply (permutation_middle Nat.eqb_eq).
}
apply permutation_skip; [ now intros a; apply Nat.eqb_eq | ].
cbn - [ nth skipn ].
rewrite fold_butn.
rewrite List_map_nth_seq with (d := 0).
apply (permutation_map Nat.eqb_eq Nat.eqb_eq).
cbn - [ seq ].
rewrite butn_length.
generalize Hin; intros H.
apply Nat.ltb_lt in H.
rewrite Hn in H; rewrite H; clear H.
rewrite <- Hn.
rewrite <- Nat.sub_succ_l; [ | cbn; flia Hin ].
rewrite Nat_sub_succ_1.
rewrite Hn.
eapply (permutation_trans Nat.eqb_eq). {
  apply canon_sym_gr_list_permut_seq.
  apply Nat.mod_upper_bound, fact_neq_0.
}
rewrite canon_sym_gr_list_length.
apply (permutation_refl Nat.eqb_eq).
Qed.

Theorem in_all_permut_iff : ∀ la lb,
  la ∈ all_permut lb ↔ isort Nat.leb la = isort Nat.leb lb.
Proof.
intros.
split; intros Hab. {
  apply in_all_permut_permutation in Hab.
  apply (isort_when_permuted Nat.eqb_eq); [ | | | easy ]. {
    apply Nat_leb_antisym.
  } {
    apply Nat_leb_trans.
  } {
    apply Nat_leb_total_relation.
  }
} {
  apply permutation_in_all_permut.
  now apply (permut_if_isort Nat.leb Nat.eqb_eq).
}
Qed.

Theorem NoDup_all_permut : ∀ A (la : list A),
  NoDup la → NoDup (all_permut la).
Proof.
intros * Hnd.
destruct la as [| d]. {
  constructor; [ easy | constructor ].
}
unfold all_permut.
remember (d :: la) as lb eqn:Hlb.
clear la Hlb.
rename lb into la.
apply (NoDup_map_iff []).
unfold canon_sym_gr_list_list.
rewrite List_map_seq_length.
intros * Hi Hj Hij.
rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
rewrite seq_nth in Hij; [ | easy ].
rewrite seq_nth in Hij; [ | easy ].
do 2 rewrite Nat.add_0_l in Hij.
apply List_eq_iff in Hij.
destruct Hij as (_, Hij).
specialize (Hij d).
remember (∀ k, _) as x in Hij; subst x.
assert
  (H : ∀ k,
   nth (nth k (canon_sym_gr_list (length la) i) 0) la d =
   nth (nth k (canon_sym_gr_list (length la) j) 0) la d). {
  intros.
  specialize (Hij k).
  destruct (lt_dec k (length la)) as [Hka| Hka]. 2: {
    apply Nat.nlt_ge in Hka.
    rewrite nth_overflow with (n := k). 2: {
      now rewrite canon_sym_gr_list_length.
    }
    rewrite nth_overflow with (n := k). 2: {
      now rewrite canon_sym_gr_list_length.
    }
    easy.
  }
  rewrite (List_map_nth' 0) in Hij. 2: {
    now rewrite canon_sym_gr_list_length.
  }
  rewrite (List_map_nth' 0) in Hij. 2: {
    now rewrite canon_sym_gr_list_length.
  }
  easy.
}
clear Hij; rename H into Hij.
apply nth_canon_sym_gr_list_inj2 with (n := length la); [ easy | easy | ].
intros k Hk.
specialize (Hij k).
remember (nth k (canon_sym_gr_list (length la) i) 0) as i' eqn:Hi'.
remember (nth k (canon_sym_gr_list (length la) j) 0) as j' eqn:Hj'.
specialize (proj1 (NoDup_nth la d) Hnd) as H1.
apply H1; [ | | easy ]. {
  now rewrite Hi'; apply canon_sym_gr_list_ub.
} {
  now rewrite Hj'; apply canon_sym_gr_list_ub.
}
Qed.

Arguments nth_canon_sym_gr_list_inj2 n%nat [i j]%nat.
