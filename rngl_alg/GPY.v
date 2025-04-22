(* preparation of GPY (Goldston–Pintz–Yıldırım sieve) *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Misc.
Require Import RingLike.RingLike.
Require Import RingLike.IterAdd.
Require Import QG.

Section a.

Instance roq : ring_like_op QG := QG_ring_like_op.
Instance roc : ring_like_prop QG := QG_ring_like_prop.

Definition QG_of_nat n : QG := rngl_of_nat n.

Theorem QG_of_nat_succ : ∀ n, QG_of_nat (S n) = (1 + QG_of_nat n)%QG.
Proof. easy. Qed.

Theorem harmonic_sum_bound :
  ∀ n, 2 ≤ n → (∑ (k = 1, n), 1 / QG_of_nat k ≤ QG_of_nat n)%L.
Proof.
assert (Hon : rngl_has_1 QG = true) by easy.
assert (Hop : rngl_has_opp QG = true) by easy.
assert (Hiv : rngl_has_inv QG = true) by easy.
assert (Hor : rngl_is_ordered QG = true) by easy.
assert (Hc1 : rngl_characteristic QG ≠ 1) by easy.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H1n.
progress unfold QG_of_nat.
induction n; [ now rewrite rngl_summation_empty | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ flia Hnz H1n | ].
rewrite rngl_summation_split_last; [ | flia ].
rewrite (rngl_summation_shift 1); [ | flia Hnz ].
do 2 rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat.add_comm, Nat.add_sub.
}
cbn - [ rngl_zero rngl_add Nat.log2 rngl_le rngl_div rngl_of_nat ].
replace ((1%QG + 1%QG)%L) with 2%L by easy.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]; [ now subst n | ].
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_r Hop Hor).
  apply IHn.
  flia Hnz Hn1.
}
rewrite rngl_of_nat_succ.
rewrite rngl_add_comm.
apply (rngl_add_le_mono_r Hop Hor).
replace 1%QG with 1%L by easy.
Time apply (rngl_le_div_l Hon Hop Hiv Hor). {
  apply (rngl_add_pos_nonneg Hor).
  apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
  apply (rngl_of_nat_nonneg Hon Hos Hor).
}
rewrite rngl_mul_add_distr_l.
do 2 rewrite (rngl_mul_1_l Hon).
apply (rngl_le_add_r Hor).
apply (rngl_of_nat_nonneg Hon Hos Hor).
Qed.

Theorem harmonic_sum_after_2_pow_bound :
  ∀ n k, n ≤ k → (∑ (i = 1, n), 1 / rngl_of_nat (k + i) ≤ 1)%L.
Proof.
assert (Hon : rngl_has_1 QG = true) by easy.
assert (Hop : rngl_has_opp QG = true) by easy.
assert (Hiv : rngl_has_inv QG = true) by easy.
assert (Hc1 : rngl_characteristic QG ≠ 1) by easy.
assert (Hor : rngl_is_ordered QG = true) by easy.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hnk.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply (rngl_le_trans Hor _ (∑ (i = 1, n), 1 / rngl_of_nat k)). {
  apply (rngl_summation_le_compat Hor).
  intros i Hi.
  Time apply (rngl_div_le_mono_pos_l Hop Hiv Hor Hii). {
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
  }
  apply (rngl_le_inv_inv Hon Hop Hiv Hor). {
    apply (rngl_lt_iff Hor).
    split; [ apply (rngl_of_nat_nonneg Hon Hos Hor) | ].
    intros H; symmetry in H.
    apply (eq_rngl_of_nat_0 Hon) in H; [ | easy ].
    flia Hi H.
  } {
    apply (rngl_lt_iff Hor).
    split; [ apply (rngl_of_nat_nonneg Hon Hos Hor) | ].
    intros H; symmetry in H.
    apply (eq_rngl_of_nat_0 Hon) in H; [ | easy ].
    subst k.
    apply Nat.nlt_ge in Hnk.
    apply Hnk; clear Hnk.
    flia Hi.
  } {
    apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
    apply Nat.le_add_r.
  }
}
rewrite (rngl_summation_const Hos Hon).
rewrite Nat_sub_succ_1.
rewrite (rngl_mul_div_assoc Hiv).
rewrite (rngl_mul_1_r Hon).
apply (rngl_div_le_1 Hon Hop Hiv Hor). {
  intros H.
  apply (eq_rngl_of_nat_0 Hon) in H; [ | easy ].
  subst k.
  apply Nat.nlt_ge in Hnk.
  apply Hnk; clear Hnk.
  now apply Nat.neq_0_lt_0.
}
split; [ apply (rngl_of_nat_nonneg Hon Hos Hor) | ].
now apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
Qed.

(* 1 + 1/2 + 1/3 = (6 + 3 + 2) / 6 = 11/6 *)
(* 2 * log2 3 = 2 ok *)
(* 1 + 1/2 + 1/3 + 1/4 = 11/6 + 1/4 = 22/12 + 3/12 = 25/12 *)
(* 2 * log2 4 = 4 ok *)

(*
Theorem harmonic_sum_log2_bound :
  ∀ n, 2 ≤ n → (∑ (k = 1, n), 1 / QG_of_nat k ≤ 2 * QG_of_nat (Nat.log2 n))%L.
Proof.
assert (Hon : rngl_has_1 QG = true) by easy.
assert (Hop : rngl_has_opp QG = true) by easy.
assert (Hiv : rngl_has_inv QG = true) by easy.
assert (Hor : rngl_is_ordered QG = true) by easy.
assert (Hc1 : rngl_characteristic QG ≠ 1) by easy.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H1n.
progress unfold QG_of_nat.
specialize (Nat.log2_spec_alt n) as H1.
assert (H : 0 < n) by flia H1n.
specialize (H1 H); clear H.
destruct H1 as (p & Hp & _ & Hpn).
remember (Nat.log2 n) as m eqn:Hm.
subst n.
clear Hm.
rename m into n.
revert p H1n Hpn.
induction n; intros. {
  cbn in H1n.
  apply Nat.lt_1_r in Hpn; subst p.
  flia H1n.
}
cbn - [ rngl_zero rngl_add Nat.log2 rngl_le rngl_div rngl_of_nat ].
rewrite Nat.add_0_r.
rewrite <- Nat.add_assoc.
(* fait chier, marche pas *)
...
eapply (rngl_le_trans Hor). {
  apply IHn.
...
*)

Theorem harmonic_sum_log2_bound_up_to_2_pow :
  ∀ n, 2 ≤ n → (∑ (k = 1, 2^ n), 1 / QG_of_nat k ≤ 2 * QG_of_nat n)%L.
Proof.
assert (Hon : rngl_has_1 QG = true) by easy.
assert (Hop : rngl_has_opp QG = true) by easy.
assert (Hiv : rngl_has_inv QG = true) by easy.
assert (Hor : rngl_is_ordered QG = true) by easy.
assert (Hc1 : rngl_characteristic QG ≠ 1) by easy.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H1n.
progress unfold QG_of_nat.
induction n; [ now rewrite rngl_summation_empty | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ flia Hnz H1n | clear H1n ].
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]; [ now subst n | ].
rewrite Nat.pow_succ_r'.
rewrite Nat_mul_2_l.
rewrite (rngl_summation_split (2 ^ n)); [ | flia ].
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_r Hop Hor).
  apply IHn.
  flia Hnz Hn1.
}
rewrite rngl_of_nat_succ.
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_1_r Hon).
rewrite rngl_add_comm.
apply (rngl_add_le_mono_r Hop Hor).
rewrite (rngl_summation_shift (2 ^ n)). 2: {
  split; [ flia | ].
  apply Nat.add_le_mono_l.
  now apply Nat.pow_lower_bound.
}
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_sub.
apply (rngl_le_trans Hor _ 1); [ | apply (rngl_1_le_2 Hon Hos Hor) ].
now apply harmonic_sum_after_2_pow_bound.
Qed.

Theorem harmonic_sum_log2_bound :
  ∀ n, 2 ≤ n → (∑ (k = 1, n), 1 / QG_of_nat k ≤ 3 * QG_of_nat (Nat.log2 n))%L.
Proof.
assert (Hon : rngl_has_1 QG = true) by easy.
assert (Hop : rngl_has_opp QG = true) by easy.
assert (Hiv : rngl_has_inv QG = true) by easy.
assert (Hor : rngl_is_ordered QG = true) by easy.
assert (Hc1 : rngl_characteristic QG ≠ 1) by easy.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H1n.
progress unfold QG_of_nat.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ flia Hnz H1n | ].
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]; [ subst n; flia H1n | ].
clear H1n.
specialize (Nat.log2_spec_alt n) as H1.
assert (H : 0 < n) by flia Hnz.
specialize (H1 H); clear H.
destruct H1 as (r & Hnr & _ & Hr).
clear Hnz.
remember (Nat.log2 n) as m; clear Heqm.
subst n; rename m into n.
remember (∑ (i = _, _), _)%L as x; subst x.
destruct (Nat.eq_dec r 0) as [Hrz| Hrz]. {
  subst r.
  rewrite Nat.add_0_r.
  rewrite Nat.add_0_r in Hn1.
  destruct (Nat.eq_dec n 1) as [Hne1| Hne1]; [ now subst n | ].
  eapply (rngl_le_trans Hor). {
    apply harmonic_sum_log2_bound_up_to_2_pow.
    destruct n; cbn in Hn1; [ easy | ].
    flia Hne1.
  }
  apply (rngl_mul_le_mono_nonneg_r Hop Hor).
  apply (rngl_of_nat_nonneg Hon Hor Hor). (* what? work with twice Hor *)
  apply (rngl_le_add_r Hor).
  apply (rngl_0_le_1 Hon Hor Hos). (* n'importe quoi, ça marche *)
  (* bug probable dans Rocq *)
}
destruct (Nat.eq_dec r 1) as [Hr1| Hr1]. {
  subst r.
  clear Hrz.
...
}
... ...
rewrite (rngl_summation_split (2 ^ n)); [ | flia ].
rewrite QG_mul_add_distr_r.
rewrite QG_mul_1_l.
rewrite rngl_add_comm.
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_l Hop Hor).
  apply harmonic_sum_log2_bound_up_to_2_pow.
  destruct n. {
    cbn in Hn1, Hr.
    now apply Nat.lt_1_r in Hr; subst r.
  }
  destruct n; [ | flia ].
  cbn in Hr.
  destruct r; [ easy | ].
  destruct r; [ easy | flia Hr ].
}
rewrite rngl_add_comm.
apply QG_add_le_compat; [ apply QG_le_refl | ].
erewrite (rngl_summation_shift (2 ^ n)); [ | flia Hrz Hr1 ].
do 2 rewrite Nat.add_comm, Nat.add_sub.
apply (rngl_le_trans Hor _ 1). 2: {
  rewrite <- rngl_of_nat_1.
  apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
  destruct n; [ | flia ].
  now apply Nat.lt_1_r in Hr; subst r.
}
apply harmonic_sum_after_2_pow_bound.
now apply Nat.lt_le_incl.
...

Theorem harmonic_sum_log2_bound :
  ∀ n, 2 ≤ n → (∑ (k = 1, n), 1 / QG_of_nat k ≤ 2 * QG_of_nat (Nat.log2 n))%L.
Proof.
assert (Hon : rngl_has_1 QG = true) by easy.
assert (Hop : rngl_has_opp QG = true) by easy.
assert (Hiv : rngl_has_inv QG = true) by easy.
assert (Hor : rngl_is_ordered QG = true) by easy.
assert (Hc1 : rngl_characteristic QG ≠ 1) by easy.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H1n.
progress unfold QG_of_nat.
induction n; [ now rewrite rngl_summation_empty | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ flia Hnz H1n | ].
rewrite rngl_summation_split_last; [ | flia ].
rewrite (rngl_summation_shift 1); [ | flia Hnz ].
do 2 rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat.add_comm, Nat.add_sub.
}
cbn - [ rngl_zero rngl_add Nat.log2 rngl_le rngl_div rngl_of_nat ].
replace ((1%QG + 1%QG)%L) with 2%L by easy.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]; [ now subst n | ].
destruct (Nat.log2_succ_or n) as [Hn| Hn]. {
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hop Hor).
    apply IHn.
    flia Hnz Hn1.
  }
  rewrite Hn.
  rewrite (rngl_of_nat_succ (Nat.log2 n)).
  rewrite QG_mul_add_distr_l.
  rewrite QG_mul_1_r.
  rewrite rngl_add_comm.
  apply (QG_add_le_mono_r).
  change (((1 / (1 + rngl_of_nat n))%L ≤ 2)%L).
  Time apply (rngl_le_div_l Hon Hop Hiv Hor). {
    apply (rngl_add_pos_nonneg Hor).
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
    apply (rngl_of_nat_nonneg Hon Hos Hor).
  }
  rewrite rngl_mul_add_distr_l.
  rewrite (rngl_mul_1_r Hon).
  rewrite <- rngl_add_assoc.
  apply (rngl_le_add_r Hor).
  apply (rngl_add_nonneg_nonneg Hor). {
    apply (rngl_0_le_1 Hon Hos Hor).
  }
  rewrite rngl_mul_add_distr_r.
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_add_nonneg_nonneg Hor); apply (rngl_of_nat_nonneg Hon Hos Hor).
}
rewrite Hn.
specialize (Nat.log2_spec_alt n) as H1.
assert (H : 0 < n) by flia Hnz.
specialize (H1 H); clear H.
destruct H1 as (r & Hnr & _ & Hr).
...

End a.
