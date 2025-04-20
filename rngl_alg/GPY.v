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

Notation "2" := (QG_of_nat 2) : QG_scope.

Theorem QG_of_nat_succ : ∀ n, QG_of_nat (S n) = (1 + QG_of_nat n)%QG.
Proof. easy. Qed.

(* 1 + 1/2 + 1/3 = (6 + 3 + 2) / 6 = 11/6 *)
(* 2 * log2 3 = 2 ok *)
(* 1 + 1/2 + 1/3 + 1/4 = 11/6 + 1/4 = 22/12 + 3/12 = 25/12 *)
(* 2 * log2 4 = 4 ok *)

Theorem harmonic_sum_log2_bound :
  ∀ n, 1 < n → (∑ (k = 1, n), 1 / QG_of_nat k ≤ 2 * QG_of_nat (Nat.log2 n))%L.
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
replace ((1%QG + 1%QG)%L) with 2%QG by easy.
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
...

End a.
