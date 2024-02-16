(* Newton binomial
    (a + b) ^ n = ∑ (k = 0, n), binomial n k * a ^ (n - k) * b ^ k
 *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.Misc Main.RingLike Main.IterAdd.
Require Import Misc.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem newton_binomial :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ n a b,
  ((a + b) ^ n)%L =
    (∑ (k = 0, n), rngl_of_nat (binomial n k) * a ^ (n - k) * b ^ k)%L.
Proof.
intros Hic Hon Hos.
intros.
induction n. {
  rewrite rngl_summation_only_one; cbn.
  rewrite rngl_add_0_r.
  now do 2 rewrite (rngl_mul_1_l Hon).
}
rewrite rngl_pow_succ_r.
rewrite IHn.
rewrite (rngl_mul_summation_distr_l Hos).
erewrite rngl_summation_eq_compat. 2: {
  intros * Hin.
  rewrite rngl_mul_add_distr_r.
  do 4 rewrite rngl_mul_assoc.
  rewrite (rngl_mul_comm Hic (a * _))%L.
  rewrite rngl_mul_assoc.
  replace a with (a ^ 1)%L at 2 by apply (rngl_mul_1_r Hon).
  rewrite <- (rngl_pow_add_r Hon).
  rewrite (rngl_mul_comm Hic (a ^ _)%L).
  rewrite rngl_add_comm.
  rewrite (rngl_mul_comm Hic _ (b ^ _))%L at 1.
  do 2 rewrite rngl_mul_assoc.
  replace b with (b ^ 1)%L at 2 by apply (rngl_mul_1_r Hon).
  rewrite <- (rngl_pow_add_r Hon).
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_mul_comm Hic).
  do 2 rewrite <- rngl_mul_assoc.
  rewrite <- rngl_mul_add_distr_l.
  easy.
}
remember (∑ (i = _, _), _) as x; subst x.
symmetry.
rewrite rngl_summation_split_first; [ | easy ].
progress unfold binomial at 1.
rewrite Nat.sub_0_r, rngl_pow_0_r, (rngl_mul_1_r Hon).
rewrite (rngl_summation_shift 1); [ | flia ].
rewrite Nat.sub_diag, Nat_sub_succ_1.
remember (rngl_of_nat 1) as x; cbn in Heqx; subst x.
rewrite rngl_add_0_r, (rngl_mul_1_l Hon).
erewrite rngl_summation_eq_compat. 2: {
  intros * Hin.
  rewrite (Nat.add_1_l i).
  rewrite binomial_succ_succ.
  rewrite Nat.sub_succ.
  rewrite rngl_of_nat_add.
  do 2 rewrite rngl_mul_add_distr_r.
  easy.
}
remember (∑ (i = _, _), _) as x; subst x.
rewrite rngl_summation_add_distr.
rewrite rngl_add_comm.
rewrite <- rngl_add_assoc.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros * Hin.
  rewrite Nat.add_1_r.
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_assoc.
  easy.
}
remember (∑ (i = _, _), _) as x; subst x.
rewrite rngl_summation_add_distr.
f_equal.
symmetry.
rewrite rngl_summation_rshift.
erewrite rngl_summation_eq_compat. 2: {
  intros * Hin.
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite Nat_sub_succ_1.
  rewrite Nat_sub_sub_assoc; [ | flia Hin ].
  easy.
}
remember (∑ (i = _, _), _) as x; subst x.
symmetry.
rewrite rngl_summation_split_first; [ | easy ].
rewrite rngl_add_comm.
symmetry.
rewrite rngl_summation_split_last; [ | now apply -> Nat.succ_le_mono ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  cbn.
  do 2 rewrite rngl_add_0_l.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite rngl_add_0_l, rngl_add_0_r.
  rewrite (rngl_mul_1_l Hon).
  do 2 rewrite (rngl_mul_1_r Hon).
  easy.
}
rewrite (rngl_summation_shift 1); [ | flia Hnz ].
do 2 rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros * Hin.
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite Nat.add_sub_swap; [ | easy ].
  rewrite <- rngl_mul_assoc.
  easy.
}
remember (∑ (i = _, _), _) as x; subst x.
rewrite <- rngl_add_assoc.
f_equal.
rewrite Nat.add_1_r, Nat.sub_diag.
rewrite Nat.sub_0_r.
rewrite <- rngl_mul_assoc.
rewrite binomial_succ_diag_r.
cbn.
destruct n; [ easy | cbn ].
rewrite Nat.add_1_r.
rewrite (rngl_mul_0_l Hos), rngl_add_0_l.
rewrite rngl_add_0_r, (rngl_mul_1_l Hon).
now rewrite rngl_mul_1_r.
Qed.

End a.
