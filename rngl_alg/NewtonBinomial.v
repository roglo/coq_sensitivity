(* *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.Misc Main.RingLike Main.IterAdd.
Require Import Misc.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

Theorem binomial_succ_succ : ∀ n k,
  binomial (S n) (S k) = binomial n k + binomial n (S k).
Proof. easy. Qed.

Theorem binomial_lt : ∀ n k, n < k → binomial n k = 0.
Proof.
intros * Hnk.
revert k Hnk.
induction n; intros; [ now destruct k | cbn ].
destruct k; [ flia Hnk | ].
apply Nat.succ_lt_mono in Hnk.
rewrite IHn; [ | easy ].
rewrite Nat.add_0_l.
apply IHn; flia Hnk.
Qed.

Theorem binomial_succ_diag_r : ∀ n, binomial n (S n) = 0.
Proof.
intros.
apply binomial_lt; flia.
Qed.

(* mini ring like *)

Class mini_rngl_prop T {ro : ring_like_op T} :=
  { mini_add_comm : ∀ a b, (a + b = b + a)%L;
    mini_mul_comm : ∀ a b, (a * b = b * a)%L;
    mini_add_assoc: ∀ a b c, (a + (b + c))%L = (a + b + c)%L;
    mini_mul_assoc: ∀ a b c, (a * (b * c))%L = (a * b * c)%L;
    mini_add_0_l : ∀ a, (0 + a = a)%L;
    mini_mul_0_l : ∀ a, (0 * a = 0)%L;
    mini_mul_1_l : ∀ a, (1 * a = a)%L;
    mini_mul_add_distr_l : ∀ a b c, (a * (b + c))%L = (a * b + a * c)%L }.

Theorem mini_add_0_r :
  ∀ {m : mini_rngl_prop T},
  ∀ a, (a + 0 = a)%L.
Proof.
intros.
rewrite mini_add_comm.
apply mini_add_0_l.
Qed.

Theorem mini_mul_1_r :
  ∀ {m : mini_rngl_prop T},
  ∀ a, (a * 1 = a)%L.
Proof.
intros.
rewrite mini_mul_comm.
apply mini_mul_1_l.
Qed.

Theorem mini_mul_0_r :
  ∀ {m : mini_rngl_prop T},
  ∀ a, (a * 0 = 0)%L.
Proof.
intros.
rewrite mini_mul_comm.
apply mini_mul_0_l.
Qed.

Theorem mini_mul_add_distr_r :
  ∀ {m : mini_rngl_prop T},
  ∀ a b c, ((a + b) * c = a * c + b * c)%L.
Proof.
intros.
rewrite mini_mul_comm.
rewrite (mini_mul_comm a).
rewrite (mini_mul_comm b).
apply mini_mul_add_distr_l.
Qed.

Theorem mini_pow_succ_r :
  ∀ {m : mini_rngl_prop T} n a, (a ^ S n = a * a ^ n)%L.
Proof.
intros.
destruct n; [ | easy ].
cbn; symmetry.
apply mini_mul_1_r.
Qed.

Theorem mini_mul_summation_distr_l :
  ∀ {m : mini_rngl_prop T},
  ∀ (a : T) (b e : nat) (f : nat → T),
  (a * (∑ (i = b, e), f i))%L = ∑ (i = b, e), a * f i.
Proof.
intros.
progress unfold iter_seq.
progress unfold iter_list.
remember (S e - b) as len eqn:Hlen.
clear Hlen.
revert b.
induction len; intros; cbn; [ apply mini_mul_0_r | ].
do 2 rewrite mini_add_0_l.
rewrite (fold_left_op_fun_from_d 0%L); cycle 1.
apply mini_add_0_l.
apply mini_add_0_r.
apply mini_add_assoc.
rewrite mini_mul_add_distr_l.
rewrite IHlen.
symmetry.
apply (fold_left_op_fun_from_d 0%L).
apply mini_add_0_l.
intros; rewrite mini_add_comm; apply mini_add_0_l.
apply mini_add_assoc.
Qed.

Theorem mini_pow_add_r :
  ∀ {m : mini_rngl_prop T},
  ∀ (a : T) (i j : nat), (a ^ (i + j))%L = (a ^ i * a ^ j)%L.
Proof.
intros.
revert j.
induction i; intros. {
  symmetry; apply mini_mul_1_l.
}
rewrite Nat.add_succ_comm.
rewrite IHi.
do 2 rewrite mini_pow_succ_r.
rewrite mini_mul_comm.
do 2 rewrite <- mini_mul_assoc.
f_equal.
apply mini_mul_comm.
Qed.

Theorem mini_of_nat_add :
  ∀ {mr : mini_rngl_prop T},
  ∀ m n, rngl_of_nat (m + n) = (rngl_of_nat m + rngl_of_nat n)%L.
Proof.
intros.
revert m.
induction n; intros. {
  now rewrite Nat.add_0_r, mini_add_0_r.
}
rewrite <- Nat.add_succ_comm.
rewrite IHn.
do 2 rewrite rngl_of_nat_succ.
rewrite (mini_add_comm 1)%L.
now rewrite mini_add_assoc.
Qed.

(* end mini ring like *)

Theorem newton_binomial :
  ∀ {m : mini_rngl_prop T},
  ∀ n a b,
  ((a + b) ^ n)%L =
    (∑ (k = 0, n), rngl_of_nat (binomial n k) * a ^ (n - k) * b ^ k)%L.
Proof.
intros.
induction n. {
  cbn.
  progress unfold iter_seq.
  progress unfold iter_list.
  cbn.
  rewrite mini_add_0_l, mini_add_0_r.
  now do 2 rewrite mini_mul_1_l.
}
rewrite mini_pow_succ_r.
rewrite IHn.
rewrite mini_mul_summation_distr_l.
erewrite rngl_summation_eq_compat. 2: {
  intros * Hin.
  rewrite mini_mul_add_distr_r.
  do 4 rewrite mini_mul_assoc.
  rewrite (mini_mul_comm (a * _))%L.
  rewrite mini_mul_assoc.
  replace a with (a ^ 1)%L at 2 by easy.
  rewrite <- mini_pow_add_r.
  rewrite (mini_mul_comm (a ^ _)%L).
  rewrite mini_add_comm.
  rewrite (mini_mul_comm _ (b ^ _))%L at 1.
  do 2 rewrite mini_mul_assoc.
  replace b with (b ^ 1)%L at 2 by easy.
  rewrite <- mini_pow_add_r.
  rewrite <- mini_mul_assoc.
  rewrite mini_mul_comm.
  do 2 rewrite <- mini_mul_assoc.
  rewrite <- mini_mul_add_distr_l.
  easy.
}
remember (∑ (i = _, _), _) as x; subst x.
symmetry.
rewrite iter_seq_split_first; cycle 1.
apply mini_add_0_l.
apply mini_add_0_r.
apply mini_add_assoc.
easy.
progress unfold binomial at 1.
rewrite Nat.sub_0_r, rngl_pow_0_r, mini_mul_1_r.
rewrite (rngl_summation_shift 1); [ | flia ].
rewrite Nat.sub_diag, Nat_sub_succ_1.
remember (rngl_of_nat 1) as x; cbn in Heqx; subst x.
rewrite mini_add_0_r, mini_mul_1_l.
erewrite rngl_summation_eq_compat. 2: {
  intros * Hin.
  rewrite (Nat.add_1_l i).
  rewrite binomial_succ_succ.
  rewrite Nat.sub_succ.
  rewrite mini_of_nat_add.
  do 2 rewrite mini_mul_add_distr_r.
  easy.
}
remember (∑ (i = _, _), _) as x; subst x.
rewrite iter_seq_distr; cycle 1.
apply mini_add_0_l.
apply mini_add_comm.
apply mini_add_assoc.
rewrite mini_add_comm.
rewrite <- mini_add_assoc.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros * Hin.
  rewrite Nat.add_1_r.
  rewrite mini_mul_add_distr_l.
  rewrite mini_mul_assoc.
  easy.
}
remember (∑ (i = _, _), _) as x; subst x.
rewrite iter_seq_distr; cycle 1.
apply mini_add_0_l.
apply mini_add_comm.
apply mini_add_assoc.
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
rewrite iter_seq_split_first; cycle 1.
apply mini_add_0_l.
apply mini_add_0_r.
apply mini_add_assoc.
easy.
rewrite mini_add_comm.
symmetry.
rewrite iter_seq_split_last; [ | flia ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  cbn.
  do 2 rewrite mini_add_0_l.
  do 2 rewrite mini_mul_0_l.
  rewrite mini_add_0_l, mini_add_0_r.
  rewrite mini_mul_1_l, mini_mul_1_r.
  easy.
}
rewrite (rngl_summation_shift 1); [ | flia Hnz ].
do 2 rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros * Hin.
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite Nat.add_sub_swap; [ | easy ].
  rewrite <- mini_mul_assoc.
  easy.
}
remember (∑ (i = _, _), _) as x; subst x.
rewrite <- mini_add_assoc.
f_equal.
rewrite Nat.add_1_r, Nat.sub_diag.
rewrite Nat.sub_0_r.
rewrite <- mini_mul_assoc.
rewrite binomial_succ_diag_r.
cbn.
destruct n; [ easy | cbn ].
rewrite Nat.add_1_r.
rewrite mini_mul_0_l, mini_add_0_l.
rewrite mini_add_0_r, mini_mul_1_l.
now rewrite mini_mul_1_r.
Qed.

End a.
