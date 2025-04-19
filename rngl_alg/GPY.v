(* preparation of GPY (Goldston–Pintz–Yıldırım sieve) *)

From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Misc.
Require Import RingLike.RingLike.
Require Import RingLike.IterAdd.
Require Import QG.

Fixpoint QG_of_nat n :=
  match n with
  | 0 => 0%QG
  | S n' => (1 + QG_of_nat n')%QG
  end.

Definition QG_2 := (QG_1 + QG_1)%QG.
Notation "2" := QG_2 : QG_scope.

Section a.

Instance roq : ring_like_op QG := QG_ring_like_op.
Instance roc : ring_like_prop QG := QG_ring_like_prop.

Theorem harmonic_sum_log2_bound :
  ∀ n, 1 < n → (∑ (k = 1, n), 1 / QG_of_nat k ≤ 2 * QG_of_nat (Nat.log2 n))%L.
Proof.
intros * H1n.
induction n; [ now rewrite rngl_summation_empty | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ flia Hnz H1n | ].
rewrite rngl_summation_split_last; [ | flia ].
rewrite (rngl_summation_shift 1); [ | flia Hnz ].
do 2 rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat.add_comm, Nat.add_sub.
}
cbn - [ rngl_zero rngl_add Nat.log2 rngl_le rngl_div ].
replace ((1%QG + 1%QG)%L) with 2%QG by easy.
...

End a.
