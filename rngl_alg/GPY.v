(* preparation of GPY (Goldston–Pintz–Yıldırım sieve) *)

From Stdlib Require Import Utf8.

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

Theorem harmonic_sum_log2_bound :
  ∀ n, (∑ (k = 1, n), 1 / QG_of_nat k ≤ 2 * QG_of_nat (Nat.log2 n))%L.
Proof.
...

End a.
