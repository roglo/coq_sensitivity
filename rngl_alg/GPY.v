(* preparation of GPY (Goldston–Pintz–Yıldırım sieve) *)

Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Import ListDef.
Import List.ListNotations.

Require Import RingLike.Misc.
Require Import RingLike.Core.
Require Import RingLike.IterAdd.
Require Import RingLike.IterMul.
Require Import RingLike.Nat_algebra.
Require Import QG.

Section a.

Instance roq : ring_like_op QG := QG_ring_like_op.
Instance roc : ring_like_prop QG := QG_ring_like_prop.

Definition QG_of_nat n : QG := rngl_of_nat n.

Theorem QG_of_nat_succ : ∀ n, QG_of_nat (S n) = (1 + QG_of_nat n)%QG.
Proof. easy. Qed.

Theorem harmonic_sum_after_2_pow_bound :
  ∀ n k, n ≤ k → (∑ (i = 1, n), 1 / rngl_of_nat (k + i) ≤ 1)%L.
Proof.
assert (Hon : rngl_has_1 QG = true) by easy.
assert (Hop : rngl_has_opp QG = true) by easy.
assert (Hiv : rngl_has_inv QG = true) by easy.
assert (Hc1 : rngl_characteristic QG ≠ 1) by easy.
assert (Hor : rngl_is_ordered QG = true) by easy.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
intros * Hnk.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply (rngl_le_trans Hor _ (∑ (i = 1, n), 1 / rngl_of_nat k)). {
  apply (rngl_summation_le_compat Hor).
  intros i Hi.
  Time apply (rngl_div_le_mono_pos_l Hop Hiv Hor Hii). {
    apply (rngl_0_lt_1 Hos Hc1 Hto).
  }
  apply (rngl_le_inv_inv Hop Hiv Hor). {
    apply (rngl_le_neq Hto).
    split; [ apply (rngl_of_nat_nonneg Hos Hor) | ].
    intros H; symmetry in H.
    apply eq_rngl_of_nat_0 in H; [ | easy ].
    flia Hi H.
  } {
    apply (rngl_le_neq Hto).
    split; [ apply (rngl_of_nat_nonneg Hos Hor) | ].
    intros H; symmetry in H.
    apply eq_rngl_of_nat_0 in H; [ | easy ].
    subst k.
    apply Nat.nlt_ge in Hnk.
    apply Hnk; clear Hnk.
    flia Hi.
  } {
    apply (rngl_of_nat_inj_le Hop Hc1 Hto).
    apply Nat.le_add_r.
  }
}
rewrite (rngl_summation_const Hos).
rewrite Nat_sub_succ_1.
rewrite (rngl_mul_div_assoc Hiv).
rewrite rngl_mul_1_r.
apply (rngl_div_le_1 Hop Hiv Hor). {
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  subst k.
  apply Nat.nlt_ge in Hnk.
  apply Hnk; clear Hnk.
  now apply Nat.neq_0_lt_0.
}
split; [ apply (rngl_of_nat_nonneg Hos Hor) | ].
now apply (rngl_of_nat_inj_le Hop Hc1 Hto).
Qed.

Theorem harmonic_sum_log2_bound_up_to_2_pow :
  ∀ n,
  2 ≤ n
  → (∑ (i = 1, 2 ^ n + 1), 1 / QG_of_nat i ≤ 2 * QG_of_nat n)%L.
Proof.
assert (Hon : rngl_has_1 QG = true) by easy.
assert (Hop : rngl_has_opp QG = true) by easy.
assert (Hiv : rngl_has_inv QG = true) by easy.
assert (Hor : rngl_is_ordered QG = true) by easy.
assert (Hc1 : rngl_characteristic QG ≠ 1) by easy.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * H1n.
progress unfold QG_of_nat.
induction n; [ now rewrite rngl_summation_empty | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ flia Hnz H1n | clear H1n ].
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]; [ now subst n | ].
rewrite Nat.pow_succ_r'.
rewrite Nat_mul_2_l.
rewrite (rngl_summation_split (2 ^ n + 1)); [ | flia ].
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_r Hop Hor).
  apply IHn.
  flia Hnz Hn1.
}
rewrite rngl_of_nat_succ.
rewrite rngl_mul_add_distr_l.
rewrite rngl_mul_1_r.
rewrite rngl_add_comm.
apply (rngl_add_le_mono_r Hop Hor).
rewrite (rngl_summation_shift (2 ^ n + 1)). 2: {
  split; [ flia | ].
  apply Nat.add_le_mono_r.
  apply Nat.add_le_mono_l.
  now apply Nat.pow_lower_bound.
}
rewrite Nat.add_comm, Nat.add_sub.
rewrite <- Nat.add_assoc.
rewrite Nat.add_sub.
apply (rngl_le_trans Hor _ 1); [ | apply (rngl_1_le_2 Hos Hiq Hto) ].
apply harmonic_sum_after_2_pow_bound.
apply Nat.le_add_r.
Qed.

Theorem harmonic_sum_log2_bound :
  ∀ n, 2 ≤ n → (∑ (k = 1, n), 1 / QG_of_nat k ≤ 3 * QG_of_nat (Nat.log2 n))%L.
Proof.
assert (Hon : rngl_has_1 QG = true) by easy.
assert (Hop : rngl_has_opp QG = true) by easy.
assert (Hiv : rngl_has_inv QG = true) by easy.
assert (Hor : rngl_is_ordered QG = true) by easy.
assert (Hc1 : rngl_characteristic QG ≠ 1) by easy.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
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
rewrite (rngl_summation_split (2 ^ n)); [ | flia ].
rewrite QG_mul_add_distr_r.
rewrite QG_mul_1_l.
rewrite rngl_add_comm.
rename Hn1 into Hnr1.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n.
  cbn in Hr.
  destruct r; [ easy | ].
  destruct r; [ easy | flia Hr ].
}
assert (H2n : 2 ≤ n). {
  destruct n. {
    cbn in Hnr1, Hr.
    flia Hnr1 Hr.
  }
  destruct n; [ easy | flia ].
}
clear Hn1.
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_l Hop Hor).
  specialize (harmonic_sum_log2_bound_up_to_2_pow n H2n) as H1.
  eapply (rngl_le_trans Hor); [ | apply H1 ].
  rewrite (rngl_summation_split_last _ (2 ^ n + 1)); [ | flia ].
  rewrite (rngl_summation_shift 1 2). 2: {
    split; [ flia | ].
    replace 2 with (1 + 1) by easy.
    apply Nat.add_le_mono_r.
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  rewrite Nat_sub_succ_1.
  erewrite (rngl_summation_eq_compat _ _ _ (_ - _)). 2: {
    intros i Hi.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite Nat.add_sub.
  apply (rngl_le_add_r Hto).
  apply (rngl_div_nonneg Hop Hiv Hto). {
    apply (rngl_0_le_1 Hos Hor).
  }
  apply (rngl_le_neq Hto).
  split; [ apply (rngl_of_nat_nonneg Hos Hor) | ].
  intros H; symmetry in H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia H.
}
rewrite rngl_add_comm.
apply QG_add_le_compat; [ apply QG_le_refl | ].
destruct (Nat.eq_dec r 0) as [Hrz| Hrz]. {
  subst r.
  rewrite Nat.add_0_r.
  rewrite rngl_summation_empty; [ | flia ].
  apply (rngl_of_nat_nonneg Hos Hor).
}
rewrite (rngl_summation_shift (2 ^ n)). 2: {
  split; [ flia | ].
  apply Nat.add_le_mono_l.
  destruct r; [ easy | flia ].
}
do 2 rewrite Nat.add_comm, Nat.add_sub.
apply (rngl_le_trans Hor _ 1). 2: {
  rewrite <- rngl_of_nat_1.
  apply (rngl_of_nat_inj_le Hop Hc1 Hto).
  flia H2n.
}
apply harmonic_sum_after_2_pow_bound.
now apply Nat.lt_le_incl.
Qed.

(* borrowed from FermatLittle.v *)
(* to prevent importing it for the moment *)

Fixpoint prime_test cnt n d :=
  match cnt with
  | 0 => true
  | S c =>
      match n mod d with
      | 0 => n <=? d
      | S _ => prime_test c n (d + 1)
      end
  end.

Definition is_prime n :=
  match n with
  | 0 | 1 => false
  | S (S c) => prime_test c n 2
  end.

(* *)

Definition prime_indicator n := if is_prime n then 1 else 0.
Definition pi n := ∑ (i = 1, n), prime_indicator i.

Theorem prime_indicator_sum_lower_bound :
  ∀ H, ∃ N₀, ∀ N,
  N₀ ≤ N
  → (QG_of_nat N / QG_of_nat (Nat.log2 N) ≤
     ∑ (n = 1, N),
       ∑ (h = 0, H), QG_of_nat (prime_indicator (n + h)))%QG.
Proof.
intros.
enough (H1 :
  ∃ N₀, ∀ N,
  N₀ ≤ N
  → (QG_of_nat N / QG_of_nat (Nat.log2 N) ≤
     ∑ (h = 0, H), ∑ (n = 1, N), QG_of_nat (prime_indicator (n + h)))%QG). {
  destruct H1 as (N₀ & H1).
  exists N₀.
  intros * HNN.
  rewrite rngl_summation_summation_exch.
  now apply H1.
}
(* https://www.cs.umd.edu/~gasarch/TOPICS/mathnotes/weakpnt.pdf *)
(* https://en.wikipedia.org/wiki/Prime_number_theorem#Non-asymptotic_bounds_on_the_prime-counting_function *)
Theorem weak_prime_number_theorem_1 :
  ∀ n, (QG_of_nat_pair 1 3 * QG_of_nat (Nat.log2_up n) ≤ QG_of_nat (pi n))%QG.
Proof.
intros.
Fixpoint rev_primes_le n :=
  match n with
  | 0 => []
  | S n' => if is_prime n then n :: rev_primes_le n' else rev_primes_le n'
  end.

Definition primes_le n := List.rev (rev_primes_le n).

Definition nth_prime n i := (primes_le n).[i].

Theorem composite_special_decompose :
  ∀ n x, x ≤ n → is_prime x = false →
  ∃ p a b c,
  (∀ i, p.[i] = nth_prime n i)
  → (∀ i, a.[i] = 2 * b.[i] + c.[i])
  → (∀ i, c.[i] ∈ [0; 1])
  → x = ∏ (i = 1, pi n), p.[i-1] ^ a.[i-1].
Proof.
intros * Hxn Hpx.
...
(*
Proof:
Let COMP be the composite numbers that are ≤ n.

a) Let x ∈ COMP and x ≤ n. We factor x so that x = p₁^a1 ... p_{a_πn}^an.
Write each ai = 2bi + ci where ci ∈ {0, 1}. Hence
  x =
    p₁^2b₁ p₂^2b₂ p₃^2b₃ ... p_{πn}^2b_{πn}
    p₁^c₁ p₂^c₂ ... p_{pin}^c_{pin}.
Note that this can be written as
    m² p₁^c₁ p₂^c₂ ... p_{pin}^c_{pin}.
How many numbers are of this form?

There are at most √n numbers of the form m² where m² ≤ n. There are at
most 2^πn numbers of the form p₁^c₁ p₂^c₂ ... p_{pin}^c_{pin}.
where each ci ∈ {0, 1}. Hence there
    #COMP ≤ √n2^πn
    n − πn ≤ √n2^πn
    n ≤ √n2^πn + πn

if πn ≤ 1/3 log2 n then
  n ≤ √n2^πn + πn ≤ √n n^(1/3) + 1/3 log2 n ≤ n^(5/6) + 1/3 log2 n

which is a contradiction.
*)
...
(*
Require Import Stdlib.QArith.QArith.
Open Scope nat_scope.
Compute (
  map (λ n,
    (n, QG_of_nat_pair 1 3 * QG_of_nat (Nat.log2_up n) ≤ QG_of_nat (pi n))%QG
  ) (seq 0 40)
).
*)
Require Import Stdlib.QArith.QArith.
Open Scope nat_scope.
Import List.ListNotations.
Compute (
  map (λ n,
    (n, QG_of_nat_pair 1 3 * QG_of_nat (Nat.log2 n), QG_of_nat (pi n))%QG
  ) (seq 0 40)
).
Compute (
  map (λ n,
    (n, QG_of_nat_pair 1 3 * QG_of_nat (Nat.log2 n) = QG_of_nat (pi n))%QG
  ) (seq 0 40)
).
Check eq_QG_eq.
...
Theorem weak_prime_number_theorem :
  ∀ ε, (0 < ε)%QG → ∃ n₀, ∀ n, n₀ ≤ n →
  let xlnx := (QG_of_nat n / QG_of_nat (Nat.log2 n))%QG in
  ((1 - ε) * xlnx < QG_of_nat (pi n) < (QG_of_nat 1 + ε) * xlnx)%QG.
Proof.
intros * Hε.
...
(*
Require Import Stdlib.QArith.QArith.
Open Scope nat_scope.
Import List.ListNotations.
Compute (
  let ε := (1/ QG_of_nat 170)%QG in
  map (λ n,
  let xlnx := (QG_of_nat n / QG_of_nat (Nat.log2 n))%QG in
  (n, (((1 - ε) * xlnx)%QG, (QG_of_nat (pi n))%QG)%QG)
  ) (seq 4 60)
).
Compute (
  let ε := (1/ QG_of_nat 170)%QG in
  map (λ n,
  let xlnx := (QG_of_nat n / QG_of_nat (Nat.log2 n))%QG in
  (n,
  (((1 - ε) * xlnx)%QG, QG_of_nat (pi n))%QG,
  (QG_of_nat (pi n), (QG_of_nat 2 + ε) * xlnx)%QG
  )
  ) (seq 4 60)
).
*)
...
Theorem weak_prime_number_theorem_1 :
  ∀ n, (QG_of_nat (Nat.log2 n) / QG_of_nat 3 ≤ QG_of_nat (pi n))%QG.
Proof.
...
Theorem weak_prime_number_theorem :
  ∀ n, (QG_of_nat_pair n (Nat.log2 n) / QG_of_nat 3 ≤ QG_of_nat (pi n))%QG.
Proof.
(**)
...
Theorem weak_prime_number_theorem :
  ∀ n, 4 ≤ n → (QG_of_nat_pair n (Nat.log2 n) ≤ QG_of_nat (pi n))%QG.
Proof.
intros * H4n.
...
Theorem weak_prime_number_theorem' :
  ∀ n, 2 ≤ n → (QG_of_nat_pair n (2 * Nat.log2 n) ≤ QG_of_nat (pi n))%QG.
Proof.
intros * H2n.
...
(*
Require Import Stdlib.QArith.QArith.
Open Scope nat_scope.
Import List.ListNotations.
Compute (
  map (λ N,
    (N, π N)
  ) (seq 2 20)
).
Compute (
  map (λ N,
    (N, QG_of_nat_pair N (2 * Nat.log2 N) ≤ QG_of_nat (π N))%QG
  ) (seq 2 20)
).
*)
(*
Require Import Stdlib.QArith.QArith.
Open Scope nat_scope.
Import List.ListNotations.
Compute (
  let H := 100 in
  List.map (λ n, (n,
     ∑ (h = 0, H), QG_of_nat (prime_indicator (n + h)))%QG
  ) (List.seq 30 40)
).
...
Compute (
  let H := 1%nat in
  List.map (λ N,
  (N, QG_of_nat N / (QG_of_nat (Nat.log2 N) * QG_of_Q (69 / 100)) ≤
   ∑ (n = 1, N),
     ∑ (h = 0, H), QG_of_nat (prime_indicator (n + h)))%QG
  ) (List.seq 0 100)
).
*)
...

End a.
