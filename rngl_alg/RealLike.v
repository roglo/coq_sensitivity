(*
Set Nested Proofs Allowed.
*)
Require Import Utf8 (*ZArith*).
(*
Import List List.ListNotations.
*)
Require Import (*Main.Misc*) Main.RingLike (*Main.IterAdd*).
(*
Require Import Init.Nat.
*)

Class real_like_prop T {ro : ring_like_op T} {rp : ring_like_prop T} :=
  { rl_has_integral_modulus : bool;
    rl_nth_root : nat → T → T;
    rl_opt_integral_modulus_prop :
      if rl_has_integral_modulus then
        ∀ a b : T, (rngl_squ a + rngl_squ b = 0 → a = 0 ∧ b = 0)%L
      else not_applicable;
    rl_nth_root_pow : ∀ n a, (0 ≤ a → rl_nth_root n a ^ n = a)%L;
    rl_nth_root_mul :
      ∀ n a b, (0 ≤ a)%L → (0 ≤ b)%L →
      (rl_nth_root n (a * b) = rl_nth_root n a * rl_nth_root n b)%L;
    rl_nth_root_inv :
      ∀ n a, (0 < a → rl_nth_root n a⁻¹ = (rl_nth_root n a)⁻¹)%L;
    rl_sqrt_nonneg : ∀ a, (0 ≤ a → 0 ≤ rl_nth_root 2 a)%L }.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition rl_sqrt a := rl_nth_root 2 a.

End a.

Notation "'√' a" := (rl_sqrt a) (at level 1, format "√ a") : ring_like_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Theorem rngl_squ_sqrt : ∀ a, (0 ≤ a)%L → rngl_squ √a = a.
Proof.
intros.
now apply (rl_nth_root_pow 2 a).
Qed.

Theorem rl_sqrt_mul :
  ∀ a b,
  (0 ≤ a)%L
  → (0 ≤ b)%L
  → rl_sqrt (a * b)%L = (rl_sqrt a * rl_sqrt b)%L.
Proof.
intros * Ha Hb.
progress unfold rl_sqrt.
now rewrite rl_nth_root_mul.
Qed.

Theorem rl_sqrt_div :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a)%L → (0 < b)%L → (√(a / b) = √a / √b)%L.
Proof.
intros Hon Hop Hiv Hor * Ha Hb.
progress unfold rngl_div.
rewrite Hiv.
rewrite rl_sqrt_mul; [ | easy | ]. 2: {
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
}
f_equal.
now apply rl_nth_root_inv.
Qed.

Theorem rl_sqrt_squ :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (√(a²))%L = rngl_abs a.
Proof.
intros Hop Hor *.
progress unfold rngl_squ.
progress unfold rngl_abs.
progress unfold rl_sqrt.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az. {
  apply rngl_leb_le in Haz.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Haz.
  rewrite <- (rngl_mul_opp_opp Hop).
  rewrite rl_nth_root_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite rngl_squ_pow_2.
  now apply rl_nth_root_pow.
} {
  apply (rngl_leb_gt Hor) in Haz.
  apply (rngl_lt_le_incl Hor) in Haz.
  rewrite rl_nth_root_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite rngl_squ_pow_2.
  now apply rl_nth_root_pow.
}
Qed.

End a.
