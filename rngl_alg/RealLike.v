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

Definition rl_sqrt := rl_nth_root 2.

Theorem rngl_squ_sqrt : ∀ a, (0 ≤ a)%L → rngl_squ (rl_sqrt a) = a.
Proof.
intros.
now apply (rl_nth_root_pow 2 a).
Qed.

End a.

Notation "'√' a" := (rl_sqrt a) (at level 1, format "√ a") : ring_like_scope.
