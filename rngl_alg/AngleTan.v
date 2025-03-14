(* trigonometry; tangent *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import Trigo.RealLike.
Require Import Trigo.Angle.
Require Import Trigo.AngleDiv2.
Require Import Trigo.AngleTypeIsComplete.
Require Import Trigo.Angle_order.
Require Import Trigo.TrigoWithoutPiExt.
Require Import DerivMul.
Require Import AngleDeriv.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Context {Heq : rngl_has_eq_dec T = true}.

Definition rngl_tan θ := (rngl_sin θ / rngl_cos θ)%L.

(* to be completed
Theorem rngl_tan_derivative :
  ∀ x₀, (rngl_cos x₀ ≠ 0%L) →
  is_derivative_at angle_lt_for_deriv angle_eucl_distance
    rngl_distance rngl_tan (λ θ, (1 - (rngl_cos θ)²)%L) x₀.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hczz.
progress unfold rngl_tan.
specialize (@derivative_inv _ _ _ Hop Hor Hic Hon Hiv Heq) as H1.
specialize (H1 _ angle_lt_for_deriv).
specialize (@derivative_mul _ _ _ _ Hop Hor Hic Hon Hiv) as H2.
specialize (H2 _ angle_lt_for_deriv).
assert (H : ∀ x, ¬ angle_lt_for_deriv x x). {
  intros x.
  progress unfold angle_lt_for_deriv.
  intros (H3, H4).
  now apply angle_lt_irrefl in H3.
}
specialize (H1 H).
specialize (H2 H); clear H.
specialize (H1 angle_eucl_distance).
specialize (H2 angle_eucl_distance).
specialize (H1 rngl_cos (rngl_opp ° rngl_sin)).
specialize (H2 rngl_sin).
set (g := λ θ, if rngl_eq_dec Heo (rngl_cos θ) 0 then 1%L else rngl_cos θ).
specialize (H2 (rngl_inv ° g)).
specialize (H2 rngl_cos (λ x, (- (rngl_opp ° rngl_sin) x / (rngl_cos x)²)%L)).
progress unfold "°" in H2 at 1.
specialize (H2 rngl_sin_derivative).
(*
specialize (H1 x₀ Hcz).
specialize (H1 (rngl_cos_derivative x₀)).
*)
assert (H :
  is_derivative angle_lt_for_deriv angle_eucl_distance
    (@rngl_distance' T ro rp Hop Hor) (λ x : angle T, (g x)⁻¹)
    (λ x : angle T, (- (rngl_opp ° rngl_sin) x / (rngl_cos x)²)%L)). {
  intros θ.
  destruct (rngl_eq_dec Heo (rngl_cos θ) 0) as [Hcz| Hcz]. {
    split. {
      progress unfold g.
(* oui, mais non, ça, ça va pas, ça *)
...
specialize (H2 H1).
progress unfold "°" in H2 at 1.
...
*)

End a.
