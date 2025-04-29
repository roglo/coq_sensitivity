(* trigonometry; tangent *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.

Require Import RingLike.RingLike.
Require Import RingLike.RealLike.
Require Import RingLike.DerivMul.

Require Import TrigoWithoutPi.Angle.
Require Import TrigoWithoutPi.AngleDiv2.
Require Import TrigoWithoutPi.Angle_order.
Require Import TrigoWithoutPi.TrigoWithoutPiExt.

Require Import AngleDeriv.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition rngl_tan θ := (rngl_sin θ / rngl_cos θ)%L.

Theorem rngl_tan_derivative :
  ∀ θ₀, (rngl_cos θ₀ ≠ 0%L) →
  is_derivative_at angle_lt_for_deriv angle_eucl_distance
    rngl_distance rngl_tan (λ θ, (1 / (rngl_cos θ)²)%L) θ₀.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_integral_or_inv_1_quot_eq_dec_order Hon Hiv Hor) as Hio.
intros * Hczz.
progress unfold rngl_tan.
specialize (@derivative_inv_at _ _ _ Hop Hor Hic Hon Hiv Hed) as H1.
specialize (H1 _ angle_lt_for_deriv).
specialize (@derivative_mul_at _ _ _ _ Hop Hor Hic Hon Hiv) as H2.
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
specialize (H1 θ₀ Hczz).
specialize (H1 (rngl_cos_derivative _)).
specialize (H2 (rngl_inv ° rngl_cos)).
specialize (H2 rngl_cos).
specialize (H2 (λ x, (- (rngl_opp ° rngl_sin) x / (rngl_cos x)²)%L)).
specialize (H2 θ₀ (rngl_sin_derivative _)).
specialize (H2 H1).
cbn in H2.
eapply is_derivative_at_eq_compat; [ | | apply H2 ]. {
  intros θ.
  apply (rngl_mul_inv_r Hiv).
} {
  intros θ; cbn.
  destruct (rngl_eq_dec Heo (rngl_cos θ) 0) as [Hcz| Hcz]. {
    rewrite Hcz.
    rewrite (rngl_squ_0 Hos).
    rewrite (rngl_mul_0_l Hos).
    rewrite rngl_add_0_r.
    progress unfold "°".
    rewrite (rngl_opp_involutive Hop).
    apply eq_rngl_cos_0 in Hcz.
    destruct Hcz; subst θ; cbn. {
      apply (rngl_mul_1_l Hon).
    } {
      rewrite (rngl_mul_div_assoc Hiv).
      f_equal.
      apply (rngl_squ_opp_1 Hon Hop).
    }
  }
  progress unfold "°".
  rewrite (rngl_opp_involutive Hop).
  rewrite (rngl_mul_div_assoc Hiv).
  rewrite fold_rngl_squ.
  rewrite (rngl_mul_inv_diag_r Hon Hiv); [ | easy ].
  assert (Hcz2 : (rngl_cos θ)² ≠ 0%L). {
    intros H; apply Hcz.
    now apply (eq_rngl_squ_0 Hos Hio) in H.
  }
  apply (rngl_mul_move_r Hi1); [ easy | ].
  rewrite rngl_mul_add_distr_r.
  rewrite (rngl_div_mul Hon Hiv); [ | easy ].
  rewrite (rngl_mul_1_l Hon).
  rewrite rngl_add_comm.
  apply cos2_sin2_1.
}
Qed.

End a.
