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

Theorem is_limit_when_tending_to_neighbourhood_eq_compat :
  ∀ is_left {A} (f g : A → T) lt da db a u,
  (∀ x, f x = g x)
  → is_limit_when_tending_to_neighbourhood is_left lt da db f a u
  → is_limit_when_tending_to_neighbourhood is_left lt da db g a u.
Proof.
intros * Hfg Hf.
intros x₀ Hx.
specialize (Hf x₀ Hx).
destruct Hf as (η & Hη & Hf).
exists η.
split; [ easy | ].
intros x Hlt Hxa.
rewrite <- Hfg.
now apply Hf.
Qed.

Theorem is_derivative_at_eq_compat :
  ∀ {A} (f f' g g' : A → T) lt da db a,
  (∀ x, f x = g x)
  → (∀ x, f' x = g' x)
  → is_derivative_at lt da db f f' a
  → is_derivative_at lt da db g g' a.
Proof.
intros * Hfg Hf'g' Hff.
destruct Hff as (H1 & H2 & H3 & H4).
split. {
  apply (is_limit_when_tending_to_neighbourhood_eq_compat _ f); [ easy | ].
  now rewrite <- Hfg.
}
split. {
  apply (is_limit_when_tending_to_neighbourhood_eq_compat _ f); [ easy | ].
  now rewrite <- Hfg.
}
split. {
  rewrite <- Hf'g'.
  eapply is_limit_when_tending_to_neighbourhood_eq_compat; [ | apply H3 ].
  intros x.
  now do 2 rewrite Hfg.
} {
  rewrite <- Hf'g'.
  eapply is_limit_when_tending_to_neighbourhood_eq_compat; [ | apply H4 ].
  intros x.
  now do 2 rewrite Hfg.
}
Qed.

(* *)

Theorem rngl_tan_derivative :
  ∀ θ₀, (rngl_cos θ₀ ≠ 0%L) →
  is_derivative_at angle_lt_for_deriv angle_eucl_distance
    rngl_distance rngl_tan (λ θ, (1 / (rngl_cos θ)²)%L) θ₀.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
intros * Hczz.
progress unfold rngl_tan.
specialize (@derivative_inv_at _ _ _ Hop Hor Hic Hon Hiv Heq) as H1.
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
