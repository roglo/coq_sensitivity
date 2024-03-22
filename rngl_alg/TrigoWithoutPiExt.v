Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import TrigoWithoutPi.
Require Import AngleLeSubAdd.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_cos_add_le_cos :
  ∀ θ1 θ2,
  (θ1 ≠ angle_straight ∨ θ2 ≠ angle_straight ∨
   0 ≤ rngl_cos θ1 ∨ 0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros * H12 Hzs1 Hzs2 Hzs12.
rewrite <- or_assoc in H12.
rewrite or_comm in H12.
rewrite or_assoc in H12.
destruct H12 as [H12| H12]. {
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_nonneg_nonneg Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_nonneg_nonneg Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_nle_gt Hor) in Hc1z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  remember (θ1 - angle_right)%A as θ' eqn:Hθ'.
  apply angle_add_move_r in Hθ'.
  subst θ1; rename θ' into θ1.
  rewrite angle_add_add_swap in Hzs12 |-*.
  rewrite rngl_cos_add_right_r in Hc1z.
  apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
  rewrite rngl_sin_add_right_r in Hzs1, Hzs12.
  do 2 rewrite rngl_cos_add_right_r.
  apply -> (rngl_opp_le_compat Hop Hor).
  apply (rngl_lt_le_incl Hor) in Hc1z.
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  now apply rngl_sin_add_nonneg.
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_nonneg_nonneg Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
destruct H12 as [H12| H12]; [ easy | ].
apply (rngl_nle_gt Hor) in Hc2z.
destruct (rngl_eq_dec Hed (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
  apply eq_rngl_sin_0 in Hs1z.
  destruct Hs1z; subst θ1. {
    rewrite angle_add_0_l.
    apply rngl_cos_bound.
  }
  destruct H12 as [H12| H12]; [ easy | ].
  rewrite (rngl_sin_add_straight_l Hon Hop) in Hzs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
  apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
  symmetry in Hzs12.
  apply eq_rngl_sin_0 in Hzs12.
  destruct Hzs12; subst θ2; [ | easy ].
  rewrite angle_add_0_r.
  apply (rngl_le_refl Hor).
}
exfalso.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
cbn.
apply (rngl_add_neg_nonpos Hop Hor). {
  apply (rngl_mul_pos_neg Hop Hor Hid); [ | easy ].
  apply not_eq_sym in Hs1z.
  now apply (rngl_lt_iff Hor).
} {
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem quadrant_1_sin_sub_nonneg_cos_le :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hsz1 Hzs2 Hzc1 Hzc2 Hzs12.
destruct (rngl_eq_dec Hed (rngl_sin θ2) 0) as [Hs2z| Hs2z]. {
  apply eq_rngl_sin_0 in Hs2z.
  destruct Hs2z; subst θ2. {
    apply rngl_cos_bound.
  }
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzc2.
  apply Hzc2; clear Hzc2; cbn.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
cbn in Hzs12.
rewrite (rngl_mul_opp_r Hop) in Hzs12.
rewrite (rngl_add_opp_r Hop) in Hzs12.
apply -> (rngl_le_0_sub Hop Hor) in Hzs12.
apply (rngl_lt_eq_cases Hor) in Hzs2.
apply not_eq_sym in Hs2z.
destruct Hzs2 as [Hzs2| Hzs2]; [ | easy ].
clear Hs2z.
apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ (rngl_sin θ2) Hzs2) in Hzs12.
rewrite <- rngl_mul_assoc in Hzs12.
rewrite fold_rngl_squ in Hzs12.
specialize (cos2_sin2_1 θ2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1 in Hzs12; clear H1.
rewrite (rngl_mul_sub_distr_l Hop) in Hzs12.
rewrite (rngl_mul_1_r Hon) in Hzs12.
apply (rngl_le_sub_le_add_l Hop Hor) in Hzs12.
eapply (rngl_le_trans Hor); [ apply Hzs12 | ].
rewrite (rngl_mul_mul_swap Hic).
progress unfold rngl_squ.
rewrite rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite <- (rngl_cos_sub Hop).
rewrite <- (rngl_mul_1_l Hon).
apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
apply rngl_cos_bound.
Qed.

Theorem rngl_cos_le_cos_add :
  ∀ θ1 θ2,
  (rngl_sin θ1 ≤ 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_cos θ1 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs12.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  change_angle_add_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    move Hzc2 before Hzc1.
    assert (Hzc12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
      cbn.
      apply (rngl_add_nonneg_nonneg Hor).
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
    }
    apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
    now apply (rngl_lt_le_incl Hor).
    apply angle_le_sub_le_add_l_lemma_1; try easy.
    rewrite angle_sub_diag.
    apply rngl_cos_bound.
    rewrite angle_sub_diag.
    apply (rngl_le_refl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  exfalso.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12; cbn.
  apply (rngl_add_nonneg_nonneg Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_sub_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_goal T.
apply (rngl_lt_le_incl Hor) in Hc1z, Hzs12.
apply rngl_cos_add_le_cos; try easy.
now right; right; left.
Qed.

End a.
