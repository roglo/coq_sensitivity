(* just a file for this theorem:
     (θ2 ≤ θ3)%A → (θ1 + θ2 ≤ θ1 + θ3)%A
 *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import TrigoWithoutPi TrigoWithoutPiExt.
Require Import AngleLeSubAdd.
Require Import AngleAddOverflowLe.
Require Import TacChangeAngle.
Require Import AngleAddOverflowEquiv3.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_add_overflow_straight_straight :
  rngl_characteristic T ≠ 1 →
  angle_add_overflow angle_straight angle_straight = true.
Proof.
intros Hc1.
destruct_ac.
progress unfold angle_add_overflow.
rewrite angle_straight_add_straight.
progress unfold angle_ltb; cbn.
rewrite (rngl_leb_refl Hor).
apply rngl_ltb_lt.
apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
Qed.

Theorem rngl_sin_add_pos_1 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 < rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros  * Hs1z Hs2z Hc1z Hc2z.
cbn.
apply (rngl_add_nonneg_pos Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_mul_pos_pos Hop Hor Hii).
Qed.

Theorem rngl_sin_add_pos_2 :
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros  * Hs1z Hs2z Hc1z Hc2z.
cbn.
apply (rngl_add_pos_nonneg Hor).
now apply (rngl_mul_pos_pos Hop Hor Hii).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem rngl_cos_add_nonneg :
  ∀ θ1 θ2,
  (rngl_sin θ1 < 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hs1z Hzs2 Hzc1 Hzc2.
change_angle_add_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hs1z.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_goal T.
apply (rngl_lt_le_incl Hor) in Hs1z.
now apply rngl_sin_add_nonneg.
Qed.

Theorem angle_lt_rngl_cos_add_pos :
  ∀ θ1 θ2,
  (θ2 < angle_right - θ1)%A ∨ (- angle_right - θ1 < θ2)%A
  → (0 < rngl_cos θ1)%L
  → (0 < rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * H21 Hs1z.
apply (rngl_nle_gt Hor).
intros Hzs12.
destruct H21 as [H21| H21]. {
  apply angle_nle_gt in H21.
  apply H21; clear H21.
  progress unfold angle_leb.
  rewrite rngl_sin_sub_right_l.
  generalize Hs1z; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H; rewrite H; clear H.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  symmetry in Hzs2.
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs2.
  apply rngl_leb_le.
  rewrite rngl_cos_sub_right_l.
  rewrite rngl_cos_add in Hzs12.
  apply -> (rngl_le_sub_0 Hop Hor) in Hzs12.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hzs1]. {
    apply (rngl_mul_le_mono_nonneg_l Hop Hor (rngl_cos θ1)) in Hzs12. 2: {
      now apply (rngl_lt_le_incl Hor) in Hs1z.
    }
    rewrite rngl_mul_assoc in Hzs12.
    rewrite fold_rngl_squ in Hzs12.
    specialize (cos2_sin2_1 θ1) as H.
    apply (rngl_add_move_r Hop) in H.
    rewrite H in Hzs12; clear H.
    rewrite (rngl_mul_sub_distr_r Hop) in Hzs12.
    rewrite (rngl_mul_1_l Hon) in Hzs12.
    apply (rngl_le_sub_le_add_r Hop Hor) in Hzs12.
    rewrite (rngl_mul_comm Hic) in Hzs12.
    progress unfold rngl_squ in Hzs12.
    do 2 rewrite <- rngl_mul_assoc in Hzs12.
    rewrite <- rngl_mul_add_distr_l in Hzs12.
    rewrite rngl_add_comm in Hzs12.
    rewrite (rngl_mul_comm Hic (rngl_sin θ2)) in Hzs12.
    rewrite <- rngl_sin_add in Hzs12.
    eapply (rngl_le_trans Hor); [ apply Hzs12 | ].
    rewrite <- (rngl_mul_1_r Hon (rngl_sin θ1)) at 2.
    apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
    apply rngl_sin_bound.
  } {
    apply (rngl_nle_gt Hor) in Hzs1.
    assert (Hc2z : (rngl_cos θ2 ≤ 0)%L). {
      apply (rngl_nlt_ge Hor).
      intros Hzc2.
      apply (rngl_nlt_ge Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      apply (rngl_le_lt_trans Hor _ 0). {
        apply (rngl_lt_le_incl Hor) in Hzs1.
        now apply (rngl_mul_nonpos_nonneg Hop Hor).
      }
      now apply (rngl_mul_pos_pos Hop Hor Hii).
    }
    apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ (rngl_sin θ2)) in Hzs12. 2: {
      easy.
    }
    do 2 rewrite <- rngl_mul_assoc in Hzs12.
    rewrite fold_rngl_squ in Hzs12.
    specialize (cos2_sin2_1 θ2) as H.
    apply (rngl_add_move_l Hop) in H.
    rewrite H in Hzs12; clear H.
    rewrite (rngl_mul_sub_distr_l Hop) in Hzs12.
    rewrite (rngl_mul_1_r Hon) in Hzs12.
    apply (rngl_le_add_le_sub_r Hop Hor) in Hzs12.
    progress unfold rngl_squ in Hzs12.
    do 2 rewrite (rngl_mul_comm Hic _ (_ * _)) in Hzs12.
    do 2 rewrite <- rngl_mul_assoc in Hzs12.
    rewrite <- rngl_mul_add_distr_l in Hzs12.
    rewrite <- rngl_sin_add in Hzs12.
    eapply (rngl_le_trans Hor); [ | apply Hzs12 ].
    rewrite <- (rngl_mul_1_r Hon (rngl_cos θ2)) at 1.
    apply (rngl_mul_le_mono_nonpos_l Hop Hor); [ easy | ].
    apply rngl_sin_bound.
  }
} {
  apply angle_nle_gt in H21.
  apply H21; clear H21.
  progress unfold angle_leb.
  rewrite <- angle_opp_add_distr.
  rewrite angle_add_comm.
  rewrite angle_opp_add_distr.
  rewrite rngl_sin_sub_right_r.
  cbn.
  rewrite (rngl_leb_0_opp Hop Hor).
  apply (rngl_leb_gt Hor) in Hs1z.
  rewrite Hs1z.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  symmetry in Hzs2.
  destruct zs2; [ easy | ].
  apply rngl_leb_le.
  rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_sub_0_l Hop).
  rewrite <- (rngl_mul_opp_r Hop).
  rewrite (rngl_opp_involutive Hop).
  rewrite (rngl_mul_1_r Hon).
  apply (rngl_leb_gt Hor) in Hs1z, Hzs2.
  apply (rngl_le_opp_r Hop Hor).
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    change_angle_add_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzc2.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_goal T.
    destruct (rngl_lt_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hc1z]. {
      exfalso.
      apply (rngl_nlt_ge Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      apply (rngl_lt_le_incl Hor) in Hs1z.
      now apply rngl_sin_add_pos_2.
    }
    apply (rngl_nlt_ge Hor) in Hc1z.
    change_angle_opp θ1.
    progress sin_cos_opp_hyp T Hs1z.
    progress sin_cos_opp_hyp T Hc1z.
    rewrite angle_add_opp_l in Hzs12.
    rewrite rngl_sin_sub_anticomm in Hzs12.
    apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc1z, Hzs12.
    cbn.
    rewrite (rngl_add_opp_r Hop).
    apply (rngl_le_sub_0 Hop Hor).
    apply (rngl_lt_le_incl Hor) in Hs1z.
    now apply rngl_sin_sub_nonneg_sin_le_sin.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  change_angle_add_r θ2 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_l Hop).
  apply (rngl_le_sub_0 Hop Hor).
  destruct (rngl_le_dec Hor (rngl_sin θ1) 0) as [Hzs1| Hzs1]. {
    apply (rngl_lt_le_incl Hor) in Hc2z.
    now apply (rngl_le_trans Hor _ 0).
  }
  apply (rngl_nle_gt Hor) in Hzs1.
  change_angle_sub_l θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hs1z.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_goal T.
  apply (rngl_lt_le_incl Hor) in Hs1z, Hc2z, Hzs2, Hzs1.
  now apply quadrant_1_sin_sub_nonneg_cos_le.
}
Qed.

Theorem angle_lt_rngl_sin_add_nonneg_sin_nonneg :
  ∀ θ1 θ2,
  (θ2 < - θ1)%A ∨ (angle_straight - θ1 < θ2)%A
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin θ1)%L.
Proof.
destruct_ac.
intros * H21 Hzs12.
apply (rngl_nlt_ge Hor).
intros Hs1z.
change_angle_add_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hs1z.
progress sin_cos_add_sub_right_hyp T Hzs12.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
rewrite angle_opp_sub_distr in H21.
rewrite <- angle_opp_straight in H21.
rewrite <- angle_opp_add_distr in H21.
rewrite <- angle_add_sub_swap in H21.
rewrite <- angle_add_sub_assoc in H21.
rewrite angle_straight_sub_right in H21.
rewrite angle_opp_add_distr in H21.
now apply angle_lt_rngl_cos_add_pos.
Qed.

Theorem angle_add_overflow_if :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (θ1 = 0 ∨ θ2 < - θ1)%A.
Proof.
intros * Haov.
apply angle_add_not_overflow_comm in Haov.
now apply angle_add_not_overflow_equiv3 in Haov.
Qed.

Theorem rngl_sin_add_nonneg_sin_nonneg :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin θ1)%L.
Proof.
destruct_ac.
intros * Haov12 Hzs12.
apply angle_add_overflow_if in Haov12.
destruct Haov12 as [H| H]. {
  subst θ1.
  apply (rngl_le_refl Hor).
}
apply (angle_lt_rngl_sin_add_nonneg_sin_nonneg _ θ2); [ | easy ].
now left.
Qed.

Theorem rngl_cos_add_nonneg_cos_add_nonneg :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin θ2 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos (θ1 + θ3))%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc1 Hzc2 Hzc3 H23 Hzc13.
eapply (rngl_le_trans Hor); [ apply Hzc13 | cbn ].
apply (rngl_sub_le_compat Hop Hor). {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
  generalize H23; intros H32.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff in H32.
}
now apply (rngl_mul_le_mono_nonneg_l Hop Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_1 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs2 Hzs3 Hzc1 Hzs12 Hzs13 H23.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; [ | easy ].
apply angle_le_sub_le_add_l_lemma_1; try easy. {
  rewrite angle_add_comm.
  now rewrite angle_add_sub.
} {
  rewrite angle_add_comm.
  now rewrite angle_add_sub.
}
Qed.

Theorem angle_add_le_mono_l_lemma_2 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ1 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs1 Hzs2 Hzs3 Hc1z Hzs12 Hzs13 H23.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
specialize rngl_sin_nonneg_cos_le_sin_le as H1.
specialize (H1 θ3 θ2 Hzs3 Hzs2 H23).
destruct (rngl_le_dec Hor 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
  move Hzc3 before Hzs1.
  apply rngl_leb_le in Hzc3.
  rewrite Hzc3 in H1.
  rename H1 into Hs23.
  apply rngl_leb_le in Hzc3.
  destruct (rngl_lt_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
    apply (rngl_nle_gt Hor) in Hc2z.
    exfalso; apply Hc2z; clear Hc2z.
    eapply (rngl_le_trans Hor); [ apply Hzc3 | easy ].
  }
  apply (rngl_nlt_ge Hor) in Hzc2.
  move Hzc2 before Hzs1.
  rename Hzs12 into Hzc12; rename Hzs13 into Hzc13.
  assert (Hzs12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
    apply (rngl_lt_le_incl Hor) in Hc1z.
    now apply rngl_sin_add_nonneg.
  }
  assert (Hzs13 : (0 ≤ rngl_sin (θ1 + θ3))%L). {
    apply (rngl_lt_le_incl Hor) in Hc1z.
    now apply rngl_sin_add_nonneg.
  }
  specialize rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff as H1.
  apply H1; try easy.
  clear H1.
  apply angle_add_le_mono_l_lemma_1; try easy.
  progress unfold angle_add_overflow.
  progress unfold angle_ltb.
  generalize Hc1z; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_leb_le in Hzs13.
  rewrite Hzs13.
  apply rngl_leb_le in Hzs13.
  apply (rngl_ltb_ge Hor).
  apply angle_le_sub_le_add_l_lemma_1; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  rewrite angle_sub_diag.
  apply rngl_cos_bound.
  rewrite angle_sub_diag.
  apply (rngl_le_refl Hor).
}
apply rngl_leb_nle in Hc3z.
rewrite Hc3z in H1.
apply (rngl_leb_gt Hor) in Hc3z.
apply (rngl_nlt_ge Hor) in Hzs13.
exfalso; apply Hzs13; clear Hzs13.
apply (rngl_lt_iff Hor).
split. {
  cbn.
  apply (rngl_le_sub_0 Hop Hor).
  apply (rngl_le_trans Hor _ 0).
  apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
intros Hc13.
apply (eq_rngl_cos_0) in Hc13.
destruct Hc13 as [Hc13| Hc13]. {
  apply angle_add_move_l in Hc13.
  subst θ3.
  apply (rngl_nle_gt Hor) in Hc3z.
  apply Hc3z.
  rewrite rngl_cos_sub_right_l.
  now apply (rngl_lt_le_incl Hor).
}
apply angle_add_move_l in Hc13.
subst θ3.
progress unfold angle_add_overflow in Haov13.
apply Bool.not_true_iff_false in Haov13.
apply Haov13; clear Haov13.
rewrite angle_add_sub_assoc.
rewrite angle_add_opp_r.
rewrite angle_add_sub.
rewrite angle_sub_diag.
progress unfold angle_ltb.
rewrite rngl_sin_add_right_r.
rewrite (rngl_leb_refl Hor).
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
rewrite rngl_cos_add_right_r.
apply (rngl_lt_opp_l Hop Hor); cbn.
apply (rngl_add_pos_nonneg Hor); [ easy | ].
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_3 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13 H23.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  move Hzc1 before Hzs3.
  now apply angle_add_le_mono_l_lemma_1.
}
apply (rngl_nle_gt Hor) in Hc1z.
move Hc1z before Hzs3.
destruct (rngl_le_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
  move Hzs1 after Hzs2.
  now apply angle_add_le_mono_l_lemma_2.
}
apply (rngl_nle_gt Hor) in Hs1z.
move Hs1z after Hzs2.
change_angle_sub_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hs1z.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress sin_cos_add_sub_straight_goal T.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ2))%L as [Hzc2| Hc2z]. {
  move Hzc2 before Hc1z.
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_pos_2.
}
apply (rngl_nlt_ge Hor) in Hc2z.
change_angle_sub_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc2z.
progress sin_cos_add_sub_right_hyp T H23.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
  move Hzc3 before Hzs2.
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_pos_2.
}
apply (rngl_nlt_ge Hor) in Hc3z.
change_angle_sub_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hc3z.
progress sin_cos_add_sub_right_hyp T H23.
progress sin_cos_add_sub_right_goal T.
generalize H23; intros H32.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff in H32; try easy.
move H32 before H23.
assert (Hs12z : (0 ≤ rngl_sin (θ1 + θ2))%L). {
  apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
  now apply rngl_sin_add_nonneg.
}
assert (Hs13z : (0 ≤ rngl_sin (θ1 + θ3))%L). {
  apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
  now apply rngl_sin_add_nonneg.
}
apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy.
apply angle_add_le_mono_l_lemma_1; try easy; cycle 1.
now apply (rngl_lt_le_incl Hor).
progress unfold angle_add_overflow.
progress unfold angle_ltb.
generalize Hs1z; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hs13z; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply (rngl_ltb_ge Hor).
apply quadrant_1_rngl_cos_add_le_cos_l; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_8 :
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_straight)%A = false
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 < rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Hzc1 Hzs2 Hc2z.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Haov12 Hzc1 Hzs2 Hc2z.
destruct (rngl_lt_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply rngl_sin_add_pos_2.
}
apply (rngl_nlt_ge Hor) in Hs1z.
apply (rngl_nle_gt Hor).
intros Hzs12.
change_angle_add_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hs1z.
progress unfold angle_add_overflow in Haov12.
apply Bool.not_true_iff_false in Haov12.
apply Haov12; clear Haov12.
rewrite angle_add_sub_assoc.
rewrite <- angle_add_sub_swap.
progress unfold angle_ltb.
rewrite rngl_sin_sub_straight_r.
rewrite rngl_sin_sub_right_r.
rewrite (rngl_opp_involutive Hop).
rewrite rngl_sin_sub_right_r.
generalize Hs1z; intros H.
apply (rngl_lt_eq_cases Hor) in H.
destruct H as [H| H]. {
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_leb_gt Hor) in H.
  rewrite H; clear H.
  rewrite rngl_cos_sub_straight_r.
  do 2 rewrite rngl_cos_sub_right_r.
  destruct (0 ≤? rngl_cos _)%L; [ easy | ].
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor).
  apply (rngl_add_pos_nonneg Hor); [ | easy ].
  apply (rngl_lt_iff Hor).
  split. {
    apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z.
    now apply rngl_sin_add_nonneg.
  }
  intros H; symmetry in H.
  apply (eq_rngl_sin_0) in H.
  destruct H as [H| H]. {
    apply angle_add_move_l in H.
    rewrite angle_sub_0_l in H.
    subst θ2.
    cbn in Hzs2.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
    now apply (rngl_nle_gt Hor) in Hzs2.
  }
  apply angle_add_move_l in H.
  subst θ2.
  rewrite rngl_cos_sub_straight_l in Hc2z.
  apply (rngl_opp_pos_neg Hop Hor) in Hc2z.
  now apply (rngl_nle_gt Hor) in Hc2z.
}
exfalso.
symmetry in H.
apply (eq_rngl_cos_0) in H.
destruct H; subst θ1. {
  rewrite rngl_cos_add_right_l in Hzs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
  now apply (rngl_nlt_ge Hor) in Hzs12.
}
apply (rngl_nlt_ge Hor) in Hzc1.
apply Hzc1.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

Theorem angle_add_le_mono_l_lemma_9 :
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_straight)%A = false
  → (rngl_cos θ1 < 0)%L
  → (rngl_sin θ1 < 0)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov12 Hc1z Hs1z.
apply (rngl_nle_gt Hor).
intros Hzs12.
change_angle_add_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hs1z.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress unfold angle_add_overflow in Haov12.
apply Bool.not_true_iff_false in Haov12.
apply Haov12; clear Haov12.
rewrite angle_add_sub_assoc.
rewrite <- angle_add_sub_swap.
rewrite <- angle_sub_add_distr.
rewrite angle_straight_add_straight.
rewrite angle_sub_0_r.
progress unfold angle_ltb.
rewrite rngl_sin_sub_straight_r.
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
rewrite rngl_cos_sub_straight_r.
apply rngl_leb_le in Hzs12.
now rewrite Hzs12.
Qed.

Theorem angle_add_le_mono_l_lemma_11 :
  ∀ θ1 θ2,
  (rngl_sin θ2 < 0)%L
  → (rngl_cos θ2 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → angle_add_overflow θ1 θ2 = true.
Proof.
destruct_ac.
intros * Hzs2 Hc2z Hzs12.
change_angle_add_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hc2z.
progress sin_cos_add_sub_straight_hyp T Hzs2.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Bool.not_false_iff_true.
  intros H.
  apply Hzs12; clear Hzs12.
  now apply angle_add_le_mono_l_lemma_8.
}
apply (rngl_nle_gt Hor) in Hc1z.
destruct (rngl_lt_dec Hor (rngl_sin θ1) 0)%L as [Hs1z| Hzs1]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Bool.not_false_iff_true.
  intros H.
  apply Hzs12; clear Hzs12.
  now apply angle_add_le_mono_l_lemma_9.
}
apply (rngl_nlt_ge Hor) in Hzs1.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress unfold angle_add_overflow.
rewrite angle_add_sub_assoc.
rewrite angle_add_add_swap.
rewrite angle_add_sub_swap.
rewrite <- angle_sub_sub_distr.
rewrite angle_straight_sub_right.
progress unfold angle_ltb.
rewrite rngl_sin_sub_right_r.
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite rngl_sin_add_right_r.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
rewrite rngl_cos_add_right_r.
rewrite rngl_cos_sub_right_r.
apply rngl_ltb_lt.
apply (rngl_lt_le_trans Hor _ 0); [ now apply (rngl_opp_neg_pos Hop Hor) | ].
apply (rngl_lt_le_incl Hor) in Hc1z, Hzs2, Hc2z.
now apply rngl_sin_add_nonneg.
Qed.

Theorem angle_add_le_mono_l_lemma_4 :
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_right)%A = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → False.
Proof.
destruct_ac.
intros * Haov12 Hzs1 Hzc2 Hzc1 Hzs2 Hzs12.
progress unfold angle_add_overflow in Haov12.
apply Bool.not_true_iff_false in Haov12.
apply Haov12; clear Haov12.
rewrite angle_add_sub_assoc.
progress unfold angle_ltb.
rewrite rngl_sin_sub_right_r.
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
rewrite rngl_cos_sub_right_r.
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzc2.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_goal T.
rewrite rngl_cos_sub_comm.
apply (rngl_lt_iff Hor).
split. {
  rewrite rngl_cos_sub_comm.
  apply quadrant_1_sin_sub_nonneg_cos_le; try easy. {
    cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  } {
    rewrite angle_sub_sub_distr.
    rewrite angle_sub_diag.
    rewrite angle_add_0_l.
    now apply (rngl_lt_le_incl Hor).
  }
}
intros H.
apply rngl_cos_eq in H.
destruct H. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  rewrite rngl_sin_sub_anticomm.
  rewrite <- H.
  apply (rngl_opp_neg_pos Hop Hor).
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H1; symmetry in H1.
  apply (eq_rngl_sin_0) in H1.
  move H1 at top.
  destruct H1; subst θ1. {
    rewrite angle_sub_0_r in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  apply angle_add_move_r in H.
  rewrite angle_straight_add_straight in H.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
rewrite angle_opp_sub_distr in H.
apply angle_sub_move_l in H.
rewrite angle_sub_diag in H.
subst θ2.
now apply (rngl_lt_irrefl Hor) in Hzs2.
Qed.

Theorem angle_add_le_mono_l_lemma_5 :
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_right)%A = false
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (rngl_sin θ1 < 0)%L
  → False.
Proof.
destruct_ac.
intros * Haov12 Hzs12 Hs1z.
progress unfold angle_add_overflow in Haov12.
apply Bool.not_true_iff_false in Haov12.
apply Haov12; clear Haov12.
rewrite angle_add_sub_assoc.
progress unfold angle_ltb.
rewrite rngl_sin_sub_right_r.
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hs1z; intros H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
now rewrite H.
Qed.

Theorem angle_add_le_mono_l_lemma_6 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 (θ3 - angle_right)%A = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ2 ≤ 0)%L
  → (0 < rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → (rngl_sin (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs2 Hzc3 Hc2z Hzs3 Hzs12 Hzs13.
change_angle_sub_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc2z.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  exfalso.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
    now apply angle_add_le_mono_l_lemma_4 in Hzs13.
  } {
    apply (rngl_nle_gt Hor) in Hs1z.
    now apply angle_add_le_mono_l_lemma_5 in Hzs13.
  }
}
apply (rngl_nle_gt Hor) in Hc1z.
destruct (rngl_le_dec Hor (rngl_sin θ1) 0)%L as [Hs1z| Hzs1]. {
  apply (rngl_add_nonpos_nonpos Hor); cbn.
  apply (rngl_add_nonpos_nonpos Hor); cbn.
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_add_nonpos_nonpos Hor); cbn.
  now apply (rngl_mul_nonpos_nonneg Hop Hor).
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
exfalso.
apply (rngl_nle_gt Hor) in Hzs1.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_lt_le_incl Hor) in Hzs1, Hc1z.
  now apply rngl_sin_add_nonneg.
}
intros H; symmetry in H.
apply (eq_rngl_sin_0) in H.
destruct H as [H| H]. {
  apply angle_add_move_l in H.
  rewrite angle_sub_0_l in H.
  subst θ2.
  cbn in Hc2z.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
  now apply (rngl_nlt_ge Hor) in Hc2z.
}
apply angle_add_move_l in H.
subst θ2.
rewrite rngl_cos_sub_straight_l in Hzs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
now apply (rngl_nlt_ge Hor) in Hzs2.
Qed.

Theorem angle_add_le_mono_l_lemma_7 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13 Hzc3.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13 Hzc3.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; [ | easy ].
change_angle_add_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hzc3.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
  now apply angle_add_le_mono_l_lemma_6.
}
apply (rngl_nle_gt Hor) in Hzc2.
move Hzc2 after Hzs3.
apply (rngl_nlt_ge Hor).
intros H123.
progress unfold angle_add_overflow in Haov13.
apply Bool.not_true_iff_false in Haov13.
apply Haov13; clear Haov13.
rewrite angle_add_sub_assoc.
progress unfold angle_ltb.
rewrite rngl_sin_sub_right_r.
generalize Hzs13; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
rewrite rngl_cos_sub_right_r.
apply rngl_ltb_lt.
change_angle_sub_l θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzc3.
progress sin_cos_add_sub_right_hyp T H123.
progress sin_cos_add_sub_right_goal T.
rewrite rngl_cos_sub_comm in H123 |-*.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  destruct (rngl_eq_dec Heo 0 (rngl_sin (θ1 - θ3)))
      as [Hzs1s3| Hs1s3z]. {
    symmetry in Hzs1s3.
    apply (eq_rngl_sin_0) in Hzs1s3.
    destruct Hzs1s3 as [H| H]. {
      apply -> (angle_sub_move_0_r) in H.
      subst θ3.
      rewrite angle_sub_diag in H123 |-*.
      cbn.
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_cos_bound | ].
      intros H.
      apply (eq_rngl_cos_1) in H.
      subst θ1.
      now apply (rngl_lt_irrefl Hor) in Hzs3.
    }
    apply angle_sub_move_l in H.
    subst θ3.
    rewrite rngl_sin_sub_straight_r in Hzs3.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs3.
    now apply (rngl_nle_gt Hor) in Hzs3.
  }
  apply not_eq_sym in Hs1s3z.
  apply rngl_cos_lt_rngl_cos_sub; try easy.
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply rngl_sin_sub_nonneg_sin_le_sin.
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T H123.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_eq_dec Heo (rngl_cos θ3) 1) as [Hc31| Hc31]. {
  apply (eq_rngl_cos_1) in Hc31.
  subst θ3.
  now apply (rngl_lt_irrefl Hor) in Hzs3.
}
cbn.
rewrite rngl_add_assoc.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_mul_r_diag_r Hon Hop).
apply (rngl_add_pos_nonneg Hor).
apply (rngl_mul_pos_pos Hop Hor Hii); [ | easy ].
apply (rngl_lt_0_sub Hop Hor).
apply (rngl_lt_iff Hor).
split; [ | easy ].
apply rngl_cos_bound.
apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_12 :
  ∀ θ1 θ2 θ3,
  (0 < rngl_cos θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 < rngl_cos θ3)%L
  → (rngl_sin (θ1 + θ2) ≤ 0)%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → False.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzc1 Hzs2 Hc2z Hzc3 Hzs3 Hzs12 Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply rngl_sin_add_pos_1.
}
apply (rngl_nle_gt Hor) in Hs1z.
change_angle_add_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_hyp T Hs1z.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
apply (rngl_nlt_ge Hor) in Hzs13.
apply Hzs13; clear Hzs13.
apply (rngl_lt_le_incl Hor) in Hs1z.
now apply rngl_sin_add_pos_2.
Qed.

Theorem angle_add_le_mono_l_lemma_13 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ1 ≤ 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_sin (θ1 + θ2) ≤ 0)%L
  → angle_add_overflow θ1 (θ2 - angle_straight)%A = true.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzc3 Hc1z Hc2z Hzs12.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Hzs1 Hzs2 Hzc3 Hc1z Hc2z Hzs12.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress unfold angle_add_overflow.
rewrite angle_add_sub_assoc.
rewrite angle_add_add_swap.
rewrite angle_add_sub_swap.
rewrite <- angle_sub_sub_distr.
rewrite angle_straight_sub_right.
progress unfold angle_ltb.
rewrite rngl_sin_sub_right_r.
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite rngl_sin_add_right_r.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
rewrite rngl_cos_sub_right_r.
rewrite rngl_cos_add_right_r.
apply rngl_ltb_lt.
apply (rngl_lt_opp_l Hop Hor).
apply (rngl_lt_iff Hor).
split. {
  cbn.
  rewrite rngl_add_assoc.
  rewrite (rngl_add_mul_r_diag_l Hon).
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
intros H; symmetry in H.
apply (rngl_add_move_0_r Hop) in H.
generalize Hc1z; intros H1.
rewrite H in H1.
apply (rngl_opp_nonneg_nonpos Hop Hor) in H1.
apply (rngl_nlt_ge Hor) in H1.
apply H1; clear H1.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply rngl_sin_add_nonneg.
}
intros H1; symmetry in H1.
apply (eq_rngl_sin_0) in H1.
destruct H1 as [H1| H1]. {
  apply angle_add_move_l in H1.
  rewrite angle_sub_0_l in H1.
  subst θ2.
  cbn in Hzs2.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
  now apply (rngl_nlt_ge Hor) in Hzs2.
}
apply angle_add_move_l in H1.
subst θ2.
rewrite rngl_cos_sub_straight_l in Hc2z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
apply (rngl_le_antisymm Hor) in Hc2z; [ | easy ].
symmetry in Hc2z.
apply (eq_rngl_cos_0) in Hc2z.
destruct Hc2z; subst θ1. {
  rewrite angle_straight_sub_right in H.
  rewrite angle_right_add_right in H.
  cbn in H.
  rewrite (rngl_opp_0 Hop) in H.
  now apply (rngl_1_eq_0_iff Hon Hos) in H.
}
apply (rngl_nlt_ge Hor) in Hc1z.
apply Hc1z; cbn.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

Theorem angle_add_le_mono_l_lemma_14 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 (θ3 - angle_right)%A = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 < rngl_cos θ3)%L
  → (rngl_sin θ2 ≤ rngl_sin θ3)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → (rngl_sin (θ1 + θ3) ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs1 Hzc2 Hzc3 Hzc1 Hzs2 Hzs3 H23 Hzs12 Hzs13.
apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy. {
  apply (rngl_lt_le_incl Hor) in Hzs3.
  now apply rngl_sin_add_nonneg.
} {
  apply (rngl_lt_le_incl Hor) in Hzc2.
  now apply rngl_sin_add_nonneg.
}
apply angle_add_le_mono_l_lemma_3; try easy. {
  apply angle_add_overflow_le with (θ2 := (θ3 - angle_right)%A);
    try easy.
  progress unfold angle_leb.
  apply rngl_leb_le in Hzc3.
  rewrite Hzc3.
  apply rngl_leb_le in Hzc3.
  rewrite rngl_sin_sub_right_r.
  generalize Hzs3; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  now rewrite H.
} {
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_lt_le_incl Hor) in Hzc2.
  now apply rngl_sin_add_nonneg.
} {
  apply (rngl_lt_le_incl Hor) in Hzs3.
  now apply rngl_sin_add_nonneg.
}
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_16 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ1 θ3 = false
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov12 Haov13 Hzs2 Hzs3 Hzc3 H23 Hzs12 Hzs13.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
change_angle_add_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T H23.
progress sin_cos_add_sub_right_hyp T Hzc3.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
  exfalso.
  change_angle_add_r θ2 angle_straight.
  progress sin_cos_add_sub_straight_hyp T H23.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
    now apply (angle_add_le_mono_l_lemma_12 θ1 θ2 θ3).
  } {
    apply (rngl_nlt_ge Hor) in Hc1z.
    apply Bool.not_true_iff_false in Haov12.
    apply Haov12.
    now apply (angle_add_le_mono_l_lemma_13 _ _ θ3).
  }
}
apply (rngl_nle_gt Hor) in Hzc2.
change_angle_add_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T H23.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hzc2.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply angle_add_le_mono_l_lemma_14.
}
apply (rngl_nle_gt Hor) in Hc1z.
apply (rngl_nlt_ge Hor).
intros Hs123.
progress unfold angle_add_overflow in Haov12.
apply Bool.not_true_iff_false in Haov12.
apply Haov12; clear Haov12.
rewrite angle_add_sub_assoc.
progress unfold angle_ltb.
rewrite rngl_sin_sub_right_r.
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
rewrite rngl_cos_sub_right_r.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hs123.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
cbn.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
rewrite <- (rngl_add_sub_assoc Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
apply (rngl_add_nonneg_pos Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
apply (rngl_lt_0_sub Hop Hor).
apply (rngl_lt_iff Hor).
split; [ apply rngl_sin_bound | ].
intros H.
apply (eq_rngl_sin_1) in H.
subst θ2.
now apply (rngl_lt_irrefl Hor) in Hzs2.
Qed.

Theorem angle_add_le_mono_l_lemma_18 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Hzs1 Hzs2 Hzs3 Hzc3 H32 Hzs12.
  rewrite (H1 (rngl_sin _)).
  apply (rngl_le_refl Hor).
}
intros * Haov12 Hzs1 Hzs2 Hzs3 Hzc3 H32 Hzs12.
apply (rngl_nlt_ge Hor).
intros Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  now apply rngl_sin_add_nonneg.
}
apply (rngl_nle_gt Hor) in Hc1z.
move Hc1z after Hzc3.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  move Hzc2 before Hzc3.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply rngl_cos_add_nonneg_cos_add_nonneg with (θ3 := θ2); try easy.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
}
apply (rngl_nle_gt Hor) in Hc2z.
change_angle_sub_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T H32.
progress sin_cos_add_sub_right_hyp T Hc2z.
progress sin_cos_add_sub_right_hyp T Hzs12.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [H| H]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_pos_1.
}
apply (rngl_nlt_ge Hor) in H.
apply (rngl_le_antisymm Hor) in H; [ | easy ].
symmetry in H.
apply (eq_rngl_cos_0) in H.
destruct H; subst θ1. {
  rewrite rngl_sin_add_right_l in Hzs12.
  apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
  symmetry in Hzs12.
  apply (eq_rngl_cos_0) in Hzs12.
  destruct Hzs12; subst θ2. {
    rewrite angle_right_add_right in Haov12.
    now rewrite angle_add_overflow_straight_straight in Haov12.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  apply Hc2z; cbn.
  apply (rngl_opp_1_le_0 Hon Hop Hor).
}
apply (rngl_nlt_ge Hor) in Hc1z.
apply Hc1z.
apply (rngl_opp_1_le_0 Hon Hop Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_10 :
  ∀ θ1 θ2,
  angle_add_overflow (θ1 + angle_right)%A θ2 = false
  → (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L
  → (0 < rngl_cos θ2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Hc1z Hzs2 Hzs1 Hzs12.
  rewrite (H1 (rngl_sin _)) in Hc1z.
  now apply (rngl_lt_irrefl Hor) in Hc1z.
}
intros * Haov12 Hc1z Hzs2 Hzs1 Hzs12.
apply (rngl_nle_gt Hor).
intros Hc2z.
change_angle_sub_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc2z.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_nonneg.
}
intros H; symmetry in H.
apply (eq_rngl_sin_0) in H.
destruct H as [H| H]. {
  apply angle_add_move_l in H.
  rewrite angle_sub_0_l in H.
  subst θ2.
  cbn in Hc2z.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
  now apply (rngl_nlt_ge Hor) in Hc2z.
}
apply angle_add_move_l in H.
subst θ2.
rewrite rngl_cos_sub_straight_l in Hzs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
symmetry in Hzs2.
apply (eq_rngl_cos_0) in Hzs2.
destruct Hzs2; subst θ1. {
  progress unfold angle_add_overflow in Haov12.
  apply Bool.not_true_iff_false in Haov12.
  apply Haov12; clear Haov12.
  rewrite angle_right_add_right.
  rewrite angle_sub_add.
  rewrite angle_straight_add_straight.
  progress unfold angle_ltb; cbn.
  rewrite (rngl_leb_refl Hor).
  apply rngl_ltb_lt.
  apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
}
rewrite angle_sub_opp_r in Hc2z.
rewrite rngl_sin_add_right_r in Hc2z.
apply (rngl_nlt_ge Hor) in Hc2z.
apply Hc2z; clear Hc2z; cbn.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

Theorem angle_add_le_mono_l_lemma_19 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs2 Hzs3 H23 Hzs13.
apply (rngl_nlt_ge Hor).
intros Hzs12.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
move Hzs1 after Hzs2.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  move Hzc2 after Hzs3.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply angle_add_le_mono_l_lemma_18 with (θ2 := θ3).
} {
  apply (rngl_nle_gt Hor) in Hc2z.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply (rngl_nlt_ge Hor) in H23.
    apply H23; clear H23.
    now apply (rngl_add_nonneg_pos Hor).
  }
  apply (rngl_nle_gt Hor) in Hc3z.
  change_angle_sub_r θ3 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hc3z.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    apply (rngl_lt_le_incl Hor) in Hc2z, Hc3z.
    now apply rngl_cos_add_nonneg_cos_add_nonneg with (θ3 := θ3).
  } {
    exfalso.
    apply (rngl_nle_gt Hor) in Hc1z.
(*
clear - ac θ1 θ3 Hzs13 Hzs1 Haov13 Hc1z Hc3z Hzs3.
(**)
destruct_ac.
    destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
      specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
      rewrite (H1 (rngl_cos θ1)) in Hc1z.
      now apply (rngl_lt_irrefl Hor) in Hc1z.
    }
    change_angle_sub_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    progress sin_cos_add_sub_right_hyp T Hc1z.
(*
theorem angle_add_overflow_move_add removed from git
*)
apply angle_add_not_overflow_move_add in Haov13.
rewrite <- angle_add_assoc in Haov13.
rewrite angle_right_add_right in Haov13.
apply angle_add_not_overflow_comm in Haov13.
rewrite angle_add_comm in Haov13.
apply angle_add_not_overflow_move_add in Haov13.
apply angle_add_not_overflow_comm in Haov13.
Search (angle_add_overflow _ angle_straight).
Search (angle_add_overflow angle_straight).
(* bon, y aurait des trucs à faire mais chais pas lesquels *)
...
Check angle_add_not_overflow_move_add.
...
    specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
    destruct (rngl_eq_dec Heo (rngl_cos θ3) 0) as [H| H]. {
      apply eq_rngl_cos_0 in H.
      destruct H; subst θ3. {
        rewrite rngl_sin_add_right_r in Hzs13.
        apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
        apply eq_rngl_cos_0 in Hzs1.
        destruct Hzs1; subst θ1. {
          rewrite angle_right_add_right in Haov13.
          now rewrite angle_add_overflow_straight_straight in Haov13.
        }
        apply (rngl_nle_gt Hor) in Hc1z.
        apply Hc1z; clear Hc1z.
        apply (rngl_opp_1_le_0 Hon Hop Hor).
      }
      apply (rngl_nle_gt Hor) in Hc3z.
      apply Hc3z; clear Hc3z.
      apply (rngl_opp_1_le_0 Hon Hop Hor).
    }
    apply (rngl_nlt_ge Hor) in Hzs13.
    apply Hzs13; clear Hzs13.
    apply rngl_sin_add_pos_2; try easy.
    now apply (rngl_lt_le_incl Hor) in Hc3z.
    now apply (rngl_lt_iff Hor).
...
*)
    rewrite angle_add_comm in Hzs13.
    apply (rngl_nle_gt Hor) in Hc1z.
    apply Hc1z; clear Hc1z.
    apply (rngl_lt_le_incl Hor).
    apply angle_add_not_overflow_comm in Haov13.
    now apply (angle_add_le_mono_l_lemma_10 θ3).
  }
}
Qed.

Theorem angle_add_le_mono_l_lemma_20 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 < rngl_cos θ3)%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_sin (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos (θ1 + θ3))%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros * Hzs2 Hzs3 Hzc3 H23 Hzs12 Hzs13.
assert (Hzc2 : (0 < rngl_cos θ2)%L). {
  eapply (rngl_lt_le_trans Hor); [ apply Hzc3 | apply H23 ].
}
destruct (rngl_lt_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    exfalso.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; clear Hzs12.
    apply (rngl_lt_le_incl Hor) in Hzc2, Hzs1.
    now apply rngl_sin_add_nonneg.
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  change_angle_sub_l θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs13.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_goal T.
  rewrite rngl_sin_sub_anticomm in Hzs13, Hzs12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs13, Hzs12.
  do 2 rewrite (rngl_cos_sub_comm θ1).
  destruct (rngl_eq_dec Heo (rngl_sin θ2) (rngl_sin θ3)) as
    [Hes23| Hes23]. {
    apply rngl_sin_eq in Hes23.
    destruct Hes23; subst θ2; [ apply (rngl_le_refl Hor) | ].
    rewrite rngl_cos_sub_straight_l in H23.
    rewrite <- angle_sub_add_distr in Hzs12 |-*.
    rewrite rngl_sin_sub_straight_l in Hzs12.
    rewrite rngl_cos_sub_straight_l in Hzc2 |-*.
    apply (rngl_opp_pos_neg Hop Hor) in Hzc2.
    apply (rngl_le_opp_r Hop Hor).
    cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_add_sub_assoc Hop).
    rewrite rngl_add_add_swap.
    rewrite (rngl_add_sub Hos).
    rewrite <- rngl_mul_add_distr_r.
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ | ].
    apply (rngl_lt_le_incl Hor) in Hzc2.
    now apply (rngl_add_nonpos_nonpos Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nlt_ge Hor).
  intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_sin_sub_nonneg in H; try easy. {
    rewrite angle_sub_sub_distr in H.
    rewrite angle_sub_sub_swap in H.
    rewrite angle_sub_add in H.
    apply (rngl_nlt_ge Hor) in H.
    apply H; clear H.
    cbn.
    rewrite rngl_add_comm.
    eapply (rngl_le_lt_trans Hor). {
      apply (rngl_add_le_mono_l Hop Hor).
      apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
      apply H23.
    }
    rewrite (rngl_mul_comm Hic).
    rewrite <- rngl_mul_add_distr_r.
    rewrite (rngl_add_opp_l Hop).
    rewrite (rngl_mul_comm Hic).
    apply (rngl_mul_pos_neg Hop Hor); [ | easy | ]. {
      rewrite Bool.orb_true_iff; right.
      rewrite Hi1; cbn.
      apply (rngl_has_eq_dec_or_is_ordered_r Hor).
    }
    apply (rngl_lt_sub_0 Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ | easy ].
    apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nlt_ge Hor) in Hs1z.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hzc1| Hc1z]. {
  cbn.
  apply (rngl_sub_le_compat Hop Hor).
  now apply (rngl_mul_le_mono_nonpos_l Hop Hor).
  apply (rngl_mul_le_mono_nonpos_l Hop Hor); [ easy | ].
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_add_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hs1z.
progress sin_cos_add_sub_right_goal T.
assert (Hs12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
  apply (rngl_lt_le_incl Hor) in Hc1z, Hzc2.
  now apply rngl_sin_add_nonneg.
}
assert (Hs13 : (0 ≤ rngl_sin (θ1 + θ3))%L). {
  apply (rngl_lt_le_incl Hor) in Hc1z, Hzc3.
  now apply rngl_sin_add_nonneg.
}
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply angle_add_le_mono_l_lemma_3; try easy.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
generalize Hc1z; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hs13; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply (rngl_ltb_ge Hor).
apply quadrant_1_rngl_cos_add_le_cos_l; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_21 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_cos (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) + rngl_sin (θ1 + θ3) ≤ 0)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc2 Hzc3 Hzs12 Hzc13.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply rngl_sin_add_nonneg.
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hzc13.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_goal T.
rewrite -> (rngl_add_comm (- _))%L.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor (rngl_cos (θ1 + θ3)) 0) as [H| Hzs13]. {
  eapply (rngl_le_trans Hor); [ apply H | ].
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_nonneg.
}
apply (rngl_nle_gt Hor) in Hzs13.
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hzc2.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_goal T.
apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply (rngl_lt_le_incl Hor) in Hc1z.
now apply rngl_cos_sub_nonneg.
rewrite angle_sub_sub_distr.
rewrite angle_add_sub_swap.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
now apply rngl_sin_add_nonneg.
Qed.

Theorem angle_add_le_mono_l_lemma_22 :
  ∀ θ1 θ2 θ3,
  (rngl_sin θ1 < 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_cos (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) + rngl_sin (θ1 + θ3) ≤ 0)%L.
Proof.
destruct_ac.
intros * Hs1z Hzs2 Hzs3 Hzc2 Hzc3 Hs12z Hs13z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  exfalso.
  apply (rngl_nle_gt Hor) in Hs13z.
  apply Hs13z; clear Hs13z.
  now apply rngl_cos_add_nonneg.
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_add_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hs1z.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress sin_cos_add_sub_straight_hyp T Hs13z.
progress sin_cos_add_sub_straight_hyp T Hs12z.
progress sin_cos_add_sub_straight_goal T.
rewrite <- (rngl_opp_add_distr Hop).
apply (rngl_opp_nonpos_nonneg Hop Hor).
change_angle_sub_l θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hzc3.
progress sin_cos_add_sub_right_hyp T Hs13z.
progress sin_cos_add_sub_right_goal T.
rewrite rngl_sin_sub_anticomm in Hs13z.
rewrite rngl_cos_sub_comm.
progress sin_cos_add_sub_right_hyp T Hs13z.
apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
rewrite angle_add_assoc.
rewrite angle_sub_add.
now apply rngl_sin_add_nonneg.
apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
now apply rngl_cos_sub_nonneg.
Qed.

Theorem angle_add_le_mono_l_lemma_23 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (rngl_cos θ1 ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzc1 Hzc2 Hc12z.
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc12z.
progress sin_cos_add_sub_right_hyp T Hzc2.
progress sin_cos_add_sub_right_goal T.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
apply rngl_cos_sub_nonneg; try easy.
apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
rewrite angle_sub_sub_distr.
rewrite angle_sub_diag.
now rewrite angle_add_0_l.
Qed.

Theorem angle_add_le_mono_l_lemma_24 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_cos θ1 ≤ 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_cos θ1 ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hc1z Hzs2.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_goal T.
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_goal T.
apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
rewrite angle_sub_sub_distr.
rewrite angle_sub_diag.
now rewrite angle_add_0_l.
Qed.

Theorem angle_add_le_mono_l_lemma_25 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin θ2 ≤ rngl_sin θ3)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → (rngl_sin (θ1 + θ3) ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc1 Hzc2 Hzc3 H23 Hzc12 Hzc13.
assert (Hzs12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
  now apply rngl_sin_add_nonneg.
}
assert (Hzs13 : (0 ≤ rngl_sin (θ1 + θ3))%L). {
  now apply rngl_sin_add_nonneg.
}
apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy.
apply angle_add_le_mono_l_lemma_1; try easy; cycle 1.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
generalize Hzs13; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hzs1; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply (rngl_ltb_ge Hor).
now apply (rngl_le_trans Hor _ 0).
Qed.

Theorem angle_add_le_mono_l_lemma_26 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ1 ≤ 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin θ2 ≤ rngl_sin θ3)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → (rngl_sin (θ1 + θ3) ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hc1z Hzc2 Hzc3 Hs23 Hc12z Hc13z.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hc13z.
progress sin_cos_add_sub_right_hyp T Hc12z.
progress sin_cos_add_sub_right_goal T.
apply angle_add_le_mono_l_lemma_1; try easy; cycle 1.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
generalize Hc13z; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hc1z; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply (rngl_ltb_ge Hor).
now apply quadrant_1_rngl_cos_add_le_cos_l.
Qed.

Theorem angle_add_le_mono_l_lemma_27 :
  ∀ θ1 θ2 θ3,
  (rngl_sin θ1 < 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ1 < 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin θ2 ≤ rngl_sin θ3)%L
  → (rngl_cos (θ1 + θ2) < 0)%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → (rngl_sin (θ1 + θ3) ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hs1z Hc2z Hc3z Hc1z Hzs2 Hzs3 h23 Hzs12 Hzs13.
change_angle_add_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hs1z.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_goal T.
apply (rngl_lt_le_incl Hor) in Hc1z, Hs1z.
apply (rngl_lt_le_incl Hor) in Hzs12.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
apply rngl_sin_add_nonneg; try easy.
apply rngl_sin_add_nonneg; try easy.
apply angle_add_le_mono_l_lemma_3; try easy; cycle 1.
apply rngl_sin_add_nonneg; try easy.
apply rngl_sin_add_nonneg; try easy.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
generalize Hs1z; intros H.
apply (rngl_sin_add_nonneg θ3) in H; try easy.
rewrite angle_add_comm in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hs1z.
rewrite Hs1z.
apply rngl_leb_le in Hs1z.
apply (rngl_ltb_ge Hor).
now apply quadrant_1_rngl_cos_add_le_cos_l.
Qed.

Theorem angle_add_le_mono_l_lemma_28 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ3 ≤ 0)%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_sin (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos (θ1 + θ3))%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs2 Hzs3 Hc3z Hc32 Hs12z Hs13z.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs2 Hzs3 Hc3z Hc32 Hs12z Hs13z.
change_angle_sub_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hc32.
progress sin_cos_add_sub_right_hyp T Hc3z.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hs13z.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    now apply angle_add_le_mono_l_lemma_21.
  } {
    apply (rngl_nle_gt Hor) in Hs1z.
    now apply angle_add_le_mono_l_lemma_22.
  }
} {
  apply (rngl_nle_gt Hor) in Hc2z.
  apply (rngl_le_opp_l Hop Hor) in Hc32.
  move Hc2z after Hzs3; move Hc32 after Hs12z.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_hyp T Hc32.
  progress sin_cos_add_sub_right_hyp T Hs12z.
  progress sin_cos_add_sub_right_goal T.
  rewrite rngl_add_comm.
  rewrite (rngl_add_opp_r Hop).
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_eq_dec Heo (rngl_cos θ2) 0) as [H| Hc2ez]. {
    apply (eq_rngl_cos_0) in H.
    destruct H; subst θ2. {
      cbn in Hc32.
      specialize (rngl_sin_bound θ3) as H.
      apply (rngl_le_antisymm Hor) in Hc32; [ clear H | easy ].
      apply (eq_rngl_sin_1) in Hc32.
      subst θ3.
      apply (rngl_le_refl Hor).
    }
    exfalso.
    apply (rngl_nle_gt Hor) in Hc2z.
    apply Hc2z; cbn.
    apply (rngl_opp_1_le_0 Hon Hop Hor).
  }
  assert (H : (0 < rngl_cos θ2)%L). {
    apply not_eq_sym in Hc2ez.
    now apply (rngl_lt_iff Hor).
  }
  move H before Hzs2; clear Hzs2.
  rename H into Hzs2; clear Hc2ez.
  destruct (rngl_eq_dec Heo (rngl_cos θ3) 0) as [H| Hc3ez]. {
    apply (eq_rngl_cos_0) in H.
    destruct H; subst θ3. {
      clear Hc3z Hc32 Hzs3.
      rewrite rngl_sin_add_right_r.
      rewrite rngl_cos_add_right_r in Hs13z.
      apply (rngl_opp_neg_pos Hop Hor) in Hs13z.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
        apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hs13z, Hs12z.
        apply angle_add_le_mono_l_lemma_23; try easy.
      } {
        apply (rngl_nle_gt Hor) in Hc1z.
        apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hs13z, Hc1z.
        apply angle_add_le_mono_l_lemma_24; try easy.
      }
    }
    exfalso.
    apply (rngl_nlt_ge Hor) in Hc3z.
    apply Hc3z; cbn.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
  }
  assert (H : (0 < rngl_cos θ3)%L). {
    apply not_eq_sym in Hc3ez.
    now apply (rngl_lt_iff Hor).
  }
  move H before Hzs3; clear Hzs3.
  rename H into Hzs3; clear Hc3ez.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hzs3, Hs12z, Hs13z.
      now apply angle_add_le_mono_l_lemma_25.
    } {
      apply (rngl_nle_gt Hor) in Hc1z.
      apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hzs3, Hs12z, Hs13z.
      apply (rngl_lt_le_incl Hor) in Hc1z.
      now apply angle_add_le_mono_l_lemma_26.
    }
  } {
    apply (rngl_nle_gt Hor) in Hs1z.
    apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      exfalso.
      apply (rngl_nle_gt Hor) in Hs12z.
      apply Hs12z; clear Hs12z.
      now apply rngl_cos_add_nonneg.
    } {
      apply (rngl_nle_gt Hor) in Hc1z.
      apply (rngl_lt_le_incl Hor) in Hzs3, Hs13z.
      now apply angle_add_le_mono_l_lemma_27.
    }
  }
}
Qed.

Theorem angle_add_le_mono_l_lemma_29 :
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_cos θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin (θ1 + θ2) < rngl_sin θ1)%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs1 Hzc1 Hs2z.
change_angle_add_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hs2z.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_eq_dec Heo (rngl_sin θ2) 1) as [Hs21| Hs21]. {
  apply (eq_rngl_sin_1) in Hs21.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hs2z.
}
cbn.
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- (rngl_add_sub_assoc Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
apply (rngl_add_nonneg_pos Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
apply (rngl_lt_0_sub Hop Hor).
apply (rngl_lt_iff Hor).
split; [ | easy ].
apply rngl_sin_bound.
Qed.

Theorem angle_add_le_mono_l_lemma_30 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (rngl_cos θ1 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → angle_add_overflow θ1 θ2 = true.
Proof.
destruct_ac.
intros * Hzs1 Hs2z Hc1z Hzs12.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
generalize Hzs12; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
rewrite -> (rngl_add_opp_r Hop).
apply <- (rngl_lt_0_sub Hop Hor).
now apply angle_add_le_mono_l_lemma_29.
Qed.

Theorem angle_add_le_mono_l_lemma_31 :
  ∀ θ1 θ2,
  (0 < rngl_cos θ1)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → angle_add_overflow (θ1 - angle_right)%A θ2 = true.
Proof.
destruct_ac.
intros * Hzs1 Hc12z.
change_angle_add_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hc12z.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
rewrite rngl_sin_sub_right_r.
rewrite angle_add_sub_assoc.
rewrite <- angle_add_sub_swap.
rewrite rngl_sin_sub_right_r.
rewrite rngl_cos_sub_right_r.
generalize Hc12z; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hzs1; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
now rewrite H.
Qed.

Theorem angle_add_le_mono_l_lemma_32 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (rngl_sin θ1 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hs1z Hzs3 Hzc1 Hzs13.
change_angle_add_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hs1z.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_lt_dec Hor (rngl_cos θ3) 0) as [Hc3z| Hzc3]. {
  apply (rngl_nlt_ge Hor).
  intros Hzc12.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13; clear Haov13.
  apply angle_add_le_mono_l_lemma_11; try easy.
  rewrite <- angle_add_sub_swap.
  rewrite rngl_sin_sub_right_r.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
} {
  apply (rngl_nlt_ge Hor) in Hzc3.
  exfalso.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13; clear Haov13.
  now apply angle_add_le_mono_l_lemma_31.
}
Qed.

Theorem angle_add_le_mono_l_lemma_33 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin (θ1 + θ2) ≤ 0)%L
  → angle_add_overflow (θ1 - angle_straight)%A θ2 = true.
Proof.
destruct_ac.
intros * Hs1z Hzs2 Hzs12.
progress unfold angle_add_overflow.
rewrite <- angle_add_sub_swap.
progress unfold angle_ltb.
do 2 rewrite rngl_sin_sub_straight_r.
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hs1z; intros H.
apply (rngl_lt_eq_cases Hor) in H.
destruct H as [H| H]. {
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  now rewrite H.
}
do 2 rewrite rngl_cos_sub_straight_r.
rewrite <- H.
rewrite (rngl_opp_0 Hop).
rewrite (rngl_leb_refl Hor).
apply rngl_ltb_lt.
apply -> (rngl_opp_lt_compat Hop Hor).
symmetry in H.
apply (eq_rngl_sin_0) in H.
destruct H; subst θ1. {
  rewrite angle_add_0_l; cbn.
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  intros H.
  apply (eq_rngl_cos_1) in H.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
rewrite rngl_sin_add_straight_l in Hzs12.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs12.
now apply (rngl_nlt_ge Hor) in Hzs12.
Qed.

Theorem angle_add_le_mono_l_lemma_34 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (rngl_sin θ1 ≤ 0)%L
  → (0 < rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hs1z Hc2z Hzs3 Hzs2 Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  rewrite angle_add_comm.
  rewrite <- angle_sub_opp_r.
  apply (rngl_lt_le_incl Hor) in Hc2z.
  apply (rngl_opp_le_compat Hop Hor) in Hs1z.
  rewrite (rngl_opp_0 Hop) in Hs1z.
  rewrite <- rngl_sin_opp in Hs1z.
  now apply rngl_cos_sub_nonneg.
} {
  apply (rngl_nle_gt Hor) in Hc1z.
  change_angle_add_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hs1z.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  progress sin_cos_add_sub_straight_hyp T Hzs13.
  progress sin_cos_add_sub_straight_goal T.
  exfalso.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13; clear Haov13.
  now apply angle_add_le_mono_l_lemma_33.
}
Qed.

Theorem angle_add_le_mono_l_lemma_35 :
  ∀ θ1 θ2,
  (rngl_sin θ2 < 0)%L
  → (0 < rngl_sin θ1)%L
  → (rngl_cos θ1 ≤ 0)%L
  → (rngl_cos θ1 < rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs2 Hzs1 Hc1z.
change_angle_add_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_goal T.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_goal T.
cbn.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
rewrite <- (rngl_add_sub_assoc Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
apply (rngl_add_pos_nonneg Hor).
now apply (rngl_mul_pos_pos Hop Hor Hii).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
apply (rngl_le_0_sub Hop Hor).
apply rngl_sin_bound.
Qed.

Theorem angle_add_le_mono_l_lemma_37 :
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → angle_add_overflow θ1 θ2 = true.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzc2 Hzs12.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
generalize Hzs12; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hzs1; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_ltb_lt.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
  now apply angle_add_le_mono_l_lemma_35.
} {
  apply (rngl_nle_gt Hor) in Hzc1.
  apply (rngl_lt_le_incl Hor) in Hzs1, Hzc1.
  now apply quadrant_1_quadrant_4_cos_lt_cos_add.
}
Qed.

Theorem angle_add_le_mono_l_lemma_38 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 < rngl_sin θ1)%L
  → (rngl_sin θ3 < 0)%L
  → (rngl_cos θ3 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs1 Hzs3 Hc3z Hzs13.
change_angle_add_r θ3 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_hyp T Hc3z.
progress sin_cos_add_sub_straight_hyp T Hzs3.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply (rngl_sin_add_pos_1); try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nlt_ge Hor) in Hc1z.
exfalso.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
apply Bool.not_true_iff_false in Haov13.
apply Haov13; clear Haov13.
apply angle_add_le_mono_l_lemma_11; try easy.
rewrite rngl_sin_sub_straight_r.
now apply (rngl_opp_neg_pos Hop Hor).
rewrite rngl_cos_sub_straight_r.
now apply (rngl_opp_neg_pos Hop Hor).
rewrite angle_add_sub_assoc.
rewrite angle_add_add_swap.
rewrite angle_add_sub_swap.
rewrite <- angle_sub_sub_distr.
rewrite angle_straight_sub_right.
rewrite rngl_sin_sub_right_r.
now apply (rngl_opp_nonneg_nonpos Hop Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_40 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 (θ3 - angle_right)%A = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ2 ≤ 0)%L
  → (0 < rngl_cos θ3)%L
  → (0 < rngl_cos (θ1 + θ3))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_sin (θ1 + θ3))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov13 Hzs2 Hzc3 Hc2z Hzs3 Hzs13.
change_angle_sub_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc2z.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    apply (rngl_add_nonneg_nonneg Hor).
    now apply rngl_sin_add_nonneg.
    apply rngl_sin_add_nonneg; try easy.
    now apply (rngl_lt_le_incl Hor).
  }
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply (rngl_nle_gt Hor) in Hc1z.
  change_angle_sub_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hc1z.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_goal T.
  apply rngl_sin_add_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hs1z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  exfalso.
  change_angle_add_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_hyp T Hs1z.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13; clear Haov13.
  progress unfold angle_add_overflow.
  rewrite angle_add_sub_assoc.
  rewrite <- angle_add_sub_swap.
  rewrite <- angle_sub_add_distr.
  rewrite angle_right_add_right.
  progress unfold angle_ltb.
  rewrite rngl_sin_sub_straight_r.
  rewrite rngl_sin_sub_right_r.
  generalize Hzs13; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  generalize Hs1z; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  rewrite rngl_cos_sub_straight_r.
  rewrite rngl_cos_sub_right_r.
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor).
  cbn.
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_pos_nonneg Hor).
  now apply (rngl_mul_pos_pos Hop Hor Hii).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_sin_bound.
}
apply (rngl_nle_gt Hor) in Hc1z.
exfalso.
change_angle_add_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress sin_cos_add_sub_straight_hyp T Hs1z.
apply Bool.not_true_iff_false in Haov13.
apply Haov13; clear Haov13.
progress unfold angle_add_overflow.
rewrite angle_add_sub_assoc.
rewrite <- angle_add_sub_swap.
rewrite angle_sub_sub_swap.
progress unfold angle_ltb.
do 2 rewrite rngl_sin_sub_straight_r.
rewrite rngl_sin_sub_right_r.
rewrite (rngl_opp_involutive Hop).
generalize Hzs13; intros H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
do 2 rewrite rngl_cos_sub_straight_r.
rewrite rngl_cos_sub_right_r.
apply rngl_ltb_lt.
apply -> (rngl_opp_lt_compat Hop Hor).
change_angle_sub_l θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzc3.
progress sin_cos_add_sub_right_goal T.
rewrite rngl_cos_sub_comm.
apply rngl_cos_lt_rngl_cos_sub; try easy.
now apply (rngl_lt_le_incl Hor).
apply (rngl_lt_le_incl Hor) in Hc1z, Hzs3, Hs1z.
apply (rngl_lt_le_incl Hor).
apply quadrant_1_sin_sub_pos_cos_lt; try easy.
Qed.

Theorem angle_add_le_mono_l_lemma_41 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_sin (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos (θ1 + θ3))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov13 Hzs2 Hzs3 Hzc3 Hzs12 Hzs13.
change_angle_add_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hzc3.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
  now apply angle_add_le_mono_l_lemma_40.
} {
  apply (rngl_nle_gt Hor) in Hzc2.
  exfalso.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
      apply (rngl_nle_gt Hor) in Hzs13.
      apply Hzs13; clear Hzs13.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hc1z.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_goal T.
      apply rngl_sin_add_nonneg; try easy.
      now apply (rngl_lt_le_incl Hor).
    } {
      apply (rngl_nle_gt Hor) in Hzc1.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      apply rngl_sin_add_nonneg; try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    }
  } {
    apply (rngl_nle_gt Hor) in Hs1z.
    destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
      change_angle_add_r θ1 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hzs13.
      progress sin_cos_add_sub_straight_hyp T Hc1z.
      progress sin_cos_add_sub_straight_hyp T Hs1z.
      apply Bool.not_true_iff_false in Haov13.
      apply Haov13; clear Haov13.
      progress unfold angle_add_overflow.
      rewrite angle_add_sub_assoc.
      rewrite <- angle_add_sub_swap.
      rewrite angle_sub_sub_swap.
      progress unfold angle_ltb.
      do 2 rewrite rngl_sin_sub_straight_r.
      rewrite rngl_sin_sub_right_r.
      rewrite (rngl_opp_involutive Hop).
      generalize Hzs13; intros H.
      apply (rngl_nle_gt Hor) in H.
      apply rngl_leb_nle in H.
      rewrite H; clear H.
      generalize Hs1z; intros H.
      apply (rngl_opp_lt_compat Hop Hor) in H.
      rewrite (rngl_opp_0 Hop) in H.
      apply (rngl_nle_gt Hor) in H.
      apply rngl_leb_nle in H.
      rewrite H; clear H.
      apply rngl_ltb_lt.
      progress sin_cos_add_sub_straight_goal T.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_lt_0_sub Hop Hor).
      change_angle_sub_l θ3 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs3.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hzc3.
      progress sin_cos_add_sub_right_goal T.
      rewrite rngl_cos_sub_comm.
      apply rngl_cos_lt_rngl_cos_sub; try easy.
      now apply (rngl_lt_le_incl Hor).
      apply (rngl_lt_le_incl Hor).
      apply quadrant_1_sin_sub_pos_cos_lt; try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    } {
      apply (rngl_nle_gt Hor) in Hzc1.
      change_angle_add_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_hyp T Hs1z.
      apply Bool.not_true_iff_false in Haov13.
      apply Haov13; clear Haov13.
      progress unfold angle_add_overflow.
      rewrite angle_add_sub_assoc.
      rewrite <- angle_add_sub_swap.
      rewrite <- angle_sub_add_distr.
      rewrite angle_right_add_right.
      progress unfold angle_ltb.
      rewrite rngl_sin_sub_straight_r.
      rewrite rngl_sin_sub_right_r.
      generalize Hzs13; intros H.
      apply (rngl_opp_lt_compat Hop Hor) in H.
      rewrite (rngl_opp_0 Hop) in H.
      apply (rngl_nle_gt Hor) in H.
      apply rngl_leb_nle in H.
      rewrite H; clear H.
      generalize Hs1z; intros H.
      apply (rngl_opp_lt_compat Hop Hor) in H.
      rewrite (rngl_opp_0 Hop) in H.
      apply (rngl_nle_gt Hor) in H.
      apply rngl_leb_nle in H.
      rewrite H; clear H.
      rewrite rngl_cos_sub_straight_r.
      rewrite rngl_cos_sub_right_r.
      apply rngl_ltb_lt.
      apply (rngl_lt_opp_l Hop Hor).
      cbn.
      rewrite <- (rngl_add_sub_swap Hop).
      rewrite <- (rngl_add_sub_assoc Hop).
      rewrite (rngl_sub_mul_r_diag_l Hon Hop).
      apply (rngl_lt_le_incl Hor) in Hzc1.
      apply (rngl_add_pos_nonneg Hor).
      now apply (rngl_mul_pos_pos Hop Hor Hii).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      apply (rngl_le_0_sub Hop Hor).
      apply rngl_sin_bound.
    }
  }
}
Qed.

Theorem angle_add_le_mono_l_lemma_42 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc1 Hzc2 Hzc3 Hc12z Hzc13.
change_angle_sub_l θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hc12z.
progress sin_cos_add_sub_right_hyp T Hzc13.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_goal T.
rewrite rngl_sin_sub_anticomm in Hc12z.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc12z.
apply (rngl_nlt_ge Hor).
intros Hc12s13.
assert (Hzs13 : (0 ≤ rngl_sin (θ1 - θ3))%L). {
  apply (rngl_lt_le_incl Hor) in Hc12s13.
  eapply (rngl_le_trans Hor); [ | apply Hc12s13 ].
  now apply rngl_cos_sub_nonneg.
}
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc12z.
progress sin_cos_add_sub_right_hyp T Hzc2.
progress sin_cos_add_sub_right_hyp T Hc12s13.
rewrite angle_add_comm in Hc12s13.
apply (rngl_nle_gt Hor) in Hc12s13.
apply Hc12s13; clear Hc12s13.
destruct (rngl_le_dec Hor (rngl_cos θ3) (rngl_cos θ2)) as [Hc32| Hc23]. {
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_le_sub_le_add_l Hop Hor).
  rewrite rngl_add_assoc.
  apply (rngl_le_0_sub Hop Hor).
  rewrite rngl_add_add_swap.
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  rewrite <- rngl_mul_add_distr_l.
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  now apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  now apply (rngl_le_0_sub Hop Hor).
}
apply (rngl_nle_gt Hor) in Hc23.
rewrite angle_add_comm in Hc12z.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
apply rngl_sin_add_nonneg; try easy.
apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
apply rngl_sin_add_nonneg; try easy.
rewrite angle_sub_sub_distr.
rewrite (angle_add_comm θ1).
rewrite angle_add_sub.
now apply rngl_sin_add_nonneg.
Qed.

Theorem angle_add_le_mono_l_lemma_43 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ1 ≤ 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hc2z Hzs3 Hc1z Hzs2 Hc3z Hzs13.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_goal T.
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc2z.
progress sin_cos_add_sub_right_goal T.
apply (rngl_le_0_sub Hop Hor).
destruct (rngl_le_dec Hor (rngl_cos θ2) (rngl_cos θ3)) as [Hc23| Hc32]. {
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_add_distr Hos).
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_add_nonneg_nonneg Hor). {
    apply (rngl_add_nonneg_nonneg Hor). {
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      now apply (rngl_le_0_sub Hop Hor).
    }
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply (rngl_nle_gt Hor) in Hc32.
apply (rngl_le_0_sub Hop Hor).
apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
apply rngl_sin_add_nonneg; try easy.
rewrite angle_sub_sub_distr.
rewrite (angle_add_comm θ1).
rewrite angle_add_sub.
now apply rngl_sin_add_nonneg.
Qed.

Theorem angle_add_le_mono_l_lemma_44 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (rngl_cos θ3 < 0)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_sin (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos (θ1 + θ3))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs2 Hzs3 Hc3z Hzs12 Hzs13.
change_angle_add_r θ3 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs3.
progress sin_cos_add_sub_straight_hyp T Hc3z.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_goal T.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  apply (rngl_lt_le_incl Hor) in Hc3z.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      exfalso.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      now apply rngl_sin_add_nonneg.
    } {
      apply (rngl_nle_gt Hor) in Hc1z.
      apply (rngl_lt_le_incl Hor) in Hzs3.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hc1z.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_le_opp_l Hop Hor).
      apply (rngl_lt_le_incl Hor) in Hc1z.
      apply (rngl_add_nonneg_nonneg Hor).
      now apply rngl_sin_add_nonneg.
      now apply rngl_sin_add_nonneg.
    }
  } {
    apply (rngl_nle_gt Hor) in Hs1z.
    exfalso.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      change_angle_add_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_hyp T Hs1z.
      apply Bool.not_true_iff_false in Haov13.
      apply Haov13; clear Haov13.
      progress unfold angle_add_overflow.
      progress sin_cos_add_sub_straight_goal T.
      progress sin_cos_add_sub_right_goal T.
      progress unfold angle_ltb.
      rewrite rngl_sin_sub_straight_r.
      rewrite rngl_sin_sub_right_r.
      rewrite (rngl_opp_involutive Hop).
      generalize Hzs13; intros H.
      apply (rngl_nle_gt Hor) in H.
      apply rngl_leb_nle in H.
      rewrite H; clear H.
      rewrite rngl_sin_sub_right_r.
      generalize Hs1z; intros H.
      apply (rngl_opp_lt_compat Hop Hor) in H.
      rewrite (rngl_opp_0 Hop) in H.
      apply (rngl_nle_gt Hor) in H.
      apply rngl_leb_nle in H.
      rewrite H; clear H.
      apply rngl_ltb_lt.
      progress sin_cos_add_sub_straight_goal T.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_add_pos_nonneg Hor); [ | easy ].
      now apply (rngl_sin_add_pos_1).
    } {
      apply (rngl_nle_gt Hor) in Hc1z.
      change_angle_add_r θ1 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hzs13.
      progress sin_cos_add_sub_straight_hyp T Hc1z.
      progress sin_cos_add_sub_straight_hyp T Hs1z.
      apply (rngl_nle_gt Hor) in Hzs13.
      apply Hzs13; clear Hzs13.
      apply (rngl_lt_le_incl Hor) in Hs1z, Hzs3, Hc1z.
      now apply rngl_sin_add_nonneg.
    }
  }
} {
  apply (rngl_nle_gt Hor) in Hc2z.
  apply (rngl_lt_le_incl Hor) in Hc2z, Hzs3, Hc3z.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_goal T.
  rewrite (rngl_add_opp_l Hop).
  apply (rngl_le_sub_0 Hop Hor).
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    apply (rngl_lt_le_incl Hor) in Hzs13, Hzs12.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      now apply angle_add_le_mono_l_lemma_42.
    } {
      apply (rngl_nle_gt Hor) in Hc1z.
      apply (rngl_lt_le_incl Hor) in Hc1z.
      now apply angle_add_le_mono_l_lemma_43.
    }
  } {
    exfalso.
    apply (rngl_nle_gt Hor) in Hs1z.
    apply (rngl_lt_le_incl Hor) in Hs1z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      change_angle_add_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_hyp T Hs1z.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      now apply rngl_sin_add_nonneg.
    } {
      apply (rngl_nle_gt Hor) in Hc1z.
      apply (rngl_lt_le_incl Hor) in Hc1z.
      change_angle_add_r θ1 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hzs13.
      progress sin_cos_add_sub_straight_hyp T Hc1z.
      progress sin_cos_add_sub_straight_hyp T Hs1z.
      apply (rngl_nle_gt Hor) in Hzs13.
      apply Hzs13; clear Hzs13.
      now apply rngl_sin_add_nonneg.
    }
  }
}
Qed.

Theorem angle_add_le_mono_l_lemma_45 :
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → rngl_sin θ1 = rngl_sin (- θ2)
  → angle_add_overflow θ1 θ2 = true.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs2 Hzs12 Hs12.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
generalize Hzs12; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hzs2; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_ltb_lt.
apply rngl_sin_eq in Hs12.
destruct Hs12; subst θ1. {
  rewrite angle_add_opp_l.
  rewrite angle_sub_diag.
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  intros H.
  cbn in H.
  apply (eq_rngl_cos_1) in H.
  subst θ2.
  cbn in Hzs2.
  rewrite (rngl_opp_0 Hop) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
rewrite angle_sub_opp_r in Hzs12, Hzs2 |-*.
rewrite <- angle_add_assoc in Hzs12 |-*.
rewrite rngl_sin_add_straight_l in Hzs12, Hzs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
do 2 rewrite rngl_cos_add_straight_l.
apply -> (rngl_opp_lt_compat Hop Hor).
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  change_angle_add_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_goal T.
  rewrite -> rngl_sin_sub_right_r.
  apply (rngl_lt_opp_l Hop Hor).
  cbn.
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_pos_nonneg Hor). {
    now apply (rngl_mul_pos_pos Hop Hor Hii).
  }
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_sin_bound.
}
apply (rngl_nle_gt Hor) in Hc2z.
exfalso.
change_angle_add_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hc2z.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hzs2.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
apply (rngl_sin_add_pos_1); try easy.
now apply (rngl_lt_le_incl Hor) in Hzs2.
now apply (rngl_lt_le_incl Hor) in Hc2z.
Qed.

Theorem angle_add_le_mono_l_lemma_46 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → rngl_sin θ1 ≠ rngl_sin (- θ2)
  → (rngl_cos θ1 < rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs1 Hzs2 Hzc2 Hzs12 Hs12.
cbn in Hs12.
change_angle_add_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hs12.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hzc2.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_lt_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
  change_angle_sub_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hs12.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hc1z.
  progress sin_cos_add_sub_right_goal T.
  cbn.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_pos_nonneg Hor). {
    apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
    apply (rngl_lt_0_sub Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_sin_bound | ].
    intros H.
    apply (eq_rngl_sin_1) in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply (rngl_nlt_ge Hor) in Hzc1.
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hs12.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hzc2.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_lt_dec Hor (rngl_cos θ1) (rngl_cos θ2))
    as [Hc12| Hc12]. {
  rewrite rngl_cos_sub_comm.
  apply (rngl_lt_le_incl Hor) in Hc12.
  now apply rngl_cos_lt_rngl_cos_sub.
} {
  apply (rngl_nlt_ge Hor) in Hc12.
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  rewrite rngl_sin_sub_anticomm.
  apply (rngl_lt_opp_l Hop Hor).
  rewrite rngl_add_0_r.
  apply (rngl_lt_iff Hor).
  split. {
    apply rngl_sin_sub_nonneg; try easy.
    now apply (rngl_lt_le_incl Hor) in Hzs2.
  }
  intros H; symmetry in H.
  apply (eq_rngl_sin_0) in H.
  destruct H as [H| H]. {
    apply angle_sub_move_r in H.
    rewrite angle_add_0_l in H.
    now subst θ2.
  }
  apply angle_sub_move_r in H.
  subst θ2.
  rewrite rngl_sin_add_straight_l in Hzs2.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
  now apply (rngl_nle_gt Hor) in Hzs2.
}
Qed.

Theorem angle_add_le_mono_l_lemma_47 :
  ∀ θ1 θ2 θ3,
  (rngl_sin θ2 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → angle_add_overflow θ1 θ3 = true.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs2 Hzs3 Hzs12 Hzs13 H23.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Hzs2 Hzs3 Hzs12 Hzs13 H23.
destruct (rngl_eq_dec Heo (rngl_sin θ1) (rngl_sin (- θ3))) as [Hs13| Hs13]. {
  apply (rngl_opp_lt_compat Hop Hor) in Hzs3.
  rewrite (rngl_opp_0 Hop) in Hzs3.
  rewrite rngl_sin_opp in Hs13.
  rewrite <- Hs13 in Hzs3.
  rewrite <- rngl_sin_opp in Hs13.
  now apply angle_add_le_mono_l_lemma_45.
}
progress unfold angle_add_overflow.
progress unfold angle_ltb.
generalize Hzs13; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
destruct (rngl_lt_dec Hor (rngl_sin θ1) 0) as [Hs1z| Hzs1]. {
  apply (rngl_nle_gt Hor) in Hs1z.
  apply rngl_leb_nle in Hs1z.
  now rewrite Hs1z.
} {
  apply (rngl_nlt_ge Hor) in Hzs1.
  generalize Hzs1; intros H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_ltb_lt.
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    assert (Hzc3 : (0 < rngl_cos θ3)%L). {
      now apply (rngl_lt_le_trans Hor _ (rngl_cos θ2)).
    }
    change_angle_add_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T H23.
    progress sin_cos_add_sub_right_hyp T Hzc2.
    cbn in Hs13.
    change_angle_add_r θ3 angle_right.
    progress sin_cos_add_sub_right_hyp T Hs13.
    progress sin_cos_add_sub_right_hyp T Hzs3.
    progress sin_cos_add_sub_right_hyp T H23.
    progress sin_cos_add_sub_right_hyp T Hzs13.
    progress sin_cos_add_sub_right_hyp T Hzc3.
    progress sin_cos_add_sub_right_goal T.
    destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
      exfalso.
      apply (rngl_lt_le_incl Hor) in Hzs2, Hzc2.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hc1z.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      now apply rngl_sin_add_nonneg.
    } {
      apply (rngl_nle_gt Hor) in Hzc1.
      change_angle_sub_l θ3 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs3.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hs13.
      progress sin_cos_add_sub_right_hyp T H23.
      progress sin_cos_add_sub_right_hyp T Hzc3.
      progress sin_cos_add_sub_right_goal T.
      destruct (rngl_eq_dec Heo (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
        apply (eq_rngl_sin_0) in Hs1z.
        destruct Hs1z; subst θ1. {
          rewrite angle_sub_0_l in Hzs13.
          cbn in Hzs13.
          apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs13.
          now apply (rngl_nlt_ge Hor) in Hzs13.
        } {
          exfalso.
          apply (rngl_nle_gt Hor) in Hzc1.
          apply Hzc1; clear Hzc1.
          apply (rngl_opp_1_le_0 Hon Hop Hor).
        }
      }
      rewrite rngl_cos_sub_comm.
      apply rngl_cos_lt_rngl_cos_sub; try easy.
      apply (rngl_lt_le_incl Hor).
      apply quadrant_1_sin_sub_pos_cos_lt; try easy. {
        apply not_eq_sym in Hs1z.
        now apply (rngl_lt_iff Hor).
      } {
        now apply (rngl_lt_le_incl Hor) in Hzc1.
      } {
        now apply (rngl_lt_le_incl Hor) in Hzc3.
      } {
        apply (rngl_lt_iff Hor).
        split; [ easy | ].
        intros H; symmetry in H.
        apply (eq_rngl_sin_0) in H.
        destruct H as [H| H]. {
          apply angle_sub_move_l in H.
          rewrite angle_sub_0_r in H.
          now subst θ3.
        }
        apply angle_sub_move_l in H.
        subst θ3.
        progress sin_cos_add_sub_straight_hyp T Hzs3.
        now apply (rngl_nle_gt Hor) in Hzs3.
      }
    }
  } {
    apply (rngl_nlt_ge Hor) in Hc2z.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T H23.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
      now apply angle_add_le_mono_l_lemma_46.
    } {
      apply (rngl_nle_gt Hor) in Hc3z.
      cbn in Hs13.
      change_angle_add_r θ3 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs3.
      progress sin_cos_add_sub_straight_hyp T Hs13.
      progress sin_cos_add_sub_straight_hyp T H23.
      progress sin_cos_add_sub_straight_hyp T Hzs13.
      progress sin_cos_add_sub_straight_hyp T Hc3z.
      progress sin_cos_add_sub_straight_goal T.
      rewrite (rngl_add_opp_l Hop) in H23.
      apply -> (rngl_le_sub_0 Hop Hor) in H23.
      move Hzs2 after Hzs1; move Hzs3 after Hzs2.
      destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
        exfalso.
        apply (rngl_nlt_ge Hor) in Hzs13.
        apply Hzs13; clear Hzs13.
        apply (rngl_lt_le_incl Hor) in Hc3z.
        now apply (rngl_sin_add_pos_1).
      }
      apply (rngl_nlt_ge Hor) in Hc1z.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hs13.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzs13.
      progress sin_cos_add_sub_right_hyp T Hc1z.
      progress sin_cos_add_sub_right_goal T.
      move Hzs1 before Hc2z.
      rewrite <- (rngl_opp_add_distr Hop).
      apply (rngl_opp_neg_pos Hop Hor).
      destruct (rngl_eq_dec Heo (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
        apply (eq_rngl_sin_0) in Hs1z.
        destruct Hs1z; subst θ1. {
          rewrite angle_add_0_l in Hzs13.
          now apply (rngl_nlt_ge Hor) in Hzs13.
        }
        exfalso.
        apply (rngl_nlt_ge Hor) in Hzs1.
        apply Hzs1; clear Hzs1.
        apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
      }
      apply (rngl_lt_eq_cases Hor) in Hc1z.
      apply not_eq_sym in Hs1z.
      destruct Hc1z as [Hc1z| H]; [ | easy ].
      apply (rngl_add_nonneg_pos Hor); [ | easy ].
      apply (rngl_lt_le_incl Hor) in Hc1z, Hzs3, Hc3z.
      now apply rngl_sin_add_nonneg.
    }
  }
}
Qed.

Theorem angle_add_le_mono_l_lemma_48 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13.
destruct (rngl_lt_dec Hor (rngl_cos θ3) 0)%L as [Hc3z| Hzc3]. {
  exfalso.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13.
  now apply angle_add_le_mono_l_lemma_11.
} {
  apply (rngl_nlt_ge Hor) in Hzc3.
  now apply angle_add_le_mono_l_lemma_7.
}
Qed.

Theorem angle_add_le_mono_l_lemma_49 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ1 θ3 = false
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov12 Haov13 Hzs2 Hzs3 Hzs12 Hzs13 H23.
destruct (rngl_lt_dec Hor (rngl_cos θ3) 0)%L as [Hc3z| Hzc3]. {
  exfalso.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13.
  now apply angle_add_le_mono_l_lemma_11.
} {
  apply (rngl_nlt_ge Hor) in Hzc3.
  now apply angle_add_le_mono_l_lemma_16.
}
Qed.

Theorem angle_add_le_mono_l_lemma_50 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs2 Hzs3 Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      now apply rngl_sin_add_nonneg.
    } {
      apply (rngl_nle_gt Hor) in Hc1z.
      exfalso.
      apply (Bool.not_true_iff_false) in Haov13.
      apply Haov13.
      now apply angle_add_le_mono_l_lemma_30.
    }
  } {
    apply (rngl_nle_gt Hor) in Hs1z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      now apply (angle_add_le_mono_l_lemma_32 _ _ θ3).
    } {
      apply (rngl_nle_gt Hor) in Hc1z.
      apply angle_add_not_overflow_comm in Haov13; try easy.
      exfalso.
      apply Bool.not_true_iff_false in Haov13.
      apply Haov13; clear Haov13.
      apply angle_add_le_mono_l_lemma_11; try easy.
      now rewrite angle_add_comm.
    }
  }
} {
  apply (rngl_nle_gt Hor) in Hc2z.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor (rngl_sin θ1) 0) as [Hs1z| Hzs1]. {
    now apply (angle_add_le_mono_l_lemma_34 _ _ θ3).
  } {
    apply (rngl_nle_gt Hor) in Hzs1.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
      apply (rngl_nlt_ge Hor).
      intros Hc12z.
      apply Bool.not_true_iff_false in Haov13.
      apply Haov13; clear Haov13.
      now apply angle_add_le_mono_l_lemma_37.
    } {
      apply (rngl_nle_gt Hor) in Hc3z.
      now apply (angle_add_le_mono_l_lemma_38 _ _ θ3).
    }
  }
}
Qed.

Theorem angle_add_le_mono_l_lemma_51 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_sin (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos (θ1 + θ3))%L.
Proof.
destruct_ac.
intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
  now apply angle_add_le_mono_l_lemma_41.
} {
  apply (rngl_nle_gt Hor) in Hc3z.
  now apply angle_add_le_mono_l_lemma_44.
}
Qed.

Theorem angle_add_le_mono_l_lemma_52 :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ1 θ3 = false
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_sin (θ1 + θ3) < 0)%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos (θ1 + θ3))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov12 Haov13 Hzs2 Hzs3 Hzs12 Hzs13 H23.
change_angle_add_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_hyp T H23.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_goal T.
change_angle_add_r θ3 angle_straight.
progress sin_cos_add_sub_straight_hyp T H23.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_hyp T Hzs3.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_l Hop) in H23.
apply -> (rngl_le_sub_0 Hop Hor) in H23.
apply angle_add_le_mono_l_lemma_3; try easy; cycle 1.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
progress unfold angle_add_overflow in Haov13.
progress unfold angle_ltb in Haov13.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
progress sin_cos_add_sub_straight_hyp T Haov13.
generalize Hzs13; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hzs13; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H in Haov13; clear H.
destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
  generalize Hzs1; intros H.
  apply rngl_leb_le in H.
  rewrite H in Haov13 |-*; clear H.
  clear Haov13.
  apply (rngl_ltb_ge Hor).
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    apply rngl_cos_add_le_cos; try easy.
    now right; right; left.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  change_angle_sub_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hc1z.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    exfalso.
    change_angle_sub_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T H23.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hc2z.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; clear Hzs12.
    apply rngl_sin_add_nonneg; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hzc2.
  move Hzs2 at bottom; move Hzs3 at bottom; move Hc1z at bottom.
  move Hzs1 at bottom.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply rngl_sin_sub_nonneg_sin_le_sin; try easy. {
      apply rngl_sin_add_nonneg; try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    } {
      now apply (rngl_lt_le_incl Hor).
    } {
      rewrite angle_add_comm.
      rewrite angle_add_sub.
      now apply (rngl_lt_le_incl Hor).
    }
  }
  exfalso.
  apply (rngl_nle_gt Hor) in Hc3z.
  change_angle_sub_r θ3 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hc3z.
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply rngl_sin_add_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hs1z.
exfalso.
generalize Hs1z; intros H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H in Haov13; clear H.
apply (rngl_ltb_ge Hor) in Haov13.
apply (rngl_le_opp_r Hop Hor) in Haov13.
move Hzs2 at bottom; move Hzs3 at bottom.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzs1| Hc1z]. {
  change_angle_add_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Haov13.
  progress sin_cos_add_sub_right_hyp T Hs1z.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  move Hs1z at bottom.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply (rngl_nlt_ge Hor) in Haov13.
    apply Haov13; clear Haov13.
    apply (rngl_add_nonneg_pos Hor); [ easy | ].
    now apply (rngl_sin_add_pos_1).
  }
  apply (rngl_nle_gt Hor) in Hc3z.
  change_angle_sub_r θ3 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_hyp T Haov13.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hc3z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    apply Bool.not_true_iff_false in Haov12.
    apply Haov12; clear Haov12.
    progress unfold angle_add_overflow.
    rewrite angle_add_sub_assoc.
    rewrite <- angle_add_sub_swap.
    progress unfold angle_ltb.
    rewrite rngl_sin_sub_straight_r.
    do 2 rewrite rngl_sin_sub_right_r.
    rewrite (rngl_opp_involutive Hop).
    generalize Hzs12; intros H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    generalize Hs1z; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite rngl_cos_sub_straight_r.
    do 2 rewrite rngl_cos_sub_right_r.
    apply rngl_ltb_lt.
    apply (rngl_lt_opp_l Hop Hor).
    apply (rngl_add_pos_nonneg Hor); [ | easy ].
    now apply (rngl_sin_add_pos_1).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T H23.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  apply Bool.not_true_iff_false in Haov12.
  apply Haov12; clear Haov12.
  progress unfold angle_add_overflow.
  rewrite angle_add_sub_assoc.
  rewrite angle_add_assoc.
  rewrite <- angle_add_sub_swap.
  rewrite angle_sub_add.
  progress unfold angle_ltb.
  rewrite rngl_sin_sub_straight_r.
  rewrite rngl_sin_sub_right_r.
  generalize Hzs12; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  generalize Hs1z; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  rewrite rngl_cos_sub_straight_r.
  rewrite rngl_cos_sub_right_r.
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor).
  cbn.
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_pos_nonneg Hor). {
    now apply (rngl_mul_pos_pos Hop Hor Hii).
  }
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_sin_bound.
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_add_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Haov13.
progress sin_cos_add_sub_straight_hyp T Hs1z.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_hyp T Hc1z.
rewrite (rngl_add_opp_r Hop) in Haov13.
rewrite <- (rngl_opp_add_distr Hop) in Haov13.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Haov13.
move Hs1z at bottom.
destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply rngl_sin_add_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc3z.
change_angle_sub_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T H23.
progress sin_cos_add_sub_right_hyp T Haov13.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hc3z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply rngl_sin_add_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc2z.
change_angle_sub_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T H23.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc2z.
rewrite angle_add_sub_swap in Haov12.
rewrite <- angle_sub_sub_distr in Haov12.
rewrite angle_straight_sub_right in Haov12.
apply Bool.not_true_iff_false in Haov12.
apply Haov12; clear Haov12.
progress unfold angle_add_overflow.
rewrite angle_add_sub_assoc.
rewrite <- angle_add_sub_swap.
rewrite angle_sub_sub_swap.
progress unfold angle_ltb.
do 2 rewrite rngl_sin_sub_straight_r.
rewrite rngl_sin_sub_right_r.
rewrite (rngl_opp_involutive Hop).
generalize Hzs12; intros H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
do 2 rewrite rngl_cos_sub_straight_r.
rewrite rngl_cos_sub_right_r.
apply rngl_ltb_lt.
apply -> (rngl_opp_lt_compat Hop Hor).
change_angle_sub_l θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T H23.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hc2z.
progress sin_cos_add_sub_right_goal T.
rewrite rngl_cos_sub_comm.
apply rngl_cos_lt_rngl_cos_sub; try easy.
now apply (rngl_lt_le_incl Hor).
apply (rngl_lt_le_incl Hor).
apply quadrant_1_sin_sub_pos_cos_lt; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (θ2 ≤ θ3)%A
  → (θ1 + θ2 ≤ θ1 + θ3)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov13 H23.
  progress unfold angle_leb.
  rewrite (H1 (rngl_sin (θ1 + θ2))).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin (θ1 + θ3))).
  rewrite (rngl_leb_refl Hor).
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_leb_refl Hor).
}
intros * Haov13 H23.
progress unfold angle_leb in H23.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
remember (0 ≤? rngl_sin (θ1 + θ3))%L as zs13 eqn:Hzs13.
symmetry in Hzs2, Hzs3, Hzs12, Hzs13.
move H23 at bottom.
destruct zs12. {
  destruct zs13; [ | easy ].
  apply rngl_leb_le in Hzs12, Hzs13.
  apply rngl_leb_le.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    destruct zs3. {
      apply rngl_leb_le in Hzs3, H23.
      now apply angle_add_le_mono_l_lemma_3.
    }
    clear H23.
    apply (rngl_leb_gt Hor) in Hzs3.
    now apply angle_add_le_mono_l_lemma_48.
  }
  destruct zs3; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
  apply rngl_leb_le in H23.
  apply angle_add_le_mono_l_lemma_49; try easy.
  apply (angle_add_overflow_le _ θ3); [ | easy ].
  progress unfold angle_leb.
  apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
  rewrite Hzs2, Hzs3.
  now apply rngl_leb_le.
}
apply (rngl_leb_gt Hor) in Hzs12.
destruct zs2. {
  apply rngl_leb_le in Hzs2.
  destruct zs3. {
    apply rngl_leb_le in Hzs3, H23.
    destruct zs13. {
      exfalso.
      apply rngl_leb_le in Hzs13.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      now apply angle_add_le_mono_l_lemma_19 with (θ3 := θ3).
    }
    apply (rngl_leb_gt Hor) in Hzs13.
    apply rngl_leb_le.
    destruct (rngl_lt_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
      now apply angle_add_le_mono_l_lemma_20.
    } {
      apply (rngl_nlt_ge Hor) in Hc3z.
      now apply angle_add_le_mono_l_lemma_28.
    }
  } {
    clear H23.
    apply (rngl_leb_gt Hor) in Hzs3.
    destruct zs13. {
      exfalso.
      apply rngl_leb_le in Hzs13.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      now apply (angle_add_le_mono_l_lemma_50 _ _  θ3).
    } {
      apply (rngl_leb_gt Hor) in Hzs13.
      apply rngl_leb_le.
      now apply angle_add_le_mono_l_lemma_51.
    }
  }
}
destruct zs3; [ easy | ].
apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
apply rngl_leb_le in H23.
destruct zs13. {
  exfalso.
  apply rngl_leb_le in Hzs13.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13; clear Haov13.
  now apply (angle_add_le_mono_l_lemma_47 _ θ2).
}
apply rngl_leb_le.
apply (rngl_leb_gt Hor) in Hzs13.
apply angle_add_le_mono_l_lemma_52; try easy.
apply (angle_add_overflow_le _ θ3); [ | easy ].
progress unfold angle_leb.
apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
rewrite Hzs2, Hzs3.
now apply rngl_leb_le.
Qed.

Theorem angle_mul_le_mono_l :
  ∀ θ1 θ2,
  (θ1 ≤ θ2)%A
  → ∀ n,
  angle_mul_nat_overflow n θ2 = false
  → (n * θ1 ≤ n * θ2)%A.
Proof.
destruct_ac.
intros * H12 * Hn2.
revert θ1 θ2 H12 Hn2.
induction n; intros; [ apply angle_le_refl | cbn ].
apply angle_mul_nat_overflow_succ_l_false in Hn2.
destruct Hn2 as (Hn2, H2n2).
generalize Hn2; intros Hn12.
apply (IHn θ1) in Hn12; [ | easy ].
apply (angle_le_trans _ (θ1 + n * θ2))%A. {
  apply angle_add_le_mono_l; [ | easy ].
  apply angle_add_not_overflow_comm.
  apply (angle_add_overflow_le _ θ2)%A; [ easy | ].
  now apply angle_add_not_overflow_comm.
} {
  rewrite (angle_add_comm θ1).
  rewrite (angle_add_comm θ2).
  apply angle_add_le_mono_l; [ | easy ].
  now apply angle_add_not_overflow_comm.
}
Qed.

Theorem angle_mul_le_mono_r :
  ∀ a b θ, angle_mul_nat_overflow b θ = false → a ≤ b → (a * θ ≤ b * θ)%A.
Proof.
intros * Hb Hab.
revert a Hab.
induction b; intros. {
  apply Nat.le_0_r in Hab; subst a.
  apply angle_le_refl.
}
destruct a; [ apply angle_nonneg | cbn ].
move a after b.
apply Nat.succ_le_mono in Hab.
apply (angle_mul_nat_overflow_succ_l_false θ b) in Hb.
destruct Hb as (H1, H2).
specialize (IHb H1 _ Hab).
now apply angle_add_le_mono_l.
Qed.

Theorem angle_mul_nat_not_overflow_le_l :
  ∀ m n,
  m ≤ n
  → ∀ θ, angle_mul_nat_overflow n θ = false
  → angle_mul_nat_overflow m θ = false.
Proof.
destruct_ac.
intros * Hmn * Hn.
revert θ m Hmn Hn.
induction n; intros. {
  now apply Nat.le_0_r in Hmn; subst m.
}
apply angle_mul_nat_overflow_succ_l_false in Hn.
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hmn.
apply angle_mul_nat_overflow_succ_l_false.
split; [ now apply IHn | ].
apply (angle_add_overflow_le _ (n * θ)); [ | easy ].
now apply angle_mul_le_mono_r.
Qed.

Theorem angle_mul_nat_overflow_le_l :
  ∀ n θ,
  angle_mul_nat_overflow n θ = true
  → ∀ m, n ≤ m → angle_mul_nat_overflow m θ = true.
Proof.
destruct_ac.
intros * Hn * Hnm.
apply Bool.not_false_iff_true in Hn.
apply Bool.not_false_iff_true.
intros H; apply Hn.
now apply (angle_mul_nat_not_overflow_le_l _ m).
Qed.

Theorem angle_mul_nat_overflow_distr_add_overflow :
  ∀ m n θ,
  angle_mul_nat_overflow (m + n) θ = false
  → angle_add_overflow (m * θ) (n * θ) = false.
Proof.
destruct_ac.
intros * Hmov.
revert n Hmov.
induction m; intros; [ apply angle_add_overflow_0_l | ].
rewrite Nat.add_succ_l in Hmov.
rewrite angle_mul_nat_overflow_succ_l in Hmov.
apply Bool.orb_false_iff in Hmov.
destruct Hmov as (Hmov, Hov).
specialize (IHm _ Hmov) as Hov'.
cbn.
apply angle_add_not_overflow_comm.
apply angle_add_not_overflow_move_add. 2: {
  rewrite <- angle_mul_add_distr_r.
  rewrite Nat.add_comm.
  now apply angle_add_not_overflow_comm.
}
now apply angle_add_not_overflow_comm.
Qed.

Theorem angle_mul_nat_overflow_true_assoc :
  ∀ m n θ,
  angle_mul_nat_overflow m (n * θ) = true
  → angle_mul_nat_overflow (m * n) θ = true.
Proof.
intros * Hmn.
revert n θ Hmn.
induction m; intros; [ easy | ].
rewrite angle_mul_nat_overflow_succ_l in Hmn.
apply Bool.orb_true_iff in Hmn.
destruct Hmn as [Hmn| Hmn]. {
  apply (angle_mul_nat_overflow_le_l (m * n)); [ now apply IHm | ].
  apply Nat.le_add_l.
}
destruct n. {
  cbn in Hmn.
  now rewrite angle_add_overflow_0_l in Hmn.
}
apply Bool.not_false_iff_true in Hmn.
apply Bool.not_false_iff_true.
intros H1; apply Hmn; clear Hmn.
rewrite angle_mul_nat_assoc.
now apply angle_mul_nat_overflow_distr_add_overflow.
Qed.

Theorem angle_mul_nat_overflow_le_r :
  ∀ θ1 θ2,
  (θ1 ≤ θ2)%A
  → ∀ n,
  angle_mul_nat_overflow n θ2 = false
  → angle_mul_nat_overflow n θ1 = false.
Proof.
destruct_ac.
intros * H12 * H2.
revert θ1 θ2 H12 H2.
induction n; intros; [ easy | ].
generalize H2; intros H.
apply angle_mul_nat_overflow_succ_l_false in H.
destruct H as (Hn2, H2n2).
cbn.
destruct n; [ easy | ].
apply Bool.orb_false_iff.
split; [ | now apply (IHn _ θ2) ].
remember (S n) as m eqn:Hm.
clear n Hm; rename m into n.
clear H2 IHn.
apply angle_add_not_overflow_comm.
eapply angle_add_overflow_le; [ apply H12 | ].
apply angle_add_not_overflow_comm.
eapply angle_add_overflow_le; [ | apply H2n2 ].
now apply angle_mul_le_mono_l.
Qed.

End a.
