Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Init.Nat.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike.
Require Import Trigo.TacChangeAngle.
Require Import Trigo.RealLike.
Require Import Trigo.TrigoWithoutPi Trigo.TrigoWithoutPiExt.
Require Import Trigo.AngleDiv2Add.
Require Import Trigo.AngleAddLeMonoL.
Require Import Trigo.AngleAddOverflowLe.
Require Import Complex.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_sqrt_min_distr :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (0 ≤ a)%L → (0 ≤ b)%L → rngl_min √a √b = √(rngl_min a b)%L.
Proof.
intros Hon Hop Hor Hii * Hza Hzb.
progress unfold rngl_min.
remember (√a ≤? √b)%L as sab eqn:Hsab.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hsab, Hab.
destruct sab. {
  destruct ab; [ easy | ].
  apply rngl_leb_le in Hsab.
  apply (rngl_leb_gt Hor) in Hab.
  apply (rngl_le_antisymm Hor); [ easy | ].
  apply (rl_sqrt_le_rl_sqrt Hon Hop Hor Hii); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
destruct ab; [ | easy ].
apply (rngl_leb_gt Hor) in Hsab.
apply rngl_leb_le in Hab.
apply (rngl_le_antisymm Hor); [ now apply (rngl_lt_le_incl Hor) | ].
now apply (rl_sqrt_le_rl_sqrt Hon Hop Hor Hii).
Qed.

Theorem quadrant_1_rngl_cos_sub_lt :
  ∀ θ1 θ2 θ3,
  (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 < rngl_cos θ1)%L
  → (rngl_cos θ1 < rngl_cos θ2)%L
  → (rngl_cos θ1 < rngl_cos θ3)%L
  → (rngl_cos (θ1 - θ3) < rngl_cos (θ1 - θ2))%L
  → (rngl_cos θ2 < rngl_cos θ3)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs1 Hzs2 Hzs3 Hzc1 Hc12 Hc13 Hc1312.
assert (H1 : (rngl_sin (θ1 - θ2) < rngl_sin (θ1 - θ3))%L). {
  apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff.
  apply rngl_sin_sub_nonneg.
  now apply (rngl_lt_le_incl Hor).
  easy.
  now apply (rngl_lt_le_incl Hor).
  apply rngl_sin_sub_nonneg.
  now apply (rngl_lt_le_incl Hor).
  easy.
  now apply (rngl_lt_le_incl Hor).
  apply rngl_cos_sub_nonneg.
  now apply (rngl_lt_le_incl Hor).
  easy.
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_le_trans Hor _ (rngl_cos θ1)).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  apply rngl_cos_sub_nonneg.
  now apply (rngl_lt_le_incl Hor).
  easy.
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_le_trans Hor _ (rngl_cos θ1)).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  easy.
}
do 2 rewrite rngl_cos_sub in Hc1312.
apply (rngl_lt_sub_lt_add_l Hop Hor) in Hc1312.
rewrite (rngl_add_sub_swap Hop) in Hc1312.
rewrite <- (rngl_mul_sub_distr_l Hop) in Hc1312.
apply (rngl_lt_add_lt_sub_r Hop Hor) in Hc1312.
rewrite <- (rngl_mul_sub_distr_l Hop) in Hc1312.
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii (rngl_sin θ1) _ _ Hzs1) in
  Hc1312.
do 2 rewrite rngl_mul_assoc in Hc1312.
rewrite fold_rngl_squ in Hc1312.
specialize (cos2_sin2_1 θ1) as H2.
apply (rngl_add_move_l Hop) in H2.
rewrite H2 in Hc1312; clear H2.
rewrite (rngl_mul_sub_distr_r Hop) in Hc1312.
rewrite (rngl_mul_1_l Hon) in Hc1312.
apply (rngl_lt_add_lt_sub_r Hop Hor) in Hc1312.
progress unfold rngl_squ in Hc1312.
rewrite (rngl_mul_comm Hic (rngl_sin θ1)) in Hc1312.
do 2 rewrite <- rngl_mul_assoc in Hc1312.
rewrite <- rngl_mul_add_distr_l in Hc1312.
do 2 rewrite (rngl_mul_sub_distr_l Hop) in Hc1312.
rewrite <- (rngl_add_sub_swap Hop) in Hc1312.
rewrite (rngl_add_sub_assoc Hop) in Hc1312.
rewrite (rngl_add_sub_swap Hop) in Hc1312.
rewrite <- rngl_sin_sub in Hc1312.
rewrite (rngl_add_sub_swap Hop) in Hc1312.
rewrite <- (rngl_sub_sub_distr Hop) in Hc1312.
rewrite <- rngl_sin_sub in Hc1312.
apply (rngl_lt_add_lt_sub_l Hop Hor) in Hc1312.
assert (H2 : (rngl_sin θ3 < rngl_sin θ2)%L). {
  eapply (rngl_le_lt_trans Hor); [ | apply Hc1312 ].
  apply (rngl_le_add_r Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff.
easy.
easy.
apply (rngl_le_trans Hor _ (rngl_cos θ1)).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply (rngl_le_trans Hor _ (rngl_cos θ1)).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
easy.
Qed.

Theorem quadrant_1_rngl_cos_add_lt :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ2) < rngl_cos (θ1 + θ3))%L
  → (rngl_cos θ2 < rngl_cos θ3)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc1 Hzc2 Hzc3 Hc213.
apply (rngl_nle_gt Hor).
intros H32.
apply (rngl_nle_gt Hor) in Hc213.
apply Hc213; clear Hc213.
do 2 rewrite rngl_cos_add.
apply (rngl_le_sub_le_add_r Hop Hor).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- (rngl_add_sub_assoc Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_le_0_sub Hop Hor).
rewrite (rngl_add_sub_swap Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_add_nonneg_nonneg Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
now apply (rngl_le_0_sub Hop Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
apply (rngl_le_0_sub Hop Hor).
now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
Qed.

Theorem angle_add_le_mono_r :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → (θ1 ≤ θ2)%A
  → (θ1 + θ3 ≤ θ2 + θ3)%A.
Proof.
intros * H23 H12.
do 2 rewrite (angle_add_comm _ θ3).
apply angle_add_not_overflow_comm in H23.
now apply angle_add_le_mono_l.
Qed.

Theorem quadrant_1_rngl_add_cos_add_cos_sub :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos θ3 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos (θ1 + θ2) + rngl_cos (θ3 - θ1))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzs3 Hzc1 Hzc2 Hzc3 H31.
  rewrite (H1 (rngl_add _ _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs1 Hzs2 Hzs3 Hzc1 Hzc2 Hzc3 H31.
assert (Hz2 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hop Hor).
destruct (rngl_le_dec Hor (rngl_sin θ2) (rngl_sin θ3)) as [Hs23| Hs23]. {
  rewrite rngl_cos_add.
  rewrite rngl_cos_sub.
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite rngl_add_assoc.
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_mul_comm Hic (rngl_sin θ3)).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_add_nonneg_nonneg Hor). {
    apply (rngl_add_nonneg_nonneg Hor). {
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
    }
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  now apply (rngl_le_0_sub Hop Hor).
}
apply (rngl_nle_gt Hor) in Hs23.
rewrite rngl_cos_add_rngl_cos.
rewrite <- rngl_mul_assoc.
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
apply (rngl_mul_nonneg_nonneg Hop Hor). {
  rewrite <- angle_div_2_add_not_overflow. 2: {
    progress unfold angle_add_overflow.
    rewrite angle_add_comm.
    rewrite angle_add_assoc.
    rewrite angle_sub_add.
    apply Bool.not_true_iff_false.
    intros H1.
    apply angle_nle_gt in H1.
    apply H1; clear H1.
    apply angle_add_le_mono_r.
    apply angle_add_overflow_lt_straight_le_straight.
    progress unfold angle_ltb.
    apply rngl_leb_le in Hzs3.
    rewrite Hzs3; cbn.
    rewrite (rngl_leb_refl Hor).
    apply rngl_ltb_lt.
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_cos_bound | ].
    intros H1.
    symmetry in H1.
    apply (rngl_nlt_ge Hor) in Hzc3.
    apply Hzc3; rewrite H1.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
    progress unfold angle_leb.
    apply rngl_leb_le in Hzs2.
    rewrite Hzs2; cbn.
    rewrite (rngl_leb_refl Hor).
    apply rngl_leb_le.
    apply rngl_cos_bound.
    progress unfold angle_leb.
    apply rngl_leb_le in Hzs1.
    rewrite Hzs1; cbn.
    apply rngl_leb_le in Hzs3.
    rewrite Hzs3; cbn.
    now apply rngl_leb_le.
  }
  apply rngl_cos_div_2_nonneg.
  rewrite angle_add_comm.
  rewrite angle_add_assoc.
  rewrite angle_sub_add.
  now apply rngl_sin_add_nonneg.
}
rewrite rngl_cos_sub.
apply (rngl_add_nonneg_nonneg Hor). {
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply rngl_cos_div_2_nonneg.
  now apply rngl_sin_add_nonneg.
  apply rngl_cos_div_2_nonneg.
  now apply rngl_sin_sub_nonneg.
}
apply (rngl_mul_nonneg_nonneg Hop Hor).
apply rngl_sin_div_2_nonneg.
apply rngl_sin_div_2_nonneg.
Qed.

Theorem quadrant_1_cos_sub_le_cos_sub :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 < rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_cos θ2 ≤ rngl_cos θ3 ≤ rngl_cos θ1)%L
  → (rngl_cos (θ2 - θ1) ≤ rngl_cos (θ3 - θ1))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzc2 (H23, H31).
apply (rngl_lt_eq_cases Hor) in H23.
destruct H23 as [H23| H23]. 2: {
  apply rngl_cos_eq in H23.
  destruct H23; subst θ2; [ apply (rngl_le_refl Hor) | ].
  cbn in Hzs2.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply (rngl_nlt_ge Hor) in Hzs2.
}
apply (rngl_lt_iff Hor).
apply (rngl_lt_le_incl Hor) in Hzs2, Hzs3.
apply (quadrant_1_rngl_cos_add_lt θ1).
easy.
apply rngl_sin_sub_nonneg; [ easy | easy | ].
apply (rngl_le_trans Hor _ (rngl_cos θ3)); [ | easy ].
now apply (rngl_lt_le_incl Hor).
now apply rngl_sin_sub_nonneg.
apply (rngl_le_trans Hor _ (rngl_cos θ3)); [ | easy ].
apply (rngl_le_trans Hor _ (rngl_cos θ2)); [ easy | ].
now apply (rngl_lt_le_incl Hor).
apply rngl_cos_sub_nonneg; [ easy | easy | easy | ].
apply (rngl_le_trans Hor _ (rngl_cos θ3)); [ | easy ].
apply (rngl_le_trans Hor _ (rngl_cos θ2)); [ easy | ].
now apply (rngl_lt_le_incl Hor).
apply rngl_cos_sub_nonneg; [ easy | easy | | ].
apply (rngl_le_trans Hor _ (rngl_cos θ2)); [ easy | ].
now apply (rngl_lt_le_incl Hor).
apply (rngl_le_trans Hor _ (rngl_cos θ3)); [ | easy ].
apply (rngl_le_trans Hor _ (rngl_cos θ2)); [ easy | ].
now apply (rngl_lt_le_incl Hor).
now do 2 rewrite angle_add_comm, angle_sub_add.
Qed.

Theorem angle_sub_lt_straight_l :
  ∀ θ1 θ2,
  (θ1 ≤ angle_straight)%A
  → (angle_straight - θ2 < angle_straight - θ1)%A
  → (θ1 < θ2)%A.
Proof.
destruct_ac.
intros * H1s H21.
progress unfold angle_ltb in H21.
progress unfold angle_ltb.
do 2 rewrite rngl_sin_sub_straight_l in H21.
do 2 rewrite rngl_cos_sub_straight_l in H21.
apply rngl_sin_nonneg_angle_le_straight in H1s.
apply rngl_leb_le in H1s.
rewrite H1s in H21 |-*.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs2.
destruct zs2; [ | easy ].
apply rngl_ltb_lt in H21.
apply rngl_ltb_lt.
now apply (rngl_opp_lt_compat Hop Hor) in H21.
Qed.

Theorem quadrant_1_sin_sub_nonneg_cos_lt :
  ∀ θ1 θ2,
  θ1 ≠ θ2
  → (0 ≤ rngl_sin (θ2 - θ1))%L
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_cos θ2 < rngl_cos θ1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros * Hz21 Hzs21 Hzs1 Hzs2 Hzc1 Hzc2.
  now rewrite (H1 θ1), (H1 θ2) in Hz21.
}
intros * Hz21 Hzs21 Hzs1 Hzs2 Hzc1 Hzc2.
apply quadrant_1_sin_sub_pos_cos_lt; try easy.
apply (rngl_lt_iff Hor).
split; [ easy | ].
intros H; symmetry in H.
apply eq_rngl_sin_0 in H.
destruct H as [H| H]. {
  apply -> angle_sub_move_0_r in H.
  now symmetry in H.
}
clear Hzs21.
apply angle_sub_move_l in H.
subst θ1.
rewrite rngl_sin_sub_straight_r in Hzs1.
rewrite rngl_cos_sub_straight_r in Hzc1.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1, Hzc1.
apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
apply eq_rngl_sin_0 in Hzs2.
destruct Hzs2; subst θ2. {
  apply (rngl_nlt_ge Hor) in Hzc1.
  apply Hzc1.
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
apply (rngl_nlt_ge Hor) in Hzc2.
apply Hzc2.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

Theorem rngl_sin_sub_nonneg_rngl_cos_lt :
  ∀ θ1 θ2,
  θ1 ≠ θ2
  → θ1 ≠ angle_straight
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ2 - θ1))%L
  → (rngl_cos θ2 < rngl_cos θ1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros * H12 H1s Hzs1 Hzs2 Hzs21.
  now rewrite (H1 θ1), (H1 θ2) in H12.
}
intros * H12 H1s Hzs1 Hzs2 Hzs21.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    now apply quadrant_1_sin_sub_nonneg_cos_lt; try easy.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  now apply (rngl_lt_le_trans Hor _ 0).
}
apply (rngl_nle_gt Hor) in Hc1z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  exfalso.
  rewrite rngl_sin_sub_anticomm in Hzs21.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs21.
  apply (rngl_nlt_ge Hor) in Hzs21.
  apply Hzs21; clear Hzs21.
  apply (rngl_lt_iff Hor).
  split. {
    rewrite rngl_sin_sub.
    apply (rngl_le_0_sub Hop Hor).
    apply (rngl_le_trans Hor _ 0). {
      apply (rngl_lt_le_incl Hor) in Hc1z.
      now apply (rngl_mul_nonpos_nonneg Hop Hor).
    }
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  intros H; symmetry in H.
  apply eq_rngl_sin_0 in H.
  destruct H as [H12z| H12z]. {
    now apply -> angle_sub_move_0_r in H12z.
  }
  apply angle_sub_move_l in H12z.
  subst θ2.
  rewrite rngl_sin_sub_straight_r in Hzs2.
  rewrite rngl_cos_sub_straight_r in Hzc2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2, Hzc2.
  apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
  apply eq_rngl_sin_0 in Hzs1.
  destruct Hzs1; subst θ1; [ | easy ].
  apply (rngl_nlt_ge Hor) in Hzc2.
  apply Hzc2.
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
apply (rngl_nle_gt Hor) in Hc2z.
change_angle_sub_l θ1 angle_straight.
change_angle_sub_l θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs1.
rewrite angle_sub_sub_swap in Hzs21.
rewrite angle_sub_sub_distr in Hzs21.
rewrite angle_sub_diag, angle_add_0_l in Hzs21.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress sin_cos_add_sub_straight_hyp T Hc2z.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_0_sub Hop Hor).
apply (rngl_lt_le_incl Hor) in Hc2z, Hc1z.
apply quadrant_1_sin_sub_nonneg_cos_lt; try easy.
now intros H; subst θ2.
Qed.

End a.
