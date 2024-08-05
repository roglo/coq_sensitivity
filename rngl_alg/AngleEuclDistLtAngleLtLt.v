Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Init.Nat.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike.
Require Import RealLike TrigoWithoutPi TrigoWithoutPiExt.
Require Import AngleAddLeMonoL.
Require Import AngleAddOverflowLe.
Require Import AngleDiv2Add.
Require Import Complex.
Require Import TacChangeAngle.

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

(* to be completed
Theorem angle_eucl_dist_lt_angle_lt_lt :
  ∀ θ1 θ2 θ3,
  (angle_eucl_dist θ1 θ2 <
     rngl_min (angle_eucl_dist θ1 θ3) (angle_eucl_dist θ1 0))%L
  → (θ1 < θ3)%A
  → (θ2 < θ3)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros * Hd12 H13.
  rewrite (H1 θ1), (H1 θ3) in H13.
  now apply angle_lt_irrefl in H13.
}
intros * Hd12 H13.
destruct (angle_le_dec θ2 θ1) as [H21| H12]. {
  now apply (angle_le_lt_trans _ θ1).
}
apply angle_nle_gt in H12.
progress unfold angle_ltb in H13.
progress unfold angle_ltb in H12.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
assert (Hz2 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hop Hor).
do 3 rewrite angle_eucl_dist_is_sqrt in Hd12.
rewrite rl_sqrt_mul in Hd12; [ | easy | ]. 2: {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite rl_sqrt_mul in Hd12; [ | easy | ]. 2: {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite rl_sqrt_mul in Hd12; [ | easy | ]. 2: {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite (rngl_mul_min_distr_l Hop Hor Hed Hii) in Hd12. 2: {
  now apply rl_sqrt_nonneg.
}
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii) in Hd12. 2: {
  apply (rl_sqrt_pos Hon Hos Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite (rngl_sqrt_min_distr Hon Hop Hor Hii) in Hd12; cycle 1. {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor) in Hd12. 2: {
  apply rl_sqrt_nonneg.
  apply rngl_min_glb. {
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  } {
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_) in Hd12. 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid) in Hd12.
rewrite (rngl_squ_sqrt Hon) in Hd12. 2: {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite (rngl_squ_sqrt Hon) in Hd12. 2: {
  apply rngl_min_glb. {
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  } {
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
}
apply (rngl_min_glb_lt_iff Hor) in Hd12.
destruct Hd12 as (Hc213, Hc211).
apply (rngl_sub_lt_mono_l Hop Hor) in Hc213, Hc211.
rewrite angle_sub_0_l in Hc211.
rewrite rngl_cos_opp in Hc211.
destruct zs1. 2: {
  destruct zs3; [ easy | ].
  destruct zs2; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs1, Hzs2, Hzs3.
  apply rngl_ltb_lt in H13, H12.
  apply rngl_ltb_lt.
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
    change_angle_opp θ1.
    change_angle_opp θ2.
    change_angle_opp θ3.
    progress sin_cos_opp_hyp T Hzs1.
    do 2 rewrite angle_sub_opp_r in Hc213.
    do 2 rewrite angle_add_opp_l in Hc213.
    progress sin_cos_opp_hyp T H13.
    progress sin_cos_opp_hyp T Hzs3.
    progress sin_cos_opp_hyp T H12.
    progress sin_cos_opp_hyp T Hzs2.
    do 2 rewrite rngl_cos_opp.
    rewrite rngl_cos_opp in Hzc1.
    apply (rngl_lt_le_incl Hor) in Hzs2, Hzs3.
    now apply (quadrant_1_rngl_cos_sub_lt θ1).
  }
  apply (rngl_nlt_ge Hor) in Hzc1.
  change_angle_add_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  rewrite angle_sub_sub_distr in Hc211.
  do 2 rewrite angle_sub_sub_distr in Hc213.
  progress sin_cos_add_sub_straight_hyp T Hc211.
  progress sin_cos_add_sub_straight_hyp T Hc213.
  progress sin_cos_add_sub_straight_hyp T H13.
  progress sin_cos_add_sub_straight_hyp T H12.
  progress sin_cos_add_sub_straight_hyp T Hzc1.
  apply (rngl_lt_opp_l Hop Hor) in H13, H12.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
    change_angle_opp θ2.
    rewrite <- angle_opp_add_distr in Hc213, Hc211.
    progress sin_cos_opp_hyp T Hc213.
    progress sin_cos_opp_hyp T Hc211.
    progress sin_cos_opp_hyp T H12.
    progress sin_cos_opp_hyp T Hzs2.
    progress sin_cos_opp_hyp T Hzc2.
    cbn.
    destruct (rngl_lt_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hzc3]. {
      change_angle_opp θ3.
      rewrite <- angle_opp_add_distr in Hc213.
      progress sin_cos_opp_hyp T Hc213.
      progress sin_cos_opp_hyp T H13.
      progress sin_cos_opp_hyp T Hzs3.
      progress sin_cos_opp_hyp T Hzc3.
      cbn.
      apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2, Hzs3, Hzc3.
      now apply (quadrant_1_rngl_cos_add_lt θ1).
    }
    apply (rngl_nlt_ge Hor) in Hzc3.
    exfalso.
    change_angle_add_r θ3 angle_straight.
    rewrite angle_sub_sub_swap in Hc213.
    progress sin_cos_add_sub_straight_hyp T Hc213.
    progress sin_cos_add_sub_straight_hyp T H13.
    progress sin_cos_add_sub_straight_hyp T Hzs3.
    progress sin_cos_add_sub_straight_hyp T Hzc3.
    rewrite (rngl_add_opp_r Hop) in H13.
    apply -> (rngl_lt_0_sub Hop Hor) in H13.
    clear H12.
    apply (rngl_lt_opp_r Hop Hor) in Hc213.
    apply (rngl_nle_gt Hor) in Hc213.
    apply Hc213; clear Hc213.
    apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2, Hzs3, H13.
    now apply quadrant_1_rngl_add_cos_add_cos_sub.
  }
  apply (rngl_nle_gt Hor) in Hzc2.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hzc3]. {
    now apply (rngl_lt_le_trans Hor _ 0).
  }
  apply (rngl_nle_gt Hor) in Hzc3.
  change_angle_add_r θ2 angle_straight.
  change_angle_add_r θ3 angle_straight.
  do 2 rewrite (angle_sub_sub_swap _ angle_straight) in Hc213.
  rewrite (angle_sub_sub_swap _ angle_straight) in Hc211.
  progress sin_cos_add_sub_straight_hyp T Hc213.
  progress sin_cos_add_sub_straight_hyp T Hc211.
  progress sin_cos_add_sub_straight_hyp T H13.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T H12.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hzc2.
  progress sin_cos_add_sub_straight_hyp T Hzc3.
  progress sin_cos_add_sub_straight_goal T.
  apply (rngl_lt_opp_l Hop Hor) in Hc211.
  rewrite (rngl_add_opp_r Hop) in H13, H12 |-*.
  apply (rngl_lt_le_incl Hor) in Hzs1, H12, H13, Hzc2, Hzc3.
  apply -> (rngl_le_0_sub Hop Hor) in H13.
  apply -> (rngl_le_0_sub Hop Hor) in H12.
  apply (rngl_lt_0_sub Hop Hor).
  apply (rngl_nle_gt Hor).
  intros H32.
  apply (rngl_nle_gt Hor) in Hc213.
  apply Hc213; clear Hc213.
  now apply quadrant_1_cos_sub_le_cos_sub.
}
apply rngl_leb_le in Hzs1.
destruct zs2. {
  apply rngl_leb_le in Hzs2.
  apply rngl_ltb_lt in H12.
  destruct zs3; [ | easy ].
  apply rngl_leb_le in Hzs3.
  apply rngl_ltb_lt.
  apply rngl_ltb_lt in H13.
  destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
    change_angle_sub_r θ1 angle_right.
    change_angle_sub_r θ2 angle_right.
    change_angle_sub_r θ3 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hc213.
    progress sin_cos_add_sub_right_hyp T Hc211.
    progress sin_cos_add_sub_right_hyp T H13.
    progress sin_cos_add_sub_right_hyp T Hzs3.
    progress sin_cos_add_sub_right_hyp T H12.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T Hc1z.
    progress sin_cos_add_sub_right_goal T.
    rewrite (rngl_add_opp_r Hop) in H13, H12 |-*.
    apply -> (rngl_lt_0_sub Hop Hor) in H13.
    apply -> (rngl_lt_0_sub Hop Hor) in H12.
    apply (rngl_lt_0_sub Hop Hor).
    apply (rngl_nle_gt Hor).
    intros H32.
    apply (rngl_nle_gt Hor) in Hc213.
    apply Hc213; clear Hc213.
    apply quadrant_1_cos_sub_le_cos_sub; try easy.
    now apply (rngl_le_lt_trans Hor _ (rngl_sin θ1)).
    now apply (rngl_le_lt_trans Hor _ (rngl_sin θ1)).
    split. {
      apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff in H32; try easy.
      apply (rngl_lt_le_incl Hor) in H13.
      now apply (rngl_le_trans Hor _ (rngl_sin θ1)).
      apply (rngl_lt_le_incl Hor) in H12.
      now apply (rngl_le_trans Hor _ (rngl_sin θ1)).
    } {
      apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff in H13; try easy.
      now apply (rngl_lt_le_incl Hor) in H13.
      apply (rngl_lt_le_incl Hor) in H13.
      now apply (rngl_le_trans Hor _ (rngl_sin θ1)).
    }
  }
  apply (rngl_nle_gt Hor) in Hzc1.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    destruct (rngl_lt_dec Hor (rngl_cos θ3) 0) as [Hc3z| Hzc3]. {
      now apply (rngl_lt_le_trans Hor _ 0).
    }
    apply (rngl_nlt_ge Hor) in Hzc3.
    apply (rngl_nle_gt Hor).
    intros H32.
    apply (rngl_nle_gt Hor) in Hc213.
    apply Hc213; clear Hc213.
    apply quadrant_1_cos_sub_le_cos_sub; try easy.
    apply (rngl_lt_iff Hor).
    split; [ easy | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H; subst θ2. {
      rewrite angle_sub_0_l in Hc211.
      now apply (rngl_lt_irrefl Hor) in Hc211.
    }
    apply (rngl_nlt_ge Hor) in Hzc2.
    apply Hzc2.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
    apply (rngl_lt_iff Hor).
    split; [ easy | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H; subst θ3. {
      apply (rngl_nle_gt Hor) in H13.
      apply H13.
      apply rngl_cos_bound.
    }
    apply (rngl_nlt_ge Hor) in Hzc3.
    apply Hzc3.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
    apply (rngl_lt_le_incl Hor) in H13.
    easy.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  change_angle_sub_l θ2 angle_straight.
  rewrite <- angle_sub_add_distr in Hc211, Hc213.
  progress sin_cos_add_sub_straight_hyp T Hc211.
  progress sin_cos_add_sub_straight_hyp T Hc213.
  progress sin_cos_add_sub_straight_hyp T H12.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_goal T.
  apply (rngl_lt_opp_r Hop Hor) in Hc211, Hc213.
  apply (rngl_lt_opp_l Hop Hor) in H12.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    exfalso.
    apply (rngl_nle_gt Hor) in Hc213.
    apply Hc213; clear Hc213.
    rewrite rngl_add_comm, angle_add_comm.
    apply (rngl_lt_le_incl Hor) in Hzc1, Hc2z, H13.
    now apply quadrant_1_rngl_add_cos_add_cos_sub.
  }
  apply (rngl_nle_gt Hor) in Hc3z.
  change_angle_sub_l θ3 angle_straight.
  rewrite <- angle_sub_add_distr in Hc213.
  progress sin_cos_add_sub_straight_hyp T Hc213.
  progress sin_cos_add_sub_straight_hyp T H13.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hc3z.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_l Hop) in Hc213 |-*.
  apply -> (rngl_lt_sub_0 Hop Hor) in Hc213.
  apply (rngl_lt_sub_0 Hop Hor).
  apply (rngl_lt_opp_l Hop Hor) in H13.
  clear H12 H13.
  apply (rngl_nle_gt Hor).
  intros H32.
  apply (rngl_nle_gt Hor) in Hc213.
  apply Hc213; clear Hc213.
  do 2 rewrite (angle_add_comm _ θ1).
  apply angle_add_le_mono_l_lemma_3; try easy.
  apply angle_add_overflow_lt_straight_le_straight.
  (* lemma like rngl_sin_nonneg_angle_le_straight used below *)
  progress unfold angle_ltb.
  apply rngl_leb_le in Hzs1.
  rewrite Hzs1; cbn.
  rewrite (rngl_leb_refl Hor).
  apply rngl_ltb_lt.
  apply (rngl_le_lt_trans Hor _ 0); [ | easy ].
  apply (rngl_opp_1_le_0 Hon Hop Hor).
  now apply rngl_sin_nonneg_angle_le_straight.
  apply (rngl_lt_le_incl Hor) in Hzc1, Hc2z.
  now apply rngl_sin_add_nonneg.
  apply (rngl_lt_le_incl Hor) in Hzc1, Hc3z.
  now apply rngl_sin_add_nonneg.
}
clear H12.
apply (rngl_leb_gt Hor) in Hzs2.
destruct zs3. {
  exfalso.
  apply rngl_leb_le in Hzs3.
  apply rngl_ltb_lt in H13.
  destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
    change_angle_sub_l θ1 angle_straight.
    change_angle_sub_l θ3 angle_straight.
    rewrite angle_sub_sub_distr in Hc211.
    rewrite <- angle_add_sub_swap in Hc211.
    do 2 rewrite angle_sub_sub_distr in Hc213.
    do 2 rewrite <- angle_add_sub_swap in Hc213.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_hyp T Hc211.
    progress sin_cos_add_sub_straight_hyp T Hc213.
    rewrite <- angle_add_sub_assoc in Hc213.
    rewrite rngl_cos_add_straight_l in Hc213.
    progress sin_cos_add_sub_straight_hyp T H13.
    progress sin_cos_add_sub_straight_hyp T Hzs3.
    progress sin_cos_add_sub_straight_hyp T Hc1z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      apply (rngl_nle_gt Hor) in Hc213.
      apply Hc213; clear Hc213.
      apply (rngl_le_opp_l Hop Hor).
      apply (rngl_add_nonneg_nonneg Hor).
      apply rngl_cos_sub_nonneg; [ easy | easy | easy | ].
      apply (rngl_lt_le_incl Hor) in H13.
      now apply (rngl_le_trans Hor _ (rngl_cos θ1)).
      now apply rngl_cos_add_nonneg.
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hc211.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    progress sin_cos_add_sub_straight_hyp T Hc213.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    apply (rngl_nle_gt Hor) in Hc213.
    apply Hc213; clear Hc213.
    rewrite angle_add_comm.
    destruct (rngl_le_dec Hor (rngl_cos (θ1 + θ2)) 0) as [Hc12z| Hzc12]. {
      apply (rngl_le_trans Hor _ 0); [ easy | ].
      apply rngl_cos_sub_nonneg; [ easy | easy | easy | ].
      apply (rngl_lt_le_incl Hor) in H13.
      now apply (rngl_le_trans Hor _ (rngl_cos θ1)).
    }
    apply (rngl_nle_gt Hor) in Hzc12.
    destruct (rngl_le_dec Hor (rngl_cos θ2) (rngl_cos θ3)) as [Hc23| Hc32]. {
      rewrite rngl_cos_add.
      apply (rngl_le_sub_le_add_r Hop Hor).
      rewrite rngl_cos_sub.
      eapply (rngl_le_trans Hor). {
        apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ | apply Hc23 ].
        easy.
      }
      rewrite <- rngl_add_assoc.
      apply (rngl_le_add_r Hor).
      apply (rngl_add_nonneg_nonneg Hor).
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
      apply (rngl_lt_le_incl Hor) in Hzs2.
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
    }
    apply (rngl_nle_gt Hor) in Hc32.
    apply (rngl_le_trans Hor _ (rngl_cos θ1)).
    apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z.
    now apply quadrant_1_rngl_cos_add_le_cos_l.
    apply quadrant_1_sin_sub_nonneg_cos_le; [ easy | | easy | | ].
    apply (rngl_lt_le_incl Hor) in H13.
    now apply rngl_sin_sub_nonneg.
    apply rngl_cos_sub_nonneg; [ easy | easy | easy | ].
    apply (rngl_lt_le_incl Hor) in H13.
    now apply (rngl_le_trans Hor _ (rngl_cos θ1)).
    now rewrite angle_sub_sub_distr, angle_sub_diag, angle_add_0_l.
  }
  apply (rngl_nle_gt Hor) in Hzc1.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    change_angle_opp θ2.
    rewrite <- angle_opp_add_distr in Hc211, Hc213.
    progress sin_cos_opp_hyp T Hc211.
    progress sin_cos_opp_hyp T Hc213.
    progress sin_cos_opp_hyp T Hzs2.
    progress sin_cos_opp_hyp T Hzc2.
    apply (rngl_nle_gt Hor) in Hc211.
    apply Hc211; clear Hc211.
    apply (rngl_lt_le_incl Hor) in Hzs2, Hzc1.
    now apply quadrant_1_rngl_cos_add_le_cos_l.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  change_angle_add_r θ2 angle_straight.
  rewrite (angle_sub_sub_swap _ angle_straight) in Hc211, Hc213.
  progress sin_cos_add_sub_straight_hyp T Hc211.
  progress sin_cos_add_sub_straight_hyp T Hc213.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  apply (rngl_lt_opp_r Hop Hor) in Hc211.
  apply (rngl_nle_gt Hor) in Hc211.
  apply Hc211; clear Hc211.
  apply (rngl_lt_le_incl Hor) in Hzc1.
  apply (rngl_add_nonneg_nonneg Hor); [ easy | ].
  apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z.
  now apply rngl_cos_sub_nonneg.
}
clear H13.
apply (rngl_leb_gt Hor) in Hzs3.
apply rngl_ltb_lt.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
  change_angle_sub_l θ1 angle_straight.
  rewrite angle_sub_sub_distr in Hc211.
  rewrite <- angle_add_sub_swap in Hc211.
  do 2 rewrite angle_sub_sub_distr in Hc213.
  do 2 rewrite <- angle_add_sub_swap in Hc213.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hc211.
  progress sin_cos_add_sub_straight_hyp T Hc213.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
      change_angle_opp θ2.
      change_angle_opp θ3.
      do 2 rewrite angle_add_opp_l in Hc213.
      rewrite angle_add_opp_l in Hc211.
      progress sin_cos_opp_hyp T Hzs3.
      progress sin_cos_opp_hyp T Hzs2.
      progress sin_cos_opp_hyp T Hzc2.
      progress sin_cos_opp_hyp T Hzc3.
      cbn.
      apply (rngl_nle_gt Hor).
      intros H32.
      destruct (rngl_le_dec Hor (rngl_cos θ2) (rngl_cos θ1))
        as [Hc21| Hc12]. {
        apply (rngl_nle_gt Hor) in Hc213.
        apply Hc213; clear Hc213.
        do 2 rewrite (rngl_cos_sub_comm θ1).
        now apply quadrant_1_cos_sub_le_cos_sub.
      }
      apply (rngl_nle_gt Hor) in Hc12.
      apply (rngl_nle_gt Hor) in Hc211.
      apply Hc211; clear Hc211.
      apply (rngl_lt_eq_cases Hor).
      left.
      rewrite rngl_cos_sub_comm.
      apply (rngl_lt_le_incl Hor) in Hc12.
      now apply rngl_cos_lt_rngl_cos_sub.
    }
    apply (rngl_nle_gt Hor) in Hc3z.
    exfalso.
    change_angle_opp θ2.
    change_angle_add_r θ3 angle_straight.
    rewrite <- angle_add_sub_swap in Hc213.
    rewrite angle_add_opp_l in Hc213, Hc211.
    progress sin_cos_add_sub_straight_hyp T Hc213.
    progress sin_cos_add_sub_straight_hyp T Hzs3.
    progress sin_cos_opp_hyp T Hzs2.
    progress sin_cos_opp_hyp T Hzc2.
    progress sin_cos_add_sub_straight_hyp T Hc3z.
    destruct (rngl_le_dec Hor (rngl_cos θ2) (rngl_cos θ1)) as [Hc21| Hc12]. {
      apply (rngl_nle_gt Hor) in Hc213.
      apply Hc213; clear Hc213.
      apply (rngl_le_opp_l Hop Hor).
      rewrite angle_add_comm.
      rewrite rngl_cos_sub_comm.
      apply (rngl_lt_le_incl Hor) in Hzs3, Hzs2, Hc3z.
      now apply quadrant_1_rngl_add_cos_add_cos_sub.
    }
    apply (rngl_nle_gt Hor) in Hc12.
    apply (rngl_nle_gt Hor) in Hc211.
    apply Hc211; clear Hc211.
    apply (rngl_lt_eq_cases Hor).
    left.
    rewrite rngl_cos_sub_comm.
    apply (rngl_lt_le_incl Hor) in Hc12.
    now apply rngl_cos_lt_rngl_cos_sub.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  change_angle_add_r θ2 angle_straight.
  rewrite <- angle_add_sub_swap in Hc213.
  rewrite <- angle_add_sub_swap in Hc211.
  progress sin_cos_add_sub_straight_hyp T Hc213.
  progress sin_cos_add_sub_straight_hyp T Hc211.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    now apply (rngl_add_pos_nonneg Hor).
  }
  apply (rngl_nle_gt Hor) in Hc3z.
  change_angle_add_r θ3 angle_straight.
  rewrite <- angle_add_sub_swap in Hc213.
  progress sin_cos_add_sub_straight_hyp T Hc213.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hc3z.
  progress sin_cos_add_sub_straight_goal T.
  apply (rngl_lt_0_sub Hop Hor).
  apply (rngl_lt_le_incl Hor) in Hzs3, Hzs2, Hc2z, Hc3z.
  do 2 rewrite (angle_add_comm _ θ1) in Hc213.
  now apply (quadrant_1_rngl_cos_add_lt θ1).
}
apply (rngl_nle_gt Hor) in Hzc1.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
  apply (rngl_nle_gt Hor).
  intros Hc32.
  change_angle_add_r θ2 angle_straight.
  change_angle_add_r θ3 angle_straight.
  move θ3 before θ2.
  rewrite angle_sub_sub_swap in Hc211.
  do 2 rewrite (angle_sub_sub_swap _ angle_straight) in Hc213.
  progress sin_cos_add_sub_straight_hyp T Hc211.
  progress sin_cos_add_sub_straight_hyp T Hc213.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hc32.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  rewrite (rngl_add_opp_l Hop) in Hc32.
  apply -> (rngl_le_sub_0 Hop Hor) in Hc32.
  apply (rngl_nle_gt Hor) in Hc211.
  apply Hc211; clear Hc211.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_lt_le_incl Hor) in Hzc1.
  apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply rngl_cos_sub_nonneg.
}
apply (rngl_nle_gt Hor) in Hzc2.
...
*)

End a.
