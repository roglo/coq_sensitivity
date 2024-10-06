(* equivalent definition of angle_add_overflow *)
Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Main.RingLike.
Require Import RealLike TrigoWithoutPi TrigoWithoutPiExt.
Require Import AngleAddOverflowLe AngleAddLeMonoL.
Require Import AngleLeSubAdd AngleDiv2Add.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_sin_sub_div_2_div_2_pos :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 < rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 /₂ - θ2 /₂))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hcc.
  do 2 rewrite (H1 (rngl_cos _)) in Hcc.
  now apply (rngl_lt_irrefl Hor) in Hcc.
}
intros * Hzs1 Hzs2 Hcc.
cbn.
generalize Hzs2; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_mul_1_l Hon).
generalize Hzs1; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_0_sub Hop Hor).
rewrite <- rl_sqrt_mul; cycle 1.
apply rngl_1_add_cos_div_2_nonneg.
apply rngl_1_sub_cos_div_2_nonneg.
rewrite <- rl_sqrt_mul; cycle 1.
apply rngl_1_sub_cos_div_2_nonneg.
apply rngl_1_add_cos_div_2_nonneg.
apply (rl_sqrt_lt_rl_sqrt Hon Hop Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor).
apply rngl_1_add_cos_div_2_nonneg.
apply rngl_1_sub_cos_div_2_nonneg.
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
apply (rngl_div_lt_mono_pos_r Hon Hop Hiv Hor Hii). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
do 2 rewrite (rngl_mul_div_assoc Hiv).
apply (rngl_div_lt_mono_pos_r Hon Hop Hiv Hor Hii). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_1_r Hon).
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_add_sub_assoc Hop).
apply (rngl_sub_lt_mono_r Hop Hor).
rewrite <- (rngl_add_sub_assoc Hop).
rewrite <- (rngl_sub_sub_distr Hop).
progress unfold rngl_sub at 2.
rewrite Hop.
apply (rngl_add_lt_mono_l Hop Hor).
rewrite (rngl_opp_sub_distr Hop).
apply (rngl_lt_add_lt_sub_r Hop Hor).
rewrite <- (rngl_add_sub_swap Hop).
apply (rngl_lt_sub_lt_add_l Hop Hor).
do 2 rewrite <- (rngl_mul_2_l Hon (rngl_cos _)).
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
easy.
Qed.

Theorem angle_sub_straight_eq_add_straight :
  ∀ θ, (θ - angle_straight = θ + angle_straight)%A.
Proof.
destruct_ac.
intros.
apply angle_sub_move_r.
rewrite <- angle_add_assoc.
rewrite angle_straight_add_straight.
symmetry.
apply angle_add_0_r.
Qed.

Theorem rngl_cos_add_right_div_2_r :
  ∀ θ,
  rngl_cos (θ + angle_right /₂) = ((rngl_cos θ - rngl_sin θ) / √2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (rngl_cos _)).
  symmetry.
  apply H1.
}
intros.
cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_0_r.
rewrite (rngl_sub_0_r Hos).
rewrite <- (rngl_mul_sub_distr_r Hop).
progress unfold rngl_div.
rewrite Hiv.
rewrite (rngl_mul_1_l Hon).
f_equal.
apply rl_nth_root_inv.
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_sin_right_div_2 : rngl_sin (angle_right /₂) = √(1 / 2)%L.
Proof.
destruct_ac.
cbn.
now rewrite (rngl_sub_0_r Hos).
Qed.

Theorem rngl_cos_right_div_2 : rngl_cos (angle_right /₂) = √(1 / 2)%L.
Proof.
destruct_ac.
cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
rewrite (rngl_mul_1_l Hon).
now rewrite rngl_add_0_r.
Qed.

Theorem rngl_cos_3_right_div_2 :
  rngl_cos (3 * (angle_right /₂)) = (- √(1 / 2))%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 (rngl_cos _)); symmetry.
  apply H1.
}
cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
do 2 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_l Hop).
f_equal.
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor). {
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_sin_3_right_div_2 :
  rngl_sin (3 * (angle_right /₂)) = √(1 / 2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 (rngl_sin _)); symmetry.
  apply H1.
}
cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
do 2 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_l.
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor). {
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_sin_5_right_div_2 :
  rngl_sin (5 * (angle_right /₂)) = (- √(1 / 2))%L.
Proof.
replace 5 with (2 + 3) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite rngl_sin_add_right_l.
apply rngl_cos_3_right_div_2.
Qed.

Theorem rngl_cos_5_right_div_2 :
  rngl_cos (5 * (angle_right /₂)) = (- √(1 / 2))%L.
Proof.
replace 5 with (2 + 3) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite rngl_cos_add_right_l.
f_equal.
apply rngl_sin_3_right_div_2.
Qed.

Theorem rl_sqrt_half_nonneg : (0 ≤ √(1 / 2))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 √_%L).
  apply (rngl_le_refl Hor).
}
apply rl_sqrt_nonneg.
apply (rngl_div_nonneg Hon Hop Hiv Hor).
apply (rngl_0_le_1 Hon Hop Hor).
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
Qed.

Theorem rl_sqrt_half_pos :
  rngl_characteristic T ≠ 1 →
  (0 < √(1 / 2))%L.
Proof.
destruct_ac.
intros Hc1.
apply (rl_sqrt_pos Hon Hos Hor).
apply (rngl_div_lt_pos Hon Hop Hiv Hor). {
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_cos_lt_sin_diag :
  ∀ θ,
  (angle_right /₂ < θ < 5 * (angle_right /₂))%A
  ↔ (rngl_cos θ < rngl_sin θ)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H2.
  intros.
  rewrite (H2 (angle_right /₂))%A.
  rewrite (H2 θ), (H2 (_ * _))%A.
  rewrite (H1 (rngl_cos _)), (H1 (rngl_sin _)).
  split. {
    intros (H, _).
    now apply angle_lt_irrefl in H.
  } {
    intros H.
    now apply (rngl_lt_irrefl Hor) in H.
  }
}
intros.
progress unfold angle_ltb.
rewrite rngl_sin_right_div_2.
rewrite rngl_cos_right_div_2.
rewrite rngl_sin_5_right_div_2.
rewrite rngl_cos_5_right_div_2.
rewrite (rngl_leb_0_opp Hop Hor).
specialize rl_sqrt_half_nonneg as H.
apply rngl_leb_le in H.
rewrite H; clear H.
specialize (rl_sqrt_half_pos Hc1) as H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  split. {
    intros (H1, _).
    apply rngl_leb_le in Hzs.
    apply rngl_ltb_lt in H1.
    destruct (rngl_lt_dec Hor (rngl_cos θ) 0) as [Hzc| Hcz]. {
      now apply (rngl_lt_le_trans Hor _ 0).
    }
    apply (rngl_nlt_ge Hor) in Hcz.
    apply (rngl_lt_le_trans Hor _ √(1/2))%L; [ easy | ].
    specialize rngl_sin_nonneg_cos_le_sin_le as H2.
    specialize (H2 θ (angle_right /₂) Hzs)%A.
    rewrite rngl_sin_right_div_2 in H2.
    rewrite rngl_cos_right_div_2 in H2.
    specialize (H2 rl_sqrt_half_nonneg).
    generalize H1; intros H.
    apply (rngl_lt_le_incl Hor) in H.
    specialize (H2 H); clear H.
    generalize Hcz; intros H.
    apply rngl_leb_le in H.
    now rewrite H in H2; clear H.
  } {
    intros Hcs.
    split; [ | easy ].
    apply rngl_leb_le in Hzs.
    apply rngl_ltb_lt.
    specialize rl_sqrt_half_nonneg as Hs2.
    destruct (rngl_lt_dec Hor (rngl_cos θ) 0) as [Hzc| Hcz]. {
      now apply (rngl_lt_le_trans Hor _ 0).
    }
    apply (rngl_nlt_ge Hor) in Hcz.
    apply (rngl_nle_gt Hor).
    intros Hcc.
    generalize Hcc; intros H.
    apply (rngl_nlt_ge Hor) in H.
    apply H; clear H.
    rewrite <- rngl_cos_right_div_2.
    apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy. {
      now rewrite rngl_sin_right_div_2.
    } {
      now rewrite rngl_cos_right_div_2.
    }
    rewrite rngl_sin_right_div_2.
    eapply (rngl_le_lt_trans Hor); [ | apply Hcs ].
    easy.
    (* bizarre, comme démonstration *)
  }
} {
  apply (rngl_leb_gt Hor) in Hzs.
  split. {
    intros (_, H1).
    apply rngl_ltb_lt in H1.
    change_angle_add_r θ angle_straight.
    progress sin_cos_add_sub_straight_hyp T H1.
    progress sin_cos_add_sub_straight_hyp T Hzs.
    progress sin_cos_add_sub_straight_goal T.
    rewrite (rngl_add_opp_r Hop).
    apply (rngl_lt_0_sub Hop Hor).
    apply (rngl_le_lt_trans Hor _ √(1/2))%L; [ | easy ].
    specialize rngl_sin_nonneg_cos_lt_sin_lt as H2.
    specialize (H2 (angle_right /₂) θ)%A.
    rewrite rngl_sin_right_div_2 in H2.
    rewrite rngl_cos_right_div_2 in H2.
    specialize (H2 (rl_sqrt_half_pos Hc1) Hzs H1).
    specialize (rl_sqrt_half_pos Hc1) as H.
    apply rngl_ltb_lt in H.
    rewrite H in H2; clear H.
    now apply (rngl_lt_le_incl Hor) in H2.
  } {
    intros Hcs.
    split; [ easy | ].
    apply rngl_ltb_lt.
    change_angle_add_r θ angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hcs.
    progress sin_cos_add_sub_straight_hyp T Hzs.
    progress sin_cos_add_sub_straight_goal T.
    rewrite (rngl_add_opp_r Hop).
    apply (rngl_lt_0_sub Hop Hor).
    rewrite <- rngl_cos_right_div_2.
    apply quadrant_1_sin_sub_pos_cos_lt. {
      rewrite rngl_sin_right_div_2.
      apply rl_sqrt_half_nonneg.
    } {
      now apply (rngl_lt_le_incl Hor) in Hzs.
    } {
      rewrite rngl_cos_right_div_2.
      apply rl_sqrt_half_nonneg.
    } {
      apply (rngl_lt_le_incl Hor) in Hcs, Hzs.
      now apply (rngl_le_trans Hor _ (rngl_sin θ)).
    }
    cbn.
    specialize (rngl_0_le_1 Hon Hop Hor) as H2.
    apply rngl_leb_le in H2.
    rewrite H2; clear H2.
    rewrite (rngl_mul_1_l Hon).
    rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_add_opp_r Hop).
    rewrite <- (rngl_mul_sub_distr_l Hop).
    apply (rngl_mul_pos_pos Hop Hor Hii). {
      apply (rl_sqrt_half_pos Hc1).
    }
    now apply (rngl_lt_0_sub Hop Hor).
  }
}
Qed.

End a.
