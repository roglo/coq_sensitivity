(* equivalent definition of angle_add_overflow *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Main.RingLike.
Require Import RealLike TrigoWithoutPi.
Require Import AngleAddOverflowLe AngleAddLeMonoL.
Require Import AngleLeSubAdd AngleDiv2Add.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition angle_add_not_overflow2 (θ1 θ2 : angle T) :=
  (θ1 / ₂ + θ2 / ₂ ≤ angle_straight)%A ∧ (θ1 = 0 ∨ θ1 + θ2 ≠ 0)%A.

Theorem angle_add_overflow_opp :
  ∀ θ, θ ≠ 0%A → angle_add_overflow θ (- θ) = true.
Proof.
intros * Hz.
progress unfold angle_add_overflow.
rewrite angle_add_opp_r.
rewrite angle_sub_diag.
apply angle_lt_iff.
split; [ apply angle_nonneg | ].
now intros H; symmetry in H.
Qed.

Theorem rngl_sin_sub_div_2_div_2_pos :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 < rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 / ₂ - θ2 / ₂))%L.
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
do 2 rewrite (rngl_add_diag Hon (rngl_cos _)).
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
  rngl_cos (θ + angle_right / ₂) = ((rngl_cos θ - rngl_sin θ) / √2)%L.
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

Theorem rngl_sin_right_div_2 : rngl_sin (angle_right / ₂) = √(1 / 2)%L.
Proof.
destruct_ac.
cbn.
now rewrite (rngl_sub_0_r Hos).
Qed.

Theorem rngl_cos_right_div_2 : rngl_cos (angle_right / ₂) = √(1 / 2)%L.
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
  rngl_cos (3 * (angle_right / ₂)) = (- √(1 / 2))%L.
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
  rngl_sin (3 * (angle_right / ₂)) = √(1 / 2)%L.
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
  rngl_sin (5 * (angle_right / ₂)) = (- √(1 / 2))%L.
Proof.
destruct_ac.
replace 5 with (2 + 3) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite (rngl_sin_add_right_l Hon Hos).
apply rngl_cos_3_right_div_2.
Qed.

Theorem rngl_cos_5_right_div_2 :
  rngl_cos (5 * (angle_right / ₂)) = (- √(1 / 2))%L.
Proof.
destruct_ac.
replace 5 with (2 + 3) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite (rngl_cos_add_right_l Hon Hop).
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
  (angle_right / ₂ < θ < 5 * (angle_right / ₂))%A
  ↔ (rngl_cos θ < rngl_sin θ)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H2.
  intros.
  rewrite (H2 (angle_right / ₂))%A.
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
rewrite (rngl_leb_opp_r Hop Hor), (rngl_opp_0 Hop).
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
    specialize (H2 θ (angle_right / ₂) Hzs)%A.
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
    specialize (H2 (angle_right / ₂) θ)%A.
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
    apply angle_add_le_mono_l_lemma_39. {
      rewrite rngl_sin_right_div_2.
      apply (rl_sqrt_half_pos Hc1).
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

Theorem rngl_sin_pos_lt_straight :
  ∀ θ,
  (0 < rngl_sin θ)%L
  → (θ < angle_straight)%A.
Proof.
destruct_ac.
intros * Hzs.
progress unfold angle_ltb.
rewrite (rngl_leb_refl Hor).
generalize Hzs; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_ltb_lt; cbn.
apply (rngl_lt_iff Hor).
split; [ apply rngl_cos_bound | ].
intros H; symmetry in H.
apply eq_rngl_cos_opp_1 in H.
subst θ.
now apply (rngl_lt_irrefl Hor) in Hzs.
Qed.

Theorem rngl_sin_nonneg_le_straight :
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → (θ ≤ angle_straight)%A.
Proof.
destruct_ac.
intros * Hzs.
progress unfold angle_leb.
rewrite (rngl_leb_refl Hor).
apply rngl_leb_le in Hzs.
rewrite Hzs.
apply rngl_leb_le; cbn.
apply rngl_cos_bound.
Qed.

Theorem angle_add_straight_r_not_overflow :
  ∀ θ, (θ < angle_straight)%A → angle_add_overflow θ angle_straight = false.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros * Hts.
  rewrite (H1 θ), (H1 angle_straight) in Hts.
  now apply angle_lt_irrefl in Hts.
}
intros * Hts.
progress unfold angle_ltb in Hts.
cbn in Hts.
rewrite (rngl_leb_refl Hor) in Hts.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
rewrite rngl_sin_add_straight_r.
rewrite rngl_cos_add_straight_r.
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
destruct (rngl_le_dec Hor 0 (rngl_sin θ)) as [Hzs| Hsz]. {
  generalize Hzs; intros H.
  apply rngl_leb_le in H.
  rewrite H in Hts |-*; clear H.
  apply rngl_ltb_lt in Hts.
  destruct (rngl_le_dec Hor (rngl_sin θ) 0) as [Hsz| Hsz]. {
    apply (rngl_le_antisymm Hor) in Hzs; [ | easy ].
    apply eq_rngl_sin_0 in Hzs.
    destruct Hzs; subst θ; cbn; rewrite (rngl_leb_refl Hor). {
      apply (rngl_ltb_ge Hor).
      apply (rngl_opp_1_le_1 Hon Hop Hor Hc1).
    }
    exfalso.
    now apply (rngl_lt_irrefl Hor) in Hts.
  }
  apply (rngl_nle_gt Hor) in Hsz.
  generalize Hsz; intros H.
  apply (rngl_leb_gt Hor) in H.
  now rewrite H; clear H.
}
apply (rngl_nle_gt Hor) in Hsz.
generalize Hsz; intros H.
apply (rngl_leb_gt Hor) in H.
now rewrite H in Hts.
Qed.

Theorem angle_add_not_overflow_equiv :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  ↔ angle_add_not_overflow2 θ1 θ2.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 θ1).
  rewrite angle_add_overflow_0_l.
  split; [ intros _ | easy ].
  split; [ | now left ].
  do 2 rewrite (H1 (_ / ₂))%A.
  rewrite angle_add_0_l.
  apply angle_nonneg.
}
intros.
split; intros H12. {
  split. {
    rewrite <- angle_div_2_add_not_overflow; [ | easy ].
    apply angle_div_2_le_straight.
  } {
    remember (θ1 =? 0)%A as t1z eqn:Ht1z.
    symmetry in Ht1z.
    destruct t1z. {
      now apply (angle_eqb_eq Hed) in Ht1z; left.
    }
    apply (angle_eqb_neq Hed) in Ht1z; right.
    intros H12z.
    rewrite angle_add_comm in H12z.
    apply angle_add_move_0_r in H12z.
    subst θ2.
    apply Bool.not_true_iff_false in H12.
    apply H12.
    now apply angle_add_overflow_opp.
  }
} {
  destruct H12 as (H12, H112).
  destruct H112 as [H1| H12z]. {
    subst θ1.
    apply angle_add_overflow_0_l.
  }
  progress unfold angle_leb in H12.
  rewrite (rngl_leb_refl Hor) in H12.
  remember (0 ≤? rngl_sin (_ / ₂ + _))%L as zs12d eqn:Hzs12d.
  symmetry in Hzs12d.
  destruct zs12d; [ | easy ].
  apply rngl_leb_le in Hzs12d.
  progress unfold angle_add_overflow.
  progress unfold angle_ltb.
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
  symmetry in Hzs12, Hzs1.
  destruct zs12. {
    destruct zs1. {
      apply rngl_leb_le in Hzs12, Hzs1.
      apply (rngl_ltb_ge Hor).
      destruct (rngl_le_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hzs2]. {
        destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
          cbn.
          progress unfold rngl_sub.
          rewrite Hop.
          apply (rngl_le_add_le_sub_l Hop Hor).
          rewrite (rngl_sub_mul_r_diag_l Hon Hop).
          apply (rngl_le_trans Hor _ 0). {
            apply (rngl_opp_nonpos_nonneg Hop Hor).
            now apply (rngl_mul_nonneg_nonneg Hop Hor).
          }
          apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
          apply (rngl_le_0_sub Hop Hor).
          apply rngl_cos_bound.
        }
        apply (rngl_nle_gt Hor) in Hzc1.
        change_angle_sub_r θ1 angle_right.
        progress sin_cos_add_sub_right_hyp T Hzs1.
        progress sin_cos_add_sub_right_hyp T Hzs12.
        progress sin_cos_add_sub_right_hyp T Hzc1.
        progress sin_cos_add_sub_right_goal T.
        destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
          apply rngl_sin_sub_nonneg_sin_le_sin; [ | easy | ]. {
            apply (rngl_lt_le_incl Hor) in Hzc1.
            now apply rngl_sin_add_nonneg.
          }
          rewrite angle_add_comm.
          now rewrite angle_add_sub.
        }
        apply (rngl_nle_gt Hor) in Hzc2.
        change_angle_sub_r θ2 angle_right.
        progress sin_cos_add_sub_right_hyp T Hzs2.
        progress sin_cos_add_sub_right_hyp T Hzs12.
        progress sin_cos_add_sub_right_hyp T Hzc2.
        progress sin_cos_add_sub_right_goal T.
        move θ2 before θ1.
        apply (rngl_nlt_ge Hor).
        intros Hcs.
        apply (rngl_nlt_ge Hor) in Hzs12.
        apply Hzs12; clear Hzs12.
        apply (rngl_lt_iff Hor).
        split. {
          apply (rngl_lt_le_incl Hor) in Hzc1, Hzc2.
          now apply rngl_sin_add_nonneg.
        }
        intros H; symmetry in H.
        apply eq_rngl_sin_0 in H.
        destruct H as [Ha12| Ha12]. {
          rewrite Ha12 in Hcs; cbn in Hcs.
          apply (rngl_nle_gt Hor) in Hcs.
          apply Hcs; clear Hcs.
          apply rngl_sin_bound.
        }
        rewrite Ha12 in Hcs.
        apply angle_add_move_l in Ha12.
        subst θ2.
        rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzs2.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
        apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
        apply eq_rngl_cos_0 in Hzs1.
        destruct Hzs1; subst θ1. {
          rewrite (angle_right_add_right Hon Hop) in H12z.
          rewrite angle_sub_add in H12z.
          now rewrite angle_straight_add_straight in H12z.
        }
        apply (rngl_nle_gt Hor) in Hzc1.
        apply Hzc1; clear Hzc1; cbn.
        apply (rngl_opp_1_le_0 Hon Hop Hor).
      }
      apply (rngl_nle_gt Hor) in Hzs2.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
        change_angle_opp θ2.
        progress sin_cos_opp_hyp T Hzs2.
        progress sin_cos_opp_hyp T Hzs12.
        progress sin_cos_opp_hyp T Hzc2.
        progress sin_cos_opp_goal T.
        rewrite angle_add_opp_r in H12z.
        rewrite angle_opp_div_2 in Hzs12d.
        remember (θ2 =? 0)%A as t2z eqn:Ht2z.
        symmetry in Ht2z.
        destruct t2z. {
          apply (angle_eqb_eq Hed) in Ht2z.
          subst θ2.
          now apply (rngl_lt_irrefl Hor) in Hzs2.
        }
        rewrite angle_add_assoc in Hzs12d.
        rewrite angle_add_opp_r in Hzs12d.
        rewrite rngl_sin_add_straight_r in Hzs12d.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12d.
        apply (rngl_nlt_ge Hor).
        intros Hcc.
        apply (rngl_nlt_ge Hor) in Hzs12d.
        apply Hzs12d; clear Hzs12d.
        apply rngl_sin_sub_div_2_div_2_pos; [ easy | | ]. {
          now apply (rngl_lt_le_incl Hor) in Hzs2.
        }
        destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
          apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy. {
            now apply (rngl_lt_le_incl Hor) in Hzs2.
          } {
            apply (rngl_lt_iff Hor).
            split; [ now apply rngl_sin_sub_nonneg_sin_le_sin | ].
            intros H.
            apply rngl_sin_eq in H.
            destruct H; subst θ2. {
              now rewrite angle_sub_diag in H12z.
            }
            apply H12z; clear H12z.
            rewrite angle_sub_sub_distr.
            rewrite <- angle_add_sub_swap.
            rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzc2.
            apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzc2.
            apply (rngl_le_antisymm Hor) in Hzc1; [ | easy ].
            apply eq_rngl_cos_0 in Hzc1.
            destruct Hzc1; subst θ1. {
              rewrite (angle_right_add_right Hon Hop).
              apply angle_sub_diag.
            }
            rewrite angle_add_opp_r.
            rewrite <- angle_opp_add_distr.
            rewrite (angle_right_add_right Hon Hop).
            rewrite <- angle_opp_add_distr.
            rewrite angle_straight_add_straight.
            apply angle_opp_0.
          }
        }
        apply (rngl_nle_gt Hor) in Hzc1.
        now apply (rngl_lt_le_trans Hor _ 0).
      }
      apply (rngl_nle_gt Hor) in Hzc2.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
        change_angle_add_r θ2 angle_straight.
        progress sin_cos_add_sub_straight_hyp T Hzs12.
        progress sin_cos_add_sub_straight_hyp T Hzc2.
        progress sin_cos_add_sub_straight_hyp T Hzs2.
        progress sin_cos_add_sub_straight_goal T.
        rewrite angle_add_sub_assoc in H12z.
        clear - ac Hzs12 Hzc2 Hzs2 Hzs1 Hzc1 H12z.
        destruct_ac.
        apply (rngl_nlt_ge Hor) in Hzs12.
        apply (rngl_nlt_ge Hor).
        intros Hcc.
        apply Hzs12; clear Hzs12.
        apply (rngl_lt_iff Hor).
        split. {
          apply (rngl_lt_le_incl Hor) in Hzc2, Hzs2.
          now apply rngl_sin_add_nonneg.
        }
        intros Hs; symmetry in Hs.
        apply eq_rngl_sin_0 in Hs.
        destruct Hs as [Hs| Hs]. {
          apply (rngl_nle_gt Hor) in Hcc.
          apply Hcc; clear Hcc.
          rewrite Hs; cbn.
          apply (rngl_le_opp_l Hop Hor).
          apply rngl_cos_bound.
        }
        rewrite Hs in H12z.
        now rewrite angle_sub_diag in H12z.
      }
      apply (rngl_nle_gt Hor) in Hzc1.
      change_angle_add_r θ2 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hzc2.
      progress sin_cos_add_sub_straight_hyp T Hzs2.
      progress sin_cos_add_sub_straight_goal T.
      rewrite angle_add_sub_assoc in H12z.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_nlt_ge Hor).
      intros Hss.
      apply (rngl_nlt_ge Hor) in Hzs12d.
      apply Hzs12d; clear Hzs12d.
      rewrite angle_div_2_add_not_overflow. 2: {
        progress unfold angle_add_overflow.
        progress unfold angle_ltb.
        progress sin_cos_add_sub_right_goal T.
        generalize Hzs1; intros H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        generalize Hzc1; intros H.
        apply (rngl_lt_le_incl Hor) in H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        apply (rngl_ltb_ge Hor).
        apply (rngl_le_trans Hor _ 0); [ | easy ].
        apply (rngl_opp_nonpos_nonneg Hop Hor).
        now apply (rngl_lt_le_incl Hor) in Hzc1.
      }
      rewrite angle_sub_straight_eq_add_straight.
      rewrite angle_div_2_add_not_overflow. 2: {
        progress unfold angle_add_overflow.
        progress unfold angle_ltb.
        progress sin_cos_add_sub_straight_goal T.
        rewrite (rngl_leb_opp_r Hop Hor).
        rewrite (rngl_opp_0 Hop).
        generalize Hzs2; intros H.
        apply (rngl_lt_le_incl Hor) in H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        generalize Hzs2; intros H.
        apply (rngl_leb_gt Hor) in H.
        now rewrite H.
      }
      rewrite angle_straight_div_2.
      rewrite angle_add_assoc.
      rewrite (angle_add_add_swap (θ1 / ₂)).
      rewrite rngl_sin_add_right_r.
      rewrite <- angle_div_2_add_not_overflow. 2: {
        apply angle_add_not_overflow_comm.
        apply angle_add_overflow_lt_straight_le_straight. {
          (* lemma? cf. rngl_sin_nonneg_angle_le_straight *)
          progress unfold angle_ltb.
          generalize Hzs2; intros H.
          apply (rngl_lt_le_incl Hor) in H.
          apply rngl_leb_le in H.
          rewrite H; clear H; cbn.
          rewrite (rngl_leb_refl Hor).
          apply rngl_ltb_lt.
          apply (rngl_le_lt_trans Hor _ 0); [ | easy ].
          apply (rngl_opp_1_le_0 Hon Hop Hor).
        } {
          apply (rngl_lt_le_incl Hor) in Hzc1.
          now apply rngl_sin_nonneg_angle_le_straight.
        }
      }
      rewrite rngl_cos_add_right_div_2_r.
      progress unfold rngl_div.
      rewrite Hiv.
      (* lemma *)
      rewrite (rngl_mul_comm Hic).
      apply (rngl_mul_pos_neg Hop Hor Hid). {
        apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
        apply (rl_sqrt_pos Hon Hos Hor).
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      apply (rngl_lt_sub_0 Hop Hor).
      apply rngl_cos_lt_sin_diag.
      split. {
        apply angle_div_2_lt_compat.
        progress unfold angle_ltb.
        cbn - [ angle_add ].
        specialize (rngl_0_le_1 Hon Hop Hor) as H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        rename Hzs12 into Hc12z.
        remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
        symmetry in Hzs12.
        destruct zs12; [ | easy ].
        apply rngl_leb_le in Hzs12.
        apply rngl_ltb_lt.
        apply (rngl_lt_iff Hor).
        split; [ easy | ].
        intros H.
        apply eq_rngl_cos_0 in H.
        rename H12 into Hco1.
        destruct H as [H12| H12]. {
          apply H12z.
          rewrite angle_add_add_swap.
          rewrite H12.
          rewrite (angle_right_add_right Hon Hop).
          apply angle_sub_diag.
        }
        apply (rngl_nlt_ge Hor) in Hzs12.
        apply Hzs12; clear Hzs12.
        rewrite H12; cbn.
        apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
      }
      progress unfold angle_ltb.
      rewrite rngl_sin_5_right_div_2.
      rewrite rngl_cos_5_right_div_2.
      rewrite (rngl_leb_opp_r Hop Hor).
      rewrite (rngl_opp_0 Hop).
      specialize (rl_sqrt_half_pos Hc1) as H.
      apply (rngl_leb_gt Hor) in H.
      rewrite H; clear H.
      specialize (rngl_sin_div_2_nonneg (θ1 + θ2)) as H.
      apply rngl_leb_le in H.
      now rewrite H; clear H.
    }
    exfalso.
    apply rngl_leb_le in Hzs12.
    apply rngl_leb_nle in Hzs1.
    apply Hzs1; clear Hzs1.
    remember (angle_add_overflow θ1 θ2) as aov eqn:Haov.
    symmetry in Haov.
    destruct aov. 2: {
      now apply (rngl_sin_add_nonneg_sin_nonneg _ θ2).
    }
    specialize (angle_div_2_add_overflow _ _ Haov) as H1.
    symmetry in H1.
    apply angle_add_move_r in H1.
    rewrite angle_sub_straight_eq_add_straight in H1.
    rewrite H1 in Hzs12d, H12.
    rewrite rngl_sin_add_straight_r in Hzs12d.
    apply (rngl_nlt_ge Hor).
    intros Hsz1.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12d.
    apply (rngl_nlt_ge Hor) in Hzs12d.
    apply Hzs12d; clear Hzs12d.
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_sin_div_2_nonneg | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H| H]. {
      now apply eq_angle_div_2_0 in H.
    }
    now apply (angle_div_2_not_straight Hc1) in H.
  }
  destruct zs1; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs12, Hzs1.
  apply (rngl_ltb_ge Hor).
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
    destruct (rngl_le_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hs2z]. {
      change_angle_add_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_goal T.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
        apply rngl_sin_sub_nonneg_sin_le_sin. {
          apply (rngl_lt_le_incl Hor) in Hzs1.
          now apply rngl_sin_add_nonneg.
        } {
          now apply (rngl_lt_le_incl Hor) in Hzs12.
        }
        rewrite angle_add_comm.
        now rewrite angle_add_sub.
      }
      exfalso.
      apply (rngl_nle_gt Hor) in Hc2z.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      change_angle_sub_r θ2 angle_right.
      progress sin_cos_add_sub_right_hyp T Hc2z.
      progress sin_cos_add_sub_right_hyp T Hzs2.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_lt_le_incl Hor) in Hzs1, Hc2z.
      now apply rngl_sin_add_nonneg.
    }
    apply (rngl_nle_gt Hor) in Hs2z.
    apply (rngl_nlt_ge Hor).
    intros Hcc.
    specialize (angle_div_2_add_overflow θ1 θ2) as H1.
    assert (H : angle_add_overflow θ1 θ2 = true). {
      progress unfold angle_add_overflow.
      progress unfold angle_ltb.
      generalize Hzs12; intros H.
      apply (rngl_leb_gt Hor) in H.
      rewrite H; clear H.
      generalize Hzs1; intros H.
      apply (rngl_leb_gt Hor) in H.
      rewrite H; clear H.
      now apply rngl_ltb_lt.
    }
    specialize (H1 H); clear H.
    symmetry in H1.
    apply angle_add_move_r in H1.
    rewrite angle_sub_straight_eq_add_straight in H1.
    rewrite H1 in Hzs12d, H12.
    rewrite rngl_sin_add_straight_r in Hzs12d.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12d.
    apply (rngl_nlt_ge Hor) in Hzs12d.
    apply Hzs12d; clear Hzs12d.
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_sin_div_2_nonneg | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H| H]. {
      now apply eq_angle_div_2_0 in H.
    }
    now apply (angle_div_2_not_straight Hc1) in H.
  }
  apply (rngl_nle_gt Hor) in Hzc1.
  change_angle_add_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzc1.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hs2z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      apply (rngl_lt_le_incl Hor) in Hzs1, Hzc1.
      now apply quadrant_1_rngl_cos_add_le_cos_l.
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    change_angle_sub_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hc2z.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_goal T.
    apply (rngl_lt_le_incl Hor) in Hzc1.
    apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
    apply (rngl_lt_le_incl Hor) in Hzs1, Hc2z.
    now apply rngl_sin_add_nonneg.
  } {
    apply (rngl_nle_gt Hor) in Hs2z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      change_angle_add_r θ2 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzc2.
      progress sin_cos_add_sub_right_hyp T Hs2z.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_nlt_ge Hor).
      intros Hcc.
      assert (Hss : (0 ≤ rngl_sin (θ1 + θ2))%L). {
        apply (rngl_lt_le_incl Hor) in Hzs1, Hzc1, Hs2z.
        now apply rngl_sin_add_nonneg.
      }
      assert (Haov : angle_add_overflow θ1 θ2 = false). {
        progress unfold angle_add_overflow.
        progress unfold angle_ltb.
        generalize Hss; intros H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        generalize Hzs1; intros H.
        apply (rngl_lt_le_incl Hor) in H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        apply (rngl_ltb_ge Hor).
        apply (rngl_lt_le_incl Hor) in Hzs1, Hzc1, Hs2z.
        now apply quadrant_1_rngl_cos_add_le_cos_l.
      }
      specialize (angle_div_2_add_not_overflow θ1 θ2 Haov) as H1.
      rewrite angle_sub_straight_eq_add_straight in Hzs12d.
      apply (rngl_opp_le_compat Hop Hor) in Hzs12d.
      rewrite (rngl_opp_0 Hop) in Hzs12d.
      rewrite <- rngl_sin_add_straight_r in Hzs12d.
      rewrite <- rngl_sin_angle_div_2_add_overflow in Hzs12d. 2: {
        progress unfold angle_add_overflow.
        rewrite angle_add_sub_assoc.
        rewrite angle_add_sub_swap.
        rewrite <- angle_add_sub_assoc.
        rewrite angle_straight_sub_right.
        rewrite angle_add_add_swap.
        progress unfold angle_ltb.
        rewrite rngl_sin_add_right_r.
        rewrite rngl_sin_add_straight_r.
        rewrite rngl_cos_add_straight_r.
        rewrite rngl_cos_add_right_r.
        rewrite (rngl_leb_opp_r Hop Hor).
        rewrite (rngl_opp_0 Hop).
        generalize Hzs12; intros H.
        apply (rngl_leb_gt Hor) in H.
        rewrite H; clear H.
        generalize Hzs1; intros H.
        apply (rngl_leb_gt Hor) in H.
        rewrite H; clear H.
        rewrite (rngl_ltb_opp_r Hop Hor), (rngl_opp_involutive Hop).
        now apply rngl_ltb_lt.
      }
      apply (rngl_nlt_ge Hor) in Hzs12d.
      apply Hzs12d; clear Hzs12d.
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_sin_div_2_nonneg | ].
      rewrite angle_add_sub_assoc.
      rewrite angle_add_add_swap.
      rewrite <- angle_add_sub_assoc.
      rewrite angle_straight_sub_right.
      intros H; symmetry in H.
      apply eq_rngl_sin_0 in H.
      destruct H as [H| H]. {
        apply eq_angle_div_2_0 in H.
        apply angle_add_move_0_r in H.
        apply (rngl_nlt_ge Hor) in Hss.
        apply Hss; clear Hss.
        rewrite H; cbn.
        apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
      }
      now apply (angle_div_2_not_straight Hc1) in H.
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    progress sin_cos_add_sub_straight_hyp T Hs2z.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_goal T.
    apply (rngl_nlt_ge Hor).
    intros Hcc.
    apply (rngl_nlt_ge Hor) in Hzs12d.
    apply Hzs12d; clear Hzs12d.
    do 2 rewrite angle_sub_straight_eq_add_straight.
    apply (rngl_opp_lt_compat Hop Hor).
    rewrite (rngl_opp_0 Hop).
    rewrite <- rngl_sin_add_straight_r.
    rewrite <- angle_div_2_add_overflow. 2: {
      progress unfold angle_add_overflow.
      rewrite angle_add_assoc.
      rewrite angle_add_add_swap.
      rewrite <- (angle_add_assoc θ1).
      rewrite angle_straight_add_straight, angle_add_0_r.
      apply angle_lt_iff.
      split. {
        apply angle_add_le_mono_l. {
          apply (rngl_lt_le_incl Hor) in Hs2z.
          apply angle_add_overflow_lt_straight_le_straight.
          now apply rngl_sin_pos_lt_straight.
          now apply rngl_sin_nonneg_le_straight.
        } {
          apply angle_add_straight_r_not_overflow.
          now apply rngl_sin_pos_lt_straight.
        } {
          apply (rngl_lt_le_incl Hor) in Hs2z.
          now apply rngl_sin_nonneg_angle_le_straight.
        }
      }
      intros H.
      apply (f_equal (λ θ, angle_sub θ θ1)) in H.
      rewrite angle_add_comm, angle_add_sub in H.
      rewrite angle_add_sub_swap, angle_sub_diag in H.
      rewrite angle_add_0_l in H; subst θ2.
      now apply (rngl_lt_irrefl Hor) in Hs2z.
    }
    rewrite angle_add_assoc.
    rewrite (angle_add_add_swap θ1).
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight, angle_add_0_r.
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_sin_div_2_nonneg | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H12d| H12d]. {
      apply eq_angle_div_2_0 in H12d.
      rewrite H12d in Hzs12.
      now apply (rngl_lt_irrefl Hor) in Hzs12.
    }
    now apply (angle_div_2_not_straight Hc1) in H12d.
  }
}
Qed.

End a.
