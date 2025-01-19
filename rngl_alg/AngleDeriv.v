(* derivation of trigonometric functions *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.

Require Import Trigo.RealLike.
Require Import Trigo.Angle.
Require Import Trigo.AngleDiv2.
Require Import Trigo.TacChangeAngle.
Require Import Trigo.TrigoWithoutPiExt.
Require Import Trigo.Angle_order.
Require Import Trigo.AngleDivNat.
Require Import Trigo.AngleAddLeMonoL.
Require Import Trigo.AngleDiv2Add.
Require Import Trigo.AngleTypeIsComplete.
Require Import Trigo.AngleAddOverflowLe.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_ltb_ge :
  ∀ θ1 θ2, (θ2 ≤ θ1)%A ↔ (θ1 <? θ2)%A = false.
Proof.
destruct_ac.
intros.
progress unfold angle_ltb.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
split; intros H21. {
  destruct zs1. {
    destruct zs2; [ | easy ].
    apply rngl_leb_le in H21.
    now apply rngl_ltb_ge.
  } {
    destruct zs2; [ easy | ].
    apply rngl_leb_le in H21.
    now apply rngl_ltb_ge.
  }
} {
  destruct zs1. {
    destruct zs2; [ | easy ].
    apply (rngl_ltb_ge_iff Hor) in H21.
    now apply rngl_leb_le.
  } {
    destruct zs2; [ easy | ].
    apply (rngl_ltb_ge_iff Hor) in H21.
    now apply rngl_leb_le.
  }
}
Qed.

Theorem angle_add_div_2_add_sub_div_2 :
  ∀ p q,
  p = ((p + q) /₂ + (p - q) /₂ +
        if Bool.bool_dec (angle_add_overflow p q) (q ≤? p)%A then
          angle_straight
        else 0)%A.
Proof.
intros.
symmetry.
destruct (Bool.bool_dec _ _) as [Hpq| Hpq]. {
  rewrite angle_div_2_add.
  rewrite angle_div_2_sub.
  rewrite Hpq.
  remember (q ≤? p)%A as qp eqn:Hqp.
  symmetry in Hqp.
  destruct qp; cbn. {
    rewrite (angle_add_add_swap _ _ (_ - _)).
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    rewrite angle_add_0_r.
    rewrite angle_add_sub_assoc.
    rewrite angle_add_add_swap.
    rewrite angle_add_sub.
    rewrite <- angle_mul_2_l.
    apply angle_div_2_mul_2.
  } {
    rewrite angle_add_assoc.
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    rewrite angle_add_0_r.
    rewrite angle_add_sub_assoc.
    rewrite angle_add_add_swap.
    rewrite angle_add_sub.
    rewrite <- angle_mul_2_l.
    apply angle_div_2_mul_2.
  }
} {
  rewrite angle_add_0_r.
  rewrite angle_div_2_add.
  rewrite angle_div_2_sub.
  assert (H : angle_add_overflow p q = negb (q ≤? p)%A). {
    remember (angle_add_overflow p q) as b eqn:Hb.
    symmetry in Hb |-*.
    apply not_eq_sym in Hpq.
    destruct b. {
      apply Bool.not_true_iff_false in Hpq.
      now rewrite Hpq.
    } {
      apply Bool.not_false_iff_true in Hpq.
      now rewrite Hpq.
    }
  }
  rewrite H.
  rewrite Bool.negb_if.
  remember (q ≤? p)%A as qp eqn:Hqp.
  symmetry in Hqp.
  destruct qp. {
    rewrite angle_add_sub_assoc.
    rewrite angle_add_add_swap.
    rewrite angle_add_sub.
    rewrite <- angle_mul_2_l.
    apply angle_div_2_mul_2.
  } {
    rewrite angle_add_assoc.
    rewrite (angle_add_add_swap (_ + q /₂)).
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    rewrite angle_add_0_r.
    rewrite angle_add_sub_assoc.
    rewrite angle_add_add_swap.
    rewrite angle_add_sub.
    rewrite <- angle_mul_2_l.
    apply angle_div_2_mul_2.
  }
}
Qed.

Theorem angle_add_div_2_sub_sub_div_2 :
  ∀ p q,
  q = ((p + q) /₂ - (p - q) /₂ +
        if Bool.bool_dec (angle_add_overflow p q) (q ≤? p)%A then
          angle_straight
        else 0)%A.
Proof.
intros.
symmetry.
destruct (Bool.bool_dec _ _) as [Hpq| Hpq]. {
  rewrite angle_div_2_add.
  rewrite angle_div_2_sub.
  rewrite <- Bool.negb_if.
  rewrite Hpq.
  remember (q ≤? p)%A as qp eqn:Hqp.
  symmetry in Hqp.
  destruct qp; cbn. {
    rewrite (angle_add_sub_swap _ _ (_ - _)).
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    rewrite angle_add_0_r.
    rewrite angle_sub_sub_distr.
    rewrite angle_add_sub_swap.
    rewrite angle_sub_diag.
    rewrite angle_add_0_l.
    rewrite <- angle_mul_2_l.
    apply angle_div_2_mul_2.
  } {
    rewrite angle_sub_add_distr.
    rewrite angle_sub_add.
    rewrite angle_sub_sub_distr.
    rewrite angle_add_sub_swap.
    rewrite angle_sub_diag.
    rewrite angle_add_0_l.
    rewrite <- angle_mul_2_l.
    apply angle_div_2_mul_2.
  }
} {
  rewrite angle_add_0_r.
  rewrite angle_div_2_add.
  rewrite angle_div_2_sub.
  assert (H : angle_add_overflow p q = negb (q ≤? p)%A). {
    remember (angle_add_overflow p q) as b eqn:Hb.
    symmetry in Hb |-*.
    apply not_eq_sym in Hpq.
    destruct b. {
      apply Bool.not_true_iff_false in Hpq.
      now rewrite Hpq.
    } {
      apply Bool.not_false_iff_true in Hpq.
      now rewrite Hpq.
    }
  }
  rewrite H.
  rewrite Bool.negb_if.
  remember (q ≤? p)%A as qp eqn:Hqp.
  symmetry in Hqp.
  destruct qp. {
    rewrite angle_sub_sub_distr.
    rewrite angle_add_sub_swap.
    rewrite angle_sub_diag.
    rewrite angle_add_0_l.
    rewrite <- angle_mul_2_l.
    apply angle_div_2_mul_2.
  } {
    rewrite angle_sub_add_distr.
    rewrite angle_sub_sub_distr.
    do 4 rewrite angle_add_sub_swap.
    rewrite angle_sub_add.
    rewrite angle_sub_diag.
    rewrite angle_add_0_l.
    rewrite <- angle_mul_2_l.
    apply angle_div_2_mul_2.
  }
}
Qed.

Theorem rngl_cos_sub_cos :
  ∀ p q,
  let c₁ := if angle_add_overflow p q then angle_straight else 0%A in
  let c₂ := if (p <? q)%A then angle_straight else 0%A in
  (rngl_cos p - rngl_cos q =
     - (2 * rngl_sin ((p + q) /₂ + c₁) * rngl_sin ((p - q) /₂ + c₂)))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (- _))%L.
  apply H1.
}
intros.
rewrite (angle_add_div_2_add_sub_div_2 p q) at 1.
rewrite (angle_add_div_2_sub_sub_div_2 p q) at 5.
destruct (Bool.bool_dec _ _) as [Hpq| Hpq]. {
  do 2 rewrite rngl_cos_add_straight_r.
  rewrite rngl_cos_add, rngl_cos_sub.
  remember ((p + q) /₂)%A as a.
  remember ((p - q) /₂)%A as b.
  move b before a.
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_opp_sub_distr Hop).
  rewrite rngl_add_assoc.
  rewrite (rngl_sub_add Hop).
  rewrite <- (rngl_mul_2_l Hon).
  rewrite <- rngl_mul_assoc.
  rewrite <- (rngl_mul_opp_r Hop).
  f_equal.
  subst c₁ c₂.
  rewrite Hpq.
  remember (q ≤? p)%A as qp eqn:Hqp.
  symmetry in Hqp.
  destruct qp. {
    apply angle_nlt_ge in Hqp.
    apply Bool.not_true_iff_false in Hqp.
    rewrite Hqp.
    rewrite rngl_sin_add_straight_r.
    rewrite angle_add_0_r.
    rewrite <- (rngl_mul_opp_l Hop).
    f_equal.
    symmetry.
    apply (rngl_opp_involutive Hop).
  } {
    apply Bool.not_true_iff_false in Hqp.
    apply angle_nle_gt in Hqp.
    rewrite Hqp.
    rewrite rngl_sin_add_straight_r.
    rewrite angle_add_0_r.
    rewrite <- (rngl_mul_opp_r Hop).
    f_equal.
    symmetry.
    apply (rngl_opp_involutive Hop).
  }
} {
  do 2 rewrite angle_add_0_r.
  rewrite rngl_cos_add, rngl_cos_sub.
  remember ((p + q) /₂)%A as a.
  remember ((p - q) /₂)%A as b.
  move b before a.
  rewrite (rngl_sub_add_distr Hos).
  rewrite (rngl_sub_sub_swap Hop (_ * _)).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_sub_0_l Hop).
  rewrite <- (rngl_opp_add_distr Hop).
  f_equal.
  rewrite <- (rngl_mul_2_l Hon).
  rewrite <- rngl_mul_assoc.
  f_equal.
  subst c₁ c₂.
  remember (q ≤? p)%A as qp eqn:Hqp.
  symmetry in Hqp.
  destruct qp. {
    apply Bool.not_true_iff_false in Hpq.
    rewrite Hpq.
    apply angle_nlt_ge in Hqp.
    apply Bool.not_true_iff_false in Hqp.
    rewrite Hqp.
    now do 2 rewrite angle_add_0_r.
  } {
    apply Bool.not_false_iff_true in Hpq.
    rewrite Hpq.
    apply Bool.not_true_iff_false in Hqp.
    apply angle_nle_gt in Hqp.
    rewrite Hqp.
    do 2 rewrite rngl_sin_add_straight_r.
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_opp_r Hop).
    symmetry.
    apply (rngl_opp_involutive Hop).
  }
}
Qed.

Theorem rngl_sin_angle_eucl_dist' :
  ∀ θ,
  (θ ≤ angle_straight)%A
  → rngl_sin θ = (angle_eucl_dist (2 * θ) 0 / 2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ / _))%L.
  apply H1.
}
intros * Hts.
destruct (angle_eq_dec θ angle_straight) as [Hts'| Hts']. {
  subst θ.
  rewrite angle_mul_2_l.
  rewrite angle_straight_add_straight.
  rewrite angle_eucl_dist_diag.
  symmetry.
  apply (rngl_div_0_l Hos Hi1).
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
}
rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2.
rewrite angle_sub_0_r.
rewrite <- angle_mul_nat_div_2. 2: {
  cbn.
  rewrite angle_add_0_r.
  rewrite Bool.orb_false_r.
  apply angle_add_not_overflow_lt_straight_le_straight; [ | easy ].
  now apply angle_lt_iff.
}
rewrite angle_div_2_mul_2.
rewrite (rngl_mul_comm Hic).
symmetry.
apply (rngl_mul_div Hi1).
apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
Qed.

Theorem angle_lt_straight_add_same_not_overflow :
  ∀ θ, (θ < angle_straight)%A → angle_add_overflow θ θ = false.
Proof.
intros * Hθ.
apply angle_add_not_overflow_lt_straight_le_straight; [ easy | ].
now apply angle_lt_le_incl.
Qed.

Theorem rngl_sin_is_continuous :
  continuous angle_eucl_dist rngl_dist rngl_sin.
Proof.
destruct_ac.
intros a ε Hε.
exists ε.
split; [ easy | ].
intros x Hxa.
progress unfold rngl_dist.
eapply (rngl_le_lt_trans Hor); [ | apply Hxa ].
apply -> (rngl_abs_le Hop Hor).
split. {
  rewrite <- (rngl_opp_sub_distr Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  rewrite angle_eucl_dist_symmetry.
  apply rngl_sin_diff_le_eucl_dist.
} {
  apply rngl_sin_diff_le_eucl_dist.
}
Qed.

Theorem angle_lt_trans : ∀ θ1 θ2 θ3, (θ1 < θ2 → θ2 < θ3 → θ1 < θ3)%A.
Proof.
intros * H12 H23.
apply (angle_le_lt_trans _ θ2); [ | easy ].
now apply angle_lt_le_incl in H12.
Qed.

Theorem rngl_sin_add_div_2_if_angle_eucl_dist :
  ∀ θ1 θ2,
  rngl_sin ((θ1 - θ2) /₂ + if (θ1 <? θ2)%A then angle_straight else 0) =
  ((if (θ1 <? θ2)%A then -1 else 1) * angle_eucl_dist θ1 θ2 / 2)%L.
Proof.
destruct_ac.
intros.
remember (θ1 <? θ2)%A as b eqn:Hb.
symmetry in Hb.
symmetry.
destruct b. {
  rewrite rngl_sin_add_straight_r.
  rewrite rngl_sin_angle_eucl_dist'. 2: {
    apply angle_div_2_le_straight.
  }
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_div_opp_l Hop Hiv).
  f_equal; f_equal.
  rewrite angle_div_2_mul_2.
  apply angle_eucl_dist_move_0_r.
} {
  rewrite angle_add_0_r.
  rewrite rngl_sin_angle_eucl_dist'. 2: {
    apply angle_div_2_le_straight.
  }
  rewrite (rngl_mul_1_l Hon).
  f_equal.
  rewrite angle_div_2_mul_2.
  apply angle_eucl_dist_move_0_r.
}
Qed.

Theorem rngl_4_eq_2_mul_2 : rngl_has_1 T = true → (2 * 2 = 4)%L.
Proof.
intros Hon.
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_1_r Hon).
apply rngl_add_assoc.
Qed.

Theorem rngl_4_div_2 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (4 / 2 = 2)%L.
Proof.
intros Hon Hos Hiv Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 2%L).
  apply H1.
}
assert (H20 : (2 ≠ 0)%L) by now apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
rewrite <- rngl_add_assoc.
rewrite (rngl_div_add_distr_r Hiv).
now rewrite (rngl_div_diag Hon Hiq).
Qed.

Theorem rngl_cos_derivative_lemma_1 :
  ∀ θ₀ θ,
  θ₀ ≠ 0%A
  → θ₀ ≠ angle_straight
  → (rngl_cos θ₀ < rngl_cos (θ - θ₀))%L
  → (- rngl_cos θ₀ < rngl_cos (θ - θ₀))%L
  → (θ ≤ θ + θ₀)%A
  → (θ₀ ≤ θ)%A
  → (θ < angle_straight)%A.
Proof.
destruct_ac.
intros * Htz Hts H5 H3 Hovt Htt.
assert (H2 : (0 < rngl_cos (θ - θ₀))%L). {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hztz| Hztz]. {
    now eapply (rngl_le_lt_trans Hor); [ | apply H5 ].
  }
  apply (rngl_nle_gt_iff Hor) in Hztz.
  eapply (rngl_le_lt_trans Hor); [ | apply H3 ].
  apply (rngl_lt_le_incl Hor) in Hztz.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
}
progress unfold angle_leb in Hovt.
progress unfold angle_leb in Htt.
progress unfold angle_ltb.
cbn.
rewrite (rngl_leb_refl Hor).
remember (0 ≤? rngl_sin θ)%L as zst eqn:Hzst.
symmetry in Hzst.
destruct zst. {
  apply rngl_ltb_lt.
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_opp_1 in H.
  subst θ.
  rewrite rngl_cos_sub_straight_l in H3.
  now apply (rngl_lt_irrefl Hor) in H3.
}
exfalso.
remember (0 ≤? rngl_sin (θ + θ₀))%L as zstt eqn:Hzstt.
symmetry in Hzstt.
destruct zstt; [ easy | ].
cbn - [ angle_sub ] in H2.
apply (rngl_leb_gt Hor) in Hzst, Hzstt.
apply rngl_leb_le in Hovt.
remember (0 ≤? rngl_sin θ₀)%L as zstz eqn:Hzstz.
symmetry in Hzstz.
destruct zstz. {
  apply rngl_leb_le in Hzstz.
  clear - Hop Hor Hzstz Hzst H3 H5 H2 Hts Htz.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
    change_angle_opp θ.
    progress sin_cos_opp_hyp T Hzst.
    progress sin_cos_opp_hyp T Hzc.
    rewrite <- angle_opp_add_distr in H3, H5, H2.
    rewrite rngl_cos_opp in H3, H5, H2.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
      apply rngl_nlt_ge in H5.
      apply H5; clear H5.
      apply (rngl_lt_le_incl Hor) in Hzst.
      now apply quadrant_1_rngl_cos_add_le_cos_l.
    }
    apply (rngl_nle_gt_iff Hor) in Hzcz.
    change_angle_sub_r θ₀ angle_right.
    progress sin_cos_add_sub_right_hyp T Hzstz.
    progress sin_cos_add_sub_right_hyp T H2.
    progress sin_cos_add_sub_right_hyp T Hzcz.
    apply rngl_nlt_ge in H2.
    apply H2; clear H2.
    apply (rngl_lt_le_incl Hor) in Hzcz, Hzst.
    now apply rngl_sin_add_nonneg.
  }
  apply (rngl_nle_gt_iff Hor) in Hzc.
  change_angle_add_r θ angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzst.
  progress sin_cos_add_sub_straight_hyp T H3.
  progress sin_cos_add_sub_straight_hyp T H5.
  progress sin_cos_add_sub_straight_hyp T H2.
  progress sin_cos_add_sub_straight_hyp T Hzc.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
    apply rngl_nlt_ge in H2.
    apply H2; clear H2.
    apply (rngl_lt_le_incl Hor) in Hzst, Hzc.
    now apply rngl_cos_sub_nonneg.
  }
  apply (rngl_nle_gt_iff Hor) in Hzcz.
  change_angle_sub_l θ₀ angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzstz.
  progress sin_cos_add_sub_straight_hyp T Hzcz.
  progress sin_cos_add_sub_straight_hyp T H3.
  progress sin_cos_add_sub_straight_hyp T H2.
  progress sin_cos_add_sub_straight_hyp T H5.
  apply rngl_nle_gt in H3.
  apply H3; clear H3.
  rewrite angle_add_comm.
  apply (rngl_lt_le_incl Hor) in Hzst, Hzcz, Hzc.
  now apply quadrant_1_rngl_cos_add_le_cos_l.
}
apply (rngl_leb_gt Hor) in Hzstz.
apply rngl_leb_le in Htt.
clear - Hop Hor Hovt Hzst Hzstz Hzstt Htt.
destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
  clear - Hop Hor Hovt Hzst Hzc Hzstz.
  change_angle_opp θ.
  progress sin_cos_opp_hyp T Hovt.
  progress sin_cos_opp_hyp T Hzst.
  progress sin_cos_opp_hyp T Hzc.
  rewrite rngl_cos_sub_comm in Hovt.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
    change_angle_opp θ₀.
    progress sin_cos_opp_hyp T Hovt.
    progress sin_cos_opp_hyp T Hzstz.
    progress sin_cos_opp_hyp T Hzcz.
    apply rngl_nlt_ge in Hovt.
    apply Hovt; clear Hovt.
    apply (rngl_lt_iff Hor).
    split. {
      apply (rngl_lt_le_incl Hor) in Hzst, Hzstz.
      now apply quadrant_1_rngl_cos_add_le_cos_l.
    }
    intros H.
    apply rngl_cos_eq in H.
    destruct H as [H| H]. {
      rewrite angle_add_comm in H.
      apply angle_add_move_r in H.
      rewrite angle_sub_diag in H.
      subst θ₀.
      now apply (rngl_lt_irrefl Hor) in Hzstz.
    }
    rewrite angle_add_comm in H.
    apply angle_add_move_r in H.
    rewrite <- angle_opp_add_distr in H.
    subst θ₀.
    rewrite rngl_sin_opp in Hzstz.
    apply -> (rngl_opp_pos_neg Hop Hor) in Hzstz.
    apply rngl_nle_gt in Hzstz.
    apply Hzstz; clear Hzstz.
    apply (rngl_lt_le_incl Hor) in Hzst.
    now apply rngl_sin_add_nonneg.
  }
  apply (rngl_nle_gt_iff Hor) in Hzcz.
  change_angle_add_r θ₀ angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hovt.
  progress sin_cos_add_sub_straight_hyp T Hzstz.
  progress sin_cos_add_sub_straight_hyp T Hzcz.
  apply rngl_nlt_ge in Hovt.
  apply Hovt; clear Hovt.
  apply (rngl_add_nonneg_pos Hor); [ easy | ].
  apply (rngl_lt_le_incl Hor) in Hzcz.
  now apply rngl_cos_sub_pos_2.
}
clear - Hop Hor Hzc Hzstt Hzc Hzst Htt Hzstz.
apply (rngl_nle_gt_iff Hor) in Hzc.
change_angle_add_r θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzstt.
progress sin_cos_add_sub_straight_hyp T Hzst.
progress sin_cos_add_sub_straight_hyp T Hzc.
progress sin_cos_add_sub_straight_hyp T Htt.
destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
  change_angle_opp θ₀.
  progress sin_cos_opp_hyp T Hzstt.
  progress sin_cos_opp_hyp T Hzcz.
  progress sin_cos_opp_hyp T Htt.
  apply rngl_nlt_ge in Htt.
  apply Htt; clear Htt.
  now apply (rngl_add_nonneg_pos Hor).
}
apply (rngl_nle_gt_iff Hor) in Hzcz.
change_angle_add_r θ₀ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzstt.
progress sin_cos_add_sub_straight_hyp T Hzstz.
progress sin_cos_add_sub_straight_hyp T Hzcz.
progress sin_cos_add_sub_straight_hyp T Htt.
apply rngl_nle_gt in Hzstt.
apply Hzstt; clear Hzstt.
apply (rngl_lt_le_incl Hor) in Hzst, Hzstz, Hzc, Hzcz.
now apply rngl_sin_add_nonneg.
Qed.

Theorem rngl_cos_derivative_lemma_2 :
  ∀ θ₀ θ,
  (rngl_cos θ₀ < rngl_cos (θ - θ₀))%L
  → (- rngl_cos θ₀ < rngl_cos (θ - θ₀))%L
  → angle_add_overflow θ₀ θ = false
  → (θ₀ ≤ θ)%A
  → (θ - θ₀ ≤ angle_straight)%A.
Proof.
destruct_ac.
intros * H5 H3 Hovt Htt.
assert (H2 : (0 < rngl_cos (θ - θ₀))%L). {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hztz| Hztz]. {
    now eapply (rngl_le_lt_trans Hor); [ | apply H5 ].
  }
  apply (rngl_nle_gt_iff Hor) in Hztz.
  eapply (rngl_le_lt_trans Hor); [ | apply H3 ].
  apply (rngl_lt_le_incl Hor) in Hztz.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
}
rewrite <- angle_add_overflow_equiv2 in Hovt.
progress unfold angle_add_overflow2 in Hovt.
apply angle_ltb_ge in Hovt.
progress unfold angle_leb in Hovt.
progress unfold angle_leb in Htt.
progress unfold angle_leb.
cbn - [ angle_sub ].
rewrite (rngl_leb_refl Hor).
remember (0 ≤? rngl_sin (θ - θ₀))%L as zstst eqn:Hzstst.
symmetry in Hzstst.
destruct zstst; [ apply rngl_leb_le, rngl_cos_bound | ].
exfalso.
remember (0 ≤? rngl_sin θ₀)%L as zstz eqn:Hzstz.
remember (0 ≤? rngl_sin θ)%L as zst eqn:Hzst.
remember (0 ≤? rngl_sin (θ₀ + θ))%L as zstt eqn:Hzstt.
symmetry in Hzstz, Hzst, Hzstt.
destruct zstz. 2: {
  destruct zst; [ easy | ].
  destruct zstt; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzstz, Hzstt, Hzst, Hzstst.
  apply rngl_leb_le in Hovt, Htt.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
    clear - Hop Hor Hzstst Hzc Hzst Hovt Hzstz.
    change_angle_opp θ.
    rewrite <- angle_opp_add_distr in Hzstst.
    progress sin_cos_opp_hyp T Hzc.
    progress sin_cos_opp_hyp T Hzstst.
    progress sin_cos_opp_hyp T Hzst.
    progress sin_cos_opp_hyp T Hovt.
    rewrite rngl_cos_sub_comm in Hovt.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
      change_angle_opp θ₀.
      rewrite angle_add_opp_l in Hzstst.
      rewrite angle_sub_opp_r in Hovt.
      progress sin_cos_opp_hyp T Hzstz.
      progress sin_cos_opp_hyp T Hzcz.
      progress sin_cos_opp_hyp T Hovt.
      apply rngl_nlt_ge in Hovt.
      apply Hovt; clear Hovt.
      apply (rngl_lt_iff Hor).
      split. {
        rewrite angle_add_comm.
        apply (rngl_lt_le_incl Hor) in Hzstz, Hzst.
        now apply quadrant_1_rngl_cos_add_le_cos_l.
      }
      intros H.
      apply rngl_cos_eq in H.
      destruct H as [H| H]. {
        apply angle_add_move_r in H.
        rewrite angle_sub_diag in H.
        subst θ.
        now apply (rngl_lt_irrefl Hor) in Hzst.
      }
      apply angle_add_move_r in H.
      rewrite <- angle_opp_add_distr in H.
      subst θ.
      rewrite rngl_sin_opp in Hzst.
      apply (rngl_opp_pos_neg Hop Hor) in Hzst.
      apply rngl_nle_gt in Hzst.
      apply Hzst; clear Hzst.
      apply (rngl_lt_le_incl Hor) in Hzstz.
      now apply rngl_sin_add_nonneg.
    }
    apply (rngl_nle_gt_iff Hor) in Hzcz.
    change_angle_add_r θ₀ angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzstz.
    progress sin_cos_add_sub_straight_hyp T Hzstst.
    progress sin_cos_add_sub_straight_hyp T Hzcz.
    apply rngl_nle_gt in Hzstst.
    apply Hzstst; clear Hzstst.
    apply (rngl_lt_le_incl Hor) in Hzstz, Hzst, Hzcz.
    now apply rngl_sin_add_nonneg.
  }
  clear - Hor Hzc Htt Hzst Hzstt Hzstz.
  apply (rngl_nle_gt_iff Hor) in Hzc.
  change_angle_add_r θ angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzc.
  progress sin_cos_add_sub_straight_hyp T Htt.
  progress sin_cos_add_sub_straight_hyp T Hzst.
  progress sin_cos_add_sub_straight_hyp T Hzstt.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
    change_angle_opp θ₀.
    rewrite angle_add_opp_l in Hzstt.
    progress sin_cos_opp_hyp T Hzstz.
    progress sin_cos_opp_hyp T Htt.
    progress sin_cos_opp_hyp T Hzcz.
    apply rngl_nlt_ge in Htt.
    apply Htt; clear Htt.
    now apply (rngl_add_nonneg_pos Hor).
  }
  apply (rngl_nle_gt_iff Hor) in Hzcz.
  change_angle_add_r θ₀ angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzstz.
  progress sin_cos_add_sub_straight_hyp T Htt.
  progress sin_cos_add_sub_straight_hyp T Hzcz.
  progress sin_cos_add_sub_straight_hyp T Hzstt.
  apply rngl_nle_gt in Hzstt.
  apply Hzstt; clear Hzstt.
  apply (rngl_lt_le_incl Hor) in Hzstz, Hzst, Hzcz, Hzc.
  now apply rngl_sin_add_nonneg.
}
apply rngl_leb_le in Hzstz.
apply (rngl_leb_gt Hor) in Hzstst.
destruct zst. {
  clear - Hop Hor Hzstz Hzstst Hzst Htt Hzstt.
  apply rngl_leb_le in Hzst, Htt.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
      destruct zstt. 2: {
        apply Bool.not_true_iff_false in Hzstt.
        apply Hzstt; clear Hzstt.
        apply rngl_leb_le.
        now apply rngl_sin_add_nonneg.
      }
      apply rngl_nle_gt in Hzstst.
      apply Hzstst; clear Hzstst.
      now apply rngl_sin_sub_nonneg.
    }
    apply (rngl_nle_gt_iff Hor) in Hzcz.
    change_angle_sub_l θ₀ angle_straight.
    rewrite angle_sub_sub_distr in Hzstst.
    rewrite <- angle_add_sub_swap in Hzstst.
    progress sin_cos_add_sub_straight_hyp T Hzstz.
    progress sin_cos_add_sub_straight_hyp T Hzstt.
    progress sin_cos_add_sub_straight_hyp T Hzstst.
    progress sin_cos_add_sub_straight_hyp T Htt.
    progress sin_cos_add_sub_straight_hyp T Hzcz.
    apply rngl_nlt_ge in Htt.
    apply Htt; clear Htt.
    now apply (rngl_add_nonneg_pos Hor).
  }
  apply (rngl_nle_gt_iff Hor) in Hzc.
  change_angle_sub_l θ angle_straight.
  rewrite <- angle_sub_add_distr in Hzstst.
  progress sin_cos_add_sub_straight_hyp T Hzc.
  progress sin_cos_add_sub_straight_hyp T Hzstst.
  progress sin_cos_add_sub_straight_hyp T Htt.
  progress sin_cos_add_sub_straight_hyp T Hzst.
  progress sin_cos_add_sub_straight_hyp T Hzstt.
  rewrite <- rngl_sin_sub_anticomm in Hzstt.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
    apply rngl_nle_gt in Hzstst.
    apply Hzstst; clear Hzstst.
    apply (rngl_lt_le_incl Hor) in Hzc.
    now apply rngl_sin_add_nonneg.
  }
  apply (rngl_nle_gt_iff Hor) in Hzcz.
  change_angle_sub_l θ₀ angle_straight.
  rewrite angle_sub_sub_distr in Hzstt.
  rewrite <- angle_add_sub_swap in Hzstt.
  progress sin_cos_add_sub_straight_hyp T Hzstz.
  progress sin_cos_add_sub_straight_hyp T Hzstt.
  progress sin_cos_add_sub_straight_hyp T Hzstst.
  progress sin_cos_add_sub_straight_hyp T Htt.
  progress sin_cos_add_sub_straight_hyp T Hzcz.
  rewrite (rngl_add_opp_l Hop) in Htt.
  apply -> (rngl_le_sub_0 Hop Hor) in Htt.
  apply rngl_nle_gt in Hzstst.
  apply Hzstst; clear Hzstst.
  rewrite rngl_sin_sub_anticomm.
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  now apply rngl_sin_sub_nonneg.
}
apply (rngl_leb_gt Hor) in Hzst.
clear - Hor Hzst H5 H2 Hzstst Hzstz.
destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
  change_angle_opp θ.
  rewrite <- angle_opp_add_distr in H5, H2, Hzstst.
  progress sin_cos_opp_hyp T H5.
  progress sin_cos_opp_hyp T H2.
  progress sin_cos_opp_hyp T Hzc.
  progress sin_cos_opp_hyp T Hzstst.
  progress sin_cos_opp_hyp T Hzst.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
    apply rngl_nle_gt in H5.
    apply H5; clear H5.
    apply (rngl_lt_le_incl Hor) in Hzst.
    now apply quadrant_1_rngl_cos_add_le_cos_l.
  }
  apply (rngl_nle_gt_iff Hor) in Hzcz.
  change_angle_sub_l θ₀ angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzstz.
  progress sin_cos_add_sub_straight_hyp T H2.
  progress sin_cos_add_sub_straight_hyp T H5.
  progress sin_cos_add_sub_straight_hyp T Hzstst.
  progress sin_cos_add_sub_straight_hyp T Hzcz.
  apply rngl_nle_gt in H5.
  apply H5; clear H5.
  apply (rngl_lt_le_incl Hor).
  rewrite rngl_cos_sub_comm.
  apply rngl_cos_lt_rngl_cos_sub; [ easy | easy | ].
  apply (rngl_lt_le_incl Hor) in Hzst, Hzcz, Hzstst.
  now apply quadrant_1_sin_sub_nonneg_cos_le.
}
apply (rngl_nle_gt_iff Hor) in Hzc.
change_angle_add_r θ angle_straight.
progress sin_cos_add_sub_straight_hyp T H5.
progress sin_cos_add_sub_straight_hyp T H2.
progress sin_cos_add_sub_straight_hyp T Hzc.
progress sin_cos_add_sub_straight_hyp T Hzstst.
progress sin_cos_add_sub_straight_hyp T Hzst.
destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
  apply rngl_nle_gt in H2.
  apply H2; clear H2.
  apply (rngl_lt_le_incl Hor) in Hzst, Hzc.
  now apply rngl_cos_sub_nonneg.
}
apply (rngl_nle_gt_iff Hor) in Hzcz.
change_angle_sub_r θ₀ angle_right.
progress sin_cos_add_sub_right_hyp T Hzstz.
progress sin_cos_add_sub_right_hyp T H2.
progress sin_cos_add_sub_right_hyp T H5.
progress sin_cos_add_sub_right_hyp T Hzstst.
progress sin_cos_add_sub_right_hyp T Hzcz.
apply rngl_nle_gt in Hzstst.
apply Hzstst; clear Hzstst.
apply (rngl_lt_le_incl Hor) in Hzst, Hzc, Hzcz.
now apply rngl_cos_sub_nonneg.
Qed.

Theorem rngl_cos_derivative_lemma_3 :
  ∀ θ₀ θ,
  (θ < θ₀)%A
  → (rngl_cos θ₀ < rngl_cos (θ₀ - θ))%L
  → angle_add_overflow θ₀ θ = false
  → (- rngl_cos θ₀ < rngl_cos (θ₀ - θ))%L
  → (θ₀ ≤ angle_straight)%A.
Proof.
destruct_ac.
intros * Htt H5 Hovt H3.
assert (H2 : (0 < rngl_cos (θ₀ - θ))%L). {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hztz| Hztz]. {
    now eapply (rngl_le_lt_trans Hor); [ | apply H5 ].
  }
  apply (rngl_nle_gt_iff Hor) in Hztz.
  eapply (rngl_le_lt_trans Hor); [ | apply H3 ].
  apply (rngl_lt_le_incl Hor) in Hztz.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
}
rewrite <- angle_add_overflow_equiv2 in Hovt.
progress unfold angle_add_overflow2 in Hovt.
apply angle_ltb_ge in Hovt.
progress unfold angle_ltb in Htt.
progress unfold angle_leb in Hovt.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
remember (0 ≤? rngl_sin θ₀)%L as zstz eqn:Hzstz.
symmetry in Hzstz.
destruct zstz; [ apply rngl_leb_le, rngl_cos_bound | ].
exfalso.
remember (0 ≤? rngl_sin (θ₀ + θ))%L as zstt eqn:Hzstt.
symmetry in Hzstt.
destruct zstt; [ easy | ].
apply (rngl_leb_gt Hor) in Hzstz, Hzstt.
apply rngl_leb_le in Hovt.
remember (0 ≤? rngl_sin θ)%L as zst eqn:Hzst.
symmetry in Hzst.
destruct zst. 2: {
  apply (rngl_leb_gt Hor) in Hzst.
  apply rngl_ltb_lt in Htt.
  now apply angle_add_overflow_le_lemma_10 in Hovt.
}
clear Htt.
apply rngl_leb_le in Hzst.
destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
  change_angle_opp θ₀.
  progress sin_cos_opp_hyp T Hzstz.
  progress sin_cos_opp_hyp T Hzcz.
  progress sin_cos_opp_hyp T H3.
  progress sin_cos_opp_hyp T H5.
  progress sin_cos_opp_hyp T H2.
  progress sin_cos_opp_hyp T Hovt.
  progress sin_cos_opp_hyp T Hzstt.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
    apply rngl_nle_gt in H5.
    apply H5; clear H5.
    rewrite angle_add_comm.
    apply (rngl_lt_le_incl Hor) in Hzstz.
    now apply quadrant_1_rngl_cos_add_le_cos_l.
  }
  apply (rngl_nle_gt_iff Hor) in Hzc.
  change_angle_sub_r θ angle_right.
  progress sin_cos_add_sub_right_hyp T Hzst.
  progress sin_cos_add_sub_right_hyp T Hzc.
  progress sin_cos_add_sub_right_hyp T H2.
  apply (rngl_nle_gt) in H2.
  apply H2; clear H2.
  apply (rngl_lt_le_incl Hor) in Hzc, Hzstz.
  now apply rngl_sin_add_nonneg.
}
apply (rngl_nle_gt_iff Hor) in Hzcz.
change_angle_sub_r θ₀ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzstz.
progress sin_cos_add_sub_straight_hyp T Hzcz.
progress sin_cos_add_sub_straight_hyp T H3.
progress sin_cos_add_sub_straight_hyp T H5.
progress sin_cos_add_sub_straight_hyp T H2.
progress sin_cos_add_sub_straight_hyp T Hovt.
progress sin_cos_add_sub_straight_hyp T Hzstt.
destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
  apply rngl_nle_gt in H2.
  apply H2; clear H2.
  apply (rngl_lt_le_incl Hor) in Hzstz, Hzcz.
  now apply rngl_cos_sub_nonneg.
}
apply (rngl_nle_gt_iff Hor) in Hzc.
change_angle_sub_l θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzst.
progress sin_cos_add_sub_straight_hyp T Hzc.
progress sin_cos_add_sub_straight_hyp T Hzstt.
progress sin_cos_add_sub_straight_hyp T Hovt.
progress sin_cos_add_sub_straight_hyp T H3.
progress sin_cos_add_sub_straight_hyp T H5.
progress sin_cos_add_sub_straight_hyp T H2.
apply rngl_nle_gt in H3.
apply H3; clear H3.
apply (rngl_lt_le_incl Hor) in Hzstz, Hzcz, Hzc.
now apply quadrant_1_rngl_cos_add_le_cos_l.
Qed.

(* *)

Definition angle_lt θ1 θ2 := (θ1 < θ2)%A.

(* to be completed
(* could be generalized, perhaps, to a ordered group which has
   a division by 2, not only my angles *)
Theorem angle_limit_by_sequence :
  rngl_is_archimedean T = true →
  ∀ db (f : angle T → T) θ₀ (L : T),
  is_limit_when_tending_to_neighbourhood _ _ angle_lt angle_eucl_dist db f θ₀ L ↔
  is_limit_when_tending_to_inf db (λ n : nat, f (θ₀ - θ₀ /₂^n))%A L.
Proof.
intros Har.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  split; intros H2 ε Hε; rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros.
split; intros H1. {
  intros ε Hε.
  specialize (H1 ε Hε).
  destruct H1 as (η & H1).
  progress unfold angle_lt in H1.
  specialize (int_part Hon Hop Hc1 Hor Har (2 / ε)%L) as H2.
  destruct H2 as (N, HN).
  exists N.
  intros n Hn.
  apply H1. 2: {
    rewrite angle_eucl_dist_sub_l_diag.
Theorem angle_eucl_dist_div_2_pow_le :
  ∀ θ n, (angle_eucl_dist (θ /₂^n) 0 ≤ 4 / 2 ^ n)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (angle_eucl_dist _ _)).
  rewrite (H1 (_ / _)%L).
  apply (rngl_le_refl Hor).
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
assert (H20 : (2 ≠ 0)%L) by now apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
intros.
revert θ.
induction n; intros. {
  cbn.
  rewrite (rngl_div_1_r Hon Hiq Hc1).
  rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2.
  rewrite (rngl_mul_comm Hic).
  apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
  rewrite angle_sub_0_r.
  rewrite (rngl_4_div_2 Hon Hos Hiv Hor).
  apply (rngl_le_trans Hor _ 1).
  apply rngl_sin_bound.
  apply (rngl_le_add_r Hor).
  apply (rngl_0_le_1 Hon Hos Hor).
}
rewrite rngl_pow_succ_r.
rewrite (rngl_mul_comm Hic 2).
rewrite <- (rngl_4_eq_2_mul_2 Hon).
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | ]. 2: {
  now apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
}
rewrite (rngl_mul_div Hi1); [ | easy ].
...
rewrite angle_div_2_pow_succ_r_2.
eapply (rngl_le_trans Hor); [ apply IHn | ].
(* ah oui non, mais c'est faux, ça *)
...
rewrite angle_eucl_dist_is_sqrt.
rewrite angle_sub_0_l.
rewrite rngl_cos_opp.
Search (_ < rngl_cos _)%L.
rngl_cos_lt_iff_angle_eucl_lt:
...
Search (angle_eucl_dist _ _ = _).
rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2.
rewrite angle_sub_0_r.
Search (rngl_sin (_ /₂)).
Search (rngl_sin (
...
*)

(* *)

Definition angle_lt_for_deriv θ1 θ2 :=
  (θ1 < θ2)%A ∧ angle_add_overflow θ1 θ2 = false.

Theorem rngl_cos_left_derivative :
  ∀ θ₀,
  left_derivative_at angle_lt_for_deriv angle_eucl_dist rngl_dist
    rngl_cos (λ θ, (- rngl_sin θ)%L) θ₀.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀.
  intros ε Hε; rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
assert (H20 : (2 ≠ 0)%L) by now apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
intros θ₀.
destruct (angle_eq_dec θ₀ 0) as [Htz| Htz]. {
  subst θ₀.
  intros ε Hε.
  exists 0%L.
  intros θ Hlt Hθ.
  destruct Hlt as (Hlt, _).
  apply angle_nle_gt in Hlt.
  exfalso; apply Hlt.
  apply angle_nonneg.
}
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  intros ε Hε.
  subst θ₀.
  cbn.
  exists ε.
  intros θ Hlt Hθ.
  rewrite <- (rngl_opp_add_distr Hop).
  rewrite (rngl_opp_0 Hop).
  rewrite rngl_cos_angle_eucl_dist_straight_r.
  rewrite (rngl_sub_add Hop).
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite (rngl_div_div_swap Hic Hiv).
  progress unfold rngl_squ.
  rewrite (rngl_mul_div Hi1). 2: {
    destruct Hlt as (H1, H2).
    intros H.
    apply angle_eucl_dist_separation in H.
    rewrite H in H1.
    now apply angle_lt_irrefl in H1.
  }
  progress unfold rngl_dist.
  rewrite (rngl_sub_0_r Hos).
  rewrite (rngl_abs_opp Hop Hor).
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_div_nonneg Hon Hop Hiv Hor); [ | easy ].
    apply angle_eucl_dist_nonneg.
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor); [ easy | ].
  eapply (rngl_lt_le_trans Hor _ ε); [ easy | ].
  rewrite <- (rngl_mul_1_r Hon ε) at 1.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_le_add_l Hor).
  apply (rngl_0_le_1 Hon Hos Hor).
}
specialize rngl_sin_is_continuous as Hsc.
progress unfold continuous in Hsc.
progress unfold continuous_at in Hsc.
progress unfold is_limit_when_tending_to in Hsc.
intros ε Hε.
specialize (Hsc θ₀ ε Hε).
destruct Hsc as (η & Hη & Hsc).
progress unfold rngl_dist in Hsc.
move η before ε.
remember (angle_eucl_dist θ₀ 0) as y.
exists (rngl_min3 y (angle_eucl_dist θ₀ angle_straight) η).
subst y.
intros θ Htt H2.
destruct Htt as (Htt, Hovt).
move θ before θ₀.
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H4).
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H3).
rename H2 into H5.
progress unfold rngl_dist.
rewrite (rngl_sub_opp_r Hop).
rewrite rngl_cos_sub_cos.
rewrite rngl_sin_add_div_2_if_angle_eucl_dist.
rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_mul_div Hi1); [ | easy ].
rewrite (rngl_div_opp_l Hop Hiv).
rewrite rngl_mul_assoc.
rewrite angle_eucl_dist_symmetry.
rewrite (rngl_mul_div Hi1). 2: {
  intros H.
  apply angle_eucl_dist_separation in H.
  rewrite H in Htt.
  now apply angle_lt_irrefl in Htt.
}
rewrite angle_add_overflow_comm in Hovt.
rewrite Hovt.
rewrite <- (rngl_abs_opp Hop Hor).
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_l Hop).
generalize Htt; intros H.
apply angle_lt_le_incl in H.
apply angle_nlt_ge in H.
apply Bool.not_true_iff_false in H.
rewrite H; clear H.
rewrite (rngl_mul_1_r Hon).
rewrite angle_add_0_r.
apply Hsc.
eapply (rngl_le_lt_trans Hor); [ | apply H4 ].
clear η Hη Hsc H4.
do 2 rewrite (angle_eucl_dist_symmetry _ θ₀).
rewrite angle_eucl_dist_move_0_r.
rewrite (angle_eucl_dist_move_0_r θ₀).
assert (Hzs : (θ₀ < angle_straight)%A). {
  apply angle_lt_iff.
  split; [ | easy ].
  apply rngl_cos_lt_iff_angle_eucl_lt in H3, H5.
  rewrite angle_sub_0_r in H5.
  rewrite rngl_cos_sub_straight_r in H3.
  rewrite rngl_cos_sub_comm in H3, H5.
  now apply (rngl_cos_derivative_lemma_3 _ θ).
}
rewrite <- (angle_div_2_mul_2 θ₀) at 1.
rewrite angle_mul_nat_div_2. 2: {
  cbn.
  rewrite angle_add_0_r.
  rewrite Bool.orb_false_r.
  now apply angle_lt_straight_add_same_not_overflow.
}
rewrite angle_div_2_sub'.
rewrite angle_mul_2_l.
rewrite angle_sub_add_distr.
rewrite angle_add_sub.
rewrite (angle_add_comm θ₀ θ).
generalize Htt; intros H.
rewrite angle_add_overflow_comm in Hovt.
apply angle_lt_le_incl in H.
apply (angle_add_le_mono_l θ₀) in H. 2: {
  now apply angle_lt_straight_add_same_not_overflow.
}
rewrite (angle_add_comm _ θ) in H.
rewrite H; clear H.
apply angle_le_angle_eucl_dist_le; cycle 2. {
  apply angle_div_2_le.
} {
  apply angle_div_2_le_straight.
}
apply rngl_sin_nonneg_angle_le_straight.
move Htt at bottom.
progress unfold angle_ltb in Htt.
progress unfold angle_ltb in Hzs.
cbn in Hzs.
rewrite (rngl_leb_refl Hor) in Hzs.
remember (0 ≤? rngl_sin θ₀)%L as zsz eqn:Hzsz.
remember (0 ≤? rngl_sin θ)%L as zst eqn:Hzst.
symmetry in Hzsz, Hzst.
destruct zsz; [ | easy ].
destruct zst; [ | easy ].
apply rngl_leb_le in Hzsz, Hzst.
apply rngl_ltb_lt in Hzs, Htt.
apply (rngl_lt_le_incl Hor) in Htt.
apply rngl_sin_sub_nonneg; try easy.
Qed.

Theorem rngl_cos_right_derivative_at_0 :
  right_derivative_at angle_lt_for_deriv angle_eucl_dist rngl_dist rngl_cos
    (λ θ : angle T, (- rngl_sin θ)%L) 0%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros ε Hε; rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
intros ε Hε; cbn.
rewrite (rngl_opp_0 Hop).
exists ε.
intros θ Hlt Hθ.
rewrite rngl_cos_angle_eucl_dist_0_r.
rewrite (rngl_sub_sub_swap Hop).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_sub_0_l Hop).
progress unfold rngl_dist.
rewrite (rngl_sub_0_r Hos).
rewrite (rngl_div_opp_l Hop Hiv).
rewrite (rngl_abs_opp Hop Hor).
rewrite (rngl_div_div_swap Hic Hiv).
progress unfold rngl_squ.
rewrite (rngl_mul_div Hi1). 2: {
  destruct Hlt as (H1, H2).
  intros H.
  apply angle_eucl_dist_separation in H.
  rewrite H in H1.
  now apply angle_lt_irrefl in H1.
}
rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor); [ | easy ].
  apply angle_eucl_dist_nonneg.
}
apply (rngl_lt_div_l Hon Hop Hiv Hor); [ easy | ].
eapply (rngl_lt_le_trans Hor _ ε); [ easy | ].
rewrite <- (rngl_mul_1_r Hon ε) at 1.
apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
apply (rngl_le_add_l Hor).
apply (rngl_0_le_1 Hon Hos Hor).
Qed.

Theorem rngl_cos_right_derivative_at_straight :
  right_derivative_at angle_lt_for_deriv angle_eucl_dist rngl_dist rngl_cos
    (λ θ : angle T, (- rngl_sin θ)%L) angle_straight.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros ε Hε; rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
intros ε Hε; cbn.
exists ε.
intros θ Hlt Hθ.
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_opp_0 Hop).
rewrite rngl_cos_angle_eucl_dist_straight_r.
rewrite (rngl_sub_add Hop).
rewrite (rngl_div_div_swap Hic Hiv).
progress unfold rngl_squ.
rewrite (rngl_mul_div Hi1). 2: {
  destruct Hlt as (H1, H2).
  intros H.
  apply angle_eucl_dist_separation in H.
  rewrite H in H1.
  now apply angle_lt_irrefl in H1.
}
progress unfold rngl_dist.
rewrite (rngl_sub_0_r Hos).
rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor); [ | easy ].
  apply angle_eucl_dist_nonneg.
}
apply (rngl_lt_div_l Hon Hop Hiv Hor); [ easy | ].
eapply (rngl_lt_le_trans Hor _ ε); [ easy | ].
rewrite <- (rngl_mul_1_r Hon ε) at 1.
apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
apply (rngl_le_add_l Hor).
apply (rngl_0_le_1 Hon Hos Hor).
Qed.

Theorem rngl_cos_right_derivative :
  ∀ θ₀,
  right_derivative_at angle_lt_for_deriv angle_eucl_dist rngl_dist
    rngl_cos (λ θ, (- rngl_sin θ)%L) θ₀.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀.
  intros ε Hε; rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
assert (H20 : (2 ≠ 0)%L) by now apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
intros θ₀.
destruct (angle_eq_dec θ₀ 0) as [Htz| Htz]. {
  subst θ₀.
  apply rngl_cos_right_derivative_at_0.
}
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  subst θ₀.
  apply rngl_cos_right_derivative_at_straight.
}
intros ε Hε.
destruct (rngl_sin_is_continuous θ₀ ε Hε) as (η & Hη & Hsc).
move η before ε.
remember (angle_eucl_dist θ₀ 0) as x.
remember (angle_eucl_dist θ₀ angle_straight) as y.
exists (rngl_min3 x y η); subst x y.
intros θ (Htt, Hovt) H1.
move θ before θ₀.
apply (rngl_min_glb_lt_iff Hor) in H1.
destruct H1 as (H1, H3).
apply (rngl_min_glb_lt_iff Hor) in H1.
destruct H1 as (H1, H2).
progress unfold rngl_dist.
rewrite (rngl_sub_opp_r Hop).
rewrite rngl_cos_sub_cos.
rewrite rngl_sin_add_div_2_if_angle_eucl_dist.
rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_mul_div Hi1); [ | easy ].
rewrite (rngl_div_opp_l Hop Hiv).
rewrite rngl_mul_assoc.
rewrite (rngl_mul_div Hi1). 2: {
  intros H.
  apply angle_eucl_dist_separation in H.
  rewrite H in Htt.
  now apply angle_lt_irrefl in Htt.
}
rewrite angle_add_overflow_comm in Hovt.
rewrite Hovt.
rewrite <- (rngl_abs_opp Hop Hor).
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_l Hop).
generalize Htt; intros H.
apply angle_lt_le_incl in H.
apply angle_nlt_ge in H.
apply Bool.not_true_iff_false in H.
rewrite H; clear H.
rewrite (rngl_mul_1_r Hon).
rewrite angle_add_0_r.
apply Hsc.
eapply (rngl_le_lt_trans Hor); [ | apply H3 ].
clear η Hη Hsc H3.
rewrite angle_eucl_dist_move_0_r.
rewrite (angle_eucl_dist_move_0_r θ).
rewrite <- (angle_div_2_mul_2 θ₀) at 2.
rewrite angle_mul_nat_div_2. 2: {
  clear - Hor Hop H1 H2 Hovt Htt Hts Htz.
  cbn.
  rewrite angle_add_0_r.
  rewrite Bool.orb_false_r.
  apply angle_lt_straight_add_same_not_overflow.
  apply (angle_lt_trans _ θ); [ easy | ].
  apply rngl_cos_lt_iff_angle_eucl_lt in H1, H2.
  rewrite angle_sub_0_r in H1.
  rewrite rngl_cos_sub_straight_r in H2.
  rewrite <- angle_add_overflow_equiv2 in Hovt.
  progress unfold angle_add_overflow2 in Hovt.
  apply angle_ltb_ge in Hovt.
  apply angle_lt_le_incl in Htt.
  now apply (rngl_cos_derivative_lemma_1 θ₀).
}
clear - Hor Hop Hovt Htt H1 H2.
rewrite angle_div_2_sub'.
rewrite angle_mul_2_l.
rewrite angle_sub_add_distr.
rewrite angle_add_sub.
generalize Htt; intros H.
rewrite angle_add_overflow_comm in Hovt.
apply angle_lt_le_incl in H.
apply (angle_add_le_mono_l θ₀) in H; [ | easy ].
rewrite (angle_add_comm _ θ) in H.
rewrite H; clear H.
apply angle_le_angle_eucl_dist_le; cycle 2. {
  apply angle_div_2_le.
} {
  apply angle_div_2_le_straight.
}
apply rngl_cos_lt_iff_angle_eucl_lt in H1, H2.
rewrite angle_sub_0_r in H1.
rewrite rngl_cos_sub_straight_r in H2.
apply angle_lt_le_incl in Htt.
now apply rngl_cos_derivative_lemma_2.
Qed.

Theorem rngl_cos_derivative :
  is_derivative angle_lt_for_deriv angle_eucl_dist rngl_dist
    rngl_cos (λ θ, (- rngl_sin θ)%L).
Proof.
intros θ₀.
split.
apply rngl_cos_left_derivative.
apply rngl_cos_right_derivative.
Qed.

Theorem angle_add_overflow_move_add_l :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ2 θ3 = false
  → angle_add_overflow (θ1 + θ2) θ3 = angle_add_overflow θ1 (θ2 + θ3).
Proof.
intros * H12 H23.
remember (angle_add_overflow (_ + _) _) as ov2 eqn:Hov2.
symmetry in Hov2.
symmetry.
destruct ov2. {
  now apply angle_add_overflow_move_add.
} {
  rewrite angle_add_comm.
  now apply angle_add_not_overflow_move_add.
}
Qed.

End a.
