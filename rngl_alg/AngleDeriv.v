(* derivation of trigonometric functions *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import Main.Misc.

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
Require Import Trigo.SeqAngleIsCauchy.

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

Theorem rngl_sin_angle_eucl_dist_twice_0 :
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
  rewrite rngl_sin_angle_eucl_dist_twice_0. 2: {
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
  rewrite rngl_sin_angle_eucl_dist_twice_0. 2: {
    apply angle_div_2_le_straight.
  }
  rewrite (rngl_mul_1_l Hon).
  f_equal.
  rewrite angle_div_2_mul_2.
  apply angle_eucl_dist_move_0_r.
}
Qed.

Theorem rngl_4_eq_2_mul_2 : rngl_has_1 T = true → (4 = 2 * 2)%L.
Proof.
intros Hon.
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_1_r Hon).
symmetry.
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

Theorem rngl_2_sub_1 : rngl_has_opp_or_subt T = true → (2 - 1 = 1)%L.
Proof.
intros Hos.
apply (rngl_add_sub Hos).
Qed.

(* *)

Definition angle_lt θ1 θ2 := (θ1 < θ2)%A.

Theorem angle_eucl_dist_div_2_pow_succ_le :
  ∀ n θ,
  (θ ≤ angle_straight)%A
  → (angle_eucl_dist (θ /₂^S n) 0 ≤ angle_eucl_dist (θ /₂^n ) 0 / √2)%L.
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
assert (H20 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hos Hor).
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
assert (H20' : (2 ≠ 0)%L) by now apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
intros * Hzs.
revert θ Hzs.
induction n; intros. {
  cbn.
  do 2 rewrite angle_eucl_dist_is_sqrt.
  do 2 rewrite angle_sub_0_l.
  do 2 rewrite rngl_cos_opp.
  rewrite <- (rl_sqrt_div Hon Hop Hiv Hor); [ | | easy ]. 2: {
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  apply (rl_sqrt_le_rl_sqrt Hon Hop Hor Hii). {
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_mul_comm Hic _ (1 - rngl_cos θ)).
  rewrite (rngl_mul_div Hi1); [ | easy ].
  rewrite (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_sub_sub_distr Hop).
  apply (rngl_sub_le_mono_l Hop Hor).
  apply (rngl_le_add_le_sub_l Hop Hor).
  cbn.
  generalize Hzs; intros H.
  apply rngl_sin_nonneg_angle_le_straight in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_comm Hic).
  apply (rngl_le_div_l Hon Hop Hiv Hor); [ easy | ].
  destruct (angle_eq_dec θ angle_straight) as [Hts| Hts]. {
    subst θ.
    cbn.
    rewrite (rngl_add_opp_r Hop).
    rewrite (rngl_sub_diag Hos).
    rewrite (rngl_div_0_l Hos Hi1); [ | easy ].
    rewrite (rl_sqrt_0 Hon Hop Hor Hii).
    apply (rngl_le_refl Hor).
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor (_ / _)) at 1. 2: {
    apply rngl_1_add_cos_div_2_nonneg.
  }
  rewrite <- (rl_sqrt_squ Hon Hop Hor).
  apply (rl_sqrt_le_rl_sqrt Hon Hop Hor Hii). {
    apply (rngl_squ_nonneg Hos Hor).
  }
  assert (Hc2z : ((1 + rngl_cos θ) / 2 ≠ 0)%L). {
    intros H.
    apply (f_equal (λ a, (a * 2)%L)) in H.
    rewrite (rngl_div_mul Hon Hiv) in H; [ | easy ].
    rewrite (rngl_mul_0_l Hos) in H.
    rewrite rngl_add_comm in H.
    apply (rngl_add_sub_eq_r Hos) in H.
    rewrite (rngl_sub_0_l Hop) in H.
    symmetry in H.
    now apply eq_rngl_cos_opp_1 in H.
  }
  apply (rngl_le_div_r Hon Hop Hiv Hor). 2: {
    rewrite (rngl_div_diag Hon Hiq); [ | easy ].
    apply (rngl_le_div_l Hon Hop Hiv Hor); [ easy | ].
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite (rngl_add_sub Hos).
    apply rngl_cos_bound.
  }
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_1_add_cos_div_2_nonneg | easy ].
}
rewrite angle_div_2_pow_succ_r_2.
rewrite (angle_div_2_pow_succ_r_2 _ θ).
apply IHn.
apply angle_div_2_le_straight.
Qed.

Theorem angle_eucl_dist_bound : ∀ θ1 θ2, (angle_eucl_dist θ1 θ2 ≤ 2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (angle_eucl_dist _ _)).
  rewrite (H1 2%L).
  apply (rngl_le_refl Hor).
}
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H20.
intros.
rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2.
rewrite (rngl_mul_comm Hic).
apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
rewrite (rngl_div_diag Hon Hiq); [ | easy ].
apply rngl_sin_bound.
Qed.

Theorem angle_eucl_dist_div_2_pow_le :
  ∀ n θ,
  (θ ≤ angle_straight)%A
  → (angle_eucl_dist (θ /₂^n) 0 ≤ angle_eucl_dist θ 0 / (√2 ^ n))%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (angle_eucl_dist _ _)).
  rewrite (H1 (_ / _)%L).
  apply (rngl_le_refl Hor).
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
specialize (rngl_0_le_2 Hon Hos Hor) as Hz2'.
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H20.
intros * Hts.
revert θ Hts.
induction n; intros. {
  cbn.
  rewrite (rngl_div_1_r Hon Hiq Hc1).
  apply (rngl_le_refl Hor).
}
rewrite angle_div_2_pow_succ_r_2.
eapply (rngl_le_trans Hor). {
  apply IHn.
  apply angle_div_2_le_straight.
}
rewrite rngl_pow_succ_r.
rewrite (rngl_mul_comm Hic).
rewrite <- (rngl_div_div Hos Hon Hiv); cycle 1. {
  intros H.
  now apply (eq_rl_sqrt_0 Hon Hos) in H.
} {
  apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
  intros H.
  now apply (eq_rl_sqrt_0 Hon Hos) in H.
}
apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii). {
  apply (rngl_pow_pos_pos Hon Hos Hiv Hc1 Hor).
  now apply (rl_sqrt_pos Hon Hos Hor).
}
apply (angle_eucl_dist_div_2_pow_succ_le 0 θ Hts).
Qed.

Theorem angle_eucl_dist_straight_0 :
  angle_eucl_dist angle_straight 0 = 2%L.
Proof.
destruct_ac.
rewrite angle_eucl_dist_is_sqrt.
rewrite angle_sub_0_l.
rewrite angle_opp_straight; cbn.
rewrite (rngl_sub_opp_r Hop).
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hon Hop Hor).
apply (rngl_abs_2 Hon Hos Hor).
Qed.

Theorem angle_eucl_dist_right_0 :
  angle_eucl_dist angle_right 0 = √2%L.
Proof.
destruct_ac.
rewrite angle_eucl_dist_is_sqrt.
f_equal.
rewrite angle_sub_0_l.
cbn.
rewrite (rngl_sub_0_r Hos).
apply (rngl_mul_1_r Hon).
Qed.

Theorem angle_eucl_dist_straight_div_2_pow_le :
  ∀ n, (angle_eucl_dist (angle_straight /₂^n) 0 ≤ 2 / √2 ^ n)%L.
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
specialize (rngl_0_le_2 Hon Hos Hor) as Hz2'.
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H20.
intros.
eapply (rngl_le_trans Hor). {
  apply angle_eucl_dist_div_2_pow_le.
  apply angle_le_refl.
}
rewrite angle_eucl_dist_straight_0.
apply (rngl_le_refl Hor).
Qed.

Theorem  rl_sqrt_le_diag :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  rngl_is_ordered T = true →
  ∀ a, (1 ≤ a)%L → (√a ≤ a)%L.
Proof.
intros Hon Hop Hii Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H1a.
assert (Hza : (0 ≤ a)%L). {
  apply (rngl_le_trans Hor _ 1); [ | easy ].
  apply (rngl_0_le_1 Hon Hos Hor).
}
apply (rngl_le_squ_le Hop Hor Hii); [ now apply rl_sqrt_nonneg | easy | ].
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite <- (rngl_mul_1_l Hon a) at 1.
now apply (rngl_mul_le_mono_nonneg_r Hop Hor).
Qed.

Theorem angle_eucl_dist_le_straight_div_2_pow_bound :
  ∀ θ n,
  (θ ≤ angle_straight)%A
  → (angle_eucl_dist (θ /₂^n) 0 ≤ 2 / √2 ^ n)%L.
Proof.
destruct_ac.
intros * Hts.
eapply (rngl_le_trans Hor). 2: {
  apply angle_eucl_dist_straight_div_2_pow_le.
}
apply angle_le_angle_eucl_dist_le. {
  eapply angle_le_trans; [ | apply Hts ].
  apply angle_div_2_pow_le_diag.
} {
  apply angle_div_2_pow_le_diag.
}
now apply angle_div_2_pow_le.
Qed.

Theorem angle_eucl_dist_div_2_pow_bound :
  ∀ θ n,
  (angle_eucl_dist (θ /₂^n) 0 ≤ 4 / √2 ^ n)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (angle_eucl_dist _ _)).
  rewrite (H1 (_ / _)%L).
  apply (rngl_le_refl Hor).
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
specialize (rngl_0_le_2 Hon Hos Hor) as Hz2'.
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H20.
intros.
revert θ.
induction n; intros. {
  cbn.
  rewrite (rngl_div_1_r Hon Hiq Hc1).
  apply (rngl_le_trans Hor _ 2); [ apply angle_eucl_dist_bound | ].
  apply (rngl_add_le_mono_r Hop Hor).
  now apply (rngl_le_add_l Hor).
}
rewrite angle_div_2_pow_succ_r_2.
eapply (rngl_le_trans Hor). {
  apply angle_eucl_dist_le_straight_div_2_pow_bound.
  apply angle_div_2_le_straight.
}
cbn.
rewrite (rngl_mul_comm Hic).
rewrite <- (rngl_div_div Hos Hon Hiv); cycle 1. {
  intros H.
  now apply (eq_rl_sqrt_0 Hon Hos) in H.
} {
  apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
  intros H.
  now apply (eq_rl_sqrt_0 Hon Hos) in H.
}
apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii). {
  apply (rngl_pow_pos_pos Hon Hos Hiv Hc1 Hor).
  now apply (rl_sqrt_pos Hon Hos Hor).
}
rewrite <- (rngl_mul_1_r Hon 2) at 1.
rewrite (rngl_4_eq_2_mul_2 Hon).
rewrite <- (rngl_mul_div_assoc Hiv).
apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
apply (rngl_le_div_r Hon Hop Hiv Hor). {
  now apply (rl_sqrt_pos Hon Hos Hor).
}
rewrite (rngl_mul_1_l Hon).
apply (rl_sqrt_le_diag Hon Hop Hii Hor).
apply (rngl_le_add_l Hor).
apply (rngl_0_le_1 Hon Hos Hor).
Qed.

Theorem Nat_pow_2_eq_2_pow_succ : ∀ n, n ^ 2 ≤ 2 ^ S n.
Proof.
intros.
cbn.
rewrite Nat.mul_1_r, Nat.add_0_r.
induction n; [ easy | cbn ].
rewrite (Nat.mul_comm n); cbn.
rewrite Nat.add_0_r.
rewrite Nat.add_assoc.
rewrite <- Nat.add_succ_l.
apply Nat.add_le_mono; [ | apply IHn ].
clear IHn.
induction n; [ now apply -> Nat.succ_le_mono | ].
cbn.
rewrite Nat.add_succ_r.
rewrite Nat.add_0_r.
do 2 rewrite <- Nat.add_1_r.
rewrite <- Nat.add_assoc.
apply Nat.add_le_mono; [ apply IHn | ].
apply Nat.add_le_mono.
now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

(* *)

(* cette définition ne convient pas ; si θ1 tend vers θ2,
   alors ça ne marche que pour θ2 < π *)
(*
Definition angle_lt_for_deriv θ1 θ2 :=
  (θ1 < θ2)%A ∧ angle_add_overflow θ1 θ2 = false.
*)
Definition angle_lt_for_deriv θ1 θ2 :=
  (θ1 < θ2)%A.

Theorem rngl_cos_left_derivative_at_straight :
  left_derivative_at angle_lt_for_deriv angle_eucl_dist rngl_dist rngl_cos
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
split; [ easy | ].
intros θ Hlt Hθ.
rewrite <- (rngl_opp_add_distr Hop).
rewrite (rngl_opp_0 Hop).
rewrite rngl_cos_angle_eucl_dist_straight_r.
rewrite (rngl_sub_add Hop).
rewrite (rngl_div_opp_l Hop Hiv).
rewrite (rngl_div_div_swap Hic Hiv).
progress unfold rngl_squ.
rewrite (rngl_mul_div Hi1). 2: {
  intros H.
  apply angle_eucl_dist_separation in H.
  rewrite H in Hlt.
  now apply angle_lt_irrefl in Hlt.
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
Qed.

Theorem angle_sub_div_2_diag :
  ∀ θ, (θ - θ /₂ = θ /₂)%A.
Proof.
intros.
apply angle_add_move_r.
rewrite angle_sub_opp_r.
symmetry.
apply angle_add_div_2_diag.
Qed.

(* to be completed
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
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H20.
intros θ₀.
destruct (angle_eq_dec θ₀ 0) as [Htz| Htz]. {
  subst θ₀.
  intros ε Hε.
  exists ε.
  split; [ easy | ].
  intros θ Hlt Hθ.
  apply angle_nle_gt in Hlt.
  exfalso; apply Hlt.
  apply angle_nonneg.
}
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  subst θ₀.
  apply rngl_cos_left_derivative_at_straight.
}
intros ε Hε.
specialize rngl_sin_is_continuous as Hsc.
specialize (Hsc θ₀ ε Hε).
destruct Hsc as (η & Hη & Hsc).
progress unfold rngl_dist in Hsc.
move η before ε.
remember (angle_eucl_dist θ₀ 0) as y.
exists (rngl_min3 y (angle_eucl_dist θ₀ angle_straight) η).
subst y.
split. {
  apply rngl_min_glb_lt; [ | easy ].
  apply rngl_min_glb_lt. {
    apply (rngl_lt_iff Hor).
    split; [ apply angle_eucl_dist_nonneg | ].
    intros H; symmetry in H.
    now apply angle_eucl_dist_separation in H.
  } {
    apply (rngl_lt_iff Hor).
    split; [ apply angle_eucl_dist_nonneg | ].
    intros H; symmetry in H.
    now apply angle_eucl_dist_separation in H.
  }
}
intros θ Htt H2.
move θ before θ₀.
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H4).
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H3).
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
remember (angle_add_overflow θ₀ θ) as ovt eqn:Hovt.
symmetry in Hovt.
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
(*1*)
destruct ovt. {
  rewrite angle_div_2_add.
  rewrite Hovt.
  rewrite <- angle_add_assoc.
  rewrite angle_straight_add_straight.
  rewrite angle_add_0_r.
  apply Hsc.
  eapply (rngl_le_lt_trans Hor); [ | apply H4 ].
  clear η Hη Hsc H4.
  do 2 rewrite (angle_eucl_dist_symmetry _ θ₀).
  rewrite angle_eucl_dist_move_0_r.
  rewrite (angle_eucl_dist_move_0_r θ₀).
  rewrite angle_sub_add_distr.
  rewrite angle_sub_div_2_diag.
  progress unfold angle_lt_for_deriv in Htt.
  rewrite angle_div_2_sub'.
  generalize Htt; intros H.
  apply angle_lt_le_incl in H.
  rewrite H; clear H.
  destruct (angle_le_dec (θ₀ - θ) angle_straight) as [Htts| Htts]. {
    apply angle_le_angle_eucl_dist_le; [ | easy | ]. {
      apply angle_div_2_le_straight.
    }
    apply angle_div_2_le.
  }
  apply angle_nle_gt in Htts.
...
  remember (θ ≤? θ₀)%A as tt eqn:Htt'.
  symmetry in Htt'.
  destruct tt. 2: {
...
  do 2 rewrite <- angle_eucl_dist_move_0_r.
Search (angle_eucl_dist _ _ ≤ angle_eucl_dist _ _)%L.
...
  apply rngl_cos_lt_iff_angle_eucl_lt in H2, H3.
  apply rngl_cos_le_iff_angle_eucl_le.
  rewrite angle_sub_0_r in H2.
  rewrite rngl_cos_sub_straight_r in H3.
...
}
...1
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
  apply rngl_cos_lt_iff_angle_eucl_lt in H2, H3.
  rewrite angle_sub_0_r in H2.
  rewrite rngl_cos_sub_straight_r in H3.
  rewrite rngl_cos_sub_comm in H2, H3.
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
split; [ easy | ].
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
split; [ easy | ].
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
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H20.
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
split. {
  apply rngl_min_glb_lt; [ | easy ].
  apply rngl_min_glb_lt. {
    apply (rngl_lt_iff Hor).
    split; [ apply angle_eucl_dist_nonneg | ].
    intros H; symmetry in H.
    now apply angle_eucl_dist_separation in H.
  } {
    apply (rngl_lt_iff Hor).
    split; [ apply angle_eucl_dist_nonneg | ].
    intros H; symmetry in H.
    now apply angle_eucl_dist_separation in H.
  }
}
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
*)

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

Theorem angle_lt_angle_lt_opp_iff :
  ∀ θ1 θ2,
  (θ1 < θ2 ∧ θ1 < - θ2)%A ↔ (0 ≤ rngl_sin θ1 ∧ rngl_cos θ2 < rngl_cos θ1)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_ltb.
rewrite rngl_sin_opp, rngl_cos_opp.
rewrite (rngl_leb_0_opp Hop Hor).
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
symmetry in Hzs1, Hzs2, Hs2z.
split; intros (H1, H2). {
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    destruct zs1; [ | easy ].
    apply rngl_leb_le in Hzs1.
    split; [ easy | ].
    now apply rngl_ltb_lt in H1.
  }
  apply (rngl_leb_gt Hor) in Hzs2.
  destruct s2z. {
    destruct zs1; [ | easy ].
    apply rngl_leb_le in Hzs1.
    split; [ easy | ].
    now apply rngl_ltb_lt in H2.
  }
  apply (rngl_leb_gt Hor) in Hs2z.
  now apply (rngl_lt_asymm Hor) in Hzs2.
}
generalize H1; intros H.
apply rngl_leb_le in H.
rewrite H in Hzs1; clear H.
subst zs1.
apply rngl_ltb_lt in H2.
split; [ now destruct zs2 | now destruct s2z ].
Qed.

Theorem rngl_sin_angle_eucl_dist_straight_r :
  ∀ θ,
  (θ ≤ angle_straight)%A
  → rngl_sin θ = (rngl_sin (θ /₂) * angle_eucl_dist θ angle_straight)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%L).
  apply H1.
}
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H20.
specialize (rngl_0_le_2 Hon Hos Hor) as Hz2'.
intros * Hts.
cbn.
rewrite angle_eucl_dist_is_sqrt.
rewrite rngl_cos_sub_straight_l.
rewrite (rngl_sub_opp_r Hop).
rewrite <- rl_sqrt_mul; cycle 1. {
  apply rngl_1_sub_cos_div_2_nonneg.
} {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
}
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
rewrite (rngl_mul_comm Hic).
rewrite (rngl_squ_sub_squ' Hop).
rewrite (rngl_mul_1_r Hon), (rngl_mul_1_l Hon).
rewrite (rngl_add_sub Hos).
rewrite (rngl_squ_1 Hon).
specialize (cos2_sin2_1 θ) as H1.
rewrite <- H1, rngl_add_comm.
rewrite (rngl_add_sub Hos).
symmetry.
rewrite (rl_sqrt_squ Hon Hop Hor).
apply (rngl_abs_nonneg_eq Hop Hor).
now apply rngl_sin_nonneg_angle_le_straight.
Qed.

(* to be completed ... à revoir plus tard
Theorem rngl_sin_left_derivative_at_straight :
  left_derivative_at angle_lt_for_deriv angle_eucl_dist rngl_dist rngl_sin
    rngl_cos angle_straight.
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
split; [ easy | ].
intros θ Hlt Hθ.
rewrite (rngl_sub_0_l Hop).
progress unfold rngl_dist.
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_div_opp_l Hop Hiv).
rewrite (rngl_add_opp_l Hop).
progress unfold angle_lt_for_deriv in Hlt.
destruct Hlt as (Hts & Hov).
rewrite rngl_sin_angle_eucl_dist_straight_r. 2: {
  now apply angle_lt_le_incl in Hts.
}
rewrite (rngl_mul_div Hi1). 2: {
  intros H.
  apply angle_eucl_dist_separation in H.
  subst θ.
  now apply angle_lt_irrefl in Hts.
}
rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_sin_bound.
}
change_angle_sub_l θ angle_straight.
rewrite angle_div_2_sub.
remember (θ ≤? angle_straight)%A as ts eqn:Hts'.
symmetry in Hts'.
destruct ts. {
  rewrite angle_straight_div_2.
  rewrite rngl_sin_sub_right_l.
...
Search ((_ - _) * (_ + _))%L.
rewrite (rngl_mul_add_sub).
...
rewrite rngl_cos_angle_eucl_dist_straight_r.
...
rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2.
cbn.
rewrite rngl_mul_opp_r.
rewrite rngl_mul_1_r.
rewrite rngl_opp_0.
rewrite rngl_mul_0_r.
rewrite rngl_sub
progress unfold angle_div_2.
...
rewrite angle_eucl_dist_is_sqrt.
rewrite rngl_cos_sub_straight_l.
rewrite (rngl_sub_opp_r Hop).
...
rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2.
...
Check rngl_cos_angle_eucl_dist_straight_r.
...
rewrite rngl_sin_sub_straight in H1.
rewrite H1.
...
specialize (angle_eucl_dist_straight_r_cos_sin) as H1.
specialize (H1 (θ + angle_right)%A).
rewrite rngl_cos_add_right_r in H1.
rewrite rngl_sin_add_right_r in H1.
rewrite (rngl_squ_add Hic Hon) in H1.
rewrite (rngl_squ_1 Hon) in H1.
rewrite (rngl_mul_1_r Hon) in H1.
rewrite <- rngl_add_assoc in H1.
rewrite (rngl_squ_opp Hop) in H1.
rewrite (rngl_add_comm _²) in H1.
rewrite cos2_sin2_1 in H1.
rewrite <- rngl_add_add_swap in H1.
rewrite (rngl_mul_opp_r Hop) in H1.
rewrite (rngl_add_opp_r Hop) in H1.
rewrite (rngl_sub_mul_r_diag_l Hon Hop) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
}
apply (rngl_sub_move_l Hop) in H1.
(* bref, c'est la merde *)
...
Qed.
About rngl_cos_angle_eucl_dist_straight_r.
...
Search (angle_eucl_dist _ angle_straight).
...
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
Qed.
*)

(* to be completed
Theorem rngl_sin_left_derivative :
  ∀ θ₀,
  left_derivative_at angle_lt_for_deriv angle_eucl_dist rngl_dist
    rngl_sin rngl_cos θ₀.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀.
  intros ε Hε; rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
specialize (rngl_0_le_2 Hon Hos Hor) as Hz2'.
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H20.
intros θ₀.
destruct (angle_eq_dec θ₀ 0) as [Htz| Htz]. {
  subst θ₀.
  intros ε Hε.
  exists ε.
  split; [ easy | ].
  intros θ Hlt Hθ.
  destruct Hlt as (Hlt, _).
  apply angle_nle_gt in Hlt.
  exfalso; apply Hlt.
  apply angle_nonneg.
}
(*
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  subst θ₀.
...
  apply rngl_sin_left_derivative_at_straight.
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
split. {
  apply rngl_min_glb_lt; [ | easy ].
  apply rngl_min_glb_lt. {
    apply (rngl_lt_iff Hor).
    split; [ apply angle_eucl_dist_nonneg | ].
    intros H; symmetry in H.
    now apply angle_eucl_dist_separation in H.
  } {
    apply (rngl_lt_iff Hor).
    split; [ apply angle_eucl_dist_nonneg | ].
    intros H; symmetry in H.
    now apply angle_eucl_dist_separation in H.
  }
}
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
...
*)
(* essai précédent, en essayant d'utiliser la dérivée du cosinus,
   déjà faite *)
specialize (rngl_cos_left_derivative (θ₀ + angle_right)%A) as H1.
intros ε Hε.
specialize (H1 ε Hε).
rewrite rngl_cos_add_right_r in H1.
rewrite rngl_sin_add_right_r in H1.
destruct H1 as (η & Hη & H1).
exists (rngl_min η (angle_eucl_dist angle_right 0)).
split. {
  apply rngl_min_glb_lt; [ easy | ].
  rewrite angle_eucl_dist_right_0.
  now apply (rl_sqrt_pos Hon Hos Hor).
}
intros θ Hlt Hθ.
apply (rngl_min_glb_lt_iff Hor) in Hθ.
destruct Hθ as (H2, H3).
specialize (H1 (θ + angle_right)%A).
rewrite rngl_cos_add_right_r in H1.
rewrite (rngl_sub_opp_r Hop) in H1.
progress unfold angle_lt_for_deriv in Hlt.
destruct Hlt as (Hlt, Hov).
rewrite angle_add_overflow_comm in Hov.
progress unfold angle_add_overflow in Hov.
apply Bool.andb_false_iff in Hov.
destruct Hov as [Hov| Hov]. {
  apply Bool.negb_false_iff in Hov.
  now apply angle_eqb_eq in Hov.
}
apply angle_leb_gt in Hov.
specialize (proj1 (angle_lt_angle_lt_opp_iff _ _) (conj Hlt Hov)) as H.
destruct H as (H4, H5).
progress unfold rngl_dist.
rewrite angle_eucl_dist_right_0 in H3.
destruct (angle_lt_dec (θ + angle_right) (θ₀ + angle_right)) as [Htt| Htt]. {
  progress unfold angle_lt_for_deriv in H1.
  assert
    (H : angle_add_overflow (θ + angle_right) (θ₀ + angle_right) = false). {
(**)
rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2.
apply angle_ltb_ge.
rewrite angle_add_assoc.
rewrite (angle_add_add_swap θ).
rewrite <- angle_add_assoc.
rewrite angle_right_add_right.
eapply angle_le_trans. {
  apply angle_lt_le_incl, Htt.
}
(* bof... *)
...
    progress unfold angle_add_overflow.
    apply Bool.andb_false_iff.
right.
apply angle_leb_gt.
...
*)

End a.
