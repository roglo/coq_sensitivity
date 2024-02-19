Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import RealLike TrigoWithoutPi AngleAddOverflowLe.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rl_sqrt_1 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
 rl_sqrt 1%L = 1%L.
Proof.
intros Hic Hon Hop Hor Hii.
specialize (rngl_0_le_1 Hon Hop Hor) as Hz1.
progress unfold rl_sqrt.
specialize (rl_nth_root_pow 2 1%L Hz1) as H1.
rewrite <- (rngl_squ_1 Hon) in H1 at 2.
rewrite <- (rngl_squ_pow_2 Hon) in H1.
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hii) in H1.
rewrite (rngl_abs_nonneg_eq Hop Hor) in H1. 2: {
  now apply rl_sqrt_nonneg.
}
now rewrite (rngl_abs_1 Hon Hop Hor) in H1.
Qed.

Theorem rngl_cos_angle_div_2_add_not_overflow :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → rngl_cos ((θ1 + θ2) / ₂) = rngl_cos (θ1 / ₂ + θ2 / ₂).
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov.
  rewrite H1; apply H1.
}
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hop Hc1 Hor) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
assert (Hz1ac :  ∀ θ, (0 ≤ 1 + rngl_cos θ)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite (rngl_squ_sqrt Hon) in H; [ | now apply (rngl_lt_le_incl Hor) ].
  now rewrite (rngl_squ_0 Hos) in H.
}
intros * Haov.
generalize Haov; intros Haov_v.
progress unfold angle_add_overflow in Haov.
apply angle_ltb_ge in Haov.
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
cbn.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
destruct zs3. {
  apply rngl_leb_le in Hzs3.
  rewrite (rngl_mul_1_l Hon).
  destruct zs1. {
    apply rngl_leb_le in Hzs1.
    rewrite (rngl_mul_1_l Hon).
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      rewrite (rngl_mul_1_l Hon).
      subst θ3.
      apply rngl_sin_nonneg_sin_nonneg_sin_nonneg; try easy.
      remember (θ1 =? angle_straight)%A as s1 eqn:Hs1.
      symmetry in Hs1.
      destruct s1. {
        apply (angle_eqb_eq Hed) in Hs1; right.
        subst θ1.
        intros H; subst θ2.
        apply angle_nlt_ge in Haov.
        apply Haov; clear Haov.
        rewrite (angle_straight_add_straight Hon Hop).
        apply (angle_straight_pos Hc1).
      }
      apply (angle_eqb_neq Hed) in Hs1.
      now left.
    }
    exfalso.
    apply (rngl_leb_gt Hor) in Hzs2.
    apply (rngl_nle_gt Hor) in Hzs2.
    apply Hzs2; clear Hzs2.
    subst θ3.
    specialize (rngl_sin_nonneg_add_nonneg θ1 θ2 Hzs1 Hzs3) as H1.
    now rewrite Haov_v in H1.
  } {
    apply (rngl_leb_gt Hor) in Hzs1.
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      exfalso.
      progress unfold angle_leb in Haov.
      apply (rngl_leb_gt Hor) in Hzs1.
      rewrite Hzs1 in Haov.
      apply rngl_leb_le in Hzs3.
      now rewrite Hzs3 in Haov.
    }
    apply (rngl_leb_gt Hor) in Hzs2.
    apply (angle_le_rngl_sin_nonneg_sin_nonneg _ _ Haov) in Hzs3.
    now apply (rngl_nlt_ge Hor) in Hzs3.
  }
}
apply (rngl_leb_gt Hor) in Hzs3.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
apply (rngl_opp_inj Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_opp_sub_distr Hop).
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  rewrite (rngl_mul_1_l Hon).
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite (rngl_mul_1_l Hon).
    subst θ3.
    now apply rngl_sin_nonneg_sin_nonneg_sin_neg.
  } {
    apply (rngl_leb_gt Hor) in Hzs2.
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_mul_1_l Hon).
    subst θ3.
    apply (rngl_lt_le_incl Hor) in Hzs2.
    now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
  }
}
apply (rngl_leb_gt Hor) in Hzs1.
destruct zs2. {
  apply rngl_leb_le in Hzs2.
  do 2 rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_sub_opp_r Hop).
  do 2 rewrite (rngl_mul_1_l Hon).
  rewrite (angle_add_comm Hic) in Hθ3.
  subst θ3.
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_comm Hic √((1 + rngl_cos θ1) / _))%L.
  apply (rngl_lt_le_incl Hor) in Hzs1.
  now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
}
apply (rngl_leb_gt Hor) in Hzs2.
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (-1))%L.
rewrite (rngl_squ_opp_1 Hon Hop).
rewrite (rngl_mul_1_l Hon).
subst θ3.
progress unfold angle_leb in Haov.
apply (rngl_nle_gt Hor) in Hzs1, Hzs3.
apply rngl_leb_nle in Hzs1, Hzs3.
rewrite Hzs1, Hzs3 in Haov.
apply rngl_leb_nle in Hzs1, Hzs3.
apply (rngl_nle_gt Hor) in Hzs1, Hzs3.
apply rngl_leb_le in Haov.
move Haov at bottom.
(* changing θ1 into θ1 - angle_straight *)
remember (θ1 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs1.
rewrite (rngl_cos_add_straight_r Hon Hop) in Haov.
apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
rewrite (rngl_cos_add_straight_r Hon Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (angle_add_add_swap Hic Hop) in Haov, Hzs3 |-*.
(* changing θ2 into θ2 - angle_straight *)
remember (θ2 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
move Hzs3 after Hzs3.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs2.
apply (rngl_opp_neg_pos Hop Hor) in Hzs2.
rewrite (rngl_cos_add_straight_r Hon Hop θ2).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (angle_add_assoc Hop) in Haov, Hzs3 |-*.
rewrite <- (angle_add_assoc Hop) in Haov, Hzs3 |-*.
rewrite (angle_straight_add_straight Hon Hop) in Haov, Hzs3 |-*.
rewrite (angle_add_0_r) in Haov, Hzs3 |-*.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1 + rngl_cos θ2))%L
  as [Hzc12| Hc12z]. {
  apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc12z.
exfalso.
apply (rngl_nlt_ge Hor) in Haov.
apply Haov; clear Haov.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
  (* changing θ1 into angle_straight - θ1 *)
  remember (angle_straight - θ1)%A as θ.
  apply angle_sub_move_r in Heqθ.
  rewrite (angle_sub_opp_r Hop) in Heqθ.
  apply angle_add_move_l in Heqθ.
  subst θ1; rename θ into θ1.
  move θ1 after θ2.
  rewrite <- angle_sub_sub_distr in Hzs3 |-*.
  rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs1, Hzs3.
  rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc12z, Hc1z.
  do 2 rewrite (rngl_cos_sub_straight_l Hon Hop).
  apply -> (rngl_opp_lt_compat Hop Hor).
  rewrite rngl_add_comm in Hc12z.
  rewrite (rngl_add_opp_r Hop) in Hc12z.
  apply (rngl_lt_sub_lt_add_l Hop Hor) in Hc12z.
  rewrite rngl_add_0_r in Hc12z.
  rewrite <- (rngl_opp_0 Hop) in Hc1z.
  apply (rngl_opp_le_compat Hop Hor) in Hc1z.
  rewrite <- (rngl_sub_0_l Hop).
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_assoc.
  apply (rngl_add_nonneg_pos Hor). {
    rewrite (rngl_add_mul_r_diag_l Hon).
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
    apply (rngl_le_sub_le_add_l Hop Hor).
    rewrite (rngl_sub_0_l Hop).
    apply rngl_cos_bound.
  }
  now apply (rngl_mul_pos_pos Hop Hor Hii).
} {
  apply (rngl_nle_gt Hor) in Hzc1.
  move Hzc1 before Hzs2.
  rewrite <- (rngl_sub_0_l Hop).
  apply (rngl_lt_add_lt_sub_l Hop Hor).
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2z| Hc2z]. {
    apply (rngl_nle_gt Hor) in Hzs3.
    exfalso.
    apply Hzs3; clear Hzs3; cbn.
    apply (rngl_add_nonneg_nonneg Hor). {
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
      now apply (rngl_lt_le_incl Hor).
    } {
      apply (rngl_mul_nonneg_nonneg Hop Hor);
        now apply (rngl_lt_le_incl Hor).
    }
  } {
    apply (rngl_nle_gt Hor) in Hc2z.
    (* changing θ2 into angle_straight - θ2 *)
    remember (angle_straight - θ2)%A as θ.
    apply angle_sub_move_r in Heqθ.
    rewrite (angle_sub_opp_r Hop) in Heqθ.
    apply angle_add_move_l in Heqθ.
    subst θ2; rename θ into θ2.
    move θ2 before θ1.
    rewrite (angle_add_comm Hic) in Hzs3 |-*.
    rewrite <- angle_sub_sub_distr in Hzs3 |-*.
    rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs2, Hzs3.
    rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc2z, Hc12z |-*.
    apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
    rewrite (rngl_add_opp_r Hop) in Hc12z |-*.
    apply (rngl_lt_sub_lt_add_l Hop Hor) in Hc12z.
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    rewrite rngl_add_0_r in Hc12z |-*.
    apply rngl_cos_lt_rngl_cos_sub; try easy.
    now apply (rngl_lt_le_incl Hor).
  }
}
Qed.

Theorem rngl_sin_angle_div_2_add_not_overflow :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → rngl_sin (angle_div_2 (θ1 + θ2)) =
     rngl_sin (angle_div_2 θ1 + angle_div_2 θ2).
Proof.
intros * Haov.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hop Hc1 Hor) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
assert (Hz1ac :  ∀ θ, (0 ≤ 1 + rngl_cos θ)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite (rngl_squ_sqrt Hon) in H; [ | now apply (rngl_lt_le_incl Hor) ].
  now rewrite (rngl_squ_0 Hos) in H.
}
generalize Haov; intros Haov_v.
progress unfold angle_add_overflow in Haov.
apply angle_ltb_ge in Haov.
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
cbn.
move Haov at bottom.
generalize Haov; intros Haov'.
progress unfold angle_leb in Haov.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  rewrite (rngl_mul_1_l Hon).
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite (rngl_mul_1_l Hon).
    subst θ3.
    remember (θ2 - angle_straight)%A as θ.
    apply angle_add_move_r in Heqθ.
    subst θ2; rename θ into θ2.
    move θ2 before θ1.
    rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs2.
    rewrite <- (rngl_opp_0 Hop) in Hzs2.
    apply (rngl_opp_le_compat Hop Hor) in Hzs2.
    rewrite (angle_add_assoc Hop).
    do 2 rewrite (rngl_cos_add_straight_r Hon Hop).
    do 2 rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_add_opp_r Hop).
    now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
  }
  apply (rngl_leb_gt Hor) in Hzs2.
  subst θ3.
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  symmetry in Hzs12.
  destruct zs12. {
    exfalso.
    apply (rngl_nle_gt Hor) in Hzs2.
    apply Hzs2; clear Hzs2.
    apply rngl_leb_le in Hzs12.
    specialize (rngl_sin_nonneg_add_nonneg θ1 θ2 Hzs1 Hzs12) as H1.
    now rewrite Haov_v in H1.
  }
  clear Haov.
  apply (rngl_leb_gt Hor) in Hzs12.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_l Hop).
  remember (θ2 - angle_straight)%A as θ.
  apply angle_add_move_r in Heqθ.
  subst θ2; rename θ into θ2.
  move θ2 before θ1.
  rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs2.
  rewrite (angle_add_assoc Hop) in Hzs12.
  rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs2, Hzs12.
  rewrite (angle_add_assoc Hop).
  do 2 rewrite (rngl_cos_add_straight_r Hon Hop).
  do 2 rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy. {
    now apply (rngl_lt_le_incl Hor).
  }
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
    apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2))%L as [Hzc2| Hc2z]. {
    rewrite rngl_add_comm.
    rewrite (angle_add_comm Hic) in Hzs12.
    apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  apply (rngl_nle_gt Hor) in Hzs12.
  exfalso; apply Hzs12; clear Hzs12; cbn.
  apply (rngl_add_nonpos_nonpos Hor). {
    apply (rngl_lt_le_incl Hor) in Hc2z.
    now apply (rngl_mul_nonneg_nonpos Hop Hor).
  } {
    apply (rngl_lt_le_incl Hor) in Hzs2, Hc1z.
    now apply (rngl_mul_nonpos_nonneg Hop Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Hzs1.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_add_opp_r Hop).
  remember (θ1 - angle_straight)%A as θ.
  apply angle_add_move_r in Heqθ.
  subst θ1; rename θ into θ1.
  move θ1 after θ2.
  subst θ3.
  rewrite (angle_add_add_swap Hic Hop) in Haov, Haov' |-*.
  do 2 rewrite (rngl_cos_add_straight_r Hon Hop) in Haov.
  rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs1, Haov.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
  do 2 rewrite (rngl_cos_add_straight_r Hon Hop).
  do 2 rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  remember (0 ≤? - rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  symmetry in Hzs12.
  destruct zs12; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
  move Hzs12 at bottom.
  apply rngl_leb_le in Haov.
  apply (rngl_opp_le_compat Hop Hor) in Haov.
  move Haov at bottom.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite (rngl_mul_1_l Hon).
    apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy. {
      now apply (rngl_lt_le_incl Hor).
    }
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
      apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    }
    apply (rngl_nle_gt Hor) in Hc1z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2))%L as [Hzc2| Hc2z]. {
      rewrite rngl_add_comm.
      rewrite (angle_add_comm Hic) in Hzs12.
      apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    apply (rngl_nle_gt Hor) in Hzs12.
    exfalso; apply Hzs12; clear Hzs12; cbn.
    apply (rngl_add_nonpos_nonpos Hor). {
      apply (rngl_lt_le_incl Hor) in Hzs1, Hc2z.
      apply (rngl_mul_nonneg_nonpos Hop Hor); try easy.
    } {
      apply (rngl_lt_le_incl Hor) in Hc1z.
      now apply (rngl_mul_nonpos_nonneg Hop Hor).
    }
  }
  exfalso. (* because goal is nonneg=nonpos *)
  clear Haov'.
  apply (rngl_leb_gt Hor) in Hzs2.
  destruct (rngl_eq_dec Hed (rngl_cos θ1) 0) as [Hc1ez| Hc1ez]. {
    apply (eq_rngl_cos_0) in Hc1ez.
    destruct Hc1ez; subst θ1. {
      cbn in Haov.
      rewrite (rngl_mul_0_l Hos) in Haov.
      rewrite (rngl_sub_0_l Hop) in Haov.
      rewrite (rngl_mul_1_l Hon) in Haov.
      apply (rngl_opp_nonpos_nonneg Hop Hor) in Haov.
      now apply (rngl_nlt_ge Hor) in Haov.
    } {
      apply (rngl_nle_gt Hor) in Hzs1.
      exfalso; apply Hzs1; clear Hzs1.
      apply (rngl_opp_nonpos_nonneg Hop Hor).
      apply (rngl_0_le_1 Hon Hop Hor).
    }
  }
  remember (θ2 - angle_straight)%A as θ.
  apply angle_add_move_r in Heqθ.
  subst θ2; rename θ into θ2.
  move θ2 before θ1.
  rewrite (angle_add_assoc Hop) in Haov, Hzs12.
  rewrite (rngl_cos_add_straight_r Hon Hop) in Haov.
  rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs12, Hzs2.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs12, Hzs2.
  rewrite (rngl_opp_involutive Hop) in Hzs12.
  move Hzs2 before Hzs1.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2))%L as [Hzc2| Hc2z]. {
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12; cbn.
      apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
      apply (rngl_add_nonneg_nonneg Hor).
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    remember (angle_straight - θ2)%A as θ.
    apply angle_sub_move_r in Heqθ.
    rewrite (angle_sub_opp_r Hop) in Heqθ.
    apply angle_add_move_l in Heqθ.
    subst θ2; rename θ into θ2.
    move θ2 before θ1.
    rewrite (angle_add_comm Hic) in Hzs12, Haov.
    rewrite <- angle_sub_sub_distr in Hzs12, Haov.
    rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs12, Hzs2.
    rewrite (rngl_cos_sub_straight_l Hon Hop) in Haov, Hc2z.
    rewrite (rngl_opp_involutive Hop) in Haov.
    apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
    move Hzs2 before Hzs1.
    move Hzc1 before Hzs2.
    move Hc2z before Hzc1.
    apply (rngl_nlt_ge Hor) in Haov.
    apply Haov; clear Haov.
    assert (Hc12 : (rngl_cos θ1 < rngl_cos θ2)%L). {
      apply (rngl_nle_gt Hor).
      apply (rngl_nle_gt Hor) in Hzs12.
      intros H.
      apply Hzs12; clear Hzs12.
      apply rngl_sin_sub_nonneg; try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    }
    apply rngl_cos_lt_rngl_cos_sub; try easy.
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  clear Hc1ez.
  remember (θ1 - angle_right)%A as θ.
  apply angle_sub_move_r in Heqθ.
  rewrite (angle_sub_opp_r Hop) in Heqθ.
  subst θ1; rename θ into θ1.
  move θ1 after θ2.
  rewrite (angle_add_add_swap Hic Hop) in Hzs12, Haov.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs12.
  rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z.
  do 2 rewrite (rngl_cos_add_right_r Hon Hop) in Haov.
  apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
  rewrite (rngl_opp_involutive Hop) in Haov.
  rename Hzs1 into Hzc1; rename Hc1z into Hzs1.
  move Hzs1 after Hzs2.
  move Hzc1 after Hzs2.
  apply (rngl_le_opp_r Hop Hor) in Haov.
  apply (rngl_nlt_ge Hor) in Haov.
  apply Haov; clear Haov; cbn.
  rewrite <- rngl_add_assoc.
  rewrite rngl_add_comm.
  rewrite <- rngl_add_assoc.
  apply (rngl_add_pos_nonneg Hor). {
    now apply (rngl_mul_pos_pos Hop Hor Hii).
  }
  rewrite (rngl_add_mul_r_diag_l Hon).
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply rngl_lt_le_incl.
  apply (rngl_le_sub_le_add_l Hop Hor).
  rewrite (rngl_sub_0_l Hop).
  apply rngl_cos_bound.
}
Qed.

Theorem rngl_cos_angle_div_2_add_overflow :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = true
  → rngl_cos ((θ1 + θ2) / ₂) = rngl_cos (θ1 / ₂ + θ2 / ₂ + angle_straight).
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
intros * Haov.
rewrite (rngl_cos_add_straight_r Hon Hop).
cbn - [ angle_add ].
progress unfold angle_add_overflow in Haov.
progress unfold angle_ltb in Haov.
cbn.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hzs2, Hzs12.
destruct zs12. {
  apply rngl_leb_le in Hzs12.
  destruct zs1. {
    apply rngl_leb_le in Hzs1.
    apply rngl_ltb_lt in Haov.
    rewrite (rngl_mul_1_l Hon).
    rewrite <- rngl_sin_add.
    rewrite <- rngl_cos_add.
    generalize Hzs12; intros H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_opp_sub_distr Hop).
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      rewrite (rngl_mul_1_l Hon).
      remember (θ1 =? angle_straight)%A as t1s eqn:Ht1s.
      symmetry in Ht1s.
      destruct t1s. 2: {
        apply (angle_eqb_neq Hed) in Ht1s.
        exfalso.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov; clear Haov.
        apply angle_add_overflow_le_lemma_111; [ | easy | easy | easy ].
        now left.
      }
      apply (angle_eqb_eq Hed) in Ht1s.
      subst θ1.
      remember (θ2 =? angle_straight)%A as t2s eqn:Ht2s.
      symmetry in Ht2s.
      destruct t2s. 2: {
        apply (angle_eqb_neq Hed) in Ht2s.
        exfalso.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov; clear Haov.
        apply angle_add_overflow_le_lemma_111; [ | easy | easy | easy ].
        now right; left.
      }
      apply (angle_eqb_eq Hed) in Ht2s.
      subst θ2.
      rewrite (angle_straight_add_straight Hon Hop).
      cbn.
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_r Hop).
      rewrite (rngl_sub_diag Hos).
      rewrite (rngl_div_diag Hon Hiq). 2: {
        apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
      }
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
      }
      rewrite (rl_sqrt_1 Hic Hon Hop Hor Hid).
      rewrite (rl_sqrt_0 Hon Hop Hic Hor Hid).
      rewrite (rngl_mul_0_l Hos).
      rewrite (rngl_sub_0_r Hos).
      symmetry.
      apply (rngl_mul_1_l Hon).
    }
    apply (rngl_leb_gt Hor) in Hzs2.
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    apply (rngl_lt_le_incl Hor) in Hzs2.
    now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
  }
  clear Haov.
  apply (rngl_leb_gt Hor) in Hzs1.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_opp_sub_distr Hop).
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_sub_opp_r Hop).
  rewrite <- rngl_sin_add.
  rewrite <- rngl_cos_add.
  generalize Hzs12; intros H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  rewrite (rngl_mul_1_l Hon).
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite (rngl_mul_1_l Hon).
    rewrite (angle_add_comm Hic).
    rewrite (rngl_mul_comm Hic).
    rewrite (rngl_mul_comm Hic √((1 + _)/2))%L.
    apply (rngl_lt_le_incl Hor) in Hzs1.
    now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
  }
  apply (rngl_leb_gt Hor) in Hzs2.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  change_angle_sub_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_goal T.
  change_angle_sub_r θ2 angle_straight.
  rewrite (angle_add_assoc Hop) in Hzs12 |-*.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_goal T.
  do 3 rewrite (rngl_sub_opp_r Hop).
  apply rngl_sin_nonneg_sin_nonneg_sin_nonneg; try easy; cycle 1.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  left; intros H; subst θ1.
  cbn in Hzs1.
  now apply (rngl_lt_irrefl Hor) in Hzs1.
}
destruct zs1; [ easy | ].
apply (rngl_leb_gt Hor) in Hzs1, Hzs12.
apply rngl_ltb_lt in Haov.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_opp_sub_distr Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite <- rngl_sin_add.
rewrite <- rngl_cos_add.
generalize Hzs12; intros H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
destruct zs2. {
  rewrite (rngl_mul_1_l Hon).
  apply rngl_leb_le in Hzs2.
  change_angle_sub_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Haov.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  exfalso.
  apply (rngl_nle_gt Hor) in Haov.
  apply Haov; clear Haov.
  apply angle_add_overflow_le_lemma_111; try easy; cycle 1.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  left; intros H; subst θ1.
  now apply (rngl_lt_irrefl Hor) in Hzs1.
}
apply (rngl_leb_gt Hor) in Hzs2.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
apply (rngl_opp_inj Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_opp_sub_distr Hop).
change_angle_sub_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Haov.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_goal T.
change_angle_sub_r θ2 angle_straight.
rewrite (angle_add_assoc Hop) in Hzs12, Haov |-*.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Haov.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_goal T.
do 3 rewrite (rngl_sub_opp_r Hop).
apply rngl_sin_nonneg_sin_nonneg_sin_neg; try easy; cycle 1.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
progress unfold angle_leb.
generalize Hzs1; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hzs12; intros H.
apply (rngl_leb_gt Hor) in H.
now rewrite H.
Qed.

Theorem rngl_sin_angle_div_2_add_overflow :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = true
  → rngl_sin ((θ1 + θ2) / ₂) = rngl_sin (θ1 / ₂ + θ2 / ₂ + angle_straight).
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
intros * Haov.
rewrite (rngl_sin_add_straight_r Hon Hop).
cbn - [ angle_add ].
progress unfold angle_add_overflow in Haov.
progress unfold angle_ltb in Haov.
cbn.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hzs2, Hzs12.
rewrite <- rngl_cos_add.
destruct zs12. {
  apply rngl_leb_le in Hzs12.
  destruct zs1. {
    apply rngl_leb_le in Hzs1.
    apply rngl_ltb_lt in Haov.
    rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_opp_add_distr Hop).
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      rewrite (rngl_mul_1_l Hon).
      remember (θ1 =? angle_straight)%A as t1s eqn:Ht1s.
      symmetry in Ht1s.
      destruct t1s. 2: {
        apply (angle_eqb_neq Hed) in Ht1s.
        exfalso.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov; clear Haov.
        apply angle_add_overflow_le_lemma_111; [ | easy | easy | easy ].
        now left.
      }
      apply (angle_eqb_eq Hed) in Ht1s.
      subst θ1.
      remember (θ2 =? angle_straight)%A as t2s eqn:Ht2s.
      symmetry in Ht2s.
      destruct t2s. 2: {
        apply (angle_eqb_neq Hed) in Ht2s.
        exfalso.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov; clear Haov.
        apply angle_add_overflow_le_lemma_111; [ | easy | easy | easy ].
        now right; left.
      }
      apply (angle_eqb_eq Hed) in Ht2s.
      subst θ2.
      rewrite (angle_straight_add_straight Hon Hop).
      cbn.
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_r Hop).
      rewrite (rngl_sub_diag Hos).
      rewrite (rngl_div_diag Hon Hiq). 2: {
        apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
      }
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
      }
      rewrite (rl_sqrt_1 Hic Hon Hop Hor Hid).
      rewrite (rl_sqrt_0 Hon Hop Hic Hor Hid).
      rewrite (rngl_mul_0_l Hos).
      rewrite (rngl_mul_0_r Hos).
      rewrite (rngl_sub_0_r Hos).
      symmetry.
      apply (rngl_opp_0 Hop).
    }
    apply (rngl_leb_gt Hor) in Hzs2.
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_add_opp_l Hop).
    change_angle_sub_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    rewrite (angle_add_assoc Hop) in Haov, Hzs12 |-*.
    progress sin_cos_add_sub_straight_hyp T Haov.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_goal T.
    do 2 rewrite (rngl_sub_opp_r Hop).
    destruct (rngl_eq_dec Hed (rngl_sin (θ1 + θ2)) 0) as [Hs12| Hs12]. {
      apply eq_rngl_sin_0 in Hs12.
      destruct Hs12 as [Hs12| Hs12]. {
        exfalso.
        rewrite Hs12 in Haov; cbn in Haov.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov, rngl_cos_bound.
      }
      rewrite Hs12 in Hzs12; cbn in Hzs12.
      rewrite Hs12 in Haov; cbn in Haov.
      rewrite Hs12.
      cbn.
      apply angle_add_move_l in Hs12.
      subst θ2.
      rewrite (rngl_cos_sub_straight_l Hon Hop).
      rewrite (rngl_sub_opp_r Hop).
      do 2 rewrite (rngl_add_opp_r Hop).
      rewrite (rngl_mul_comm Hic).
      do 2 rewrite (rngl_sub_diag Hos).
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
      }
      apply (rl_sqrt_0 Hon Hop Hic Hor Hid).
    }
    apply rngl_sin_nonneg_sin_nonneg_sin_neg; try easy; cycle 1. {
      now apply (rngl_lt_le_incl Hor).
    } {
      now apply (rngl_lt_iff Hor).
    }
    progress unfold angle_leb.
    generalize Hzs1; intros H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    remember (0 ≤? rngl_sin (θ1 + θ2))%L as z12 eqn:Hz12.
    symmetry in Hz12.
    destruct z12; [ | easy ].
    apply rngl_leb_le in Hz12.
    now apply (rngl_le_antisymm Hor) in Hz12.
  }
  clear Haov.
  apply (rngl_leb_gt Hor) in Hzs1.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_opp_add_distr Hop).
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_opp_involutive Hop).
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite (rngl_mul_1_l Hon).
    change_angle_sub_r θ1 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_goal T.
    do 2 rewrite (rngl_sub_opp_r Hop).
    destruct (rngl_eq_dec Hed (rngl_sin (θ1 + θ2)) 0) as [Hs12| Hs12]. {
      apply eq_rngl_sin_0 in Hs12.
      destruct Hs12 as [Hs12| Hs12]. {
        rewrite Hs12.
        apply angle_add_move_l in Hs12.
        rewrite angle_sub_0_l in Hs12.
        subst θ2.
        cbn in Hzs2.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
        now apply (rngl_nlt_ge Hor) in Hzs2.
      }
      rewrite Hs12.
      cbn.
      apply angle_add_move_l in Hs12.
      subst θ2.
      rewrite (rngl_cos_sub_straight_l Hon Hop).
      rewrite (rngl_sub_opp_r Hop).
      do 2 rewrite (rngl_add_opp_r Hop).
      rewrite (rngl_mul_comm Hic).
      do 2 rewrite (rngl_sub_diag Hos).
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
      }
      apply (rl_sqrt_0 Hon Hop Hic Hor Hid).
    }
    apply rngl_sin_nonneg_sin_nonneg_sin_neg; try easy; cycle 1. {
      now apply (rngl_lt_le_incl Hor).
    } {
      now apply (rngl_lt_iff Hor).
    }
    progress unfold angle_leb.
    generalize Hzs1; intros H.
    apply (rngl_lt_le_incl Hor) in H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    remember (0 ≤? rngl_sin (θ1 + θ2))%L as z12 eqn:Hz12.
    symmetry in Hz12.
    destruct z12; [ | easy ].
    apply rngl_leb_le in Hz12.
    now apply (rngl_le_antisymm Hor) in Hz12.
  }
  apply (rngl_leb_gt Hor) in Hzs2.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  change_angle_sub_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_goal T.
  do 2 rewrite (rngl_sub_opp_r Hop).
  apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
  now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
}
destruct zs1; [ easy | ].
apply (rngl_leb_gt Hor) in Hzs1, Hzs12.
apply rngl_ltb_lt in Haov.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_opp_involutive Hop).
destruct zs2. {
  apply rngl_leb_le in Hzs2.
  rewrite (rngl_mul_1_l Hon).
  change_angle_sub_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Haov.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_goal T.
  do 2 rewrite (rngl_sub_opp_r Hop).
  exfalso.
  apply (rngl_nle_gt Hor) in Haov.
  apply Haov; clear Haov.
  apply angle_add_overflow_le_lemma_111; try easy; cycle 1. {
    now apply (rngl_lt_le_incl Hor).
  } {
    now apply (rngl_lt_le_incl Hor).
  }
  remember (θ1 =? angle_straight)%A as t1s eqn:Ht1s.
  symmetry in Ht1s.
  destruct t1s. 2: {
    apply (angle_eqb_neq Hed) in Ht1s.
    now left.
  }
  apply (angle_eqb_eq Hed) in Ht1s.
  subst θ1.
  now apply (rngl_lt_irrefl Hor) in Hzs1.
}
apply (rngl_leb_gt Hor) in Hzs2.
change_angle_sub_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Haov.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_goal T.
do 2 rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
Qed.

Theorem angle_div_2_add :
  ∀ θ1 θ2,
  ((θ1 + θ2) / ₂)%A =
    if angle_add_overflow θ1 θ2 then
      (θ1 / ₂ + θ2 / ₂ + angle_straight)%A
    else
      (θ1 / ₂ + θ2 / ₂)%A.
Proof.
intros.
remember (angle_add_overflow θ1 θ2) as aov eqn:Haov.
symmetry in Haov.
destruct aov. 2: {
  apply eq_angle_eq.
  f_equal. {
    now apply rngl_cos_angle_div_2_add_not_overflow.
  } {
    now apply rngl_sin_angle_div_2_add_not_overflow.
  }
} {
  apply eq_angle_eq.
  f_equal. {
    now apply rngl_cos_angle_div_2_add_overflow.
  } {
    now apply rngl_sin_angle_div_2_add_overflow.
  }
}
Qed.

End a.
