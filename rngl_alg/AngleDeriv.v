(* derivation of trigonometric functions *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import Main.Misc.

Require Import Trigo.RealLike.
Require Import Trigo.Angle.
Require Import Trigo.AngleDiv2.
Require Import Trigo.TrigoWithoutPiExt.
Require Import Trigo.Angle_order.
Require Import Trigo.AngleDiv2Add.
Require Import Trigo.AngleDivNat.
Require Import Trigo.SeqAngleIsCauchy.
Require Import Trigo.AngleTypeIsComplete.
Require Import Trigo.TacChangeAngle.

Notation "a '°' b" := (comp a b) (at level 40, left associativity).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

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

Theorem rngl_sin_sub_sin :
  ∀ p q,
  let c₁ := if angle_add_overflow p q then angle_straight else 0%A in
  let c₂ := if (p <? q)%A then angle_straight else 0%A in
  (rngl_sin p - rngl_sin q =
     2 * rngl_cos ((p + q) /₂ + c₁) * rngl_sin ((p - q) /₂ + c₂))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros.
rewrite (angle_add_div_2_add_sub_div_2 p q) at 1.
rewrite (angle_add_div_2_sub_sub_div_2 p q) at 5.
destruct (Bool.bool_dec _ _) as [Hpq| Hpq]. {
  do 2 rewrite rngl_sin_add_straight_r.
  rewrite rngl_sin_add, rngl_sin_sub.
  remember ((p + q) /₂)%A as a.
  remember ((p - q) /₂)%A as b.
  move b before a.
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_opp_add_distr Hop).
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_add Hop).
  rewrite <- (rngl_add_opp_l Hop).
  rewrite <- (rngl_mul_2_l Hon).
  rewrite <- rngl_mul_assoc.
  progress f_equal.
  subst c₁ c₂.
  rewrite Hpq.
  remember (q ≤? p)%A as qp eqn:Hqp.
  symmetry in Hqp.
  destruct qp. {
    apply angle_nlt_ge in Hqp.
    apply Bool.not_true_iff_false in Hqp.
    rewrite Hqp.
    rewrite rngl_cos_add_straight_r.
    rewrite angle_add_0_r.
    rewrite <- (rngl_mul_opp_l Hop).
    easy.
  } {
    apply Bool.not_true_iff_false in Hqp.
    apply angle_nle_gt in Hqp.
    rewrite Hqp.
    rewrite rngl_sin_add_straight_r.
    rewrite angle_add_0_r.
    rewrite <- (rngl_mul_opp_r Hop).
    easy.
  }
} {
  do 2 rewrite angle_add_0_r.
  rewrite rngl_sin_add, rngl_sin_sub.
  remember ((p + q) /₂)%A as a.
  remember ((p - q) /₂)%A as b.
  move b before a.
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_add_sub_swap Hop (_ * _)).
  rewrite (rngl_sub_diag Hos).
  rewrite rngl_add_0_l.
  rewrite <- (rngl_mul_2_l Hon).
  rewrite <- rngl_mul_assoc.
  progress f_equal.
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
    rewrite rngl_cos_add_straight_r.
    rewrite rngl_sin_add_straight_r.
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

Theorem angle_lt_angle_le_straight_angle_sub_le :
  ∀ θ1 θ2,
  (θ1 < θ2 ≤ angle_straight)%A
  → (θ2 - θ1 ≤ θ2)%A.
Proof.
destruct_ac.
intros * (Hθ, Hts).
progress unfold angle_ltb in Hθ.
progress unfold angle_leb.
generalize Hts; intros Hzst.
apply rngl_sin_nonneg_angle_le_straight in Hzst.
apply rngl_leb_le in Hzst.
rewrite Hzst in Hθ |-*.
apply rngl_leb_le in Hzst.
remember (0 ≤? rngl_sin θ1)%L as tst eqn:Htst.
symmetry in Htst.
destruct tst; [ | easy ].
apply rngl_leb_le in Htst.
apply rngl_ltb_lt in Hθ.
remember (0 ≤? rngl_sin (θ2 - θ1))%L as zstt eqn:Hzstt.
symmetry in Hzstt.
destruct zstt. {
  apply rngl_leb_le.
  rewrite rngl_cos_sub_comm.
  apply (rngl_lt_le_incl Hor) in Hθ.
  now apply rngl_cos_le_cos_sub.
}
apply (rngl_leb_gt Hor) in Hzstt.
apply rngl_nle_gt in Hzstt.
exfalso; apply Hzstt; clear Hzstt.
apply (rngl_lt_le_incl Hor) in Hθ.
now apply rngl_sin_sub_nonneg.
Qed.

Theorem angle_straight_le_lt_sub_le_straight :
  ∀ θ₀ θ,
  (angle_straight ≤ θ₀ < θ)%A
  → (θ - θ₀ ≤ angle_straight)%A.
Proof.
destruct_ac.
intros * (Hts, Hθ).
progress unfold angle_leb in Hts.
progress unfold angle_ltb in Hθ.
progress unfold angle_leb.
cbn in Hts.
cbn - [ angle_sub ].
rewrite (rngl_leb_refl Hor) in Hts |-*.
remember (0 ≤? rngl_sin (θ - θ₀))%L as zstt eqn:Hzstt.
symmetry in Hzstt.
destruct zstt; [ apply rngl_leb_le, rngl_cos_bound | exfalso ].
apply (rngl_leb_gt Hor) in Hzstt.
rewrite (rngl_sin_sub_anticomm) in Hzstt.
apply (rngl_opp_neg_pos Hop Hor) in Hzstt.
remember (0 ≤? rngl_sin θ₀)%L as zstz eqn:Hzstz.
remember (0 ≤? rngl_sin θ)%L as zst eqn:Hzst.
symmetry in Hzstz, Hzst.
destruct zstz. {
  apply rngl_leb_le in Hzstz, Hts.
  apply rngl_nlt_ge in Hts.
  apply Hts; clear Hts.
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_opp_1 in H; subst θ₀.
  clear Hzstz.
  rewrite rngl_sin_sub_straight_l in Hzstt.
  generalize Hzstt; intros H.
  apply (rngl_lt_le_incl Hor) in Hzstt.
  apply rngl_leb_le in Hzstt.
  rewrite Hzstt in Hzst; subst zst.
  apply rngl_ltb_lt in Hθ.
  apply rngl_nle_gt in Hθ.
  apply Hθ, rngl_cos_bound.
}
clear Hts.
destruct zst; [ easy | ].
apply (rngl_leb_gt Hor) in Hzstz, Hzst.
apply rngl_ltb_lt in Hθ.
apply rngl_nle_gt in Hθ.
apply Hθ; clear Hθ.
change_angle_add_r θ₀ angle_straight.
change_angle_add_r θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzstz.
progress sin_cos_add_sub_straight_hyp T Hzst.
progress sin_cos_add_sub_straight_hyp T Hzstt.
progress sin_cos_add_sub_straight_goal T.
rewrite rngl_add_0_r in Hzstt.
apply rngl_sin_sub_nonneg_iff; [ easy | | ].
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

(* *)

Definition angle_lt_for_deriv θ1 θ2 :=
  (θ1 < θ2)%A ∧ (θ2 - θ1 ≤ angle_straight)%A.

Definition angle_lt θ1 θ2 :=
  (θ1 < θ2)%A.

Definition angle_le θ1 θ2 :=
  (θ1 ≤ θ2)%A.

(* special cases where the contraint "θ2 - θ1 ≤ angle_straight" is not
   compulsory ; not used in the final proof but interesting to know *)

Theorem angle_le_straight_is_limit_if :
  ∀ (is_left : bool) f θ₀ θ₀',
  (if is_left then θ₀ ≤ angle_straight else angle_straight ≤ θ₀)%A
  → is_limit_when_tending_to_neighbourhood is_left angle_lt_for_deriv
      angle_eucl_distance rngl_distance f θ₀ θ₀'
  → is_limit_when_tending_to_neighbourhood is_left angle_lt
      angle_eucl_distance rngl_distance f θ₀ θ₀'.
Proof.
destruct_ac.
intros * Hts Hd.
intros ε Hε.
specialize (Hd ε Hε).
destruct Hd as (η & Hη & Hd).
exists η.
split; [ easy | ].
intros θ Hθ Hθη.
destruct is_left. {
  apply Hd; try easy.
  destruct (angle_le_dec (θ₀ - θ) angle_straight) as [Htts| Htts]; [ easy | ].
  exfalso.
  apply Htts; clear Htts.
  progress unfold angle_lt in Hθ.
  eapply angle_le_trans; [ | apply Hts ].
  now apply angle_lt_angle_le_straight_angle_sub_le.
} {
  apply Hd; try easy.
  destruct (angle_le_dec (θ - θ₀) angle_straight) as [Htts| Htts]; [ easy | ].
  exfalso.
  apply Htts; clear Htts.
  now apply angle_straight_le_lt_sub_le_straight.
}
Qed.

Theorem angle_le_straight_left_derivative_if :
  ∀ f θ₀ θ₀',
  (θ₀ ≤ angle_straight)%A
  → left_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
       f θ₀ θ₀'
  → left_derivative_at angle_lt angle_eucl_distance rngl_distance f θ₀ θ₀'.
Proof.
intros * Hts Hd.
now apply angle_le_straight_is_limit_if.
Qed.

Theorem angle_le_straight_right_derivative_if :
  ∀ f θ₀ θ₀',
  (angle_straight ≤ θ₀)%A
  → right_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
      f θ₀ θ₀'
  → right_derivative_at angle_lt angle_eucl_distance rngl_distance f θ₀ θ₀'.
Proof.
intros * Hts Hd.
now apply angle_le_straight_is_limit_if.
Qed.

(* *)

Theorem angle_sub_div_2_diag :
  ∀ θ, (θ - θ /₂ = θ /₂)%A.
Proof.
intros.
apply angle_add_move_r.
rewrite angle_sub_opp_r.
symmetry.
apply angle_add_div_2_diag.
Qed.

Theorem rngl_sin_angle_eucl_dist_0_r :
  ∀ θ,
  rngl_sin θ = (rngl_cos (θ /₂) * angle_eucl_dist θ 0)%L.
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
intros.
cbn.
rewrite angle_eucl_dist_is_sqrt.
rewrite angle_sub_0_l.
cbn.
rewrite <- rngl_mul_assoc.
rewrite <- rl_sqrt_mul; cycle 1. {
  apply rngl_1_add_cos_div_2_nonneg.
} {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
rewrite (rngl_squ_sub_squ' Hop).
rewrite (rngl_mul_1_r Hon), (rngl_mul_1_l Hon).
rewrite (rngl_add_sub Hos).
rewrite (rngl_squ_1 Hon).
specialize (cos2_sin2_1 θ) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite <- H1; clear H1.
symmetry.
rewrite (rl_sqrt_squ Hon Hop Hor).
remember (0 ≤? rngl_sin θ)%L as ss eqn:Hss.
symmetry in Hss.
destruct ss. {
  apply rngl_leb_le in Hss.
  rewrite (rngl_mul_1_l Hon).
  now apply (rngl_abs_nonneg_eq Hop Hor).
} {
  apply (rngl_leb_gt Hor) in Hss.
  apply (rngl_lt_le_incl Hor) in Hss.
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
  rewrite (rngl_mul_opp_l Hop), (rngl_mul_opp_r Hop).
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_opp_involutive Hop).
}
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

Theorem rngl_sin_angle_eucl_dist_straight_r' :
  ∀ θ,
  (angle_straight ≤ θ)%A
  → rngl_sin θ = (- rngl_sin (θ /₂) * angle_eucl_dist θ angle_straight)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%L).
  apply H1.
}
intros * Hst.
change_angle_opp θ.
destruct (angle_eq_dec θ 0) as [Htz| Htz]. {
  subst θ.
  rewrite angle_opp_0.
  rewrite angle_0_div_2; cbn.
  rewrite (rngl_opp_0 Hop); symmetry.
  apply (rngl_mul_0_l Hos).
}
rewrite rngl_sin_opp.
rewrite <- angle_eucl_dist_opp_opp.
apply angle_opp_le_compat_if in Hst. 2: {
  specialize (angle_straight_pos Hc1) as H1.
  intros H; rewrite H in H1.
  now apply angle_lt_irrefl in H1.
}
rewrite angle_opp_involutive in Hst |-*.
rewrite angle_opp_straight in Hst |-*.
apply rngl_sin_angle_eucl_dist_straight_r in Hst.
specialize (angle_opp_div_2 θ) as H1.
symmetry in H1.
apply angle_add_move_r in H1.
rewrite H1.
remember (θ =? 0)%A as tz eqn:Htz'.
symmetry in Htz'.
destruct tz; [ now apply angle_eqb_eq in Htz' | ].
clear Htz'.
rewrite rngl_sin_sub_straight_r.
rewrite rngl_sin_opp.
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_mul_opp_l Hop).
progress f_equal.
easy.
Qed.

Theorem rngl_squ_div_2_add_1_sub_squ_mul_2_le_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a < 1)%L → (a² / 2 + (1 - a)² * 2 ≤ 2)%L.
Proof.
intros Hic Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ + _)%L), (H1 2%L).
  now apply (rngl_le_refl Hor).
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
specialize (rngl_0_le_2 Hon Hos Hor) as Hz2'.
intros * Ha1.
rewrite rngl_add_comm.
apply (rngl_le_add_le_sub_l Hop Hor).
apply (rngl_le_div_l Hon Hop Hiv Hor); [ easy | ].
rewrite (rngl_mul_sub_distr_r Hop).
rewrite <- rngl_mul_assoc.
rewrite <- (rngl_4_eq_2_mul_2 Hon).
apply (rngl_le_add_le_sub_l Hop Hor).
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_1_l Hon).
rewrite <- (rngl_sub_sub_distr Hop).
apply (rngl_le_add_le_sub_r Hop Hor).
apply (rngl_sub_le_mono_l Hop Hor).
apply (rngl_le_add_le_sub_l Hop Hor).
rewrite (rngl_add_mul_l_diag_l Hon).
rewrite (rngl_mul_comm Hic 2).
rewrite <- rngl_mul_assoc.
apply (rngl_mul_le_compat_nonneg Hor). {
  split; [ apply (rngl_squ_nonneg Hos Hor) | ].
  rewrite <- (rngl_mul_1_l Hon a) at 2.
  progress unfold rngl_squ.
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
specialize (rngl_0_le_1 Hon Hos Hor) as H01.
split. {
  apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
  apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
  apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
  now apply (rngl_add_nonneg_nonneg Hor).
}
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_1_l Hon).
apply (rngl_add_le_mono_l Hop Hor).
apply (rngl_le_add_l Hor).
now apply (rngl_add_nonneg_nonneg Hor).
Qed.

Theorem rngl_1_sub_cos_div_2_le_angle_eucl_dist_0_r :
  ∀ θ,
  (θ ≤ angle_straight)%A
  → (1 - rngl_cos (θ /₂) ≤ angle_eucl_dist θ 0)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ - _)%L), (H1 (angle_eucl_dist _ _)).
  now apply (rngl_le_refl Hor).
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
specialize (rngl_0_le_2 Hon Hos Hor) as Hz2'.
intros * Htt.
cbn.
apply rngl_sin_nonneg_angle_le_straight in Htt.
apply rngl_leb_le in Htt.
rewrite Htt.
rewrite (rngl_mul_1_l Hon).
destruct (rngl_le_dec Hor 1 (angle_eucl_dist θ 0)) as [H1d| H1d]. {
  eapply (rngl_le_trans Hor); [ | apply H1d ].
  apply (rngl_le_sub_nonneg Hop Hor).
  apply rl_sqrt_nonneg.
  apply rngl_1_add_cos_div_2_nonneg.
}
apply (rngl_nle_gt_iff Hor) in H1d.
apply (rngl_le_sub_le_add_r Hop Hor).
rewrite rngl_add_comm.
apply (rngl_le_sub_le_add_r Hop Hor).
rewrite <- (rngl_abs_nonneg_eq Hop Hor (_ - _)). 2: {
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_lt_le_incl Hor) in H1d.
}
rewrite <- (rl_sqrt_squ Hon Hop Hor).
apply (rl_sqrt_le_rl_sqrt Hon Hop Hor Hii). {
  apply (rngl_squ_nonneg Hos Hor).
}
apply (rngl_le_div_r Hon Hop Hiv Hor _²); [ easy | ].
rewrite rngl_cos_angle_eucl_dist_0_r.
rewrite (rngl_add_sub_assoc Hop).
remember (angle_eucl_dist θ 0) as a.
apply (rngl_le_add_le_sub_l Hop Hor).
apply (rngl_squ_div_2_add_1_sub_squ_mul_2_le_2 Hic Hon Hop Hiv Hor).
split; [ | easy ].
subst a.
apply angle_eucl_dist_nonneg.
Qed.

Theorem rngl_1_sub_sin_div_2_le_angle_eucl_dist_straight_r :
  ∀ θ, (1 - rngl_sin (θ /₂) ≤ angle_eucl_dist θ angle_straight)%L.
Proof.
intros.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ - _)%L), (H1 (angle_eucl_dist _ _)).
  now apply (rngl_le_refl Hor).
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
intros.
cbn.
destruct (rngl_le_dec Hor 1 (angle_eucl_dist θ angle_straight))
  as [H1s| H1s]. {
  eapply (rngl_le_trans Hor); [ | apply H1s ].
  apply (rngl_le_sub_nonneg Hop Hor).
  apply rl_sqrt_nonneg.
  apply rngl_1_sub_cos_div_2_nonneg.
}
apply (rngl_nle_gt_iff Hor) in H1s.
apply (rngl_le_sub_le_add_r Hop Hor).
rewrite rngl_add_comm.
apply (rngl_le_sub_le_add_r Hop Hor).
rewrite <- (rngl_abs_nonneg_eq Hop Hor (_ - _)). 2: {
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_lt_le_incl Hor) in H1s.
}
rewrite <- (rl_sqrt_squ Hon Hop Hor).
apply (rl_sqrt_le_rl_sqrt Hon Hop Hor Hii). {
  apply (rngl_squ_nonneg Hos Hor).
}
apply (rngl_le_div_r Hon Hop Hiv Hor _²); [ easy | ].
rewrite rngl_cos_angle_eucl_dist_straight_r.
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_add_sub_swap Hop).
remember (angle_eucl_dist θ angle_straight) as a.
apply (rngl_le_add_le_sub_l Hop Hor).
apply (rngl_squ_div_2_add_1_sub_squ_mul_2_le_2 Hic Hon Hop Hiv Hor).
split; [ | easy ].
subst a.
apply angle_eucl_dist_nonneg.
Qed.

(* *)

Theorem rngl_cos_is_continuous :
  is_continuous angle_le angle_eucl_distance rngl_distance rngl_cos.
Proof.
destruct_ac.
intros a.
assert (H :
  ∀ is_left le,
  is_limit_when_tending_to_neighbourhood is_left le
    angle_eucl_distance rngl_distance rngl_cos a (rngl_cos a)). {
  intros * ε Hε.
  exists ε.
  split; [ easy | ].
  intros x _ Hxa.
  cbn.
  progress unfold rngl_dist.
  eapply (rngl_le_lt_trans Hor); [ | apply Hxa ].
  apply -> (rngl_abs_le Hop Hor).
  split. {
    rewrite <- (rngl_opp_sub_distr Hop).
    apply -> (rngl_opp_le_compat Hop Hor).
    cbn.
    rewrite angle_eucl_dist_symmetry.
    apply rngl_cos_diff_le_eucl_dist.
  } {
    apply rngl_cos_diff_le_eucl_dist.
  }
}
split; apply H.
Qed.

Theorem rngl_sin_is_continuous :
  is_continuous angle_le angle_eucl_distance rngl_distance rngl_sin.
Proof.
destruct_ac.
intros a.
assert (H :
  ∀ is_left le,
  is_limit_when_tending_to_neighbourhood is_left le
    angle_eucl_distance rngl_distance rngl_sin a (rngl_sin a)). {
  intros * ε Hε.
  exists ε.
  split; [ easy | ].
  intros x _ Hxa.
  cbn.
  progress unfold rngl_dist.
  eapply (rngl_le_lt_trans Hor); [ | apply Hxa ].
  apply -> (rngl_abs_le Hop Hor).
  split. {
    rewrite <- (rngl_opp_sub_distr Hop).
    apply -> (rngl_opp_le_compat Hop Hor).
    cbn.
    rewrite angle_eucl_dist_symmetry.
    apply rngl_sin_diff_le_eucl_dist.
  } {
    apply rngl_sin_diff_le_eucl_dist.
  }
}
split; apply H.
Qed.

(* *)

Theorem rngl_sin_left_or_right_derivative_at_0 :
  ∀ is_left,
  left_or_right_derivative_at is_left (angle T) angle_lt_for_deriv
    angle_eucl_distance rngl_distance rngl_sin 0%A (rngl_cos 0).
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * ε Hε; rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
specialize (rngl_0_le_2 Hon Hos Hor) as H20.
intros * ε Hε; cbn.
exists ε.
split; [ easy | ].
intros θ Hlt Hθ.
rewrite (rngl_sub_0_l Hop).
rewrite rngl_sin_angle_eucl_dist_0_r.
progress unfold angle_lt_for_deriv in Hlt.
rewrite (rngl_mul_opp_r Hop).
rewrite <- (rngl_mul_opp_l Hop).
rewrite rngl_mul_assoc.
rewrite (rngl_mul_div Hi1). 2: {
  intros H.
  apply angle_eucl_dist_separation in H.
  rewrite H in Hlt.
  destruct is_left; destruct Hlt as (Hlt, Htt);
  now apply angle_lt_irrefl in Hlt.
}
progress unfold rngl_dist.
rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
  apply (rngl_le_sub_0 Hop Hor).
  destruct is_left. {
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_le_opp_l Hop Hor).
    rewrite rngl_add_comm.
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  }
  do 2 rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_opp_involutive Hop).
  rewrite (rngl_mul_1_l Hon).
  apply rngl_cos_bound.
}
destruct is_left. {
  exfalso.
  destruct Hlt as (Ht, Hlt).
  apply angle_nle_gt in Ht.
  apply Ht.
  apply angle_nonneg.
}
rewrite angle_sub_0_r in Hlt.
rewrite (rngl_opp_sub_distr Hop).
eapply (rngl_le_lt_trans Hor); [ | apply Hθ ].
do 2 rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
now apply rngl_1_sub_cos_div_2_le_angle_eucl_dist_0_r.
Qed.

Theorem rngl_sin_right_derivative_at_0 :
  right_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_sin 0%A (rngl_cos 0).
Proof.
apply rngl_sin_left_or_right_derivative_at_0.
Qed.

Theorem rngl_sin_right_derivative_at_straight :
  right_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_sin angle_straight (rngl_cos angle_straight).
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
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_opp_sub_distr Hop).
rewrite (rngl_sub_0_r Hos).
destruct Hlt as (Hlt, Htt).
rewrite rngl_sin_angle_eucl_dist_straight_r'. 2: {
  now apply angle_lt_le_incl in Hlt.
}
rewrite (rngl_mul_div Hi1). 2: {
  intros H.
  apply angle_eucl_dist_separation in H.
  rewrite H in Hlt.
  now apply angle_lt_irrefl in Hlt.
}
progress unfold rngl_dist.
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_l Hop).
rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_sin_bound.
}
eapply (rngl_le_lt_trans Hor); [ | apply Hθ ].
apply rngl_1_sub_sin_div_2_le_angle_eucl_dist_straight_r.
Qed.

Theorem rngl_sin_left_derivative_at_straight :
  left_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_sin angle_straight (rngl_cos angle_straight).
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
exists √ε.
split; [ now apply (rl_sqrt_pos Hon Hos Hor) | ].
intros θ Hlt Hθ.
rewrite (rngl_mul_1_l Hon).
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
rewrite angle_eucl_dist_sub_l_diag in Hθ.
rewrite angle_div_2_sub.
rewrite Hov.
rewrite angle_straight_div_2.
rewrite rngl_sin_sub_right_l.
generalize Hε.
intros Hε'.
apply (rngl_lt_le_incl Hor) in Hε'.
apply rngl_cos_lt_angle_eucl_dist_lt in Hθ. 2: {
  now apply rl_sqrt_nonneg.
}
rewrite (rngl_squ_sqrt Hon) in Hθ; [ | easy ].
rewrite angle_sub_0_l in Hθ.
cbn in Hθ.
apply (rngl_lt_sub_lt_add_l Hop Hor) in Hθ.
apply (rngl_lt_sub_lt_add_r Hop Hor).
eapply (rngl_lt_le_trans Hor); [ apply Hθ | ].
apply (rngl_add_le_compat Hor). {
  apply (rngl_le_div_l Hon Hop Hiv Hor); [ easy | ].
  rewrite (rngl_mul_2_r Hon).
  now apply (rngl_le_add_l Hor).
}
apply rngl_cos_le_cos_div_2.
eapply angle_le_trans; [ apply Hov | ].
apply angle_straight_le_4_angle_straight_div_3.
Qed.

Theorem rngl_cos_right_derivative_at_0 :
  right_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_cos 0%A ((rngl_opp ° rngl_sin) 0%A).
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
progress unfold "°".
cbn.
rewrite (rngl_opp_0 Hop).
exists ε.
split; [ easy | ].
intros θ Hlt Hθ.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_opp_sub_distr Hop).
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
  right_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_cos angle_straight ((rngl_opp ° rngl_sin) angle_straight).
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
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_opp_sub_distr Hop).
rewrite (rngl_sub_opp_r Hop).
progress unfold "°".
cbn.
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

Theorem rngl_cos_left_derivative_at_straight :
  left_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_cos angle_straight ((rngl_opp ° rngl_sin) angle_straight).
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
rewrite (rngl_mul_1_l Hon).
rewrite <- (rngl_opp_add_distr Hop).
progress unfold "°".
cbn.
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
  destruct Hlt as (Hlt, _).
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

(* *)

Theorem rngl_sin_right_derivative :
  ∀ θ₀,
  right_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_sin θ₀ (rngl_cos θ₀).
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
  apply rngl_sin_right_derivative_at_0.
}
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  subst θ₀.
  apply rngl_sin_right_derivative_at_straight.
}
intros ε Hε.
specialize (rngl_cos_is_continuous θ₀) as (Hcl, Hcr).
destruct (Hcl ε Hε) as (η & Hη & Hcc).
destruct (Hcr ε Hε) as (η' & Hη' & Hcc').
move η before ε.
move η' before η.
remember (angle_eucl_dist θ₀ 0) as x.
remember (angle_eucl_dist θ₀ angle_straight) as y.
exists (rngl_min3 x y (rngl_min η η')); subst x y.
split. {
  apply rngl_min_glb_lt; [ | now apply rngl_min_glb_lt ].
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
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_opp_sub_distr Hop).
move θ before θ₀.
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H4).
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H3).
apply (rngl_min_glb_lt_iff Hor) in H4.
destruct H4 as (H4, H5).
cbn.
progress unfold rngl_dist.
rewrite rngl_sin_sub_sin.
rewrite rngl_sin_add_div_2_if_angle_eucl_dist.
rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_mul_div Hi1); [ | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_div Hi1). 2: {
  intros H.
  apply angle_eucl_dist_separation in H.
  destruct Htt as (Htt, _).
  rewrite H in Htt.
  now apply angle_lt_irrefl in Htt.
}
destruct Htt as (Hlt, Htt).
generalize Hlt; intros H.
apply angle_lt_le_incl in H.
apply angle_nlt_ge in H.
apply Bool.not_true_iff_false in H.
rewrite H; clear H.
rewrite (rngl_mul_1_r Hon).
rewrite angle_div_2_add.
progress replace (rngl_abs _) with
  (rngl_abs (rngl_cos (θ /₂ + θ₀ /₂) - rngl_cos θ₀)). 2: {
  remember (angle_add_overflow θ θ₀) as ovt eqn:Hovt.
  symmetry in Hovt.
  destruct ovt. {
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    now rewrite angle_add_0_r.
  }
  now rewrite angle_add_0_r.
}
assert (H : (angle_eucl_dist (θ /₂ + θ₀ /₂) θ₀ ≤ angle_eucl_dist θ θ₀)%L). {
  clear - Hlt Htt.
  (* lemma to do: I found the same proof below;
     there is also a similar version with θ instead of θ₀
     in 2 versions; must think of it... *)
(*
  Hlt : (θ₀ < θ)%A
  Htt : (θ - θ₀ ≤ angle_straight)%A
  ============================
  (angle_eucl_dist (θ /₂ + θ₀ /₂) θ₀ ≤ angle_eucl_dist θ θ₀)%L
*)
  rewrite angle_eucl_dist_move_0_r.
  rewrite (angle_eucl_dist_move_0_r θ).
  rewrite angle_add_sub_swap.
  rewrite <- angle_sub_sub_distr.
  rewrite angle_sub_div_2_diag.
  rewrite angle_div_2_sub'.
  generalize Hlt; intros H.
  apply angle_lt_le_incl in H.
  rewrite H; clear H.
  apply angle_le_angle_eucl_dist_le; [ | easy | ]. {
    apply angle_div_2_le_straight.
  }
  apply angle_div_2_le.
}
destruct (angle_le_dec (θ /₂ + θ₀ /₂) θ₀) as [Httt| Httt]. {
  apply (Hcc _ Httt).
  eapply (rngl_le_lt_trans Hor); [ | apply H4 ].
  easy.
} {
  apply angle_nle_gt in Httt.
  apply angle_lt_le_incl in Httt.
  apply (Hcc' _ Httt).
  eapply (rngl_le_lt_trans Hor); [ | apply H5 ].
  easy.
}
Qed.

Theorem rngl_sin_left_derivative :
  ∀ θ₀,
  left_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_sin θ₀ (rngl_cos θ₀).
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
  destruct Hlt as (Hlt, _).
  apply angle_nle_gt in Hlt.
  exfalso; apply Hlt.
  apply angle_nonneg.
}
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  subst θ₀.
  apply rngl_sin_left_derivative_at_straight.
}
intros ε Hε.
specialize (rngl_cos_is_continuous θ₀) as (Hcl, Hcr).
destruct (Hcl ε Hε) as (η & Hη & Hcc).
destruct (Hcr ε Hε) as (η' & Hη' & Hcc').
move η before ε.
move η' before η.
remember (angle_eucl_dist θ₀ 0) as x.
remember (angle_eucl_dist θ₀ angle_straight) as y.
exists (rngl_min3 x y (rngl_min η η')); subst x y.
split. {
  apply rngl_min_glb_lt; [ | now apply rngl_min_glb_lt ].
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
rewrite (rngl_mul_1_l Hon).
move θ before θ₀.
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H4).
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H3).
apply (rngl_min_glb_lt_iff Hor) in H4.
destruct H4 as (H4, H5).
cbn.
progress unfold rngl_dist.
rewrite rngl_sin_sub_sin.
rewrite rngl_sin_add_div_2_if_angle_eucl_dist.
rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_mul_div Hi1); [ | easy ].
rewrite rngl_mul_assoc.
rewrite angle_eucl_dist_symmetry.
rewrite (rngl_mul_div Hi1). 2: {
  intros H.
  apply angle_eucl_dist_separation in H.
  destruct Htt as (Htt, _).
  rewrite H in Htt.
  now apply angle_lt_irrefl in Htt.
}
destruct Htt as (Hlt, Htt).
generalize Hlt; intros H.
apply angle_lt_le_incl in H.
apply angle_nlt_ge in H.
apply Bool.not_true_iff_false in H.
rewrite H; clear H.
rewrite (rngl_mul_1_r Hon).
rewrite angle_div_2_add.
progress replace (rngl_abs _) with
  (rngl_abs (rngl_cos (θ₀ /₂ + θ /₂) - rngl_cos θ₀)). 2: {
  remember (angle_add_overflow θ₀ θ) as ovt eqn:Hovt.
  symmetry in Hovt.
  destruct ovt. {
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    now rewrite angle_add_0_r.
  }
  now rewrite angle_add_0_r.
}
rewrite angle_add_comm.
assert (H : (angle_eucl_dist (θ /₂ + θ₀ /₂) θ₀ ≤ angle_eucl_dist θ θ₀)%L). {
  clear - Hlt Htt.
  rewrite angle_eucl_dist_move_0_r.
  rewrite (angle_eucl_dist_move_0_r θ).
  rewrite angle_add_sub_swap.
  rewrite <- angle_sub_sub_distr.
  rewrite angle_sub_div_2_diag.
  do 2 rewrite <- (angle_eucl_dist_opp_opp _ 0).
  do 2 rewrite angle_opp_sub_distr.
  rewrite angle_opp_0.
  rewrite angle_div_2_sub'.
  generalize Hlt; intros H.
  apply angle_lt_le_incl in H.
  rewrite H; clear H.
  apply angle_le_angle_eucl_dist_le; [ | easy | ]. {
    apply angle_div_2_le_straight.
  }
  apply angle_div_2_le.
}
destruct (angle_le_dec (θ /₂ + θ₀ /₂) θ₀) as [Httt| Httt]. {
  apply (Hcc _ Httt).
  eapply (rngl_le_lt_trans Hor); [ | apply H4 ].
  easy.
} {
  apply angle_nle_gt in Httt.
  apply angle_lt_le_incl in Httt.
  apply (Hcc' _ Httt).
  eapply (rngl_le_lt_trans Hor); [ | apply H5 ].
  easy.
}
Qed.

Theorem rngl_cos_right_derivative :
  ∀ θ₀,
  right_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_cos θ₀ ((rngl_opp ° rngl_sin) θ₀).
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
specialize (rngl_sin_is_continuous θ₀) as (Hsl, Hsr).
destruct (Hsl ε Hε) as (η & Hη & Hss).
destruct (Hsr ε Hε) as (η' & Hη' & Hss').
move η before ε.
move η' before η.
remember (angle_eucl_dist θ₀ 0) as x.
remember (angle_eucl_dist θ₀ angle_straight) as y.
exists (rngl_min3 x y (rngl_min η η')); subst x y.
split. {
  apply rngl_min_glb_lt; [ | now apply rngl_min_glb_lt ].
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
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_opp_sub_distr Hop).
move θ before θ₀.
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H4).
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H3).
apply (rngl_min_glb_lt_iff Hor) in H4.
destruct H4 as (H4, H5).
cbn.
progress unfold rngl_dist.
progress unfold "°".
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
  destruct Htt as (Htt, _).
  rewrite H in Htt.
  now apply angle_lt_irrefl in Htt.
}
destruct Htt as (Hlt, Htt).
generalize Hlt; intros H.
apply angle_lt_le_incl in H.
apply angle_nlt_ge in H.
apply Bool.not_true_iff_false in H.
rewrite H; clear H.
rewrite (rngl_mul_1_r Hon).
rewrite angle_div_2_add.
progress replace (rngl_abs _) with
  (rngl_abs (rngl_sin (θ /₂ + θ₀ /₂) - rngl_sin θ₀)). 2: {
  remember (angle_add_overflow θ θ₀) as ovt eqn:Hovt.
  symmetry in Hovt.
  destruct ovt. {
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    rewrite angle_add_0_r.
    rewrite <- (rngl_abs_opp Hop Hor).
    rewrite (rngl_opp_sub_distr Hop).
    now rewrite (rngl_add_opp_l Hop).
  }
  rewrite angle_add_0_r.
  rewrite <- (rngl_abs_opp Hop Hor).
  rewrite (rngl_opp_sub_distr Hop).
  now rewrite (rngl_add_opp_l Hop).
}
rewrite angle_add_comm.
assert (H : (angle_eucl_dist (θ /₂ + θ₀ /₂) θ₀ ≤ angle_eucl_dist θ θ₀)%L). {
clear - Hlt Htt.
(*
  Hlt : (θ₀ < θ)%A
  Htt : (θ - θ₀ ≤ angle_straight)%A
  ============================
  (angle_eucl_dist (θ /₂ + θ₀ /₂) θ₀ ≤ angle_eucl_dist θ θ₀)%L
*)
  rewrite angle_eucl_dist_move_0_r.
  rewrite (angle_eucl_dist_move_0_r θ).
  rewrite angle_add_sub_swap.
  rewrite <- angle_sub_sub_distr.
  rewrite angle_sub_div_2_diag.
  rewrite angle_div_2_sub'.
  generalize Hlt; intros H.
  apply angle_lt_le_incl in H.
  rewrite H; clear H.
  apply angle_le_angle_eucl_dist_le; [ | easy | ]. {
    apply angle_div_2_le_straight.
  }
  apply angle_div_2_le.
}
rewrite angle_add_comm.
destruct (angle_le_dec (θ /₂ + θ₀ /₂) θ₀) as [Httt| Httt]. {
  apply (Hss _ Httt).
  eapply (rngl_le_lt_trans Hor); [ | apply H4 ].
  easy.
} {
  apply angle_nle_gt in Httt.
  apply angle_lt_le_incl in Httt.
  apply (Hss' _ Httt).
  eapply (rngl_le_lt_trans Hor); [ | apply H5 ].
  easy.
}
Qed.

Theorem rngl_cos_left_derivative :
  ∀ θ₀,
  left_derivative_at angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_cos θ₀ ((rngl_opp ° rngl_sin) θ₀).
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
  destruct Hlt as (Hlt, _).
  apply angle_nle_gt in Hlt.
  exfalso; apply Hlt.
  apply angle_nonneg.
}
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  subst θ₀.
  apply rngl_cos_left_derivative_at_straight.
}
intros ε Hε.
specialize (rngl_sin_is_continuous θ₀) as (Hsl, Hsr).
destruct (Hsl ε Hε) as (η & Hη & Hss).
destruct (Hsr ε Hε) as (η' & Hη' & Hss').
move η before ε.
move η' before η.
cbn in Hss, Hss'.
progress unfold rngl_dist in Hss.
progress unfold rngl_dist in Hss'.
remember (angle_eucl_dist θ₀ angle_straight) as x.
remember (angle_eucl_dist θ₀ 0) as y.
exists (rngl_min3 x y (rngl_min η η')); subst x y.
split. {
  apply rngl_min_glb_lt; [ | now apply rngl_min_glb_lt ].
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
rewrite (rngl_mul_1_l Hon).
move θ before θ₀.
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H4).
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H3).
apply (rngl_min_glb_lt_iff Hor) in H4.
destruct H4 as (H4, H5).
cbn.
progress unfold rngl_dist.
progress unfold "°".
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
  destruct Htt as (Htt, _).
  rewrite H in Htt.
  now apply angle_lt_irrefl in Htt.
}
rewrite <- (rngl_abs_opp Hop Hor).
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_l Hop).
destruct Htt as (Hlt, Htt).
generalize Hlt; intros H.
apply angle_lt_le_incl in H.
apply angle_nlt_ge in H.
apply Bool.not_true_iff_false in H.
rewrite H; clear H.
rewrite (rngl_mul_1_r Hon).
rewrite angle_div_2_add.
progress replace (rngl_abs _) with
  (rngl_abs (rngl_sin (θ₀ /₂ + θ /₂) - rngl_sin θ₀)). 2: {
  remember (angle_add_overflow θ₀ θ) as ovt eqn:Hovt.
  symmetry in Hovt.
  destruct ovt. {
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    now rewrite angle_add_0_r.
  }
  now rewrite angle_add_0_r.
}
rewrite angle_add_comm.
assert (H : (angle_eucl_dist (θ /₂ + θ₀ /₂) θ₀ ≤ angle_eucl_dist θ θ₀)%L). {
  clear - Hlt Htt.
  rewrite angle_eucl_dist_move_0_r.
  rewrite (angle_eucl_dist_move_0_r θ).
  rewrite angle_add_sub_swap.
  rewrite <- angle_sub_sub_distr.
  rewrite angle_sub_div_2_diag.
  do 2 rewrite <- (angle_eucl_dist_opp_opp _ 0).
  do 2 rewrite angle_opp_sub_distr.
  rewrite angle_opp_0.
  rewrite angle_div_2_sub'.
  generalize Hlt; intros H.
  apply angle_lt_le_incl in H.
  rewrite H; clear H.
  apply angle_le_angle_eucl_dist_le; [ | easy | ]. {
    apply angle_div_2_le_straight.
  }
  apply angle_div_2_le.
}
destruct (angle_le_dec (θ /₂ + θ₀ /₂) θ₀) as [Httt| Httt]. {
  apply (Hss _ Httt).
  eapply (rngl_le_lt_trans Hor); [ | apply H4 ].
  easy.
} {
  apply angle_nle_gt in Httt.
  apply angle_lt_le_incl in Httt.
  apply (Hss' _ Httt).
  eapply (rngl_le_lt_trans Hor); [ | apply H5 ].
  easy.
}
Qed.

(* *)

Theorem rngl_cos_derivative :
  is_derivative angle_le angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_cos (rngl_opp ° rngl_sin)%L.
Proof.
intros θ₀.
split.
apply rngl_cos_is_continuous.
split.
apply rngl_cos_is_continuous.
split.
apply rngl_cos_left_derivative.
apply rngl_cos_right_derivative.
Qed.

Theorem rngl_sin_derivative :
  is_derivative angle_le angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_sin rngl_cos.
Proof.
intros θ₀.
split.
apply rngl_sin_is_continuous.
split.
apply rngl_sin_is_continuous.
split.
apply rngl_sin_left_derivative.
apply rngl_sin_right_derivative.
Qed.

End a.
