(* derivation of trigonometric functions *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.Misc.
Require Import Main.RingLike.
Require Import Main.IterAdd.

Require Import Trigo.RealLike.
Require Import Trigo.Angle.
Require Import Trigo.AngleDiv2.
Require Import Trigo.AngleDiv2Add.
Require Import Trigo.TrigoWithoutPiExt.
Require Import Trigo.Angle_order.
Require Import Trigo.TacChangeAngle.
Require Import Trigo.AngleAddOverflowLe.
Require Import Trigo.AngleDivNat.
Require Import Trigo.SeqAngleIsCauchy.
Require Import Trigo.AngleTypeIsComplete.
Require Import Trigo.AngleAddLeMonoL.
Require Import AngleEuclDist_sin.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_cos_straight : rngl_cos angle_straight = (-1)%L.
Proof. easy. Qed.

Theorem rngl_sin_straight : rngl_sin angle_straight = 0%L.
Proof. easy. Qed.

Theorem angle_add_overflow_opp_r_eq :
  ∀ p q, angle_add_overflow p (- q) = ((q ≠? 0)%A && (q ≤? p)%A)%bool.
Proof.
destruct_ac.
intros.
rewrite angle_add_overflow_comm.
progress unfold angle_add_overflow.
rewrite angle_opp_involutive.
f_equal.
(* lemma *)
f_equal.
progress unfold angle_eqb.
cbn.
f_equal.
remember (rngl_sin q =? 0)%L as qz eqn:Hqz.
symmetry in Hqz.
destruct qz. {
  apply (rngl_eqb_eq Hed) in Hqz.
  rewrite Hqz.
  rewrite (rngl_opp_0 Hop).
  apply (rngl_eqb_refl Hed).
}
apply (rngl_eqb_neq Hed) in Hqz.
apply (rngl_eqb_neq Hed).
intros H; apply Hqz; clear Hqz.
apply (f_equal rngl_opp) in H.
now rewrite (rngl_opp_involutive Hop), (rngl_opp_0 Hop) in H.
Qed.

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

(* to be moved to the right place *)
Theorem rngl_leb_antisymm :
  rngl_is_ordered T = true →
  ∀ a b, (b ≤? a)%L = negb (a <? b)%L.
Proof.
intros Hor *.
progress unfold rngl_leb.
progress unfold rngl_ltb.
progress unfold rngl_is_ordered in Hor.
destruct rngl_opt_leb; [ | easy ].
symmetry; apply Bool.negb_involutive.
Qed.

(* to be moved to the right place *)
Theorem rngl_ltb_antisymm :
  rngl_is_ordered T = true →
  ∀ a b, (b <? a)%L = negb (a ≤? b)%L.
Proof.
intros Hor *.
progress unfold rngl_leb.
progress unfold rngl_ltb.
progress unfold rngl_is_ordered in Hor.
now destruct rngl_opt_leb.
Qed.

(* to be moved to the right place *)
Theorem angle_leb_antisymm :
  ∀ θ1 θ2, (θ2 ≤? θ1)%A = negb (θ1 <? θ2)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_ltb.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  destruct zs2; [ | easy ].
  now apply rngl_leb_antisymm.
} {
  destruct zs2; [ easy | ].
  now apply rngl_leb_antisymm.
}
Qed.

(* to be moved to the right place *)
Theorem angle_ltb_antisymm :
  ∀ θ1 θ2, (θ2 <? θ1)%A = negb (θ1 ≤? θ2)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_ltb.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  destruct zs2; [ | easy ].
  now apply rngl_ltb_antisymm.
} {
  destruct zs2; [ easy | ].
  now apply rngl_ltb_antisymm.
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

(* I'm not happy of the statement of this theorem which is not really
   symmetric. *)

Theorem rngl_cos_add_cos :
  ∀ p q,
  let c₁ := if angle_add_overflow p q then angle_straight else 0%A in
  let c₂ := if (p <? q)%A then angle_straight else 0%A in
  (rngl_cos p + rngl_cos q =
     2 * rngl_cos ((p + q) /₂ + c₁) * rngl_cos ((p - q) /₂ + c₂))%L.
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
  do 2 rewrite rngl_cos_add_straight_r.
  rewrite rngl_cos_add, rngl_cos_sub.
  remember ((p + q) /₂)%A as a.
  remember ((p - q) /₂)%A as b.
  move b before a.
  rewrite (rngl_add_opp_r Hop).
  rewrite (rngl_opp_sub_distr Hop).
  rewrite (rngl_sub_add_distr Hos).
  rewrite (rngl_sub_sub_swap Hop).
  rewrite (rngl_sub_sub_swap Hop (rngl_sin _ * _)).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_sub_0_l Hop).
  rewrite <- (rngl_opp_add_distr Hop).
  rewrite <- (rngl_mul_2_l Hon).
  rewrite <- (rngl_mul_opp_r Hop).
  rewrite <- rngl_mul_assoc.
  f_equal.
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
    symmetry.
    apply (rngl_mul_opp_l Hop).
  } {
    apply Bool.not_true_iff_false in Hqp.
    apply angle_nle_gt in Hqp.
    rewrite Hqp.
    rewrite rngl_cos_add_straight_r.
    rewrite angle_add_0_r.
    symmetry.
    apply (rngl_mul_opp_r Hop).
  }
} {
  do 2 rewrite angle_add_0_r.
  rewrite rngl_cos_add, rngl_cos_sub.
  remember ((p + q) /₂)%A as a.
  remember ((p - q) /₂)%A as b.
  move b before a.
  rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap.
  rewrite (rngl_sub_add Hop).
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
    do 2 rewrite rngl_cos_add_straight_r.
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_opp_r Hop).
    symmetry.
    apply (rngl_opp_involutive Hop).
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
  rewrite <- (rngl_opp_add_distr Hop).
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
    rewrite rngl_cos_add_straight_r.
    rewrite angle_add_0_r.
    now rewrite <- (rngl_mul_opp_l Hop).
  } {
    apply Bool.not_true_iff_false in Hqp.
    apply angle_nle_gt in Hqp.
    rewrite Hqp.
    rewrite rngl_sin_add_straight_r.
    rewrite angle_add_0_r.
    now rewrite (rngl_mul_opp_r Hop).
  }
} {
  do 2 rewrite angle_add_0_r.
  rewrite rngl_sin_add, rngl_sin_sub.
  remember ((p + q) /₂)%A as a.
  remember ((p - q) /₂)%A as b.
  move b before a.
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite (rngl_sub_diag Hos).
  rewrite rngl_add_0_l.
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
    rewrite rngl_cos_add_straight_r, rngl_sin_add_straight_r.
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_opp_r Hop).
    symmetry.
    apply (rngl_opp_involutive Hop).
  }
}
Qed.

Theorem fold_angle_add_overflow2 :
  ∀ θ1 θ2, (θ1 + θ2 <? θ1)%A = angle_add_overflow2 θ1 θ2.
Proof. easy. Qed.

Theorem rl_sqrt_inv :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → (1 / √a = √a / a)%L.
Proof.
intros Hon Hic Hos Hiv Hor * Hza.
apply (rngl_div_div_mul_mul Hon Hic Hiv). {
  intros H.
  apply (eq_rl_sqrt_0 Hon Hos) in H.
  now subst a; apply (rngl_lt_irrefl Hor) in Hza.
  now apply (rngl_lt_le_incl Hor) in Hza.
} {
  intros H.
  now subst a; apply (rngl_lt_irrefl Hor) in Hza.
}
rewrite (rngl_mul_1_l Hon).
symmetry.
rewrite fold_rngl_squ.
apply (rngl_squ_sqrt Hon).
now apply (rngl_lt_le_incl Hor) in Hza.
Qed.

Theorem angle_add_overflow_angle_lt_cos_sub_cos :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = true
  → (θ1 < θ2)%A
  → (rngl_cos θ1 - rngl_cos θ2 =
     - rngl_sin ((θ1 + θ2) /₂) * angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hov Htt.
  rewrite (H1 (_ * _)%L).
  apply H1.
}
intros * Hov Htt.
assert (Hz2 : (0 < 2)%L) by apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
assert (Hze2 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hos Hor).
assert (H2nz : 2%L ≠ 0%L) by apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
rewrite angle_eucl_dist_is_sqrt.
remember (1 - rngl_cos (θ2 - θ1))%L as a.
assert (Hz1c : (0 ≤ a)%L). {
  subst a.
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite rngl_cos_sub_cos.
(**)
rewrite Hov, Htt.
do 2 rewrite rngl_sin_add_straight_r.
do 2 rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_mul_opp_l Hop).
f_equal.
rewrite (rngl_mul_comm Hic 2).
rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_mul_comm Hic).
progress unfold angle_div_2.
cbn - [ angle_div_2 angle_sub ].
rewrite rngl_cos_sub_comm.
rewrite <- Heqa.
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite rl_sqrt_mul; [ | easy | easy ].
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- (rngl_div_1_l Hon Hiv).
rewrite (rl_sqrt_inv Hon Hic Hos Hiv Hor); [ | easy ].
now apply (rngl_div_mul Hon Hiv).
Qed.

Theorem angle_add_overflow_angle_ge_cos_sub_cos :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = true
  → (θ2 ≤ θ1)%A
  → (rngl_cos θ1 - rngl_cos θ2 =
       rngl_sin ((θ1 + θ2) /₂) * angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hov Htt.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros * Hov Htt.
assert (Hz2 : (0 < 2)%L) by apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
assert (Hze2 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hos Hor).
assert (H2nz : 2%L ≠ 0%L) by apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
rewrite angle_eucl_dist_is_sqrt.
remember (1 - rngl_cos (θ2 - θ1))%L as a.
assert (Hz1c : (0 ≤ a)%L). {
  subst a.
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite rngl_cos_sub_cos.
(**)
apply angle_ltb_ge in Htt.
rewrite Hov, Htt.
rewrite rngl_sin_add_straight_r.
rewrite angle_add_0_r.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_mul_comm Hic 2).
rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_mul_comm Hic).
progress unfold angle_div_2.
cbn - [ angle_div_2 angle_sub ].
rewrite rngl_cos_sub_comm.
rewrite <- Heqa.
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite rl_sqrt_mul; [ | easy | easy ].
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- (rngl_div_1_l Hon Hiv).
rewrite (rl_sqrt_inv Hon Hic Hos Hiv Hor); [ | easy ].
now apply (rngl_div_mul Hon Hiv).
Qed.

Theorem angle_add_not_overflow_angle_lt_cos_sub_cos :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (θ1 < θ2)%A
  → (rngl_cos θ1 - rngl_cos θ2 =
       rngl_sin ((θ1 + θ2) /₂) * angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hov Htt.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros * Hov Htt.
assert (Hz2 : (0 < 2)%L) by apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
assert (Hze2 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hos Hor).
assert (H2nz : 2%L ≠ 0%L) by apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
rewrite angle_eucl_dist_is_sqrt.
remember (1 - rngl_cos (θ2 - θ1))%L as a.
assert (Hz1c : (0 ≤ a)%L). {
  subst a.
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite rngl_cos_sub_cos.
(**)
rewrite Hov, Htt.
rewrite rngl_sin_add_straight_r.
rewrite angle_add_0_r.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_mul_comm Hic 2).
rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_mul_comm Hic).
progress unfold angle_div_2.
cbn - [ angle_div_2 angle_sub ].
rewrite rngl_cos_sub_comm.
rewrite <- Heqa.
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite rl_sqrt_mul; [ | easy | easy ].
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- (rngl_div_1_l Hon Hiv).
rewrite (rl_sqrt_inv Hon Hic Hos Hiv Hor); [ | easy ].
now apply (rngl_div_mul Hon Hiv).
Qed.

Theorem angle_add_not_overflow_angle_ge_cos_sub_cos :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (θ2 ≤ θ1)%A
  → (rngl_cos θ1 - rngl_cos θ2 =
       - rngl_sin ((θ1 + θ2) /₂) * angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hov Htt.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros * Hov Htt.
assert (Hz2 : (0 < 2)%L) by apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
assert (Hze2 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hos Hor).
assert (H2nz : 2%L ≠ 0%L) by apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
rewrite angle_eucl_dist_is_sqrt.
remember (1 - rngl_cos (θ2 - θ1))%L as a.
assert (Hz1c : (0 ≤ a)%L). {
  subst a.
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite rngl_cos_sub_cos.
(**)
apply angle_ltb_ge in Htt.
rewrite Hov, Htt.
do 2 rewrite angle_add_0_r.
rewrite (rngl_mul_opp_l Hop).
f_equal.
rewrite (rngl_mul_comm Hic 2).
rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_mul_comm Hic).
progress unfold angle_div_2.
cbn - [ angle_div_2 angle_sub ].
rewrite rngl_cos_sub_comm.
rewrite <- Heqa.
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite rl_sqrt_mul; [ | easy | easy ].
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- (rngl_div_1_l Hon Hiv).
rewrite (rl_sqrt_inv Hon Hic Hos Hiv Hor); [ | easy ].
now apply (rngl_div_mul Hon Hiv).
Qed.

Theorem angle_cos_sub_cos_angle_eucl_dist_mul :
  ∀ θ1 θ2,
  (rngl_cos θ1 - rngl_cos θ2 =
     angle_eucl_dist θ1 θ2 *
     if Bool.eqb (angle_add_overflow θ1 θ2) (θ1 <? θ2)%A then
       - rngl_sin ((θ1 + θ2) /₂)
     else
       rngl_sin ((θ1 + θ2) /₂))%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros.
destruct (rngl_eq_dec Heo (angle_eucl_dist θ1 θ2) 0) as [H12| H12]. {
  rewrite H12.
  apply angle_eucl_dist_separation in H12.
  rewrite H12, (rngl_sub_diag Hos).
  symmetry.
  apply (rngl_mul_0_l Hos).
}
remember (angle_add_overflow θ1 θ2) as ov eqn:Hov.
remember (θ1 <? θ2)%A as tt eqn:Htt.
symmetry in Hov, Htt.
rewrite (rngl_mul_comm Hic).
destruct ov. {
  destruct tt. {
    apply (angle_add_overflow_angle_lt_cos_sub_cos _ _ Hov Htt).
  } {
    apply angle_ltb_ge in Htt.
    apply (angle_add_overflow_angle_ge_cos_sub_cos _ _ Hov Htt).
  }
} {
  destruct tt. {
    apply (angle_add_not_overflow_angle_lt_cos_sub_cos _ _ Hov Htt).
  } {
    apply angle_ltb_ge in Htt.
    apply (angle_add_not_overflow_angle_ge_cos_sub_cos _ _ Hov Htt).
  }
}
Qed.

Theorem angle_eucl_dist_lt_angle_eucl_dist :
  ∀ θ1 θ2 θ3 θ4,
  (angle_eucl_dist θ1 θ2 < angle_eucl_dist θ3 θ4)%L
  ↔ (rngl_cos (θ3 - θ4) < rngl_cos (θ1 - θ2))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (angle_eucl_dist _ _)).
  do 2 rewrite (H1 (rngl_cos _)).
  easy.
}
intros.
do 2 rewrite angle_eucl_dist_is_sqrt.
split. {
  intros Hdd.
  apply (rngl_lt_lt_squ Hop Hor Hii) in Hdd; cycle 1. {
    apply (rngl_mul_comm Hic).
  } {
    apply rl_sqrt_nonneg.
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hon Hos Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_squ_sqrt Hon) in Hdd. 2: {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hon Hos Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_squ_sqrt Hon) in Hdd. 2: {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hon Hos Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii) in Hdd. 2: {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  apply (rngl_sub_lt_mono_l Hop Hor) in Hdd.
  rewrite rngl_cos_sub_comm in Hdd.
  now rewrite (rngl_cos_sub_comm θ2 θ1) in Hdd.
} {
  intros Hcc.
  apply (rl_sqrt_lt_rl_sqrt Hon Hor). {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hon Hos Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii).
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  apply (rngl_sub_lt_mono_l Hop Hor).
  rewrite (rngl_cos_sub_comm θ4).
  rewrite (rngl_cos_sub_comm θ2).
  easy.
}
Qed.

Theorem angle_add_not_overflow_iff :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  ↔ (θ1 = 0%A ∨ (θ2 < - θ1)%A).
Proof.
intros.
split; intros Hov. {
  apply Bool.andb_false_iff in Hov.
  destruct Hov as [Hov| Hov]; [ left | right ]. {
    apply Bool.negb_false_iff in Hov.
    now apply angle_eqb_eq in Hov.
  } {
    now apply angle_leb_gt in Hov.
  }
} {
  apply Bool.andb_false_iff.
  destruct Hov as [Hov| Hov]; [ left | right ]. {
    apply Bool.negb_false_iff.
    now apply angle_eqb_eq.
  } {
    now apply angle_leb_gt.
  }
}
Qed.

Theorem angle_eucl_dist_pos_angle_neq :
  ∀ θ1 θ2, (0 < angle_eucl_dist θ1 θ2)%L ↔ θ1 ≠ θ2.
Proof.
destruct_ac.
intros.
split; intros Hd. {
  apply (rngl_lt_iff Hor) in Hd.
  destruct Hd as (_, Hd).
  intros H1; apply Hd; symmetry.
  now apply angle_eucl_dist_separation.
} {
  apply (rngl_lt_iff Hor).
  split; [ apply angle_eucl_dist_nonneg | ].
  intros H1; apply Hd.
  now apply angle_eucl_dist_separation.
}
Qed.

Theorem angle_around_straight_eucl_dist :
  ∀ θ1 θ2,
  (θ1 < angle_straight < θ2)%A
  → (θ2 < θ1 + angle_right)%A
  → (angle_eucl_dist θ1 angle_straight < angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
intros * (H1s, Hs2) H21.
progress unfold angle_ltb in H1s.
progress unfold angle_ltb in Hs2.
progress unfold angle_ltb in H21.
rewrite rngl_sin_add_right_r in H21.
rewrite rngl_cos_add_right_r in H21.
cbn in H1s, Hs2, H21.
rewrite (rngl_leb_refl Hor) in H1s, Hs2.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_cos θ1)%L as zc1 eqn:Hzc1.
symmetry in Hzs1, Hzs2, Hzc1.
destruct zs1; [ | easy ].
destruct zs2. {
  exfalso.
  apply rngl_ltb_lt in Hs2.
  apply rngl_nle_gt in Hs2.
  apply Hs2, rngl_cos_bound.
}
clear Hs2.
destruct zc1; [ easy | ].
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt in H1s, H21.
apply (rngl_leb_gt Hor) in Hzs2, Hzc1.
apply (rngl_lt_opp_r Hop Hor) in H21.
apply angle_eucl_dist_lt_angle_eucl_dist.
rewrite rngl_cos_sub_straight_r.
apply (rngl_lt_opp_r Hop Hor).
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  exfalso.
  apply (rngl_nle_gt) in H21.
  apply H21; clear H21.
  now apply (rngl_add_nonneg_nonneg Hor).
}
apply (rngl_nle_gt_iff Hor) in Hzc2.
rewrite rngl_cos_sub.
rewrite rngl_add_add_swap.
apply (rngl_add_neg_nonpos Hop Hor). {
  rewrite (rngl_add_mul_l_diag_l Hon).
  rewrite (rngl_mul_comm Hic).
  apply (rngl_mul_pos_neg Hop Hor); [ | | easy ]. {
    rewrite Bool.orb_true_iff; right.
    rewrite Hi1; cbn.
    apply (rngl_has_eq_dec_or_is_ordered_r Hor).
  }
  rewrite rngl_add_comm.
  apply (rngl_lt_opp_l Hop Hor).
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_opp_1 in H; subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
apply (rngl_lt_le_incl Hor) in Hzs2.
now apply (rngl_mul_nonneg_nonpos Hop Hor).
Qed.

Theorem angle_eqb_refl : ∀ θ, (θ =? θ)%A = true.
Proof.
destruct_ac.
intros.
progress unfold angle_eqb.
now do 2 rewrite (rngl_eqb_refl Hed).
Qed.

Theorem rngl_1_sub_cos_div_squ_sin :
  ∀ θ,
  (rngl_sin θ ≠ 0)%L
  → (((1 - rngl_cos θ) / (rngl_sin θ)²)%L =
     1 / (1 + rngl_cos θ))%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
intros * Hcz.
assert (H1scnz : (1 - rngl_cos θ)%L ≠ 0%L). {
  intros H.
  apply -> (rngl_sub_move_0_r Hop) in H.
  symmetry in H.
  apply eq_rngl_cos_1 in H.
  now subst θ.
}
specialize (cos2_sin2_1 θ) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite <- (rngl_squ_1 Hon) at 2.
rewrite (rngl_squ_sub_squ Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_add_sub Hos).
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | ]. 2: {
  intros H.
  rewrite rngl_add_comm in H.
  apply -> (rngl_add_move_0_r Hop) in H.
  apply eq_rngl_cos_opp_1 in H.
  now subst θ.
}
now rewrite (rngl_div_diag Hon Hiq).
Qed.

Theorem angle_right_le_straight :
  (angle_right ≤ angle_straight)%A.
Proof.
destruct_ac.
progress unfold angle_leb.
cbn.
rewrite (rngl_0_leb_1 Hon Hos Hor).
rewrite (rngl_leb_refl Hor).
apply rngl_leb_le.
apply (rngl_opp_1_le_0 Hon Hop Hor).
Qed.

Theorem formula_div_add_summation_succ :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ (a : T) n,
  (0 ≤ a)%L
  → (a / (1 + a) + (∑ (k = 1, S n), (-1) ^ k * a ^ k) =
    - a * (a / (1 + a) + (∑ (k = 1, n), (-1) ^ k * a ^ k)))%L.
Proof.
intros Hic Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hza.
  rewrite (H1 (- _ * _))%L.
  apply H1.
}
intros * Hza.
destruct n. {
  rewrite rngl_summation_only_one.
  rewrite rngl_summation_empty; [ | easy ].
  do 2 rewrite (rngl_pow_1_r Hon).
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_add_opp_r Hop).
  rewrite rngl_add_0_r.
  rewrite <- (rngl_mul_div Hi1 a (1 + a)) at 3. 2: {
    intros H.
    rewrite rngl_add_comm in H.
    apply (rngl_add_move_0_r Hop) in H.
    rewrite H in Hza.
    apply rngl_nlt_ge in Hza.
    apply Hza; clear Hza.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
  }
  rewrite <- (rngl_div_sub_distr_r Hop Hiv).
  rewrite rngl_mul_add_distr_l.
  rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_sub_add_distr Hos).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite (rngl_mul_opp_l Hop).
  f_equal.
  rewrite (rngl_mul_div_assoc Hiv).
  easy.
}
rewrite rngl_summation_split_first; [ | flia ].
do 2 rewrite (rngl_pow_1_r Hon).
rewrite (rngl_summation_shift 1); [ | flia ].
do 2 rewrite Nat_sub_succ_1.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_assoc.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_add_sub_swap Hop).
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite Nat.add_comm at 2.
  do 2 rewrite (rngl_pow_add_r Hon).
  do 2 rewrite (rngl_pow_1_r Hon).
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_opp_l Hop).
  rewrite rngl_mul_assoc.
  rewrite <- (rngl_mul_opp_l Hop).
  easy.
}
cbn.
rewrite <- (rngl_mul_summation_distr_r Hos).
rewrite <- (rngl_opp_summation Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_sub_sub_swap Hop).
rewrite <- (rngl_mul_div Hi1 a (1 + a)) at 3. 2: {
  intros H.
  rewrite rngl_add_comm in H.
  apply (rngl_add_move_0_r Hop) in H.
  rewrite H in Hza.
  apply rngl_nlt_ge in Hza.
  apply Hza; clear Hza.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_div_opp_l Hop Hiv).
rewrite <- (rngl_opp_add_distr Hop).
rewrite rngl_add_comm.
rewrite (rngl_mul_opp_l Hop).
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_div_assoc Hiv).
f_equal.
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem formula_div_add_summation :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a n,
  (a ≠ -1)%L
  → (a / (1 + a) + (∑ (k = 1, n), (-1) ^ k * a ^ k) =
     (-1) ^ n * a ^ S n / (1 + a))%L.
Proof.
intros Hic Hon Hop Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
intros * Ha1.
induction n. {
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_add_0_r.
  rewrite rngl_pow_0_r.
  rewrite (rngl_mul_1_l Hon).
  now rewrite (rngl_pow_1_r Hon).
}
rewrite rngl_summation_split_first; [ | now apply -> Nat.succ_le_mono ].
do 2 rewrite (rngl_pow_1_r Hon).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_assoc.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_mul_div Hi1 a (1 + a)) at 3. 2: {
  intros H.
  rewrite rngl_add_comm in H.
  now apply (rngl_add_move_0_r Hop) in H.
}
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_sub_0_l Hop).
destruct n. {
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_add_0_r.
  rewrite (rngl_pow_1_r Hon).
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  cbn.
  now rewrite (rngl_mul_1_r Hon).
}
rewrite (rngl_summation_shift 1); [ | flia ].
do 2 rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  do 2 rewrite rngl_pow_succ_r.
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_mul_swap Hic (-1)).
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite <- rngl_mul_assoc.
  easy.
}
cbn - [ "^"%L ].
rewrite <- (rngl_mul_summation_distr_l Hos).
rewrite <- (rngl_mul_opp_l Hop).
rewrite <- (rngl_mul_div_assoc Hiv).
rewrite <- rngl_mul_add_distr_l.
rewrite IHn.
rewrite (rngl_mul_div_assoc Hiv).
f_equal.
rewrite rngl_mul_assoc.
rewrite (rngl_mul_opp_l Hop).
rewrite <- (rngl_mul_opp_r Hop).
rewrite (rngl_mul_comm Hic a).
rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_pow_succ_r (S n)).
rewrite (rngl_mul_opp_l Hop).
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_eq_div_0_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a b, (a / b = 0 → b ≠ 0 → a = 0)%L.
Proof.
intros Hon Hos Hiv.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hab Hbz.
progress unfold rngl_div in Hab.
rewrite Hiv in Hab.
apply (rngl_eq_mul_0_l Hos Hii) in Hab; [ easy | ].
now apply (rngl_inv_neq_0 Hon Hos Hiv).
Qed.

Theorem rngl_acos_cos :
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → rngl_acos (rngl_cos θ) = θ.
Proof.
destruct_ac.
intros * Hzs.
apply eq_angle_eq.
rewrite rngl_cos_acos; [ | apply rngl_cos_bound ].
rewrite rngl_sin_acos; [ | apply rngl_cos_bound ].
f_equal.
rewrite <- (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
rewrite <- (rl_sqrt_squ Hon Hop Hor (rngl_sin _)).
f_equal.
apply (rngl_sub_move_r Hop).
symmetry; rewrite rngl_add_comm.
apply cos2_sin2_1.
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

(* parametric sin and cos *)

(* cos θ = (1-t²)/(1+t²), sin θ = 2t/(1+t²) *)
Definition circ_trigo_param θ :=
  if (θ =? 0)%A then 0%L
  else ((1 - rngl_cos θ) / rngl_sin θ)%L.

Definition param_cos θ :=
  if (θ =? angle_straight)%A then (-1)%L
  else
    let t := circ_trigo_param θ in
    ((1 - t²) / (1 + t²))%L.

Definition param_sin θ :=
  if (θ =? angle_straight)%A then 0%L
  else
    let t := circ_trigo_param θ in
    (2 * t / (1 + t²))%L.

Theorem rngl_cos_of_param :
  ∀ θ t,
  θ ≠ 0%A
  → θ ≠ angle_straight%A
  → t = circ_trigo_param θ
  → rngl_cos θ = ((1 - t²) / (1 + t²))%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Htz Hts Ht.
  rewrite (H1 (_ / _))%L.
  apply H1.
}
intros * Htz Hts Ht; subst t.
assert (Hsnz : rngl_sin θ ≠ 0%L). {
  intros H.
  apply eq_rngl_sin_0 in H.
  now destruct H.
}
assert (Hs2nz : ((rngl_sin θ)² ≠ 0)%L). {
  intros H.
  now apply (eq_rngl_squ_0 Hos Hio) in H.
}
assert (H1scnz : (1 - rngl_cos θ)%L ≠ 0%L). {
  intros H.
  apply -> (rngl_sub_move_0_r Hop) in H.
  symmetry in H.
  now apply eq_rngl_cos_1 in H.
}
assert (H1acnz : (1 + rngl_cos θ)%L ≠ 0%L). {
  intros H.
  rewrite rngl_add_comm in H.
  apply -> (rngl_add_move_0_r Hop) in H.
  now apply eq_rngl_cos_opp_1 in H.
}
assert (H20 : 2%L ≠ 0%L). {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
}
progress unfold circ_trigo_param.
apply angle_eqb_neq in Htz.
rewrite Htz.
apply angle_eqb_neq in Htz.
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
specialize (cos2_sin2_1 θ) as H1.
apply (rngl_add_move_r Hop) in H1.
rewrite H1; clear H1.
rewrite (rngl_add_sub_assoc Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite (rngl_div_sub_distr_r Hop Hiv (2 * _))%L.
rewrite (rngl_div_diag Hon Hiq); [ | easy ].
rewrite (rngl_sub_sub_distr Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_add_sub_swap Hop _ (_ / _))%L.
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
rewrite (rngl_div_sub_distr_r Hop Hiv).
rewrite (rngl_div_diag Hon Hiq). 2: {
  intros H.
  apply (f_equal (λ a, (a * (rngl_sin θ)²)))%L in H.
  rewrite (rngl_div_mul Hon Hiv) in H; [ | easy ].
  rewrite (rngl_mul_0_l Hos) in H.
  apply (rngl_eq_mul_0_r Hos) in H; [ easy | | easy ].
  now rewrite Hi1, Bool.orb_true_r.
}
specialize (cos2_sin2_1 θ) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite <- (rngl_squ_1 Hon) at 6.
rewrite (rngl_squ_sub_squ Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_add_sub Hos).
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_mul_div Hi1); [ | easy ].
rewrite (rngl_div_div_r Hon Hos Hiv); [ | easy | easy ].
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_div Hi1); [ | easy ].
rewrite rngl_add_comm.
symmetry.
apply (rngl_add_sub Hos).
Qed.

Theorem rngl_sin_of_param :
  ∀ θ t,
  θ ≠ 0%A
  → θ ≠ angle_straight%A
  → t = circ_trigo_param θ
  → rngl_sin θ = (2 * t / (1 + t²))%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Htz Hts Ht.
  rewrite (H1 (_ / _))%L.
  apply H1.
}
intros * Htz Hts Ht; subst t.
assert (Hsnz : rngl_sin θ ≠ 0%L). {
  intros H.
  apply eq_rngl_sin_0 in H.
  now destruct H.
}
assert (Hs2nz : ((rngl_sin θ)² ≠ 0)%L). {
  intros H.
  now apply (eq_rngl_squ_0 Hos Hio) in H.
}
assert (H1scnz : (1 - rngl_cos θ)%L ≠ 0%L). {
  intros H.
  apply -> (rngl_sub_move_0_r Hop) in H.
  symmetry in H.
  now apply eq_rngl_cos_1 in H.
}
assert (H1acnz : (1 + rngl_cos θ)%L ≠ 0%L). {
  intros H.
  rewrite rngl_add_comm in H.
  apply -> (rngl_add_move_0_r Hop) in H.
  now apply eq_rngl_cos_opp_1 in H.
}
assert (H20 : 2%L ≠ 0%L). {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
}
assert (H1cds2 : ((1 - rngl_cos θ) / (rngl_sin θ)²)%L ≠ 0%L). {
  specialize (cos2_sin2_1 θ) as H1.
  apply (rngl_add_move_l Hop) in H1.
  rewrite H1; clear H1.
  rewrite <- (rngl_squ_1 Hon) at 2.
  rewrite (rngl_squ_sub_squ Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_add_sub Hos).
  rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
  rewrite (rngl_div_diag Hon Hiq); [ | easy ].
  rewrite (rngl_div_1_l Hon Hiv).
  now apply (rngl_inv_neq_0 Hon Hos Hiv).
}
progress unfold circ_trigo_param.
apply angle_eqb_neq in Htz.
rewrite Htz.
apply angle_eqb_neq in Htz.
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
specialize (cos2_sin2_1 θ) as H1.
apply (rngl_add_move_r Hop) in H1.
rewrite H1; clear H1.
rewrite (rngl_add_sub_assoc Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite (rngl_div_sub_distr_r Hop Hiv (2 * _))%L.
rewrite (rngl_div_diag Hon Hiq); [ | easy ].
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
rewrite <- (rngl_mul_div_assoc Hiv).
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | ]. 2: {
  intros H.
  apply (f_equal (λ a, (a * (rngl_sin θ)²)))%L in H.
  rewrite (rngl_div_mul Hon Hiv) in H; [ | easy ].
  rewrite (rngl_mul_0_l Hos) in H.
  apply (rngl_eq_mul_0_r Hos) in H; [ easy | | easy ].
  now rewrite Hi1, Bool.orb_true_r.
}
rewrite <- (rngl_mul_div_assoc Hiv).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_div_assoc Hiv).
do 2 rewrite (rngl_mul_comm Hic 2).
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | ]. 2: {
  intros H.
  apply (rngl_eq_mul_0_r Hos) in H; [ easy | | easy ].
  now rewrite Hi1, Bool.orb_true_r.
}
rewrite (rngl_mul_div Hi1); [ | easy ].
rewrite (rngl_mul_comm Hic).
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_div_r Hon Hos Hiv); [ | easy | easy ].
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_div Hi1); [ | easy ].
progress unfold rngl_squ.
symmetry.
now apply (rngl_mul_div Hi1).
Qed.

Theorem rngl_param_cos : ∀ θ, rngl_cos θ = param_cos θ.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
intros.
progress unfold param_cos.
remember (θ =? 0)%A as tz eqn:Htz.
remember (θ =? angle_straight)%A as ts eqn:Hts.
symmetry in Htz, Hts.
destruct ts; [ now apply angle_eqb_eq in Hts; subst θ | ].
destruct tz. {
  apply angle_eqb_eq in Htz; subst θ.
  progress unfold circ_trigo_param.
  rewrite angle_eqb_refl.
  rewrite (rngl_squ_0 Hos).
  rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
  now rewrite (rngl_div_1_r' Hon Hos Hiq).
}
apply angle_eqb_neq in Htz, Hts.
now apply rngl_cos_of_param.
Qed.

Theorem rngl_param_sin : ∀ θ, rngl_sin θ = param_sin θ.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
intros.
progress unfold param_sin.
remember (θ =? 0)%A as tz eqn:Htz.
remember (θ =? angle_straight)%A as ts eqn:Hts.
symmetry in Htz, Hts.
destruct ts; [ now apply angle_eqb_eq in Hts; subst θ | ].
destruct tz. {
  apply angle_eqb_eq in Htz; subst θ.
  progress unfold circ_trigo_param.
  rewrite angle_eqb_refl.
  rewrite (rngl_squ_0 Hos).
  rewrite (rngl_mul_0_r Hos), rngl_add_0_r.
  now rewrite (rngl_div_1_r' Hon Hos Hiq).
}
apply angle_eqb_neq in Htz, Hts.
now apply rngl_sin_of_param.
Qed.

Theorem rngl_eq_is_derivative_is_derivative :
  ∀ f f' g g' dist,
  (∀ x, f x = g x)
  → (∀ x, f' x = g' x)
  → is_derivative angle_eucl_dist dist f f'
  → is_derivative angle_eucl_dist dist g g'.
Proof.
intros * Hfg Hfg' Hff.
intros θ ε Hε.
specialize (Hff θ ε Hε).
destruct Hff as (η & Hη & Hff).
exists η.
split; [ easy | ].
intros θ' Hθ'.
do 2 rewrite <- Hfg.
rewrite <- Hfg'.
now apply Hff.
Qed.

Theorem angle_eucl_dist_0_straight :
  angle_eucl_dist 0 angle_straight = 2%L.
Proof.
destruct_ac.
progress unfold angle_eucl_dist.
progress unfold rl_modl.
cbn.
rewrite <- (rngl_opp_add_distr Hop).
rewrite (rngl_squ_opp Hop).
rewrite (rngl_sub_0_r Hos).
rewrite (rngl_squ_0 Hos).
rewrite rngl_add_0_r.
rewrite (rl_sqrt_squ Hon Hop Hor).
apply (rngl_abs_nonneg_eq Hop Hor).
apply (rngl_0_le_2 Hon Hos Hor).
Qed.

Theorem fold_param_cos :
  ∀ θ,
  θ ≠ angle_straight
  → let t := circ_trigo_param θ in
    ((1 - t²) / (1 + t²))%L = param_cos θ.
Proof.
intros * Hts.
progress unfold param_cos.
apply angle_eqb_neq in Hts.
now rewrite Hts.
Qed.

Theorem fold_param_sin :
  ∀ θ,
  θ ≠ angle_straight
  → let t := circ_trigo_param θ in
    (2 * t / (1 + t²))%L = param_sin θ.
Proof.
intros * Hts.
progress unfold param_sin.
apply angle_eqb_neq in Hts.
now rewrite Hts.
Qed.

Definition seq_cos_param_when_lt_right θ :=
  let t := circ_trigo_param θ in
  λ i, (1 + 2 * ∑ (k = 1, i), (-1)^k * t² ^ k)%L.

(* proof that the implicit function x²+y²-1 is of class C∞ *)

Definition U_implicit_function x y := (x² + y² - 1)%L.

Definition is_partial_deriv_on_x (f f' : T → T → T) :=
  ∀ x y,
  ∀ ε, (0 < ε)%L → ∃ η, (0 < η)%L ∧
  ∀ h, (0 < h < η)%L → (rngl_abs ((f (x + h) y - f x y) / h - f' x y) < ε)%L.

Definition is_partial_deriv_on_y (f f' : T → T → T) :=
  ∀ x y,
  ∀ ε, (0 < ε)%L → ∃ η, (0 < η)%L ∧
  ∀ h, (0 < h < η)%L → (rngl_abs ((f x (y + h) - f x y) / h - f' x y) < ε)%L.

Theorem U_implicit_function_partial_deriv :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv_and_1_or_quot T = true →
  rngl_is_ordered T = true →
  ∀ x y ε, (0 < ε)%L → ∃ η : T, (0 < η)%L ∧
  ∀ h : T,
  (0 < h < η)%L
  → (rngl_abs (((x + h)² + y² - 1 - (x² + y² - 1)) / h - 2 * x) < ε)%L.
Proof.
intros Hic Hon Hop Hi1 Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hε.
exists ε.
split; [ easy | ].
intros h Hh.
rewrite (rngl_sub_sub_distr Hop).
rewrite (rngl_sub_sub_swap Hop).
rewrite (rngl_sub_add Hop).
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_sub_sub_swap Hop).
rewrite (rngl_add_sub Hos).
rewrite (rngl_squ_add Hic Hon).
do 2 rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
progress unfold rngl_squ.
rewrite <- rngl_mul_add_distr_r.
destruct Hh as (Hzh, Hhη).
rewrite (rngl_mul_div Hi1). 2: {
  intros H; subst h.
  now apply (rngl_lt_irrefl Hor) in Hzh.
}
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
rewrite (rngl_abs_nonneg_eq Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor) in Hzh.
Qed.

Fixpoint has_nth_partial_deriv n f :=
  match n with
  | 0 => True
  | S n' =>
      (∃ f₁,
       is_partial_deriv_on_x f f₁ ∧
       has_nth_partial_deriv n' f₁) ∧
      (∃ f₂,
       is_partial_deriv_on_y f f₂ ∧
       has_nth_partial_deriv n' f₂)
  end.

Theorem zero_fun_has_nth_partial_deriv :
  rngl_has_opp T = true →
  rngl_has_inv_and_1_or_quot T = true →
  rngl_is_ordered T = true →
  ∀ n, has_nth_partial_deriv n (λ _ _ : T, 0%L).
Proof.
intros Hop Hi1 Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
induction n; [ easy | cbn ].
split. {
  exists (λ _ _, 0%L).
  split; [ | easy ].
  intros x y ε Hε.
  exists ε.
  split; [ easy | ].
  intros h (Hhz, Hhe).
  rewrite (rngl_sub_diag Hos), (rngl_sub_0_r Hos).
  rewrite (rngl_div_0_l Hos Hi1). 2: {
    intros H; subst h.
    now apply (rngl_lt_irrefl Hor) in Hhz.
  }
  now rewrite (rngl_abs_0 Hop).
} {
  exists (λ _ _, 0%L).
  split; [ | easy ].
  intros x y ε Hε.
  exists ε.
  split; [ easy | ].
  intros h (Hhz, Hhe).
  rewrite (rngl_sub_diag Hos), (rngl_sub_0_r Hos).
  rewrite (rngl_div_0_l Hos Hi1). 2: {
    intros H; subst h.
    now apply (rngl_lt_irrefl Hor) in Hhz.
  }
  now rewrite (rngl_abs_0 Hop).
}
Qed.

Theorem fun_2_has_nth_partial_deriv :
  rngl_has_opp T = true →
  rngl_has_inv_and_1_or_quot T = true →
  rngl_is_ordered T = true →
  ∀ n, has_nth_partial_deriv n (λ _ _ : T, 2%L).
Proof.
intros Hop Hi1 Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
destruct n; [ easy | cbn ].
split. {
  exists (λ _ _, 0%L).
  split. {
    intros x y ε Hε.
    exists ε.
    split; [ easy | ].
    intros h (Hhz, Hhe).
    rewrite (rngl_sub_diag Hos), (rngl_sub_0_r Hos).
    rewrite (rngl_div_0_l Hos Hi1). 2: {
      intros H; subst h.
      now apply (rngl_lt_irrefl Hor) in Hhz.
    }
    now rewrite (rngl_abs_0 Hop).
  }
  apply (zero_fun_has_nth_partial_deriv Hop Hi1 Hor).
} {
  exists (λ _ _, 0%L).
  split. {
    intros x y ε Hε.
    exists ε.
    split; [ easy | ].
    intros h (Hhz, Hhe).
    rewrite (rngl_sub_diag Hos), (rngl_sub_0_r Hos).
    rewrite (rngl_div_0_l Hos Hi1). 2: {
      intros H; subst h.
      now apply (rngl_lt_irrefl Hor) in Hhz.
    }
    now rewrite (rngl_abs_0 Hop).
  }
  apply (zero_fun_has_nth_partial_deriv Hop Hi1 Hor).
}
Qed.

Theorem U_implicit_function_partial_C_infinite :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv_and_1_or_quot T = true →
  rngl_is_ordered T = true →
  ∀ n, has_nth_partial_deriv n U_implicit_function.
Proof.
intros Hic Hon Hop Hi1 Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
destruct n; [ easy | cbn ].
split. {
  exists (λ x y, (2 * x)%L).
  split. {
    intros x y ε Hε.
    progress unfold U_implicit_function.
    now apply (U_implicit_function_partial_deriv Hic Hon Hop Hi1 Hor).
  }
  destruct n; [ easy | cbn ].
  split. {
    exists (λ x y, 2%L).
    split. {
      intros x y ε Hε.
      exists ε.
      split; [ easy | ].
      intros h (Hhz, Hhe).
      rewrite <- (rngl_mul_sub_distr_l Hop).
      rewrite (rngl_add_comm x), (rngl_add_sub Hos).
      rewrite (rngl_mul_div Hi1). 2: {
        intros H; subst h.
        now apply (rngl_lt_irrefl Hor) in Hhz.
      }
      rewrite (rngl_sub_diag Hos).
      now rewrite (rngl_abs_0 Hop).
    }
    apply (fun_2_has_nth_partial_deriv Hop Hi1 Hor).
  } {
    exists (λ x y, 0%L).
    split. {
      intros x y ε Hε.
      exists ε.
      split; [ easy | ].
      intros h (Hhz, Hhe).
      rewrite (rngl_sub_diag Hos), (rngl_sub_0_r Hos).
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        intros H; subst h.
        now apply (rngl_lt_irrefl Hor) in Hhz.
      }
      now rewrite (rngl_abs_0 Hop).
    }
    apply (zero_fun_has_nth_partial_deriv Hop Hi1 Hor).
  }
} {
  exists (λ x y, (2 * y)%L).
  split. {
    intros x y ε Hε.
    progress unfold U_implicit_function.
    specialize (U_implicit_function_partial_deriv Hic Hon Hop Hi1 Hor) as H1.
    specialize (H1 y x ε Hε).
    destruct H1 as (η & Hη & Hle).
    exists η.
    split; [ easy | ].
    intros h Hh.
    do 2 rewrite (rngl_add_comm x²).
    now apply Hle.
  }
  destruct n; [ easy | cbn ].
  split. {
    exists (λ x y, 0%L).
    split. {
      intros x y ε Hε.
      exists ε.
      split; [ easy | ].
      intros h (Hhz, Hhe).
      rewrite (rngl_sub_diag Hos), (rngl_sub_0_r Hos).
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        intros H; subst h.
        now apply (rngl_lt_irrefl Hor) in Hhz.
      }
      now rewrite (rngl_abs_0 Hop).
    }
    apply (zero_fun_has_nth_partial_deriv Hop Hi1 Hor).
  } {
    exists (λ x y, 2%L).
    split. {
      intros x y ε Hε.
      exists ε.
      split; [ easy | ].
      intros h (Hhz, Hhe).
      rewrite rngl_mul_add_distr_l.
      rewrite (rngl_add_sub_swap Hop).
      rewrite (rngl_sub_diag Hos).
      rewrite rngl_add_0_l.
      rewrite (rngl_mul_div Hi1). 2: {
        intros H; subst h.
        now apply (rngl_lt_irrefl Hor) in Hhz.
      }
      rewrite (rngl_sub_diag Hos).
      now rewrite (rngl_abs_0 Hop).
    }
    apply (fun_2_has_nth_partial_deriv Hop Hi1 Hor).
  }
}
Qed.

Theorem angle_le_dec :
  ∀ θ1 θ2 : angle T, {(θ1 ≤ θ2)%A} + {¬ (θ1 ≤ θ2)%A}.
Proof.
intros.
remember (θ1 ≤? θ2)%A as t12 eqn:Ht12.
symmetry in Ht12.
destruct t12; [ now left | now right ].
Qed.

Theorem angle_lt_dec :
  ∀ θ1 θ2 : angle T, {(θ1 < θ2)%A} + {¬ (θ1 < θ2)%A}.
Proof.
intros.
remember (θ1 <? θ2)%A as t12 eqn:Ht12.
symmetry in Ht12.
destruct t12; [ now left | now right ].
Qed.

(* to be completed
Theorem param_cos_derivative :
  is_derivative angle_eucl_dist rngl_dist param_cos (λ θ, (- param_sin θ)%L).
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀ ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros θ ε Hε.
enough (H :
  ∃ η : T, (0 < η)%L ∧
  ∀ dθ,
  (0 < angle_eucl_dist dθ 0 < η)%L
  → (rngl_abs
        ((param_cos (θ + dθ) - param_cos θ) / angle_eucl_dist dθ 0 +
         param_sin θ) < ε)%L). {
  destruct H as (η & Hη & Hde).
  move η before ε.
  exists η.
  split; [ easy | ].
  intros θ' Ht.
  remember (θ' - θ)%A as dθ eqn:Hdt.
  symmetry in Hdt.
  apply angle_sub_move_r in Hdt.
  subst θ'.
  rewrite angle_eucl_dist_move_0_r in Ht |-*.
  rewrite angle_add_sub in Ht |-*.
  progress unfold rngl_dist.
  rewrite angle_add_comm.
  rewrite (rngl_sub_opp_r Hop).
  now apply Hde.
}
enough (H :
  ∃ η : T, (0 < η)%L ∧
  ∀ dθ,
  (0 < angle_eucl_dist dθ 0 < η)%L
  → (rngl_abs
        ((param_cos (θ + dθ) - param_cos θ) / angle_eucl_dist dθ 0 +
         param_sin θ) < ε)%L). {
  destruct H as (η & Hη & Hde).
  move η before ε.
  exists η.
  split; [ easy | ].
  intros dθ Hdt.
  progress unfold param_cos.
  remember (θ + dθ =? angle_straight)%A as tds eqn:Htds.
  symmetry in Htds.
  destruct tds. 2: {
    remember (θ =? angle_straight)%A as ts eqn:Hts.
    symmetry in Hts.
    destruct ts. 2: {
      remember (circ_trigo_param (θ + dθ)) as td eqn:Htd.
      remember (circ_trigo_param θ) as t eqn:Ht.
      move t before td.
      symmetry in Htd, Ht.
      progress unfold param_sin.
      rewrite Hts.
      rewrite Ht.
      progress unfold circ_trigo_param in Htd, Ht.
      remember (θ + dθ =? 0)%A as tdz eqn:Htdz.
      symmetry in Htdz.
      destruct tdz. 2: {
...
  progress unfold param_cos.
  progress unfold param_sin.
  progress unfold rngl_dist.
  remember (circ_trigo_param θ) as t eqn:Ht.
  remember (θ =? angle_straight)%A as ts eqn:Hts.
  symmetry in Hts.
  destruct ts. 2: {
    remember (θ₀ =? angle_straight)%A as tsz eqn:Htsz.
    symmetry in Htsz.
    destruct tsz. 2: {
      remember (circ_trigo_param θ₀) as tz eqn:Htz.
      rewrite (rngl_sub_opp_r Hop).
...
    apply angle_eqb_eq in Hts.
    subst θ.
    remember (θ₀ =? angle_straight)%A as tsz eqn:Htsz.
    symmetry in Htsz.
    destruct tsz. {
      apply angle_eqb_eq in Htsz.
      subst θ₀.
      rewrite angle_eucl_dist_diag in Hθ.
      destruct Hθ as (H1, _).
      now apply (rngl_lt_irrefl Hor) in H1.
    }
    remember (circ_trigo_param θ₀) as tz eqn:Htz.
    clear t Ht.
...

Theorem lim_seq_cos_param_when_lt_right :
  rngl_is_archimedean T = true →
  ∀ θ,
  (θ < angle_right)%A
  → is_limit_when_tending_to_inf rngl_dist
      (seq_cos_param_when_lt_right θ) (rngl_cos θ).
Proof.
destruct_ac.
intros Har.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hθ ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hθ.
intros ε Hε.
enough (H :
  ∃ N : nat, ∀ n : nat, N ≤ n →
  let t := circ_trigo_param θ in
  (2 * rngl_abs
     (t² / (1 + t²) +
      (∑ (k = 1, n), (-1) ^ k * t² ^ k)) < ε)%L). {
  destruct H as (N & HN).
  exists N.
  intros n Hn.
  progress unfold rngl_dist.
  progress unfold seq_cos_param_when_lt_right.
  rewrite rngl_param_cos.
  progress unfold param_cos.
  remember (θ =? angle_straight)%A as ts eqn:Hts.
  symmetry in Hts.
  destruct ts. {
    exfalso.
    apply angle_eqb_eq in Hts.
    subst θ.
    apply angle_nle_gt in Hθ.
    apply Hθ; clear Hθ.
    apply angle_right_le_straight.
  }
  set (t := circ_trigo_param θ).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_div_diag Hon Hiq (1 + t²)) at 1. 2: {
    intros H.
    rewrite rngl_add_comm in H.
    apply (rngl_add_move_0_r Hop) in H.
    specialize (rngl_squ_nonneg Hos Hor t) as H1.
    rewrite H in H1.
    apply rngl_nlt_ge in H1.
    apply H1; clear H1.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
  }
  rewrite <- (rngl_div_sub_distr_r Hop Hiv).
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite (rngl_sub_diag Hos).
  rewrite rngl_add_0_l.
  rewrite <- (rngl_mul_2_l Hon).
  rewrite <- (rngl_mul_div_assoc Hiv).
  rewrite <- rngl_mul_add_distr_l.
  rewrite (rngl_abs_mul Hop Hi1 Hor).
  rewrite (rngl_abs_2 Hon Hos Hor).
  now apply HN.
}
destruct (rngl_eq_dec Heo (circ_trigo_param θ)² 0) as [Htpz| Htpz]. {
  exists 0.
  intros n _.
  cbn; rewrite Htpz.
  rewrite rngl_add_0_r.
  rewrite (rngl_div_1_r Hon Hiq Hc1).
  rewrite rngl_add_0_l.
  rewrite all_0_rngl_summation_0. 2: {
    intros i Hi.
    rewrite (rngl_pow_0_l Hos).
    destruct i; [ easy | ].
    apply (rngl_mul_0_r Hos).
  }
  rewrite (rngl_abs_0 Hop).
  now rewrite (rngl_mul_0_r Hos).
}
assert (Hte : ((circ_trigo_param θ)² < 1)%L). {
  progress unfold circ_trigo_param.
  remember (θ =? 0)%A as tz eqn:Htz.
  symmetry in Htz.
  destruct tz. {
    rewrite (rngl_squ_0 Hos).
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
  }
  apply angle_eqb_neq in Htz.
  rewrite (rngl_squ_div Hic Hon Hos Hiv). 2: {
    intros H.
    apply eq_rngl_sin_0 in H.
    destruct H; subst θ; [ easy | ].
    exfalso.
    apply angle_nle_gt in Hθ.
    apply Hθ; clear Hθ.
    apply angle_right_le_straight.
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). 2: {
    rewrite (rngl_mul_1_l Hon).
    specialize (cos2_sin2_1 θ) as H1.
    apply (rngl_add_move_l Hop) in H1.
    rewrite H1; clear H1.
    rewrite (rngl_squ_sub Hop Hic Hon).
    rewrite (rngl_mul_1_r Hon).
    rewrite (rngl_squ_1 Hon).
    rewrite <- (rngl_add_sub_swap Hop).
    apply (rngl_lt_sub_lt_add_r Hop Hor).
    rewrite <- (rngl_add_sub_swap Hop).
    apply -> (rngl_lt_add_lt_sub_r Hop Hor).
    rewrite <- rngl_add_assoc.
    rewrite <- (rngl_mul_2_l Hon).
    apply (rngl_add_lt_mono_l Hop Hor).
    apply (rngl_mul_lt_mono_pos_l Hop Hor Hii). {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    apply (rngl_lt_0_sub Hop Hor).
    progress unfold rngl_squ.
    rewrite (rngl_sub_mul_r_diag_l Hon Hop).
    apply (rngl_mul_pos_pos Hos Hor Hii). {
      now apply rngl_lt_0_cos.
    }
    apply (rngl_lt_0_sub Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_cos_bound | ].
    intros H.
    now apply eq_rngl_cos_1 in H.
  }
  apply (rngl_lt_iff Hor).
  split; [ apply (rngl_squ_nonneg Hos Hor) | ].
  intros H; symmetry in H.
  apply (eq_rngl_squ_0 Hos Hio) in H.
  apply (eq_rngl_sin_0) in H.
  destruct H; subst θ; [ easy | ].
  exfalso.
  apply angle_nle_gt in Hθ.
  apply Hθ; clear Hθ.
  apply angle_right_le_straight.
}
enough (H :
  ∃ N, ∀ n, N ≤ n →
  let t := circ_trigo_param θ in
  (2 * t² ^ S n / (1 + t²) < ε)%L). {
  destruct H as (N & HN).
  exists N.
  intros n Hn.
  cbn - [ "*" ].
  set (t := circ_trigo_param θ).
  rewrite (formula_div_add_summation Hic Hon Hop Hiv). 2: {
    specialize (rngl_squ_nonneg Hos Hor t) as H1.
    intros H2.
    rewrite H2 in H1.
    apply rngl_nlt_ge in H1.
    apply H1; clear H1.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
  }
  rewrite (rngl_abs_div Hon Hop Hiv Hed Hor). 2: {
    specialize (rngl_squ_nonneg Hos Hor t) as H1.
    intros H2.
    rewrite rngl_add_comm in H2.
    apply (rngl_add_move_0_r Hop) in H2.
    rewrite H2 in H1.
    apply rngl_nlt_ge in H1.
    apply H1; clear H1.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
  }
  rewrite (rngl_abs_mul Hop Hi1 Hor).
  (* lemma to do *)
  replace (rngl_abs ((-1) ^ n)) with 1%L. 2: {
    symmetry.
    clear Hn.
    induction n; [ apply (rngl_abs_1 Hon Hos Hor) | ].
    rewrite rngl_pow_succ_r.
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_1_l Hon).
    now rewrite (rngl_abs_opp Hop Hor).
  }
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    clear Hn.
    induction n. {
      rewrite (rngl_pow_1_r Hon).
      apply (rngl_squ_nonneg Hos Hor).
    }
    rewrite rngl_pow_succ_r.
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
    apply (rngl_squ_nonneg Hos Hor).
  }
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_le_trans Hor _ 1). {
      apply (rngl_0_le_1 Hon Hos Hor).
    }
    apply (rngl_le_add_r Hor).
    apply (rngl_squ_nonneg Hos Hor).
  }
  rewrite (rngl_mul_div_assoc Hiv).
  now apply HN.
}
specialize (int_part Hon Hop Hc1 Hor Har) as Hint.
destruct (Hint (2 / ε))%L as (n2ε & Hn2ε).
...
exists (1 + Nat.log2_up n2ε).
intros n Hn.
cbn - [ rngl_power ].
set (t := circ_trigo_param θ).
apply (rngl_lt_div_l Hon Hop Hiv Hor). {
  apply (rngl_lt_le_trans Hor _ 1).
  apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
  apply (rngl_le_add_r Hor).
  apply (rngl_squ_nonneg Hos Hor).
}
apply (rngl_le_lt_trans Hor _ ε). 2: {
  rewrite <- (rngl_mul_1_r Hon ε) at 1.
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_lt_add_r Hos Hor).
  apply (rngl_lt_iff Hor).
  split; [ apply (rngl_squ_nonneg Hos Hor) | ].
  intros H; symmetry in H.
  apply (eq_rngl_squ_0 Hos Hio) in H.
  subst t.
  progress unfold circ_trigo_param in H.
  progress unfold circ_trigo_param in Htpz.
  remember (θ =? 0)%A as tz eqn:Htz.
  symmetry in Htz.
  destruct tz; [ now rewrite rngl_squ_0 in Htpz | ].
  apply angle_eqb_neq in Htz.
  apply (rngl_eq_div_0_r Hon Hos Hiv) in H. 2: {
    intros H1.
    apply eq_rngl_sin_0 in H1.
    destruct H1; [ easy | subst θ ].
    apply angle_nle_gt in Hθ.
    apply Hθ; clear Hθ.
    apply angle_right_le_straight.
  }
  apply -> (rngl_sub_move_0_r Hop) in H.
  symmetry in H.
  now apply eq_rngl_cos_1 in H.
}
apply Nat.le_add_le_sub_l in Hn.
(**)
destruct (rngl_le_dec Hor 2 ε) as [H2e| H2e]. {
  apply (rngl_le_trans Hor _ 2); [ | easy ].
  fold t in Hte.
  rewrite <- (rngl_mul_1_r Hon 2) at 2.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii).
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  rewrite <- (rngl_pow_1_l Hon (S n)).
  apply (rngl_pow_le_mono_l Hop Hon Hor).
  apply (rngl_squ_nonneg Hos Hor).
  now apply (rngl_lt_le_incl Hor) in Hte.
}
apply (rngl_nle_gt_iff Hor) in H2e.
rewrite (rngl_abs_nonneg_eq Hop Hor) in Hn2ε. 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor); [ | easy ].
  now apply (rngl_0_le_2 Hon Hos Hor).
}
apply Nat.log2_up_le_pow2 in Hn. 2: {
  apply Nat.neq_0_lt_0.
  intros H1; subst n2ε.
  cbn in Hn2ε.
  rewrite rngl_add_0_r in Hn2ε.
  destruct Hn2ε as (H1, H2).
  apply (rngl_lt_div_l Hon Hop Hiv Hor) in H2; [ | easy ].
  rewrite (rngl_mul_1_l Hon) in H2.
  apply (rngl_lt_le_incl Hor) in H2.
  now apply rngl_nlt_ge in H2.
}
assert (H2ee: (2 / ε < 2 ^ (n - 1) + 1)%L). {
  eapply (rngl_lt_le_trans Hor); [ apply Hn2ε | ].
  rewrite rngl_of_nat_add.
  rewrite rngl_of_nat_1.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite (rngl_add_sub Hos).
  rewrite <- rngl_of_nat_2.
  rewrite <- (rngl_of_nat_pow Hon Hos).
  now apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
}
apply (rngl_lt_div_l Hon Hop Hiv Hor) in H2ee; [ | easy ].
eapply (rngl_mul_le_mono_pos_l Hop Hor Hii). 2: {
  eapply (rngl_le_trans Hor). 2: {
    apply (rngl_lt_le_incl Hor) in H2ee.
    apply H2ee.
  }
(* ouais, chais pas, d'ailleurs ça sent pas très bon *)
...
Search (Nat.log2_up).
Search (Nat.log2_up _ ≤ Nat.log2_up _).
Search (Nat.log2_up _ ≤ _).
Search (Nat.log2_up _ ≤ _).
...
(*
    apply Nat.le_0_r in Hn; subst N.
    rewrite rngl_summation_empty; [ | easy ].
    rewrite rngl_add_0_r.
    specialize (HN _ (Nat.le_0_l 0)).
    cbn - [ "^"%L ] in HN.
    rewrite (rngl_pow_1_r Hon) in HN.
    progress fold t in HN.
    rewrite <- (rngl_mul_div_assoc Hiv) in HN.
    rewrite (rngl_abs_nonneg_eq Hop Hor); [ easy | ].
    apply (rngl_div_nonneg Hon Hop Hiv Hor). {
      apply (rngl_squ_nonneg Hos Hor).
    }
    apply (rngl_lt_le_trans Hor _ 1).
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
    apply (rngl_le_add_r Hor).
    apply (rngl_squ_nonneg Hos Hor).
*)
  rewrite (formula_div_add_summation_succ Hic Hon Hop Hiv Hor). 2: {
    apply (rngl_squ_nonneg Hos Hor).
  }
  rewrite (rngl_abs_mul Hop Hi1 Hor).
  rewrite (rngl_abs_opp Hop Hor).
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_squ_nonneg Hos Hor).
  }
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_comm Hic 2).
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_mul_comm Hic).
  destruct (rngl_eq_dec Heo t² 0) as [Hez| Hez]. {
    rewrite Hez.
    rewrite rngl_add_0_r.
    rewrite (rngl_div_1_r Hon Hiq Hc1).
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros i Hi.
      rewrite (rngl_pow_0_l Hos).
      destruct i; [ easy | ].
      apply (rngl_mul_0_r Hos).
    }
    now rewrite (rngl_mul_0_r Hos).
  }
  apply (rngl_lt_div_r Hon Hop Hiv Hor). {
    apply (rngl_lt_iff Hor).
    split; [ apply (rngl_squ_nonneg Hos Hor) | easy ].
  }
  apply Nat.succ_le_mono in Hn.
...
  apply (IHn _ N).
3: {
easy.
...
    apply (eq_rngl_sin_0) in H1.
  destruct H; subst θ; [ easy | ].
  exfalso.
  apply angle_nle_gt in Hθ.
  apply Hθ; clear Hθ.
  apply angle_right_le_straight.
2: {
...6
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    clear Hn.
    induction n. {
      rewrite rngl_summation_empty; [ | easy ].
      rewrite rngl_add_0_r.
      apply (rngl_div_nonneg Hon Hop Hiv Hor).
      apply (rngl_squ_nonneg Hos Hor).
      apply (rngl_lt_le_trans Hor _ 1).
      apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
      apply (rngl_le_add_r Hor).
      apply (rngl_squ_nonneg Hos Hor).
    }
    rewrite rngl_summation_split_first; [ | flia ].
    cbn - [ "*" ].
    do 2 rewrite (rngl_mul_opp_l Hop).
    do 2 rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_mul_1_r Hon).
    rewrite rngl_add_assoc.
    rewrite (rngl_add_opp_r Hop).
    rewrite <- (rngl_mul_div Hi1 t² (1 + t²)) at 3. 2: {
      intros H.
      rewrite rngl_add_comm in H.
      apply (rngl_add_move_0_r Hop) in H.
      specialize (rngl_squ_nonneg Hos Hor t) as H1.
      rewrite H in H1.
      apply rngl_nlt_ge in H1.
      apply H1; clear H1.
      apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
    }
    rewrite <- (rngl_div_sub_distr_r Hop Hiv).
    rewrite rngl_mul_add_distr_l.
    rewrite (rngl_mul_1_r Hon).
    rewrite (rngl_sub_add_distr Hos).
    rewrite (rngl_sub_diag Hos).
    rewrite (rngl_sub_0_l Hop).
...
Search (_ / _ - _)%L.
Search (_ / _ + _)%L.
...
  induction n. {
    rewrite rngl_summation_empty; [ | easy ].
    rewrite (rngl_mul_0_r Hos).
    rewrite rngl_add_0_r.
    rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
      apply (rngl_div_nonneg Hon Hop Hiv Hor).
      apply (rngl_mul_nonneg_nonneg Hos Hor).
      apply (rngl_0_le_2 Hon Hos Hor).
      apply (rngl_squ_nonneg Hos Hor).
      apply (rngl_lt_le_trans Hor _ 1).
      apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
      apply (rngl_le_add_r Hor).
      apply (rngl_squ_nonneg Hos Hor).
    }
    apply Nat.le_0_r in Hn; subst N.
    specialize (HN 1 Nat.le_0_1).
    cbn in HN.
    rewrite (rngl_mul_1_r Hon) in HN.
    easy.
  }
...
remember (λ (ε : T), 1) as f.
clear Heqf.
exists (f ε).
intros n Hn.
cbn - [ "*" ].
set (t := circ_trigo_param θ).
induction n. {
  rewrite rngl_summation_empty; [ | easy ].
  rewrite (rngl_mul_0_r Hos).
  rewrite rngl_add_0_r.
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_div_nonneg Hon Hop Hiv Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hon Hos Hor).
    apply (rngl_squ_nonneg Hos Hor).
    apply (rngl_lt_le_trans Hor _ 1).
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
    apply (rngl_le_add_r Hor).
    apply (rngl_squ_nonneg Hos Hor).
  }
...
}
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  rewrite rngl_summation_only_one.
  cbn.
  do 2 rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite fold_rngl_squ.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
...
}
rewrite rngl_summation_split_last; [ | now apply -> Nat.succ_le_mono ].
rewrite (rngl_summation_shift 1); [ | flia Hnz ].
do 2 rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite Nat.add_comm, Nat.add_sub.
  easy.
}
cbn - [ "*" ].
(* ahhhh, pute vierge... *)
...
  progress unfold t.
  progress unfold circ_trigo_param.
...

Theorem param_cos_derivative :
  is_derivative angle_eucl_dist rngl_dist param_cos (λ θ, (- param_sin θ)%L).
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀ ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros θ₀ ε Hε.
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ,
 (0 < angle_eucl_dist θ θ₀ < η)%L
 → (rngl_dist
      ((param_cos θ - param_cos θ₀) / angle_eucl_dist θ θ₀)
      (- param_sin θ₀) < ε)%L) by easy.
...
(*4*)
remember (λ a, (2 * a + 1)%L) as f eqn:Hf.
clear Hf.
exists (rngl_min (f ε) 2).
split; [ ... | ].
intros θ (Htz, Hze).
progress unfold param_cos.
progress unfold param_sin.
remember (θ =? angle_straight)%A as ts eqn:Hts.
remember (θ₀ =? angle_straight)%A as tzs eqn:Htzs.
symmetry in Hts, Htzs.
destruct ts. {
  apply angle_eqb_eq in Hts; subst θ.
  destruct tzs. {
    apply angle_eqb_eq in Htzs; subst θ₀.
    rewrite (proj2 (angle_eucl_dist_separation _ _) eq_refl) in Htz.
    now apply (rngl_lt_irrefl Hor) in Htz.
  }
  set (t := circ_trigo_param θ₀).
  progress unfold rngl_dist.
  rewrite <- (rngl_opp_add_distr Hop).
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite (rngl_add_opp_l Hop).
  remember (θ₀ =? 0)%A as tzz eqn:Htzz.
  symmetry in Htzz.
  destruct tzz. {
    exfalso.
    apply angle_eqb_eq in Htzz; subst θ₀.
    rewrite angle_eucl_dist_symmetry in Hze.
    rewrite angle_eucl_dist_0_straight in Hze.
    apply rngl_nle_gt in Hze.
    apply Hze; clear Hze.
    apply (rngl_le_min_r Hor).
  }
  apply angle_eqb_neq in Htzz, Htzs.
  move Htzz after Htzs.
  progress unfold t.
  rewrite fold_param_sin; [ | easy ].
  rewrite fold_param_cos; [ | easy ].
  rewrite <- rngl_param_sin.
  rewrite <- rngl_param_cos.
  remember (rngl_sin θ₀) as x.
  remember ((rngl_cos θ₀ + 1) / _)%L as y.
  progress unfold rngl_abs.
  rewrite (rngl_leb_sub_0 Hop Hor).
  remember (x ≤? y)%L as xy eqn:Hxy.
  subst x y.
  symmetry in Hxy.
  destruct xy. {
    apply rngl_leb_le in Hxy.
    rewrite (rngl_opp_sub_distr Hop).
...
Check rngl_cos_lt_angle_eucl_dist_lt.
apply rngl_cos_lt_angle_eucl_dist_lt in Hze.
rewrite rngl_cos_sub_straight_r in Hze.
apply (rngl_lt_opp_r Hop Hor) in Hze.
rewrite <- (rngl_add_sub_swap Hop) in Hze.
apply -> (rngl_lt_sub_0 Hop Hor) in Hze.
(* ouais, chais pas *)
...
Check angle_le_angle_eucl_dist_le.
Check angle_eucl_dist_is_2_mul_sin_sub_div_2.
Check angle_eucl_dist_is_sqrt.
...4
enough (H :
  ∃ η : T,
  (0 < η)%L ∧
  ∀ θ : angle T,
  (0 < angle_eucl_dist θ θ₀ < η)%L
  → (rngl_dist ((param_cos θ - param_cos θ₀) / angle_eucl_dist θ θ₀)
       (- param_sin θ₀) < ε)%L). {
  destruct H as (η & Hη & H1).
  move η before ε.
  exists (rngl_min η 2).
  split. {
    apply rngl_min_glb_lt; [ easy | ].
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  intros θ (Htz, Hze).
  progress unfold param_cos.
  progress unfold param_sin.
  remember (θ =? angle_straight)%A as ts eqn:Hts.
  remember (θ₀ =? angle_straight)%A as tzs eqn:Htzs.
  symmetry in Hts, Htzs.
  destruct ts. {
    apply angle_eqb_eq in Hts; subst θ.
    destruct tzs. {
      apply angle_eqb_eq in Htzs; subst θ₀.
      rewrite (proj2 (angle_eucl_dist_separation _ _) eq_refl) in Htz.
      now apply (rngl_lt_irrefl Hor) in Htz.
    }
    set (t := circ_trigo_param θ₀).
    progress unfold rngl_dist.
    rewrite <- (rngl_opp_add_distr Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_div_opp_l Hop Hiv).
    rewrite (rngl_add_opp_l Hop).
    remember (θ₀ =? 0)%A as tzz eqn:Htzz.
    symmetry in Htzz.
    destruct tzz. {
      exfalso.
      apply angle_eqb_eq in Htzz; subst θ₀.
      rewrite angle_eucl_dist_symmetry in Hze.
      rewrite angle_eucl_dist_0_straight in Hze.
      apply rngl_nle_gt in Hze.
      apply Hze; clear Hze.
      apply (rngl_le_min_r Hor).
    }
    apply angle_eqb_neq in Htzz, Htzs.
    move Htzz after Htzs.
    progress unfold t.
    rewrite fold_param_sin; [ | easy ].
    rewrite fold_param_cos; [ | easy ].
    rewrite <- rngl_param_sin.
    rewrite <- rngl_param_cos.
...
  ============================
  (rngl_abs (rngl_sin θ₀ - (rngl_cos θ₀ + 1) / angle_eucl_dist angle_straight θ₀) < ε)%L
...
rewrite angle_eucl_dist_is_sqrt.
rewrite rngl_cos_sub_straight_r.
rewrite (rngl_sub_opp_r Hop).
...
remember ((1 - _²) / _)%L as y.
rewrite rngl_sub_add_distr.
...
*)

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

Theorem angle_mul_2_div_2 :
  ∀ θ, (θ < angle_straight → (2 * θ) /₂ = θ)%A.
Proof.
intros * Hts.
rewrite <- angle_mul_nat_div_2; [ apply angle_div_2_mul_2 | cbn ].
rewrite angle_add_0_r.
rewrite Bool.orb_false_r.
now apply angle_lt_straight_add_same_not_overflow.
Qed.

(* to be completed
Theorem rngl_cos_derivative :
  ∀ θ₀, θ₀ ≠ 0%A →
  derivative_at angle_eucl_dist rngl_dist rngl_cos
    (λ θ, (- rngl_sin θ)%L) θ₀.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀ Hθ ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros θ₀ Htz ε Hε.
clear Htz. (* AAAAAAA VOIR ..... *)
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ dθ,
  (0 < angle_eucl_dist dθ 0 < η)%L
  → (rngl_dist
        ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_eucl_dist dθ 0)
        (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hη & Hd).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  remember (θ - θ₀)%A as dθ eqn:H.
  symmetry in H.
  apply angle_sub_move_r in H.
  subst θ.
  specialize (Hd dθ).
  rewrite angle_eucl_dist_move_0_r in Hθ |-*.
  rewrite angle_add_sub in Hθ |-*.
  rewrite angle_add_comm.
  now apply Hd.
}
specialize rngl_sin_is_continuous as Hsc.
progress unfold continuous in Hsc.
progress unfold continuous_at in Hsc.
progress unfold is_limit_when_tending_to in Hsc.
specialize (Hsc θ₀ ε Hε).
destruct Hsc as (η1 & Hη1 & Hsc).
move η1 before ε.
enough (H :
  ∃ η : T, (0 < η)%L ∧
  ∀ dθ : angle T,
  (0 < angle_eucl_dist dθ 0 < η)%L
  → (rngl_dist
       ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_eucl_dist dθ 0)
       (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hη & Hd).
clear Hd.
(* delete η one day *)
  move η before ε.
  move Hη before Hε.
  destruct (angle_lt_dec θ₀ angle_straight) as [Hts| Hts]. {
    exists (rngl_min (angle_eucl_dist θ₀ angle_straight) (rngl_min η1 η)).
    split. {
      apply rngl_min_glb_lt. {
        apply angle_eucl_dist_pos_angle_neq.
        intros H.
        rewrite H in Hts.
        now apply angle_lt_irrefl in Hts.
      }
      now apply (rngl_min_glb_lt).
    }
    intros dθ Hdθ.
    progress unfold rngl_dist.
    rewrite (rngl_sub_opp_r Hop).
    rewrite rngl_cos_sub_cos.
    remember (angle_add_overflow (θ₀ + dθ) θ₀) as ovt eqn:Hovt.
    remember (θ₀ + dθ <? θ₀)%A as tt eqn:Htt.
    symmetry in Hovt, Htt.
    destruct (angle_le_dec dθ angle_straight) as [Htds| Htds]. {
      destruct tt. {
        exfalso.
        apply angle_nle_gt in Htt.
        apply Htt; clear Htt.
        (* lemma *)
        rewrite <- (angle_add_0_r θ₀) at 1.
        apply angle_add_le_mono_l; [ | apply angle_nonneg ].
        now apply angle_add_not_overflow_lt_straight_le_straight.
      }
      apply angle_ltb_ge in Htt.
      rewrite angle_add_sub_swap.
      rewrite angle_sub_diag.
      rewrite angle_add_0_l.
      rewrite angle_add_0_r.
      rewrite (angle_add_comm θ₀).
      rewrite <- angle_add_assoc.
      rewrite <- angle_mul_2_l.
      destruct ovt. 2: {
        rewrite angle_add_0_r.
        rewrite angle_div_2_add_not_overflow. 2: {
          rewrite angle_mul_2_l.
          rewrite angle_add_comm in Hovt.
          rewrite angle_add_not_overflow_move_add; [ easy | | easy ].
          rewrite angle_add_overflow_comm.
          apply angle_ltb_ge in Htt.
          now rewrite <- angle_add_overflow_equiv2.
        }
        rewrite (rngl_sin_angle_eucl_dist' (dθ/₂)). 2: {
          apply angle_div_2_le_straight.
        }
        rewrite angle_mul_2_div_2; [ | easy ].
        rewrite angle_div_2_mul_2.
        rewrite (rngl_mul_div_assoc Hiv).
        rewrite (rngl_div_opp_l Hop Hiv).
        rewrite (rngl_div_div_swap Hic Hiv).
        rewrite (rngl_mul_div Hi1). 2: {
          intros H.
          rewrite H in Hdθ.
          destruct Hdθ as (H1, _).
          now apply (rngl_lt_irrefl Hor) in H1.
        }
        rewrite <- (rngl_div_opp_l Hop Hiv).
        rewrite (rngl_mul_comm Hic).
        rewrite <- (rngl_mul_opp_l Hop).
        rewrite (rngl_mul_div Hi1). 2: {
          apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
        }
        rewrite <- (rngl_abs_opp Hop Hor).
        rewrite (rngl_opp_add_distr Hop).
        rewrite (rngl_sub_opp_r Hop).
        rewrite (rngl_add_opp_l Hop).
        rewrite angle_add_comm.
        specialize (Hsc (θ₀ + dθ /₂))%A.
        rewrite angle_eucl_dist_move_0_r in Hsc.
        rewrite angle_add_comm, angle_add_sub in Hsc.
        rewrite angle_add_comm.
        apply Hsc.
        apply (rngl_lt_le_trans Hor _ (rngl_min η1 η)). {
          apply (rngl_le_lt_trans Hor _ (angle_eucl_dist dθ 0)). {
            apply angle_le_angle_eucl_dist_le; [ | easy | ]. 2: {
              apply angle_div_2_le.
            }
            apply angle_div_2_le_straight.
          }
          eapply (rngl_lt_le_trans Hor); [ apply Hdθ | ].
          apply (rngl_le_min_r Hor).
        }
        apply (rngl_le_min_l Hor).
      }
      rewrite angle_div_2_add_overflow. 2: {
        rewrite angle_mul_2_l.
        rewrite angle_add_comm in Hovt.
        rewrite angle_add_overflow_move_add; [ easy | | easy ].
        now apply angle_lt_straight_add_same_not_overflow.
      }
      rewrite <- angle_add_assoc.
      rewrite angle_straight_add_straight.
      rewrite angle_add_0_r.
      rewrite angle_mul_2_div_2; [ | easy ].
      rewrite (rngl_sin_angle_eucl_dist' (dθ/₂)). 2: {
        apply angle_div_2_le_straight.
      }
      rewrite angle_div_2_mul_2.
      rewrite (rngl_mul_comm Hic).
      rewrite rngl_mul_assoc.
      rewrite (rngl_div_mul Hon Hiv). 2: {
        apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
      }
      rewrite (rngl_mul_comm Hic).
      rewrite (rngl_div_opp_l Hop Hiv).
      rewrite (rngl_mul_div Hi1). 2: {
        intros H.
        destruct Hdθ as (H1, _).
        rewrite H in H1.
        now apply (rngl_lt_irrefl Hor) in H1.
      }
      rewrite <- (rngl_abs_opp Hop Hor).
      rewrite (rngl_opp_add_distr Hop).
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_l Hop).
      apply Hsc.
      rewrite angle_eucl_dist_move_0_r.
      rewrite angle_add_sub.
      apply (rngl_lt_le_trans Hor _ (rngl_min η1 η)). {
        apply (rngl_le_lt_trans Hor _ (angle_eucl_dist dθ 0)). {
          apply angle_le_angle_eucl_dist_le; [ | easy | ]. 2: {
            apply angle_div_2_le.
          }
          apply angle_div_2_le_straight.
        }
        eapply (rngl_lt_le_trans Hor); [ apply Hdθ | ].
        apply (rngl_le_min_r Hor).
      }
      apply (rngl_le_min_l Hor).
    }
    apply angle_nle_gt in Htds.
    rewrite (angle_add_comm θ₀).
    rewrite angle_add_sub.
    rewrite <- angle_add_assoc.
    rewrite <- angle_mul_2_l.
    destruct ovt. {
      rewrite rngl_sin_add_straight_r.
      rewrite angle_add_comm in Hovt.
      apply angle_add_overflow_move_add in Hovt. 2: {
        now apply angle_lt_straight_add_same_not_overflow.
      }
      rewrite <- angle_mul_2_l in Hovt.
      rewrite angle_div_2_add. {
        rewrite Hovt.
        rewrite rngl_sin_add_straight_r.
        rewrite angle_mul_2_div_2; [ | easy ].
        rewrite (rngl_opp_involutive Hop).
        destruct tt. {
exfalso.
destruct Hdθ as (_, H1).
apply (rngl_min_glb_lt_iff Hor) in H1.
destruct H1 as (H1, _).
move Hts at bottom.
move H1 at bottom.
apply angle_nle_gt in Htds.
apply Htds; clear Htds.
Search (angle_eucl_dist _ _ < angle_eucl_dist _ _)%L.
...
apply angle_nle_gt in Htt.
apply Htt; clear Htt.
rewrite <- (angle_add_0_r θ₀) at 1.
apply angle_add_le_mono_l; [ | apply angle_nonneg ].
...
rewrite angle_add_overflow_comm.
apply (angle_add_overflow_le _ angle_straight). {
  now apply angle_lt_le_incl.
}
(*
progress unfold angle_leb.
progress unfold angle_ltb in Htds.
cbn in Htds.
rewrite (rngl_leb_refl Hor) in Htds.
*)
...
destruct Hdθ as (_, H1).
apply (rngl_min_glb_lt_iff Hor) in H1.
destruct H1 as (H1, _).
move Hts at bottom.
move H1 at bottom.
rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2.
apply angle_ltb_ge.
rewrite <- (angle_add_0_r θ₀) at 1.
apply angle_add_le_mono_l; [ | apply angle_nonneg ].
...
          rewrite rngl_sin_add_straight_r.
          rewrite (rngl_mul_opp_r Hop).
          rewrite (rngl_opp_involutive Hop).
          rewrite (rngl_sin_angle_eucl_dist' (dθ /₂)). 2: {
            apply angle_div_2_le_straight.
          }
          rewrite angle_div_2_mul_2.
          rewrite (rngl_mul_div_assoc Hiv).
          rewrite (rngl_div_div_swap Hic Hiv).
          rewrite (rngl_mul_div Hi1). 2: {
            intros H.
            rewrite H in Hdθ.
            destruct Hdθ as (H1, _).
            now apply (rngl_lt_irrefl Hor) in H1.
          }
          rewrite (rngl_mul_comm Hic).
          rewrite (rngl_mul_div Hi1). 2: {
            apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
          }
          rewrite angle_add_comm.
          progress unfold rngl_dist in Hsc.
...
      apply angle_ltb_ge in Htt.
...
      exfalso.
      apply angle_nle_gt in Htds.
      apply Htds; clear Htds.
...
    exfalso.
    destruct Hdθ as (_, H1).
    apply rngl_nle_gt in H1.
    apply H1; clear H1.
... à voir...
    apply (rngl_min_le_iff Hor).
    left.
Search (angle_eucl_dist _ _ < angle_eucl_dist _ _)%L.
    apply angle_nle_gt in Htds.
    apply Htds; clear Htds.
...
enough (H :
  ∃ η : T, (0 < η)%L ∧
  ∀ dθ : angle T,
  (0 < angle_eucl_dist dθ 0 < η)%L
  → (rngl_dist
       ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_eucl_dist dθ 0)
       (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hη & Hd).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros dθ Hdθ.
  do 2 rewrite rngl_cos_angle_eucl_dist.
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_sub_sub_swap Hop).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_add_opp_l Hop).
  rewrite <- (rngl_div_sub_distr_r Hop Hiv).
  progress unfold rngl_dist.
  rewrite (rngl_div_div_swap Hic Hiv).
  rewrite (rngl_sub_opp_r Hop).
  destruct (angle_le_dec θ₀ angle_straight) as [Hts| Hts]. {
    rewrite rngl_sin_angle_eucl_dist'; [ | easy ].
    rewrite <- (rngl_div_add_distr_r Hiv).
    rewrite angle_mul_2_l.
    rewrite (rngl_abs_div Hon Hop Hiv Hed Hor). 2: {
      apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_abs_2 Hon Hos Hor).
    apply (rngl_lt_div_l Hon Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_abs_nonneg_eq Hop Hor).
    eapply (rngl_le_lt_trans Hor). {
      apply (rngl_add_le_mono_l Hop Hor).
      apply (angle_eucl_dist_triangular _ θ₀).
    }
    rewrite (angle_eucl_dist_move_0_r (_ + _) θ₀).
    rewrite angle_add_sub.
    rewrite <- (rngl_mul_2_r Hon).
Search (rngl_cos _ - rngl_cos _ = _)%L.
Check rngl_cos_sub_cos.
...
rngl_cos_angle_eucl_dist:
  ∀ {T : Type} {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T} 
    {ac : angle_ctx T} (θ : angle T), rngl_cos θ = (1 - (angle_eucl_dist θ 0)² / 2)%L
rngl_sin_angle_eucl_dist':
  ∀ θ : angle T, (θ ≤ angle_straight)%A → rngl_sin θ = (angle_eucl_dist (2 * θ) 0 / 2)%L
...
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ,
  (0 < angle_eucl_dist θ θ₀ < η)%L
  → (rngl_dist
        ((rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀)
        (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hη & Hd).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  do 2 rewrite rngl_cos_angle_eucl_dist.
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_sub_sub_swap Hop).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_add_opp_l Hop).
  rewrite <- (rngl_div_sub_distr_r Hop Hiv).
  progress unfold rngl_dist.
  rewrite (rngl_div_div_swap Hic Hiv).
  rewrite (rngl_sub_opp_r Hop).
  destruct (angle_le_dec θ₀ angle_straight) as [Hts| Hts]. {
    rewrite rngl_sin_angle_eucl_dist'; [ | easy ].
    rewrite <- (rngl_div_add_distr_r Hiv).
    rewrite angle_mul_2_l.
    rewrite (rngl_abs_div Hon Hop Hiv Hed Hor). 2: {
      apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_abs_2 Hon Hos Hor).
    apply (rngl_lt_div_l Hon Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_abs_nonneg_eq Hop Hor).
    eapply (rngl_le_lt_trans Hor). {
      apply (rngl_add_le_mono_l Hop Hor).
      apply (angle_eucl_dist_triangular _ θ₀).
    }
    rewrite (angle_eucl_dist_move_0_r (_ + _)).
    rewrite angle_add_sub.
    rewrite <- (rngl_mul_2_r Hon).
...
Check angle_eucl_dist_is_2_mul_sin_sub_div_2.
Search (rngl_sin _ = _).
Search (angle_eucl_dist _ _ + _)%L.
(* bof, j'y arrive pas, chuis nul *)
...4
enough (H :
  if (θ₀ <? angle_straight)%A then
    ∃ η : T, (0 < η)%L ∧
    ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L
    → (rngl_dist
           ((rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀)
           (- rngl_sin θ₀) < ε)%L
  else
    ∃ η : T, (0 < η)%L ∧
    ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L
    → (rngl_dist
           ((rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀)
           (- rngl_sin θ₀) < ε)%L). {
  remember (θ₀ <? angle_straight)%A as tzs eqn:Htzs.
  symmetry in Htzs.
  destruct tzs. {
    exists (angle_eucl_dist θ₀ angle_straight)%L.
    split. {
      apply (rngl_lt_iff Hor).
      split; [ apply angle_eucl_dist_nonneg | ].
      intros H1; symmetry in H1.
      rewrite angle_eucl_dist_separation in H1; subst θ₀.
      now apply angle_lt_irrefl in Htzs.
    }
    intros θ Hθ.
    move θ before θ₀.
    (* todo: define angle_dec? *)
    remember (angle_ltb (θ + angle_right) θ₀) as tr eqn:Htr.
    symmetry in Htr.
    destruct tr. {
      exfalso.
      apply angle_nle_gt in Htr.
      apply Htr; clear Htr.
      progress unfold angle_leb.
      rewrite rngl_sin_add_right_r.
      rewrite rngl_cos_add_right_r.
      generalize Htzs; intros H1.
      apply angle_lt_le_incl in H1.
      apply rngl_sin_nonneg_angle_le_straight in H1.
      apply rngl_leb_le in H1.
      rewrite H1; clear H1.
      remember (0 ≤? rngl_cos θ)%L as zc eqn:Hzc.
      symmetry in Hzc.
      destruct zc; [ | easy ].
      apply rngl_leb_le in Hzc.
      apply rngl_leb_le.
      destruct Hθ as (Hzt, Ht).
      apply angle_eucl_dist_lt_angle_eucl_dist in Ht.
      rewrite rngl_cos_sub_straight_r in Ht.
      apply (rngl_le_opp_l Hop Hor).
      apply (rngl_lt_opp_l Hop Hor) in Ht.
(**)
      remember (θ - θ₀)%A as dθ eqn:Hd.
      apply angle_add_move_r in Hd.
      subst θ.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
        destruct (rngl_le_dec Hor 0 (rngl_cos dθ)) as [Hzcd| Hzcd]. {
          cbn.
          rewrite rngl_add_add_swap.
          rewrite (rngl_add_mul_l_diag_r Hon).
          apply (rngl_add_nonneg_nonneg Hor). {
            apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
            rewrite rngl_add_comm.
            apply (rngl_le_opp_l Hop Hor).
            apply rngl_sin_bound.
          }
          apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
          apply angle_lt_le_incl in Htzs.
          now apply rngl_sin_nonneg_angle_le_straight in Htzs.
        }
        apply (rngl_nle_gt_iff Hor) in Hzcd.
        destruct (rngl_le_dec Hor 0 (rngl_sin dθ)) as [Hzsd| Hzsd]. {
          exfalso.
          rewrite rngl_cos_add in Hzc.
          apply -> (rngl_le_0_sub Hop Hor) in Hzc.
          apply rngl_nlt_ge in Hzc.
          apply Hzc; clear Hzc.
          eapply (rngl_lt_le_trans Hor _ 0). {
            rewrite (rngl_mul_comm Hic).
            apply (rngl_mul_pos_neg Hop Hor); [ | | easy ]. 2: {
              apply (rngl_lt_iff Hor).
              split; [ easy | ].
              intros H1; symmetry in H1.
              apply eq_rngl_cos_0 in H1.
              destruct H1; subst θ₀. {
                cbn in Ht.
                rewrite rngl_add_0_l in Ht.
                apply (rngl_lt_le_incl Hor) in Ht.
                now apply rngl_nlt_ge in Ht.
              }
              cbn in Ht.
              rewrite rngl_add_0_l in Ht.
              apply (rngl_lt_le_incl Hor) in Ht.
              now apply rngl_nlt_ge in Ht.
            }
            rewrite Bool.orb_true_iff; right.
            rewrite Hi1; cbn.
            apply (rngl_has_eq_dec_or_is_ordered_r Hor).
          }
          apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
          apply angle_lt_le_incl in Htzs.
          now apply rngl_sin_nonneg_angle_le_straight.
        }
        generalize Htzs; intros Hz.
        apply angle_lt_le_incl in Hz.
        apply rngl_sin_nonneg_angle_le_straight in Hz.
        apply (rngl_nle_gt_iff Hor) in Hzsd.
        change_angle_add_r dθ angle_straight.
        progress sin_cos_add_sub_straight_hyp T Hzc.
        progress sin_cos_add_sub_straight_hyp T Ht.
        progress sin_cos_add_sub_straight_hyp T Hzt.
        progress sin_cos_add_sub_straight_hyp T Hzsd.
        progress sin_cos_add_sub_straight_hyp T Hzcd.
        progress sin_cos_add_sub_straight_goal T.
        change_angle_sub_l dθ angle_right.
        progress sin_cos_add_sub_right_hyp T Hzc.
        progress sin_cos_add_sub_right_hyp T Ht.
        progress sin_cos_add_sub_right_hyp T Hzt.
        progress sin_cos_add_sub_right_hyp T Hzsd.
        progress sin_cos_add_sub_right_hyp T Hzcd.
        progress sin_cos_add_sub_right_goal T.
        rewrite (rngl_add_opp_l Hop).
        apply (rngl_le_0_sub Hop Hor).
        rewrite rngl_sin_sub_anticomm in Hzc.
        apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzc.
        rewrite rngl_cos_sub_comm.
        change_angle_sub_l θ₀ angle_right.
        progress sin_cos_add_sub_right_hyp T Hz.
        progress sin_cos_add_sub_right_hyp T Hzcz.
        progress sin_cos_add_sub_right_hyp T Hzc.
        progress sin_cos_add_sub_right_hyp T Ht.
        progress sin_cos_add_sub_right_hyp T Hzt.
        progress sin_cos_add_sub_right_goal T.
        rewrite <- angle_sub_add_distr.
        rewrite rngl_cos_sub_right_l.
        apply -> (rngl_lt_0_sub Hop Hor) in Ht.
(* je crois que c'est faux *)
...
Search (rngl_cos (_ - _) ≤ rngl_cos _)%L.
Search (rngl_cos _ < rngl_cos (_ - _))%L.
...
            apply (rngl_lt_le_incl Hor) in Hzcd.
            now apply (rngl_mul_nonpos_nonneg Hop Hor).
          }
          eapply (rngl_le_lt_trans Hor _ 0). {
            apply (rngl_lt_le_incl Hor) in Hzcd.
            now apply (rngl_mul_nonpos_nonneg Hop Hor).
          }
...
(*
      change_angle_sub_l θ angle_straight.
      rewrite <- angle_sub_add_distr in Ht.
      progress sin_cos_add_sub_straight_hyp T Hzc.
      progress sin_cos_add_sub_straight_hyp T Ht.
      progress sin_cos_add_sub_straight_goal T.
...
*)
      change_angle_add_r θ angle_right.
      rewrite angle_sub_sub_swap in Ht.
      progress sin_cos_add_sub_right_hyp T Hzc.
      progress sin_cos_add_sub_right_hyp T Ht.
      progress sin_cos_add_sub_right_goal T.
...
Search (angle_eucl_dist _ _ < angle_eucl_dist _ _)%L.
...
    rewrite angle_cos_sub_cos_angle_eucl_dist_mul.
    rewrite (rngl_mul_comm Hic).
    rewrite (rngl_mul_div Hi1). 2: {
      destruct Hθ as (Hθ, _).
      apply (rngl_lt_iff Hor) in Hθ.
      destruct Hθ as (_, Hθ).
      now apply not_eq_sym in Hθ.
    }
(*1
    remember (Bool.eqb _ _) as b eqn:Hb.
    symmetry in Hb.
    destruct b. {
      progress unfold rngl_dist.
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_l Hop).
      specialize (angle_eucl_dist_is_2_mul_sin_sub_div_2 θ₀ (-θ)) as H1.
      rewrite angle_sub_opp_r in H1.
      rewrite angle_add_comm in H1.
      apply (f_equal (λ x, (x / 2)%L)) in H1.
      rewrite (rngl_mul_comm Hic) in H1.
      rewrite (rngl_mul_div Hi1) in H1. 2: {
        apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
      }
      rewrite <- H1; clear H1.
...1
*)
    assert (Hov : angle_add_overflow θ θ₀ = false). {
(*
rename θ₀ into θ1.
rename θ into θ2.
*)
      rewrite angle_add_overflow_comm.
      apply angle_add_not_overflow_lt_straight_le_straight; [ easy | ].
      destruct Hθ as (_, Hθ).
(*
clear ε Hε H.
     move θ2 before θ1.
*)
      move θ before θ₀.
      move Htzs at bottom.
      rewrite angle_eucl_dist_symmetry in Hθ.
      apply angle_nlt_ge.
      intros Hst.
      apply rngl_nle_gt in Hθ.
      apply Hθ; clear Hθ.
      destruct H as (η & Hzη & H).
      move η before ε.
...
specialize (H θ2).
Inspect 1.
apply (rngl_lt_le_incl Hor).
apply angle_around_straight_eucl_dist; [ easy | ].
(* à voir *)
...
Theorem glop :
  ∀ θ1 θ2 θ3,
  (θ1 < θ2 < θ3)%A
  → (θ3 < θ1 + angle_straight)%A
  → (angle_eucl_dist θ1 θ2 < angle_eucl_dist θ1 θ3)%L.
Proof.
(* en fait c'est faux : par exemple si θ1, θ2 et θ3 sont
   dans le premier quadrant *)
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * (H12, H23) H31.
progress unfold angle_ltb in H12.
progress unfold angle_ltb in H23.
progress unfold angle_ltb in H31.
rewrite rngl_sin_add_straight_r in H31.
rewrite rngl_cos_add_straight_r in H31.
rewrite (rngl_leb_0_opp Hop Hor) in H31.
(*2*)
apply angle_eucl_dist_lt_angle_eucl_dist.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
destruct zs2. {
  destruct zs1; [ | easy ].
  destruct zs3. {
    apply rngl_ltb_lt in H12, H23.
    apply rngl_leb_le in Hzs1, Hzs2, Hzs3.
    remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
    symmetry in Hs1z.
    destruct s1z. {
      apply rngl_leb_le in Hs1z.
      apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
      clear Hs1z.
      apply eq_rngl_sin_0 in Hzs1.
      destruct Hzs1; subst θ1; [ now do 2 rewrite angle_sub_0_l | ].
      exfalso.
      apply rngl_ltb_lt in H31.
      apply rngl_nle_gt in H31.
      apply H31; clear H31; cbn.
      rewrite (rngl_opp_involutive Hop).
      apply rngl_cos_bound.
    }
    clear H31.
    apply (rngl_leb_gt Hor) in Hs1z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
        destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hzc3]. {
          apply (rngl_lt_iff Hor).
          split. {
(*
            do 2 rewrite rngl_cos_sub.
            apply (rngl_le_sub_le_add_r Hop Hor).
            rewrite <- (rngl_add_sub_assoc Hop).
            rewrite <- (rngl_mul_sub_distr_l Hop).
            apply (rngl_le_add_le_sub_l Hop Hor).
            rewrite <- (rngl_mul_sub_distr_l Hop).
            destruct (rngl_le_dec Hor (rngl_cos θ1) (rngl_cos θ2))
                as [Hc12| Hc12]. {
            apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
*)
rngl_cos _ ≤ rngl_cos _)%L.
...
      do 2 rewrite rngl_cos_sub.
      apply (rngl_add_lt_compat Hop Hor). {
        now apply (rngl_mul_lt_mono_pos_l Hop Hor Hii).
      }
      apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ easy | ].
...
      apply (rngl_lt_trans Hor _ (rngl_sin θ2)). {
        apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy.
...
      apply (rngl_lt_le_incl Hor).
      now apply glop.
...
specialize (angle_eucl_dist_triangular θ1 angle_straight θ2) as H1.
apply (rngl_nle_gt_iff Hor) in Hθ.
apply Hθ; clear Hθ.
eapply (rngl_le_trans Hor).
...
      assert (H1 : (angle_straight - θ1 < θ2 - θ1)%A). {
...
        destruct Hθ as (H1, H2).
        move Htzs before Hst.
        (* lemma *)
        progress unfold angle_ltb in Htzs.
        progress unfold angle_ltb in Hst.
        progress unfold angle_ltb.
        cbn in Htzs.
        rewrite (rngl_leb_refl Hor) in Htzs.
        cbn in Hst.
        rewrite (rngl_leb_refl Hor) in Hst.
        rewrite rngl_sin_sub_straight_l.
        rewrite rngl_cos_sub_straight_l.
        remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
        symmetry in Hzs1.
        destruct zs1; [ | easy ].
        apply rngl_leb_le in Hzs1.
        apply rngl_ltb_lt in Htzs.
        apply (rngl_lt_iff Hor) in Htzs.
        destruct Htzs as (_, Hco1).
        apply not_eq_sym in Hco1.
        remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
        symmetry in Hzs2.
        destruct zs2; [ | clear Hst ]. {
          exfalso.
          apply rngl_ltb_lt in Hst.
          apply rngl_nle_gt in Hst.
          apply Hst, rngl_cos_bound.
        }
        apply (rngl_leb_gt Hor) in Hzs2.
        progress unfold angle_eucl_dist in H2.
        rewrite rngl_cos_straight in H2.
        rewrite rngl_sin_straight in H2.
        rewrite (rngl_sub_0_l Hop) in H2.
        progress unfold rl_modl in H2.
        rewrite <- (rngl_opp_add_distr Hop) in H2.
        do 2 rewrite (rngl_squ_opp Hop) in H2.
        rewrite (rngl_add_comm _ 1) in H2.
        rewrite (rngl_squ_add Hic Hon) in H2.
        rewrite (rngl_squ_1 Hon) in H2.
        rewrite (rngl_mul_1_r Hon) in H2.
        rewrite <- rngl_add_assoc in H2.
        rewrite cos2_sin2_1 in H2.
        rewrite rngl_add_add_swap in H2.
...
        remember (0 ≤? rngl_sin (θ2 - θ1))%L as zs21 eqn:Hzs21.
        symmetry in Hzs21.
        destruct zs21; [ | easy ].
        apply rngl_leb_le in Hzs21.
        apply rngl_ltb_lt.
Search (rngl_cos _ + rngl_cos _ < 0)%L.
rewrite rngl_cos_sub.
...
Search (_ + _ < _ + _)%A.
Search (_ - _ < _ - _)%A.
Search (_ - _ < _)%A.
Search (_ < _ - _)%A.
Search (_ < _ + _)%A.
...
      rewrite (angle_eucl_dist_symmetry θ₀) in Hθ.
      do 2 rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2 in Hθ.
...
      progress unfold angle_leb.
      cbn.
      rewrite (rngl_leb_refl Hor).
      remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
      symmetry in Hzs.
      destruct zs; [ apply rngl_leb_le, rngl_cos_bound | exfalso ].
      apply (rngl_leb_gt Hor) in Hzs.
      destruct Hθ as (H1, H2).
do 2 rewrite angle_eucl_dist_is_sqrt in H2.
...
      do 2 rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2 in H2.
      rewrite <- (rngl_mul_div_assoc Hiv) in H2.
      apply (rngl_mul_lt_mono_pos_l Hop Hor Hii) in H2. 2: {
        apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
      }
      do 2 rewrite angle_div_2_sub in H2.
      generalize Htzs; intros H3.
      apply angle_nle_gt in H3.
      apply Bool.not_true_iff_false in H3.
      rewrite H3 in H2; clear H3.
      rewrite angle_straight_div_2 in H2.
      rewrite <- (angle_add_sub_swap (θ₀ /₂))in H2.
      rewrite <- angle_add_sub_assoc in H2.
      rewrite angle_straight_sub_right in H2.
      rewrite rngl_sin_add_right_r in H2.
      remember (θ₀ ≤? θ)%A as tt eqn:Htt.
      symmetry in Htt.
      destruct tt. {
        rewrite rngl_sin_sub in H2.
        cbn in H2.
        generalize Hzs; intros H3.
        apply (rngl_leb_gt Hor) in H3.
        rewrite H3 in H2; clear H3.
        rewrite (rngl_mul_opp_l Hop) in H2.
        rewrite (rngl_mul_1_l Hon) in H2.
        remember (0 ≤? rngl_sin θ₀)%L as zz eqn:Hzz.
        symmetry in Hzz.
        destruct zz. 2: {
          progress unfold angle_ltb in Htzs.
          cbn in Htzs.
          rewrite (rngl_leb_refl Hor) in Htzs.
          now rewrite Hzz in Htzs.
        }
        rewrite (rngl_mul_1_l Hon) in H2.
        rewrite (rngl_mul_opp_l Hop) in H2.
        rewrite (rngl_sub_opp_r Hop) in H2.
Search (√_ * √_ + _)%L.
...
Check angle_eucl_dist_is_2_mul_sin_sub_div_2.
Check angle_eucl_dist_is_sqrt.
...
Search angle_ltb.
Check angle_le_angle_eucl_dist_le.
(* θ-θ₀ ≤ π-θ₀ *)
...
      change_angle_add_r θ1 angle_straight.
      rewrite rngl_sin_sub_straight_r in Hzs1.
      apply (rngl_leb_gt Hor) in Hzs1.
      apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
      rewrite rngl_cos_sub_straight_r.
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_r Hop).
Search (angle_eucl_dist (_ - _)).
rewrite angle_eucl_dist_move_0_r.
rewrite angle_sub_sub_swap.
rewrite <- angle_eucl_dist_move_0_r.
Search (angle_eucl_dist angle_straight _).
Check angle_eucl_dist_2_mul_sqrt_sub_sqrt.
...
Search (- _ < 0)%L.

Search (_ ≤? - _)%L.
rewrite rngl_leb_0_opp in Hzs1.
...
...
Search (√ _ + √ _)%L.
About rngl_sin_nonneg_sin_nonneg_add_1_cos_add_add.
...
destruct_ac.
intros.
rewrite angle_eucl_dist_is_sqrt.
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_0_le_2 Hon Hos Hor).
} {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
Arguments rngl_squ_sqrt {T ro rp rl} Hon a%_L.
rewrite <- (rngl_squ_sqrt Hon 2) at 2. 2: {
  apply (rngl_0_le_2 Hon Hos Hor).
}
progress unfold rngl_squ.
rewrite <- rngl_mul_assoc.
f_equal.
rewrite <- (rl_sqrt_squ Hon Hop Hor).
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (rngl_0_le_2 Hon Hos Hor).
} {
  apply (rngl_squ_nonneg Hos Hor).
}
f_equal.
specialize (cos2_sin2_1 ((θ1 - θ2) /₂)) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite angle_div_2_sub.
remember (θ2 ≤? θ1)%A as t21 eqn:Ht21.
symmetry in Ht21.
destruct t21. {
  rewrite (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_sub_sub_distr Hop).
  f_equal.
  symmetry.
  apply (rngl_sub_move_0_r Hop).
  rewrite (rngl_sub_sub_swap Hop).
  do 2 rewrite rngl_cos_sub.
  rewrite (rngl_sub_add_distr Hos).
  cbn.
  remember (rngl_cos θ1) as c1 eqn:Hco1.
  remember (rngl_cos θ2) as c2 eqn:Hco2.
  remember (rngl_sin θ1) as s1 eqn:Hsi1.
  remember (rngl_sin θ2) as s2 eqn:Hsi2.
  move c2 before c1; move s1 before c2; move s2 before s1.
  remember (0 ≤? s1)%L as zs1 eqn:Hzs1.
  remember (0 ≤? s2)%L as zs2 eqn:Hzs2.
  symmetry in Hzs1, Hzs2.
  destruct zs1. {
    rewrite (rngl_mul_1_l Hon).
    destruct zs2. {
      rewrite (rngl_mul_1_l Hon).
...
rewrite angle_add_overflow_comm.
apply angle_add_not_overflow_lt_straight_le_straight; [ easy | ].
destruct Hθ as (H1, H2).
apply angle_nlt_ge.
intros Hst.
apply (rngl_nle_gt_iff Hor) in H2.
apply H2; clear H2.
apply (rngl_le_div_l Hon Hop Hiv Hor). {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
rewrite (rngl_mul_2_r Hon).
eapply (rngl_le_trans Hor). {
  apply angle_eucl_dist_triangular with (θ2 := θ).
}
rewrite angle_eucl_dist_symmetry.
apply (rngl_add_le_mono_l Hop Hor).
...
apply angle_eucl_dist_lt_angle_eucl_dist in H2.
rewrite rngl_cos_sub_straight_r in H2.
...
apply angle_eucl_dist_pos_angle_neq in H1.
apply (rngl_lt_opp_l Hop Hor) in H2.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; [ apply rngl_leb_le, rngl_cos_bound | ].
exfalso.
apply rngl_leb_nle in Hzs.
apply Hzs; clear Hzs.
move Htzs at bottom.
progress unfold angle_ltb in Htzs.
cbn in Htzs.
rewrite (rngl_leb_refl Hor) in Htzs.
remember (0 ≤? rngl_sin θ₀)%L as zz eqn:Hzz.
symmetry in Hzz.
destruct zz; [ | easy ].
apply rngl_leb_le in Hzz.
apply rngl_ltb_lt in Htzs.
apply (rngl_lt_iff Hor) in Htzs.
destruct Htzs as (_, Hc).
apply not_eq_sym in Hc.
destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hcz| Hcz]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hct| Hct]. {
    apply (rngl_nlt_ge_iff Hor).
    intros Hsz.
    rewrite rngl_cos_sub in H2.
    change_angle_opp θ.
    progress sin_cos_opp_hyp T H2.
    progress sin_cos_opp_hyp T Hsz.
    progress sin_cos_opp_hyp T Hct.
...
    change_angle_add_r θ angle_right.
    progress sin_cos_add_sub_right_hyp T H2.
    progress sin_cos_add_sub_right_hyp T Hsz.
    progress sin_cos_add_sub_right_hyp T Hct.
...
      apply angle_add_not_overflow_iff.
      destruct Hθ as (H1, H2).
      apply angle_eucl_dist_lt_angle_eucl_dist in H2.
      rewrite rngl_cos_sub_straight_r in H2.
      apply angle_eucl_dist_pos_angle_neq in H1.
      destruct (angle_eq_dec θ 0) as [Htz| Htz]; [ now left | right ].
      apply (rngl_lt_opp_l Hop Hor) in H2.
(*
rewrite rngl_cos_sub in H2.
rewrite rngl_add_assoc in H2.
rewrite (rngl_add_mul_r_diag_r Hon) in H2.
*)
      progress unfold angle_ltb.
      cbn.
      rewrite (rngl_leb_0_opp Hop Hor).
      remember (0 ≤? rngl_sin θ₀)%L as zs eqn:Hzs.
      remember (rngl_sin θ ≤? 0)%L as sz eqn:Hsz.
      symmetry in Hzs, Hsz.
      destruct zs. {
        destruct sz; [ | easy ].
        apply rngl_ltb_lt.
        apply rngl_leb_le in Hzs, Hsz.
...
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L →
  (rngl_dist
     (if Bool.eqb (angle_add_overflow θ θ₀) (θ <? θ₀)%A then
        - rngl_sin ((θ + θ₀) /₂)
      else
        rngl_sin ((θ + θ₀) /₂))
     (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  rewrite angle_cos_sub_cos_angle_eucl_dist_mul.
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_div Hi1). 2: {
    destruct Hθ as (Hθ, _).
    apply (rngl_lt_iff Hor) in Hθ.
    destruct Hθ as (_, Hθ).
    now apply not_eq_sym in Hθ.
  }
  now apply H.
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ dθ, (0 < angle_eucl_dist θ₀ (θ₀ + dθ) < η)%L →
  (rngl_dist
     (if Bool.eqb (angle_add_overflow θ₀ (θ₀ + dθ)) (θ₀ + dθ <? θ₀)%A then
        - rngl_sin ((2 * θ₀ + dθ) /₂)
      else
        rngl_sin ((2 * θ₀ + dθ) /₂))
     (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  specialize (H (θ - θ₀))%A.
  rewrite angle_add_sub_assoc in H.
  rewrite angle_add_comm in H.
  rewrite angle_add_sub in H.
  rewrite angle_eucl_dist_symmetry in H.
  specialize (H Hθ).
  rewrite angle_add_overflow_comm in H.
  rewrite angle_mul_2_l in H.
  rewrite angle_add_sub_assoc in H.
  rewrite (angle_add_comm _ θ) in H.
  rewrite angle_add_assoc in H.
  now rewrite angle_add_sub in H.
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ dθ, (0 < angle_eucl_dist dθ 0 < η)%L →
  (rngl_abs
     (rngl_sin θ₀ +
      (if Bool.eqb (angle_add_overflow θ₀ (θ₀ + dθ)) (θ₀ + dθ <? θ₀)%A then
         - rngl_sin ((2 * θ₀ + dθ) /₂)
       else
         rngl_sin ((2 * θ₀ + dθ) /₂))) < ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros dθ Hθ.
  rewrite angle_eucl_dist_move_0_l in Hθ.
  rewrite angle_add_comm in Hθ.
  rewrite angle_add_sub in Hθ.
  progress unfold rngl_dist.
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_comm.
  now apply H.
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L →
  (rngl_abs
     (rngl_sin θ₀ + (rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀) <
     ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  progress unfold rngl_dist.
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_comm.
  now apply H.
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L →
  let s :=
    if Bool.eqb (angle_add_overflow θ θ₀) (θ <? θ₀)%A then (-1)%L
    else 1%L
  in
  (rngl_abs (rngl_sin θ₀ + s * rngl_sin ((θ + θ₀) /₂)) < ε)%L). {
  clear - H Hor Hop Hon Hic Hi1.
  destruct H as (η & Hzη & H).
  exists η.
  split; [ easy | ].
  intros θ Hθ.
  specialize (H θ Hθ).
  cbn - [ angle_div_2 ] in H.
  destruct Hθ as (Hθ, _).
  apply (rngl_lt_iff Hor) in Hθ.
  destruct Hθ as (_, Hθ).
  apply not_eq_sym in Hθ.
  rewrite angle_cos_sub_cos_angle_eucl_dist_mul.
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_div Hi1); [ | easy ].
  destruct (Bool.eqb _ _). {
    rewrite (rngl_mul_opp_l Hop) in H.
    now rewrite (rngl_mul_1_l Hon) in H.
  } {
    now rewrite (rngl_mul_1_l Hon) in H.
  }
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L →
  let s :=
    if Bool.eqb (angle_add_overflow θ θ₀) (θ <? θ₀)%A then (-1)%L
    else 1%L
  in
  (rngl_abs (rngl_sin θ₀ + s * rngl_sin ((θ + θ₀) /₂)) < ε)%L). {
  destruct H as (η & Hzη & H1).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  specialize (H1 θ Hθ).
  cbn - [ angle_div_2 ] in H1.
  remember (angle_add_overflow θ θ₀) as ov eqn:Hov.
  remember (θ <? θ₀)%A as tt eqn:Htt.
  symmetry in Hov, Htt.
  destruct ov. {
    progress replace (Bool.eqb true tt) with tt in H1 |-*. 2: {
      now destruct tt.
    }
    destruct tt. {
      cbn - [ angle_div_2 ].
      rewrite (rngl_mul_opp_l Hop).
      rewrite (rngl_mul_1_l Hon).
      rewrite (rngl_add_opp_r Hop).
      rewrite rngl_sin_angle_div_2_add_overflow; [ | easy ].
      rewrite rngl_sin_add_straight_r.
      rewrite (rngl_sub_opp_r Hop).
      destruct Hθ as (Hzd, Hde).
      apply rngl_cos_lt_angle_eucl_dist_lt in Hde. 2: {
        now apply (rngl_lt_le_incl Hor) in Hzη.
      }
Search (rngl_cos _ + rngl_cos _ = _)%L.
...
Search (rngl_sin _ + rngl_sin _)%L.
...
Inspect 4.
...
(* bien. Bon, faut voir... *)
Check rngl_cos_lt_angle_eucl_dist_lt.
Check exists_nat_such_that_rngl_cos_close_to_1.
...
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (angle_eucl_dist θ θ₀ < η)%L →
  (rngl_abs
     ((rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀ + rngl_sin θ₀) <
     ε)%L). {
  destruct H as (η & Hη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  rewrite rngl_cos_sub_cos.
  remember (angle_add_overflow θ θ₀) as ov eqn:Hov.
  remember (θ <? θ₀)%A as tt eqn:Htt.
  symmetry in Hov, Htt.
  destruct ov. {
    destruct tt. {
      do 2 rewrite rngl_sin_add_straight_r.
      do 2 rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_mul_opp_l Hop).
      rewrite (rngl_opp_involutive Hop).
      rewrite (rngl_div_opp_l Hop Hiv).
      rewrite (rngl_add_opp_l Hop).
      rewrite <- (rngl_add_opp_r Hop).
      rewrite <- (rngl_div_opp_l Hop Hiv).
      rewrite <- (rngl_mul_opp_r Hop).
      rewrite <- rngl_sin_opp.
      rewrite angle_opp_div_2.
      rewrite angle_opp_sub_distr.
      remember (θ - θ₀ =? 0)%A as ttz eqn:Httz.
      symmetry in Httz.
      destruct ttz. {
        apply angle_eqb_eq in Httz.
        apply -> angle_sub_move_0_r in Httz; subst θ.
        now apply angle_lt_irrefl in Htt.
      }
      rewrite rngl_sin_add_straight_r.
      rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_div_opp_l Hop Hiv).
      rewrite (rngl_add_opp_r Hop).
      rewrite angle_div_2_add.
      rewrite Hov.
      rewrite rngl_sin_add_straight_r.
      rewrite angle_div_2_sub.
      generalize Htt; intros H1.
      apply angle_lt_le_incl in H1.
      rewrite H1; clear H1.
      rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_mul_opp_l Hop).
      rewrite (rngl_div_opp_l Hop Hiv).
      rewrite (rngl_sub_opp_r Hop).
      rewrite angle_add_comm.
      rewrite <- rngl_mul_assoc.
      rewrite rngl_sin_add, rngl_sin_sub.
      remember (rngl_sin (θ₀ /₂)) as a.
      remember (rngl_cos (θ₀ /₂)) as b.
      remember (rngl_sin (θ /₂)) as c.
      remember (rngl_cos (θ /₂)) as d.
      rewrite (rngl_mul_comm Hic (_ + _)).
      rewrite (rngl_squ_sub_squ' Hop).
      rewrite (rngl_mul_comm Hic (b * c)).
      rewrite (rngl_add_sub Hos).
      subst a b c d.
      cbn.
      do 4 rewrite (rngl_squ_mul Hic).
      rewrite (rngl_squ_sqrt Hon); [ | apply rngl_1_sub_cos_div_2_nonneg ].
      rewrite (rngl_squ_sqrt Hon); [ | apply rngl_1_add_cos_div_2_nonneg ].
      rewrite (rngl_squ_sqrt Hon); [ | apply rngl_1_add_cos_div_2_nonneg ].
      rewrite (rngl_squ_sqrt Hon); [ | apply rngl_1_sub_cos_div_2_nonneg ].
      replace (if _ ≤? _ then _ else _)²%L with 1%L. 2: {
        destruct (0 ≤? rngl_sin θ)%L; symmetry; [ apply (rngl_squ_1 Hon) | ].
        apply (rngl_squ_opp_1 Hon Hop).
      }
      replace (if _ ≤? _ then _ else _)²%L with 1%L. 2: {
        destruct (0 ≤? rngl_sin θ₀)%L; symmetry; [ apply (rngl_squ_1 Hon) | ].
        apply (rngl_squ_opp_1 Hon Hop).
      }
      do 2 rewrite (rngl_mul_1_l Hon).
      rewrite (rngl_mul_sub_distr_r Hop).
      do 2 rewrite <- rngl_mul_assoc.
      rewrite (rngl_div_mul Hon Hiv). 2: {
        apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
      }
      rewrite (rngl_div_mul Hon Hiv). 2: {
        apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
      }
      do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
...
      remember ((θ + q) /₂)%A as a.
  remember ((p - q) /₂)%A as b.
  move b before a.
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_opp_add_distr Hop).
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_add Hop).
  rewrite <- (rngl_opp_add_distr Hop).
  rewrite <- (rngl_mul_2_l Hon).
  rewrite <- rngl_mul_assoc.
  rewrite <- (rngl_mul_opp_r Hop).
  f_equal.
...
enough (H :
  ∃ η : T,
  (0 < η)%L ∧
  ∀ dθ : angle T,
    (angle_eucl_dist (θ₀ + dθ) θ₀ < η)%L
    → (rngl_dist
         (rngl_dist
            (rngl_cos (θ + dθ)) (rngl_cos θ) / angle_eucl_dist (θ + dθ) θ)
            (- rngl_sin θ) <
       ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  split; [ easy | ].
  intros θ' Hθ'.
  specialize (H (θ' - θ))%A.
  rewrite angle_add_sub_assoc in H.
  rewrite angle_add_sub_swap in H.
  rewrite angle_sub_diag, angle_add_0_l in H.
  now specialize (H Hθ').
}
enough (H :
  ∃ η : T,
  (0 < η)%L ∧
  ∀ dθ : angle T,
    (angle_eucl_dist (θ + dθ) θ < η)%L
    → (rngl_dist
         (rngl_abs (rngl_cos (θ + dθ) - rngl_cos θ) /
            rl_modl
              (rngl_cos (θ + dθ) - rngl_cos θ)
              (rngl_sin (θ + dθ) - rngl_sin θ))
         (- rngl_sin θ) <
       ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  split; [ easy | ].
  intros dθ Hdθ.
  specialize (H dθ Hdθ)%A.
  progress unfold rngl_dist at 2.
  (* lemma *)
  progress unfold angle_eucl_dist.
  progress unfold rl_modl.
  rewrite (rngl_squ_sub_comm Hop).
  rewrite (rngl_squ_sub_comm Hop (rngl_sin θ)).
  rewrite fold_rl_modl.
  easy.
}
enough (H :
  ∃ η : T,
  (0 < η)%L ∧
  ∀ dθ : angle T,
    (1 - η² / 2 < rngl_cos dθ)%L
  → (rngl_abs
     (rngl_sin θ +
      rngl_abs (rngl_cos (θ + dθ) - rngl_cos θ) /
      rl_modl
        (rngl_cos (θ + dθ) - rngl_cos θ)
        (rngl_sin (θ + dθ) - rngl_sin θ)) < ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros dθ Hdθ.
  rewrite angle_eucl_dist_is_sqrt in Hdθ.
  rewrite angle_sub_add_distr in Hdθ.
  rewrite angle_sub_diag in Hdθ.
  rewrite angle_sub_0_l in Hdθ.
  rewrite rngl_cos_opp in Hdθ.
  apply (rngl_lt_lt_squ Hop Hor Hii) in Hdθ; cycle 1. {
    apply (rngl_mul_comm Hic).
  } {
    apply rl_sqrt_nonneg.
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hon Hos Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_squ_sqrt Hon) in Hdθ. 2: {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hon Hos Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_mul_comm Hic) in Hdθ.
  apply (rngl_lt_div_r Hon Hop Hiv Hor) in Hdθ. 2: {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  apply (rngl_lt_sub_lt_add_r Hop Hor) in Hdθ.
  rewrite rngl_add_comm in Hdθ.
  apply (rngl_lt_sub_lt_add_r Hop Hor) in Hdθ.
  progress unfold rngl_dist.
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_comm.
  now apply H.
}
...
  specialize (H dθ Hdθ)%A.
  rewrite rngl_cos_sub_cos.
  rewrite rngl_sin_sub_sin.
  rewrite (angle_add_comm θ).
  rewrite angle_add_sub.
  rewrite <- angle_add_assoc.
  do 2 rewrite (angle_add_comm dθ).
  rewrite <- angle_mul_2_l.
  rewrite angle_div_2_add.
(**)
  rewrite fold_angle_add_overflow2.
  rewrite angle_add_overflow_equiv3.
  remember (angle_add_overflow θ dθ) as ov1 eqn:Hov1.
  remember (angle_add_overflow (θ + dθ) θ) as ov2 eqn:Hov2.
  remember (angle_add_overflow (2 * θ) dθ) as ov3 eqn:Hov3.
  symmetry in Hov1, Hov2, Hov3.
  destruct ov1. {
    rewrite rngl_sin_add_straight_r.
    destruct ov2. {
      rewrite rngl_sin_add_straight_r.
      destruct ov3. {
        rewrite rngl_sin_add_straight_r.
        rewrite <- angle_add_assoc.
        rewrite angle_straight_add_straight.
        rewrite angle_add_0_r.
        do 4 rewrite (rngl_mul_opp_r Hop).
        do 2 rewrite (rngl_opp_involutive Hop).
        rewrite angle_mul_2_l in Hov3.
...
        rewrite <- angle_mul_nat_div_2. 2: {
Search ((2 * _) /₂)%A.
Search (rngl_dist _ (- _)).
...
    rewrite angle_add_comm in Hov2.
    apply angle_add_not_overflow_move_add in Hov2. 2: {
...
    rewrite angle_add_overflow_comm in Hov2.
    rewrite <- angle_mul_2_l in Hov2.
    rewrite Hov2.
    rewrite angle_add_0_r.
...
Search ((_ * _) /₂)%A.
    rewrite <- angle_mul_nat_div_2. 2: {
      cbn.
      rewrite angle_add_0_r, Bool.orb_false_r.
      rewrite <- (angle_mul_1_l θ).
      apply angle_mul_nat_overflow_distr_add_overflow.
      cbn - [ angle_mul_nat_overflow ].
      rewrite <-<- angle_mul_2_l in Hov2.
Search (angle_add_overflow (_ + _)).
      apply angle_add_not_overflow_move_add in Hov2.
(* ouais, bon, c'est pas clair *)
...
    apply angle_mul_nat_overflow_distr_add_overflow in Hov2.
    rewrite <-<- angle_mul_2_l in Hov2.
...

Theorem rngl_cos_sub_cos :
  ∀ p q,
  (rngl_cos p - rngl_cos q =
     - (2 * rngl_sin ((p + q) /₂) * rngl_sin ((p - q) /₂)))%L.
Proof.
destruct_ac.
intros.
specialize (rngl_cos_add_cos p (q + angle_straight)) as H1.
rewrite angle_add_assoc in H1.
rewrite angle_sub_add_distr in H1.
rewrite rngl_cos_add_straight_r in H1.
rewrite (rngl_add_opp_r Hop) in H1.
(* I need a lemma angle_lt_dec *)
remember ((p + q) <? angle_straight)%A as pqs eqn:Hpqs.
symmetry in Hpqs.
destruct pqs. {
  rewrite rngl_sin_angle_div_2_add_not_overflow in H1. 2: {
    (* lemma *)
    progress unfold angle_add_overflow.
    apply Bool.andb_false_iff.
    remember (p + q ≠? 0)%A as pqz eqn:Hpqz.
    symmetry in Hpqz.
    destruct pqz; [ right | now left ].
    apply angle_leb_gt.
    apply angle_lt_opp_r; [ | now rewrite angle_opp_straight ].
    intros H.
    now apply angle_neqb_neq in Hpqz.
  }
...
    (* lemma *)
    rewrite <- angle_add_overflow_equiv3.
    progress unfold angle_add_overflow2.
    (* lemma *)
    apply Bool.not_true_iff_false.
    intros H.
    apply angle_nle_gt in H.
    apply H; clear H.
    (* end lemma *)
Search (_ ≤ _ + _)%A.
    (* lemma *)
    rewrite <- (angle_add_0_r (p + q)) at 1.
    apply angle_add_le_mono_l.
...
    apply angle_le_add_l.
    apply angle_ltb_ge.
...
    rewrite angle_add_overflow_equiv2.
    progress unfold angle_add_overflow.
    apply Bool.andb_false_iff.

Search (_ → angle_add_overflow _ _ = false).
Search (rngl_sin ((_ + _) /₂)).
...
rewrite H1; clear H1.
...
rewrite rngl_mul_assoc.
...
Print rngl_dist.
progress unfold rngl_dist.
enough (H : ...
...
Check rngl_cos_add_cos.
Search (rngl_cos _ - rngl_cos _)%L.
progress unfold angle_eucl_dist at 1.
...
*)

End a.
