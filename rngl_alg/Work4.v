(* derivation of trigonometric functions *)
(* the file AngleDeriv.v being too big, I make this
   file *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.Misc.
Require Import Main.RingLike.
Require Import Main.IterAdd.

Require Import Trigo.RealLike.
Require Import Trigo.Angle.
Require Import Trigo.AngleDiv2.
Require Import Trigo.TrigoWithoutPiExt.
Require Import Trigo.Angle_order.
Require Import Trigo.TacChangeAngle.
Require Import Trigo.AngleAddOverflowLe.
Require Import Trigo.AngleDivNat.
Require Import Trigo.SeqAngleIsCauchy.
Require Import Trigo.AngleTypeIsComplete.
Require Import Trigo.AngleAddLeMonoL.
Require Import Trigo.AngleDiv2Add.
Require Import AngleEuclDist_sin.
Require Import AngleAddOverflowEquiv.

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

Theorem rngl_sin_add_sin :
  ∀ p q,
  let c₁ := if angle_add_overflow p q then angle_straight else 0%A in
  let c₂ := if (p <? q)%A then angle_straight else 0%A in
  (rngl_sin p + rngl_sin q =
      2 * rngl_sin ((p + q) /₂ + c₁) * rngl_cos ((p - q) /₂ + c₂))%L.
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
  rewrite (rngl_add_opp_r Hop).
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_opp_add_distr Hop).
  do 2 rewrite <- (rngl_add_sub_swap Hop).
  rewrite (rngl_add_opp_l Hop).
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
    rewrite rngl_sin_add_straight_r.
    rewrite angle_add_0_r.
    now rewrite <- (rngl_mul_opp_l Hop).
  } {
    apply Bool.not_true_iff_false in Hqp.
    apply angle_nle_gt in Hqp.
    rewrite Hqp.
    rewrite rngl_cos_add_straight_r.
    rewrite angle_add_0_r.
    now rewrite (rngl_mul_opp_r Hop).
  }
} {
  do 2 rewrite angle_add_0_r.
  rewrite rngl_sin_add, rngl_sin_sub.
  remember ((p + q) /₂)%A as a.
  remember ((p - q) /₂)%A as b.
  move b before a.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite (rngl_add_sub Hos).
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

(* min max on angles *)

Definition angle_min θ1 θ2 := if (θ1 ≤? θ2)%A then θ1 else θ2.
Definition angle_max θ1 θ2 := if (θ1 ≤? θ2)%A then θ2 else θ1.

Theorem angle_le_min_l : ∀ θ1 θ2, (angle_min θ1 θ2 ≤ θ1)%A.
Proof.
intros.
progress unfold angle_min.
remember (θ1 ≤? θ2)%A as t12 eqn:Ht12.
symmetry in Ht12.
destruct t12; [ apply angle_le_refl | ].
apply angle_leb_gt in Ht12.
now apply angle_lt_le_incl in Ht12.
Qed.

Theorem angle_le_min_r : ∀ θ1 θ2, (angle_min θ1 θ2 ≤ θ2)%A.
Proof.
intros.
progress unfold angle_min.
remember (θ1 ≤? θ2)%A as t12 eqn:Ht12.
symmetry in Ht12.
destruct t12; [ easy | apply angle_le_refl ].
Qed.

Theorem angle_min_l_iff :
  ∀ θ1 θ2, angle_min θ1 θ2 = θ1 ↔ (θ1 ≤ θ2)%A.
Proof.
intros.
progress unfold angle_min.
split; intros H12; [ | now rewrite H12 ].
remember (θ1 ≤? θ2)%A as t12 eqn:Ht12.
symmetry in Ht12.
destruct t12; [ easy | ].
subst θ2.
apply angle_leb_gt in Ht12.
now apply angle_lt_irrefl in Ht12.
Qed.

Theorem angle_min_r_iff :
  ∀ θ1 θ2, angle_min θ1 θ2 = θ2 ↔ (θ2 ≤ θ1)%A.
Proof.
intros.
progress unfold angle_min.
remember (θ1 ≤? θ2)%A as t12 eqn:Ht12.
symmetry in Ht12.
split; intros H12. {
  destruct t12; [ now subst θ2 | ].
  apply angle_leb_gt in Ht12.
  now apply angle_lt_le_incl in Ht12.
} {
  destruct t12; [ | easy ].
  now apply angle_le_antisymm.
}
Qed.

(* end min max *)

Definition angle_lt_sub θ1 θ2 θ3 := (0 < θ1 - θ2 < θ3)%A.

Definition old_is_limit_when_tending_to_neighbourhood {A B} da db lt_suba
     (f : A → B) (x₀ : A) (L : B) :=
  (∀ ε, 0 < ε → ∃ (η : A) ζ, 0 < ζ ∧
   ∀ x : A, lt_suba x x₀ η → 0 < da x x₀ < ζ → db (f x) L < ε)%L.

Definition old_derivative_at {A} (da : A → A → T) (db : T → T → T) lt_suba f f' a :=
  let g x := ((f x - f a) / da x a)%L in
  old_is_limit_when_tending_to_neighbourhood da db lt_suba g a (f' a).

Definition old_is_derivative {A} (da : A → A → T) (db : T → T → T) lt_suba f f' :=
  ∀ a, old_derivative_at da db lt_suba f f' a.

Theorem is_derivative_iff :
  ∀ f (f' : angle T → T) dist,
   old_is_derivative angle_eucl_dist dist angle_lt_sub f f'
   ↔ is_derivative angle_eucl_dist dist angle_lt_sub f f'.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as Hc.
  intros.
  split. {
    intros H θ₀ ε Hε.
    rewrite (Hc ε) in Hε.
    now apply (rngl_lt_irrefl Hor) in Hε.
  }
  intros H θ₀ ε Hε.
  rewrite (Hc ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros.
progress unfold angle_lt_sub.
split; intros Hff. {
  intros θ₀ ε Hε.
  specialize (Hff θ₀ ε Hε).
  destruct Hff as (η & ζ & Hζ & Hff).
  exists (angle_min η (rngl_acos (1 - ζ² / 2))).
  intros θ Hθ.
  apply Hff. {
    split; [ apply Hθ | ].
    eapply angle_lt_le_trans; [ apply Hθ | ].
    apply angle_le_min_l.
  }
  rewrite angle_eucl_dist_move_0_r.
  split. {
    apply (rngl_lt_iff Hor).
    split; [ apply angle_eucl_dist_nonneg | ].
    intros H; symmetry in H.
    apply angle_eucl_dist_separation in H.
    rewrite H in Hθ.
    destruct Hθ as (H1, H2).
    now apply angle_lt_irrefl in H1.
  }
  destruct Hθ as (H1, H2).
  apply rngl_cos_lt_angle_eucl_dist_lt. {
    now apply (rngl_lt_le_incl Hor) in Hζ.
  }
  rewrite angle_sub_0_l.
  rewrite rngl_cos_opp.
  destruct (rngl_le_dec Hor (1 - ζ² / 2)² 1) as [Hz1| Hz1]. {
    rewrite <- (rngl_cos_acos (1 - _))%L. 2: {
      now apply (rngl_squ_le_1_if Hon Hop Hor Hii).
    }
    apply rngl_cos_decr_lt.
    split. {
      eapply angle_lt_le_trans; [ apply H2 | ].
      apply angle_le_min_r.
    }
    apply rngl_sin_nonneg_angle_le_straight.
    rewrite rngl_sin_acos. {
      apply rl_sqrt_nonneg.
      now apply (rngl_le_0_sub Hop Hor).
    }
    now apply (rngl_squ_le_1_if Hon Hop Hor Hii).
  }
  exfalso.
  apply Hz1; clear Hz1.
  apply (rngl_squ_le_1 Hon Hop Hor).
  split. 2: {
    apply (rngl_le_sub_le_add_l Hop Hor).
    apply (rngl_le_add_l Hor).
    apply (rngl_div_nonneg Hon Hop Hiv Hor). {
      apply (rngl_squ_nonneg Hos Hor).
    }
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  apply (rngl_le_opp_l Hop Hor).
  rewrite (rngl_add_sub_assoc Hop).
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  rewrite fold_rngl_squ.
  apply (rngl_le_le_squ Hop Hor Hii). {
    now apply (rngl_lt_le_incl Hor) in Hζ.
  }
  progress unfold rngl_acos in H2.
  fold Hor in H2.
  destruct (rngl_le_dec Hor _ _) as [Hz1| Hz1]. {
    clear H2.
    apply (rngl_nlt_ge_iff Hor).
    intros H2.
    apply rngl_nlt_ge in Hz1.
    apply Hz1; clear Hz1.
    rewrite <- (rngl_squ_1 Hon) at 1.
    apply (rngl_abs_lt_squ_lt Hop Hor Hii).
    apply (rngl_mul_comm Hic).
    rewrite (rngl_abs_1 Hon Hos Hor).
    rewrite <- (rngl_abs_opp Hop Hor).
    rewrite (rngl_opp_sub_distr Hop).
    rewrite (rngl_abs_nonneg_eq Hop Hor). {
      apply (rngl_lt_add_lt_sub_r Hop Hor).
      apply (rngl_lt_div_r Hon Hop Hiv Hor). {
        apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
      }
      rewrite fold_rngl_squ.
      apply (rngl_lt_lt_squ Hop Hor Hii); [ | | easy ].
      apply (rngl_mul_comm Hic).
      apply (rngl_0_le_2 Hon Hos Hor).
    }
    apply (rngl_le_0_sub Hop Hor).
    apply (rngl_le_div_r Hon Hop Hiv Hor).
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_le_trans Hor _ 2²). {
      apply (rngl_le_div_l Hon Hop Hiv Hor).
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
      rewrite (rngl_div_diag Hon Hiq).
      apply (rngl_le_add_l Hor).
      apply (rngl_0_le_1 Hon Hos Hor).
      apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
    }
    apply (rngl_le_le_squ Hop Hor Hii).
    apply (rngl_0_le_2 Hon Hos Hor).
    now apply (rngl_lt_le_incl Hor) in H2.
  }
  exfalso.
  apply angle_nle_gt in H2.
  apply H2; clear H2.
  rewrite (proj2 (angle_min_r_iff _ _)); apply angle_nonneg.
}
intros θ₀ ε Hε.
specialize (Hff θ₀ ε Hε).
destruct Hff as (η & Hff).
exists η, 1%L.
split; [ apply (rngl_0_lt_1 Hon Hos Hc1 Hor) | ].
intros θ Hθ Hd.
now apply Hff.
Qed.

Theorem rngl_eq_is_derivative_is_derivative :
  ∀ f f' g g' dist,
  (∀ x, f x = g x)
  → (∀ x, f' x = g' x)
  → is_derivative angle_eucl_dist dist angle_lt_sub f f'
  → is_derivative angle_eucl_dist dist angle_lt_sub g g'.
Proof.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as Hc.
  intros * Hfg Hfg' Hff.
  apply is_derivative_iff in Hff.
  apply is_derivative_iff.
  intros θ ε Hε.
  specialize (Hff θ ε Hε).
  destruct Hff as (η & ζ & Hζ & Hff).
  exists η, ζ.
  split; [ easy | ].
  progress unfold angle_lt_sub.
  intros θ2 H Hθ2.
  rewrite (Hc (_ - _)%A), (Hc η) in H.
  destruct H as (H, _).
  now apply angle_lt_irrefl in H.
}
progress unfold angle_lt_sub.
intros * Hfg Hfg' Hff.
apply is_derivative_iff in Hff.
apply is_derivative_iff.
intros θ ε Hε.
specialize (Hff θ ε Hε).
destruct Hff as (η & ζ & Hζ & Hff).
exists η, ζ.
split; [ easy | ].
intros θ' Hθ' Hzθ.
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

Theorem angle_sub_le_mono_l :
  ∀ θ2 θ3 θ1,
  angle_add_overflow θ3 (- θ1) = false
  → θ1 ≠ 0%A
  → (θ1 ≤ θ2)%A
  → (θ3 - θ2 ≤ θ3 - θ1)%A.
Proof.
intros * Hov H1z H12.
apply angle_add_le_mono_l; [ easy | ].
now apply angle_opp_le_compat_if.
Qed.

Theorem angle_eucl_dist_opp_0 :
  ∀ θ, angle_eucl_dist (- θ) 0 = angle_eucl_dist θ 0.
Proof.
intros.
rewrite <- angle_opp_0 at 1.
apply angle_eucl_dist_opp_opp.
Qed.

Definition rngl_min4 a b c d :=
  rngl_min (rngl_min (rngl_min a b) c) d.

Theorem rngl_cos_derivative_lemma_1 :
  ∀ ε η θ₀ dθ,
  (∀ x : angle T,
    (angle_eucl_dist x θ₀ < η)%L
    → (rngl_abs (rngl_sin x - rngl_sin θ₀) < ε)%L)
  → (θ₀ < angle_straight)%A
  → (angle_straight < dθ)%A
  → (0 < angle_eucl_dist dθ 0)%L
  → (angle_eucl_dist dθ 0 < angle_eucl_dist θ₀ angle_straight)%L
  → (angle_eucl_dist dθ 0 < η)%L
  → (θ₀ + dθ < θ₀)%A
  → (rngl_abs
      (- (2 * rngl_sin (dθ /₂ + θ₀) * rngl_sin (dθ /₂ + angle_straight)) /
       angle_eucl_dist dθ 0 + rngl_sin θ₀) < ε)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as Hc.
  intros * Hsc Hts Htds H1 H3 H4 Htt.
  rewrite (Hc (angle_eucl_dist _ _)) in H1.
  now apply (rngl_lt_irrefl Hor) in H1.
}
intros * Hsc Hts Htds H1 H3 H4 Htt.
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
  rewrite H in H1.
  now apply (rngl_lt_irrefl Hor) in H1.
}
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_div Hi1). 2: {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
}
rewrite angle_add_comm.
clear - Hor Hop Htt Htds Hts Hsc H1 H3 H4.
move Hts at bottom.
move H3 at bottom.
progress unfold angle_ltb in Htt.
progress unfold angle_ltb in Htds.
progress unfold angle_ltb in Hts.
apply angle_eucl_dist_lt_angle_eucl_dist in H3.
rewrite rngl_cos_sub_straight_r in H3.
rewrite angle_sub_0_r in H3.
cbn in Htds, Hts.
rewrite (rngl_leb_refl Hor) in Htds, Hts.
remember (0 ≤? rngl_sin θ₀)%L as zst eqn:Hzst.
symmetry in Hzst.
destruct zst; [ | easy ].
apply rngl_leb_le in Hzst.
apply rngl_ltb_lt in Hts.
remember (0 ≤? rngl_sin dθ)%L as zsd eqn:Hzsd.
symmetry in Hzsd.
remember (0 ≤? rngl_sin (θ₀ + dθ))%L as zstd eqn:Hzstd.
symmetry in Hzstd.
destruct zstd; [ | easy ].
apply rngl_leb_le in Hzstd.
apply rngl_ltb_lt in Htt.
destruct zsd. {
  exfalso.
  apply rngl_ltb_lt in Htds.
  apply rngl_nle_gt in Htds.
  apply Htds, rngl_cos_bound.
}
clear Htds.
apply (rngl_leb_gt Hor) in Hzsd.
change_angle_add_r dθ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzsd.
progress sin_cos_add_sub_straight_hyp T Htt.
progress sin_cos_add_sub_straight_hyp T Hzstd.
progress sin_cos_add_sub_straight_hyp T H3.
rewrite angle_div_2_sub.
rewrite angle_straight_div_2.
remember (angle_straight ≤? dθ)%A as sd eqn:Hsd.
symmetry in Hsd.
destruct sd. {
  exfalso.
  (* lemma *)
  progress unfold angle_leb in Hsd.
  cbn in Hsd.
  rewrite (rngl_leb_refl Hor) in Hsd.
  generalize Hzsd; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H in Hsd; clear H.
  apply rngl_leb_le in Hsd.
  apply (rngl_lt_eq_cases Hor) in Hsd.
  destruct Hsd as [Hsd| Hsd]. {
    apply rngl_nle_gt in Hsd.
    apply Hsd, rngl_cos_bound.
  }
  apply eq_rngl_cos_opp_1 in Hsd.
  subst dθ.
  now apply (rngl_lt_irrefl Hor) in Hzsd.
}
apply angle_leb_gt in Hsd.
rewrite angle_add_assoc.
rewrite rngl_sin_add_straight_r.
rewrite <- (rngl_abs_opp Hop Hor).
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_l Hop).
apply Hsc.
rewrite angle_add_sub_assoc.
rewrite angle_eucl_dist_move_0_r.
rewrite angle_sub_sub_swap.
rewrite angle_add_sub_swap.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
eapply (rngl_le_lt_trans Hor); [ | apply H4 ].
destruct (rngl_le_dec Hor 0 (rngl_cos dθ)) as [Hzc| Hzc]. {
  apply rngl_cos_le_iff_angle_eucl_le.
  rewrite rngl_cos_sub_straight_r.
  rewrite rngl_cos_sub_right_r.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_add_nonneg_nonneg Hor); [ easy | ].
  apply rngl_sin_div_2_nonneg.
}
apply (rngl_nle_gt_iff Hor) in Hzc.
change_angle_sub_l dθ angle_straight.
rewrite angle_sub_sub_swap in H1, H4 |-*.
rewrite angle_sub_diag in H1, H4 |-*.
rewrite angle_sub_0_l in H1, H4 |-*.
progress sin_cos_add_sub_straight_hyp T Hzstd.
progress sin_cos_add_sub_straight_hyp T Htt.
progress sin_cos_add_sub_straight_hyp T Hzsd.
progress sin_cos_add_sub_straight_hyp T Hzc.
progress sin_cos_add_sub_straight_hyp T H3.
apply rngl_cos_le_iff_angle_eucl_le.
rewrite angle_div_2_sub.
rewrite angle_straight_div_2.
remember (dθ ≤? angle_straight)%A as ds eqn:Hds.
symmetry in Hds.
apply (rngl_lt_le_incl Hor) in Hzsd.
destruct ds. {
  rewrite angle_sub_sub_swap.
  rewrite angle_sub_diag, angle_sub_0_l.
  do 2 rewrite rngl_cos_opp.
  now apply rngl_cos_le_cos_div_2.
}
exfalso.
apply angle_leb_gt in Hds.
apply angle_nle_gt in Hds.
apply Hds; clear Hds.
now apply rngl_sin_nonneg_angle_le_straight.
Qed.

Theorem rngl_cos_derivative_lemma_2 :
  ∀ θ₀ dθ,
  (- rngl_cos θ₀ < rngl_cos dθ)%L
  → (0 ≤ rngl_sin θ₀)%L
  → (rngl_sin dθ < 0)%L
  → (0 ≤ rngl_sin (θ₀ + dθ))%L
  → (rngl_cos (θ₀ + dθ) ≤ rngl_cos θ₀)%L
  → False.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * H3 Hzs Hzsd Hzst Htt.
change_angle_add_r dθ angle_straight.
progress sin_cos_add_sub_straight_hyp T H3.
progress sin_cos_add_sub_straight_hyp T Htt.
progress sin_cos_add_sub_straight_hyp T Hzst.
progress sin_cos_add_sub_straight_hyp T Hzsd.
destruct (rngl_le_dec Hor 0 (rngl_cos dθ)) as [Hzcd| Hzcd]. {
  apply rngl_nlt_ge in Hzst.
  apply Hzst; clear Hzst.
  cbn.
  apply (rngl_add_nonneg_pos Hor). {
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
  apply (rngl_mul_pos_pos Hos Hor Hii); [ | easy ].
  now apply (rngl_le_lt_trans Hor _ (rngl_cos dθ)).
}
apply (rngl_nle_gt_iff Hor) in Hzcd.
change_angle_sub_l dθ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzcd.
progress sin_cos_add_sub_straight_hyp T Hzsd.
progress sin_cos_add_sub_straight_hyp T Hzst.
progress sin_cos_add_sub_straight_hyp T Htt.
progress sin_cos_add_sub_straight_hyp T H3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzc| Hzc]. {
  apply rngl_nlt_ge in Htt.
  apply Htt; clear Htt.
  rewrite rngl_cos_sub_comm.
  apply rngl_cos_lt_rngl_cos_sub; [ easy | easy | ].
  apply (rngl_lt_le_incl Hor) in Hzsd, Hzcd.
  now apply quadrant_1_sin_sub_nonneg_cos_le.
}
apply (rngl_nle_gt_iff Hor) in Hzc.
change_angle_sub_l θ₀ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs.
progress sin_cos_add_sub_straight_hyp T Hzc.
progress sin_cos_add_sub_straight_hyp T H3.
rewrite <- angle_sub_add_distr in Htt, Hzst.
progress sin_cos_add_sub_straight_hyp T Htt.
progress sin_cos_add_sub_straight_hyp T Hzst.
apply rngl_nlt_ge in Htt.
apply Htt; clear Htt.
rewrite (rngl_add_opp_l Hop).
apply (rngl_lt_0_sub Hop Hor).
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_lt_le_incl Hor) in Hzsd, Hzcd, Hzc.
  now apply quadrant_1_rngl_cos_add_le_cos_l.
}
intros H.
apply rngl_cos_eq in H.
rewrite angle_add_comm in H.
destruct H as [H| H]. {
  apply angle_add_move_r in H.
  rewrite angle_sub_diag in H.
  subst dθ.
  now apply (rngl_lt_irrefl Hor) in Hzsd.
}
apply angle_add_move_r in H.
subst dθ.
rewrite angle_add_sub_assoc in Hzst.
rewrite angle_add_opp_r in Hzst.
rewrite angle_sub_diag in Hzst.
rewrite angle_sub_0_l in Hzst.
cbn in Hzst.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzst.
apply (rngl_le_antisymm Hor) in Hzs; [ | easy ].
apply eq_rngl_sin_0 in Hzs.
destruct Hzs; subst θ₀. {
  rewrite angle_sub_0_r in Hzsd.
  cbn in Hzsd.
  rewrite (rngl_opp_0 Hop) in Hzsd.
  now apply (rngl_lt_irrefl Hor) in Hzsd.
}
rewrite rngl_sin_sub_straight_r in Hzsd.
cbn in Hzsd.
rewrite (rngl_opp_involutive Hop) in Hzsd.
now apply (rngl_lt_irrefl Hor) in Hzsd.
Qed.

Theorem rngl_cos_derivative_lemma_3 :
  ∀ ε η1 θ₀ dθ,
  (∀ x : angle T,
      (angle_eucl_dist x θ₀ < η1)%L
      → (rngl_abs (rngl_sin x - rngl_sin θ₀) < ε)%L)
  → (θ₀ < angle_straight)%A
  → (0 < angle_eucl_dist dθ 0)%L
  → (angle_eucl_dist dθ 0 < angle_eucl_dist angle_right 0)%L
  → (angle_eucl_dist dθ 0 < angle_eucl_dist θ₀ 0)%L
  → (angle_eucl_dist dθ 0 < angle_eucl_dist θ₀ angle_straight)%L
  → (angle_eucl_dist dθ 0 < η1)%L
  → angle_add_overflow (θ₀ + dθ) θ₀ = true
  → (angle_straight < dθ)%A
  → (rngl_abs
       (-
        (2 * - rngl_sin ((dθ + 2 * θ₀) /₂) *
         rngl_sin
           (dθ /₂ +
            if (θ₀ + dθ <? θ₀)%A then angle_straight else 0%A)) /
        angle_eucl_dist dθ 0 + rngl_sin θ₀) < ε)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H.
  intros * Hsc Hts H1 H2 H5 H3 H4 Hovt Htds.
  rewrite (H (angle_eucl_dist _ _)) in H1.
  now apply (rngl_lt_irrefl Hor) in H1.
}
intros * Hsc Hts H1 H2 H5 H3 H4 Hovt Htds.
remember (θ₀ + dθ <? θ₀)%A as tt eqn:Htt.
symmetry in Htt.
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
    now apply (rngl_cos_derivative_lemma_1 ε η1).
  }
  apply angle_ltb_ge in Htt.
  move Hts at bottom.
  move Htds at bottom.
  move Htt at bottom.
  progress unfold angle_ltb in Hts.
  progress unfold angle_ltb in Htds.
  progress unfold angle_leb in Htt.
  apply angle_eucl_dist_lt_angle_eucl_dist in H3.
  rewrite rngl_cos_sub_straight_r in H3.
  rewrite angle_sub_0_r in H3.
  cbn in Hts, Htds.
  rewrite (rngl_leb_refl Hor) in Hts, Htds.
  remember (0 ≤? rngl_sin θ₀)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs; [ | easy ].
  apply rngl_leb_le in Hzs.
  apply rngl_ltb_lt in Hts.
  remember (0 ≤? rngl_sin dθ)%L as zsd eqn:Hzsd.
  symmetry in Hzsd.
  destruct zsd. {
    exfalso.
    apply rngl_ltb_lt in Htds.
    apply rngl_nle_gt in Htds.
    apply Htds, rngl_cos_bound.
  }
  clear Htds.
  apply (rngl_leb_gt Hor) in Hzsd.
  remember (0 ≤? rngl_sin (θ₀ + dθ))%L as zst eqn:Hzst.
  symmetry in Hzst.
  destruct zst. {
    exfalso.
    apply rngl_leb_le in Hzst.
    apply rngl_leb_le in Htt.
    apply (rngl_cos_derivative_lemma_2 _ _ H3 Hzs Hzsd Hzst Htt).
  }
  clear Htt.
  apply (rngl_leb_gt Hor) in Hzst.
  change_angle_add_r dθ angle_straight.
  progress sin_cos_add_sub_straight_hyp T H3.
  progress sin_cos_add_sub_straight_hyp T Hzst.
  progress sin_cos_add_sub_straight_hyp T Hzsd.
  rewrite angle_sub_straight_eq_add_straight in Hovt, H4, H1 |-*.
  rewrite angle_add_0_r.
  rewrite angle_div_2_add.
  rewrite <- angle_add_overflow_equiv2.
  progress unfold angle_add_overflow2.
  progress unfold angle_ltb.
  rewrite rngl_sin_add_straight_r.
  rewrite rngl_cos_add_straight_r.
  rewrite (rngl_leb_0_opp Hop Hor).
  generalize Hzsd; intros H.
  apply (rngl_leb_gt Hor) in H.
  rewrite H; clear H.
  generalize Hzsd; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  rewrite angle_straight_div_2.
  rewrite angle_add_add_swap.
  do 2 rewrite rngl_sin_add_right_r.
  destruct (rngl_le_dec Hor 0 (rngl_cos dθ)) as [Hzd| Hzd]. {
    move H2 at bottom.
    apply angle_eucl_dist_lt_angle_eucl_dist in H2.
    do 2 rewrite angle_sub_0_r in H2.
    rewrite rngl_cos_sub_straight_r in H2.
    cbn in H2.
    apply (rngl_opp_pos_neg Hop Hor) in H2.
    now apply rngl_nle_gt in H2.
  }
  apply (rngl_nle_gt_iff Hor) in Hzd.
  change_angle_sub_l dθ angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzd.
  progress sin_cos_add_sub_straight_hyp T Hzsd.
  progress sin_cos_add_sub_straight_hyp T Hzst.
  progress sin_cos_add_sub_straight_hyp T H3.
  rewrite rngl_sin_sub_anticomm in Hzst.
  apply (rngl_opp_neg_pos Hop Hor) in Hzst.
  rewrite <- angle_add_sub_swap.
  rewrite angle_straight_add_straight.
  rewrite angle_sub_0_l.
  rewrite angle_div_2_sub.
  remember (dθ ≤? angle_straight)%A as ds eqn:Hds.
  symmetry in Hds.
  destruct ds. 2: {
    exfalso.
    apply Bool.not_true_iff_false in Hds.
    apply Hds.
    apply (rngl_lt_le_incl Hor) in Hzsd.
    now apply rngl_sin_nonneg_angle_le_straight.
  }
  rewrite <- angle_add_sub_swap in H1.
  rewrite angle_straight_add_straight in H1.
  rewrite angle_sub_0_l in H1.
  (* lemma *)
  rewrite <- angle_opp_0 in H1.
  rewrite angle_eucl_dist_opp_opp in H1.
  rewrite angle_sub_sub_swap in H2.
  rewrite angle_sub_diag, angle_sub_0_l in H2.
  rewrite <- angle_add_sub_swap in H4, Hovt.
  rewrite angle_straight_add_straight in H4, Hovt.
  rewrite angle_sub_0_l in H4, Hovt.
  rewrite angle_eucl_dist_opp_0 in H2, H4.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzc| Hzc]. {
    rewrite angle_straight_div_2.
    rewrite <- angle_sub_sub_distr.
    do 2 rewrite rngl_cos_sub_right_l.
    (* lemma *)
    rewrite <- angle_opp_0.
    rewrite angle_eucl_dist_opp_opp.
    rewrite (rngl_sin_angle_eucl_dist' (dθ /₂)). 2: {
      apply angle_div_2_le_straight.
    }
    rewrite angle_div_2_mul_2.
    rewrite (rngl_mul_div_assoc Hiv).
    rewrite <- (rngl_div_opp_l Hop Hiv).
    rewrite (rngl_div_div_swap Hic Hiv).
    rewrite (rngl_div_opp_l Hop Hiv).
    rewrite (rngl_mul_div Hi1). 2: {
      intros H.
      rewrite H in H1.
      now apply (rngl_lt_irrefl Hor) in H1.
    }
    rewrite (rngl_mul_comm Hic).
    rewrite <- (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_div Hi1). 2: {
      apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
    }
    rewrite <- (rngl_abs_opp Hop Hor).
    rewrite (rngl_opp_add_distr Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_add_opp_l Hop).
    apply (rngl_lt_le_incl Hor) in Hzsd, Hzd.
    apply quadrant_1_sin_sub_pos_cos_lt in Hzst; try easy.
    rewrite angle_sub_sub_swap in H5.
    rewrite angle_sub_diag, angle_sub_0_l in H5.
    rewrite angle_eucl_dist_opp_0 in H5.
    apply angle_eucl_dist_lt_angle_eucl_dist in H5.
    do 2 rewrite angle_sub_0_r in H5.
    now apply (rngl_lt_asymm Hor) in H5.
  }
  exfalso.
  apply (rngl_nle_gt_iff Hor) in Hzc.
  change_angle_sub_l θ₀ angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hts.
  progress sin_cos_add_sub_straight_hyp T Hzs.
  progress sin_cos_add_sub_straight_hyp T H3.
  rewrite angle_sub_sub_distr in Hzst.
  rewrite <- angle_add_sub_swap in Hzst.
  progress sin_cos_add_sub_straight_hyp T Hzst.
  progress sin_cos_add_sub_straight_hyp T Hzc.
  (* lemma *)
  apply rngl_nle_gt in Hzst.
  apply Hzst; clear Hzst.
  apply (rngl_lt_le_incl Hor) in Hzsd, Hzd, Hzc.
  now apply rngl_sin_add_nonneg.
}
Qed.

Theorem angle_eucl_dist_bound :
  ∀ θ1 θ2, (angle_eucl_dist θ1 θ2 ≤ 2)%L.
Proof.
destruct_ac.
intros.
rewrite <- (rngl_mul_1_r Hon 2).
rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2.
apply (rngl_mul_le_mono_nonneg_l Hop Hor).
apply (rngl_0_le_2 Hon Hos Hor).
apply rngl_sin_bound.
Qed.

Theorem angle_lt_asymm :
  ∀ θ1 θ2, (θ1 < θ2 → ¬ (θ2 < θ1))%A.
Proof.
intros * H12.
apply angle_lt_le_incl in H12.
now apply angle_nlt_ge in H12.
Qed.

Theorem angle_min_id : ∀ θ, angle_min θ θ = θ.
Proof.
intros.
progress unfold angle_min.
now rewrite angle_le_refl.
Qed.

Theorem angle_max_l_iff :
  ∀ θ1 θ2, angle_max θ1 θ2 = θ1 ↔ (θ2 ≤ θ1)%A.
Proof.
intros.
progress unfold angle_max.
remember (θ1 ≤? θ2)%A as t12 eqn:Ht12.
symmetry in Ht12.
split; intros H12. {
  destruct t12; [ now subst θ2 | ].
  apply angle_leb_gt in Ht12.
  now apply angle_lt_le_incl in Ht12.
} {
  destruct t12; [ | easy ].
  now apply angle_le_antisymm.
}
Qed.

Theorem angle_max_r_iff :
  ∀ θ1 θ2, angle_max θ1 θ2 = θ2 ↔ (θ1 ≤ θ2)%A.
Proof.
intros.
progress unfold angle_max.
remember (θ1 ≤? θ2)%A as t12 eqn:Ht12.
symmetry in Ht12.
destruct t12; [ easy | ].
split; [ | easy ]; intros H12.
subst θ2.
now rewrite angle_le_refl in Ht12.
Qed.

Theorem angle_max_id : ∀ θ, angle_max θ θ = θ.
Proof.
intros.
progress unfold angle_max.
now rewrite angle_le_refl.
Qed.

Theorem bool_eqb_sym : ∀ a b, Bool.eqb a b = Bool.eqb b a.
Proof. now intros; destruct a, b. Qed.

(* distance of angles which respects angle inequality *)

Definition angle_same_side θ1 θ2 :=
  Bool.eqb (θ1 ≤? angle_straight)%A (θ2 ≤? angle_straight)%A.

Definition angle_dist_greater_smaller θ1 θ2 :=
  if angle_same_side θ1 θ2 then angle_eucl_dist θ1 θ2
  else if (θ1 ≤? θ2 + angle_straight)%A then angle_eucl_dist θ1 θ2
  else (2 + angle_eucl_dist θ1 (θ2 + angle_straight))%L.

Definition angle_dist θ1 θ2 :=
  angle_dist_greater_smaller (angle_max θ1 θ2) (angle_min θ1 θ2).

Theorem angle_same_side_symmetry :
  ∀ θ1 θ2, angle_same_side θ1 θ2 = angle_same_side θ2 θ1.
Proof.
intros.
progress unfold angle_same_side.
apply bool_eqb_sym.
Qed.

Theorem angle_le_straight_same_side_straight_iff :
  ∀ θ, angle_same_side θ angle_straight = true ↔ (θ ≤ angle_straight)%A.
Proof.
intros.
progress unfold angle_same_side.
rewrite angle_le_refl.
split; intros Hss. {
  now apply -> Bool.eqb_true_iff in Hss.
}
now rewrite Hss.
Qed.

Theorem angle_gt_straight_not_same_side_0_iff :
  ∀ θ, angle_same_side θ 0 = false ↔ (angle_straight < θ)%A.
Proof.
intros.
progress unfold angle_same_side.
rewrite angle_straight_nonneg.
split; intros Hss. {
  apply Bool.eqb_false_iff in Hss.
  now apply angle_nle_gt in Hss.
}
apply angle_leb_gt in Hss.
now rewrite Hss.
Qed.

Theorem angle_same_side_id : ∀ θ, angle_same_side θ θ = true.
Proof.
intros.
progress unfold angle_same_side.
apply Bool.eqb_reflx.
Qed.

Theorem angle_le_straight_same_side_0_iff :
  ∀ θ, angle_same_side θ 0 = true ↔ (θ ≤ angle_straight)%A.
Proof.
intros.
progress unfold angle_same_side.
rewrite angle_straight_nonneg.
split; intros Hss. {
  now apply -> Bool.eqb_true_iff in Hss.
}
now rewrite Hss.
Qed.

Theorem angle_gt_straight_not_same_side_straight_iff :
  ∀ θ, angle_same_side θ angle_straight = false ↔ (angle_straight < θ)%A.
Proof.
intros.
progress unfold angle_same_side.
rewrite angle_le_refl.
split; intros Hss. {
  apply Bool.eqb_false_iff in Hss.
  now apply angle_nle_gt in Hss.
}
apply angle_leb_gt in Hss.
now rewrite Hss.
Qed.

Theorem angle_dist_symmetry :
  ∀ θ1 θ2, angle_dist θ1 θ2 = angle_dist θ2 θ1.
Proof.
destruct_ac.
intros.
progress unfold angle_dist.
progress unfold angle_min.
progress unfold angle_max.
remember (θ1 ≤? θ2)%A as t12 eqn:Ht12.
remember (θ2 ≤? θ1)%A as t21 eqn:Ht21.
symmetry in Ht12, Ht21.
destruct t12. {
  destruct t21; [ | easy ].
  apply angle_le_antisymm in Ht12; [ | easy ].
  now subst θ2.
} {
  destruct t21; [ easy | ].
  apply angle_leb_gt in Ht12, Ht21.
  now apply angle_lt_asymm in Ht12.
}
Qed.

Theorem angle_dist_separation :
  ∀ θ1 θ2, angle_dist θ1 θ2 = 0%L ↔ θ1 = θ2.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (angle_dist _ _)).
  split; [ | easy ].
  intros _.
  apply eq_angle_eq.
  do 2 rewrite (H1 (rngl_cos _)), (H1 (rngl_sin _)).
  easy.
}
intros.
progress unfold angle_dist.
split; intros Hab. {
  progress unfold angle_dist_greater_smaller in Hab.
  destruct (angle_le_dec θ2 θ1) as [Ht21| Ht21]. {
    rewrite (proj2 (angle_max_l_iff _ _) Ht21) in Hab.
    rewrite (proj2 (angle_min_r_iff _ _) Ht21) in Hab.
    remember (angle_same_side θ1 θ2) as ss12 eqn:Hss12.
    remember (θ1 ≤? θ2 + angle_straight)%A as t12s eqn:Ht12s.
    symmetry in Hss12, Ht12s.
    destruct ss12; [ now apply angle_eucl_dist_separation | ].
    destruct t12s; [ now apply angle_eucl_dist_separation | ].
    exfalso.
    rewrite rngl_add_comm in Hab.
    apply (rngl_add_move_0_r Hop) in Hab.
    specialize (angle_eucl_dist_nonneg θ1 (θ2 + angle_straight)) as H1.
    rewrite Hab in H1.
    apply rngl_nlt_ge in H1.
    apply H1; clear H1.
    apply (rngl_opp_neg_pos Hop Hor).
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  } {
    apply angle_nle_gt in Ht21.
    generalize Ht21; intros Ht21'.
    apply angle_lt_le_incl in Ht21.
    rewrite (proj2 (angle_max_r_iff _ _) Ht21) in Hab.
    rewrite (proj2 (angle_min_l_iff _ _) Ht21) in Hab.
    symmetry.
    remember (angle_same_side θ2 θ1) as ss12 eqn:Hss12.
    remember (θ2 ≤? θ1 + angle_straight)%A as t12s eqn:Ht12s.
    symmetry in Hss12, Ht12s.
    destruct ss12; [ now apply angle_eucl_dist_separation | ].
    destruct t12s; [ now apply angle_eucl_dist_separation | ].
    exfalso.
    rewrite rngl_add_comm in Hab.
    apply (rngl_add_move_0_r Hop) in Hab.
    specialize (angle_eucl_dist_nonneg θ2 (θ1 + angle_straight)) as H1.
    rewrite Hab in H1.
    apply rngl_nlt_ge in H1.
    apply H1; clear H1.
    apply (rngl_opp_neg_pos Hop Hor).
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
}
subst θ2.
rewrite angle_max_id, angle_min_id.
progress unfold angle_dist_greater_smaller.
progress unfold angle_same_side.
rewrite Bool.eqb_reflx.
apply angle_eucl_dist_diag.
Qed.

Theorem angle_eucl_dist_to_0_to_straight :
  ∀ θ, ((angle_eucl_dist θ 0)² + (angle_eucl_dist θ angle_straight)² = 2²)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
cbn.
rewrite (rngl_sub_0_l Hop).
progress unfold rl_modl.
rewrite <- (rngl_opp_add_distr Hop).
do 2 rewrite (rngl_squ_opp Hop).
rewrite (rngl_add_comm _ 1).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hos Hor).
  apply (rngl_squ_nonneg Hos Hor).
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hos Hor).
  apply (rngl_squ_nonneg Hos Hor).
}
rewrite rngl_add_assoc.
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_add Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
do 2 rewrite rngl_add_assoc.
rewrite <- (rngl_add_assoc (_ - _)).
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
do 2 rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_add Hop).
rewrite <- rngl_add_assoc.
symmetry.
apply (rngl_mul_2_l Hon).
Qed.

Theorem angle_sub_straight_le_straight :
  ∀ θ,
  (angle_straight ≤ θ)%A
  → (θ - angle_straight ≤ angle_straight)%A.
Proof.
destruct_ac.
intros * Has.
progress unfold angle_leb in Has.
progress unfold angle_leb.
rewrite rngl_sin_sub_straight_r.
rewrite rngl_cos_sub_straight_r.
rewrite (rngl_leb_0_opp Hop Hor).
cbn in Has |-*.
rewrite (rngl_leb_refl Hor) in Has |-*.
remember (rngl_sin θ ≤? 0)%L as s1z eqn:Hs1z.
symmetry in Hs1z.
destruct s1z. {
  apply rngl_leb_le.
  apply -> (rngl_opp_le_compat Hop Hor).
  apply rngl_cos_bound.
}
exfalso.
apply (rngl_leb_gt Hor) in Hs1z.
generalize Hs1z; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H in Has; clear H.
apply Bool.not_false_iff_true in Has.
apply Has; clear Has.
apply (rngl_leb_gt Hor).
apply (rngl_lt_iff Hor).
split; [ apply rngl_cos_bound | ].
intros H; symmetry in H.
apply eq_rngl_cos_opp_1 in H.
subst θ.
now apply (rngl_lt_irrefl Hor) in Hs1z.
Qed.

Theorem angle_le_sub_straight_sub_straight :
  ∀ θ1 θ2,
  (θ1 ≤ θ2)%A
  → (angle_straight ≤ θ1)%A
  → (angle_straight ≤ θ2)%A
  → (θ1 - angle_straight ≤ θ2 - angle_straight)%A.
Proof.
destruct_ac.
intros * H12 Has1 Has2.
progress unfold angle_leb in H12.
progress unfold angle_leb in Has1.
progress unfold angle_leb in Has2.
progress unfold angle_leb.
do 2 rewrite rngl_sin_sub_straight_r.
do 2 rewrite rngl_cos_sub_straight_r.
do 2 rewrite (rngl_leb_0_opp Hop Hor).
cbn in Has1, Has2 |-*.
rewrite (rngl_leb_refl Hor) in Has1, Has2.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
symmetry in Hzs1, Hzs2, Hs1z, Hs2z.
destruct s1z. {
  destruct s2z; [ | easy ].
  apply rngl_leb_le in Hs1z, Hs2z.
  apply rngl_leb_le.
  apply -> (rngl_opp_le_compat Hop Hor).
  destruct zs1. {
    apply rngl_leb_le in Has1.
    apply (rngl_lt_eq_cases Hor) in Has1.
    destruct Has1 as [Has1| Has1]. {
      exfalso; apply rngl_nle_gt in Has1.
      apply Has1, rngl_cos_bound.
    }
    apply eq_rngl_cos_opp_1 in Has1; subst θ1.
    apply rngl_cos_bound.
  }
  destruct zs2; [ easy | ].
  now apply rngl_leb_le in H12.
}
exfalso.
apply (rngl_leb_gt Hor) in Hs1z.
generalize Hs1z; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H in Hzs1; clear H; subst zs1.
apply rngl_leb_le in Has1.
apply (rngl_lt_eq_cases Hor) in Has1.
destruct Has1 as [Has1| Has1]. {
  apply rngl_nle_gt in Has1.
  apply Has1, rngl_cos_bound.
}
apply eq_rngl_cos_opp_1 in Has1; subst θ1.
now apply (rngl_lt_irrefl Hor) in Hs1z.
Qed.

Theorem angle_0_right_same_side :
  angle_same_side 0 angle_right = true.
Proof.
progress unfold angle_same_side.
rewrite angle_straight_nonneg.
apply Bool.eqb_true_iff; symmetry.
apply angle_right_le_straight.
Qed.

Theorem angle_0_straight_same_side :
  angle_same_side 0 angle_straight = true.
Proof.
progress unfold angle_same_side.
rewrite angle_le_refl.
apply Bool.eqb_true_iff.
apply angle_straight_nonneg.
Qed.

Theorem angle_eucl_dist_0_right : angle_eucl_dist 0 angle_right = √2%L.
Proof.
destruct_ac.
rewrite angle_eucl_dist_is_sqrt.
rewrite angle_sub_0_r.
cbn.
rewrite (rngl_sub_0_r Hos).
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem angle_dist_greater_smaller_move_0_r :
  ∀ θ1 θ2,
  (θ2 ≤ θ1)%A
  → angle_same_side θ1 θ2 = true
  → angle_dist_greater_smaller θ1 θ2 = angle_dist_greater_smaller (θ1 - θ2) 0.
Proof.
destruct_ac.
intros  * Ht21 Hb12.
progress unfold angle_dist_greater_smaller.
rewrite Hb12.
remember (angle_same_side (θ1 - θ2) 0) as b12z eqn:Hb12z.
symmetry in Hb12z.
destruct b12z; [ apply angle_eucl_dist_move_0_r | ].
exfalso.
progress unfold angle_same_side in Hb12.
progress unfold angle_same_side in Hb12z.
apply -> Bool.eqb_true_iff in Hb12.
apply Bool.eqb_false_iff in Hb12z.
rewrite angle_straight_nonneg in Hb12z.
apply Bool.not_true_iff_false in Hb12z.
apply angle_leb_gt in Hb12z.
apply angle_nle_gt in Hb12z.
apply Hb12z; clear Hb12z.
(* lemma *)
progress unfold angle_leb in Ht21.
progress unfold angle_leb in Hb12.
progress unfold angle_leb.
cbn in Hb12.
cbn - [ angle_sub ].
rewrite (rngl_leb_refl Hor) in Hb12 |-*.
remember (0 ≤? rngl_sin (θ1 - θ2))%L as zs12 eqn:Hzs12.
symmetry in Hzs12.
destruct zs12; [ apply rngl_leb_le, rngl_cos_bound | ].
exfalso.
apply Bool.not_true_iff_false in Hzs12.
apply Hzs12; clear Hzs12.
apply rngl_leb_le.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  destruct zs2. 2: {
    apply (rngl_leb_gt Hor) in Hb12.
    exfalso.
    apply rngl_nle_gt in Hb12.
    apply Hb12, rngl_cos_bound.
  }
  apply rngl_leb_le in Hzs1, Hzs2, Ht21.
  now apply rngl_sin_sub_nonneg.
}
symmetry in Hb12.
destruct zs2. {
  exfalso.
  apply Bool.not_true_iff_false in Hb12.
  apply Hb12, rngl_leb_le, rngl_cos_bound.
}
apply (rngl_leb_gt Hor) in Hzs1, Hzs2.
apply rngl_leb_le in Ht21.
change_angle_opp θ1.
progress sin_cos_opp_hyp T Hzs1.
progress sin_cos_opp_hyp T Ht21.
change_angle_opp θ2.
progress sin_cos_opp_hyp T Ht21.
progress sin_cos_opp_hyp T Hzs2.
rewrite angle_sub_opp_r.
rewrite angle_add_opp_l.
apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
now apply rngl_sin_sub_nonneg.
Qed.

Theorem angle_dist_move_0_r :
  ∀ θ1 θ2,
  (θ2 ≤ θ1)%A
  → angle_same_side θ1 θ2 = true
  → angle_dist θ1 θ2 = angle_dist (θ1 - θ2) 0.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (angle_dist _ 0)).
  apply H1.
}
intros * Ht21 Hb12.
progress unfold angle_dist.
rewrite (proj2 (angle_max_l_iff _ _) Ht21).
rewrite (proj2 (angle_min_r_iff _ _) Ht21).
rewrite (proj2 (angle_max_l_iff _ _)); [ | apply angle_nonneg ].
rewrite (proj2 (angle_min_r_iff _ _)); [ | apply angle_nonneg ].
now apply angle_dist_greater_smaller_move_0_r.
Qed.

(* to be completed (plus tard ou à supprimer)
Theorem angle_dist_greater_smaller_triangular :
  ∀ θ1 θ2 θ3,
  (θ1 ≤ θ2 ≤ θ3)%A
  → (angle_dist_greater_smaller θ3 θ1 ≤
       angle_dist_greater_smaller θ3 θ2 + angle_dist_greater_smaller θ2 θ1)%L.
Proof.
destruct_ac.
intros * (H12, H23).
progress unfold angle_dist_greater_smaller.
remember (angle_same_side θ3 θ1) as ss31 eqn:Hss31.
remember (angle_same_side θ2 θ1) as ss21 eqn:Hss21.
remember (angle_same_side θ3 θ2) as ss32 eqn:Hss32.
remember (θ2 ≤? θ1 + angle_straight)%A as t21s eqn:Ht21s.
remember (θ3 ≤? θ2 + angle_straight)%A as t32s eqn:Ht32s.
remember (θ3 ≤? θ1 + angle_straight)%A as t31s eqn:Ht31s.
symmetry in Hss31, Hss21, Hss32, Ht21s, Ht32s, Ht31s.
destruct ss31. {
  destruct ss21. {
    destruct ss32; [ apply angle_eucl_dist_triangular | ].
    progress unfold angle_same_side in Hss31.
    progress unfold angle_same_side in Hss21.
    progress unfold angle_same_side in Hss32.
    apply -> Bool.eqb_true_iff in Hss31.
    apply -> Bool.eqb_true_iff in Hss21.
    apply Bool.eqb_false_iff in Hss32.
    congruence.
  }
  destruct ss32. {
    progress unfold angle_same_side in Hss31.
    progress unfold angle_same_side in Hss21.
    progress unfold angle_same_side in Hss32.
    apply -> Bool.eqb_true_iff in Hss31.
    apply -> Bool.eqb_true_iff in Hss32.
    apply Bool.eqb_false_iff in Hss21.
    congruence.
  }
  destruct t21s. {
    destruct t32s; [ apply angle_eucl_dist_triangular | ].
    eapply (rngl_le_trans Hor). {
      apply (angle_eucl_dist_triangular _ θ2).
    }
    apply (rngl_add_le_mono_r Hop Hor).
    apply (rngl_le_trans Hor _ 2); [ apply angle_eucl_dist_bound | ].
    apply (rngl_le_add_r Hor).
    apply angle_eucl_dist_nonneg.
  }
  apply (rngl_le_trans Hor _ 2); [ apply angle_eucl_dist_bound | ].
  rewrite (rngl_add_comm _ (2 + _)).
  rewrite <- rngl_add_assoc.
  apply (rngl_le_add_r Hor).
  apply (rngl_add_nonneg_nonneg Hor).
  apply angle_eucl_dist_nonneg.
  destruct t32s; [ apply angle_eucl_dist_nonneg | ].
  apply (rngl_add_nonneg_nonneg Hor); [ | apply angle_eucl_dist_nonneg ].
  apply (rngl_0_le_2 Hon Hos Hor).
}
destruct t31s. {
  destruct ss32. {
    destruct ss21; [ apply angle_eucl_dist_triangular | ].
    destruct t21s; [ apply angle_eucl_dist_triangular | ].
    rewrite rngl_add_comm.
    rewrite <- rngl_add_assoc.
    eapply (rngl_le_trans Hor); [ apply angle_eucl_dist_bound | ].
    apply (rngl_le_add_r Hor).
    apply (rngl_add_nonneg_nonneg Hor).
    apply angle_eucl_dist_nonneg.
    apply angle_eucl_dist_nonneg.
  }
  destruct t32s. {
    destruct ss21; [ apply angle_eucl_dist_triangular | ].
    destruct t21s; [ apply angle_eucl_dist_triangular | ].
    rewrite rngl_add_comm.
    rewrite <- rngl_add_assoc.
    eapply (rngl_le_trans Hor); [ apply angle_eucl_dist_bound | ].
    apply (rngl_le_add_r Hor).
    apply (rngl_add_nonneg_nonneg Hor).
    apply angle_eucl_dist_nonneg.
    apply angle_eucl_dist_nonneg.
  }
  rewrite <- rngl_add_assoc.
  eapply (rngl_le_trans Hor); [ apply angle_eucl_dist_bound | ].
  apply (rngl_le_add_r Hor).
  apply (rngl_add_nonneg_nonneg Hor).
  apply angle_eucl_dist_nonneg.
  destruct ss21; [ apply angle_eucl_dist_nonneg | ].
  destruct t21s; [ apply angle_eucl_dist_nonneg | ].
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_0_le_2 Hon Hos Hor).
  apply angle_eucl_dist_nonneg.
}
destruct ss32. {
  destruct ss21. {
    progress unfold angle_same_side in Hss31.
    progress unfold angle_same_side in Hss21.
    progress unfold angle_same_side in Hss32.
    apply -> Bool.eqb_false_iff in Hss31.
    apply -> Bool.eqb_true_iff in Hss32.
    apply -> Bool.eqb_true_iff in Hss21.
    congruence.
  }
  destruct t21s. {
    apply angle_leb_gt in Ht31s.
    progress unfold angle_same_side in Hss31.
    progress unfold angle_same_side in Hss21.
    progress unfold angle_same_side in Hss32.
    apply -> Bool.eqb_false_iff in Hss31.
    apply -> Bool.eqb_true_iff in Hss32.
    apply -> Bool.eqb_false_iff in Hss21.
    remember (θ1 ≤? angle_straight)%A as t1s eqn:Ht1s.
    symmetry in Ht1s.
    destruct t1s. 2: {
      exfalso.
      apply Bool.not_false_iff_true in Hss21.
      apply Bool.not_true_iff_false in Ht1s.
      apply Ht1s; clear Ht1s.
      now apply (angle_le_trans _ θ2).
    }
    apply angle_nle_gt in Hss31, Hss21.
    clear Hss32 H12.
    progress unfold angle_leb in H23.
    progress unfold angle_leb in Ht1s.
    progress unfold angle_leb in Ht21s.
    progress unfold angle_leb in Ht32s.
    progress unfold angle_ltb in Hss31.
    progress unfold angle_ltb in Hss21.
    progress unfold angle_ltb in Ht31s.
    cbn - [ angle_add ] in Ht1s, Hss31, Hss21, Ht21s, Ht32s, Ht31s.
    rewrite (rngl_leb_refl Hor) in Ht1s, Hss31, Hss21.
    rewrite rngl_sin_add_straight_r in Ht21s, Ht32s, Ht31s.
    rewrite rngl_cos_add_straight_r in Ht21s, Ht32s, Ht31s.
    rewrite (rngl_leb_0_opp Hop Hor) in Ht31s, Ht21s, Ht32s.
    remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
    remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
    remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
    remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
    remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
    symmetry in Hzs1, Hzs2, Hzs3, Hs1z, Hs2z.
    destruct zs1; [ clear Ht1s | easy ].
    destruct t32s. {
      exfalso.
      destruct zs2. {
        apply rngl_ltb_lt in Hss21.
        apply rngl_nle_gt in Hss21.
        apply Hss21, rngl_cos_bound.
      }
      destruct zs3. {
        apply rngl_ltb_lt in Hss31.
        apply rngl_nle_gt in Hss31.
        apply Hss31, rngl_cos_bound.
      }
      clear Hss21 Hss31 Hzs1.
      destruct s1z; [ easy | ].
      destruct s2z; [ easy | ].
      apply rngl_leb_le in H23, Ht21s, Ht32s.
      apply rngl_ltb_lt in Ht31s.
      apply (rngl_leb_gt Hor) in Hzs2, Hzs3, Hs1z, Hs2z.
      apply (rngl_le_opp_r Hop Hor) in Ht21s, Ht32s.
      apply (rngl_lt_opp_l Hop Hor) in Ht31s.
      now apply (rngl_lt_asymm Hor) in Hzs2.
    }
    destruct zs2. {
      exfalso.
      apply rngl_ltb_lt in Hss21.
      apply rngl_nle_gt in Hss21.
      apply Hss21, rngl_cos_bound.
    }
    destruct zs3. {
      exfalso.
      apply rngl_ltb_lt in Hss31.
      apply rngl_nle_gt in Hss31.
      apply Hss31, rngl_cos_bound.
    }
    destruct s1z; [ easy | ].
    clear Hss31 Hss21.
    apply rngl_leb_le in H23, Hzs1, Ht21s.
    apply (rngl_leb_gt Hor) in Hzs2, Hzs3, Hs1z.
    apply rngl_ltb_lt in Ht31s.
    clear Hzs1.
    destruct s2z. 2: {
      apply (rngl_leb_gt Hor) in Hs2z.
      now apply (rngl_lt_asymm Hor) in Hs2z.
    }
    clear Hs2z Ht32s.
    apply (rngl_le_opp_r Hop Hor) in Ht21s.
    apply (rngl_lt_opp_l Hop Hor) in Ht31s.
    move Hs1z after Hzs2.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      change_angle_add_r θ2 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs2.
      progress sin_cos_add_sub_straight_hyp T Ht21s.
      progress sin_cos_add_sub_straight_hyp T H23.
      rewrite (rngl_add_opp_l Hop) in Ht21s.
      apply -> (rngl_le_sub_0 Hop Hor) in Ht21s.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hzc3]. {
        change_angle_opp θ3.
        progress sin_cos_opp_hyp T Hzs3.
        progress sin_cos_opp_hyp T Ht31s.
        progress sin_cos_opp_hyp T H23.
        progress sin_cos_opp_hyp T Hzc3.
        clear H23.
        move θ2 before θ1.
        move θ3 before θ2.
        move Hzc1 before Hzs3.
        move Hzc3 before Hzc1.
        rewrite <- angle_eucl_dist_opp_opp.
        rewrite angle_opp_involutive.
        rewrite angle_opp_add_distr.
        rewrite angle_opp_straight.
        rewrite <- (angle_eucl_dist_opp_opp (- θ3)).
        rewrite angle_opp_involutive.
        rewrite angle_opp_sub_distr.
        rewrite angle_eucl_dist_move_0_l.
        rewrite <- angle_sub_add_distr.
        rewrite <- angle_eucl_dist_move_0_l.
        rewrite (angle_eucl_dist_move_0_l θ3).
        rewrite <- angle_sub_add_distr.
        rewrite <- angle_eucl_dist_move_0_l.
        rewrite (angle_eucl_dist_move_0_l _ θ1).
        rewrite angle_sub_sub_distr.
        rewrite <- angle_sub_straight_eq_add_straight.
        rewrite <- angle_eucl_dist_move_0_l.
        rewrite (angle_eucl_dist_symmetry angle_straight).
...

Theorem angle_dist_triangular :
  ∀ θ1 θ2 θ3, (angle_dist θ1 θ3 ≤ angle_dist θ1 θ2 + angle_dist θ2 θ3)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_dist.
destruct (angle_le_dec θ1 θ3) as [H13| H13]. {
  rewrite (proj2 (angle_max_r_iff _ _) H13).
  rewrite (proj2 (angle_min_l_iff _ _) H13).
  destruct (angle_le_dec θ1 θ2) as [H12| H12]. {
    rewrite (proj2 (angle_max_r_iff _ _) H12).
    rewrite (proj2 (angle_min_l_iff _ _) H12).
    destruct (angle_le_dec θ2 θ3) as [H23| H23]. {
      rewrite (proj2 (angle_max_r_iff _ _) H23).
      rewrite (proj2 (angle_min_l_iff _ _) H23).
      apply angle_dist_greater_smaller_triangular.
...
progress unfold angle_same_side.
remember (Bool.eqb _ _) as b13 eqn:Hb13 in |-*.
remember (Bool.eqb _ _) as b12 eqn:Hb12 in |-*.
remember (Bool.eqb _ _) as b23 eqn:Hb23 in |-*.
symmetry in Hb13, Hb12, Hb23.
destruct b13. {
  destruct b12. {
    destruct b23; [ apply angle_eucl_dist_triangular | ].
    eapply (rngl_le_trans Hor). {
      apply angle_eucl_dist_triangular.
    }
    apply (rngl_add_le_mono_l Hop Hor).
    rewrite (angle_eucl_dist_symmetry θ3).
    apply angle_eucl_dist_triangular.
  }
  destruct b23. {
    eapply (rngl_le_trans Hor). {
      apply (angle_eucl_dist_triangular _ θ2).
    }
    apply (rngl_add_le_mono_r Hop Hor).
    rewrite (angle_eucl_dist_symmetry θ2).
    apply angle_eucl_dist_triangular.
  }
  rewrite rngl_add_add_swap.
  rewrite rngl_add_assoc.
  rewrite (rngl_add_add_swap (angle_eucl_dist _ _)).
  rewrite <- rngl_add_assoc.
  rewrite (angle_eucl_dist_symmetry θ3).
  eapply (rngl_le_trans Hor). 2: {
    apply (rngl_le_add_r Hor).
    apply (rngl_add_nonneg_nonneg Hor).
    apply angle_eucl_dist_nonneg.
    apply angle_eucl_dist_nonneg.
  }
  apply angle_eucl_dist_triangular.
}
destruct b12. {
  destruct b23. {
    apply Bool.eqb_false_iff in Hb13.
    apply -> Bool.eqb_true_iff in Hb12.
    apply -> Bool.eqb_true_iff in Hb23.
    now rewrite Hb12, Hb23 in Hb13.
  }
  rewrite rngl_add_assoc.
  apply (rngl_add_le_mono_r Hop Hor).
  apply angle_eucl_dist_triangular.
}
destruct b23. {
  rewrite <- rngl_add_assoc.
  apply (rngl_add_le_mono_l Hop Hor).
  rewrite (angle_eucl_dist_symmetry θ3).
  rewrite (angle_eucl_dist_symmetry θ2).
  apply angle_eucl_dist_triangular.
}
rewrite rngl_add_assoc.
apply (rngl_add_le_mono_r Hop Hor).
rewrite <- rngl_add_assoc.
apply (rngl_le_add_r Hor).
apply (rngl_add_nonneg_nonneg Hor).
apply angle_eucl_dist_nonneg.
apply angle_eucl_dist_nonneg.
Qed.

Theorem angle_dist_is_dist : is_dist angle_dist.
Proof.
split.
apply angle_dist_symmetry.
apply angle_dist_separation.
apply angle_dist_triangular.
Qed.

Theorem angle_dist_move_0_r :
  ∀ θ1 θ2,
  (θ2 ≤ θ1)%A
  → angle_same_side θ1 θ2 = true
  → angle_dist θ1 θ2 = angle_dist (θ1 - θ2) 0.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (angle_dist _ 0)).
  apply H1.
}
intros * Ht21 Hb12.
progress unfold angle_dist.
rewrite angle_eucl_dist_0_straight.
rewrite Hb12.
remember (angle_same_side (θ1 - θ2) 0) as b12z eqn:Hb12z.
symmetry in Hb12z.
destruct b12z; [ apply angle_eucl_dist_move_0_r | ].
exfalso.
apply -> Bool.eqb_true_iff in Hb12.
apply Bool.eqb_false_iff in Hb12z.
rewrite angle_straight_nonneg in Hb12z.
apply Hb12z; clear Hb12z.
progress unfold angle_leb in Ht21.
progress unfold angle_leb in Hb12.
progress unfold angle_leb.
cbn - [ angle_sub ] in Ht21, Hb12 |-*.
rewrite (rngl_leb_refl Hor) in Hb12 |-*.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin (θ1 - θ2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hzs2, Hzs12.
destruct zs12; [ apply rngl_leb_le, rngl_cos_bound | exfalso ].
apply Bool.not_true_iff_false in Hzs12.
apply Hzs12; clear Hzs12.
apply rngl_leb_le.
destruct zs2. {
  destruct zs1. {
    apply rngl_leb_le in Hzs1, Hzs2, Ht21.
    now apply rngl_sin_sub_nonneg.
  }
  exfalso.
  clear Ht21; symmetry in Hb12.
  apply Bool.not_true_iff_false in Hb12.
  apply Hb12; clear Hb12.
  apply rngl_leb_le, rngl_cos_bound.
}
destruct zs1; [ easy | ].
apply rngl_leb_le in Ht21.
apply (rngl_leb_gt Hor) in Hzs1, Hzs2.
clear Hb12.
change_angle_opp θ1.
change_angle_opp θ2.
progress sin_cos_opp_hyp T Hzs1.
progress sin_cos_opp_hyp T Hzs2.
cbn in Ht21.
rewrite angle_sub_opp_r.
rewrite angle_add_opp_l.
apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
now apply rngl_sin_sub_nonneg.
Qed.

Theorem angle_dist_angle_eucl_dist :
  ∀ θ1 θ2,
  angle_same_side θ1 θ2 = true
  → angle_dist θ1 θ2 = angle_eucl_dist θ1 θ2.
Proof.
intros * Hss.
progress unfold angle_dist.
now rewrite Hss.
Qed.

Theorem angle_dist_to_0_to_straight :
  ∀ θ,
  (θ ≤ angle_straight)%A
  → ((angle_dist θ 0)² + (angle_dist θ angle_straight)² = 2²)%L.
Proof.
destruct_ac.
intros.
rewrite angle_dist_angle_eucl_dist. 2: {
  now apply angle_le_straight_same_side_0_iff.
}
rewrite angle_dist_angle_eucl_dist. 2: {
  now apply angle_le_straight_same_side_straight_iff.
}
apply angle_eucl_dist_to_0_to_straight.
Qed.

Theorem rngl_cos_angle_dist :
  ∀ θ, (θ ≤ angle_straight)%A → rngl_cos θ = (1 - (angle_dist θ 0)² / 2)%L.
Proof.
intros * Hts.
progress unfold angle_dist.
remember (angle_same_side θ 0) as tz eqn:Htz.
symmetry in Htz.
destruct tz; [ apply rngl_cos_angle_eucl_dist | ].
exfalso.
progress unfold angle_same_side in Htz.
apply Bool.not_true_iff_false in Htz.
apply Htz; clear Htz.
apply Bool.eqb_true_iff.
now rewrite angle_straight_nonneg.
Qed.

Theorem rngl_cos_angle_dist' :
  ∀ θ,
  (angle_straight < θ)%A
  → rngl_cos θ = ((angle_dist θ angle_straight)² / 2 - 1)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ - _)%L).
  apply H1.
}
intros * Hst.
progress unfold angle_dist.
remember (angle_same_side θ angle_straight) as ts eqn:Hts.
symmetry in Hts.
destruct ts. {
  exfalso.
  apply angle_le_straight_same_side_straight_iff in Hts.
  now apply angle_nlt_ge in Hts.
}
rewrite angle_eucl_dist_diag.
rewrite rngl_add_0_r.
specialize (angle_eucl_dist_to_0_to_straight θ) as H1.
rewrite rngl_add_comm in H1.
apply (rngl_add_move_r Hop) in H1.
rewrite H1.
rewrite (rngl_div_sub_distr_r Hop Hiv).
progress unfold rngl_squ at 1.
rewrite (rngl_mul_div Hi1). 2: {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
}
rewrite (rngl_sub_sub_swap Hop).
rewrite (rngl_add_sub Hos).
apply rngl_cos_angle_eucl_dist.
Qed.

Theorem angle_le_angle_dist_le :
  ∀ θ1 θ2, (θ1 ≤ θ2)%A ↔ (angle_dist θ1 0 ≤ angle_dist θ2 0)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H2.
  intros.
  rewrite (H2 θ1), (H2 θ2).
  rewrite (H1 (angle_dist _ _)).
  rewrite angle_le_refl.
  split; [ intros | easy ].
  apply (rngl_le_refl Hor).
}
intros.
progress unfold angle_dist.
rewrite angle_eucl_dist_0_straight.
remember (angle_same_side θ1 0) as as1 eqn:Has1.
remember (angle_same_side θ2 0) as as2 eqn:Has2.
symmetry in Has1, Has2.
split; intros H12. {
  destruct as1. {
    destruct as2. {
      apply angle_le_angle_eucl_dist_le; [ | | easy ].
      now apply angle_le_straight_same_side_0_iff.
      now apply angle_le_straight_same_side_0_iff.
    }
    apply (rngl_le_trans Hor _ 2).
    apply angle_eucl_dist_bound.
    apply (rngl_le_add_l Hor).
    apply angle_eucl_dist_nonneg.
  }
  destruct as2. {
    exfalso.
    apply angle_le_straight_same_side_0_iff in Has2.
    apply Bool.not_true_iff_false in Has1.
    apply Has1; clear Has1.
    apply angle_le_straight_same_side_0_iff.
    now apply (angle_le_trans _ θ2).
  }
  apply (rngl_add_le_mono_r Hop Hor).
  apply angle_gt_straight_not_same_side_0_iff in Has1, Has2.
  do 2 rewrite (angle_eucl_dist_move_0_r _ angle_straight).
  apply angle_lt_le_incl in Has1, Has2.
  apply angle_le_angle_eucl_dist_le.
  now apply angle_sub_straight_le_straight.
  now apply angle_sub_straight_le_straight.
  now apply angle_le_sub_straight_sub_straight.
}
destruct as1. {
  destruct as2. {
    apply angle_le_angle_eucl_dist_le in H12; [ easy | | ].
    now apply angle_le_straight_same_side_0_iff.
    now apply angle_le_straight_same_side_0_iff.
  }
  apply angle_le_straight_same_side_0_iff in Has1.
  apply angle_gt_straight_not_same_side_0_iff in Has2.
  apply (angle_le_trans _ angle_straight); [ easy | ].
  now apply angle_lt_le_incl in Has2.
}
destruct as2. {
  exfalso.
  apply rngl_nlt_ge in H12.
  apply H12; clear H12.
  apply angle_le_straight_same_side_0_iff in Has2.
  apply angle_gt_straight_not_same_side_0_iff in Has1.
  eapply (rngl_le_lt_trans Hor _ 2). {
    apply angle_eucl_dist_bound.
  }
  apply (rngl_lt_add_l Hos Hor).
  apply (rngl_lt_iff Hor).
  split ; [ apply angle_eucl_dist_nonneg | ].
  intros H; symmetry in H.
  apply angle_eucl_dist_separation in H.
  subst θ1.
  now apply angle_lt_irrefl in Has1.
}
apply (rngl_add_le_mono_r Hop Hor) in H12.
apply angle_gt_straight_not_same_side_0_iff in Has1.
apply angle_gt_straight_not_same_side_0_iff in Has2.
(* lemma *)
apply angle_nlt_ge.
intros H21.
apply rngl_nlt_ge in H12.
apply H12; clear H12.
apply angle_eucl_dist_lt_angle_eucl_dist.
do 2 rewrite rngl_cos_sub_straight_r.
apply -> (rngl_opp_lt_compat Hop Hor).
change_angle_opp θ1.
change_angle_opp θ2.
cbn.
(* lemma *)
apply angle_opp_lt_compat_if in H21. 2: {
  intros H.
  apply (f_equal angle_opp) in H.
  rewrite angle_opp_involutive in H.
  rewrite angle_opp_0 in H; subst θ2.
  rewrite angle_opp_0 in Has2.
  apply angle_nle_gt in Has2.
  apply Has2, angle_straight_nonneg.
}
do 2 rewrite angle_opp_involutive in H21.
apply angle_lt_opp_r in Has1, Has2; cycle 1. {
  (* lemma *)
  intros H.
  specialize (angle_straight_pos Hc1) as H1.
  rewrite H in H1.
  now apply angle_lt_irrefl in H1.
} {
  (* lemma *)
  intros H.
  specialize (angle_straight_pos Hc1) as H1.
  rewrite H in H1.
  now apply angle_lt_irrefl in H1.
}
rewrite angle_opp_straight in Has1, Has2.
(* lemma *)
apply (rngl_nle_gt_iff Hor).
intros Hcc.
apply angle_nle_gt in H21.
apply H21; clear H21.
progress unfold angle_leb.
apply angle_lt_le_incl in Has1, Has2.
apply rngl_sin_nonneg_angle_le_straight in Has1, Has2.
apply rngl_leb_le in Has1, Has2.
rewrite Has1, Has2.
now apply rngl_leb_le.
Qed.

Theorem angle_eucl_dist_le_angle_dist :
  ∀ θ1 θ2, (angle_eucl_dist θ1 θ2 ≤ angle_dist θ1 θ2)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_dist.
remember (angle_same_side θ1 θ2) as t12 eqn:Ht12.
symmetry in Ht12.
destruct t12; [ apply (rngl_le_refl Hor) | ].
rewrite (angle_eucl_dist_symmetry θ2).
apply angle_eucl_dist_triangular.
Qed.

Theorem angle_dist_0_straight : angle_dist 0 angle_straight = 2%L.
Proof.
progress unfold angle_dist.
rewrite angle_0_straight_same_side.
apply angle_eucl_dist_0_straight.
Qed.

Theorem angle_dist_nonneg : ∀ θ1 θ2 : angle T, (0 ≤ angle_dist θ1 θ2)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_dist.
remember (angle_same_side θ1 θ2) as ss eqn:Hss.
symmetry in Hss.
destruct ss; [ apply angle_eucl_dist_nonneg | ].
apply (rngl_add_nonneg_nonneg Hor).
apply angle_eucl_dist_nonneg.
apply angle_eucl_dist_nonneg.
Qed.

Theorem angle_dist_pos_angle_neq :
  ∀ θ1 θ2, (0 < angle_dist θ1 θ2)%L ↔ θ1 ≠ θ2.
Proof.
destruct_ac.
intros.
split; intros Hd. {
  apply (rngl_lt_iff Hor) in Hd.
  destruct Hd as (_, Hd).
  intros H1; apply Hd; symmetry.
  now apply angle_dist_separation.
} {
  apply (rngl_lt_iff Hor).
  split; [ apply angle_dist_nonneg | ].
  intros H1; apply Hd.
  now apply angle_dist_separation.
}
Qed.

Theorem angle_le_straight_dist_angle_eucl_dist :
  ∀ θ1 θ2,
  (θ1 ≤ angle_straight)%A
  → (θ2 ≤ angle_straight)%A
  → angle_dist θ1 θ2 = angle_eucl_dist θ1 θ2.
Proof.
intros * H1s H2s.
progress unfold angle_dist.
progress unfold angle_same_side.
now rewrite H1s, H2s.
Qed.

Theorem angle_dist_0_right : angle_dist 0 angle_right = √2%L.
Proof.
rewrite angle_dist_angle_eucl_dist. {
  apply angle_eucl_dist_0_right.
} {
  apply angle_0_right_same_side.
}
Qed.

Theorem rngl_cos_derivative :
  is_derivative angle_dist rngl_dist rngl_cos (λ θ, (- rngl_sin θ)%L).
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀ ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros θ₀ ε Hε.
destruct (angle_eq_dec θ₀ 0) as [Htz| Htz]. {
  subst θ₀.
  cbn.
  exists (rngl_min ε 2).
  split. {
    apply rngl_min_glb_lt; [ easy | ].
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  intros dθ Hdθ.
  rewrite (rngl_opp_0 Hop).
  rewrite rngl_cos_angle_dist. 2: {
    destruct Hdθ as (H1, H2).
    apply angle_le_angle_eucl_dist_le; cycle 1. {
      apply angle_le_refl.
    } {
      rewrite (angle_eucl_dist_symmetry angle_straight).
      rewrite angle_eucl_dist_0_straight.
      apply (rngl_min_glb_lt_iff Hor) in H2.
      destruct H2 as (H2, H3).
      apply (rngl_lt_le_incl Hor) in H3.
      eapply (rngl_le_trans Hor); [ | apply H3 ].
      apply angle_eucl_dist_le_angle_dist.
    }
    apply (rngl_min_glb_lt_iff Hor) in H2.
    destruct H2 as (H2, H3).
    apply (rngl_lt_le_incl Hor) in H3.
    apply angle_le_angle_dist_le.
    rewrite (angle_dist_symmetry angle_straight).
    now rewrite angle_dist_0_straight.
  }
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
    intros H; rewrite H in Hdθ.
    destruct Hdθ as (H1, _).
    now apply (rngl_lt_irrefl Hor) in H1.
  }
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    apply angle_dist_nonneg.
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  apply (rngl_lt_le_trans Hor _ (rngl_min ε 2)); [ easy | ].
  apply (rngl_le_trans Hor _ ε).
  apply (rngl_le_min_l Hor).
  rewrite (rngl_mul_2_r Hon).
  apply (rngl_le_add_l Hor).
  now apply (rngl_lt_le_incl Hor) in Hε.
}
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  subst θ₀.
  cbn.
  exists (rngl_min ε (angle_dist 0 angle_right)).
  split. {
    apply rngl_min_glb_lt; [ easy | ].
    rewrite angle_dist_0_right.
    apply (rl_sqrt_pos Hon Hos Hor).
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  intros dθ Hdθ.
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_opp_0 Hop).
  destruct (angle_le_dec dθ angle_straight) as [Hts| Hts]. {
    rewrite rngl_cos_angle_dist; [ | easy ].
    specialize (angle_dist_to_0_to_straight dθ Hts) as H1.
    apply (rngl_add_move_r Hop) in H1.
    rewrite H1; clear H1.
    rewrite (rngl_div_sub_distr_r Hop Hiv).
    progress unfold rngl_squ at 1.
    rewrite (rngl_mul_div Hi1). 2: {
      apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_sub_sub_distr Hop).
    rewrite rngl_add_add_swap.
    rewrite <- (rngl_add_sub_swap Hop).
    rewrite (rngl_sub_diag Hos).
    rewrite rngl_add_0_l.
    rewrite (rngl_div_div_swap Hic Hiv).
    progress unfold rngl_squ.
    rewrite (rngl_mul_div Hi1). 2: {
      intros H; rewrite H in Hdθ.
      destruct Hdθ as (H1, _).
      now apply (rngl_lt_irrefl Hor) in H1.
    }
    progress unfold rngl_dist.
    rewrite (rngl_sub_0_r Hos).
    rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
      apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
        apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
      }
      apply angle_dist_nonneg.
    }
    apply (rngl_lt_div_l Hon Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    rewrite angle_dist_0_right in Hdθ.
    apply (rngl_lt_le_trans Hor _ (rngl_min ε √2)); [ easy | ].
    apply (rngl_le_trans Hor _ ε).
    apply (rngl_le_min_l Hor).
    rewrite (rngl_mul_2_r Hon).
    apply (rngl_le_add_l Hor).
    now apply (rngl_lt_le_incl Hor) in Hε.
  }
  apply angle_nle_gt in Hts.
  rewrite rngl_cos_angle_dist'; [ | easy ].
  rewrite (rngl_sub_add Hop).
  rewrite (rngl_div_div_swap Hic Hiv).
  progress unfold rngl_squ.
  rewrite (rngl_mul_div Hi1). 2: {
    intros H; rewrite H in Hdθ.
    destruct Hdθ as (H1, _).
    now apply (rngl_lt_irrefl Hor) in H1.
  }
  progress unfold rngl_dist.
  rewrite (rngl_sub_0_r Hos).
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    apply angle_dist_nonneg.
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  rewrite angle_dist_0_right in Hdθ.
  apply (rngl_lt_le_trans Hor _ (rngl_min ε √2)); [ easy | ].
  apply (rngl_le_trans Hor _ ε).
  apply (rngl_le_min_l Hor).
  rewrite (rngl_mul_2_r Hon).
  apply (rngl_le_add_l Hor).
  now apply (rngl_lt_le_incl Hor) in Hε.
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ dθ,
  (0 < angle_dist dθ 0 < η)%L
  → (rngl_dist
        ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_dist dθ 0)
        (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hη & Hd).
  remember (angle_eucl_dist θ₀ angle_straight) as x.
  exists (rngl_min3 x η (angle_dist θ₀ 0)).
  subst x.
  move η before ε.
  split. {
    apply rngl_min_glb_lt. {
      apply rngl_min_glb_lt; [ | easy ].
      apply angle_eucl_dist_pos_angle_neq.
      apply neq_angle_neq; intros H.
      injection H; clear H; intros H1 H2.
      apply eq_rngl_sin_0 in H1.
      now destruct H1.
    }
    now apply angle_dist_pos_angle_neq.
  }
  intros θ Hθ.
  remember (θ - θ₀)%A as dθ eqn:H.
  symmetry in H.
  apply angle_sub_move_r in H.
  subst θ.
  specialize (Hd dθ).
Check angle_dist_move_0_r.
...
  rewrite angle_dist_move_0_r; cycle 1. {
    (* lemma *)
    rewrite angle_add_comm.
    progress unfold angle_leb.
    remember (0 ≤? rngl_sin θ₀)%L as zs eqn:Hzs.
    remember (0 ≤? rngl_sin (θ₀ + dθ))%L as zstd eqn:Hzstd.
    symmetry in Hzs, Hzstd.
    destruct zs. {
      destruct zstd; [ | easy ].
      apply rngl_leb_le in Hzs, Hzstd.
      apply rngl_leb_le.
      rewrite angle_add_comm in Hθ.
...
      destruct Hθ as (H1, H2).
      apply (rngl_min_glb_lt_iff Hor) in H2.
      destruct H2 as (H2, H4).
      apply (rngl_min_glb_lt_iff Hor) in H2.
      destruct H2 as (H2, H3).
      rewrite angle_dist_angle_eucl_dist in H4. 2: {
        (* lemma *)
        apply rngl_sin_nonneg_angle_le_straight in Hzs, Hzstd.
        progress unfold angle_same_side.
        now rewrite Hzs, Hzstd.
      }
      rewrite angle_dist_angle_eucl_dist in H4. 2: {
        (* lemma *)
        apply rngl_sin_nonneg_angle_le_straight in Hzs, Hzstd.
        progress unfold angle_same_side.
        now rewrite Hzs, angle_straight_nonneg.
      }
      rewrite angle_dist_angle_eucl_dist in H2. 2: {
        (* lemma *)
        apply rngl_sin_nonneg_angle_le_straight in Hzs, Hzstd.
        progress unfold angle_same_side.
        now rewrite Hzs, Hzstd.
      }
Search (rngl_cos _ ≤ rngl_cos _)%L.
apply rngl_cos_decr.
...
Search (_ ≤ _ + _)%A.
        apply Complex.rngl_cos_le_anticompat_when_sin_nonneg; [ easy | easy | ].
...
...
        now apply rngl_sin_nonneg_angle_le_straight.
      }
      rewrite angle_dist_angle_eucl_dist in H3; cycle 1. {
        now apply rngl_sin_nonneg_angle_le_straight.
      } {
        apply angle_straight_nonneg.
      }
      rewrite angle_eucl_dist_move_0_r in H3.
      rewrite angle_add_comm, angle_add_sub in H3.
      apply angle_eucl_dist_lt_angle_eucl_dist in H3.
      do 2 rewrite angle_sub_0_r in H3.
...
rewrite rngl_cos_add.
Search (rngl_cos _ ≤ rngl_cos _)%L.
...
apply Complex.rngl_cos_le_anticompat_when_sin_nonneg; [ easy | easy | ].
progress unfold angle_leb.
...
      destruct (rngl_le_dec Hor 0 (rngl_sin dθ)) as [Hzsd| Hzsd]. {
        destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzc| Hzc]. {
          apply quadrant_1_rngl_cos_add_le_cos_l; [ easy | easy | easy | ].
          apply (rngl_le_trans Hor _ (rngl_cos θ₀)); [ easy | ].
          now apply (rngl_lt_le_incl Hor) in H3.
        }
        apply (rngl_nle_gt_iff Hor) in Hzc.
Search (rngl_cos _ ≤ rngl_cos _)%L.
Search (rngl_cos (_ + _) ≤ rngl_cos _)%L.
...
      apply rngl_cos_decr.
      split; [ | now apply rngl_sin_nonneg_angle_le_straight ].
      progress unfold angle_leb.
      apply rngl_leb_le in Hzs, Hzsd.
      rewrite Hzs, Hzsd.
      apply rngl_leb_le.
...
Search (rngl_cos _ ≤ rngl_cos _)%L.
Search (rngl_cos (_ + _) ≤ rngl_cos _)%L.
apply quadrant_1_rngl_cos_add_le_cos_l; [ easy | | | ].
3: {
...
    rewrite angle_add_comm.
    rewrite <- (angle_add_0_r θ₀) at 1.
    (* lemma *)
    apply angle_add_le_mono_l. 2: {
...
      rewrite rngl_sin_sub_sin.
      rewrite angle_add_overflow_div_2_div_2.
      rewrite angle_add_0_r.
Search (angle_add_overflow (_ /₂)).
        rewrite rngl_sin_sub_anticomm in H12z.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in H12z.
        apply (rngl_le_antisymm Hor) in Ht12s; [ clear H12z | easy ].
        apply eq_rngl_sin_0 in Ht12s.
        destruct Ht12s as [H1| H1]. {
          apply -> angle_sub_move_0_r in H1; subst θ2.
          rewrite angle_eucl_dist_diag.
          apply (rngl_sub_diag Hos).
        }
        apply -> angle_sub_move_r in H1; subst θ1.
        rewrite rngl_sin_add_straight_l in Ht1s.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Ht1s.
        apply (rngl_le_antisymm Hor) in Ht2s; [ clear Ht1s | easy ].
        apply eq_rngl_sin_0 in Ht2s.
        destruct Ht2s; subst θ2. {
          exfalso.
          rewrite angle_add_0_r in HHHH.
          cbn in HHHH.
          apply rngl_nlt_ge in HHHH.
          apply HHHH; clear HHHH.
          apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
        }
        rewrite angle_straight_add_straight.
        rewrite angle_eucl_dist_diag.
        rewrite angle_eucl_dist_symmetry.
        apply (rngl_sub_0_r Hos).
...
destruct (angle_le_dec (θ2 - θ1) angle_straight) as [H1| H1].
      apply angle_eucl_dist_sub_angle_eucl_dist; [ easy | easy | | easy ].
easy.
apply angle_nle_gt in H1.
...
Search (_ - _ ≤ angle_straight).
(*
Theorem angle_sub_le_straight :
  ∀ θ1 θ2, (θ1 - θ2 ≤ angle_straight → θ2 - θ1 ≤ angle_straight)%A.
Proof.
destruct_ac.
intros * H12.
progress unfold angle_leb in H12.
progress unfold angle_leb.
cbn - [ angle_sub ] in H12 |-*.
rewrite (rngl_leb_refl Hor) in H12 |-*.
remember (0 ≤? rngl_sin (θ1 - θ2))%L as zs12 eqn:Hzs12.
remember (0 ≤? rngl_sin (θ2 - θ1))%L as zs21 eqn:Hzs21.
symmetry in Hzs12, Hzs21.
destruct zs12. {
  destruct zs21. {
    apply rngl_leb_le.
    apply rngl_cos_bound.
  }
  apply rngl_leb_le in Hzs12.
  apply (rngl_leb_gt Hor) in Hzs21.
...
*)
      (* lemma *)
      progress unfold angle_leb in Ht12s.
      progress unfold angle_leb.
      cbn - [ angle_sub ] in Ht12s |-*.
      rewrite (rngl_leb_refl Hor) in Ht12s |-*.
      remember (0 ≤? rngl_sin (θ1 - θ2))%L as zs12 eqn:Hzs12.
      remember (0 ≤? rngl_sin (θ2 - θ1))%L as zs21 eqn:Hzs21.
      symmetry in Hzs12, Hzs21.
      destruct zs12; [ | easy ].
      destruct zs21. {
        apply rngl_leb_le.
        apply rngl_cos_bound.
      }
      apply (rngl_leb_le) in Hzs12.
      apply (rngl_leb_gt Hor) in Hzs21.
      clear Ht12s.
...
Search (0 ≤ rngl_sin (_ - _))%L.
...
Search (_ ≤ angle_straight)%A.
        progress unfold angle_leb in Ht1s.
        progress unfold angle_leb in Ht2s.
        progress unfold angle_leb in Ht12s.
        cbn - [ angle_sub ] in Ht1s, Ht2s, Ht12s.
        rewrite (rngl_leb_refl Hor) in Ht1s, Ht2s, Ht12s.
        remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
        remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
        symmetry in Hzs1, Hzs2.
        destruct zs1; [ | easy ].
        destruct zs2; [ | easy ].
...
        apply (rngl_sub_move_r Hop).
        rewrite (angle_eucl_dist_symmetry θ1).
        apply (rngl_le_antisymm Hor). {
          apply angle_eucl_dist_triangular.
        }
Search (_ - _ = _ → _)%L.
Search (_ - _ = _ ↔ _)%L.

Search (_ = _ - _ → _)%L.
Search (_ = _ - _ ↔ _)%L.
Search (_ = _ + _ → _)%L.
Search (_ = _ + _ ↔ _)%L.
        apply rngl_add_

Search (angle_eucl_dist _ _ + angle_eucl_dist _ _)%L.
        rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2.
...
        apply angle_le_angle_eucl_dist_le in H12z; [ | easy | easy ].
Search (angle_eucl_dist _ _ ≤ angle_eucl_dist _ _)%L.
...
          apply (rngl_le_0_sub Hop Hor).
Search (angle_eucl_dist _ _ - _)%L.
...
  rewrite angle_dist_move_0_r in Hθ |-*.
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
progress unfold rngl_dist in Hsc.
move η1 before ε.
destruct (angle_lt_dec θ₀ angle_straight) as [Hts| Hts]. {
...
*)

End a.
