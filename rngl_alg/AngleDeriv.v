(* derivation of trigonometric functions *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import Trigo.RealLike.

Require Import Trigo.Angle.
Require Import Trigo.AngleDiv2.

Require Import Trigo.AngleDiv2Add.
Require Import Trigo.SeqAngleIsCauchy.
Require Import Trigo.TrigoWithoutPiExt.
Require Import Trigo.Angle_order.

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

Theorem angle_add_overflow_angle_lt_abs_lt :
  ∀ ε θ θ₀,
  angle_add_overflow θ θ₀ = true
  → (θ < θ₀)%A
  → (rngl_abs (rngl_sin θ₀ - rngl_sin ((θ + θ₀) /₂)) < ε)%L
  → (rngl_abs
        (rngl_sin θ₀ + (rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀) <
     ε)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hov Htt Hε.
  rewrite (H1 (rngl_abs _)), (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hov Htt Hε.
rewrite rngl_cos_sub_cos.
rewrite Hov, Htt.
do 2 rewrite rngl_sin_add_straight_r.
do 2 rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_div_opp_l Hop Hiv).
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_mul_div_assoc Hiv).
rewrite angle_eucl_dist_is_sqrt.
progress unfold angle_div_2 at 2.
cbn - [ angle_div_2 angle_sub ].
rewrite rngl_cos_sub_comm.
assert (Hz1c : (0 ≤ 1 - rngl_cos (θ₀ - θ))%L). {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
assert (Hz2 : (0 < 2)%L) by apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
assert (Hze2 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hos Hor).
assert (H2nz : 2%L ≠ 0%L) by apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
assert (Hsnz : √2 ≠ 0%L). {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1. 2: {
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  now apply (rngl_2_neq_0 Hon Hos Hc1 Hor) in H1.
}
remember (1 - _)%L as a.
assert (Hsanz : √a ≠ 0%L). {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1; [ | easy ].
  subst a.
  apply -> (rngl_sub_move_0_r Hop) in H1.
  symmetry in H1.
  apply eq_rngl_cos_1 in H1.
  apply -> angle_sub_move_0_r in H1.
  subst θ.
  now apply angle_lt_irrefl in Htt.
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor _ _ Hz1c Hz2).
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | ]. 2: {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1. 2: {
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
  apply (rngl_eq_mul_0_r Hos Hii) in H1; [ | easy ].
  move H1 at top.
  subst a.
  now rewrite (rl_sqrt_0 Hon Hop Hor Hii) in Hsanz.
}
rewrite rl_sqrt_mul; [ | easy | easy ].
rewrite <- (rngl_mul_mul_swap Hic √_).
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_diag Hon Hiq); [ | easy ].
rewrite (rngl_mul_comm Hic).
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem angle_add_overflow_angle_ge_abs_lt :
  ∀ ε θ θ₀,
  angle_add_overflow θ θ₀ = true
  → (θ₀ ≤ θ)%A
  → angle_eucl_dist θ θ₀ ≠ 0%L
  → (rngl_abs (rngl_sin θ₀ + rngl_sin ((θ + θ₀) /₂)) < ε)%L
  → (rngl_abs
        (rngl_sin θ₀ + (rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀) <
     ε)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hov Htt Hθ Hε.
  rewrite (H1 (rngl_abs _)), (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hov Htt Hθ Hε.
rewrite rngl_cos_sub_cos.
apply angle_ltb_ge in Htt.
rewrite Hov, Htt.
rewrite rngl_sin_add_straight_r.
rewrite angle_add_0_r.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_opp_involutive Hop).
rewrite <- (rngl_mul_div_assoc Hiv).
rewrite angle_eucl_dist_is_sqrt.
progress unfold angle_div_2 at 2.
cbn - [ angle_div_2 angle_sub ].
rewrite rngl_cos_sub_comm.
assert (Hz1c : (0 ≤ 1 - rngl_cos (θ₀ - θ))%L). {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
assert (Hz2 : (0 < 2)%L) by apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
assert (Hze2 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hos Hor).
assert (H2nz : 2%L ≠ 0%L) by apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
assert (Hsnz : √2 ≠ 0%L). {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1. 2: {
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  now apply (rngl_2_neq_0 Hon Hos Hc1 Hor) in H1.
}
remember (1 - _)%L as a.
assert (Hsanz : √a ≠ 0%L). {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1; [ | easy ].
  subst a.
  apply -> (rngl_sub_move_0_r Hop) in H1.
  symmetry in H1.
  apply eq_rngl_cos_1 in H1.
  apply -> angle_sub_move_0_r in H1.
  subst θ.
  now rewrite angle_eucl_dist_diag in Hθ.
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | ]. 2: {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1. 2: {
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
  apply (rngl_eq_mul_0_r Hos Hii) in H1; [ | easy ].
  rewrite H1 in Hsanz.
  now rewrite (rl_sqrt_0 Hon Hop Hor Hii) in Hsanz.
}
rewrite rl_sqrt_mul; [ | easy | easy ].
rewrite <- (rngl_mul_mul_swap Hic √_).
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_diag Hon Hiq); [ | easy ].
rewrite (rngl_mul_comm Hic).
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem angle_add_not_overflow_angle_lt_abs_lt :
  ∀ ε θ θ₀,
  angle_add_overflow θ θ₀ = false
  → (θ < θ₀)%A
  → (rngl_abs (rngl_sin θ₀ + rngl_sin ((θ + θ₀) /₂)) < ε)%L
  → (rngl_abs
        (rngl_sin θ₀ + (rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀) <
     ε)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hov Htt Hε.
  rewrite (H1 (rngl_abs _)), (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hov Htt Hε.
rewrite rngl_cos_sub_cos.
rewrite Hov, Htt.
rewrite rngl_sin_add_straight_r.
rewrite angle_add_0_r.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_opp_involutive Hop).
rewrite <- (rngl_mul_div_assoc Hiv).
rewrite angle_eucl_dist_is_sqrt.
progress unfold angle_div_2 at 2.
cbn - [ angle_div_2 angle_sub ].
rewrite rngl_cos_sub_comm.
assert (Hz1c : (0 ≤ 1 - rngl_cos (θ₀ - θ))%L). {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
assert (Hz2 : (0 < 2)%L) by apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
assert (Hze2 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hos Hor).
assert (H2nz : 2%L ≠ 0%L) by apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
assert (Hsnz : √2 ≠ 0%L). {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1. 2: {
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  now apply (rngl_2_neq_0 Hon Hos Hc1 Hor) in H1.
}
remember (1 - _)%L as a.
assert (Hsanz : √a ≠ 0%L). {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1; [ | easy ].
  subst a.
  apply -> (rngl_sub_move_0_r Hop) in H1.
  symmetry in H1.
  apply eq_rngl_cos_1 in H1.
  apply -> angle_sub_move_0_r in H1.
  subst θ.
  now apply angle_lt_irrefl in Htt.
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | ]. 2: {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1. 2: {
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
  apply (rngl_eq_mul_0_r Hos Hii) in H1; [ | easy ].
  rewrite H1 in Hsanz.
  now rewrite (rl_sqrt_0 Hon Hop Hor Hii) in Hsanz.
}
rewrite rl_sqrt_mul; [ | easy | easy ].
rewrite <- (rngl_mul_mul_swap Hic √_).
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_diag Hon Hiq); [ | easy ].
rewrite (rngl_mul_comm Hic).
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem angle_add_not_overflow_angle_ge_abs_lt :
  ∀ ε θ θ₀,
  angle_add_overflow θ θ₀ = false
  → (θ₀ ≤ θ)%A
  → angle_eucl_dist θ θ₀ ≠ 0%L
  → (rngl_abs (rngl_sin θ₀ - rngl_sin ((θ + θ₀) /₂)) < ε)%L
  → (rngl_abs
        (rngl_sin θ₀ + (rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀) <
     ε)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hov Htt Hθ Hε.
  rewrite (H1 (rngl_abs _)), (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hov Htt Hθ Hε.
rewrite rngl_cos_sub_cos.
apply angle_ltb_ge in Htt.
rewrite Hov, Htt.
do 2 rewrite angle_add_0_r.
rewrite (rngl_div_opp_l Hop Hiv).
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_mul_div_assoc Hiv).
rewrite angle_eucl_dist_is_sqrt.
progress unfold angle_div_2 at 2.
cbn - [ angle_div_2 angle_sub ].
rewrite rngl_cos_sub_comm.
assert (Hz1c : (0 ≤ 1 - rngl_cos (θ₀ - θ))%L). {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
assert (Hz2 : (0 < 2)%L) by apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
assert (Hze2 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hos Hor).
assert (H2nz : 2%L ≠ 0%L) by apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
assert (Hsnz : √2 ≠ 0%L). {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1. 2: {
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  now apply (rngl_2_neq_0 Hon Hos Hc1 Hor) in H1.
}
remember (1 - _)%L as a.
assert (Hsanz : √a ≠ 0%L). {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1; [ | easy ].
  subst a.
  apply -> (rngl_sub_move_0_r Hop) in H1.
  symmetry in H1.
  apply eq_rngl_cos_1 in H1.
  apply -> angle_sub_move_0_r in H1.
  subst θ.
  now rewrite angle_eucl_dist_diag in Hθ.
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor _ _ Hz1c Hz2).
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | ]. 2: {
  intros H1.
  apply (eq_rl_sqrt_0 Hon Hos) in H1. 2: {
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
  apply (rngl_eq_mul_0_r Hos Hii) in H1; [ | easy ].
  move H1 at top.
  subst a.
  now rewrite (rl_sqrt_0 Hon Hop Hor Hii) in Hsanz.
}
rewrite rl_sqrt_mul; [ | easy | easy ].
rewrite <- (rngl_mul_mul_swap Hic √_).
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_diag Hon Hiq); [ | easy ].
rewrite (rngl_mul_comm Hic).
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
now rewrite (rngl_mul_1_l Hon).
Qed.

(* to be completed
Theorem rngl_cos_derivative :
  is_derivative angle_eucl_dist rngl_dist rngl_cos (λ θ, (- rngl_sin θ))%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ ε Hε.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros θ₀ ε Hε.
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L →
  (rngl_dist
     ((rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀)
     (- rngl_sin θ₀) < ε)%L). {
  easy.
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L →
  (rngl_abs
     (rngl_sin θ₀ + (rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀) <
     ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
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
clear - H Hor Hop Hon.
  destruct H as (η & Hzη & H).
  exists η.
  split; [ easy | ].
  intros θ Hθ.
  specialize (H θ Hθ).
  cbn - [ angle_div_2 ] in H.
  remember (angle_add_overflow θ θ₀) as ov eqn:Hov.
  remember (θ <? θ₀)%A as tt eqn:Htt.
  symmetry in Hov, Htt.
  destruct ov. {
    destruct tt. {
      cbn - [ angle_div_2 ] in H.
      rewrite (rngl_mul_opp_l Hop) in H.
      rewrite (rngl_add_opp_r Hop) in H.
      rewrite (rngl_mul_1_l Hon) in H.
      now apply angle_add_overflow_angle_lt_abs_lt.
    } {
      rewrite (rngl_mul_1_l Hon) in H.
      apply angle_ltb_ge in Htt.
      destruct Hθ as (Hθ, _).
      apply (rngl_lt_iff Hor) in Hθ.
      now apply angle_add_overflow_angle_ge_abs_lt.
    }
  } {
    destruct tt. {
      rewrite (rngl_mul_1_l Hon) in H.
      destruct Hθ as (Hθ, _).
      now apply angle_add_not_overflow_angle_lt_abs_lt.
    } {
      cbn - [ angle_div_2 ] in H.
      rewrite (rngl_mul_opp_l Hop) in H.
      rewrite (rngl_add_opp_r Hop) in H.
      rewrite (rngl_mul_1_l Hon) in H.
      destruct Hθ as (Hθ, _).
      apply (rngl_lt_iff Hor) in Hθ.
      destruct Hθ as (_, Hθ).
      apply not_eq_sym in Hθ.
      apply angle_ltb_ge in Htt.
      now apply angle_add_not_overflow_angle_ge_abs_lt.
    }
  }
}
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
