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

(* min max on angles *)

Definition angle_min θ1 θ2 := if (θ1 ≤? θ2)%A then θ1 else θ2.

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

Definition old_derivative_at {A} (da : A → A → T) (db : T → T → T) lt_suba
    f f' a :=
  let g x := ((f x - f a) / da x a)%L in
  old_is_limit_when_tending_to_neighbourhood da db lt_suba g a (f' a).

Definition old_is_derivative {A} (da : A → A → T) (db : T → T → T)
    lt_suba f f' :=
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
  ∀ θ,
  ((2 * θ) /₂ = θ + if θ <? angle_straight then 0 else angle_straight)%A.
Proof.
destruct_ac.
intros.
remember (θ <? angle_straight)%A as ts eqn:Hts.
symmetry in Hts.
destruct ts. {
  rewrite angle_add_0_r.
  rewrite <- angle_mul_nat_div_2; [ apply angle_div_2_mul_2 | cbn ].
  rewrite angle_add_0_r.
  rewrite Bool.orb_false_r.
  now apply angle_lt_straight_add_same_not_overflow.
} {
  progress unfold angle_ltb in Hts.
  change_angle_add_r θ angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hts.
  cbn in Hts.
  rewrite (rngl_leb_0_opp Hop Hor) in Hts.
  rewrite (rngl_leb_refl Hor) in Hts.
  rewrite angle_mul_sub_distr_l.
  rewrite (angle_mul_2_l angle_straight).
  rewrite angle_straight_add_straight.
  rewrite angle_sub_0_r.
  remember (rngl_sin θ ≤? 0)%L as tz eqn:Htz.
  symmetry in Htz.
  destruct tz. {
    apply rngl_leb_le in Htz.
    apply (rngl_ltb_ge_iff Hor) in Hts.
    apply (rngl_opp_le_compat Hop Hor) in Hts.
    apply (rngl_lt_eq_cases Hor) in Hts.
    destruct Hts as [Hts| Hts]. {
      exfalso.
      apply rngl_nle_gt in Hts.
      apply Hts, rngl_cos_bound.
    }
    symmetry in Hts.
    apply eq_rngl_cos_1 in Hts.
    subst θ.
    rewrite angle_mul_0_r.
    apply angle_0_div_2.
  }
  clear Hts.
  apply (rngl_leb_gt Hor) in Htz.
  rewrite <- angle_mul_nat_div_2; [ apply angle_div_2_mul_2 | cbn ].
  rewrite angle_add_0_r.
  rewrite Bool.orb_false_r.
  apply angle_lt_straight_add_same_not_overflow.
  now apply rngl_sin_pos_lt_straight.
}
Qed.

Definition rngl_min4 a b c d :=
  rngl_min (rngl_min (rngl_min a b) c) d.

End a.
