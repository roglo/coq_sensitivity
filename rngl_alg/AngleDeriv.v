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
Require Import Trigo.SeqAngleIsCauchy.
Require Import Trigo.AngleTypeIsComplete.
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

(* end min max *)

Definition angle_diff θ1 θ2 := (angle_max θ1 θ2 - angle_min θ1 θ2)%A.
Definition angle_lt_sub θ1 θ2 θ3 := (0 < angle_diff θ1 θ2 < θ3)%A.

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
  split. {
    apply (rngl_lt_iff Hor).
    split; [ apply angle_eucl_dist_nonneg | ].
    intros H; symmetry in H.
    apply angle_eucl_dist_separation in H.
    subst θ.
    progress unfold angle_diff in Hθ.
    rewrite angle_sub_diag in Hθ.
    destruct Hθ as (H1, H2).
    now apply angle_lt_irrefl in H1.
  }
  destruct Hθ as (H1, H2).
  apply rngl_cos_lt_angle_eucl_dist_lt. {
    now apply (rngl_lt_le_incl Hor) in Hζ.
  }
  replace (rngl_cos (θ₀ - θ)) with (rngl_cos (angle_diff θ θ₀)). 2: {
    progress unfold angle_diff.
    destruct (angle_le_dec θ θ₀) as [Htt| Htt]. {
      rewrite (proj2 (angle_min_l_iff _ _) Htt).
      rewrite (proj2 (angle_max_r_iff _ _) Htt).
      easy.
    }
    apply angle_nle_gt in Htt.
    apply angle_lt_le_incl in Htt.
    rewrite rngl_cos_sub_comm.
    rewrite (proj2 (angle_min_r_iff _ _) Htt).
    rewrite (proj2 (angle_max_l_iff _ _) Htt).
    easy.
  }
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

Theorem angle_straight_lt_add_straight_r :
  ∀ θ,
  (angle_straight < θ + angle_straight)%A
  → (θ < angle_straight)%A.
Proof.
destruct_ac.
intros * Hs.
progress unfold angle_ltb in Hs.
progress unfold angle_ltb.
rewrite rngl_sin_add_straight_r in Hs.
rewrite rngl_cos_add_straight_r in Hs.
rewrite (rngl_leb_0_opp Hop Hor) in Hs.
cbn in Hs |-*.
rewrite (rngl_leb_refl Hor) in Hs |-*.
remember (rngl_sin θ ≤? 0)%L as sz eqn:Hsz.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hsz, Hzs.
destruct sz. {
  exfalso.
  apply rngl_ltb_lt in Hs.
  apply (rngl_opp_lt_compat Hop Hor) in Hs.
  apply rngl_nle_gt in Hs.
  apply Hs, rngl_cos_bound.
}
apply (rngl_leb_gt Hor) in Hsz.
destruct zs. {
  apply rngl_ltb_lt.
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_opp_1 in H; subst θ.
  now apply (rngl_lt_irrefl Hor) in Hsz.
}
apply (rngl_leb_gt Hor) in Hzs.
now apply (rngl_lt_asymm Hor) in Hzs.
Qed.

Theorem rngl_cos_derivative_lemma_4 :
  ∀ θ₀ ε,
  (0 < ε)%L
  → (0 < θ₀ < angle_straight)%A
  → ∃ (η : angle T) (ζ : T), (0 < ζ)%L ∧
    ∀ dθ : angle T,
    (0 < dθ < η)%A
    → (0 < angle_eucl_dist dθ 0 < ζ)%L
    → (rngl_dist
         ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_eucl_dist dθ 0)
         (- rngl_sin θ₀) < ε)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀ ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hε (Htz, Htls).
specialize rngl_sin_is_continuous as Hsc.
progress unfold continuous in Hsc.
progress unfold continuous_at in Hsc.
progress unfold is_limit_when_tending_to in Hsc.
specialize (Hsc θ₀ ε Hε).
destruct Hsc as (ζ1 & Hζ1 & Hsc).
progress unfold rngl_dist in Hsc.
move ζ1 before ε.
remember (angle_eucl_dist angle_right 0) as x.
remember (angle_eucl_dist θ₀ 0) as y.
exists angle_right.
exists (rngl_min4 x y (angle_eucl_dist θ₀ angle_straight) ζ1).
subst x y.
split. {
  apply rngl_min_glb_lt; [ | easy ].
  apply rngl_min_glb_lt. {
    apply rngl_min_glb_lt. {
      apply angle_eucl_dist_pos_angle_neq.
      apply neq_angle_neq; intros H.
      injection H; clear H; intros H1 H2.
      now apply (rngl_1_neq_0_iff Hon) in H1.
    }
    apply angle_eucl_dist_pos_angle_neq.
    intros H; rewrite H in Htz.
    now apply angle_lt_irrefl in Htz.
  }
  apply angle_eucl_dist_pos_angle_neq.
  intros H; rewrite H in Htls.
  now apply angle_lt_irrefl in Htls.
}
intros dθ Hdθ Hζ.
destruct Hζ as (H1, H2).
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H4).
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H3).
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H5).
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
    rewrite angle_mul_2_div_2, Htls, angle_add_0_r.
    rewrite angle_div_2_mul_2.
    rewrite (rngl_mul_div_assoc Hiv).
    rewrite (rngl_div_opp_l Hop Hiv).
    rewrite (rngl_div_div_swap Hic Hiv).
    rewrite (rngl_mul_div Hi1). 2: {
      intros H.
      rewrite H in H1.
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
    apply (rngl_le_lt_trans Hor _ (angle_eucl_dist dθ 0)); [ | easy ].
    apply angle_le_angle_eucl_dist_le; [ | easy | ]. 2: {
      apply angle_div_2_le.
    }
    apply angle_div_2_le_straight.
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
  rewrite angle_mul_2_div_2, Htls, angle_add_0_r.
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
  apply (rngl_le_lt_trans Hor _ (angle_eucl_dist dθ 0)); [ | easy ].
  apply angle_le_angle_eucl_dist_le; [ | easy | ]. 2: {
    apply angle_div_2_le.
  }
  apply angle_div_2_le_straight.
}
exfalso.
apply Htds; clear Htds.
apply (angle_le_trans _ angle_right).
now apply angle_lt_le_incl.
apply angle_right_le_straight.
Qed.

Theorem rngl_cos_derivative_lemma_5 :
  ∀ θ₀ ε,
  (0 < ε)%L
  → (angle_straight < θ₀)%A
  → ∃ (η : angle T) (ζ : T), (0 < ζ)%L ∧
    ∀ dθ : angle T,
    (0 < dθ < η)%A
    → (0 < angle_eucl_dist dθ 0 < ζ)%L
    → (rngl_dist
         ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_eucl_dist dθ 0)
         (- rngl_sin θ₀) < ε)%L.
Proof.
destruct_ac.
intros * Hε Htls.
change_angle_sub_l θ₀ angle_straight.
destruct (angle_eq_dec θ₀ 0) as [Htz| Htz]. {
  subst θ₀.
  rewrite angle_sub_0_r in Htls.
  now apply angle_lt_irrefl in Htls.
}
specialize (rngl_cos_derivative_lemma_4) as H1.
specialize (H1 (- θ₀)%A ε Hε).
progress unfold angle_sub in Htls.
rewrite angle_add_comm in Htls.
apply angle_straight_lt_add_straight_r in Htls.
assert (H : (0 < - θ₀ < angle_straight)%A). {
  split; [ | easy ].
  apply angle_lt_iff.
  split; [ apply angle_nonneg | ].
  intros H; symmetry in H.
  rewrite <- angle_opp_0 in H.
  now apply angle_opp_inj in H.
}
specialize (H1 H); clear H.
destruct H1 as (η & ζ & Hζ & H1).
exists η, ζ.
split; [ easy | ].
intros * Hdθ Hzd.
rewrite <- angle_add_sub_swap.
rewrite <- angle_add_sub_assoc.
rewrite rngl_cos_add_straight_l.
rewrite <- angle_add_opp_l.
rewrite rngl_cos_sub_straight_l.
rewrite rngl_sin_sub_straight_l.
progress unfold rngl_dist in H1.
progress unfold rngl_dist.
rewrite <- rngl_sin_opp in H1.
rewrite angle_opp_involutive in H1.
rewrite rngl_cos_opp in H1.
rewrite <- (rngl_abs_opp Hop Hor).
do 2 rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_opp_sub_swap Hop).
rewrite <- (rngl_div_opp_l Hop Hiv).
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_l Hop).
now apply H1.
Qed.

Theorem angle_lt_trans : ∀ θ1 θ2 θ3, (θ1 < θ2 → θ2 < θ3 → θ1 < θ3)%A.
Proof.
intros * H12 H23.
apply (angle_le_lt_trans _ θ2); [ | easy ].
now apply angle_lt_le_incl in H12.
Qed.

Theorem angle_min_glb_lt_iff :
  ∀ θ1 θ2 θ3, (θ1 < angle_min θ2 θ3)%A ↔ (θ1 < θ2)%A ∧ (θ1 < θ3)%A.
Proof.
intros.
progress unfold angle_min.
remember (θ2 ≤? θ3)%A as t23 eqn:Ht23.
symmetry in Ht23.
split; intros H1. {
  destruct t23. {
    split; [ easy | ].
    now apply (angle_lt_le_trans _ θ2).
  }
  split; [ | easy ].
  apply angle_leb_gt in Ht23.
  now apply (angle_lt_trans _ θ3).
}
now destruct t23.
Qed.

(* to be completed
Print is_derivative.
Print derivative_at.
Print is_limit_when_tending_to_neighbourhood.
(*
Il faut que lt_suba soit du genre
  lt_suba a b c ↔ 0 < |a-b] < c

Il faut que da soit tel que
    0 < |a-b| < c ↔ d(a,b) < d(c,0)
*)
Theorem glop :
  ∀ a b c,
  (c ≤ angle_straight)%A
  → angle_lt_sub a b c ↔ (angle_eucl_dist a b < angle_eucl_dist c 0)%L.
Proof.
destruct_ac.
intros * Hcs.
progress unfold angle_lt_sub.
progress unfold angle_diff.
split; intros H1. {
  apply (rngl_lt_iff Hor).
  split. {
    rewrite angle_eucl_dist_move_0_r.
    apply rngl_cos_le_iff_angle_eucl_le.
    destruct (angle_le_dec a b) as [Hab| Hab]. {
      rewrite (proj2 (angle_max_r_iff _ _) Hab) in H1.
      rewrite (proj2 (angle_min_l_iff _ _) Hab) in H1.
      progress unfold angle_ltb in H1.
      progress unfold angle_leb in Hab.
      cbn - [ angle_sub ] in H1.
      rewrite (rngl_leb_refl Hor) in H1.
      destruct H1 as (H1, H2).
      rewrite rngl_cos_sub_comm.
      apply rngl_sin_nonneg_angle_le_straight in Hcs.
      generalize Hcs; intros H.
      apply rngl_leb_le in H.
      rewrite H in H2; clear H.
      remember (0 ≤? rngl_sin a)%L as zsa eqn:Hzsa.
      remember (0 ≤? rngl_sin b)%L as zsb eqn:Hzsb.
      remember (0 ≤? rngl_sin (b - a))%L as zba eqn:Hzba.
      symmetry in Hzsa, Hzsb, Hzba.
      destruct zba; [ | easy ].
      apply rngl_ltb_lt in H2.
      now apply (rngl_lt_le_incl Hor) in H2.
    }
    rewrite rngl_cos_sub_comm.
    apply angle_nle_gt in Hab.
    generalize Hab; intros H.
    apply angle_lt_le_incl in H.
    rewrite (proj2 (angle_max_l_iff _ _) H) in H1.
    rewrite (proj2 (angle_min_r_iff _ _) H) in H1.
    clear H.
    progress unfold angle_ltb in H1, Hab.
    cbn - [ angle_sub ] in H1.
    rewrite (rngl_leb_refl Hor) in H1.
    destruct H1 as (H1, H2).
    rewrite rngl_cos_sub_comm.
    apply rngl_sin_nonneg_angle_le_straight in Hcs.
    generalize Hcs; intros H.
    apply rngl_leb_le in H.
    rewrite H in H2; clear H.
    remember (0 ≤? rngl_sin a)%L as zsa eqn:Hzsa.
    remember (0 ≤? rngl_sin b)%L as zsb eqn:Hzsb.
    remember (0 ≤? rngl_sin (a - b))%L as zab eqn:Hzab.
    symmetry in Hzsa, Hzsb, Hzab.
    destruct zab; [ | easy ].
    apply rngl_ltb_lt in H2.
    now apply (rngl_lt_le_incl Hor) in H2.
  }
  intros Hab.
  rewrite angle_eucl_dist_move_0_r in Hab.
Search (angle_eucl_dist _ _ = angle_eucl_dist _ _).
...

Theorem rngl_cos_derivative :
  is_derivative angle_eucl_dist rngl_dist angle_lt_sub
    rngl_cos (λ θ, (- rngl_sin θ)%L).
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀ ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
apply is_derivative_iff.
intros θ₀ ε Hε.
destruct (angle_eq_dec θ₀ 0) as [Htz| Htz]. {
  subst θ₀.
  cbn.
  exists angle_right, ε.
  split; [ easy | ].
  progress unfold angle_lt_sub.
  progress unfold angle_diff.
  intros dθ Hzθ Hdθ.
  rewrite (proj2 (angle_max_l_iff _ _)) in Hzθ; [ | apply angle_nonneg ].
  rewrite (proj2 (angle_min_r_iff _ _)) in Hzθ; [ | apply angle_nonneg ].
  rewrite angle_sub_0_r in Hzθ.
  rewrite (rngl_opp_0 Hop).
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
    intros H; rewrite H in Hdθ.
    destruct Hdθ as (H1, _).
    now apply (rngl_lt_irrefl Hor) in H1.
  }
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    apply angle_eucl_dist_nonneg.
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  eapply (rngl_lt_le_trans Hor _ ε); [ easy | ].
  rewrite <- (rngl_mul_1_r Hon ε) at 1.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_le_add_l Hor).
  apply (rngl_0_le_1 Hon Hos Hor).
}
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  subst θ₀.
  cbn.
  exists angle_right, ε.
  split; [ easy | ].
  progress unfold angle_lt_sub.
  intros dθ Hzθ Hdθ.
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_opp_0 Hop).
  rewrite rngl_cos_angle_eucl_dist_straight_r.
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
    apply angle_eucl_dist_nonneg.
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  eapply (rngl_lt_le_trans Hor _ ε); [ easy | ].
  rewrite <- (rngl_mul_1_r Hon ε) at 1.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_le_add_l Hor).
  apply (rngl_0_le_1 Hon Hos Hor).
}
progress unfold angle_lt_sub.
enough (H :
  ∃ η ζ, (0 < ζ)%L ∧
  ∀ dθ,
  (0 < dθ < η)%A
  → (0 < angle_eucl_dist dθ 0 < ζ)%L
  → (rngl_dist
        ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_eucl_dist dθ 0)
        (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & ζ & Hζ & Hd).
  exists (angle_min η angle_straight).
  exists ζ.
  split; [ easy | ].
  intros θ Hη Hθ.
  remember (θ - θ₀)%A as dθ eqn:H.
  symmetry in H.
  apply angle_sub_move_r in H.
  subst θ.
  assert (H : (0 < dθ < η)%A). {
    destruct Hη as (H1, H2).
    apply angle_min_glb_lt_iff in H2.
    destruct H2 as (H2, H3).
    progress unfold angle_diff in H3.
...
    progress unfold angle_diff in Hη.
    destruct (angle_le_dec θ₀ (dθ + θ₀)) as [Htt| Htt]. {
      rewrite (proj2 (angle_max_l_iff _ _) Htt) in Hη.
      rewrite (proj2 (angle_min_r_iff _ _) Htt) in Hη.
      now rewrite angle_add_sub in Hη.
    }
    apply angle_nle_gt in Htt.
exfalso.
rewrite angle_eucl_dist_move_0_r in Hθ.
rewrite angle_add_sub in Hθ.
destruct Hθ as (H1, H2).
apply (rngl_min_glb_lt_iff Hor) in H2.
destruct H2 as (H2, H3).
apply angle_nle_gt in Htt.
apply Htt; clear Htt.
progress unfold angle_leb.
rewrite angle_add_comm.
remember (0 ≤? rngl_sin θ₀)%L as zs eqn:Hzs.
symmetry in Hzs.
remember (0 ≤? rngl_sin (θ₀ + dθ))%L as zsd eqn:Hzsd.
symmetry in Hzsd.
destruct zs. {
  destruct zsd; [ | easy ].
  apply rngl_leb_le in Hzs, Hzsd.
  apply rngl_leb_le.
Search (rngl_cos _ ≤ rngl_cos _)%L.
apply rngl_cos_add_le_cos; try easy.
now left.
Search (angle_eucl_dist
...
Search (rngl_cos (_ + _) ≤ rngl_cos _)%L.
apply quadrant_1_rngl_cos_add_le_cos_l; try easy.
...
Search (angle_eucl_dist _ _ ≤ angle_eucl_dist _ _)%L.
Search (angle_eucl_dist _ _ < angle_eucl_dist _ _)%L.
...
    generalize Htt; intros H.
    apply angle_lt_le_incl in H.
    rewrite (proj2 (angle_max_r_iff _ _) H) in Hη.
    rewrite (proj2 (angle_min_l_iff _ _) H) in Hη.
    clear H.
    rewrite angle_sub_add_distr in Hη.
    rewrite angle_sub_sub_swap in Hη.
    rewrite angle_sub_diag in Hη.
    rewrite angle_sub_0_l in Hη.
...
  specialize (Hd dθ Hη).
  rewrite angle_eucl_dist_move_0_r in Hθ |-*.
  rewrite angle_add_sub in Hθ |-*.
  rewrite angle_add_comm.
  now apply Hd.
...
}
destruct (angle_lt_dec θ₀ angle_straight) as [Htls| Htls]. {
  apply (rngl_cos_derivative_lemma_4 _ _ Hε).
  split; [ | easy ].
  apply angle_lt_iff.
  split; [ apply angle_nonneg | ].
  easy.
} {
  apply angle_nlt_ge in Htls.
  change_angle_sub_r θ₀ angle_straight.
  apply (rngl_cos_derivative_lemma_5 _ _ Hε).
  now apply angle_lt_iff.
}
Qed.

Theorem rngl_sin_derivative :
  is_derivative angle_eucl_dist rngl_dist angle_lt_sub rngl_sin rngl_cos.
Proof.
destruct_ac.
intros θ₀.
specialize (rngl_cos_derivative (θ₀ + angle_right))%A as H1.
intros ε Hε.
specialize (H1 ε Hε).
rewrite rngl_cos_add_right_r in H1.
rewrite rngl_sin_add_right_r in H1.
destruct H1 as (η & H1).
exists η.
progress unfold rngl_dist in H1 |-*.
progress unfold angle_lt_sub in H1 |-*.
intros θ Hθ.
specialize (H1 (θ + angle_right))%A.
rewrite rngl_cos_add_right_r in H1.
rewrite angle_sub_add_distr in H1.
rewrite angle_sub_sub_swap in H1.
rewrite angle_add_sub in H1.
specialize (H1 Hθ).
do 2 rewrite (rngl_sub_opp_r Hop) in H1.
rewrite angle_eucl_dist_move_0_r in H1.
rewrite angle_sub_add_distr in H1.
rewrite angle_sub_sub_swap in H1.
rewrite angle_add_sub in H1.
rewrite <- angle_eucl_dist_move_0_r in H1.
rewrite <- (rngl_abs_opp Hop Hor) in H1.
rewrite (rngl_opp_add_distr Hop) in H1.
rewrite (rngl_opp_sub_swap Hop) in H1.
rewrite <- (rngl_div_opp_l Hop Hiv) in H1.
rewrite (rngl_opp_add_distr Hop) in H1.
rewrite (rngl_sub_opp_r Hop) in H1.
rewrite (rngl_add_opp_l Hop) in H1.
easy.
Qed.
*)

End a.
