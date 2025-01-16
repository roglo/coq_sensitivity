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
Require Import Trigo.AngleDiv2.
Require Import Trigo.AngleDiv2Add.
Require Import Trigo.SeqAngleIsCauchy.
Require Import Trigo.AngleTypeIsComplete.
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

Theorem angle_lt_asymm : ∀ a b, (a < b)%A → ¬ (b < a)%A.
Proof.
destruct_ac.
intros * Hab Hba.
progress unfold angle_ltb in Hab.
progress unfold angle_ltb in Hba.
remember (0 ≤? rngl_sin a)%L as za eqn:Hza.
remember (0 ≤? rngl_sin b)%L as zb eqn:Hzb.
symmetry in Hza, Hzb.
destruct za, zb; [ | easy | easy | ].
apply rngl_ltb_lt in Hab, Hba.
now apply (rngl_lt_asymm Hor) in Hab.
apply rngl_ltb_lt in Hab, Hba.
now apply (rngl_lt_asymm Hor) in Hab.
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

Theorem angle_min_comm : ∀ a b, angle_min a b = angle_min b a.
Proof.
intros.
progress unfold angle_min.
remember (a ≤? b)%A as ab eqn:Hab.
remember (b ≤? a)%A as ba eqn:Hba.
symmetry in Hab, Hba.
destruct ab, ba; [ | easy | easy | ].
now apply angle_le_antisymm.
apply angle_leb_gt in Hab, Hba.
now apply angle_lt_asymm in Hab.
Qed.

Theorem angle_max_comm : ∀ a b, angle_max a b = angle_max b a.
Proof.
intros.
progress unfold angle_max.
remember (a ≤? b)%A as ab eqn:Hab.
remember (b ≤? a)%A as ba eqn:Hba.
symmetry in Hab, Hba.
destruct ab, ba; [ | easy | easy | ].
now apply angle_le_antisymm.
apply angle_leb_gt in Hab, Hba.
now apply angle_lt_asymm in Hab.
Qed.

(* end min max *)

Definition angle_diff θ1 θ2 := (angle_max θ1 θ2 - angle_min θ1 θ2)%A.
Definition angle_lt_sub θ1 θ2 θ3 := (0 < angle_diff θ1 θ2 < θ3)%A.

Theorem angle_diff_comm : ∀ θ1 θ2, angle_diff θ1 θ2 = angle_diff θ2 θ1.
Proof.
intros.
progress unfold angle_diff.
now rewrite angle_max_comm, angle_min_comm.
Qed.

Theorem angle_lt_sub_comm_iff :
  ∀ θ1 θ2 θ3, angle_lt_sub θ1 θ2 θ3 ↔ angle_lt_sub θ2 θ1 θ3.
Proof.
intros.
progress unfold angle_lt_sub.
now rewrite angle_diff_comm.
Qed.

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

Theorem angle_is_mul_2_div_2 :
  ∀ θ, θ = ((2 * θ) /₂ + if θ <? angle_straight then 0 else angle_straight)%A.
Proof.
intros.
rewrite angle_mul_2_div_2.
destruct (θ <? angle_straight)%A; [ now do 2 rewrite angle_add_0_r | ].
rewrite <- angle_add_assoc.
rewrite angle_straight_add_straight.
symmetry.
apply angle_add_0_r.
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

Theorem angle_eucl_dist_eq_diag_r :
  ∀ θ1 θ2 θ3,
  angle_eucl_dist θ1 θ3 = angle_eucl_dist θ2 θ3 ↔
  θ1 = θ2 ∨ (θ1 - θ3 = θ3 - θ2)%A.
Proof.
intros.
split; intros H12. {
  apply angle_eucl_dist_eq_angle_eucl_dist in H12.
  destruct H12 as [H12| H12]. {
    left.
    rewrite (angle_add_comm θ3) in H12.
    apply (f_equal (λ θ, (θ - θ3)%A)) in H12.
    now do 2 rewrite angle_add_sub in H12.
  } {
    right.
    rewrite angle_add_move_r in H12.
    subst θ1.
    rewrite angle_sub_sub_swap.
    now rewrite angle_add_sub.
  }
} {
  apply angle_eucl_dist_eq_angle_eucl_dist.
  destruct H12 as [H12| H12]. {
    left.
    subst θ1.
    apply angle_add_comm.
  } {
    right.
    rewrite angle_sub_move_r in H12.
    subst θ1.
    rewrite angle_add_add_swap.
    now rewrite angle_sub_add.
  }
}
Qed.

Theorem angle_lt_sub_prop :
  ∀ θ1 θ2 θ3,
  angle_lt_sub θ1 θ2 θ3
  → (θ3 ≤ angle_straight)%A
  → (θ1 - θ2)%A = θ3 ∨ (θ1 - θ2)%A = (- θ3)%A
  → (θ1 ≤ θ2)%A
  → False.
Proof.
destruct_ac.
intros a b c H1 Hcs Hab Hab'.
progress unfold angle_lt_sub in H1.
progress unfold angle_diff in H1.
rewrite (proj2 (angle_max_r_iff _ _) Hab') in H1.
rewrite (proj2 (angle_min_l_iff _ _) Hab') in H1.
destruct Hab as [Hab| Hab]. {
  apply angle_sub_move_r in Hab.
  subst a.
  rewrite angle_sub_add_distr in H1.
  rewrite angle_sub_sub_swap in H1.
  rewrite angle_sub_diag in H1.
  rewrite angle_sub_0_l in H1.
  progress unfold angle_ltb in H1.
  cbn in H1.
  rewrite (rngl_leb_refl Hor) in H1.
  rewrite (rngl_leb_0_opp Hop Hor) in H1.
  generalize Hcs; intros H.
  apply rngl_sin_nonneg_angle_le_straight in H.
  apply rngl_leb_le in H.
  rewrite H in H1.
  destruct H1 as (H1, H2).
  destruct (rngl_sin c ≤? 0)%L; [ | easy ].
  apply rngl_ltb_lt in H2.
  now apply (rngl_lt_irrefl Hor) in H2.
}
apply (f_equal angle_opp) in Hab.
rewrite angle_opp_sub_distr in Hab.
rewrite angle_opp_involutive in Hab.
subst c.
destruct H1 as (H1, H2).
now apply angle_lt_irrefl in H2.
Qed.

Theorem angle_lt_sub_eucl_dist :
  ∀ a b c,
  (c ≤ angle_straight)%A
  → angle_lt_sub a b c
  → (angle_eucl_dist a b < angle_eucl_dist c 0)%L.
Proof.
destruct_ac.
intros * Hcs H1.
apply rngl_cos_lt_iff_angle_eucl_lt.
rewrite angle_sub_0_r.
destruct (angle_le_dec a b) as [Hab| Hab]. {
  progress unfold angle_lt_sub in H1.
  progress unfold angle_diff in H1.
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
  now apply rngl_ltb_lt in H2.
}
rewrite rngl_cos_sub_comm.
apply angle_nle_gt in Hab.
generalize Hab; intros H.
apply angle_lt_le_incl in H.
progress unfold angle_lt_sub in H1.
progress unfold angle_diff in H1.
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
now apply rngl_ltb_lt in H2.
Qed.

(* to be completed - peut-être à abandonner...
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
enough (H :
  ∃ η ζ, (0 < ζ)%L ∧
  ∀ dθ,
  (0 < dθ < η)%A
  → (0 < angle_eucl_dist dθ 0 < ζ)%L
  → (rngl_dist
        ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_eucl_dist dθ 0)
        (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & ζ & Hζ & Hd).
  progress unfold angle_lt_sub.
  progress unfold angle_diff.
(* problème : angle_diff et angle_eucl_dist ont le même problème :
   on ne sait pas dans quelle direction se trouve dθ ;
   la solution par angle_lt_sub ne permet pas de résoudre
   la question *)
Inspect 1.
(* mais alors pourquoi angle_lt_sub_eucl_dist est une implication
   et pas une équivalence, alors ? *)
...
  exists (angle_min η angle_right).
  exists ζ.
  split; [ easy | ].
  intros θ Hη Hθ.
  remember (θ - θ₀)%A as dθ eqn:H.
  symmetry in H.
  apply angle_sub_move_r in H.
  subst θ.
  rewrite angle_eucl_dist_move_0_r.
  rewrite angle_add_sub.
  rewrite angle_add_comm.
  rewrite angle_eucl_dist_move_0_r in Hθ.
  rewrite angle_add_sub in Hθ.
  apply Hd; [ | easy ].
  destruct Hη as (H1, H2).
  apply angle_min_glb_lt_iff in H2.
  destruct H2 as (H2, H3).
  progress unfold angle_diff in H1.
  progress unfold angle_diff in H2.
  progress unfold angle_diff in H3.
  destruct (angle_le_dec θ₀ (dθ + θ₀)) as [Htt| Htt]. {
    rewrite (proj2 (angle_max_l_iff _ _) Htt) in H1, H2, H3.
    rewrite (proj2 (angle_min_r_iff _ _) Htt) in H1, H2, H3.
    now rewrite angle_add_sub in H1, H2, H3.
  }
  apply angle_nle_gt in Htt.
  generalize Htt; intros H.
  apply angle_lt_le_incl in H.
  rewrite (proj2 (angle_max_r_iff _ _) H) in H1, H2, H3.
  rewrite (proj2 (angle_min_l_iff _ _) H) in H1, H2, H3.
  clear H.
  rewrite angle_sub_add_distr in H1, H2, H3.
  rewrite angle_sub_sub_swap in H1, H2, H3.
  rewrite angle_sub_diag in H1, H2, H3.
  rewrite angle_sub_0_l in H1, H2, H3.
  apply angle_opp_lt_compat_if in H3. 2: {
    intros H.
    rewrite H in H1.
    now apply angle_lt_irrefl in H1.
  }
  rewrite angle_opp_involutive in H3.
  assert (Hdd : (- dθ ≤ dθ)%A). {
    progress unfold angle_ltb in H3.
    progress unfold angle_leb.
    cbn in H3 |-*.
    rewrite (rngl_leb_0_opp Hop Hor) in H3.
    specialize (rngl_0_lt_1 Hon Hos Hc1 Hor) as H.
    apply rngl_nle_gt in H.
    apply rngl_leb_nle in H.
    rewrite H in H3; clear H.
    rewrite (rngl_leb_0_opp Hop Hor).
    remember (0 ≤? rngl_sin dθ)%L as zs eqn:Hzs.
    symmetry in Hzs.
    destruct zs; [ easy | ].
    apply (rngl_leb_gt Hor) in Hzs.
    apply (rngl_lt_le_incl Hor) in Hzs.
    apply rngl_leb_le in Hzs.
    now rewrite Hzs.
  }
...
  split; [ now apply (angle_lt_le_trans _ (- dθ)) | ].
  apply (angle_le_lt_trans _ (- dθ)); [ | easy ].
...
  apply angle_opp_le_compat_if in Hdd. 2: {
    intros H; rewrite H in H1.
    now apply angle_lt_irrefl in H1.
  }

...
Search (- _ < - _)%A.
...
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

Theorem angle_add_if_distr_r :
  ∀ (u : bool) a b c,
  ((if u then a else b) + c = if u then a + c else b + c)%A.
Proof. now intros; destruct u. Qed.

Theorem rngl_cos_derivative_lemma_1 :
  ∀ θ₀ θ,
  θ₀ ≠ 0%A
  → θ₀ ≠ angle_straight
  → (0 < rngl_cos (θ - θ₀))%L
  → (rngl_cos θ₀ < rngl_cos (θ - θ₀))%L
  → (- rngl_cos θ₀ < rngl_cos (θ - θ₀))%L
  → (θ ≤ θ + θ₀)%A
  → (θ₀ ≤ θ)%A
  → (θ < angle_straight)%A.
Proof.
destruct_ac.
intros * Htz Hts H2 H5 H3 Hovt Htt.
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
  (0 < rngl_cos (θ - θ₀))%L
  → (rngl_cos θ₀ < rngl_cos (θ - θ₀))%L
  → (- rngl_cos θ₀ < rngl_cos (θ - θ₀))%L
  → angle_add_overflow θ₀ θ = false
  → (θ₀ ≤ θ)%A
  → (θ - θ₀ ≤ angle_straight)%A.
Proof.
destruct_ac.
intros * H2 H5 H3 Hovt Htt.
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

Theorem angle_add_overflow_lt_straight_le_straight  :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = true
  → (θ1 ≤ θ2)%A
  → (θ1 < angle_straight)%A
  → (angle_straight ≤ θ2)%A.
Proof.
destruct_ac.
intros θ₀ θ Hovt Htt Htzs.
rewrite angle_add_overflow_comm in Hovt.
rewrite <- angle_add_overflow_equiv2 in Hovt.
progress unfold angle_add_overflow2 in Hovt.
progress unfold angle_ltb in Hovt.
progress unfold angle_leb in Htt.
progress unfold angle_ltb in Htzs.
progress unfold angle_leb.
cbn in Htzs |-*.
rewrite (rngl_leb_refl Hor) in Htzs |-*.
remember (0 ≤? rngl_sin θ₀)%L as ztz eqn:Hztz.
remember (0 ≤? rngl_sin θ)%L as zt eqn:Hzt.
remember (0 ≤? rngl_sin (θ + θ₀))%L as ztt eqn:Hztt.
symmetry in Hztz, Hzt, Hztt.
destruct zt; [ | easy ].
destruct ztz; [ | easy ].
destruct ztt; [ | easy ].
apply rngl_leb_le in Hzt, Hztt, Hztz, Htt.
apply rngl_ltb_lt in Hovt, Htzs.
apply rngl_leb_le.
apply (rngl_nlt_ge_iff Hor).
intros H1c.
apply rngl_nle_gt in Hovt.
apply Hovt; clear Hovt.
apply rngl_cos_add_le_cos; [ | easy | easy | easy ].
right; left.
intros H; rewrite H in Htzs.
cbn in Htzs.
now apply (rngl_lt_irrefl Hor) in Htzs.
Qed.

Theorem eq_angle_mul_2_0 : ∀ θ, (2 * θ = 0)%A ↔ θ = 0%A ∨ θ = angle_straight.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%A), (H1 θ).
  split; [ now intros; left | easy ].
}
intros.
split; intros Htt. {
  apply eq_angle_eq in Htt.
  remember (2 * θ)%A.
  injection Htt; clear Htt; intros Ht1 Ht2; subst a.
  rewrite rngl_cos_mul_2_l in Ht2.
  rewrite rngl_sin_mul_2_l in Ht1.
  rewrite <- rngl_mul_assoc in Ht1.
  apply (rngl_eq_mul_0_r Hos Hii) in Ht1. 2: {
    apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
  }
  apply (rngl_integral Hos) in Ht1. 2: {
    apply Bool.orb_true_iff; right.
    rewrite Hi1; cbn.
    now apply rngl_has_eq_dec_or_is_ordered_r.
  }
  destruct Ht1 as [Ht1| Ht1]; [ now apply eq_rngl_sin_0 in Ht1 | ].
  exfalso.
  apply eq_rngl_cos_0 in Ht1.
  destruct Ht1; subst θ; cbn in Ht2. {
    rewrite (rngl_squ_0 Hos) in Ht2.
    rewrite (rngl_squ_1 Hon) in Ht2.
    rewrite (rngl_sub_0_l Hop) in Ht2.
    (* lemma *)
    apply (f_equal (rngl_add 1)) in Ht2.
    rewrite (rngl_add_opp_r Hop) in Ht2.
    rewrite (rngl_sub_diag Hos) in Ht2.
    symmetry in Ht2.
    now apply (rngl_2_neq_0 Hon Hos Hc1 Hor) in Ht2.
  } {
    rewrite (rngl_squ_0 Hos) in Ht2.
    rewrite (rngl_squ_opp Hop) in Ht2.
    rewrite (rngl_squ_1 Hon) in Ht2.
    rewrite (rngl_sub_0_l Hop) in Ht2.
    (* lemma *)
    apply (f_equal (rngl_add 1)) in Ht2.
    rewrite (rngl_add_opp_r Hop) in Ht2.
    rewrite (rngl_sub_diag Hos) in Ht2.
    symmetry in Ht2.
    now apply (rngl_2_neq_0 Hon Hos Hc1 Hor) in Ht2.
  }
}
destruct Htt; subst θ; [ apply angle_mul_0_r | ].
(* lemma *)
rewrite angle_mul_2_l.
apply angle_straight_add_straight.
Qed.

Theorem eq_angle_mul_2_straight :
  ∀ θ, (2 * θ = angle_straight)%A ↔ θ = angle_right ∨ θ = (- angle_right)%A.
Proof.
intros.
change_angle_sub_r θ angle_right.
rewrite angle_mul_add_distr_l.
rewrite (angle_mul_2_l angle_right).
rewrite angle_right_add_right.
split; intros Htt. {
  apply angle_add_move_r in Htt.
  rewrite angle_sub_diag in Htt.
  apply eq_angle_mul_2_0 in Htt.
  destruct Htt; subst θ; [ left; apply angle_add_0_l | right ].
  apply angle_add_move_r.
  rewrite <- angle_opp_add_distr.
  rewrite angle_right_add_right.
  symmetry.
  apply angle_opp_straight.
}
apply angle_add_move_r.
rewrite angle_sub_diag.
apply eq_angle_mul_2_0.
destruct Htt as [Htt| Htt]. {
  left; apply angle_add_move_r in Htt.
  now rewrite angle_sub_diag in Htt.
}
right; apply angle_add_move_r in Htt.
rewrite <- angle_opp_add_distr in Htt.
rewrite angle_right_add_right in Htt.
now rewrite angle_opp_straight in Htt.
Qed.

Theorem rngl_cos_4_angle_straight_div_3 :
  rngl_cos (4 * angle_straight_div_3) = (- (1 / 2))%L.
Proof.
rewrite angle_mul_4_angle_straight_div_3.
now rewrite rngl_cos_add_straight_r.
Qed.

Theorem rngl_sin_4_angle_straight_div_3 :
  rngl_sin (4 * angle_straight_div_3) = (- (√3 / 2))%L.
Proof.
rewrite angle_mul_4_angle_straight_div_3.
now rewrite rngl_sin_add_straight_r.
Qed.

Definition is_gen_limit_when_tending_to_neighbourhood A B lta da db
  (f : A → B) (x₀ : A) (L : B) :=
  (∀ ε : T, 0 < ε →
   ∃ η : T, ∀ x : A, lta x x₀ → da x x₀ < η → db (f x) L < ε)%L.

Definition is_left_limit_when_tending_to_neighbourhood {A B} lta :=
  is_gen_limit_when_tending_to_neighbourhood A B (λ a b, lta a b).

Definition is_right_limit_when_tending_to_neighbourhood {A B} lta :=
  is_gen_limit_when_tending_to_neighbourhood A B (λ a b, lta b a).

Definition left_derivative_at {A} lta (da : A → A → T) (db : T → T → T)
    f f' a :=
  let g x := ((f x - f a) / da x a)%L in
  is_left_limit_when_tending_to_neighbourhood lta da db g a (f' a).

Definition right_derivative_at {A} lta (da : A → A → T) (db : T → T → T)
    f f' a :=
  let g x := ((f x - f a) / da x a)%L in
  is_right_limit_when_tending_to_neighbourhood lta da db g a (f' a).

Definition new_is_derivative {A} lta (da : A → A → T) (db : T → T → T) f f' :=
  ∀ a,
  left_derivative_at lta da db f f' a ∧ right_derivative_at lta da db f f' a.

Definition angle_lt_for_deriv θ1 θ2 :=
  (θ1 < θ2)%A ∧ angle_add_overflow θ1 θ2 = false.

(* to be completed
Theorem rngl_cos_derivative :
  new_is_derivative angle_lt_for_deriv
    angle_eucl_dist rngl_dist rngl_cos (λ θ, (- rngl_sin θ)%L).
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀.
  split; intros ε Hε; rewrite (H1 ε) in Hε. {
    now apply (rngl_lt_irrefl Hor) in Hε.
  } {
    now apply (rngl_lt_irrefl Hor) in Hε.
  }
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
assert (H20 : (2 ≠ 0)%L) by now apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
intros θ₀.
destruct (angle_eq_dec θ₀ 0) as [Htz| Htz]. {
  subst θ₀.
  split; intros ε Hε; cbn; rewrite (rngl_opp_0 Hop); exists ε. {
    intros θ Hlt Hθ.
    rewrite rngl_cos_angle_eucl_dist_0_r.
    rewrite (rngl_sub_sub_swap Hop).
    rewrite (rngl_sub_diag Hos).
    rewrite (rngl_sub_0_l Hop).
    progress unfold rngl_dist.
    rewrite (rngl_sub_0_r Hos).
(* bon, ça m'embête parce que pour la dérivée à gauche et la dérivée à
   droite, ça risque d'être le même code, ou similaire *)
...
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite (rngl_abs_opp Hop Hor).
  rewrite (rngl_div_div_swap Hic Hiv).
  progress unfold rngl_squ.
  rewrite (rngl_mul_div Hi1). 2: {
    intros H; rewrite H in Hθ.
    destruct Hθ as (H1, _).
    now apply (rngl_lt_irrefl Hor) in H1.
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
}
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  intros ε Hε.
  subst θ₀.
  cbn.
  exists ε.
  intros θ Hθ.
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_opp_0 Hop).
  rewrite rngl_cos_angle_eucl_dist_straight_r.
  rewrite (rngl_sub_add Hop).
  rewrite (rngl_div_div_swap Hic Hiv).
  progress unfold rngl_squ.
  rewrite (rngl_mul_div Hi1). 2: {
    intros H; rewrite H in Hθ.
    destruct Hθ as (H1, _).
    now apply (rngl_lt_irrefl Hor) in H1.
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
}
enough (H :
  (∀ ε, (0 < ε)%L → ∃ η1 : T, ∀ θ : angle T,
   (θ₀ < θ)%A
   → (angle_eucl_dist θ θ₀ < η1)%L
   → (rngl_dist ((rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀)
       (- rngl_sin θ₀) < ε)%L) ∧
  (∀ ε, (0 < ε)%L → ∃ η2 : T, ∀ θ : angle T,
   (θ < θ₀)%A
   → (angle_eucl_dist θ θ₀ < η2)%L
   → (rngl_dist ((rngl_cos θ₀ - rngl_cos θ) / angle_eucl_dist θ θ₀)
       (- rngl_sin θ₀) < ε)%L)). {

...
  intros ε Hε.
  destruct H as (H1, H2).
  specialize (H1 ε Hε).
  specialize (H2 ε Hε).
  destruct H1 as (η1 & H1).
  destruct H2 as (η2 & H2).
  exists (rngl_min η1 η2).
  intros θ (H3, H4).
  destruct (angle_lt_dec θ₀ θ) as [Htt| Htt]. {
    apply H1; [ easy | ].
    eapply (rngl_lt_le_trans Hor); [ apply H4 | ].
    apply (rngl_le_min_l Hor).
  } {
...
    apply angle_nlt_ge in Htt.
    assert (H : (θ < θ₀)%A). {
      apply angle_lt_iff.
      split; [ easy | ].
      intros H; subst θ.
      rewrite angle_eucl_dist_diag in H3.
      now apply (rngl_lt_irrefl Hor) in H3.
    }
    apply H2; [ easy | ].
    eapply (rngl_lt_le_trans Hor); [ apply H4 | ].
    apply (rngl_le_min_r Hor).
  }
}
specialize rngl_sin_is_continuous as Hsc.
progress unfold continuous in Hsc.
progress unfold continuous_at in Hsc.
progress unfold is_limit_when_tending_to in Hsc.
split. {
  specialize (Hsc θ₀ ε Hε).
  destruct Hsc as (η & Hη & Hsc).
  progress unfold rngl_dist in Hsc.
  move η before ε.
  remember (angle_eucl_dist angle_right 0) as x.
  remember (angle_eucl_dist θ₀ 0) as y.
  exists (rngl_min4 x y (angle_eucl_dist θ₀ angle_straight) η).
  subst x y.
  intros θ Htt H2.
  move θ before θ₀.
  apply (rngl_min_glb_lt_iff Hor) in H2.
  destruct H2 as (H2, H4).
  apply (rngl_min_glb_lt_iff Hor) in H2.
  destruct H2 as (H2, H3).
  apply (rngl_min_glb_lt_iff Hor) in H2.
  destruct H2 as (H2, H5).
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
  remember (angle_add_overflow θ θ₀) as ovt eqn:Hovt.
  symmetry in Hovt.
  rewrite <- (rngl_abs_opp Hop Hor).
  rewrite (rngl_opp_add_distr Hop).
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_add_opp_l Hop).
  (**)
  destruct ovt. 2: {
    generalize Htt; intros H.
    apply angle_lt_le_incl in H.
    apply angle_nlt_ge in H.
    apply Bool.not_true_iff_false in H.
    rewrite H; clear H.
    rewrite (rngl_mul_1_r Hon).
    remember (_ + _)%A as x eqn:Hx.
    apply Hsc.
    subst x.
    eapply (rngl_le_lt_trans Hor); [ | apply H4 ].
    clear η Hη Hsc H4.
    rewrite angle_add_0_r.
    rewrite angle_eucl_dist_move_0_r.
    rewrite (angle_eucl_dist_move_0_r θ).
    rewrite <- (angle_div_2_mul_2 θ₀) at 2.
    rewrite angle_mul_nat_div_2. 2: {
      cbn.
      rewrite angle_add_0_r.
      rewrite Bool.orb_false_r.
      apply angle_lt_straight_add_same_not_overflow.
      apply (angle_lt_trans _ θ); [ easy | ].
      apply rngl_cos_lt_iff_angle_eucl_lt in H2, H3, H5.
      rewrite angle_sub_0_r in H2, H5.
      rewrite rngl_cos_sub_straight_r in H3.
      cbn - [ angle_sub ] in H2.
      rewrite <- angle_add_overflow_equiv2 in Hovt.
      progress unfold angle_add_overflow2 in Hovt.
      apply angle_ltb_ge in Hovt.
      clear - Hor Hop H2 H3 H5 Hovt Htt Hts Htz.
      apply angle_lt_le_incl in Htt.
      now apply (rngl_cos_derivative_lemma_1 θ₀).
    }
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
    apply rngl_cos_lt_iff_angle_eucl_lt in H2, H3, H5.
    rewrite angle_sub_0_r in H2, H5.
    rewrite rngl_cos_sub_straight_r in H3.
    cbn - [ angle_sub ] in H2.
    clear - Hor Hop Hovt Htt H3 H5 H2.
    apply angle_lt_le_incl in Htt.
    now apply rngl_cos_derivative_lemma_2.
  }
(* faut peut-être ajouter angle_add_overflow θ θ₀ = false dans les
   deux cas ∃ η1 et ∃ η2 *)
...
  rewrite angle_add_0_r.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_mul_1_r Hon).
  rewrite <- rngl_sin_opp.
...
  apply Hsc.
  eapply (rngl_le_lt_trans Hor); [ | apply H4 ].
  clear η Hη Hsc H4 H1.
...
  apply rngl_cos_le_iff_angle_eucl_le.
  rewrite angle_add_sub_swap.
  rewrite rngl_cos_add_straight_r.
  apply (rngl_le_opp_r Hop Hor).
  rewrite (angle_is_mul_2_div_2 θ₀) at 3.
  rewrite angle_sub_add_distr.
  rewrite angle_div_2_sub'.
  rewrite angle_mul_2_l.
  rewrite angle_sub_add_distr.
  rewrite angle_add_sub.
  remember (θ₀ + θ₀ ≤? θ + θ₀)%A as t2t eqn:Ht2t.
  symmetry in Ht2t.
  destruct t2t. {
    remember (θ₀ <? angle_straight)%A as tzs eqn:Htzs.
    symmetry in Htzs.
    destruct tzs. {
      exfalso.
      apply Bool.not_false_iff_true in Ht2t.
      apply Ht2t; clear Ht2t.
      apply angle_leb_gt.
      assert (Hst : (angle_straight ≤ θ)%A). {
        clear - Hor Hovt Htt Htzs.
        rewrite angle_add_overflow_comm in Hovt.
        now apply (angle_add_overflow_lt_straight_le_straight θ₀).
      }
      rewrite <- angle_add_overflow_equiv2 in Hovt.
      progress unfold angle_add_overflow2 in Hovt.
      progress unfold angle_ltb in Hovt.
      progress unfold angle_leb in Htt.
      progress unfold angle_ltb in Htzs.
      progress unfold angle_leb in Hst.
      progress unfold angle_ltb.
      cbn in Hst, Htzs.
      rewrite (rngl_leb_refl Hor) in Htzs, Hst.
      remember (0 ≤? rngl_sin θ₀)%L as zs eqn:Hzs.
      symmetry in Hzs.
      destruct zs; [ | easy ].
      apply rngl_leb_le in Hzs.
      remember (0 ≤? rngl_sin (θ + θ₀))%L as ztt eqn:Hztt.
      remember (0 ≤? rngl_sin (θ₀ + θ₀))%L as ztztz eqn:Hztztz.
      remember (0 ≤? rngl_sin θ)%L as zt eqn:Hzt.
      symmetry in Hztt, Hztztz, Hzt.
      destruct ztt. {
        destruct ztztz; [ | easy ].
        apply rngl_ltb_lt in Htzs.
        apply rngl_leb_le in Hztztz.
        apply rngl_ltb_lt.
        destruct zt. {
          apply rngl_leb_le in Hztt, Hzt, Htt, Hst.
          apply rngl_ltb_lt in Hovt.
          apply (rngl_nle_gt_iff Hor).
          intros Hcc.
          apply rngl_nlt_ge in Hst.
          apply Hst; clear Hst.
          apply (rngl_lt_iff Hor).
          split ; [ apply rngl_cos_bound | ].
          intros H; symmetry in H.
          apply eq_rngl_cos_opp_1 in H.
          subst θ.
          rewrite rngl_sin_add_straight_l in Hztt.
          apply (rngl_opp_nonneg_nonpos Hop Hor) in Hztt.
          apply (rngl_le_antisymm Hor) in Hzs; [ | easy ].
          clear Hztt.
          apply eq_rngl_sin_0 in Hzs.
          now destruct Hzs.
        }
        clear Hovt Htt Hst.
        apply rngl_leb_le in Hztt.
        apply (rngl_leb_gt Hor) in Hzt.
        destruct (rngl_lt_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
          destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
            change_angle_opp θ.
            rewrite angle_add_opp_l in Hztt |-*.
            progress sin_cos_opp_hyp T Hzt.
            progress sin_cos_opp_hyp T Hzc.
            rewrite rngl_cos_add, rngl_cos_sub.
            apply (rngl_lt_sub_lt_add_r Hop Hor).
            rewrite <- rngl_add_assoc.
            eapply (rngl_le_lt_trans Hor). 2: {
              apply (rngl_lt_add_r Hos Hor).
              apply (rngl_add_pos_nonneg Hor). {
                apply (rngl_mul_pos_pos Hos Hor Hii); [ | easy ].
                apply (rngl_lt_iff Hor).
                split; [ easy | ].
                intros H; symmetry in H.
                apply eq_rngl_sin_0 in H.
                now destruct H.
              }
              now apply (rngl_mul_nonneg_nonneg Hos Hor).
            }
            apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
            apply (rngl_lt_le_incl Hor) in Hzcz, Hzt.
            now apply quadrant_1_sin_sub_nonneg_cos_le.
          }
          exfalso.
          apply (rngl_nle_gt_iff Hor) in Hzc.
          change_angle_add_r θ angle_straight.
          progress sin_cos_add_sub_straight_hyp T Hzt.
          progress sin_cos_add_sub_straight_hyp T Hztt.
          progress sin_cos_add_sub_straight_hyp T Hzc.
          apply rngl_nlt_ge in Hztt.
          apply Hztt; clear Hztt.
          apply (rngl_lt_le_incl Hor) in Hzc.
          now apply rngl_sin_add_pos_2.
        }
        apply (rngl_nlt_ge_iff Hor) in Hzcz.
        change_angle_sub_l θ₀ angle_straight.
        progress sin_cos_add_sub_straight_hyp T Hztt.
        progress sin_cos_add_sub_straight_hyp T Hzcz.
        progress sin_cos_add_sub_straight_hyp T Hztztz.
        progress sin_cos_add_sub_straight_hyp T Htzs.
        progress sin_cos_add_sub_straight_hyp T Hzs.
        progress sin_cos_add_sub_straight_goal T.
        progress sin_cos_add_sub_straight_goal T.
        rewrite <- angle_sub_add_distr in Hztztz |-*.
        progress sin_cos_add_sub_straight_goal T.
        progress sin_cos_add_sub_straight_hyp T Hztztz.
        rewrite <- (rngl_opp_add_distr Hop).
        apply (rngl_opp_pos_neg Hop Hor).
        apply (rngl_nle_gt_iff Hor).
        intros Hcc.
        apply rngl_nlt_ge in Hztztz.
        apply Hztztz; clear Hztztz.
        apply rngl_sin_add_pos_2; [ | easy | easy | ]. {
          apply (rngl_lt_iff Hor).
          split; [ easy | ].
          intros H; symmetry in H.
          apply eq_rngl_sin_0 in H.
          destruct H; subst θ₀; [ now rewrite angle_sub_0_r in Hts | ].
          now rewrite angle_sub_diag in Htz.
        } {
          apply (rngl_lt_iff Hor).
          split; [ easy | ].
          intros H; symmetry in H.
          apply eq_rngl_cos_0 in H.
          destruct H; subst θ₀. {
            rewrite rngl_sin_sub_right_r in Hztt.
            clear Hzs Htzs Hzcz.
            rewrite rngl_cos_sub_right_r in Hcc.
            rewrite angle_right_add_right in Hcc.
            cbn in Hcc.
            rewrite (rngl_add_opp_r Hop) in Hcc.
            apply -> (rngl_le_0_sub Hop Hor) in Hcc.
            apply rngl_nlt_ge in Hcc.
            apply Hcc; clear Hcc.
            apply (rngl_lt_le_trans Hor _ 0); [ easy |].
            apply (rngl_0_le_1 Hon Hos Hor).
          }
          apply rngl_nlt_ge in Hzs.
          apply Hzs; clear Hzs.
          apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
        }
      }
      destruct zt; [ easy | ].
      clear Htt Hst.
      destruct ztztz. {
        exfalso.
        apply (rngl_leb_gt Hor) in Hztt, Hzt.
        apply rngl_ltb_lt in Hovt, Htzs.
        apply rngl_leb_le in Hztztz.
        destruct (rngl_lt_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
          destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
            change_angle_opp θ.
            rewrite angle_add_opp_l in Hovt, Hztt.
            progress sin_cos_opp_hyp T Hovt.
            progress sin_cos_opp_hyp T Hzt.
            progress sin_cos_opp_hyp T Hzc.
            rewrite rngl_sin_sub_anticomm in Hztt.
            apply (rngl_opp_neg_pos Hop Hor) in Hztt.
            apply rngl_nle_gt in Hovt.
            apply Hovt; clear Hovt.
            apply (rngl_lt_eq_cases Hor).
            left.
            apply (rngl_lt_le_incl Hor) in Hzt, Hzcz, Hztt.
            apply rngl_cos_lt_rngl_cos_sub; [ easy | | ]. {
              apply (rngl_lt_iff Hor).
              split; [ easy | ].
              intros H; symmetry in H.
              apply eq_rngl_sin_0 in H.
              now destruct H.
            }
            now apply quadrant_1_sin_sub_nonneg_cos_le.
          }
          apply (rngl_nle_gt_iff Hor) in Hzc.
          change_angle_add_r θ angle_straight.
          progress sin_cos_add_sub_straight_hyp T Hovt.
          progress sin_cos_add_sub_straight_hyp T Hzt.
          progress sin_cos_add_sub_straight_hyp T Hztt.
          progress sin_cos_add_sub_straight_hyp T Hzc.
          apply rngl_nle_gt in Hovt.
          apply Hovt; clear Hovt.
          apply (rngl_lt_le_incl Hor) in Hzt, Hzc, Hzcz.
          now apply quadrant_1_rngl_cos_add_le_cos_l.
        }
        apply (rngl_nlt_ge_iff Hor) in Hzcz.
        change_angle_sub_l θ₀ angle_straight.
        progress sin_cos_add_sub_straight_hyp T Hzcz.
        progress sin_cos_add_sub_straight_hyp T Hztztz.
        progress sin_cos_add_sub_straight_hyp T Hzs.
        progress sin_cos_add_sub_straight_hyp T Hztt.
        progress sin_cos_add_sub_straight_hyp T Htzs.
        progress sin_cos_add_sub_straight_hyp T Hovt.
        rewrite <- angle_sub_add_distr in Hztztz.
        rewrite rngl_sin_sub_straight_l in Hztztz.
        apply rngl_nlt_ge in Hztztz.
        apply Hztztz; clear Hztztz.
        apply (rngl_lt_iff Hor).
        split; [ now apply rngl_sin_add_nonneg | ].
        intros H; symmetry in H.
        rewrite <- angle_mul_2_l in H.
        apply eq_rngl_sin_0 in H.
        destruct H as [H| H]. {
          apply eq_angle_mul_2_0 in H.
          destruct H; subst θ₀. {
            now rewrite angle_sub_0_r in Hts.
          }
          now rewrite angle_sub_diag in Htz.
        }
        apply eq_angle_mul_2_straight in H.
        destruct H; subst θ₀. {
          rewrite rngl_sin_sub_right_r in Hztt.
          rewrite rngl_cos_sub_right_r in Hovt.
          apply (rngl_opp_pos_neg Hop Hor) in Hztt.
          apply rngl_nle_gt in Hovt.
          apply Hovt.
          apply (rngl_lt_le_incl Hor) in Hztt, Hzt.
          now apply (rngl_add_nonpos_nonpos Hor).
        }
        apply rngl_nlt_ge in Hzs.
        apply Hzs; clear Htz.
        apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
      }
      apply (rngl_leb_gt Hor) in Hztt, Hztztz, Hzt.
      apply rngl_ltb_lt in Hovt, Htzs.
      apply rngl_ltb_lt.
      destruct (rngl_lt_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
        exfalso.
        apply rngl_nle_gt in Hztztz.
        apply Hztztz; clear Hztztz.
        apply (rngl_lt_le_incl Hor) in Hzcz.
        now apply rngl_sin_add_nonneg.
      }
      apply (rngl_nlt_ge_iff Hor) in Hzcz.
      change_angle_sub_l θ₀ angle_straight.
      rewrite angle_add_sub_assoc in Hztztz.
      do 2 rewrite angle_add_sub_assoc.
      rewrite <- angle_add_sub_swap in Hztztz |-*.
      rewrite angle_straight_add_straight in Hztztz |-*.
      rewrite angle_sub_0_l in Hztztz |-*.
      rewrite <- angle_opp_add_distr in Hztztz |-*.
      progress sin_cos_add_sub_straight_hyp T Hztt.
      progress sin_cos_add_sub_straight_hyp T Hzcz.
      progress sin_cos_add_sub_straight_hyp T Hztztz.
      progress sin_cos_add_sub_straight_hyp T Htzs.
      progress sin_cos_add_sub_straight_hyp T Hzs.
      progress sin_cos_add_sub_straight_hyp T Hovt.
      progress sin_cos_add_sub_straight_goal T.
      rewrite rngl_cos_opp.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
        exfalso.
        change_angle_opp θ.
        rewrite <- angle_opp_add_distr in Hztt.
        progress sin_cos_opp_hyp T Hzt.
        progress sin_cos_opp_hyp T Hztt.
        progress sin_cos_opp_hyp T Hzc.
        apply rngl_nle_gt in Hztt.
        apply Hztt; clear Hztt.
        apply (rngl_opp_nonpos_nonneg Hop Hor).
        apply (rngl_lt_le_incl Hor) in Hzt.
        now apply rngl_sin_add_nonneg.
      }
      exfalso.
      apply (rngl_nle_gt_iff Hor) in Hzc.
      change_angle_add_r θ angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzt.
      progress sin_cos_add_sub_straight_hyp T Hzc.
      progress sin_cos_add_sub_straight_hyp T Hovt.
      apply rngl_nle_gt in Hovt.
      apply Hovt; clear Hovt.
      apply (rngl_lt_le_incl Hor) in Hzt, Hzc.
      apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
      now apply rngl_cos_sub_nonneg.
    }
    apply angle_ltb_ge in Htzs.
    rewrite rngl_cos_sub_straight_r.
    rewrite (rngl_add_opp_r Hop).
    apply (rngl_le_sub_0 Hop Hor).
    destruct (angle_le_dec (θ - θ₀) (4 * angle_straight_div_3))
        as [Hztt| Hztt]. {
      now apply rngl_cos_le_cos_div_2.
    }
    exfalso.
    apply Hztt; clear Hztt.
    move Htt at bottom.
    progress unfold angle_leb in Htzs.
    progress unfold angle_leb in Htt.
    cbn in Htzs.
    rewrite (rngl_leb_refl Hor) in Htzs.
    remember (0 ≤? rngl_sin θ₀)%L as zst eqn:Hzst.
    remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
    symmetry in Hzst, Hzs.
    destruct zst. {
      exfalso.
      apply rngl_leb_le in Htzs.
      apply rngl_nlt_ge in Htzs.
      apply Htzs; clear Htzs.
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_cos_bound | ].
      intros H; symmetry in H.
      now apply eq_rngl_cos_opp_1 in H.
    }
    clear Htzs.
    destruct zs; [ easy | ].
    apply (rngl_leb_gt Hor) in Hzst, Hzs.
    apply rngl_leb_le in Htt.
    change_angle_add_r θ₀ angle_straight.
    change_angle_add_r θ angle_straight.
    move Hzst at bottom.
    move Hzs at bottom.
    move Htt at bottom.
    progress sin_cos_add_sub_straight_hyp T Hzst.
    progress sin_cos_add_sub_straight_hyp T Hzs.
    progress sin_cos_add_sub_straight_hyp T Htt.
    progress sin_cos_add_sub_straight_goal T.
    rewrite angle_sub_sub_distr.
    rewrite angle_add_sub.
    rewrite (rngl_add_opp_l Hop) in Htt.
    apply -> (rngl_le_sub_0 Hop Hor) in Htt.
    apply (rngl_lt_le_incl Hor) in Hzst, Hzs.
    apply (angle_le_trans _ angle_straight). 2: {
      apply angle_straight_le_4_angle_straight_div_3.
    }
    apply rngl_sin_nonneg_angle_le_straight.
    now apply rngl_sin_sub_nonneg.
  }
  apply angle_leb_gt in Ht2t.
  rewrite angle_add_sub_swap, rngl_cos_add_straight_r.
  rewrite (rngl_add_opp_r Hop).
  destruct (angle_le_dec (θ - θ₀) (4 * angle_straight_div_3))
      as [Hztt| Hztt]. {
    remember (θ₀ <? angle_straight)%A as tzs eqn:Htzs.
    symmetry in Htzs.
    destruct tzs. {
      apply (rngl_le_sub_0 Hop Hor).
      rewrite angle_sub_0_r.
      now apply rngl_cos_le_cos_div_2.
    }
    apply angle_ltb_ge in Htzs.
    rewrite rngl_cos_sub_straight_r.
    rewrite (rngl_sub_opp_r Hop).
    progress unfold angle_leb in Htt.
    progress unfold angle_ltb in Ht2t.
    progress unfold angle_leb in Hztt.
    progress unfold angle_leb in Htzs.
    rewrite rngl_cos_4_angle_straight_div_3 in Hztt.
    rewrite rngl_sin_4_angle_straight_div_3 in Hztt.
    rewrite (rngl_0_leb_opp_sqrt_3_div_2 Hon Hop Hiv Hor Hc1) in Hztt.
    cbn in Htzs.
    rewrite (rngl_leb_refl Hor) in Htzs.
    remember (0 ≤? rngl_sin θ₀)%L as zst eqn:Hzst.
    remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
    symmetry in Hzst, Hzs.
    destruct zst. {
      apply (rngl_nlt_ge_iff Hor).
      intros Hcc.
      apply Bool.not_false_iff_true in Htzs.
      apply Htzs; clear Htzs.
      apply (rngl_leb_gt Hor).
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_cos_bound | ].
      intros H; symmetry in H.
      now apply eq_rngl_cos_opp_1 in H.
    }
    clear Htzs.
    destruct zs; [ easy | ].
    apply (rngl_leb_gt Hor) in Hzst, Hzs.
    apply rngl_leb_le in Htt.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
      change_angle_opp θ₀.
      progress sin_cos_opp_hyp T Hzst.
      progress sin_cos_opp_hyp T Hzcz.
      progress sin_cos_opp_hyp T Hztt.
      progress sin_cos_opp_hyp T Ht2t.
      progress sin_cos_opp_hyp T Htt.
      progress sin_cos_opp_goal T.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
        change_angle_opp θ.
        progress sin_cos_opp_hyp T Hzs.
        progress sin_cos_opp_hyp T Hzc.
        progress sin_cos_opp_hyp T Htt.
        progress sin_cos_opp_hyp T Ht2t.
        progress sin_cos_opp_hyp T Hztt.
        progress sin_cos_opp_goal T.
(* ça n'a pas l'air d'être vrai *)
...
(**)
destruct tt. {
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_mul_1_r Hon).
  rewrite <- rngl_sin_add_straight_r.
  rewrite <- angle_add_assoc.
  rewrite angle_add_if_distr_r.
  rewrite angle_straight_add_straight.
  rewrite angle_add_0_l.
  remember (_ + _)%A as x eqn:Hx.
(*
  Htt : (θ < θ₀)%A
  Hx : x = ((θ + θ₀) /₂ + (if ovt then 0 else angle_straight))%A
  ============================
  (rngl_abs (rngl_sin x - rngl_sin θ₀) < ε)%L
*)
  apply Hsc.
(*
  Htt : (θ < θ₀)%A
  Hx : x = ((θ + θ₀) /₂ + (if ovt then 0 else angle_straight))%A
  ============================
  (angle_eucl_dist x θ₀ < η)%L
*)
  subst x.
  destruct (angle_lt_dec θ₀ angle_straight) as [Htzs| Htzs]. {
    destruct ovt. 2: {
      rewrite angle_eucl_dist_move_0_r.
      rewrite <- (angle_div_2_mul_2 θ₀) at 2.
      rewrite angle_mul_nat_div_2. 2: {
        cbn.
        rewrite angle_add_0_r.
        rewrite Bool.orb_false_r.
        now apply angle_lt_straight_add_same_not_overflow.
      }
      rewrite angle_add_sub_swap.
      rewrite angle_div_2_sub'.
      rewrite angle_mul_2_l.
      rewrite angle_sub_add_distr.
      rewrite angle_add_sub.
      (* lemma *)
      rewrite (angle_add_comm θ).
      remember (_ + _ ≤? _ + _)%A as b eqn:Hb.
      symmetry in Hb.
      destruct b. {
        exfalso.
        apply angle_nlt_ge in Hb.
        apply Hb; clear Hb.
        apply angle_lt_iff.
        split. {
          apply angle_lt_le_incl in Htt.
          apply angle_add_le_mono_l; [ | easy ].
          now apply angle_lt_straight_add_same_not_overflow.
        }
        intros H.
        apply angle_add_move_l in H.
        rewrite angle_add_sub in H.
        rewrite H in Htt.
        now apply angle_lt_irrefl in Htt.
      }
      rewrite <- angle_add_assoc.
      rewrite angle_straight_add_straight.
      rewrite angle_add_0_r.
(**)
      rewrite <- angle_eucl_dist_opp_opp.
      rewrite angle_opp_0.
      rewrite angle_opp_div_2.
      remember (θ - θ₀ =? 0)%A as ttz eqn:Httz.
      symmetry in Httz.
      destruct ttz. {
        apply angle_eqb_eq in Httz.
        apply -> angle_sub_move_0_r in Httz.
        rewrite Httz in Htt.
        now apply angle_lt_irrefl in Htt.
      }
      rewrite angle_opp_sub_distr.
      rewrite <- angle_sub_straight_eq_add_straight.
      rewrite <- angle_eucl_dist_move_0_r.
(* je le sens moyen, tout ça... *)
...
      eapply (rngl_le_lt_trans Hor); [ | apply H4 ].
      rewrite (angle_eucl_dist_move_0_r θ).
(**)
      rewrite <- angle_eucl_dist_opp_opp.
      rewrite <- (angle_eucl_dist_opp_opp _ 0).
      rewrite angle_opp_0.
      rewrite angle_opp_div_2.
      rewrite angle_opp_sub_distr.
      remember (θ - θ₀ =? 0)%A as ttz eqn:Httz.
      symmetry in Httz.
      destruct ttz. {
        apply angle_eqb_eq in Httz.
        apply -> angle_sub_move_0_r in Httz.
        rewrite Httz in Htt.
        now apply angle_lt_irrefl in Htt.
      }
      rewrite <- angle_sub_straight_eq_add_straight.
      do 2 rewrite <- angle_eucl_dist_move_0_r
...
rewrite <- angle_opp_0.
rewrite <- (angle_opp_involutive (_ /₂)).
rewrite <- (angle_opp_involutive (_ - _)).
Search (angle_eucl_dist (- _) (- _)).
do 2 rewrite -> angle_eucl_dist_opp_opp.
...
(**)
      (* theorem to be renamed *)
      apply rngl_cos_le_iff_angle_eucl_le.
      rewrite rngl_cos_sub_comm.
      rewrite <- (rngl_cos_opp (_ /₂)).
      rewrite angle_opp_div_2.
      remember (θ - θ₀ =? 0)%A as ttz eqn:Httz.
      symmetry in Httz.
      destruct ttz. {
        apply angle_eqb_eq in Httz.
        apply -> angle_sub_move_0_r in Httz.
        rewrite Httz in Htt.
        now apply angle_lt_irrefl in Htt.
      }
      rewrite angle_opp_sub_distr.
      rewrite rngl_cos_add_straight_r.
(* putain ça marche pas *)
...
      apply angle_le_angle_eucl_dist_le; cycle 2. {
        apply angle_div_2_le.
      } {
        apply angle_div_2_le_straight.
      }
(* je pense que c'est faux *)
Check angle_le_angle_eucl_dist_le.
(* conditions trop fortes *)
...
*)

End a.
