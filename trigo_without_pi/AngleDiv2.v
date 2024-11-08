(* dividing an angle by 2 and by 2^n *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.Misc1 Main.RingLike.
Require Import RealLike.
Require Import TrigoWithoutPi.
Require Import TrigoWithoutPiExt.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_div_2_prop :
  ∀ a (ε := (if (0 ≤? rngl_sin a)%L then 1%L else (-1)%L)),
  cos2_sin2_prop
    (ε * √((1 + rngl_cos a) / 2))%L
    (√((1 - rngl_cos a) / 2)%L).
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
intros.
progress unfold cos2_sin2_prop.
rewrite Hon, Hop, Hic, Hed.
apply Bool.orb_true_iff; right.
assert (Hε : (ε² = 1)%L). {
  progress unfold ε.
  destruct (0 ≤? _)%L. {
    apply (rngl_mul_1_l Hon).
  } {
    apply (rngl_squ_opp_1 Hon Hop).
  }
}
rewrite (rngl_squ_mul Hic).
rewrite Hε, (rngl_mul_1_l Hon).
apply (rngl_eqb_eq Hed).
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 (_ + _)%L), (H1 1%L).
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_sub_le_add_l Hop Hor).
  rewrite (rngl_sub_0_l Hop).
  apply rngl_cos_bound.
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub Hos).
apply (rngl_div_diag Hon Hiq).
apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
Qed.

Definition angle_div_2 a :=
  let ε := if (0 ≤? rngl_sin a)%L then 1%L else (-1)%L in
  {| rngl_cos := ε * √((1 + rngl_cos a) / 2)%L;
     rngl_sin := √((1 - rngl_cos a)%L / 2%L);
     rngl_cos2_sin2 := angle_div_2_prop a |}.

End a.

Notation "θ /₂" := (angle_div_2 θ) (at level 40) : angle_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_div_2_mul_2 :
  ∀ a, (2 * (a /₂))%A = a.
Proof.
intros *.
destruct_ac.
apply eq_angle_eq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  do 2 rewrite (H1 (rngl_cos _)).
  do 2 rewrite (H1 (rngl_sin _)).
  easy.
}
specialize (rngl_2_neq_0 Hon Hop Hc1 Hor) as H20.
progress unfold angle_mul_nat.
progress unfold angle_div_2.
progress unfold angle_add.
cbn.
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
do 2 rewrite (rngl_mul_1_r Hon).
rewrite rngl_add_0_r.
do 2 rewrite fold_rngl_squ.
set (ε := if (0 ≤? rngl_sin a)%L then 1%L else (-1)%L).
assert (Hε : (ε² = 1)%L). {
  progress unfold ε.
  destruct (0 ≤? _)%L. {
    apply (rngl_mul_1_l Hon).
  } {
    apply (rngl_squ_opp_1 Hon Hop).
  }
}
rewrite (rngl_squ_mul Hic).
rewrite Hε, (rngl_mul_1_l Hon).
assert (Hz1ac : (0 ≤ 1 + rngl_cos a)%L). {
  apply (rngl_le_sub_le_add_l Hop Hor).
  rewrite (rngl_sub_0_l Hop).
  apply rngl_cos_bound.
}
assert (Hz1sc : (0 ≤ 1 - rngl_cos a)%L). {
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
}
progress unfold rngl_div.
rewrite Hiv.
rewrite <- (rngl_mul_sub_distr_r Hop).
rewrite (rngl_sub_sub_distr Hop).
rewrite (rngl_add_comm 1%L) at 1.
rewrite (rngl_add_sub Hos).
rewrite <- (rngl_mul_2_r Hon).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_r Hon Hiv); [ | easy ].
rewrite (rngl_mul_1_r Hon); f_equal.
progress unfold rl_sqrt.
rewrite rngl_add_comm.
rewrite (rngl_mul_comm Hic).
rewrite <- (rngl_mul_2_r Hon).
rewrite (rngl_mul_comm Hic ε).
rewrite rngl_mul_assoc.
rewrite <- rl_nth_root_mul; cycle 1. {
  rewrite (rngl_mul_inv_r Hiv).
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
} {
  rewrite (rngl_mul_inv_r Hiv).
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
}
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (1 - _)%L).
do 2 rewrite <- rngl_mul_assoc.
rewrite rl_nth_root_mul; cycle 1. {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
} {
  apply (rngl_mul_diag_nonneg Hop Hor).
}
rewrite rl_nth_root_mul; [ | easy | easy ].
assert (Hz2 : (0 ≤ 2⁻¹)%L). {
  apply (rngl_lt_le_incl Hor).
  apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite rl_nth_root_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite fold_rl_sqrt.
rewrite (rngl_squ_pow_2 Hon).
progress unfold rl_sqrt.
rewrite rl_nth_root_pow; [ | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic).
rewrite (rngl_mul_comm Hic).
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hon Hiv); [ | easy ].
rewrite (rngl_mul_1_r Hon).
rewrite <- rl_nth_root_mul; [ | easy | easy ].
rewrite (rngl_mul_comm Hic (1 - _)%L).
rewrite (rngl_squ_sub_squ' Hop).
rewrite (rngl_mul_1_r Hon), (rngl_mul_1_l Hon).
rewrite (rngl_add_sub Hos).
progress unfold rngl_squ at 1.
rewrite (rngl_mul_1_r Hon).
destruct a as (ca, sa, Ha); cbn in ε, Hz1ac, Hz1sc |-*.
apply (cos2_sin2_prop_add_squ) in Ha.
rewrite <- Ha, rngl_add_comm, (rngl_add_sub Hos).
progress unfold rngl_squ.
progress unfold ε.
remember (0 ≤? sa)%L as saz eqn:Hsaz; symmetry in Hsaz.
destruct saz. {
  apply rngl_leb_le in Hsaz.
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rl_nth_root_pow 2); [ cbn | easy ].
  rewrite (rngl_mul_1_r Hon).
  now rewrite rl_nth_root_mul.
} {
  apply (rngl_leb_gt Hor) in Hsaz.
  apply (rngl_opp_lt_compat Hop Hor) in Hsaz.
  rewrite (rngl_opp_0 Hop) in Hsaz.
  apply (rngl_lt_le_incl Hor) in Hsaz.
  rewrite <- (rngl_mul_opp_opp Hop sa).
  rewrite rl_nth_root_mul; [ | easy | easy ].
  apply (rngl_opp_inj Hop).
  rewrite <- (rngl_mul_opp_l Hop).
  rewrite (rngl_opp_involutive Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rl_nth_root_pow 2); [ cbn | easy ].
  now rewrite (rngl_mul_1_r Hon).
}
Qed.

Theorem rngl_sin_div_2_nonneg : ∀ θ, (0 ≤ rngl_sin (θ /₂))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 (rngl_sin _)).
  apply (rngl_le_refl Hor).
}
intros.
apply rl_sqrt_nonneg.
apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
apply (rngl_le_0_sub Hop Hor).
apply rngl_cos_bound.
Qed.

Theorem angle_div_2_le_straight : ∀ θ, (θ /₂ ≤ angle_straight)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  rewrite (H1 (_ /₂))%A, (H1 angle_straight).
  apply angle_le_refl.
}
intros.
progress unfold angle_leb.
specialize (rngl_sin_div_2_nonneg θ) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
cbn.
rewrite (rngl_leb_refl Hor).
apply rngl_leb_le.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_le_trans Hor _ 0). {
    apply (rngl_opp_1_le_0 Hon Hop Hor).
  }
  apply rl_sqrt_nonneg.
  apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_leb_gt Hor) in Hzs.
  rewrite (rngl_mul_opp_l Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rl_sqrt_1 Hon Hop Hor Hii) at 4.
  apply (rl_sqrt_le_rl_sqrt Hon Hop Hor Hii). {
    apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  } {
    apply (rngl_le_div_l Hon Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_add_le_mono_l Hop Hor).
    apply rngl_cos_bound.
  }
}
Qed.

Theorem angle_0_div_2 : (0 /₂ = 0)%A.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  apply H1.
}
apply eq_angle_eq; cbn.
rewrite (rngl_leb_refl Hor).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite (rl_sqrt_1 Hon Hop Hor). 2: {
  rewrite Bool.orb_true_iff; right.
  apply (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv).
}
f_equal.
rewrite (rngl_sub_diag Hos).
rewrite (rngl_div_0_l Hos Hi1). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rl_sqrt_0 Hon Hop Hor).
rewrite Bool.orb_true_iff; right.
apply (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv).
Qed.

Theorem angle_straight_div_2 : (angle_straight /₂ = angle_right)%A.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  rewrite (H1 angle_right).
  apply H1.
}
apply eq_angle_eq; cbn.
rewrite (rngl_leb_refl Hor).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_div_0_l Hos Hi1). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite (rl_sqrt_0 Hon Hop Hor). 2: {
  rewrite Bool.orb_true_iff; right.
  apply (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv).
}
f_equal.
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rl_sqrt_1 Hon Hop Hor).
rewrite Bool.orb_true_iff; right.
apply (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv).
Qed.

Theorem angle_div_2_le_compat :
  ∀ θ1 θ2, (θ1 ≤ θ2 → θ1 /₂ ≤ θ2 /₂)%A.
Proof.
destruct_ac.
intros * H12.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  do 2 rewrite (H1 (_ /₂))%A.
  apply angle_le_refl.
}
progress unfold angle_leb in H12.
progress unfold angle_leb.
cbn.
specialize rngl_1_add_cos_div_2_nonneg as Hzac.
specialize rngl_1_sub_cos_div_2_nonneg as Hzsc.
specialize (rl_sqrt_nonneg ((1 - rngl_cos θ1) / 2)%L) as H1.
rewrite fold_rl_sqrt in H1.
specialize (H1 (Hzsc _)).
apply rngl_leb_le in H1.
rewrite H1; clear H1.
specialize (rl_sqrt_nonneg ((1 - rngl_cos θ2) / 2)%L) as H1.
rewrite fold_rl_sqrt in H1.
specialize (H1 (Hzsc _)).
apply rngl_leb_le in H1.
rewrite H1; clear H1.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  rewrite (rngl_mul_1_l Hon).
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    apply rngl_leb_le in H12.
    rewrite (rngl_mul_1_l Hon).
    apply rngl_leb_le.
    rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
      now apply rl_sqrt_nonneg.
    }
    rewrite <- (rngl_abs_nonneg_eq Hop Hor (√_))%L. 2: {
      now apply rl_sqrt_nonneg.
    }
    apply (rngl_squ_le_abs_le Hop Hor Hii).
    rewrite (rngl_squ_sqrt Hon); [ | easy ].
    rewrite (rngl_squ_sqrt Hon); [ | easy ].
    apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with (c := 2%L). {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    rewrite (rngl_div_mul Hon Hiv). 2: {
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    rewrite (rngl_div_mul Hon Hiv). 2: {
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    now apply (rngl_add_le_mono_l Hop Hor).
  }
  apply rngl_leb_le.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_le_trans Hor _ 0). {
    apply (rngl_opp_nonpos_nonneg Hop Hor).
    now apply rl_sqrt_nonneg.
  } {
    now apply rl_sqrt_nonneg.
  }
}
apply (rngl_leb_gt Hor) in Hzs1.
destruct zs2; [ easy | ].
apply (rngl_leb_gt Hor) in Hzs2.
apply rngl_leb_le in H12.
apply rngl_leb_le.
do 2 rewrite (rngl_mul_opp_l Hop).
do 2 rewrite (rngl_mul_1_l Hon).
apply -> (rngl_opp_le_compat Hop Hor).
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  now apply rl_sqrt_nonneg.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor (√_))%L. 2: {
  now apply rl_sqrt_nonneg.
}
apply (rngl_squ_le_abs_le Hop Hor Hii).
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite (rngl_squ_sqrt Hon); [ | easy ].
apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with (c := 2%L). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite (rngl_div_mul Hon Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
now apply (rngl_add_le_mono_l Hop Hor).
Qed.

Fixpoint angle_div_2_pow θ i :=
  match i with
  | 0 => θ
  | S i' => angle_div_2 (angle_div_2_pow θ i')
  end.

End a.

Notation "θ /₂^ n" := (angle_div_2_pow θ n)
  (at level 40, format "θ  /₂^ n") : angle_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_div_2_pow_succ_r_1 :
  ∀ n θ, angle_div_2_pow θ (S n) = (angle_div_2_pow θ n /₂)%A.
Proof. easy. Qed.

Theorem angle_div_2_pow_succ_r_2 :
  ∀ n θ, angle_div_2_pow θ (S n) = angle_div_2_pow (θ /₂) n.
Proof.
intros.
induction n; intros; [ easy | ].
remember (S n) as sn; cbn; subst sn.
now rewrite IHn.
Qed.

Theorem angle_div_2_pow_add_r :
  ∀ i j θ, (θ /₂^(i + j) = θ /₂^i /₂^j)%A.
Proof.
intros.
revert j θ.
induction i; intros; [ easy | ].
rewrite Nat.add_succ_l.
do 2 rewrite angle_div_2_pow_succ_r_2.
apply IHi.
Qed.

Theorem angle_div_2_pow_mul_2_pow :
  ∀ n θ, (2 ^ n * (θ /₂^n))%A = θ.
Proof.
intros.
induction n; intros; [ apply angle_add_0_r | ].
cbn - [ "^" ].
rewrite Nat.pow_succ_r; [ | easy ].
rewrite Nat.mul_comm.
rewrite <- angle_mul_nat_assoc.
rewrite angle_div_2_mul_2.
apply IHn.
Qed.

Theorem angle_0_div_2_pow : ∀ n, (0 /₂^n = 0)%A.
Proof.
intros.
induction n; [ easy | cbn ].
rewrite IHn.
apply angle_0_div_2.
Qed.

Theorem angle_div_2_pow_le :
  ∀ n θ1 θ2, (θ1 ≤ θ2)%A → (θ1 /₂^n ≤ θ2 /₂^n)%A.
Proof.
intros * H12.
revert θ1 θ2 H12.
induction n; intros; [ easy | cbn ].
apply angle_div_2_le_compat.
now apply IHn.
Qed.

Theorem rngl_cos_div_pow_2_eq :
  ∀ θ n, rngl_cos (θ /₂^S n) = rngl_cos_div_pow_2 (θ /₂) n.
Proof.
destruct_ac.
intros.
rewrite angle_div_2_pow_succ_r_2.
induction n; intros; [ easy | cbn ].
rewrite IHn.
remember (0 ≤? _)%L as zsa eqn:Hzsa.
symmetry in Hzsa.
destruct zsa; [ apply (rngl_mul_1_l Hon) | ].
exfalso.
apply rngl_leb_nle in Hzsa.
apply Hzsa; clear Hzsa.
destruct n; cbn. {
  apply rl_sqrt_nonneg.
  apply rngl_1_sub_cos_div_2_nonneg.
} {
  apply rl_sqrt_nonneg.
  apply rngl_1_sub_cos_div_2_nonneg.
}
Qed.

Theorem rngl_cos_div_pow_2_div_2_bound :
  ∀ n θ, (-1 ≤ rngl_cos_div_pow_2 (θ /₂) n)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (-1)%L), (H1 (rngl_cos_div_pow_2 _ _)).
  apply (rngl_le_refl Hor).
}
intros.
induction n; cbn - [ angle_div_2 ]; [ apply rngl_cos_bound | ].
apply (rngl_le_trans Hor _ 0). {
  apply (rngl_opp_1_le_0 Hon Hop Hor).
}
apply rl_sqrt_nonneg.
apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
now apply (rngl_le_opp_l Hop Hor).
Qed.

Theorem squ_rngl_cos_div_pow_2_div_2_bound :
  ∀ n θ, (-1 ≤ squ_rngl_cos_div_pow_2 (θ /₂) n ≤ 1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (-1)%L), (H1 (squ_rngl_cos_div_pow_2 _ _)), (H1 1%L).
  split; apply (rngl_le_refl Hor).
}
intros.
induction n; cbn - [ angle_div_2 ]; [ apply rngl_cos_bound | ].
split. {
  apply (rngl_le_trans Hor _ 0). {
    apply (rngl_opp_1_le_0 Hon Hop Hor).
  }
  apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now apply (rngl_le_opp_l Hop Hor).
} {
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_add_le_mono_l Hop Hor).
  apply IHn.
}
Qed.

Theorem rngl_cos_div_pow_2_lower_bound :
  ∀ n θ,
  (squ_rngl_cos_div_pow_2 (θ /₂) n ≤ rngl_cos_div_pow_2 (θ /₂) n)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 (squ_rngl_cos_div_pow_2 _ _)).
  rewrite (H1 (rngl_cos_div_pow_2 _ _)).
  apply (rngl_le_refl Hor).
}
intros.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply angle_eqb_eq in Htz.
  subst θ.
  rewrite angle_0_div_2.
  rewrite rngl_cos_div_pow_2_0.
  rewrite squ_rngl_cos_div_pow_2_0.
  apply (rngl_le_refl Hor).
}
apply angle_eqb_neq in Htz.
revert θ Htz.
induction n; intros; [ apply (rngl_le_refl Hor) | ].
cbn.
remember (1 + squ_rngl_cos_div_pow_2 _ _)%L as a eqn:Ha.
remember (1 + rngl_cos_div_pow_2 _ _)%L as b eqn:Hb.
move b before a.
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply rl_sqrt_nonneg; subst b.
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_div_pow_2_div_2_bound.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor (a / 2))%L. 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  subst a.
  apply (rngl_le_opp_l Hop Hor).
  apply squ_rngl_cos_div_pow_2_div_2_bound.
}
apply (rngl_squ_le_abs_le Hop Hor Hii).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  subst b.
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_div_pow_2_div_2_bound.
}
rewrite (rngl_squ_div Hic Hon Hos Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
progress unfold rngl_squ at 2.
rewrite <- (rngl_div_div Hos Hon Hiv); cycle 1. {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
} {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
apply (rngl_le_div_l Hon Hop Hiv Hor). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
subst a b.
rewrite (rngl_squ_add Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite <- rngl_add_assoc.
rewrite (rngl_mul_add_distr_r _ _ 2)%L.
rewrite (rngl_mul_1_l Hon).
rewrite <- rngl_add_assoc.
apply (rngl_add_le_mono_l Hop Hor).
rewrite (rngl_mul_comm Hic), rngl_add_comm.
apply (rngl_add_le_compat Hor). 2: {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor). {
    apply (rngl_0_le_2 Hon Hop Hor).
  }
  now apply IHn.
}
rewrite <- (rngl_squ_1 Hon).
apply (rngl_abs_le_squ_le Hop Hor).
rewrite (rngl_abs_1 Hon Hop Hor).
progress unfold rngl_abs.
remember (squ_rngl_cos_div_pow_2 (θ /₂) n ≤? 0)%L as scz eqn:Hscz.
symmetry in Hscz.
destruct scz. {
  apply rngl_leb_le in Hscz.
  apply (rngl_le_opp_l Hop Hor).
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply squ_rngl_cos_div_pow_2_div_2_bound.
}
apply (rngl_leb_gt Hor) in Hscz.
apply squ_rngl_cos_div_pow_2_div_2_bound.
Qed.

Theorem rngl_cos_angle_div_2_pow_tending_to_1 :
  rngl_characteristic T ≠ 1 →
  rngl_is_archimedean T = true →
  ∀ θ, rngl_is_limit_when_tending_to_inf (λ i, rngl_cos (θ /₂^i)) 1%L.
Proof.
intros Hc1 Har.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros.
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n → (1 - rngl_cos (θ /₂^n) < ε)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  progress unfold rngl_dist.
  rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
    apply (rngl_le_sub_0 Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_opp_sub_distr Hop).
  easy.
}
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n →
    (1 - ε < rngl_cos_div_pow_2 (θ /₂) n)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists (S N).
  intros n Hn.
  destruct n; [ easy | ].
  apply Nat.succ_le_mono in Hn.
  specialize (HN n Hn).
  rewrite rngl_cos_div_pow_2_eq.
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  easy.
}
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n →
    (1 - ε < squ_rngl_cos_div_pow_2 (θ /₂) n)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros n Hn.
  eapply (rngl_lt_le_trans Hor). 2: {
    apply rngl_cos_div_pow_2_lower_bound.
  }
  now apply HN.
}
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n →
    ((1 - rngl_cos (θ /₂)) / 2 ^ n < ε)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros n Hn.
  remember (θ /₂)%A as θ' eqn:Hθ.
  specialize (HN n Hn).
  clear N Hn.
  revert ε Hε HN.
  induction n; intros. {
    cbn in HN |-*.
    rewrite (rngl_div_1_r Hon Hiq Hc1) in HN.
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    apply (rngl_lt_sub_lt_add_r Hop Hor).
    easy.
  }
  cbn.
  apply (rngl_lt_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rngl_add_sub_assoc Hop).
  apply (rngl_add_lt_mono_l Hop Hor).
  apply IHn. {
    rewrite rngl_mul_add_distr_l.
    rewrite (rngl_mul_1_r Hon).
    apply (rngl_lt_trans Hor _ ε); [ easy | ].
    now apply (rngl_lt_add_l Hos Hor).
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_div_div Hos Hon Hiv); cycle 1. {
    apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  } {
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  }
  cbn in HN.
  now destruct n.
}
intros ε Hε.
remember ((1 - rngl_cos (θ /₂)))%L as a eqn:Ha.
specialize (int_part Hon Hop Hc1 Hor Har) as H1.
specialize (H1 (a / ε))%L.
destruct H1 as (N, HN).
exists (Nat.log2 N + 1).
intros n Hn.
apply (rngl_lt_div_l Hon Hop Hiv Hor). {
  apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite (rngl_mul_comm Hic).
apply (rngl_lt_div_l Hon Hop Hiv Hor); [ easy | ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor (_ / _))%L. 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
  rewrite (rngl_mul_0_l Hos).
  rewrite Ha.
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
eapply (rngl_lt_le_trans Hor); [ apply HN | ].
apply (Nat.pow_le_mono_r 2) in Hn; [ | easy ].
apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor) in Hn.
do 2 rewrite (rngl_of_nat_pow Hon Hos) in Hn.
cbn in Hn.
rewrite rngl_add_0_r in Hn.
eapply (rngl_le_trans Hor); [ | apply Hn ].
replace 2%L with (rngl_of_nat 2). 2: {
  cbn.
  now rewrite rngl_add_0_r.
}
rewrite <- (rngl_of_nat_pow Hon Hos).
apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
rewrite Nat.add_1_r.
apply Nat.le_succ_l.
clear HN Hn.
rewrite Nat.add_1_r.
cbn.
rewrite Nat.add_0_r.
induction N; [ easy | ].
specialize (Nat.log2_succ_or N) as H1.
destruct H1 as [H1| H1]. {
  rewrite H1.
  cbn.
  rewrite Nat.add_0_r.
  apply Nat.succ_lt_mono in IHN.
  eapply Nat.lt_le_trans; [ apply IHN | ].
  rewrite <- Nat.add_1_r.
  apply Nat.add_le_mono_l.
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.eq_add_0 in H.
  destruct H as (H, _).
  revert H.
  now apply Nat.pow_nonzero.
}
apply Nat.le_neq.
split; [ now rewrite H1 | ].
intros H2.
rewrite H1 in H2.
rewrite <- Nat_mul_2_l in H2.
rewrite <- Nat.pow_succ_r in H2; [ | easy ].
specialize (Nat.log2_spec (S N)) as H3.
specialize (H3 (Nat.lt_0_succ _)).
rewrite H1 in H3.
rewrite <- H2 in H3.
destruct H3 as (H3, H4).
now apply Nat.lt_irrefl in H4.
Qed.

End a.
