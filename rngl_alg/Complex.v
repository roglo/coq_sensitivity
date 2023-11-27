(* Real-Like numbers *)
(* Algebraic structure having the same properties as real numbers *)
(* and complex numbers *)
(* see also Quaternions.v *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Init.Nat.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike Main.IterAdd.
Require Import RealLike TrigoWithoutPi AngleLeSubAdd.
Require Import AngleAddOverflowLe.

Notation "x ≤ y" := (Z.le x y) : Z_scope.

(* general complex whose real and imaginary parts are of type T
   that is not necessarily the real numbers *)

Class GComplex T := mk_gc {gre : T; gim : T}.

Arguments mk_gc {T} gre%L gim%L.
Arguments gre {T} GComplex%L.
Arguments gim {T} GComplex%L.

Arguments rngl_opt_eq_dec T {ring_like_op}.
Arguments rngl_opt_inv_or_quot T {ring_like_op}.
Arguments rngl_opt_one T {ring_like_op}.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

Theorem eq_gc_eq :
  ∀ a b : GComplex T, gre a = gre b ∧ gim a = gim b ↔ a = b.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct a, b; cbn in Hab.
now f_equal.
Qed.

Theorem neq_gc_neq :
  ∀ a b : GComplex T, gre a ≠ gre b ∨ gim a ≠ gim b → a ≠ b.
Proof.
intros * Hab.
intros H; subst b.
now destruct Hab.
Qed.

Theorem neq_neq_GComplex :
  rngl_has_eq_dec T = true →
  ∀ a b : GComplex T, a ≠ b → gre a ≠ gre b ∨ gim a ≠ gim b.
Proof.
intros Heb * Hab.
destruct a as (ra, ia).
destruct b as (rb, ib); cbn.
destruct (rngl_eq_dec Heb ra rb) as [Hrab| Hrab]. {
  subst rb; right.
  now intros Hiab; apply Hab; clear Hab; subst ib.
} {
  now left.
}
Qed.

Definition gc_zero : GComplex T :=
  {| gre := rngl_zero; gim := rngl_zero |}.

Definition gc_one : GComplex T :=
  {| gre := rngl_one; gim := rngl_zero |}.

Definition gc_opt_one : option (GComplex T) :=
  match rngl_opt_one T with
  | Some one => Some (mk_gc one rngl_zero)
  | None => None
  end.

Definition gc_add (ca cb : GComplex T) :=
  {| gre := gre ca + gre cb; gim := gim ca + gim cb |}.

Definition gc_mul (ca cb : GComplex T) :=
  {| gre := (gre ca * gre cb - gim ca * gim cb)%L;
     gim := (gre ca * gim cb + gim ca * gre cb)%L |}.

Definition gc_opt_opp_or_subt :
  option ((GComplex T → GComplex T) + (GComplex T → GComplex T → GComplex T)) :=
  match rngl_opt_opp_or_subt with
  | Some (inl opp) =>
      Some (inl (λ c, mk_gc (opp (gre c)) (opp (gim c))))
  | Some (inr subt) =>
      Some (inr (λ c d, mk_gc (subt (gre c) (gre d)) (subt (gim c) (gim d))))
  | None =>
      None
  end.

Definition gc_inv a :=
  let d := (gre a * gre a + gim a * gim a)%L in
  mk_gc (gre a / d) (- gim a / d)%L.

End a.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Arguments rl_has_integral_modulus T {ro rp real_like_prop}.

Definition gc_opt_inv_or_quot :
  option ((GComplex T → GComplex T) + (GComplex T → GComplex T → GComplex T)) :=
  match rngl_opt_inv_or_quot T with
  | Some (inl inv) =>
      if rngl_mul_is_comm T then
        if rl_has_integral_modulus T then Some (inl gc_inv) else None
      else None
  | Some (inr quot) =>
      None (* à voir *)
  | None =>
      None
  end.

Theorem rl_integral_modulus_prop :
  rl_has_integral_modulus T = true →
  ∀ a b : T, (rngl_squ a + rngl_squ b = 0 → a = 0 ∧ b = 0)%L.
Proof.
intros Him * Hab.
specialize rl_opt_integral_modulus_prop as Hmi.
rewrite Him in Hmi.
now apply Hmi.
Qed.

Theorem rl_sqrt_squ :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (√(a²))%L = rngl_abs a.
Proof.
intros Hop Hor *.
progress unfold rngl_squ.
progress unfold rngl_abs.
progress unfold rl_sqrt.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az. {
  apply rngl_leb_le in Haz.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Haz.
  rewrite <- (rngl_mul_opp_opp Hop).
  rewrite rl_nth_root_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite rngl_squ_pow_2.
  now apply rl_nth_root_pow.
} {
  apply (rngl_leb_gt Hor) in Haz.
  apply (rngl_lt_le_incl Hor) in Haz.
  rewrite rl_nth_root_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite rngl_squ_pow_2.
  now apply rl_nth_root_pow.
}
Qed.

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
rewrite <- rngl_squ_pow_2 in H1.
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hii) in H1.
rewrite (rngl_abs_nonneg_eq Hop Hor) in H1. 2: {
  now apply rl_sqrt_nonneg.
}
now rewrite (rngl_abs_1 Hon Hop Hor) in H1.
Qed.

Theorem rl_acos_prop :
  rngl_is_ordered T = true →
  ∀ x, (x² ≤ 1)%L → cos2_sin2_prop x √(1 - x²)%L.
Proof.
intros Hor * Hx1.
progress unfold cos2_sin2_prop.
remember (rngl_has_1 T) as on eqn:Hon; symmetry in Hon.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
remember (rngl_has_eq_dec T) as ed eqn:Hed; symmetry in Hed.
destruct on; [ | easy ].
destruct op; [ | easy ].
destruct ic; [ | easy ].
destruct ed; [ cbn | easy ].
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_eqb_eq Hed).
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_add_le_sub_r Hop Hor).
  now rewrite rngl_add_0_l.
}
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
apply (rngl_add_sub Hos).
Qed.

Context {Hor : rngl_is_ordered T = true}.

Definition rl_acos (x : T) :=
  match (rngl_le_dec Hor x² 1)%L with
  | left Hx1 =>
      {| rngl_cos := x; rngl_sin := rl_sqrt (1 - rngl_squ x)%L;
         rngl_cos2_sin2 := rl_acos_prop Hor x Hx1 |}
  | _ =>
      angle_zero
  end.

Arguments rl_acos x%L.

Theorem rl_cos_acos : ∀ x, (x² ≤ 1)%L → rngl_cos (rl_acos x) = x.
Proof.
intros * Hx1.
progress unfold rl_acos.
now destruct (rngl_le_dec Hor x² 1).
Qed.

Theorem gc_eq_dec :
  rngl_has_eq_dec T = true →
  ∀ a b : GComplex T, {a = b} + {a ≠ b}.
Proof.
intros Hed *.
destruct a as (ra, ia).
destruct b as (rb, ib).
specialize (rngl_eq_dec Hed ra rb) as H1.
specialize (rngl_eq_dec Hed ia ib) as H2.
destruct H1 as [H1| H1]. {
  subst rb.
  destruct H2 as [H2| H2]; [ now subst ib; left | right ].
  intros H; apply H2.
  now injection H.
} {
  right.
  intros H; apply H1.
  now injection H.
}
Qed.

Definition gc_opt_eq_dec : option (∀ a b : GComplex T, {a = b} + {a ≠ b}) :=
  match Bool.bool_dec (rngl_has_eq_dec T) true with
  | left Hed => Some (gc_eq_dec Hed)
  | right _ => None
  end.

Fixpoint gc_power_nat {T} {ro : ring_like_op T} (z : GComplex T) n :=
  match n with
  | 0 => gc_one
  | S n' => gc_mul z (gc_power_nat z n')
  end.

End a.

Arguments rl_has_integral_modulus T {ro rp real_like_prop}.
Arguments rl_opt_integral_modulus_prop T {ro rp real_like_prop}.

Declare Scope gc_scope.
Delimit Scope gc_scope with C.

Notation "x + y" := (gc_add x y) : gc_scope.
Notation "x * y" := (gc_mul x y) : gc_scope.
Notation "'√' a" := (rl_sqrt a) (at level 1, format "√ a") : ring_like_scope.
Notation "x + 'ℹ' * y" := (mk_gc x y) (at level 50) : gc_scope.
Notation "z ^ n" := (gc_power_nat z n) : gc_scope.

Definition gc_ring_like_op T
  {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T} :
  ring_like_op (GComplex T) :=
  {| rngl_zero := gc_zero;
     rngl_add := gc_add;
     rngl_mul := gc_mul;
     rngl_opt_one := gc_opt_one;
     rngl_opt_opp_or_subt := gc_opt_opp_or_subt;
     rngl_opt_inv_or_quot := gc_opt_inv_or_quot;
     rngl_opt_eq_dec := gc_opt_eq_dec;
     rngl_opt_leb := None |}.

Arguments gc_power_nat {T ro} z%C n%nat.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_mul_2_div_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ a,
  angle_div_2 (angle_mul_nat a 2) =
    if angle_ltb a angle_straight then a else angle_add a angle_straight.
Proof.
intros Hic Hon Hop Hed *.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
apply eq_angle_eq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now do 2 rewrite (H1 (rngl_cos _)), (H1 (rngl_sin _)).
}
move Hc1 after Hc2.
specialize (rngl_2_neq_0 Hon Hop Hc1 Hor) as H20.
remember (angle_ltb a angle_straight) as ap eqn:Hap; symmetry in Hap.
destruct ap. {
  progress unfold angle_mul_nat.
  progress unfold angle_div_2.
  progress unfold angle_add.
  cbn.
  do 2 rewrite (rngl_mul_0_r Hos).
  rewrite rngl_add_0_l.
  rewrite (rngl_sub_0_r Hos).
  do 2 rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_mul_comm Hic (rngl_cos a)).
  rewrite (rngl_add_diag Hon).
  rewrite rngl_mul_assoc.
  set (ε := if (0 ≤? _)%L then 1%L else (-1)%L).
  assert (Hε : (ε² = 1)%L). {
    progress unfold ε.
    destruct (0 ≤? _)%L. {
      apply (rngl_mul_1_l Hon).
    } {
      apply (rngl_squ_opp_1 Hon Hop).
    }
  }
  do 2 rewrite fold_rngl_squ.
  progress unfold angle_ltb in Hap.
  cbn in Hap.
  rewrite (rngl_leb_refl Hor) in Hap.
  destruct a as (ca, sa, Ha); cbn in ε, Hap |-*.
  remember (0 ≤? sa)%L as zs eqn:Hzs; symmetry in Hzs.
  destruct zs; [ | easy ].
  apply rngl_ltb_lt in Hap.
  apply rngl_leb_le in Hzs.
  apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed) in Ha.
  apply (rngl_add_sub_eq_r Hos) in Ha.
  rewrite <- Ha.
  rewrite <- (rngl_sub_add_distr Hos).
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_sub_diag Hos), rngl_add_0_l.
  rewrite (rngl_add_diag Hon sa²%L).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  do 2 rewrite (rngl_mul_comm Hic 2%L).
  rewrite (rngl_mul_div Hi1); [ | easy ].
  rewrite (rngl_mul_div Hi1); [ | easy ].
  rewrite Ha.
  do 2 rewrite (rl_sqrt_squ Hop Hor).
  rewrite (rngl_abs_nonneg_eq Hop Hor sa); [ | easy ].
  f_equal.
  subst ε.
  remember (0 ≤? 2 * sa * ca)%L as zsc eqn:Hzsc; symmetry in Hzsc.
  destruct zsc. {
    apply rngl_leb_le in Hzsc.
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_abs_nonneg_eq Hop Hor).
    apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2⁻¹%L) in Hzsc. 2: {
      apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    rewrite (rngl_mul_0_r Hos) in Hzsc.
    do 2 rewrite rngl_mul_assoc in Hzsc.
    rewrite (rngl_mul_inv_diag_l Hon Hiv) in Hzsc; [ | easy ].
    rewrite (rngl_mul_1_l Hon) in Hzsc.
    destruct (rngl_eq_dec Hed sa 0) as [Hsz| Hsz]. {
      subst sa.
      rewrite (rngl_squ_0 Hos) in Ha.
      rewrite (rngl_sub_0_r Hos) in Ha.
      symmetry in Ha.
      rewrite <- (rngl_squ_1 Hon) in Ha.
      apply (rngl_squ_eq_cases Hic Hon Hop Hiv Hed) in Ha.
      destruct Ha as [Ha| Ha]; subst ca. 2: {
        now apply (rngl_lt_irrefl Hor) in Hap.
      }
      apply (rngl_0_le_1 Hon Hop Hor).
    }
    rewrite (rngl_mul_comm Hic) in Hzsc.
    apply (rngl_le_div_l Hon Hop Hiv Hor) in Hzsc. 2: {
      apply not_eq_sym in Hsz.
      now apply (rngl_lt_iff Hor).
    }
    now rewrite (rngl_div_0_l Hos Hi1) in Hzsc.
  }
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_opp_inj Hop).
  rewrite (rngl_opp_involutive Hop).
  apply (rngl_abs_nonpos_eq Hop Hor).
  apply (rngl_leb_gt Hor) in Hzsc.
  rewrite <- (rngl_mul_0_r Hos 2)%L in Hzsc.
  rewrite <- rngl_mul_assoc in Hzsc.
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii) in Hzsc. 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  apply (rngl_nle_gt Hor) in Hzsc.
  apply (rngl_lt_le_incl Hor).
  apply (rngl_nle_gt Hor).
  intros H; apply Hzsc.
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
} {
  progress unfold angle_mul_nat.
  progress unfold angle_div_2.
  progress unfold angle_add.
  cbn.
  do 2 rewrite (rngl_mul_0_r Hos).
  rewrite rngl_add_0_l.
  rewrite (rngl_sub_0_r Hos).
  do 2 rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_mul_comm Hic (rngl_cos a)).
  rewrite (rngl_add_diag Hon).
  rewrite rngl_mul_assoc.
  set (ε := if (0 ≤? _)%L then 1%L else (-1)%L).
  assert (Hε : (ε² = 1)%L). {
    progress unfold ε.
    destruct (0 ≤? _)%L. {
      apply (rngl_mul_1_l Hon).
    } {
      apply (rngl_squ_opp_1 Hon Hop).
    }
  }
  do 2 rewrite fold_rngl_squ.
  progress unfold angle_ltb in Hap.
  cbn in Hap.
  rewrite (rngl_leb_refl Hor) in Hap.
  destruct a as (ca, sa, Ha); cbn in ε, Hap |-*.
  remember (0 ≤? sa)%L as zs eqn:Hzs; symmetry in Hzs.
  destruct zs. {
    apply (rngl_ltb_ge Hor) in Hap.
    specialize (rngl_cos_proj_bound Hic Hon Hop Hiv Hed Hor) as H1.
    specialize (H1 _ _ Ha).
    apply (rngl_le_antisymm Hor) in Hap; [ | easy ].
    subst ca; clear H1.
    apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed) in Ha.
    rewrite (rngl_squ_opp Hop) in Ha.
    rewrite (rngl_squ_1 Hon) in Ha.
    apply (rngl_add_sub_eq_l Hos) in Ha.
    rewrite (rngl_sub_diag Hos) in Ha.
    symmetry in Ha.
    apply (eq_rngl_squ_0 Hos Hid) in Ha.
    subst sa.
    subst ε.
    rewrite (rngl_mul_0_r Hos).
    rewrite (rngl_mul_0_l Hos).
    rewrite (rngl_leb_refl Hor).
    rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_squ_opp Hop).
    rewrite (rngl_squ_1 Hon).
    rewrite (rngl_squ_0 Hos).
    rewrite (rngl_sub_0_r Hos).
    rewrite (rngl_div_diag Hon Hiq); [ | easy ].
    rewrite (rl_sqrt_1 Hic Hon Hop Hor Hid).
    rewrite (rngl_sub_diag Hos).
    rewrite (rngl_div_0_l Hos Hi1); [ | easy ].
    rewrite (rl_sqrt_0 Hop Hic Hor Hid).
    rewrite (rngl_sub_0_r Hos).
    rewrite (rngl_squ_opp_1 Hon Hop).
    now rewrite rngl_add_0_l.
  } {
    clear Hap.
    apply (rngl_leb_gt Hor) in Hzs.
    apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed) in Ha.
    rewrite (rngl_sub_0_r Hos).
    rewrite rngl_add_0_l.
    do 2 rewrite (rngl_mul_opp_r Hop).
    do 2 rewrite (rngl_mul_1_r Hon).
    rewrite <- Ha at 1.
    rewrite (rngl_add_sub_assoc Hop).
    rewrite rngl_add_add_swap.
    rewrite (rngl_add_sub Hos).
    rewrite (rngl_add_diag Hon).
    rewrite (rngl_mul_comm Hic 2)%L.
    rewrite (rngl_mul_div Hi1); [ | easy ].
    rewrite (rl_sqrt_squ Hop Hor).
    rewrite <- Ha at 1.
    rewrite (rngl_sub_sub_distr Hop).
    rewrite (rngl_add_comm ca²%L).
    rewrite (rngl_add_sub Hos).
    rewrite (rngl_add_diag Hon).
    rewrite (rngl_mul_comm Hic 2%L).
    rewrite (rngl_mul_div Hi1); [ | easy ].
    rewrite (rl_sqrt_squ Hop Hor).
    rewrite (rngl_abs_nonpos_eq Hop Hor sa). 2: {
      now apply (rngl_lt_le_incl Hor).
    }
    f_equal.
    subst ε.
    remember (0 ≤? _)%L as zsc eqn:Hzsc; symmetry in Hzsc.
    destruct zsc. {
      rewrite (rngl_mul_1_l Hon).
      apply (rngl_abs_nonpos_eq Hop Hor).
      apply rngl_leb_le in Hzsc.
      apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2⁻¹%L) in Hzsc. 2: {
        apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      rewrite (rngl_mul_0_r Hos) in Hzsc.
      do 2 rewrite rngl_mul_assoc in Hzsc.
      rewrite (rngl_mul_inv_diag_l Hon Hiv) in Hzsc; [ | easy ].
      rewrite (rngl_mul_1_l Hon) in Hzsc.
      apply (rngl_nle_gt Hor) in Hzs.
      apply (rngl_nlt_ge Hor).
      intros H; apply Hzs; clear Hzs.
      rewrite <- (rngl_mul_0_l Hos ca) in Hzsc.
      now apply (rngl_mul_le_mono_pos_r Hop Hor Hii) in Hzsc.
    } {
      rewrite (rngl_mul_opp_l Hop).
      rewrite (rngl_mul_1_l Hon).
      f_equal.
      apply (rngl_abs_nonneg_eq Hop Hor).
      apply (rngl_leb_gt Hor) in Hzsc.
      apply (rngl_nle_gt Hor) in Hzsc.
      apply (rngl_nlt_ge Hor).
      intros Hca; apply Hzsc; clear Hzsc.
      apply (rngl_mul_nonpos_nonpos Hop Hor). 2: {
        now apply (rngl_lt_le_incl Hor).
      }
      rewrite <- (rngl_add_diag Hon).
      rewrite <- (rngl_add_0_l 0)%L.
      apply (rngl_lt_le_incl Hor) in Hzs.
      now apply (rngl_add_le_compat Hor).
    }
  }
}
Qed.

Theorem gc_add_comm :
  let roc := gc_ring_like_op T in
  ∀ a b, (a + b)%L = (b + a)%L.
Proof.
intros; cbn.
progress unfold gc_add.
f_equal; apply rngl_add_comm.
Qed.

Theorem gc_add_assoc :
  let roc := gc_ring_like_op T in
  ∀ a b c : GComplex T, (a + (b + c))%L = (a + b + c)%L.
Proof.
intros; cbn.
progress unfold gc_add; cbn.
f_equal; apply rngl_add_assoc.
Qed.

Theorem gc_add_0_l :
  let roc := gc_ring_like_op T in
  ∀ a : GComplex T, (0 + a)%L = a.
Proof.
intros; cbn.
progress unfold gc_add; cbn.
do 2 rewrite rngl_add_0_l.
now apply eq_gc_eq.
Qed.

Theorem gc_mul_assoc :
  let roc := gc_ring_like_op T in
  rngl_has_opp T = true →
  ∀ a b c : GComplex T, (a * (b * c))%L = (a * b * c)%L.
Proof.
intros * Hop *; cbn.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold gc_mul; cbn.
do 2 rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_sub_distr_r Hop).
do 2 rewrite rngl_mul_add_distr_l.
do 2 rewrite rngl_mul_add_distr_r.
do 8 rewrite rngl_mul_assoc.
do 2 rewrite <- (rngl_sub_add_distr Hos).
f_equal. {
  f_equal.
  do 2 rewrite rngl_add_assoc.
  now rewrite rngl_add_comm, rngl_add_assoc.
} {
  unfold rngl_sub; rewrite Hop.
  do 2 rewrite <- rngl_add_assoc.
  f_equal.
  do 2 rewrite rngl_add_assoc.
  rewrite rngl_add_comm.
  now rewrite rngl_add_assoc.
}
Qed.

Theorem gc_opt_mul_1_l :
  let roc := gc_ring_like_op T in
  rngl_has_opp_or_subt T = true →
  if rngl_has_1 (GComplex T) then ∀ a : GComplex T, (1 * a)%L = a
  else not_applicable.
Proof.
intros * Hos.
remember (rngl_has_1 (GComplex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ | easy ].
intros; cbn.
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honc; cbn in Honc.
  progress unfold gc_opt_one in Honc.
  progress unfold rngl_has_1 in Honc |-*.
  now destruct rngl_opt_one.
}
progress unfold gc_mul.
apply eq_gc_eq; cbn.
specialize (rngl_mul_1_l Hon) as H1.
progress unfold rngl_has_1 in Hon.
progress unfold "1"%L in H1; cbn in H1.
progress unfold "1"%L; cbn.
progress unfold gc_opt_one; cbn.
destruct (rngl_opt_one T) as [one| ]; [ cbn | easy ].
do 2 rewrite H1.
do 2 rewrite (rngl_mul_0_l Hos).
now rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
Qed.

Theorem gc_mul_add_distr_l :
  let roc := gc_ring_like_op T in
  rngl_has_opp T = true →
  ∀ a b c : GComplex T, (a * (b + c))%L = (a * b + a * c)%L.
Proof.
intros * Hop *; cbn.
apply eq_gc_eq; cbn.
progress unfold rngl_sub; rewrite Hop.
do 4 rewrite rngl_mul_add_distr_l.
rewrite (rngl_opp_add_distr Hop).
progress unfold rngl_sub; rewrite Hop.
do 4 rewrite <- rngl_add_assoc.
split; f_equal. {
  now rewrite rngl_add_assoc, rngl_add_comm.
} {
  rewrite rngl_add_comm.
  rewrite <- rngl_add_assoc; f_equal.
  apply rngl_add_comm.
}
Qed.

Theorem gc_opt_mul_comm :
  let roc := gc_ring_like_op T in
  if rngl_mul_is_comm T then ∀ a b : GComplex T, (a * b)%L = (b * a)%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_comm Hic (gre b)).
do 2 rewrite (rngl_mul_comm Hic (gim b)).
split; [ easy | ].
apply rngl_add_comm.
Qed.

Theorem gc_opt_mul_1_r :
  let roc := gc_ring_like_op T in
  rngl_has_opp_or_subt T = true →
  if rngl_mul_is_comm T then not_applicable
  else if rngl_has_1 (GComplex T) then ∀ a : GComplex T, (a * 1)%L = a
  else not_applicable.
Proof.
intros * Hos.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
remember (rngl_has_1 (GComplex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ | easy ].
intros.
apply eq_gc_eq; cbn.
progress unfold "1"%L; cbn.
progress unfold gc_opt_one.
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honc; cbn in Honc.
  progress unfold gc_opt_one in Honc.
  progress unfold rngl_has_1.
  now destruct (rngl_opt_one T).
}
specialize (rngl_mul_1_r Hon) as H1.
unfold rngl_has_1 in Honc.
cbn in Honc.
progress unfold gc_opt_one in Honc.
progress unfold "1"%L in H1.
remember (rngl_opt_one T) as on eqn:Hon'; symmetry in Hon'.
destruct on as [one| ]; [ cbn | easy ].
do 2 rewrite H1.
do 2 rewrite (rngl_mul_0_r Hos).
now rewrite (rngl_sub_0_r Hos), rngl_add_0_l.
Qed.

Theorem gc_opt_mul_add_distr_r :
  let roc := gc_ring_like_op T in
  rngl_has_opp T = true →
  if rngl_mul_is_comm T then not_applicable
  else ∀ a b c : GComplex T, ((a + b) * c)%L = (a * c + b * c)%L.
Proof.
intros * Hop.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
intros.
apply eq_gc_eq; cbn.
do 4 rewrite rngl_mul_add_distr_r.
progress unfold rngl_sub.
rewrite Hop.
rewrite (rngl_opp_add_distr Hop).
do 4 rewrite <- rngl_add_assoc.
split; f_equal. {
  progress unfold rngl_sub.
  rewrite Hop.
  do 2 rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap; f_equal.
  apply rngl_add_comm.
} {
  rewrite rngl_add_comm.
  rewrite <- rngl_add_assoc; f_equal.
  apply rngl_add_comm.
}
Qed.

Theorem gc_opt_add_opp_diag_l :
  let roc := gc_ring_like_op T in
  rngl_has_opp T = true →
  if rngl_has_opp (GComplex T) then ∀ a : GComplex T, (- a + a)%L = 0%L
  else not_applicable.
Proof.
intros * Hop.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
remember (rngl_has_opp (GComplex T)) as opc eqn:Hopc; symmetry in Hopc.
destruct opc; [ | easy ].
intros.
apply eq_gc_eq; cbn.
specialize (rngl_add_opp_diag_l Hop) as H1.
progress unfold rngl_opp; cbn.
progress unfold gc_opt_opp_or_subt; cbn.
progress unfold rngl_has_opp in Hop.
progress unfold rngl_opp in H1.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ cbn | easy ].
now do 2 rewrite H1.
Qed.

Theorem gc_opt_add_sub :
  let roc := gc_ring_like_op T in
  rngl_has_subt T = false →
  if rngl_has_subt (GComplex T) then ∀ a b : GComplex T, (a + b - b)%L = a
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_subt; cbn.
progress unfold gc_opt_opp_or_subt.
progress unfold rngl_has_subt in Hsu.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem gc_opt_sub_add_distr :
  let roc := gc_ring_like_op T in
  rngl_has_subt T = false →
  if rngl_has_subt (GComplex T) then
    ∀ a b c : GComplex T, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_subt; cbn.
progress unfold gc_opt_opp_or_subt.
progress unfold rngl_has_subt in Hsu.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem gc_inv_re :
  let roc := gc_ring_like_op T in
  rngl_mul_is_comm T = true →
  rl_has_integral_modulus T = true →
  ∀ a : GComplex T, a ≠ 0%L →
  gre a⁻¹ = (gre a / (gre a * gre a + gim a * gim a))%L.
Proof.
intros * Hic Hrl * Haz.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
progress unfold rngl_inv; cbn.
progress unfold gc_opt_inv_or_quot.
progress unfold rngl_has_inv_or_quot in Hiq.
progress unfold rngl_has_inv in Hiv.
rewrite Hrl.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
destruct iq; [ | easy ].
now rewrite Hic.
Qed.

Theorem gc_inv_im :
  let roc := gc_ring_like_op T in
  rngl_mul_is_comm T = true →
  rl_has_integral_modulus T = true →
  ∀ a : GComplex T, a ≠ 0%L →
  gim a⁻¹ = (- gim a / (gre a * gre a + gim a * gim a))%L.
Proof.
intros * Hic Hrl * Haz.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
progress unfold rngl_inv; cbn.
progress unfold gc_opt_inv_or_quot.
progress unfold rngl_has_inv_or_quot in Hiq.
progress unfold rngl_has_inv in Hiv.
rewrite Hrl.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
destruct iq; [ | easy ].
now rewrite Hic.
Qed.

Theorem gc_opt_mul_inv_diag_l :
  let roc := gc_ring_like_op T in
  rngl_has_opp T = true →
  if (rngl_has_inv (GComplex T) && rngl_has_1 (GComplex T))%bool then
    ∀ a : GComplex T, a ≠ 0%L → (a⁻¹ * a)%L = 1%L
  else not_applicable.
Proof.
intros * Hop.
destruct ac as (Hiv, Hc2, Hor).
remember (rl_has_integral_modulus T) as hrl eqn:Hrl; symmetry in Hrl.
destruct hrl. 2: {
  progress unfold rngl_inv; cbn.
  progress unfold gc_opt_inv_or_quot; cbn.
  progress unfold rngl_has_inv; cbn.
  progress unfold gc_opt_inv_or_quot; cbn.
  rewrite Hrl.
  destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
  destruct iq as [inv| quot]; [ | easy ].
  now destruct (rngl_mul_is_comm T).
}
remember (rngl_has_inv (GComplex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 (GComplex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ cbn | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honc; cbn in Honc.
  progress unfold gc_opt_one in Honc.
  progress unfold rngl_has_1.
  unfold rngl_has_1 in Honc; cbn in Honc.
  now destruct rngl_opt_one.
}
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
assert (Hic : rngl_mul_is_comm T = true). {
  progress unfold rngl_has_inv in Hivc; cbn in Hivc.
  progress unfold gc_opt_inv_or_quot in Hivc.
  remember (rngl_opt_inv_or_quot T) as iq eqn:Hiq; symmetry in Hiq.
  destruct iq as [iq| ]; [ | easy ].
  destruct iq; [ | easy ].
  now destruct (rngl_mul_is_comm T).
}
intros * Haz.
apply eq_gc_eq; cbn.
specialize (rngl_mul_inv_diag_l Hon Hiv) as H1.
rewrite (gc_inv_re Hic Hrl); [ | now intros H; subst a ].
rewrite (gc_inv_im Hic Hrl); [ | now intros H; subst a ].
progress unfold rngl_sub.
progress unfold rngl_div.
rewrite Hop, Hiv.
rewrite (rngl_mul_mul_swap Hic (gre a)).
do 2 rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_mul_swap Hic (gim a)).
rewrite (rngl_opp_involutive Hop).
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_mul_comm Hic).
split. {
  progress unfold "1"%L; cbn.
  progress unfold gc_opt_one.
  progress unfold rngl_has_1 in Hon.
  progress unfold "1"%L in H1.
  remember (rngl_opt_one T) as x eqn:Hx; symmetry in Hx.
  destruct x as [one| ]; [ cbn | easy ].
  rewrite H1; [ easy | ].
  intros H2.
  generalize Hrl; intros H.
  apply (rl_integral_modulus_prop H) in H2.
  apply Haz.
  apply eq_gc_eq; cbn.
  now f_equal.
} {
  progress unfold "1"%L; cbn.
  progress unfold gc_opt_one.
  progress unfold rngl_has_1 in Hon.
  progress unfold "1"%L in H1.
  remember (rngl_opt_one T) as x eqn:Hx; symmetry in Hx.
  destruct x as [one| ]; [ cbn | easy ].
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_add_opp_r Hop).
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_mul_swap Hic).
  apply (rngl_sub_diag Hos).
}
Qed.

Theorem gc_opt_mul_inv_diag_r :
  let roc := gc_ring_like_op T in
  if (rngl_has_inv (GComplex T) && rngl_has_1 (GComplex T) &&
      negb (rngl_mul_is_comm T))%bool then
    ∀ a : GComplex T, a ≠ 0%L → (a / a)%L = 1%L
  else not_applicable.
Proof.
cbn.
remember (rl_has_integral_modulus T) as hrl eqn:Hrl; symmetry in Hrl.
destruct hrl. 2: {
  progress unfold rngl_has_inv; cbn.
  progress unfold gc_opt_inv_or_quot; cbn.
  rewrite Hrl.
  destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
  destruct iq as [inv| quot]; [ | easy ].
  now destruct (rngl_mul_is_comm T).
}
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ now rewrite Bool.andb_false_r | ].
rewrite Bool.andb_true_r.
remember (rngl_has_inv (GComplex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
progress unfold rngl_has_inv in Hivc; cbn in Hivc.
progress unfold gc_opt_inv_or_quot in Hivc.
rewrite Hic in Hivc.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
now destruct iq.
Qed.

Theorem gc_opt_mul_div :
  let roc := gc_ring_like_op T in
  if rngl_has_quot (GComplex T) then
    ∀ a b : GComplex T, b ≠ 0%L → (a * b / b)%L = a
  else not_applicable.
Proof.
progress unfold rngl_has_quot; cbn.
progress unfold gc_opt_inv_or_quot.
remember (rngl_opt_inv_or_quot T) as iq eqn:Hiq; symmetry in Hiq.
destruct iq as [iq| ]; [ | easy ].
destruct iq as [inv| quot]; [ | easy ].
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
now destruct (rl_has_integral_modulus T).
Qed.

Theorem gc_opt_mul_quot_r :
  let roc := gc_ring_like_op T in
  if (rngl_has_quot (GComplex T) && negb (rngl_mul_is_comm T))%bool then
    ∀ a b : GComplex T, b ≠ 0%L → (b * a / b)%L = a
  else not_applicable.
Proof.
progress unfold rngl_has_quot; cbn.
progress unfold gc_opt_inv_or_quot.
remember (rngl_opt_inv_or_quot T) as iq eqn:Hiq; symmetry in Hiq.
destruct iq as [iq| ]; [ | easy ].
destruct iq as [inv| quot]; [ | easy ].
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
now destruct (rl_has_integral_modulus T).
Qed.

Theorem gc_characteristic_prop :
  let roc := gc_ring_like_op T in
  if rngl_has_1 (GComplex T) then
    if rngl_characteristic T =? 0 then ∀ i : nat, rngl_mul_nat 1 (S i) ≠ 0%L
    else
      (∀ i : nat, 0 < i < rngl_characteristic T → rngl_mul_nat 1 i ≠ 0%L)
      ∧ rngl_mul_nat 1 (rngl_characteristic T) = 0%L
  else not_applicable.
Proof.
cbn - [ rngl_mul_nat ].
specialize (rngl_opt_characteristic_prop) as H1.
progress unfold rngl_has_1 in H1.
progress unfold rngl_has_1; cbn - [ rngl_mul_nat ].
progress unfold gc_opt_one.
remember (rngl_opt_one T) as on eqn:Hon; symmetry in Hon.
destruct on as [one| ]; [ | easy ].
cbn - [ rngl_mul_nat ] in H1 |-*.
assert
  (Hr :
    ∀ n,
    @rngl_mul_nat _ (gc_ring_like_op T) (mk_gc 1 0) n =
    mk_gc (rngl_mul_nat 1 n) 0). {
  intros.
  progress unfold rngl_mul_nat.
  progress unfold mul_nat; cbn.
  induction n; [ easy | cbn ].
  rewrite IHn.
  progress unfold gc_add; cbn.
  now rewrite rngl_add_0_l.
}
unfold "1"%L in Hr.
rewrite Hon in Hr.
remember (rngl_characteristic T) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  cbn - [ rngl_mul_nat ] in H1 |-*; intros.
  apply neq_gc_neq.
  cbn - [ rngl_mul_nat ].
  left.
  specialize (H1 i).
  intros H2; apply H1; clear H1.
  progress unfold "1"%L in H2; cbn - [ rngl_mul_nat ] in H2.
  progress unfold gc_opt_one in H2.
  progress unfold rngl_of_nat.
  progress unfold "1"%L.
  rewrite Hon in H2 |-*; cbn - [ rngl_mul_nat ] in H2 |-*.
  now rewrite Hr in H2.
} {
  cbn - [ rngl_mul_nat ] in H1 |-*.
  destruct H1 as (H1, H2).
  split. {
    intros i Hi.
    apply neq_gc_neq.
    cbn; left.
    specialize (H1 i Hi).
    intros H3; apply H1; clear H1.
    progress unfold rngl_of_nat.
    progress unfold "1"%L.
    rewrite Hon.
    progress unfold "1"%L in H3; cbn in H3.
    progress unfold gc_opt_one in H3.
    rewrite Hon in H3; cbn in H3.
    now rewrite Hr in H3; cbn in H3.
  } {
    apply eq_gc_eq.
    cbn - [ rngl_mul_nat ].
    progress unfold "1"%L; cbn - [ rngl_mul_nat ].
    progress unfold gc_opt_one.
    progress unfold rngl_of_nat in H2.
    progress unfold "1"%L in H2; cbn - [ rngl_mul_nat ] in H2.
    rewrite Hon in H2 |-*.
    now rewrite Hr.
  }
}
Qed.

(* algebraically closed *)

Definition gc_modl (z : GComplex T) :=
  (gre z * gre z + gim z * gim z)%L.

Theorem le_rl_sqrt_add :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, (0 ≤ b → a ≤ rl_sqrt (rngl_squ a + b))%L.
Proof.
intros * Hon Hop Heb * Hzb.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
apply (rngl_le_trans Hor _ (rngl_abs a)). {
  apply (rngl_le_abs Hop Hor).
}
apply (rngl_square_le_simpl_nonneg Hop Hor Hii). {
  apply rl_sqrt_nonneg.
  apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
  apply (rngl_squ_nonneg Hop Hor).
}
do 2 rewrite fold_rngl_squ.
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
  apply (rngl_squ_nonneg Hop Hor).
}
rewrite (rngl_squ_abs Hop).
now apply (rngl_le_add_r Hor).
Qed.

Theorem rl_sqrt_div_squ_squ :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  rl_has_integral_modulus T = true →
  ∀ x y, (x ≠ 0 ∨ y ≠ 0)%L →
  (-1 ≤ x / rl_sqrt (rngl_squ x + rngl_squ y) ≤ 1)%L.
Proof.
intros * Hon Hop Hed Hmi * Hxyz.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
assert (Hxy : (0 ≤ x² + y²)%L). {
  apply (rngl_add_nonneg_nonneg Hor);
  apply (rngl_squ_nonneg Hop Hor).
}
split. {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    remember (rngl_squ x + rngl_squ y)%L as a eqn:Ha.
    symmetry in Ha.
    apply (rngl_lt_iff Hor).
    split. {
      now apply rl_sqrt_nonneg.
    } {
      intros H3; symmetry in H3.
      apply (f_equal rngl_squ) in H3.
      progress unfold rngl_squ in H3 at 2.
      rewrite (rngl_mul_0_l Hos) in H3.
      rewrite rngl_squ_sqrt in H3; [ | easy ].
      move H3 at top; subst a.
      apply (rl_integral_modulus_prop Hmi) in Ha.
      now destruct Hxyz.
    }
  }
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  destruct (rngl_le_dec Hor 0 x) as [Hzx| Hzx]. {
    apply (rngl_le_trans Hor _ 0). {
      rewrite <- (rngl_opp_0 Hop).
      now apply -> (rngl_opp_le_compat Hop Hor).
    }
    now apply rl_sqrt_nonneg.
  } {
    apply (rngl_nle_gt Hor) in Hzx.
    apply (rngl_opp_lt_compat Hop Hor) in Hzx.
    rewrite (rngl_opp_0 Hop) in Hzx.
    rewrite <- (rngl_squ_opp Hop).
    apply (le_rl_sqrt_add Hon Hop Hed).
    apply (rngl_squ_nonneg Hop Hor).
  }
} {
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    remember (rngl_squ x + rngl_squ y)%L as a eqn:Ha.
    symmetry in Ha.
    apply (rngl_lt_iff Hor).
    split. {
      now apply rl_sqrt_nonneg.
    } {
      intros H3; symmetry in H3.
      apply (f_equal rngl_squ) in H3.
      progress unfold rngl_squ in H3 at 2.
      rewrite (rngl_mul_0_l Hos) in H3.
      rewrite rngl_squ_sqrt in H3; [ | easy ].
      move H3 at top; subst a.
      apply (rl_integral_modulus_prop Hmi) in Ha.
      now destruct Hxyz.
    }
  }
  rewrite (rngl_mul_1_l Hon).
  destruct (rngl_le_dec Hor 0 x) as [Hzx| Hzx]. {
    apply (le_rl_sqrt_add Hon Hop Hed).
    apply (rngl_squ_nonneg Hop Hor).
  } {
    apply (rngl_nle_gt Hor) in Hzx.
    apply (rngl_le_trans Hor _ 0). {
      now apply (rngl_lt_le_incl Hor).
    }
    now apply rl_sqrt_nonneg.
  }
}
Qed.

Arguments rl_acos {T ro rp rl} Hor x%L.
Arguments rl_sqrt_squ {T ro rp rl} Hor Hop a%L.

Theorem polar :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  rl_has_integral_modulus T = true →
  ∀ (z : GComplex T) ρ θ,
  ρ = √((gre z)² + (gim z)²)%L
  → θ =
       (if (0 ≤? gim z)%L then rl_acos ac_or (gre z / ρ)%L
        else angle_opp (rl_acos ac_or (gre z / ρ)%L))
  → z = mk_gc (ρ * rngl_cos θ) (ρ * rngl_sin θ).
Proof.
intros * Hic Hon Hop Hed Hmi * Hρ Hθ.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  destruct z as (rz, iz).
  f_equal; rewrite H1; apply H1.
}
move Hc1 after Hc2.
destruct (gc_eq_dec Hed z gc_zero) as [Hz| Hz]. {
  destruct z as (zr, zi).
  progress unfold gc_zero in Hz.
  injection Hz; clear Hz; intros; subst zr zi.
  cbn in Hρ.
  progress unfold rngl_squ in Hρ.
  rewrite (rngl_mul_0_l Hos) in Hρ.
  rewrite rngl_add_0_l in Hρ.
  rewrite (rl_sqrt_0 Hop Hic Hor Hid) in Hρ.
  rewrite Hρ.
  now do 2 rewrite (rngl_mul_0_l Hos).
}
subst θ.
destruct z as (zr, zi).
cbn in Hρ |-*.
assert (Hρz : ρ ≠ 0%L). {
  rewrite Hρ.
  intros H.
  apply (eq_rl_sqrt_0 Hos) in H. 2: {
    apply (rngl_add_nonneg_nonneg Hor);
    apply (rngl_squ_nonneg Hop Hor).
  }
  apply (rl_integral_modulus_prop Hmi) in H.
  now destruct H; subst zr zi.
}
assert (Hzρ : (0 < ρ)%L). {
  apply not_eq_sym in Hρz.
  apply (rngl_lt_iff Hor).
  split; [ | easy ].
  rewrite Hρ.
  apply rl_sqrt_nonneg.
  apply (rngl_add_nonneg_nonneg Hor);
  apply (rngl_squ_nonneg Hop Hor).
}
assert (Hzr : zr = (ρ * (zr / ρ))%L). {
  rewrite (rngl_mul_comm Hic).
  now symmetry; apply (rngl_div_mul Hon Hiv).
}
assert (Hr : zr = (ρ * rngl_cos (rl_acos Hor (zr / ρ)))%L). {
  rewrite rl_cos_acos; [ easy | ].
  rewrite <- (rngl_squ_1 Hon).
  apply (rngl_abs_le_squ_le Hop Hor).
  rewrite (rngl_abs_1 Hon Hop Hor).
  rewrite (rngl_abs_div Hon Hop Hiv Hed Hor); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor ρ). 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_le_div_l Hon Hop Hiv Hor); [ easy | ].
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
    rewrite Hρ.
    apply rl_sqrt_nonneg.
    apply (rngl_add_nonneg_nonneg Hor);
    apply (rngl_squ_nonneg Hop Hor).
  }
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  rewrite Hρ.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_add_nonneg_nonneg Hor);
    apply (rngl_squ_nonneg Hop Hor).
  }
  apply (rngl_le_add_r Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
f_equal; [ now destruct (0 ≤? zi)%L | ].
assert (Hri : ((zr / ρ)² + (zi / ρ)² = 1)%L). {
  rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
  rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
  progress unfold rngl_div.
  rewrite Hiv.
  rewrite <- rngl_mul_add_distr_r.
  rewrite (rngl_mul_inv_r Hiv).
  rewrite Hρ.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_add_nonneg_nonneg Hor);
    apply (rngl_squ_nonneg Hop Hor).
  }
  apply (rngl_div_diag Hon Hiq).
  intros H.
  apply (rl_integral_modulus_prop Hmi) in H.
  now move H at top; destruct H; subst zr zi.
}
assert (Hzρ21 : ((zr / ρ)² ≤ 1)%L). {
  rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    now apply (rngl_mul_pos_pos Hop Hor Hii).
  }
  rewrite (rngl_mul_1_l Hon).
  rewrite Hρ.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_add_nonneg_nonneg Hor);
    apply (rngl_squ_nonneg Hop Hor).
  }
  apply (rngl_le_add_r Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
remember (0 ≤? zi)%L as zzi eqn:Hzzi; symmetry in Hzzi.
destruct zzi. {
  progress unfold rl_acos.
  destruct (rngl_le_dec Hor (zr / ρ)² 1)%L as [Hzρ1| Hzρ1]; [ | easy ].
  apply rngl_leb_le in Hzzi.
  cbn.
  apply (rngl_add_sub_eq_l Hos) in Hri.
  rewrite Hri.
  rewrite (rl_sqrt_squ Hop Hor).
  rewrite (rngl_abs_div Hon Hop Hiv Hed Hor); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor ρ). 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_div_mul Hon Hiv); [ | easy ].
  symmetry.
  now apply (rngl_abs_nonneg_eq Hop Hor).
} {
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  apply (rngl_opp_inj Hop).
  rewrite (rngl_opp_involutive Hop).
  apply (rngl_leb_gt Hor) in Hzzi.
  apply (rngl_lt_le_incl Hor) in Hzzi.
  progress unfold rl_acos.
  destruct (rngl_le_dec Hor (zr / ρ)² 1)%L as [Hzρ1| Hzρ1]; [ | easy ].
  cbn.
  apply (rngl_add_sub_eq_l Hos) in Hri.
  rewrite Hri.
  rewrite (rl_sqrt_squ Hop Hor).
  rewrite (rngl_abs_div Hon Hop Hiv Hed Hor); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor ρ). 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_div_mul Hon Hiv); [ | easy ].
  symmetry.
  now apply (rngl_abs_nonpos_eq Hop Hor).
}
Qed.

Definition seq_converging_to_rat (rad a b n : nat) :=
  (rngl_of_nat (a * rad ^ n / b) / rngl_of_nat rad ^ n)%L.

Theorem gc_cos_add_sin_add_is_mul :
  ∀ a b,
  (rngl_cos (a + b) + ℹ * rngl_sin (a + b))%C =
  ((rngl_cos a + ℹ * rngl_sin a) * (rngl_cos b + ℹ * rngl_sin b))%C.
Proof. easy. Qed.

Theorem gc_cos_sin_pow :
  ∀ a n,
  ((rngl_cos a + ℹ * rngl_sin a) ^ n)%C =
  (rngl_cos (n * a) + ℹ * rngl_sin (n * a))%C.
Proof.
intros.
induction n; [ easy | cbn ].
now rewrite IHn.
Qed.

Theorem rngl_rat_frac_part_lt_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b,
  rngl_of_nat b ≠ 0%L
  → (rngl_of_nat a / rngl_of_nat b - rngl_of_nat (a / b) < 1)%L.
Proof.
intros Hon Hop * Hrbz.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 (rngl_of_nat b)) in Hrbz.
}
assert (Hbz : b ≠ 0) by now intros H; subst b.
assert (Hzb : (0 < rngl_of_nat b)%L). {
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  apply Nat.neq_0_lt_0.
  now intros H; subst b.
}
specialize (Nat.div_mod a b Hbz) as H1.
rewrite H1.
rewrite rngl_of_nat_add.
rewrite Nat.mul_comm.
rewrite Nat.div_add_l; [ | easy ].
rewrite (Nat.div_small (a mod b)). 2: {
  now apply Nat.mod_upper_bound.
}
rewrite Nat.add_0_r.
(* a lemma, perhaps, like Nat.div_add_l ? *)
progress unfold rngl_div.
rewrite Hiv.
rewrite rngl_mul_add_distr_r.
do 2 rewrite (rngl_mul_inv_r Hiv).
rewrite (rngl_of_nat_mul Hon Hos).
rewrite (rngl_mul_div Hi1); [ | easy ].
rewrite rngl_add_comm, (rngl_add_sub Hos).
apply (rngl_lt_div_l Hon Hop Hiv Hor); [ easy | ].
rewrite (rngl_mul_1_l Hon).
apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
now apply Nat.mod_upper_bound.
Qed.

(* e.g. 1/5 = 1/8 + 1/16 + 1/128 + 1/256 + ...
   corresponding to 1/5 written in binary, which is
     [0; 0; 1; 1; 0; 0; 1; 1; 0; 0]
*)
Theorem rat_is_inf_sum_of_inv_rad_pow :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_archimedean T = true →
  ∀ rad a b,
  2 ≤ rad
  → rngl_of_nat b ≠ 0%L
  → rngl_is_limit_when_tending_to_inf (seq_converging_to_rat rad a b)
       (rngl_of_nat a / rngl_of_nat b)%L.
Proof.
intros Hic Hon Hop Har * H2r Hbz.
intros ε Hε.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (int_part Hon Hop Hc1 Hor Har) as H1.
destruct (H1 (1 / ε)%L) as (N, HN).
clear H1.
rewrite (rngl_abs_nonneg_eq Hop Hor) in HN. 2: {
  apply (rngl_div_pos Hon Hop Hiv Hor); [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
}
assert (Hnε : (1 / rngl_of_nat (N + 1) < ε)%L). {
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    rewrite <- rngl_of_nat_0.
    apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
    now rewrite Nat.add_comm.
  }
  rewrite <- (rngl_mul_comm Hic).
  now apply (rngl_lt_div_l Hon Hop Hiv Hor).
}
assert (Hzr : (0 < rngl_of_nat rad)%L). {
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  apply Nat.neq_0_lt_0.
  now intros H; subst rad.
}
assert (Hzb : (0 < rngl_of_nat b)%L). {
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  apply Nat.neq_0_lt_0.
  now intros H; subst b.
}
assert (Hzr' : rad ≠ 0) by now intros H; subst rad.
assert (Hzb' : b ≠ 0) by now intros H; subst b.
enough (H : ∃ M, ∀ m, M ≤ m → N + 1 ≤ rad ^ m). {
  destruct H as (M, HM).
  exists M.
  intros m Hm.
  eapply (rngl_le_lt_trans Hor); [ | apply Hnε ].
  clear ε Hε HN Hnε.
  progress unfold seq_converging_to_rat.
  progress unfold rngl_dist.
  rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
    apply (rngl_le_sub_0 Hop Hor).
    clear Hm.
    apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
    progress unfold rngl_div.
    rewrite Hiv.
    rewrite (rngl_mul_mul_swap Hic).
    rewrite <- (rngl_of_nat_pow Hon Hos).
    rewrite (rngl_mul_inv_r Hiv).
    apply (rngl_le_div_l Hon Hop Hiv Hor). {
      rewrite <- rngl_of_nat_0.
      apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
      apply Nat.neq_0_lt_0.
      now apply Nat.pow_nonzero.
    }
    do 2 rewrite <- (rngl_of_nat_mul Hon Hos).
    apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
    rewrite Nat.mul_comm.
    eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
    now rewrite Nat.mul_comm, Nat.div_mul.
  }
  rewrite (rngl_opp_sub_distr Hop).
  rewrite <- (rngl_of_nat_pow Hon Hos).
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with
    (c := rngl_of_nat (rad ^ m)). {
    rewrite <- rngl_of_nat_0.
    apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite <- (rngl_of_nat_mul Hon Hos).
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite <- (rngl_of_nat_mul Hon Hos).
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_of_nat_mul Hon Hos (a * rad ^ m / b)).
  rewrite (rngl_mul_div Hi1). 2: {
    rewrite (rngl_of_nat_pow Hon Hos).
    apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
    intros H.
    rewrite H in Hzr.
    now apply (rngl_lt_irrefl Hor) in Hzr.
  }
  remember (a * rad ^ m) as c.
  apply (rngl_le_trans Hor _ 1%L). 2: {
    apply (rngl_le_div_r Hon Hop Hiv Hor). {
      rewrite <- rngl_of_nat_0.
      apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
      now rewrite Nat.add_comm.
    }
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
    now apply HM.
  }
  clear a Heqc.
  rename c into a.
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_rat_frac_part_lt_1 Hon Hop).
}
enough (H : ∃ M : nat, ∀ m : nat, M ≤ m → N + 1 ≤ 2 ^ m). {
  destruct H as (M, HM).
  exists M.
  intros m Hm.
  apply (Nat.le_trans _ (2 ^ m)); [ now apply HM | ].
  now apply Nat.pow_le_mono_l.
}
exists (Nat.log2_up (N + 2)).
intros m Hm.
apply (Nat.pow_le_mono_r 2) in Hm; [ | easy ].
eapply Nat.le_trans; [ | apply Hm ].
eapply Nat.le_trans. 2: {
  apply Nat.log2_up_spec.
  rewrite Nat.add_comm; cbn.
  now apply -> Nat.succ_lt_mono.
}
apply Nat.add_le_mono_l.
now apply -> Nat.succ_le_mono.
Qed.

Theorem rat_is_inf_sum_of_inv_rad_pow' :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_archimedean T = true →
  ∀ rad a i c,
  2 ≤ rad
  → rngl_of_nat i ≠ 0%L
  → rngl_is_limit_when_tending_to_inf (seq_converging_to_rat rad a i) c
  → rngl_of_nat a = (rngl_of_nat i * c)%L.
Proof.
intros Hic Hon Hop Har * H2r Hbz Hlim.
destruct ac as (Hiv, Hc2, Hor).
specialize (rat_is_inf_sum_of_inv_rad_pow Hic Hon Hop Har _ a i H2r) as H1.
specialize (H1 Hbz).
progress unfold rngl_is_limit_when_tending_to_inf in Hlim.
progress unfold rngl_is_limit_when_tending_to_inf in H1.
specialize (limit_unique Hon Hop Hiv Hor _ rngl_dist) as H2.
specialize (H2 (rngl_dist_is_dist Hop Hor)).
specialize (H2 _ _ _ Hlim H1).
subst c.
rewrite (rngl_mul_comm Hic).
symmetry.
now apply (rngl_div_mul Hon Hiv).
Qed.

(*
End a.

Require Import Rational.
Import Q.Notations.
Require Import Qrl.

Compute (
  let ro := Q_ring_like_op in
  let rp := Q_ring_like_prop in
...
*)

(*
Fixpoint angle_div_2_pow_nat θ i :=
  match i with
  | 0 => θ
  | S i' => angle_div_2_pow_nat (angle_div_2 θ) i'
  end.
*)

(* θ / 2^i * (2^i / n) *)
Definition seq_angle_converging_to_angle_div_nat θ (n i : nat) :=
  ((2 ^ i / n) * angle_div_2_pow_nat θ i)%A.

Arguments seq_angle_converging_to_angle_div_nat θ%A (n i)%nat.
Arguments rl_sqrt_0 {T ro rp rl} Hor Hop Hic Hii.

Theorem angle_mul_nat_assoc :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b θ, (a * (b * θ) = (a * b) * θ)%A.
Proof.
intros Hon Hop *.
induction a; [ easy | cbn ].
rewrite IHa.
symmetry.
apply (angle_mul_add_distr_r Hon Hop).
Qed.

Definition is_angle_eucl_limit_when_tending_to_inf :=
  is_limit_when_tending_to_inf angle_eucl_dist.

Theorem angle_eqb_eq :
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 : angle T, (θ1 =? θ2)%A = true ↔ θ1 = θ2.
Proof.
intros Hed *.
split; intros H12. {
  progress unfold angle_eqb in H12.
  apply Bool.andb_true_iff in H12.
  destruct H12 as (Hc12, Hs12).
  apply (rngl_eqb_eq Hed) in Hc12, Hs12.
  apply eq_angle_eq.
  now rewrite Hc12, Hs12.
} {
  subst θ2.
  progress unfold angle_eqb.
  now do 2 rewrite (rngl_eqb_refl Hed).
}
Qed.

Theorem angle_leb_refl :
  ∀ θ, (θ ≤? θ)%A = true.
Proof.
intros.
destruct ac as (Hiv, Hc2, Hor).
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; apply (rngl_leb_refl Hor).
Qed.

(*
Theorem angle_eqb_refl :
  rngl_has_eq_dec T = true →
  ∀ θ, (θ =? θ)%A = true.
Proof.
intros Hed *.
progress unfold angle_eqb.
now do 2 rewrite (rngl_eqb_refl Hed).
Qed.

Theorem angle_eqb_neq :
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 =? θ2)%A = false ↔ θ1 ≠ θ2.
Proof.
intros Hed *.
progress unfold angle_eqb.
split; intros H12. {
  intros H; subst θ2.
  now do 2 rewrite (rngl_eqb_refl Hed) in H12.
} {
  apply Bool.not_true_iff_false.
  intros H; apply H12; clear H12.
  apply eq_angle_eq; cbn.
  apply Bool.andb_true_iff in H.
  destruct H as (Hc, Hs).
  apply (rngl_eqb_eq Hed) in Hc, Hs.
  now rewrite Hc, Hs.
}
Qed.

Theorem le_1_rngl_cos :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (1 ≤ rngl_cos θ)%L → θ = 0%A.
Proof.
intros Hic Hon Hop Hed * Hθ.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_cos_bound Hon Hop Hiv Hic Hed Hor θ) as H1.
apply (rngl_le_antisymm Hor) in Hθ; [ | easy ].
specialize (cos2_sin2_1 Hon Hop Hic Hed θ) as H2.
rewrite Hθ in H2.
rewrite (rngl_squ_1 Hon) in H2.
apply (rngl_add_sub_eq_l Hos) in H2.
rewrite (rngl_sub_diag Hos) in H2.
symmetry in H2.
apply (eq_rngl_squ_0 Hos Hid) in H2.
apply eq_angle_eq.
now rewrite Hθ, H2.
Qed.

Theorem angle_leb_nle :
  ∀ θ1 θ2, (θ1 ≤? θ2)%A = false ↔ ¬ (θ1 ≤ θ2)%A.
Proof.
intros.
now split; intros; apply Bool.not_true_iff_false.
Qed.

Theorem angle_leb_le :
  ∀ θ1 θ2, (θ1 ≤? θ2)%A = true ↔ (θ1 ≤ θ2)%A.
Proof. easy. Qed.

Theorem angle_opp_le_compat :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, θ1 ≠ 0%A → θ2 ≠ 0%A → (θ1 ≤ θ2)%A ↔ (- θ2 ≤ - θ1)%A.
Proof.
intros Hic Hon Hop Hed * H1z H2z.
destruct ac as (Hiv, Hc2, Hor).
assert (H : ∀ θ1 θ2, θ1 ≠ 0%A → θ2 ≠ 0%A → (θ1 ≤ θ2)%A → (- θ2 ≤ - θ1)%A). {
  clear θ1 θ2 H1z H2z.
  intros θ1 θ2 H1z H2z H12.
  progress unfold angle_leb in H12 |-*.
  progress unfold angle_opp.
  cbn.
  remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
  remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
  remember (0 ≤? - rngl_sin θ1)%L as zo1 eqn:Hzo1.
  remember (0 ≤? - rngl_sin θ2)%L as zo2 eqn:Hzo2.
  symmetry in Hz1, Hz2, Hzo1, Hzo2.
  destruct z1. {
    apply rngl_leb_le in Hz1.
    destruct z2. {
      apply rngl_leb_le in Hz2.
      destruct zo1; [ | now destruct zo2 ].
      apply rngl_leb_le in Hzo1.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzo1.
      apply (rngl_le_antisymm Hor) in Hz1; [ | easy ].
      clear Hzo1.
      apply (eq_rngl_sin_0 Hic Hon Hop Hed) in Hz1.
      destruct Hz1 as [Hz1| Hz1]; [ easy | ].
      subst θ1; cbn in H12 |-*.
      clear H1z.
      apply rngl_leb_le in H12.
      specialize (rngl_cos_bound Hon Hop Hiv Hic Hed Hor θ2) as H1.
      apply (rngl_le_antisymm Hor) in H12; [ | easy ].
      symmetry in H12.
      apply (eq_rngl_cos_opp_1 Hic Hon Hop Hed) in H12.
      apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H12.
      destruct H12 as [H12| H12]; [ easy | ].
      subst θ2; cbn in Hzo2 |-*.
      clear H2z H1 Hz2.
      rewrite (rngl_opp_0 Hop) in Hzo2.
      rewrite (rngl_leb_refl Hor) in Hzo2; subst zo2.
      apply (rngl_leb_refl Hor).
    }
    clear H12.
    apply (rngl_leb_gt Hor) in Hz2.
    destruct zo1. {
      apply rngl_leb_le in Hzo1.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzo1.
      apply (rngl_le_antisymm Hor) in Hzo1; [ | easy ].
      symmetry in Hzo1.
      apply (eq_rngl_sin_0 Hic Hon Hop Hed) in Hzo1.
      destruct Hzo1 as [Hzo1| Hzo1]; [ easy | ].
      subst θ1; cbn.
      destruct zo2. {
        apply rngl_leb_le.
        apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
      }
      apply rngl_leb_nle in Hzo2.
      exfalso; apply Hzo2.
      apply (rngl_opp_nonneg_nonpos Hop Hor).
      now apply (rngl_lt_le_incl Hor).
    }
    destruct zo2; [ easy | ].
    apply rngl_leb_nle in Hzo2.
    exfalso; apply Hzo2.
    apply (rngl_opp_nonneg_nonpos Hop Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  destruct z2; [ easy | ].
  destruct zo2; [ now destruct zo1 | ].
  apply (rngl_leb_gt Hor) in Hz2.
  apply rngl_leb_nle in Hzo2.
  exfalso; apply Hzo2.
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
split; intros H12; [ now apply H | ].
apply H in H12. {
  now do 2 rewrite (angle_opp_involutive Hop) in H12.
} {
  intros H1.
  apply (f_equal angle_opp) in H1.
  rewrite (angle_opp_involutive Hop) in H1.
  now rewrite (angle_opp_0 Hop) in H1.
} {
  intros H1.
  apply (f_equal angle_opp) in H1.
  rewrite (angle_opp_involutive Hop) in H1.
  now rewrite (angle_opp_0 Hop) in H1.
}
Qed.
*)

Arguments angle_ltb {T ro rp} (θ1 θ2)%A.

(*
Theorem angle_div_2_0 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  angle_div_2 0 = 0%A.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
move Hi1 before Hos.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  apply eq_angle_eq; cbn.
  rewrite (rngl_leb_refl Hor).
  now rewrite (H1 (_ * _))%L, (H1 √_)%L, (H1 1)%L.
}
specialize (rngl_2_neq_0 Hon Hop Hc1 Hor) as H20.
apply eq_angle_eq; cbn.
rewrite (rngl_leb_refl Hor).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_div_diag Hon Hiq); [ | easy ].
rewrite (rl_sqrt_1 Hic Hon Hop Hor Hid).
f_equal.
rewrite (rngl_sub_diag Hos).
rewrite (rngl_div_0_l Hos Hi1); [ | easy ].
apply (rl_sqrt_0 Hop Hic Hor Hid).
Qed.

Theorem angle_add_sub_eq_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ a b c, (a + b)%A = c → (c - b)%A = a.
Proof.
intros Hic Hon Hop Hed * Hab.
rewrite (angle_add_comm Hic) in Hab.
now apply angle_add_sub_eq_l.
Qed.

Theorem rngl_sin_nonneg_cos_le_angle_le :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_cos θ2 ≤ rngl_cos θ1)%L
  → (θ1 ≤ θ2)%A.
Proof.
intros * Hzs2 Hc12.
progress unfold angle_leb.
apply (rngl_leb_le) in Hzs2, Hc12.
rewrite Hzs2.
now destruct (0 ≤? rngl_sin θ2)%L.
Qed.

Theorem angle_nle_gt :
  ∀ θ1 θ2, ¬ (θ1 ≤ θ2)%A ↔ (θ2 < θ1)%A.
Proof.
intros.
destruct ac as (Hiv, Hc2, Hor).
progress unfold angle_leb.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
symmetry in Hz1, Hz2.
destruct z1. {
  destruct z2; [ | easy ].
  split; intros H12. {
    apply Bool.not_true_iff_false in H12.
    apply (rngl_leb_gt Hor) in H12.
    now apply rngl_ltb_lt.
  } {
    apply Bool.not_true_iff_false.
    apply (rngl_leb_gt Hor).
    now apply rngl_ltb_lt.
  }
} {
  destruct z2; [ easy | ].
  split; intros H12. {
    apply Bool.not_true_iff_false in H12.
    apply (rngl_leb_gt Hor) in H12.
    now apply rngl_ltb_lt.
  } {
    apply Bool.not_true_iff_false.
    apply (rngl_leb_gt Hor).
    now apply rngl_ltb_lt.
  }
}
Qed.
*)

Theorem rngl_cos_le_anticompat_when_sin_nonneg :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L ↔ (θ2 ≤ θ1)%A.
Proof.
intros * Hs1 Hs2.
progress unfold angle_leb.
apply rngl_leb_le in Hs1, Hs2.
rewrite Hs1, Hs2.
apply iff_sym.
apply rngl_leb_le.
Qed.

Theorem angle_div_2_le_compat :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (θ1 ≤ θ2 → angle_div_2 θ1 ≤ angle_div_2 θ2)%A.
Proof.
intros Hon Hop Hic Hed * H12.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  progress unfold angle_leb.
  rewrite (H1 (rngl_sin _)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin _)).
  rewrite (rngl_leb_refl Hor).
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_leb_refl Hor).
}
progress unfold angle_leb in H12.
progress unfold angle_leb.
cbn.
assert (Hzac : ∀ θ, (0 ≤ (1 + rngl_cos θ) / 2)%L). {
  intros.
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with (c := 2%L). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_div_mul Hon Hiv). 2: {
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  }
  apply (rngl_le_sub_le_add_l Hop Hor).
  rewrite (rngl_sub_0_l Hop).
  now apply rngl_cos_bound.
}
assert (Hzsc : ∀ θ, (0 ≤ (1 - rngl_cos θ) / 2)%L). {
  intros.
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with (c := 2%L). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_div_mul Hon Hiv). 2: {
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  }
  apply (rngl_le_0_sub Hop Hor).
  now apply rngl_cos_bound.
}
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
    rewrite rngl_squ_sqrt; [ | easy ].
    rewrite rngl_squ_sqrt; [ | easy ].
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
    now apply (rl_sqrt_nonneg).
  } {
    now apply (rl_sqrt_nonneg).
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
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
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

Theorem angle_div_2_pow_nat_add :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ n θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → angle_div_2_pow_nat (θ1 + θ2) n =
    (angle_div_2_pow_nat θ1 n + angle_div_2_pow_nat θ2 n)%A.
Proof.
intros Hic Hon Hop Hed * Haov.
revert θ1 θ2 Haov.
induction n; intros; [ easy | cbn ].
rewrite (angle_div_2_add_not_overflow Hic Hon Hop Hed); [ | easy ].
apply IHn.
progress unfold angle_add_overflow.
progress unfold angle_add_overflow in Haov.
apply angle_ltb_ge.
rewrite <- (angle_div_2_add_not_overflow Hic Hon Hop Hed); [ | easy ].
apply angle_ltb_ge in Haov.
now apply (angle_div_2_le_compat).
Qed.

Theorem angle_div_2_pow_nat_mul :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ n m θ,
  m ≠ 0
  → angle_mul_nat_overflow m θ = false
  → angle_div_2_pow_nat (m * θ) n =
      (m * angle_div_2_pow_nat θ n)%A.
Proof.
intros Hic Hon Hop Hed * Hmz Haov.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
induction m; [ easy | clear Hmz; cbn ].
cbn in Haov.
destruct m. {
  cbn.
  rewrite (angle_add_0_r Hon Hos).
  symmetry; apply (angle_add_0_r Hon Hos).
}
specialize (IHm (Nat.neq_succ_0 _)).
apply Bool.orb_false_iff in Haov.
rewrite (angle_div_2_pow_nat_add Hic Hon Hop Hed); [ | easy ].
f_equal.
now apply IHm.
Qed.

Theorem angle_eucl_dist_sub_l_diag :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ Δθ, angle_eucl_dist (θ - Δθ) θ = angle_eucl_dist Δθ 0.
Proof.
intros Hic Hon Hop Hed *.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold angle_eucl_dist.
remember (θ - Δθ)%A as x; cbn; subst x.
do 4 rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_squ_0 Hos).
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_add_add_swap).
rewrite <- (rngl_add_sub_swap Hop (rngl_cos θ)²)%L.
rewrite (cos2_sin2_1 Hon Hop Hic Hed).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_add_assoc.
rewrite (cos2_sin2_1 Hon Hop Hic Hed).
rewrite <- (rngl_add_sub_swap Hop 1)%L.
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_sub_add_distr Hos).
remember (θ - Δθ)%A as x.
replace (_ * _ + _ * _)%L with (rngl_cos (θ - x))%A. 2: {
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  now rewrite rngl_sub_opp_r.
}
subst x.
rewrite (angle_sub_sub_distr Hic Hop).
rewrite (angle_sub_diag Hic Hon Hop Hed).
rewrite (angle_add_0_l Hon Hos).
rewrite <- rngl_add_assoc.
rewrite (cos2_sin2_1 Hon Hop Hic Hed).
rewrite <- (rngl_add_sub_swap Hop).
now rewrite (rngl_sub_mul_r_diag_l Hon Hop).
Qed.

Theorem one_sub_squ_cos_add_squ_sin :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, ((1 - rngl_cos θ)² + (rngl_sin θ)² = 2 * (1 - rngl_cos θ))%L.
Proof.
intros Hic Hon Hop Hed *.
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite <- rngl_add_assoc.
rewrite (cos2_sin2_1 Hon Hop Hic Hed).
rewrite <- (rngl_add_sub_swap Hop).
apply (rngl_sub_mul_r_diag_l Hon Hop).
Qed.

Theorem rngl_cos_decr :
  ∀ θ1 θ2, (θ1 ≤ θ2 ≤ angle_straight)%A → (rngl_cos θ2 ≤ rngl_cos θ1)%L.
Proof.
intros * (H12, H2s).
destruct ac as (Hiv, Hc2, Hor).
progress unfold angle_leb in H12, H2s.
cbn in H2s.
rewrite (rngl_leb_refl Hor) in H2s.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs2.
destruct zs2; [ | easy ].
destruct (0 ≤? rngl_sin θ1)%L; [ | easy ].
now apply rngl_leb_le in H12.
Qed.

Theorem rngl_sin_incr :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (θ1 ≤ θ2 ≤ angle_right)%A
  → (rngl_sin θ1 ≤ rngl_sin θ2)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * (H12, H2s).
progress unfold angle_leb in H12, H2s.
cbn in H2s.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1 in H2s; clear H1.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs2; [ | easy ].
destruct zs1; [ | easy ].
apply rngl_leb_le in Hzs1, Hzs2, H12, H2s.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
Qed.

Theorem rngl_sin_incr_lt :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (θ1 < θ2 ≤ angle_right)%A
  → (rngl_sin θ1 < rngl_sin θ2)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * (H12, H2s).
progress unfold angle_ltb in H12.
progress unfold angle_leb in H2s.
cbn in H2s.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1 in H2s; clear H1.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs2; [ | easy ].
destruct zs1; [ | easy ].
apply rngl_leb_le in Hzs1, Hzs2, H2s.
apply rngl_ltb_lt in H12.
apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy.
apply (rngl_le_trans Hor _ (rngl_cos θ2)); [ easy | ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (0 ≤ θ)%A.
Proof.
intros Hic Hon Hop Hed *.
destruct ac as (Hiv, Hc2, Hor).
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
destruct (0 ≤? rngl_sin θ)%L; [ | easy ].
apply rngl_leb_le.
apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
Qed.

Theorem rngl_cos_add_rngl_cos :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ p q,
  (rngl_cos p + rngl_cos q =
   2 *
   rngl_cos (angle_div_2 p + angle_div_2 q) *
   rngl_cos (angle_div_2 p - angle_div_2 q))%L.
Proof.
intros Hic Hon Hop Hed *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite <- (angle_div_2_mul_2 Hic Hon Hop Hed p) at 1.
rewrite <- (angle_div_2_mul_2 Hic Hon Hop Hed q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite (rngl_mul_1_r Hon).
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_l.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic (_ - _))%L.
rewrite <- (rngl_squ_sub_squ Hop Hic).
do 4 rewrite fold_rngl_squ.
do 2 rewrite (rngl_squ_mul Hic).
specialize (cos2_sin2_1 Hon Hop Hic Hed p2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
specialize (cos2_sin2_1 Hon Hop Hic Hed q2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite (rngl_sub_sub_distr Hop _²)%L.
rewrite <- (rngl_add_sub_swap Hop _²)%L.
rewrite (rngl_add_diag Hon).
rewrite <- (rngl_add_sub_swap Hop (_ * _²))%L.
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_sub_add_distr Hos).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_add_assoc.
rewrite (rngl_add_diag Hon _²)%L.
rewrite <- rngl_mul_add_distr_l.
rewrite (rngl_sub_mul_l_diag_l Hon Hop).
f_equal.
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_add_sub_swap Hop _ _ (_ * _))%L.
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
rewrite (rngl_sub_sub_distr Hop).
rewrite rngl_add_comm.
apply (rngl_add_sub_swap Hop).
Qed.

Theorem rngl_cos_sub_rngl_cos :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ p q,
  (rngl_cos p - rngl_cos q =
   - 2%L *
   rngl_sin (angle_div_2 p + angle_div_2 q) *
   rngl_sin (angle_div_2 p - angle_div_2 q))%L.
Proof.
intros Hic Hon Hop Hed *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite <- (angle_div_2_mul_2 Hic Hon Hop Hed p) at 1.
rewrite <- (angle_div_2_mul_2 Hic Hon Hop Hed q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite (rngl_mul_1_r Hon).
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_l.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_comm (_ * _)%L).
rewrite (rngl_sub_sub_distr Hop).
rewrite <- rngl_mul_assoc.
rewrite (rngl_add_opp_l Hop).
rewrite <- (rngl_squ_sub_squ Hop Hic).
do 4 rewrite fold_rngl_squ.
do 2 rewrite (rngl_squ_mul Hic).
specialize (cos2_sin2_1 Hon Hop Hic Hed p2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
specialize (cos2_sin2_1 Hon Hop Hic Hed q2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite (rngl_sub_sub_distr Hop _²)%L.
rewrite <- (rngl_add_sub_swap Hop _²)%L.
rewrite (rngl_add_diag Hon).
rewrite (rngl_sub_sub_swap Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_sub_add Hop).
rewrite <- (rngl_sub_add_distr Hos).
rewrite (rngl_add_diag Hon _²)%L.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite <- (rngl_mul_opp_r Hop).
f_equal.
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_add Hop).
now rewrite (rngl_opp_sub_distr Hop).
Qed.

Theorem rngl_sin_add_rngl_sin :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ p q,
  (rngl_sin p + rngl_sin q =
   2 *
   rngl_sin (angle_div_2 p + angle_div_2 q) *
   rngl_cos (angle_div_2 p - angle_div_2 q))%L.
Proof.
intros Hic Hon Hop Hed *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite <- (angle_div_2_mul_2 Hic Hon Hop Hed p) at 1.
rewrite <- (angle_div_2_mul_2 Hic Hon Hop Hed q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite (rngl_mul_1_r Hon).
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_l.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_add_distr_l.
do 2 rewrite (rngl_mul_add_distr_r (_ * _))%L.
do 2 rewrite rngl_add_assoc.
do 4 rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (rngl_cos p2)).
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic (rngl_sin p2)).
rewrite <- (rngl_mul_assoc (rngl_sin p2 * _))%L.
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic (rngl_cos p2)).
rewrite <- (rngl_mul_assoc (rngl_cos p2 * _))%L.
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic _ (rngl_cos q2)).
rewrite fold_rngl_squ.
rewrite (rngl_add_add_swap (_ * _ * _ + _))%L.
rewrite (rngl_add_add_swap (_ * _ * _))%L.
rewrite (rngl_mul_mul_swap Hic).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite (cos2_sin2_1 Hon Hop Hic Hed).
rewrite (rngl_mul_1_l Hon).
rewrite <- (rngl_add_assoc (rngl_cos q2 * _))%L.
rewrite (rngl_mul_comm Hic (rngl_sin p2)).
do 2 rewrite <- rngl_mul_add_distr_l.
rewrite (cos2_sin2_1 Hon Hop Hic Hed).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_comm Hic (rngl_sin q2)).
rewrite <- rngl_add_assoc.
rewrite (rngl_add_diag Hon).
rewrite (rngl_add_diag Hon (rngl_cos q2 * _))%L.
rewrite rngl_mul_assoc.
rewrite (rngl_mul_comm Hic _ 2)%L.
rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_l.
f_equal.
apply rngl_add_comm.
Qed.

Theorem rngl_sin_sub_rngl_sin :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ p q,
  (rngl_sin p - rngl_sin q =
   2%L *
   rngl_cos (angle_div_2 p + angle_div_2 q) *
   rngl_sin (angle_div_2 p - angle_div_2 q))%L.
Proof.
intros Hic Hon Hop Hed *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite <- (angle_div_2_mul_2 Hic Hon Hop Hed p) at 1.
rewrite <- (angle_div_2_mul_2 Hic Hon Hop Hed q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite (rngl_mul_1_r Hon).
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_l.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_comm (_ * _)%L).
rewrite (rngl_add_opp_l Hop).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_sub_distr_r Hop).
do 4 rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (rngl_cos p2)).
rewrite <- rngl_mul_assoc.
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic (rngl_sin p2)).
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic _ (rngl_cos q2)).
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic (rngl_sin p2)).
rewrite <- (rngl_mul_assoc (rngl_sin p2 * _))%L.
rewrite fold_rngl_squ.
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_mul_comm Hic (rngl_sin p2)).
rewrite <- rngl_mul_add_distr_l.
rewrite <- rngl_mul_add_distr_l.
rewrite (cos2_sin2_1 Hon Hop Hic Hed).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_mul_swap Hic _ (rngl_sin q2)).
rewrite <- (rngl_sub_add_distr Hos).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_add_comm _²)%L.
rewrite (cos2_sin2_1 Hon Hop Hic Hed).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_comm Hic (rngl_sin q2)).
rewrite <- rngl_mul_add_distr_l.
rewrite (rngl_add_diag Hon).
rewrite (rngl_add_diag Hon (rngl_sin q2)).
do 2 rewrite rngl_mul_assoc.
do 2 rewrite (rngl_mul_comm Hic _ 2)%L.
do 2 rewrite <- rngl_mul_assoc.
now rewrite <- (rngl_mul_sub_distr_l Hop).
Qed.

Theorem angle_eucl_dist_cos_sin :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ θ, ((angle_eucl_dist θ 0)² = (1 - rngl_cos θ)² + (rngl_sin θ)²)%L.
Proof.
intros Hop Hor *.
progress unfold angle_eucl_dist; cbn.
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_squ_opp Hop).
apply rngl_squ_sqrt.
apply (rngl_add_nonneg_nonneg Hor);
apply (rngl_squ_nonneg Hop Hor).
Qed.

Theorem angle_eucl_dist_sin_cos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ θ,
  ((angle_eucl_dist θ angle_right)² =
     (1 - rngl_sin θ)² + (rngl_cos θ)²)%L.
Proof.
intros Hop Hor *.
progress unfold angle_eucl_dist; cbn.
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_squ_opp Hop).
rewrite rngl_add_comm.
apply rngl_squ_sqrt.
apply (rngl_add_nonneg_nonneg Hor);
apply (rngl_squ_nonneg Hop Hor).
Qed.

Theorem rngl_cos_angle_eucl_dist :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (rngl_cos θ = 1 - (angle_eucl_dist θ 0)² / 2)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1; apply H1.
}
intros.
specialize (angle_eucl_dist_cos_sin Hop Hor θ) as H1.
rewrite (rngl_squ_sub Hop Hic Hon) in H1.
rewrite (rngl_squ_1 Hon) in H1.
rewrite (rngl_mul_1_r Hon) in H1.
rewrite <- rngl_add_assoc in H1.
rewrite (cos2_sin2_1 Hon Hop Hic Hed) in H1.
rewrite <- (rngl_add_sub_swap Hop) in H1.
rewrite (rngl_sub_mul_r_diag_l Hon Hop) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
now apply (rngl_sub_move_l Hop) in H1.
Qed.

Theorem rngl_sin_angle_eucl_dist :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (rngl_sin θ = 1 - (angle_eucl_dist θ angle_right)² / 2)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1; apply H1.
}
intros.
specialize (angle_eucl_dist_sin_cos Hop Hor θ) as H1.
rewrite (rngl_squ_sub Hop Hic Hon) in H1.
rewrite (rngl_squ_1 Hon) in H1.
rewrite (rngl_mul_1_r Hon) in H1.
rewrite rngl_add_add_swap in H1.
rewrite <- rngl_add_assoc in H1.
rewrite (cos2_sin2_1 Hon Hop Hic Hed) in H1.
rewrite <- (rngl_add_sub_swap Hop) in H1.
rewrite (rngl_sub_mul_r_diag_l Hon Hop) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
now apply (rngl_sub_move_l Hop) in H1.
Qed.

Theorem rngl_cos_le_iff_angle_eucl_le :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ θ',
  (rngl_cos θ ≤ rngl_cos θ' ↔ angle_eucl_dist θ' 0 ≤ angle_eucl_dist θ 0)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  split; intros. {
    rewrite H1, (H1 (angle_eucl_dist _ _)).
    apply (rngl_le_refl Hor).
  } {
    rewrite H1, (H1 (rngl_cos _)).
    apply (rngl_le_refl Hor).
  }
}
intros.
rewrite <- (rngl_abs_nonneg_eq Hop Hor (angle_eucl_dist _ _)). 2: {
  apply (dist_nonneg Hon Hop Hiv Hor).
  apply (angle_eucl_dist_is_dist Hic Hon Hop Hed).
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor (angle_eucl_dist θ _)). 2: {
  apply (dist_nonneg Hon Hop Hiv Hor).
  apply (angle_eucl_dist_is_dist Hic Hon Hop Hed).
}
do 2 rewrite (rngl_cos_angle_eucl_dist Hic Hon Hop Hed).
split; intros H1. {
  apply (rngl_sub_le_mono_l Hop Hor) in H1.
  apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii) in H1. 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now apply (rngl_squ_le_abs_le Hop Hor Hii) in H1.
} {
  apply (rngl_sub_le_mono_l Hop Hor).
  apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now apply (rngl_abs_le_squ_le Hop Hor).
}
Qed.

Theorem rngl_sin_le_iff_angle_eucl_le :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ θ',
  (rngl_sin θ ≤ rngl_sin θ' ↔
     angle_eucl_dist θ' angle_right ≤ angle_eucl_dist θ angle_right)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  split; intros. {
    rewrite H1, (H1 (angle_eucl_dist _ _)).
    apply (rngl_le_refl Hor).
  } {
    rewrite H1, (H1 (rngl_sin _)).
    apply (rngl_le_refl Hor).
  }
}
assert (Hz1ss : ∀ θ, (0 ≤ 1 - rngl_sin θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_sin_bound Hon Hop Hiv Hic Hed Hor).
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as Hz2.
intros.
progress unfold angle_eucl_dist.
cbn.
do 2 rewrite (rngl_sub_0_l Hop).
do 2 rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
do 2 rewrite (rngl_squ_opp Hop).
do 2 rewrite rngl_add_assoc.
do 2 rewrite (rngl_add_add_swap _ _ _²)%L.
do 2 rewrite (cos2_sin2_1 Hon Hop Hic Hed).
do 2 rewrite (rngl_add_sub_assoc Hop).
do 2 rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite rl_sqrt_mul; [ | | easy ]. 2: {
  now apply (rngl_lt_le_incl Hor).
}
rewrite rl_sqrt_mul; [ | | easy ]. 2: {
  now apply (rngl_lt_le_incl Hor).
}
split; intros Hθθ. {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
    apply rl_sqrt_nonneg.
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply rl_sqrt_nonneg.
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
    now apply rl_sqrt_nonneg.
  }
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  rewrite rngl_squ_sqrt; [ | easy ].
  rewrite rngl_squ_sqrt; [ | easy ].
  now apply (rngl_sub_le_mono_l Hop Hor).
} {
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii) in Hθθ. 2: {
    rewrite <- (rngl_abs_0 Hop).
    rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
      apply rl_sqrt_nonneg.
      now apply (rngl_lt_le_incl Hor).
    }
    apply (rngl_squ_lt_abs_lt Hop Hor Hii).
    rewrite (rngl_squ_0 Hos).
    rewrite rngl_squ_sqrt; [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor) in Hθθ. 2: {
    now apply rl_sqrt_nonneg.
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L in Hθθ. 2: {
    now apply rl_sqrt_nonneg.
  }
  apply (rngl_abs_le_squ_le Hop Hor) in Hθθ.
  rewrite rngl_squ_sqrt in Hθθ; [ | easy ].
  rewrite rngl_squ_sqrt in Hθθ; [ | easy ].
  now apply (rngl_sub_le_mono_l Hop Hor) in Hθθ.
}
Qed.

Theorem angle_mul_nat_overflow_succ_l_false :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ n,
  angle_mul_nat_overflow (S n) θ = false
  → angle_mul_nat_overflow n θ = false ∧
    angle_add_overflow θ (n * θ)%A = false.
Proof.
intros Hon Hos * Hn.
destruct n. {
  split; [ easy | cbn ].
  progress unfold angle_add_overflow.
  rewrite (angle_add_0_r Hon Hos).
  apply angle_ltb_ge.
  apply angle_leb_refl.
}
remember (S n) as sn; cbn in Hn; subst sn.
now apply Bool.orb_false_iff in Hn.
Qed.

Theorem angle_sub_move_0_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 - θ2)%A = 0%A ↔ θ1 = θ2.
Proof.
intros Hic Hon Hop Hed.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
split; intros H12. {
  apply (angle_sub_move_r Hic Hon Hop Hed) in H12.
  now rewrite (angle_add_0_l Hon Hos) in H12.
} {
  apply (angle_sub_move_r Hic Hon Hop Hed).
  now rewrite (angle_add_0_l Hon Hos).
}
Qed.

Theorem angle_add_overflow_straight_straight :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  angle_add_overflow angle_straight angle_straight = true.
Proof.
intros Hon Hop Hc1.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold angle_add_overflow.
rewrite (angle_straight_add_straight Hon Hop).
progress unfold angle_ltb; cbn.
rewrite (rngl_leb_refl Hor).
apply rngl_ltb_lt.
apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
Qed.

Theorem rngl_sin_add_nonneg :
  rngl_has_opp T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L.
Proof.
intros Hop.
destruct ac as (Hiv, Hc2, Hor).
intros * Hzs1 Hzs2 Hcs1 Hcs2.
cbn.
apply (rngl_add_nonneg_nonneg Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem rngl_sin_add_is_pos_1 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 < rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros  * Hs1z Hs2z Hc1z Hc2z.
cbn.
apply (rngl_add_pos_nonneg Hor).
now apply (rngl_mul_pos_pos Hop Hor Hii).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem rngl_sin_add_is_pos_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros  * Hs1z Hs2z Hc1z Hc2z.
cbn.
apply (rngl_add_nonneg_pos Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_mul_pos_pos Hop Hor Hii).
Qed.

Theorem rngl_sin_add_nonneg_sin_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin θ1)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Haov12 Hzs12.
apply (rngl_nlt_ge Hor).
intros Hs1z.
remember (θ1 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12, Hs1z.
apply (rngl_opp_neg_pos Hop Hor) in Hs1z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite <- (angle_add_sub_swap Hic Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
now rewrite H; clear H.
Qed.

Theorem rngl_cos_add_nonneg_cos_add_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin θ2 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos (θ1 + θ3))%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Hzs1 Hzs2 Hzs3 Hzc1 Hzc2 Hzc3 H23 Hzc13.
eapply (rngl_le_trans Hor); [ apply Hzc13 | cbn ].
apply (rngl_sub_le_compat Hop Hor). {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
  generalize H23; intros H32.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff in H32.
}
now apply (rngl_mul_le_mono_nonneg_l Hop Hor).
Qed.

(* pas très satisfait de cette preuve. Elle a marché, certes,
   mais me paraît bien compliquée. Il y aurait sûrement un
   moyen de la rendre plus simple, mais j'ai pas le temps
   de regarder. Tant pis, c'est prouvé, c'est déjà ça. Et
   puis ce théorème est important. *)
Theorem angle_add_overflow_false_comm :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ2 θ1 = false.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  progress unfold angle_leb.
  rewrite (H1 (rngl_sin _)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin _)).
  rewrite (rngl_leb_refl Hor).
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_leb_refl Hor).
}
intros * Haov.
progress unfold angle_add_overflow in Haov.
progress unfold angle_add_overflow.
apply angle_ltb_ge in Haov.
apply angle_ltb_ge.
progress unfold angle_leb in Haov.
progress unfold angle_leb.
rewrite (angle_add_comm Hic θ2).
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs12, Hzs1, Hzs2.
destruct zs2. {
  destruct zs12; [ | easy ].
  destruct zs1; [ | easy ].
  apply rngl_leb_le in Hzs1, Hzs12, Hzs2, Haov.
  apply rngl_leb_le.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    rewrite (angle_add_comm Hic).
    apply angle_add_overflow_le_lemma_111; try easy.
    now rewrite (angle_add_comm Hic).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  destruct (rngl_eq_dec Hed (rngl_cos θ2) (- 1)) as [Hc2o1| Ho1c2]. {
    apply (eq_rngl_cos_opp_1 Hic Hon Hop Hed) in Hc2o1.
    subst θ2.
    rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs12.
    rewrite (rngl_cos_add_straight_r Hon Hop).
    apply -> (rngl_opp_le_compat Hop Hor).
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
    apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
    symmetry in Hzs12.
    apply (eq_rngl_sin_0 Hic Hon Hop Hed) in Hzs12.
    destruct Hzs12; subst θ1; [ apply (rngl_le_refl Hor) | ].
    rewrite (angle_straight_add_straight Hon Hop) in Haov.
    exfalso.
    apply (rngl_nlt_ge Hor) in Haov.
    apply Haov; cbn.
    apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
  }
  rewrite (angle_add_comm Hic).
  apply angle_add_overflow_le_lemma_2 with (θ2 := θ1); try easy.
  now apply (rngl_lt_le_incl Hor).
  now rewrite (angle_add_comm Hic).
} {
  apply (rngl_leb_gt Hor) in Hzs2.
  destruct zs12. {
    exfalso.
    destruct zs1; [ | easy ].
    apply rngl_leb_le in Hzs1.
    apply rngl_leb_le in Hzs12.
    apply rngl_leb_le in Haov.
    apply angle_add_overflow_le_lemma_6 in Haov; try easy.
  }
  apply (rngl_leb_gt Hor) in Hzs12.
  apply rngl_leb_le.
  destruct zs1. {
    clear Haov.
    apply rngl_leb_le in Hzs1.
    rewrite (angle_add_comm Hic).
    apply angle_add_overflow_le_lemma_11; try easy.
    now apply (rngl_lt_le_incl Hor).
    now rewrite (angle_add_comm Hic).
  }
  apply (rngl_leb_gt Hor) in Hzs1.
  apply rngl_leb_le in Haov.
  apply (rngl_nlt_ge Hor).
  intros Hc12.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  (**)
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    remember (θ1 + angle_right)%A as θ eqn:Hθ.
    apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
    subst θ1; rename θ into θ1.
    rewrite <- (angle_add_sub_swap Hic Hop) in Haov, Hc12 |-*.
    rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs1 |-*.
    rewrite (rngl_cos_sub_right_r Hon Hop) in Haov, Haov, Hzc1, Hc12.
    apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
    apply (rngl_opp_nonneg_nonpos Hop Hor).
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      exfalso.
      remember (θ2 + angle_right)%A as θ eqn:Hθ.
      apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
      subst θ2; rename θ into θ2.
      rewrite (angle_add_sub_assoc Hop) in Haov, Hc12.
      rewrite (rngl_sin_sub_right_r Hon Hop) in Haov, Hzs2, Hc12.
      rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc2, Hc12.
      apply (rngl_opp_neg_pos Hop Hor) in Hzs2.
      apply (rngl_le_opp_r Hop Hor) in Haov.
      apply (rngl_lt_opp_l Hop Hor) in Hc12.
      apply (rngl_nlt_ge Hor) in Haov.
      apply Haov; clear Haov; cbn.
      rewrite (rngl_add_sub_assoc Hop).
      rewrite (rngl_add_sub_swap Hop).
      rewrite (rngl_sub_mul_r_diag_l Hon Hop).
      apply (rngl_add_nonneg_pos Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      apply (rngl_le_0_sub Hop Hor).
      apply (rngl_sin_bound Hon Hop Hiv Hic Hed Hor).
      now apply (rngl_mul_pos_pos Hop Hor Hii).
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    remember (θ2 + angle_straight)%A as θ eqn:Hθ.
    apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
    subst θ2; rename θ into θ2.
    rewrite (angle_add_sub_assoc Hop) in Haov, Hc12 |-*.
    rewrite (rngl_sin_sub_straight_r Hon Hop) in Haov, Hzs2, Hc12.
    rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc2z, Hc12 |-*.
    apply (rngl_le_opp_r Hop Hor) in Haov.
    apply (rngl_opp_neg_pos Hop Hor) in Hzs2, Hc2z.
    apply (rngl_opp_lt_compat Hop Hor) in Hc12.
    apply (rngl_opp_nonpos_nonneg Hop Hor).
    exfalso.
    apply (rngl_nlt_ge Hor) in Haov.
    apply Haov; clear Haov.
    apply (rngl_add_nonneg_pos Hor); [ easy | ].
    eapply (rngl_le_lt_trans Hor); [ | apply Hc12 ].
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  remember (θ1 + angle_straight)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ1; rename θ into θ1.
  rewrite <- (angle_add_sub_swap Hic Hop) in Haov, Hc12 |-*.
  rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs1 |-*.
  rewrite (rngl_cos_sub_straight_r Hon Hop) in Haov, Haov, Hc1z, Hc12.
  apply (rngl_opp_le_compat Hop Hor) in Haov.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1, Hc1z.
  apply (rngl_lt_opp_l Hop Hor) in Hc12.
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    cbn.
    apply (rngl_add_nonpos_nonpos Hor).
    apply (rngl_mul_nonneg_nonpos Hop Hor).
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
    apply (rngl_mul_nonneg_nonpos Hop Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hzc2.
  remember (θ2 + angle_right)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2.
  rewrite (angle_add_sub_assoc Hop) in Haov, Hc12 |-*.
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs2 |-*.
  rewrite (rngl_cos_sub_right_r Hon Hop) in Haov, Hzc2, Hc12, Hc12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs2.
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  apply (rngl_nlt_ge Hor).
  intros Hc12z.
  apply (rngl_nlt_ge Hor) in Haov.
  apply Haov; clear Haov.
  remember (angle_right - θ2)%A as θ eqn:Hθ.
  apply (angle_sub_move_l Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2; move θ2 before θ1.
  rewrite (angle_add_comm Hic) in Hc12, Hc12z |-*.
  rewrite <- (angle_sub_sub_distr Hic Hop) in Hc12, Hc12z |-*.
  rewrite (rngl_sin_sub_right_l Hon Hos) in Hc12, Hzc2, Hc12 |-*.
  rewrite (rngl_cos_sub_right_l Hon Hop) in Hzs2, Hc12z.
  rewrite (rngl_sin_sub_anticomm Hic Hop) in Hc12z.
  apply (rngl_opp_neg_pos Hop Hor) in Hc12z.
  rewrite (rngl_cos_sub_comm Hic Hop) in Hc12.
  (**)
  rewrite (rngl_cos_sub_comm Hic Hop) in Hc12 |-*.
  apply (rngl_lt_iff Hor).
  split. {
    apply rngl_sin_cos_nonneg_sin_sub_nonneg_cos_le; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor). {
      cbn.
      rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_sub_opp_r Hop).
      apply (rngl_add_nonneg_nonneg Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor).
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor).
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    }
    rewrite (angle_sub_sub_distr Hic Hop).
    rewrite (angle_sub_diag Hic Hon Hop Hed).
    rewrite (angle_add_0_l Hon Hos).
    now apply (rngl_lt_le_incl Hor).
  }
  intros H.
  apply (rngl_cos_eq Hic Hon Hop Hed) in H.
  destruct H as [H| H]. {
    apply (angle_sub_move_l Hic Hon Hop Hed) in H.
    rewrite (angle_sub_diag Hic Hon Hop Hed) in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  rewrite (angle_opp_sub_distr Hic Hop) in H.
  rewrite (rngl_sin_sub_anticomm Hic Hop) in Hc12z.
  rewrite <- H in Hc12z.
  apply (rngl_opp_pos_neg Hop Hor) in Hc12z.
  apply (rngl_lt_le_incl Hor) in Hc12z.
  now apply (rngl_nlt_ge Hor) in Hc12z.
}
Qed.

(*
Theorem angle_add_overflow_comm :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = angle_add_overflow θ2 θ1.
Proof.
intros Hic Hon Hop Hed *.
remember (angle_add_overflow θ1 θ2) as o12 eqn:Ho12.
remember (angle_add_overflow θ2 θ1) as o21 eqn:Ho21.
symmetry in Ho12, Ho21.
destruct o12, o21; [ easy | | | easy ]. {
...
*)

Theorem angle_add_le_mono_l_lemma_1 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
intros * Haov13 Hzs2 Hzs3 Hzc1 Hzs12 Hzs13 H23.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
apply angle_le_sub_le_add_l_lemma_1; try easy. {
  rewrite (angle_add_comm Hic).
  now rewrite (angle_add_sub Hic Hon Hop Hed).
} {
  rewrite (angle_add_comm Hic).
  now rewrite (angle_add_sub Hic Hon Hop Hed).
}
Qed.

Theorem angle_add_le_mono_l_lemma_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ1 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haov13 Hzs1 Hzs2 Hzs3 Hc1z Hzs12 Hzs13 H23.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12.
rewrite (angle_add_add_swap Hic Hop).
rewrite (angle_add_add_swap Hic Hop _ _ θ2).
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs13, Hzs12, Hzs1.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z.
do 2 rewrite (rngl_cos_add_right_r Hon Hop).
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
apply -> (rngl_opp_le_compat Hop Hor).
move Hc1z after Hzs2; move Hzs1 before Hzs3.
specialize rngl_sin_nonneg_cos_le_sin_le as H1.
specialize (H1 Hic Hon Hop Hed θ3 θ2 Hzs3 Hzs2 H23).
destruct (rngl_le_dec Hor 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
  move Hzc3 before Hzs1.
  apply rngl_leb_le in Hzc3.
  rewrite Hzc3 in H1.
  rename H1 into Hs23.
  apply rngl_leb_le in Hzc3.
  destruct (rngl_lt_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
    apply (rngl_nle_gt Hor) in Hc2z.
    exfalso; apply Hc2z; clear Hc2z.
    eapply (rngl_le_trans Hor); [ apply Hzc3 | easy ].
  }
  apply (rngl_nlt_ge Hor) in Hzc2.
  move Hzc2 before Hzs1.
  rename Hzs12 into Hzc12; rename Hzs13 into Hzc13.
  assert (Hzs12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
    apply (rngl_lt_le_incl Hor) in Hc1z.
    now apply (rngl_sin_add_nonneg Hop).
  }
  assert (Hzs13 : (0 ≤ rngl_sin (θ1 + θ3))%L). {
    apply (rngl_lt_le_incl Hor) in Hc1z.
    now apply (rngl_sin_add_nonneg Hop).
  }
  specialize rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff as H1.
  apply H1; try easy.
  clear H1.
  apply angle_add_le_mono_l_lemma_1; try easy.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  progress unfold angle_leb.
  generalize Hc1z; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_leb_le in Hzs13.
  rewrite Hzs13.
  apply rngl_leb_le in Hzs13.
  apply rngl_leb_le.
  apply angle_le_sub_le_add_l_lemma_1; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  rewrite (angle_sub_diag Hic Hon Hop Hed).
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  rewrite (angle_sub_diag Hic Hon Hop Hed).
  apply (rngl_le_refl Hor).
}
apply rngl_leb_nle in Hc3z.
rewrite Hc3z in H1.
apply (rngl_leb_gt Hor) in Hc3z.
apply (rngl_nlt_ge Hor) in Hzs13.
exfalso; apply Hzs13; clear Hzs13.
apply (rngl_lt_iff Hor).
split. {
  cbn.
  apply (rngl_le_sub_0 Hop Hor).
  apply (rngl_le_trans Hor _ 0).
  apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
intros Hc13.
apply (eq_rngl_cos_0 Hic Hon Hop Hed) in Hc13.
destruct Hc13 as [Hc13| Hc13]. {
  apply (angle_add_move_l Hic Hon Hop Hed) in Hc13.
  subst θ3.
  apply (rngl_nle_gt Hor) in Hc3z.
  apply Hc3z.
  rewrite (rngl_cos_sub_right_l Hon Hop).
  now apply (rngl_lt_le_incl Hor).
}
apply (angle_add_move_l Hic Hon Hop Hed) in Hc13.
subst θ3.
progress unfold angle_add_overflow in Haov13.
apply angle_ltb_ge in Haov13.
apply angle_nlt_ge in Haov13.
apply Haov13; clear Haov13.
rewrite (angle_add_sub_assoc Hop).
rewrite angle_add_opp_r.
rewrite (angle_add_sub Hic Hon Hop Hed).
rewrite (angle_sub_diag Hic Hon Hop Hed).
progress unfold angle_ltb.
rewrite (rngl_sin_add_right_r Hon Hos).
rewrite (rngl_leb_refl Hor).
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
rewrite (rngl_cos_add_right_r Hon Hop).
apply (rngl_lt_opp_l Hop Hor); cbn.
apply (rngl_add_pos_nonneg Hor); [ easy | ].
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_3 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13 H23.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  move Hzc1 before Hzs3.
  now apply angle_add_le_mono_l_lemma_1.
}
apply (rngl_nle_gt Hor) in Hc1z.
move Hc1z before Hzs3.
destruct (rngl_le_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
  move Hzs1 after Hzs2.
  now apply angle_add_le_mono_l_lemma_2.
}
apply (rngl_nle_gt Hor) in Hs1z.
move Hs1z after Hzs2.
remember (θ1 - angle_straight)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12 |-*.
rewrite (angle_add_add_swap Hic Hop _ _ θ2).
rewrite (rngl_sin_add_straight_r Hon Hop) in Hs1z, Hzs13, Hzs12.
rewrite (rngl_cos_add_straight_r Hon Hop) in Hc1z.
do 2 rewrite (rngl_cos_add_straight_r Hon Hop).
apply (rngl_opp_neg_pos Hop Hor) in Hs1z, Hc1z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs13, Hzs12.
apply -> (rngl_opp_le_compat Hop Hor).
move Hs1z before Hzs2; move Hc1z before Hzs3.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ2))%L as [Hzc2| Hc2z]. {
  move Hzc2 before Hc1z.
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_is_pos_2.
}
apply (rngl_nlt_ge Hor) in Hc2z.
remember (θ2 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ1.
rewrite (angle_add_assoc Hop) in Hzs12 |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hzs12.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc2z, H23 |-*.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z.
apply (rngl_le_opp_r Hop Hor) in H23.
apply (rngl_le_opp_l Hop Hor).
move Hc2z before Hs1z; move Hzs2 after Hc1z.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
  move Hzc3 before Hzs2.
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_is_pos_2.
}
apply (rngl_nlt_ge Hor) in Hc3z.
remember (θ3 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ3; rename θ into θ3; move θ3 before θ2.
rewrite (angle_add_assoc Hop) in Hzs13 |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs3, Hzs13.
rewrite (rngl_cos_add_right_r Hon Hop) in H23, Hc3z |-*.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc3z.
rewrite (rngl_add_opp_l Hop) in H23.
rewrite (rngl_add_opp_r Hop).
apply -> (rngl_le_sub_0 Hop Hor) in H23.
apply (rngl_le_0_sub Hop Hor).
move Hc3z before Hc2z; move Hzs3 after Hzs2.
generalize H23; intros H32.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff in H32; try easy.
move H32 before H23.
assert (Hs12z : (0 ≤ rngl_sin (θ1 + θ2))%L). {
  apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
  now apply (rngl_sin_add_nonneg Hop).
}
assert (Hs13z : (0 ≤ rngl_sin (θ1 + θ3))%L). {
  apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
  now apply (rngl_sin_add_nonneg Hop).
}
apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy.
apply angle_add_le_mono_l_lemma_1; try easy; cycle 1.
now apply (rngl_lt_le_incl Hor).
progress unfold angle_add_overflow.
apply angle_ltb_ge.
progress unfold angle_leb.
generalize Hs1z; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hs13z; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le.
apply angle_add_overflow_le_lemma_111; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_4 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_right)%A = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → False.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haov12 Hzs1 Hzc2 Hzc1 Hzs2 Hzs12.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
rewrite (rngl_cos_sub_right_r Hon Hop).
remember (angle_right - θ2)%A as θ eqn:Hθ.
apply (angle_sub_move_l Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2.
rewrite (angle_add_sub_assoc Hop) in Hzs12 |-*.
rewrite (angle_add_sub_swap Hic Hop) in Hzs12 |-*.
rewrite (rngl_sin_sub_right_l Hon Hos) in Hzc2.
rewrite (rngl_sin_add_right_r Hon Hos).
rewrite (rngl_cos_sub_right_l Hon Hop) in Hzs2.
rewrite (rngl_cos_add_right_r Hon Hop) in Hzs12.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs12.
rewrite (rngl_cos_sub_comm Hic Hop).
apply (rngl_lt_iff Hor).
split. {
  rewrite (rngl_cos_sub_comm Hic Hop).
  apply rngl_sin_cos_nonneg_sin_sub_nonneg_cos_le; try easy. {
    cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  } {
    rewrite (angle_sub_sub_distr Hic Hop).
    rewrite (angle_sub_diag Hic Hon Hop Hed).
    rewrite (angle_add_0_l Hon Hos).
    now apply (rngl_lt_le_incl Hor).
  }
}
intros H.
apply (rngl_cos_eq Hic Hon Hop Hed) in H.
destruct H. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  rewrite (rngl_sin_sub_anticomm Hic Hop).
  rewrite <- H.
  apply (rngl_opp_neg_pos Hop Hor).
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H1; symmetry in H1.
  apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H1.
  move H1 at top.
  destruct H1; subst θ1. {
    rewrite (angle_sub_0_r Hon Hop) in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  apply (angle_add_move_r Hic Hon Hop Hed) in H.
  rewrite (angle_straight_add_straight Hon Hop) in H.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
rewrite (angle_opp_sub_distr Hic Hop) in H.
apply (angle_sub_move_l Hic Hon Hop Hed) in H.
rewrite (angle_sub_diag Hic Hon Hop Hed) in H.
subst θ2.
now apply (rngl_lt_irrefl Hor) in Hzs2.
Qed.

Theorem angle_add_le_mono_l_lemma_5 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_right)%A = false
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (rngl_sin θ1 < 0)%L
  → False.
Proof.
intros Hon Hop.
destruct ac as (Hiv, Hc2, Hor).
intros * Haov12 Hzs12 Hs1z.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hs1z; intros H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
now rewrite H.
Qed.

Theorem angle_add_le_mono_l_lemma_6 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 (θ3 - angle_right)%A = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ2 ≤ 0)%L
  → (0 < rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → (rngl_sin (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haov13 Hzs2 Hzc3 Hc2z Hzs3 Hzs12 Hzs13.
remember (θ2 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ1.
rewrite (angle_add_assoc Hop) in Hzs12 |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hzs12.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc2z |-*.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z.
apply (rngl_le_opp_r Hop Hor).
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  exfalso.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
    now apply angle_add_le_mono_l_lemma_4 in Hzs13.
  } {
    apply (rngl_nle_gt Hor) in Hs1z.
    now apply angle_add_le_mono_l_lemma_5 in Hzs13.
  }
}
apply (rngl_nle_gt Hor) in Hc1z.
destruct (rngl_le_dec Hor (rngl_sin θ1) 0)%L as [Hs1z| Hzs1]. {
  apply (rngl_add_nonpos_nonpos Hor); cbn.
  apply (rngl_add_nonpos_nonpos Hor); cbn.
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_add_nonpos_nonpos Hor); cbn.
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_mul_nonpos_nonneg Hop Hor).
}
apply (rngl_nle_gt Hor) in Hzs1.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1; move θ1 after θ2.
rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12 |-*.
rewrite (angle_add_add_swap Hic Hop _ _ θ2).
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1.
do 2 rewrite (rngl_sin_add_right_r Hon Hos).
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z, Hzs13, Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs13.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
exfalso.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_lt_le_incl Hor) in Hzs1, Hc1z.
  now apply (rngl_sin_add_nonneg Hop).
}
intros H; symmetry in H.
apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H.
destruct H as [H| H]. {
  apply (angle_add_move_l Hic Hon Hop Hed) in H.
  rewrite (angle_sub_0_l Hon Hos) in H.
  subst θ2.
  cbn in Hc2z.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
  now apply (rngl_nlt_ge Hor) in Hc2z.
}
apply (angle_add_move_l Hic Hon Hop Hed) in H.
subst θ2.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
now apply (rngl_nlt_ge Hor) in Hzs2.
Qed.

Theorem angle_add_le_mono_l_lemma_7 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13 Hzc3.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13 Hzc3.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
remember (θ3 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ3; rename θ into θ3; move θ3 before θ2.
rewrite (angle_add_sub_assoc Hop) in Hzs13 |-*.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs3, Hzs13.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc3 |-*.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs13.
apply (rngl_opp_neg_pos Hop Hor) in Hzs3.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
  now apply angle_add_le_mono_l_lemma_6.
}
apply (rngl_nle_gt Hor) in Hzc2.
move Hzc2 after Hzs3.
apply (rngl_nlt_ge Hor).
intros H123.
progress unfold angle_add_overflow in Haov13.
apply angle_ltb_ge in Haov13.
apply angle_nlt_ge in Haov13.
apply Haov13; clear Haov13.
rewrite (angle_add_sub_assoc Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs13; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
rewrite (rngl_cos_sub_right_r Hon Hop).
apply rngl_ltb_lt.
remember (angle_right - θ3)%A as θ.
apply (angle_sub_move_l Hic Hon Hop Hed) in Heqθ.
subst θ3; rename θ into θ3; move θ3 before θ2.
rewrite (angle_add_comm Hic) in Hzs13 |-*.
rewrite (angle_add_comm Hic _ (_ - _))%A in H123.
rewrite <- (angle_sub_sub_distr Hic Hop) in H123, Hzs13 |-*.
rewrite (rngl_sin_sub_right_l Hon Hos) in Hzc3, H123 |-*.
rewrite (rngl_cos_sub_right_l Hon Hop) in Hzs3, Hzs13.
rewrite (rngl_sin_sub_anticomm Hic Hop) in Hzs13.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  destruct (rngl_eq_dec Hed 0 (rngl_sin (θ1 - θ3)))
      as [Hzs1s3| Hs1s3z]. {
    symmetry in Hzs1s3.
    apply (eq_rngl_sin_0 Hic Hon Hop Hed) in Hzs1s3.
    destruct Hzs1s3 as [H| H]. {
      apply -> (angle_sub_move_0_r Hic Hon Hop Hed) in H.
      subst θ3.
      rewrite (angle_sub_diag Hic Hon Hop Hed) in H123 |-*.
      cbn.
      apply (rngl_lt_iff Hor).
      split; [ apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor) | ].
      intros H.
      apply (eq_rngl_cos_1 Hic Hon Hop Hed) in H.
      subst θ1.
      now apply (rngl_lt_irrefl Hor) in Hzs3.
    }
    apply (angle_sub_move_l Hic Hon Hop Hed) in H.
    subst θ3.
    rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs3.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs3.
    now apply (rngl_nle_gt Hor) in Hzs3.
  }
  apply not_eq_sym in Hs1s3z.
  apply rngl_cos_lt_rngl_cos_sub; try easy.
  apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy.
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_lt_iff Hor).
  split; [ now apply rngl_sin_sub_nonneg_sin_le_sin | ].
  intros H.
  apply (rngl_sin_eq Hic Hon Hop Hed) in H.
  destruct H; subst θ3. {
    now rewrite (angle_sub_diag Hic Hon Hop Hed) in Hs1s3z.
  }
  rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzc3.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzc3.
  apply (rngl_le_antisymm Hor) in Hzc3; [ | easy].
  symmetry in Hzc3.
  apply (eq_rngl_cos_0 Hic Hon Hop Hed) in Hzc3.
  destruct Hzc3; subst θ1. {
    rewrite (angle_straight_sub_right Hon Hop) in Hs1s3z.
    now rewrite (angle_sub_diag Hic Hon Hop Hed) in Hs1s3z.
  }
  apply (rngl_nlt_ge Hor) in Hzs1.
  apply Hzs1; cbn.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1; move θ1 after θ2.
rewrite (angle_add_sub_swap Hic Hop) in Hzs13.
rewrite (angle_add_add_swap Hic Hop) in H123, Hzs12.
rewrite (angle_sub_add_distr Hic Hop) in H123 |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs13, Hzs12.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z, H123 |-*.
rewrite (rngl_cos_sub_right_r Hon Hop) in H123 |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
apply (rngl_lt_opp_l Hop Hor) in H123.
apply (rngl_lt_opp_l Hop Hor).
destruct (rngl_eq_dec Hed (rngl_cos θ3) 1) as [Hc31| Hc31]. {
  apply (eq_rngl_cos_1 Hic Hon Hop Hed) in Hc31.
  subst θ3.
  now apply (rngl_lt_irrefl Hor) in Hzs3.
}
cbn.
rewrite rngl_add_assoc.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_sub_mul_r_diag_r Hon Hop).
apply (rngl_add_pos_nonneg Hor).
apply (rngl_mul_pos_pos Hop Hor Hii); [ | easy ].
apply (rngl_lt_0_sub Hop Hor).
apply (rngl_lt_iff Hor).
split; [ | easy ].
apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_8 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_straight)%A = false
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 < rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov12 Hzc1 Hzs2 Hc2z.
destruct (rngl_lt_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply rngl_sin_add_is_pos_2.
}
apply (rngl_nlt_ge Hor) in Hs1z.
apply (rngl_nle_gt Hor).
intros Hzs12.
remember (θ1 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12, Hs1z.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc1.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs1z, Hzs12.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
rewrite <- (angle_add_sub_swap Hic Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_straight_r Hon Hop).
rewrite (rngl_sin_sub_right_r Hon Hop).
rewrite (rngl_opp_involutive Hop).
apply rngl_leb_le in Hzs12.
rewrite Hzs12.
apply rngl_leb_le in Hzs12.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hs1z; intros H.
apply (rngl_lt_eq_cases Hor) in H.
destruct H as [H| H]. {
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_leb_gt Hor) in H.
  now rewrite H.
}
rewrite <- H.
rewrite (rngl_opp_0 Hop).
rewrite (rngl_leb_refl Hor).
rewrite (rngl_cos_sub_right_r Hon Hop).
rewrite (rngl_cos_sub_straight_r Hon Hop).
rewrite (rngl_cos_sub_right_r Hon Hop).
apply rngl_ltb_lt.
apply (rngl_lt_opp_r Hop Hor).
symmetry in H.
apply (eq_rngl_cos_0 Hic Hon Hop Hed) in H.
destruct H; subst θ1. {
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  rewrite (rngl_cos_add_right_l Hon Hop).
  now apply (rngl_opp_neg_pos Hop Hor).
}
rewrite (angle_add_opp_l Hic).
rewrite (rngl_sin_sub_right_r Hon Hop).
rewrite (rngl_add_opp_r Hop).
cbn.
apply (rngl_lt_sub_0 Hop Hor).
apply (rngl_lt_iff Hor).
split; [ apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor) | ].
intros H.
symmetry in H.
apply (eq_rngl_cos_opp_1 Hic Hon Hop Hed) in H.
subst θ2.
now apply (rngl_lt_irrefl Hor) in Hzs2.
Qed.

Theorem angle_add_le_mono_l_lemma_9 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_straight)%A = false
  → (rngl_cos θ1 < 0)%L
  → (rngl_sin θ1 < 0)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Haov12 Hc1z Hs1z.
apply (rngl_nle_gt Hor).
intros Hzs12.
remember (θ1 + angle_straight)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hs1z, Hzs12.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc1z.
apply (rngl_opp_neg_pos Hop Hor) in Hs1z, Hc1z.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs12.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
rewrite <- (angle_add_sub_swap Hic Hop).
rewrite <- (angle_sub_add_distr Hic Hop).
rewrite (angle_straight_add_straight Hon Hop).
rewrite (angle_sub_0_r Hon Hop).
progress unfold angle_ltb.
apply rngl_leb_le in Hzs12.
rewrite Hzs12.
apply rngl_leb_le in Hzs12.
rewrite (rngl_sin_sub_straight_r Hon Hop).
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply (rngl_leb_nle) in H.
now rewrite H.
Qed.

Theorem angle_add_le_mono_l_lemma_10 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow (θ1 + angle_right)%A θ2 = false
  → (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (rngl_cos θ2 ≤ 0)%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L
  → False.
Proof.
intros Hic Hon Hop Hed.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct ac as (Hiv, Hc2, Hor).
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Hc1z Hzs2 Hzs1 Hc2z Hzs12.
  rewrite (H1 (rngl_sin _)) in Hc1z.
  now apply (rngl_lt_irrefl Hor) in Hc1z.
}
intros * Haov12 Hc1z Hzs2 Hzs1 Hc2z Hzs12.
remember (θ2 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ1.
rewrite (angle_add_assoc Hop) in Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc2z, Hzs12.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply (rngl_sin_add_nonneg Hop).
}
intros H; symmetry in H.
apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H.
destruct H as [H| H]. {
  apply (angle_add_move_l Hic Hon Hop Hed) in H.
  rewrite (angle_sub_0_l Hon Hos) in H.
  subst θ2.
  cbn in Hc2z.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
  now apply (rngl_nlt_ge Hor) in Hc2z.
}
apply (angle_add_move_l Hic Hon Hop Hed) in H.
subst θ2.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
symmetry in Hzs2.
apply (eq_rngl_cos_0 Hic Hon Hop Hed) in Hzs2.
destruct Hzs2; subst θ1. {
  progress unfold angle_add_overflow in Haov12.
  apply angle_ltb_ge in Haov12.
  apply (angle_nlt_ge) in Haov12.
  apply Haov12; clear Haov12.
  rewrite (angle_right_add_right Hon Hop).
  rewrite (angle_sub_add Hic Hon Hop Hed).
  rewrite (angle_straight_add_straight Hon Hop).
  progress unfold angle_ltb; cbn.
  rewrite (rngl_leb_refl Hor).
  apply rngl_ltb_lt.
  apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
}
rewrite (angle_sub_opp_r Hop) in Hc2z.
rewrite (rngl_sin_add_right_r Hon Hos) in Hc2z.
apply (rngl_nlt_ge Hor) in Hc2z.
apply Hc2z; clear Hc2z; cbn.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

Theorem angle_add_le_mono_l_lemma_11 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (rngl_sin θ2 < 0)%L
  → (rngl_cos θ2 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → False.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haov12 Hzs2 Hc2z Hzs12.
remember (θ2 + angle_straight)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2.
rewrite (angle_add_sub_assoc Hop) in Hzs12.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs2, Hzs12.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc2z.
apply (rngl_opp_neg_pos Hop Hor) in Hzs2, Hc2z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply angle_add_le_mono_l_lemma_8.
}
apply (rngl_nle_gt Hor) in Hc1z.
destruct (rngl_lt_dec Hor (rngl_sin θ1) 0)%L as [Hs1z| Hzs1]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply angle_add_le_mono_l_lemma_9.
}
apply (rngl_nlt_ge Hor) in Hzs1.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
rewrite (angle_add_add_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs12.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
rewrite (angle_add_add_swap Hic Hop).
rewrite (angle_add_sub_swap Hic Hop).
rewrite <- (angle_sub_sub_distr Hic Hop).
rewrite (angle_straight_sub_right Hon Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_sin_add_right_r Hon Hos).
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
rewrite (rngl_cos_add_right_r Hon Hop).
rewrite (rngl_cos_sub_right_r Hon Hop).
apply rngl_ltb_lt.
apply (rngl_lt_le_trans Hor _ 0); [ now apply (rngl_opp_neg_pos Hop Hor) | ].
apply (rngl_lt_le_incl Hor) in Hc1z, Hzs2, Hc2z.
now apply (rngl_sin_add_nonneg Hop).
Qed.

Theorem angle_add_le_mono_l_lemma_12 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (0 < rngl_cos θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 < rngl_cos θ3)%L
  → (rngl_sin (θ1 + θ2) ≤ 0)%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → False.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzc1 Hzs2 Hc2z Hzc3 Hzs3 Hzs12 Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply rngl_sin_add_is_pos_1.
}
apply (rngl_nle_gt Hor) in Hs1z.
remember (θ1 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs13, Hzs12.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12, Hs1z.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hzs13, Hzc1.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hs1z.
apply (rngl_nlt_ge Hor) in Hzs13.
apply Hzs13; clear Hzs13.
apply (rngl_lt_le_incl Hor) in Hs1z.
now apply rngl_sin_add_is_pos_2.
Qed.

Theorem angle_add_le_mono_l_lemma_13 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 (θ2 - angle_straight)%A = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ1 ≤ 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_sin (θ1 + θ2) ≤ 0)%L
  → (rngl_sin (θ1 + θ3) + rngl_cos (θ1 + θ2) ≤ 0)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Hzs1 Hzs2 Hzc3 Hc1z Hc2z Hzs12.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Haov12 Hzs1 Hzs2 Hzc3 Hc1z Hc2z Hzs12.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
rewrite (angle_add_add_swap Hic Hop) in Hzs12.
do 2 rewrite (angle_add_add_swap Hic Hop _ angle_right).
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs12 |-*.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z |-*.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc1z.
rewrite (rngl_add_opp_r Hop).
apply (rngl_le_sub_0 Hop Hor).
apply (rngl_nlt_ge Hor).
intros Hs12.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
rewrite (angle_add_add_swap Hic Hop).
rewrite (angle_add_sub_swap Hic Hop).
rewrite <- (angle_sub_sub_distr Hic Hop).
rewrite (angle_straight_sub_right Hon Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_sin_add_right_r Hon Hos).
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
rewrite (rngl_cos_sub_right_r Hon Hop).
rewrite (rngl_cos_add_right_r Hon Hop).
apply rngl_ltb_lt.
apply (rngl_lt_opp_l Hop Hor).
apply (rngl_lt_iff Hor).
split. {
  cbn.
  rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap.
  rewrite (rngl_add_mul_r_diag_l Hon).
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
intros H; symmetry in H.
apply (rngl_add_move_0_r Hop) in H.
generalize Hc1z; intros H1.
rewrite H in H1.
apply (rngl_opp_nonneg_nonpos Hop Hor) in H1.
apply (rngl_nlt_ge Hor) in H1.
apply H1; clear H1.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply (rngl_sin_add_nonneg Hop).
}
intros H1; symmetry in H1.
apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H1.
destruct H1 as [H1| H1]. {
  apply (angle_add_move_l Hic Hon Hop Hed) in H1.
  rewrite (angle_sub_0_l Hon Hos) in H1.
  subst θ2.
  cbn in Hzs2.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
  now apply (rngl_nlt_ge Hor) in Hzs2.
}
apply (angle_add_move_l Hic Hon Hop Hed) in H1.
subst θ2.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc2z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
apply (rngl_le_antisymm Hor) in Hc2z; [ | easy ].
symmetry in Hc2z.
apply (eq_rngl_cos_0 Hic Hon Hop Hed) in Hc2z.
destruct Hc2z; subst θ1. {
  rewrite (angle_straight_sub_right Hon Hop) in Hs12.
  rewrite (angle_right_add_right Hon Hop) in Hs12.
  rewrite (rngl_cos_add_right_l Hon Hop) in Hs12.
  cbn in Hs12.
  apply (rngl_opp_pos_neg Hop Hor) in Hs12.
  now apply (rngl_nle_gt Hor) in Hs12.
}
apply (rngl_nlt_ge Hor) in Hc1z.
apply Hc1z; cbn.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

Theorem angle_add_le_mono_l_lemma_14 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 (θ3 - angle_right)%A = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_cos θ2)%L
  → (0 < rngl_cos θ3)%L
  → (rngl_sin θ2 ≤ rngl_sin θ3)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → (rngl_sin (θ1 + θ3) ≤ rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Haov13 Hzs1 Hzc2 Hzc3 Hzc1 Hzs2 Hzs3 H23 Hzs12 Hzs13.
apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy. {
  apply (rngl_lt_le_incl Hor) in Hzs3.
  now apply (rngl_sin_add_nonneg Hop).
} {
  apply (rngl_lt_le_incl Hor) in Hzc2, Hzs2.
  now apply (rngl_sin_add_nonneg Hop).
}
apply angle_add_le_mono_l_lemma_3; try easy. {
  apply (angle_add_overflow_le) with (θ2 := (θ3 - angle_right)%A);
    try easy.
  progress unfold angle_leb.
  apply rngl_leb_le in Hzc3.
  rewrite Hzc3.
  apply rngl_leb_le in Hzc3.
  rewrite (rngl_sin_sub_right_r Hon Hop).
  generalize Hzs3; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  now rewrite H.
} {
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_lt_le_incl Hor) in Hzc2, Hzs2.
  now apply (rngl_sin_add_nonneg Hop).
} {
  apply (rngl_lt_le_incl Hor) in Hzs3.
  now apply (rngl_sin_add_nonneg Hop).
}
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_15 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_right)%A = false
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (rngl_sin θ1 < 0)%L
  → False.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Haov12 Hzs12 Hs1z.
remember (θ1 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hs1z.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hs1z.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
rewrite <- (angle_add_sub_swap Hic Hop).
rewrite <- (angle_sub_add_distr Hic Hop).
rewrite (angle_right_add_right Hon Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_straight_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
now rewrite H.
Qed.

Theorem angle_add_le_mono_l_lemma_16 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ1 θ3 = false
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov12 Haov13 Hzs2 Hzs3 Hzc3 H23 Hzs12 Hzs13.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
remember (θ3 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ3; rename θ into θ3; move θ3 before θ2.
rewrite (angle_add_sub_assoc Hop) in Hzs13 |-*.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs3, Hzs13.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc3, H23 |-*.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs13.
apply (rngl_opp_neg_pos Hop Hor) in Hzs3.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
  remember (θ2 + angle_straight)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2.
  rewrite (angle_add_sub_assoc Hop) in Hzs12 |-*.
  rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs2, Hzs12.
  rewrite (rngl_cos_sub_straight_r Hon Hop) in H23, Hc2z |-*.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z.
  apply (rngl_le_opp_l Hop Hor) in H23.
  apply (rngl_le_opp_r Hop Hor).
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
    exfalso.
    now apply (angle_add_le_mono_l_lemma_12 Hic Hon Hop Hed θ1 θ2 θ3).
  } {
    apply (rngl_nlt_ge Hor) in Hc1z.
    now apply angle_add_le_mono_l_lemma_13.
  }
}
apply (rngl_nle_gt Hor) in Hzc2.
remember (θ2 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ1.
rewrite (angle_add_sub_assoc Hop) in Hzs12 |-*.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs2, Hzs12.
rewrite (rngl_cos_sub_right_r Hon Hop) in H23, Hzc2 |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hzs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
move Hzc2 after Hzc3; move Hzs2 before Hzs3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  now apply angle_add_le_mono_l_lemma_14.
}
apply (rngl_nle_gt Hor) in Hc1z.
apply (rngl_nlt_ge Hor).
intros Hs123.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
rewrite (rngl_cos_sub_right_r Hon Hop).
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12 |-*.
do 2 rewrite (angle_add_add_swap Hic Hop _ angle_right) in Hs123.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hs123, Hs123 |-*.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z, Hzs13, Hzs12 |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs13, Hzs12.
apply (rngl_lt_opp_l Hop Hor).
cbn.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
rewrite <- (rngl_add_sub_assoc Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
apply (rngl_add_nonneg_pos Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
apply (rngl_lt_0_sub Hop Hor).
apply (rngl_lt_iff Hor).
split; [ apply (rngl_sin_bound Hon Hop Hiv Hic Hed Hor) | ].
intros H.
apply (eq_rngl_sin_1 Hic Hon Hop Hed) in H.
subst θ2.
now apply (rngl_lt_irrefl Hor) in Hzs2.
Qed.

Theorem angle_add_le_mono_l_lemma_18 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc3, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Hzs1 Hzs2 Hzs3 Hzc3 H32 Hzs12.
  rewrite (H1 (rngl_sin _)).
  apply (rngl_le_refl Hor).
}
intros * Haov12 Hzs1 Hzs2 Hzs3 Hzc3 H32 Hzs12.
apply (rngl_nlt_ge Hor).
intros Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  now apply (rngl_sin_add_nonneg Hop).
}
apply (rngl_nle_gt Hor) in Hc1z.
move Hc1z after Hzc3.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1; move θ1 after θ3.
rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs12, Hzs13.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
move Hc1z after Hzs3; move Hzs1 before Hzc3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  move Hzc2 before Hzc3.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply rngl_cos_add_nonneg_cos_add_nonneg with (θ3 := θ2); try easy.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
}
apply (rngl_nle_gt Hor) in Hc2z.
remember (θ2 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ3.
rewrite (angle_add_assoc Hop) in Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2.
rewrite (rngl_cos_add_right_r Hon Hop) in Hzs12, Hc2z, H32.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
apply (rngl_le_opp_l Hop Hor) in H32.
move Hc2z before Hzs3; move Hzs2 after Hzc3.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [H| H]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_is_pos_1.
}
apply (rngl_nlt_ge Hor) in H.
apply (rngl_le_antisymm Hor) in H; [ | easy ].
symmetry in H.
apply (eq_rngl_cos_0 Hic Hon Hop Hed) in H.
destruct H; subst θ1. {
  rewrite (rngl_sin_add_right_l Hon Hos) in Hzs12.
  apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
  symmetry in Hzs12.
  apply (eq_rngl_cos_0 Hic Hon Hop Hed) in Hzs12.
  destruct Hzs12; subst θ2. {
    rewrite (angle_right_add_right Hon Hop) in Haov12.
    now rewrite angle_add_overflow_straight_straight in Haov12.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  apply Hc2z; cbn.
  apply (rngl_opp_1_le_0 Hon Hop Hor).
}
apply (rngl_nlt_ge Hor) in Hc1z.
apply Hc1z.
apply (rngl_opp_1_le_0 Hon Hop Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_19 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haov13 Hzs2 Hzs3 H23 Hzs13.
apply (rngl_nlt_ge Hor).
intros Hzs12.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
move Hzs1 after Hzs2.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  move Hzc2 after Hzs3.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply angle_add_le_mono_l_lemma_18 with (θ2 := θ3).
} {
  apply (rngl_nle_gt Hor) in Hc2z.
  remember (θ2 - angle_right)%A as θ eqn:Hθ.
  apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2; move θ2 before θ3.
  rewrite (angle_add_assoc Hop) in Hzs12.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hzs12.
  rewrite (rngl_cos_add_right_r Hon Hop) in Hc2z, H23.
  apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
  apply (rngl_le_opp_r Hop Hor) in H23.
  move Hc2z before Hzs3.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply (rngl_nlt_ge Hor) in H23.
    apply H23; clear H23.
    now apply (rngl_add_nonneg_pos Hor).
  }
  apply (rngl_nle_gt Hor) in Hc3z.
  remember (θ3 - angle_right)%A as θ eqn:Hθ.
  apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
  subst θ3; rename θ into θ3; move θ3 before θ2.
  rewrite (angle_add_assoc Hop) in Hzs13.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs3, Hzs13.
  rewrite (rngl_cos_add_right_r Hon Hop) in H23, Hc3z.
  apply (rngl_opp_neg_pos Hop Hor) in Hc3z.
  rewrite (rngl_add_opp_l Hop) in H23.
  apply -> (rngl_le_sub_0 Hop Hor) in H23.
  move Hc3z before Hc2z.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    apply (rngl_lt_le_incl Hor) in Hc2z, Hc3z.
    now apply rngl_cos_add_nonneg_cos_add_nonneg with (θ3 := θ3).
  } {
    apply (rngl_nle_gt Hor) in Hc1z.
    rewrite (angle_add_comm Hic) in Hzs13.
    apply angle_add_le_mono_l_lemma_10 in Hzs13; try easy.
    2: now apply (rngl_lt_le_incl Hor).
    now apply (angle_add_overflow_false_comm Hic Hon Hop Hed).
  }
}
Qed.

Theorem angle_add_le_mono_l_lemma_20 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 < rngl_cos θ3)%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_sin (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos (θ1 + θ3))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros * Hzs2 Hzs3 Hzc3 H23 Hzs12 Hzs13.
assert (Hzc2 : (0 < rngl_cos θ2)%L). {
  eapply (rngl_lt_le_trans Hor); [ apply Hzc3 | apply H23 ].
}
destruct (rngl_lt_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    exfalso.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; clear Hzs12.
    apply (rngl_lt_le_incl Hor) in Hzc2, Hzs1.
    now apply (rngl_sin_add_nonneg Hop).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  remember (angle_straight - θ1)%A as θ.
  apply (angle_sub_move_l Hic Hon Hop Hed) in Heqθ.
  subst θ1; rename θ into θ1; move θ1 after θ2.
  rewrite <- (angle_sub_sub_distr Hic Hop) in Hzs13, Hzs12.
  do 2 rewrite <- (angle_sub_sub_distr Hic Hop).
  rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs13, Hzs12(*, Hzs1*).
  rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc1z.
  do 2 rewrite (rngl_cos_sub_straight_l Hon Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_sin_sub_anticomm Hic Hop) in Hzs13, Hzs12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs13, Hzs12, Hc1z.
  do 2 rewrite (rngl_cos_sub_comm Hic Hop θ1).
  destruct (rngl_eq_dec Hed (rngl_sin θ2) (rngl_sin θ3)) as
    [Hes23| Hes23]. {
    apply (rngl_sin_eq Hic Hon Hop Hed) in Hes23.
    destruct Hes23; subst θ2; [ apply (rngl_le_refl Hor) | ].
    rewrite (rngl_cos_sub_straight_l Hon Hop) in H23.
    rewrite <- (angle_sub_add_distr Hic Hop) in Hzs12 |-*.
    rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs12.
    rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzc2 |-*.
    apply (rngl_opp_pos_neg Hop Hor) in Hzc2.
    apply (rngl_le_opp_r Hop Hor).
    cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_add_sub_assoc Hop).
    rewrite (rngl_add_add_swap).
    rewrite (rngl_add_sub Hos).
    rewrite <- (rngl_mul_add_distr_r).
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ | ].
    apply (rngl_lt_le_incl Hor) in Hzc2.
    now apply (rngl_add_nonpos_nonpos Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nlt_ge Hor).
  intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_sin_nonneg_cos_le_sin_sub_nonneg in H; try easy. {
    rewrite (angle_sub_sub_distr Hic Hop) in H.
    rewrite (angle_sub_sub_swap Hic Hop) in H.
    rewrite (angle_sub_add Hic Hon Hop Hed) in H.
    apply (rngl_nlt_ge Hor) in H.
    apply H; clear H.
    cbn.
    eapply (rngl_le_lt_trans Hor). {
      apply (rngl_add_le_mono_l Hop Hor).
      apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
      apply H23.
    }
    rewrite (rngl_mul_comm Hic).
    rewrite <- rngl_mul_add_distr_r.
    rewrite (rngl_add_opp_l Hop).
    rewrite (rngl_mul_comm Hic).
    apply (rngl_mul_pos_neg Hop Hor Hid); [ easy | ].
    apply (rngl_lt_sub_0 Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ | easy ].
    apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nlt_ge Hor) in Hs1z.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hzc1| Hc1z]. {
  cbn.
  apply (rngl_sub_le_compat Hop Hor).
  now apply (rngl_mul_le_mono_nonpos_l Hop Hor).
  apply (rngl_mul_le_mono_nonpos_l Hop Hor); [ easy | ].
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1; move θ1 after θ2.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs13, Hzs12.
do 2 rewrite <- (angle_add_sub_swap Hic Hop).
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs13, Hzs12, Hs1z.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hc1z.
do 2 rewrite (rngl_cos_sub_right_r Hon Hop).
apply (rngl_opp_neg_pos Hop Hor) in Hzs13, Hzs12.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs1z.
assert (Hs12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
  apply (rngl_lt_le_incl Hor) in Hc1z, Hzc2.
  now apply (rngl_sin_add_nonneg Hop).
}
assert (Hs13 : (0 ≤ rngl_sin (θ1 + θ3))%L). {
  apply (rngl_lt_le_incl Hor) in Hc1z, Hzc3.
  now apply (rngl_sin_add_nonneg Hop).
}
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply angle_add_le_mono_l_lemma_3; try easy.
progress unfold angle_add_overflow.
apply angle_ltb_ge.
progress unfold angle_leb.
generalize Hc1z; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hs13; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le.
apply angle_add_overflow_le_lemma_111; try easy.
now apply (rngl_lt_le_incl Hor).
Qed.

(* to be completed
Theorem angle_add_le_mono_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
    angle_add_overflow θ1 θ2 = false
    → angle_add_overflow θ1 θ3 = false
    → (θ2 ≤ θ3)%A ↔ (θ1 + θ2 ≤ θ1 + θ3)%A.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Haov13.
  progress unfold angle_leb.
  rewrite (H1 (rngl_sin θ2)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin θ3)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_cos θ3)), (H1 (rngl_cos θ2)).
  rewrite (rngl_leb_refl Hor).
  split; [ | easy ].
  intros _.
  rewrite (H1 (rngl_sin (θ1 + θ2))).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin (θ1 + θ3))).
  rewrite (rngl_leb_refl Hor).
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_leb_refl Hor).
}
intros * Haov12 Haov13.
split; intros H23. {
  progress unfold angle_leb in H23.
  progress unfold angle_leb.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  remember (0 ≤? rngl_sin (θ1 + θ3))%L as zs13 eqn:Hzs13.
  symmetry in Hzs2, Hzs3, Hzs12, Hzs13.
  move H23 at bottom.
  destruct zs12. {
    destruct zs13; [ | easy ].
    apply rngl_leb_le in Hzs12, Hzs13.
    apply rngl_leb_le.
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      destruct zs3. {
        apply rngl_leb_le in Hzs3, H23.
        now apply angle_add_le_mono_l_lemma_3.
      }
      clear H23.
      apply (rngl_leb_gt Hor) in Hzs3.
      destruct (rngl_lt_dec Hor (rngl_cos θ3) 0)%L as [Hc3z| Hzc3]. {
        exfalso.
        now apply angle_add_le_mono_l_lemma_11 in Hzs13.
      } {
        apply (rngl_nlt_ge Hor) in Hzc3.
        now apply angle_add_le_mono_l_lemma_7.
      }
    }
    destruct zs3; [ easy | ].
    apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
    apply rngl_leb_le in H23.
    destruct (rngl_lt_dec Hor (rngl_cos θ3) 0)%L as [Hc3z| Hzc3]. {
      exfalso.
      now apply angle_add_le_mono_l_lemma_11 in Hzs13.
    } {
      apply (rngl_nlt_ge Hor) in Hzc3.
      now apply angle_add_le_mono_l_lemma_16.
    }
  }
  apply (rngl_leb_gt Hor) in Hzs12.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    destruct zs3. {
      apply rngl_leb_le in Hzs3, H23.
      destruct zs13. {
        exfalso.
        apply rngl_leb_le in Hzs13.
        apply (rngl_nle_gt Hor) in Hzs12.
        apply Hzs12; clear Hzs12.
        now apply angle_add_le_mono_l_lemma_19 with (θ3 := θ3).
      }
      apply (rngl_leb_gt Hor) in Hzs13.
      apply rngl_leb_le.
      destruct (rngl_lt_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
        now apply angle_add_le_mono_l_lemma_20.
      }
      apply (rngl_nlt_ge Hor) in Hc3z.
(**)
      remember (θ3 - angle_right)%A as θ eqn:Hθ.
      apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
      subst θ3; rename θ into θ3; move θ3 before θ2.
      rewrite (angle_add_assoc Hop) in Hzs13 |-*.
      rewrite (rngl_sin_add_right_r Hon Hos) in Hzs3, Hzs13.
      rewrite (rngl_cos_add_right_r Hon Hop) in H23, Hc3z |-*.
      apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc3z.
      move Hc3z before Hzs2.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
        move Hzc2 after Hzs3.
        clear H23.
        destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
          move Hzs1 after Hzs2.
          destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
            exfalso.
            apply (rngl_nle_gt Hor) in Hzs12.
            apply Hzs12; clear Hzs12.
            now apply (rngl_sin_add_nonneg Hop).
          }
          apply (rngl_nle_gt Hor) in Hc1z.
          remember (θ1 - angle_right)%A as θ.
          apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
          subst θ1; rename θ into θ1; move θ1 after θ2.
          rewrite (angle_add_add_swap Hic Hop) in Hzs12, Hzs13.
          do 2 rewrite (angle_add_add_swap Hic Hop _ angle_right).
          rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs12 |-*.
          rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z, Hzs13 |-*.
          apply (rngl_opp_neg_pos Hop Hor) in Hc1z, Hzs13.
          apply -> (rngl_opp_le_compat Hop Hor).
          move Hc1z after Hzs2; move Hzs1 before Hzc2.
          destruct (rngl_le_dec Hor (rngl_cos (θ1 + θ3)) 0) as [H| Hzc13]. {
            eapply (rngl_le_trans Hor); [ apply H | ].
            apply (rngl_lt_le_incl Hor) in Hc1z.
            now apply (rngl_sin_add_nonneg Hop).
          }
          apply (rngl_nle_gt Hor) in Hzc13.
          move Hzc13 before Hzs13.
...
      remember (angle_straight - θ3)%A as θ.
      apply (angle_sub_move_l Hic Hon Hop Hed) in Heqθ.
      subst θ3; rename θ into θ3; move θ3 before θ2.
      rewrite (angle_add_comm Hic) in Hzs13.
      rewrite (angle_add_comm Hic _ (_ - _))%A.
      rewrite <- (angle_add_sub_swap Hic Hop) in Hzs13 |-*.
      rewrite <- (angle_add_sub_assoc Hop) in Hzs13 |-*.
      rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs3.
      rewrite (rngl_cos_sub_straight_l Hon Hop) in H23, Hc3z.
      rewrite (rngl_sin_add_straight_l Hon Hop) in Hzs13.
      rewrite (rngl_cos_add_straight_l Hon Hop).
      apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc3z.
      apply (rngl_le_opp_l Hop Hor) in H23.
      apply (rngl_opp_neg_pos Hop Hor) in Hzs13.
...
(*
assert (Hs32 : (rngl_sin θ3 ≤ rngl_sin θ2)%L).
...
*)
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
        destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
          destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
            exfalso.
            apply (rngl_nle_gt Hor) in Hzs12.
            apply Hzs12; clear Hzs12.
            now apply (rngl_sin_add_nonneg Hop).
          }
          apply (rngl_nle_gt Hor) in Hc1z.
(*
          remember (angle_straight - θ1)%A as θ.
          apply (angle_sub_move_l Hic Hon Hop Hed) in Heqθ.
          subst θ1; rename θ into θ1; move θ1 after θ2.
          rewrite <- (angle_add_sub_swap Hic Hop) in Hzs12 |-*.
          rewrite <- (angle_add_sub_assoc Hop) in Hzs12 |-*.
          rewrite <- (angle_sub_add_distr Hic Hop) in Hzs13 |-*.
          rewrite (rngl_sin_add_straight_l Hon Hop) in Hzs12.
          rewrite (rngl_cos_add_straight_l Hon Hop).
          rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs13, Hzs1.
          rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc1z |-*.
          apply (rngl_opp_neg_pos Hop Hor) in Hzs12, Hc1z.
          apply -> (rngl_opp_le_compat Hop Hor).
          apply (rngl_le_opp_l Hop Hor).
          cbn.
          rewrite (rngl_mul_opp_r Hop).
          rewrite (rngl_sub_opp_r Hop).
          rewrite rngl_add_assoc.
          rewrite <- (rngl_add_sub_swap Hop).
...
*)
          remember (θ1 - angle_right)%A as θ.
          apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
          subst θ1; rename θ into θ1; move θ1 after θ2.
          rewrite (angle_add_add_swap Hic Hop) in Hzs12 |-*.
          rewrite (angle_add_sub_swap Hic Hop) in Hzs13 |-*.
          rewrite (rngl_sin_add_right_r Hon Hos) in Hzs12, Hzs13, Hzs1.
          rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z.
          do 2 rewrite (rngl_cos_add_right_r Hon Hop).
          apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
          rewrite (rngl_opp_involutive Hop).
          apply (rngl_le_opp_l Hop Hor).
(*
enough (Hs32 : (rngl_sin θ3 ≤ rngl_sin θ2)%L).
*)
          destruct (rngl_le_dec Hor (rngl_sin θ3) (rngl_sin θ1))
              as [Hs31| Hs13]. {
            apply (rngl_add_nonneg_nonneg Hor). {
              apply (rngl_lt_le_incl Hor) in Hc1z.
              now apply (rngl_sin_add_nonneg Hop).
            } {
              apply (rngl_lt_le_incl Hor) in Hc1z.
              apply rngl_sin_nonneg_cos_le_sin_sub_nonneg; try easy.
              now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
            }
          }
          apply (rngl_nle_gt Hor) in Hs13.
          rewrite (rngl_sin_sub_anticomm Hic Hop).
          rewrite (rngl_cos_sub_comm Hic Hop) in Hzs13.
          rewrite (rngl_add_opp_r Hop).
          apply (rngl_le_0_sub Hop Hor).
          generalize Hs13; intros Hc31.
          apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff in Hc31;
              try easy.
          2: now apply (rngl_lt_le_incl Hor) in Hc1z.
...
Check rngl_sin_nonneg_cos_le_sin_le.
...
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy.
apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
apply rngl_sin_incr; try easy.
... ...
apply (rngl_sin_add_nonneg Hop); [ | easy | easy | easy ].
now apply (rngl_lt_le_incl Hor).
...

      destruct (rngl_le_dec Hor (rngl_sin θ2) (rngl_sin θ3))
          as [Hs23| Hs23]. {
...
clear H23.
          cbn.
          rewrite rngl_add_assoc.
          rewrite (rngl_add_add_swap (_ * _))%L.
          rewrite <- rngl_add_assoc.
          do 2 rewrite <- rngl_mul_add_distr_l.
          rewrite (rngl_add_opp_r Hop).
...
          rewrite (rngl_add_comm (rngl_cos θ2)).
          apply (rngl_add_nonneg_nonneg Hor). {
            apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
...
          rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12.
          do 2 rewrite (angle_add_add_swap Hic Hop _ angle_right).
          rewrite (rngl_sin_add_right_r Hon Hos) in Hzs12, Hzs1 |-*.
          rewrite (rngl_cos_add_right_r Hon Hop) in Hzs13, Hc1z |-*.
          apply (rngl_le_opp_l Hop Hor) in H23.
          apply (rngl_opp_neg_pos Hop Hor) in Hzs13, Hc1z.
          apply -> (rngl_opp_le_compat Hop Hor).
...
      remember (θ3 - angle_right)%A as θ eqn:Hθ.
      apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
      subst θ3; rename θ into θ3; move θ3 before θ2.
      rewrite (angle_add_assoc Hop) in Hzs13 |-*.
      rewrite (rngl_sin_add_right_r Hon Hos) in Hzs3, Hzs13.
      rewrite (rngl_cos_add_right_r Hon Hop) in H23, Hc3z |-*.
      apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc3z.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
        destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
          destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
            exfalso.
            apply (rngl_nle_gt Hor) in Hzs12.
            apply Hzs12; clear Hzs12; cbn.
            apply (rngl_add_nonneg_nonneg Hor).
            now apply (rngl_mul_nonneg_nonneg Hop Hor).
            now apply (rngl_mul_nonneg_nonneg Hop Hor).
          }
          apply (rngl_nle_gt Hor) in Hc1z.
(*
          remember (angle_straight - θ1)%A as θ.
          apply (angle_sub_move_l Hic Hon Hop Hed) in Heqθ.
          subst θ1; rename θ into θ1; move θ1 after θ2.
          rewrite <- (angle_sub_sub_distr Hic Hop) in Hzs13, Hzs12.
          do 2 rewrite <- (angle_sub_sub_distr Hic Hop).
          rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs12, Hzs1 |-*.
          rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzs13, Hc1z |-*.
...
          remember (θ1 - angle_right)%A as θ.
          apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
          subst θ1; rename θ into θ1; move θ1 after θ2.
          rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12.
          do 2 rewrite (angle_add_add_swap Hic Hop _ angle_right).
          rewrite (rngl_sin_add_right_r Hon Hos) in Hzs12, Hzs1 |-*.
          rewrite (rngl_cos_add_right_r Hon Hop) in Hzs13, Hc1z |-*.
          apply (rngl_le_opp_l Hop Hor) in H23.
          apply (rngl_opp_neg_pos Hop Hor) in Hzs13, Hc1z.
          apply -> (rngl_opp_le_compat Hop Hor).
*)
...
intros Hic Hon Hop Hed * Haov12 Haov13.
split; intros H23. {
  apply (angle_le_sub_le_add_l Hic Hon Hop Hed); [ easy | | | ]; cycle 1. {
    progress unfold angle_add_overflow in Haov12.
    now apply angle_ltb_ge in Haov12.
  } {
    rewrite (angle_add_comm Hic).
    now rewrite (angle_add_sub Hic Hon Hop Hed).
  }
  progress unfold angle_add_overflow in Haov12.
  apply angle_ltb_ge in Haov12.
  progress unfold angle_add_overflow.
  rewrite angle_add_opp_r.
  rewrite (angle_add_comm Hic).
  rewrite (angle_add_sub Hic Hon Hop Hed).
  apply angle_ltb_ge.
(**)
  progress unfold angle_leb in Haov12.
  progress unfold angle_leb.
  rewrite (angle_add_comm Hic).
  remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  symmetry in Hzs1, Hzs2, Hzs12.
  destruct zs12. {
    apply rngl_leb_le in Hzs12.
    destruct zs2; [ | easy ].
    apply rngl_leb_le in Hzs2.
    apply rngl_leb_le.
    destruct zs1; [ | easy ].
    apply rngl_leb_le in Haov12.
    apply rngl_leb_le in Hzs1.
    move Hzs2 before Hzs1.
(* bobo ! *)
...
intros Hic Hon Hop Hed * Haov12 Haov13.
split; intros H23. {
  do 2 rewrite (angle_add_comm Hic θ1).
  apply (angle_le_sub_le_add_l Hic Hon Hop Hed); cycle 1. {
    progress unfold angle_add_overflow in Haov12.
    apply angle_ltb_ge in Haov12.
    progress unfold angle_add_overflow.
    rewrite angle_add_opp_r.
    rewrite (angle_add_comm Hic).
    apply angle_ltb_ge.
    progress unfold angle_leb.
    (* faut voir mais bof *)
...
intros Hic Hon Hop Hed * Haov12 Haov13.
split; intros H23. {
  rewrite (angle_add_comm Hic θ1 θ2).
  apply (angle_le_sub_le_add_l Hic Hon Hop Hed); [ easy | | | ]. {
    progress unfold angle_add_overflow in Haov12.
    apply angle_ltb_ge in Haov12.
    progress unfold angle_add_overflow.
    rewrite angle_add_opp_r.
    rewrite (angle_add_sub Hic Hon Hop Hed).
    apply angle_ltb_ge.
    progress unfold angle_leb.
...
(*
Theorem angle_add_overflow_comm :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, angle_add_overflow θ1 θ2 = angle_add_overflow θ2 θ1.
Proof.
intros Hic Hon Hop Hed *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold angle_add_overflow.
remember (θ1 =? 0)%A as z1 eqn:Hz1.
symmetry in Hz1.
destruct z1. {
  apply (angle_eqb_eq Hed) in Hz1.
  subst θ1; cbn.
  rewrite (angle_add_0_l Hon Hos).
  rewrite (angle_add_0_r Hon Hos).
  remember (θ2 =? 0)%A as z2 eqn:Hz2.
  remember (- θ2 ≤? 0)%A as o2z eqn:Ho2z.
  symmetry in Hz2, Ho2z.
  destruct z2.
...
  destruct z2; [ easy | ].
  destruct o2z; [ exfalso | easy ].
  apply (angle_eqb_neq Hed) in Hz2.
  apply (angle_le_0_r Hic Hon Hop Hed) in Ho2z.
  rewrite <- (angle_opp_0 Hop) in Ho2z.
  now apply angle_opp_inj in Ho2z.
}
cbn.
apply (angle_eqb_neq Hed) in Hz1.
remember (θ2 =? 0)%A as z2 eqn:Hz2.
symmetry in Hz2.
destruct z2; cbn. {
  apply (angle_eqb_eq Hed) in Hz2.
  subst θ2.
  apply Bool.not_true_iff_false.
  intros H.
  apply (angle_le_0_r Hic Hon Hop Hed) in H.
  rewrite <- (angle_opp_0 Hop) in H.
  now apply (angle_opp_inj Hop) in H.
}
apply (angle_eqb_neq Hed) in Hz2.
remember (- θ1 ≤? θ2)%A as o12 eqn:Ho12.
remember (- θ2 ≤? θ1)%A as o21 eqn:Ho21.
symmetry in Ho12, Ho21.
destruct o12. {
  destruct o21; [ easy | exfalso ].
  apply angle_leb_nle in Ho21.
  apply Ho21; clear Ho21.
  apply (angle_opp_le_compat Hic Hon Hop Hed); [ | easy | ]. {
    intros H.
    apply (f_equal angle_opp) in H.
    rewrite (angle_opp_involutive Hop) in H.
    now rewrite (angle_opp_0 Hop) in H.
  }
  now rewrite (angle_opp_involutive Hop).
} {
  destruct o21; [ exfalso | easy ].
  apply angle_leb_nle in Ho12.
  apply Ho12; clear Ho12.
  apply (angle_opp_le_compat Hic Hon Hop Hed); [ | easy | ]. {
    intros H.
    apply (f_equal angle_opp) in H.
    rewrite (angle_opp_involutive Hop) in H.
    now rewrite (angle_opp_0 Hop) in H.
  }
  now rewrite (angle_opp_involutive Hop).
}
Qed.
...
*)
Theorem angle_add_overflow_comm :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2, angle_add_overflow θ1 θ2 = angle_add_overflow θ2 θ1.
Proof.
intros Hic Hon Hop.
destruct ac as (Hiv, Hc2, Hor).
intros.
remember (angle_add_overflow _ _) as o12 eqn:Ho12.
remember (angle_add_overflow _ _) as o21 eqn:Ho21 in |-*.
symmetry in Ho12, Ho21.
destruct o12. {
  destruct o21; [ easy | exfalso ].
  progress unfold angle_add_overflow in Ho12.
  progress unfold angle_add_overflow in Ho21.
  apply (angle_ltb_ge) in Ho21.
  apply angle_nlt_ge in Ho21.
  apply Ho21; clear Ho21.
  progress unfold angle_ltb in Ho12.
  progress unfold angle_ltb.
  rewrite (angle_add_comm Hic).
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  symmetry in Hzs12, Hzs1, Hzs2.
  move Hzs2 before Hzs1.
  destruct zs12. {
    apply rngl_leb_le in Hzs12.
    destruct zs2; [ | easy ].
    apply rngl_leb_le in Hzs2.
    apply rngl_ltb_lt.
    destruct zs1. {
      apply rngl_leb_le in Hzs1.
      apply rngl_ltb_lt in Ho12.
      destruct (rngl_le_dec Hor (rngl_cos θ2) (rngl_cos θ1)) as [H21| H12]. {
        now apply (rngl_le_lt_trans Hor _ (rngl_cos θ1)).
      }
      apply (rngl_nle_gt Hor) in H12.
      apply (rngl_nle_gt Hor).
      intros Hc12.
...
      apply (rngl_nle_gt Hor) in Ho12.
      apply Ho12; clear Ho12; cbn.
      apply (rngl_le_sub_le_add_l Hop Hor).
      apply (rngl_le_sub_le_add_r Hop Hor).
      rewrite (rngl_sub_mul_l_diag_l Hon Hop).
      apply (rngl_nlt_ge Hor).
      intros Hss.
      apply (rngl_nlt_ge Hor) in Hc12.
      apply Hc12; clear Hc12; cbn.
      apply (rngl_lt_add_lt_sub_r Hop Hor).
      apply (rngl_lt_add_lt_sub_l Hop Hor).
      rewrite (rngl_sub_mul_l_diag_r Hon Hop).
      apply (rngl_nle_gt Hor).
      intros Hc12.
...
progress unfold angle_add_overflow.
rewrite (angle_add_comm Hic).
progress unfold angle_ltb.
remember (0 ≤? rngl_sin (θ2 + θ1))%L as zs21 eqn:Hzs21.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs21, Hzs1, Hzs2.
destruct zs21. {
  apply rngl_leb_le in Hzs21.
  destruct zs1. {
    apply rngl_leb_le in Hzs1.
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
...
    progress unfold angle_add_overflow.
    apply angle_ltb_ge.
    rewrite angle_add_opp_r.
    rewrite (angle_add_comm Hic).
    rewrite (angle_add_sub Hic Hon Hop Hed).
...
*)

(* to be completed
Theorem angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_archimedean T = true →
  rngl_has_eq_dec T = true →
  rngl_characteristic T = 0 →
  ∀ n θ,
  n ≠ 0
  → angle_mul_nat_overflow n θ = false
  → is_angle_eucl_limit_when_tending_to_inf
      (seq_angle_converging_to_angle_div_nat (n * θ) n) θ.
Proof.
intros Hic Hon Hop Har Hed Hch * Hnz Haov.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite Hc1 in Hch.
}
assert (H02 : (0 ≤ 2)%L). {
  apply (rngl_lt_le_incl Hor), (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
progress unfold seq_angle_converging_to_angle_div_nat.
enough (H :
  is_angle_eucl_limit_when_tending_to_inf
    (λ i, (2 ^ i mod n * angle_div_2_pow_nat θ i))%A 0%A). {
  progress unfold is_angle_eucl_limit_when_tending_to_inf.
  progress unfold is_limit_when_tending_to_inf.
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros i Hi.
  rewrite (angle_div_2_pow_nat_mul Hic Hon Hop Hed); [ | easy | easy ].
  rewrite (angle_mul_nat_assoc Hon Hop).
  specialize (Nat.div_mod_eq (2 ^ i) n) as H1.
  symmetry in H1.
  apply Nat.add_sub_eq_r in H1.
  symmetry in H1.
  rewrite Nat.mul_comm in H1.
  rewrite H1; clear H1.
  rewrite (angle_mul_sub_distr_r Hic Hon Hop Hed); [ | now apply Nat.mod_le ].
  rewrite (angle_mul_2_pow_div_2_pow Hic Hon Hop Hed).
  rewrite (angle_eucl_dist_sub_l_diag Hic Hon Hop Hed).
  now apply HN.
}
enough (H :
  is_angle_eucl_limit_when_tending_to_inf
    (λ i, (n * angle_div_2_pow_nat θ i))%A 0%A). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros i Hi.
  eapply (rngl_le_lt_trans Hor); [ | now apply (HN i) ].
  progress unfold angle_eucl_dist.
  cbn.
  do 2 rewrite (rngl_sub_0_l Hop).
  do 2 rewrite (rngl_squ_opp Hop).
  remember (angle_div_2_pow_nat θ i) as Δθ.
  do 2 rewrite (one_sub_squ_cos_add_squ_sin Hic Hon Hop Hed).
  rewrite rl_sqrt_mul; [ | easy | easy ].
  rewrite rl_sqrt_mul; [ | easy | easy ].
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ now apply rl_sqrt_nonneg | ].
  rewrite <- (rngl_abs_nonneg_eq Hop Hor); [ | now apply rl_sqrt_nonneg ].
  rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L; [ | now apply rl_sqrt_nonneg ].
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  rewrite rngl_squ_sqrt; [ | easy ].
  rewrite rngl_squ_sqrt; [ | easy ].
  apply (rngl_sub_le_mono_l Hop Hor).
  apply rngl_cos_decr.
Theorem angle_mul_nat_le_mono_nonneg_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ a b θ, angle_mul_nat_overflow b θ = false → a ≤ b → (a * θ ≤ b * θ)%A.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hb Hab.
revert a Hab.
induction b; intros. {
  apply Nat.le_0_r in Hab; subst a.
  apply (angle_leb_refl).
}
destruct a; [ apply (angle_nonneg Hic Hon Hop Hed) | cbn ].
move a after b.
apply Nat.succ_le_mono in Hab.
apply (angle_mul_nat_overflow_succ_l_false Hon Hos θ b) in Hb.
destruct Hb as (H1, H2).
specialize (IHb H1 _ Hab).
(*
apply angle_le_sub_le_add_l; try easy; cycle 2. {
  rewrite (angle_add_sub_swap Hic Hop).
  rewrite (angle_sub_diag Hic Hon Hop Hed).
  now rewrite (angle_add_0_l Hon Hos).
} {
  progress unfold angle_add_overflow.
  rewrite angle_add_opp_r.
  rewrite (angle_add_sub_swap Hic Hop).
  rewrite (angle_sub_diag Hic Hon Hop Hed).
  apply angle_ltb_ge.
  apply angle_leb_refl.
*)
... ...
apply angle_add_le_mono_l; try easy.
... ...
now apply (angle_add_overflow_le Hic Hon Hop Hed _ (b * θ))%A.
...
progress unfold angle_add_overflow in H2.
progress unfold angle_add_overflow.
apply angle_ltb_ge in H2.
apply angle_ltb_ge.
progress unfold angle_leb in H2.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ)%L as zst eqn:Hzst.
symmetry in Hzst.
destruct zst. {
  apply rngl_leb_le in Hzst.
  remember (0 ≤? rngl_sin (θ + (a * θ)%A))%L as zsta eqn:Hzsta.
  remember (0 ≤? rngl_sin (θ + (b * θ)%A))%L as zstb eqn:Hzstb.
  symmetry in Hzsta, Hzstb.
  destruct zsta; [ | easy ].
  apply rngl_leb_le.
  apply rngl_leb_le in Hzsta.
  destruct zstb. {
    apply rngl_leb_le in Hzstb.
    apply rngl_leb_le in H2.
    move Hzsta after Hzstb.
    eapply (rngl_le_trans Hor); [ | apply H2 ].
(*
Search (rngl_cos (_ + _) ≤ rngl_cos (_ + _))%L.
Search (rngl_cos _ ≤ rngl_cos _)%L.
*)
specialize rngl_sin_nonneg_cos_le_sin_le as H3.
specialize (H3 Hic Hon Hop Hed).
specialize (H3 _ _ Hzstb Hzst H2).
Search angle_mul_nat_overflow.
...
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
Search (rngl_cos _ < rngl_cos _)%L.
...
    cbn.
...

Theorem angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_archimedean T = true →
  rngl_has_eq_dec T = true →
  rngl_characteristic T = 0 →
  ∀ i θ θ',
  i ≠ 0
  → is_angle_limit_when_tending_to_inf
       (seq_angle_converging_to_angle_div_nat θ i) θ'
  → θ = (i * θ')%A.
Proof.
(**)
intros Hic Hon Hop Har Hed Hch * Hiz Hlim.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
progress unfold is_angle_limit_when_tending_to_inf in Hlim.
progress unfold is_gen_limit_when_tending_to_inf in Hlim.
progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
assert
  (H :
    ∀ ε : T, (0 < ε)%L →
      ∃ N : nat, ∀ n : nat, N ≤ n →
      (angle_dist θ θ' < ε)%L). {
  intros ε Hε.
  specialize (Hlim ε Hε).
  destruct Hlim as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  specialize (Nat.div_mod_eq (2 ^ n) i) as H1.
  symmetry in H1.
  apply Nat.add_sub_eq_r in H1.
  apply (f_equal rngl_of_nat) in H1.
  rewrite (rngl_of_nat_mul Hon Hos) in H1.
  symmetry in H1.
  apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
    intros Hi.
    now apply (eq_rngl_of_nat_0 Hon Hch) in Hi.
  }
...
Fixpoint rngl_to_nat :
  ∀ a,
...
Check rngl_mul_move_l.
Check rngl_mul_move_r.
...
Search (_ * _ = _)%L.
...
Search (_ = _ * _)%L.
...
Search ((_ * _) * _)%A.
progress unfold angle_dist in HN.
Search (rngl_cos (_ * _)%A).
Inspect 8.
...
rat_is_inf_sum_of_inv_rad_pow.
...
(**)
intros Hic Hon Hop Har Hed Hch * Hiz Hlim.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
revert θ θ' Hlim.
induction i; intros; [ easy | ].
clear Hiz.
destruct i. {
  clear IHi; cbn.
  rewrite (angle_add_0_r Hon Hos).
  progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
  assert (H : is_angle_limit_when_tending_to_inf (λ _, θ) θ'). {
    intros ε Hε.
    specialize (Hlim ε Hε).
    destruct Hlim as (N, HN).
    exists N.
    intros n Hn.
    specialize (HN n Hn).
    rewrite Nat.div_1_r in HN.
    now rewrite angle_mul_2_pow_div_2_pow in HN.
  }
  clear Hlim; rename H into Hlim.
  progress unfold is_angle_limit_when_tending_to_inf in Hlim.
  specialize (angle_dist_is_dist Hic Hon Hop Hed) as H1.
  specialize (gen_limit_unique Hon Hop Hiv Hor _ _ H1) as H2.
  specialize (H2 (λ _, θ) θ' θ Hlim).
  symmetry.
  apply H2.
  intros ε Hε.
  exists 0.
  intros n Hn.
  now rewrite dist_refl.
}
specialize (IHi (Nat.neq_succ_0 _)).
(**)
destruct i. {
  clear IHi; cbn.
  rewrite (angle_add_0_r Hon Hos).
  progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
  assert (H : is_angle_limit_when_tending_to_inf (λ _, θ) (2 * θ')%A). {
    intros ε Hε.
enough (H2ε : (0 < 2 * ε)%L).
    specialize (Hlim (2 * ε)%L H2ε).
    destruct Hlim as (N, HN).
    exists (N - 1). (* au pif *)
    intros n Hn.
    apply Nat.le_sub_le_add_r in Hn.
    specialize (HN (n + 1) Hn).
    rewrite Nat.add_1_r in HN.
    rewrite Nat.pow_succ_r in HN; [ | easy ].
    rewrite Nat.mul_comm in HN.
    rewrite Nat.div_mul in HN; [ | easy ].
    cbn in HN.
    rewrite (angle_mul_2_pow_div_2_pow Hic Hon Hop Hed) in HN.
    progress unfold angle_dist in HN.
    progress unfold angle_dist.
    rewrite (rngl_cos_mul_2_l Hon Hos).
    rewrite (rngl_sin_mul_2_l Hic Hon Hos).
...
    rewrite Nat.mul_div in HN.
    rewrite Nat.pow_add_r in HN.
    rewrite
Search (_ ^ (_ + _)).
    rewrite Nat.add_
    destruct n. {
...
    rewrite angle_mul_2_pow_div_2_pow in HN.
...
remember (S n) as sn; cbn; subst sn.
rewrite (angle_add_comm Hic).
apply (angle_sub_move_r Hic Hon Hop Hed).
apply IHn.
progress unfold seq_angle_converging_to_angle_div_nat.
progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
...
Search (rngl_of_nat _ = 0%L).
  rewrite rngl_of_nat_succ.
...
intros Hic Hon Hop Har Hed * Hnz Hlim.
(*
progress unfold is_angle_upper_limit_when_tending_to_inf in Hlim.
Check rat_is_inf_sum_of_inv_rad_pow.
*)
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
move Hos before Hed.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
move Hi1 before Hos.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
move Hid before Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 _) in Hnz.
}
move Hc1 before Hid.
move α before θ.
specialize (rat_is_inf_sum_of_inv_rad_pow Hic Hon Hop Hiv Har) as H1.
specialize (H1 2 1 n (le_refl _) Hnz).
progress unfold is_limit_when_tending_to_inf in H1.
progress unfold seq_converging_to_rat in H1.
progress unfold seq_angle_converging_to_angle_div_nat.
Search angle_dist.
...
progress unfold angle_lt in Hα.
progress unfold angle_compare in Hα.
progress unfold rngl_compare in Hα.
cbn in Hα.
rewrite (rngl_leb_refl Hor) in Hα.
remember (0 ≤? rngl_sin α)%L as zs eqn:Hzs; symmetry in Hzs.
destruct zs. {
  apply rngl_leb_le in Hzs.
  remember (rngl_cos α =? 1)%L as ce1 eqn:Hce1; symmetry in Hce1.
  destruct ce1; [ easy | ].
  apply (rngl_eqb_neq Hed) in Hce1.
  remember (rngl_cos α ≤? 1)%L as cl1 eqn:Hcl1; symmetry in Hcl1.
  destruct cl1; [ clear Hα | easy ].
  apply rngl_leb_le in Hcl1.
  specialize (H1 (rngl_sin (angle_div_2 Hiv Hc2 Hor α))).
  assert (H : (0 < rngl_sin (angle_div_2 Hiv Hc2 Hor α))%L). {
    progress unfold angle_div_2.
    cbn.
    rewrite <- (rl_sqrt_0 Hor Hop Hic Hid).
    apply (rl_sqrt_lt_rl_sqrt Hic Hop). {
      apply (rngl_le_refl Hor).
    }
    apply (rngl_div_lt_pos Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    apply (rngl_lt_0_sub Hop Hor).
    now apply (rngl_lt_iff Hor).
  }
  specialize (H1 H); clear H.
  destruct H1 as (N, HN).
  exists N. (* au pif *)
  intros m Hm.
...
rewrite (rngl_squ_mul Hic) in H2.
rewrite <- rngl_squ
Search (√_ * √_)%L.
Search (√_)%L.
...
apply (rngl_mul_le_compat Hop Hor) with (b := √b%L) (d := √a%L).
apply (rngl_
Search (_ * _ < _ * _)%Z.
...
apply (rngl_mul_lt_mono_pos_r Hop Hor Hi1) with (a := √(
...
apply rl_sqrt_lt_rl_sqrt.
Search (_ < √ _)%L.
Search (rngl_squ _ < rngl_squ _)%L.
Search (rngl_squ _ ≤ rngl_squ _)%L.
Search (rngl_abs (√ _))%L.
Search (√ 0)%L.
...
    apply (rngl_div_lt_pos).
...

Definition angle_div_nat θ n :=
  {| rngl_cos := 1; rngl_sin := 0;
     rngl_cos2_sin2 := 42 |}%L.
...

Theorem all_gc_has_nth_root :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 2 →
  rl_has_integral_modulus T = true →
  ∀ n, n ≠ 0 → ∀ z : GComplex T, ∃ x : GComplex T, gc_power_nat x n = z.
Proof.
intros Hic Hon Hop Hiv Hed Hor Hc2 Him * Hnz *.
specialize (polar Hic Hon Hop Hiv Hed Hc2 Him Hor z) as H1.
set (ρ := √((gre z)² + (gim z)²)%L).
set
  (θ :=
     (if (0 ≤? gim z)%L then rl_acos Hor (gre z / ρ)%L
      else angle_opp (rl_acos Hor (gre z / ρ)%L))).
specialize (H1 ρ θ eq_refl eq_refl).
set (ρ' := rl_nth_root n ρ).
...
set (θ' := angle_div_nat θ n).
exists (mk_gc (ρ' * cos θ') (ρ' * sin θ')).
...
assert (Hre : (-1 ≤ gre z / ρ ≤ 1)%L). {
  subst ρ.
... ...
apply rl_sqrt_div_squ_squ.
}
...
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hiz| Hiz]. {
  rewrite (rl_cos_acos Htr).
...
  rewrite (rngl_mul_div_r Hon Hic Hiv). 2: {
    subst ρ.
    progress unfold rl_sqrt.
    progress unfold rl_pow.
    rewrite if_bool_if_dec.
    destruct (Sumbool.sumbool_of_bool _) as [H2| H2]. {
      apply (rngl_eqb_eq Heb) in H2.
      generalize Hmi; intros H.
      progress unfold rl_has_integral_modulus in H.
      remember (rl_opt_mod_intgl_prop T) as mi eqn:Hmi1.
      symmetry in Hmi1.
      destruct mi as [mi| ]; [ clear H | easy ].
      apply mi in H2.
      apply (neq_neq_GComplex Heb) in Hz.
      cbn in Hz.
      now destruct Hz.
    }
    apply (rngl_eqb_neq Heb) in H2.
    apply (rl_exp_neq_0 Hon Hop Hiv H10 Htr).
  }
...
Theorem rl_sin_acos {T} {ro : ring_like_op T} {rp : ring_like_prop T}
  {rl : real_like_prop T} :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_has_eq_dec T = true →
  rngl_is_ordered = true →
  rl_has_trigo = true →
  ∀ x, (-1 ≤ x ≤ 1)%L →
  rl_sin (rl_acos x) = rl_sqrt (1%L - rngl_squ x).
Proof.
intros * Hon Hop Hiv Hc2 Heb Hor Htr * Hx1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rl_cos2_sin2 Htr (rl_acos x)) as H1.
rewrite (rl_cos_acos Htr _ Hx1) in H1.
apply (rngl_add_sub_eq_l Hos) in H1.
rewrite H1.
rewrite (rl_sqrt_squ Hon Hop Hiv Hc2 Heb Hor Htr).
(* acos est dans [0,Π[, donc sin est >0 *)
...
Theorem rl_sin_acos {T} {ro : ring_like_op T} {rp : ring_like_prop T}
  {rl : real_like_prop T} :
  ∀ x, rl_sin (rl_acos x) = rl_sqrt (1 - rngl_squ x)%L.
... ...
rewrite rl_sin_acos.
...
rewrite (rl_cos_atan2 Htr).
rewrite <- Hρ.
rewrite (rngl_mul_div_r Hon Hic Hiv). 2: {
  subst ρ.
  progress unfold rl_sqrt.
  progress unfold rl_pow.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H2| H2]. {
    apply (rngl_eqb_eq Heb) in H2.
    generalize Hmi; intros H.
    progress unfold rl_has_integral_modulus in H.
    remember (rl_opt_mod_intgl_prop T) as mi eqn:Hmi1.
    symmetry in Hmi1.
    destruct mi as [mi| ]; [ clear H | easy ].
    apply mi in H2.
    apply (neq_neq_GComplex Heb) in Hz.
    cbn in Hz.
    now destruct Hz.
  }
  apply (rngl_eqb_neq Heb) in H2.
  apply (rl_exp_neq_0 Hon Hop Hiv H10 Htr).
}
Check rl_cos_atan2.
Theorem rl_sin_atan2 {T} {ro : ring_like_op T} {rp : ring_like_prop T}
  {rl : real_like_prop T} :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_has_eq_dec T = true →
  rngl_is_ordered = true →
  rl_has_trigo = true →
  ∀ x y, rl_sin (rl_atan2 y x) = (y / rl_sqrt (rngl_squ x + rngl_squ y))%L.
Proof.
intros * Hon Hop Hiv Hc2 Heb Hor Htr *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rl_cos2_sin2 Htr (rl_atan2 y x)) as H1.
rewrite (rl_cos_atan2 Htr) in H1.
apply (rngl_add_sub_eq_l Hos) in H1.
remember (rl_sqrt _) as ρ eqn:Hρ.
...
specialize (rl_cos2_sin2 Htr (rl_acos x)) as H1.
rewrite (rl_cos_acos Htr) in H1.
apply (rngl_add_sub_eq_l Hos) in H1.
rewrite H1.
rewrite (rl_sqrt_squ Hon Hop Hiv Hc2 Heb Hor Hle Htr).
(* acos est dans [0,Π[, donc sin est >0 *)
...

Theorem polyn_modl_tends_tow_inf_when_var_modl_tends_tow_inf {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T} :
  let roc := gc_ring_like_op T in
  rngl_has_opp T = true →
  rngl_has_inv (GComplex T) = true →
  rngl_has_1 (GComplex T) = true →
  ∀ la, 1 < length la → llast la 0%L ≠ 0%L →
  ∀ mz, ∃ z₀, ∀ z, (gc_modl z₀ ≤ gc_modl z →
  mz ≤ gc_modl (rngl_eval_polyn la z))%L.
Proof.
intros * Hop Hivc Honc * Hla Hl1 *.
...
*)

(* to be completed
Theorem gc_opt_alg_closed :
  let ro := gc_ring_like_op T in
  if (rngl_has_opp T && rngl_has_inv (GComplex T) &&
      rngl_has_1 (GComplex T))%bool
  then
     ∀ l : list (GComplex T), 1 < length l → List.last l 0%L ≠ 0%L →
     ∃ x : GComplex T, rngl_eval_polyn l x = 0%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
destruct op; [ | easy ].
remember (rngl_has_inv (GComplex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 (GComplex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ cbn | easy ].
intros la Hla Hl1.
*)

End a.

(* to be completed
Definition gc_ring_like_prop T
  {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T}
  {roc : ring_like_op (GComplex T)}
  (Hop : rngl_has_opp T = true) :
    @ring_like_prop (GComplex T) (gc_ring_like_op T) :=
  let Hos := rngl_has_opp_has_opp_or_subt Hop in
  let Hsu := rngl_has_opp_has_no_subt Hop in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_integral_domain := false;
     rngl_is_archimedean := false;
     rngl_is_alg_closed :=
       (rngl_has_opp T && rngl_has_inv (GComplex T) &&
        rngl_has_1 (GComplex T))%bool;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := gc_add_comm;
     rngl_add_assoc := gc_add_assoc;
     rngl_add_0_l := gc_add_0_l;
     rngl_mul_assoc := gc_mul_assoc Hop;
     rngl_opt_mul_1_l := gc_opt_mul_1_l Hos;
     rngl_mul_add_distr_l := gc_mul_add_distr_l Hop;
     rngl_opt_mul_comm := gc_opt_mul_comm;
     rngl_opt_mul_1_r := gc_opt_mul_1_r Hos;
     rngl_opt_mul_add_distr_r := gc_opt_mul_add_distr_r Hop;
     rngl_opt_add_opp_diag_l := gc_opt_add_opp_diag_l Hop;
     rngl_opt_add_sub := gc_opt_add_sub Hsu;
     rngl_opt_sub_add_distr := gc_opt_sub_add_distr Hsu;
     rngl_opt_mul_inv_diag_l := gc_opt_mul_inv_diag_l Hop;
     rngl_opt_mul_inv_diag_r := gc_opt_mul_inv_diag_r;
     rngl_opt_mul_div := gc_opt_mul_div;
     rngl_opt_mul_quot_r := gc_opt_mul_quot_r;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := gc_opt_alg_closed;
     rngl_characteristic_prop := gc_characteristic_prop;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA;
     rngl_opt_archimedean := NA |}.
*)
