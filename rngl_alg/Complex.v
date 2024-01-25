(* Real-Like numbers *)
(* Algebraic structure having the same properties as real numbers *)
(* and complex numbers *)
(* see also Quaternions.v *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Init.Nat.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike Main.IterAdd.
Require Import Misc.
Require Import RealLike TrigoWithoutPi.
Require Import AngleAddOverflowLe AngleAddLeMonoL.
Require Import AngleDiv2Add.
Require Import TacChangeAngle.

Notation "x ≤ y" := (Z.le x y) : Z_scope.

(* general complex whose real and imaginary parts are of type T
   that is not necessarily the real numbers *)

Class GComplex T := mk_gc {gre : T; gim : T}.

Declare Scope gc_scope.
Delimit Scope gc_scope with C.
Bind Scope gc_scope with GComplex.

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

Definition rl_acos Hor (x : T) :=
  match (rngl_le_dec Hor x² 1)%L with
  | left Hx1 =>
      {| rngl_cos := x; rngl_sin := rl_sqrt (1 - rngl_squ x)%L;
         rngl_cos2_sin2 := rl_acos_prop Hor x Hx1 |}
  | _ =>
      angle_zero
  end.

Theorem rl_cos_acos :
  ∀ Hor : rngl_is_ordered T = true,
  ∀ x, (x² ≤ 1)%L → rngl_cos (rl_acos Hor x) = x.
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

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

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

Fixpoint angle_div_2_pow_nat θ i :=
  match i with
  | 0 => θ
  | S i' => angle_div_2 (angle_div_2_pow_nat θ i')
  end.

Fixpoint angle_mul_nat_overflow n θ :=
  match n with
  | 0 | 1 => false
  | S n' =>
      (angle_add_overflow θ (n' * θ) ||
       angle_mul_nat_overflow n' θ)%bool
  end.

Theorem angle_mul_2_pow_div_2_pow :
  ∀ n θ, (2 ^ n * angle_div_2_pow_nat θ n)%A = θ.
Proof.
destruct_ac; intros.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
induction n; intros; [ apply angle_add_0_r | ].
cbn - [ "^" ].
rewrite Nat.pow_succ_r; [ | easy ].
rewrite Nat.mul_comm.
rewrite <- (angle_mul_nat_assoc Hon Hop).
rewrite angle_div_2_mul_2.
apply IHn.
Qed.

Theorem angle_mul_2_div_2 :
  ∀ a,
  angle_div_2 (angle_mul_nat a 2) =
    if angle_ltb a angle_straight then a else angle_add a angle_straight.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros.
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
  apply cos2_sin2_prop_add_squ in Ha.
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
    specialize rngl_cos_proj_bound as H1.
    specialize (H1 _ _ Ha).
    apply (rngl_le_antisymm Hor) in Hap; [ | easy ].
    subst ca; clear H1.
    apply cos2_sin2_prop_add_squ in Ha.
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
    apply cos2_sin2_prop_add_squ in Ha.
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
  rl_has_integral_modulus T = true →
  ∀ a : GComplex T, a ≠ 0%L →
  gre a⁻¹ = (gre a / (gre a * gre a + gim a * gim a))%L.
Proof.
intros * Hrl * Haz.
destruct_ac.
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
  rl_has_integral_modulus T = true →
  ∀ a : GComplex T, a ≠ 0%L →
  gim a⁻¹ = (- gim a / (gre a * gre a + gim a * gim a))%L.
Proof.
intros * Hrl * Haz.
destruct_ac.
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
  if (rngl_has_inv (GComplex T) && rngl_has_1 (GComplex T))%bool then
    ∀ a : GComplex T, a ≠ 0%L → (a⁻¹ * a)%L = 1%L
  else not_applicable.
Proof.
destruct_ac.
remember (rl_has_integral_modulus T) as hrl eqn:Hrl; symmetry in Hrl.
destruct hrl. 2: {
  progress unfold rngl_inv; cbn.
  progress unfold gc_opt_inv_or_quot; cbn.
  progress unfold rngl_has_inv; cbn.
  progress unfold gc_opt_inv_or_quot; cbn.
  rewrite Hrl.
  destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
  destruct iq as [inv| quot]; [ | easy ].
  now rewrite Hic.
}
intros.
remember (rngl_has_inv (GComplex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 (GComplex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ cbn | easy ].
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haz.
apply eq_gc_eq; cbn.
specialize (rngl_mul_inv_diag_l Hon Hiv) as H1.
rewrite (gc_inv_re Hrl); [ | now intros H; subst a ].
rewrite (gc_inv_im Hrl); [ | now intros H; subst a ].
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
specialize rngl_opt_characteristic_prop as H1.
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
  ∀ a b, (0 ≤ b → a ≤ rl_sqrt (rngl_squ a + b))%L.
Proof.
destruct_ac.
intros * Hzb.
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
  rl_has_integral_modulus T = true →
  ∀ x y, (x ≠ 0 ∨ y ≠ 0)%L →
  (-1 ≤ x / rl_sqrt (rngl_squ x + rngl_squ y) ≤ 1)%L.
Proof.
intros Hmi * Hxyz.
destruct_ac.
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
    apply le_rl_sqrt_add.
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
    apply le_rl_sqrt_add.
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
  rl_has_integral_modulus T = true →
  ∀ (z : GComplex T) ρ θ,
  ρ = √((gre z)² + (gim z)²)%L
  → θ =
       (if (0 ≤? gim z)%L then rl_acos ac_or (gre z / ρ)%L
        else angle_opp (rl_acos ac_or (gre z / ρ)%L))
  → z = mk_gc (ρ * rngl_cos θ) (ρ * rngl_sin θ).
Proof.
destruct_ac.
intros Hmi * Hρ Hθ.
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
  ∀ a b,
  rngl_of_nat b ≠ 0%L
  → (rngl_of_nat a / rngl_of_nat b - rngl_of_nat (a / b) < 1)%L.
Proof.
intros * Hrbz.
destruct_ac.
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
  rngl_is_archimedean T = true →
  ∀ rad a b,
  2 ≤ rad
  → rngl_of_nat b ≠ 0%L
  → rngl_is_limit_when_tending_to_inf (seq_converging_to_rat rad a b)
       (rngl_of_nat a / rngl_of_nat b)%L.
Proof.
destruct_ac.
intros Har * H2r Hbz.
intros ε Hε.
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
  apply (rngl_div_nonneg Hon Hop Hiv Hor); [ | easy ].
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
  now apply rngl_rat_frac_part_lt_1.
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
  rngl_is_archimedean T = true →
  ∀ rad a i c,
  2 ≤ rad
  → rngl_of_nat i ≠ 0%L
  → rngl_is_limit_when_tending_to_inf (seq_converging_to_rat rad a i) c
  → rngl_of_nat a = (rngl_of_nat i * c)%L.
Proof.
destruct_ac.
intros Har * H2r Hbz Hlim.
specialize (rat_is_inf_sum_of_inv_rad_pow Har _ a i H2r) as H1.
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

(* θ / 2^i * (2^i / n) *)
Definition seq_angle_converging_to_angle_div_nat θ (n i : nat) :=
  ((2 ^ i / n) * angle_div_2_pow_nat θ i)%A.

Arguments rl_sqrt_0 {T ro rp rl} Hor Hop Hic Hii.

Definition angle_lim :=
  is_limit_when_tending_to_inf angle_eucl_dist.

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

Theorem rngl_1_add_cos_div_2_nonneg :
  ∀ θ, (0 ≤ (1 + rngl_cos θ) / 2)%L.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ / _))%L.
  apply (rngl_le_refl Hor).
}
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
Qed.

Theorem rngl_1_sub_cos_div_2_nonneg :
  ∀ θ, (0 ≤ (1 - rngl_cos θ) / 2)%L.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ / _))%L.
  apply (rngl_le_refl Hor).
}
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
Qed.

Theorem angle_div_2_le_compat :
  ∀ θ1 θ2, (θ1 ≤ θ2 → angle_div_2 θ1 ≤ angle_div_2 θ2)%A.
Proof.
destruct_ac.
intros * H12.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  do 2 rewrite (H1 (_ / ₂))%A.
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

Theorem angle_div_2_pow_nat_le :
  ∀ n θ1 θ2,
  (θ1 ≤ θ2)%A
  → (angle_div_2_pow_nat θ1 n ≤ angle_div_2_pow_nat θ2 n)%A.
Proof.
intros * H12.
revert θ1 θ2 H12.
induction n; intros; [ easy | cbn ].
apply angle_div_2_le_compat.
now apply IHn.
Qed.

Theorem angle_le_trans :
  ∀ θ1 θ2 θ3,
  (θ1 ≤ θ2 → θ2 ≤ θ3 → θ1 ≤ θ3)%A.
Proof.
destruct_ac.
intros * H12 H23.
progress unfold angle_leb in H12.
progress unfold angle_leb in H23.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
remember (0 ≤? rngl_sin θ3)%L as z3 eqn:Hz3.
symmetry in Hz1, Hz2, Hz3.
destruct z1. {
  apply rngl_leb_le in Hz1.
  (* c'est bizarre, quand même : si j'avais utilisé rngl_eq_dec,
     il m'aurait fallu que "rngl_has_eq_dec T = true" soit en
     hypothèse. Tandis que là, non *)
  destruct z3; [ | easy ].
  apply rngl_leb_le.
  apply rngl_leb_le in Hz3.
  destruct z2; [ | easy ].
  apply rngl_leb_le in Hz2, H12, H23.
  now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
} {
  destruct z2; [ easy | ].
  destruct z3; [ easy | ].
  apply rngl_leb_le in H12, H23.
  apply rngl_leb_le.
  now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
}
Qed.

Theorem angle_lt_le_trans :
  ∀ θ1 θ2 θ3,
  (θ1 < θ2 → θ2 ≤ θ3 → θ1 < θ3)%A.
Proof.
destruct_ac.
intros * H12 H23.
progress unfold angle_ltb in H12.
progress unfold angle_leb in H23.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
remember (0 ≤? rngl_sin θ3)%L as z3 eqn:Hz3.
symmetry in Hz1, Hz2, Hz3.
destruct z1. {
  apply rngl_leb_le in Hz1.
  destruct z3; [ | easy ].
  apply rngl_ltb_lt.
  apply rngl_leb_le in Hz3.
  destruct z2; [ | easy ].
  apply rngl_leb_le in Hz2, H23.
  apply rngl_ltb_lt in H12.
  now apply (rngl_le_lt_trans Hor _ (rngl_cos θ2)).
} {
  destruct z2; [ easy | ].
  destruct z3; [ easy | ].
  apply rngl_ltb_lt in H12.
  apply rngl_leb_le in H23.
  apply rngl_ltb_lt.
  now apply (rngl_lt_le_trans Hor _ (rngl_cos θ2)).
}
Qed.

Theorem angle_le_lt_trans :
  ∀ θ1 θ2 θ3,
  (θ1 ≤ θ2 → θ2 < θ3 → θ1 < θ3)%A.
Proof.
destruct_ac.
intros * H12 H23.
progress unfold angle_leb in H12.
progress unfold angle_ltb in H23.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
remember (0 ≤? rngl_sin θ3)%L as z3 eqn:Hz3.
symmetry in Hz1, Hz2, Hz3.
destruct z1. {
  apply rngl_leb_le in Hz1.
  destruct z3; [ | easy ].
  apply rngl_ltb_lt.
  apply rngl_leb_le in Hz3.
  destruct z2; [ | easy ].
  apply rngl_leb_le in Hz2, H12.
  apply rngl_ltb_lt in H23.
  now apply (rngl_lt_le_trans Hor _ (rngl_cos θ2)).
} {
  destruct z2; [ easy | ].
  destruct z3; [ easy | ].
  apply rngl_leb_le in H12.
  apply rngl_ltb_lt in H23.
  apply rngl_ltb_lt.
  now apply (rngl_le_lt_trans Hor _ (rngl_cos θ2)).
}
Qed.

Theorem angle_mul_1_l :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ, (1 * θ)%A = θ.
Proof.
intros Hon Hos *; cbn.
apply angle_add_0_r.
Qed.

Theorem angle_nonneg : ∀ θ, (0 ≤ θ)%A.
Proof.
destruct_ac; intros.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
destruct (0 ≤? rngl_sin θ)%L; [ | easy ].
apply rngl_leb_le.
apply rngl_cos_bound.
Qed.

Theorem angle_mul_nat_not_overflow_succ_l :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ n,
  angle_mul_nat_overflow (S n) θ = false
  ↔ angle_mul_nat_overflow n θ = false ∧
    angle_add_overflow θ (n * θ) = false.
Proof.
intros Hon Hos *.
split; intros Hn. {
  destruct n. {
    split; [ easy | cbn ].
    progress unfold angle_add_overflow.
    rewrite angle_add_0_r.
    apply angle_ltb_ge.
    apply angle_le_refl.
  }
  remember (S n) as sn; cbn in Hn; subst sn.
  now apply Bool.orb_false_iff in Hn.
} {
  destruct n; [ easy | ].
  remember (S n) as sn; cbn; subst sn.
  now apply Bool.orb_false_iff.
}
Qed.

Theorem angle_mul_nat_overflow_succ_l :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ n,
  angle_mul_nat_overflow (S n) θ = true
  ↔ angle_mul_nat_overflow n θ = true ∨
    angle_add_overflow θ (n * θ) = true.
Proof.
intros Hon Hos *.
split; intros Hn. {
  apply Bool.not_false_iff_true in Hn.
  remember (angle_mul_nat_overflow n θ) as x eqn:Hx.
  symmetry in Hx.
  destruct x; [ now left | right ].
  apply Bool.not_false_iff_true.
  intros Hy.
  apply Hn.
  now apply (angle_mul_nat_not_overflow_succ_l Hon Hos).
} {
  apply Bool.not_false_iff_true.
  intros Hx.
  apply (angle_mul_nat_not_overflow_succ_l Hon Hos) in Hx.
  destruct Hx as (Hx, Hy).
  rewrite Hx in Hn.
  rewrite Hy in Hn.
  now destruct Hn.
}
Qed.

Theorem angle_mul_nat_le_mono_nonneg_r :
  ∀ a b θ, angle_mul_nat_overflow b θ = false → a ≤ b → (a * θ ≤ b * θ)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hb Hab.
revert a Hab.
induction b; intros. {
  apply Nat.le_0_r in Hab; subst a.
  apply angle_le_refl.
}
destruct a; [ apply angle_nonneg | cbn ].
move a after b.
apply Nat.succ_le_mono in Hab.
apply (angle_mul_nat_not_overflow_succ_l Hon Hos θ b) in Hb.
destruct Hb as (H1, H2).
specialize (IHb H1 _ Hab).
apply angle_add_le_mono_l; try easy.
now apply (angle_add_overflow_le _ (b * θ))%A.
Qed.

(**)

Theorem rngl_sin_div_2_nonneg : ∀ θ, (0 ≤ rngl_sin (θ / ₂))%L.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
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

Theorem angle_div_2_lt_straight :
  rngl_characteristic T ≠ 1 →
  ∀ θ, (θ / ₂ < angle_straight)%A.
Proof.
destruct_ac.
intros Hc1.
specialize rngl_has_opp_has_opp_or_subt as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros.
progress unfold angle_ltb.
specialize (rngl_sin_div_2_nonneg θ) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
cbn.
rewrite (rngl_leb_refl Hor).
apply rngl_ltb_lt.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_lt_le_trans Hor _ 0). {
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
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
  apply -> (rngl_opp_lt_compat Hop Hor).
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rl_sqrt_1 Hic Hon Hop Hor Hid) at 4.
  apply (rl_sqrt_lt_rl_sqrt Hop Hor). {
    apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  } {
    apply (rngl_lt_div_l Hon Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_add_lt_mono_l Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_cos_bound | ].
    intros H.
    apply eq_rngl_cos_1 in H.
    subst θ.
    now apply (rngl_lt_irrefl Hor) in Hzs.
  }
}
Qed.

Theorem angle_div_2_le_straight : ∀ θ, (θ / ₂ ≤ angle_straight)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  rewrite (H1 (_ / ₂))%A, (H1 angle_straight).
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
  rewrite <- (rl_sqrt_1 Hic Hon Hop Hor Hid) at 4.
  apply (rl_sqrt_le_rl_sqrt Hop Hor Hii). {
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

Theorem angle_add_overflow_lt_straight_le_straight :
  ∀ θ1 θ2,
  (θ1 < angle_straight)%A
  → (θ2 ≤ angle_straight)%A
  → angle_add_overflow θ1 θ2 = false.
Proof.
destruct_ac.
intros * H1 H2.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
progress unfold angle_ltb in H1.
progress unfold angle_leb in H2.
cbn in H1, H2.
rewrite (rngl_leb_refl Hor) in H1.
rewrite (rngl_leb_refl Hor) in H2.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hzs2, Hzs12.
destruct zs1; [ | easy ].
destruct zs2; [ | easy ].
destruct zs12; [ | easy ].
apply rngl_ltb_lt in H1.
clear H2.
apply rngl_leb_le in Hzs1.
apply rngl_leb_le in Hzs2.
apply rngl_leb_le in Hzs12.
apply (rngl_ltb_ge Hor).
remember (0 ≤? rngl_cos θ1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_leb_le in Hzc1.
  apply angle_add_overflow_le_lemma_111; try easy.
  now right; right; left.
}
apply (rngl_leb_gt Hor) in Hzc1.
apply angle_add_overflow_le_lemma_2; try easy. 2: {
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply (eq_rngl_cos_opp_1) in H.
subst θ1.
now apply (rngl_lt_irrefl Hor) in H1.
Qed.

Theorem angle_add_overflow_div_2_div_2 :
  ∀ θ1 θ2, angle_add_overflow (θ1 / ₂) (θ2 / ₂) = false.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
  intros.
  rewrite (rngl_characteristic_1_angle_0 Hon Hos Hc1 (θ1 / ₂)%A).
  rewrite (rngl_characteristic_1_angle_0 Hon Hos Hc1 (θ2 / ₂)%A).
  apply (angle_add_overflow_0_0 Hon Hos).
}
intros.
apply angle_add_overflow_lt_straight_le_straight.
apply (angle_div_2_lt_straight Hc1).
apply angle_div_2_le_straight.
Qed.

Theorem angle_div_2_le : ∀ θ, (θ / ₂ ≤ θ)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
remember (θ / ₂)%A as x.
rewrite <- (angle_div_2_mul_2 θ).
rewrite <- (angle_mul_1_l Hon Hos) in Heqx.
subst x.
apply angle_mul_nat_le_mono_nonneg_r. 2: {
  now apply -> Nat.succ_le_mono.
}
cbn.
apply Bool.orb_false_iff.
split; [ | easy ].
rewrite angle_add_0_r.
apply angle_add_overflow_div_2_div_2.
Qed.

Theorem angle_div_2_pow_nat_le_diag : ∀ n θ, (angle_div_2_pow_nat θ n ≤ θ)%A.
Proof.
intros.
induction n; [ apply angle_le_refl | cbn ].
apply (angle_le_trans _ (θ / ₂)). {
  now apply angle_div_2_le_compat.
}
apply angle_div_2_le.
Qed.

(*
Notation "⌊ a / b ⌋" := (div a b).
*)
Notation "θ / ₂ ^ n" := (angle_div_2_pow_nat θ n)
  (at level 40, format "θ  /  ₂ ^ n") : angle_scope.

Theorem angle_div_2_pow_nat_succ_r_1 :
  ∀ n θ, angle_div_2_pow_nat θ (S n) = (angle_div_2_pow_nat θ n / ₂)%A.
Proof. easy. Qed.

Theorem angle_div_2_pow_nat_succ_r_2 :
  ∀ n θ, angle_div_2_pow_nat θ (S n) = angle_div_2_pow_nat (θ / ₂) n.
Proof.
intros.
induction n; intros; [ easy | ].
remember (S n) as sn; cbn; subst sn.
now rewrite IHn.
Qed.

Theorem angle_div_2_add_not_overflow :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → ((θ1 + θ2) / ₂)%A = (θ1 / ₂ + θ2 / ₂)%A.
Proof.
intros * Haov.
rewrite angle_div_2_add.
now rewrite Haov.
Qed.

Theorem angle_div_2_add_overflow :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = true
  → ((θ1 + θ2) / ₂)%A = (θ1 / ₂ + θ2 / ₂ + angle_straight)%A.
Proof.
intros * Haov.
rewrite angle_div_2_add.
now rewrite Haov.
Qed.

Theorem angle_div_2_pow_nat_add :
  ∀ n θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → ((θ1 + θ2) / ₂^n = θ1 / ₂^n + θ2 / ₂^n)%A.
Proof.
intros * Haov.
induction n; [ easy | cbn ].
rewrite IHn.
apply angle_div_2_add_not_overflow.
apply angle_add_overflow_le with (θ2 := θ2). {
  apply angle_div_2_pow_nat_le_diag.
}
apply angle_add_not_overflow_comm.
apply angle_add_overflow_le with (θ2 := θ1). {
  apply angle_div_2_pow_nat_le_diag.
}
now apply angle_add_not_overflow_comm.
Qed.

Theorem angle_div_2_pow_nat_add' :
  ∀ n θ1 θ2,
  ((θ1 + θ2) / ₂^n)%A =
     if angle_add_overflow θ1 θ2 then
       match n with
       | 0 => (θ1 + θ2)%A
       | S n' => ((θ1 / ₂ + θ2 / ₂ + angle_straight) / ₂^n')%A
       end
     else
       (θ1 / ₂^n + θ2 / ₂^n)%A.
Proof.
destruct_ac.
intros.
remember (angle_add_overflow θ1 θ2) as aov eqn:Haov.
symmetry in Haov.
destruct aov. 2: {
  induction n; [ easy | cbn ].
  rewrite IHn.
  apply angle_div_2_add_not_overflow.
  apply angle_add_overflow_le with (θ2 := θ2). {
    apply angle_div_2_pow_nat_le_diag.
  }
  apply angle_add_not_overflow_comm.
  apply angle_add_overflow_le with (θ2 := θ1). {
    apply angle_div_2_pow_nat_le_diag.
  }
  now apply angle_add_not_overflow_comm.
} {
  destruct n; [ easy | ].
  rewrite angle_div_2_pow_nat_succ_r_2.
  f_equal.
  now apply angle_div_2_add_overflow.
}
Qed.

Theorem angle_div_2_pow_nat_mul :
  ∀ n m θ,
  m ≠ 0
  → angle_mul_nat_overflow m θ = false
  → angle_div_2_pow_nat (m * θ) n =
      (m * angle_div_2_pow_nat θ n)%A.
Proof.
intros * Hmz Haov.
specialize rngl_has_opp_has_opp_or_subt as Hos.
induction m; [ easy | clear Hmz; cbn ].
cbn in Haov.
destruct m. {
  cbn.
  rewrite angle_add_0_r.
  symmetry; apply angle_add_0_r.
}
specialize (IHm (Nat.neq_succ_0 _)).
apply Bool.orb_false_iff in Haov.
rewrite angle_div_2_pow_nat_add; [ | easy ].
f_equal.
now apply IHm.
Qed.

Theorem angle_eucl_dist_sub_l_diag :
  ∀ θ Δθ, angle_eucl_dist (θ - Δθ) θ = angle_eucl_dist Δθ 0.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
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
rewrite rngl_add_add_swap.
rewrite <- (rngl_add_sub_swap Hop (rngl_cos θ)²)%L.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
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
rewrite angle_sub_diag.
rewrite (angle_add_0_l Hon Hos).
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
now rewrite (rngl_sub_mul_r_diag_l Hon Hop).
Qed.

Theorem angle_eucl_dist_opp_opp :
  ∀ θ1 θ2, angle_eucl_dist (- θ1) (- θ2) = angle_eucl_dist θ1 θ2.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
cbn.
f_equal.
f_equal.
rewrite (rngl_sub_opp_r Hop).
rewrite rngl_add_comm.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_opp_sub_distr Hop).
apply (rngl_squ_opp Hop).
Qed.

Theorem angle_opp_0 : (- 0)%A = 0%A.
Proof.
destruct_ac.
apply eq_angle_eq.
cbn; f_equal.
apply (rngl_opp_0 Hop).
Qed.

Theorem angle_eucl_dist_move_0_l :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = angle_eucl_dist (θ2 - θ1) 0.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
replace θ1 with (θ2 - (θ2 - θ1))%A. 2: {
  rewrite (angle_sub_sub_distr Hic Hop).
  rewrite angle_sub_diag.
  apply (angle_add_0_l Hon Hos).
}
rewrite angle_eucl_dist_sub_l_diag.
rewrite (angle_sub_sub_distr Hic Hop).
rewrite angle_sub_diag.
f_equal; symmetry.
apply (angle_add_0_l Hon Hos).
Qed.

Theorem angle_eucl_dist_move_0_r :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = angle_eucl_dist (θ1 - θ2) 0.
Proof.
destruct_ac.
intros.
rewrite angle_eucl_dist_move_0_l.
rewrite <- angle_eucl_dist_opp_opp.
rewrite angle_opp_0.
f_equal.
apply (angle_opp_sub_distr Hic Hop).
Qed.

Theorem one_sub_squ_cos_add_squ_sin :
  ∀ θ, ((1 - rngl_cos θ)² + (rngl_sin θ)² = 2 * (1 - rngl_cos θ))%L.
Proof.
destruct_ac; intros.
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
apply (rngl_sub_mul_r_diag_l Hon Hop).
Qed.

Theorem rngl_cos_decr :
  ∀ θ1 θ2, (θ1 ≤ θ2 ≤ angle_straight)%A → (rngl_cos θ2 ≤ rngl_cos θ1)%L.
Proof.
intros * (H12, H2s).
destruct_ac.
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
  ∀ θ1 θ2,
  (θ1 ≤ θ2 ≤ angle_right)%A
  → (rngl_sin θ1 ≤ rngl_sin θ2)%L.
Proof.
destruct_ac.
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
  ∀ θ1 θ2,
  (θ1 < θ2 ≤ angle_right)%A
  → (rngl_sin θ1 < rngl_sin θ2)%L.
Proof.
destruct_ac.
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

Theorem rngl_cos_add_rngl_cos :
  ∀ p q,
  (rngl_cos p + rngl_cos q =
   2 *
   rngl_cos (angle_div_2 p + angle_div_2 q) *
   rngl_cos (angle_div_2 p - angle_div_2 q))%L.
Proof.
destruct_ac; intros *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
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
specialize (cos2_sin2_1 p2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
specialize (cos2_sin2_1 q2) as H1.
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
  ∀ p q,
  (rngl_cos p - rngl_cos q =
   - (2%L *
      rngl_sin (angle_div_2 p + angle_div_2 q) *
      rngl_sin (angle_div_2 p - angle_div_2 q)))%L.
Proof.
destruct_ac; intros *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
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
specialize (cos2_sin2_1 p2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
specialize (cos2_sin2_1 q2) as H1.
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
  ∀ p q,
  (rngl_sin p + rngl_sin q =
   2 *
   rngl_sin (angle_div_2 p + angle_div_2 q) *
   rngl_cos (angle_div_2 p - angle_div_2 q))%L.
Proof.
destruct_ac; intros *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
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
rewrite cos2_sin2_1.
rewrite (rngl_mul_1_l Hon).
rewrite <- (rngl_add_assoc (rngl_cos q2 * _))%L.
rewrite (rngl_mul_comm Hic (rngl_sin p2)).
do 2 rewrite <- rngl_mul_add_distr_l.
rewrite cos2_sin2_1.
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
  ∀ p q,
  (rngl_sin p - rngl_sin q =
   2%L *
   rngl_cos (angle_div_2 p + angle_div_2 q) *
   rngl_sin (angle_div_2 p - angle_div_2 q))%L.
Proof.
destruct_ac; intros *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
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
rewrite cos2_sin2_1.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_mul_swap Hic _ (rngl_sin q2)).
rewrite <- (rngl_sub_add_distr Hos).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_add_comm _²)%L.
rewrite cos2_sin2_1.
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
  ∀ θ, (rngl_cos θ = 1 - (angle_eucl_dist θ 0)² / 2)%L.
Proof.
destruct_ac.
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
rewrite cos2_sin2_1 in H1.
rewrite <- (rngl_add_sub_swap Hop) in H1.
rewrite (rngl_sub_mul_r_diag_l Hon Hop) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
now apply (rngl_sub_move_l Hop) in H1.
Qed.

Theorem rngl_sin_angle_eucl_dist :
  ∀ θ, (rngl_sin θ = 1 - (angle_eucl_dist θ angle_right)² / 2)%L.
Proof.
destruct_ac.
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
rewrite cos2_sin2_1 in H1.
rewrite <- (rngl_add_sub_swap Hop) in H1.
rewrite (rngl_sub_mul_r_diag_l Hon Hop) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
now apply (rngl_sub_move_l Hop) in H1.
Qed.

Theorem rngl_cos_le_iff_angle_eucl_le :
  ∀ θ θ',
  (rngl_cos θ ≤ rngl_cos θ' ↔ angle_eucl_dist θ' 0 ≤ angle_eucl_dist θ 0)%L.
Proof.
destruct_ac.
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
  apply angle_eucl_dist_is_dist.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor (angle_eucl_dist θ _)). 2: {
  apply (dist_nonneg Hon Hop Hiv Hor).
  apply angle_eucl_dist_is_dist.
}
do 2 rewrite rngl_cos_angle_eucl_dist.
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
  ∀ θ θ',
  (rngl_sin θ ≤ rngl_sin θ' ↔
     angle_eucl_dist θ' angle_right ≤ angle_eucl_dist θ angle_right)%L.
Proof.
destruct_ac.
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
  apply rngl_sin_bound.
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
do 2 rewrite cos2_sin2_1.
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

Theorem angle_mul_le_mono_l :
  ∀ θ1 θ2,
  (θ1 ≤ θ2)%A
  → ∀ n,
  angle_mul_nat_overflow n θ2 = false
  → (n * θ1 ≤ n * θ2)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H12 * Hn2.
revert θ1 θ2 H12 Hn2.
induction n; intros; [ apply angle_le_refl | cbn ].
apply (angle_mul_nat_not_overflow_succ_l Hon Hos) in Hn2.
destruct Hn2 as (Hn2, H2n2).
generalize Hn2; intros Hn12.
apply (IHn θ1) in Hn12; [ | easy ].
apply (angle_le_trans _ (θ1 + n * θ2))%A. {
  apply angle_add_le_mono_l; [ | | easy ]. {
    apply (angle_add_overflow_le _ (n * θ2))%A; [ easy | ].
    apply angle_add_not_overflow_comm.
    apply (angle_add_overflow_le _ θ2); [ easy | ].
    now apply angle_add_not_overflow_comm.
  } {
    apply angle_add_not_overflow_comm.
    apply (angle_add_overflow_le _ θ2)%A; [ easy | ].
    now apply angle_add_not_overflow_comm.
  }
} {
  rewrite (angle_add_comm Hic θ1).
  rewrite (angle_add_comm Hic θ2).
  apply angle_add_le_mono_l; [ | | easy ]. {
    apply (angle_add_overflow_le _ θ2)%A; [ easy | ].
    now apply angle_add_not_overflow_comm.
  } {
    now apply angle_add_not_overflow_comm.
  }
}
Qed.

Theorem angle_mul_nat_overflow_le_r :
  ∀ θ1 θ2,
  (θ1 ≤ θ2)%A
  → ∀ n,
  angle_mul_nat_overflow n θ2 = false
  → angle_mul_nat_overflow n θ1 = false.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H12 * H2.
revert θ1 θ2 H12 H2.
induction n; intros; [ easy | ].
generalize H2; intros H.
apply (angle_mul_nat_not_overflow_succ_l Hon Hos) in H.
destruct H as (Hn2, H2n2).
cbn.
destruct n; [ easy | ].
apply Bool.orb_false_iff.
split; [ | now apply (IHn _ θ2) ].
remember (S n) as m eqn:Hm.
clear n Hm; rename m into n.
clear H2 IHn.
apply angle_add_not_overflow_comm.
eapply angle_add_overflow_le; [ apply H12 | ].
apply angle_add_not_overflow_comm.
eapply angle_add_overflow_le; [ | apply H2n2 ].
now apply angle_mul_le_mono_l.
Qed.

Theorem angle_add_overflow_0_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ, angle_add_overflow θ 0 = false.
Proof.
intros Hon Hos.
intros.
progress unfold angle_add_overflow.
apply angle_ltb_ge.
rewrite angle_add_0_r.
apply angle_le_refl.
Qed.

Theorem rl_sqrt_nonneg : ∀ a, (0 ≤ a → 0 ≤ √ a)%L.
Proof.
intros * Ha.
now apply rl_sqrt_nonneg.
Qed.

Theorem angle_mul_0_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ n, (n * 0 = 0)%A.
Proof.
intros Hon Hos *.
apply eq_angle_eq; cbn.
induction n; [ easy | cbn ].
do 2 rewrite (rngl_mul_1_l Hon).
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
now rewrite rngl_add_0_r.
Qed.

Theorem angle_mul_nat_overflow_0_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ n, angle_mul_nat_overflow n 0 = false.
Proof.
intros Hon Hos *.
induction n; [ easy | cbn ].
destruct n; [ easy | ].
rewrite (angle_mul_0_r Hon Hos).
apply Bool.orb_false_iff.
split; [ | easy ].
apply (angle_add_overflow_0_0 Hon Hos).
Qed.

Theorem angle_add_not_overflow_move_add :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → angle_add_overflow (θ1 + θ3) θ2 = false
  → angle_add_overflow θ1 (θ2 + θ3) = false.
Proof.
destruct_ac.
intros * H13 H132.
progress unfold angle_add_overflow in H132.
progress unfold angle_add_overflow.
apply angle_ltb_ge in H132.
apply angle_ltb_ge.
rewrite (angle_add_add_swap Hic Hop) in H132.
rewrite <- (angle_add_assoc Hop) in H132.
apply (angle_le_trans _ (θ1 + θ3))%A; [ | apply H132 ].
progress unfold angle_add_overflow in H13.
now apply angle_ltb_ge in H13.
Qed.

Theorem angle_add_diag :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ, (θ + θ = 2 * θ)%A.
Proof.
intros Hon Hos *; cbn.
now rewrite angle_add_0_r.
Qed.

Theorem angle_mul_nat_overflow_mul_2_div_2 :
  ∀ n θ,
  angle_mul_nat_overflow n θ = false
  → angle_mul_nat_overflow (2 * n) (θ / ₂) = false.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hn.
revert θ Hn.
induction n; intros; [ easy | ].
apply (angle_mul_nat_not_overflow_succ_l Hon Hos) in Hn.
destruct Hn as (Hmn, Han).
cbn - [ angle_mul_nat_overflow ].
rewrite Nat.add_0_r.
rewrite Nat.add_succ_r.
rewrite Nat_add_diag.
apply <- (angle_mul_nat_not_overflow_succ_l Hon Hos).
split. {
  apply <- (angle_mul_nat_not_overflow_succ_l Hon Hos).
  split; [ now apply IHn | ].
  rewrite Nat.mul_comm.
  rewrite <- (angle_mul_nat_assoc Hon Hop).
  rewrite angle_div_2_mul_2.
  apply angle_add_not_overflow_comm in Han.
  apply angle_add_not_overflow_comm.
  apply (angle_add_overflow_le _ θ); [ | easy ].
  apply angle_div_2_le.
}
rewrite <- Nat.add_1_r.
rewrite (angle_mul_add_distr_r Hon Hop).
rewrite (angle_mul_1_l Hon Hos).
apply angle_add_not_overflow_move_add. {
  apply angle_add_overflow_div_2_div_2.
}
rewrite (angle_add_diag Hon Hos).
rewrite angle_div_2_mul_2.
rewrite Nat.mul_comm.
rewrite <- (angle_mul_nat_assoc Hon Hop).
now rewrite angle_div_2_mul_2.
Qed.

Theorem angle_div_2_pow_nat_div_2_distr :
  ∀ n θ, angle_div_2_pow_nat (θ / ₂) n = (angle_div_2_pow_nat θ n / ₂)%A.
Proof.
intros.
now rewrite <- angle_div_2_pow_nat_succ_r_2.
Qed.

Theorem angle_mul_nat_overflow_angle_div_2_mul_2_div_2 :
  ∀ m n θ,
  angle_mul_nat_overflow n (angle_div_2_pow_nat θ m) = false
  → angle_mul_nat_overflow (2 * n) (angle_div_2_pow_nat (θ / ₂) m) = false.
Proof.
destruct_ac.
intros * Hnm.
revert θ n Hnm.
induction m; intros. {
  cbn in Hnm; cbn.
  rewrite Nat.add_0_r.
  rewrite Nat_add_diag.
  now apply angle_mul_nat_overflow_mul_2_div_2.
}
rewrite angle_div_2_pow_nat_succ_r_2.
apply IHm.
cbn in Hnm.
eapply angle_mul_nat_overflow_le_r; [ | apply Hnm ].
rewrite <- angle_div_2_pow_nat_succ_r_2.
apply angle_le_refl.
Qed.

Theorem angle_mul_nat_overflow_pow_div :
  ∀ n θ,
  angle_mul_nat_overflow (2 ^ n) (angle_div_2_pow_nat θ n) = false.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  rewrite (rngl_characteristic_1_angle_0 Hon Hos Hc1 (angle_div_2_pow_nat _ _)).
  apply (angle_mul_nat_overflow_0_r Hon Hos).
}
assert (H2z : (2 ≠ 0)%L) by apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
intros.
revert θ.
induction n; intros; [ easy | cbn ].
destruct n. {
  cbn.
  apply Bool.orb_false_iff.
  split; [ | easy ].
  rewrite angle_add_0_r.
  apply angle_add_overflow_div_2_div_2.
}
cbn.
do 2 rewrite Nat.add_0_r.
rewrite Nat.add_assoc.
cbn in IHn.
rewrite Nat.add_0_r in IHn.
specialize (IHn θ) as H1.
apply angle_mul_nat_overflow_mul_2_div_2 in H1.
cbn in H1.
rewrite Nat.add_0_r in H1.
now rewrite Nat.add_assoc in H1.
Qed.

Theorem angle_lt_le_incl :
  ∀ θ1 θ2, (θ1 < θ2 → θ1 ≤ θ2)%A.
Proof.
specialize ac_or as Hor.
intros * H12.
progress unfold angle_ltb in H12.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
symmetry in Hz1, Hz2.
destruct z1. {
  destruct z2; [ | easy ].
  apply rngl_ltb_lt in H12.
  apply rngl_leb_le.
  now apply (rngl_lt_le_incl Hor).
} {
  destruct z2; [ easy | ].
  apply rngl_ltb_lt in H12.
  apply rngl_leb_le.
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem rngl_sin_div_2_pow_nat_nonneg :
  ∀ n θ, n ≠ 0 → (0 ≤ rngl_sin (angle_div_2_pow_nat θ n))%L.
Proof.
intros * Hnz.
destruct n; [ easy | ].
rewrite angle_div_2_pow_nat_succ_r_1.
apply rngl_sin_div_2_nonneg.
Qed.

Theorem angle_lt_iff :
  ∀ θ1 θ2, (θ1 < θ2 ↔ θ1 ≤ θ2 ∧ θ1 ≠ θ2)%A.
Proof.
destruct_ac; intros.
progress unfold angle_ltb.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    split; intros H12. {
      apply rngl_ltb_lt in H12.
      split. {
        apply rngl_leb_le.
        now apply (rngl_lt_le_incl Hor).
      }
      intros H; subst θ2.
      now apply (rngl_lt_irrefl Hor) in H12.
    } {
      destruct H12 as (Hc12, H12).
      apply rngl_leb_le in Hc12.
      apply rngl_ltb_lt.
      apply (rngl_lt_iff Hor).
      split; [ easy | ].
      intros H; symmetry in H.
      apply rngl_cos_eq in H.
      destruct H as [H| H]; [ easy | ].
      subst θ1.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1.
      apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
      apply eq_rngl_sin_0 in Hzs2.
      destruct Hzs2; subst θ2. {
        apply H12.
        apply eq_angle_eq; cbn.
        now rewrite rngl_opp_0.
      } {
        apply H12.
        apply eq_angle_eq; cbn.
        now rewrite rngl_opp_0.
      }
    }
  }
  split; [ | easy ].
  intros _.
  split; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs2.
  apply (rngl_nle_gt Hor) in Hzs2.
  now intros H; subst θ2.
} {
  apply (rngl_leb_gt Hor) in Hzs1.
  destruct zs2; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs2.
  split; intros H12. {
    apply rngl_ltb_lt in H12.
    split. {
      apply rngl_leb_le.
      now apply (rngl_lt_le_incl Hor).
    }
    intros H; subst θ2.
    now apply (rngl_lt_irrefl Hor) in H12.
  }
  destruct H12 as (Hc12, H12).
  apply rngl_leb_le in Hc12.
  apply rngl_ltb_lt.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; apply H12; clear H12.
  apply rngl_cos_eq in H.
  destruct H; subst θ1; [ easy | ].
  cbn in Hzs1.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
  now apply (rngl_lt_le_incl Hor), (rngl_nlt_ge Hor) in Hzs1.
}
Qed.

Theorem rl_sqrt_pos :
  rngl_has_opp_or_subt T = true →
  ∀ a, (0 < a)%L → (0 < √a)%L.
Proof.
intros Hos.
specialize ac_or as Hor.
intros a Ha.
apply (rngl_lt_iff Hor).
split. {
  apply rl_sqrt_nonneg.
  now apply (rngl_lt_le_incl Hor).
}
intros H; symmetry in H.
apply (eq_rl_sqrt_0 Hos) in H; [ | now apply (rngl_lt_le_incl Hor) ].
subst a.
now apply (rngl_lt_irrefl Hor) in Ha.
Qed.

Theorem eq_angle_div_2_0 : ∀ θ, (θ / ₂ = 0 → θ = 0)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  apply H1.
}
intros * Htz.
apply eq_angle_eq in Htz.
apply eq_angle_eq; cbn.
injection Htz; clear Htz; intros Hc Hs.
apply (eq_rl_sqrt_0 Hos) in Hc. 2: {
  apply rngl_1_sub_cos_div_2_nonneg.
}
apply (f_equal (λ x, rngl_mul x 2)) in Hc.
rewrite (rngl_div_mul Hon Hiv) in Hc. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite (rngl_mul_0_l Hos) in Hc.
apply -> (rngl_sub_move_0_r Hop) in Hc.
symmetry in Hc.
apply eq_rngl_cos_1 in Hc.
now subst θ.
Qed.

Theorem rngl_cos_lt_sqrt_1_add_cos_div_2 :
  rngl_characteristic T ≠ 1 →
  ∀ θ,
  θ ≠ 0%A
  → (rngl_cos θ < √((1 + rngl_cos θ) / 2))%L.
Proof.
destruct_ac.
intros Hc1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as Hz2.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hsz.
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
}
destruct (rngl_lt_dec Hor (rngl_cos θ) 0) as [Hcz| Hzc]. {
  apply (rngl_lt_le_trans Hor _ 0); [ easy | ].
  apply (rngl_abs_nonneg Hop Hor).
}
apply (rngl_nlt_ge Hor) in Hzc.
rewrite <- (rngl_abs_nonneg_eq Hop Hor (rngl_cos θ)) at 1; [ | easy ].
apply (rngl_squ_lt_abs_lt Hop Hor Hii).
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
}
apply -> (rngl_lt_div_r Hon Hop Hiv Hor); [ | easy ].
apply (rngl_le_lt_trans Hor _ (rngl_cos θ * 2))%L. 2: {
  rewrite rngl_mul_add_distr_l.
  rewrite (rngl_mul_1_r Hon).
  apply (rngl_add_lt_le_mono Hop Hor); [ | now apply (rngl_le_refl Hor) ].
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  intros H.
  now apply eq_rngl_cos_1 in H.
}
apply (rngl_mul_le_mono_pos_r Hop Hor Hii); [ easy | ].
progress unfold rngl_squ.
rewrite <- (rngl_mul_1_r Hon).
apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
apply rngl_cos_bound.
Qed.

Theorem angle_div_2_lt : ∀ θ, (θ ≠ 0 → θ / ₂ < θ)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  exfalso; apply H, H1.
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as Hz2.
intros * Htz.
progress unfold angle_ltb.
specialize (rngl_sin_div_2_nonneg θ) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; [ | easy ].
apply rngl_ltb_lt.
cbn.
rewrite Hzs.
rewrite (rngl_mul_1_l Hon).
apply rngl_leb_le in Hzs.
remember (0 ≤? rngl_cos θ)%L as zc eqn:Hzc.
symmetry in Hzc.
destruct zc. 2: {
  apply (rngl_leb_gt Hor) in Hzc.
  apply (rngl_lt_le_trans Hor _ 0); [ easy | ].
  apply rl_sqrt_nonneg.
  apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
}
apply rngl_leb_le in Hzc.
now apply rngl_cos_lt_sqrt_1_add_cos_div_2.
Qed.

Theorem angle_div_2_neq_0 : ∀ θ, (θ ≠ 0 → θ / ₂ ≠ θ)%A.
Proof.
destruct_ac.
intros * H2.
specialize (angle_div_2_lt _ H2) as H1.
now apply angle_lt_iff in H1.
Qed.

Theorem eq_angle_div_2_pow_nat_0 :
  ∀ n θ, (angle_div_2_pow_nat θ n = 0 → θ = 0)%A.
Proof.
destruct_ac.
intros * Htn.
induction n; [ easy | ].
cbn in Htn.
apply eq_angle_div_2_0 in Htn.
now apply IHn.
Qed.

Theorem rl_sqrt_div_2 : ∀ a, (0 ≤ a → √(a / 2) = √(2 * a) / 2)%L.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 √_)%L, (H1 (_ / _))%L.
}
intros * Hza.
assert (Hza2 : (0 ≤ a / 2)%L). {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
}
assert (Hz2a : (0 ≤ 2 * a)%L). {
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  apply (rngl_0_le_2 Hon Hop Hor).
}
assert (H2z : (2 ≠ 0)%L) by apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  now apply (rl_sqrt_nonneg).
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
  now apply rl_sqrt_nonneg.
}
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hid).
rewrite rngl_squ_sqrt; [ | easy ].
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
progress unfold rngl_squ.
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_mul_comm Hic).
now rewrite (rngl_mul_div Hi1).
Qed.

Fixpoint rngl_cos_div_pow_2 θ n :=
  match n with
  | 0 => rngl_cos θ
  | S n' => (√((1 + rngl_cos_div_pow_2 θ n') / 2))%L
  end.

Fixpoint squ_rngl_cos_div_pow_2 θ n :=
  match n with
  | 0 => rngl_cos θ
  | S n' => ((1 + squ_rngl_cos_div_pow_2 θ n') / 2)%L
  end.

Theorem rngl_cos_div_pow_2_eq :
  ∀ θ n,
  rngl_cos (angle_div_2_pow_nat θ (S n)) = rngl_cos_div_pow_2 (θ / ₂) n.
Proof.
destruct_ac.
intros.
rewrite angle_div_2_pow_nat_succ_r_2.
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

Theorem rngl_cos_div_pow_2_succ_r :
  ∀ n θ,
  (0 ≤ rngl_sin θ)%L
  → rngl_cos_div_pow_2 θ (S n) = rngl_cos_div_pow_2 (θ / ₂) n.
Proof.
destruct_ac; intros * Hzs.
cbn.
induction n. {
  cbn.
  apply rngl_leb_le in Hzs.
  rewrite Hzs; symmetry.
  apply (rngl_mul_1_l Hon).
}
cbn.
now rewrite IHn.
Qed.

Theorem rngl_cos_div_pow_2_div_2_bound :
  ∀ n θ, (-1 ≤ rngl_cos_div_pow_2 (θ / ₂) n)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
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
  ∀ n θ, (-1 ≤ squ_rngl_cos_div_pow_2 (θ / ₂) n ≤ 1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
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

Theorem rngl_cos_pow_2_div_2_succ_nonneg :
  ∀ n θ, (0 ≤ rngl_cos_div_pow_2 (θ / ₂) (S n))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1.
  apply (rngl_le_refl Hor).
}
intros.
cbn.
apply rl_sqrt_nonneg.
apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
apply (rngl_le_opp_l Hop Hor).
apply rngl_cos_div_pow_2_div_2_bound.
Qed.

Theorem angle_0_div_2 : (0 / ₂ = 0)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  apply H1.
}
apply eq_angle_eq; cbn.
rewrite (rngl_leb_refl Hor).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite (rl_sqrt_1 Hic Hon Hop Hor Hid).
f_equal.
rewrite (rngl_sub_diag Hos).
rewrite (rngl_div_0_l Hos Hi1). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rl_sqrt_0 Hop Hic Hor Hid).
Qed.

Theorem angle_straight_div_2 : (angle_straight / ₂ = angle_right)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
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
rewrite (rl_sqrt_0 Hop Hic Hor Hid).
f_equal.
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rl_sqrt_1 Hic Hon Hop Hor Hid).
Qed.

Theorem angle_div_2_not_straight :
  rngl_characteristic T ≠ 1 →
  ∀ θ, (θ / ₂)%A ≠ angle_straight.
Proof.
destruct_ac.
intros Hc1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H.
apply eq_angle_eq in H.
injection H; clear H; intros Hs Hc.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  rewrite (rngl_mul_1_l Hon) in Hc.
  remember √((1 + rngl_cos θ) / 2)%L as a eqn:Ha.
  assert (H1 : (a < 0)%L). {
    rewrite Hc.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
  }
  apply (rngl_nle_gt Hor) in H1.
  apply H1; clear H1.
  rewrite Ha.
  apply rl_sqrt_nonneg.
  apply rngl_1_add_cos_div_2_nonneg.
}
apply (rngl_leb_gt Hor) in Hzs.
rewrite (rngl_mul_opp_l Hop) in Hc.
rewrite (rngl_mul_1_l Hon) in Hc.
apply (rngl_opp_inj Hop) in Hc.
apply (f_equal rngl_squ) in Hc.
rewrite rngl_squ_sqrt in Hc. 2: {
  apply rngl_1_add_cos_div_2_nonneg.
}
rewrite (rngl_squ_1 Hon) in Hc.
apply (f_equal (λ x, (x * 2)%L)) in Hc.
rewrite (rngl_div_mul Hon Hiv) in Hc. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite (rngl_mul_1_l Hon) in Hc.
apply (rngl_add_cancel_l Hos) in Hc.
apply (eq_rngl_cos_1) in Hc.
rewrite Hc in Hzs.
cbn in Hzs.
now apply (rngl_lt_irrefl Hor) in Hzs.
Qed.

Theorem rngl_cos_div_pow_2_incr :
  rngl_characteristic T ≠ 1 →
  ∀ n θ,
  (θ ≠ 0)%A
  → (rngl_cos_div_pow_2 (θ / ₂) n < rngl_cos_div_pow_2 (θ / ₂) (S n))%L.
Proof.
destruct_ac; intros Hc1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Htz.
destruct (rngl_eq_dec Hed (rngl_cos θ) (-1)%L) as [Ht1| Ht1]. {
  apply (eq_rngl_cos_opp_1) in Ht1.
  subst θ.
  rewrite angle_straight_div_2.
  remember angle_right as θ.
  assert (Hθ : (θ ≤ angle_right)%A) by (subst θ; apply angle_le_refl).
  assert (Hθz : (θ ≠ 0)%A). {
    intros H; rewrite H in Heqθ.
    injection Heqθ; intros H1 H2.
    now apply (rngl_1_neq_0_iff Hon) in H2.
  }
  clear Heqθ.
  revert θ Hθ Hθz.
  induction n; intros. {
    now apply (rngl_cos_lt_sqrt_1_add_cos_div_2 Hc1).
  }
  assert (Hzs : (0 ≤ rngl_sin θ)%L). {
    progress unfold angle_leb in Hθ.
    cbn in Hθ.
    specialize (rngl_0_le_1 Hon Hop Hor) as H1.
    apply rngl_leb_le in H1.
    rewrite H1 in Hθ; clear H1.
    apply rngl_leb_le.
    apply Bool.not_false_iff_true.
    now intros H; rewrite H in Hθ.
  }
  rewrite rngl_cos_div_pow_2_succ_r; [ | easy ].
  rewrite rngl_cos_div_pow_2_succ_r; [ | easy ].
  apply IHn. {
    apply (angle_le_trans _ θ); [ | easy ].
    apply angle_div_2_le.
  }
  intros H.
  now apply eq_angle_div_2_0 in H.
}
revert θ Htz Ht1.
induction n; intros. {
  cbn.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    rewrite (rngl_mul_1_l Hon).
    apply (rl_sqrt_lt_rl_sqrt Hop Hor). {
      apply rngl_1_add_cos_div_2_nonneg.
    }
    progress unfold rngl_div at 1 2.
    rewrite Hiv.
    apply (rngl_mul_lt_mono_pos_r Hop Hor Hii). {
      apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    apply (rngl_add_lt_mono_l Hop Hor).
    remember (0 ≤? rngl_cos θ)%L as zc eqn:Hzc.
    symmetry in Hzc.
    destruct zc. 2: {
      apply (rngl_leb_gt Hor) in Hzc.
      apply (rngl_lt_le_trans Hor _ 0); [ easy | ].
      apply rl_sqrt_nonneg.
      apply (rngl_le_div_r Hon Hop Hiv Hor). {
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      rewrite (rngl_mul_0_l Hos).
      apply (rngl_le_opp_l Hop Hor).
      apply rngl_cos_bound.
    }
    apply rngl_leb_le in Hzc.
    now apply (rngl_cos_lt_sqrt_1_add_cos_div_2 Hc1).
  }
  apply (rngl_leb_gt Hor) in Hzs.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_lt_le_trans Hor _ 0). {
    apply (rngl_opp_neg_pos Hop Hor).
    apply (rl_sqrt_pos Hos).
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_1_add_cos_div_2_nonneg | ].
    intros H; symmetry in H.
    progress unfold rngl_div in H.
    rewrite Hiv in H.
    apply (rngl_eq_mul_0_l Hos Hii) in H. 2: {
      apply (rngl_inv_neq_0 Hon Hos Hiv).
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    rewrite rngl_add_comm in H.
    now apply (rngl_add_move_0_r Hop) in H.
  }
  apply rl_sqrt_nonneg.
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
    apply rl_sqrt_nonneg.
    apply (rngl_le_div_r Hon Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    rewrite (rngl_mul_0_l Hos).
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  }
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  rewrite rngl_squ_sqrt. 2: {
    apply rngl_1_add_cos_div_2_nonneg.
  }
  rewrite (rngl_squ_1 Hon).
  apply (rngl_div_le_1 Hon Hop Hiv Hor). {
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  }
  split. {
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  }
  apply (rngl_add_le_mono_l Hop Hor).
  apply rngl_cos_bound.
}
rewrite rngl_cos_div_pow_2_succ_r. 2: {
  apply rngl_sin_div_2_nonneg.
}
rewrite rngl_cos_div_pow_2_succ_r. 2: {
  apply rngl_sin_div_2_nonneg.
}
apply IHn. {
  intros H.
  now apply eq_angle_div_2_0 in H.
}
intros H.
apply (eq_rngl_cos_opp_1) in H.
now apply (angle_div_2_not_straight Hc1) in H.
Qed.

Theorem squ_rngl_cos_non_0_div_pow_2_bound :
  rngl_characteristic T ≠ 1 →
  ∀ n θ,
  θ ≠ 0%A
  → (squ_rngl_cos_div_pow_2 θ n < 1)%L.
Proof.
destruct_ac.
intros Hc1.
intros * Htz.
induction n; cbn. {
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  intros H.
  now apply (eq_rngl_cos_1) in H.
}
apply (rngl_lt_div_l Hon Hop Hiv Hor).
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
rewrite (rngl_mul_1_l Hon).
now apply (rngl_add_lt_mono_l Hop Hor).
Qed.

Theorem squ_rngl_cos_div_pow_2_incr :
  rngl_characteristic T ≠ 1 →
  ∀ n θ,
  θ ≠ 0%A
  → (squ_rngl_cos_div_pow_2 θ n < squ_rngl_cos_div_pow_2 θ (S n))%L.
Proof.
destruct_ac.
intros Hc1.
intros * Htz; cbn.
remember (squ_rngl_cos_div_pow_2 θ n) as a eqn:Ha.
apply (rngl_lt_div_r Hon Hop Hiv Hor).
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
rewrite (rngl_mul_comm Hic).
rewrite <- (rngl_add_diag Hon).
apply (rngl_add_lt_mono_r Hop Hor).
subst a.
now apply (squ_rngl_cos_non_0_div_pow_2_bound Hc1).
Qed.

Theorem rngl_cos_div_pow_2_0 : ∀ n, rngl_cos_div_pow_2 0 n = 1%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 1%L).
  apply H1.
}
intros n.
induction n; [ easy | cbn ].
rewrite IHn.
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rl_sqrt_1 Hic Hon Hop Hor Hid).
Qed.

Theorem squ_rngl_cos_div_pow_2_0 : ∀ n, squ_rngl_cos_div_pow_2 0 n = 1%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 1%L).
  apply H1.
}
intros n.
induction n; [ easy | cbn ].
rewrite IHn.
apply (rngl_div_diag Hon Hiq).
apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_cos_div_pow_2_lower_bound :
  ∀ n θ,
  (squ_rngl_cos_div_pow_2 (θ / ₂) n ≤ rngl_cos_div_pow_2 (θ / ₂) n)%L.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
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
  apply (angle_eqb_eq Hed) in Htz.
  subst θ.
  rewrite angle_0_div_2.
  rewrite rngl_cos_div_pow_2_0.
  rewrite squ_rngl_cos_div_pow_2_0.
  apply (rngl_le_refl Hor).
}
apply (angle_eqb_neq Hed) in Htz.
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
rewrite rngl_squ_sqrt. 2: {
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
remember (squ_rngl_cos_div_pow_2 (θ / ₂) n ≤? 0)%L as scz eqn:Hscz.
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

Theorem rngl_cos_angle_div_2_pow_nat_tending_to_1 :
  rngl_characteristic T ≠ 1 →
  rngl_is_archimedean T = true →
  ∀ θ,
  rngl_is_limit_when_tending_to_inf
    (λ i, rngl_cos (angle_div_2_pow_nat θ i)) 1%L.
Proof.
intros Hc1 Har.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros.
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n →
    (1 - rngl_cos (angle_div_2_pow_nat θ n) < ε)%L). {
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
    (1 - ε < rngl_cos_div_pow_2 (θ / ₂) n)%L). {
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
    (1 - ε < squ_rngl_cos_div_pow_2 (θ / ₂) n)%L). {
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
    ((1 - rngl_cos (θ / ₂)) / 2 ^ n < ε)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros n Hn.
  remember (θ / ₂)%A as θ' eqn:Hθ.
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
  destruct n; [ | easy ].
  cbn.
  now rewrite (rngl_mul_1_r Hon).
}
intros ε Hε.
(*
2 ^ n > (1 - cos (θ/2)) / ε
n > ln₂ ((1 - cos (θ/2)) / ε)
*)
remember ((1 - rngl_cos (θ / ₂)))%L as a eqn:Ha.
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
rewrite Nat_add_diag in H2.
rewrite <- Nat.pow_succ_r in H2; [ | easy ].
specialize (Nat.log2_spec (S N)) as H3.
specialize (H3 (Nat.lt_0_succ _)).
rewrite H1 in H3.
rewrite <- H2 in H3.
destruct H3 as (H3, H4).
now apply Nat.lt_irrefl in H4.
Qed.

Theorem angle_mul_nat_not_overflow_le_l :
  ∀ m n,
  m ≤ n
  → ∀ θ, angle_mul_nat_overflow n θ = false
  → angle_mul_nat_overflow m θ = false.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hmn * Hn.
revert θ m Hmn Hn.
induction n; intros. {
  now apply Nat.le_0_r in Hmn; subst m.
}
apply (angle_mul_nat_not_overflow_succ_l Hon Hos) in Hn.
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hmn.
apply (angle_mul_nat_not_overflow_succ_l Hon Hos).
split; [ now apply IHn | ].
apply (angle_add_overflow_le _ (n * θ)); [ | easy ].
now apply angle_mul_nat_le_mono_nonneg_r.
Qed.

Theorem angle_mul_nat_overflow_le_l :
  ∀ n θ,
  angle_mul_nat_overflow n θ = true
  → ∀ m, n ≤ m → angle_mul_nat_overflow m θ = true.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hn * Hnm.
apply Bool.not_false_iff_true in Hn.
apply Bool.not_false_iff_true.
intros H; apply Hn.
now apply (angle_mul_nat_not_overflow_le_l _ m).
Qed.

Theorem angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat :
  rngl_is_archimedean T = true →
  rngl_characteristic T = 0 →
  ∀ n θ,
  n ≠ 0
  → angle_mul_nat_overflow n θ = false
  → angle_lim (seq_angle_converging_to_angle_div_nat (n * θ) n) θ.
Proof.
destruct_ac.
intros Har Hch.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_cos_bound.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite Hc1 in Hch.
}
assert (H02 : (0 ≤ 2)%L) by apply (rngl_0_le_2 Hon Hop Hor).
intros * Hnz Haov.
(*
clear Haov.
*)
progress unfold seq_angle_converging_to_angle_div_nat.
enough (H : angle_lim (λ i, (2 ^ i mod n * angle_div_2_pow_nat θ i))%A 0%A). {
  progress unfold angle_lim.
  progress unfold is_limit_when_tending_to_inf.
  intros ε Hε.
(*
set (j := S (Nat.log2 n)).
assert (Hjn : n < 2 ^ j). {
  subst j.
  apply Nat.log2_spec.
  now apply Nat.neq_0_lt_0.
}
remember (θ / ₂^j)%A as θ'' eqn:Hθ''.
assert (Htj : angle_mul_nat_overflow n θ'' = false). {
  subst θ''.
  subst j.
  apply (angle_mul_nat_overflow_le_l _ (2 ^ S (Nat.log2 n))). {
    now apply Nat.lt_le_incl.
  }
  apply angle_mul_nat_overflow_pow_div.
}
rename H into H1.
specialize (H1 (ε / 2 ^ j))%L.
assert (Hz2j : (0 < 2 ^ j)%L). {
  apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
assert (H : (0 < ε / 2 ^ j)%L). {
  now apply (rngl_div_lt_pos Hon Hop Hiv Hor).
}
specialize (H1 H); clear H.
destruct H1 as (N, HN).
exists N.
intros m Hm.
specialize (HN m Hm).
apply (rngl_lt_div_r Hon Hop Hiv Hor) in HN; [ | easy ].
rewrite (rngl_mul_comm Hic) in HN.
rename θ into θ'.
...
*)
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros i Hi.
  rewrite angle_div_2_pow_nat_mul; [ | easy | easy ].
  rewrite (angle_mul_nat_assoc Hon Hop).
  specialize (Nat.div_mod_eq (2 ^ i) n) as H1.
  symmetry in H1.
  apply Nat.add_sub_eq_r in H1.
  symmetry in H1.
  rewrite Nat.mul_comm in H1.
  rewrite H1; clear H1.
  rewrite angle_mul_sub_distr_r; [ | now apply Nat.mod_le ].
  rewrite angle_mul_2_pow_div_2_pow.
  rewrite angle_eucl_dist_sub_l_diag.
  now apply HN.
}
enough (H : angle_lim (λ i, (n * angle_div_2_pow_nat θ i))%A 0%A). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists (max N (S (S (Nat.log2 n)))).
  intros i Hi.
  eapply (rngl_le_lt_trans Hor). 2: {
    apply (HN i).
    now apply Nat.max_lub_l in Hi.
  }
  progress unfold angle_eucl_dist.
  cbn.
  do 2 rewrite (rngl_sub_0_l Hop).
  do 2 rewrite (rngl_squ_opp Hop).
  remember (angle_div_2_pow_nat θ i) as Δθ.
  do 2 rewrite one_sub_squ_cos_add_squ_sin.
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
  split. {
    apply angle_mul_nat_le_mono_nonneg_r. 2: {
      apply Nat.lt_le_incl.
      now apply Nat.mod_upper_bound.
    }
    subst Δθ.
    move Haov at bottom.
    apply (angle_mul_nat_overflow_le_r _ θ); [ | easy ].
    rewrite <- (angle_mul_2_pow_div_2_pow i θ) at 2.
    rewrite <- (angle_mul_1_l Hon Hos) at 1.
    apply angle_mul_nat_le_mono_nonneg_r. 2: {
      apply Nat.lt_succ_r.
      apply -> Nat.succ_lt_mono.
      clear Hi.
      (* strange that this theorem does not exist; I should add it *)
      induction i; cbn; [ easy | ].
      rewrite Nat.add_0_r.
      apply (Nat.lt_le_trans _ (2 ^ i)); [ easy | ].
      apply Nat.le_add_r.
    }
    clear Hi HN.
    apply angle_mul_nat_overflow_pow_div.
  }
  subst Δθ.
  apply Nat.max_lub_r in Hi.
  destruct i; [ easy | ].
  apply Nat.succ_le_mono in Hi.
  rewrite <- (Nat.log2_pow2 i) in Hi; [ | easy ].
  apply Nat.log2_lt_cancel in Hi.
  rewrite angle_div_2_pow_nat_succ_r_2.
  rewrite <- angle_div_2_pow_nat_mul; [ | easy | ]. {
    apply (angle_le_trans _ (angle_div_2_pow_nat (n * θ) i)). {
      apply angle_div_2_pow_nat_le.
      apply angle_mul_le_mono_l; [ | easy ].
      apply angle_div_2_le.
    }
    destruct i; [ now apply Nat.lt_1_r in Hi; subst n | ].
    clear Hi.
    induction i; [ apply angle_div_2_le_straight | ].
    remember (S i) as x; cbn; subst x.
    eapply angle_le_trans; [ | apply IHi ].
    apply angle_div_2_le.
  }
  apply (angle_mul_nat_overflow_le_r _ θ); [ | easy ].
  apply angle_div_2_le.
}
assert (Hzs2 : (0 < √2)%L). {
  apply (rngl_lt_iff Hor).
  split. {
    apply rl_sqrt_nonneg.
    apply (rngl_0_le_2 Hon Hop Hor).
  }
  intros H; symmetry in H.
  apply (eq_rl_sqrt_0 Hos) in H. {
    revert H.
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  } {
    apply (rngl_0_le_2 Hon Hop Hor).
  }
}
enough (H :
  ∀ ε, (0 < ε)%L →
  ∃ N : nat, ∀ m : nat, N ≤ m →
  (1 - ε²/2 < rngl_cos (angle_div_2_pow_nat (n * θ) m))%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N & HN).
  exists N.
  intros m Hm.
  specialize (HN m Hm).
  progress unfold angle_eucl_dist.
  cbn.
  rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_squ_opp Hop).
  remember (n * angle_div_2_pow_nat θ m)%A as θ1 eqn:Hθ1.
  rewrite (rngl_squ_sub Hop Hic Hon).
  rewrite (rngl_squ_1 Hon).
  rewrite (rngl_mul_1_r Hon).
  rewrite <- rngl_add_assoc.
  rewrite cos2_sin2_1.
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  subst θ1.
  rewrite <- (angle_div_2_pow_nat_mul _ _ _ Hnz Haov).
  rewrite rl_sqrt_mul; [ | easy | ]. 2: {
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_mul_comm Hic).
  apply (rngl_lt_div_r Hon Hop Hiv Hor); [ easy | ].
  rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
    rewrite (rngl_mul_0_l Hos).
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
    apply rl_sqrt_nonneg.
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  apply (rngl_squ_lt_abs_lt Hop Hor Hii).
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_squ_div Hic Hon Hos Hiv). 2: {
    intros H; rewrite H in Hzs2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  rewrite rngl_squ_sqrt; [ | easy ].
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  easy.
}
intros ε Hε.
specialize (rngl_cos_angle_div_2_pow_nat_tending_to_1 Hc1 Har (n * θ)) as H1.
progress unfold rngl_is_limit_when_tending_to_inf in H1.
progress unfold is_limit_when_tending_to_inf in H1.
specialize (H1 (ε² / 2))%L.
progress unfold rngl_dist in H1.
assert (H : (0 < ε² / 2)%L). {
  apply (rngl_div_lt_pos Hon Hop Hiv Hor).
  rewrite <- (rngl_squ_0 Hos). 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
  specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
  apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid).
  rewrite (rngl_abs_0 Hop).
  apply (rngl_abs_pos Hop Hor).
  intros H; rewrite H in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (H1 H); clear H.
destruct H1 as (N, HN).
exists N.
intros m Hm.
specialize (HN m Hm).
rewrite (rngl_abs_nonpos_eq Hop Hor) in HN. 2: {
  apply (rngl_le_sub_0 Hop Hor).
  apply rngl_cos_bound.
}
rewrite (rngl_opp_sub_distr Hop) in HN.
apply (rngl_lt_sub_lt_add_l Hop Hor) in HN.
now apply (rngl_lt_sub_lt_add_r Hop Hor) in HN.
Qed.

Theorem angle_mul_nat_div_2 :
  ∀ n θ,
  angle_mul_nat_overflow n θ = false
  → (n * (θ / ₂) = (n * θ) / ₂)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haov.
induction n; cbn. {
  symmetry; apply angle_0_div_2.
}
apply (angle_mul_nat_not_overflow_succ_l Hon Hos) in Haov.
rewrite IHn; [ | easy ].
symmetry.
now apply angle_div_2_add_not_overflow.
Qed.

Theorem angle_add_overflow_diag :
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → θ ≠ angle_straight
  → angle_add_overflow θ θ = false.
Proof.
destruct_ac.
intros * Hzs Hts.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
apply rngl_leb_le in Hzs.
rewrite Hzs.
apply rngl_leb_le in Hzs.
remember (0 ≤? rngl_sin (θ + θ))%L as zsd eqn:Hzsd.
symmetry in Hzsd.
destruct zsd; [ | easy ].
apply rngl_leb_le in Hzsd.
apply (rngl_ltb_ge Hor).
destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hzc| Hzc]. {
  now apply quadrant_1_rngl_cos_add_le_cos_l.
}
apply (rngl_nle_gt Hor) in Hzc.
apply angle_add_overflow_le_lemma_2; try easy. {
  intros H.
  now apply (eq_rngl_cos_opp_1) in H.
}
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_div_2_diag : ∀ θ, (θ / ₂ + θ / ₂)%A = θ.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
apply eq_angle_eq.
cbn - [ angle_div_2 ].
do 2 rewrite fold_rngl_squ.
rewrite <- (rngl_cos_mul_2_l Hon Hos).
rewrite (rngl_mul_comm Hic (rngl_cos (_ / ₂))).
rewrite (rngl_add_diag Hon).
rewrite rngl_mul_assoc.
rewrite <- (rngl_sin_mul_2_l Hic Hon Hos).
now rewrite angle_div_2_mul_2.
Qed.

Theorem angle_mul_0_l : ∀ θ, (0 * θ = 0)%A.
Proof. easy. Qed.

Theorem angle_mul_2_pow_add_distr_l :
  ∀ n θ1 θ2, (2 ^ n * (θ1 + θ2) = 2 ^ n * θ1 + 2 ^ n * θ2)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
apply eq_angle_eq.
cbn.
revert θ1 θ2.
induction n; intros. {
  cbn.
  do 6 rewrite (rngl_mul_1_r Hon).
  do 6 rewrite (rngl_mul_0_r Hos).
  do 3 rewrite (rngl_sub_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  easy.
}
rewrite Nat.pow_succ_r'.
rewrite Nat.mul_comm.
rewrite <- (angle_mul_nat_assoc Hon Hop).
rewrite <- (angle_add_diag Hon Hos).
rewrite (angle_add_add_swap Hic Hop).
rewrite (angle_add_assoc Hop).
rewrite <- (angle_add_assoc Hop).
do 2 rewrite (angle_add_diag Hon Hos).
rewrite IHn.
now do 2 rewrite (angle_mul_nat_assoc Hon Hop).
Qed.

Theorem angle_lim_eq_compat :
  ∀ a b f g θ,
  (∀ i, f (i + a) = g (i + b))
  → angle_lim f θ
  → angle_lim g θ.
Proof.
intros * Hfg Hf.
intros ε Hε.
specialize (Hf ε Hε).
destruct Hf as (N, HN).
exists (N + max a b).
intros n Hn.
specialize (HN (n - b + a)).
assert (H : N ≤ n - b + a) by flia Hn.
specialize (HN H).
rewrite Hfg in HN.
rewrite Nat.sub_add in HN; [ easy | flia Hn ].
Qed.

Theorem rngl_cos_div_2 :
  ∀ θ,
  rngl_cos (θ / ₂) =
  ((if (0 ≤? rngl_sin θ)%L then 1%L else (-1)%L) *
   √((1 + rngl_cos θ) / 2))%L.
Proof. easy. Qed.

Theorem rngl_sin_div_2 :
  ∀ θ, rngl_sin (θ / ₂) = √((1 - rngl_cos θ) / 2)%L.
Proof. easy. Qed.

Theorem angle_mul_sub_distr_l :
  ∀ n θ1 θ2, (n * (θ1 - θ2) = n * θ1 - n * θ2)%A.
Proof.
destruct_ac.
intros.
revert θ1 θ2.
induction n; intros; cbn; [ symmetry; apply angle_sub_diag | ].
rewrite (angle_sub_add_distr Hic Hop).
rewrite (angle_add_sub_swap Hic Hop).
rewrite <- (angle_add_sub_assoc Hop).
f_equal.
apply IHn.
Qed.

Theorem angle_lim_div_2 :
  ∀ f θ,
  angle_lim f (θ / ₂)
  → angle_lim (λ i, (2 * f i)%A) θ.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros * Hf ε Hε.
  rewrite (rngl_characteristic_1 Hon Hos Hc1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hf.
intros ε Hε.
assert (H2ε : (0 < ε / 2)%L). {
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  now rewrite (rngl_mul_0_l Hos).
}
specialize (Hf _ H2ε)%L.
destruct Hf as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
rewrite angle_eucl_dist_move_0_l in HN.
rewrite angle_eucl_dist_move_0_l.
specialize (angle_eucl_dist_triangular) as H1.
specialize (H1 (2 * (θ / ₂ - f n)) (θ / ₂ - f n) 0)%A.
rewrite angle_mul_sub_distr_l in H1.
rewrite angle_div_2_mul_2 in H1.
eapply (rngl_le_lt_trans Hor); [ apply H1 | ].
rewrite <- (angle_add_div_2_diag θ) at 1.
rewrite (angle_mul_add_distr_r Hon Hop 1)%L.
rewrite (angle_mul_1_l Hon Hos).
rewrite (angle_sub_add_distr Hic Hop).
rewrite (angle_add_sub_swap Hic Hop).
rewrite (angle_add_sub_swap Hic Hop).
rewrite <- (angle_sub_sub_distr Hic Hop).
rewrite angle_eucl_dist_sub_l_diag.
rewrite <- angle_eucl_dist_opp_opp.
rewrite (angle_opp_sub_distr Hic Hop).
rewrite angle_opp_0.
rewrite <- (rngl_mul_div_r Hon Hiv ε 2)%L.
rewrite (rngl_mul_comm Hic). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite <- (rngl_add_diag Hon).
apply (rngl_add_lt_compat Hop Hor _ _ _ _ HN HN).
Qed.

Theorem angle_div_pow_2_add_distr :
  ∀ i j θ, (θ / ₂^(i + j) = θ / ₂^i / ₂^j)%A.
Proof.
intros.
revert j θ.
induction i; intros; [ easy | ].
rewrite Nat.add_succ_l.
do 2 rewrite angle_div_2_pow_nat_succ_r_2.
apply IHi.
Qed.

Theorem angle_lim_add_add :
  ∀ u v θ1 θ2,
  angle_lim u θ1
  → angle_lim v θ2
  → angle_lim (λ i, (u i + v i))%A (θ1 + θ2).
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros * Hu Hv ε Hε.
  rewrite (rngl_characteristic_1 Hon Hos Hc1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hu Hv.
intros ε Hε.
assert (Hε2 : (0 < ε / 2)%L). {
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  now rewrite (rngl_mul_0_l Hos).
}
specialize (Hu _ Hε2).
specialize (Hv _ Hε2).
destruct Hu as (M, HM).
destruct Hv as (N, HN).
exists (max M N).
intros n Hn.
specialize (HM n (Nat.max_lub_l _ _ _ Hn)).
specialize (HN n (Nat.max_lub_r _ _ _ Hn)).
rewrite angle_eucl_dist_move_0_l in HM, HN.
rewrite angle_eucl_dist_move_0_l.
specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as Hεε2.
rewrite (rngl_add_diag2 Hon) in Hεε2.
rewrite (rngl_mul_div Hi1) in Hεε2. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite Hεε2.
eapply (rngl_le_lt_trans Hor). {
  apply (angle_eucl_dist_triangular _ (θ1 - u n)).
}
apply (rngl_add_lt_compat Hop Hor); [ | easy ].
rewrite (angle_add_comm Hic).
rewrite angle_eucl_dist_move_0_r.
rewrite (angle_sub_sub_swap Hic Hop).
rewrite (angle_sub_sub_distr Hic Hop).
rewrite angle_add_sub.
rewrite (angle_sub_add_distr Hic Hop).
now rewrite angle_add_sub.
Qed.

Theorem angle_lim_add_add_if :
  ∀ u v θ1 θ2,
  angle_lim u θ1
  → angle_lim (λ i : nat, (u i + v i)%A) (θ1 + θ2)
  → angle_lim v θ2.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros * Hu Huv ε Hε.
  rewrite (rngl_characteristic_1 Hon Hos Hc1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hu Huv.
intros ε Hε.
assert (Hε2 : (0 < ε / 2)%L). {
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  now rewrite (rngl_mul_0_l Hos).
}
specialize (Hu _ Hε2).
specialize (Huv _ Hε2).
destruct Hu as (M, HM).
destruct Huv as (N, HN).
exists (max M N).
intros n Hn.
specialize (HM n (Nat.max_lub_l _ _ _ Hn)).
specialize (HN n (Nat.max_lub_r _ _ _ Hn)).
rewrite angle_eucl_dist_move_0_l in HM, HN.
rewrite angle_eucl_dist_move_0_l.
specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as Hεε2.
rewrite (rngl_add_diag2 Hon) in Hεε2.
rewrite (rngl_mul_div Hi1) in Hεε2. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite Hεε2.
eapply (rngl_le_lt_trans Hor). {
  apply (angle_eucl_dist_triangular _ (u n - θ1)).
}
rewrite <- (angle_eucl_dist_opp_opp (u n - θ1)).
rewrite (angle_opp_sub_distr Hic Hop).
rewrite angle_opp_0.
apply (rngl_add_lt_compat Hop Hor); [ | easy ].
rewrite angle_eucl_dist_move_0_l.
rewrite <- angle_eucl_dist_opp_opp.
rewrite (angle_opp_sub_distr Hic Hop).
rewrite (angle_sub_sub_distr Hic Hop).
do 2 rewrite <- (angle_add_sub_swap Hic Hop).
rewrite (angle_add_comm Hic).
rewrite <- (angle_sub_add_distr Hic Hop).
rewrite (angle_add_comm Hic (v n)).
now rewrite angle_opp_0.
Qed.

Theorem angle_lim_mul :
  ∀ k u θ,
  angle_lim u θ
  → angle_lim (λ i, (k * u i)%A) (k * θ).
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros * Hu.
induction k. {
  intros ε Hε.
  exists 0.
  intros n _.
  progress unfold angle_eucl_dist.
  cbn.
  do 2 rewrite (rngl_sub_diag Hos).
  rewrite (rngl_squ_0 Hos).
  rewrite rngl_add_0_l.
  now rewrite (rl_sqrt_0 Hop Hic Hor Hid).
}
cbn.
now apply angle_lim_add_add.
Qed.

Theorem angle_0_div_2_pow : ∀ n, (0 / ₂^n = 0)%A.
Proof.
intros.
induction n; [ easy | cbn ].
rewrite IHn.
apply angle_0_div_2.
Qed.

Theorem angle_eucl_dist_nonneg : ∀ θ1 θ2, (0 ≤ angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
apply rl_sqrt_nonneg.
apply (rngl_add_squ_nonneg Hop Hor).
Qed.

Theorem angle_lim_const :
  ∀ θ1 θ2, angle_lim (λ _, θ1) θ2 → θ2 = θ1.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
  intros.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  rewrite (H1 θ1); apply H1.
}
intros * H1.
progress unfold angle_lim in H1.
progress unfold is_limit_when_tending_to_inf in H1.
apply angle_eucl_dist_separation.
rewrite (angle_eucl_dist_symmetry Hic Hop).
specialize (angle_eucl_dist_nonneg θ1 θ2) as Hzx.
remember (angle_eucl_dist θ1 θ2) as x eqn:Hx.
clear θ1 θ2 Hx.
specialize (proj1 (rngl_lt_eq_cases Hor _ x) Hzx) as H3.
destruct H3 as [H3| H3]; [ | easy ].
clear Hzx; exfalso.
specialize (H1 (x / 2)%L).
assert (H : (0 < x / 2)%L). {
  apply (rngl_div_lt_pos Hon Hop Hiv Hor); [ easy | ].
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
specialize (H1 H); clear H.
destruct H1 as (N, HN).
specialize (HN N (Nat.le_refl _)).
apply (rngl_nle_gt Hor) in HN.
apply HN; clear HN.
apply (rngl_le_div_l Hon Hop Hiv Hor).
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
rewrite <- (rngl_add_diag2 Hon).
apply (rngl_le_add_l Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_eucl_dist_diag : ∀ θ, angle_eucl_dist θ θ = 0%L.
Proof.
intros.
now apply angle_eucl_dist_separation.
Qed.

Theorem angle_add_div_2_pow_diag :
  ∀ n θ, (θ / ₂^S n + θ / ₂^S n = θ / ₂^n)%A.
Proof.
intros; cbn.
now rewrite angle_add_div_2_diag.
Qed.

Theorem sequence_false_min :
  ∀ n u,
  u 0 = false
  → u n = true
  → ∃ i, u i = false ∧ u (S i) = true.
Proof.
intros * Huz Hun.
revert u Huz Hun.
induction n; intros; [ now rewrite Huz in Hun | ].
rename Hun into Husn.
remember (u n) as un eqn:Hun.
symmetry in Hun.
destruct un; [ | now exists n ].
now apply IHn.
Qed.

Theorem angle_mul_nat_overflow_true_after :
  ∀ m n θ,
  m ≤ n
  → angle_mul_nat_overflow m θ = true
  → angle_mul_nat_overflow n θ = true.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hmn Hm.
destruct (Nat.eq_dec m n) as [H1| H1]; [ now subst m | ].
assert (H : m < n) by flia Hmn H1.
clear Hmn H1; rename H into Hmn.
revert m Hmn Hm.
induction n; intros; [ easy | ].
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hmn.
apply (angle_mul_nat_overflow_succ_l Hon Hos) in Hm.
apply (angle_mul_nat_overflow_succ_l Hon Hos).
destruct Hm as [Hm| Hm]. {
  left.
  now apply (IHn m).
}
left.
destruct (Nat.eq_dec (S m) n) as [Hsmn| Hsmn]. 2: {
  apply (IHn (S m)); [ flia Hmn Hsmn | ].
  apply (angle_mul_nat_overflow_succ_l Hon Hos).
  now right.
}
subst n.
apply (angle_mul_nat_overflow_succ_l Hon Hos).
now right.
Qed.

Theorem angle_mul_nat_overflow_exist :
  ∀ n θ,
  angle_mul_nat_overflow n θ = true
  → ∃ m,
  m < n ∧
  (∀ p, p ≤ m → angle_add_overflow θ (p * θ) = false) ∧
  angle_add_overflow θ (S m * θ) = true.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hn.
specialize (sequence_false_min n (λ i, angle_mul_nat_overflow i θ)) as H1.
specialize (H1 eq_refl Hn).
destruct H1 as (i & Hi & Hsi).
destruct i; [ easy | ].
rewrite (angle_mul_nat_not_overflow_succ_l Hon Hos) in Hi.
destruct Hi as (Hi, Hit).
exists i.
split. {
  apply Nat.nle_gt.
  intros Hni.
  apply (angle_mul_nat_overflow_true_after _ i) in Hn; [ | easy ].
  now rewrite Hn in Hi.
}
split. {
  intros p Hpi.
  apply angle_add_overflow_le with (θ2 := (i * θ)%A); [ | easy ].
  now apply angle_mul_nat_le_mono_nonneg_r.
}
rewrite (angle_mul_nat_overflow_succ_l Hon Hos) in Hsi.
destruct Hsi as [Hsi| Hsi]; [ | easy ].
rewrite (angle_mul_nat_overflow_succ_l Hon Hos) in Hsi.
destruct Hsi as [Hsi| Hsi]; [ now rewrite Hi in Hsi | ].
now rewrite Hit in Hsi.
Qed.

Theorem angle_all_add_not_overflow :
  ∀ n θ,
  (∀ m, m < n → angle_add_overflow θ (m * θ) = false)
  → angle_mul_nat_overflow n θ = false.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Ha.
induction n; [ easy | ].
rewrite (angle_mul_nat_not_overflow_succ_l Hon Hos).
split; [ | now apply Ha ].
apply IHn.
intros m Hm.
apply Ha.
now apply Nat.lt_lt_succ_r.
Qed.

Theorem angle_mul_add_distr_l :
  ∀ n θ1 θ2, (n * (θ1 + θ2) = n * θ1 + n * θ2)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
induction n. {
  do 3 rewrite angle_mul_0_l.
  symmetry.
  apply (angle_add_0_l Hon Hos).
}
cbn.
rewrite IHn.
do 2 rewrite (angle_add_assoc Hop).
now rewrite (angle_add_add_swap Hic Hop θ1 _ θ2).
Qed.

Theorem angle_add_move_0_r : ∀ θ1 θ2, (θ1 + θ2 = 0 ↔ θ1 = (- θ2))%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
split; intros H12. {
  rewrite <- (angle_sub_0_l Hon Hos).
  rewrite <- H12; symmetry.
  apply angle_add_sub.
} {
  subst θ1.
  rewrite (angle_add_opp_l Hic).
  apply angle_sub_diag.
}
Qed.

Theorem rngl_leb_opp_r :
  ∀ a b, (a ≤? -b)%L = (b ≤? -a)%L.
Proof.
destruct_ac.
intros.
remember (a ≤? -b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_leb_le in Hab.
  apply rngl_leb_le.
  apply (rngl_le_opp_r Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_le_opp_r Hop Hor) in Hab.
} {
  apply (rngl_leb_gt Hor) in Hab.
  apply (rngl_leb_gt Hor).
  apply (rngl_lt_opp_l Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_lt_opp_l Hop Hor).
}
Qed.

Theorem angle_opp_div_2 :
  ∀ θ, ((- θ) / ₂ = - (θ / ₂) + if (θ =? 0)%A then 0 else angle_straight)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
intros.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  rewrite angle_add_0_r.
  apply (angle_eqb_eq Hed) in Htz.
  subst θ.
  rewrite angle_0_div_2.
  rewrite angle_opp_0.
  now rewrite angle_0_div_2.
}
apply (angle_eqb_neq Hed) in Htz.
apply eq_angle_eq.
cbn.
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
do 2 rewrite (rngl_mul_opp_r Hop).
do 2 rewrite (rngl_mul_1_r Hon).
rewrite rngl_leb_opp_r.
rewrite (rngl_opp_0 Hop).
rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_l.
rewrite (rngl_opp_involutive Hop).
f_equal.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
remember (rngl_sin θ ≤? 0)%L as sz eqn:Hsz.
symmetry in Hzs, Hsz.
destruct zs. {
  apply rngl_leb_le in Hzs.
  rewrite (rngl_mul_1_l Hon).
  destruct sz. {
    apply rngl_leb_le in Hsz.
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_le_antisymm Hor) in Hsz; [ | easy ].
    symmetry in Hsz.
    apply eq_rngl_sin_0 in Hsz.
    destruct Hsz; subst θ; [ easy | cbn ].
    rewrite (rngl_add_opp_r Hop).
    rewrite (rngl_sub_diag Hos).
    rewrite (rngl_div_0_l Hos Hi1). 2: {
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    symmetry.
    rewrite (rl_sqrt_0 Hop Hic Hor Hid).
    apply (rngl_opp_0 Hop).
  }
  rewrite (rngl_mul_opp_l Hop).
  now rewrite (rngl_mul_1_l Hon).
} {
  apply (rngl_leb_gt Hor) in Hzs.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_opp_involutive Hop).
  destruct sz; [ now rewrite (rngl_mul_1_l Hon) | ].
  apply (rngl_leb_gt Hor) in Hsz.
  apply (rngl_nle_gt Hor) in Hsz.
  exfalso.
  apply Hsz.
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem rngl_cos_div_2_nonneg :
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → (0 ≤ rngl_cos (θ / ₂))%L.
Proof.
destruct_ac.
intros * Hzs.
cbn.
apply rngl_leb_le in Hzs.
rewrite Hzs.
rewrite (rngl_mul_1_l Hon).
apply rl_sqrt_nonneg.
apply rngl_1_add_cos_div_2_nonneg.
Qed.

Theorem angle_straight_neq_0 :
  rngl_characteristic T ≠ 1
  → angle_straight ≠ 0%A.
Proof.
destruct_ac.
intros Hc1 Hs2z.
apply eq_angle_eq in Hs2z.
cbn in Hs2z.
injection Hs2z; clear Hs2z; intros H1.
exfalso; revert H1.
apply (rngl_lt_iff Hor).
apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
Qed.

Theorem rngl_cos_div_pow_2_decr :
  ∀ n θ1 θ2,
  (θ2 ≤ θ1 ≤ angle_straight)%A
  → (rngl_cos_div_pow_2 θ1 n ≤ rngl_cos_div_pow_2 θ2 n)%L.
Proof.
destruct_ac.
intros * H21.
revert θ1 θ2 H21.
induction n; intros; [ now apply rngl_cos_decr | ].
rewrite rngl_cos_div_pow_2_succ_r. 2: {
  destruct H21 as (_, H1).
  progress unfold angle_leb in H1.
  cbn in H1.
  rewrite (rngl_leb_refl Hor) in H1.
  remember (0 ≤? rngl_sin θ1)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs; [ | easy ].
  now apply rngl_leb_le in Hzs.
}
rewrite rngl_cos_div_pow_2_succ_r. 2: {
  assert (H2 : (θ2 ≤ angle_straight)%A) by now apply (angle_le_trans _ θ1).
  progress unfold angle_leb in H2.
  cbn in H2.
  rewrite (rngl_leb_refl Hor) in H2.
  remember (0 ≤? rngl_sin θ2)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs; [ | easy ].
  now apply rngl_leb_le in Hzs.
}
apply IHn.
split; [ | apply angle_div_2_le_straight ].
now apply angle_div_2_le_compat.
Qed.

Definition two_straight_div_2_pow i :=
  match i with
  | 0 => 0%A
  | S i' => (angle_straight / ₂^i')%A
  end.

Theorem angle_mul_2_div_2_pow :
  ∀ i θ,
  angle_mul_nat_overflow 2 θ = true
  → ((2 * θ) / ₂^i = 2 * (θ / ₂^i) - two_straight_div_2_pow i)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
intros * Hmov.
cbn.
apply (angle_mul_nat_overflow_succ_l Hon Hos) in Hmov.
cbn in Hmov.
destruct Hmov as [Hmov| Haov]; [ easy | ].
rewrite angle_add_0_r in Haov.
do 2 rewrite angle_add_0_r.
rewrite angle_div_2_pow_nat_add'.
rewrite Haov.
rewrite angle_add_div_2_diag.
destruct i. {
  cbn; symmetry.
  apply (angle_sub_0_r Hon Hop).
}
cbn.
rewrite angle_add_div_2_diag.
(**)
induction i. {
  cbn.
  progress unfold angle_sub.
  f_equal.
  apply eq_angle_eq; cbn; f_equal; symmetry.
  apply (rngl_opp_0 Hop).
}
cbn.
rewrite IHi.
progress unfold angle_sub.
rewrite angle_div_2_add.
rewrite angle_add_opp_r.
rewrite angle_opp_div_2.
remember (angle_straight / ₂^i =? 0)%A as s2z eqn:Hs2z.
symmetry in Hs2z.
destruct s2z. {
  apply (angle_eqb_eq Hed) in Hs2z.
  apply eq_angle_div_2_pow_nat_0 in Hs2z.
  now apply (angle_straight_neq_0 Hc1) in Hs2z.
}
clear Hs2z.
rewrite (angle_add_assoc Hop).
rewrite <- (angle_add_assoc Hop).
rewrite (angle_straight_add_straight Hon Hop).
rewrite angle_add_0_r.
rewrite angle_add_opp_r.
remember (angle_add_overflow (θ / ₂^i) (- (angle_straight / ₂^i))) as aov2
  eqn:Haov2.
symmetry in Haov2.
destruct aov2; [ easy | ].
exfalso.
apply Bool.not_true_iff_false in Haov2.
apply Haov2; clear Haov2.
progress unfold angle_add_overflow.
rewrite angle_add_opp_r.
progress unfold angle_ltb.
rewrite <- IHi.
remember (0 ≤? rngl_sin ((θ + angle_straight) / ₂^i))%L as zs eqn:Hzs.
remember (0 ≤? rngl_sin (θ / ₂^i))%L as zs2 eqn:Hzs2.
symmetry in Hzs, Hzs2.
destruct zs. {
  apply rngl_leb_le in Hzs.
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs2.
  apply rngl_ltb_lt.
  rewrite IHi.
  rewrite (rngl_cos_sub_comm Hic Hop).
  destruct i. {
    cbn - [ rngl_sin ] in Hzs, Hzs2.
    rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs.
    apply (rngl_le_antisymm Hor) in Hzs; [ | easy ].
    symmetry in Hzs.
    apply eq_rngl_sin_0 in Hzs.
    destruct Hzs; subst θ. {
      now rewrite (angle_add_overflow_0_0 Hon Hos) in Haov.
    }
    cbn - [ rngl_cos ].
    rewrite angle_sub_diag; cbn.
    apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
  }
  apply (rngl_lt_iff Hor).
  split. {
    rewrite (rngl_cos_sub_comm Hic Hop).
    apply rngl_cos_decr.
    split. {
      rewrite <- IHi.
      apply angle_div_2_pow_nat_le.
      progress unfold angle_add_overflow in Haov.
      progress unfold angle_ltb in Haov.
      progress unfold angle_leb.
      rewrite (rngl_sin_add_straight_r Hon Hop).
      rewrite rngl_leb_opp_r.
      rewrite (rngl_opp_0 Hop).
      remember (0 ≤? rngl_sin θ)%L as zst eqn:Hzst.
      symmetry in Hzst.
      destruct zst. {
        apply rngl_leb_le in Hzst.
        remember (0 ≤? rngl_sin (θ + θ))%L as zstt eqn:Hzstt.
        symmetry in Hzstt.
        destruct zstt; [ | easy ].
        apply rngl_leb_le in Hzstt.
        apply rngl_ltb_lt in Haov.
        rewrite (rngl_cos_add_straight_r Hon Hop).
        remember (rngl_sin θ ≤? 0)%L as sz eqn:Hsz.
        symmetry in Hsz.
        destruct sz. {
          apply rngl_leb_le.
          apply rngl_leb_le in Hsz.
          apply (rngl_le_antisymm Hor) in Hsz; [ | easy ].
          symmetry in Hsz.
          apply eq_rngl_sin_0 in Hsz.
          destruct Hsz; subst θ. {
            cbn in Haov.
            rewrite (rngl_mul_1_l Hon) in Haov.
            rewrite (rngl_mul_0_l Hos) in Haov.
            rewrite (rngl_sub_0_r Hos) in Haov.
            now apply (rngl_lt_irrefl Hor) in Haov.
          }
          cbn.
          rewrite (rngl_opp_involutive Hop).
          apply (rngl_opp_1_le_1 Hon Hop Hor Hc1).
        }
        exfalso.
        apply (rngl_leb_gt Hor) in Hsz.
        apply (rngl_nle_gt Hor) in Haov.
        apply Haov; clear Haov.
        apply angle_add_overflow_le_lemma_111; try easy.
        left.
        intros H; subst θ.
        cbn in Hsz.
        now apply (rngl_lt_irrefl Hor) in Hsz.
      }
      remember (rngl_sin θ ≤? 0)%L as sz eqn:Hsz.
      symmetry in Hsz.
      destruct sz; [ easy | ].
      apply (rngl_leb_gt Hor) in Hzst.
      apply (rngl_leb_gt Hor) in Hsz.
      apply (rngl_lt_le_incl Hor) in Hsz.
      now apply (rngl_nlt_ge Hor) in Hsz.
    }
    rewrite angle_div_2_pow_nat_succ_r_1.
    apply angle_div_2_le_straight.
  }
  intros H.
  rewrite (rngl_cos_sub_comm Hic Hop) in H.
  apply rngl_cos_eq in H.
  destruct H as [H| H]. {
    symmetry in H.
    apply angle_sub_move_l in H.
    rewrite angle_sub_diag in H.
    apply eq_angle_div_2_pow_nat_0 in H.
    now apply (angle_straight_neq_0 Hc1) in H.
  }
  rewrite (angle_opp_sub_distr Hic Hop) in H.
  symmetry in H.
  apply angle_sub_move_r in H.
  rewrite angle_add_div_2_pow_diag in H.
  rewrite angle_div_2_pow_nat_succ_r_2 in H.
  apply (f_equal (λ a, (2 ^ i * a)%A)) in H.
  do 2 rewrite angle_mul_2_pow_div_2_pow in H.
  subst θ.
  apply Bool.not_false_iff_true in Haov.
  apply Haov.
  apply angle_add_overflow_div_2_div_2.
}
apply (rngl_leb_gt Hor) in Hzs.
destruct zs2. {
  exfalso.
  apply rngl_leb_le in Hzs2.
  rewrite IHi in Hzs.
  apply (rngl_leb_gt Hor) in Hzs.
  apply Bool.not_true_iff_false in Hzs.
  apply Hzs; clear Hzs.
  apply rngl_leb_le.
  apply rngl_sin_sub_nonneg; [ easy | | ]. {
    destruct i; [ cbn; apply (rngl_le_refl Hor) | ].
    now apply rngl_sin_div_2_pow_nat_nonneg.
  }
  destruct i. {
    cbn in Hzs2 |-*.
    destruct (rngl_eq_dec Hed (rngl_cos θ) (-1)) as [Hco1| Hco1]. {
      apply eq_rngl_cos_opp_1 in Hco1.
      subst θ.
      apply (rngl_le_refl Hor).
    }
    exfalso.
    apply Bool.not_false_iff_true in Haov.
    apply Haov.
    apply angle_add_overflow_diag; [ easy | ].
    now intros H; subst θ.
  }
  do 2 rewrite rngl_cos_div_pow_2_eq.
  apply rngl_cos_div_pow_2_decr.
  split; [ | apply angle_div_2_le_straight ].
  apply angle_div_2_le_compat.
  progress unfold angle_leb.
  cbn.
  rewrite (rngl_leb_refl Hor).
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs; [ | easy ].
  apply rngl_leb_le.
  apply rngl_leb_le in Hzs.
  remember (0 ≤? rngl_sin (θ + θ))%L as zss eqn:Hzss.
  symmetry in Hzss.
  destruct (rngl_eq_dec Hed (rngl_cos θ) (-1)) as [Hco1| Hco1]. {
    apply eq_rngl_cos_opp_1 in Hco1.
    subst θ.
    apply (rngl_le_refl Hor).
  }
  exfalso.
  apply Bool.not_false_iff_true in Haov.
  apply Haov.
  apply angle_add_overflow_diag; [ easy | ].
  now intros H; subst θ.
}
apply (rngl_leb_gt Hor) in Hzs2.
destruct i. {
  cbn - [ rngl_sin ] in Hzs.
  rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs.
  cbn in Hzs2.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs.
  apply (rngl_lt_le_incl Hor) in Hzs.
  now apply (rngl_nlt_ge Hor) in Hzs.
}
exfalso.
apply (rngl_nle_gt Hor) in Hzs2.
apply Hzs2; clear Hzs2.
cbn.
apply rl_sqrt_nonneg.
apply rngl_1_sub_cos_div_2_nonneg.
Qed.

(* seems false, the hypothesis angle_mul_nat_overflow n θ = false
   seems required
Theorem angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat' :
  rngl_is_archimedean T = true →
  rngl_characteristic T = 0 →
  ∀ n θ,
  n ≠ 0
  → angle_lim (seq_angle_converging_to_angle_div_nat (n * θ) n) θ.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros Har Hch * Hnz ε Hε.
  rewrite (rngl_characteristic_1 Hon Hos Hc1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros Har Hch * Hnz.
remember (angle_mul_nat_overflow n θ) as nt eqn:Hnt.
symmetry in Hnt.
destruct nt. 2: {
  now apply (angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat Har Hch).
}
specialize (angle_mul_nat_overflow_le_l _ _ Hnt) as Hmt.
apply angle_mul_nat_overflow_exist in Hnt.
destruct Hnt as (m & Hmn & Hm & Hsm).
(*
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  subst m.
  cbn in Hsm.
  rewrite angle_add_0_r in Hsm.
  clear Hm.
  progress unfold seq_angle_converging_to_angle_div_nat.
...
*)
set (j := S (Nat.log2 n)).
assert (Hjn : n < 2 ^ j). {
  subst j.
  apply Nat.log2_spec.
  now apply Nat.neq_0_lt_0.
}
remember (θ / ₂^j)%A as θ'' eqn:Hθ''.
assert (Htj : angle_mul_nat_overflow n θ'' = false). {
  subst θ''.
  subst j.
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ S (Nat.log2 n))). {
    now apply Nat.lt_le_incl.
  }
  apply angle_mul_nat_overflow_pow_div.
}
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat as H1.
specialize (H1 Har Hch _ _ Hnz Htj)%A.
rename θ into θ'.
progress unfold seq_angle_converging_to_angle_div_nat in H1.
progress unfold seq_angle_converging_to_angle_div_nat.
(*
eapply (angle_lim_eq_compat 0 0) in H1. 2: {
  intros i.
  rewrite Nat.add_0_r.
  rewrite angle_div_2_pow_nat_mul; [ | easy | easy ].
  rewrite (angle_mul_nat_assoc Hon Hop).
  easy.
}
apply (angle_lim_mul (2 ^ j)) in H1.
rewrite Hθ'' in H1 at 1.
rewrite angle_mul_2_pow_div_2_pow in H1.
eapply (angle_lim_eq_compat 0 0) in H1. 2: {
  intros i.
  rewrite Nat.add_0_r.
  rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite Nat.mul_comm.
  rewrite <- (angle_mul_nat_assoc Hon Hop).
  rewrite <- angle_div_2_pow_nat_mul; cycle 1. {
    now apply Nat.pow_nonzero.
  } {
    rewrite Hθ''.
    apply angle_mul_nat_overflow_pow_div.
  }
  reflexivity.
}
rewrite Hθ'' in H1.
rewrite angle_mul_2_pow_div_2_pow in H1.
...
*)
apply (angle_lim_mul (2 ^ j)) in H1.
rewrite Hθ'' in H1.
rewrite angle_mul_2_pow_div_2_pow in H1.
eapply (angle_lim_eq_compat 0 0) in H1. 2: {
  intros i.
  rewrite Nat.add_0_r.
  rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite Nat.mul_comm.
  rewrite <- (angle_mul_nat_assoc Hon Hop).
  rewrite angle_div_2_pow_nat_mul; [ | easy | now rewrite <- Hθ'' ].
  do 2 rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite Nat.mul_shuffle0.
  rewrite <- (angle_mul_nat_assoc Hon Hop).
  rewrite <- angle_div_pow_2_add_distr.
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
  rewrite angle_mul_2_pow_div_2_pow.
  rewrite <- (angle_mul_nat_assoc Hon Hop).
  reflexivity.
}
(*
  Htj : angle_mul_nat_overflow n θ'' = false
  H1 : angle_lim (λ i : nat, (2 ^ i / n * (n * (θ' / ₂^i)))%A) θ'
  ============================
  angle_lim (λ i : nat, (2 ^ i / n * ((n * θ') / ₂^i))%A) θ'
*)
(*
eapply (angle_lim_eq_compat j 0) in H1. 2: {
  intros i; rewrite Nat.add_0_r.
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
  rewrite <- angle_div_2_pow_nat_mul; [ | easy | now rewrite <- Hθ'' ].
  rewrite Nat.add_comm.
  easy.
}
*)
(*
eapply (angle_lim_eq_compat 0 0) in H1. 2: {
  intros i; rewrite Nat.add_0_r.
  rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite Nat.mul_comm.
  rewrite <- (angle_mul_nat_assoc Hon Hop).
  easy.
}
*)
(*
eapply (angle_lim_eq_compat 0 j). {
  intros i; rewrite Nat.add_0_r; symmetry.
  reflexivity.
}
eapply (angle_lim_eq_compat j 0) in H1. 2: {
  intros i; rewrite Nat.add_0_r; symmetry.
  reflexivity.
}
*)
intros ε Hε.
(**)
assert (Hε2 : (0 < ε / 2)%L). {
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  now rewrite (rngl_mul_0_l Hos).
}
specialize (H1 _ Hε2).
destruct H1 as (N, HN).
exists (max N j).
intros i Hi.
specialize (HN i).
assert (H : N ≤ i). {
  apply (Nat.le_trans _ (max N j)); [ | easy ].
  now apply Nat.le_max_l.
}
specialize (HN H); clear H.
remember (2 ^ i / n * (n * (θ' / ₂^i)))%A as θ.
eapply (rngl_le_lt_trans Hor). {
  apply (angle_eucl_dist_triangular _ θ).
}
specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as Hεε2.
rewrite (rngl_add_diag2 Hon) in Hεε2.
rewrite (rngl_mul_div Hi1) in Hεε2. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite Hεε2; clear Hεε2.
apply (rngl_add_lt_compat Hop Hor); [ | easy ].
subst θ.
rewrite angle_eucl_dist_move_0_r.
destruct (Nat.eq_dec n 2) as [Hn2| Hn2]. {
  subst n.
  rewrite angle_mul_2_div_2_pow; [ | now apply Hmt ].
  rewrite angle_mul_sub_distr_l.
  rewrite (angle_sub_sub_swap Hic Hop).
  rewrite angle_sub_diag.
  rewrite (angle_sub_0_l Hon Hos).
  rewrite <- angle_eucl_dist_opp_opp.
  rewrite (angle_opp_involutive Hop).
  rewrite angle_opp_0.
Check angle_mul_2_div_2_pow.
...
2: {
...
rewrite angle_eucl_dist_move_0_l in HN.
rewrite angle_eucl_dist_move_0_l.
...
Search (_ → angle_add_overflow _ _ = false).
angle_add_overflow_diag: ∀ θ : angle T, (0 ≤ rngl_sin θ)%L → θ ≠ angle_straight → angle_add_overflow θ θ = false
rngl_cos_div_pow_2_eq: ∀ (θ : angle T) (n : nat), rngl_cos (θ / ₂^S n) = rngl_cos_div_pow_2 (θ / ₂) n
...
    rewrite <- IHi in H.
...
apply angle_add_overflow_le_lemma_4 with (θ2 := θ); try easy.
apply quadrant_1_rngl_cos_add_le_cos_l; try easy.
...
}
Search (_ / ₂ ≤ angle_straight)%A.
apply angle_div_2_le_straight.
}
intros H.
Search (rngl_cos _ = rngl_cos _)%L.
rewrite (rngl_cos_sub_comm Hic Hop) in H.
apply rngl_cos_eq in H.
destruct H as [H| H]. {
rewrite <- IHi in H.
Search (_ / ₂^_ = _ / ₂^_)%A.
Search (_ / ₂ = _ / ₂)%A.
...
Search (_ / ₂^_ - _ / ₂^_)%A.
Search (_ - _ ≤ _)%A.
...
    apply rngl_cos_lt_rngl_cos_sub; try easy. {
      apply (rngl_lt_iff Hor).
      split; [ now apply rngl_sin_div_2_pow_nat_nonneg | ].
      intros H; symmetry in H.
      apply eq_rngl_sin_0 in H.
      apply (angle_eqb_neq Hed) in Hs2z.
      destruct H as [H| H]; [ easy | ].
      apply eq_angle_eq in H.
      injection H; clear H; intros H1 H2.
      apply (eq_rl_sqrt_0 Hos) in H1. 2: {
        apply rngl_1_sub_cos_div_2_nonneg.
      }
      progress unfold rngl_div in H1.
      rewrite Hiv in H1.
      apply (rngl_eq_mul_0_l Hos Hii) in H1. 2: {
        apply (rngl_inv_neq_0 Hon Hos Hiv).
        apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
      }
      apply -> (rngl_sub_move_0_r Hop) in H1.
      symmetry in H1.
      apply eq_rngl_cos_1 in H1.
      apply eq_angle_div_2_pow_nat_0 in H1.
      apply eq_angle_eq in H1.
      cbn in H1.
      injection H1; clear H1; intros H1.
      exfalso; revert H1.
      apply (rngl_lt_iff Hor).
      apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
    }
(* mais ça, c'est faux, en fait, maintenant que j'y réfléchis *)
...
Check rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff.
Check rngl_cos_decr.
apply (rngl_lt_iff Hor).
split. {
  apply rngl_cos_le_anticompat_when_sin_nonneg; try easy.
  apply rngl_
...
Theorem glop :
  ∀ θ1 θ2,
  (θ2 < θ1)
  (rngl_cos (θ1 / ₂) < rngl_cos (θ2 / ₂))%L.
...
do 2 rewrite angle_div_2_pow_nat_succ_r_1.
apply glop.
...
Check rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff.
Search (rngl_cos _ < rngl_cos _)%L.
    apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy. {
      rewrite angle_div_2_pow_nat_succ_r_1.
      apply rngl_sin_div_2_nonneg.
    } {
      rewrite angle_div_2_pow_nat_succ_r_1.
      apply rngl_cos_div_2_nonneg.
      destruct i; [ apply (rngl_le_refl Hor) | ].
      now apply rngl_sin_div_2_pow_nat_nonneg.
    } {
      rewrite angle_div_2_pow_nat_succ_r_1.
...
      apply rngl_cos_div_2_nonneg.
      destruct i. {
cbn.
        cbn in IHi.

cbn in *.

cbn - [ rngl_sin ] in Hzs.
cbn in IHi.
...
      now apply rngl_sin_div_2_pow_nat_nonneg.
...
Search (0 ≤ rngl_sin (angle_straight / ₂))%L.
Search (0 ≤ rngl_sin (angle_straight / ₂^_))%L.
Search (0 < rngl_sin (angle_straight / ₂))%L.
Search (0 < rngl_sin (angle_straight / ₂^_))%L.

...
      cbn.
      remember (0 ≤? rngl_sin _)%L as zss eqn:Hzss.
      symmetry in Hzss.
      destruct zss. {
        rewrite (rngl_mul_1_l Hon).
        apply rl_sqrt_nonneg.
...
Search (0 ≤ rngl_cos (_ / ₂))%L.
      apply rngl_cos_div_2_nonneg.
    } {
Search (rngl_cos _ < rngl_cos _)%L.
...
    apply angle_add_le_mono_l_lemma_39; try easy; cycle 1. {
      now apply rngl_sin_div_2_pow_nat_nonneg.
    } {
Search (rngl_sin (angle_straight / ₂^_)).
...
    cbn.
...
rngl_cos_div_pow_2_eq: ∀ (θ : angle T) (n : nat), rngl_cos (θ / ₂^S n) = rngl_cos_div_pow_2 (θ / ₂) n
...
rewrite angle_div_2_add_not_overflow.
f_equal.
Search (- (_ / ₂))%A.
...
rewrite angle_div_2_pow_nat_succ_r_1.
...
rewrite angle_div_2_pow_nat_add'.
remember (angle_add_overflow θ angle_straight) as aov2 eqn:Haov2.
symmetry in Haov2.
destruct aov2. 2: {
  exfalso.
  progress unfold angle_add_overflow in Haov.
  progress unfold angle_add_overflow in Haov2.
  apply angle_ltb_ge in Haov2.
  apply angle_nlt_ge in Haov2.
  apply Haov2; clear Haov2.
  progress unfold angle_ltb.
  rewrite (rngl_sin_add_straight_r Hon Hop).
  rewrite (rngl_cos_add_straight_r Hon Hop).
  progress unfold angle_ltb in Haov.
  cbn in Haov |-*.
  rewrite <- rngl_cos_add in Haov.
  rewrite rngl_add_comm in Haov.
  rewrite <- rngl_sin_add in Haov.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  remember (0 ≤? rngl_cos θ)%L as zc eqn:Hzc.
  symmetry in Hzs, Hzc.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    remember (0 ≤? - rngl_sin θ)%L as zns eqn:Hzns.
    symmetry in Hzns.
    destruct zns. {
      apply rngl_leb_le in Hzns.
      apply rngl_ltb_lt.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzns.
      apply (rngl_le_antisymm Hor) in Hzns; [ | easy ].
      symmetry in Hzns.
      apply eq_rngl_sin_0 in Hzns.
      destruct Hzns; subst θ. {
        rewrite (angle_add_0_l Hon Hos) in Haov.
        cbn in Haov.
        rewrite (rngl_leb_refl Hor) in Haov.
        apply rngl_ltb_lt in Haov.
        now apply (rngl_lt_irrefl Hor) in Haov.
      }
      cbn.
      rewrite (rngl_opp_involutive Hop).
      apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
    }
    exfalso.
    apply (rngl_leb_gt Hor) in Hzns.
    apply (rngl_opp_neg_pos Hop Hor) in Hzns.
    remember (0 ≤? rngl_sin (θ + θ))%L as zsa eqn:Hzsa.
    symmetry in Hzsa.
    destruct zsa; [ | easy ].
    apply rngl_leb_le in Hzsa.
    apply rngl_ltb_lt in Haov.
    apply (rngl_nle_gt Hor) in Haov.
    apply Haov; clear Haov.
    apply angle_add_overflow_le_lemma_111; try easy.
    left.
    intros H; subst θ.
    cbn in Hzns.
    now apply (rngl_lt_irrefl Hor) in Hzns.
  }
  apply (rngl_leb_gt Hor) in Hzs.
  apply (rngl_opp_lt_compat Hop Hor) in Hzs.
  rewrite (rngl_opp_0 Hop) in Hzs.
  apply (rngl_lt_le_incl Hor) in Hzs.
  apply rngl_leb_le in Hzs.
  now rewrite Hzs.
}
rewrite angle_straight_div_2.
destruct i. {
  cbn.
  progress unfold angle_sub.
  f_equal.
  apply eq_angle_eq; cbn; f_equal; symmetry.
  apply (rngl_opp_0 Hop).
}
rewrite angle_add_div_2_pow_diag in IHi.
remember (angle_add_overflow (θ / ₂) (angle_right + angle_straight))
    as aov3 eqn:Haov3. {
symmetry in Haov3.
destruct aov3. 2: {
  exfalso.
  progress unfold angle_add_overflow in Haov.
  progress unfold angle_add_overflow in Haov2.
  progress unfold angle_add_overflow in Haov3.
  apply angle_ltb_ge in Haov3.
  apply angle_nlt_ge in Haov3.
  apply Haov3; clear Haov3.
  rewrite (angle_add_assoc Hop).
  progress unfold angle_ltb.
  rewrite (rngl_sin_add_straight_r Hon Hop).
  rewrite (rngl_cos_add_straight_r Hon Hop).
  rewrite (rngl_sin_add_right_r Hon Hos).
  rewrite (rngl_cos_add_right_r Hon Hop).
  rewrite (rngl_opp_involutive Hop).
  progress unfold angle_ltb in Haov.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  specialize (rngl_sin_div_2_nonneg θ) as H1.
  apply rngl_leb_le in H1.
  rewrite H1.
  apply rngl_leb_le in H1.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    remember (0 ≤? rngl_sin (θ + θ))%L as zstt eqn:Hzstt.
    symmetry in Hzstt.
    destruct zstt; [ | easy ].
    apply rngl_leb_le in Hzstt.
    apply rngl_ltb_lt in Haov.
    remember (θ =? angle_straight)%A as ts eqn:Hts.
    symmetry in Hts.
    destruct ts. {
      apply (angle_eqb_eq Hed) in Hts.
      subst θ.
      cbn.
      rewrite (rngl_leb_refl Hor).
      rewrite (rngl_mul_1_l Hon).
      rewrite (rngl_add_opp_r Hop).
      rewrite (rngl_sub_diag Hos).
      rewrite (rngl_div_0_l Hos Hi1). 2: {
        apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
      }
      rewrite (rl_sqrt_0 Hop Hic Hor Hid).
      rewrite (rngl_opp_0 Hop).
      rewrite (rngl_leb_refl Hor).
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_div_diag Hon Hiq). 2: {
        apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
      }
      rewrite (rl_sqrt_1 Hic Hon Hop Hor Hid).
      apply rngl_ltb_lt.
      apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
    }
    apply (angle_eqb_neq Hed) in Hts.
    exfalso.
    apply angle_leb_gt in Haov2.
    apply Bool.not_true_iff_false in Haov2.
    apply Haov2; clear Haov2.
    progress unfold angle_leb.
    apply rngl_leb_le in Hzs.
    rewrite Hzs.
    apply rngl_leb_le in Hzs.
    rewrite (rngl_sin_add_straight_r Hon Hop).
    remember (0 ≤? - rngl_sin θ)%L as zns eqn:Hzns.
    symmetry in Hzns.
    destruct zns; [ | easy ].
    apply rngl_leb_le in Hzns.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzns.
    apply (rngl_le_antisymm Hor) in Hzns; [ | easy ].
    symmetry in Hzns.
    apply eq_rngl_sin_0 in Hzns.
    destruct Hzns; subst θ; [ | easy ].
    rewrite (rngl_cos_add_straight_r Hon Hop).
    apply rngl_leb_le.
    apply (rngl_opp_1_le_1 Hon Hop Hor Hc1).
  }
  apply (rngl_leb_gt Hor) in Hzs.
  rewrite rngl_leb_opp_r.
  rewrite (rngl_opp_0 Hop).
  remember (rngl_cos (θ / ₂) ≤? 0)%L as c2z eqn:Hc2z.
  symmetry in Hc2z.
  destruct c2z. {
    apply rngl_leb_le in Hc2z.
    apply rngl_ltb_lt.
    cbn.
    apply (rngl_leb_gt Hor) in Hzs.
    rewrite Hzs.
    apply (rngl_leb_gt Hor) in Hzs.
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_le_lt_trans Hor _ 0). {
      apply (rngl_opp_nonpos_nonneg Hop Hor).
      apply rl_sqrt_nonneg.
      apply rngl_1_add_cos_div_2_nonneg.
    }
    apply (rl_sqrt_pos Hos).
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_1_sub_cos_div_2_nonneg | ].
    intros H.
    symmetry in H.
    progress unfold rngl_div in H.
    rewrite Hiv in H.
    apply (rngl_eq_mul_0_l Hos Hii) in H. 2: {
      apply (rngl_inv_neq_0 Hon Hos Hiv).
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    apply -> (rngl_sub_move_0_r Hop) in H.
    symmetry in H.
    apply eq_rngl_cos_1 in H; subst θ.
    now apply (rngl_lt_irrefl Hor) in Hzs.
  }
  exfalso.
  apply (rngl_leb_gt Hor) in Hc2z.
  apply (rngl_nle_gt Hor) in Hzs.
  apply Hzs; clear Hzs.
  rewrite <- (angle_add_div_2_diag θ).
  apply (rngl_lt_le_incl Hor) in Hc2z.
  now apply rngl_sin_add_nonneg.
}
rewrite <- (angle_add_assoc Hop).
rewrite angle_div_2_pow_nat_add'.
rewrite Haov3.
destruct i. {
  cbn.
  progress unfold angle_sub.
  f_equal.
  rewrite angle_straight_div_2.
  apply angle_add_move_0_r.
  rewrite (angle_add_add_swap Hic Hop).
  rewrite (angle_right_add_right Hon Hop).
  apply (angle_straight_add_straight Hon Hop).
}
rewrite <- (angle_add_assoc Hop).
destruct i. {
  cbn.
  cbn in IHi.
  progress unfold angle_sub.
  f_equal.
  rewrite angle_straight_div_2.
  rewrite angle_div_2_add_not_overflow. 2: {
    progress unfold angle_add_overflow.
    apply angle_ltb_ge.
    progress unfold angle_leb.
    rewrite (rngl_sin_add_straight_r Hon Hop).
    rewrite (rngl_cos_add_straight_r Hon Hop).
    cbn.
    specialize (rngl_0_le_1 Hon Hop Hor) as H1.
    apply rngl_leb_le in H1.
    rewrite H1; clear H1.
    rewrite (rngl_opp_0 Hop).
    rewrite (rngl_leb_refl Hor).
    now destruct (0 ≤? - 1)%L.
  }
  rewrite angle_straight_div_2.
  apply angle_add_move_0_r.
  rewrite (angle_add_add_swap Hic Hop).
  rewrite (angle_add_add_swap Hic Hop _ angle_right).
  rewrite angle_add_div_2_diag.
  rewrite (angle_right_add_right Hon Hop).
  apply (angle_straight_add_straight Hon Hop).
}
destruct i. {
  cbn.
cbn in IHi.
...
rewrite <- angle_div_2_pow_nat_add. 2: {
  apply angle_add_overflow_div_2_div_2.
}
destruct i. {
  cbn.
  rewrite angle_div_2_add_overflow; [ | easy ].
...
f_equal.
rewrite angle_div_2_add_overflow; [ | easy ].
rewrite (angle_add_add_swap Hic Hop).
f_equal.
(* eh non *)
...
Search (_ / ₂^S _)%A.
Search (_ / ₂^_ + _ / ₂^_)%A.
rewrite angle_div_2_pow_nat_add'.
rewrite angle_add_div_2_pow_diag.
do 2 rewrite angle_div_2_pow_nat_succ_r_2.
Search (_ / ₂^
...
      rewrite (angle_sub_0_r Hon Hop).
Search ((_ * _) / ₂)%A.
...
rewrite angle_mul_nat_div_2.
Search ((_ + _) / ₂^_)%A.
rewrite angle_div_2_pow_nat_add.
...
rewrite <- (angle_div_2_pow_nat_mul _ _ θ').
3: {
(* ouais, bon, n'importe quoi *)
...
Search (_ * (_ / ₂^_))%A.
rewrite <- (angle_div_2_pow_nat_mul i (2 ^ i / n) θ').
3: {
...
rewrite <- angle_div_2_pow_nat_mul in HN.
...
assert (Hε2 : (0 < ε / 2)%L). {
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  now rewrite (rngl_mul_0_l Hos).
}
specialize (H1 _ Hε2).
destruct H1 as (N, HN).
exists N. (* pour voir *)
intros i Hi.
specialize (HN i Hi).
...
remember (2 ^ i / n * (n * (θ' / ₂^i)))%A as θ.
eapply (rngl_le_lt_trans Hor). {
  apply (angle_eucl_dist_triangular _ θ).
}
specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as Hεε2.
rewrite (rngl_add_diag2 Hon) in Hεε2.
rewrite (rngl_mul_div Hi1) in Hεε2. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite Hεε2; clear Hεε2.
apply (rngl_add_lt_compat Hop Hor); [ | easy ].
subst θ.
rewrite angle_eucl_dist_move_0_r.
(*
destruct i. {
  cbn.
  rewrite angle_sub_diag.
  now rewrite angle_eucl_dist_diag.
}
apply (rngl_le_lt_trans Hor) with
  (b :=
     angle_eucl_dist
       (2 ^ S i / n *
          (angle_straight / ₂^i + n * (angle_straight / ₂^i)))%A 0). {
  apply rngl_cos_le_iff_angle_eucl_le.
  rewrite <- angle_mul_sub_distr_l.
  apply rngl_cos_le_anticompat_when_sin_nonneg; cycle 1. {
...
Search (_ → 0 ≤ rngl_sin _)%L.
Search (rngl_sin (_ * _)).
...
Search (rngl_cos (_ * _) ≤ rngl_cos (_ * _))%L.
...
eapply (rngl_le_lt_trans Hor). {
Check angle_eucl_dist_triangular.
  apply angle_eucl_dist_triangular with
    (θ2 :=
       (2 ^ S i / n *
          (angle_straight / ₂^i + n * (angle_straight / ₂^i)))%A).
}
specialize (rngl_div_add_distr_r Hiv (ε / 2) (ε / 2) 2)%L as Hεε4.
rewrite (rngl_add_diag2 Hon) in Hεε4.
rewrite (rngl_mul_div Hi1) in Hεε4. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite Hεε4; clear Hεε4.
apply (rngl_add_lt_compat Hop Hor). {
...
Therorem glop :
  angle_eucl_dist θ1 θ2 < ε
...
a / ₂^S i ≤ angle_straight / ₂^i
...
  ============================
  (angle_eucl_dist
     (2 ^ i / n * ((n * θ') / ₂^i) - 2 ^ i / n * (n * (θ' / ₂^i))) 0 +
   angle_eucl_dist 0 0 < ε / 2)%L
...
*)
rewrite <- angle_mul_sub_distr_l.
specialize (Hmt n (le_refl _)) as Hnt.
replace n with (m + (n - m)) at 1 by flia Hmn.
rewrite (angle_mul_add_distr_r Hon Hop).
rewrite angle_div_2_pow_nat_add'.
remember (angle_add_overflow (m * θ') ((n - m) * θ')) as aov eqn:Haov.
symmetry in Haov.
destruct aov. 2: {
  destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
    subst m.
    cbn in Hsm.
    rewrite angle_add_0_r in Hsm.
    cbn.
    rewrite Nat.sub_0_r.
    rewrite angle_0_div_2_pow.
    rewrite (angle_add_0_l Hon Hos).
    clear Hm Haov.
Search ((_ * _) / ₂^_)%A.
...
destruct n; [ easy | ].
apply angle_mul_nat_overflow_succ_l in Hnt.
destruct Hnt as [Hnt| Hnt]. {
  destruct n; [ easy | ].
  apply angle_mul_nat_overflow_succ_l in Hnt.
...
  rewrite angle_div_2_pow_nat_mul; cycle 2. {
    apply angle_all_add_not_overflow.
    intros p Hp.
    now apply Hm, Nat.lt_le_incl.
  }
...
(*
replace θ' with (2 ^ i * (θ' / ₂^i))%A at 1. 2: {
  apply angle_mul_2_pow_div_2_pow.
}
rewrite (angle_mul_nat_assoc Hon Hop).
rewrite Nat.mul_comm.
rewrite <- (angle_mul_nat_assoc Hon Hop).
(**)
...
remember (n * (θ' / ₂^(i + j)))%A as θ.
...
  eapply angle_mul_nat_overflow_le_r. 2: {
    apply angle_mul_nat_overflow_pow_div with (θ := (n * θ')%A).
  }
  destruct n; [ easy | ].
  destruct n. {
    rewrite (angle_mul_1_l Hon Hos).
    rewrite (angle_mul_1_l Hon Hos).
    apply angle_le_refl.
  }
  destruct n. {
    cbn.
    do 2 rewrite angle_add_0_r.
    destruct k. {
      cbn in Hnk; flia Hnk.
    }
    rewrite angle_add_div_2_pow_diag.
    rewrite angle_div_2_pow_nat_succ_r_2.
    rewrite (angle_add_diag Hon Hos).
    rewrite angle_mul_2_div_2.
...
Search ((_ + _) / ₂)%A.
Search ((_ + _) / ₂^_)%A.
rewrite <- angle_div_2_pow_nat_add.
...
}
(*
...
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
  rewrite <- Hθ''.
  rewrite <- angle_div_2_pow_nat_mul; [ | easy | easy ].
...
  rewrite Hθ''.
  rewrite angle_div_2_pow_nat_mul; [ | easy | ]. 2: {
    now rewrite <- Hθ''.
  }
  rewrite <- angle_div_pow_2_add_distr.
Search (angle_mul_nat_overflow (2 ^ _)).
...
(*
Search (_ * (_ / ₂^_))%A.
*)
  rewrite <- angle_div_2_pow_nat_mul; [ | easy | ]. 2: {
... ...
}
*)
rewrite angle_mul_2_pow_div_2_pow.
rewrite angle_sub_diag.
rewrite (angle_mul_0_r Hon Hos).
now rewrite angle_eucl_dist_diag.
...
remember (n * (θ' / ₂^i))%A as θ.
Search ((_ * _) / ₂^_)%A.
Check angle_mul_2_pow_div_2_pow.
rewrite angle_mul_2_pow_div_2_pow.
rewrite (angle_mul_2_pow_div_2_pow i (n * (θ' / ₂^i))).
...
*)
remember (2 ^ i / n * _)%A as θ eqn:Hθ in |-*.
progress unfold angle_eucl_dist.
cbn.
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_squ_opp Hop).
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
subst θ.
...
eapply (rngl_le_lt_trans Hor).
Theorem angle_eucl_list_mul_le_mono_l :
  ∀ n θ1 θ2,
  (angle_eucl_dist (n * θ1) (n * θ2) ≤
     rngl_of_nat n * angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
revert θ1 θ2.
induction n; intros. {
  cbn.
  rewrite angle_eucl_dist_diag.
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_refl Hor).
}
rewrite rngl_of_nat_succ; cbn.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_1_l Hon).
destruct n. {
  cbn.
  rewrite (rngl_mul_0_l Hos).
  do 2 rewrite angle_add_0_r.
  rewrite rngl_add_0_r.
  apply (rngl_le_refl Hor).
}
destruct n. {
  cbn.
  do 2 rewrite angle_add_0_r.
  rewrite rngl_add_0_r.
  rewrite (rngl_mul_1_l Hon).
... ...
rewrite angle_eucl_list_mul_mono_l.
...
eapply (angle_lim_eq_compat 0 j). {
  intros i; rewrite Nat.add_0_r; symmetry.
  easy.
}
...
(*
eapply (angle_lim_eq_compat j 0). {
  intros i; rewrite Nat.add_0_r.
  symmetry.
  replace i with ((i + j) - j) at 1 2 by flia.
  remember (i + j) as k.
  rename i into l.
  rename k into i.
  easy.
}
...
eapply (angle_lim_eq_compat 0 j). {
  intros i; rewrite Nat.add_0_r; symmetry.
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
  rewrite <- angle_div_2_pow_nat_mul; [ | | ].
  rewrite <- angle_div_2_pow_nat_mul; [ | | ].
...
  rewrite <- angle_div_2_pow_nat_mul; [ | easy | now rewrite <- Hθ'' ].
  rewrite Nat.add_comm.
...
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
  rewrite <- angle_div_2_pow_nat_mul; [ | easy | now rewrite <- Hθ'' ].
  rewrite Nat.add_comm.
  easy.
}
...
*)
Theorem glop :
  ∀ n u θ,
  angle_lim (λ i, (n * u i)%A) θ
  → ∃ θ', (n * θ' = θ)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hθ.
revert u θ Hθ.
induction n; intros; cbn. {
  cbn in Hθ.
  apply angle_lim_const in Hθ.
  now exists 0%A.
}
cbn in Hθ.
destruct n. {
  exists θ.
  rewrite angle_mul_0_l.
  apply angle_add_0_r.
}
destruct n. {
  exists (θ / ₂)%A.
  rewrite (angle_mul_1_l Hon Hos).
  apply angle_add_div_2_diag.
}
destruct n. {
...
eapply angle_lim_add_add_if with (v := λ i, (- u i)%A) in Hθ. 2: {
  eapply (angle_lim_eq_compat 0 0). {
    intros i; rewrite Nat.add_0_r; symmetry.
    rewrite (angle_add_add_swap Hic Hop).
    rewrite angle_add_opp_r.
    rewrite angle_sub_diag.
    rewrite (angle_add_0_l Hon Hos).
    reflexivity.
  }
...
Search (angle_lim (λ _, (_ + _)))%A.
Search (angle_lim (λ _, (_ * _)))%A.
...
... ...
Check angle_lim_const.
Show.
Search (_ * 2)%L.
...
Search (_ / _ ≤ _)%L.
  ∀ (T : Type) (ro : ring_like_op T),
    ring_like_prop T → rngl_is_ordered T = true → ∀ a b : T, (a ≤ b)%L ↔ (a < b)%L ∨ a = b

destruct (rngl_lt_dec Hor x 0) as [H2| H2]. {
  subst x.
  exfalso.
  apply (rngl_nle_gt Hor) in H2.
  apply H2; clear H2.
Check angle_eucl_dist_nonneg.
...
  progress unfold angle_eucl_dist.
  app
...
clear θ1 θ2 Hx.
...
destruct_ac.
intros * H1.
apply eq_angle_eq.
f_equal. {
  progress unfold angle_lim in H1.
  progress unfold is_limit_when_tending_to_inf in H1.
  destruct (rngl_lt_dec Hor (angle_eucl_dist θ1 θ2) 0) as [H2| H2]. {
Search angle_eucl_dist.
...
  symmetry in Hd.
Search (_ < _)%L.
...
rngl_lt_eq_cases:
  ∀ (T : Type) (ro : ring_like_op T),
    ring_like_prop T → rngl_is_ordered T = true → ∀ a b : T, (a ≤ b)%L ↔ (a < b)%L ∨ a = b
rngl_lt_iff:
  ∀ (T : Type) (ro : ring_like_op T),
    ring_like_prop T → rngl_is_ordered T = true → ∀ a b : T, (a < b)%L ↔ (a ≤ b)%L ∧ a ≠ b
...
  progress unfold angle_eucl_dist in H1.
...
intros * H1.
remember (θ2 <? θ1)%A as tt eqn:Htt.
symmetry in Htt.
destruct tt. {
  apply angle_lt_iff in Htt.
  destruct Htt as (Hte, Htn).
...
remember (θ2 =? θ1)%A as tt eqn:Htt.
symmetry in Htt.
destruct tt. {
...
progress unfold angle_lim in H1.
progress unfold is_limit_when_tending_to_inf in H1.

angle_lt_iff: ∀ θ1 θ2 : angle T, (θ1 < θ2)%A ↔ (θ1 ≤ θ2)%A ∧ θ1 ≠ θ2
...
Theorem glop :
  ∀ n u θ,
  angle_lim (λ i, (n * u i)%A) θ
  → ∃ θ', angle_lim u θ' ∧ (n * θ' = θ)%A.
Proof.
intros * Hθ.
revert u θ Hθ.
induction n; intros; cbn. {
  cbn in Hθ.
... ...
  apply glop in Hθ.
  subst θ.
...
Search (angle_lim (λ _, _)).
progress unfold angle_lim in Hθ.
Search (is_limit_when_tending_to_inf _ (λ _, _)).
...
specialize (glop n (λ i, (2 ^ i / n * (θ' / ₂^i))))%A as H2.
cbn in H2.
specialize (H2 θ' H1).
destruct H2 as (θ & Hθ & Hθθ).
...
eapply (angle_lim_eq_compat j 0) in H1. 2: {
  intros i; rewrite Nat.add_0_r.
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
  rewrite <- angle_div_2_pow_nat_mul; [ | easy | ]. 2: {
    now rewrite <- Hθ''.
  }
  rewrite Nat.add_comm.
  rewrite <- angle_div_2_pow_nat_mul; cycle 1. {
    intros H.
    apply Nat.div_small_iff in H; [ | easy ].
    apply Nat.nle_gt in H.
    apply H; clear H.
    eapply le_trans; [ apply Nat.lt_le_incl, Hjn | ].
    rewrite Nat.pow_add_r.
    rewrite Nat.mul_comm.
    apply Nat_mul_le_pos_r.
    apply Nat.le_succ_l.
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  } {
    rewrite <- Hθ''.
...
  }
Search (_ * (_ / ₂^_))%A.
(* contre-exemple : m=2 n=2 θ=π *)
Theorem angle_div_2_pow_nat_mul' :
  ∀ n m θ,
  m < 2 ^ n
  → ((m * θ) / ₂^n = m * (θ / ₂^n))%A.
Proof.
intros * Hmn.
revert n Hmn.
induction m; intros. {
  cbn.
  apply angle_0_div_2_pow.
}
cbn.
rewrite <- IHm; [ | flia Hmn ].
...
Search ((_ + _) / ₂^_)%A.
apply angle_div_2_pow_nat_add.
Check angle_div_2_pow_nat_mul.
...
cbn in Haov.
destruct m. {
  cbn.
  rewrite angle_add_0_r.
  symmetry; apply angle_add_0_r.
}
specialize (IHm (Nat.neq_succ_0 _)).
apply Bool.orb_false_iff in Haov.
rewrite angle_div_2_pow_nat_add; [ | easy ].
f_equal.
now apply IHm.
Qed.
...
rewrite <- angle_div_2_pow_nat_mul'; [ | easy ].
...
  rewrite <- angle_div_2_pow_nat_mul; [ | easy | ].
}
...
  rewrite (angle_mul_nat_assoc Hon Hop).
  easy.
}
...
apply (angle_lim_eq_compat 0 j (λ i, 2 ^ (i + j) / n * n * (θ' / ₂^j) / ₂^i)%A). {
  intros i; rewrite Nat.add_0_r.
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
(*
  rewrite angle_div_2_pow_nat_mul; [ | admit | ]. 2: {
Search (angle_mul_nat_overflow _ (_ / ₂^_)).
...
*)
...
  rewrite angle_div_2_pow_nat_mul; [ | admit | admit ].
  easy.
}
...
eapply (angle_lim_eq_compat 0 j). {
  intros i; rewrite Nat.add_0_r.
  symmetry.
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
remember ((n * θ') / ₂^j)%A as θ.
Search (_ * (_ / ₂^_))%A.
  rewrite <- angle_div_2_pow_nat_mul; [ | admit | admit ].
  rewrite Nat.add_comm.

  rewrite angle_div_2_pow_nat_mul; [ | admit | admit ].
}
...
(**)
assert (angle_mul_nat_overflow n θ = false). {
  rewrite Hθ'' in H1 at 1.
  apply (angle_lim_mul (2 ^ j)) in H1.
  rewrite angle_mul_2_pow_div_2_pow in H1.
  rewrite Hθ'' in H1.
  eapply (angle_lim_eq_compat 0 0) in H1. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite (angle_mul_nat_assoc Hon Hop).
    rewrite Nat.mul_comm.
    rewrite <- (angle_mul_nat_assoc Hon Hop).
    rewrite angle_div_2_pow_nat_mul; [ | easy | now rewrite <- Hθ'' ].
    do 2 rewrite (angle_mul_nat_assoc Hon Hop).
    rewrite Nat.mul_shuffle0.
    rewrite <- (angle_mul_nat_assoc Hon Hop).
    rewrite <- angle_div_pow_2_add_distr.
    rewrite Nat.add_comm.
    rewrite angle_div_pow_2_add_distr.
    rewrite angle_mul_2_pow_div_2_pow.
    rewrite Nat.mul_comm.
    rewrite <- (angle_mul_nat_assoc Hon Hop).
    reflexivity.
  }
...
(* suspect *)
Theorem glop :
  ∀ n u θ,
  angle_lim (λ i, (n * u i))%A θ
  → angle_mul_nat_overflow n θ = false.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hu.
revert u θ Hu.
induction n; intros; [ easy | ].
apply (angle_mul_nat_not_overflow_succ_l Hon Hos).
Search (angle_lim (λ _, (_ * _))%A).
Search (angle_lim (λ _, (_ + _))%A).
... ...
apply glop in H1.
...
apply (angle_lim_eq_compat j 0) with
    (g := λ i, (n * (2 ^ (i + j) / n * (θ'' / ₂^(i + j))))%A) in H1. 2: {
  intros i.
  rewrite Nat.add_0_r.
  rewrite (angle_div_2_pow_nat_mul _ _ _ Hnz Htj).
  rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite Nat.mul_comm.
  now rewrite <- (angle_mul_nat_assoc Hon Hop).
}
rewrite Hθ'' in H1 at 1.
(*
destruct (Nat.eq_dec j 0) as [Hjz| Hjz]. {
  rewrite Hjz in Hjn.
  now apply Nat.lt_1_r in Hjn.
}
destruct (Nat.eq_dec j 1) as [Hj1| Hj1]. {
  rewrite Hj1 in Hjn.
  cbn in Hjn.
  destruct n; [ easy | ].
  destruct n; [ | flia Hjn ].
  cbn.
  rewrite angle_add_0_r.
  progress unfold seq_angle_converging_to_angle_div_nat.
  eapply (angle_lim_eq_compat 0 0). {
    intros i.
    rewrite Nat.div_1_r.
    rewrite Nat.add_0_r.
    rewrite (angle_mul_2_pow_div_2_pow i θ).
    reflexivity.
  }
  intros ε Hε.
  exists 0.
  intros n Hn.
  now rewrite (proj2 (angle_eucl_dist_separation θ θ) eq_refl).
}
*)
apply (angle_lim_mul (2 ^ j)) in H1.
rewrite angle_mul_2_pow_div_2_pow in H1.
...
(**)
intros ε Hε.
specialize (H1 ε Hε).
destruct H1 as (N, HN).
exists N.
intros i Hi.
specialize (HN i Hi).
...
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hu.
intros ε Hε.
specialize (Hu ε Hε).
destruct Hu as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
replace (u n) with (θ - (θ - u n))%A in HN |-*. 2: {
  rewrite (angle_sub_sub_distr Hic Hop).
  rewrite angle_sub_diag.
  apply (angle_add_0_l Hon Hos).
}
rewrite angle_eucl_dist_sub_l_diag in HN.
rewrite angle_mul_sub_distr_l.
rewrite angle_eucl_dist_sub_l_diag.
specialize angle_eucl_dist_triangular as H1.
specialize (H1 (k * (θ - u n)))%A.
specialize (H1 (θ - u n))%A.
specialize (H1 0)%A.
eapply (rngl_le_lt_trans Hor); [ apply H1 | ].
...
(*
progress unfold seq_angle_converging_to_angle_div_nat.
rewrite Hθ'' in H1.
eapply angle_lim_eq_compat in H1. 2: {
  intros i.
(*
  rewrite <- angle_div_pow_2_add_distr.
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
*)
  do 2 rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite Nat.mul_comm.
  rewrite Nat.mul_assoc.
(*
  rewrite (Nat.mul_comm _ n).
  rewrite Nat.mul_assoc.
*)
  rewrite <- (angle_mul_nat_assoc Hon Hop).
  rewrite <- angle_div_2_pow_nat_mul; [ | easy | now rewrite <- Hθ'' ].
(*
Search ((_ * _) / ₂^_)%A.
...
  rewrite angle_mul_2_pow_div_2_pow.
  rewrite (Nat.mul_comm n).
  rewrite <- (angle_mul_nat_assoc Hon Hop).
*)
  reflexivity.
}
...
*)
(**)
...
eapply (angle_lim_eq_compat 0 0) in H1; [ apply H1 | ].
intros i.
rewrite Nat.add_0_r.
do 2 rewrite (angle_mul_nat_assoc Hon Hop).
rewrite Nat.mul_comm.
rewrite Nat.mul_assoc.
rewrite (Nat.mul_comm _ n).
rewrite Nat.mul_assoc.
rewrite <- (angle_mul_nat_assoc Hon Hop).
rewrite (Nat.mul_comm n).
rewrite <- (angle_mul_nat_assoc Hon Hop).
rewrite <- angle_div_2_pow_nat_mul; cycle 1. {
  now apply Nat.pow_nonzero.
} {
  rewrite Hθ''.
  apply angle_mul_nat_overflow_pow_div.
}
Search (_ / ₂^(_ + _))%A.
rewrite Nat.add_comm.
rewrite angle_div_pow_2_add_distr.
Search ((_ * _) / ₂^_)%A.
rewrite angle_div_2_pow_nat_mul.
rewrite angle_mul_2_pow_div_2_pow.
rewrite Nat.add_comm.
...
(* faux : θ1=π/2 θ2=π a=4 *)
Theorem angle_mul_cancel_l :
  ∀ a θ1 θ2, a ≠ 0 → (a * θ1)%A = (a * θ2)%A → θ1 = θ2.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haz H12.
(**)
apply angle_sub_move_0_r in H12.
rewrite <- angle_mul_sub_distr_l in H12.
...
Search (_ * _ = 0)%A.
Search (_ * _ = 0)%L.
Theorem angle_eq_mul_0_r :
  ∀ a θ, (a * θ)%A = 0%A → a ≠ 0 → θ = 0%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hatz Haz.
revert θ Hatz.
induction a; intros; [ easy | clear Haz ].
destruct a. {
  now rewrite (angle_mul_1_l Hon Hos) in Hatz.
}
specialize (IHa (Nat.neq_succ_0 _)).
remember (S a) as sa; cbn in Hatz; subst sa.
(* non, c'est faux *)
...
apply eq_angle_eq in Hatz.
injection Hatz; clear Hatz; intros Hs Hc.
apply eq_rngl_cos_1 in Hc.
...
apply eq_angle_eq in H12.
injection H12; clear H12; intros Hs Hc.
apply eq_angle_eq.
revert θ1 θ2 Hc Hs.
induction a; intros; [ easy | clear Haz ].
destruct a. {
  do 2 rewrite (angle_mul_1_l Hon Hos) in Hc, Hs.
  now rewrite Hc, Hs.
}
specialize (IHa (Nat.neq_succ_0 _)).
remember (S a) as sa; cbn in Hc, Hs; subst sa.
specialize (IHa θ1 θ2).
...
apply (angle_mul_cancel_l (2 ^ i)).
now apply Nat.pow_nonzero.
rewrite (angle_mul_nat_assoc Hon Hop).
rewrite Nat.mul_comm.
rewrite (angle_mul_nat_assoc Hon Hop).
rewrite Nat.mul_shuffle0.
rewrite <- (angle_mul_nat_assoc Hon Hop).
Search ((_ * _) / ₂^_)%A.
rewrite angle_div_2_pow_nat_mul.
rewrite Hθ''.
Search ((_ / ₂^_) / ₂^_)%A.
(*
rewrite <- angle_div_pow_2_add_distr.
*)
(**)
rewrite (angle_mul_nat_assoc Hon Hop (2 ^ i)).
rewrite <- Nat.pow_add_r.
(*
rewrite (Nat.add_comm j).
*)
rewrite (angle_mul_nat_assoc Hon Hop).
rewrite Nat.mul_shuffle0.
rewrite <- (angle_mul_nat_assoc Hon Hop).
Search (_ * (_ / ₂^_))%A.
rewrite <- angle_div_2_pow_nat_mul.
Search (_ * (_ / ₂^_))%A.
Search (_ / ₂^_)%A.
...
rewrite <- (angle_mul_nat_assoc Hon Hop).
...
rewrite (Nat.add_comm j).
rewrite angle_div_pow_2_add_distr.
...
Search (_ * (_ * _))%A.
rewrite (angle_mul_nat_assoc Hon Hop (2 ^ i)).
Search (_ ^ (_ + _)).
...
rewrite <- Nat.pow_add_r.
rewrite (Nat.add_comm j).
Search (2 ^ _ * _)%A.
rewrite angle_mul_2_pow_div_2_pow.
...
rewrite <- angle_div_2_pow_nat_mul.
...
rewrite angle_mul_2_pow_div_2_pow.
rewrite <- (angle_mul_nat_assoc Hon Hop).
Search (_ * (_ * _))%A.
rewrite (angle_mul_nat_assoc Hon Hop).
rewrite (angle_mul_nat_assoc Hon Hop).
rewrite Nat.mul_shuffle0.
rewrite <- (angle_mul_nat_assoc Hon Hop).
rewrite Hθ''.
...
rewrite <- angle_div_2_pow_nat_mul; [ | | ]. 2: {
...
Search (_ * (_ / ₂^_))%A.
rewrite <- angle_div_2_pow_nat_mul; [ | easy | ]. 2: {
....

rewrite Hθ''.
rewrite <- angle_div_pow_2_add_distr.
rewrite Nat.add_comm.
rewrite angle_div_pow_2_add_distr.
...
rewrite angle_mul_2_pow_div_2_pow.
...
replace j with (S (S (j - 2))) in H1 by flia Hjz Hj1.
do 2 rewrite angle_div_2_pow_nat_succ_r_2 in H1.
apply (angle_lim_mul (2 ^ j)) in H1.
...
rewrite Hθ'' in H1.
destruct j; [ easy | clear Hjz ].
destruct j; [ easy | clear Hj1 ].
do 2 rewrite Nat.sub_succ in H1.
rewrite Nat.sub_0_r in H1.
Inspect 2.
...
apply angle_lim_div_pow_2 in H1.
(*
eapply angle_lim_eq_compat in H1. 2: {
  intros i.
  rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite Nat.mul_comm.
  rewrite <- (angle_mul_nat_assoc Hon Hop).
  rewrite (angle_mul_nat_assoc Hon Hop (2 ^ j)).
  rewrite Nat.mul_comm.
  rewrite <- angle_div_pow_2_add_distr.
  do 2 rewrite Nat.add_succ_comm.
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
  rewrite <- (angle_mul_nat_assoc Hon Hop).
  rewrite angle_mul_2_pow_div_2_pow.
  rewrite angle_div_2_pow_nat_succ_r_1.
  rewrite angle_div_2_pow_nat_succ_r_1.
  reflexivity.
}
*)
apply angle_lim_div_2 in H1.
apply angle_lim_div_2 in H1.
eapply angle_lim_eq_compat in H1. 2: {
  intros i.
  do 3 rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite <- (Nat.mul_assoc 2).
  do 2 rewrite <- Nat.pow_succ_r'.
  rewrite Nat.mul_comm.
(*
  rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite Nat.mul_shuffle0.
  rewrite <- (angle_mul_nat_assoc Hon Hop).
*)
  rewrite <- angle_div_pow_2_add_distr.
  rewrite Nat.add_comm.
  rewrite angle_div_pow_2_add_distr.
(*
  rewrite angle_mul_2_pow_div_2_pow.
*)
  reflexivity.
}
Inspect 2.
...
  rewrite <- Nat.pow_succ_r'.
  rewrite (Nat.mul_shuffle0 2).
  rewrite (Nat.mul_shuffle0 (2 * 2 ^ j)).
  do 3 rewrite <- (angle_mul_nat_assoc Hon Hop).
  rewrite angle_div_2_mul_2.
  do 2 rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite Nat.mul_comm, Nat.mul_assoc.
  rewrite (Nat.mul_shuffle0 _ 2).
  do 2 rewrite <- (angle_mul_nat_assoc Hon Hop).
  rewrite angle_div_2_mul_2.
(*
  rewrite (angle_mul_nat_assoc Hon Hop).
  rewrite Nat.mul_comm.
  rewrite <- (angle_mul_nat_assoc Hon Hop).
*)
  reflexivity.
}
...
  H1 : angle_lim (λ i : nat, (2 ^ i / n * (n * (θ / ₂^i)))%A) θ
  ============================
  angle_lim (λ i : nat, (2 ^ i / n * ((n * θ) / ₂^i))%A) θ
...
Search (angle_lim _ (_ / ₂)).
Search (_ / ₂^(_ + _))%A.
Search (_ / ₂^_ / ₂^_)%A.
Check angle_div_pow_2_add_distr.
...
rewrite Hθ'' in H1.
apply angle_lim_glop in H1.
rewrite <- Hθ'' in H1.
...
specialize (H1 (ε / 2 ^ j))%L.
assert (Hz2j : (0 < 2 ^ j)%L). {
  apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
assert (H : (0 < ε / 2 ^ j)%L). {
  now apply (rngl_div_lt_pos Hon Hop Hiv Hor).
}
specialize (H1 H); clear H.
destruct H1 as (N, HN).
exists N.
intros i Hi.
...
specialize (HN i Hi).
apply (rngl_lt_div_r Hon Hop Hiv Hor) in HN; [ | easy ].
rewrite (rngl_mul_comm Hic) in HN.
rename θ into θ'.
progress unfold seq_angle_converging_to_angle_div_nat in HN.
Search (_ * (_ / ₂^_))%A.
rewrite <- angle_div_2_pow_nat_mul in HN; cycle 1. {
  intros H.
  apply Nat.div_small_iff in H.
  apply Nat.nle_gt in H.
  apply H; clear H.
...
eapply (rngl_le_lt_trans Hor); [ | apply HN ].
Theorem angle_eucl_dist_mul_nat_le :
  ∀ (n : nat) (θ1 θ2 : angle T),
  (angle_eucl_dist (2 ^ n * θ1) (2 ^ n * θ2) ≤
   2 ^ n * angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 (angle_eucl_dist _ _)).
  rewrite (H1 (_ * _))%L.
  apply (rngl_le_refl Hor).
}
(**)
intros.
revert θ1 θ2.
induction n; intros. {
  cbn.
  do 2 rewrite angle_add_0_r.
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_le_refl Hor).
}
(**)
rewrite Nat.pow_succ_r'.
rewrite Nat.mul_comm.
do 2 rewrite <- (angle_mul_nat_assoc Hon Hop).
eapply (rngl_le_trans Hor); [ apply IHn | ].
rewrite (rngl_pow_succ_r Hon).
rewrite (rngl_mul_comm Hic 2)%L.
rewrite <- rngl_mul_assoc.
apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
  apply (rngl_lt_le_incl Hor).
  apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
...
Theorem angle_eucl_dist_twice_twice_le :
  ∀ θ1 θ2, (angle_eucl_dist (2 * θ1) (2 * θ2) ≤ 2 * angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
eapply (rngl_le_trans Hor). {
  apply angle_eucl_dist_triangular with (θ2 := θ1).
}
...
progress unfold angle_eucl_dist.
cbn.
do 4 rewrite (rngl_mul_1_r Hon).
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_l.
do 4 rewrite fold_rngl_squ.
... ...
apply angle_eucl_dist_twice_twice_le.
...
rewrite (angle_add_diag Hon Hos).
...
do 2 rewrite (angle_mul_add_distr_r Hon Hop).
do 2 rewrite <- angle_mul_2_pow_add_distr_l.
do 2 rewrite (angle_add_diag Hon Hos).
eapply (rngl_le_trans Hor); [ apply IHn | ].
...
rewrite (rngl_pow_succ_r Hon).
rewrite <- rngl_mul_assoc.
rewrite <- (rngl_add_diag Hon).
eapply (rngl_le_trans Hor). 2: {
  apply (rngl_add_le_compat Hor).
  apply IHn.
  apply IHn.
}
cbn.
rewrite Nat.add_0_r.
do 2 rewrite (angle_mul_add_distr_r Hon Hop).
do 2 rewrite <- angle_mul_2_pow_add_distr_l.
do 2 rewrite (angle_add_diag Hon Hos).
eapply (rngl_le_trans Hor); [ apply IHn | ].
...
do 2 rewrite <- (angle_add_diag Hon Hos).
...
  rewrite Nat.add_0_r.
... ...
rewrite <- angle_mul_add_distr_l.
...
Check angle_eucl_dist_triangular.
...
Search (angle_eucl_dist (_ + _)).
Search (angle_eucl_dist _ (_ + _)).
...
rewrite rngl_squ_pow_2.
rewrite Nat.pow_succ_r'.
...
intros.
progress unfold angle_eucl_dist.
rewrite <- (rngl_abs_nonneg_eq Hop Hor (2 ^ n)%L). 2: {
  apply (rngl_lt_le_incl Hor).
  apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite <- (rl_sqrt_squ Hop Hor).
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (rngl_squ_nonneg Hop Hor).
} {
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hop Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
Search (rngl_cos (_ * _)).
... ...
eapply (rngl_le_trans Hor). 2: {
  apply angle_eucl_dist_mul_nat_le.
}
rewrite Hθ'' at 2.
rewrite angle_mul_2_pow_div_2_pow.
...
replace 2%L with (rngl_of_nat 2) in HN. 2: {
  now cbn; rewrite rngl_add_0_r.
}
rewrite <- (rngl_of_nat_pow Hon Hos) in HN.
Theorem angle_eucl_dist_mul_nat_le :
  ∀ (a : nat) (θ1 θ2 : angle T),
  (angle_eucl_dist (a * θ1) (a * θ2) ≤
   rngl_of_nat a * angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
rewrite <- (rngl_abs_nonneg_eq Hop Hor (rngl_of_nat a)). 2: {
  apply (rngl_of_nat_nonneg Hon Hop Hor).
}
rewrite <- (rl_sqrt_squ Hop Hor).
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (rngl_squ_nonneg Hop Hor).
} {
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hop Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
Search (rngl_cos (_ * _)).
... ...
eapply (rngl_le_trans Hor). 2: {
  apply angle_eucl_dist_mul_nat_le.
}
rewrite Hθ'' at 2.
rewrite angle_mul_2_pow_div_2_pow.
...
progress unfold seq_angle_converging_to_angle_div_nat in HN.
...
progress unfold angle_eucl_dist in HN.
progress unfold angle_eucl_dist.
progress unfold seq_angle_converging_to_angle_div_nat.
Search (rngl_cos (_ / ₂^_)).
Search rngl_cos_div_pow_2.
...
specialize (H1 ε Hε).
destruct H1 as (N, HN).
exists (N / 2 ^ j).
intros m Hm.
specialize (HN (m * 2 ^ j)).
...
  revert θ.
  induction n; intros; [ easy | ].
Check angle_mul_nat_overflow_succ_l.
...
  apply (angle_mul_nat_overflow_succ_l Hon Hos).
...
(*
Search (_ / ₂^S n)%A.
Search (angle_add_overflow (_ / ₂)).
Search (_ → angle_add_overflow _ _ = false).
Search (_ / ₂ ≤ _)%A.
Search (_ ≤ angle_straight)%A.
Search (_ < angle_straight)%A.
...
  angle_add_overflow (θ1 / ₂^S n) (θ2 / ₂^S n) = false
*)
...
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat as H1.
specialize (H1 Har Hch n θ Hnz)%A.
remember (angle_mul_nat_overflow n θ) as ont eqn:Hont.
symmetry in Hont.
destruct ont; [ | now apply H1 ].
clear H1.
...
specialize (H1 Har Hch n (θ / ₂^n) Hnz Hov)%A.
specialize (H1 ε Hε).
destruct H1 as (N, HN).
...
exists (2 ^ N).
intros m Hm.
specialize (HN m).
Print seq_angle_converging_to_angle_div_nat.
...
Theorem glop :
  ∀ n i j θ,
  n ≤ 2 ^ i
  → i < j
  → (seq_angle_converging_to_angle_div_nat θ n j <
     seq_angle_converging_to_angle_div_nat θ n i)%A.
Proof.
intros * Hn Hij.
progress unfold seq_angle_converging_to_angle_div_nat.
revert n j θ Hn Hij.
induction i; intros. {
  cbn in Hn.
  destruct j; [ easy | ].
  cbn.
  rewrite Nat.add_0_r.
...
Theorem seq_angle_converging_to_angle_div_nat_succ_r_le :
  ∀ n i θ,
  n ≤ 2 ^ i
  → (seq_angle_converging_to_angle_div_nat θ n i ≤
     seq_angle_converging_to_angle_div_nat θ n (S i))%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros * Hn.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  rewrite (H1 (seq_angle_converging_to_angle_div_nat θ n i)).
  rewrite (H1 (seq_angle_converging_to_angle_div_nat θ n (S i))).
  apply angle_le_refl.
}
intros * Hn.
progress unfold seq_angle_converging_to_angle_div_nat.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  apply angle_le_refl.
}
specialize (Nat.div_mod (2 ^ i) n Hnz) as H1.
remember (2 ^ i / n) as q eqn:Hq.
remember (2 ^ i mod n) as r eqn:Hr.
rewrite Nat.pow_succ_r'.
rewrite H1.
rewrite Nat.mul_add_distr_l.
rewrite Nat.mul_assoc, Nat.mul_shuffle0.
rewrite (Nat.div_add_l _ _ _ Hnz).
rewrite (angle_mul_add_distr_r Hon Hop).
rewrite angle_div_2_pow_nat_succ_r_1 at 1.
rewrite (Nat.mul_comm 2).
rewrite <- (angle_mul_nat_assoc Hon Hop).
rewrite angle_div_2_mul_2.
remember (q * (θ / ₂^i))%A as θ' eqn:Hθ'.
rewrite <- (angle_add_0_r θ') at 1.
apply angle_add_le_mono_l; cycle 2. {
  apply angle_nonneg.
} {
  apply (angle_add_overflow_0_r Hon Hos).
}
subst θ' q r.
rewrite angle_div_2_pow_nat_succ_r_1.
destruct (lt_dec (2 * (2 ^ i mod n)) n) as [H2| H2]. {
  rewrite (Nat.div_small (2 * (2 ^ i mod n))); [ | easy ].
  apply (angle_add_overflow_0_r Hon Hos).
}
apply Nat.nlt_ge in H2.
rewrite (Nat_mod_less_small (2 ^ i / n)). 2: {
  split. {
    rewrite H1 at 2.
    rewrite Nat.mul_comm.
    apply Nat.le_add_r.
  }
  rewrite H1 at 1.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_comm, Nat.mul_1_l.
  apply Nat.add_lt_mono_l.
  apply (Nat.mod_upper_bound _ _ Hnz).
}
rewrite Nat.mul_sub_distr_l.
rewrite Nat.mul_assoc.
rewrite (Nat_div_sub _ _ _ Hnz).
destruct (lt_dec (2 ^ i) (2 * n)) as [Hin| Hin]. {
  rewrite (Nat_div_less_small 1); [ | now rewrite Nat.mul_1_l ].
  rewrite (angle_mul_1_l Hon Hos).
  rewrite Nat.mul_1_r.
  apply angle_add_overflow_lt_straight_le_straight. {
    destruct i. {
      cbn in Hn.
      destruct n; [ easy | ].
      destruct n; [ | flia Hn ].
      cbn in H2.
      easy.
    }
    rewrite angle_div_2_pow_nat_succ_r_1.
    apply (angle_div_2_lt_straight Hc1).
  }
  apply (angle_le_trans _ (2 ^ i * ((θ / ₂^i) / ₂))). 2: {
    rewrite <- angle_div_2_pow_nat_succ_r_1.
    rewrite angle_div_2_pow_nat_succ_r_2.
    rewrite angle_mul_2_pow_div_2_pow.
    apply angle_div_2_le_straight.
  }
  apply angle_mul_nat_le_mono_nonneg_r. 2: {
    cbn.
    rewrite Nat.add_0_r.
    apply Nat.le_sub_le_add_r.
    apply (Nat.div_le_upper_bound _ _ _ Hnz).
    rewrite Nat.mul_add_distr_l.
    rewrite (Nat.mul_comm _ 2).
    apply Nat.add_le_mono; [ | now apply Nat.lt_le_incl ].
    destruct n; [ easy | cbn ].
    apply Nat.le_add_r.
  }
  rewrite <- angle_div_2_pow_nat_succ_r_1.
  rewrite angle_div_2_pow_nat_succ_r_2.
  apply angle_mul_nat_overflow_pow_div.
}
apply Nat.nlt_ge in Hin.
(*
remember (2 ^ i / n) as q eqn:Hq.
remember (2 ^ i mod n) as r eqn:Hr.
move r before q.
*)
clear Hnz H1 H2 Hn.
(*
revert n Hin.
induction i; intros. {
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  cbn in Hin; flia Hin.
}
destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
rewrite Nat.pow_succ_r' in Hin.
apply Nat.mul_le_mono_pos_l in Hin; [ | easy ].
...
*)
(**)
destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
rewrite <- Nat_div_sub; [ | easy ].
rewrite <- Nat.mul_assoc.
rewrite <- Nat.mul_sub_distr_l.
(*
remember (2 ^ i - 2 ^ i / S n * S n) as m eqn:Hm.
Search (_ / _ * _).
*)
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  do 2 rewrite Nat.div_1_r.
  rewrite Nat.mul_1_r.
  rewrite Nat.sub_diag.
  rewrite Nat.mul_0_r.
  rewrite angle_mul_0_l.
  apply (angle_add_overflow_0_r Hon Hos).
}
rewrite angle_mul_nat_div_2. {
  destruct i; [ cbn in Hin; flia Hin | ].
  rewrite angle_div_2_pow_nat_succ_r_1.
  rewrite angle_mul_nat_div_2. {
    apply angle_add_overflow_div_2_div_2.
  }
  apply angle_mul_nat_overflow_le_l with (n := 2 * (2 ^ i / n)). {
    apply Nat.div_le_upper_bound; [ easy | ].
    rewrite Nat.mul_comm.
    rewrite Nat.pow_succ_r'.
    rewrite <- Nat.mul_assoc.
    apply Nat.mul_le_mono_l.
    destruct n; [ easy | ].
    destruct i; [ cbn in Hin; flia Hin | ].
    destruct i. {
      cbn in Hin.
      destruct n; [ cbn; flia | flia Hin ].
    }
...
    destruct i; cbn. {
      destruct n; [ easy | cbn ].
      cbn in Hin; flia Hin.
    }
...
    remember (2 ^ i) as a eqn:Ha.
    assert (Haz : a ≠ 0). {
      intros H; subst a.
      now apply Nat.pow_nonzero in H.
    }
    destruct a; [ easy | clear Haz ].
    destruct n; [ easy | clear Hnz ].
    destruct a. {
      cbn.
      destruct n; [ cbn; flia | ].
      cbn.
...
clear Ha.
destruct n; [ easy | ].
destruct a; [ easy | ].
destruct a; cbn. {
  destruct n; [ cbn; flia | ].
  cbn.
...
(*
    clear i Hin Ha.
    specialize (Nat.div_mod a n Hnz) as H1.
    rewrite <- (Nat.add_1_r n).
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_1_r.
*)
    rewrite <- (Nat.add_1_r n).
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_1_r.
    specialize (Nat.div_mod a n Hnz) as H1.
    rewrite Nat.mul_comm in H1.
    rewrite H1 at 1.
    apply Nat.add_le_mono_l.
...
    induction n; [ easy | clear Hnz ].
    destruct n. {
      rewrite Nat.div_1_r, Nat.mul_comm.
      rewrite <- Nat_add_diag.
      apply Nat.le_add_r.
    }
    specialize (IHn (Nat.neq_succ_0 _)).
    remember
    destruct n. {
      rewrite Nat.div_1_r, Nat.mul_comm.
      rewrite <- Nat_add_diag.
      apply Nat.le_add_r.
    }
...
    rewrite <- (Nat.add_1_r n).
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_1_r.
...
replace 2 with (1 + 1) at 4 by easy.
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_1_l.
rewrite Nat.sub_add_distr.
Search ((_ - _) / _).
Search ((_ + _) / _).
...
Search (_ / _ + _ / _)%nat.
Search (_ / _ - _ / _)%nat.
...
destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
destruct i; [ cbn in Hin; flia Hin | ].
(**)
rewrite Nat.pow_succ_r' in Hin.
apply Nat.mul_le_mono_pos_l in Hin; [ | easy ].
cbn - [ "/" ].
do 3 rewrite Nat.add_0_r.
rewrite angle_mul_nat_div_2. {
  rewrite angle_mul_nat_div_2. {
    apply angle_add_overflow_div_2_div_2.
  }
...
Search (_ * (_ / ₂))%A.
...
destruct i. {
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  cbn in Hin; flia Hin.
}
destruct i. {
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  cbn in Hin; flia Hin.
}
destruct i. {
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n. {
    cbn.
    do 2 rewrite angle_add_0_r.
    rewrite angle_add_div_2_diag.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  cbn in Hin; flia Hin.
}
destruct i. {
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n. {
    cbn.
    do 2 rewrite angle_add_0_r.
    rewrite angle_add_div_2_diag.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  destruct n; [ apply (angle_add_overflow_0_r Hon Hos) | ].
  cbn in Hin; flia Hin.
}
...
specialize (Nat.div_mod (2 ^ S i) n Hnz) as H2.
remember (2 ^ S i / n) as q' eqn:Hq'.
remember (2 ^ S i mod n) as r' eqn:Hr'.
rewrite Nat.pow_succ_r' in H2 at 1.
rewrite H1 in H2.
move q' before q; move r before q'; move r' before r.
Search (_ + _ mod _).
...
revert n θ Hn Hnz.
induction i; intros. {
  cbn in Hn |-*.
  destruct n; [ apply angle_le_refl | cbn ].
  destruct n; [ | flia Hn ].
  clear Hn; cbn.
  do 2 rewrite angle_add_0_r.
  progress unfold angle_leb.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    remember (θ =? angle_straight)%A as ts eqn:Hts.
    symmetry in Hts.
    destruct ts. {
      apply (angle_eqb_eq Hed) in Hts.
      subst θ.
      rewrite angle_straight_div_2.
      rewrite (angle_right_add_right Hon Hop).
      cbn.
      rewrite (rngl_leb_refl Hor).
      apply (rngl_leb_refl Hor).
    } {
      apply (angle_eqb_neq Hed) in Hts.
      rewrite <- rngl_sin_angle_div_2_add. 2: {
        now apply angle_add_overflow_diag.
      }
      rewrite <- rngl_cos_angle_div_2_add. 2: {
        now apply angle_add_overflow_diag.
      }
      rewrite (angle_add_diag Hon Hos).
      rewrite angle_mul_2_div_2.
      remember (θ <? angle_straight)%A as tst eqn:Htst.
      symmetry in Htst.
      destruct tst. {
        apply rngl_leb_le in Hzs.
        rewrite Hzs.
        apply (rngl_leb_refl Hor).
      }
      exfalso.
      apply angle_ltb_ge in Htst.
      apply angle_nlt_ge in Htst.
      apply Htst; clear Htst.
      progress unfold angle_ltb.
      apply rngl_leb_le in Hzs.
      rewrite Hzs.
      cbn.
      rewrite (rngl_leb_refl Hor).
      apply rngl_ltb_lt.
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_cos_bound | ].
      intros H; symmetry in H.
      now apply eq_rngl_cos_opp_1 in H.
    }
  }
  apply (rngl_leb_gt Hor) in Hzs.
  rewrite angle_add_div_2_diag.
  generalize Hzs; intros H.
  apply (rngl_leb_gt Hor) in H.
  rewrite H.
  apply rngl_leb_le.
  apply (rngl_le_refl Hor).
}
rewrite (Nat.pow_succ_r' _ (S i)).
...
eapply angle_le_trans. 2: {
  apply (angle_mul_nat_le_mono_nonneg_r (2 * (2 ^ S i / n))). 2: {
    now apply Nat.div_mul_le.
  }
Check (angle_mul_nat_le_mono_nonneg_r).
...
(*
  rewrite <- Nat.pow_succ_r'.
*)
  rewrite angle_div_2_pow_nat_succ_r_1.
Theorem glop :
  ∀ m n θ,
  m ≤ n
  → angle_mul_nat_overflow n θ = false
  → angle_mul_nat_overflow m θ = false.
...
eapply glop with (n := 2 * (2 *
...
apply
Search (_ * _ / _)%nat.
Search angle_mul_nat_overflow.
...
eapply angle_mul_nat_overflow_le_r.
...
Search (angle_mul_nat_overflow _ (_ / ₂)).
Check angle_mul_nat_overflow_angle_div_2_mul_2_div_2.
...
  apply angle_mul_nat_overflow_angle_div_2_mul_2_div_2.
Search (angle_mul_nat_overflow _ (_ / ₂^_)).
Search (_ / _ * (_ / ₂^_))%A.
Search (_ * _ / _).
...
rewrite angle_div_2_pow_nat_succ_r_1.
...
Search (_ / ₂^(S _))%A.
...
intros.
apply eq_angle_eq.
cbn.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  rewrite rngl_mul_1_l
...
Search (_ / ₂ + _ / ₂)%A.
...
  rewrite <- rngl_sin_angle_div_2_add. 2: {
...
    apply angle_add_overflow_diag.
...
...
apply quadrant_1_rngl_cos_add_le_cos_l; try easy.
...
apply angle_add_overflow_le_lemma_111; try easy.
...
symmetry in Hzsd.
...
Search (rngl_cos (_ + _) ≤ rngl_cos _)%L.
(* peut-être qu'il faut affaiblir l'hypothèse angle_add_overflow
   dans rngl_sin_angle_div_2_add, pareil pour cos *)
...
apply angle_add_overflow_le_lemma_111; try easy.
...
Search (rngl_sin (_ / ₂ + _ / ₂)%A).
About rngl_cos_angle_div_2_add.
...
  cbn.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs. {
Search (_ / ₂ + _ / ₂)%A.
  rewrite <- angle_div_2_add_not_overflow.
...
progress unfold seq_angle_converging_to_angle_div_nat in HN.
...
assert (H : angle_mul_nat_overflow n (θ / ₂^j) = false). {
  clear ε Hε H1.
  subst j.
  clear Hnz.
...
  induction n; [ easy | ].
  rewrite (angle_mul_nat_not_overflow_succ_l Hon Hos).
  split. {
    specialize (Nat.log2_succ_or n) as H1.
    destruct H1 as [H1| H1]. {
      rewrite H1.
      rewrite angle_div_2_pow_nat_succ_r_1.
      apply angle_mul_nat_overflow_mul_2_div_2 in IHn.
Check angle_mul_nat_overflow_mul_2_div_2.
...
Search (angle_mul_nat_overflow _ (_ / ₂)).
      apply angle_mul_nat_overflow_mul_2_div_2.
...
... ...
now apply angle_mul_nat_not_overflow_double.
...
Theorem angle_mul_nat_overflow_mul_cancel_l :
  ∀ a b θ,
  a ≠ 0
  → angle_mul_nat_overflow (a * b) θ = false
  → angle_mul_nat_overflow b θ = false.
Proof.
intros * Haz Hab.
destruct a; [ easy | clear Haz ].
cbn in Hab.
Theorem angle_mul_nat_overflow_add_cancel_r :
  ∀ a b θ,
  angle_mul_nat_overflow (a + b) θ = false
  → angle_mul_nat_overflow a θ = false.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hab.
revert b Hab.
induction a; intros; [ easy | ].
rewrite Nat.add_succ_l in Hab.
apply (angle_mul_nat_not_overflow_succ_l Hon Hos) in Hab.
apply (angle_mul_nat_not_overflow_succ_l Hon Hos).
destruct Hab as (Hab, Hab2).
split; [ apply (IHa b), Hab | ].
rewrite (angle_mul_add_distr_r Hon Hop) in Hab2.
... ...
apply (angle_add_not_overflow_add_r_cancel_r θ (a * θ)) in Hab2; [ easy | ].
(* bon, je pense que c'est bon *)
...
apply angle_add_not_overflow_add_r_cancel_r in Hab2.
now apply angle_add_not_overflow_add_r_cancel_r in Hab2.
... ...
now apply angle_mul_nat_overflow_add_cancel_r in Hab.
...
intros * Haz Hab.
revert b Hab.
induction a; intros; [ easy | clear Haz ].
destruct a; [ now rewrite Nat.mul_1_l in Hab | ].
specialize (IHa (Nat.neq_succ_0 _)).
remember (S a) as sa; cbn in Hab; subst sa.
cbn in IHa.
apply IHa.
... ...
now apply angle_mul_nat_overflow_mul_cancel_l in IHn.
...
Search (2 ^ Nat.log2 _).
specialize (Nat.log2_spec_alt n) as H2.
apply angle_mul_nat_overflow_mul_2_div_2.
...
progress unfold angle_lim.
progress unfold is_limit_when_tending_to_inf.
int
progress unfold seq_angle_converging_to_angle_div_nat.
...
*)

Theorem angle_add_diag_not_overflow :
  rngl_characteristic T ≠ 1 →
  ∀ θ,
  (θ < angle_straight)%A
  ↔ angle_add_overflow θ θ = false.
Proof.
intros Hc1.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros.
split; intros Hθ. {
  progress unfold angle_ltb in Hθ.
  progress unfold angle_add_overflow.
  progress unfold angle_ltb.
  cbn in Hθ.
  rewrite (rngl_leb_refl Hor) in Hθ.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs; [ | easy ].
  apply rngl_leb_le in Hzs.
  apply rngl_ltb_lt in Hθ.
  remember (0 ≤? rngl_sin (θ + θ))%L as zst eqn:Hzst.
  symmetry in Hzst.
  destruct zst; [ | easy ].
  apply (rngl_ltb_ge Hor).
  apply rngl_leb_le in Hzst.
  cbn.
  apply (rngl_le_trans Hor _ (rngl_cos θ * rngl_cos θ)). {
    apply (rngl_le_sub_nonneg Hop Hor).
    apply (rngl_mul_diag_nonneg Hop Hor).
  }
  (* TODO: lemma *)
  remember (_ * _)%L as x.
  rewrite <- (rngl_mul_1_r Hon (rngl_cos _)).
  subst x.
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ | apply rngl_cos_bound ].
  cbn in Hzst.
  rewrite (rngl_mul_comm Hic) in Hzst.
  rewrite (rngl_add_diag Hon) in Hzst.
  apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzst.
  destruct Hzst as [(_, Hzst)| (H, _)]. 2: {
    apply (rngl_nlt_ge Hor) in H.
    exfalso; apply H; clear H.
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzst.
  destruct Hzst as [Hzst| (Hs, Hc)]; [ easy | ].
  apply (rngl_le_antisymm Hor) in Hs; [ | easy ].
  symmetry in Hs.
  apply eq_rngl_sin_0 in Hs.
  destruct Hs; subst θ. {
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  now apply (rngl_lt_irrefl Hor) in Hθ.
} {
  progress unfold angle_add_overflow in Hθ.
  progress unfold angle_ltb in Hθ.
  progress unfold angle_ltb.
  cbn.
  rewrite (rngl_leb_refl Hor).
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    apply rngl_ltb_lt.
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_cos_bound | ].
    intros H; symmetry in H.
    apply eq_rngl_cos_opp_1 in H.
    subst θ.
    rewrite (angle_straight_add_straight Hon Hop) in Hθ.
    cbn in Hθ.
    rewrite (rngl_leb_refl Hor) in Hθ.
    apply Bool.not_true_iff_false in Hθ.
    apply Hθ.
    apply rngl_ltb_lt.
    apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
  }
  exfalso.
  apply (rngl_leb_gt Hor) in Hzs.
  remember (0 ≤? rngl_sin (θ + θ))%L as zst eqn:Hzst.
  symmetry in Hzst.
  destruct zst; [ easy | ].
  apply (rngl_ltb_ge Hor) in Hθ.
  apply (rngl_leb_gt Hor) in Hzst.
  rewrite (angle_add_diag Hon Hos) in Hzst.
  rewrite (rngl_sin_mul_2_l Hic Hon Hos) in Hzst.
  rewrite <- rngl_mul_assoc in Hzst.
  apply (rngl_nle_gt Hor) in Hzst.
  apply Hzst; clear Hzst.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_0_le_2 Hon Hop Hor).
  }
  apply (rngl_mul_nonpos_nonpos Hop Hor). {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nlt_ge Hor).
  intros Hzc.
  apply (rngl_nlt_ge Hor) in Hθ.
  apply Hθ; clear Hθ.
  rewrite (angle_add_diag Hon Hos).
  rewrite (rngl_cos_mul_2_l Hon Hos).
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  apply (rngl_le_lt_trans Hor _ (rngl_cos θ)). {
    progress unfold rngl_squ.
    remember (_ * _)%L as x.
    rewrite <- (rngl_mul_1_r Hon (rngl_cos _)).
    subst x.
    apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ | apply rngl_cos_bound ].
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_lt_add_r Hos Hor).
  progress unfold rngl_squ.
  now apply (rngl_mul_neg_neg Hop Hor Hii).
}
Qed.

Theorem angle_mul_succ_l : ∀ n θ, (S n * θ = θ + n * θ)%A.
Proof. easy. Qed.

Theorem rngl_sin_nonneg_angle_le_straight :
  ∀ θ, (0 ≤ rngl_sin θ)%L ↔ (θ ≤ angle_straight)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  apply rngl_leb_le in Hzs.
  split; [ | easy ].
  intros _; cbn.
  apply rngl_leb_le.
  apply rngl_cos_bound.
}
apply (rngl_leb_gt Hor) in Hzs.
now apply (rngl_nle_gt Hor) in Hzs.
Qed.

Theorem rngl_cos_le_cos_div_2 :
  ∀ θ, (0 ≤ rngl_sin θ)%L → (rngl_cos θ ≤ rngl_cos (θ / ₂))%L.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply (angle_eqb_eq Hed) in Htz.
  subst θ.
  rewrite angle_0_div_2.
  apply (rngl_le_refl Hor).
}
apply (angle_eqb_neq Hed) in Htz.
cbn.
apply rngl_leb_le in Hzs.
rewrite Hzs.
apply (rngl_lt_le_incl Hor).
rewrite (rngl_mul_1_l Hon).
now apply (rngl_cos_lt_sqrt_1_add_cos_div_2 Hc1).
Qed.

Theorem angle_right_nonneg : (0 ≤ angle_right)%A.
Proof.
destruct_ac.
intros.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
now destruct (0 ≤? 1)%L.
Qed.

Theorem angle_lt_eq_cases :
  ∀ θ1 θ2, (θ1 ≤ θ2)%A ↔ (θ1 < θ2)%A ∨ θ1 = θ2.
Proof.
destruct_ac.
intros.
split; intros H12. {
  remember (θ1 =? θ2)%A as e12 eqn:He12.
  symmetry in He12.
  destruct e12. {
    apply (angle_eqb_eq Hed) in He12.
    now right.
  }
  left.
  apply (angle_eqb_neq Hed) in He12.
  now apply angle_lt_iff.
}
destruct H12 as [H12| H12]; [ now apply angle_lt_le_incl | ].
subst θ2.
apply angle_le_refl.
Qed.

(* to be completed
Theorem angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat' :
  rngl_is_archimedean T = true →
  rngl_characteristic T = 0 →
  ∀ n θ θ',
  n ≠ 0
  → angle_lim (seq_angle_converging_to_angle_div_nat θ n) θ'
  → θ = (n * θ')%A.
Proof.
destruct_ac.
intros Har Hch.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite Hc1 in Hch.
}
intros * Hiz Hlim.
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat as Hlim'.
(* pourquoi il faut que nθ ne déborde pas ? on est fichus ! *)
Search (_ * (_ / ₂^_))%A.
specialize (Hlim' Har Hch n θ' Hiz).
remember (angle_mul_nat_overflow n θ') as ao eqn:Hao.
symmetry in Hao.
(**)
destruct ao. {
  clear Hlim'.
  apply Bool.not_false_iff_true in Hao.
  exfalso; apply Hao; clear Hao.
Theorem angle_lim_seq_angle_not_mul_overflow :
  ∀ n θ θ',
  angle_lim (seq_angle_converging_to_angle_div_nat θ n) θ'
  → angle_mul_nat_overflow n θ' = false.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 θ').
  apply (angle_mul_nat_overflow_0_r Hon Hos).
}
intros * Hlim.
progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
apply (angle_all_add_not_overflow n θ').
intros m Hm.
(*
progress unfold angle_lim in Hlim.
progress unfold is_limit_when_tending_to_inf in Hlim.
*)
progress unfold angle_add_overflow.
apply angle_ltb_ge.
progress unfold angle_leb.
rewrite <- angle_mul_succ_l.
remember (0 ≤? rngl_sin θ')%L as zs eqn:Hzs.
remember (0 ≤? rngl_sin (S m * θ'))%L as zsm eqn:Hzsm.
symmetry in Hzs, Hzsm.
destruct zsm. {
  apply rngl_leb_le in Hzsm.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    apply rngl_leb_le.
    cbn - [ rngl_cos ].
    destruct (rngl_le_dec Hor 0 (rngl_cos θ')) as [Hzc| Hzc]. {
      destruct (rngl_le_dec Hor 0 (rngl_sin (m * θ'))) as [Hzm| Hzm]. {
        apply angle_add_overflow_le_lemma_111; try easy.
        now right; right; left.
      }
      apply (rngl_nle_gt Hor) in Hzm.
      cbn - [ rngl_sin ] in Hzsm.
(* c'est faux : m*θ'=-ε ; il faut donc essayer d'utiliser l'hypothèse Hlim,
   mais comment ? *)
Theorem angles_lim_le :
  ∀ u v θ θ',
  (∀ i, (u i ≤ v i)%A)
  → (θ ≤ angle_straight)%A
  → angle_lim u θ
  → angle_lim v θ'
  → (θ ≤ θ')%A.
Proof.
destruct_ac.
intros * Huv Hts Hu Hv.
progress unfold angle_lim in Hu.
progress unfold angle_lim in Hv.
progress unfold is_limit_when_tending_to_inf in Hu.
progress unfold is_limit_when_tending_to_inf in Hv.
apply angle_nlt_ge.
intros Htt.
assert (Hd : (0 < angle_eucl_dist θ θ')%L). {
  apply (rngl_lt_iff Hor).
  split; [ apply angle_eucl_dist_nonneg | ].
  intros H; symmetry in H.
  apply angle_eucl_dist_separation in H.
  subst θ'.
  now apply angle_lt_irrefl in Htt.
}
apply angle_nle_gt in Htt.
apply Htt; clear Htt.
set (ε := angle_eucl_dist θ θ') in Hd.
specialize (Hu _ Hd).
specialize (Hv _ Hd).
destruct Hu as (N1, Hu).
destruct Hv as (N2, Hv).
set (N := max N1 N2) in Hu, Hv.
specialize (Hu N (Nat.le_max_l _ _)).
specialize (Hv N (Nat.le_max_r _ _)).
Theorem angle_lim_le :
  ∀ u θ θ',
  (θ ≤ angle_straight)%A
  → (∀ i, (u i ≤ θ')%A)
  → angle_lim u θ
  → (θ ≤ θ')%A.
Proof.
destruct_ac.
intros * Hts Hut Hu.
progress unfold angle_lim in Hu.
progress unfold is_limit_when_tending_to_inf in Hu.
apply angle_nlt_ge.
intros Htt.
assert (Hd : (0 < angle_eucl_dist θ θ')%L). {
  apply (rngl_lt_iff Hor).
  split; [ apply angle_eucl_dist_nonneg | ].
  intros H; symmetry in H.
  apply angle_eucl_dist_separation in H.
  subst θ'.
  now apply angle_lt_irrefl in Htt.
}
(*
apply angle_nle_gt in Htt.
apply Htt; clear Htt.
*)
set (ε := angle_eucl_dist θ θ') in Hd.
specialize (Hu _ Hd) as H1.
destruct H1 as (N, H1).
specialize (H1 N (Nat.le_refl _)).
progress unfold ε in H1.
specialize (Hut N) as H2.
apply angle_nlt_ge in H2.
apply H2; clear H2.
move Htt before H1.
Theorem angle_dist_le :
  ∀ θ1 θ2 θ3,
  (θ3 ≤ angle_straight)%A
  → (θ1 ≤ θ2 ≤ θ3)%A
  → (angle_eucl_dist θ2 θ3 ≤ angle_eucl_dist θ1 θ3)%L.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hts (H12, H23).
do 2 rewrite (angle_eucl_dist_move_0_l _ θ3).
apply rngl_cos_le_iff_angle_eucl_le.
assert (Hzs1 : (0 ≤ rngl_sin θ1)%L). {
  apply rngl_sin_nonneg_angle_le_straight.
  apply (angle_le_trans _ θ2); [ easy | ].
  now apply (angle_le_trans _ θ3).
}
assert (Hzs2 : (0 ≤ rngl_sin θ2)%L). {
  apply rngl_sin_nonneg_angle_le_straight.
  now apply (angle_le_trans _ θ3).
}
assert (Hzs3 : (0 ≤ rngl_sin θ3)%L). {
  now apply rngl_sin_nonneg_angle_le_straight.
}
assert (Hzc32 : (rngl_cos θ3 ≤ rngl_cos θ2)%L) by now apply rngl_cos_decr.
assert (Hzc21 : (rngl_cos θ2 ≤ rngl_cos θ1)%L). {
  apply rngl_cos_decr.
  split; [ easy | ].
  now apply (angle_le_trans _ θ3).
}
(*
...
apply rngl_cos_decr.
split. {
Search (_ ≤ _ + _ ↔ _ - _ ≤ _)%L.
Search (_ - _ ≤ _ ↔ _)%L.
Theorem angle_le_add_r_le_sub_l :
  ∀ θ1 θ2 θ3, (θ1 ≤ θ2 + θ3 → θ1 - θ2 ≤ θ3)%A.
Proof.
intros * H123.
... ...
Theorem angle_le_add_l_le_sub_r :
  ∀ θ1 θ2 θ3, (θ1 + θ2 ≤ θ3 → θ1 ≤ θ3 - θ2)%A.
... ...
apply angle_le_add_r_le_sub_l.
rewrite (angle_add_sub_assoc Hop).
apply angle_le_add_l_le_sub_r.
rewrite (angle_add_comm Hic θ2).
apply angle_add_le_mono_l.
...
Search (_ - _ ≤ _ - _)%A.
...
*)
destruct (rngl_le_dec Hor 0 (rngl_cos (θ3 - θ1))) as [Hzc31| Hc31z]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos (θ3 - θ2))) as [Hz32| H32z]. {
    apply rngl_sin_cos_nonneg_sin_sub_nonneg_cos_le; try easy. {
      apply rngl_sin_sub_nonneg; [ easy | easy | ].
      apply rngl_cos_decr.
      split; [ | easy ].
      now apply (angle_le_trans _ θ2).
    } {
      now apply rngl_sin_sub_nonneg.
    }
    rewrite (angle_sub_sub_distr Hic Hop).
    rewrite (angle_sub_sub_swap Hic Hop).
    rewrite angle_sub_diag.
    rewrite (angle_sub_0_l Hon Hos).
    rewrite (angle_add_opp_l Hic).
    now apply rngl_sin_sub_nonneg.
  }
  apply (rngl_nle_gt Hor) in H32z.
  exfalso.
  apply (rngl_nle_gt Hor) in H32z.
  apply H32z; clear H32z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
     destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
       cbn.
       rewrite (rngl_mul_opp_r Hop).
       rewrite (rngl_sub_opp_r Hop).
       apply (rngl_add_nonneg_nonneg Hor).
       now apply (rngl_mul_nonneg_nonneg Hop Hor).
       now apply (rngl_mul_nonneg_nonneg Hop Hor).
     }
     apply (rngl_nle_gt Hor) in Hc3z.
     change_angle_sub_r θ3 angle_right.
     progress sin_cos_add_sub_right_hyp T Hzc32.
     progress sin_cos_add_sub_right_hyp T Hzs3.
     progress sin_cos_add_sub_right_hyp T Hzc31.
     progress sin_cos_add_sub_right_hyp T Hc3z.
     progress sin_cos_add_sub_right_goal T.
     rewrite (rngl_sin_sub_anticomm Hic Hop) in Hzc31 |-*.
     apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzc31.
     apply (rngl_opp_nonpos_nonneg Hop Hor).
     clear Hzc32.
     cbn.
     cbn in Hzc31.
     rewrite (rngl_mul_opp_r Hop) in Hzc31 |-*.
     rewrite (rngl_add_opp_l Hop) in Hzc31 |-*.
     apply -> (rngl_le_0_sub Hop Hor) in Hzc31.
     apply (rngl_le_0_sub Hop Hor).
     apply (rngl_le_trans Hor) with (b := (rngl_cos θ1 * rngl_sin θ3)%L). {
       apply (rngl_lt_le_incl Hor) in Hc3z.
       now apply (rngl_mul_le_mono_nonneg_r Hop Hor).
     }
     apply (rngl_le_trans Hor) with (b := (rngl_sin θ1 * rngl_cos θ3)%L). {
       apply Hzc31.
     }
     apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
     apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
     now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
  }
...
     rewrite <- (rngl_cos_sub Hop).
(*
...
     remember (θ3 - θ2)%A as θ eqn:Hθ.
     apply angle_sub_move_r in Hθ.
     rewrite (angle_sub_opp_r Hop) in Hθ.
     subst θ3.
     rename θ into θ3.
     rewrite <- (angle_add_sub_assoc Hop) in Hzc31.
     remember (θ2 - θ1)%A as θ eqn:Hθ.
     apply angle_sub_move_r in Hθ.
     rewrite (angle_sub_opp_r Hop) in Hθ.
     subst θ2.
     rename θ into θ2.
...
*)
Search (_ → 0 ≤ rngl_cos _)%L.
apply rngl_cos_add_nonneg_cos_add_nonneg with (θ3 := θ1); try easy. (* non *)
apply angle_add_le_mono_l_lemma_34 with (θ3 := (- θ3)%A); try easy. (* non *)
apply angle_add_le_mono_l_lemma_38 with (θ3 := (- θ3)%A); try easy. (* non *)
apply rngl_cos_add_nonneg; try easy. (* non *)
apply rngl_cos_sub_nonneg; try easy. (* non *)
...
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
cbn in Hzc31.
rewrite (rngl_mul_opp_r Hop) in Hzc31.
rewrite (rngl_sub_opp_r Hop) in Hzc31.
...
apply (rngl_add_nonneg_nonneg Hor). {
  apply (rngl_le_trans Hor) with (b := (rngl_cos θ2 * rngl_cos θ2)%L). {
    rewrite fold_rngl_squ.
    apply (rngl_squ_nonneg Hop Hor).
  }
Search
...
     change_angle_sub_l θ3 angle_straight.
     progress sin_cos_add_sub_straight_hyp T Hzc32.
     progress sin_cos_add_sub_straight_hyp T Hzs3.
     rewrite <- (angle_sub_add_distr Hic Hop) in Hzc31 |-*.
     progress sin_cos_add_sub_straight_hyp T Hzc31.
     progress sin_cos_add_sub_straight_hyp T Hc3z.
     progress sin_cos_add_sub_straight_goal T.
cbn.
...
     change_angle_sub_r θ3 angle_right.
     progress sin_cos_add_sub_right_hyp T Hzc32.
     progress sin_cos_add_sub_right_hyp T Hzs3.
     progress sin_cos_add_sub_right_hyp T Hzc31.
     progress sin_cos_add_sub_right_hyp T Hc3z.
     progress sin_cos_add_sub_right_goal T.
(* ouais bin chais pas *)
...
Search (0 ≤ rngl_cos (_ + _))%L.
apply rngl_cos_add_nonneg_cos_add_nonneg with (θ3 := (- θ1)%A); cbn; try easy.
...
rewrite (rngl_cos_sub_comm Hic Hop).
apply rngl_cos_add_nonneg; [ | | | ].
2: cbn.
...
...
apply rngl_cos_add_nonneg; [ | | | ].
Search (0 ≤ rngl_cos (_ - _))%L.
...
     apply (rngl_add_nonneg_nonneg Hor).
       now apply (rngl_mul_nonneg_nonneg Hop Hor).
       now apply (rngl_mul_nonneg_nonneg Hop Hor).

Search (0 ≤ rngl_cos (_ - _))%L.
About rngl_cos_sub_nonneg.
...
Search (rngl_cos _ ≤ rngl_cos _)%L.
apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
...
apply rngl_cos_le_anticompat_when_sin_nonneg. {
  apply rngl_sin_sub_nonneg; [ | easy | ].
  now apply rngl_sin_nonneg_angle_le_straight.
  apply rngl_cos_decr.
  split; [ | easy ].
  now apply (angle_le_trans _ θ2).
} {
  apply rngl_sin_sub_nonneg; [ | easy | ].
  now apply rngl_sin_nonneg_angle_le_straight.
  now apply rngl_cos_decr.
}
apply angle_add_le_mono_l. {
...
  apply angle_add_overflow_le with (θ2 := θ2). {
    progress unfold angle_leb.
    cbn.
    rewrite rngl_leb_opp_r.
    rewrite (rngl_opp_0 Hop).
    apply rngl_leb_le in Hzs2.
    rewrite Hzs2.
...
Search (_ - _ ≤ _)%A.
Search (_ → angle_add_overflow _ _ = false).
...
  apply angle_add_overflow_le_straight_lt_straight.
...
...
Search (0 ≤ rngl_sin (_ - _))%L.
...
progress unfold angle_leb in H12.
progress unfold angle_leb in H23.
(*
do 2 rewrite (rngl_cos_sub Hop).
*)
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs3. {
    apply rngl_leb_le in Hzs3.
    destruct zs2; [ | easy ].
    apply rngl_leb_le in Hzs2.
    apply rngl_leb_le in H12.
    apply rngl_leb_le in H23.
... ...
apply angle_nle_gt.
intros Hnt.
apply (rngl_nle_gt Hor) in H1.
apply H1; clear H1.
rewrite (angle_eucl_dist_symmetry Hic Hop θ).
apply angle_dist_le; [ easy | ].
split; [ easy | ].
now apply angle_lt_le_incl.
...
(* poub *)
specialize (angle_eucl_dist_triangular θ θ' (u N)) as H2.
rewrite (angle_eucl_dist_symmetry Hic Hop) in H1.
specialize (Hut N) as H3.
progress unfold ε in H1.
...
apply angle_nlt_ge in H3.
apply H3; clear H3.
eapply angle_lt_le_trans; [ apply Htt | ].
...
progress unfold ε in H1.
(*
specialize (angle_eucl_dist_triangular θ' (u N) θ) as H2.
*)
(*
apply (rngl_nle_gt Hor) in H1.
apply H1; clear H1.
*)
specialize (Hu (angle_eucl_dist (u N) θ)) as H2.
destruct (rngl_lt_dec Hor 0 (angle_eucl_dist (u N) θ)) as [Hzut| Hzut]. {
  specialize (H2 Hzut).
  destruct H2 as (M, HM).
...
specialize (angle_eucl_dist_triangular θ θ' (u N)) as H2.
rewrite (angle_eucl_dist_symmetry Hic Hop) in H2.
...
eapply (rngl_le_trans Hor).
apply H2.
...
apply angle_nlt_ge.
intros Htt.
apply (rngl_nle_gt Hor) in H1.
apply H1; clear H1.
specialize (angle_eucl_dist_triangular θ' (u N) θ) as H1.
rewrite (angle_eucl_dist_symmetry Hic Hop) in H1.
...
progress unfold angle_eucl_dist in Hu.
progress unfold angle_eucl_dist in Hv.
progress unfold angle_leb.
(* ouais, chais pas *)
...
rewrite angle_eucl_dist_move_0_r in Hu, Hv.
...
specialize (angle_eucl_dist_triangular θ' (f N) θ) as H1.
rewrite (angle_eucl_dist_symmetry Hic Hop) in H1.
progress fold ε in H1.
specialize (angle_eucl_dist_triangular θ (g N) θ') as H2.
progress fold ε in H2.
...
progress unfold angle_ltb in Htt.
...
apply angle_lt_eq_cases.
remember (θ =? θ')%A as ett eqn:Hett.
symmetry in Hett.
destruct ett. {
  apply (angle_eqb_eq Hed) in Hett.
  now right.
}
apply (angle_eqb_neq Hed) in Hett.
left.

...
Check angle_eucl_dist_separation.
Check angle_eucl_dist_symmetry.
... ...
specialize (angles_lim_le (λ i, 2 ^ i / n * (θ / ₂^i)) (λ _, θ))%A as H1.
specialize (H1 θ' θ)%A.
assert (Htt : (θ' ≤ θ)%A). {
  apply H1; [ | easy | ]. 2: {
    intros ε Hε.
    exists 0.
    intros p _.
    now rewrite angle_eucl_dist_diag.
  }
  intros.
Theorem seq_angle_converging_to_angle_div_nat_le :
  ∀ i n θ, (2 ^ i / n * (θ / ₂^i) ≤ θ)%A.
Proof.
... ...
  apply seq_angle_converging_to_angle_div_nat_le.
}
...
      specialize (Hlim (angle_eucl_dist θ' 0)).
      assert (Htz : (0 < angle_eucl_dist θ' 0)%L). {
        apply (rngl_lt_iff Hor).
        split; [ apply angle_eucl_dist_nonneg | ].
        intros H; symmetry in H.
        apply angle_eucl_dist_separation in H.
        subst θ'.
        rewrite (angle_mul_0_r Hon Hos) in Hzm.
        now apply (rngl_lt_irrefl Hor) in Hzm.
      }
      specialize (Hlim Htz).
      destruct Hlim as (N, HN).
      specialize (HN N (le_refl _)).
...
specialize (angle_eucl_dist_triangular) as H1.
specialize (H1 θ' (2 ^ N / n * (θ / ₂^N)) 0)%A.
exfalso.
apply (rngl_nlt_ge Hor) in H1.
apply H1; clear H1.
rewrite (angle_eucl_dist_symmetry Hic Hop).
eapply (rngl_le_lt_trans Hor); [ | apply HN ].
(* ah bin non *)
...
Search (rngl_cos _ ≤ rngl_cos _)%L.
apply angle_add_overflow_le_lemma_4 with (θ2 := (m * θ')%A); try easy.
apply quadrant_1_rngl_cos_add_le_cos_l.
Check seq_angle_converging_to_angle_div_nat_le.
... ...
Theorem seq_angle_converging_to_angle_div_nat_le :
  ∀ i n θ, (2 ^ i / n * (θ / ₂^i) ≤ θ)%A.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%A), (H1 θ).
  apply angle_le_refl.
}
intros.
progress unfold angle_leb.
remember (0 ≤? rngl_sin (2 ^ i / n * (θ / ₂^i)))%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs2, Hzs.
destruct zs2. {
  clear Hzs2.
  destruct zs; [ | easy ].
  apply rngl_leb_le in Hzs.
  apply rngl_leb_le.
  destruct i. {
    cbn.
    destruct n; [ apply rngl_cos_bound | ].
    destruct n. {
      rewrite Nat.div_1_r.
      rewrite (angle_mul_1_l Hon Hos).
      apply (rngl_le_refl Hor).
    }
    rewrite Nat.div_small; [ | now apply -> Nat.succ_lt_mono ].
    rewrite angle_mul_0_l.
    apply rngl_cos_bound.
  }
  destruct n; [ apply rngl_cos_bound | ].
  destruct n. {
    rewrite Nat.div_1_r.
    rewrite angle_mul_2_pow_div_2_pow.
    apply (rngl_le_refl Hor).
  }
  apply (rngl_le_trans Hor _ (rngl_cos (2 ^ S i / 2 * (θ / ₂^S i)))). {
    rewrite Nat.pow_succ_r'.
    rewrite Nat.mul_comm.
    rewrite Nat.div_mul; [ | easy ].
    rewrite angle_div_2_pow_nat_succ_r_2.
    rewrite angle_mul_2_pow_div_2_pow.
    now apply rngl_cos_le_cos_div_2.
  }
  apply rngl_cos_decr.
  split. {
    apply angle_mul_nat_le_mono_nonneg_r. {
      rewrite Nat.pow_succ_r'.
      rewrite Nat.mul_comm.
      rewrite Nat.div_mul; [ | easy ].
      rewrite angle_div_2_pow_nat_succ_r_2.
      apply angle_mul_nat_overflow_pow_div.
    }
    apply Nat.div_le_compat_l.
    split; [ easy | ].
    now do 2 apply -> Nat.succ_le_mono.
  }
  rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  rewrite angle_div_2_pow_nat_succ_r_2.
  rewrite angle_mul_2_pow_div_2_pow.
  apply angle_div_2_le_straight.
}
destruct zs. {
  exfalso.
  apply (rngl_leb_gt Hor) in Hzs2.
  apply rngl_leb_le in Hzs.
  apply (rngl_nle_gt Hor) in Hzs2.
  apply Hzs2; clear Hzs2.
  revert n θ Hzs.
  induction i; intros. {
    cbn.
    destruct n; [ apply (rngl_le_refl Hor) | ].
    destruct n. {
      rewrite Nat.div_1_r.
      now rewrite (angle_mul_1_l Hon Hos).
    }
    rewrite Nat.div_small; [ | now do 2 apply -> Nat.succ_le_mono ].
    apply (rngl_le_refl Hor).
  }
  rewrite angle_div_2_pow_nat_succ_r_2.
  eapply (rngl_le_trans Hor). {
    apply (IHi n (θ / ₂)%A).
    apply rngl_sin_div_2_nonneg.
  }
(*
destruct n; [ apply (rngl_le_refl Hor) | ].
destruct n. {
  do 2 rewrite Nat.div_1_r.
  rewrite <- angle_div_2_pow_nat_succ_r_2.
  rewrite angle_mul_2_pow_div_2_pow.
  rewrite -> angle_div_2_pow_nat_succ_r_2.
  rewrite angle_mul_2_pow_div_2_pow.
}
*)
  remember (θ ≤? angle_right)%A as tr eqn:Htr.
  symmetry in Htr.
  destruct tr. {
    apply rngl_sin_incr.
    split. {
      apply angle_mul_nat_le_mono_nonneg_r. {
        destruct n; [ easy | ].
        apply angle_mul_nat_not_overflow_le_l with (n := 2 ^ S i). {
          rewrite <- Nat.div_1_r.
          apply Nat.div_le_compat_l.
          split; [ easy | ].
          now apply -> Nat.succ_le_mono.
        }
        rewrite Nat.pow_succ_r'.
        apply angle_mul_nat_overflow_angle_div_2_mul_2_div_2.
        apply angle_mul_nat_overflow_pow_div.
      }
      destruct n; [ easy | ].
      apply Nat.div_le_mono; [ easy | ].
      apply Nat.pow_le_mono_r; [ easy | ].
      apply Nat.le_succ_diag_r.
    }
    destruct n; [ apply angle_right_nonneg | ].
    destruct n. {
      rewrite Nat.div_1_r.
      rewrite <- angle_div_2_pow_nat_succ_r_2.
      now rewrite angle_mul_2_pow_div_2_pow.
    }
...
(*
  rewrite <- (angle_mul_1_l Hon Hos angle_right).
  rewrite <- angle_straight_div_2.
*)
  rewrite <- angle_div_2_pow_nat_succ_r_2.
(*
  rewrite angle_div_2_pow_nat_succ_r_1.
*)
  apply angle_le_trans with (θ2 := (2 ^ S i * (θ / ₂^S i))%A). {
(*
    rewrite <- (angle_mul_1_l Hon Hos (2 ^ S i * _)).
*)
    apply angle_mul_nat_le_mono_nonneg_r. {
      apply angle_mul_nat_overflow_pow_div.
    }
    rewrite <- (Nat.div_1_r (2 ^ S i)) at 2.
    apply Nat.div_le_compat_l.
    split; [ easy | ].
    now apply -> Nat.succ_le_mono.
  }
  rewrite angle_mul_2_pow_div_2_pow.
(* rahhhh... fait chier *)
...
  apply angle_le_trans with (θ2 := 0%A).
Search (_ * _ ≤ _ * _)%A.
...
Show.
Check seq_angle_converging_to_angle_div_nat_le.
Search (_ → angle_mul_nat_overflow _ _ = false).
...
(*
...
Search (_ * (_ / ₂^_))%A.
Search (rngl_cos (_ * _)).
(* faire un Fixpoint, comme pour rngl_cos_div_pow_2 *)
...
Search rngl_cos_div_pow_2.
rngl_cos_div_pow_2_eq: ∀ (θ : angle T) (n : nat), rngl_cos (θ / ₂^S n) = rngl_cos_div_pow_2 (θ / ₂) n
...
Search (_ * _)%A.
rewrite rngl
Search (rngl_cos _ ≤ rngl_cos _)%L.
Check angle_add_overflow_le_lemma_111.
remember ((2 ^ i / n * (θ / ₂^i)))%A as θ' eqn:Hθ'.
destruct (rngl_le_dec Hor 0 (rngl_cos θ')) as [Hsc| Hsc].
specialize (angle_add_overflow_le_lemma_111 θ' (θ - θ')) as H1.
Search (_ + (_ - _))%A.
Search (_ - _ + _)%A.
rewrite (angle_add_comm Hic) in H1.
rewrite angle_sub_add in H1.
apply H1; try easy; [ now right; right; left | ].
(* θ' ≤ θ ? *)
...
Search (0 ≤ rngl_sin (_ - _))%L.
apply rngl_sin_sub_nonneg; try easy.
...
rewrite angle
rewrite angle_add_0_r in H1.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
apply rngl_cos_le_anticompat_when_sin_nonneg; try easy.
...
  apply rngl_cos_decr.
  split. {
progress unfold angle_leb.
apply rngl_leb_le in Hzs2, Hzs.
rewrite Hzs2, Hzs.
    destruct i. {
      cbn.
      rewrite <- (angle_mul_1_l Hon Hos θ) at 2.
      apply angle_mul_nat_le_mono_nonneg_r; [ easy | ].
      destruct n; [ easy | ].
      apply Nat.div_le_upper_bound; [ easy | ].
      cbn.
      now apply -> Nat.succ_le_mono.
    }
    cbn.
    rewrite Nat.add_0_r.
    destruct i. {
      cbn.
Search (_ * (_ / ₂))%A.
rewrite angle_mul_nat_div_2.
...
  destruct i. {
    destruct n; [ apply rngl_cos_bound | ].
    remember (S n) as sn; cbn; subst sn.
*)
...
Theorem glop :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
intros * Hzs1 Hzc1 Hzs12.
cbn.
(* non, c'est faux, ça, suffit que θ2 = 2π-ε *)
... ...
now apply glop.
Search (0 ≤ rngl_sin (_ + _))%L.
specialize (rngl_sin_nonneg_add_nonneg θ' (m * θ') Hzs Hzsm) as H1.
      apply angle_add_overflow_le_lemma_111; try easy. {
        now right; right; left.
      }
      rewrite (angle_add_comm Hic) in Hzsm.
      apply rngl_sin_add_nonneg_sin_nonneg with (θ2 := θ'); [ | easy ].
      progress unfold angle_add_overflow.
      apply angle_ltb_ge.
      progress unfold angle_leb.
      apply rngl_leb_le in Hzsm.
      rewrite Hzsm.
...
Search (0 ≤ rngl_sin (_ + _))%L.
Search (rngl_cos (_ + _) ≤ rngl_cos _)%L.
...
    apply rngl_cos_decr.
    split; [ | now apply rngl_sin_nonneg_angle_le_straight ].
    progress unfold angle_leb.
    rewrite Hzs.
    apply rngl_leb_le in Hzsm.
    rewrite Hzsm.
    apply rngl_leb_le.
...
destruct n; [ easy | ].
destruct n. {
  cbn.
  rewrite Bool.orb_false_r.
  rewrite angle_add_0_r.
  progress unfold angle_lim in Hlim.
  progress unfold is_limit_when_tending_to_inf in Hlim.
  progress unfold angle_add_overflow.
  progress unfold angle_ltb.
  remember (0 ≤? rngl_sin (θ' + θ'))%L as zsa eqn:Hzsa.
  remember (0 ≤? rngl_sin θ')%L as zs eqn:Hzs.
  symmetry in Hzsa, Hzs.
  destruct zsa. {
    apply rngl_leb_le in Hzsa.
    destruct zs. {
      apply rngl_leb_le in Hzs.
      apply (rngl_ltb_ge Hor).
      destruct (rngl_le_dec Hor 0 (rngl_cos θ')) as [Hzc| Hzc]. {
        apply angle_add_overflow_le_lemma_111; try easy.
        now right; right; left.
      }
      apply (rngl_nle_gt Hor) in Hzc.
      remember (θ' =? angle_straight)%A as ts eqn:Hts.
      symmetry in Hts.
      destruct ts. {
        apply (angle_eqb_eq Hed) in Hts.
        subst θ'.
        clear Hzc Hzs Hzsa.
...
        apply angle_add_overflow_le_lemma_2; try easy. {
          intros H.
          apply eq_rngl_cos_opp_1 in H.
          subst θ'.
cbn in *.
Search (rngl_cos (_ + _) ≤ rngl_cos _)%L.
...
apply angle_add_overflow_le_lemma_111; try easy.
apply angle_add_overflow_le_lemma_1 with (θ2 := θ'); try easy.
apply quadrant_1_rngl_cos_add_le_cos_l; try easy.
...
}
... ...
now apply angle_lim_seq_angle_not_mul_overflow in Hlim.
... ...
destruct ao. 2: {
  specialize (Hlim' eq_refl).
  progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
  progress unfold seq_angle_converging_to_angle_div_nat in Hlim'.
  set (θi := λ i, (2 ^ i / n * (θ / ₂^i))%A).
  set (θ'i := λ i, (2 ^ i / n * (n * θ' / ₂^i))%A).
  progress fold θi in Hlim.
  progress fold θ'i in Hlim'.
  move Hlim before Hlim'.
  move θ'i before θi.
...
(*
...
  clear Hlim'.
  destruct n; [ easy | ].
  apply (angle_mul_nat_overflow_succ_l Hon Hos) in Hao.
...
  apply Bool.not_false_iff_true in Hao.
  exfalso; apply Hao; clear Hao Hlim'.
(**)
  progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
...
Theorem glop :
  ∀ n θ u,
  angle_lim u θ
  → (∀ i, angle_mul_nat_overflow n (u i) = false)
  → angle_mul_nat_overflow n θ = false.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hlim Hov.
induction n; [ easy | ].
apply (angle_mul_nat_not_overflow_succ_l Hon Hos).
split. {
  apply IHn.
  intros i.
  specialize (Hov i).
  now apply (angle_mul_nat_not_overflow_succ_l Hon Hos) in Hov.
}
progress unfold angle_lim in Hlim.
progress unfold is_limit_when_tending_to_inf in Hlim.
... ...
apply (glop n) in Hlim; [ easy | ].
intros i.
clear Hlim Hiz.
induction n; [ easy | ].
cbn - [ div ].
destruct n; [ easy | ].
set (u := seq_angle_converging_to_angle_div_nat θ).
cbn in IHn.
destruct n. {
  clear IHn.
  cbn - [ u ].
  rewrite Bool.orb_false_iff.
  rewrite angle_add_0_r.
  split; [ | easy ].
  apply angle_add_diag_not_overflow; [ easy | ].
  progress unfold u; cbn - [ div ].
  progress unfold seq_angle_converging_to_angle_div_nat.
  induction i. {
    cbn.
    apply (angle_straight_pos Hc1).
  }
  cbn - [ div ].
  rewrite Nat.add_0_r.
  rewrite Nat_add_diag.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  rewrite angle_mul_nat_div_2. 2: {
    apply angle_mul_nat_overflow_pow_div.
  }
  apply (angle_div_2_lt_straight Hc1).
}
...
  apply angle_div_2_add_not_overflow.
  cbn in Haov.
Print angle_add_overflow.
Print angle_mul_nat_overflow.
...
Check angle_mul_overflow.
...
2: {
Search (angle_add_overflow _ (S _ * _)).
Search (angle_add_overflow (S _ * _) _).
cbn in Haov.
Search (angle_add_overflow _ (_ + _)).
...
symmetry.
apply angle_div_2_add_not_overflow.
... ...
rewrite angle_mul_nat_div_2.
Search (_ / ₂ < angle_straight)%A.
...
Search (0 ≤ angle_straight)%A.
Search (0 < angle_straight)%A.
    apply angle_straight_nonneg.
...
apply rngl_mul_neg_neg.
...
  apply rngl_leb_nle in Hzst.
  apply Hzst; clear Hzst; cbn.
...
  cbn.
  apply (rngl_le_trans Hor _ (rngl_cos θ * rngl_cos θ)). {
    apply (rngl_le_sub_nonneg Hop Hor).
    apply (rngl_mul_diag_nonneg Hop Hor).
  }
...
apply rngl_mul_non
...
  apply (rngl_mul_nonneg_r).
...
  apply (rngl_le_sub_le_add_r Hop Hor).
Search (_ ≤ _ + _)%L.
...
Search (_ → angle_add_overflow _ _ = false).
Theorem glip :
  ∀ θ i,
  angle_add_overflow (seq_angle_converging_to_angle_div_nat θ 2 i)
    (seq_angle_converging_to_angle_div_nat θ 2 i) = false.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
induction i. {
  cbn.
  apply (angle_add_overflow_0_r Hon Hos).
}
cbn - [ div ].
Theorem seq_angle_converging_to_angle_div_nat_succ_r :
  ∀ θ n i,
  seq_angle_converging_to_angle_div_nat θ n (S i) = 0%A.
Proof.
intros.
progress unfold seq_angle_converging_to_angle_div_nat.
cbn.
rewrite Nat.add_0_r.
Search ((_ + _) / _).
(* ah la la la la... ça a pas l'air simple, c't'histoire *)
...
  revert θ' Hlim.
  induction n; intros; [ easy | clear Hiz ].
  destruct n; [ easy | ].
  specialize (IHn (Nat.neq_succ_0 _)).
  destruct n. {
    cbn.
    rewrite angle_add_0_r.
    rewrite Bool.orb_false_r.
    clear IHn.
    progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
    progress unfold angle_lim in Hlim.
    progress unfold is_limit_when_tending_to_inf in Hlim.
...
  rewrite (angle_mul_nat_not_overflow_succ_l Hon Hos).
...
  progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
  progress unfold angle_lim in Hlim.
  progress unfold is_limit_when_tending_to_inf in Hlim.
*)
...
} {
  specialize (Hlim' eq_refl).
  move Hao before Hiz.
(**)
  progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
  progress unfold seq_angle_converging_to_angle_div_nat in Hlim'.
  set (θi := λ i, (2 ^ i / n * (θ / ₂^i))%A).
  set (θ'i := λ i, (2 ^ i / n * (n * θ / ₂^i))%A).
  progress fold θi in Hlim.
  progress fold θ'i in Hlim'.
...
  assert
      (H :
       angle_lim (λ i, (n * (θi i))%A) θ'). {
    progress unfold angle_lim in Hlim'.
    progress unfold angle_lim.
    progress unfold is_limit_when_tending_to_inf in Hlim'.
    progress unfold is_limit_when_tending_to_inf.
    intros ε Hε.
    specialize (Hlim' ε Hε).
    destruct Hlim' as (N, HN).
    exists N.
    intros m Hm.
    specialize (HN m Hm).
    rewrite angle_div_2_pow_nat_mul in HN; [ | easy | easy ].
    rewrite (angle_mul_nat_assoc Hon Hop) in HN.
    rewrite Nat.mul_comm in HN.
    rewrite <- (angle_mul_nat_assoc Hon Hop) in HN.
    easy.
  }
  clear Hlim'; rename H into Hlim'.
...
  set (u := seq_angle_converging_to_angle_div_nat) in Hlim, Hlim'.
  assert (H :
    ∀ ε, (0 < ε)%L →
    ∃ N, ∀ p, N ≤ p → (angle_eucl_dist (u θ n p) (u (n * θ')%A n p) < ε)%L). {
    intros ε Hε.
    assert (Hε2 : (0 < ε / 2)%L). {
      apply (rngl_lt_div_r Hon Hop Hiv Hor).
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      now rewrite (rngl_mul_0_l Hos).
    }
    specialize (Hlim (ε / 2) Hε2)%L.
    specialize (Hlim' (ε / 2) Hε2)%L.
    destruct Hlim as (N, HN).
    destruct Hlim' as (N', HN').
    exists (max N N').
    intros p Hp.
    assert (H : N ≤ p) by flia Hp.
    specialize (HN _ H); clear H.
    assert (H : N' ≤ p) by flia Hp.
    specialize (HN' _ H); clear H.
    specialize (angle_eucl_dist_triangular) as H1.
    specialize (H1 (u θ n p) θ' (u (n * θ')%A n p)).
    rewrite (angle_eucl_dist_symmetry Hic Hop θ') in H1.
    eapply (rngl_le_lt_trans Hor); [ apply H1 | ].
    specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as H2.
    rewrite (rngl_add_diag2 Hon) in H2.
    rewrite (rngl_mul_div Hi1) in H2. 2: {
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    rewrite H2.
    now apply (rngl_add_lt_compat Hop Hor).
  }
  remember (θ <? n * θ')%A as tt' eqn:Htt'.
  symmetry in Htt'.
  destruct tt'. {
    exfalso.
    remember (n * θ' - θ)%A as Δθ eqn:Hdt.
    apply angle_add_move_l in Hdt.
    specialize (H 1%L).
    assert (H1 : (0 < 1)%L) by apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
    specialize (H H1); clear H1.
    destruct H as (N, HN).
    specialize (HN N (Nat.le_refl _)).
    rewrite <- Hdt in HN.
    progress unfold u in HN.
    progress unfold seq_angle_converging_to_angle_div_nat in HN.
...
  remember (θ =? n * θ')%A as tt eqn:Htt.
  symmetry in Htt.
  destruct tt; [ now apply angle_eqb_eq in Htt | ].
  apply (angle_eqb_neq Hed) in Htt; exfalso.
Search (_ <? _)%A.
...
    specialize (HN' _ H).
    specialize (HN (Nat.le_max_l _ _)).
  specialize (HN' (Nat.le_max_r _ _)).
  progress unfold angle_eucl_dist in HN.
  progress unfold angle_eucl_dist in HN'.
  set (m := max N N') in HN, HN'.
...
  specialize (Hlim 1%L).
  specialize (H1 1%L).
  assert (H : (0 < 1)%L) by apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  specialize (Hlim H).
  specialize (H1 H); clear H.
  destruct Hlim as (N, HN).
  destruct H1 as (N', HN').
  specialize (HN (max N N')).
  specialize (HN' (max N N')).
  specialize (HN (Nat.le_max_l _ _)).
  specialize (HN' (Nat.le_max_r _ _)).
  progress unfold angle_eucl_dist in HN.
  progress unfold angle_eucl_dist in HN'.
  set (m := max N N') in HN, HN'.
...
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
intros Hic Hon Hop Har Hed Hch * Hiz Hlim.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
revert θ θ' Hlim.
induction i; intros; [ easy | ].
clear Hiz.
destruct i. {
  clear IHi; cbn.
  rewrite angle_add_0_r.
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
  specialize (angle_dist_is_dist Hic) as H1.
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
  rewrite angle_add_0_r.
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
    rewrite (angle_mul_2_pow_div_2_pow Hic) in HN.
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
apply (angle_sub_move_r Hic).
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
    apply rngl_div_lt_pos.
...

Definition angle_div_nat θ n :=
  {| rngl_cos := 1; rngl_sin := 0;
     rngl_cos2_sin2 := 42 |}%L.
...
*)

Theorem Cauchy_sin_cos_Cauchy_angle :
  ∀ u,
  rngl_is_Cauchy_sequence (λ i, rngl_cos (u i))
  → rngl_is_Cauchy_sequence (λ i, rngl_sin (u i))
  → is_Cauchy_sequence angle_eucl_dist u.
Proof.
destruct_ac.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hcc Hcs.
  intros ε Hε.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hcc Hcs.
intros ε Hε.
assert (Hε2 : (0 < √(ε² / 2))%L). {
  apply (rl_sqrt_pos Hos).
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  rewrite (rngl_mul_0_l Hos).
  progress unfold rngl_squ.
  now apply (rngl_mul_pos_pos Hop Hor Hii).
}
specialize (Hcc _ Hε2).
specialize (Hcs _ Hε2).
destruct Hcc as (cn, Hcc).
destruct Hcs as (sn, Hcs).
move sn before cn.
exists (max cn sn).
intros p q Hp Hq.
progress unfold angle_eucl_dist.
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hop Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor ε)%L. 2: {
  now apply (rngl_lt_le_incl Hor) in Hε.
}
apply (rngl_squ_lt_abs_lt Hop Hor Hii).
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hop Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
specialize (Hcc p q).
specialize (Hcs p q).
assert (H : cn ≤ p) by now apply Nat.max_lub_l in Hp.
specialize (Hcc H); clear H.
assert (H : cn ≤ q) by now apply Nat.max_lub_l in Hq.
specialize (Hcc H); clear H.
assert (H : sn ≤ p) by now apply Nat.max_lub_r in Hp.
specialize (Hcs H); clear H.
assert (H : sn ≤ q) by now apply Nat.max_lub_r in Hq.
specialize (Hcs H); clear H.
progress unfold rngl_dist in Hcc.
progress unfold rngl_dist in Hcs.
apply (rngl_lt_le_incl Hor) in Hε2.
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L in Hcc, Hcs; [ | easy | easy ].
apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid) in Hcc, Hcs.
assert (Hzε2 : (0 ≤ ε² / 2)%L). {
  apply (rngl_le_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_squ_nonneg Hop Hor).
}
rewrite rngl_squ_sqrt in Hcc, Hcs; [ | easy | easy ].
specialize (rngl_div_add_distr_r Hiv ε² ε² 2)%L as H1.
rewrite (rngl_add_diag2 Hon) in H1.
rewrite (rngl_mul_div Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite H1.
rewrite (rngl_squ_sub_comm Hop) in Hcc, Hcs.
now apply (rngl_add_lt_compat Hop Hor).
Qed.

(* to be completed
Theorem seq_angle_converging_to_angle_div_nat_is_Cauchy :
  ∀ n θ,
  is_Cauchy_sequence angle_eucl_dist
    (seq_angle_converging_to_angle_div_nat θ n).
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  intros ε Hε.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros.
set (u := λ i, (2 ^ i / n * angle_div_2_pow_nat θ i)%A).
apply Cauchy_sin_cos_Cauchy_angle. {
  progress unfold seq_angle_converging_to_angle_div_nat.
  enough (H :
    ∀ ε, (0 < ε)%L →
    ∃ N : nat,
      ∀ p q : nat,
      N ≤ p
      → N ≤ q
      → (rngl_abs (rngl_sin (u p / ₂ + u q / ₂)) < ε / 2)%L). {
  intros ε Hε.
  progress unfold rngl_dist.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros p q Hp Hq.
  specialize (HN p q Hp Hq).
  progress fold (u p).
  progress fold (u q).
  rewrite rngl_cos_sub_rngl_cos.
  rewrite (rngl_abs_opp Hop Hor).
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_abs_mul Hop Hi1 Hor).
  replace (rngl_abs 2) with 2%L. 2: {
    symmetry; apply (rngl_abs_nonneg_eq Hop Hor).
    apply (rngl_0_le_2 Hon Hop Hor).
  }
  rewrite (rngl_mul_comm Hic).
  apply (rngl_lt_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_abs_mul Hop Hi1 Hor).
  remember (rngl_sin _)%L as s eqn:Hs.
  eapply (rngl_le_lt_trans Hor _ (rngl_abs s * 1))%L. {
    apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
      apply (rngl_abs_nonneg Hop Hor).
    }
    clear s Hs HN.
    remember (rngl_sin _) as s eqn:Hs.
    progress unfold rngl_abs.
    remember (s ≤? 0)%L as sz eqn:Hsz.
    symmetry in Hsz; subst s.
    destruct sz. {
      apply (rngl_opp_le_compat Hop Hor).
      rewrite (rngl_opp_involutive Hop).
      apply rngl_sin_bound.
    }
    apply rngl_sin_bound.
  }
  rewrite (rngl_mul_1_r Hon).
  easy.
}
intros ε Hε.
...
set (u := seq_angle_converging_to_angle_div_nat θ n).
...

Theorem all_gc_has_nth_root :
  rngl_is_archimedean T = true →
  rngl_characteristic T = 0 →
  rl_has_integral_modulus T = true →
  ∀ n, n ≠ 0 → ∀ z : GComplex T, ∃ x : GComplex T, gc_power_nat x n = z.
Proof.
destruct_ac.
intros Har Hch Him * Hnz *.
specialize (polar Him z) as H1.
set (ρ := √((gre z)² + (gim z)²)%L).
set
  (θ :=
     (if (0 ≤? gim z)%L then rl_acos Hor (gre z / ρ)%L
      else angle_opp (rl_acos Hor (gre z / ρ)%L))).
specialize (H1 ρ θ eq_refl eq_refl).
set (ρ' := rl_nth_root n ρ).
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat as H2.
specialize (H2 Har Hch).
remember (seq_angle_converging_to_angle_div_nat θ n) as θi eqn:Hθi.
progress unfold seq_angle_converging_to_angle_div_nat in Hθi.
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
     rngl_opt_mul_le_compat_non_opp := NA;
     rngl_opt_not_le := NA;
     rngl_opt_archimedean := NA |}.
*)
