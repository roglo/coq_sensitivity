(* Real-Like numbers *)
(* Algebraic structure having the same properties as real numbers *)
(* and complex numbers *)
(* see also Quaternions.v *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Init.Nat.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike Main.IterAdd.
Require Import RealLike.
Require Import TrigoWithoutPi.

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

Theorem fold_rl_sqrt : rl_nth_root 2 = rl_sqrt.
Proof. easy. Qed.

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

Theorem rl_sqrt_0 :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  rl_sqrt 0%L = 0%L.
Proof.
intros Hop Hic Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rl_nth_root_pow 2 0%L (rngl_le_refl Hor _)) as H1.
rewrite <- (rngl_squ_0 Hos) in H1 at 2.
rewrite <- rngl_squ_pow_2 in H1.
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hii) in H1.
rewrite (rngl_abs_0 Hop) in H1.
rewrite (rngl_abs_nonneg Hop Hor) in H1; [ easy | ].
apply rl_sqrt_nonneg, (rngl_le_refl Hor).
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
rewrite (rngl_abs_nonneg Hop Hor) in H1. 2: {
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

Theorem eq_rl_sqrt_0 :
  rngl_has_opp_or_subt T = true →
  ∀ a, (0 ≤ a)%L → rl_sqrt a = 0%L → a = 0%L.
Proof.
intros Hos * Hza Ha.
apply (f_equal rngl_squ) in Ha.
rewrite rngl_squ_sqrt in Ha; [ | easy ].
progress unfold rngl_squ in Ha.
now rewrite (rngl_mul_0_l Hos) in Ha.
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

(*
End a.
*)

Fixpoint gc_power_nat {T} {ro : ring_like_op T} (z : GComplex T) n :=
  match n with
  | 0 => gc_one
  | S n' => gc_mul z (gc_power_nat z n')
  end.

(*
Arguments rl_sqrt {T ro rp rl} _%L.
*)

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

Theorem angle_div_2_mul_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ a, angle_mul_nat (angle_div_2 a) 2 = a.
Proof.
intros Hic Hon Hop Hed *.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
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
rewrite rngl_add_0_l.
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
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Hz1sc : (0 ≤ 1 - rngl_cos a)%L). {
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
}
rewrite rngl_squ_sqrt. 2: {
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
rewrite (rngl_add_diag2 Hon).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_r Hon Hiv); [ | easy ].
rewrite (rngl_mul_1_r Hon); f_equal.
progress unfold rl_sqrt.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_add_diag2 Hon).
rewrite (rngl_mul_comm Hic ε).
rewrite rngl_mul_assoc.
rewrite <- rl_nth_root_mul; cycle 1. {
  rewrite (fold_rngl_div Hiv).
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
} {
  rewrite (fold_rngl_div Hiv).
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
  apply (rngl_square_ge_0 Hop Hor).
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
rewrite rngl_squ_pow_2.
progress unfold rl_sqrt.
rewrite rl_nth_root_pow; [ | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic).
rewrite (rngl_mul_comm Hic).
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_l Hon Hiv); [ | easy ].
rewrite (rngl_mul_1_r Hon).
rewrite <- rl_nth_root_mul; [ | easy | easy ].
rewrite (rngl_mul_comm Hic (1 - _)%L).
rewrite <- (rngl_squ_sub_squ Hop Hic).
progress unfold rngl_squ at 1.
rewrite (rngl_mul_1_r Hon).
destruct a as (ca, sa, Ha); cbn in ε, Hz1ac, Hz1sc |-*.
apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed) in Ha.
rewrite <- Ha, rngl_add_comm, (rngl_add_sub Hos).
progress unfold rngl_squ.
progress unfold ε.
remember (0 ≤? sa)%L as saz eqn:Hsaz; symmetry in Hsaz.
destruct saz. {
  apply rngl_leb_le in Hsaz.
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rl_nth_root_pow 2); [ | easy ].
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
  rewrite <- (rl_nth_root_pow 2); [ | easy ].
  easy.
}
Qed.

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
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
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
  rewrite <- (rngl_mul_1_r Hon 2%L) at 1.
  rewrite <- (rngl_mul_sub_distr_l Hop).
  do 2 rewrite (rngl_mul_comm Hic 2%L).
  rewrite (rngl_mul_div Hi1); [ | easy ].
  rewrite (rngl_mul_div Hi1); [ | easy ].
  rewrite Ha.
  do 2 rewrite (rl_sqrt_squ Hop Hor).
  rewrite (rngl_abs_nonneg Hop Hor sa); [ | easy ].
  f_equal.
  subst ε.
  remember (0 ≤? 2 * sa * ca)%L as zsc eqn:Hzsc; symmetry in Hzsc.
  destruct zsc. {
    apply rngl_leb_le in Hzsc.
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_abs_nonneg Hop Hor).
    apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2⁻¹%L) in Hzsc. 2: {
      apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    rewrite (rngl_mul_0_r Hos) in Hzsc.
    do 2 rewrite rngl_mul_assoc in Hzsc.
    rewrite (rngl_mul_inv_l Hon Hiv) in Hzsc; [ | easy ].
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
  apply (rngl_abs_nonpos Hop Hor).
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
    rewrite (rngl_abs_nonpos Hop Hor sa). 2: {
      now apply (rngl_lt_le_incl Hor).
    }
    f_equal.
    subst ε.
    remember (0 ≤? _)%L as zsc eqn:Hzsc; symmetry in Hzsc.
    destruct zsc. {
      rewrite (rngl_mul_1_l Hon).
      apply (rngl_abs_nonpos Hop Hor).
      apply rngl_leb_le in Hzsc.
      apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2⁻¹%L) in Hzsc. 2: {
        apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      rewrite (rngl_mul_0_r Hos) in Hzsc.
      do 2 rewrite rngl_mul_assoc in Hzsc.
      rewrite (rngl_mul_inv_l Hon Hiv) in Hzsc; [ | easy ].
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
      apply (rngl_abs_nonneg Hop Hor).
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

Theorem gc_opt_add_opp_l :
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
specialize (rngl_add_opp_l Hop) as H1.
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

Theorem gc_opt_mul_inv_l :
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
(*
assert (Hiv : rngl_has_inv T = true). {
  progress unfold rngl_has_inv in Hivc; cbn in Hivc.
  progress unfold gc_opt_inv_or_quot in Hivc.
  progress unfold rngl_has_inv.
  destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
  now destruct iq.
}
*)
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
specialize (rngl_mul_inv_l Hon Hiv) as H1.
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
  rewrite (fold_rngl_sub Hop).
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_mul_swap Hic).
  apply (rngl_sub_diag Hos).
}
Qed.

Theorem gc_opt_mul_inv_r :
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
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
apply (rngl_le_trans Hor _ (rngl_abs a)). {
  apply (rngl_le_abs Hop Hor).
}
apply (rngl_square_le_simpl_nonneg Hop Hor Hii). {
  apply rl_sqrt_nonneg.
  apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
  apply (rngl_square_ge_0 Hop Hor).
}
do 2 rewrite fold_rngl_squ.
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
  apply (rngl_square_ge_0 Hop Hor).
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
  apply (rngl_square_ge_0 Hop Hor).
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
    apply (rngl_square_ge_0 Hop Hor).
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
    apply (rngl_square_ge_0 Hop Hor).
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
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
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
    apply (rngl_add_nonneg_nonneg Hor).
    apply (rngl_square_ge_0 Hop Hor).
    apply (rngl_square_ge_0 Hop Hor).
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
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_square_ge_0 Hop Hor).
  apply (rngl_square_ge_0 Hop Hor).
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
  rewrite (rngl_abs_nonneg Hop Hor ρ). 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_le_div_l Hon Hop Hiv Hor); [ easy | ].
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rngl_abs_nonneg Hop Hor). 2: {
    rewrite Hρ.
    apply rl_sqrt_nonneg.
    apply (rngl_add_nonneg_nonneg Hor).
    apply (rngl_square_ge_0 Hop Hor).
    apply (rngl_square_ge_0 Hop Hor).
  }
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  rewrite Hρ.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_add_nonneg_nonneg Hor).
    apply (rngl_square_ge_0 Hop Hor).
    apply (rngl_square_ge_0 Hop Hor).
  }
  apply (rngl_le_add_r Hor).
  apply (rngl_square_ge_0 Hop Hor).
}
f_equal; [ now destruct (0 ≤? zi)%L | ].
assert (Hri : ((zr / ρ)² + (zi / ρ)² = 1)%L). {
  rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
  rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
  progress unfold rngl_div.
  rewrite Hiv.
  rewrite <- rngl_mul_add_distr_r.
  rewrite (fold_rngl_div Hiv).
  rewrite Hρ.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_add_nonneg_nonneg Hor).
    apply (rngl_square_ge_0 Hop Hor).
    apply (rngl_square_ge_0 Hop Hor).
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
    apply (rngl_add_nonneg_nonneg Hor).
    apply (rngl_square_ge_0 Hop Hor).
    apply (rngl_square_ge_0 Hop Hor).
  }
  apply (rngl_le_add_r Hor).
  apply (rngl_square_ge_0 Hop Hor).
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
  rewrite (rngl_abs_nonneg Hop Hor ρ). 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_div_mul Hon Hiv); [ | easy ].
  symmetry.
  now apply (rngl_abs_nonneg Hop Hor).
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
  rewrite (rngl_abs_nonneg Hop Hor ρ). 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_div_mul Hon Hiv); [ | easy ].
  symmetry.
  now apply (rngl_abs_nonpos Hop Hor).
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
do 2 rewrite (fold_rngl_div Hiv).
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
  → is_limit_when_tending_to_inf (seq_converging_to_rat rad a b)
       (rngl_of_nat a / rngl_of_nat b)%L.
Proof.
intros Hic Hon Hop Har * H2r Hbz.
intros ε Hε.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (int_part Hon Hop Hc1 Hor Har) as H1.
destruct (H1 (1 / ε)%L) as (N, HN).
clear H1.
rewrite (rngl_abs_nonneg Hop Hor) in HN. 2: {
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
  rewrite (rngl_abs_nonpos Hop Hor). 2: {
    apply (rngl_le_sub_0 Hop Hor).
    clear Hm.
    apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
    progress unfold rngl_div.
    rewrite Hiv.
    rewrite (rngl_mul_mul_swap Hic).
    rewrite <- (rngl_of_nat_pow Hon Hos).
    rewrite (fold_rngl_div Hiv).
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

Fixpoint angle_div_2_pow_nat θ i :=
  match i with
  | 0 => θ
  | S i' => angle_div_2 (angle_div_2_pow_nat θ i')
  end.

Arguments angle_div_2_pow_nat θ%A i%nat.

Definition seq_angle_converging_to_angle_div_nat θ (n i : nat) :=
  angle_div_2_pow_nat (2 ^ i / n * θ) i.

Arguments seq_angle_converging_to_angle_div_nat θ%A (n i)%nat.
Arguments rl_sqrt_0 {T ro rp rl} Hor Hop Hic Hii.

Theorem rl_sqrt_lt_rl_sqrt :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ a b,
  (0 ≤ a)%L
  → (a < b)%L
  → (√ a < √ b)%L.
Proof.
intros Hic Hop * Ha Hab.
destruct ac as (Hiv, Hc2, Hor).
apply (rngl_nle_gt Hor).
intros H1.
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H2.
specialize (H2 √b √b √a √a)%L.
assert (H : (0 ≤ √b ≤ √a)%L). {
  split; [ | easy ].
  apply rl_sqrt_nonneg.
  apply (rngl_le_trans Hor _ a); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
specialize (H2 H H).
do 2 rewrite fold_rngl_squ in H2.
rewrite rngl_squ_sqrt in H2. 2: {
  apply (rngl_le_trans Hor _ a); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
rewrite rngl_squ_sqrt in H2; [ | easy ].
now apply (rngl_nle_gt Hor) in Hab.
Qed.

Theorem angle_mul_add_distr_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b θ, ((a + b) * θ = a * θ + b * θ)%A.
Proof.
intros Hon Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
induction a; cbn; [ symmetry; apply (angle_add_0_l Hon Hos) | ].
rewrite IHa.
apply (angle_add_assoc Hop).
Qed.

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

Definition angle_dist θ1 θ2 :=
  rl_sqrt
    ((rngl_cos θ2 - rngl_cos θ1)² +
     (rngl_sin θ2 - rngl_sin θ1)²)%L.

Theorem angle_dist_symmetric :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2, angle_dist θ1 θ2 = angle_dist θ2 θ1.
Proof.
intros Hic Hop *.
progress unfold angle_dist.
f_equal.
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_opp_sub_distr Hop).
f_equal.
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_opp_sub_distr Hop).
easy.
Qed.

Theorem angle_dist_separation :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, angle_dist θ1 θ2 = 0%L → θ1 = θ2.
Proof.
intros Hic Hon Hop Hed * H12.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
apply eq_angle_eq.
destruct θ1 as (c1, s1, Hcs1).
destruct θ2 as (c2, s2, Hcs2).
cbn in H12 |-*.
progress unfold angle_dist in H12.
cbn in H12.
apply (eq_rl_sqrt_0 Hos) in H12. 2: {
  apply (rngl_add_squ_nonneg Hop Hor).
}
apply (rngl_eq_add_0 Hor) in H12; cycle 1. {
  apply (rngl_square_ge_0 Hop Hor).
} {
  apply (rngl_square_ge_0 Hop Hor).
}
destruct H12 as (Hc, Hs).
apply (eq_rngl_squ_0 Hos Hid) in Hc, Hs.
apply -> (rngl_sub_move_0_r Hop) in Hc.
apply -> (rngl_sub_move_0_r Hop) in Hs.
now subst c2 s2.
Qed.

Theorem rl_sqrt_sqr_le_sqrt_add_sqrt :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b c d,
  (√((a + b)² + (c + d)²) ≤ √(a² + c²) + √(b² + d²))%L.
Proof.
intros Hic Hon Hop *.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
rewrite <- (rngl_abs_nonneg Hop Hor). 2: {
  apply (rngl_add_nonneg_nonneg Hor). {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hop Hor).
  } {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hop Hor).
  }
}
rewrite <- (rngl_abs_nonneg Hop Hor (√_))%L. 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_add_squ_nonneg Hop Hor).
}
apply (rngl_squ_le_abs_le Hop Hor Hii).
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hop Hor) ].
rewrite (rngl_squ_add Hic Hon √_)%L.
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hop Hor) ].
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hop Hor) ].
apply (rngl_le_sub_le_add_r Hop Hor).
apply -> (rngl_le_sub_le_add_l Hop Hor).
do 2 rewrite (rngl_squ_add Hic Hon)%L.
rewrite rngl_add_assoc.
rewrite (rngl_sub_add_distr Hos _ b²)%L.
rewrite (rngl_sub_sub_swap Hop _ b²)%L.
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_add_sub Hos).
rewrite rngl_add_assoc.
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_sub_sub_swap Hop).
rewrite rngl_add_add_swap.
rewrite (rngl_add_sub Hos).
rewrite <- rngl_add_assoc.
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
do 3 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_l.
apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
  apply (rngl_le_trans Hor _ 1)%L.
  apply (rngl_0_le_1 Hon Hop Hor).
  apply (rngl_le_add_r Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
eapply (rngl_le_trans Hor); [ apply (rngl_le_abs Hop Hor) | ].
rewrite <- (rngl_abs_nonneg Hop Hor). 2: {
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hop Hor).
  } {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hop Hor).
  }
}
apply (rngl_squ_le_abs_le Hop Hor Hii).
rewrite (rngl_squ_mul Hic).
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hop Hor) ].
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hop Hor) ].
(* c'est pas une formule connue, ça ? un truc chinois, chais plus *)
rewrite (rngl_squ_add Hic Hon).
do 2 rewrite (rngl_squ_mul Hic).
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_add_distr_r _ _ b²)%L.
rewrite (rngl_mul_add_distr_r _ _ d²)%L.
rewrite rngl_add_assoc.
apply (rngl_add_le_mono_r Hop Hor).
rewrite <- rngl_add_assoc.
apply (rngl_add_le_mono_l Hop Hor).
rewrite (rngl_add_comm (_ * _))%L.
rewrite (rngl_mul_comm Hic c²)%L.
do 2 rewrite <- (rngl_squ_mul Hic).
do 2 rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (2 * a * b))%L.
rewrite (rngl_mul_mul_swap Hic (2 * a))%L.
rewrite <- rngl_mul_assoc.
rewrite <- (rngl_mul_assoc 2)%L.
apply (rngl_le_0_sub Hop Hor).
rewrite (rngl_add_sub_swap Hop).
rewrite <- (rngl_squ_sub Hop Hic Hon).
apply (rngl_square_ge_0 Hop Hor).
Qed.

Theorem euclidean_distance_triangular :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ x1 y1 x2 y2 x3 y3,
  (√((x3 - x1)² + (y3 - y1)²)
   ≤ √((x2 - x1)² + (y2 - y1)²) + √((x3 - x2)² + (y3 - y2)²))%L.
Proof.
intros Hic Hon Hop *.
destruct ac as (Hiv, Hc2, Hor).
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
rewrite (rngl_add_comm √((x2 - x1)² + (y2 - y1)²))%L.
replace (x3 - x1)%L with ((x3 - x2) + (x2 - x1))%L. 2: {
  rewrite (rngl_add_sub_assoc Hop).
  now rewrite (rngl_sub_add Hop).
}
replace (y3 - y1)%L with ((y3 - y2) + (y2 - y1))%L. 2: {
  rewrite (rngl_add_sub_assoc Hop).
  now rewrite (rngl_sub_add Hop).
}
apply (rl_sqrt_sqr_le_sqrt_add_sqrt Hic Hon Hop).
Qed.

Theorem angle_dist_triangular :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (angle_dist θ1 θ3 ≤ angle_dist θ1 θ2 + angle_dist θ2 θ3)%L.
Proof.
intros Hic Hon Hop Hed *.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct θ1 as (c1, s1, Hcs1).
destruct θ2 as (c2, s2, Hcs2).
destruct θ3 as (c3, s3, Hcs3).
progress unfold angle_dist.
cbn.
specialize (rngl_abs_triangle Hop Hor) as H1.
apply (euclidean_distance_triangular Hic Hon Hop).
Qed.

Definition is_angle_upper_limit_when_tending_to_inf f (l : angle T) :=
  ∀ ε, (0 < ε)%L → ∃ N, ∀ n : nat, N ≤ n → (angle_dist l (f n) < ε)%L.

Theorem eq_rngl_cos_opp_1 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (rngl_cos θ = -1 → rngl_sin θ = 0)%L.
Proof.
intros Hic Hon Hop Hed * Hθ.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
destruct θ as (c, s, Hcs).
cbn in Hθ |-*.
subst c.
apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed) in Hcs.
rewrite (rngl_squ_opp Hop) in Hcs.
rewrite (rngl_squ_1 Hon) in Hcs.
apply (rngl_add_sub_eq_l Hos) in Hcs.
rewrite (rngl_sub_diag Hos) in Hcs.
symmetry in Hcs.
now apply (eq_rngl_squ_0 Hos Hid) in Hcs.
Qed.

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

Theorem angle_opp_0 :
  rngl_has_opp T = true →
  (- 0)%A = 0%A.
Proof.
intros Hop.
apply eq_angle_eq; cbn.
now rewrite (rngl_opp_0 Hop).
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
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
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

Theorem angle_le_0_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (θ ≤ 0)%A → θ = 0%A.
Proof.
intros Hic Hon Hop Hed * Hθ.
destruct ac as (Hiv, Hc2, Hor).
progress unfold angle_leb in Hθ.
cbn in Hθ.
rewrite (rngl_leb_refl Hor) in Hθ.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; [ | easy ].
apply rngl_leb_le in Hzs, Hθ.
now apply (le_1_rngl_cos Hic Hon Hop Hed) in Hθ.
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

Arguments angle_ltb {T ro rp} (θ1 θ2)%A.

(*here*)

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
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
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

Theorem angle_leb_gt : ∀ θ1 θ2, (θ1 ≤? θ2)%A = false ↔ (θ2 < θ1)%A.
Proof.
intros.
destruct ac as (Hiv, Hc2, Hor).
progress unfold angle_leb.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs2.
  split; intros H12. {
    apply (rngl_leb_gt Hor) in H12.
    now apply rngl_ltb_lt.
  } {
    apply (rngl_leb_gt Hor).
    now apply rngl_ltb_lt in H12.
  }
} {
  apply (rngl_leb_gt Hor) in Hzs1.
  destruct zs2; [ easy | ].
  split; intros H12. {
    apply (rngl_leb_gt Hor) in H12.
    now apply rngl_ltb_lt.
  } {
    apply (rngl_leb_gt Hor).
    now apply rngl_ltb_lt in H12.
  }
}
Qed.

Theorem angle_ltb_ge : ∀ θ1 θ2, (θ1 <? θ2)%A = false ↔ (θ2 ≤ θ1)%A.
Proof.
intros.
destruct ac as (Hiv, Hc2, Hor).
progress unfold angle_ltb.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
split; intros H12. {
  destruct zs1. {
    destruct zs2; [ | easy ].
    apply (rngl_ltb_ge Hor) in H12.
    now apply rngl_leb_le.
  } {
    destruct zs2; [ easy | ].
    apply (rngl_ltb_ge Hor) in H12.
    now apply rngl_leb_le.
  }
} {
  destruct zs1. {
    destruct zs2; [ | easy ].
    apply rngl_leb_le in H12.
    now apply (rngl_ltb_ge Hor).
  } {
    destruct zs2; [ easy | ].
    apply rngl_leb_le in H12.
    now apply (rngl_ltb_ge Hor).
  }
}
Qed.

Theorem fold_angle_sub : ∀ θ1 θ2, (θ1 + - θ2 = θ1 - θ2)%A.
Proof. easy. Qed.

Theorem rngl_cos_opp : ∀ θ, rngl_cos (- θ) = rngl_cos θ.
Proof. easy. Qed.

Theorem rngl_sin_opp : ∀ θ, rngl_sin (- θ) = (- rngl_sin θ)%L.
Proof. easy. Qed.

Theorem angle_opp_add_distr :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2, (- (θ1 + θ2))%A = (- θ2 - θ1)%A.
Proof.
intros Hic Hop *.
apply eq_angle_eq; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (fold_rngl_sub Hop).
do 2 rewrite (rngl_mul_comm Hic (rngl_cos θ1)).
do 2 rewrite (rngl_mul_comm Hic (rngl_sin θ1)).
f_equal.
rewrite (rngl_opp_add_distr Hop).
rewrite <- (rngl_mul_opp_r Hop).
rewrite (rngl_mul_opp_l Hop).
now rewrite (fold_rngl_sub Hop).
Qed.

Theorem rngl_sin_nonneg_nonneg_cos_nonneg_neg2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (rngl_cos θ2 < 0)%L
  → (rngl_cos θ1 + rngl_cos θ2 < 0)%L
  → (rngl_sin θ2 < rngl_sin θ1)%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2 Hzc1 Hzc2 Hcc.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
apply (rngl_lt_add_lt_sub_r Hop Hor) in Hcc.
rewrite (rngl_sub_0_l Hop) in Hcc.
rewrite <- (rngl_abs_nonneg Hop Hor); [ | easy ].
rewrite <- (rngl_abs_nonneg Hop Hor (_ θ2)); [ | easy ].
apply (rngl_squ_lt_abs_lt Hop Hor Hii).
apply (rngl_sub_lt_mono_l Hop Hor _ _ 1)%L.
specialize (cos2_sin2_1 Hon Hop Hic Hed) as H1.
rewrite <- (H1 θ1) at 1.
rewrite <- (H1 θ2) at 1.
do 2 rewrite (rngl_add_sub Hos).
apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid).
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
rewrite (rngl_abs_nonpos Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_add_cos_nonneg_when_sin_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ1 + rngl_cos θ2)%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2 Hzs3 Hzc1.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1.
  apply (rngl_le_refl Hor).
}
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  rewrite <- (rngl_mul_1_r Hon (rngl_cos θ1)).
  rewrite <- (rngl_mul_1_l Hon (rngl_cos θ2)).
  eapply (rngl_le_trans Hor); [ apply Hzs3 | ].
  rewrite Hθ3; cbn.
  apply (rngl_add_le_compat Hor). {
    apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
    apply (rngl_sin_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
    apply (rngl_sin_bound Hon Hop Hiv Hic Hed Hor).
  }
} {
  apply (rngl_nle_gt Hor) in Hzc2.
  (* here, for sin θ3 to be non negative, then the negativity
     of θ2 must not be greater than the positivity of θ1 *)
  apply (rngl_le_sub_le_add_r Hop Hor).
  rewrite (rngl_sub_0_l Hop).
  apply (rngl_nlt_ge Hor).
  intros Hcc.
  apply (rngl_nlt_ge Hor) in Hzs3.
  apply Hzs3; clear Hzs3.
  subst θ3; cbn.
  (* special case for sin θ2 = 0 *)
  destruct (rngl_eq_dec Hed (rngl_sin θ2) 0) as [H2z| H2z]. {
    rewrite H2z, (rngl_mul_0_r Hos), rngl_add_0_l.
    destruct (rngl_eq_dec Hed (rngl_sin θ1) 0) as [H1z| H1z]. {
      apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H2z, H1z.
      destruct H2z as [H2z| H2z]. {
        subst θ2.
        apply (rngl_nle_gt Hor) in Hzc2.
        exfalso; apply Hzc2; clear Hzc2; cbn.
        apply (rngl_0_le_1 Hon Hop Hor).
      }
      subst θ2.
      clear Hzs2 Hzc2.
      cbn in Hcc.
      exfalso.
      destruct H1z as [H1z| H1z]. {
        subst θ1.
        rewrite (rngl_opp_involutive Hop) in Hcc.
        cbn in Hcc.
        now apply (rngl_lt_irrefl Hor) in Hcc.
      } {
        subst θ1.
        cbn in Hzc1.
        apply (rngl_nlt_ge Hor) in Hzc1.
        apply Hzc1; clear Hzc1.
        apply (rngl_opp_lt_compat Hop Hor).
        rewrite (rngl_opp_0 Hop).
        rewrite (rngl_opp_involutive Hop).
        apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
      }
    }
    apply (rngl_mul_pos_neg Hop Hor Hid); [ | easy ].
    apply (rngl_lt_iff Hor).
    split; [ easy | ].
    now apply not_eq_sym.
  }
  assert (Hzls2 : (0 < rngl_sin θ2)%L). {
    apply (rngl_lt_iff Hor).
    split; [ easy | ].
    now apply not_eq_sym.
  }
  clear H2z.
  assert (Hs21 : (rngl_sin θ2 < rngl_sin θ1)%L). {
    rewrite <- (rngl_sub_0_l Hop) in Hcc.
    apply (rngl_lt_add_lt_sub_r Hop Hor) in Hcc.
    now apply rngl_sin_nonneg_nonneg_cos_nonneg_neg2.
(* * *)
  }
  apply
    (rngl_le_lt_trans Hor _
       ((- rngl_cos θ2) * rngl_sin θ2 +
          rngl_sin θ1 * rngl_cos θ2))%L. {
    apply (rngl_add_le_mono_r Hop Hor).
    apply (rngl_mul_le_mono_pos_r Hop Hor Hii); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  } {
    rewrite rngl_add_comm.
    rewrite (rngl_mul_comm Hic).
    rewrite (rngl_mul_opp_l Hop).
    rewrite (fold_rngl_sub Hop).
    rewrite <- (rngl_mul_sub_distr_l Hop).
    rewrite (rngl_mul_comm Hic).
    apply (rngl_mul_pos_neg Hop Hor Hid); [ | easy ].
    now apply (rngl_lt_0_sub Hop Hor).
  }
}
Qed.

Theorem rngl_add_cos_nonneg_when_sin_nonpos :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (rngl_sin θ1 ≤ 0)%L
  → (rngl_sin θ2 ≤ 0)%L
  → (rngl_sin (θ1 + θ2) ≤ 0)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ1 + rngl_cos θ2)%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2 Hzs3 Hzc1.
destruct ac as (Hiv, Hc2, Hor).
rewrite <- rngl_cos_opp.
rewrite <- (rngl_cos_opp θ2).
apply (rngl_add_cos_nonneg_when_sin_nonneg Hic Hon Hop Hed). {
  rewrite rngl_sin_opp.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
} {
  rewrite rngl_sin_opp.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
} {
  rewrite fold_angle_sub.
  rewrite <- (angle_opp_add_distr Hic Hop).
  rewrite rngl_sin_opp.
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  now rewrite (angle_add_comm Hic).
} {
  now rewrite rngl_cos_opp.
}
Qed.

Theorem rngl_sin_nonneg_nonneg_cos_nonneg_neg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (rngl_cos θ2 < 0)%L
  → (0 ≤ rngl_cos θ1 + rngl_cos θ2)%L
  → (rngl_sin θ1 ≤ rngl_sin θ2)%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2 Hzc1 Hzc2 Hcc.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
rewrite rngl_add_comm in Hcc.
apply (rngl_le_sub_le_add_l Hop Hor) in Hcc.
rewrite (rngl_sub_0_l Hop) in Hcc.
rewrite <- (rngl_abs_nonneg Hop Hor); [ | easy ].
rewrite <- (rngl_abs_nonneg Hop Hor (_ θ2)); [ | easy ].
apply (rngl_squ_le_abs_le Hop Hor Hii).
apply (rngl_sub_le_mono_l Hop Hor _ _ 1)%L.
specialize (cos2_sin2_1 Hon Hop Hic Hed) as H1.
rewrite <- (H1 θ2) at 1.
rewrite <- (H1 θ1) at 1.
do 2 rewrite (rngl_add_sub Hos).
apply (rngl_abs_le_squ_le Hop Hor).
apply (rngl_lt_le_incl Hor) in Hzc2.
rewrite (rngl_abs_nonpos Hop Hor); [ | easy ].
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
easy.
Qed.

Theorem rngl_add_cos_neg_when_sin_nonneg_neg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_cos θ1)%L
  → (rngl_cos θ1 + rngl_cos θ2 < 0)%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2 Hs3z Hzc1.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 (rngl_sin _)) in Hs3z.
  now apply (rngl_lt_irrefl Hor) in Hs3z.
}
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  apply (rngl_nle_gt Hor) in Hs3z.
  exfalso; apply Hs3z; clear Hs3z.
  rewrite Hθ3; cbn.
  apply (rngl_add_nonneg_nonneg Hor). {
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  } {
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
}
apply (rngl_nle_gt Hor) in Hzc2.
apply (rngl_nle_gt Hor).
intros Hcc.
assert (Hs21 : (rngl_sin θ1 ≤ rngl_sin θ2)%L). {
  now apply rngl_sin_nonneg_nonneg_cos_nonneg_neg.
}
apply (rngl_nle_gt Hor) in Hs3z.
apply Hs3z; clear Hs3z.
rewrite Hθ3; cbn.
replace (rngl_cos θ1) with (rngl_cos θ1 + rngl_cos θ2 - rngl_cos θ2)%L. 2: {
  apply (rngl_add_sub Hos).
}
rewrite (rngl_mul_sub_distr_r Hop).
rewrite <- (rngl_sub_sub_distr Hop).
rewrite (rngl_mul_comm Hic (rngl_cos θ2)).
rewrite <- (rngl_mul_sub_distr_r Hop).
progress unfold rngl_sub at 1.
rewrite Hop.
rewrite <- (rngl_mul_opp_r Hop).
(* ok, all terms are non negative *)
apply (rngl_add_nonneg_nonneg Hor). {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply (rngl_mul_nonneg_nonneg Hop Hor). {
  now apply (rngl_le_0_sub Hop Hor).
} {
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem rngl_add_cos_nonneg_sqrt_mul_le :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_cos θ1 + rngl_cos θ2)%L
  → (√((1 - rngl_cos θ1) * (1 - rngl_cos θ2)) ≤
      √((1 + rngl_cos θ1) * (1 + rngl_cos θ2)))%L.
Proof.
intros Hic Hon Hop Hed Hii * H12.
destruct ac as (Hiv, Hc2, Hor).
assert (Hz1ac :  ∀ θ, (0 ≤ 1 + rngl_cos θ)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1, (H1 √_)%L.
  apply (rngl_le_refl Hor).
}
apply (rngl_square_le_simpl_nonneg Hop Hor Hii). {
  apply rl_sqrt_nonneg.
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
do 2 rewrite fold_rngl_squ.
rewrite rngl_squ_sqrt. 2: {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
rewrite rngl_squ_sqrt. 2: {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_sub_distr Hop).
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_1_r Hon).
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_assoc.
apply (rngl_add_le_mono_r Hop Hor).
rewrite <- (rngl_sub_add_distr Hos).
apply (rngl_le_sub_le_add_r Hop Hor).
do 2 rewrite <- rngl_add_assoc.
apply (rngl_le_add_r Hor).
rewrite rngl_add_assoc.
rewrite rngl_add_add_swap.
rewrite rngl_add_assoc.
rewrite <- rngl_add_assoc.
rewrite (rngl_add_diag Hon).
rewrite (rngl_add_diag Hon (rngl_cos θ2)).
rewrite <- rngl_mul_add_distr_l.
apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
apply (rngl_lt_le_incl Hor).
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
Qed.

Theorem angle_sub_diag :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (θ - θ = 0)%A.
Proof.
intros Hic Hon Hop Hed *.
apply eq_angle_eq; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
do 2 rewrite fold_rngl_squ.
rewrite (cos2_sin2_1 Hon Hop Hic Hed).
f_equal.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_comm Hic).
apply (rngl_add_opp_l Hop).
Qed.

Theorem angle_add_sub_eq_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ a b c, (a + b)%A = c → (c - a)%A = b.
Proof.
intros Hic Hon Hop Hed * Hab.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite <- Hab.
rewrite (angle_add_comm Hic).
progress unfold angle_sub.
rewrite <- (angle_add_assoc Hop).
rewrite fold_angle_sub.
rewrite (angle_sub_diag Hic Hon Hop Hed).
apply (angle_add_0_r Hon Hos).
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

Theorem angle_le_rngl_sin_nonneg_sin_nonneg :
  ∀ θ1 θ2,
  (θ2 ≤ θ1)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L.
Proof.
intros * H21 Hzs1.
destruct ac as (Hiv, Hc2, Hor).
apply Bool.not_false_iff_true in H21.
apply (rngl_nlt_ge Hor).
intros Hs2z.
apply H21; clear H21.
apply angle_leb_gt.
progress unfold angle_ltb.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply (rngl_leb_gt Hor) in Hs2z.
now rewrite Hs2z.
Qed.

Theorem rngl_sin_nonneg_cos_le_sin_le :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L
  → if (0 ≤? rngl_cos θ1)%L then (rngl_sin θ2 ≤ rngl_sin θ1)%L
    else if (0 ≤? rngl_cos θ2)%L then (0 ≤ rngl_sin (θ1 - θ2))%L
    else (rngl_sin θ1 ≤ rngl_sin θ2)%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2 Hc12.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
remember (0 ≤? rngl_cos θ1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_leb_le in Hzc1.
  rewrite <- (rngl_abs_nonneg Hop Hor) in Hc12. 2: {
    eapply (rngl_le_trans Hor); [ apply Hzc1 | easy ].
  }
  rewrite <- (rngl_abs_nonneg Hop Hor _ Hzc1) in Hc12.
  rewrite <- (rngl_abs_nonneg Hop Hor); [ | easy ].
  rewrite <- (rngl_abs_nonneg Hop Hor _ Hzs2).
  apply (rngl_abs_le_squ_le Hop Hor) in Hc12.
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  specialize (cos2_sin2_1 Hon Hop Hic Hed θ1) as Hcs1.
  specialize (cos2_sin2_1 Hon Hop Hic Hed θ2) as Hcs2.
  apply (rngl_add_sub_eq_r Hos) in Hcs1, Hcs2.
  rewrite <- Hcs1, <- Hcs2 in Hc12.
  now apply (rngl_sub_le_mono_l Hop Hor) in Hc12.
}
apply (rngl_leb_gt Hor) in Hzc1.
remember (0 ≤? rngl_cos θ2)%L as zc2 eqn:Hzc2.
symmetry in Hzc2.
destruct zc2. {
  apply rngl_leb_le in Hzc2; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite rngl_add_comm.
  rewrite (fold_rngl_sub Hop).
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_le_trans Hor _ 0)%L. {
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
  } {
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Hzc2.
  apply (rngl_opp_le_compat Hop Hor) in Hc12.
  rewrite <- (rngl_abs_nonpos Hop Hor) in Hc12. 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite <- (rngl_abs_nonpos Hop Hor) in Hc12. 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite <- (rngl_abs_nonneg Hop Hor); [ | easy ].
  rewrite <- (rngl_abs_nonneg Hop Hor _ Hzs1).
  apply (rngl_abs_le_squ_le Hop Hor) in Hc12.
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  specialize (cos2_sin2_1 Hon Hop Hic Hed θ1) as Hcs1.
  specialize (cos2_sin2_1 Hon Hop Hic Hed θ2) as Hcs2.
  apply (rngl_add_sub_eq_r Hos) in Hcs1, Hcs2.
  rewrite <- Hcs1, <- Hcs2 in Hc12.
  now apply (rngl_sub_le_mono_l Hop Hor) in Hc12.
}
Qed.

Theorem rngl_sin_nonneg_cos_lt_sin_lt :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (rngl_cos θ1 < rngl_cos θ2)%L
  → if (0 <? rngl_cos θ1)%L then (rngl_sin θ2 < rngl_sin θ1)%L
    else if (0 <? rngl_cos θ2)%L then (0 < rngl_sin (θ1 - θ2))%L
    else (rngl_sin θ1 < rngl_sin θ2)%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2 Hc12.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
remember (0 <? rngl_cos θ1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_ltb_lt in Hzc1.
  rewrite <- (rngl_abs_nonneg Hop Hor) in Hc12. 2: {
    eapply (rngl_le_trans Hor); [ apply (rngl_lt_le_incl Hor), Hzc1 | ].
    now apply (rngl_lt_le_incl Hor).
  }
  specialize (rngl_lt_le_incl Hor _ _ Hzc1) as H.
  rewrite <- (rngl_abs_nonneg Hop Hor _ H) in Hc12; clear H.
  specialize (rngl_lt_le_incl Hor _ _ Hzs1) as H.
  rewrite <- (rngl_abs_nonneg Hop Hor _ H); clear H.
  specialize (rngl_lt_le_incl Hor _ _ Hzs2) as H.
  rewrite <- (rngl_abs_nonneg Hop Hor _ H); clear H.
  apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid) in Hc12.
  apply (rngl_squ_lt_abs_lt Hop Hor Hii).
  specialize (cos2_sin2_1 Hon Hop Hic Hed θ1) as Hcs1.
  specialize (cos2_sin2_1 Hon Hop Hic Hed θ2) as Hcs2.
  apply (rngl_add_sub_eq_r Hos) in Hcs1, Hcs2.
  rewrite <- Hcs1, <- Hcs2 in Hc12.
  now apply (rngl_sub_lt_mono_l Hop Hor) in Hc12.
}
apply (rngl_ltb_ge Hor) in Hzc1.
remember (0 <? rngl_cos θ2)%L as zc2 eqn:Hzc2.
symmetry in Hzc2.
destruct zc2. {
  apply rngl_ltb_lt in Hzc2; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite rngl_add_comm.
  rewrite (fold_rngl_sub Hop).
  apply (rngl_lt_0_sub Hop Hor).
  apply (rngl_le_lt_trans Hor _ 0)%L. {
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  } {
    now apply (rngl_mul_pos_pos Hop Hor).
  }
} {
  apply (rngl_ltb_ge Hor) in Hzc2.
  apply (rngl_opp_lt_compat Hop Hor) in Hc12.
  rewrite <- (rngl_abs_nonpos Hop Hor) in Hc12; [ | easy ].
  rewrite <- (rngl_abs_nonpos Hop Hor) in Hc12; [ | easy ].
  rewrite <- (rngl_abs_nonneg Hop Hor); [ | now apply (rngl_lt_le_incl Hor) ].
  specialize (rngl_lt_le_incl Hor _ _ Hzs1) as H.
  rewrite <- (rngl_abs_nonneg Hop Hor _ H); clear H.
  apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid) in Hc12.
  apply (rngl_squ_lt_abs_lt Hop Hor Hii).
  specialize (cos2_sin2_1 Hon Hop Hic Hed θ1) as Hcs1.
  specialize (cos2_sin2_1 Hon Hop Hic Hed θ2) as Hcs2.
  apply (rngl_add_sub_eq_r Hos) in Hcs1, Hcs2.
  rewrite <- Hcs1, <- Hcs2 in Hc12.
  now apply (rngl_sub_lt_mono_l Hop Hor) in Hc12.
}
Qed.

Theorem rngl_sin_nonneg_cos_le_sin_sub_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L.
Proof.
intros Hic Hon Hop Hed * Hs1 Hs2 Hc12.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_sin_nonneg_cos_le_sin_le Hic Hon Hop Hed) as H1.
specialize (H1 _ _ Hs1 Hs2 Hc12).
remember (0 ≤? rngl_cos θ1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_leb_le in Hzc1; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite rngl_add_comm.
  rewrite (fold_rngl_sub Hop).
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_mul_comm Hic).
  now apply (rngl_mul_le_compat_nonneg Hop Hor).
}
apply (rngl_leb_gt Hor) in Hzc1.
remember (0 ≤? rngl_cos θ2)%L as zc2 eqn:Hzc2.
symmetry in Hzc2.
destruct zc2; [ easy | ].
apply (rngl_leb_gt Hor) in Hzc2; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite rngl_add_comm.
rewrite (fold_rngl_sub Hop).
apply (rngl_le_0_sub Hop Hor).
rewrite (rngl_mul_comm Hic).
(* a lemma, perhaps? *)
apply (rngl_opp_le_compat Hop Hor).
do 2 rewrite <- (rngl_mul_opp_r Hop).
apply (rngl_mul_le_compat_nonneg Hop Hor); [ easy | ].
split. {
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  now apply (rngl_lt_le_incl Hor).
} {
  now apply -> (rngl_opp_le_compat Hop Hor).
}
Qed.

Theorem angle_sub_opp_r :
  rngl_has_opp T = true →
  ∀ θ1 θ2, (θ1 - - θ2)%A = (θ1 + θ2)%A.
Proof.
intros Hop *.
apply eq_angle_eq; cbn.
now rewrite (rngl_opp_involutive Hop).
Qed.

Theorem angle_straight_add_straight :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  (angle_straight + angle_straight = 0)%A.
Proof.
intros Hon Hop.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply eq_angle_eq; cbn.
rewrite (rngl_mul_opp_opp Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
f_equal.
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_mul_0_l Hos).
apply rngl_add_0_l.
Qed.

Theorem angle_add_sub :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 + θ2 - θ2)%A = θ1.
Proof.
intros Hic Hon Hop Hed *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold angle_sub.
rewrite <- (angle_add_assoc Hop).
rewrite fold_angle_sub.
rewrite (angle_sub_diag Hic Hon Hop Hed).
apply (angle_add_0_r Hon Hos).
Qed.

Theorem angle_sub_add :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 - θ2 + θ2)%A = θ1.
Proof.
intros Hic Hon Hop Hed *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold angle_sub.
rewrite <- (angle_add_assoc Hop).
rewrite (angle_add_opp_l Hic Hon Hop Hed).
apply (angle_add_0_r Hon Hos).
Qed.

Theorem angle_add_move_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3, (θ1 + θ2)%A = θ3 ↔ θ2 = (θ3 - θ1)%A.
Proof.
intros Hic Hon Hop Hed *.
split; intros H2. {
  subst θ3; symmetry.
  rewrite (angle_add_comm Hic).
  apply (angle_add_sub Hic Hon Hop Hed).
} {
  subst θ2.
  rewrite (angle_add_comm Hic).
  apply (angle_sub_add Hic Hon Hop Hed).
}
Qed.

Theorem angle_add_move_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3, (θ1 + θ2)%A = θ3 ↔ θ1 = (θ3 - θ2)%A.
Proof.
intros Hic Hon Hop Hed *.
rewrite (angle_add_comm Hic).
apply (angle_add_move_l Hic Hon Hop Hed).
Qed.

Theorem angle_sub_move_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3, (θ1 - θ2)%A = θ3 ↔ θ1 = (θ3 + θ2)%A.
Proof.
intros Hic Hon Hop Hed *.
split; intros Ha. {
  subst θ3; symmetry.
  apply (angle_sub_add Hic Hon Hop Hed).
} {
  subst θ1.
  apply (angle_add_sub Hic Hon Hop Hed).
}
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_add_1_cos_add_add :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → ((1 + rngl_cos (θ1 - θ2)) * 2)%L =
      (√((1 + rngl_cos θ1) * (1 + rngl_cos θ2)) +
       √((1 - rngl_cos θ1) * (1 - rngl_cos θ2)))²%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2.
destruct ac as (Hiv, Hc2, Hor).
(* proof borrowed from rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub
   and it works: perhaps there is a way to unify these two theorems *)
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
assert (Ha12 : ∀ θ1 θ2, (0 ≤ (1 + rngl_cos θ1) * (1 + rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
}
assert (Hs12 : ∀ θ1 θ2, (0 ≤ (1 - rngl_cos θ1) * (1 - rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
}
rewrite (rngl_squ_add Hic Hon).
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_add_add_swap.
rewrite <- rngl_mul_assoc.
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (1 + rngl_cos θ1))%L.
rewrite <- rngl_mul_assoc.
do 2 rewrite <- (rngl_squ_sub_squ Hop Hic).
rewrite (rngl_squ_1 Hon).
replace (1 - (rngl_cos θ1)²)%L with (rngl_sin θ1)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed).
  apply rngl_cos2_sin2.
}
replace (1 - (rngl_cos θ2)²)%L with (rngl_sin θ2)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed).
  apply rngl_cos2_sin2.
}
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_square_ge_0 Hop Hor).
} {
  apply (rngl_square_ge_0 Hop Hor).
}
do 2 rewrite (rl_sqrt_squ Hop Hor).
rewrite (rngl_mul_add_distr_l (1 + rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_add_distr_r 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_sub_distr_l Hop (1 - rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop (1 + _ + _ + _ * _))%L.
rewrite (rngl_add_sub_assoc Hop _ 1 (rngl_cos θ1))%L.
rewrite (rngl_sub_sub_distr Hop _ (rngl_cos θ2)).
rewrite (rngl_add_add_swap (1 + _ + _))%L.
rewrite (rngl_add_add_swap _ (rngl_cos θ2) 1)%L.
rewrite (rngl_add_add_swap _ (rngl_cos θ1) 1)%L.
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ2)).
rewrite (rngl_add_sub Hos).
rewrite <- (rngl_add_assoc 2)%L.
rewrite (rngl_add_diag Hon (rngl_cos θ1 * _)%L).
rewrite <- (rngl_mul_1_r Hon 2)%L at 2.
rewrite <- rngl_mul_add_distr_l.
rewrite <- rngl_mul_add_distr_l.
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- rngl_add_assoc.
f_equal; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
f_equal.
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
easy.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → ((1 + rngl_cos (θ1 + θ2)) * 2)%L =
      (√((1 + rngl_cos θ1) * (1 + rngl_cos θ2)) -
       √((1 - rngl_cos θ1) * (1 - rngl_cos θ2)))²%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
assert (Ha12 : ∀ θ1 θ2, (0 ≤ (1 + rngl_cos θ1) * (1 + rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
}
assert (Hs12 : ∀ θ1 θ2, (0 ≤ (1 - rngl_cos θ1) * (1 - rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
}
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_mul_assoc.
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (1 + rngl_cos θ1))%L.
rewrite <- rngl_mul_assoc.
do 2 rewrite <- (rngl_squ_sub_squ Hop Hic).
rewrite (rngl_squ_1 Hon).
replace (1 - (rngl_cos θ1)²)%L with (rngl_sin θ1)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed).
  apply rngl_cos2_sin2.
}
replace (1 - (rngl_cos θ2)²)%L with (rngl_sin θ2)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed).
  apply rngl_cos2_sin2.
}
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_square_ge_0 Hop Hor).
} {
  apply (rngl_square_ge_0 Hop Hor).
}
do 2 rewrite (rl_sqrt_squ Hop Hor).
rewrite (rngl_mul_add_distr_l (1 + rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_add_distr_r 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_sub_distr_l Hop (1 - rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop (1 + _ + _ + _ * _))%L.
rewrite (rngl_add_sub_assoc Hop _ 1 (rngl_cos θ1))%L.
rewrite (rngl_sub_sub_distr Hop _ (rngl_cos θ2)).
rewrite rngl_add_add_swap.
rewrite (rngl_add_add_swap _ (rngl_cos θ2) 1)%L.
rewrite (rngl_add_add_swap _ (rngl_cos θ1) 1)%L.
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ2)).
rewrite (rngl_add_sub Hos).
rewrite <- rngl_add_assoc.
rewrite (rngl_add_diag Hon (rngl_cos θ1 * _)%L).
rewrite <- (rngl_mul_1_r Hon 2)%L at 2.
rewrite <- rngl_mul_add_distr_l.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- (rngl_add_sub_assoc Hop).
f_equal; cbn.
f_equal.
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
easy.
Qed.

(*
Theorem rngl_sin_nonneg_sin_neg_sin_add_neg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → √((1 + rngl_cos (θ1 - θ2)) / 2)%L =
       (√((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2) +
        √((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2))%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2.
...
*)

Theorem rngl_sin_nonneg_sin_neg_sin_add_neg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → √((1 + rngl_cos (θ1 + θ2)) / 2)%L =
     (√((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2) +
      √((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2))%L.
Proof.
(*
intros Hic Hon Hop Hed * Hzs1 Hzs2.
remember (- θ2)%A as θ eqn:Hθ.
symmetry in Hθ.
rewrite <- (angle_opp_involutive Hop) in Hθ.
apply (angle_opp_inj Hop) in Hθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite rngl_sin_opp in Hzs2.
rewrite <- (rngl_opp_0 Hop) in Hzs2.
apply (rngl_opp_lt_compat Hop Hor) in Hzs2.
rewrite fold_angle_sub.
rewrite rngl_cos_opp.
apply (rngl_lt_le_incl Hor) in Hzs2.
rewrite (rngl_add_comm (_ * _))%L.
(* possible new statement of this theorem, with all sin pos:
  Hzs1 : (0 ≤ rngl_sin θ1)%L
  Hzs2 : (0 ≤ rngl_sin θ2)%L
  ============================
  √((1 + rngl_cos (θ1 - θ2)) / 2)%L =
  (√((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2) +
   √((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2))%L
*)
...
*)
(*
intros Hic Hon Hop Hed * Hzs1 Hzs2.
remember (θ2 - angle_straight)%A as θ eqn:Hθ.
symmetry in Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs2.
rewrite <- (rngl_opp_0 Hop) in Hzs2.
apply (rngl_opp_lt_compat Hop Hor) in Hzs2.
rewrite (angle_add_assoc Hop).
do 2 rewrite (rngl_cos_add_straight_r Hon Hop).
do 2 rewrite (fold_rngl_sub Hop).
rewrite (rngl_sub_opp_r Hop).
(* possible new statement of this theorem, with all sin pos:
  θ1, θ2 : angle T
  Hzs1 : (0 ≤ rngl_sin θ1)%L
  Hzs2 : (0 < rngl_sin θ2)%L
  ============================
  √((1 - rngl_cos (θ1 + θ2)) / 2)%L =
  (√((1 - rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2) +
   √((1 + rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2))%L
*)
...
*)
intros Hic Hon Hop Hed * Hzs1 Hzs2.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hop Hc1 Hor) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
assert (Hz1ac :  ∀ θ, (0 ≤ 1 + rngl_cos θ)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H; [ | now apply (rngl_lt_le_incl Hor) ].
  now rewrite (rngl_squ_0 Hos) in H.
}
assert (Ha12 : ∀ θ1 θ2, (0 ≤ (1 + rngl_cos θ1) * (1 + rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
}
assert (Hs12 : ∀ θ1 θ2, (0 ≤ (1 - rngl_cos θ1) * (1 - rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hop Hor).
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
rewrite <- (rngl_div_add_distr_r Hiv).
apply (rngl_mul_cancel_r Hi1 _ _ 2)%L; [ easy | ].
rewrite (rngl_mul_div_r Hon Hiv); [ | easy ].
rewrite <- (rngl_abs_nonneg Hop Hor (√_ / _ * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  apply (rngl_div_pos Hon Hop Hiv Hor). 2: {
    apply (rngl_lt_iff Hor).
    split; [ now apply rl_sqrt_nonneg | ].
    now apply not_eq_sym.
  }
  now apply rl_sqrt_nonneg.
}
rewrite <- (rngl_abs_nonneg Hop Hor). 2: {
  now apply (rngl_add_nonneg_nonneg Hor); apply rl_sqrt_nonneg.
}
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hid).
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
progress unfold rngl_squ at 1.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_squ_opp Hop).
rewrite (rngl_add_comm √_)%L.
remember (- θ2)%A as θ eqn:Hθ.
symmetry in Hθ.
rewrite <- (angle_opp_involutive Hop) in Hθ.
apply (angle_opp_inj Hop) in Hθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite rngl_sin_opp in Hzs2.
rewrite <- (rngl_opp_0 Hop) in Hzs2.
apply (rngl_opp_lt_compat Hop Hor) in Hzs2.
rewrite fold_angle_sub.
rewrite rngl_cos_opp.
apply (rngl_lt_le_incl Hor) in Hzs2.
now apply rngl_sin_nonneg_sin_nonneg_add_1_cos_add_add.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_add_cos_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1 + rngl_cos θ2)%L
  → √((1 + rngl_cos (θ1 + θ2)) / 2)%L =
    (√((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2) -
     √((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2))%L.
Proof.
intros Hic Hon Hop Hed * Hzs1 Hzs2 Hzc12.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1.
  apply H1.
}
assert (Hz1ac :  ∀ θ, (0 ≤ 1 + rngl_cos θ)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Ha12 : ∀ θ1 θ2, (0 ≤ (1 + rngl_cos θ1) * (1 + rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
}
assert (Hs12 : ∀ θ1 θ2, (0 ≤ (1 - rngl_cos θ1) * (1 - rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
}
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hop Hc1 Hor) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H; [ | now apply (rngl_lt_le_incl Hor) ].
  now rewrite (rngl_squ_0 Hos) in H.
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hop Hor).
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
apply (rngl_mul_cancel_r Hi1 _ _ 2)%L; [ easy | ].
rewrite (rngl_mul_div_r Hon Hiv); [ | easy ].
rewrite <- (rngl_abs_nonneg Hop Hor (√_ / _ * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  apply (rngl_div_pos Hon Hop Hiv Hor). 2: {
    apply (rngl_lt_iff Hor).
    split; [ now apply rl_sqrt_nonneg | ].
    now apply not_eq_sym.
  }
  now apply rl_sqrt_nonneg.
}
rewrite <- (rngl_abs_nonneg Hop Hor). 2: {
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_add_cos_nonneg_sqrt_mul_le Hic Hon Hop Hed Hii).
}
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hid).
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
progress unfold rngl_squ at 1.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_squ_opp Hop).
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_mul_assoc.
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (1 + rngl_cos θ1))%L.
rewrite <- rngl_mul_assoc.
do 2 rewrite <- (rngl_squ_sub_squ Hop Hic).
rewrite (rngl_squ_1 Hon).
replace (1 - (rngl_cos θ1)²)%L with (rngl_sin θ1)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed).
  apply rngl_cos2_sin2.
}
replace (1 - (rngl_cos θ2)²)%L with (rngl_sin θ2)²%L. 2: {
  symmetry.
  apply (rngl_add_sub_eq_l Hos).
  apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed).
  apply rngl_cos2_sin2.
}
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_square_ge_0 Hop Hor).
} {
  apply (rngl_square_ge_0 Hop Hor).
}
do 2 rewrite (rl_sqrt_squ Hop Hor).
rewrite (rngl_mul_add_distr_l (1 + rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_add_distr_r 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_sub_distr_l Hop (1 - rngl_cos θ1))%L.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop 1 (rngl_cos θ1))%L.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop (1 + _ + _ + _ * _))%L.
rewrite (rngl_add_sub_assoc Hop _ 1 (rngl_cos θ1))%L.
rewrite (rngl_sub_sub_distr Hop _ (rngl_cos θ2)).
rewrite (rngl_add_add_swap (1 + _ + _))%L.
rewrite (rngl_add_add_swap _ (rngl_cos θ2) 1)%L.
rewrite (rngl_add_add_swap _ (rngl_cos θ1) 1)%L.
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ1)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop _ _ (rngl_cos θ2)).
rewrite (rngl_add_sub Hos).
rewrite <- (rngl_add_assoc 2)%L.
rewrite (rngl_add_diag Hon (rngl_cos θ1 * _)%L).
rewrite <- (rngl_mul_1_r Hon 2)%L at 2.
rewrite <- rngl_mul_add_distr_l.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_comm Hic).
f_equal.
rewrite <- (rngl_add_sub_assoc Hop).
f_equal; cbn.
progress unfold rngl_sub.
rewrite Hop.
f_equal.
f_equal.
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
easy.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_sin_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (θ1 ≤ θ1 + θ2)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → √((1 + rngl_cos (θ1 + θ2)) / 2)%L =
      (√((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2) -
       √((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2))%L.
Proof.
(* same goal but different hypotheses in the theorem
   rngl_sin_nonneg_sin_nonneg_add_cos_nonneg defined above;
   perhaps there is something to do? *)
(*
intros Hic Hon Hop Hed * Haov Hzs1 Hzs2 Hzs3.
apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy.
...
*)
intros Hic Hon Hop Hed * Haov Hzs1 Hzs2 Hzs3.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1.
  apply H1.
}
assert (Hz1ac :  ∀ θ, (0 ≤ 1 + rngl_cos θ)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Ha12 : ∀ θ1 θ2, (0 ≤ (1 + rngl_cos θ1) * (1 + rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_le_sub_le_add_l Hop Hor).
    progress unfold rngl_sub.
    rewrite Hop, rngl_add_0_l.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
}
assert (Hs12 : ∀ θ1 θ2, (0 ≤ (1 - rngl_cos θ1) * (1 - rngl_cos θ2))%L). {
  intros.
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_add_0_r.
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
}
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hop Hc1 Hor) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H; [ | now apply (rngl_lt_le_incl Hor) ].
  now rewrite (rngl_squ_0 Hos) in H.
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hop Hor).
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
apply (rngl_mul_cancel_r Hi1 _ _ 2)%L; [ easy | ].
rewrite (rngl_mul_div_r Hon Hiv); [ | easy ].
rewrite <- (rngl_abs_nonneg Hop Hor (√_ / _ * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  apply (rngl_div_pos Hon Hop Hiv Hor). 2: {
    apply (rngl_lt_iff Hor).
    split; [ now apply rl_sqrt_nonneg | ].
    now apply not_eq_sym.
  }
  now apply rl_sqrt_nonneg.
}
remember (√(_ * _))%L as x eqn:Hx.
remember (√(_ * _))%L as y eqn:Hy in |-*.
destruct (rngl_lt_dec Hor x y) as [Hxy| Hxy]. {
  exfalso.
  apply (rngl_nle_gt Hor) in Hxy.
  apply Hxy; clear Hxy.
  subst x y.
  apply (rngl_add_cos_nonneg_sqrt_mul_le Hic Hon Hop Hed Hii).
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
    now apply rngl_add_cos_nonneg_when_sin_nonneg.
  }
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
    rewrite (angle_add_comm Hic) in Hzs3.
    rewrite rngl_add_comm.
    now apply rngl_add_cos_nonneg_when_sin_nonneg.
  }
  apply (rngl_nle_gt Hor) in Hzc1, Hzc2.
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs3.
  apply Hzs3; clear Hzs3.
  cbn.
  (* special case for sin θ2 = 0 *)
  destruct (rngl_eq_dec Hed (rngl_sin θ2) 0) as [H2z| H2z]. {
    rewrite H2z, (rngl_mul_0_r Hos), rngl_add_0_l.
    destruct (rngl_eq_dec Hed (rngl_sin θ1) 0) as [H1z| H1z]. {
      apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H2z, H1z.
      destruct H2z as [H2z| H2z]. {
        subst θ2.
        apply (rngl_nle_gt Hor) in Hzc2.
        exfalso; apply Hzc2; clear Hzc2; cbn.
        apply (rngl_0_le_1 Hon Hop Hor).
      }
      subst θ2.
      clear Hzs2 Hzc2.
      exfalso.
      destruct H1z as [H1z| H1z]. {
        subst θ1.
        apply (rngl_nle_gt Hor) in Hzc1.
        apply Hzc1; clear Hzc1; cbn.
        apply (rngl_0_le_1 Hon Hop Hor).
      } {
        subst θ1.
        clear Hzc1 Hzs1.
        progress unfold angle_leb in Haov.
        cbn in Haov.
        rewrite (rngl_leb_refl Hor) in Haov.
        cbn in Haov.
        rewrite (rngl_mul_0_r Hos) in Haov.
        rewrite rngl_add_0_l in Haov.
        do 2 rewrite (rngl_mul_0_l Hos) in Haov.
        rewrite (rngl_leb_refl Hor) in Haov.
        apply rngl_leb_le in Haov.
        apply (rngl_nlt_ge Hor) in Haov.
        apply Haov; clear Haov.
        rewrite (rngl_squ_opp_1 Hon Hop).
        rewrite (rngl_sub_0_r Hos).
        apply (rngl_add_lt_mono_l Hop Hor _ _ 1)%L.
        rewrite (fold_rngl_sub Hop).
        now rewrite (rngl_sub_diag Hos).
      }
    }
    apply (rngl_mul_pos_neg Hop Hor Hid); [ | easy ].
    apply (rngl_lt_iff Hor).
    split; [ easy | ].
    now apply not_eq_sym.
  }
  apply (rngl_add_neg_nonpos Hop Hor). {
    rewrite (rngl_mul_comm Hic).
    apply (rngl_mul_pos_neg Hop Hor Hid); [ | easy ].
    apply (rngl_lt_iff Hor).
    split; [ easy | ].
    now apply not_eq_sym.
  }
  apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nlt_ge Hor) in Hxy.
rewrite <- (rngl_abs_nonneg Hop Hor). 2: {
  now apply (rngl_le_0_sub Hop Hor).
}
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hid).
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
progress unfold rngl_squ at 1.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
subst x y.
now apply rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub.
Qed.

Theorem rngl_sin_nonneg_sin_nonneg_sin_neg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (θ1 ≤ θ1 + θ2)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → √((1 + rngl_cos (θ1 + θ2)) / 2)%L =
       (√((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2) -
        √((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2))%L.
Proof.
intros Hic Hon Hop Hed * Haov Hzs1 Hzs2 Hzs3.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hop Hc1 Hor) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
assert (Hz1ac :  ∀ θ, (0 ≤ 1 + rngl_cos θ)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H; [ | now apply (rngl_lt_le_incl Hor) ].
  now rewrite (rngl_squ_0 Hos) in H.
}
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hop Hor).
rewrite (rngl_abs_nonneg Hop Hor); [ | easy ].
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
apply (rngl_mul_cancel_r Hi1 _ _ 2)%L; [ easy | ].
rewrite (rngl_mul_div_r Hon Hiv); [ | easy ].
rewrite <- (rngl_abs_nonneg Hop Hor (√_ / _ * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  apply (rngl_div_pos Hon Hop Hiv Hor). 2: {
    apply (rngl_lt_iff Hor).
    split; [ now apply rl_sqrt_nonneg | ].
    now apply not_eq_sym.
  }
  now apply rl_sqrt_nonneg.
}
remember (√(_ * _))%L as x eqn:Hx.
remember (√(_ * _))%L as y eqn:Hy in |-*.
destruct (rngl_lt_dec Hor x y) as [Hxy| Hxy]. {
  exfalso.
  apply (rngl_nle_gt Hor) in Hxy.
  apply Hxy; clear Hxy.
  subst x y.
  progress unfold rngl_sub.
  rewrite Hop.
  do 2 rewrite <- (rngl_sub_opp_r Hop).
  do 2 rewrite <- (rngl_cos_add_straight_r Hon Hop).
  apply (rngl_add_cos_nonneg_sqrt_mul_le Hic Hon Hop Hed Hii). {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      do 2 rewrite (rngl_cos_add_straight_r Hon Hop).
      rewrite (fold_rngl_sub Hop).
      rewrite <- (rngl_opp_add_distr Hop).
      apply (rngl_opp_nonneg_nonpos Hop Hor).
      rewrite Hθ3 in Hzs3.
      rewrite rngl_add_comm.
      apply (rngl_lt_le_incl Hor).
      now apply rngl_add_cos_neg_when_sin_nonneg_neg.
    }
    apply (rngl_nle_gt Hor) in Hzc1.
    (* case rngl_cos θ1 ≤ 0 *)
    apply rngl_add_cos_nonneg_when_sin_nonpos; try easy. {
      rewrite (rngl_sin_add_straight_r Hon Hop).
      now apply (rngl_opp_nonpos_nonneg Hop Hor).
    } {
      rewrite (rngl_sin_add_straight_r Hon Hop).
      now apply (rngl_opp_nonpos_nonneg Hop Hor).
    } {
      rewrite (angle_add_assoc Hop).
      rewrite (angle_add_comm Hic θ1).
      rewrite (angle_add_comm Hic).
      do 2 rewrite (angle_add_assoc Hop).
      rewrite (angle_straight_add_straight Hon Hop).
      rewrite (angle_add_0_l Hon Hos).
      rewrite Hθ3 in Hzs3.
      now apply (rngl_lt_le_incl Hor).
    }
    rewrite (rngl_cos_add_straight_r Hon Hop).
    apply (rngl_opp_nonneg_nonpos Hop Hor).
    now apply (rngl_lt_le_incl Hor).
  }
}
apply (rngl_nlt_ge Hor) in Hxy.
rewrite <- (rngl_abs_nonneg Hop Hor). 2: {
  now apply (rngl_le_0_sub Hop Hor).
}
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hid).
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
progress unfold rngl_squ at 1.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
subst x y.
subst θ3.
rewrite <- (rngl_squ_opp Hop).
rewrite (rngl_opp_sub_distr Hop).
now apply rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub.
Qed.

Theorem angle_add_add_swap :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2 θ3, (θ1 + θ2 + θ3)%A = (θ1 + θ3 + θ2)%A.
Proof.
intros Hic Hop *.
do 2 rewrite <- (angle_add_assoc Hop).
f_equal.
apply (angle_add_comm Hic).
Qed.

Theorem rngl_cos_add_right :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ, rngl_cos (θ + angle_right) = (- rngl_sin θ)%L.
Proof.
intros Hon Hop *; cbn.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_0_r Hos).
apply (rngl_sub_0_l Hop).
Qed.

Theorem rngl_sin_add_right :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ, rngl_sin (θ + angle_right) = rngl_cos θ.
Proof.
intros Hon Hos *; cbn.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_0_r Hos).
apply rngl_add_0_r.
Qed.

Theorem rngl_cos_sub_right_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ, rngl_cos (angle_right - θ) = rngl_sin θ.
Proof.
intros Hon Hop *; cbn.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_opp_r Hop).
apply rngl_add_0_l.
Qed.

Theorem rngl_sin_sub_right_l :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ, rngl_sin (angle_right - θ) = rngl_cos θ.
Proof.
intros Hon Hos *; cbn.
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_l.
apply (rngl_mul_1_l Hon).
Qed.

Theorem angle_add_sub_assoc :
  rngl_has_opp T = true →
  ∀ θ1 θ2 θ3, (θ1 + (θ2 - θ3))%A = (θ1 + θ2 - θ3)%A.
Proof.
intros Hop *.
progress unfold angle_sub.
apply (angle_add_assoc Hop).
Qed.

Theorem rngl_cos_sub_comm :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2, rngl_cos (θ1 - θ2) = rngl_cos (θ2 - θ1).
Proof.
intros Hic Hop *; cbn.
rewrite (rngl_mul_comm Hic).
f_equal.
do 2 rewrite (rngl_mul_opp_r Hop).
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_sin_sub_anticomm :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2, rngl_sin (θ1 - θ2) = (- rngl_sin (θ2 - θ1))%L.
Proof.
intros Hic Hop *; cbn.
do 2 rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_mul_comm Hic).
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem angle_sub_sub_distr :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2 θ3, (θ1 - (θ2 - θ3))%A = (θ1 - θ2 + θ3)%A.
Proof.
intros Hic Hop *.
progress unfold angle_sub.
rewrite <- (angle_add_assoc Hop).
f_equal.
rewrite (angle_opp_add_distr Hic Hop).
rewrite (angle_opp_involutive Hop).
apply (angle_add_comm Hic).
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

Theorem angle_nlt_ge :
  ∀ θ1 θ2, ¬ (θ1 < θ2)%A ↔ (θ2 ≤ θ1)%A.
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
    apply (rngl_ltb_ge Hor) in H12.
    now apply rngl_leb_le.
  } {
    apply Bool.not_true_iff_false.
    apply (rngl_ltb_ge Hor).
    now apply rngl_leb_le.
  }
} {
  destruct z2; [ easy | ].
  split; intros H12. {
    apply Bool.not_true_iff_false in H12.
    apply (rngl_ltb_ge Hor) in H12.
    now apply rngl_leb_le.
  } {
    apply Bool.not_true_iff_false.
    apply (rngl_ltb_ge Hor).
    now apply rngl_leb_le.
  }
}
Qed.

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

Theorem angle_sub_add_distr :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2 θ3, (θ1 - (θ2 + θ3))%A = (θ1 - θ2 - θ3)%A.
Proof.
intros Hic Hop *.
progress unfold angle_sub.
rewrite (angle_opp_add_distr Hic Hop).
progress unfold angle_sub.
rewrite (angle_add_assoc Hop).
apply (angle_add_add_swap Hic Hop).
Qed.

Theorem eq_rngl_cos_1 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, rngl_cos θ = 1%L ↔ θ = 0%A.
Proof.
intros Hic Hon Hop Hed *.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
split; intros Hθ; [ | now subst θ ].
specialize (cos2_sin2_1 Hon Hop Hic Hed θ) as H1.
rewrite Hθ in H1.
rewrite (rngl_squ_1 Hon) in H1.
apply (rngl_add_move_l Hop) in H1.
rewrite (rngl_sub_diag Hos) in H1.
apply (eq_rngl_squ_0 Hos Hid) in H1.
apply eq_angle_eq.
now rewrite Hθ, H1.
Qed.

Theorem rngl_sin_nonneg_add_nonneg_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (θ1 ≤ θ1 + θ2)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin θ2)%L.
Proof.
intros Hic Hon Hop Hed * Haov Hzs1 Hzs3.
destruct ac as (Hiv, Hc2, Hor).
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
apply (rngl_nlt_ge Hor).
intros Hzs2.
progress unfold angle_leb in Haov.
cbn in Haov.
apply (rngl_leb_le) in Hzs1.
rewrite Hzs1 in Haov.
apply (rngl_leb_le) in Hzs1.
apply (rngl_leb_le) in Hzs3.
rewrite Hzs3 in Haov.
apply (rngl_leb_le) in Hzs3.
apply rngl_leb_le in Haov.
apply (rngl_nlt_ge Hor) in Haov.
apply Haov; clear Haov.
apply (rngl_nle_gt Hor).
intros Hc31.
apply (rngl_nle_gt Hor) in Hzs2.
apply Hzs2; clear Hzs2.
symmetry in Hθ3.
apply (angle_add_sub_eq_l Hic Hon Hop Hed) in Hθ3.
subst θ2.
now apply (rngl_sin_nonneg_cos_le_sin_sub_nonneg Hic Hon Hop Hed).
Qed.

Theorem rngl_cos_angle_div_2_add_not_overflow' :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → rngl_cos (angle_div_2 (θ1 + θ2)) =
     rngl_cos (angle_div_2 θ1 + angle_div_2 θ2).
Proof.
intros Hic Hon Hop Hed * Haov.
destruct ac as (Hiv, Hc2, Hor).
progress unfold angle_add_overflow in Haov.
apply angle_ltb_ge in Haov.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hop Hc1 Hor) as H20.
assert (Hze2 : (0 ≤ 2)%L) by now apply (rngl_lt_le_incl Hor).
assert (Hz1ac :  ∀ θ, (0 ≤ 1 + rngl_cos θ)%L). {
  intros.
  apply (rngl_le_sub_le_add_l Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Hz1sc : ∀ θ, (0 ≤ 1 - rngl_cos θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
assert (Hs2z : (√2 ≠ 0)%L). {
  intros H.
  apply (f_equal rngl_squ) in H.
  rewrite rngl_squ_sqrt in H; [ | now apply (rngl_lt_le_incl Hor) ].
  now rewrite (rngl_squ_0 Hos) in H.
}
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
cbn.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
destruct zs3. {
  apply rngl_leb_le in Hzs3.
  rewrite (rngl_mul_1_l Hon).
  destruct zs1. {
    apply rngl_leb_le in Hzs1.
    rewrite (rngl_mul_1_l Hon).
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      rewrite (rngl_mul_1_l Hon).
      subst θ3.
      now apply rngl_sin_nonneg_sin_nonneg_sin_nonneg.
    }
    exfalso.
    apply (rngl_leb_gt Hor) in Hzs2.
    apply (rngl_nle_gt Hor) in Hzs2.
    apply Hzs2; clear Hzs2.
    subst θ3.
    now apply (rngl_sin_nonneg_add_nonneg_nonneg Hic Hon Hop Hed θ1 θ2).
  } {
    apply (rngl_leb_gt Hor) in Hzs1.
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      exfalso.
      progress unfold angle_leb in Haov.
      apply (rngl_leb_gt Hor) in Hzs1.
      rewrite Hzs1 in Haov.
      apply (rngl_leb_le) in Hzs3.
      now rewrite Hzs3 in Haov.
    }
    apply (rngl_leb_gt Hor) in Hzs2.
    apply (angle_le_rngl_sin_nonneg_sin_nonneg _ _ Haov) in Hzs3.
    now apply (rngl_nlt_ge Hor) in Hzs3.
  }
}
apply (rngl_leb_gt Hor) in Hzs3.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
apply (rngl_opp_inj Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_opp_sub_distr Hop).
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  rewrite (rngl_mul_1_l Hon).
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    rewrite (rngl_mul_1_l Hon).
    subst θ3.
    now apply rngl_sin_nonneg_sin_nonneg_sin_neg.
  } {
    apply (rngl_leb_gt Hor) in Hzs2.
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_mul_1_l Hon).
    subst θ3.
    now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
  }
}
(*to be cleaned from here*)
apply (rngl_leb_gt Hor) in Hzs1.
destruct zs2. {
  apply rngl_leb_le in Hzs2.
  do 2 rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_sub_opp_r Hop).
  do 2 rewrite (rngl_mul_1_l Hon).
  rewrite (angle_add_comm Hic) in Hθ3.
  subst θ3.
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_comm Hic √((1 + rngl_cos θ1) / _))%L.
  now apply rngl_sin_nonneg_sin_neg_sin_add_neg.
}
apply (rngl_leb_gt Hor) in Hzs2.
progress unfold angle_leb in Haov.
apply (rngl_leb_gt Hor) in Hzs1.
rewrite Hzs1 in Haov.
apply (rngl_leb_gt Hor) in Hzs3.
rewrite Hzs3 in Haov.
apply rngl_leb_le in Haov.
apply (rngl_leb_gt Hor) in Hzs1, Hzs3.
rename Haov into Hc13.
move Hc13 at bottom.
subst θ3.
apply (rngl_opp_lt_compat Hop Hor) in Hzs1, Hzs2, Hzs3.
apply (rngl_opp_le_compat Hop Hor) in Hc13.
rewrite (rngl_opp_0 Hop) in Hzs1, Hzs2, Hzs3.
rewrite <- (rngl_sin_add_straight_r Hon Hop) in Hzs1, Hzs2, Hzs3.
do 2 rewrite <- (rngl_cos_add_straight_r Hon Hop) in Hc13.
rewrite (angle_add_add_swap Hic Hop) in Hzs3, Hc13.
apply (rngl_opp_lt_compat Hop Hor) in Hzs3.
apply (rngl_opp_le_compat Hop Hor) in Hc13.
rewrite (rngl_opp_0 Hop) in Hzs3.
rewrite <- (rngl_sin_add_straight_r Hon Hop) in Hzs3.
rewrite <- (rngl_cos_add_straight_r Hon Hop (_ + θ2)%A) in Hc13.
rewrite <- (angle_add_assoc Hop) in Hzs3, Hc13.
rewrite <- (rngl_sub_opp_r Hop).
rewrite <- (rngl_cos_add_straight_r Hon Hop).
rewrite (angle_add_add_swap Hic Hop).
progress unfold rngl_sub at 1.
rewrite Hop.
rewrite <- (rngl_cos_add_straight_r Hon Hop).
rewrite <- (angle_add_assoc Hop).
progress unfold rngl_sub at 2.
rewrite Hop.
rewrite <- (rngl_cos_add_straight_r Hon Hop).
progress unfold rngl_sub at 2.
rewrite Hop.
rewrite <- (rngl_cos_add_straight_r Hon Hop).
rewrite <- (rngl_sub_opp_r Hop 1 (rngl_cos θ1))%L.
rewrite <- (rngl_cos_add_straight_r Hon Hop).
rewrite <- (rngl_sub_opp_r Hop 1 (rngl_cos θ2))%L.
rewrite <- (rngl_cos_add_straight_r Hon Hop).
remember (θ1 + angle_straight)%A as θ.
clear θ1 Heqθ.
rename θ into θ1.
remember (θ2 + angle_straight)%A as θ.
clear θ2 Heqθ.
rename θ into θ2.
move θ2 before θ1.
rewrite <- (rngl_sub_0_l Hop) in Hc13.
apply (rngl_le_sub_le_add_l Hop Hor) in Hc13.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
  apply (rngl_nlt_ge Hor) in Hc13.
  exfalso.
  apply Hc13; clear Hc13; cbn.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite <- (rngl_mul_1_r Hon (rngl_cos θ1)) at 1.
  rewrite <- rngl_mul_add_distr_l.
  progress unfold rngl_sub.
  rewrite Hop.
  apply (rngl_add_nonpos_neg Hop Hor). {
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ easy | ].
    apply (rngl_le_sub_le_add_l Hop Hor).
    rewrite (rngl_sub_0_l Hop).
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  } {
    rewrite <- (rngl_opp_0 Hop).
    apply -> (rngl_opp_lt_compat Hop Hor).
    now apply (rngl_mul_pos_pos Hop Hor Hii).
  }
}
apply (rngl_nle_gt Hor) in Hzc1.
move Hzc1 before Hzs2.
destruct (rngl_le_dec Hor 0 (rngl_cos (θ1 + θ2))) as [Hzc3| Hc3z]. {
  apply (rngl_nlt_ge Hor) in Hzc3.
  exfalso.
  apply Hzc3; clear Hzc3.
  destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    cbn.
    progress unfold rngl_sub.
    rewrite Hop.
    apply (rngl_add_nonpos_neg Hop Hor). {
      apply (rngl_mul_nonneg_nonpos Hop Hor); [ | easy ].
      now apply (rngl_lt_le_incl Hor).
    } {
      rewrite <- (rngl_opp_0 Hop).
      apply -> (rngl_opp_lt_compat Hop Hor).
      now apply (rngl_mul_pos_pos Hop Hor Hii).
    }
  }
  apply (rngl_nle_gt Hor) in Hzc2.
  move Hzc2 before Hzc1.
  apply (rngl_nle_gt Hor) in Hzs3.
  exfalso; apply Hzs3; clear Hzs3; cbn.
  apply (rngl_add_nonneg_nonneg Hor). {
    apply (rngl_mul_nonneg_nonneg Hop Hor);
      now apply (rngl_lt_le_incl Hor).
  } {
    apply (rngl_mul_nonneg_nonneg Hop Hor);
      now apply (rngl_lt_le_incl Hor).
  }
}
apply (rngl_nle_gt Hor) in Hc3z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2z| Hc2z]. {
  apply (rngl_nle_gt Hor) in Hzs3.
  exfalso.
  apply Hzs3; clear Hzs3; cbn.
  apply (rngl_add_nonneg_nonneg Hor). {
    apply (rngl_mul_nonneg_nonneg Hop Hor);
      now apply (rngl_lt_le_incl Hor).
  } {
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
  }
}
apply (rngl_nle_gt Hor) in Hc2z.
move Hc2z before Hzc1.
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (-1))%L.
rewrite (rngl_squ_opp_1 Hon Hop).
rewrite (rngl_mul_1_l Hon).
destruct (rngl_le_dec Hor 0 (rngl_cos θ1 + rngl_cos θ2))%L
  as [Hzc12| Hc12z]. {
  apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc12z.
exfalso.
remember (θ2 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (angle_add_assoc Hop) in Hzs3, Hc3z, Hc13.
rewrite (rngl_sin_add_right Hon Hos) in Hzs2, Hzs3.
rewrite (rngl_cos_add_right Hon Hop) in Hc12z, Hc3z, Hc13, Hc2z.
rewrite (fold_rngl_sub Hop) in Hc12z, Hc13.
rewrite <- (rngl_opp_0 Hop) in Hc2z, Hc3z.
apply (rngl_opp_lt_compat Hop Hor) in Hc2z, Hc3z.
move Hc2z before Hzs1.
move Hzc1 after Hzs2.
apply (rngl_lt_sub_lt_add_l Hop Hor) in Hc12z.
apply (rngl_le_add_le_sub_l Hop Hor) in Hc13.
rewrite rngl_add_0_r in Hc12z, Hc13.
remember (angle_right - θ2)%A as θ.
apply (angle_add_move_l Hic Hon Hop Hed) in Heqθ.
rewrite (angle_add_comm Hic) in Heqθ.
apply (angle_add_move_l Hic Hon Hop Hed) in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (rngl_sin_sub_right_l Hon Hos) in Hc2z.
rewrite (angle_add_comm Hic) in Hc13.
rewrite <- (angle_sub_sub_distr Hic Hop) in Hc13.
rewrite (rngl_sin_sub_right_l Hon Hos) in Hc13.
rewrite (angle_add_comm Hic) in Hzs3.
rewrite <- (angle_sub_sub_distr Hic Hop) in Hzs3.
rewrite (rngl_cos_sub_right_l Hon Hop) in Hzs3.
rewrite (angle_add_comm Hic) in Hc3z.
rewrite <- (angle_sub_sub_distr Hic Hop) in Hc3z.
rewrite (rngl_sin_sub_right_l Hon Hos) in Hc3z.
rewrite (rngl_sin_sub_right_l Hon Hos) in Hc12z.
rewrite (rngl_cos_sub_right_l Hon Hop) in Hzs2.
move  Hzs2 before Hzs1.
move Hzc1 after Hc2z.
move Hzs3 before Hc2z.
move Hc3z before Hzs3.
move Hc12z after Hc13.
rewrite (rngl_cos_sub_comm Hic Hop) in Hc3z, Hc13.
rewrite (rngl_sin_sub_anticomm Hic Hop) in Hzs3.
rewrite <- (rngl_opp_0 Hop) in Hzs3.
apply (rngl_opp_lt_compat Hop Hor) in Hzs3.
assert (Hss : (rngl_sin θ2 < rngl_sin θ1)%L). {
  specialize (rngl_sin_nonneg_cos_lt_sin_lt) as H1.
  specialize (H1 Hic Hon Hop Hed).
  specialize (H1 _ _ Hzs1 Hzs2 Hc12z).
  apply rngl_ltb_lt in Hzc1.
  now rewrite Hzc1 in H1.
}
move Hss after Hc12z.
rename Hc12z into Hcc.
apply (rngl_nlt_ge Hor) in Hc13.
apply Hc13; clear Hc13.
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
apply (rngl_lt_sub_lt_add_l Hop Hor).
rewrite <- (rngl_mul_1_r Hon (rngl_cos θ1))%L at 1.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_abs_nonneg Hop Hor). 2: {
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
rewrite <- (rngl_abs_nonneg Hop Hor (rngl_cos θ1 * _))%L. 2: {
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
apply (rngl_squ_lt_abs_lt Hop Hor Hii).
rewrite (rngl_squ_mul Hic (rngl_sin _)).
specialize (cos2_sin2_1 Hon Hop Hic Hed θ1) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
specialize (cos2_sin2_1 Hon Hop Hic Hed θ2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_squ_mul Hic).
apply (rngl_lt_add_lt_sub_l Hop Hor).
rewrite <- rngl_mul_add_distr_l.
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop).
rewrite <- (rngl_add_sub_swap Hop 1)%L.
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_add Hop).
rewrite <- (rngl_mul_1_r Hon 2)%L at 1.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite rngl_mul_assoc.
rewrite (rngl_mul_comm Hic _ 2)%L.
rewrite <- (rngl_squ_1 Hon) at 4.
rewrite (rngl_squ_sub_squ Hop Hic).
apply (rngl_mul_lt_mono_pos_r Hop Hor Hii). {
  apply (rngl_lt_0_sub Hop Hor).
  apply (rngl_lt_iff Hor).
  split; [ now apply rngl_cos_bound | ].
  intros H.
  apply (eq_rngl_cos_1 Hic Hon Hop Hed) in H.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
apply (rngl_lt_le_trans Hor _ (2 * (rngl_cos θ2)²))%L. {
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid).
  rewrite (rngl_abs_nonneg Hop Hor); [ | now apply rngl_lt_le_incl ].
  rewrite (rngl_abs_nonneg Hop Hor); [ | now apply rngl_lt_le_incl ].
  easy.
}
apply (rngl_le_trans Hor _ (2 * rngl_cos θ2))%L. {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
  rewrite <- (rngl_mul_1_l Hon (rngl_cos θ2)) at 2.
  progress unfold rngl_squ.
  apply (rngl_mul_le_mono_nonneg_r Hop Hor). {
    now apply (rngl_lt_le_incl Hor).
  }
  now apply (rngl_cos_bound).
}
rewrite <- (rngl_add_diag Hon).
apply (rngl_add_le_mono_r Hop Hor).
now apply rngl_cos_bound.
Qed.

(* to be completed
Theorem angle_div_2_add :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_div_2 (θ1 + θ2) =
    if angle_add_overflow θ1 θ2 then
      (angle_div_2 θ1 + angle_div_2 θ2 + angle_straight)%A
    else
      (angle_div_2 θ1 + angle_div_2 θ2)%A.
Proof.
intros Hic Hon Hop Hed *.
remember (angle_add_overflow θ1 θ2) as aov eqn:Haov.
symmetry in Haov.
destruct aov. 2: {
  apply eq_angle_eq.
  f_equal. {
(* c'est bizarre qu'il accepte que j'applique indifféremment
   rngl_cos_angle_div_2_add_not_overflow de TrigoWithoutPi.v ou celui
   ce Complex.v alors qu'il s'agit de deux définitions de angle_div_2
*)
    now apply (rngl_cos_angle_div_2_add_not_overflow Hic Hon Hop Hed).
...
    now apply (rngl_cos_angle_div_2_add_not_overflow' Hic Hon Hop Hed).
(*
Check rngl_cos_angle_div_2_add_not_overflow.
Check rngl_cos_angle_div_2_add_not_overflow'.
rngl_cos_angle_div_2_add_not_overflow
     : rngl_mul_is_comm T = true
       → rngl_has_1 T = true
         → rngl_has_opp T = true
           → rngl_has_eq_dec T = true
             → ∀ θ1 θ2 : angle T,
                 TrigoWithoutPi.angle_add_overflow θ1 θ2 = false
                 → rngl_cos (TrigoWithoutPi.angle_div_2 (θ1 + θ2)%A) =
                   rngl_cos (TrigoWithoutPi.angle_div_2 θ1 + TrigoWithoutPi.angle_div_2 θ2)
rngl_cos_angle_div_2_add_not_overflow'
     : rngl_mul_is_comm T = true
       → rngl_has_1 T = true
         → rngl_has_opp T = true
           → rngl_has_eq_dec T = true
             → ∀ θ1 θ2 : angle T,
                 angle_add_overflow θ1 θ2 = false
                 → rngl_cos (angle_div_2 (θ1 + θ2)) = rngl_cos (angle_div_2 θ1 + angle_div_2 θ2)
*)
  }
About angle_div_2.
About TrigoWithoutPi.angle_div_2.
...

Theorem angle_div_2_pow_nat_add :
  ∀ n θ1 θ2,
  angle_div_2_pow_nat (θ1 + θ2) n =
  (angle_div_2_pow_nat θ1 n + angle_div_2_pow_nat θ2 n)%A.
Proof.
intros.
induction n; [ easy | cbn ].
rewrite IHn.
... ...
apply angle_div_2_add.
...

Theorem angle_div_2_pow_nat_pow_nat_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ n θ, angle_div_2_pow_nat (2 ^ n * θ) n = θ.
Proof.
intros Hon Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
revert θ.
induction n; intros; cbn. {
  apply (angle_add_0_r Hon Hos).
}
rewrite Nat.add_0_r.
rewrite (angle_mul_add_distr_r Hon Hop).
... ...
rewrite angle_div_2_pow_nat_add.
rewrite IHn.
...

Theorem angle_div_nat_is_inf_sum_of_angle_div_2_pow_nat :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_archimedean T = true →
  rngl_has_eq_dec T = true →
  ∀ n θ θ',
  rngl_of_nat n ≠ 0%L
  → is_angle_upper_limit_when_tending_to_inf
       (seq_angle_converging_to_angle_div_nat θ n) θ'
  → θ = (n * θ')%A.
Proof.
intros Hic Hon Hop Har Hed * Hnz Hlim.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply eq_angle_eq.
induction n; [ easy | ].
clear Hnz.
destruct n. {
  clear IHn; cbn.
  do 2 rewrite (rngl_mul_1_r Hon).
  do 2 rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_sub_0_r Hos).
  rewrite rngl_add_0_l.
  progress unfold seq_angle_converging_to_angle_div_nat in Hlim.
  assert
    (H : is_angle_upper_limit_when_tending_to_inf
           (λ i, angle_div_2_pow_nat (2 ^ i * θ) i) θ'). {
    intros ε Hε.
    specialize (Hlim ε Hε).
    destruct Hlim as (N, HN).
    exists N. (* au pif *)
    intros n Hn.
    specialize (HN n Hn).
    rewrite Nat.div_1_r in HN.
... ...
rewrite angle_div_2_pow_nat_pow_nat_l.
...
    assert (H : angle_div_2_pow_nat (2 ^ n * θ) n = θ). {
      clear HN Hn.
      revert θ.
      induction n; intros; [ apply (angle_add_0_r Hon Hos) | ].
      cbn.
      rewrite Nat.add_0_r.
      rewrite (angle_mul_add_distr_r Hon Hop).
Search angle_div_2.
...
  }
  clear Hlim; rename H into Hlim.
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
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
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
     rngl_opt_add_opp_l := gc_opt_add_opp_l Hop;
     rngl_opt_add_sub := gc_opt_add_sub Hsu;
     rngl_opt_sub_add_distr := gc_opt_sub_add_distr Hsu;
     rngl_opt_mul_inv_l := gc_opt_mul_inv_l Hop;
     rngl_opt_mul_inv_r := gc_opt_mul_inv_r;
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
