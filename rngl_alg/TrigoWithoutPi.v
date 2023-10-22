(* angles without π *)
(* in this vision, an angle is not a real but a pair of reals (x,y)
   such that x²+y²=1; the cosinus is then x and the sinus is y.

   The property sin²+cos²=1 is therefore by definition. It is possible
   to add angles (see below) and we inherit the properties of cos(x+y)
   and sin(x+y) in an obvous way. *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
(*
Import List List.ListNotations.
*)
Require Import Main.Misc Main.RingLike (*Main.IterAdd*).
(*
Require Import Init.Nat.
*)
Require Import RealLike.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition cos2_sin2_prop x y :=
  (negb
     (rngl_has_1 T && rngl_has_opp T && rngl_mul_is_comm T &&
      rngl_has_eq_dec T) ||
   (x² + y² =? 1)%L)%bool = true.

Record angle := mk_ang
  { rngl_cos : T;
    rngl_sin : T;
    rngl_cos2_sin2 : cos2_sin2_prop rngl_cos rngl_sin }.

Class angle_ctx :=
  { ac_iv : rngl_has_inv T = true;
    ac_c2 : rngl_characteristic T ≠ 2;
    ac_or : rngl_is_ordered T = true }.

End a.

Arguments angle T {ro rp}.
Arguments angle_ctx T {ro rp}.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Theorem eq_angle_eq : ∀ θ1 θ2,
  (rngl_cos θ1, rngl_sin θ1) = (rngl_cos θ2, rngl_sin θ2) ↔ θ1 = θ2.
Proof.
intros.
split; intros Hab; [ | now subst θ2 ].
injection Hab; clear Hab; intros Hs Hc.
destruct θ1 as (aco, asi, Hacs).
destruct θ2 as (bco, bsi, Hbcs).
cbn in Hs, Hc.
subst bsi bco.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem angle_zero_prop : (cos2_sin2_prop 1 0)%L.
Proof.
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
progress unfold rngl_squ.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
apply (rngl_eqb_refl Hed).
Qed.

Theorem angle_right_prop : cos2_sin2_prop 0%L 1%L.
Proof.
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
rewrite (rngl_squ_0 Hos).
rewrite (rngl_squ_1 Hon).
rewrite rngl_add_0_l.
apply (rngl_eqb_refl Hed).
Qed.

Theorem angle_straight_prop : (cos2_sin2_prop (-1) 0)%L.
Proof.
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
rewrite (rngl_squ_opp Hop).
progress unfold rngl_squ.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
apply (rngl_eqb_refl Hed).
Qed.

Theorem angle_add_prop :
  ∀ a b,
  cos2_sin2_prop
    (rngl_cos a * rngl_cos b - rngl_sin a * rngl_sin b)%L
    (rngl_cos a * rngl_sin b + rngl_sin a * rngl_cos b)%L.
Proof.
intros.
destruct a as (x, y, Hxy).
destruct b as (x', y', Hxy'); cbn.
move x' before y; move y' before x'.
progress unfold cos2_sin2_prop in Hxy, Hxy' |-*.
remember (rngl_has_1 T) as on eqn:Hon; symmetry in Hon.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
remember (rngl_has_eq_dec T) as ed eqn:Hed; symmetry in Hed.
destruct on; [ | easy ].
destruct op; [ | easy ].
destruct ic; [ | easy ].
destruct ed; [ | easy ].
cbn in Hxy, Hxy' |-*.
rewrite (rngl_squ_add Hic Hon).
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite rngl_add_add_swap.
do 2 rewrite rngl_add_assoc.
rewrite <- (rngl_add_sub_swap Hop).
do 4 rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (2 * x * y')%L).
rewrite (rngl_mul_mul_swap Hic (2 * x) y')%L.
rewrite (rngl_mul_mul_swap Hic (2 * x * x') y' y)%L.
rewrite (rngl_sub_add Hop).
do 4 rewrite (rngl_squ_mul Hic).
rewrite <- rngl_add_assoc.
do 2 rewrite <- rngl_mul_add_distr_l.
apply (rngl_eqb_eq Hed) in Hxy'.
rewrite Hxy'.
now do 2 rewrite (rngl_mul_1_r Hon).
Qed.

Theorem angle_opp_prop : ∀ a, cos2_sin2_prop (rngl_cos a) (- rngl_sin a)%L.
Proof.
intros.
destruct a as (x, y, Hxy); cbn.
progress unfold cos2_sin2_prop in Hxy |-*.
remember (rngl_has_1 T) as on eqn:Hon; symmetry in Hon.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
remember (rngl_has_eq_dec T) as ed eqn:Hed; symmetry in Hed.
destruct on; [ | easy ].
destruct op; [ | easy ].
destruct ic; [ | easy ].
destruct ed; [ | easy ].
cbn in Hxy |-*.
now rewrite (rngl_squ_opp Hop).
Qed.

Definition angle_zero :=
  {| rngl_cos := 1; rngl_sin := 0; rngl_cos2_sin2 := angle_zero_prop |}%L.

Definition angle_right :=
  {| rngl_cos := 0; rngl_sin := 1;
     rngl_cos2_sin2 := angle_right_prop |}%L.

Definition angle_straight :=
  {| rngl_cos := -1; rngl_sin := 0;
     rngl_cos2_sin2 := angle_straight_prop |}%L.

Definition angle_add a b :=
  {| rngl_cos := (rngl_cos a * rngl_cos b - rngl_sin a * rngl_sin b)%L;
     rngl_sin := (rngl_cos a * rngl_sin b + rngl_sin a * rngl_cos b)%L;
     rngl_cos2_sin2 := angle_add_prop a b |}.

Definition angle_opp a :=
  {| rngl_cos := rngl_cos a; rngl_sin := (- rngl_sin a)%L;
     rngl_cos2_sin2 := angle_opp_prop a |}.

Definition angle_sub θ1 θ2 := angle_add θ1 (angle_opp θ2).

Fixpoint angle_mul_nat a n :=
  match n with
  | 0 => angle_zero
  | S n' => angle_add a (angle_mul_nat a n')
  end.

Theorem cos2_sin2_prop_add_squ :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_has_eq_dec T = true →
  ∀ c s, cos2_sin2_prop c s → (c² + s² = 1)%L.
Proof.
intros Hon Hop Hic Hed * Hcs.
progress unfold cos2_sin2_prop in Hcs.
cbn in Hcs.
rewrite Hon, Hop, Hic, Hed in Hcs; cbn in Hcs.
now apply (rngl_eqb_eq Hed) in Hcs.
Qed.

Theorem cos2_sin2_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, ((rngl_cos θ)² + (rngl_sin θ)² = 1)%L.
Proof.
intros Hon Hop Hic Hed *.
destruct θ as (c, s, Hcs); cbn.
progress unfold cos2_sin2_prop in Hcs.
rewrite Hon, Hop, Hic, Hed in Hcs; cbn in Hcs.
now apply (rngl_eqb_eq Hed) in Hcs.
Qed.

Theorem rngl_cos_proj_bound:
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  ∀ c s, cos2_sin2_prop c s → (-1 ≤ c ≤ 1)%L.
Proof.
intros Hic Hon Hop Hiv Hed Hor * Hcs.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed) in Hcs.
assert (H : (c² ≤ 1)%L). {
  rewrite <- Hcs.
  apply (rngl_le_add_r Hor).
  apply (rngl_square_ge_0 Hop Hor).
}
replace 1%L with 1²%L in H. 2: {
  apply (rngl_mul_1_l Hon).
}
rewrite <- (rngl_squ_abs Hop c) in H.
rewrite <- (rngl_squ_abs Hop 1%L) in H.
apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in H. 2: {
  rewrite (rngl_abs_1 Hon Hop Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
rewrite (rngl_abs_1 Hon Hop Hor) in H.
now apply (rngl_abs_le Hop Hor) in H.
Qed.

Theorem rngl_sin_proj_bound:
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  ∀ c s, cos2_sin2_prop c s → (-1 ≤ s ≤ 1)%L.
Proof.
intros Hic Hon Hop Hiv Hed Hor * Hcs.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed) in Hcs.
assert (H : (s² ≤ 1)%L). {
  rewrite <- Hcs.
  apply (rngl_le_add_l Hor).
  apply (rngl_square_ge_0 Hop Hor).
}
replace 1%L with 1²%L in H. 2: {
  apply (rngl_mul_1_l Hon).
}
rewrite <- (rngl_squ_abs Hop s) in H.
rewrite <- (rngl_squ_abs Hop 1%L) in H.
apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in H. 2: {
  rewrite (rngl_abs_1 Hon Hop Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
rewrite (rngl_abs_1 Hon Hop Hor) in H.
now apply (rngl_abs_le Hop Hor) in H.
Qed.

Theorem rngl_cos_bound :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_mul_is_comm T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  ∀ a, (-1 ≤ rngl_cos a ≤ 1)%L.
Proof.
intros Hon Hop Hiv Hic Hed Hor *.
destruct a as (ca, sa, Ha); cbn.
now apply (rngl_cos_proj_bound Hic Hon Hop Hiv Hed Hor ca sa).
Qed.

Theorem rngl_sin_bound :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_mul_is_comm T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  ∀ a, (-1 ≤ rngl_sin a ≤ 1)%L.
Proof.
intros Hon Hop Hiv Hic Hed Hor *.
destruct a as (ca, sa, Ha); cbn.
now apply (rngl_sin_proj_bound Hic Hon Hop Hiv Hed Hor ca sa).
Qed.

(* *)

Context {ac : angle_ctx T}.

Theorem angle_div_2_prop :
  ∀ a (ε := (if (0 ≤? rngl_sin a)%L then 1%L else (-1)%L)),
  cos2_sin2_prop
    (ε * √((1 + rngl_cos a) / 2))%L
    (√((1 - rngl_cos a) / 2)%L).
Proof.
intros.
destruct ac as (Hiv, Hc2, Hor).
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
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_sub_le_add_l Hop Hor).
  rewrite (rngl_sub_0_l Hop).
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
}
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub Hos).
apply (rngl_mul_inv_diag_r Hon Hiv).
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1.
remember (rngl_characteristic T =? 0) as cz eqn:Hcz; symmetry in Hcz.
destruct cz. {
  specialize (H1 1); cbn in H1.
  now rewrite rngl_add_0_r in H1.
}
destruct H1 as (H1, H2).
apply Nat.eqb_neq in Hcz.
remember (rngl_characteristic T) as ch eqn:Hch; symmetry in Hch.
destruct ch; [ easy | clear Hcz ].
destruct ch; [ easy | clear Hc1 ].
destruct ch; [ easy | clear Hc2 ].
specialize (H1 2).
cbn in H1.
rewrite rngl_add_0_r in H1.
apply H1.
split; [ easy | ].
now do 2 apply -> Nat.succ_lt_mono.
Qed.

Definition angle_div_2 a :=
  let ε := if (0 ≤? rngl_sin a)%L then 1%L else (-1)%L in
  {| rngl_cos := (ε * rl_sqrt ((1 + rngl_cos a) / 2))%L;
     rngl_sin := (rl_sqrt ((1 - rngl_cos a) / 2))%L;
     rngl_cos2_sin2 := angle_div_2_prop a |}.

Definition angle_eqb a b :=
  ((rngl_cos a =? rngl_cos b)%L && (rngl_sin a =? rngl_sin b)%L)%bool.

Definition angle_leb θ1 θ2 :=
  if (0 ≤? rngl_sin θ1)%L then
    if (0 ≤? rngl_sin θ2)%L then (rngl_cos θ2 ≤? rngl_cos θ1)%L
    else true
  else
    if (0 ≤? rngl_sin θ2)%L then false
    else (rngl_cos θ1 ≤? rngl_cos θ2)%L.

Definition angle_ltb θ1 θ2 :=
  if (0 ≤? rngl_sin θ1)%L then
    if (0 ≤? rngl_sin θ2)%L then (rngl_cos θ2 <? rngl_cos θ1)%L
    else true
  else
    if (0 ≤? rngl_sin θ2)%L then false
    else (rngl_cos θ1 <? rngl_cos θ2)%L.

End a.

Declare Scope angle_scope.
Delimit Scope angle_scope with A.

Notation "0" := (angle_zero) : angle_scope.
Notation "θ1 + θ2" := (angle_add θ1 θ2) : angle_scope.
Notation "θ1 - θ2" := (angle_sub θ1 θ2) : angle_scope.
Notation "- θ" := (angle_opp θ) : angle_scope.
Notation "θ1 =? θ2" := (angle_eqb θ1 θ2) : angle_scope.
Notation "θ1 ≤? θ2" := (angle_leb θ1 θ2) : angle_scope.
Notation "θ1 <? θ2" := (angle_ltb θ1 θ2) : angle_scope.
Notation "θ1 ≤ θ2" := (angle_leb θ1 θ2 = true) : angle_scope.
Notation "θ1 < θ2" := (angle_ltb θ1 θ2 = true) : angle_scope.
Notation "n * θ" := (angle_mul_nat θ n) : angle_scope.
Notation "θ1 ≤ θ2 < θ3" :=
  (angle_leb θ1 θ2 = true ∧ angle_ltb θ2 θ3 = true)%L : angle_scope.

Arguments angle_div_2 {T ro rp rl ac} a%A.
Arguments rngl_cos {T ro rp} a%A.
Arguments rngl_sin {T ro rp} a%A.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition angle_add_overflow θ1 θ2 := (θ1 + θ2 <? θ1)%A.

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

Theorem eq_rngl_sin_0 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, rngl_sin θ = 0%L → θ = 0%A ∨ θ = angle_straight.
Proof.
intros Hic Hon Hop Hed * Hθ.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct θ as (c, s, Hcs).
cbn in Hθ |-*.
subst s; cbn.
specialize (cos2_sin2_prop_add_squ Hon Hop Hic Hed _ _ Hcs) as H1.
rewrite (rngl_squ_0 Hos) in H1.
rewrite rngl_add_0_r in H1.
rewrite <- (rngl_squ_1 Hon) in H1.
apply (rngl_squ_eq_cases Hic Hon Hop Hiv Hed) in H1.
now destruct H1; subst c; [ left | right ]; apply eq_angle_eq.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
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
    rewrite (rngl_add_opp_r Hop).
    rewrite <- (rngl_mul_sub_distr_l Hop).
    rewrite (rngl_mul_comm Hic).
    apply (rngl_mul_pos_neg Hop Hor Hid); [ | easy ].
    now apply (rngl_lt_0_sub Hop Hor).
  }
}
Qed.

Theorem angle_add_comm :
  rngl_mul_is_comm T = true →
  ∀ θ1 θ2, (θ1 + θ2 = θ2 + θ1)%A.
Proof.
intros Hic *.
apply eq_angle_eq; cbn.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_comm Hic (rngl_sin θ1)).
f_equal.
rewrite rngl_add_comm.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_comm Hic (rngl_cos θ1)).
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
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
        rewrite (rngl_add_opp_r Hop).
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

Theorem angle_add_assoc :
  rngl_has_opp T = true →
  ∀ θ1 θ2 θ3, (θ1 + (θ2 + θ3) = (θ1 + θ2) + θ3)%A.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply eq_angle_eq; cbn.
destruct θ1 as (c1, s1, Hcs1).
destruct θ2 as (c2, s2, Hcs2).
destruct θ3 as (c3, s3, Hcs3).
cbn.
f_equal. {
  rewrite (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_add_distr_r.
  do 4 rewrite rngl_mul_assoc.
  do 2 rewrite <- (rngl_sub_add_distr Hos).
  f_equal.
  do 2 rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap; f_equal.
  apply rngl_add_comm.
} {
  rewrite (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_add_distr_r.
  do 4 rewrite rngl_mul_assoc.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite rngl_add_assoc.
  rewrite (rngl_add_sub_swap Hop).
  f_equal.
  apply (rngl_add_sub_swap Hop).
}
Qed.

Theorem angle_add_opp_r : ∀ θ1 θ2, (θ1 + - θ2 = θ1 - θ2)%A.
Proof. easy. Qed.

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
apply (rngl_add_opp_diag_l Hop).
Qed.

Theorem angle_add_0_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ, (θ + 0 = θ)%A.
Proof.
intros Hon Hos *.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_1_r Hon).
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
now rewrite rngl_add_0_l.
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
rewrite angle_add_opp_r.
rewrite (angle_sub_diag Hic Hon Hop Hed).
apply (angle_add_0_r Hon Hos).
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
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
  rewrite (rngl_add_opp_r Hop).
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
  rewrite (rngl_add_opp_r Hop).
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
rewrite (rngl_add_opp_r Hop).
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

Theorem rngl_cos_add_straight_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ, rngl_cos (θ + angle_straight) = (- rngl_cos θ)%L.
Proof.
intros Hon Hop *; cbn.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_0_r Hos).
apply (rngl_sub_0_r Hos).
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
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
rewrite (rngl_add_opp_r Hop).
do 2 rewrite (rngl_mul_comm Hic (rngl_cos θ1)).
do 2 rewrite (rngl_mul_comm Hic (rngl_sin θ1)).
f_equal.
rewrite (rngl_opp_add_distr Hop).
rewrite <- (rngl_mul_opp_r Hop).
rewrite (rngl_mul_opp_l Hop).
now rewrite (rngl_add_opp_r Hop).
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
  rewrite angle_add_opp_r.
  rewrite <- (angle_opp_add_distr Hic Hop).
  rewrite rngl_sin_opp.
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  now rewrite (angle_add_comm Hic).
} {
  now rewrite rngl_cos_opp.
}
Qed.

Theorem rngl_sin_add_straight_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ, (rngl_sin (θ + angle_straight) = - rngl_sin θ)%L.
Proof.
intros Hon Hop *; cbn.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_l.
rewrite (rngl_mul_opp_r Hop).
f_equal.
apply (rngl_mul_1_r Hon).
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

Theorem angle_add_0_l :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ, (0 + θ = θ)%A.
Proof.
intros Hon Hos *.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_1_l Hon).
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
now rewrite rngl_add_0_r.
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
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
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
      rewrite (rngl_add_opp_r Hop).
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

(* to be completed perhaps
Theorem rngl_sin_nonneg_sin_nonneg_sin_neg2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (θ1 + angle_straight ≤ θ1 + θ2)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → √((1 + rngl_cos (θ1 + θ2)) / 2)%L =
       (√((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2) -
        √((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2))%L.
Proof.
intros Hic Hon Hop Hed * Haov Hzs1 Hzs2 Hzs3.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
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
destruct (rngl_lt_dec Hor y x) as [Hxy| Hxy]. {
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
      rewrite (rngl_add_opp_r Hop).
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
(* bizarre, ce cas-là aussi serait exfalso aussi *)
...
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
...
*)

Theorem angle_opp_involutive :
  rngl_has_opp T = true →
  ∀ θ, (- - θ)%A = θ.
Proof.
intros Hop *.
apply eq_angle_eq; cbn.
f_equal.
apply (rngl_opp_involutive Hop).
Qed.

Theorem angle_opp_inj :
  rngl_has_opp T = true →
  ∀ θ1 θ2, (- θ1)%A = (- θ2)%A → θ1 = θ2.
Proof.
intros Hop * H12.
progress unfold angle_opp in H12.
injection H12; clear H12; intros H1 H2.
apply (rngl_opp_inj Hop) in H1.
apply eq_angle_eq.
now rewrite H1, H2.
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
(* proof borrowed from rngl_sin_nonneg_sin_nonneg_add_1_cos_add_sub
   and it works: perhaps there is a way to unify these two theorems *)
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
rewrite angle_add_opp_r.
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
do 2 rewrite (rngl_add_opp_r Hop).
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
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
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
rewrite angle_add_opp_r.
rewrite rngl_cos_opp.
apply (rngl_lt_le_incl Hor) in Hzs2.
now apply rngl_sin_nonneg_sin_nonneg_add_1_cos_add_add.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
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
rewrite angle_add_opp_r.
rewrite (angle_sub_diag Hic Hon Hop Hed).
apply (angle_add_0_r Hon Hos).
Qed.

Theorem angle_add_opp_diag_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (- θ + θ = 0)%A.
Proof.
intros Hic Hon Hop Hed *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_opp_l Hop).
progress unfold rngl_sub.
rewrite Hop.
rewrite (rngl_opp_involutive Hop).
do 2 rewrite fold_rngl_squ.
rewrite (cos2_sin2_1 Hon Hop Hic Hed).
f_equal.
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_mul_comm Hic).
apply (rngl_sub_diag Hos).
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
rewrite (angle_add_opp_diag_l Hic Hon Hop Hed).
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
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
  rewrite (rngl_add_opp_r Hop).
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
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
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

Theorem angle_sub_opp_r :
  rngl_has_opp T = true →
  ∀ θ1 θ2, (θ1 - - θ2)%A = (θ1 + θ2)%A.
Proof.
intros Hop *.
apply eq_angle_eq; cbn.
now rewrite (rngl_opp_involutive Hop).
Qed.

Theorem rngl_cos_sub_straight_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ, rngl_cos (angle_straight - θ) = (- rngl_cos θ)%L.
Proof.
intros Hon Hop *; cbn.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
now rewrite (rngl_sub_0_r Hos).
Qed.

Theorem rngl_sin_sub_straight_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ, rngl_sin (angle_straight - θ) = rngl_sin θ.
Proof.
intros Hon Hop *; cbn.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
apply (rngl_opp_involutive Hop).
Qed.

Theorem angle_add_sub_swap :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2 θ3, (θ1 + θ2 - θ3 = θ1 - θ3 + θ2)%A.
Proof.
intros Hic Hop *.
apply (angle_add_add_swap Hic Hop).
Qed.

Theorem angle_add_sub_assoc :
  rngl_has_opp T = true →
  ∀ θ1 θ2 θ3, (θ1 + (θ2 - θ3))%A = (θ1 + θ2 - θ3)%A.
Proof.
intros Hop *.
progress unfold angle_sub.
apply (angle_add_assoc Hop).
Qed.

Theorem rngl_cos_angle_div_2_add_not_overflow :
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
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
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
progress unfold angle_add_overflow in Haov.
apply angle_ltb_ge in Haov.
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
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (-1))%L.
rewrite (rngl_squ_opp_1 Hon Hop).
rewrite (rngl_mul_1_l Hon).
(*to be cleaned from here*)
(* to be completed
subst θ3.
progress unfold angle_leb in Haov.
remember (θ1 - angle_straight)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (rngl_sin_add_straight_r Hon Hop) in Haov, Hzs1.
rewrite (rngl_cos_add_straight_r Hon Hop) in Haov.
rewrite <- (rngl_opp_0 Hop) in Hzs1.
apply (rngl_opp_lt_compat Hop Hor) in Hzs1.
rewrite (rngl_cos_add_straight_r Hon Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
remember (0 ≤? - rngl_sin θ1)%L as x eqn:Hx.
symmetry in Hx.
destruct x. {
  apply (rngl_leb_le) in Hx.
  rewrite <- (rngl_opp_0 Hop) in Hx.
  apply (rngl_opp_le_compat Hop Hor) in Hx.
  now apply (rngl_nlt_ge Hor) in Hx.
}
clear Hx.
rewrite (angle_add_add_swap Hic Hop) in Haov, Hzs3 |-*.
remember (θ2 - angle_straight)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
move Hzs3 after Hzs3.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs2.
rewrite <- (rngl_opp_0 Hop) in Hzs2.
apply (rngl_opp_lt_compat Hop Hor) in Hzs2.
rewrite (rngl_cos_add_straight_r Hon Hop θ2).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (angle_add_assoc Hop) in Haov, Hzs3 |-*.
rewrite <- (angle_add_assoc Hop) in Haov, Hzs3 |-*.
rewrite (angle_straight_add_straight Hon Hop) in Haov, Hzs3 |-*.
rewrite (angle_add_0_r Hon Hos) in Haov, Hzs3 |-*.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1 + rngl_cos θ2))%L
  as [Hzc12| Hc12z]. {
  apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc12z.
apply (rngl_nle_gt Hor) in Hzs3.
apply rngl_leb_nle in Hzs3.
rewrite Hzs3 in Haov.
apply (rngl_leb_gt Hor) in Hzs3.
apply rngl_leb_le in Haov.
move Haov at bottom.
exfalso.
apply (rngl_nlt_ge Hor) in Haov.
apply Haov; clear Haov.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
  remember (angle_straight - θ1)%A as θ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Heqθ.
  rewrite (angle_sub_opp_r Hop) in Heqθ.
  apply (angle_add_move_l Hic Hon Hop Hed) in Heqθ.
  subst θ1; rename θ into θ1.
  move θ1 after θ2.
  rewrite <- (angle_sub_sub_distr Hic Hop) in Hzs3 |-*.
  rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs1, Hzs3.
  rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc12z, Hc1z.
  do 2 rewrite (rngl_cos_sub_straight_l Hon Hop).
  apply -> (rngl_opp_lt_compat Hop Hor).
  rewrite rngl_add_comm in Hc12z.
  rewrite (rngl_add_opp_r Hop) in Hc12z.
  apply (rngl_lt_sub_lt_add_l Hop Hor) in Hc12z.
  rewrite rngl_add_0_r in Hc12z.
  rewrite <- (rngl_opp_0 Hop) in Hc1z.
  apply (rngl_opp_le_compat Hop Hor) in Hc1z.
  rewrite <- (rngl_sub_0_l Hop).
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_assoc.
  apply (rngl_add_nonneg_pos Hor Hos). {
    rewrite <- (rngl_mul_1_r Hon (rngl_cos θ1)) at 1.
    rewrite <- rngl_mul_add_distr_l.
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
    apply (rngl_le_sub_le_add_l Hop Hor).
    rewrite (rngl_sub_0_l Hop).
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
  now apply (rngl_mul_pos_pos Hop Hor Hii).
}
apply (rngl_nle_gt Hor) in Hzc1.
move Hzc1 before Hzs2.
rewrite <- (rngl_sub_0_l Hop).
apply (rngl_lt_add_lt_sub_l Hop Hor).
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
remember (angle_straight - θ2)%A as θ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Heqθ.
rewrite (angle_sub_opp_r Hop) in Heqθ.
apply (angle_add_move_l Hic Hon Hop Hed) in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (angle_add_comm Hic) in Hzs3 |-*.
rewrite <- (angle_sub_sub_distr Hic Hop) in Hzs3 |-*.
rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs2, Hzs3.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc2z, Hc12z |-*.
rewrite <- (rngl_opp_0 Hop) in Hc2z.
apply (rngl_opp_lt_compat Hop Hor) in Hc2z.
rewrite (rngl_add_opp_r Hop) in Hc12z |-*.
apply (rngl_lt_sub_lt_add_l Hop Hor) in Hc12z.
apply (rngl_lt_sub_lt_add_l Hop Hor).
rewrite rngl_add_0_r in Hc12z |-*.
...
(*
...
apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
now apply rngl_sin_nonneg_sin_nonneg_sin_neg2.
...
differences:
    Haov : (θ1 + angle_straight ≤ θ1 + θ2)%A
    goal : opposite subtraction
...
rngl_sin_nonneg_sin_nonneg_sin_neg:
  rngl_mul_is_comm T = true
  → rngl_has_1 T = true
    → rngl_has_opp T = true
      → rngl_has_eq_dec T = true
        → ∀ θ1 θ2 : angle T,
            (θ1 ≤ θ1 + θ2)%A
            → (0 ≤ rngl_sin θ1)%L
              → (0 ≤ rngl_sin θ2)%L
                → (rngl_sin (θ1 + θ2) < 0)%L
                  → √((1 + rngl_cos (θ1 + θ2)) / 2)%L =
                    (√((1 - rngl_cos θ1) / 2) * √((1 - rngl_cos θ2) / 2) -
                     √((1 + rngl_cos θ1) / 2) * √((1 + rngl_cos θ2) / 2))%L
Search (√((1 + rngl_cos _) / 2))%L.
...
*)
*)
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
destruct (rngl_le_dec Hor 0 (rngl_cos θ1 + rngl_cos θ2))%L
  as [Hzc12| Hc12z]. {
  apply rngl_sin_nonneg_sin_nonneg_add_cos_nonneg; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc12z.
progress exfalso.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
  apply (rngl_nlt_ge Hor) in Hc13.
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
  progress exfalso; apply Hzs3; clear Hzs3; cbn.
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
remember (θ2 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (angle_add_assoc Hop) in Hzs3, Hc3z, Hc13.
rewrite (rngl_sin_add_right Hon Hos) in Hzs2, Hzs3.
rewrite (rngl_cos_add_right Hon Hop) in Hc12z, Hc3z, Hc13, Hc2z.
rewrite (rngl_add_opp_r Hop) in Hc12z, Hc13.
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
    now apply (rngl_cos_angle_div_2_add_not_overflow Hic Hon Hop Hed).
  } {
...
    now apply rngl_sin_angle_div_2_add_not_overflow.
  }
...
*)

End a.
