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
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
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
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
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

Definition angle_compare θ1 θ2 :=
  if (rngl_zero ≤? rngl_sin θ1)%L then
    if (rngl_zero ≤? rngl_sin θ2)%L then
      rngl_compare (rngl_cos θ2) (rngl_cos θ1)
    else Lt
  else
    if (rngl_zero ≤? rngl_sin θ2)%L then Gt
    else rngl_compare (rngl_cos θ1) (rngl_cos θ2).

Definition angle_eq θ1 θ2 := angle_compare θ1 θ2 = Eq.
Definition angle_lt θ1 θ2 := angle_compare θ1 θ2 = Lt.
Definition angle_le θ1 θ2 := angle_compare θ1 θ2 ≠ Gt.

(*
Definition bool_of_angle_compare cmp θ1 θ2 :=
  match (cmp, angle_compare θ1 θ2) with
  | (Eq, Eq) | (Lt, Lt) | (Gt, Gt) => true
  | _ => false
  end.

Definition angle_eqb := bool_of_angle_compare Eq.
Definition angle_ltb := bool_of_angle_compare Lt.
Definition angle_leb θ1 θ2 := negb (bool_of_angle_compare Gt θ1 θ2).
*)

Definition angle_eqb θ1 θ2 :=
  match angle_compare θ1 θ2 with
  | Eq => true
  | _ => false
  end.

Definition angle_ltb θ1 θ2 :=
  match angle_compare θ1 θ2 with
  | Lt => true
  | _ => false
  end.

Definition angle_leb θ1 θ2 :=
  match angle_compare θ1 θ2 with
  | Gt => false
  | _ => true
  end.

End a.

Arguments angle T {ro rp}.

(* to be completed
Declare Scope angle_scope.
Delimit Scope angle_scope with A.

Notation "θ1 + θ2" := (angle_add θ1 θ2) : angle_scope.
Notation "θ1 - θ2" := (angle_sub θ1 θ2) : angle_scope.
Notation "n * a" := (angle_mul_nat a n) : angle_scope.

Notation "θ1 ?= θ2" := (angle_compare θ1 θ2) : angle_scope.
Notation "θ1 =? θ2" := (angle_eqb θ1 θ2) : angle_scope.
Notation "θ1 <? θ2" := (angle_ltb θ1 θ2) : angle_scope.
Notation "θ1 ≤? θ2" := (angle_leb θ1 θ2) : angle_scope.
Notation "θ1 < θ2" := (angle_lt θ1 θ2) : angle_scope.
Notation "θ1 ≤ θ2" := (angle_le θ1 θ2) : angle_scope.
Notation "- θ" := (angle_opp θ) : angle_scope.
Notation "0" := (angle_zero) : angle_scope.
Notation "a ≤ b < c" := (angle_leb a b = true ∧ angle_ltb b c = true)%L :
  angle_scope.

Arguments rngl_cos {T ro rp} a%A.
Arguments rngl_sin {T ro rp} a%A.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Context {Hiv : rngl_has_inv T = true}.
Context {Hc2 : rngl_characteristic T ≠ 2}.
Context {Hor : rngl_is_ordered T = true}.

Theorem angle_div_2_prop :
  ∀ a (ε := (if (0 ≤? rngl_sin a)%L then 1%L else (-1)%L)),
  cos2_sin2_prop
    (ε * √((1 + rngl_cos a) / 2))%L
    (√((1 - rngl_cos a) / 2)%L).
Proof.
intros.
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
move Hc1 after Hc2.
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub Hos).
apply (rngl_mul_inv_r Hon Hiv).
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

Definition angle_div_2 θ :=
  let ε := if (0 ≤? rngl_sin θ)%L then 1%L else (-1)%L in
  {| rngl_cos := (ε * rl_sqrt ((1 + rngl_cos θ) / 2))%L;
     rngl_sin := (rl_sqrt ((1 - rngl_cos θ) / 2))%L;
     rngl_cos2_sin2 := angle_div_2_prop θ |}.

Arguments angle_div_2 θ%A.

Definition angle_add_overflow θ1 θ2 := (θ1 + θ2 <? θ1)%A.

Theorem angle_eqb_refl :
  rngl_has_eq_dec T = true →
  ∀ θ, (θ =? θ)%A = true.
Proof.
intros Hed *.
progress unfold angle_eqb.
progress unfold angle_compare.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  progress unfold rngl_compare.
  now rewrite (rngl_eqb_refl Hed).
} {
  progress unfold rngl_compare.
  now rewrite (rngl_eqb_refl Hed).
}
Qed.

Theorem angle_compare_eq_iff :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 ?= θ2)%A = Eq ↔ θ1 = θ2.
Proof.
intros Hic Hon Hop Hed *.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert
  (Hid :
    (rngl_is_integral_domain T ||
       rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1, Hed.
}
progress unfold angle_compare.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (rngl_cos θ2 ?= rngl_cos θ1)%L as c21 eqn:Hc21.
remember (rngl_cos θ1 ?= rngl_cos θ2)%L as c12 eqn:Hc12.
symmetry in Hzs1, Hzs2, Hc21, Hc12.
split; intros H12. {
  destruct zs1. {
    destruct zs2; [ | easy ].
    destruct c21; [ | easy | easy ].
    apply (rngl_compare_eq_iff Hed) in Hc21.
    rewrite Hc21 in Hc12.
    apply eq_angle_eq.
    rewrite Hc21; f_equal.
    apply (rngl_leb_le) in Hzs1, Hzs2.
    rewrite <- (rngl_abs_nonneg Hop Hor); [ | easy ].
    rewrite <- (rngl_abs_nonneg Hop Hor (rngl_sin θ1)); [ | easy ].
    apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hid).
    specialize (cos2_sin2_1 Hon Hop Hic Hed θ1) as H1.
    apply (rngl_add_move_l Hop) in H1.
    rewrite H1; clear H1.
    specialize (cos2_sin2_1 Hon Hop Hic Hed θ2) as H1.
    apply (rngl_add_move_l Hop) in H1.
    rewrite H1; clear H1.
    now f_equal; f_equal.
  } {
    destruct zs2; [ easy | ].
    destruct c12; [ | easy | easy ].
    apply (rngl_compare_eq_iff Hed) in Hc12.
    apply eq_angle_eq.
    rewrite Hc12; f_equal.
    apply (rngl_leb_gt Hor) in Hzs1, Hzs2.
    apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
    apply (rngl_opp_inj Hop).
    rewrite <- (rngl_abs_nonpos Hop Hor); [ | easy ].
    rewrite <- (rngl_abs_nonpos Hop Hor (rngl_sin θ2))%L; [ | easy ].
    apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hid).
    specialize (cos2_sin2_1 Hon Hop Hic Hed θ1) as H1.
    apply (rngl_add_move_l Hop) in H1.
    rewrite H1; clear H1.
    specialize (cos2_sin2_1 Hon Hop Hic Hed θ2) as H1.
    apply (rngl_add_move_l Hop) in H1.
    rewrite H1; clear H1.
    now f_equal; f_equal.
  }
} {
  subst θ2.
  rewrite Hzs1 in Hzs2; subst zs2.
  rewrite Hc21 in Hc12; subst c12.
  destruct zs1. {
    destruct c21; [ easy | | ]. {
      apply (rngl_compare_lt_iff Hor Hed) in Hc21.
      now apply (rngl_lt_irrefl Hor) in Hc21.
    } {
      apply (rngl_compare_gt_iff Hor Hed) in Hc21.
      now apply (rngl_lt_irrefl Hor) in Hc21.
    }
  } {
    destruct c21; [ easy | | ]. {
      apply (rngl_compare_lt_iff Hor Hed) in Hc21.
      now apply (rngl_lt_irrefl Hor) in Hc21.
    } {
      apply (rngl_compare_gt_iff Hor Hed) in Hc21.
      now apply (rngl_lt_irrefl Hor) in Hc21.
    }
  }
}
Qed.

Theorem angle_compare_lt_iff : ∀ θ1 θ2, (θ1 ?= θ2)%A = Lt ↔ (θ1 < θ2)%A.
Proof. easy. Qed.

Theorem angle_compare_gt_iff :
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 ?= θ2)%A = Gt ↔ (θ2 < θ1)%A.
Proof.
intros Hed *.
progress unfold angle_lt.
progress unfold angle_compare.
destruct (0 ≤? rngl_sin θ1)%L. {
  destruct (0 ≤? rngl_sin θ2)%L; [ | easy ].
  remember (rngl_cos θ2 ?= rngl_cos θ1)%L as c21 eqn:Hc21.
  remember (rngl_cos θ1 ?= rngl_cos θ2)%L as c12 eqn:Hc12.
  symmetry in Hc21, Hc12.
  destruct c21. {
    split; [ easy | ].
    intros H; move H at top; subst c12.
    apply (rngl_compare_eq_iff Hed) in Hc21.
    apply (rngl_compare_lt_iff Hor Hed) in Hc12.
    rewrite Hc21 in Hc12.
    now apply (rngl_lt_irrefl Hor) in Hc12.
  } {
    split; [ easy | ].
    intros H; move H at top; subst c12.
    apply (rngl_compare_lt_iff Hor Hed) in Hc21.
    apply (rngl_compare_lt_iff Hor Hed) in Hc12.
    now apply (rngl_lt_asymm Hor) in Hc21.
  } {
    split; [ | easy ].
    intros _.
    apply (rngl_compare_gt_iff Hor Hed) in Hc21.
    destruct c12; [ | easy | ]. {
      apply (rngl_compare_eq_iff Hed) in Hc12.
      rewrite Hc12 in Hc21.
      now apply (rngl_lt_irrefl Hor) in Hc21.
    } {
      apply (rngl_compare_gt_iff Hor Hed) in Hc12.
      now apply (rngl_lt_asymm Hor) in Hc21.
    }
  }
}
destruct (0 ≤? rngl_sin θ2)%L; [ easy | ].
progress unfold rngl_compare.
rewrite (rngl_eqb_sym Hed).
remember (rngl_cos θ2 =? rngl_cos θ1)%L as ce12 eqn:Hce12.
symmetry in Hce12.
destruct ce12; [ easy | ].
apply (rngl_eqb_neq Hed) in Hce12.
remember (rngl_cos θ1 ≤? rngl_cos θ2)%L as c12 eqn:Hc12.
remember (rngl_cos θ2 ≤? rngl_cos θ1)%L as c21 eqn:Hc21.
symmetry in Hc12, Hc21.
destruct c12. {
  split; [ easy | ].
  destruct c21; [ | easy ].
  apply (rngl_leb_le) in Hc12, Hc21.
  now apply (rngl_le_antisymm Hor) in Hc12.
} {
  split; [ intros _ | easy ].
  destruct c21; [ easy | ].
  apply (rngl_leb_gt Hor) in Hc12, Hc21.
  now apply (rngl_lt_asymm Hor) in Hc12.
}
Qed.

Theorem angle_lt_irrefl :
  rngl_has_eq_dec T = true →
  ∀ θ, ¬ (θ < θ)%A.
Proof.
intros Hed * Hc.
progress unfold angle_lt in Hc.
progress unfold angle_compare in Hc.
destruct (0 ≤? rngl_sin θ)%L. {
  apply (rngl_compare_lt_iff Hor Hed) in Hc.
  now apply (rngl_lt_irrefl Hor) in Hc.
} {
  apply (rngl_compare_lt_iff Hor Hed) in Hc.
  now apply (rngl_lt_irrefl Hor) in Hc.
}
Qed.

Theorem angle_eqb_eq :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 : angle T, (θ1 =? θ2)%A = true ↔ θ1 = θ2.
Proof.
intros Hic Hon Hop Hed *.
progress unfold angle_eqb.
remember (θ1 ?= θ2)%A as c12 eqn:Hc12.
symmetry in Hc12.
destruct c12. {
  now apply (angle_compare_eq_iff Hic Hon Hop Hed) in Hc12.
} {
  apply -> angle_compare_lt_iff in Hc12.
  split; [ easy | ].
  intros H; subst θ2.
  now apply (angle_lt_irrefl Hed) in Hc12.
} {
  apply (angle_compare_gt_iff Hed) in Hc12.
  split; [ easy | ].
  intros; subst θ2.
  now apply (angle_lt_irrefl Hed) in Hc12.
}
Qed.

Theorem angle_lt_asymm :
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 < θ2 → ¬ θ2 < θ1)%A.
Proof.
intros Hed * H12 H21.
progress unfold angle_lt in H12, H21.
progress unfold angle_compare in H12.
progress unfold angle_compare in H21.
destruct (0 ≤? rngl_sin θ1)%L. {
  destruct (0 ≤? rngl_sin θ2)%L; [ | easy ].
  apply -> (rngl_compare_lt_iff Hor Hed) in H12.
  apply -> (rngl_compare_lt_iff Hor Hed) in H21.
  now apply (rngl_lt_asymm Hor) in H12.
} {
  destruct (0 ≤? rngl_sin θ2)%L; [ easy | ].
  apply -> (rngl_compare_lt_iff Hor Hed) in H12.
  apply -> (rngl_compare_lt_iff Hor Hed) in H21.
  now apply (rngl_lt_asymm Hor) in H12.
}
Qed.

Theorem angle_ltb_ge :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 <? θ2)%A = false ↔ (θ2 ≤ θ1)%A.
Proof.
intros Hic Hon Hop Hed *.
progress unfold angle_ltb.
progress unfold angle_le.
remember (θ1 ?= θ2)%A as t12 eqn:Ht12.
remember (θ2 ?= θ1)%A as t21 eqn:Ht21.
symmetry in Ht12, Ht21.
destruct t12. {
  split; [ intros _ | easy ].
  apply (angle_compare_eq_iff Hic Hon Hop Hed) in Ht12.
  subst θ2.
  destruct t21; [ easy | easy | ].
  apply (angle_compare_gt_iff Hed) in Ht21.
  now apply (angle_lt_irrefl Hed) in Ht21.
} {
  split; [ easy | ].
  destruct t21; [ | | easy ]. {
    apply -> angle_compare_lt_iff in Ht12.
    apply -> (angle_compare_eq_iff Hic Hon Hop Hed) in Ht21.
    subst θ2.
    now apply (angle_lt_irrefl Hed) in Ht12.
  } {
    apply -> angle_compare_lt_iff in Ht12.
    apply -> angle_compare_lt_iff in Ht21.
    now apply (angle_lt_asymm Hed) in Ht12.
  }
} {
  split; [ intros _ | easy ].
  destruct t21; [ easy | easy | ].
  apply -> (angle_compare_gt_iff Hed) in Ht12.
  apply -> (angle_compare_gt_iff Hed) in Ht21.
  now apply (angle_lt_asymm Hed) in Ht12.
}
Qed.

Theorem rl_sqrt_mul :
  ∀ a b,
  (0 ≤ a)%L
  → (0 ≤ b)%L
  → rl_sqrt (a * b)%L = (rl_sqrt a * rl_sqrt b)%L.
Proof.
intros * Ha Hb.
progress unfold rl_sqrt.
now rewrite rl_nth_root_mul.
Qed.

Theorem rl_sqrt_div :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b, (0 ≤ a)%L → (0 < b)%L → (√(a / b) = √a / √b)%L.
Proof.
intros Hon Hop * Ha Hb.
progress unfold rngl_div.
rewrite Hiv.
rewrite rl_sqrt_mul; [ | easy | ]. 2: {
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
}
f_equal.
now apply rl_nth_root_inv.
Qed.

Theorem rl_sqrt_squ :
  rngl_has_opp T = true →
  ∀ a, (√(a²))%L = rngl_abs a.
Proof.
intros Hop *.
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
do 2 rewrite (rl_sqrt_squ Hop).
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
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hop).
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
        progress unfold angle_le in Haov.
        progress unfold angle_compare in Haov.
        cbn in Haov.
        rewrite (rngl_leb_refl Hor) in Haov.
        rewrite (rngl_mul_0_r Hos) in Haov.
        rewrite rngl_add_0_l in Haov.
        do 2 rewrite (rngl_mul_0_l Hos) in Haov.
        rewrite (rngl_leb_refl Hor) in Haov.
        apply Haov; clear Haov.
        rewrite (rngl_squ_opp_1 Hon Hop).
        rewrite (rngl_sub_0_r Hos).
        apply (rngl_compare_gt_iff Hor Hed).
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

Theorem fold_angle_sub : ∀ θ1 θ2, (θ1 + - θ2 = θ1 - θ2)%A.
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
apply (rngl_add_opp_l Hop).
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
rewrite fold_angle_sub.
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
remember (θ1 + θ2)%A as θ3 eqn:Hθ3.
apply (rngl_nlt_ge Hor).
intros Hzs2.
progress unfold angle_le in Haov.
progress unfold angle_compare in Haov.
apply (rngl_leb_le) in Hzs1.
rewrite Hzs1 in Haov.
apply (rngl_leb_le) in Hzs1.
apply (rngl_leb_le) in Hzs3.
rewrite Hzs3 in Haov.
apply (rngl_leb_le) in Hzs3.
apply Haov; clear Haov.
apply (rngl_compare_gt_iff Hor Hed).
apply (rngl_nle_gt Hor).
intros Hc31.
apply (rngl_nle_gt Hor) in Hzs2.
apply Hzs2; clear Hzs2.
symmetry in Hθ3.
apply (angle_add_sub_eq_l Hic Hon Hop Hed) in Hθ3.
subst θ2.
now apply (rngl_sin_nonneg_cos_le_sin_sub_nonneg Hic Hon Hop Hed).
Qed.

Theorem angle_le_rngl_sin_nonneg_sin_nonneg :
  ∀ θ1 θ2,
  (θ2 ≤ θ1)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L.
Proof.
intros * H21 Hzs1.
progress unfold angle_le in H21.
apply (rngl_nlt_ge Hor).
intros Hs2z.
apply H21; clear H21.
progress unfold angle_compare.
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
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hop).
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

Theorem angle_add_opp_l :
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
rewrite (fold_rngl_sub Hop).
rewrite (rngl_mul_comm Hic).
apply (rngl_sub_diag Hos).
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

Theorem angle_dist_separation :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, angle_dist θ1 θ2 = 0%L → θ1 = θ2.
Proof.
intros Hic Hon Hop Hed * H12.
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
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct θ1 as (c1, s1, Hcs1).
destruct θ2 as (c2, s2, Hcs2).
destruct θ3 as (c3, s3, Hcs3).
progress unfold angle_dist.
cbn.
specialize (rngl_abs_triangle Hop Hor) as H1.
apply (euclidean_distance_triangular Hic Hon Hop).
Qed.

Definition is_angle_upper_limit_when_tending_to_inf f l :=
  ∀ ε, (0 < ε)%L → ∃ N, ∀ n : nat, N ≤ n → (angle_dist l (f n) < ε)%L.

(* TODO : rename parameters a and b into θ1 and θ2 in initial definitions
   e.g. angle_add *)

Theorem eq_rngl_cos_opp_1 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (rngl_cos θ = -1 → rngl_sin θ = 0)%L.
Proof.
intros Hic Hon Hop Hed * Hθ.
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

(*
Theorem rngl_cos_eq_sin_add_right :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ θ, rngl_cos θ = rngl_sin (θ + angle_right).
Proof.
intros Hon Hos *; cbn.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_0_r Hos).
symmetry.
apply rngl_add_0_r.
Qed.
*)

Theorem angle_leb_refl :
  rngl_has_eq_dec T = true →
  ∀ θ, (θ ≤? θ)%A = true.
Proof.
intros Hed *.
progress unfold angle_leb.
progress unfold angle_compare.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  progress unfold rngl_compare.
  now rewrite (rngl_eqb_refl Hed).
} {
  progress unfold rngl_compare.
  now rewrite (rngl_eqb_refl Hed).
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

Theorem angle_eqb_neq :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 =? θ2)%A = false ↔ θ1 ≠ θ2.
Proof.
intros Hic Hon Hop Hed *.
split. {
  intros H12 H.
  apply Bool.not_true_iff_false in H12.
  apply H12; clear H12.
  now apply (angle_eqb_eq Hic Hon Hop Hed).
} {
  intros H.
  apply Bool.not_true_iff_false.
  intros H12; apply H; clear H.
  now apply (angle_eqb_eq Hic Hon Hop Hed).
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
progress unfold angle_le in Hθ.
progress unfold angle_compare in Hθ.
cbn in Hθ.
rewrite (rngl_leb_refl Hor) in Hθ.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; [ | easy ].
remember (1 ?= rngl_cos θ)%L as oc eqn:Hoc.
symmetry in Hoc.
destruct oc; [ | | easy ]. {
  apply (rngl_compare_eq_iff Hed) in Hoc.
  symmetry in Hoc.
  apply (le_1_rngl_cos Hic Hon Hop Hed).
  rewrite Hoc.
  apply (rngl_le_refl Hor).
} {
  apply (rngl_compare_lt_iff Hor Hed) in Hoc.
  apply (rngl_nle_gt Hor) in Hoc.
  exfalso; apply Hoc; clear Hoc.
  now apply rngl_cos_bound.
}
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

Theorem angle_leb_le :
  ∀ θ1 θ2, (θ1 ≤? θ2)%A = true ↔ (θ1 ≤ θ2)%A.
Proof.
intros.
progress unfold angle_leb.
progress unfold angle_le.
now destruct (θ1 ?= θ2)%A.
Qed.

Theorem angle_leb_nle :
  ∀ θ1 θ2, (θ1 ≤? θ2)%A = false ↔ ¬ (θ1 ≤ θ2)%A.
Proof.
intros.
split; intros H12. {
  intros H; apply angle_leb_le in H.
  now rewrite H in H12.
} {
  apply Bool.not_true_iff_false.
  intros H; apply H12.
  now apply angle_leb_le.
}
Qed.

Theorem angle_opp_involutive :
  rngl_has_opp T = true →
  ∀ θ, (- - θ)%A = θ.
Proof.
intros Hop *.
apply eq_angle_eq; cbn.
f_equal.
apply (rngl_opp_involutive Hop).
Qed.

Theorem angle_opp_le_compat :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, θ1 ≠ 0%A → θ2 ≠ 0%A → (θ1 ≤ θ2)%A ↔ (- θ2 ≤ - θ1)%A.
Proof.
intros Hic Hon Hop Hed * H1z H2z.
assert (H : ∀ θ1 θ2, θ1 ≠ 0%A → θ2 ≠ 0%A → (θ1 ≤ θ2)%A → (- θ2 ≤ - θ1)%A). {
  clear θ1 θ2 H1z H2z.
  intros θ1 θ2 H1z H2z H12.
  progress unfold angle_le in H12 |-*.
  intros H; apply H12; clear H12; rename H into H12.
  apply (angle_compare_gt_iff Hed) in H12.
  apply (angle_compare_gt_iff Hed).
  progress unfold angle_lt in H12.
  progress unfold angle_lt.
  progress unfold angle_compare in H12.
  progress unfold angle_compare.
  cbn in H12.
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
      apply (rngl_compare_lt_iff Hor Hed).
      apply (rngl_lt_iff Hor).
      split; [ apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor) | ].
      intros H; symmetry in H.
      rewrite H in H12.
      rewrite (rngl_compare_refl Hed) in H12.
      destruct zo2; [ easy | ].
      apply (eq_rngl_cos_opp_1 Hic Hon Hop Hed) in H.
      rewrite H in Hzo2.
      rewrite (rngl_opp_0 Hop) in Hzo2.
      now rewrite (rngl_leb_refl Hor) in Hzo2.
    }
    apply (rngl_leb_gt Hor) in Hz2.
    destruct zo1. {
      apply rngl_leb_le in Hzo1.
      apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzo1.
      apply (rngl_le_antisymm Hor) in Hzo1; [ | easy ].
      symmetry in Hzo1.
      apply (eq_rngl_sin_0 Hic Hon Hop Hed) in Hzo1.
      destruct Hzo1 as [Hzo1| Hzo1]; [ easy | ].
      subst θ1; cbn in H12.
      destruct zo2. {
        apply (rngl_compare_lt_iff Hor Hed) in H12.
        apply (rngl_nle_gt Hor) in H12.
        exfalso; apply H12.
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

Theorem rl_sqrt_1 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
 rl_sqrt 1%L = 1%L.
Proof.
intros Hic Hon Hop Hii.
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

Theorem rl_sqrt_0 :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  rl_sqrt 0%L = 0%L.
Proof.
intros Hop Hic Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rl_nth_root_pow 2 0%L (rngl_le_refl Hor _)) as H1.
rewrite <- (rngl_squ_0 Hos) in H1 at 2.
rewrite <- rngl_squ_pow_2 in H1.
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hii) in H1.
rewrite (rngl_abs_0 Hop) in H1.
rewrite (rngl_abs_nonneg Hop Hor) in H1; [ easy | ].
apply rl_sqrt_nonneg, (rngl_le_refl Hor).
Qed.

Theorem angle_div_2_0 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  angle_div_2 0 = 0%A.
Proof.
intros Hic Hon Hop Hed.
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
rewrite (rl_sqrt_1 Hic Hon Hop Hid).
f_equal.
rewrite (rngl_sub_diag Hos).
rewrite (rngl_div_0_l Hos Hi1); [ | easy ].
apply (rl_sqrt_0 Hop Hic Hid).
Qed.

Theorem angle_leb_gt :
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 ≤? θ2)%A = false ↔ (θ2 < θ1)%A.
Proof.
intros Hed *.
progress unfold angle_leb.
progress unfold angle_lt.
progress unfold angle_compare.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs2.
  remember (rngl_cos θ2 ?= rngl_cos θ1)%L as cc eqn:Hcc.
  symmetry in Hcc.
  split; intros H12. {
    destruct cc; [ easy | easy | ].
    apply (rngl_compare_lt_iff Hor Hed).
    now apply (rngl_compare_gt_iff Hor Hed) in Hcc.
  } {
    destruct cc; [ | | easy ]. {
      apply (rngl_compare_eq_iff Hed) in Hcc.
      apply (rngl_compare_lt_iff Hor Hed) in H12.
      rewrite Hcc in H12.
      now apply (rngl_lt_irrefl Hor) in H12.
    } {
      apply (rngl_compare_lt_iff Hor Hed) in Hcc.
      apply (rngl_compare_lt_iff Hor Hed) in H12.
      now apply (rngl_lt_asymm Hor) in Hcc.
    }
  }
} {
  apply (rngl_leb_gt Hor) in Hzs1.
...
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
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
rewrite (rl_sqrt_div Hon Hop); [ | easy | easy ].
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
progress unfold angle_add_overflow in Haov.
apply (angle_ltb_ge Hed) in Haov.
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
      progress unfold angle_le in Haov.
      progress unfold angle_compare in Haov.
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
...
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

...

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
  }
*)
