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

(* to be completed
Declare Scope angle_scope.
Delimit Scope angle_scope with A.

Notation "a + b" := (angle_add a b) : angle_scope.
Notation "n * a" := (angle_mul_nat a n) : angle_scope.

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

Theorem angle_ltb_ge :
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 <? θ2)%A = false ↔ (θ2 ≤ θ1)%A.
Proof.
intros Hed *.
progress unfold angle_ltb.
progress unfold angle_le.
progress unfold angle_compare.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (rngl_cos θ2 ?= rngl_cos θ1)%L as c21 eqn:Hc21.
remember (rngl_cos θ1 ?= rngl_cos θ2)%L as c12 eqn:Hc12.
symmetry in Hzs1, Hzs2, Hc21, Hc12.
split; intros H12. {
  destruct zs1. {
    destruct zs2; [ | easy ].
    destruct c12; [ easy | easy | exfalso ].
    destruct c21; [ | easy | ]. {
      apply (rngl_compare_eq_iff Hed) in Hc21.
      apply (rngl_compare_gt_iff Hor Hed) in Hc12.
      rewrite Hc21 in Hc12.
      now apply (rngl_lt_irrefl Hor) in Hc12.
    } {
      apply (rngl_compare_gt_iff Hor Hed) in Hc21, Hc12.
      now apply (rngl_lt_asymm Hor) in Hc12.
    }
  } {
    destruct zs2; [ easy | ].
    destruct c21; [ easy | easy | exfalso ].
    apply (rngl_compare_gt_iff Hor Hed) in Hc21.
    destruct c12; [ | easy | ]. {
      apply (rngl_compare_eq_iff Hed) in Hc12.
      rewrite Hc12 in Hc21.
      now apply (rngl_lt_irrefl Hor) in Hc21.
    } {
      apply (rngl_compare_gt_iff Hor Hed) in Hc12.
      now apply (rngl_lt_asymm Hor) in Hc12.
    }
  }
}
...
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
...
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
