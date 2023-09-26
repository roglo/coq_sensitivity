(* Real-Like numbers *)
(* Algebraic structure having the same properties as real numbers *)
(* and complex numbers *)
(* see also Quaternions.v *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike Main.IterAdd.
Require Import Init.Nat.
Require Import IntermVal.

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

Definition is_derivative f f' :=
  ∀ a, is_limit_when_tending_to (λ x, (f x - f a) / (x - a))%L a (f' a).

End a.

(* angles; personal idea *)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* in this vision, an angle is not a real but a pair of reals (x,y)
   such that x²+y²=1; the cosinus is then x and the sinus is y.
   The property sin²+cos²=1 is by definition. It is possible to
   add angles (see below) and we inherit the properties of
   cos(x+y) and sin(x+y) in an obvious way. *)

Definition cos2_sin2_prop x y :=
  (negb
     (rngl_has_1 T && rngl_has_opp T && rngl_mul_is_comm T &&
      rngl_has_eq_dec T) ||
   (x² + y² =? 1)%L)%bool = true.

Record angle := mk_ang
  { rngl_cos : T;
    rngl_sin : T;
    rngl_cos2_sin2 : cos2_sin2_prop rngl_cos rngl_sin }.

Theorem eq_angle_eq : ∀ a b,
  (rngl_cos a, rngl_sin a) = (rngl_cos b, rngl_sin b) ↔ a = b.
Proof.
intros.
split; intros Hab; [ | now subst b ].
injection Hab; clear Hab; intros Hs Hc.
destruct a as (aco, asi, Hacs).
destruct b as (bco, bsi, Hbcs).
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
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
progress unfold rngl_squ.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
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
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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

End a.

Arguments angle T {ro rp}.

(* end angles *)

Class real_like_prop T {ro : ring_like_op T} {rp : ring_like_prop T} :=
  { rl_has_integral_modulus : bool;
    rl_nth_root : nat → T → T;
    rl_opt_integral_modulus_prop :
      if rl_has_integral_modulus then
        ∀ a b : T, (rngl_squ a + rngl_squ b = 0 → a = 0 ∧ b = 0)%L
      else not_applicable;
    rl_nth_root_pow : ∀ n a, (0 ≤ a → rl_nth_root n a ^ n = a)%L;
    rl_nth_root_mul :
      ∀ n a b, (0 ≤ a)%L → (0 ≤ b)%L →
      (rl_nth_root n a * rl_nth_root n b = rl_nth_root n (a * b))%L;
    rl_sqrt_nonneg : ∀ a, (0 ≤ a → 0 ≤ rl_nth_root 2 a)%L }.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition rl_sqrt := rl_nth_root 2.
Notation "'√' a" := (rl_sqrt a) (at level 1, format "√ a") : ring_like_scope.

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

Theorem rngl_squ_sqrt : ∀ a, (0 ≤ a)%L → rngl_squ (rl_sqrt a) = a.
Proof.
intros.
now apply (rl_nth_root_pow 2 a).
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
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
destruct a as (ca, sa, Ha); cbn.
progress unfold cos2_sin2_prop in Ha.
cbn in Ha.
rewrite Hon, Hop, Hic, Hed in Ha; cbn in Ha.
apply (rngl_eqb_eq Hed) in Ha.
assert (H : (ca² ≤ 1)%L). {
  rewrite <- Ha.
  apply (rngl_le_add_r Hor).
  apply (rngl_square_ge_0 Hop Hor).
}
replace 1%L with 1²%L in H. 2: {
  apply (rngl_mul_1_l Hon).
}
rewrite <- (rngl_squ_abs Hop ca) in H.
rewrite <- (rngl_squ_abs Hop 1%L) in H.
apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in H. 2: {
  rewrite (rngl_abs_1 Hon Hop Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
rewrite (rngl_abs_1 Hon Hop Hor) in H.
now apply (rngl_abs_le Hop Hor) in H.
Qed.

Theorem angle_div_2_prop :
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_is_ordered T = true →
  ∀ a (ε := (if (0 ≤? rngl_sin a)%L then 1%L else (-1)%L)),
  cos2_sin2_prop
    (ε * √((1 + rngl_cos a) / 2))%L
    (√((1 - rngl_cos a) / 2)%L).
Proof.
intros Hiv Hc2 Hor *.
progress unfold cos2_sin2_prop.
remember (rngl_has_1 T) as on eqn:Hon; symmetry in Hon.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
remember (rngl_has_eq_dec T) as ed eqn:Hed; symmetry in Hed.
destruct on; [ | easy ].
destruct op; [ | easy ].
destruct ic; [ | easy ].
destruct ed; [ cbn | easy ].
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
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

Definition angle_div_2 Hiv Hc2 Hor a :=
  let ε := if (0 ≤? rngl_sin a)%L then 1%L else (-1)%L in
  {| rngl_cos := (ε * rl_sqrt ((1 + rngl_cos a) / 2))%L;
     rngl_sin := (rl_sqrt ((1 - rngl_cos a) / 2))%L;
     rngl_cos2_sin2 := angle_div_2_prop Hiv Hc2 Hor a |}.

Theorem angle_div_2_mul_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ (Hiv : rngl_has_inv T = true)
    (Hc2 : rngl_characteristic T ≠ 2)
    (Hor : rngl_is_ordered T = true),
  ∀ a,
  angle_mul_nat (angle_div_2 Hiv Hc2 Hor a) 2 = a.
Proof.
intros Hic Hon Hop Hed *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
apply eq_angle_eq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  do 2 rewrite (H1 (rngl_cos _)).
  do 2 rewrite (H1 (rngl_sin _)).
  easy.
}
move Hc1 after Hc2.
assert (H20 : 2%L ≠ 0%L). {
  remember (rngl_characteristic T) as ch eqn:Hch; symmetry in Hch.
  destruct ch. {
    specialize (rngl_characteristic_0 Hon Hch 1) as H1.
    cbn in H1.
    now rewrite rngl_add_0_r in H1.
  }
  destruct ch; [ easy | ].
  destruct ch; [ easy | ].
  specialize rngl_opt_characteristic_prop as H1.
  rewrite Hon in H1.
  rewrite Hch in H1.
  cbn - [ rngl_of_nat ] in H1.
  destruct H1 as (H1, H2).
  specialize (H1 2); cbn in H1.
  rewrite rngl_add_0_r in H1.
  apply H1.
  split; [ easy | ].
  do 2 apply -> Nat.succ_lt_mono.
  easy.
}
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
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
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
rewrite rl_nth_root_mul; cycle 1. {
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
rewrite <- rl_nth_root_mul; cycle 1. {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
} {
  apply (rngl_square_ge_0 Hop Hor).
}
rewrite <- rl_nth_root_mul; [ | easy | easy ].
assert (Hz2 : (0 ≤ 2⁻¹)%L). {
  apply (rngl_lt_le_incl Hor).
  apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite <- rl_nth_root_mul; [ | easy | easy ].
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
rewrite rl_nth_root_mul; [ | easy | easy ].
rewrite (rngl_mul_comm Hic (1 - _)%L).
rewrite <- (rngl_squ_sub_squ Hop Hic).
progress unfold rngl_squ at 1.
rewrite (rngl_mul_1_r Hon).
destruct a as (ca, sa, Ha); cbn in ε, Hz1ac, Hz1sc |-*.
progress unfold cos2_sin2_prop in Ha.
rewrite Hon, Hop, Hic, Hed in Ha; cbn in Ha.
apply (rngl_eqb_eq Hed) in Ha.
rewrite <- Ha, rngl_add_comm, (rngl_add_sub Hos).
progress unfold rngl_squ.
progress unfold ε.
remember (0 ≤? sa)%L as saz eqn:Hsaz; symmetry in Hsaz.
destruct saz. {
  apply rngl_leb_le in Hsaz.
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rl_nth_root_pow 2); [ | easy ].
  now rewrite <- rl_nth_root_mul.
} {
  apply (rngl_leb_gt Hor) in Hsaz.
  apply (rngl_opp_lt_compat Hop Hor) in Hsaz.
  rewrite (rngl_opp_0 Hop) in Hsaz.
  apply (rngl_lt_le_incl Hor) in Hsaz.
  rewrite <- (rngl_mul_opp_opp Hop sa).
  rewrite <- rl_nth_root_mul; [ | easy | easy ].
  apply (rngl_opp_inj Hop).
  rewrite <- (rngl_mul_opp_l Hop).
  rewrite (rngl_opp_involutive Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rl_nth_root_pow 2); [ | easy ].
  easy.
}
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
  apply (rngl_opp_le_compat Hop Hor) in Haz.
  rewrite (rngl_opp_0 Hop) in Haz.
  rewrite <- (rngl_mul_opp_opp Hop).
  rewrite <- rl_nth_root_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite rngl_squ_pow_2.
  now apply rl_nth_root_pow.
} {
  apply (rngl_leb_gt Hor) in Haz.
  apply (rngl_lt_le_incl Hor) in Haz.
  rewrite <- rl_nth_root_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite rngl_squ_pow_2.
  now apply rl_nth_root_pow.
}
Qed.

Definition angle_eqb a b :=
  ((rngl_cos a =? rngl_cos b)%L && (rngl_sin a =? rngl_sin b)%L)%bool.

Definition angle_leb a b :=
  if (0 ≤? rngl_sin a)%L then
    if (0 ≤? rngl_sin b)%L then (rngl_cos b ≤? rngl_cos a)%L
    else true
  else
    if (0 ≤? rngl_sin b)%L then false
    else (rngl_cos a ≤? rngl_cos b)%L.

Definition angle_ltb a b :=
  (angle_leb a b && negb (angle_eqb a b))%bool.

Theorem rl_sqrt_0 :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  rl_sqrt 0%L = 0%L.
Proof.
intros Hop Hic Hor Hii.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
 rl_sqrt 1%L = 1%L.
Proof.
intros Hic Hon Hop Hiv Hor Hii.
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

Theorem angle_mul_2_div_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ (Hiv : rngl_has_inv T = true)
    (Hc2 : rngl_characteristic T ≠ 2)
    (Hor : rngl_is_ordered T = true),
  ∀ a,
  angle_div_2 Hiv Hc2 Hor (angle_mul_nat a 2) =
    if angle_ltb a angle_straight then a else angle_add a angle_straight.
Proof.
intros Hic Hon Hop Hed *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_and_1_or_quot_iff.
  now rewrite Hiv, Hon; left.
}
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
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
apply eq_angle_eq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now do 2 rewrite (H1 (rngl_cos _)), (H1 (rngl_sin _)).
}
move Hc1 after Hc2.
assert (H20 : 2%L ≠ 0%L). {
  remember (rngl_characteristic T) as ch eqn:Hch; symmetry in Hch.
  destruct ch. {
    specialize (rngl_characteristic_0 Hon Hch 1) as H1.
    cbn in H1.
    now rewrite rngl_add_0_r in H1.
  }
  destruct ch; [ easy | ].
  destruct ch; [ easy | ].
  specialize rngl_opt_characteristic_prop as H1.
  rewrite Hon in H1.
  rewrite Hch in H1.
  cbn - [ rngl_of_nat ] in H1.
  destruct H1 as (H1, H2).
  specialize (H1 2); cbn in H1.
  rewrite rngl_add_0_r in H1.
  apply H1.
  split; [ easy | ].
  do 2 apply -> Nat.succ_lt_mono.
  easy.
}
(**)
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
  apply Bool.andb_true_iff in Hap.
  destruct Hap as (Hal, Hae).
  apply Bool.negb_true_iff in Hae.
  progress unfold angle_leb in Hal.
  progress unfold angle_eqb in Hae.
  apply Bool.andb_false_iff in Hae.
  cbn in Hal, Hae.
  rewrite (rngl_leb_refl Hor) in Hal.
  destruct a as (ca, sa, Ha); cbn in ε, Hal, Hae |-*.
  remember (0 ≤? sa)%L as zs eqn:Hzs; symmetry in Hzs.
  destruct zs; [ clear Hal | easy ].
  apply rngl_leb_le in Hzs.
  progress unfold cos2_sin2_prop in Ha.
  rewrite Hon, Hop, Hic, Hed in Ha; cbn in Ha.
  apply (rngl_eqb_eq Hed) in Ha.
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
    destruct Hae as [Hae| Hae]. {
      apply (rngl_eqb_neq Hed) in Hae.
      destruct (rngl_eq_dec Hed sa 0) as [Hsz| Hsz]. {
        subst sa.
        rewrite (rngl_squ_0 Hos) in Ha.
        rewrite (rngl_sub_0_r Hos) in Ha.
        symmetry in Ha.
        rewrite <- (rngl_squ_1 Hon) in Ha.
        apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hid) in Ha.
        rewrite (rngl_abs_1 Hon Hop Hor) in Ha.
        progress unfold rngl_abs in Ha.
        remember (ca ≤? 0)%L as cz eqn:Hcz; symmetry in Hcz.
        destruct cz. {
          apply (f_equal rngl_opp) in Ha.
          now rewrite (rngl_opp_involutive Hop) in Ha.
        } {
          rewrite Ha.
          apply (rngl_0_le_1 Hon Hop Hor).
        }
      }
      rewrite (rngl_mul_comm Hic) in Hzsc.
      apply (rngl_le_div_l Hon Hop Hiv Hor) in Hzsc. 2: {
        apply not_eq_sym in Hsz.
        now apply (rngl_lt_iff Hor).
      }
      now rewrite (rngl_div_0_l Hos Hi1) in Hzsc.
    }
    apply (rngl_eqb_neq Hed) in Hae.
    rewrite (rngl_mul_comm Hic) in Hzsc.
    apply (rngl_le_div_l Hon Hop Hiv Hor) in Hzsc. 2: {
      apply not_eq_sym in Hae.
      now apply (rngl_lt_iff Hor).
    }
    now rewrite (rngl_div_0_l Hos Hi1) in Hzsc.
  } {
    apply (rngl_opp_inj Hop).
    rewrite <- (rngl_mul_opp_l Hop).
    rewrite (rngl_opp_involutive Hop).
    rewrite (rngl_mul_1_l Hon).
    apply (rngl_abs_nonpos Hop Hor).
    apply (rngl_leb_gt Hor) in Hzsc.
    apply (rngl_mul_lt_mono_pos_l Hop Hor Hii 2⁻¹%L) in Hzsc. 2: {
      apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    rewrite (rngl_mul_0_r Hos) in Hzsc.
    do 2 rewrite rngl_mul_assoc in Hzsc.
    rewrite (rngl_mul_inv_l Hon Hiv) in Hzsc; [ | easy ].
    rewrite (rngl_mul_1_l Hon) in Hzsc.
    apply (rngl_nle_gt Hor) in Hzsc.
    apply (rngl_nlt_ge Hor).
    intros Hca; apply Hzsc; clear Hzsc.
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  }
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
  apply Bool.andb_false_iff in Hap.
(**)
  progress unfold angle_leb in Hap.
  progress unfold angle_eqb in Hap.
  cbn in Hap.
  rewrite (rngl_leb_refl Hor) in Hap.
  remember (0 ≤? rngl_sin a)%L as zs eqn:Hzs; symmetry in Hzs.
  destruct zs. {
    destruct Hap as [Hap| Hap]. {
      apply (rngl_leb_gt Hor) in Hap.
      apply (rngl_nle_gt Hor) in Hap.
      exfalso; apply Hap; clear Hap.
      apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
    } {
      apply Bool.negb_false_iff in Hap.
      apply Bool.andb_true_iff in Hap.
      destruct Hap as (Hac, Has).
      apply (rngl_eqb_eq Hed) in Hac, Has.
      progress unfold ε.
      rewrite Hac, Has.
      rewrite (rngl_squ_0 Hos).
      rewrite (rngl_mul_0_r Hos).
      rewrite (rngl_mul_0_l Hos).
      rewrite (rngl_leb_refl Hor).
      rewrite (rngl_mul_1_l Hon).
      do 2 rewrite (rngl_sub_0_r Hos).
      rewrite rngl_add_0_l.
      rewrite (rngl_squ_opp Hop).
      rewrite (rngl_squ_1 Hon).
      rewrite (rngl_div_diag Hon Hiq); [ | easy ].
      rewrite (rngl_sub_diag Hos).
      rewrite (rngl_div_0_l Hos Hi1); [ | easy ].
      rewrite fold_rngl_squ.
      rewrite (rngl_squ_opp Hop).
      rewrite (rngl_squ_1 Hon).
      rewrite (rl_sqrt_0 Hop Hic Hor Hid).
      rewrite (rl_sqrt_1 Hic Hon Hop Hiv Hor Hid).
      easy.
    }
  } {
    apply (rngl_leb_gt Hor) in Hzs.
    clear Hap.
    destruct a as (ca, sa, Ha); cbn in Hzs, ε |-*.
    progress unfold cos2_sin2_prop in Ha.
    rewrite Hon, Hop, Hic, Hed in Ha; cbn in Ha.
    apply (rngl_eqb_eq Hed) in Ha.
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
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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

Arguments rl_acos Hor x%L.

Theorem rl_cos_acos : ∀ Hor x, (x² ≤ 1)%L → rngl_cos (rl_acos Hor x) = x.
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

End a.

Fixpoint gc_power_nat {T} {ro : ring_like_op T} (z : GComplex T) n :=
  match n with
  | 0 => gc_one
  | S n' => gc_mul z (gc_power_nat z n')
  end.

Arguments rl_sqrt {T ro rp rl} _%L.

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
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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
  rngl_has_inv T = true →
  rl_has_integral_modulus T = true →
  ∀ a : GComplex T, a ≠ 0%L →
  gre a⁻¹ = (gre a / (gre a * gre a + gim a * gim a))%L.
Proof.
intros * Hic Hiv Hrl * Haz.
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
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
  rngl_has_inv T = true →
  rl_has_integral_modulus T = true →
  ∀ a : GComplex T, a ≠ 0%L →
  gim a⁻¹ = (- gim a / (gre a * gre a + gim a * gim a))%L.
Proof.
intros * Hic Hiv Hrl * Haz.
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
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
assert (Hiv : rngl_has_inv T = true). {
  progress unfold rngl_has_inv in Hivc; cbn in Hivc.
  progress unfold gc_opt_inv_or_quot in Hivc.
  progress unfold rngl_has_inv.
  destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
  now destruct iq.
}
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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
rewrite (gc_inv_re Hic Hiv Hrl); [ | now intros H; subst a ].
rewrite (gc_inv_im Hic Hiv Hrl); [ | now intros H; subst a ].
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
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_characteristic T ≠ 2 →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ b → a ≤ rl_sqrt (rngl_squ a + b))%L.
Proof.
intros * Hon Hop Hiv Heb Hc2 Hor * Hzb.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_and_1_or_quot_iff.
  now rewrite Hiv, Hon; left.
}
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
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 2 →
  rl_has_integral_modulus T = true →
  ∀ x y, (x ≠ 0 ∨ y ≠ 0)%L →
  (-1 ≤ x / rl_sqrt (rngl_squ x + rngl_squ y) ≤ 1)%L.
Proof.
intros * Hon Hop Hiv Hed Hor Hc2 Hmi * Hxyz.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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
    apply (le_rl_sqrt_add Hon Hop Hiv Hed Hc2 Hor).
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
    apply (le_rl_sqrt_add Hon Hop Hiv Hed Hc2 Hor).
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

Theorem polar :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_characteristic T ≠ 2 →
  rl_has_integral_modulus T = true →
  ∀ (Hor : rngl_is_ordered T = true),
  ∀ (z : GComplex T) ρ θ,
  ρ = √((gre z)² + (gim z)²)%L
  → θ =
       (if (0 ≤? gim z)%L then rl_acos Hor (gre z / ρ)%L
        else angle_opp (rl_acos Hor (gre z / ρ)%L))
  → z = mk_gc (ρ * rngl_cos θ) (ρ * rngl_sin θ).
Proof.
intros * Hic Hon Hop Hiv Hed Hc2 Hmi * Hρ Hθ.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_and_1_or_quot_iff.
  now left; rewrite Hiv, Hon.
}
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
  (* TODO: lemma √0=0 *)
  progress unfold rl_sqrt in Hρ.
  specialize (rl_nth_root_pow 2 0%L) as H1.
  rewrite <- Hρ in H1.
  apply (rngl_integral Hos Hid) in H1. 2: {
    apply (rngl_le_refl Hor).
  }
  assert (H2 : ρ = 0%L) by now destruct H1.
  rewrite H2.
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

(* to be completed
   attempt to define the decimals of a number using rngl_int
   (integer part of a positive number), which supposes that
   T is ordered and archimedean, and that rngl_int is defined
   in RingLike.v which is not at the time I write this comment
     rngl_int : T → nat
     rngl_opt_int_prop :
       if (rngl_is_ordered T && rngl_is_archimedean T)%bool then
         ∀ x, (rngl_of_nat (rngl_int x) ≤ x < rngl_of_nat (rngl_int x + 1))%L
       else not_applicable;
   Interesting but what do I do with the theorem int_part defined
   in IntermVal.v ?
     A generalization of nth_dec_of_rat ant partial_sum_of_inv_power
   below where x is the rational a/b

About int_part.
...

Definition nth_dec rngl_int rad x n :=
  rngl_int (x * rngl_of_nat rad ^ n)%L mod rad.

Definition partial_sum_of_inv_power (rad : nat) (x : T) (n : nat) :=
  let u := nth_dec rad x in
  ∑ (i = 1, n), rngl_of_nat (u i) / rngl_of_nat rad ^ i.
*)

(* nth decimal (in radix rad) of rational p/q *)
Definition nth_dec_of_rat rad a b n :=
  (a * rad ^ n / b) mod rad.

Definition partial_sum_of_inv_power (rad a b n : nat) :=
  let u := nth_dec_of_rat rad a b in
  ∑ (i = 1, n), rngl_of_nat (u i) / rngl_of_nat rad ^ i.

(*
Fixpoint nth_dec_of_rat rad a b n :=
  match n with
  | 0 => rad * a / b
  | S n' =>
      let r := (rad * a) mod b in
      nth_dec_of_rat rad r b n'
  end.
*)

(* first n decimals (in radix rad) of rational p/q
   where 0 ≤ p/q ≤ 1
Fixpoint first_dec_of_rat rad a b n :=
  match n with
  | 0 => []
  | S n' =>
      let q := rad * a / b in
      let r := (rad * a) mod b in
      q :: first_dec_of_rat rad r b n'
  end.

Compute (
  let rad := 10 in
  let a := 6 in
  let b := 7 in
  let n := 0 in
  (first_dec_of_rat rad a b (S n),
   nth_dec_of_rat rad a b n,
   nth_dec_of_rat' rad a b n)).

Definition partial_sum_of_inv_power (rad a b n : nat) :=
  let u := first_dec_of_rat rad a b n in
  ∑ (i = 1, n), rngl_of_nat u.(i) / rngl_of_nat rad ^ i.

Definition partial_sum_of_inv_power (rad a b n : nat) :=
  let u := nth_dec_of_rat rad a b in
  ∑ (i = 1, n), rngl_of_nat (u (i - 1)%nat) / rngl_of_nat rad ^ i.
*)

Declare Scope angle_scope.
Delimit Scope angle_scope with A.

Notation "a + b" := (angle_add a b) : angle_scope.
Notation "n * a" := (angle_mul_nat a n) : angle_scope.

Arguments rngl_cos {T ro rp} a%A.
Arguments rngl_sin {T ro rp} a%A.

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

Theorem partial_sum_of_inv_power_succ :
  ∀ rad a b n,
  partial_sum_of_inv_power rad a b (S n) =
  (partial_sum_of_inv_power rad a b n +
     rngl_of_nat (nth_dec_of_rat rad a b (S n)) / rngl_of_nat rad ^ S n)%L.
Proof.
intros.
progress unfold partial_sum_of_inv_power.
rewrite rngl_summation_split_last; [ | now apply -> Nat.succ_le_mono ].
destruct n. {
  rewrite rngl_summation_empty; [ | easy ].
  now rewrite rngl_summation_empty.
}
rewrite (rngl_summation_shift 1). 2: {
  split; [ now apply -> Nat.succ_le_mono | ].
  now do 2 apply -> Nat.succ_le_mono.
}
f_equal.
rewrite (Nat_sub_succ_1 (S n)).
apply rngl_summation_eq_compat.
intros i Hi.
now rewrite Nat.add_comm, Nat.add_sub.
Qed.

(* to be completed
(* e.g. 1/5 = 1/8 + 1/16 + 1/128 + 1/256 + ...
   corresponding to 1/5 written in binary, which is
     [0; 0; 1; 1; 0; 0; 1; 1; 0; 0]
*)
Theorem inv_is_inf_sum_of_inv_pow_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  rngl_is_archimedean T = true →
  ∀ rad a b,
  rngl_of_nat rad ≠ 0%L
  → rngl_of_nat b ≠ 0%L
  → is_limit_when_tending_to_inf (partial_sum_of_inv_power rad a b)
       (rngl_of_nat a / rngl_of_nat b)%L.
Proof.
intros Hic Hon Hop Hiv Hor Har * Hrz Hbz.
intros ε Hε.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_and_1_or_quot_iff.
  now rewrite Hiv, Hon; left.
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
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (int_part Hon Hop Hc1 Hor Har) as H1.
destruct (H1 (1 / ε)%L) as (N, HN).
clear H1.
(*
exists (S (S (Nat.log2_up N))).
*)
exists (2 ^ S (Nat.log2_up N)).
(**)
intros m Hm.
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
eapply (rngl_le_lt_trans Hor); [ | apply Hnε ].
clear ε Hε HN Hnε.
(**)
progress unfold partial_sum_of_inv_power.
progress unfold nth_dec_of_rat.
...
rewrite (rngl_abs_nonpos Hop Hor). 2: {
  apply (rngl_le_sub_0 Hop Hor).
  clear Hm.
  (* lemma to do *)
  progress unfold partial_sum_of_inv_power.
(**)
  progress unfold nth_dec_of_rat.
  induction m. {
    rewrite rngl_summation_empty; [ | easy ].
    apply (rngl_div_pos Hon Hop Hiv Hor). 2: {
      rewrite <- rngl_of_nat_0.
      apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
      apply Nat.neq_0_lt_0.
      now intros H; subst b.
    }
    apply (rngl_of_nat_nonneg Hon Hop Hor).
  }
  destruct m. {
    rewrite rngl_summation_only_one.
    cbn.
    rewrite Nat.mul_1_r.
    destruct b; [ easy | ].
    destruct b. {
      rewrite Nat.div_1_r.
      rewrite Nat.mod_mul; [ | now intros H; subst rad ].
      rewrite rngl_of_nat_1.
      rewrite (rngl_div_1_r Hon Hiq Hc1).
      rewrite (rngl_div_0_l Hos Hi1); [ | easy ].
      apply (rngl_of_nat_nonneg Hon Hop Hor).
    }
    destruct b. {
      cbn - [ "/" ].
      rewrite rngl_add_0_r.
...
      apply (rngl_le_refl Hor).
    }
    rewrite Nat.div_small; [ | now do 2 apply -> Nat.succ_lt_mono ].
    rewrite Nat.mod_0_l; [ | easy ].
    rewrite rngl_of_nat_0.
    rewrite (rngl_div_0_l Hos Hi1). 2: {
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    apply (rngl_div_pos Hon Hop Hiv Hor). 2: {
      rewrite <- rngl_of_nat_0.
      now apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
    }
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  destruct m. {
...
  eapply (rngl_le_trans Hor). {
    apply (rngl_summation_le_compat Hor) with
      (h := λ i, (1 / rngl_of_nat 2 ^ i)%L).
    intros i Hi.
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_mul_le_mono_nonneg_r Hop Hor). {
      apply (rngl_mul_le_mono_pos_l Hop Hor Hii) with
        (c := (rngl_of_nat 2 ^ i)%L). {
        apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
        cbn; rewrite rngl_add_0_r.
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      rewrite (rngl_mul_0_r Hos).
      rewrite (rngl_mul_inv_r Hon Hiv). 2: {
        apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
        cbn; rewrite rngl_add_0_r.
        apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
      }
      apply (rngl_0_le_1 Hon Hop Hor).
    }
    rewrite <- rngl_of_nat_1.
    apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
    progress unfold nth_dec_of_rat.
    apply Nat.lt_succ_r.
    now apply Nat.mod_upper_bound.
  }
(* ah bin non, ça marche pas du tout, ça *)
...
}
rewrite (rngl_opp_sub_distr Hop).
(*
apply (rngl_le_sub_le_add_r Hop Hor).
*)
revert N Hm.
induction m; intros. {
  apply Nat.le_0_r in Hm.
  now apply Nat.pow_eq_0 in Hm.
}
rewrite partial_sum_of_inv_power_succ.
prewrite (rngl_sub_add_distr Hos).
apply (rngl_le_sub_le_add_r Hop Hor).
destruct N. {
  admit. (* à voir *)
}
eapply (rngl_le_trans Hor). {
  specialize (Nat.log2_up_succ_or N) as H1.
  destruct H1 as [H1| H1]. {
    apply (IHm N).
    apply Nat.succ_le_mono.
    eapply Nat.le_trans; [ | apply Hm ].
    rewrite H1.
    admit.
  }
Search (Nat.log2_up (S _)).
...
}
apply (rngl_le_sub_le_add_l Hop Hor).
progress unfold nth_dec_of_rat.
rewrite Nat.mul_1_l.
(* faut voir... *)
...
progress unfold partial_sum_of_inv_power.
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hm.
rewrite rngl_summation_split_last; [ | now apply -> Nat.succ_le_mono ].
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hm.
rewrite (rngl_summation_shift 2). 2: {
  split; [ easy | ].
  now do 2 apply -> Nat.succ_le_mono.
}
rewrite Nat.sub_diag.
rewrite Nat.sub_succ.
rewrite Nat_sub_succ_1.
cbn - [ rngl_of_nat Nat.modulo ].
...
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  subst m.
  apply Nat.le_0_r in Hm.
  apply Nat.log2_up_null in Hm.
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_add_0_l.
  cbn - [ rngl_of_nat Nat.modulo ].
  rewrite (rngl_of_nat_add 1).
  rewrite rngl_of_nat_1.
  progress unfold nth_dec_of_rat.
  rewrite Nat.mul_1_l, Nat.pow_1_r.
  destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
    subst n.
    rewrite Nat.div_1_r.
    rewrite Nat.mod_same; [ | easy ].
    rewrite rngl_of_nat_0.
    rewrite (rngl_div_0_l Hos Hi1). 2: {
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    progress unfold rngl_sub.
    rewrite Hop.
    rewrite rngl_add_0_l.
    rewrite rngl_of_nat_1.
    rewrite (rngl_div_1_r Hon Hiq Hc1).
    rewrite (rngl_abs_opp Hop Hor).
    rewrite (rngl_abs_1 Hon Hop Hor).
    apply (rngl_le_div_r Hon Hop Hiv Hor). {
      rewrite <- rngl_of_nat_0.
      apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
      rewrite Nat.add_1_r.
      apply Nat.lt_0_succ.
    }
    destruct N. {
      cbn; rewrite rngl_add_0_r.
      rewrite (rngl_mul_1_l Hon).
      apply (rngl_le_refl Hor).
    }
    rewrite (rngl_mul_1_l Hon).
    apply Nat.succ_le_mono in Hm.
    destruct N; [ | easy ].
(* et paf ! ça marche pas *)
...
  rewrite Nat.mod_small. 2: {
    destruct n; [ easy | ].
...
    apply Nat.div_lt; [ easy | ].
    apply Nat.div_lt_upper_bound; [ easy | ].
...
  ============================
  (rngl_abs (rngl_of_nat (2 / n) / 2 - 1 / rngl_of_nat n) ≤ 1 / rngl_of_nat (N + 1))%L
  ============================
  (rngl_abs (rngl_of_nat ((2 / n) mod 2) / 2 - 1 / rngl_of_nat n) ≤ 1 / rngl_of_nat (N + 1))%L
  destruct N. {
    cbn; rewrite rngl_add_0_r.
    rewrite (rngl_div_diag Hon Hiq). 2: {
      now apply (rngl_1_neq_0_iff Hon).
    }
    destruct n; [ easy | ].
    cbn.
    destruct n; cbn. {
      rewrite rngl_add_0_r.
      rewrite (rngl_div_diag Hon Hiq). 2: {
        now apply (rngl_2_neq_0 Hon).
      }
      rewrite (rngl_div_diag Hon Hiq). 2: {
        now apply (rngl_1_neq_0_iff Hon).
      }
      rewrite (rngl_sub_diag Hos).
      rewrite (rngl_abs_0 Hop).
      apply (rngl_0_le_1 Hon Hop Hor).
    }
    destruct n; cbn.
...
  apply Nat.le_0_r in Hm.
  apply Nat.log2_up_null in Hm.
...
rewrite (rngl_summation_shift 1). 2: {
  split; [ now apply -> Nat.succ_le_mono | ].
  apply -> Nat.succ_le_mono.
  destruct m; [ | now apply -> Nat.succ_le_mono ].
  exfalso.
Search (_ < Nat.log2_up _).
...
revert N Hm.
induction m; intros; [ easy | ].
apply Nat.succ_le_mono in Hm.
destruct N. {
  rewrite Nat.add_0_l.
  rewrite rngl_of_nat_1.
  rewrite (rngl_div_diag Hon Hiq). 2: {
    now apply (rngl_1_neq_0_iff Hon).
  }
...
}
Search (Nat.log2_up (S _)).
specialize (Nat.log2_up_succ_or N) as H2.
destruct H2 as [H2| H2]. {
  rewrite H2 in Hm.
  specialize (IHm N Hm).
...
Theorem glop :
  ∀ rad a b n,
  ∃ d, 0 ≤ d < rad ∧
  first_dec_of_rat rad a b (S n) =
  first_dec_of_rat rad a b n ++ [d].
Proof.
...
rewrite glop.
...
cbn in Hm.
Search (Nat.log2_up (S _)).
...
remember (first_dec_of_rat 2 1 n m) as u eqn:Hu.
revert u Hu.
induction m as (m, IHm) using lt_wf_rec; intros.
destruct m; [ easy | ].
...
destruct (glop 2 1 n m) as (x & Hx2 & Hx).
destruct Hx2 as (_, Hx2).
rewrite Hx in Hu.
...
apply (Nat.pow_le_mono_r 2) in Hm; [ | easy ].
Search Nat.log2_up.
Search (_ ^ Nat.log2 _).
...
induction m; [ easy | ].
...
  rewrite rngl_summation_empty; [ | easy ].
  progress unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_add_0_l.
  rewrite (rngl_abs_nonpos Hop Hor). 2: {
    rewrite <- (rngl_opp_0 Hop).
    apply -> (rngl_opp_le_compat Hop Hor).
    apply (rngl_div_pos Hon Hop Hiv Hor). {
      apply (rngl_0_le_1 Hon Hop Hor).
    }
    rewrite <- rngl_of_nat_0.
    apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
    apply Nat.neq_0_lt_0.
    now intros H; subst n.
  }
  rewrite (rngl_opp_involutive Hop).
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    rewrite <- rngl_of_nat_0.
    apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
    apply Nat.neq_0_lt_0.
    now intros H; subst n.
  }
...
rewrite <- rngl_of_nat_1.
eapply (rngl_lt_le_trans Hor). {
  apply (partial_sum_of_inv_pow_lt Hon).
  apply Nat.le_succ_l.
  apply Nat.neq_0_lt_0.
  now intros H; subst n.
}
apply (rngl_le_div_l Hon Hop Hiv Hor). {
  apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
  cbn; rewrite rngl_add_0_r.
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite (rngl_mul_comm Hic).
apply (rngl_le_div_l Hon Hop Hiv Hor); [ easy | ].
eapply (rngl_le_trans Hor). {
  apply (rngl_lt_le_incl Hor).
  apply HN.
}
rewrite <- (rngl_of_nat_pow Hon Hos).
apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
apply (Nat.pow_le_mono_r 2) in Hm; [ | easy ].
eapply le_trans; [ | apply Hm ].
cbn; rewrite Nat.add_0_r.
apply Nat.add_le_mono. {
  destruct (Nat.eq_dec N 0) as [HNz| HNz]; [ now subst N | ].
  destruct (Nat.eq_dec N 1) as [HN1| HN1]; [ now subst N | ].
  apply Nat.log2_up_spec.
  destruct N; [ easy | ].
  destruct N; [ easy | ].
  now apply -> Nat.succ_lt_mono.
}
apply Nat.neq_0_lt_0.
now apply Nat.pow_nonzero.
...
apply -> (rngl_abs_lt Hop Hor).
...
rewrite (rngl_abs_nonpos Hop Hor). 2: {
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_0 Hop).
  rewrite (rngl_opp_sub_distr Hop).
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_lt_iff Hor).
    split; [ apply (rngl_of_nat_nonneg Hon Hop Hor) | ].
    now apply not_eq_sym.
  }
...
Theorem partial_sum_of_inv_pow_le :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ rad a b i n, (rngl_of_nat a < rngl_of_nat b)%L →
  (partial_sum_of_inv_pow rad a b (S i) n * rngl_of_nat rad ^ i ≤
     rngl_of_nat a / rngl_of_nat b)%L.
Proof.
intros Hon Hop Hiv Hor * Hab.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
revert rad a b i Hab.
induction n as (n, IHn) using lt_wf_rec; intros.
destruct n. {
  cbn.
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_div_pos Hon Hop Hiv Hor).
  apply (rngl_of_nat_nonneg Hon Hop Hor).
  apply (rngl_lt_iff Hor).
  split; [ apply (rngl_of_nat_nonneg Hon Hop Hor) | ].
  apply not_eq_sym.
  intros H; rewrite H in Hab.
  apply (rngl_nle_gt Hor) in Hab.
  apply Hab.
  apply (rngl_of_nat_nonneg Hon Hop Hor).
}
Theorem glop :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  ∀ rad a  b i n, rngl_of_nat rad ≠ 0%L → a < b →
  ∃ x, (x < 1 ∧
  partial_sum_of_inv_pow rad a b (S i) (S n) =
    partial_sum_of_inv_pow rad a b (S i) n + x)%L.
Proof.
intros Hon Hop Hiv Hor Hc1 * Hrz Hab.
...
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
revert rad a b i Hrz Hab.
induction n as (n, IHn) using lt_wf_rec; intros.
destruct n. {
  remember (S i) as si; cbn; subst si.
  exists (rngl_of_nat (rad * a / b) / rngl_of_nat rad ^ S i)%L.
  split; [ | now rewrite rngl_add_0_r, rngl_add_0_l ].
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
    apply (rngl_nle_gt Hor).
    intros H; apply Hrz; clear Hrz.
    apply (rngl_le_antisymm Hor); [ easy | ].
    apply (rngl_of_nat_nonneg Hon Hop Hor).
  }
  rewrite (rngl_mul_1_l Hon).
  induction i. {
    apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
    apply Nat.div_lt_upper_bound; [ now intros H; subst b | ].
    rewrite Nat.mul_comm.
    apply Nat.mul_lt_mono_pos_r; [ | easy ].
    apply Nat.neq_0_lt_0.
    now intros H; subst rad.
  }
  eapply (rngl_lt_le_trans Hor); [ apply IHi | ].
  rewrite <- (rngl_mul_1_l Hon (_ ^ S i)%L).
  remember (S i) as si; cbn; subst si.
  apply (rngl_mul_le_mono_nonneg_r Hop Hor). 2: {
    rewrite <- rngl_of_nat_1.
    apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
    apply Nat.nlt_ge.
    intros H.
    now apply Nat.lt_1_r in H; subst rad.
  }
  rewrite <- (rngl_of_nat_pow Hon Hos).
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
  apply Nat_pow_nonneg.
}
specialize (IHn n (Nat.lt_succ_diag_r _) rad a b i Hrz Hab).
destruct IHn as (x & Hx1 & Hx).
... ...
  specialize (partial_sum_of_inv_pow_le 2 1 n 0 m) as H2.
  cbn in H2.
  now rewrite (rngl_mul_1_r Hon), rngl_add_0_r in H2.
}
...
Print first_dec_of_rat.
Print partial_sum_of_inv_power.
Theorem glop :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ rad d a b n, d ≠ 0 → a < b →
  (partial_sum_of_inv_power rad d (first_dec_of_rat rad a b n) *
     rngl_of_nat b * rngl_of_nat rad ^ (d - 1) ≤ rngl_of_nat a)%L.
Proof.
intros Hon Hop Hor * Hdz Hab.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
revert d a b Hdz Hab.
induction n; intros. {
  cbn.
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_of_nat_nonneg Hon Hop Hor).
}
cbn.
...
Theorem glop :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ d p q n m,
  p ≤ q
  → rngl_of_nat d ≠ 0%L
  → rngl_of_nat q ≠ 0%L
  → (rngl_of_nat p / rngl_of_nat q -
      partial_sum_of_inv_power d m (first_dec_of_rat d p q n) ≤
        1 / rngl_of_nat (d ^ n))%L.
Proof.
intros Hon Hop Hiv Hor * Hpq Hdz Hqz.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_and_1_or_quot_iff.
  now rewrite Hiv, Hon; left.
}
assert
  (Hii :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1.
  rewrite (H1 (_ - _)%L).
  apply (rngl_le_refl Hor).
}
apply (rngl_le_sub_le_add_l Hop Hor).
(*
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]. {
  subst p; cbn.
  rewrite (rngl_div_0_l Hos Hi1); [ | easy ].
  progress unfold rngl_sub.
  rewrite Hop, rngl_add_0_l.
...
  apply (rngl_le_trans Hor _ 0). 2: {
    apply (rngl_le_div_r Hon Hop Hiv Hor). 2: {
      rewrite (rngl_mul_0_l Hos).
      apply (rngl_0_le_1 Hon Hop Hor).
    }
    apply (rngl_lt_iff Hor).
    split; [ apply (rngl_of_nat_nonneg Hon Hop Hor) | ].
    apply not_eq_sym.
...
Search (rngl_of_nat _ = 0)%L.
    rewrite <- rngl_of_nat_0.
    intros H.
    apply (rngl_of_nat_inj Hon Hos) in H.
    apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
  }
    apply rngl_
...
  rewrite first_bits_of_rat_0_l; [ | now intros H; subst q ].
...
  revert m.
  induction n; intros; [ apply (rngl_le_refl Hor) | ].
  cbn.
  rewrite (rngl_div_0_l Hos Hi1). 2: {
    now apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
  }
  rewrite rngl_add_0_l.
  apply IHn.
}
*)
induction n. {
  cbn.
  rewrite rngl_add_0_l, rngl_add_0_r.
  rewrite (rngl_div_1_r Hon Hiq Hc1).
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    apply (rngl_lt_iff Hor).
    split; [ apply (rngl_of_nat_nonneg Hon Hop Hor) | ].
    now apply not_eq_sym.
  }
  rewrite (rngl_mul_1_l Hon).
  now apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
}
Theorem glop :
  ∀ d p q n, d ≠ 0 → p < q → ∃ a, a < d ∧
  partial_sum_of_inv_power d 1 (first_dec_of_rat d p q (S n)) =
  (partial_sum_of_inv_power d 1 (first_dec_of_rat d p q n) +
     rngl_of_nat a / rngl_of_nat (d ^ S n))%L.
Proof.
intros * Hdz Hpq.
induction n. {
  cbn.
  rewrite rngl_add_0_r.
  rewrite Nat.mul_1_r.
  destruct d; [ easy | clear Hdz ].
  cbn.
  exists ((p + d * p) / q).
  split. 2: {
    now rewrite rngl_add_0_l.
  }
  apply Nat.div_lt_upper_bound. {
    now intros H; subst q.
  }
  rewrite Nat.mul_succ_r, Nat.add_comm.
  apply Nat.add_le_lt_mono; [ | easy ].
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_nonneg_r; [ easy | ].
  now apply Nat.lt_le_incl.
}
destruct IHn as (a & Had & Ha).
rewrite Ha.
... ...
destruct (glop d p q n m) as (a & Had & Ha).
rewrite Ha.
...
Theorem first_bits_of_rat_succ :
  ∀ p q n, p < q →
  ∃ a, a < 2 ∧
  first_bits_of_rat p q (S n) =
  first_bits_of_rat p q n ++ [a].
Proof.
(*
intros * Hpq.
cbn.
rewrite Nat.add_0_r.
rewrite Nat_add_diag.
...
*)
intros * Hpq.
induction n. {
  cbn.
  rewrite Nat.add_0_r.
  rewrite Nat_add_diag.
  exists (2 * p / q).
  split; [ | easy ].
  apply Nat.div_lt_upper_bound. {
    now intros H; subst q.
  }
  rewrite Nat.mul_comm.
  now apply Nat.mul_lt_mono_pos_r.
}
destruct IHn as (a & Ha2 & Ha).
...
remember (S n) as sn; cbn.
rewrite Nat.add_0_r.
rewrite Nat_add_diag.
... ...
destruct (first_bits_of_rat_succ p q n) as (a & Ha2 & Ha).
rewrite Ha.
...
partial_sum_of_inv_power d m (l ++ [a]) =
partial_sum_of_inv_power d m l + a/d^length l
...
induction m. {
  cbn.
  progress unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_add_0_l.
  rewrite (rngl_abs_nonpos Hop Hor). 2: {
    apply (rngl_opp_le_compat Hop Hor).
    rewrite (rngl_opp_0 Hop).
    rewrite (rngl_opp_involutive Hop).
    apply (rngl_div_pos Hon Hop Hiv Hor). {
      apply (rngl_0_le_1 Hon Hop Hor).
    }
    rewrite <- rngl_of_nat_0.
    apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
    now apply Nat.neq_0_lt_0.
  }
  rewrite (rngl_opp_involutive Hop).
  apply Nat.le_0_r in Hm; subst N.
  cbn in HN.
  rewrite rngl_add_0_r in HN.
  destruct HN as (_, HN).
  rewrite (rngl_abs_nonneg Hop Hor) in HN. 2: {
    apply (rngl_div_pos Hon Hop Hiv Hor); [ | easy ].
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor) in HN; [ | easy ].
  rewrite (rngl_mul_1_l Hon) in HN.
  apply (rngl_le_lt_trans Hor _ 1)%L; [ | easy ].
  apply (rngl_le_div_l Hon Hop Hiv Hor). 2: {
    rewrite (rngl_mul_1_l Hon).
    rewrite <- rngl_of_nat_1.
    apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
    apply Nat.le_succ_l.
    now apply Nat.neq_0_lt_0.
  }
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  now apply Nat.neq_0_lt_0.
}
...
End a.

Require Import Rational.
Import Q.Notations.
Require Import Qrl.

Compute (
  let ro := Q_ring_like_op in
  let rp := Q_ring_like_prop in
  let rad := 2 in
  let a := 6 in
  let b := 7 in
  let i := 0 in
  let n := 8 in
  (partial_sum_of_inv_pow rad a b (S i) n * rngl_of_nat rad ^ i,
   rngl_of_nat a / rngl_of_nat b,
   rngl_of_nat (rad * a / b) / rngl_of_nat rad ^ S i, 1)%L).
...
Theorem glop :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ d p q n m,
  rngl_of_nat d ≠ 0%L
  → rngl_of_nat q ≠ 0%L
  → (partial_sum_of_inv_power d m (first_bits_of_rat p q n) ≤
       rngl_of_nat p / rngl_of_nat q)%L.
Proof.
Print first_bits_of_rat.
Print first_dec_of_rat.
Theorem first_bits_of_rat_succ :
  ∀ p q n,
  first_bits_of_rat p q (S n) =
    first_bits_of_rat p q n ++ [2 * ah oui non chais pas].
...
Theorem glop :
  ∀ d l,
  (∀ i, i ∈ l → i < d)
  → (partial_sum_of_inv_power d 1 l - 1 / d ≤ 1)%L.
...
(*
...
specialize (glop 2 (first_dec_of_rat 2 1
...
exists (Nat.log2 ...)
...

(* first nth bits of p/q *)
Compute (first_bits_of_rat 10 1 2).
Compute (first_bits_of_rat 10 1 3).
*)

End a.

(**)
Require Import Rational.
Import Q.Notations.
Require Import Qrl.

Compute (first_bits_of_rat 4 1 3).
Compute (
  let ro := Q_ring_like_op in
  partial_sum_of_inv_pow_2_of_inv 5 6).
Compute (first_bits_of_rat 1 5 10).
Compute (1/8 + 1/16 + 1/128 + 1/256)%Q.
Compute (
  let ro := Q_ring_like_op in
  let rp := Q_ring_like_prop in
  let d := 2 in
  let l := [1;1;1;1] in
  (partial_sum_of_inv_power d 1 l, 1/rngl_of_nat d)%L).
...
Compute (51 * 5).
...
Compute (@partial_sum_of_inv_pow_2_of_inv Q Q_ring_like_op 5 0).
...
Compute (@partial_sum_of_power Q Q_ring_like_op (1/2) (1/2) (first_bits_of_rat 12 1 3))%Q.
Compute (1365 * 3).
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
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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
