Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Init.Nat.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike Main.IterAdd.
Require Import Trigo.TacChangeAngle.
Require Import Trigo.RealLike.
Require Import Trigo.TrigoWithoutPi Trigo.TrigoWithoutPiExt.
Require Import Trigo.AngleAddOverflowLe.
Require Import Trigo.AngleAddLeMonoL.
Require Import Trigo.AngleDiv2Add.
Require Import Misc.

Notation "x ≤ y" := (Z.le x y) : Z_scope.

(* general complex whose real and imaginary parts are of type T
   that is not necessarily the real numbers *)

Class GComplex T := mk_gc {gre : T; gim : T}.

Declare Scope gc_scope.
Delimit Scope gc_scope with C.
Bind Scope gc_scope with GComplex.

Arguments mk_gc {T} gre%_L gim%_L.
Arguments gre {T} GComplex%_L.
Arguments gim {T} GComplex%_L.

Arguments rngl_opt_eq_dec T {ring_like_op}.
Arguments rngl_opt_inv_or_quot T {ring_like_op}.
Arguments rngl_opt_one T {ring_like_op}.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

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
intros Hed.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Hab.
destruct a as (ra, ia).
destruct b as (rb, ib); cbn.
destruct (rngl_eq_dec Heo ra rb) as [Hrab| Hrab]. {
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
     gim := (gim ca * gre cb + gre ca * gim cb)%L |}.

Definition gc_opt_opp_or_subt :
  option
    ((GComplex T → GComplex T) + (GComplex T → GComplex T → GComplex T)) :=
  match rngl_opt_opp_or_subt T with
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
  option
    ((GComplex T → GComplex T) + (GComplex T → GComplex T → GComplex T)) :=
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

Theorem gc_eq_dec :
  rngl_has_eq_dec T = true →
  ∀ a b : GComplex T, {a = b} + {a ≠ b}.
Proof.
intros Hed.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
destruct a as (ra, ia).
destruct b as (rb, ib).
specialize (rngl_eq_dec Heo ra rb) as H1.
specialize (rngl_eq_dec Heo ia ib) as H2.
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

Arguments rl_has_integral_modulus T {ro rp real_like_prop}.
Arguments rl_opt_integral_modulus_prop T {ro rp real_like_prop}.

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

Definition gc_pow_nat {T}
    {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T}
    (z : GComplex T) n :=
  @rngl_power (GComplex T) (gc_ring_like_op T) z n.

Notation "x + y" := (gc_add x y) : gc_scope.
Notation "x * y" := (gc_mul x y) : gc_scope.
Notation "'√' a" := (rl_sqrt a) (at level 1, format "√ a") : ring_like_scope.
Notation "x +ℹ y" := (mk_gc x y) (at level 50) : gc_scope.
Notation "z ^ n" := (gc_pow_nat z n) : gc_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_between_opp_1_and_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a, (a² ≤ 1 → -1 ≤ a ≤ 1)%L.
Proof.
intros Hon Hop Hor Hii.
intros * Ha.
rewrite <- (rngl_squ_1 Hon) in Ha.
apply (rngl_squ_le_abs_le Hop Hor Hii) in Ha.
rewrite (rngl_abs_1 Hon Hop Hor) in Ha.
now apply (rngl_abs_le Hop Hor) in Ha.
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
  rewrite rngl_add_comm.
  symmetry.
  apply rngl_add_assoc.
} {
  unfold rngl_sub; rewrite Hop.
  do 2 rewrite <- rngl_add_assoc.
  f_equal.
  rewrite (rngl_add_opp_l Hop).
  rewrite (rngl_add_opp_r Hop).
  symmetry.
  apply (rngl_add_sub_assoc Hop).
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
now rewrite (rngl_sub_0_r Hos), rngl_add_0_l.
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
now rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
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
  rewrite (rngl_add_opp_l Hop).
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

Definition gc_ring_like_prop_not_alg_closed
  (Hop : rngl_has_opp T = true) : ring_like_prop (GComplex T) :=
  let Hos := rngl_has_opp_has_opp_or_subt Hop in
  let Hsu := rngl_has_opp_has_no_subt Hop in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_integral_domain := false;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
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
     rngl_opt_mul_inv_diag_l := gc_opt_mul_inv_diag_l;
     rngl_opt_mul_inv_diag_r := gc_opt_mul_inv_diag_r;
     rngl_opt_mul_div := gc_opt_mul_div;
     rngl_opt_mul_quot_r := gc_opt_mul_quot_r;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := gc_characteristic_prop;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.

(* algebraically closed *)

Definition gc_modl (z : GComplex T) :=
  (gre z * gre z + gim z * gim z)%L.

Theorem le_rl_sqrt_add :
  ∀ a b, (0 ≤ b → a ≤ rl_sqrt (rngl_squ a + b))%L.
Proof.
destruct_ac.
intros * Hzb.
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
rewrite (rngl_squ_sqrt Hon). 2: {
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
      rewrite (rngl_squ_sqrt Hon) in H3; [ | easy ].
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
      rewrite (rngl_squ_sqrt Hon) in H3; [ | easy ].
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

Arguments rl_sqrt_squ {T ro rp rl} Hor Hop a%_L.

Theorem polar :
  rl_has_integral_modulus T = true →
  ∀ (z : GComplex T) ρ θ,
  ρ = √((gre z)² + (gim z)²)%L
  → θ =
       (if (0 ≤? gim z)%L then rngl_acos (gre z / ρ)%L
        else angle_opp (rngl_acos (gre z / ρ)%L))
  → z = mk_gc (ρ * rngl_cos θ) (ρ * rngl_sin θ).
Proof.
destruct_ac.
intros Hmi * Hρ Hθ.
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
  rewrite (rl_sqrt_0 Hon Hop Hic Hor Hii) in Hρ.
  rewrite Hρ.
  now do 2 rewrite (rngl_mul_0_l Hos).
}
subst θ.
destruct z as (zr, zi).
cbn in Hρ |-*.
assert (Hρz : ρ ≠ 0%L). {
  rewrite Hρ.
  intros H.
  apply (eq_rl_sqrt_0 Hon Hos) in H. 2: {
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
assert (Hr : zr = (ρ * rngl_cos (rngl_acos (zr / ρ)))%L). {
  rewrite rngl_cos_acos; [ easy | ].
  apply (rngl_between_opp_1_and_1 Hon Hop Hor Hii).
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
  rewrite (rngl_squ_sqrt Hon). 2: {
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
  rewrite (rngl_squ_sqrt Hon). 2: {
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
  rewrite (rngl_squ_sqrt Hon). 2: {
    apply (rngl_add_nonneg_nonneg Hor);
    apply (rngl_squ_nonneg Hop Hor).
  }
  apply (rngl_le_add_r Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
remember (0 ≤? zi)%L as zzi eqn:Hzzi; symmetry in Hzzi.
destruct zzi. {
  progress unfold rngl_acos.
  progress fold Hor.
  destruct (rngl_le_dec Hor (zr / ρ)² 1)%L as [Hzρ1| Hzρ1]; [ | easy ].
  apply rngl_leb_le in Hzzi.
  cbn.
  apply (rngl_add_sub_eq_l Hos) in Hri.
  rewrite Hri.
  rewrite (rl_sqrt_squ Hon Hop Hor).
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
  progress unfold rngl_acos.
  progress fold Hor.
  destruct (rngl_le_dec Hor (zr / ρ)² 1)%L as [Hzρ1| Hzρ1]; [ | easy ].
  cbn.
  apply (rngl_add_sub_eq_l Hos) in Hri.
  rewrite Hri.
  rewrite (rl_sqrt_squ Hon Hop Hor).
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
  (rngl_cos (a + b) +ℹ rngl_sin (a + b))%C =
  ((rngl_cos a +ℹ rngl_sin a) * (rngl_cos b +ℹ rngl_sin b))%C.
Proof. easy. Qed.

(* Moivre formula *)
Theorem gc_cos_sin_pow :
  ∀ a n,
  ((rngl_cos a +ℹ rngl_sin a) ^ n)%C =
  (rngl_cos (n * a) +ℹ rngl_sin (n * a))%C.
Proof.
intros.
progress unfold gc_pow_nat.
induction n. {
  cbn; progress unfold rngl_one.
  cbn; progress unfold gc_opt_one.
  now destruct (rngl_opt_one T).
}
rewrite rngl_pow_succ_r.
rewrite IHn.
now apply eq_gc_eq.
Qed.

Theorem rngl_rat_frac_part_lt_1 :
  ∀ a b,
  rngl_of_nat b ≠ 0%L
  → (rngl_of_nat a / rngl_of_nat b - rngl_of_nat (a / b) < 1)%L.
Proof.
intros * Hrbz.
destruct_ac.
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
    eapply Nat.le_trans; [ apply Nat.Div0.div_mul_le | ].
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

Arguments rl_sqrt_0 {T ro rp rl} Hor Hop Hic Hii.

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

(*
Notation "⌊ a / b ⌋" := (div a b).
*)

Theorem angle_div_2_add_overflow :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = true
  → ((θ1 + θ2) /₂)%A = (θ1 /₂ + θ2 /₂ + angle_straight)%A.
Proof.
intros * Haov.
rewrite angle_div_2_add.
now rewrite Haov.
Qed.

Theorem angle_div_2_pow_add' :
  ∀ n θ1 θ2,
  ((θ1 + θ2) /₂^n)%A =
     if angle_add_overflow θ1 θ2 then
       match n with
       | 0 => (θ1 + θ2)%A
       | S n' => ((θ1 /₂ + θ2 /₂ + angle_straight) /₂^n')%A
       end
     else
       (θ1 /₂^n + θ2 /₂^n)%A.
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
    apply angle_div_2_pow_le_diag.
  }
  apply angle_add_not_overflow_comm.
  apply angle_add_overflow_le with (θ2 := θ1). {
    apply angle_div_2_pow_le_diag.
  }
  now apply angle_add_not_overflow_comm.
} {
  destruct n; [ easy | ].
  rewrite angle_div_2_pow_succ_r_2.
  f_equal.
  now apply angle_div_2_add_overflow.
}
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

Theorem rngl_cos_add_rngl_cos :
  ∀ p q,
  (rngl_cos p + rngl_cos q =
   2 *
   rngl_cos (angle_div_2 p + angle_div_2 q) *
   rngl_cos (angle_div_2 p - angle_div_2 q))%L.
Proof.
destruct_ac; intros *.
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite (rngl_mul_1_r Hon).
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
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
rewrite <- (rngl_mul_2_l Hon).
rewrite <- (rngl_add_sub_swap Hop (_ * _²))%L.
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_sub_add_distr Hos).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_add_assoc.
rewrite <- (rngl_mul_2_l Hon _²)%L.
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
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite (rngl_mul_1_r Hon).
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_comm (_ * _)%L).
rewrite (rngl_sub_sub_distr Hop).
rewrite <- rngl_mul_assoc.
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_add_comm (rngl_cos p2 * _))%L.
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
rewrite <- (rngl_mul_2_l Hon).
rewrite (rngl_sub_sub_swap Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_sub_add Hop).
rewrite <- (rngl_sub_add_distr Hos).
rewrite <- (rngl_mul_2_l Hon _²)%L.
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
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite (rngl_mul_1_r Hon).
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
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
rewrite (rngl_mul_comm Hic (rngl_sin p2)).
rewrite (rngl_mul_comm Hic (rngl_sin q2)).
rewrite <- rngl_mul_add_distr_r.
rewrite <- rngl_add_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite <- (rngl_mul_2_l Hon).
rewrite <- (rngl_mul_2_l Hon (rngl_cos _)).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_l.
f_equal.
rewrite <- rngl_mul_add_distr_l.
rewrite cos2_sin2_1.
rewrite (rngl_mul_1_r Hon).
rewrite <- (rngl_add_assoc (rngl_cos p2 * _))%L.
rewrite (rngl_mul_mul_swap Hic).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite cos2_sin2_1.
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_sin_sub_rngl_sin :
  ∀ p q,
  (rngl_sin p - rngl_sin q =
   2%L *
   rngl_cos (angle_div_2 p + angle_div_2 q) *
   rngl_sin (angle_div_2 p - angle_div_2 q))%L.
Proof.
destruct_ac; intros *.
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite (rngl_mul_1_r Hon).
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
rewrite (rngl_mul_comm Hic (rngl_cos p2)).
rewrite <- (rngl_mul_2_l Hon).
rewrite (rngl_mul_comm Hic (rngl_cos q2)).
rewrite <- (rngl_mul_2_l Hon (_ * _))%L.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_sub_sub_distr Hop).
do 4 rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (rngl_cos p2)).
rewrite <- rngl_mul_assoc.
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic (rngl_sin p2)).
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic _ (rngl_cos q2)).
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic (rngl_sin p2)).
rewrite <- (rngl_mul_assoc (_ * _))%L.
rewrite fold_rngl_squ.
do 2 rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_mul_comm Hic (rngl_cos p2)).
rewrite <- rngl_mul_add_distr_l.
rewrite cos2_sin2_1.
rewrite (rngl_mul_1_r Hon).
rewrite <- (rngl_sub_add_distr Hos).
rewrite (rngl_mul_mul_swap Hic _ (rngl_cos q2)).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite rngl_add_comm.
rewrite cos2_sin2_1.
rewrite (rngl_mul_1_l Hon).
easy.
Qed.

Theorem angle_eucl_dist_sin_cos :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ θ,
  ((angle_eucl_dist θ angle_right)² =
     (1 - rngl_sin θ)² + (rngl_cos θ)²)%L.
Proof.
intros Hon Hop Hor *.
progress unfold angle_eucl_dist; cbn.
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_squ_opp Hop).
rewrite rngl_add_comm.
apply (rngl_squ_sqrt Hon).
apply (rngl_add_nonneg_nonneg Hor);
apply (rngl_squ_nonneg Hop Hor).
Qed.

Theorem rngl_sin_angle_eucl_dist :
  ∀ θ, (rngl_sin θ = 1 - (angle_eucl_dist θ angle_right)² / 2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1; apply H1.
}
intros.
specialize (angle_eucl_dist_sin_cos Hon Hop Hor θ) as H1.
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

Theorem rngl_sin_le_iff_angle_eucl_le :
  ∀ θ θ',
  (rngl_sin θ ≤ rngl_sin θ' ↔
     angle_eucl_dist θ' angle_right ≤ angle_eucl_dist θ angle_right)%L.
Proof.
destruct_ac.
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
  rewrite (rngl_squ_sqrt Hon); [ | easy ].
  rewrite (rngl_squ_sqrt Hon); [ | easy ].
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
    rewrite (rngl_squ_sqrt Hon); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor) in Hθθ. 2: {
    now apply rl_sqrt_nonneg.
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L in Hθθ. 2: {
    now apply rl_sqrt_nonneg.
  }
  apply (rngl_abs_le_squ_le Hop Hor) in Hθθ.
  rewrite (rngl_squ_sqrt Hon) in Hθθ; [ | easy ].
  rewrite (rngl_squ_sqrt Hon) in Hθθ; [ | easy ].
  now apply (rngl_sub_le_mono_l Hop Hor) in Hθθ.
}
Qed.

Theorem rl_sqrt_nonneg : ∀ a, (0 ≤ a → 0 ≤ √ a)%L.
Proof.
intros * Ha.
now apply rl_sqrt_nonneg.
Qed.

Theorem rngl_sin_div_2_pow_nat_nonneg :
  ∀ n θ, n ≠ 0 → (0 ≤ rngl_sin (angle_div_2_pow θ n))%L.
Proof.
intros * Hnz.
destruct n; [ easy | ].
rewrite angle_div_2_pow_succ_r_1.
apply rngl_sin_div_2_nonneg.
Qed.

Theorem rngl_cos_lt_sqrt_1_add_cos_div_2 :
  rngl_characteristic T ≠ 1 →
  ∀ θ,
  θ ≠ 0%A
  → (rngl_cos θ < √((1 + rngl_cos θ) / 2))%L.
Proof.
destruct_ac.
intros Hc1.
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
rewrite (rngl_squ_sqrt Hon). 2: {
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

Theorem eq_angle_div_2_0 : ∀ θ, (θ /₂ = 0 → θ = 0)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  apply H1.
}
intros * Htz.
apply eq_angle_eq in Htz.
apply eq_angle_eq; cbn.
injection Htz; clear Htz; intros Hc Hs.
apply (eq_rl_sqrt_0 Hon Hos) in Hc. 2: {
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

Theorem eq_angle_div_2_pow_0 :
  ∀ n θ, (angle_div_2_pow θ n = 0 → θ = 0)%A.
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
apply (eq_rngl_squ_rngl_abs Hop Hic Hor). {
  now rewrite Bool.orb_true_iff; right.
}
rewrite (rngl_squ_sqrt Hon); [ | easy ].
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite (rngl_squ_sqrt Hon); [ | easy ].
progress unfold rngl_squ.
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite (rngl_mul_comm Hic).
now rewrite (rngl_mul_div Hi1).
Qed.

Theorem rngl_cos_div_pow_2_succ_r :
  ∀ n θ,
  (0 ≤ rngl_sin θ)%L
  → rngl_cos_div_pow_2 θ (S n) = rngl_cos_div_pow_2 (θ /₂) n.
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

Theorem rngl_cos_pow_2_div_2_succ_nonneg :
  ∀ n θ, (0 ≤ rngl_cos_div_pow_2 (θ /₂) (S n))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
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

Theorem angle_div_2_not_straight :
  rngl_characteristic T ≠ 1 →
  ∀ θ, (θ /₂)%A ≠ angle_straight.
Proof.
destruct_ac.
intros Hc1.
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
rewrite (rngl_squ_sqrt Hon) in Hc. 2: {
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
  → (rngl_cos_div_pow_2 (θ /₂) n < rngl_cos_div_pow_2 (θ /₂) (S n))%L.
Proof.
destruct_ac; intros Hc1.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Htz.
destruct (rngl_eq_dec Heo (rngl_cos θ) (-1)%L) as [Ht1| Ht1]. {
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
    apply (rl_sqrt_lt_rl_sqrt Hon Hop Hor). {
      apply rngl_1_add_cos_div_2_nonneg.
    }
    apply (rngl_div_lt_mono_pos_r Hon Hop Hiv Hor Hii). {
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
    apply (rl_sqrt_pos Hon Hos Hor).
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
  rewrite (rngl_squ_sqrt Hon). 2: {
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
rewrite (rngl_mul_2_l Hon).
apply (rngl_add_lt_mono_r Hop Hor).
subst a.
now apply (squ_rngl_cos_non_0_div_pow_2_bound Hc1).
Qed.

Theorem rngl_sin_mul_2_l :
  ∀ θ, rngl_sin (2 * θ) = (2 * rngl_sin θ * rngl_cos θ)%L.
Proof.
destruct_ac.
intros; cbn.
do 2 rewrite (rngl_mul_1_r Hon).
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_r.
rewrite (rngl_mul_comm Hic (rngl_cos θ)).
rewrite <- rngl_mul_assoc; symmetry.
apply (rngl_mul_2_l Hon).
Qed.

Theorem rngl_cos_mul_2_l :
  ∀ θ, rngl_cos (2 * θ) = ((rngl_cos θ)² - (rngl_sin θ)²)%L.
Proof.
destruct_ac.
intros; cbn.
do 2 rewrite (rngl_mul_1_r Hon).
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_r.
now do 2 rewrite fold_rngl_squ.
Qed.

Theorem angle_add_div_2_diag : ∀ θ, (θ /₂ + θ /₂)%A = θ.
Proof.
destruct_ac.
intros.
apply eq_angle_eq.
cbn - [ angle_div_2 ].
do 2 rewrite fold_rngl_squ.
rewrite <- rngl_cos_mul_2_l.
rewrite (rngl_mul_comm Hic (rngl_cos (_ /₂))).
rewrite <- (rngl_mul_2_l Hon).
rewrite rngl_mul_assoc.
rewrite <- rngl_sin_mul_2_l.
now rewrite angle_div_2_mul_2.
Qed.

Theorem angle_mul_0_l : ∀ θ, (0 * θ = 0)%A.
Proof. easy. Qed.

Theorem rngl_cos_div_2 :
  ∀ θ,
  rngl_cos (θ /₂) =
  ((if (0 ≤? rngl_sin θ)%L then 1%L else (-1)%L) *
   √((1 + rngl_cos θ) / 2))%L.
Proof. easy. Qed.

Theorem rngl_sin_div_2 :
  ∀ θ, rngl_sin (θ /₂) = √((1 - rngl_cos θ) / 2)%L.
Proof. easy. Qed.

Theorem angle_mul_sub_distr_l :
  ∀ n θ1 θ2, (n * (θ1 - θ2) = n * θ1 - n * θ2)%A.
Proof.
intros.
revert θ1 θ2.
induction n; intros; cbn; [ symmetry; apply angle_sub_diag | ].
rewrite angle_sub_add_distr.
rewrite angle_add_sub_swap.
rewrite <- angle_add_sub_assoc.
f_equal.
apply IHn.
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
intros * Hmn Hm.
destruct (Nat.eq_dec m n) as [H1| H1]; [ now subst m | ].
assert (H : m < n) by flia Hmn H1.
clear Hmn H1; rename H into Hmn.
revert m Hmn Hm.
induction n; intros; [ easy | ].
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hmn.
apply angle_mul_nat_overflow_succ_l_true in Hm.
apply angle_mul_nat_overflow_succ_l_true.
destruct Hm as [Hm| Hm]. {
  left.
  now apply (IHn m).
}
left.
destruct (Nat.eq_dec (S m) n) as [Hsmn| Hsmn]. 2: {
  apply (IHn (S m)); [ flia Hmn Hsmn | ].
  apply angle_mul_nat_overflow_succ_l_true.
  now right.
}
subst n.
apply angle_mul_nat_overflow_succ_l_true.
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
intros * Hn.
specialize (sequence_false_min n (λ i, angle_mul_nat_overflow i θ)) as H1.
specialize (H1 eq_refl Hn).
destruct H1 as (i & Hi & Hsi).
destruct i; [ easy | ].
rewrite angle_mul_nat_overflow_succ_l_false in Hi.
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
  now apply angle_mul_le_mono_r.
}
rewrite angle_mul_nat_overflow_succ_l_true in Hsi.
destruct Hsi as [Hsi| Hsi]; [ | easy ].
rewrite angle_mul_nat_overflow_succ_l_true in Hsi.
destruct Hsi as [Hsi| Hsi]; [ now rewrite Hi in Hsi | ].
now rewrite Hit in Hsi.
Qed.

Theorem angle_all_add_not_overflow :
  ∀ n θ,
  (∀ m, m < n → angle_add_overflow θ (m * θ) = false)
  ↔ angle_mul_nat_overflow n θ = false.
Proof.
destruct_ac.
intros.
split; intros Ha. {
  induction n; [ easy | ].
  rewrite angle_mul_nat_overflow_succ_l_false.
  split; [ | now apply Ha ].
  apply IHn.
  intros m Hm.
  apply Ha.
  now apply Nat.lt_lt_succ_r.
} {
  intros m Hm.
  induction n; [ easy | ].
  rewrite angle_mul_nat_overflow_succ_l_false in Ha.
  destruct Ha as (Ha1, Ha2).
  destruct (Nat.eq_dec m n) as [Hmen| Hmen]; [ now subst m | ].
  apply IHn; [ easy | ].
  flia Hm Hmen.
}
Qed.

Theorem rngl_cos_div_2_nonneg :
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → (0 ≤ rngl_cos (θ /₂))%L.
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

Theorem angle_right_neq_0 :
  rngl_characteristic T ≠ 1
  → angle_right ≠ 0%A.
Proof.
destruct_ac.
intros Hc1 Hrz.
apply eq_angle_eq in Hrz.
cbn in Hrz.
injection Hrz; clear Hrz; intros H1 H2.
now apply (rngl_1_eq_0_iff Hon Hos) in H1.
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
  | S i' => (angle_straight /₂^i')%A
  end.

Theorem angle_mul_succ_l : ∀ n θ, (S n * θ = θ + n * θ)%A.
Proof. easy. Qed.

Theorem rngl_cos_le_cos_div_2 :
  ∀ θ, (0 ≤ rngl_sin θ)%L → (rngl_cos θ ≤ rngl_cos (θ /₂))%L.
Proof.
destruct_ac.
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
  apply angle_eqb_eq in Htz.
  subst θ.
  rewrite angle_0_div_2.
  apply (rngl_le_refl Hor).
}
apply angle_eqb_neq in Htz.
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

Theorem eq_angle_mul_0 :
  ∀ n θ,
  (n * θ)%A = 0%A
  ↔ n = 0 ∨ rngl_cos (n * θ) = 1%L ∧ rngl_sin (n * θ) = 0%L.
Proof.
intros.
split; intros Hnt. {
  induction n; [ now left | right ].
  cbn in Hnt.
  progress unfold angle_add in Hnt.
  injection Hnt; clear Hnt; intros Hs Hc.
  rewrite <- rngl_cos_add in Hc.
  rewrite <- rngl_sin_add in Hs.
  rewrite <- angle_mul_succ_l in Hs, Hc.
  easy.
}
destruct Hnt as [Hnt| Hnt]. {
  subst n.
  apply angle_mul_0_l.
}
destruct Hnt as (Hc, Hs).
induction n; [ easy | cbn ].
progress unfold angle_add.
apply eq_angle_eq; cbn.
apply pair_equal_spec.
split; [ now rewrite <- rngl_cos_add | ].
now rewrite <- rngl_sin_add.
Qed.

Fixpoint rngl_cos_mul n θ :=
  match n with
  | 0 => 1%L
  | S n' =>
      (rngl_cos θ * rngl_cos_mul n' θ - rngl_sin θ * rngl_sin_mul n' θ)%L
  end
with rngl_sin_mul n θ :=
  match n with
  | 0 => 0%L
  | S n' =>
      (rngl_sin θ * rngl_cos_mul n' θ + rngl_cos θ * rngl_sin_mul n' θ)%L
  end.

Theorem rngl_cos_mul_sin_mul :
  ∀ n θ,
  rngl_cos (n * θ) = rngl_cos_mul n θ ∧
  rngl_sin (n * θ) = rngl_sin_mul n θ.
Proof.
intros.
induction n; intros; [ easy | cbn ].
destruct IHn as (Hc, Hs).
now rewrite Hc, Hs.
Qed.

Theorem rngl_cos_cos_mul :
  ∀ n θ, rngl_cos (n * θ) = rngl_cos_mul n θ.
Proof.
intros.
apply rngl_cos_mul_sin_mul.
Qed.

Theorem rngl_sin_sin_mul :
  ∀ n θ, rngl_sin (n * θ) = rngl_sin_mul n θ.
Proof.
intros.
apply rngl_cos_mul_sin_mul.
Qed.

Theorem rngl_2_x2_sub_1_le_x :
  ∀ x, (0 ≤ x ≤ 1)%L → (2 * x² - 1 ≤ x)%L.
Proof.
destruct_ac.
intros * Hx.
apply (rngl_le_sub_le_add_l Hop Hor).
apply (rngl_le_sub_le_add_r Hop Hor).
progress unfold rngl_squ.
rewrite rngl_mul_assoc.
rewrite (rngl_sub_mul_l_diag_r Hon Hop).
destruct (rngl_le_dec Hor 0 (2 * x - 1)%L) as [Hz2c| H2cz]. {
  rewrite <- (rngl_mul_1_r Hon 1%L) at 4.
  apply (rngl_mul_le_compat_nonneg Hop Hor); [ | easy ].
  split; [ easy | ].
  apply (rngl_le_sub_le_add_r Hop Hor).
  rewrite <- (rngl_mul_1_r Hon 2%L) at 2.
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ | easy ].
  apply (rngl_0_le_2 Hon Hop Hor).
}
apply (rngl_nle_gt Hor) in H2cz.
apply (rngl_le_trans Hor _ 0)%L. 2: {
  apply (rngl_0_le_1 Hon Hop Hor).
}
apply (rngl_lt_le_incl Hor) in H2cz.
now apply (rngl_mul_nonpos_nonneg Hop Hor).
Qed.

Theorem angle_straight_lt_opp_right :
  rngl_characteristic T ≠ 1
  → (angle_straight < - angle_right)%A.
Proof.
destruct_ac.
intros Hc1.
progress unfold angle_ltb.
cbn.
rewrite (rngl_leb_refl Hor).
remember (0 ≤? -1)%L as x eqn:Hx.
symmetry in Hx.
destruct x; [ exfalso | easy ].
apply rngl_leb_le in Hx.
apply (rngl_nlt_ge Hor) in Hx.
apply Hx; clear Hx.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

End a.

Arguments gc_opt_one T {ro}.
