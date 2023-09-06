(* Real-Like numbers *)
(* Algebraic structure having the same properties as real numbers *)
(* and complex numbers *)
(* see also Quaternions.v *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Main.Misc Main.RingLike.
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

Class real_like_prop T {ro : ring_like_op T} {rp : ring_like_prop T} :=
  { rl_nth_sqrt : nat → T → T;
    rl_cos : T → T;
    rl_sin : T → T;
    rl_acos : T → T;
    rl_opt_integral_modulus_prop :
      option (∀ a b : T, (rngl_squ a + rngl_squ b = 0 → a = 0 ∧ b = 0)%L);
    rl_nth_sqrt_pow : ∀ n a, (rl_nth_sqrt n a ^ n = a)%L;
(* can be added if required
    rl_nth_sqrt_mul_l :
      ∀ m n a, rl_nth_sqrt (m * n) a = rl_nth_sqrt m (rl_nth_sqrt n a);
*)
    rl_opt_sqrt_prop :
      if rngl_is_ordered T then ∀ a, (0 ≤ a → 0 ≤ rl_nth_sqrt 2 a)%L
      else not_applicable;
    rl_opt_cos_acos :
      if rngl_is_ordered T then
        ∀ x, (-1 ≤ x ≤ 1)%L → rl_cos (rl_acos x) = x
      else not_applicable }.

(*
Class real_like_prop T {ro : ring_like_op T} {rp : ring_like_prop T} :=
  { rl_excl_midd : ∀ P, P + notT P;
    rl_has_trigo : bool;
    rl_exp : T → T;
    rl_log : T → T;
    rl_cos : T → T;
    rl_sin : T → T;
    rl_acos : T → T;
    rl_opt_mod_intgl_prop :
      option (∀ a b : T, (rngl_squ a + rngl_squ b = 0 → a = 0 ∧ b = 0)%L);
    rl_opt_cos2_sin2 :
      if rl_has_trigo then
        ∀ x : T, (rngl_squ (rl_cos x) + rngl_squ (rl_sin x))%L = 1%L
      else not_applicable;
    rl_opt_cos_acos :
      if rl_has_trigo then
        ∀ x, (-1 ≤ x ≤ 1)%L → rl_cos (rl_acos x) = x
      else not_applicable;
    rl_opt_exp_not_all_0 :
      if rl_has_trigo then ∃ x, rl_exp x ≠ 0%L else not_applicable;
    rl_opt_exp_add :
      if rl_has_trigo then
        ∀ x y : T, (rl_exp (x + y) = rl_exp x * rl_exp y)%L
      else not_applicable;
    rl_exp_continuous_at :
      if rl_has_trigo then ∃ a : T, continuous_at rl_exp a
      else not_applicable;
    rl_opt_exp_log :
      if rl_has_trigo then ∀ x : T, (0 < x)%L → rl_exp (rl_log x) = x
      else not_applicable;
    rl_opt_log_exp :
      if rl_has_trigo then ∀ x : T, rl_log (rl_exp x) = x
      else not_applicable }.
*)

Definition rl_has_integral_modulus {T} {ro : ring_like_op T}
    {rp : ring_like_prop T} {rl : real_like_prop T} :=
  bool_of_option rl_opt_integral_modulus_prop.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition rl_sqrt := rl_nth_sqrt 2.

Arguments rl_acos {T ro rp real_like_prop} x%L.
Arguments rl_cos {T ro rp real_like_prop} x%L.
(*
Arguments rl_exp {T ro rp real_like_prop} x%L.
*)
Arguments rl_has_integral_modulus T {ro rp rl}.
(*
Arguments rl_opt_mod_intgl_prop T {ro rp real_like_prop}.
Arguments rl_log {T ro rp real_like_prop} x%L.
*)
Arguments rl_sin {T ro rp real_like_prop} x%L.
(*
Arguments rl_has_trigo T {ro rp real_like_prop}.
*)

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

Theorem fold_rl_sqrt : rl_nth_sqrt 2 = rl_sqrt.
Proof. easy. Qed.

Theorem rl_sqrt_prop :
  rngl_is_ordered T = true →
  ∀ a : T, (0 ≤ a)%L → (0 ≤ rl_nth_sqrt 2 a)%L.
Proof.
intros Hor.
specialize rl_opt_sqrt_prop as H1.
now rewrite Hor in H1.
Qed.

Theorem gc_opt_eq_dec : option (∀ a b : GComplex T, {a = b} + {a ≠ b}).
Proof.
remember (rngl_opt_eq_dec T) as ed eqn:Hed; symmetry in Hed.
destruct ed as [rngl_eq_dec| ]; [ | apply None ].
apply Some.
intros.
destruct a as (ra, ia).
destruct b as (rb, ib).
specialize (rngl_eq_dec ra rb) as H1.
specialize (rngl_eq_dec ia ib) as H2.
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

End a.

Arguments rl_acos {T ro rp real_like_prop} x%L.
Arguments rl_has_integral_modulus T {ro rp rl}.
Arguments rl_opt_integral_modulus_prop T {ro rp real_like_prop}.

Declare Scope gc_scope.
Delimit Scope gc_scope with C.

Notation "x + y" := (gc_add x y) : gc_scope.
Notation "x * y" := (gc_mul x y) : gc_scope.

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

(*
Definition gc_exp (z : GComplex T) :=
  mk_gc
    ((rl_exp (gre z) * rl_cos (gre z))%L)
    ((rl_exp (gre z) * rl_sin (gre z))%L).
*)

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
  unfold rl_has_integral_modulus in H.
  destruct (rl_opt_integral_modulus_prop T) as [H3| ]; [ clear H | easy ].
  apply H3 in H2.
  apply Haz.
  now apply eq_gc_eq; cbn.
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
specialize (rngl_characteristic_prop) as H1.
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

Fixpoint gc_power_nat (z : GComplex T) n :=
  match n with
  | 0 => gc_one
  | S n' => (z * gc_power_nat z n')%C
  end.

(*
Definition rl_pow (x y : T) :=
  rl_exp (y * rl_log x).

Definition rl_sqrt (x : T) :=
  if (x =? 0)%L then 0%L else rl_pow x (1 / (1 + 1))%L.

Theorem rl_exp_not_all_0 :
  rl_has_trigo T = true → ∃ x : T, rl_exp x ≠ 0%L.
Proof.
intros * Htr.
specialize rl_opt_exp_not_all_0 as H1.
now rewrite Htr in H1.
Qed.

Theorem rl_exp_add :
  rl_has_trigo T = true → ∀ x y : T, rl_exp (x + y) = (rl_exp x * rl_exp y)%L.
Proof.
intros * Htr.
specialize rl_opt_exp_add as H1.
now rewrite Htr in H1.
Qed.

Theorem rl_exp_ln :
  rl_has_trigo T = true → ∀ x : T, (0 < x)%L → rl_exp (rl_log x) = x.
Proof.
intros * Htr.
specialize rl_opt_exp_log as H1.
now rewrite Htr in H1.
Qed.

Theorem rl_log_exp :
  rl_has_trigo T = true → ∀ x : T, rl_log (rl_exp x) = x.
Proof.
intros * Htr.
specialize rl_opt_log_exp as H1.
now rewrite Htr in H1.
Qed.

Theorem rl_cos_acos :
  rl_has_trigo T = true → ∀ x : T, (-1 ≤ x ≤ 1)%L → rl_cos (rl_acos x) = x.
Proof.
intros * Htr.
specialize rl_opt_cos_acos as H1.
now rewrite Htr in H1.
Qed.

Theorem rl_cos2_sin2 :
  rl_has_trigo T = true →
  ∀ x, (rngl_squ (rl_cos x) + rngl_squ (rl_sin x))%L = 1%L.
Proof.
intros * Htr.
specialize rl_opt_cos2_sin2 as H1.
now rewrite Htr in H1.
Qed.

Theorem rl_exp_0 :
  rngl_has_1 T = true →
  rngl_has_inv_or_quot T = true →
  rl_has_trigo T = true →
  rl_exp 0 = 1%L.
Proof.
intros * Hon Hiq Htr *.
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_or_quot_iff in Hiq.
  apply rngl_has_inv_and_1_or_quot_iff.
  now destruct Hiq; [ left | right ].
}
specialize (rl_exp_not_all_0 Htr) as H1.
destruct H1 as (y, H1).
specialize (rl_exp_add Htr 0%L y) as H2.
rewrite rngl_add_0_l in H2.
apply (f_equal (λ x, (x / rl_exp y)%L)) in H2.
rewrite (rngl_div_diag Hon Hiq _ H1) in H2.
now rewrite (rngl_mul_div Hi1) in H2.
Qed.

Theorem rngl_characteristic_1_not_trigo :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T = 1 →
  rl_has_trigo T = false.
Proof.
intros * Hon Hos Hc1.
specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
apply Bool.not_true_iff_false.
intros Htr.
specialize (rl_exp_not_all_0 Htr) as H2.
destruct H2 as (a, Ha).
exfalso; apply Ha, H1.
Qed.

Theorem rl_exp_neq_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rl_has_trigo T = true →
  ∀ x : T, rl_exp x ≠ 0%L.
Proof.
intros * Hon Hop Hiv Htr *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite (rngl_characteristic_1_not_trigo Hon Hos Hc1) in Htr.
}
intros Hxz.
specialize (rl_exp_add Htr x (- x)%L) as H3.
rewrite (fold_rngl_sub Hop) in H3.
rewrite (rngl_sub_diag Hos) in H3.
rewrite (rl_exp_0 Hon Hiq Htr) in H3.
rewrite Hxz in H3.
rewrite (rngl_mul_0_l Hos) in H3.
now revert H3; apply (rngl_1_neq_0_iff Hon).
Qed.

Theorem rl_exp_ge_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_is_ordered T = true →
  rl_has_trigo T = true →
  ∀ x : T, (0 ≤ rl_exp x)%L.
Proof.
intros * Hon Hop Hiv Hc2 Hor Htr *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_and_1_or_quot_iff.
  now rewrite Hiv, Hon; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1.
  apply (rngl_le_refl Hor).
}
move Hc1 after Hc2.
assert (H20 : (2 ≠ 0)%L). {
  specialize rngl_characteristic_prop as H1.
  rewrite Hon in H1.
  remember (rngl_characteristic T =? 0) as ch eqn:Hch.
  symmetry in Hch.
  destruct ch. {
    specialize (H1 1); cbn in H1.
    now rewrite rngl_add_0_r in H1.
  }
  apply Nat.eqb_neq in Hch.
  destruct H1 as (H1, H2).
  specialize (H1 2).
  assert (H : 0 < 2 < rngl_characteristic T). {
    split; [ easy | flia Hch Hc1 Hc2 ].
  }
  specialize (H1 H); clear H.
  cbn in H1.
  now rewrite rngl_add_0_r in H1.
}
assert (H : ∀ x, x = (x / 2 + x / 2)%L). {
  clear x; intros.
  apply (rngl_mul_cancel_r Hi1) with (c := 2%L); [ easy | ].
  rewrite rngl_mul_add_distr_r.
  rewrite (rngl_div_mul Hon Hiv); [ | easy ].
  rewrite rngl_mul_add_distr_l.
  now rewrite (rngl_mul_1_r Hon).
}
rewrite (H x).
rewrite (rl_exp_add Htr).
apply (rngl_square_ge_0 Hop Hor).
Qed.

Theorem rl_exp_gt_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_is_ordered T = true →
  rl_has_trigo T = true →
  ∀ x : T, (0 < rl_exp x)%L.
Proof.
intros * Hon Hop Hiv Hc2 Hor Htr *.
apply (rngl_lt_iff Hor).
split. {
  apply (rl_exp_ge_0 Hon Hop Hiv Hc2 Hor Htr).
} {
  apply not_eq_sym.
  apply (rl_exp_neq_0 Hon Hop Hiv Htr).
}
Qed.

Theorem rl_pow_neq_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rl_has_trigo T = true →
  ∀ x y, rl_pow x y ≠ 0%L.
Proof.
intros * Hon Hop Hiv Htr *.
unfold rl_pow.
apply (rl_exp_neq_0 Hon Hop Hiv Htr).
Qed.

Theorem rl_pow_ge_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_is_ordered T = true →
  rl_has_trigo T = true →
  ∀ x y, (0 ≤ rl_pow x y)%L.
Proof.
intros * Hon Hop Hiv Hc2 Hor Htr *.
unfold rl_pow.
apply (rl_exp_ge_0 Hon Hop Hiv Hc2 Hor Htr).
Qed.

Theorem rl_log_mul :
  rl_has_trigo T = true →
  ∀ x y, (0 < x)%L → (0 < y)%L →
  rl_log (x * y) = (rl_log x + rl_log y)%L.
Proof.
intros * Htr * Hx Hy.
rewrite <- (rl_log_exp Htr (_ + _)%L).
f_equal.
rewrite (rl_exp_add Htr).
now rewrite (rl_exp_ln Htr _ Hx), (rl_exp_ln Htr _ Hy).
Qed.

Theorem rl_sqrt_squ :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  rl_has_trigo T = true →
  ∀ x : T, rl_sqrt (rngl_squ x) = rngl_abs x.
Proof.
intros * Hon Hop Hiv Hc2 Heb Hor Htr *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
progress unfold rl_sqrt.
destruct (rngl_eq_dec Heb x 0%L) as [Hxz| Hxz]. {
  subst x.
  progress unfold rngl_squ.
  progress unfold rngl_abs.
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_eqb_refl Heb).
  rewrite (rngl_leb_refl Hor).
  symmetry; apply (rngl_opp_0 Hop).
}
assert (H2z : 2%L ≠ 0%L). {
  specialize rngl_characteristic_prop as H2.
  rewrite Hon in H2.
  rewrite if_bool_if_dec in H2.
  destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
    specialize (H2 1); cbn in H2.
    now rewrite rngl_add_0_r in H2.
  }
  apply Nat.eqb_neq in Hcz.
  destruct H2 as (H2, H4).
  remember (rngl_characteristic T) as ch eqn:Hch; symmetry in Hch.
  destruct ch; [ easy | clear Hcz ].
  destruct ch. {
    specialize (rngl_characteristic_1 Hon Hos Hch) as H5.
    now specialize (H5 x).
  }
  destruct ch; [ easy | ].
  specialize (H2 2); cbn in H2.
  rewrite rngl_add_0_r in H2.
  apply H2.
  split; [ easy | ].
  now do 2 apply -> Nat.succ_lt_mono.
}
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [H3| H3]. {
  apply (rngl_eqb_eq Heb) in H3.
  progress unfold rngl_squ in H3.
  apply (rngl_integral Hos) in H3; [ now destruct H3 | ].
  apply Bool.orb_true_iff; right.
  apply Bool.andb_true_iff.
  split; [ | easy ].
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
apply (rngl_eqb_neq Heb) in H3.
progress unfold rl_pow.
progress unfold rngl_squ.
progress unfold rngl_abs.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [H1| H1]. {
  apply rngl_leb_le in H1.
  assert (Hxl : (x < 0)%L). {
    specialize (rngl_le_antisymm Hor) as H2.
    progress unfold rngl_le in H2.
    progress unfold rngl_lt.
    progress unfold rngl_is_ordered in Hor.
    progress unfold rngl_le in H1.
    destruct rngl_opt_leb as [rngl_leb| ]; [ | easy ].
    apply Bool.not_true_iff_false.
    intros H4.
    now specialize (H2 x 0%L H1 H4).
  }
  assert (Hlx : (0 < -x)%L). {
    apply (rngl_add_le_compat Hor (- x)%L (- x)%L) in H1. 2: {
      apply (rngl_le_refl Hor).
    }
    rewrite (rngl_add_opp_l Hop) in H1.
    rewrite rngl_add_0_r in H1.
    specialize (rngl_le_antisymm Hor) as H2.
    progress unfold rngl_le in H2.
    progress unfold rngl_lt.
    progress unfold rngl_is_ordered in Hor.
    progress unfold rngl_le in H1.
    destruct rngl_opt_leb as [rngl_leb| ]; [ | easy ].
    apply Bool.not_true_iff_false.
    intros H.
    specialize (H2 _ _ H H1).
    apply (f_equal rngl_opp) in H2.
    rewrite (rngl_opp_0 Hop) in H2.
    now rewrite (rngl_opp_involutive Hop) in H2.
  }
  rewrite <- (rngl_mul_opp_opp Hop x).
  rewrite (rl_log_mul Htr _ _ Hlx Hlx).
  rewrite <- (rngl_mul_1_l Hon (rl_log (- x))).
  rewrite <- rngl_mul_add_distr_r.
  rewrite rngl_mul_assoc.
  rewrite (rngl_div_mul Hon Hiv _ _ H2z).
  rewrite (rngl_mul_1_l Hon).
  specialize rl_exp_ln as H2.
  rewrite Htr in H2.
  now apply H2.
}
apply rngl_leb_nle in H1.
apply (rngl_not_le Hor) in H1.
destruct H1 as (_, H1).
assert (Hxl : (0 < x)%L). {
  specialize (rngl_le_antisymm Hor) as H2.
  progress unfold rngl_le in H2.
  progress unfold rngl_lt.
  progress unfold rngl_le in H1.
  destruct rngl_opt_leb as [rngl_leb| ]; [ | easy ].
  apply Bool.not_true_iff_false.
  intros H.
  now specialize (H2 _ _ H H1).
}
rewrite (rl_log_mul Htr _ _ Hxl Hxl).
rewrite <- (rngl_mul_1_l Hon (rl_log x)).
rewrite <- rngl_mul_add_distr_r.
rewrite rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv _ _ H2z).
rewrite (rngl_mul_1_l Hon).
now apply (rl_exp_ln Htr).
Qed.

Theorem fold_rl_pow : ∀ x y, rl_exp (y * rl_log x) = rl_pow x y.
Proof. easy. Qed.

Theorem fold_rl_sqrt :
  ∀ x, (if (x =? 0)%L then 0%L else rl_pow x (1 / (1 + 1))%L) = rl_sqrt x.
Proof. easy. Qed.

Theorem rl_log_1 :
  rngl_has_1 T = true →
  rngl_has_inv_or_quot T = true →
  rl_has_trigo T = true →
  rl_log 1 = 0%L.
Proof.
intros * Hon Hiq Htr.
rewrite <- (rl_exp_0 Hon Hiq Htr).
apply (rl_log_exp Htr).
Qed.

Theorem rl_exp_continuous :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  rl_has_trigo T = true →
  continuous rl_exp.
Proof.
intros * Hon Hop Hiv Hc2 Heb Hor Htr b.
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
specialize rl_exp_continuous_at as H1.
rewrite Htr in H1.
destruct H1 as (a, Ha).
progress unfold continuous_at in Ha.
progress unfold continuous_at.
intros ε Hε.
specialize (Ha (ε * rl_exp (a - b))%L) as H1.
assert (H : (0 < ε * rl_exp (a - b))%L). {
  apply (rngl_mul_pos_pos Hop Hor); [ | easy | ]. {
    rewrite Hi1.
    apply Bool.orb_true_r.
  } {
    apply (rl_exp_gt_0 Hon Hop Hiv Hc2 Hor Htr).
  }
}
specialize (H1 H); clear H.
destruct H1 as (η & Hzη & Hη).
exists η.
split; [ easy | ].
intros x Hxη.
specialize (Hη (x - b + a))%L as H1.
rewrite (rngl_add_sub Hos) in H1.
specialize (H1 Hxη).
rewrite <- (rngl_mul_1_l Hon (rl_exp a)) in H1.
rewrite <- (rl_exp_0 Hon Hiq Htr) in H1.
rewrite <- (rngl_sub_diag Hos b) in H1.
progress unfold rngl_sub in H1 at 2 3.
rewrite Hop in H1.
rewrite <- (rl_exp_add Htr) in H1.
rewrite (rngl_add_add_swap x) in H1.
rewrite (rngl_add_add_swap b) in H1.
do 2 rewrite <- rngl_add_assoc in H1.
rewrite (fold_rngl_sub Hop) in H1.
do 2 rewrite (rl_exp_add Htr) in H1.
rewrite <- (rngl_mul_sub_distr_r Hop) in H1.
rewrite (rngl_abs_mul Hop Hi1 Hor) in H1.
rewrite (rngl_abs_nonneg Hop Hor (rl_exp _)) in H1. 2: {
  apply (rl_exp_ge_0 Hon Hop Hiv Hc2 Hor Htr).
}
apply (rngl_mul_lt_mono_pos_r Hop Hor) in H1; [ easy | | ]. {
  rewrite Hi1.
  apply Bool.orb_true_r.
} {
  apply (rl_exp_gt_0 Hon Hop Hiv Hc2 Hor Htr).
}
Qed.

Theorem rl_exp_inj :
  rl_has_trigo T = true →
  ∀ a b, rl_exp a = rl_exp b → a = b.
Proof.
intros Htr * Hab.
rewrite <- (rl_log_exp Htr a).
rewrite <- (rl_log_exp Htr b).
now f_equal.
Qed.
*)

(**)

(* should be called with "a ≤ rngl_of_nat n" *)
Fixpoint int_part_loop n a :=
  match n with
  | 0%nat => 0%nat
  | S n' => if (rngl_of_nat n ≤? a)%L then n else int_part_loop n' a
  end.

(*
End a.
Require Import QArith.
Require Import QG.
Compute (
  let ro := QG_ring_like_op in
  let rp := QG_ring_like_prop in
  let a := QG_of_Q (19 # 5) in
  let n := 4%nat in
  ((a ≤? rngl_of_nat n)%L, int_part_loop n a)).
Compute (
  let ro := QG_ring_like_op in
  let rp := QG_ring_like_prop in
  let a := QG_of_Q (4 # 5) in
  let n := 1%nat in
  ((a ≤? rngl_of_nat n)%L, int_part_loop n a)).
Compute (
  let ro := QG_ring_like_op in
  let rp := QG_ring_like_prop in
  let a := QG_of_Q (18 # 1) in
  let n := 18%nat in
  ((a ≤? rngl_of_nat n)%L, int_part_loop n a)).
Compute (
  let ro := QG_ring_like_op in
  let rp := QG_ring_like_prop in
  let a := QG_of_Q (37 # 2) in
  let n := 19%nat in
  ((a ≤? rngl_of_nat n)%L, int_part_loop n a)).
Compute (
  let ro := QG_ring_like_op in
  let rp := QG_ring_like_prop in
  let a := QG_of_Q (35 # 2) in
  let n := 18%nat in
  ((a ≤? rngl_of_nat n)%L, int_part_loop n a)).
*)

Theorem int_part_loop_le :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ n a,
  (0 ≤ a)%L
  → (a ≤ rngl_of_nat n)%L
  → (rngl_of_nat (int_part_loop n a) ≤ a)%L.
Proof.
intros Hon Hop Hor * Hxz Hxn.
induction n; [ easy | ].
cbn in Hxn |-*.
rewrite fold_rngl_of_nat in Hxn.
do 2 rewrite fold_rngl_of_nat.
remember (1 + rngl_of_nat n ≤? a)%L as c eqn:Hc; symmetry in Hc.
destruct c. {
  apply rngl_leb_le in Hc.
  now rewrite rngl_of_nat_succ.
}
apply (rngl_leb_gt Hor) in Hc.
destruct (rngl_le_dec Hor a (rngl_of_nat n)) as [Han| Han]. {
  now apply IHn.
}
apply (rngl_nle_gt Hor) in Han.
apply (rngl_le_trans Hor _ (rngl_of_nat n)). 2: {
  now apply (rngl_lt_le_incl Hor).
}
clear IHn Hxn Hc.
induction n; [ apply (rngl_le_refl Hor) | cbn ].
do 2 rewrite fold_rngl_of_nat.
rewrite <- rngl_of_nat_succ.
remember (_ ≤? a)%L as d eqn:Hd; symmetry in Hd.
destruct d. 2: {
  assert (H : (rngl_of_nat n ≤ rngl_of_nat (S n))%L). {
    cbn; rewrite fold_rngl_of_nat.
    apply (rngl_le_add_l Hor).
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  eapply (rngl_le_trans Hor); [ | apply H ].
  apply IHn.
  eapply (rngl_le_lt_trans Hor); [ apply H | apply Han ].
}
apply (rngl_le_refl Hor).
Qed.

Theorem rngl_squ_sqrt : ∀ a, rngl_squ (rl_sqrt a) = a.
Proof.
intros.
apply (rl_nth_sqrt_pow 2 a).
Qed.

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
  apply (rl_sqrt_prop Hor).
  apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
  apply (rngl_square_ge_0 Hop Hor).
}
do 2 rewrite fold_rngl_squ.
rewrite rngl_squ_sqrt.
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
progress unfold rl_has_integral_modulus in Hmi.
remember (rl_opt_integral_modulus_prop T) as im eqn:Him.
symmetry in Him.
destruct im as [H2| ]; [ clear Hmi | easy ].
clear Him.
split. {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    remember (rngl_squ x + rngl_squ y)%L as a eqn:Ha.
    symmetry in Ha.
    apply (rngl_lt_iff Hor).
    split. {
      apply (rl_sqrt_prop Hor).
      rewrite <- Ha.
      rewrite <- (rngl_add_0_r 0%L).
      apply (rngl_add_le_compat Hor); apply (rngl_square_ge_0 Hop Hor).
    } {
      intros H3; symmetry in H3.
      apply (f_equal rngl_squ) in H3.
      progress unfold rngl_squ in H3 at 2.
      rewrite (rngl_mul_0_l Hos) in H3.
      rewrite rngl_squ_sqrt in H3.
      move H3 at top; subst a.
      apply H2 in Ha.
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
    apply (rl_sqrt_prop Hor).
    apply (rngl_add_nonneg_nonneg Hor); apply (rngl_square_ge_0 Hop Hor).
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
      apply (rl_sqrt_prop Hor).
      rewrite <- Ha.
      rewrite <- (rngl_add_0_r 0%L).
      apply (rngl_add_le_compat Hor); apply (rngl_square_ge_0 Hop Hor).
    } {
      intros H3; symmetry in H3.
      apply (f_equal rngl_squ) in H3.
      progress unfold rngl_squ in H3 at 2.
      rewrite (rngl_mul_0_l Hos) in H3.
      rewrite rngl_squ_sqrt in H3.
      move H3 at top; subst a.
      apply H2 in Ha.
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
    apply (rl_sqrt_prop Hor).
    apply (rngl_add_nonneg_nonneg Hor); apply (rngl_square_ge_0 Hop Hor).
  }
}
Qed.

(* to be completed
Theorem all_gc_has_nth_root :
  ∀ n, n ≠ 0 → ∀ z : GComplex T, ∃ x : GComplex T, gc_power_nat x n = z.
Proof.
intros * Hnz *.
About rl_acos.
Theorem polar :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  rl_has_integral_modulus T = true →
  ∀ (z : GComplex T) ρ θ,
  z ≠ gc_zero
  → ρ = rl_sqrt (rngl_squ (gre z) + rngl_squ (gim z))%L
  → θ =
       (if rngl_leb 0%L (gim z) then rl_acos (gre z / ρ)
        else (- rl_acos (gre z / ρ))%L)
  → z = mk_gc (ρ * rl_cos θ) (ρ * rl_sin θ).
Proof.
intros * Hic Hon Hop Hiv Hed Hor Hmi * Hz Hρ Hθ.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [H10| H10]. {
  specialize (rngl_characteristic_1 Hon Hos H10) as H1.
  destruct z as (rz, iz).
  f_equal; rewrite H1; apply H1.
}
subst θ.
(**)
destruct z as (zr, zi).
cbn in Hρ |-*.
f_equal. {
  remember (0 ≤? zi)%L as c eqn:Hc; symmetry in Hc.
  destruct c. {
    apply rngl_leb_le in Hc.
    specialize rl_opt_cos_acos as H1.
    rewrite Hor in H1.
    rewrite H1.
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
