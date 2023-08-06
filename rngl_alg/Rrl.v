(* complex numbers *)
(* see also Quaternions.v *)

Set Nested Proofs Allowed.
Require Import Utf8 Reals.
Require Import Main.Misc Main.RingLike.

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

Definition is_Cauchy_sequence (u : nat → T) :=
  ∀ ε : T, (0 < ε)%L →
  ∃ N : nat, ∀ p q : nat, N ≤ p → N ≤ q → (rngl_abs (u p - u q) ≤ ε)%L.

Definition is_limit_when_tending_to f a l :=
  (∀ ε, 0 < ε → ∃ η, 0 < η ∧
   ∀ x, rngl_abs (x - a) ≤ η → rngl_abs (f x - l) ≤ ε)%L.

Definition is_limit_when_tending_to_inf f l :=
  ∀ ε, (0 < ε)%L → ∃ N,
  ∀ n, N < n → (rngl_abs (f n - l) ≤ ε)%L.

Definition is_complete :=
  ∀ u, is_Cauchy_sequence u → ∃ c, is_limit_when_tending_to_inf u c.

Definition continuous_at f a := is_limit_when_tending_to f a (f a).
Definition continuous f := ∀ a, continuous_at f a.

Definition is_derivative f f' :=
  ∀ a, is_limit_when_tending_to (λ x, (f x - f a) / (x - a))%L a (f' a).

End a.

Arguments is_complete T {ro}.

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

Theorem rl_forall_or_exist_not {T} {ro : ring_like_op T}
    {rp : ring_like_prop T} {rl : real_like_prop T} :
  ∀ (P : T → Prop), {∀ x, P x} + {∃ x, ¬ P x}.
Proof.
intros.
specialize (rl_excl_midd (∃ x, ¬ P x)) as H2.
destruct H2 as [H2| H2]; [ now right | left ].
intros.
specialize (rl_excl_midd (P x)) as H3.
destruct H3 as [H3| H3]; [ easy | ].
exfalso; apply H2.
now exists x.
Qed.

Definition rl_has_mod_intgl {T} {ro : ring_like_op T}
    {rp : ring_like_prop T} {rl : real_like_prop T} :=
  bool_of_option rl_opt_mod_intgl_prop.

Arguments rl_acos {T ro rp real_like_prop} x%L.
Arguments rl_cos {T ro rp real_like_prop} x%L.
Arguments rl_exp {T ro rp real_like_prop} x%L.
Arguments rl_has_mod_intgl T {ro rp rl}.
Arguments rl_opt_mod_intgl_prop T {ro rp real_like_prop}.
Arguments rl_log {T ro rp real_like_prop} x%L.
Arguments rl_sin {T ro rp real_like_prop} x%L.
Arguments rl_has_trigo T {ro rp real_like_prop}.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition gc_opt_inv_or_quot :
  option ((GComplex T → GComplex T) + (GComplex T → GComplex T → GComplex T)) :=
  match rngl_opt_inv_or_quot T with
  | Some (inl inv) =>
      if rngl_mul_is_comm T then
        if rl_has_mod_intgl T then Some (inl gc_inv) else None
      else None
  | Some (inr quot) =>
      None (* à voir *)
  | None =>
      None
  end.

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

Definition gc_exp (z : GComplex T) :=
  mk_gc
    ((rl_exp (gre z) * rl_cos (gre z))%L)
    ((rl_exp (gre z) * rl_sin (gre z))%L).

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
  rl_has_mod_intgl T = true →
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
rewrite Hic, Hrl.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ now destruct iq | easy ].
Qed.

Theorem gc_inv_im :
  let roc := gc_ring_like_op T in
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  rl_has_mod_intgl T = true →
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
rewrite Hic, Hrl.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ now destruct iq | easy ].
Qed.

Theorem gc_opt_mul_inv_l :
  let roc := gc_ring_like_op T in
  rngl_has_opp T = true →
  if (rngl_has_inv (GComplex T) && rngl_has_1 (GComplex T))%bool then
    ∀ a : GComplex T, a ≠ 0%L → (a⁻¹ * a)%L = 1%L
  else not_applicable.
Proof.
intros * Hop.
remember (rl_has_mod_intgl T) as hrl eqn:Hrl; symmetry in Hrl.
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
  unfold rl_has_mod_intgl in H.
  destruct (rl_opt_mod_intgl_prop T) as [H3| ]; [ clear H | easy ].
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
remember (rl_has_mod_intgl T) as hrl eqn:Hrl; symmetry in Hrl.
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
now destruct (rl_has_mod_intgl T).
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
now destruct (rl_has_mod_intgl T).
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
  ∀ a, continuous_at rl_exp a.
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
apply (rngl_mul_le_mono_pos_r Hop Hor) in H1; [ easy | | ]. {
  rewrite Hi1.
  apply Bool.orb_true_r.
} {
  apply (rl_exp_gt_0 Hon Hop Hiv Hc2 Hor Htr).
}
Qed.

(**)

Definition is_upper_bound (Q : T → Type) c :=
  rl_forall_or_exist_not (λ x : T, Q x → (x ≤ c)%L).

Definition is_supremum (Q : T → Type) c :=
  match is_upper_bound Q c with
  | left _ => ∀ c', if is_upper_bound Q c' then (c ≤ c')%L else True
  | right _ => False
  end.

Fixpoint bisection (P : T → bool) lb ub n :=
  match n with
  | 0 => lb
  | S n' =>
      let x := ((lb + ub) / 2)%L in
      if P x then bisection P x ub n'
      else bisection P lb x n'
  end.

(* to be defined with "bisection", perhaps? *)
Fixpoint AnBn (P : T → Type) (An Bn : T) n :=
  match n with
  | 0 => Bn
  | S n' =>
      let A := ((An + Bn) / 2)%L in
      if is_upper_bound P A then AnBn P An A n'
      else AnBn P A Bn n'
  end.

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

Theorem rngl_archimedean_ub :
  rngl_is_archimedean T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a < b)%L →
  ∃ n : nat, (rngl_mul_nat a n ≤ b < rngl_mul_nat a (n + 1))%L.
Proof.
intros Har Hor * (Ha, Hab).
specialize rngl_opt_archimedean as H1.
rewrite Har, Hor in H1; cbn in H1.
specialize (H1 a b Ha).
destruct H1 as (m, Hm).
induction m. {
  exfalso; cbn in Hm.
  apply (rngl_nle_gt Hor) in Hm.
  apply Hm; clear Hm.
  now apply (rngl_le_trans Hor _ a); apply (rngl_lt_le_incl Hor).
}
destruct (rngl_le_dec Hor (rngl_mul_nat a m) b) as [Hba| Hba]. {
  now exists m; rewrite Nat.add_1_r.
}
apply (rngl_nle_gt Hor) in Hba.
now apply IHm.
Qed.

Theorem int_part :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  rngl_is_archimedean T = true →
  ∀ a, ∃ n, (rngl_of_nat n ≤ rngl_abs a < rngl_of_nat (n + 1))%L.
Proof.
intros Hon Hop Hc1 Hor Har *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
specialize (rngl_archimedean_ub Har Hor) as H1.
destruct (rngl_lt_dec Hor (rngl_abs a) 1) as [H1x| H1x]. {
  exists 0; cbn.
  rewrite rngl_add_0_r.
  split; [ | easy ].
  apply (rngl_0_le_abs Hop Hor).
}
destruct (rngl_lt_dec Hor 1 (rngl_abs a)) as [Hx1| Hx1]. 2: {
  apply (rngl_nlt_ge Hor) in H1x, Hx1.
  apply (rngl_le_antisymm Hor) in H1x; [ | easy ].
  rewrite H1x.
  exists 1; cbn.
  rewrite rngl_add_0_r.
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_lt_iff Hor).
  split. 2: {
    intros H12.
    apply (f_equal (λ b, rngl_sub b 1)) in H12.
    rewrite (rngl_sub_diag Hos) in H12.
    rewrite (rngl_add_sub Hos) in H12.
    symmetry in H12; revert H12.
    apply (rngl_1_neq_0_iff Hon), Hc1.
  }
  apply (rngl_le_add_r Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
clear H1x.
apply (H1 1 (rngl_abs a))%L.
split; [ apply (rngl_0_lt_1 Hon Hop Hc1 Hor) | easy ].
Qed.

(* to be completed
Theorem least_upper_bound :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  rngl_is_archimedean T = true →
  is_complete T →
  ∀ (P : T → Prop) a b,
  P a
  → (∀ x, P x → (x < b)%L)
  → ∃ c, is_supremum P c ∧ (c ≤ b)%L.
Proof.
intros Hon Hop Hc1 Hor Har Hco * Ha Hs.
(* Proof in
   https://en.wikipedia.org/wiki/Least-upper-bound_property#Proof_using_Cauchy_sequences *)
unfold is_supremum.
progress unfold is_complete in Hco.
set (v := AnBn P a b).
assert (H : is_Cauchy_sequence v). {
  unfold is_Cauchy_sequence.
  intros ε Hε.
  (* N = int ((b - a) / ε + 1), truc comme ça
     mais pour que "int" existe, il faut que T soit archimédien *)
  specialize (int_part Hon Hop Hc1 Hor Har) as H1.
  specialize (H1 ((b - a) / ε + 1))%L.
  destruct H1 as (N, HN).
  exists N.
  intros * Hp Hq.
...

Theorem rl_sqrt_div_squ_squ :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  rl_has_mod_intgl T = true →
  rl_has_trigo T = true →
  ∀ x y, (x ≠ 0 ∨ y ≠ 0)%L →
  (-1 ≤ x / rl_sqrt (rngl_squ x + rngl_squ y) ≤ 1)%L.
Proof.
intros * Hon Hop Hiv Heb Hor Hmi Htr * Hxyz.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
unfold rl_sqrt.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hxy| Hxy]. {
  apply (rngl_eqb_eq Heb) in Hxy.
  progress unfold rl_has_mod_intgl in Hmi.
  destruct (rl_opt_mod_intgl_prop T) as [H1| ]; [ | easy ].
  apply H1 in Hxy.
  destruct Hxy; subst x y.
  now destruct Hxyz.
}
apply (rngl_abs_le Hop Hor).
rewrite (rngl_abs_div Hon Hop Hiv Heb Hor). 2: {
  apply (rl_pow_neq_0 Hon Hop Hiv Htr).
}
apply (rngl_div_le_1 Hon Hop Hiv Hor). 2: {
  split; [ apply (rngl_0_le_abs Hop Hor) | ].
Theorem le_rngl_abs_rl_sqrt_add :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_characteristic T ≠ 2 →
  rngl_is_ordered T = true →
  rl_has_trigo T = true →
  ∀ a b, (0 ≤ b → a ≤ rngl_abs (rl_sqrt (rngl_squ a + b)))%L.
Proof.
intros * Hon Hop Hiv Heb Hc2 Hor Htr * Hzb.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_and_1_or_quot_iff.
  now rewrite Hiv, Hon; left.
}
progress unfold rl_sqrt.
remember (rngl_squ _ + _ =? _)%L as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  apply (rngl_eqb_eq Heb) in Hab.
  rewrite (rngl_abs_0 Hop).
  apply (rngl_add_sub_eq_l Hos) in Hab.
  progress unfold rngl_sub in Hab.
  rewrite Hop, rngl_add_0_l in Hab.
  subst b.
  apply (rngl_opp_le_compat Hop Hor) in Hzb.
  rewrite (rngl_opp_involutive Hop) in Hzb.
  rewrite (rngl_opp_0 Hop) in Hzb.
  specialize (rngl_square_ge_0 Hop Hor a) as H1.
  unfold rngl_squ in Hzb.
  specialize (rngl_le_antisymm Hor _ _ Hzb H1) as H2.
  specialize (rngl_integral Hos) as H3.
  rewrite Hi1, Heb in H3; cbn in H3.
  rewrite Bool.orb_true_r in H3.
  specialize (H3 eq_refl).
  apply H3 in H2.
  destruct H2; subst a; apply (rngl_le_refl Hor).
}
rewrite (rngl_abs_nonneg Hop Hor). 2: {
  apply (rl_pow_ge_0 Hon Hop Hiv Hc2 Hor Htr).
}
unfold rl_pow.
destruct (rngl_le_dec Hor a 0)%L as [Haz| Haz]. {
  apply (rngl_le_trans Hor _ 0%L); [ easy | ].
  apply (rl_exp_ge_0 Hon Hop Hiv Hc2 Hor Htr).
}
apply (rngl_nle_gt Hor) in Haz.
specialize rl_opt_exp_log as H1.
rewrite Htr in H1.
rewrite <- (H1 a Haz) at 1.
Theorem rl_exp_increasing :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  rl_has_trigo T = true →
  (1 < rl_exp 1 → ∀ a b, a ≤ b → rl_exp a ≤ rl_exp b)%L.
Proof.
intros * Hon Hop Hiv Hc2 Heb Hor Htr He1 * Hab.
destruct (rngl_eq_dec Heb a b) as [Haeb| Haeb]. {
  subst b; apply (rngl_le_refl Hor).
}
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ clear Haeb | easy ].
apply (rngl_lt_le_incl Hor).
specialize (rl_exp_continuous Hon Hop Hiv Hc2 Heb Hor Htr) as H1.
progress unfold continuous_at in H1.
progress unfold is_limit_when_tending_to in H1.
specialize (H1 a) as Ha.
specialize (H1 b) as Hb.
(*
https://uel.unisciel.fr/mathematiques/analyse3/analyse3_ch01/co/apprendre_ch01_02.html
*)
Theorem intermediate_value :
  ∀ f, continuous f
  → ∀ a b u, (a ≤ b)%L
  → (rngl_min (f a) (f b) ≤ u ≤ rngl_max (f a) (f b))%L
  → ∃ c, (a ≤ c ≤ b)%L ∧ f c = u.
Proof.
intros * Hfc * Hab Hfab.
progress unfold rngl_min in Hfab.
progress unfold rngl_max in Hfab.
remember (f a ≤? f b)%L as ab eqn:Hlab; symmetry in Hlab.
destruct ab. {
(* https://en.wikipedia.org/wiki/Intermediate_value_theorem#Proof *)
Theorem intermediate_value_le :
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  is_complete T →
  ∀ f, continuous f
  → ∀ a b u, (a ≤ b)%L
  → (f a ≤ u ≤ f b)%L
  → ∃ c : T, (a ≤ c ≤ b)%L ∧ f c = u.
Proof.
intros * Heb Hor Hco * Hfc * Hab Hfab.
destruct (rngl_eq_dec Heb (f a) u) as [Hau| Hau]. {
  exists a.
  split; [ | easy ].
  split; [ apply (rngl_le_refl Hor) | easy ].
}
destruct (rngl_eq_dec Heb (f b) u) as [Hbu| Hbu]. {
  exists b.
  split; [ | easy ].
  split; [ easy | apply (rngl_le_refl Hor) ].
}
assert (H : (f a < u < f b)%L). {
  apply not_eq_sym in Hbu.
  now split; apply (rngl_lt_iff Hor).
}
clear Hfab Hau Hbu; rename H into Hfab.
assert (H : (a < b)%L). {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; subst b.
  destruct Hfab as (Hfau, Hfua).
  apply (rngl_lt_trans Hor u) in Hfau; [ | easy ].
  now apply (rngl_lt_irrefl Hor) in Hfau.
}
move H before Hab; clear Hab; rename H into Hab.
set (P := λ x : T, (a ≤ x ≤ b)%L ∧ (f x < u)%L).
set (s := { x | P x }).
assert (Ha : P a). {
  unfold P; cbn.
  split; [ | easy ].
  split; [ apply (rngl_le_refl Hor) | now apply (rngl_lt_le_incl Hor) ].
}
(*
assert (xa : s). {
  exists a.
  split; [ | easy ].
  split; [ apply (rngl_le_refl Hor) | now apply (rngl_lt_le_incl Hor) ].
}
*)
assert (Hs : ∀ x : s, (proj1_sig x < b)%L). {
  intros.
  destruct x as (x & (Hax & Hxb) & Hx); cbn.
  destruct Hfab as (Hfau & Hufb).
  apply (rngl_lt_eq_cases Hor) in Hxb.
  destruct Hxb as [Hxb| Hxb]; [ easy | subst x ].
  move Hufb at bottom.
  now apply (rngl_lt_asymm Hor) in Hx.
}
(* "Since S is non-empty and bounded above by b, by completeness, the
    supremum c = sup S exists" *)
set (Q := λ y, (∃ x, y = f x ∧ a ≤ x ≤ b)%L ∧ (y < u)%L).
specialize (least_upper_bound Q) as H1.
(**)
specialize (H1 (f a) (f b)).
assert (H : Q (f a)). {
  split; [ | easy ].
  exists a.
  split; [ easy | ].
  split; [ apply (rngl_le_refl Hor) | ].
  now apply (rngl_lt_le_incl Hor).
}
specialize (H1 H); clear H.
assert (H : (∀ x, Q x → (x < f b)%L)). {
  intros y (Hx & Hy).
  now apply (rngl_lt_trans Hor _ u).
}
specialize (H1 H); clear H.
destruct H1 as (c & Hc & H1).
progress unfold is_supremum in Hc.
remember (is_upper_bound _ _) as Hub1 eqn:Hub2; symmetry in Hub2.
destruct Hub1 as [Hub1| ]; [ | easy ].
progress unfold is_upper_bound in Hub2.
destruct (rl_forall_or_exist_not _) as [Hub3| ]; [ | easy ].
clear Hub2 Hub3.
enough (H : ∃ d, _) by apply H.
(* probably must use continuity of f to prove that c has an
   antecedent *)
...
specialize (H1 (f a) u).
assert (H : Q (f a)). {
  split; [ | easy ].
  exists a.
  split; [ easy | ].
  split; [ apply (rngl_le_refl Hor) | ].
  now apply (rngl_lt_le_incl Hor).
}
specialize (H1 H); clear H.
assert (H : (∀ x, Q x → (x < u)%L)). {
  now intros y (Hx & Hy).
}
specialize (H1 H); clear H.
destruct H1 as (c & Hc & H1).
progress unfold is_supremum in Hc.
remember (is_upper_bound _ _) as Hub1 eqn:Hub2; symmetry in Hub2.
destruct Hub1 as [Hub1| ]; [ | easy ].
progress unfold is_upper_bound in Hub2.
destruct (rl_forall_or_exist_not _) as [Hub3| ]; [ | easy ].
clear Hub2 Hub3.
enough (H : ∃ d, _) by apply H.
(* probably must use continuity of f to prove that c has an
   antecedent *)
...
clear Hc.
destruct H1 as [Hc| Hc]. 2: {
  destruct Hc as (c', Hc).
  destruct (is_upper_bound Q c') as [H1| H1]; [ | easy ].
  apply (rngl_nle_gt Hor) in Hc.
  specialize (Hub1 c') as H2.
  specialize (H1 c) as H3.
  assert (H : Q c). {
    progress unfold Q.
...
specialize (least_upper_bound (λ x, (f a ≤ x ≤ f b ∧ x < u)%L)) as H1.
specialize (H1 (f a) u).
cbn in H1.
assert (H : (f a ≤ f a ≤ f b ∧ f a < u)%L). {
  split; [ | easy ].
  split; [ apply (rngl_le_refl Hor) | ].
  now apply (rngl_le_trans Hor _ u); apply (rngl_lt_le_incl Hor).
}
specialize (H1 H); clear H.
assert (H : ∀ x, (f a ≤ x ≤ f b)%L ∧ (x < u)%L → (x < u)%L) by easy.
specialize (H1 H); clear H.
destruct H1 as (c, Hc).
unfold is_supremum in Hc.
remember (is_upper_bound _ _) as Hub1 eqn:Hub2; symmetry in Hub2.
destruct Hub1 as [Hub1| ]; [ | easy ].
(* ouais, y a un truc à voir dans la définition de is_supremum
   ou alors, c'est least_upper_bound qui ne va pas ; parce qu'il
   faut que ce soit "least", donc que ça ne tombe pas sur "Some False" *)
...
clear Hc.
unfold is_upper_bound in Hub2.
Check rl_forall_or_exist_not.
...
... ...
(* "That is, c is the smallest number that is greater than or equal to
    every member of s" *)
assert
  (∃ c,
    (∀ x : s, (proj1_sig x ≤ c)%L) ∧
    (∀ c', (∀ x : s, (proj1_sig x ≤ c')%L → (c ≤ c')%L))). {
    set (Ps := λ x : T, (a ≤ x ≤ b)%L ∧ (f x < u)%L) in s.
    assert (∃ c, rngl_is_supremum Ps c). {
subst s.
.... ...
  now apply intermediate_value_le.
...
intros * Hon Hop Hiv Hc2 Hor Htr He1 * Hab.
apply (rngl_le_0_sub Hop Hor) in Hab.
rewrite <- (rngl_sub_add Hop b a).
rewrite (rl_exp_add Htr).
rewrite <- (rngl_mul_1_l Hon) at 1.
apply (rngl_mul_le_compat_nonneg Hor Hop). 2: {
  split; [ | apply (rngl_le_refl Hor) ].
  apply (rl_exp_ge_0 Hon Hop Hiv Hc2 Hor Htr).
}
split; [ apply (rngl_0_le_1 Hon Hop Hor) | ].
Theorem rl_exp_nonneg_ge_1 {T} {ro : ring_like_op T}
  {rp : ring_like_prop T} {rl : real_like_prop T} :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  rl_has_trigo T = true →
  (1 < rl_exp 1 → ∀ x, 0 ≤ x → 1 ≤ rl_exp x)%L.
Proof.
intros Hon Hop Hiv Hc2 Heb Hor Htr * He1 * Hzx.
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
move x after He1.
(* since rl_log is supposed to be the inverse of rl_exp,
   rl_exp must be monotonic. No need to use derivative. *)
...
specialize (rl_exp_continuous Hon Hop Hiv Hc2 Heb Hor Htr) as H1.
progress unfold continuous_at in H1.
progress unfold is_limit_when_tending_to in H1.
specialize (H1 0)%L as H2.
specialize (H2 (rl_exp x - rl_exp 1))%L.
assert (H : (0 < rl_exp 1 - 1)%L) by _admit.
specialize (H2 H); clear H.
destruct H2 as (η & Hzη & Hη).
rewrite (rl_exp_0 Hon Hiq Htr) in Hη.
...
Print is_limit_when_tending_to.
Theorem rl_exp_derivative_prop {T} {ro : ring_like_op T}
  {rp : ring_like_prop T} {rl : real_like_prop T} :
  ∀ f', is_derivative rl_exp f' →
  ∀ x, f' x = (f' 0 * rl_exp x)%L.
Proof.
intros * Hff' *.
progress unfold is_derivative in Hff'.
Theorem rl_exp_derivative_exists {T} {ro : ring_like_op T}
  {rp : ring_like_prop T} {rl : real_like_prop T} :
  ∃ f', is_derivative rl_exp f'.
Proof.
intros.
progress unfold is_derivative.
Print is_derivative.
Theorem glop {T} {ro : ring_like_op T}
  {rp : ring_like_prop T} {rl : real_like_prop T} :
  is_complete T →
  ∃ c, (is_limit_when_tending_to (λ x, (rl_exp x - 1) / x) 0 c)%L.
Proof.
intros Hc.
unfold is_complete in Hc.
Print is_limit_when_tending_to.
Theorem glop {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ f a l,
  is_limit_when_tending_to f a l
  → is_limit_when_tending_to_inf (λ n, f (a + 1 / rngl_of_nat n)%L) l.
Proof.
intros Hos Hor * Hlim.
progress unfold is_limit_when_tending_to in Hlim.
progress unfold is_limit_when_tending_to_inf.
intros ε Hε.
specialize (Hlim ε Hε).
destruct Hlim as (η & Hzη & Hη).
specialize (Hη (a + η)%L).
rewrite rngl_add_comm in Hη at 1.
rewrite (rngl_add_sub Hos) in Hη.
assert (H : (rngl_abs η ≤ η)%L). {
  unfold rngl_abs.
  remember (η ≤? 0)%L as ηz eqn:Hηz; symmetry in Hηz.
  destruct ηz; [ | apply (rngl_le_refl Hor) ].
  apply rngl_leb_le in Hηz.
  now apply (rngl_nlt_ge Hor) in Hηz.
}
specialize (Hη H); clear H.
...
(* hou, là... j'ai peur qu'il faille ajouter que T est archimédien... *)
(* pourquoi pas, mais bon... *)
exists (1 / η).
...
assert
  (H :
    is_Cauchy_sequence
      (λ n, (rngl_of_nat n * rl_exp (1 / rngl_of_nat n - 1)))%L). {
  intros ε Hε.
...
exists 0.
intros.
rewrite rngl_mul_nat_add_r.
rewrite rngl_mul_add_distr_r.
Print rngl_mul_nat.
...
Theorem rl_exp_derivative_prop {T} {ro : ring_like_op T}
  {rp : ring_like_prop T} {rl : real_like_prop T} :
  ∃ c, is_derivative rl_exp (λ x, rl_exp x * c)%L.
Proof.
intros.
unfold is_derivative.
...
Theorem glop {T} {ro : ring_like_op T}
  {rp : ring_like_prop T} {rl : real_like_prop T} :
  rngl_has_1 T = true →
  ∀ x ε, (0 < ε → ε < rl_exp (x + ε) - rl_exp x)%L.
Proof.
intros * Hon * Hε.
rewrite rl_exp_add.
remember (_ * _)%L as z.
rewrite <- (rngl_mul_1_r Hon (rl_exp x)).
subst z.
rewrite <- rngl_mul_sub_distr_l.
... ...
now apply rl_exp_nonneg_ge_1.
... ...
specialize rl_opt_exp_ln as H1.
rewrite Htr in H1.
rewrite <- (H1 a Haz) at 1.
apply rl_exp_increasing.
... ...
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_and_1_or_quot_iff.
  now rewrite Hiv, Hon; left.
}
specialize (le_rngl_abs_rl_sqrt_add Hop Hi1 Heb Hor) as H1.
specialize (H1 (rngl_abs x) (rngl_squ y)) as H1.
assert (H : (0 ≤ rngl_squ y)%L). {
  progress unfold rngl_squ.
  apply (rngl_square_ge_0 Hop Hor).
}
specialize (H1 H); clear H.
unfold rl_sqrt in H1.
...
intros * Hon Hop Hiv Hor * Haz Hza.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
rewrite <- (rngl_mul_inv_l Hon Hiv a Haz) in H1.
destruct (rngl_le_dec Hor 0 a⁻¹)%L as [H2| H2]; [ easy | ].
apply (rngl_not_le Hor) in H2.
destruct H2 as (H2, H3).
specialize (rngl_mul_nonneg_nonpos Hop Hor) as H4.
specialize (H4 _ _ Hza H3).
Check rngl_not_le.
...
About rngl_squ_opp_1.
Search rngl_inv.
Check rngl_mul_nonneg_nonneg.
...
Require Import ZArith.
Search (0 <= _ * _)%Z.
Z.mul_nonneg_nonneg: ∀ n m : Z, (0 <= n)%Z → (0 <= m)%Z → (0 <= n * m)%Z
...
Check rngl_mul_le_compat_nonneg.
specialize (rngl_mul_le_compat_nonneg Hor Hop 0 (a⁻¹) 1 (a⁻¹))%L as H1.
...
About rngl_inv_neq_0.
Check rngl_mul_move_1_r.
(*
Check rngl_inv_le_0_compat.
*)
Require Import Rational.
Import Q.Notations.
Search Q.inv.
Require Import QArith.
Search (_ <= / _)%Q.
Print Qinv_le_0_compat.
Qinv_le_0_compat
     : ∀ a : Q, 0 <= a → 0 <= / a
...
Check Qopp_le_compat.

Search (_ * _ == 1)%Q.
Search (/ _)%Q.
Search (_⁻¹ ≤ _)%L.
Check rngl_not_le.
...
        exfalso.
Check rngl_mul_le_compat_nonneg.
...
        rewrite (rngl_mul_opp_l Hop).
...
rngl_mul_le_compat_nonneg:
  ∀ (T : Type) (ro : ring_like_op T),
    ring_like_prop T
    → rngl_is_ordered T = true
      → rngl_has_opp T = true → ∀ a b c d : T, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L
rngl_mul_le_compat_nonpos:
  ∀ (T : Type) (ro : ring_like_op T),
    ring_like_prop T
    → rngl_is_ordered T = true
      → rngl_has_opp T = true → ∀ a b c d : T, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L
... ...
rewrite rngl_abs_div.
rngl_abs (x / y) ≤ 1 ↔ rngl_abs x ≤ rngl_abs y
...

Theorem all_gc_has_nth_root {T} {ro : ring_like_op T} :
  ∀ n, n ≠ 0 → ∀ z : GComplex T, ∃ x : GComplex T, gc_power_nat x n = z.
Proof.
intros * Hnz *.
Theorem polar {T} {ro : ring_like_op T} {rp : ring_like_prop T}
  {rl : real_like_prop T} :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rl_has_trigo = true →
  rl_has_mod_intgl T = true →
  ∀ (z : GComplex T) ρ θ,
  z ≠ gc_zero
  → ρ = rl_sqrt (rngl_squ (gre z) + rngl_squ (gim z))%L
  → θ =
      (if rngl_leb 0%L (gim z) then rl_acos (gre z / ρ)
       else (- rl_acos (gre z / ρ))%L)
  → z = mk_gc (ρ * rl_cos θ) (ρ * rl_sin θ).
Proof.
intros * Hic Hon Hop Hiv Heb Htr Hmi * Hz Hρ Hθ.
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
      progress unfold rl_has_mod_intgl in H.
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
    progress unfold rl_has_mod_intgl in H.
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

(* Coq reals as Cauchy sequences *)

Set Nested Proofs Allowed.
Require Import Utf8.
Require Import Reals.Cauchy.ConstructiveCauchyReals.
Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
(*
Require Import Reals.Cauchy.ConstructiveCauchyAbs.
Require Import Reals.Cauchy.ConstructiveRcomplete.
*)
Require Import QArith.
Require Import Main.RingLike.

Axiom CReal_appart_or_eq : ∀ x y, (x # y)%CReal + (x = y).

Definition CReal_eqb x y :=
  match CReal_appart_or_eq x y with
  | inl _ => false
  | inr _ => true
  end.

Theorem CReal_eqb_refl : ∀ x, CReal_eqb x x = true.
Proof.
intros.
unfold CReal_eqb.
destruct (CReal_appart_or_eq x x) as [Hxx| Hxx]; [ exfalso | easy ].
now destruct Hxx; apply (CRealLt_irrefl x).
Qed.

Theorem CReal_appart_irrefl : ∀ x, (x # x)%CReal → False.
Proof.
intros * H1.
now destruct H1 as [H1| H1]; apply CRealLt_irrefl in H1.
Qed.

Theorem CReal_appart_sym : ∀ x y, (x # y)%CReal → (y # x)%CReal.
Proof.
intros * Hxy.
now destruct Hxy; [ right | left ].
Qed.

Theorem eq_CReal_eq : ∀ x y, ((x # y)%CReal → False) ↔ x = y.
Proof.
intros.
split. {
  intros Hxy.
  now destruct (CReal_appart_or_eq x y).
} {
  intros H1; subst y.
  apply CReal_appart_irrefl.
}
Qed.

Theorem CReal_eq_dec : ∀ a b : CReal, {a = b} + {a ≠ b}.
Proof.
intros.
specialize (CReal_appart_or_eq a b) as H1.
destruct H1 as [H1| H1]; [ right | now left ].
intros H; subst b.
now destruct H1 as [H1| H1]; apply CRealLt_irrefl in H1.
Qed.

Definition CReal_inv' (x : CReal) : CReal :=
  match CReal_appart_or_eq x 0%CReal with
  | inl H => CReal_inv x H
  | inr _ => inject_Q 0
  end.

Definition CReal_div (x y : CReal) := (x * CReal_inv' y)%CReal.

Notation "x / y" := (CReal_div x y) : CReal_scope.

Definition CReal_ring_like_op : ring_like_op CReal :=
  {| rngl_zero := 0%CReal;
     rngl_add := CReal_plus;
     rngl_mul := CReal_mult;
     rngl_opt_one := Some 1%CReal;
     rngl_opt_opp_or_subt := Some (inl CReal_opp);
     rngl_opt_inv_or_quot := Some (inl CReal_inv');
     rngl_opt_eq_dec := Some CReal_eq_dec;
     rngl_opt_leb := None (*Some CRealLe*) |}.

(*
Print Assumptions CReal_ring_like_op.
*)

Theorem CReal_add_comm : let ro := CReal_ring_like_op in
  ∀ a b : CReal, (a + b)%L = (b + a)%L.
Proof.
intros; cbn.
apply eq_CReal_eq.
intros H1.
rewrite CReal_plus_comm in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_add_assoc : let ro := CReal_ring_like_op in
  ∀ a b c : CReal, (a + (b + c))%L = (a + b + c)%L.
Proof.
intros; cbn.
apply eq_CReal_eq.
intros H1.
rewrite CReal_plus_assoc in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_add_0_l : let ro := CReal_ring_like_op in
  ∀ a : CReal, (0 + a)%L = a.
Proof.
intros; cbn.
apply eq_CReal_eq.
intros H1.
rewrite CReal_plus_0_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_assoc : let ro := CReal_ring_like_op in
  ∀ a b c : CReal, (a * (b * c))%L = (a * b * c)%L.
Proof.
intros; cbn.
apply eq_CReal_eq.
intros H1.
rewrite CReal_mult_assoc in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_1_l : let ro := CReal_ring_like_op in
  ∀ a : CReal, (1 * a)%L = a.
Proof.
cbn; intros.
apply eq_CReal_eq.
intros H1.
rewrite CReal_mult_1_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_add_distr_l : let ro := CReal_ring_like_op in
  ∀ a b c : CReal, (a * (b + c))%L = (a * b + a * c)%L.
Proof.
cbn; intros.
apply eq_CReal_eq.
intros H1.
rewrite CReal_mult_plus_distr_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_comm : let ro := CReal_ring_like_op in
  ∀ a b : CReal, (a * b)%L = (b * a)%L.
Proof.
cbn; intros.
apply eq_CReal_eq.
intros H1.
rewrite CReal_mult_comm in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_add_opp_l : let ro := CReal_ring_like_op in
  ∀ a : CReal, (- a + a)%L = 0%L.
Proof.
cbn; intros.
apply eq_CReal_eq.
intros H1.
rewrite CReal_plus_opp_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_inv_l : let ro := CReal_ring_like_op in
  ∀ a : CReal, a ≠ 0%L → (a⁻¹ * a)%L = 1%L.
Proof.
cbn; intros * Haz.
apply eq_CReal_eq.
intros H1.
unfold CReal_inv' in H1.
destruct (CReal_appart_or_eq _ _) as [H2| H2]; [ | easy ].
rewrite CReal_inv_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_eqb_eq : ∀ x y, CReal_eqb x y = true ↔ x = y.
Proof.
intros.
split; intros Hxy; [ | subst y; apply CReal_eqb_refl ].
unfold CReal_eqb in Hxy.
now destruct (CReal_appart_or_eq x y).
Qed.

(*
Theorem CReal_le_dec : let ro := CReal_ring_like_op in
  ∀ a b : CReal, {(a ≤ b)%L} + {¬ (a ≤ b)%L}.
Proof.
cbn; intros.
destruct (CReal_appart_or_eq a b) as [Hab| Hab]. {
  destruct Hab as [Hab| Hba]. {
    now left; apply CRealLt_asym.
  } {
    now right.
  }
}
subst b; left.
apply CRealLe_refl.
Qed.
*)

Theorem CReal_characteristic_prop : let ro := CReal_ring_like_op in
  ∀ i : nat, rngl_of_nat (S i) ≠ 0%L.
Proof.
intros * H1.
apply eq_CReal_eq in H1; [ easy | clear H1 H ].
right.
cbn - [ rngl_mul_nat ].
induction i. {
  rewrite <- CReal_plus_0_l at 1.
  apply CReal_plus_lt_compat_r.
  now apply inject_Q_lt.
}
remember (S i) as si; cbn; subst si.
apply CReal_lt_trans with (y := 1%CReal). {
  now apply inject_Q_lt.
}
apply CReal_plus_lt_compat_l with (x := 1%CReal) in IHi.
now rewrite CReal_plus_0_r in IHi.
Qed.

Theorem CReal_le_antisymm : let ro := CReal_ring_like_op in
  ∀ a b : CReal, (a ≤ b)%L → (b ≤ a)%L → a = b.
Proof.
cbn; intros * Hab Hba.
apply eq_CReal_eq.
intros H1.
now destruct H1.
Qed.

(*
Theorem CReal_mul_le_compat_nonneg : let ro := CReal_ring_like_op in
  ∀ a b c d : CReal, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
cbn; intros * Hac Hbd.
apply CReal_le_trans with (y := (a * d)%CReal). {
  now apply CReal_mult_le_compat_l.
} {
  apply CReal_mult_le_compat_r; [ | easy ].
  now apply CReal_le_trans with (y := b).
}
Qed.
*)

(*
Theorem CReal_mul_le_compat_nonpos : let ro := CReal_ring_like_op in
  ∀ a b c d : CReal, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
cbn; intros * Hac Hbd.
rewrite <- CReal_opp_involutive.
rewrite <- (CReal_opp_involutive (c * d)).
rewrite CReal_opp_mult_distr_l.
rewrite CReal_opp_mult_distr_r.
rewrite CReal_opp_mult_distr_l.
rewrite CReal_opp_mult_distr_r.
destruct Hac as (Hca, Haz).
destruct Hbd as (Hdb, Hbz).
apply CReal_opp_ge_le_contravar in Hca, Haz, Hdb, Hbz.
rewrite <- opp_inject_Q in Haz, Hbz.
apply CReal_le_trans with (y := (- a * - d)%CReal). {
  now apply CReal_mult_le_compat_l.
} {
  apply CReal_mult_le_compat_r; [ | easy ].
  now apply CReal_le_trans with (y := (- b)%CReal).
}
Qed.
*)

(*
Theorem CReal_not_le : let ro := CReal_ring_like_op in
  ∀ a b : CReal, ¬ (a ≤ b)%L → a = b ∨ (b ≤ a)%L.
Proof.
cbn; intros * Hab.
destruct (CReal_appart_or_eq a b) as [Haeb| Haeb]; [ | now left ].
right.
now destruct Haeb as [H1| H1]; apply CRealLt_asym in H1.
Qed.
*)

Definition CReal_ring_like_prop : ring_like_prop CReal :=
  {| rngl_mul_is_comm := true;
     rngl_is_integral_domain := false;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := CReal_add_comm;
     rngl_add_assoc := CReal_add_assoc;
     rngl_add_0_l := CReal_add_0_l;
     rngl_mul_assoc := CReal_mul_assoc;
     rngl_opt_mul_1_l := CReal_mul_1_l;
     rngl_mul_add_distr_l := CReal_mul_add_distr_l;
     rngl_opt_mul_comm := CReal_mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := CReal_add_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_l := CReal_mul_inv_l;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_le_dec := NA; (*CReal_le_dec;*)
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := CReal_characteristic_prop;
     rngl_opt_le_refl := NA; (*CRealLe_refl;*)
     rngl_opt_le_antisymm := NA; (*CReal_le_antisymm;*)
     rngl_opt_le_trans := NA; (*CReal_le_trans;*)
     rngl_opt_add_le_compat := NA; (*CReal_plus_le_compat;*)
     rngl_opt_mul_le_compat_nonneg := NA; (*CReal_mul_le_compat_nonneg;*)
     rngl_opt_mul_le_compat_nonpos := NA; (*CReal_mul_le_compat_nonpos;*)
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA (*CReal_not_le*);
     rngl_opt_archimedean := NA |}.

(*
Print Assumptions CReal_ring_like_prop.
*)

(* complex on CReals *)

Record CComplex := mk_cc {cre : CReal; cim : CReal}.

Definition CComplex_zero : CComplex := {| cre := 0%CReal; cim := 0%CReal |}.

Definition CComplex_one : CComplex := {| cre := 1%CReal; cim := 0%CReal |}.

Definition CComplex_add (ca cb : CComplex) : CComplex :=
  {| cre := cre ca + cre cb; cim := cim ca + cim cb |}.

Definition CComplex_mul (ca cb : CComplex) : CComplex :=
  {| cre := cre ca * cre cb - cim ca * cim cb;
     cim := cre ca * cim cb + cim ca * cre cb |}.

Definition CComplex_opp c := mk_cc (- cre c) (- cim c).

Definition CComplex_inv c :=
  let d := (cre c * cre c + cim c * cim c)%CReal in
  mk_cc (cre c / d) (- cim c / d).

Definition CComplex_ring_like_op : ring_like_op CComplex :=
  {| rngl_zero := CComplex_zero;
     rngl_add := CComplex_add;
     rngl_mul := CComplex_mul;
     rngl_opt_one := Some CComplex_one;
     rngl_opt_opp_or_subt := Some (inl CComplex_opp);
     rngl_opt_inv_or_quot := Some (inl CComplex_inv);
     rngl_opt_eq_dec := None;
     rngl_opt_leb := None |}.

(* to be completed

Mais, maintenant que je me suis rendu compte que je n'avais pas besoin
de racine carrée, qu'est-ce qui m'empêche de faire des complexes sur
un type T quelconque ? bon, il lui faut un opposé et un inverse, mais
sinon ?

Definition CComplex_ring_like_prop : ring_like_op CComplex :=
  {| rngl_mul_is_comm := true |}.
...
*)

(* Classical Reals defined by axioms *)

Set Nested Proofs Allowed.
Require Import Utf8 Reals.
Require Import Main.RingLike.

Definition reals_ring_like_op : ring_like_op R :=
  {| rngl_zero := R0;
     rngl_add := Rplus;
     rngl_mul := Rmult;
     rngl_opt_one := Some R1;
     rngl_opt_opp_or_subt := Some (inl Ropp);
     rngl_opt_inv_or_quot := Some (inl Rinv);
     rngl_opt_eq_dec := None;
     rngl_opt_leb := None (*Some Rle*) |}.

(*
Print Assumptions reals_ring_like_op.
*)

Theorem Rminus_plus_distr : ∀ x y z, (x - (y + z) = x - y - z)%R.
Proof.
intros.
unfold Rminus.
rewrite Ropp_plus_distr.
symmetry; apply Rplus_assoc.
Qed.

Theorem Rplus_minus_distr : ∀ x y z, (x + (y - z) = x + y - z)%R.
Proof.
intros.
unfold Rminus.
symmetry; apply Rplus_assoc.
Qed.

Theorem Rmult_mult_swap : ∀ x y z, (x * y * z = x * z * y)%R.
Proof.
intros.
do 2 rewrite Rmult_assoc.
f_equal.
apply Rmult_comm.
Qed.

Theorem Rplus_assoc' : ∀ a b c : R, (a + (b + c))%R = (a + b + c)%R.
Proof. intros; now rewrite Rplus_assoc. Qed.

Theorem Rmult_assoc' : ∀ a b c : R, (a * (b * c))%R = (a * b * c)%R.
Proof. intros; now rewrite Rmult_assoc. Qed.

Theorem Rcharacteristic_prop :
  let ror := reals_ring_like_op in
  ∀ i : nat, rngl_of_nat (S i) ≠ 0%L.
Proof.
intros.
cbn - [ rngl_mul_nat ].
assert (H : ∀ n, rngl_mul_nat R1 n = INR n). {
  intros.
  progress unfold rngl_mul_nat.
  progress unfold mul_nat; cbn.
  induction n; [ easy | cbn ].
  destruct n; [ apply Rplus_0_r | ].
  rewrite IHn.
  apply Rplus_comm.
}
progress unfold rngl_of_nat.
rewrite H.
now apply not_0_INR.
Qed.

(*
Theorem Ropt_mul_le_compat_nonneg :
  let ror := reals_ring_like_op in
  ∀ a b c d : R, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros * Hac Hbd.
now apply Rmult_le_compat.
Qed.
*)

(*
Theorem Ropt_mul_le_compat_nonpos :
  let ror := reals_ring_like_op in
  ∀ a b c d : R, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros * Hca Hdb; cbn.
apply Rle_trans with (r2 := (a * d)%R). {
  now apply Rmult_le_compat_neg_l.
}
rewrite (Rmult_comm a), (Rmult_comm c).
apply Rmult_le_compat_neg_l; [ | easy ].
now apply Rle_trans with (r2 := b).
Qed.
*)

(*
Theorem Ropt_not_le :
  let ror := reals_ring_like_op in
  ∀ a b : R, ¬ (a ≤ b)%L → a = b ∨ (b ≤ a)%L.
Proof.
intros * Hab.
cbn in Hab |-*.
apply Rnot_le_lt in Hab.
specialize (Rle_or_lt b a) as H1.
destruct H1 as [| Hba]; [ now right | left ].
now apply Rlt_asym in Hba.
Qed.
*)

Canonical Structure reals_ring_like_prop : ring_like_prop R :=
  let ro := reals_ring_like_op in
  {| rngl_mul_is_comm := true;
     rngl_is_integral_domain := true;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Rplus_comm;
     rngl_add_assoc := Rplus_assoc';
     rngl_add_0_l := Rplus_0_l;
     rngl_mul_assoc := Rmult_assoc';
     rngl_opt_mul_1_l := Rmult_1_l;
     rngl_mul_add_distr_l := Rmult_plus_distr_l;
     rngl_opt_mul_comm := Rmult_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := Rplus_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_l := Rinv_l;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_le_dec := NA; (*Rle_dec;*)
     rngl_opt_integral := Rmult_integral;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := Rcharacteristic_prop;
     rngl_opt_le_refl := NA; (*Rle_refl;*)
     rngl_opt_le_antisymm := NA; (*Rle_antisym;*)
     rngl_opt_le_trans := NA; (*Rle_trans;*)
     rngl_opt_add_le_compat := NA; (*Rplus_le_compat;*)
     rngl_opt_mul_le_compat_nonneg := NA; (*Ropt_mul_le_compat_nonneg;*)
     rngl_opt_mul_le_compat_nonpos := NA; (*Ropt_mul_le_compat_nonpos;*)
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA (*Ropt_not_le*);
     rngl_opt_archimedean := NA |}.

(* complex numbers *)
(* see also Quaternions.v *)

(*
Record complex := mk_c {re : R; im : R}.

(*
Arguments rngl_has_dec_le T {ro ring_like_prop}.
Arguments rngl_opt_inv_or_quot T {ring_like_op}.
Arguments rngl_opt_one T {ring_like_op}.
*)

Theorem eq_complex_eq :
  ∀ a b : complex, re a = re b ∧ im a = im b ↔ a = b.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct a, b; cbn in Hab.
now f_equal.
Qed.

Theorem neq_complex_neq :
  ∀ a b : complex, re a ≠ re b ∨ im a ≠ im b ↔ a ≠ b.
Proof.
intros *.
split; intros Hab. {
  intros H; subst b.
  now destruct Hab.
}
destruct a as (ra, ia).
destruct b as (rb, ib); cbn.
destruct (Req_dec ra rb) as [Hr| Hr]; [ | now left ].
right.
intros Hi; apply Hab.
now subst.
Qed.

Definition complex_zero : complex := {| re := R0; im := R0 |}.

Definition complex_one : complex := {| re := R1; im := R0 |}.

Definition complex_add (ca cb : complex) : complex :=
  {| re := re ca + re cb; im := im ca + im cb |}.

Definition complex_mul (ca cb : complex) : complex :=
  {| re := (re ca * re cb - im ca * im cb);
     im := (re ca * im cb + im ca * re cb) |}.

Definition complex_opp c := mk_c (- re c) (- im c).

Definition Rsqrt' (a : R) :=
  match Rle_dec R0 a with
  | left Hle => Rsqrt (mknonnegreal a Hle)
  | right _ => R0
  end.

Definition complex_inv (a : complex) :=
  let d := Rsqrt' (re a * re a + im a * im a) in
  mk_c (re a / d) (- im a / d).

Definition complex_ring_like_op : ring_like_op complex :=
  {| rngl_zero := complex_zero;
     rngl_add := complex_add;
     rngl_mul := complex_mul;
     rngl_opt_one := Some complex_one;
     rngl_opt_opp_or_subt := Some (inl complex_opp);
     rngl_opt_inv_or_quot := Some (inl complex_inv);
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

(*
Print Assumptions complex_ring_like_op.
*)

Theorem complex_add_comm : let roc := complex_ring_like_op in
  ∀ a b, (a + b)%L = (b + a)%L.
Proof.
intros; cbn.
progress unfold complex_add.
f_equal; apply Rplus_comm.
Qed.

Theorem complex_add_assoc : let roc := complex_ring_like_op in
  ∀ a b c : complex, (a + (b + c))%L = (a + b + c)%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
split; symmetry; apply Rplus_assoc.
Qed.

Theorem complex_add_0_l : let roc := complex_ring_like_op in
  ∀ a : complex, (0 + a)%L = a.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
split; apply Rplus_0_l.
Qed.

Theorem complex_mul_assoc : let roc := complex_ring_like_op in
  ∀ a b c : complex, (a * (b * c))%L = (a * b * c)%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
do 2 rewrite Rmult_minus_distr_l.
do 2 rewrite Rmult_minus_distr_r.
do 2 rewrite Rmult_plus_distr_l.
do 2 rewrite Rmult_plus_distr_r.
do 8 rewrite <- Rmult_assoc.
rewrite Rplus_comm.
do 2 rewrite Rminus_plus_distr.
split. {
  f_equal.
  rewrite <- Rminus_plus_distr.
  rewrite Rplus_comm.
  apply Rminus_plus_distr.
} {
  progress unfold Rminus.
  do 2 rewrite Rplus_assoc.
  f_equal.
  now rewrite <- Rplus_assoc, Rplus_comm.
}
Qed.

Theorem complex_mul_1_l : let roc := complex_ring_like_op in
  ∀ a : complex, (1 * a)%L = a.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
do 2 rewrite Rmult_1_l.
do 2 rewrite Rmult_0_l.
now rewrite Rminus_0_r, Rplus_0_r.
Qed.

Theorem complex_mul_add_distr_l : let roc := complex_ring_like_op in
  ∀ a b c : complex, (a * (b + c))%L = (a * b + a * c)%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
do 4 rewrite Rmult_plus_distr_l.
rewrite Rminus_plus_distr.
rewrite Rplus_minus_distr.
split. {
  f_equal.
  progress unfold Rminus.
  do 2 rewrite Rplus_assoc.
  f_equal; apply Rplus_comm.
} {
  do 2 rewrite Rplus_assoc.
  f_equal.
  rewrite Rplus_comm, Rplus_assoc.
  f_equal; apply Rplus_comm.
}
Qed.

Theorem complex_mul_comm : let roc := complex_ring_like_op in
  ∀ a b : complex, (a * b)%L = (b * a)%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
do 2 rewrite (Rmult_comm (re b)).
do 2 rewrite (Rmult_comm (im b)).
now rewrite Rplus_comm.
Qed.

Theorem complex_add_opp_l : let roc := complex_ring_like_op in
  ∀ a : complex, (- a + a)%L = 0%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
now do 2 rewrite Rplus_opp_l.
Qed.

(* to be completed
Theorem complex_mul_inv_l : let roc := complex_ring_like_op in
  ∀ a : complex, a ≠ 0%L → (a⁻¹ * a)%L = 1%L.
Proof.
cbn; intros * Haz.
apply eq_complex_eq; cbn.
unfold Rsqrt'.
remember (_ + _)%R as m eqn:Hm.
destruct (Rle_dec R0 m) as [Hmz| Hmz]. 2: {
  exfalso; apply Hmz; clear Hmz; subst m.
  rewrite <- (Rplus_0_l R0); cbn.
  unfold IZR.
  apply Rplus_le_compat. {
    replace (_ * _)%R with (Rsqr (re a)) by easy.
    apply Rle_0_sqr.
  } {
    replace (_ * _)%R with (Rsqr (im a)) by easy.
    apply Rle_0_sqr.
  }
}
unfold Rdiv.
do 2 rewrite <- Ropp_mult_distr_l.
unfold Rminus.
rewrite Ropp_involutive.
rewrite (Rmult_mult_swap (re a)).
rewrite (Rmult_mult_swap (im a)).
rewrite <- Rmult_plus_distr_r, <- Hm.
(* mais putain, chuis nul, y a pas de racine carrée ! *)
...
do 2 rewrite (Rmult_mult_swap (im a)).

rewrite (Rmult_mult_swap (im a)).
...
Search (Rsqr _ = _ * _)%R.
Search (_ * _ = Rsqr _)%R.
Search (_ ^ _ = _ * _)%R.
Search (_ * _ = _ ^ _)%R.
Search Rsqr.
Print Rsqr.
fold Rsqr.
...
Rle_0_sqr: ∀ r : R, (0 <= r²)%R
Search (_ <= _ * _)%R.
Search (0 <= _ * _)%R.
Search (R0 <= _ * _)%R.
Search (_ * _ <= _ * _)%R.
...
intros * Hop Heb Hor Hdl.
clear Heb.
remember (rngl_has_inv complex) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 complex) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ cbn | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honc; cbn in Honc.
  progress unfold complex_opt_one in Honc.
  now destruct (rngl_has_1 T).
}
assert (Hiv : rngl_has_inv T = true). {
  progress unfold rngl_has_inv in Hivc; cbn in Hivc.
  progress unfold complex_opt_inv_or_quot in Hivc.
  progress unfold rngl_has_inv.
  destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
  now destruct iq.
}
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (His : rngl_has_inv_and_1_or_quot T = true). {
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
intros * Haz.
apply eq_complex_eq; cbn.
specialize (rngl_mul_inv_l Hon Hiv) as H1.
assert (Hic : rngl_mul_is_comm T = true). {
  progress unfold rngl_has_inv in Hivc; cbn in Hivc.
  progress unfold complex_opt_inv_or_quot in Hivc.
  progress unfold rngl_has_inv_and_1_or_quot in His.
  rewrite Hon in His.
  destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
  destruct iq as [inv| quot]; [ | easy ].
  now destruct (rngl_mul_is_comm T).
}
rewrite (complex_inv_re Hiv Hic); [ | easy ].
rewrite (complex_inv_im Hiv Hic); [ | easy ].
unfold rngl_div.
rewrite Hiv.
do 2 rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_mul_swap Hic (re a)).
rewrite (rngl_mul_mul_swap Hic (im a)).
progress unfold rngl_sub.
rewrite Hop.
rewrite (rngl_opp_involutive Hop).
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_mul_comm Hic).
split. {
  progress unfold "1"%L; cbn.
  progress unfold complex_opt_one.
  rewrite Hon; cbn.
  apply H1.
  intros Hri.
  apply (eq_rngl_add_square_0 Hop Hor Hdl) in Hri. 2: {
(**)
(* Si un anneau a un inverse, c'est un corps, il est forcément
   intègre, non ? *)
Theorem glop : ∀ T {ro : ring_like_op T} {rp : ring_like_prop T},
  rngl_has_inv T = true → rngl_is_integral_domain T = true.
Proof.
intros * Hiv.
Search rngl_is_integral_domain.
...
rewrite His; cbn.
...
    apply Bool.orb_true_iff; right.
    now rewrite His, Heb.
  }
  destruct Hri as (Hra, Hia); apply Haz.
  apply eq_complex_eq.
  now rewrite Hra, Hia.
}
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_mul_swap Hic).
rewrite rngl_mul_assoc.
rewrite (fold_rngl_sub Hop).
rewrite (rngl_sub_diag Hos).
progress unfold "1"%L.
progress unfold "0"%L.
progress unfold rngl_has_1 in Hon.
remember (rngl_opt_one T) as on eqn:H2; symmetry in H2.
destruct on as [one| ]; [ cbn | easy ].
progress unfold complex_opt_one.
progress unfold rngl_has_1.
rewrite H2; cbn.
progress unfold "1"%L.
now rewrite H2.
Qed.
*)

(* to be completed
Theorem complex_opt_add_sub {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op in
  rngl_has_subt T = false →
  if rngl_has_subt complex then ∀ a b : complex, (a + b - b)%L = a
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_subt; cbn.
progress unfold complex_opt_opp_or_subt.
progress unfold rngl_has_subt in Hsu.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem complex_opt_sub_add_distr {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op in
  rngl_has_subt T = false →
  if rngl_has_subt complex then
    ∀ a b c : complex, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_subt; cbn.
progress unfold complex_opt_opp_or_subt.
progress unfold rngl_has_subt in Hsu.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem complex_inv_re {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op in
  rngl_has_inv T = true →
  rngl_mul_is_comm T = true →
  ∀ a : complex, a ≠ 0%L →
  re a⁻¹ = (re a / (re a * re a + im a * im a))%L.
Proof.
intros * Hiv Hic * Haz.
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
progress unfold rngl_inv; cbn.
progress unfold complex_opt_inv_or_quot.
progress unfold rngl_has_inv_or_quot in Hiq.
progress unfold rngl_div.
rewrite Hiv, Hic.
generalize Hiv; intros H.
progress unfold rngl_has_inv in H.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
destruct iq as [inv| quot]; [ | easy ].
symmetry; apply (fold_rngl_div Hiv).
Qed.

Theorem complex_inv_im {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op in
  rngl_has_inv T = true →
  rngl_mul_is_comm T = true →
  ∀ a : complex, a ≠ 0%L →
  im a⁻¹ = ((- im a)/(re a * re a + im a * im a))%L.
Proof.
intros * Hiv Hic * Haz.
progress unfold rngl_inv; cbn.
progress unfold complex_opt_inv_or_quot.
progress unfold rngl_div.
rewrite Hiv, Hic.
generalize Hiv; intros H.
progress unfold rngl_has_inv in H.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
destruct iq as [inv| quot]; [ | easy ].
symmetry; apply (fold_rngl_div Hiv).
Qed.
*)

(* to be completed
Definition complex_ring_like_prop : ring_like_prop complex :=
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := false;
     rngl_is_integral_domain := false;
     rngl_is_alg_closed := true;
     rngl_characteristic := rngl_characteristic;
     rngl_add_comm := complex_add_comm;
     rngl_add_assoc := complex_add_assoc;
     rngl_add_0_l := complex_add_0_l;
     rngl_mul_assoc := complex_mul_assoc;
     rngl_opt_mul_1_l := complex_mul_1_l;
     rngl_mul_add_distr_l := complex_mul_add_distr_l;
     rngl_opt_mul_comm := complex_mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := complex_add_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_l := complex_opt_mul_inv_l Hop;
     rngl_opt_mul_inv_r := 42;
     rngl_opt_mul_div := ?rngl_opt_mul_div;
     rngl_opt_mul_quot_r := ?rngl_opt_mul_quot_r;
     rngl_opt_eqb_eq := ?rngl_opt_eqb_eq;
     rngl_opt_le_dec := ?rngl_opt_le_dec;
     rngl_opt_integral := ?rngl_opt_integral;
     rngl_opt_alg_closed := ?rngl_opt_alg_closed;
     rngl_characteristic_prop := ?rngl_characteristic_prop;
     rngl_opt_le_refl := ?rngl_opt_le_refl;
     rngl_opt_le_antisymm := ?rngl_opt_le_antisymm;
     rngl_opt_le_trans := ?rngl_opt_le_trans;
     rngl_opt_add_le_compat := ?rngl_opt_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := ?rngl_opt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := ?rngl_opt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := ?rngl_opt_mul_le_compat;
     rngl_opt_not_le := ?rngl_opt_not_le |}.
*)
*)
