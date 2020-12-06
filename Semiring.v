(* Semiring *)

Require Import Utf8.

Class ring_op A :=
  { rng_zero : A;
    rng_one : A;
    rng_add : A → A → A;
    rng_mul : A → A → A;
    rng_opp : A → A }.

Declare Scope ring_scope.
Delimit Scope ring_scope with Rng.

Definition rng_sub A {R : ring_op A} a b :=
  rng_add a (rng_opp b).

Notation "0" := rng_zero : ring_scope.
Notation "1" := rng_one : ring_scope.
Notation "a + b" := (rng_add a b) : ring_scope.
Notation "a - b" := (rng_sub a b) : ring_scope.
Notation "a * b" := (rng_mul a b) : ring_scope.
Notation "- a" := (rng_opp a) : ring_scope.

Class ring_prop A {ro : ring_op A} :=
  { rng_is_comm : bool;
     rng_is_semiring : bool;
    rng_add_comm : ∀ a b : A, (a + b = b + a)%Rng;
    rng_add_assoc : ∀ a b c : A, (a + (b + c) = (a + b) + c)%Rng;
    rng_add_0_l : ∀ a : A, (0 + a)%Rng = a;
    rng_mul_assoc : ∀ a b c : A, (a * (b * c) = (a * b) * c)%Rng;
    rng_mul_1_l : ∀ a : A, (1 * a)%Rng = a;
    rng_mul_add_distr_l : ∀ a b c : A, (a * (b + c) = a * b + a * c)%Rng;
    rng_mul_0_l : ∀ a, (0 * a = 0)%Rng;
    (* when commutative *)
    rng_c_mul_comm :
      if rng_is_comm then ∀ a b, (a * b = b * a)%Rng else True;
    (* when not commutative *)
    rng_nc_mul_1_r :
      if rng_is_comm then True else ∀ a, (a * 1 = a)%Rng;
    rng_nc_mul_0_r :
      if rng_is_comm then True else ∀ a, (a * 0 = 0)%Rng;
    rng_nc_mul_add_distr_r :
      if rng_is_comm then True else
       ∀ a b c, ((a + b) * c = a * c + b * c)%Rng;
    (* when only semiring *)
    rng_s_add_opp_l :
      if rng_is_semiring then True else ∀ a : A, (- a + a = 0)%Rng }.

(* decidability of equality in rings
   and the fact that 1 ≠ 0 *)

Class ring_dec_prop T {ro : ring_op T} :=
  { rng_eq_dec : ∀ a b : T, {a = b} + {a ≠ b};
    rng_1_neq_0 : (1 ≠ 0)%Rng }.

Arguments rng_eq_dec {T}%type {ro ring_dec_prop} _%Rng _%Rng.

Fixpoint rng_power {A} {R : ring_op A} a n :=
  match n with
  | O => 1%Rng
  | S m => (a * rng_power a m)%Rng
  end.

Notation "a ^ b" := (rng_power a b) : ring_scope.

Section ring_theorems.

Context {A : Type}.
Context {ro : ring_op A}.

Theorem rng_add_0_r : ∀ a, (a + 0 = a)%Rng.
Proof.
intros a; simpl.
rewrite rng_add_comm.
apply rng_add_0_l.
Qed.

Theorem rng_add_add_swap : ∀ n m p, (n + m + p = n + p + m)%Rng.
Proof.
intros n m p; simpl.
do 2 rewrite <- rng_add_assoc.
assert (m + p = p + m)%Rng as H by apply rng_add_comm.
rewrite H; reflexivity.
Qed.

Theorem rng_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%Rng.
Proof.
intros x y z; simpl.
specialize rng_c_mul_comm as rng_mul_comm.
specialize rng_nc_mul_add_distr_r as rng_mul_add_distr_r.
destruct rng_is_comm. {
  rewrite rng_mul_comm.
  rewrite rng_mul_add_distr_l.
  rewrite rng_mul_comm.
  now rewrite (rng_mul_comm z).
} {
  apply rng_mul_add_distr_r.
}
Qed.

Theorem rng_add_compat_l : ∀ a b c,
  (a = b)%Rng → (c + a = c + b)%Rng.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rng_add_compat_r : ∀ a b c,
  (a = b)%Rng → (a + c = b + c)%Rng.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rng_mul_1_r : ∀ a, (a * 1 = a)%Rng.
Proof.
intros.
specialize rng_c_mul_comm as rng_mul_comm.
specialize rng_nc_mul_1_r as rng_mul_1_r.
destruct rng_is_comm. {
  now rewrite rng_mul_comm, rng_mul_1_l.
} {
  apply rng_mul_1_r.
}
Qed.

Theorem rng_mul_0_r : ∀ a, (a * 0 = 0)%Rng.
Proof.
intros.
specialize rng_c_mul_comm as rng_mul_comm.
specialize rng_nc_mul_0_r as rng_mul_0_r.
destruct rng_is_comm. {
  rewrite rng_mul_comm.
  apply rng_mul_0_l.
} {
  apply rng_mul_0_r.
}
Qed.

End ring_theorems.

(* Rings *)

Class ring_op A :=
  { rng_opp : A → A }.

Definition rng_sub A {R : ring_op A} {S : ring_op A} a b :=
  rng_add a (rng_opp b).

Declare Scope ring_scope.
Delimit Scope ring_scope with Rng.

Notation "0" := (@rng_zero _ _) : ring_scope.
Notation "1" := (@rng_one _ _) : ring_scope.
Notation "- a" := (@rng_opp _ _ a) : ring_scope.
Notation "a + b" := (@rng_add _ _ a b) : ring_scope.
Notation "a - b" := (@rng_sub _ _ _ a b) : ring_scope.
Notation "a * b" := (@rng_mul _ _ a b) : ring_scope.

Class ring_prop A {ro : ring_op A} {ro : ring_op A} :=
  { rng_add_opp_l : ∀ a : A, (- a + a = 0)%Rng }.

Section ring_theorems.

Context {A : Type}.
Context {ro : ring_op A}.
Context {rp : ring_prop A}.

Theorem rng_sub_compat_l : ∀ a b c,
  (a = b)%Rng → (a - c = b - c)%Rng.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem fold_rng_sub : ∀ a b, (a + - b)%Rng = (a - b)%Rng.
Proof. intros; easy. Qed.

Theorem rng_add_opp_r : ∀ x, (x - x = 0)%Rng.
Proof.
intros x; unfold rng_sub; rewrite rng_add_comm.
apply rng_add_opp_l.
Qed.

Theorem rng_add_sub : ∀ a b, (a + b - b = a)%Rng.
Proof.
intros.
unfold rng_sub.
rewrite <- rng_add_assoc.
rewrite fold_rng_sub.
rewrite rng_add_opp_r.
apply rng_add_0_r.
Qed.

Theorem rng_add_reg_r : ∀ a b c, (a + c = b + c)%Rng → (a = b)%Rng.
Proof.
intros a b c Habc; simpl in Habc; simpl.
eapply rng_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rng_add_sub in Habc.
Qed.

Theorem rng_add_reg_l : ∀ a b c, (c + a = c + b)%Rng → (a = b)%Rng.
Proof.
intros a b c Habc; simpl in Habc; simpl.
apply rng_add_reg_r with (c := c).
rewrite rng_add_comm; symmetry.
now rewrite rng_add_comm; symmetry.
Qed.

Theorem rng_opp_0 : (- 0 = 0)%Rng.
Proof.
transitivity (0 + - 0)%Rng. {
  symmetry.
  apply rng_add_0_l.
}
apply rng_add_opp_r.
Qed.

Theorem rng_sub_0_r : ∀ a, (a - 0 = a)%Rng.
Proof.
intros.
unfold rng_sub.
rewrite rng_opp_0.
apply rng_add_0_r.
Qed.

Theorem rng_add_move_0_r : ∀ a b, (a + b = 0)%Rng ↔ (a = - b)%Rng.
Proof.
intros a b.
split; intros H. {
  apply rng_sub_compat_l with (c := b) in H.
  rewrite rng_add_sub in H.
  unfold rng_sub in H.
  now rewrite rng_add_0_l in H.
} {
  rewrite H.
  now rewrite rng_add_opp_l.
}
Qed.

Theorem rng_opp_involutive : ∀ x, (- - x)%Rng = x.
Proof.
intros.
symmetry.
apply rng_add_move_0_r.
apply rng_add_opp_r.
Qed.

Theorem rng_mul_opp_l : ∀ a b, (- a * b = - (a * b))%Rng.
Proof.
intros.
specialize (rng_mul_add_distr_r (- a)%Rng a b) as H.
rewrite rng_add_opp_l in H.
rewrite rng_mul_0_l in H.
symmetry in H.
now apply rng_add_move_0_r in H.
Qed.

Theorem rng_mul_opp_r : ∀ a b, (a * - b = - (a * b))%Rng.
Proof.
intros.
specialize (rng_mul_add_distr_l a b (- b)%Rng) as H.
rewrite fold_rng_sub in H.
rewrite rng_add_opp_r in H.
rewrite rng_mul_0_r in H.
symmetry in H.
rewrite rng_add_comm in H.
now apply rng_add_move_0_r in H.
Qed.

Theorem rng_mul_opp_opp : ∀ a b, (- a * - b = a * b)%Rng.
Proof.
intros.
rewrite rng_mul_opp_l.
rewrite rng_mul_opp_r.
apply rng_opp_involutive.
Qed.

Theorem rng_opp_inj : ∀ a b, (- a = - b)%Rng → a = b.
Proof.
intros.
rewrite <- (rng_opp_involutive a).
rewrite H.
apply rng_opp_involutive.
Qed.

End ring_theorems.
