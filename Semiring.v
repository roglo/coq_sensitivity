(* Semiring *)

Require Import Utf8.

Class semiring_op A :=
  { srng_zero : A;
    srng_one : A;
    srng_add : A → A → A;
    srng_mul : A → A → A }.

Declare Scope semiring_scope.
Delimit Scope semiring_scope with Srng.
Notation "a + b" := (srng_add a b) : semiring_scope.
Notation "a * b" := (srng_mul a b) : semiring_scope.
Notation "0" := srng_zero : semiring_scope.
Notation "1" := srng_one : semiring_scope.

Class semiring_prop A {so : semiring_op A} :=
  { srng_is_comm : bool;
    srng_add_comm : ∀ a b : A, (a + b = b + a)%Srng;
    srng_add_assoc : ∀ a b c : A, (a + (b + c) = (a + b) + c)%Srng;
    srng_add_0_l : ∀ a : A, (0 + a)%Srng = a;
    srng_mul_assoc : ∀ a b c : A, (a * (b * c) = (a * b) * c)%Srng;
    srng_mul_1_l : ∀ a : A, (1 * a)%Srng = a;
    srng_mul_add_distr_l : ∀ a b c : A, (a * (b + c) = a * b + a * c)%Srng;
    srng_mul_0_l : ∀ a, (0 * a = 0)%Srng;
    (* when commutative *)
    srng_c_mul_comm :
      if srng_is_comm then ∀ a b, (a * b = b * a)%Srng else True;
    (* when not commutative *)
    srng_nc_mul_1_r :
      if srng_is_comm then True else ∀ a, (a * 1 = a)%Srng;
    srng_nc_mul_0_r :
      if srng_is_comm then True else ∀ a, (a * 0 = 0)%Srng;
    srng_nc_mul_add_distr_r :
      if srng_is_comm then True else
       ∀ a b c, ((a + b) * c = a * c + b * c)%Srng }.

(* decidability of equality in semirings
   and the fact that 1 ≠ 0 *)

Class sring_dec_prop T {so : semiring_op T} :=
  { srng_eq_dec : ∀ a b : T, {a = b} + {a ≠ b};
    srng_1_neq_0 : (1 ≠ 0)%Srng }.

Arguments srng_eq_dec {T}%type {so sring_dec_prop} _%Srng _%Srng.

Fixpoint srng_power {A} {R : semiring_op A} a n :=
  match n with
  | O => 1%Srng
  | S m => (a * srng_power a m)%Srng
  end.

Notation "a ^ b" := (srng_power a b) : semiring_scope.

Section semiring_theorems.

Context {A : Type}.
Context {so : semiring_op A}.
Context {sp : semiring_prop A}.

Theorem srng_add_0_r : ∀ a, (a + 0 = a)%Srng.
Proof.
intros a; simpl.
rewrite srng_add_comm.
apply srng_add_0_l.
Qed.

Theorem srng_add_add_swap : ∀ n m p, (n + m + p = n + p + m)%Srng.
Proof.
intros n m p; simpl.
do 2 rewrite <- srng_add_assoc.
assert (m + p = p + m)%Srng as H by apply srng_add_comm.
rewrite H; reflexivity.
Qed.

Theorem srng_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%Srng.
Proof.
intros x y z; simpl.
specialize srng_c_mul_comm as srng_mul_comm.
specialize srng_nc_mul_add_distr_r as srng_mul_add_distr_r.
destruct srng_is_comm. {
  rewrite srng_mul_comm.
  rewrite srng_mul_add_distr_l.
  rewrite srng_mul_comm.
  now rewrite (srng_mul_comm z).
} {
  apply srng_mul_add_distr_r.
}
Qed.

Theorem srng_add_compat_l : ∀ a b c,
  (a = b)%Srng → (c + a = c + b)%Srng.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem srng_add_compat_r : ∀ a b c,
  (a = b)%Srng → (a + c = b + c)%Srng.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem srng_mul_1_r : ∀ a, (a * 1 = a)%Srng.
Proof.
intros.
specialize srng_c_mul_comm as srng_mul_comm.
specialize srng_nc_mul_1_r as srng_mul_1_r.
destruct srng_is_comm. {
  now rewrite srng_mul_comm, srng_mul_1_l.
} {
  apply srng_mul_1_r.
}
Qed.

Theorem srng_mul_0_r : ∀ a, (a * 0 = 0)%Srng.
Proof.
intros.
specialize srng_c_mul_comm as srng_mul_comm.
specialize srng_nc_mul_0_r as srng_mul_0_r.
destruct srng_is_comm. {
  rewrite srng_mul_comm.
  apply srng_mul_0_l.
} {
  apply srng_mul_0_r.
}
Qed.

End semiring_theorems.

(* Rings *)

Class ring_op A :=
  { rng_opp : A → A }.

Definition rng_sub A {R : ring_op A} {S : semiring_op A} a b :=
  srng_add a (rng_opp b).

Declare Scope ring_scope.
Delimit Scope ring_scope with Rng.

Notation "0" := (@srng_zero _ _) : ring_scope.
Notation "1" := (@srng_one _ _) : ring_scope.
Notation "- a" := (@rng_opp _ _ a) : ring_scope.
Notation "a + b" := (@srng_add _ _ a b) : ring_scope.
Notation "a - b" := (@rng_sub _ _ _ a b) : ring_scope.
Notation "a * b" := (@srng_mul _ _ a b) : ring_scope.

Class ring_prop A {so : semiring_op A} {ro : ring_op A} :=
  { rng_add_opp_l : ∀ a : A, (- a + a = 0)%Rng }.

Section ring_theorems.

Context {A : Type}.
Context {ro : ring_op A}.
Context {so : semiring_op A}.
Context {sp : semiring_prop A}.
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
intros x; unfold rng_sub; rewrite srng_add_comm.
apply rng_add_opp_l.
Qed.

Theorem rng_add_sub : ∀ a b, (a + b - b = a)%Rng.
Proof.
intros.
unfold rng_sub.
rewrite <- srng_add_assoc.
rewrite fold_rng_sub.
rewrite rng_add_opp_r.
apply srng_add_0_r.
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
rewrite srng_add_comm; symmetry.
now rewrite srng_add_comm; symmetry.
Qed.

Theorem rng_opp_0 : (- 0 = 0)%Rng.
Proof.
transitivity (0 + - 0)%Rng. {
  symmetry.
  apply srng_add_0_l.
}
apply rng_add_opp_r.
Qed.

Theorem rng_sub_0_r : ∀ a, (a - 0 = a)%Rng.
Proof.
intros.
unfold rng_sub.
rewrite rng_opp_0.
apply srng_add_0_r.
Qed.

Theorem rng_add_move_0_r : ∀ a b, (a + b = 0)%Rng ↔ (a = - b)%Rng.
Proof.
intros a b.
split; intros H. {
  apply rng_sub_compat_l with (c := b) in H.
  rewrite rng_add_sub in H.
  unfold rng_sub in H.
  now rewrite srng_add_0_l in H.
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
specialize (srng_mul_add_distr_r (- a)%Rng a b) as H.
rewrite rng_add_opp_l in H.
rewrite srng_mul_0_l in H.
symmetry in H.
now apply rng_add_move_0_r in H.
Qed.

Theorem rng_mul_opp_r : ∀ a b, (a * - b = - (a * b))%Rng.
Proof.
intros.
specialize (srng_mul_add_distr_l a b (- b)%Rng) as H.
rewrite fold_rng_sub in H.
rewrite rng_add_opp_r in H.
rewrite srng_mul_0_r in H.
symmetry in H.
rewrite srng_add_comm in H.
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
