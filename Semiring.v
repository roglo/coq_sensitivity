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
  { srng_add_comm : ∀ a b : A, (a + b = b + a)%Srng;
    srng_add_assoc : ∀ a b c : A, (a + (b + c) = (a + b) + c)%Srng;
    srng_add_0_l : ∀ a : A, (0 + a)%Srng = a;
    srng_mul_comm : ∀ a b : A, (a * b = b * a)%Srng;
    srng_mul_1_l : ∀ a : A, (1 * a)%Srng = a;
    srng_mul_add_distr_l : ∀ a b c : A, (a * (b + c) = a * b + a * c)%Srng;
    srng_mul_0_l : ∀ a, (0 * a = 0)%Srng }.

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

Theorem srng_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%Srng.
Proof.
intros x y z; simpl.
rewrite srng_mul_comm.
rewrite srng_mul_add_distr_l.
rewrite srng_mul_comm.
assert (H : srng_mul z y = srng_mul y z). {
 apply srng_mul_comm.
}
now rewrite H.
Qed.

End semiring_theorems.

(* Rings *)

Class ring_op A :=
  { rng_semiring : semiring_op A;
    rng_opp : A → A }.

Definition rng_sub A {R : ring_op A} (S := rng_semiring) a b :=
  srng_add a (rng_opp b).

Declare Scope ring_scope.

Delimit Scope ring_scope with Rng.
Notation "0" := (@srng_zero _ rng_semiring) : ring_scope.
Notation "1" := (@srng_one _ rng_semiring) : ring_scope.
Notation "- a" := (@rng_opp _ _ a) : ring_scope.
Notation "a + b" := (@srng_add _ rng_semiring a b) : ring_scope.
Notation "a - b" := (@rng_sub _ _ a b) : ring_scope.
Notation "a * b" := (@srng_mul _ rng_semiring a b) : ring_scope.

Class ring_prop A {so : ring_op A} :=
  { rng_add_opp_l : ∀ a : A, (- a + a = 0)%Rng }.

Section ring_theorems.

Context {A : Type}.
Context {ro : ring_op A}.
Context (so := @rng_semiring A ro).
Context {sp : @semiring_prop A so}.
Context {rp : @ring_prop A ro}.

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

Theorem rng_mul_0_l : ∀ a, (0 * a = 0)%Rng.
Proof.
intros a.
assert (H : (0 * a + a = a)%Rng). {
 transitivity ((0 * a + 1 * a)%Rng). {
   now rewrite srng_mul_1_l.
 }
 rewrite <- srng_mul_add_distr_r.
 now rewrite srng_add_0_l, srng_mul_1_l.
}
apply rng_add_reg_r with (c := a).
now rewrite srng_add_0_l.
Qed.

Theorem rng_opp_0 : (- 0 = 0)%Rng.
Proof.
transitivity (0 + - 0)%Rng. {
  symmetry.
  apply srng_add_0_l.
}
apply rng_add_opp_r.
Qed.

End ring_theorems.

(* Ring of integers *)

Require Import ZArith.

Definition Z_semiring_op : semiring_op Z :=
  {| srng_zero := 0%Z;
     srng_one := 1%Z;
     srng_add := Z.add;
     srng_mul := Z.mul |}.

Definition Z_ring_op : ring_op Z :=
  {| rng_semiring := Z_semiring_op;
     rng_opp := Z.opp |}.

(* borrowed from Ring2.v because, now, I want to start with
   semirings, and define rings later from semirings; this way,
   summations with syntax Σ can be defined (later) on semirings,
   more general than rings, and testable on type nat *)
(*
Class semiring_prop {A} {ro : ring_op A} :=
  { srng_1_neq_0 : (1 ≠ 0)%Rng;
    srng_eq_dec : ∀ a b : A, {a = b} + {a ≠ b};
    srng_add_comm : ∀ a b : A, (a + b = b + a)%Rng;
    srng_add_assoc : ∀ a b c : A, (a + (b + c) = (a + b) + c)%Rng;
    srng_add_0_l : ∀ a : A, (0 + a)%Rng = a;
    srng_add_opp_l : ∀ a : A, (- a + a = 0)%Rng;
    srng_mul_comm : ∀ a b : A, (a * b = b * a)%Rng;
    srng_mul_assoc : ∀ a b c : A, (a * (b * c) = (a * b) * c)%Rng;
    srng_mul_1_l : ∀ a : A, (1 * a)%Rng = a;
    srng_mul_add_distr_l : ∀ a b c : A, (a * (b + c) = a * b + a * c)%Rng }.

Arguments srng_eq_dec {_} {_} {_} _%Rng _%Rng.
*)

(*
Context {rp : ring_prop}.
*)

(*
Theorem srng_mul_1_r : ∀ a, (a * 1 = a)%Srng.
Proof.
intros a; simpl.
rewrite srng_mul_comm, srng_mul_1_l.
reflexivity.
Qed.

Theorem srng_add_compat_l : ∀ a b c,
  (a = b)%Srng → (c + a = c + b)%Srng.
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Theorem srng_add_compat_r : ∀ a b c,
  (a = b)%Srng → (a + c = b + c)%Srng.
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Theorem srng_add_compat : ∀ a b c d,
  (a = b)%Srng
  → (c = d)%Srng
    → (a + c = b + d)%Srng.
Proof.
intros a b c d Hab Hcd.
rewrite Hab, Hcd; reflexivity.
Qed.

Theorem srng_sub_compat_l : ∀ a b c,
  (a = b)%Srng → (a - c = b - c)%Srng.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem srng_sub_compat_r : ∀ a b c,
  (b = c)%Srng → (a - b = a - c)%Srng.
Proof.
intros a b c Hbc.
now rewrite Hbc.
Qed.

Theorem srng_mul_compat_r : ∀ a b c,
  (a = b)%Srng
  → (a * c = b * c)%Srng.
Proof.
intros a b c Hab; simpl in Hab |- *.
rewrite Hab; reflexivity.
Qed.

Theorem srng_mul_compat : ∀ a b c d,
  (a = b)%Srng
  → (c = d)%Srng
    → (a * c = b * d)%Srng.
Proof.
intros a b c d Hab Hcd.
rewrite Hab, Hcd; reflexivity.
Qed.

Theorem srng_add_0_r : ∀ a, (a + 0 = a)%Srng.
Proof.
intros a; simpl.
rewrite srng_add_comm.
apply srng_add_0_l.
Qed.

Theorem fold_srng_sub : ∀ a b, (a + - b)%Srng = (a - b)%Srng.
Proof. intros; easy. Qed.T

Theorem srng_add_sub : ∀ a b, (a + b - b = a)%Srng.
Proof.
intros.
unfold srng_sub.
rewrite <- srng_add_assoc.
rewrite fold_srng_sub.
rewrite srng_add_opp_r.
apply srng_add_0_r.
Qed.

heorem srng_sub_add : ∀ a b, (a - b + b = a)%Srng.
Proof.
intros.
unfold srng_sub.
rewrite <- srng_add_assoc.
rewrite srng_add_opp_l.
apply srng_add_0_r.
Qed.

Theorem srng_add_reg_r : ∀ a b c, (a + c = b + c)%Srng → (a = b)%Srng.
Proof.
intros a b c Habc; simpl in Habc; simpl.
eapply srng_sub_compat_l with (c := c) in Habc.
now do 2 rewrite srng_add_sub in Habc.
Qed.

Theorem srng_add_reg_l : ∀ a b c, (c + a = c + b)%Srng → (a = b)%Srng.
Proof.
intros a b c Habc; simpl in Habc; simpl.
apply srng_add_reg_r with (c := c).
rewrite srng_add_comm; symmetry.
rewrite srng_add_comm; symmetry.
assumption.
Qed.

Theorem srng_opp_add_distr : ∀ a b,
  (- (a + b) = - a - b)%Srng.
Proof.
intros.
apply (srng_add_reg_l _ _ (b + a)%Srng).
unfold srng_sub.
rewrite srng_add_assoc.
do 3 rewrite fold_srng_sub.
rewrite srng_add_sub.
rewrite srng_add_comm.
now do 2 rewrite srng_add_opp_r.
Qed.

Theorem srng_sub_add_distr : ∀ a b c, (a - (b + c) = a - b - c)%Srng.
Proof.
intros.
unfold srng_sub.
rewrite srng_opp_add_distr.
apply srng_add_assoc.
Qed.

Theorem srng_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%Srng.
Proof.
intros x y z; simpl.
rewrite srng_mul_comm.
rewrite srng_mul_add_distr_l.
rewrite srng_mul_comm.
assert (srng_mul z y = srng_mul y z) as H.
 apply srng_mul_comm.

 rewrite H; reflexivity.
Qed.

Theorem srng_mul_0_r : ∀ a, (a * 0 = 0)%Srng.
Proof.
intros a; simpl.
rewrite srng_mul_comm, srng_mul_0_l.
reflexivity.
Qed.

Theorem srng_mul_opp_l : ∀ a b, ((- a) * b = - (a * b))%Srng.
Proof.
intros a b; simpl.
apply srng_add_reg_l with (c := (a * b)%Srng).
rewrite fold_srng_sub.
rewrite srng_add_opp_r.
rewrite <- srng_mul_add_distr_r.
rewrite fold_srng_sub.
rewrite srng_add_opp_r, srng_mul_0_l.
reflexivity.
Qed.

Theorem srng_mul_opp_r : ∀ a b, (a * (- b) = - (a * b))%Srng.
Proof.
intros a b; simpl.
rewrite srng_mul_comm; symmetry.
rewrite srng_mul_comm; symmetry.
apply srng_mul_opp_l.
Qed.

Theorem srng_mul_sub_distr_l : ∀ x y z,
  (x * (y - z) = x * y - x * z)%Srng.
Proof.
intros.
unfold srng_sub.
rewrite srng_mul_add_distr_l.
now rewrite <- srng_mul_opp_r.
Qed.

Theorem srng_mul_sub_distr_r : ∀ x y z,
  ((x - y) * z = x * z - y * z)%Srng.
Proof.
intros.
rewrite srng_mul_comm.
rewrite srng_mul_sub_distr_l.
rewrite (srng_mul_comm _ x).
rewrite (srng_mul_comm _ y).
easy.
Qed.

Theorem srng_opp_0 : (- 0 = 0)%Srng.
Proof.
simpl; etransitivity; [ symmetry; apply srng_add_0_l | idtac ].
apply srng_add_opp_r.
Qed.

Theorem srng_sub_0_r : ∀ a, (a - 0 = a)%Srng.
Proof.
intros.
unfold srng_sub.
rewrite srng_opp_0.
apply srng_add_0_r.
Qed.

Theorem srng_add_move_0_r : ∀ a b, (a + b = 0)%Srng ↔ (a = - b)%Srng.
Proof.
intros a b.
split; intros H.
 apply srng_sub_compat_l with (c := b) in H.
 rewrite srng_add_sub in H.
 unfold srng_sub in H.
 now rewrite srng_add_0_l in H.

 rewrite H.
 rewrite srng_add_opp_l; reflexivity.
Qed.

Theorem srng_opp_inj_wd : ∀ a b, (- a = - b)%Srng ↔ (a = b)%Srng.
Proof.
intros a b; split; intros H.
 apply srng_add_move_0_r in H.
 rewrite srng_add_comm in H.
 apply srng_add_move_0_r in H.
 rewrite H.
 apply srng_add_move_0_r.
 apply srng_add_opp_r.

 rewrite H; reflexivity.
Qed.

Theorem srng_opp_involutive : ∀ x, (- - x)%Srng = x.
Proof.
intros.
symmetry.
apply srng_add_move_0_r.
apply srng_add_opp_r.
Qed.

Theorem srng_add_add_swap : ∀ n m p, (n + m + p = n + p + m)%Srng.
Proof.
intros n m p; simpl.
do 2 rewrite <- srng_add_assoc.
assert (m + p = p + m)%Srng as H by apply srng_add_comm.
rewrite H; reflexivity.
Qed.

Theorem srng_mul_mul_swap : ∀ n m p, (n * m * p = n * p * m)%Srng.
Proof.
intros n m p.
do 2 rewrite <- srng_mul_assoc.
assert (m * p = p * m)%Srng as H by apply srng_mul_comm.
rewrite H; reflexivity.
Qed.

Theorem srng_mul_eq_0 : ∀ n m,
  (n = 0)%Srng ∨ (m = 0)%Srng
  → (n * m = 0)%Srng.
Proof.
intros n m H; simpl in H; simpl.
destruct H as [H| H]; rewrite H; [ apply srng_mul_0_l | apply srng_mul_0_r ].
Qed.

Theorem srng_pow_1_r : ∀ a, (a ^ 1 = a)%Srng.
Proof. now intros; cbn; rewrite srng_mul_1_r. Qed.
*)
