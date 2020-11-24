(* Semiring *)

Set Implicit Arguments.

Require Import Utf8.

Inductive opp_opt T :=
| Has_opp : (T → T) → opp_opt T
| Has_sub : (T → T → T) → opp_opt T
| Has_no_sub : opp_opt T.

(* ring operators
   * only semiring if rng_opp_opt = Has_sub (e.g. ℕ) or Has_no_sub
   * ring if rng_opp = Has_opp *)

Class ring_op T :=
  { rng_zero : T;
    rng_one : T;
    rng_add : T → T → T;
    rng_mul : T → T → T;
    rng_opp_opt : opp_opt T }.

Definition rng_opp T {ro : ring_op T} (a : T) :=
  match rng_opp_opt with
  | Has_opp rng_opp => rng_opp a
  | Has_sub rng_sub => rng_zero
  | Has_no_sub _ => rng_zero
  end.

Definition rng_sub T {ro : ring_op T} (a b : T) :=
  match rng_opp_opt with
  | Has_opp rng_opp => rng_add a (rng_opp b)
  | Has_sub rng_sub => rng_sub a b
  | Has_no_sub _ => rng_zero
  end.

Declare Scope ring_scope.
Delimit Scope ring_scope with Rng.

Notation "0" := rng_zero : ring_scope.
Notation "1" := rng_one : ring_scope.
Notation "- a" := (rng_opp a) : ring_scope.
Notation "a + b" := (rng_add a b) : ring_scope.
Notation "a - b" := (rng_sub a b) : ring_scope.
Notation "a * b" := (rng_mul a b) : ring_scope.

Class ring_prop T {ro : ring_op T} (is_comm : bool) :=
  { rng_add_comm : ∀ a b : T, (a + b = b + a)%Rng;
    rng_add_assoc : ∀ a b c : T, (a + (b + c) = (a + b) + c)%Rng;
    rng_add_0_l : ∀ a : T, (0 + a)%Rng = a;
    rng_mul_assoc : ∀ a b c : T, (a * (b * c) = (a * b) * c)%Rng;
    rng_mul_add_distr_l : ∀ a b c : T, (a * (b + c) = a * b + a * c)%Rng;
    rng_mul_1_l : ∀ a : T, (1 * a)%Rng = a;
    (* below: rings have opp *)
    rng_add_opp_r :
      match rng_opp_opt with
      | Has_opp rng_opp => ∀ a : T, (a + rng_opp a = 0)%Rng
      | Has_sub rng_sub => ∀ a : T, (rng_sub a a = 0)%Rng
      | Has_no_sub _ => True
      end;
    (* below: axiom of commutative rings *)
    rng_c_mul_comm : if is_comm then ∀ a b : T, (a * b = b * a)%Rng else True;
    (* below: non provable in non-commutative rings *)
    rng_nc_add_opp_r :
      match rng_opp_opt with
      | Has_opp _ => ∀ a : T, (- a + a = 0)%Rng
      | Has_sub _ | Has_no_sub _ => True
      end;
    rng_nc_mul_0_l : if is_comm then True else ∀ a, (0 * a = 0)%Rng;
    rng_nc_mul_0_r : if is_comm then True else ∀ a, (a * 0 = 0)%Rng;
    rng_nc_mul_1_r : if is_comm then True else ∀ a : T, (a * 1 = a)%Rng;
    rng_nc_mul_add_distr_r : if is_comm then True else
      ∀ a b c : T, ((a + b) * c = a * c + b * c)%Rng }.

(* decidability of equality in rings and the fact that 1 ≠ 0 *)

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

Context {T : Type}.
Context {ro : ring_op T}.
Context {is_comm : bool}.
Context {opp_status : opp_opt T}.
Context {rp : ring_prop is_comm}.

Theorem rng_add_0_r : ∀ a, (a + 0 = a)%Rng.
Proof.
intros a; simpl.
rewrite rng_add_comm.
apply rng_add_0_l.
Qed.

Theorem rng_c_mul_1_r : ∀ a, (a * 1 = a)%Rng.
Proof.
intros a; simpl.
destruct is_comm. {
  specialize rng_c_mul_comm as Hmc.
  cbn in Hmc.
  now rewrite Hmc, rng_mul_1_l.
} {
  specialize rng_nc_mul_1_r as Hm1r.
  cbn in Hm1r.
  apply Hm1r.
}
Qed.

Theorem rng_add_add_swap : ∀ n m p, (n + m + p = n + p + m)%Rng.
Proof.
intros n m p; simpl.
do 2 rewrite <- rng_add_assoc.
assert (m + p = p + m)%Rng as H by apply rng_add_comm.
rewrite H; reflexivity.
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

Theorem rng_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%Rng.
Proof.
intros x y z; simpl.
destruct is_comm. {
  specialize rng_c_mul_comm as H1.
  rewrite H1.
  rewrite rng_mul_add_distr_l.
  rewrite H1.
  now rewrite (H1 z).
} {
  specialize rng_nc_mul_add_distr_r as H1.
  apply H1.
}
Qed.

Theorem rng_sub_compat_l : ∀ a b c,
  (a = b)%Rng → (a - c = b - c)%Rng.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Definition has_opp :=
  match rng_opp_opt with
  | Has_opp _ => True
  | _ => False
  end.

Theorem rng_add_sub : ∀ a b, has_opp → (a + b - b = a)%Rng.
Proof.
intros * Ho.
unfold has_opp in Ho.
unfold rng_sub.
specialize rng_add_opp_r as Hao.
destruct rng_opp_opt as [rng_opp| | ]; [ | easy | easy ].
rewrite <- rng_add_assoc.
rewrite Hao.
apply rng_add_0_r.
Qed.

Theorem rng_add_reg_r : ∀ a b c, has_opp → (a + c = b + c)%Rng → (a = b)%Rng.
Proof.
intros a b c Ho Habc; simpl in Habc; simpl.
eapply rng_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rng_add_sub in Habc.
Qed.

Theorem rng_mul_0_l : ∀ a, (0 * a = 0)%Rng.
Proof.
intros.
specialize rng_mul_add_distr_r as Hmad.
specialize rng_add_reg_r as Har.
destruct is_comm. {
  assert (H : (0 * a + a = a)%Rng). {
    transitivity ((0 * a + 1 * a)%Rng). {
      now rewrite rng_mul_1_l.
    }
    rewrite <- Hmad.
    now rewrite rng_add_0_l, rng_mul_1_l.
  }
  apply Har with (c := a).
...

  apply rng_add_reg_r with (c := a).
now rewrite rng_add_0_l.
...
} {
  specialize rng_nc_mul_0_l as H; apply H.
}
...

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

Class ring_prop A {so : ring_op A} {ro : ring_op A} :=
  { rng_add_opp_l : ∀ a : A, (- a + a = 0)%Rng }.

Section ring_theorems.

Context {A : Type}.
Context {is_comm : bool}.
Context {ro : ring_op A}.
Context {so : ring_op A}.
Context {sp : ring_prop A is_comm}.
Context {rp : ring_prop A}.

Theorem fold_rng_sub : ∀ a b, (a + - b)%Rng = (a - b)%Rng.
Proof. intros; easy. Qed.

Theorem rng_add_reg_l : ∀ a b c, (c + a = c + b)%Rng → (a = b)%Rng.
Proof.
intros a b c Habc; simpl in Habc; simpl.
apply rng_add_reg_r with (c := c).
rewrite rng_add_comm; symmetry.
now rewrite rng_add_comm; symmetry.
Qed.

Theorem rng_mul_0_l : ∀ a, (0 * a = 0)%Rng.
Proof.
intros a.
assert (H : (0 * a + a = a)%Rng). {
  transitivity ((0 * a + 1 * a)%Rng). {
    now rewrite rng_mul_1_l.
  }
  rewrite <- rng_mul_add_distr_r.
  now rewrite rng_add_0_l, rng_mul_1_l.
}
apply rng_add_reg_r with (c := a).
now rewrite rng_add_0_l.
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
Check rng_nc_mul_0_l.
...
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

(* allows to use ring theorems on Z
Canonical Structure Z_ring_op.
Canonical Structure Z_ring_prop.
*)

(* borrowed from Ring2.v because, now, I want to start with
   rings, and define rings later from rings; this way,
   summations with syntax Σ can be defined (later) on rings,
   more general than rings, and testable on type nat *)
(*
Class ring_prop {A} {ro : ring_op A} :=
  { rng_1_neq_0 : (1 ≠ 0)%Rng;
    rng_eq_dec : ∀ a b : A, {a = b} + {a ≠ b};
    rng_add_comm : ∀ a b : A, (a + b = b + a)%Rng;
    rng_add_assoc : ∀ a b c : A, (a + (b + c) = (a + b) + c)%Rng;
    rng_add_0_l : ∀ a : A, (0 + a)%Rng = a;
    rng_add_opp_l : ∀ a : A, (- a + a = 0)%Rng;
    rng_mul_comm : ∀ a b : A, (a * b = b * a)%Rng;
    rng_mul_assoc : ∀ a b c : A, (a * (b * c) = (a * b) * c)%Rng;
    rng_mul_1_l : ∀ a : A, (1 * a)%Rng = a;
    rng_mul_add_distr_l : ∀ a b c : A, (a * (b + c) = a * b + a * c)%Rng }.

Arguments rng_eq_dec {_} {_} {_} _%Rng _%Rng.
*)

(*
Context {rp : ring_prop}.
*)

(*
Theorem rng_add_compat_l : ∀ a b c,
  (a = b)%Rng → (c + a = c + b)%Rng.
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Theorem rng_add_compat_r : ∀ a b c,
  (a = b)%Rng → (a + c = b + c)%Rng.
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Theorem rng_add_compat : ∀ a b c d,
  (a = b)%Rng
  → (c = d)%Rng
    → (a + c = b + d)%Rng.
Proof.
intros a b c d Hab Hcd.
rewrite Hab, Hcd; reflexivity.
Qed.

Theorem rng_sub_compat_r : ∀ a b c,
  (b = c)%Rng → (a - b = a - c)%Rng.
Proof.
intros a b c Hbc.
now rewrite Hbc.
Qed.

Theorem rng_mul_compat_r : ∀ a b c,
  (a = b)%Rng
  → (a * c = b * c)%Rng.
Proof.
intros a b c Hab; simpl in Hab |- *.
rewrite Hab; reflexivity.
Qed.

Theorem rng_mul_compat : ∀ a b c d,
  (a = b)%Rng
  → (c = d)%Rng
    → (a * c = b * d)%Rng.
Proof.
intros a b c d Hab Hcd.
rewrite Hab, Hcd; reflexivity.
Qed.

Theorem rng_add_0_r : ∀ a, (a + 0 = a)%Rng.
Proof.
intros a; simpl.
rewrite rng_add_comm.
apply rng_add_0_l.
Qed.

Theorem fold_rng_sub : ∀ a b, (a + - b)%Rng = (a - b)%Rng.
Proof. intros; easy. Qed.T

Theorem rng_add_sub : ∀ a b, (a + b - b = a)%Rng.
Proof.
intros.
unfold rng_sub.
rewrite <- rng_add_assoc.
rewrite fold_rng_sub.
rewrite rng_add_opp_r.
apply rng_add_0_r.
Qed.

heorem rng_sub_add : ∀ a b, (a - b + b = a)%Rng.
Proof.
intros.
unfold rng_sub.
rewrite <- rng_add_assoc.
rewrite rng_add_opp_l.
apply rng_add_0_r.
Qed.

Theorem rng_add_reg_r : ∀ a b c, (a + c = b + c)%Rng → (a = b)%Rng.
Proof.
intros a b c Habc; simpl in Habc; simpl.
eapply rng_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rng_add_sub in Habc.
Qed.

Theorem rng_opp_add_distr : ∀ a b,
  (- (a + b) = - a - b)%Rng.
Proof.
intros.
apply (rng_add_reg_l _ _ (b + a)%Rng).
unfold rng_sub.
rewrite rng_add_assoc.
do 3 rewrite fold_rng_sub.
rewrite rng_add_sub.
rewrite rng_add_comm.
now do 2 rewrite rng_add_opp_r.
Qed.

Theorem rng_sub_add_distr : ∀ a b c, (a - (b + c) = a - b - c)%Rng.
Proof.
intros.
unfold rng_sub.
rewrite rng_opp_add_distr.
apply rng_add_assoc.
Qed.

Theorem rng_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%Rng.
Proof.
intros x y z; simpl.
rewrite rng_mul_comm.
rewrite rng_mul_add_distr_l.
rewrite rng_mul_comm.
assert (rng_mul z y = rng_mul y z) as H.
 apply rng_mul_comm.

 rewrite H; reflexivity.
Qed.

Theorem rng_mul_0_r : ∀ a, (a * 0 = 0)%Rng.
Proof.
intros a; simpl.
rewrite rng_mul_comm, rng_mul_0_l.
reflexivity.
Qed.

Theorem rng_mul_opp_l : ∀ a b, ((- a) * b = - (a * b))%Rng.
Proof.
intros a b; simpl.
apply rng_add_reg_l with (c := (a * b)%Rng).
rewrite fold_rng_sub.
rewrite rng_add_opp_r.
rewrite <- rng_mul_add_distr_r.
rewrite fold_rng_sub.
rewrite rng_add_opp_r, rng_mul_0_l.
reflexivity.
Qed.

Theorem rng_mul_opp_r : ∀ a b, (a * (- b) = - (a * b))%Rng.
Proof.
intros a b; simpl.
rewrite rng_mul_comm; symmetry.
rewrite rng_mul_comm; symmetry.
apply rng_mul_opp_l.
Qed.

Theorem rng_mul_sub_distr_l : ∀ x y z,
  (x * (y - z) = x * y - x * z)%Rng.
Proof.
intros.
unfold rng_sub.
rewrite rng_mul_add_distr_l.
now rewrite <- rng_mul_opp_r.
Qed.

Theorem rng_mul_sub_distr_r : ∀ x y z,
  ((x - y) * z = x * z - y * z)%Rng.
Proof.
intros.
rewrite rng_mul_comm.
rewrite rng_mul_sub_distr_l.
rewrite (rng_mul_comm _ x).
rewrite (rng_mul_comm _ y).
easy.
Qed.

Theorem rng_opp_0 : (- 0 = 0)%Rng.
Proof.
simpl; etransitivity; [ symmetry; apply rng_add_0_l | idtac ].
apply rng_add_opp_r.
Qed.

Theorem rng_sub_0_r : ∀ a, (a - 0 = a)%Rng.
Proof.
intros.
unfold rng_sub.
rewrite rng_opp_0.
apply rng_add_0_r.
Qed.

Theorem rng_mul_mul_swap : ∀ n m p, (n * m * p = n * p * m)%Rng.
Proof.
intros n m p.
do 2 rewrite <- rng_mul_assoc.
assert (m * p = p * m)%Rng as H by apply rng_mul_comm.
rewrite H; reflexivity.
Qed.

Theorem rng_mul_eq_0 : ∀ n m,
  (n = 0)%Rng ∨ (m = 0)%Rng
  → (n * m = 0)%Rng.
Proof.
intros n m H; simpl in H; simpl.
destruct H as [H| H]; rewrite H; [ apply rng_mul_0_l | apply rng_mul_0_r ].
Qed.

Theorem rng_pow_1_r : ∀ a, (a ^ 1 = a)%Rng.
Proof. now intros; cbn; rewrite rng_mul_1_r. Qed.
*)
