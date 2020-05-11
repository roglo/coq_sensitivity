(* Ring2.v *)

Require Import Utf8.

Class ring A :=
  { rng_zero : A;
    rng_one : A;
    rng_add : A → A → A;
    rng_mul : A → A → A;
    rng_opp : A → A;
    rng_1_neq_0 : rng_one ≠ rng_zero;
    rng_eq_dec : ∀ a b : A, {a = b} + {a ≠ b};
    rng_add_comm : ∀ a b, rng_add a b = rng_add b a;
    rng_add_assoc : ∀ a b c,
      rng_add a (rng_add b c) = rng_add (rng_add a b) c;
    rng_add_0_l : ∀ a, rng_add rng_zero a = a;
    rng_add_opp_l : ∀ a, rng_add (rng_opp a) a = rng_zero;
    rng_mul_comm : ∀ a b, rng_mul a b = rng_mul b a;
    rng_mul_assoc : ∀ a b c,
      rng_mul a (rng_mul b c) = rng_mul (rng_mul a b) c;
    rng_mul_1_l : ∀ a, rng_mul rng_one a = a;
    rng_mul_add_distr_l : ∀ a b c,
      rng_mul a (rng_add b c) = rng_add (rng_mul a b) (rng_mul a c) }.

Definition rng_sub {A} {R : ring A} a b := rng_add a (rng_opp b).

Declare Scope ring_scope.
Delimit Scope ring_scope with Rng.
Bind Scope ring_scope with ring.
Notation "a + b" := (rng_add a b) : ring_scope.
Notation "a - b" := (rng_sub a b) : ring_scope.
Notation "a * b" := (rng_mul a b) : ring_scope.
Notation "- a" := (rng_opp a) : ring_scope.
Notation "0" := rng_zero : ring_scope.
Notation "1" := rng_one : ring_scope.

Arguments rng_eq_dec {_} {_} _%Rng _%Rng.

Fixpoint rng_power {A} {R : ring A} a n :=
  match n with
  | O => 1%Rng
  | S m => (a * rng_power a m)%Rng
  end.

Notation "a ^ b" := (rng_power a b) : ring_scope.

Section ring_theorems.

Context {A : Type}.
Context {r : ring A}.

Theorem rng_add_opp_r : ∀ x, (x - x = 0)%Rng.
Proof.
intros x; unfold rng_sub; rewrite rng_add_comm.
apply rng_add_opp_l.
Qed.

Theorem rng_mul_1_r : ∀ a, (a * 1 = a)%Rng.
Proof.
intros a; simpl.
rewrite rng_mul_comm, rng_mul_1_l.
reflexivity.
Qed.

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

Theorem rng_sub_compat_l : ∀ a b c,
  (a = b)%Rng → (a - c = b - c)%Rng.
Proof.
intros a b c Hab.
now rewrite Hab.
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
Proof. intros; easy. Qed.

Theorem rng_add_sub : ∀ a b, (a + b - b = a)%Rng.
Proof.
intros.
unfold rng_sub.
rewrite <- rng_add_assoc.
rewrite fold_rng_sub.
rewrite rng_add_opp_r.
apply rng_add_0_r.
Qed.

Theorem rng_sub_add : ∀ a b, (a - b + b = a)%Rng.
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

Theorem rng_add_reg_l : ∀ a b c, (c + a = c + b)%Rng → (a = b)%Rng.
Proof.
intros a b c Habc; simpl in Habc; simpl.
apply rng_add_reg_r with (c := c).
rewrite rng_add_comm; symmetry.
rewrite rng_add_comm; symmetry.
assumption.
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

Theorem rng_mul_0_l : ∀ a, (0 * a = 0)%Rng.
Proof.
intros a.
assert ((0 * a + a = a)%Rng) as H.
 transitivity ((0 * a + 1 * a)%Rng).
  rewrite rng_mul_1_l; reflexivity.

  rewrite <- rng_mul_add_distr_r.
  rewrite rng_add_0_l, rng_mul_1_l.
  reflexivity.

 apply rng_add_reg_r with (c := a).
 rewrite rng_add_0_l; assumption.
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

Theorem rng_add_move_0_r : ∀ a b, (a + b = 0)%Rng ↔ (a = - b)%Rng.
Proof.
intros a b.
split; intros H.
 apply rng_sub_compat_l with (c := b) in H.
 rewrite rng_add_sub in H.
 unfold rng_sub in H.
 now rewrite rng_add_0_l in H.

 rewrite H.
 rewrite rng_add_opp_l; reflexivity.
Qed.

Theorem rng_opp_inj_wd : ∀ a b, (- a = - b)%Rng ↔ (a = b)%Rng.
Proof.
intros a b; split; intros H.
 apply rng_add_move_0_r in H.
 rewrite rng_add_comm in H.
 apply rng_add_move_0_r in H.
 rewrite H.
 apply rng_add_move_0_r.
 apply rng_add_opp_r.

 rewrite H; reflexivity.
Qed.

Theorem rng_opp_involutive : ∀ x, (- - x)%Rng = x.
Proof.
intros.
symmetry.
apply rng_add_move_0_r.
apply rng_add_opp_r.
Qed.

Theorem rng_add_add_swap : ∀ n m p, (n + m + p = n + p + m)%Rng.
Proof.
intros n m p; simpl.
do 2 rewrite <- rng_add_assoc.
assert (m + p = p + m)%Rng as H by apply rng_add_comm.
rewrite H; reflexivity.
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

End ring_theorems.
