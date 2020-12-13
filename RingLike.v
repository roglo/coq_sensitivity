(* Ring-like *)
(* Algebraic structures with two operations *)
(* Allows to define semirings, rings, fields, commutative or not,
   with two classes:
     ring_like_op, holding the operations, and
     ring_like_prop, holding their properties.
   In class ring_like_prop, we can set,
     to make a semiring:
        rngl_has_opp = false
        rngl_has_inv = false
     to make a ring:
        rngl_has_opp = true
        rngl_has_inv = false
     to make a field:
        rngl_has_opp = true
        rngl_has_inv = true
   They can be commutative or not by setting rngl_is_comm to true or false.
   There are many properties that are implemented here or could be
   implemented :
     - algebraically closed or not
     - archimedian or not
     - with decidable equality or not
     - commutative or not
     - complete or not
     - with characteristic 0 or not
     - finite or infinite
     - ordered or not
     - totally ordered or not
     - valuated or not
     - with associative addition or multiplication or not
     - with commutative addition or not
     - with 0 or without, right or left
     - with 1 or without, right or left
     - with division or not
     and so on.
   One problem is that some of these properties imply some others. If I
   take a boolean ab for the property A, and a boolean bb for the property
   B, and if A → B, then in the four cases of (ab,bb), the case (true,false)
   does not happen, and should not appear. But it does. How to do with that?
     Example:
       has inverse ⇒ has division (that is multiplication by inverse)
     But we can have a division without inverse : examples ℕ and ℤ
     Neither division nor inverse : matrices and ℤ/nℤ (n composed)
     But we cannot say "has inverse" and "has no division".
     By "has division", I mean an operation such that "a * b / b = a".
   What a mess!
*)

Require Import Utf8.

Class ring_like_op T :=
  { rngl_has_opp : bool;
    rngl_has_inv : bool;
    rngl_has_no_inv_but_div : bool;
    rngl_zero : T;
    rngl_one : T;
    rngl_add : T → T → T;
    rngl_mul : T → T → T;
    rngl_opp : T → T;
    rngl_inv : T → T;
    rngl_opt_sub : T → T → T;
    rngl_opt_div : T → T → T }.

Declare Scope ring_like_scope.
Delimit Scope ring_like_scope with F.

Definition rngl_sub {T} {R : ring_like_op T} a b :=
  if rngl_has_opp then rngl_add a (rngl_opp b) else rngl_opt_sub a b.
Definition rngl_div {T} {R : ring_like_op T} a b :=
  if rngl_has_inv then rngl_mul a (rngl_inv b) else rngl_opt_div a b.

Notation "0" := rngl_zero : ring_like_scope.
Notation "1" := rngl_one : ring_like_scope.
Notation "a + b" := (rngl_add a b) : ring_like_scope.
Notation "a - b" := (rngl_sub a b) : ring_like_scope.
Notation "a * b" := (rngl_mul a b) : ring_like_scope.
Notation "a / b" := (rngl_div a b) : ring_like_scope.
Notation "- a" := (rngl_opp a) : ring_like_scope.
Notation "¹/ a" := (rngl_inv a) (at level 35, right associativity) :
  ring_like_scope.

Fixpoint rngl_of_nat {T} {ro : ring_like_op T} n :=
  match n with
  | 0 => 0%F
  | S n' => (1 + rngl_of_nat n')%F
  end.

Class ring_like_prop T {ro : ring_like_op T} :=
  { rngl_is_comm : bool;
    rngl_has_dec_eq : bool;
    rngl_is_domain : bool;
    rngl_characteristic : nat;
    rngl_add_comm : ∀ a b : T, (a + b = b + a)%F;
    rngl_add_assoc : ∀ a b c : T, (a + (b + c) = (a + b) + c)%F;
    rngl_add_0_l : ∀ a : T, (0 + a)%F = a;
    rngl_mul_assoc : ∀ a b c : T, (a * (b * c) = (a * b) * c)%F;
    rngl_mul_1_l : ∀ a : T, (1 * a)%F = a;
    rngl_mul_add_distr_l : ∀ a b c : T, (a * (b + c) = a * b + a * c)%F;
    rngl_1_neq_0 : (1 ≠ 0)%F;
    (* when multiplication is commutative *)
    rngl_opt_mul_comm :
      if rngl_is_comm then ∀ a b, (a * b = b * a)%F else True;
    (* when multiplication is not commutative *)
    rngl_opt_mul_1_r :
      if rngl_is_comm then True else ∀ a, (a * 1 = a)%F;
    rngl_opt_mul_add_distr_r :
      if rngl_is_comm then True else
       ∀ a b c, ((a + b) * c = a * c + b * c)%F;
    (* when has opposite *)
    rngl_opt_add_opp_l :
      if rngl_has_opp then ∀ a : T, (- a + a = 0)%F else True;
    (* when has not opposite *)
    rngl_opt_add_sub :
      if rngl_has_opp then True else ∀ a b : T, (a + b - b = a)%F;
    rngl_opt_mul_0_l :
      if rngl_has_opp then True else ∀ a, (0 * a = 0)%F;
    rngl_opt_mul_0_r :
      if rngl_has_opp then True else ∀ a, (a * 0 = 0)%F;
    (* when has inverse *)
    rngl_opt_mul_inv_l :
      if rngl_has_inv then ∀ a : T, a ≠ 0%F → (¹/ a * a = 1)%F else True;
    rngl_opt_mul_inv_r :
      if (rngl_has_inv && negb rngl_is_comm)%bool then
        ∀ a : T, a ≠ 0%F → (a / a = 1)%F
      else True;
    (* when has no inverse but division *)
    rngl_opt_mul_div :
      if rngl_has_no_inv_but_div then ∀ a b : T, b ≠ 0%F → (a * b / b = a)%F
      else True;
    (* when equality is decidable *)
    rngl_opt_eq_dec :
      if rngl_has_dec_eq then ∀ a b : T, {a = b} + {a ≠ b} else True;
    (* when has_no_zero_divisors *)
    rngl_opt_is_integral :
      if rngl_is_domain then
        ∀ a b, (a * b = 0)%F → a = 0%F ∨ b = 0%F
      else True;
    (* characteristic *)
    rngl_characteristic_prop :
      match rngl_characteristic with
      | 0 => ∀ i, rngl_of_nat (S i) ≠ 0%F
      | n => rngl_of_nat n = 0%F
      end }.

Fixpoint rngl_power {T} {R : ring_like_op T} a n :=
  match n with
  | O => 1%F
  | S m => (a * rngl_power a m)%F
  end.

Notation "a ^ b" := (rngl_power a b) : ring_like_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {Hro : rngl_has_opp = true}.
Context {Hin : rngl_has_inv = true}.
Context {Hid : rngl_has_no_inv_but_div = true}.
Context {Hii : rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true}.

Theorem rngl_add_0_r : ∀ a, (a + 0 = a)%F.
Proof.
intros a; simpl.
rewrite rngl_add_comm.
apply rngl_add_0_l.
Qed.

Theorem rngl_add_add_swap : ∀ n m p, (n + m + p = n + p + m)%F.
Proof.
intros n m p; simpl.
do 2 rewrite <- rngl_add_assoc.
assert (m + p = p + m)%F as H by apply rngl_add_comm.
rewrite H; reflexivity.
Qed.

Theorem rngl_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%F.
Proof.
intros x y z; simpl.
specialize rngl_opt_mul_comm as rngl_mul_comm.
specialize rngl_opt_mul_add_distr_r as rngl_mul_add_distr_r.
destruct rngl_is_comm. {
  rewrite rngl_mul_comm.
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_comm.
  now rewrite (rngl_mul_comm z).
} {
  apply rngl_mul_add_distr_r.
}
Qed.

Theorem rngl_add_compat_l : ∀ a b c,
  (a = b)%F → (c + a = c + b)%F.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_add_compat_r : ∀ a b c,
  (a = b)%F → (a + c = b + c)%F.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_mul_1_r : ∀ a, (a * 1 = a)%F.
Proof.
intros.
specialize rngl_opt_mul_comm as rngl_mul_comm.
specialize rngl_opt_mul_1_r as rngl_mul_1_r.
destruct rngl_is_comm. {
  now rewrite rngl_mul_comm, rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
}
Qed.

Theorem rngl_mul_inv_r : ∀ a : T, a ≠ 0%F → (a / a = 1)%F.
Proof.
intros * Ha.
clear Hro Hin.
specialize rngl_opt_mul_inv_l as rngl_mul_inv_l.
specialize rngl_opt_mul_inv_r as rngl_mul_inv_r.
specialize rngl_opt_mul_comm as rngl_mul_comm.
specialize rngl_opt_mul_div as rngl_mul_div.
unfold rngl_div in rngl_mul_inv_r, rngl_mul_div |-*.
destruct rngl_has_inv. {
  destruct rngl_is_comm. {
    rewrite rngl_mul_comm.
    now apply rngl_mul_inv_l.
  } {
    cbn in rngl_mul_inv_r.
    now apply rngl_mul_inv_r.
  }
} {
  rewrite Hid in rngl_mul_div.
  specialize (rngl_mul_div 1%F a Ha) as H.
  now rewrite rngl_mul_1_l in H.
}
Qed.

Theorem rngl_mul_reg_r : ∀ a b c,
  c ≠ 0%F
  → (a * c = b * c)%F
  → a = b.
Proof.
intros * Hcz Hab.
clear Hro Hin Hid.
specialize rngl_opt_mul_inv_l as rngl_mul_inv_l.
specialize rngl_opt_mul_inv_r as rngl_mul_inv_r.
specialize rngl_opt_mul_comm as rngl_mul_comm.
specialize rngl_opt_mul_div as rngl_mul_div.
assert (H : (a * c / c = b * c / c)%F) by now rewrite Hab.
unfold rngl_div in H, rngl_mul_inv_r.
do 2 rewrite <- rngl_mul_assoc in H.
unfold rngl_div in rngl_mul_div.
destruct rngl_has_inv. {
  destruct rngl_is_comm. {
    rewrite (rngl_mul_comm c) in H.
    rewrite rngl_mul_inv_l in H; [ | easy ].
    now do 2 rewrite rngl_mul_1_r in H.
  } {
    rewrite rngl_mul_inv_r in H; [ | easy ].
    now do 2 rewrite rngl_mul_1_r in H.
  }
} {
  destruct Hii as [Hii'| Hii']; [ easy | ].
  rewrite Hii' in rngl_mul_div.
  rewrite rngl_mul_div in H; [ | easy ].
  now rewrite rngl_mul_div in H.
}
Qed.

Theorem rngl_sub_compat_l : ∀ a b c,
  (a = b)%F → (a - c = b - c)%F.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem fold_rngl_sub : ∀ a b, (a + - b)%F = (a - b)%F.
Proof.
intros.
unfold rngl_sub.
now rewrite Hro.
Qed.

Theorem rngl_add_opp_l : ∀ x, (- x + x = 0)%F.
Proof.
intros.
specialize rngl_opt_add_opp_l as rngl_add_opp_l.
destruct rngl_has_opp; [ | easy ].
apply rngl_add_opp_l.
Qed.

Theorem rngl_add_opp_r : ∀ x, (x - x = 0)%F.
Proof.
intros.
clear Hro.
specialize rngl_opt_add_opp_l as rngl_add_opp_l.
specialize rngl_opt_add_sub as rngl_add_sub.
unfold rngl_sub in rngl_add_sub |-*.
destruct rngl_has_opp. {
  rewrite rngl_add_comm.
  apply rngl_add_opp_l.
} {
  specialize (rngl_add_sub 0%F x).
  now rewrite rngl_add_0_l in rngl_add_sub.
}
Qed.

Theorem rngl_add_sub : ∀ a b, (a + b - b = a)%F.
Proof.
intros.
clear Hro.
specialize rngl_opt_add_opp_l as rngl_add_opp_l.
specialize rngl_opt_add_sub as rngl_add_sub.
unfold rngl_sub in rngl_add_sub |-*.
destruct rngl_has_opp. {
  rewrite <- rngl_add_assoc.
  rewrite (rngl_add_comm b).
  now rewrite rngl_add_opp_l, rngl_add_0_r.
} {
  apply rngl_add_sub.
}
Qed.

Theorem rngl_add_reg_r : ∀ a b c, (a + c = b + c)%F → (a = b)%F.
Proof.
intros * Habc.
eapply rngl_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rngl_add_sub in Habc.
Qed.

Theorem rngl_add_reg_l : ∀ a b c, (c + a = c + b)%F → (a = b)%F.
Proof.
intros * Habc.
eapply rngl_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rngl_add_comm, rngl_add_sub in Habc.
Qed.

Theorem rngl_mul_0_l : ∀ a, (0 * a = 0)%F.
Proof.
intros a.
apply (rngl_add_reg_r _ _ (1 * a)%F).
rewrite <- rngl_mul_add_distr_r.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_mul_0_r : ∀ a, (a * 0 = 0)%F.
Proof.
intros.
apply (rngl_add_reg_r _ _ (a * 1)%F).
rewrite <- rngl_mul_add_distr_l.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_opp_0 : (- 0 = 0)%F.
Proof.
specialize rngl_add_opp_r as H.
unfold rngl_sub in H.
rewrite Hro in H.
transitivity (0 + - 0)%F. {
  symmetry.
  apply rngl_add_0_l.
}
apply H.
Qed.

Theorem rngl_sub_0_r : ∀ a, (a - 0 = a)%F.
Proof.
intros.
clear Hro.
specialize (rngl_add_sub a 0%F) as H.
now rewrite rngl_add_0_r in H.
Qed.

Theorem rngl_add_move_0_r : ∀ a b, (a + b = 0)%F ↔ (a = - b)%F.
Proof.
intros a b.
split; intros H. {
  apply rngl_sub_compat_l with (c := b) in H.
  rewrite rngl_add_sub in H.
  unfold rngl_sub in H.
  rewrite Hro in H.
  now rewrite rngl_add_0_l in H.
} {
  rewrite H.
  now rewrite rngl_add_opp_l.
}
Qed.

Theorem rngl_opp_involutive : ∀ x, (- - x)%F = x.
Proof.
intros.
symmetry.
specialize rngl_add_opp_r as H.
unfold rngl_sub in H.
rewrite Hro in H.
now apply rngl_add_move_0_r.
Qed.

Theorem rngl_mul_opp_l : ∀ a b, (- a * b = - (a * b))%F.
Proof.
intros.
specialize (rngl_mul_add_distr_r (- a)%F a b) as H.
rewrite rngl_add_opp_l in H.
rewrite rngl_mul_0_l in H.
symmetry in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_opp_r : ∀ a b, (a * - b = - (a * b))%F.
Proof.
intros.
specialize (rngl_mul_add_distr_l a b (- b)%F) as H.
rewrite fold_rngl_sub in H.
rewrite rngl_add_opp_r in H.
rewrite rngl_mul_0_r in H.
symmetry in H.
rewrite rngl_add_comm in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_opp_opp : ∀ a b, (- a * - b = a * b)%F.
Proof.
intros.
rewrite rngl_mul_opp_l.
rewrite rngl_mul_opp_r.
apply rngl_opp_involutive.
Qed.

Theorem rngl_opp_inj : ∀ a b, (- a = - b)%F → a = b.
Proof.
intros.
rewrite <- (rngl_opp_involutive a).
rewrite H.
apply rngl_opp_involutive.
Qed.

Theorem rngl_integral :
  if (rngl_is_domain ||
      (rngl_has_inv && rngl_has_dec_eq))%bool then
    ∀ a b, (a * b = 0)%F → a = 0%F ∨ b = 0%F
  else True.
Proof.
specialize rngl_opt_mul_inv_l as rngl_mul_inv_l.
specialize rngl_opt_eq_dec as rngl_eq_dec.
specialize rngl_opt_is_integral as rngl_integral.
destruct rngl_is_domain; [ easy | ].
cbn in rngl_integral |-*.
destruct rngl_has_inv; [ | easy ].
destruct rngl_has_dec_eq; [ | easy ].
cbn; clear rngl_integral.
intros * Hab.
assert (H : (¹/a * a * b = ¹/a * 0)%F). {
  now rewrite <- rngl_mul_assoc, Hab.
}
rewrite rngl_mul_0_r in H.
destruct (rngl_eq_dec a 0%F) as [Haz| Haz]; [ now left | ].
rewrite rngl_mul_inv_l in H; [ | easy ].
rewrite rngl_mul_1_l in H.
now right.
Qed.

End a.

Arguments rngl_add_opp_l {T}%type {ro rp} Hro.
Arguments rngl_add_opp_r {T}%type {ro rp} x%F.
Arguments rngl_add_reg_l {T}%type {ro rp} (a b c)%F.
Arguments rngl_add_sub {T}%type {ro rp} (a b)%F.
Arguments rngl_integral {T}%type {ro rp} Hin.
Arguments rngl_mul_opp_opp {T}%type {ro rp} Hro.
Arguments rngl_mul_0_l {T}%type {ro rp} a%F.
Arguments rngl_mul_opp_r {T}%type {ro rp} Hro.
Arguments rngl_mul_reg_r {T}%type {ro rp} Hii (a b c)%F.
Arguments rngl_mul_0_r {T}%type {ro rp} a%F.
Arguments rngl_opp_0 {T}%type {ro rp}.
