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
 *)

Require Import Utf8.

Class ring_like_op T :=
  { rngl_zero : T;
    rngl_one : T;
    rngl_add : T → T → T;
    rngl_mul : T → T → T;
    rngl_opp : T → T;
    rngl_inv : T → T }.

Declare Scope ring_like_scope.
Delimit Scope ring_like_scope with F.

Definition rngl_sub {T} {R : ring_like_op T} a b := rngl_add a (rngl_opp b).
Definition rngl_div {T} {R : ring_like_op T} a b := rngl_mul a (rngl_inv b).

Notation "0" := rngl_zero : ring_like_scope.
Notation "1" := rngl_one : ring_like_scope.
Notation "a + b" := (rngl_add a b) : ring_like_scope.
Notation "a - b" := (rngl_sub a b) : ring_like_scope.
Notation "a * b" := (rngl_mul a b) : ring_like_scope.
Notation "a / b" := (rngl_div a b) : ring_like_scope.
Notation "- a" := (rngl_opp a) : ring_like_scope.
Notation "¹/ a" := (rngl_inv a) (at level 35) : ring_like_scope.

Class ring_like_prop T {ro : ring_like_op T} :=
  { rngl_is_comm : bool;
    rngl_has_opp : bool;
    rngl_has_inv : bool;
    rngl_eq_is_dec : bool;
    rngl_is_integral : bool;
    rngl_add_comm : ∀ a b : T, (a + b = b + a)%F;
    rngl_add_assoc : ∀ a b c : T, (a + (b + c) = (a + b) + c)%F;
    rngl_add_0_l : ∀ a : T, (0 + a)%F = a;
    rngl_mul_assoc : ∀ a b c : T, (a * (b * c) = (a * b) * c)%F;
    rngl_mul_1_l : ∀ a : T, (1 * a)%F = a;
    rngl_mul_add_distr_l : ∀ a b c : T, (a * (b + c) = a * b + a * c)%F;
    (* when multiplication is commutative *)
    rngl_c_mul_comm :
      if rngl_is_comm then ∀ a b, (a * b = b * a)%F else True;
    (* when multiplication is not commutative *)
    rngl_nc_mul_1_r :
      if rngl_is_comm then True else ∀ a, (a * 1 = a)%F;
    rngl_nc_mul_add_distr_r :
      if rngl_is_comm then True else
       ∀ a b c, ((a + b) * c = a * c + b * c)%F;
    (* when has opposite *)
    rngl_o_add_opp_l :
      if rngl_has_opp then ∀ a : T, (- a + a = 0)%F else True;
    (* when has not opposite *)
    rngl_no_mul_0_l :
      if rngl_has_opp then True else ∀ a, (0 * a = 0)%F;
    rngl_no_mul_0_r :
      if rngl_has_opp then True else ∀ a, (a * 0 = 0)%F;
    (* when has inverse *)
    rngl_i_mul_inv_l :
      if rngl_has_inv then ∀ a : T, a ≠ 0%F → (¹/ a * a = 1)%F else True;
    (* when equality is decidable *)
    rngl_d_eq_dec :
      if rngl_eq_is_dec then ∀ a b : T, {a = b} + {a ≠ b} else True;
    (* when has_no_zero_divisors *)
    rngl_i_is_integral :
      if rngl_is_integral then ∀ a b, (a * b = 0)%F → a = 0%F ∨ b = 0%F
      else True }.

(* the fact that 1 ≠ 0 *)

Class ring_like_one_neq_zero T {ro : ring_like_op T} :=
  { rngl_1_neq_0 : (1 ≠ 0)%F }.

(*
Arguments rngl_eq_dec {T}%type {ro ring_like_dec_prop} _%F _%F.
*)

Fixpoint rngl_power {T} {R : ring_like_op T} a n :=
  match n with
  | O => 1%F
  | S m => (a * rngl_power a m)%F
  end.

Notation "a ^ b" := (rngl_power a b) : ring_like_scope.

Section ring_like_theorems.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {Hro : rngl_has_opp = true}.

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
specialize rngl_c_mul_comm as rngl_mul_comm.
specialize rngl_nc_mul_add_distr_r as rngl_mul_add_distr_r.
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
specialize rngl_c_mul_comm as rngl_mul_comm.
specialize rngl_nc_mul_1_r as rngl_mul_1_r.
destruct rngl_is_comm. {
  now rewrite rngl_mul_comm, rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
}
Qed.

Theorem rngl_sub_compat_l : ∀ a b c,
  (a = b)%F → (a - c = b - c)%F.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem fold_rngl_sub : ∀ a b, (a + - b)%F = (a - b)%F.
Proof. intros; easy. Qed.

Theorem rngl_add_opp_r : ∀ x, (x - x = 0)%F.
Proof.
intros.
specialize rngl_o_add_opp_l as rngl_add_opp_l.
destruct rngl_has_opp; [ | easy ].
unfold rngl_sub.
rewrite rngl_add_comm.
apply rngl_add_opp_l.
Qed.

Theorem rngl_add_sub : ∀ a b, (a + b - b = a)%F.
Proof.
intros.
unfold rngl_sub.
rewrite <- rngl_add_assoc.
rewrite fold_rngl_sub.
rewrite rngl_add_opp_r.
apply rngl_add_0_r.
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

Theorem rngl_add_opp_l : ∀ x, (- x + x = 0)%F.
Proof.
intros.
specialize rngl_o_add_opp_l as rngl_add_opp_l.
destruct rngl_has_opp; [ | easy ].
apply rngl_add_opp_l.
Qed.

Theorem rngl_opp_0 : (- 0 = 0)%F.
Proof.
transitivity (0 + - 0)%F. {
  symmetry.
  apply rngl_add_0_l.
}
apply rngl_add_opp_r.
Qed.

Theorem rngl_sub_0_r : ∀ a, (a - 0 = a)%F.
Proof.
intros.
unfold rngl_sub.
rewrite rngl_opp_0.
apply rngl_add_0_r.
Qed.

Theorem rngl_add_move_0_r : ∀ a b, (a + b = 0)%F ↔ (a = - b)%F.
Proof.
intros a b.
split; intros H. {
  apply rngl_sub_compat_l with (c := b) in H.
  rewrite rngl_add_sub in H.
  unfold rngl_sub in H.
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
apply rngl_add_move_0_r.
apply rngl_add_opp_r.
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

Theorem rngl_is_integral_if_inv_and_eq_dec :
  if (rngl_has_inv && rngl_eq_is_dec)%bool then
    ∀ a b, (a * b = 0)%F → a = 0%F ∨ b = 0%F
  else True.
Proof.
specialize rngl_i_mul_inv_l as rngl_mul_inv_l.
specialize rngl_d_eq_dec as rngl_eq_dec.
destruct rngl_has_inv; [ | easy ].
destruct rngl_eq_is_dec; [ | easy ].
cbn.
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

End ring_like_theorems.

Arguments rngl_add_opp_l {T}%type_scope {ro rp} Hro.
Arguments rngl_add_opp_r {T}%type_scope {ro rp} Hro.
Arguments rngl_add_reg_l {T}%type_scope {ro rp} Hro.
Arguments rngl_add_sub {T}%type_scope {ro rp} Hro.
Arguments rngl_mul_opp_opp {T}%type_scope {ro rp} Hro.
Arguments rngl_mul_0_l {T}%type_scope {ro rp} Hro.
Arguments rngl_mul_opp_r {T}%type_scope {ro rp} Hro.
Arguments rngl_mul_0_r {T}%type_scope {ro rp} Hro.
Arguments rngl_opp_0 {T}%type_scope {ro rp} Hro.
