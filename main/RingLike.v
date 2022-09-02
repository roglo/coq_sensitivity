(* Ring-like *)
(* Algebraic structures with two operations *)
(* Allows to define all kinds of semirings, rings, fields *)
(* Allows to define semirings, rings, fields, commutative or not,
   with two classes:
     ring_like_op, holding the operations, and
     ring_like_prop, holding their properties.
   In class ring_like_prop, we can set,
     to make a semiring:
        rngl_opt_opp_or_sous = Some (inr sous) where sous is a subtraction
        rngl_opt_opp_or_sous = None otherwise
        rngl_opt_inv = None
     to make a ring:
        rngl_opt_opp_or_sous = Some (inl opp), where opp is the opposite
        rngl_opt_inv = None
     to make a field:
        rngl_opt_opp_or_sous = Some (inl opp), where opp is the opposite
        rngl_opt_inv = Some inv, where opp is the inverse function
   They can be commutative or not by setting rngl_is_comm to true or false.
   There are many other properties that are implemented here or could be
   implemented :
     - archimedian or not
     - with calculable equality or not
     - commutative or not
     - with some characteristic
     - finite or infinite
     - ordered or not
     - totally ordered or not
     - valuated or not
     - principal or not
     - factorial or not
     - euclidean or not
     - algebraically closed or not
     - complete or not
     - with associative addition or multiplication or not
     - with commutative addition or not
     - with 0 or without, right or left
     - with 1 or without, right or left
     - with specific subtraction (sous) or not
     - with specific division or not
     and so on. *)

Set Nested Proofs Allowed.
Require Import Utf8.

Definition bool_of_option {T} (x : option T) :=
  match x with
  | Some _ => true
  | None => false
  end.

Class ring_like_op T :=
  { rngl_zero : T;
    rngl_one : T;
    rngl_add : T → T → T;
    rngl_mul : T → T → T;
    rngl_opt_opp_or_sous : option (sum (T → T) (T → T → T));
    rngl_opt_inv_or_quot : option (sum (T → T) (T → T → T));
    rngl_opt_eqb : option (T → T → bool);
    rngl_le : T → T → Prop }.

Declare Scope ring_like_scope.
Delimit Scope ring_like_scope with F.

Definition rngl_has_opp_or_sous {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_opp_or_sous.

Definition rngl_has_inv_or_quot {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_inv_or_quot.

Definition rngl_has_opp {T} {R : ring_like_op T} :=
  match rngl_opt_opp_or_sous with
  | Some (inl _) => true
  | _ => false
  end.

Definition rngl_has_sous {T} {R : ring_like_op T} :=
  match rngl_opt_opp_or_sous with
  | Some (inr _) => true
  | _ => false
  end.

Definition rngl_has_inv {T} {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot with
  | Some (inl _) => true
  | _ => false
  end.

Definition rngl_has_quot {T} {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot with
  | Some (inr _) => true
  | _ => false
  end.

Definition rngl_opp {T} {R : ring_like_op T} a :=
  match rngl_opt_opp_or_sous with
  | Some (inl rngl_opp) => rngl_opp a
  | _ => rngl_zero
  end.

Definition rngl_sous {T} {R : ring_like_op T} a b :=
  match rngl_opt_opp_or_sous with
  | Some (inr rngl_sous) => rngl_sous a b
  | _ => rngl_zero
  end.

Definition rngl_inv {T} {R : ring_like_op T} a :=
  match rngl_opt_inv_or_quot with
  | Some (inl rngl_inv) => rngl_inv a
  | _ => rngl_zero
  end.

Definition rngl_quot {T} {R : ring_like_op T} a b :=
  match rngl_opt_inv_or_quot with
  | Some (inr rngl_quot) => rngl_quot a b
  | _ => rngl_zero
  end.

Definition rngl_sub {T} {R : ring_like_op T} a b :=
  match rngl_opt_opp_or_sous with
  | Some (inl rngl_opp) => rngl_add a (rngl_opp b)
  | Some (inr rngl_sous) => rngl_sous a b
  | None => rngl_zero
  end.

Definition rngl_div {T} {R : ring_like_op T} a b :=
  match rngl_opt_inv_or_quot with
  | Some (inl rngl_inv) => rngl_mul a (rngl_inv b)
  | Some (inr rngl_quot) => rngl_quot a b
  | None => rngl_zero
  end.

Definition rngl_eqb {T} {R : ring_like_op T} a b :=
  match rngl_opt_eqb with
  | Some rngl_eqb => rngl_eqb a b
  | None => false
  end.

Notation "0" := rngl_zero : ring_like_scope.
Notation "1" := rngl_one : ring_like_scope.
Notation "a + b" := (rngl_add a b) : ring_like_scope.
Notation "a - b" := (rngl_sub a b) : ring_like_scope.
Notation "a * b" := (rngl_mul a b) : ring_like_scope.
Notation "a / b" := (rngl_div a b) : ring_like_scope.
Notation "a ≤ b" := (rngl_le a b) : ring_like_scope.
Notation "- a" := (rngl_opp a) : ring_like_scope.
Notation "a '⁻¹'" := (rngl_inv a) (at level 1, format "a ⁻¹") :
  ring_like_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c)%F (at level 70, b at next level) :
  ring_like_scope.

Notation "a =? b" := (rngl_eqb a b) (at level 70) : ring_like_scope.
Notation "a ≠? b" := (negb (rngl_eqb a b)) (at level 70) : ring_like_scope.

Notation "- 1" := (rngl_opp rngl_one) : ring_like_scope.

Inductive not_applicable := NA.

Fixpoint rngl_of_nat {T} {ro : ring_like_op T} n :=
  match n with
  | 0 => 0%F
  | S n' => (1 + rngl_of_nat n')%F
  end.

Class ring_like_prop T {ro : ring_like_op T} :=
  { rngl_is_comm : bool;
    rngl_has_eqb : bool;
    rngl_has_dec_le : bool;
    rngl_has_1_neq_0 : bool;
    rngl_is_ordered : bool;
    rngl_is_integral : bool;
    rngl_characteristic : nat;
    rngl_add_comm : ∀ a b : T, (a + b = b + a)%F;
    rngl_add_assoc : ∀ a b c : T, (a + (b + c) = (a + b) + c)%F;
    rngl_add_0_l : ∀ a : T, (0 + a)%F = a;
    rngl_mul_assoc : ∀ a b c : T, (a * (b * c) = (a * b) * c)%F;
    rngl_mul_1_l : ∀ a : T, (1 * a)%F = a;
    rngl_mul_add_distr_l : ∀ a b c : T, (a * (b + c) = a * b + a * c)%F;
    (* when 1 ≠ 0 *)
    rngl_opt_1_neq_0 : if rngl_has_1_neq_0 then (1 ≠ 0)%F else not_applicable;
    (* when multiplication is commutative *)
    rngl_opt_mul_comm :
      if rngl_is_comm then ∀ a b, (a * b = b * a)%F else not_applicable;
    (* when multiplication is not commutative *)
    rngl_opt_mul_1_r :
      if rngl_is_comm then not_applicable else ∀ a, (a * 1 = a)%F;
    rngl_opt_mul_add_distr_r :
      if rngl_is_comm then not_applicable else
       ∀ a b c, ((a + b) * c = a * c + b * c)%F;
    (* when has opposite *)
    rngl_opt_add_opp_l :
      if rngl_has_opp then ∀ a : T, (- a + a = 0)%F else not_applicable;
    (* when has subtraction (sous) *)
    rngl_opt_add_sub :
      if rngl_has_sous then ∀ a b, (a + b - b)%F = a
      else not_applicable;
    rngl_opt_sub_sub_sub_add :
      if rngl_has_sous then ∀ a b c, ((a - b) - c = a - (b + c))%F
      else not_applicable;
    rngl_opt_mul_sub_distr_l :
      if rngl_has_sous then ∀ a b c : T, (a * (b - c) = a * b - a * c)%F
      else not_applicable;
    rngl_opt_mul_sub_distr_r :
      if rngl_has_sous then
        if rngl_is_comm then not_applicable
        else ∀ a b c : T, ((a - b) * c = a * c - b * c)%F
      else not_applicable;
    (* when has inverse *)
    rngl_opt_mul_inv_l :
      if rngl_has_inv then ∀ a : T, a ≠ 0%F → (a⁻¹ * a = 1)%F
      else not_applicable;
    rngl_opt_mul_inv_r :
      if (rngl_has_inv && negb rngl_is_comm)%bool then
        ∀ a : T, a ≠ 0%F → (a / a = 1)%F
      else not_applicable;
    (* when has division (quot) *)
    rngl_opt_mul_div :
      if rngl_has_quot then ∀ a b, b ≠ 0%F → (a * b / b)%F = a
      else not_applicable;
    rngl_opt_mul_quot_r :
      if (rngl_has_quot && negb rngl_is_comm)%bool then
        ∀ a b, b ≠ 0%F → (b * a / b)%F = a
      else not_applicable;
    (* when equality is calculable *)
    rngl_opt_eqb_eq :
      if rngl_has_eqb then ∀ a b : T, (a =? b)%F = true ↔ a = b
      else not_applicable;
    (* when le comparison is decidable *)
    rngl_opt_le_dec :
      if rngl_has_dec_le then ∀ a b : T, ({a ≤ b} + {¬ a ≤ b})%F
      else not_applicable;
    (* when has_no_zero_divisors *)
    rngl_opt_integral :
      if rngl_is_integral then
        ∀ a b, (a * b = 0)%F → a = 0%F ∨ b = 0%F
      else not_applicable;
    (* characteristic *)
    rngl_characteristic_prop :
      if Nat.eqb (rngl_characteristic) 0 then ∀ i, rngl_of_nat (S i) ≠ 0%F
      else rngl_of_nat rngl_characteristic = 0%F;
    (* when ordered *)
    rngl_opt_le_refl :
      if rngl_is_ordered then ∀ a, (a ≤ a)%F else not_applicable;
    rngl_opt_le_antisymm :
      if rngl_is_ordered then ∀ a b, (a ≤ b → b ≤ a → a = b)%F
      else not_applicable;
    rngl_opt_le_trans :
      if rngl_is_ordered then ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%F
      else not_applicable;
    rngl_opt_add_le_compat :
      if rngl_is_ordered then ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%F
      else not_applicable;
    rngl_opt_mul_le_compat_nonneg :
      if (rngl_is_ordered && rngl_has_opp)%bool then
        ∀ a b c d, (0 ≤ a ≤ c)%F → (0 ≤ b ≤ d)%F → (a * b ≤ c * d)%F
      else not_applicable;
    rngl_opt_mul_le_compat_nonpos :
      if (rngl_is_ordered && rngl_has_opp)%bool then
        ∀ a b c d, (c ≤ a ≤ 0)%F → (d ≤ b ≤ 0)%F → (a * b ≤ c * d)%F
      else not_applicable;
    rngl_opt_mul_le_compat :
      if (rngl_is_ordered && negb rngl_has_opp)%bool then
        ∀ a b c d, (a ≤ c)%F → (b ≤ d)%F → (a * b ≤ c * d)%F
      else not_applicable;
    rngl_opt_not_le :
      if rngl_is_ordered then
        ∀ a b, (¬ a ≤ b → a = b ∨ b ≤ a)%F
      else not_applicable }.

Fixpoint rngl_power {T} {ro : ring_like_op T} a n :=
  match n with
  | O => 1%F
  | S m => (a * rngl_power a m)%F
  end.

Definition rngl_squ {T} {ro : ring_like_op T} x := (x * x)%F.

Notation "a ^ b" := (rngl_power a b) : ring_like_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_has_opp_has_opp_or_sous :
  rngl_has_opp = true
  → rngl_has_opp_or_sous = true.
Proof.
intros H.
unfold rngl_has_opp in H.
unfold rngl_has_opp_or_sous, bool_of_option.
now destruct rngl_opt_opp_or_sous.
Qed.

Theorem rngl_has_inv_has_inv_or_quot :
  rngl_has_inv = true
  → rngl_has_inv_or_quot = true.
Proof.
intros H.
unfold rngl_has_inv in H.
unfold rngl_has_inv_or_quot, bool_of_option.
now destruct rngl_opt_inv_or_quot.
Qed.

(* theorems easier to use *)

Theorem rngl_1_neq_0 :
  rngl_has_1_neq_0 = true →
  (1 ≠ 0)%F.
Proof.
intros H10.
specialize rngl_opt_1_neq_0 as H.
now rewrite H10 in H.
Qed.

Theorem rngl_mul_comm :
  rngl_is_comm = true →
  ∀ a b, (a * b = b * a)%F.
Proof.
intros H1 *.
specialize rngl_opt_mul_comm as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_1_r : ∀ a, (a * 1 = a)%F.
Proof.
intros.
specialize rngl_opt_mul_1_r as rngl_mul_1_r.
remember rngl_is_comm as ic eqn:Hic.
symmetry in Hic.
destruct ic; [ | easy ].
now rewrite rngl_mul_comm, rngl_mul_1_l.
Qed.

Theorem rngl_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%F.
Proof.
intros x y z; simpl.
specialize rngl_opt_mul_add_distr_r as rngl_mul_add_distr_r.
remember rngl_is_comm as ic eqn:Hic.
symmetry in Hic.
destruct ic. {
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_comm; [ | easy ].
  now rewrite (rngl_mul_comm Hic z).
} {
  apply rngl_mul_add_distr_r.
}
Qed.

Theorem rngl_add_opp_l :
  rngl_has_opp = true →
  ∀ x, (- x + x = 0)%F.
Proof.
intros H1 *.
specialize rngl_opt_add_opp_l as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_inv_l :
  rngl_has_inv = true →
  ∀ a : T, a ≠ 0%F → (a⁻¹ * a = 1)%F.
Proof.
intros H1 *.
specialize rngl_opt_mul_inv_l as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_eqb_eq :
  rngl_has_eqb = true →
  ∀ a b : T, rngl_eqb a b = true ↔ a = b.
Proof.
intros Heqb *.
specialize rngl_opt_eqb_eq as H.
now rewrite Heqb in H.
Qed.

Theorem rngl_eqb_neq :
  rngl_has_eqb = true →
  ∀ a b : T, rngl_eqb a b = false ↔ a ≠ b.
Proof.
intros Heqb *.
split; intros Hab. {
  intros H.
  apply (rngl_eqb_eq Heqb) in H.
  congruence.
} {
  remember (a =? b)%F as x eqn:Hx.
  symmetry in Hx.
  destruct x; [ | easy ].
  exfalso; apply Hab.
  now apply rngl_eqb_eq.
}
Qed.

Theorem rngl_eq_dec : rngl_has_eqb = true → ∀ a b : T, {a = b} + {a ≠ b}.
Proof.
intros Heq *.
remember (rngl_eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ now left; apply rngl_eqb_eq | now right; apply rngl_eqb_neq ].
Qed.

Theorem rngl_le_dec :
  rngl_has_dec_le = true →
  ∀ a b : T, ({a ≤ b} + {¬ a ≤ b})%F.
Proof.
intros H1 *.
specialize rngl_opt_le_dec as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_le_refl : rngl_is_ordered = true → ∀ a, (a ≤ a)%F.
Proof.
intros Hor *.
specialize rngl_opt_le_refl as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_trans :
  rngl_is_ordered = true →
   ∀ a b c : T, (a ≤ b)%F → (b ≤ c)%F → (a ≤ c)%F.
Proof.
intros H1 *.
specialize rngl_opt_le_trans as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_add_le_compat :
  rngl_is_ordered = true →
  ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%F.
Proof.
intros H1 *.
specialize rngl_opt_add_le_compat as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_nonneg :
  rngl_is_ordered = true →
  rngl_has_opp = true →
  ∀ a b c d, (0 ≤ a ≤ c)%F → (0 ≤ b ≤ d)%F → (a * b ≤ c * d)%F.
Proof.
intros Hor Hop *.
specialize rngl_opt_mul_le_compat_nonneg as H.
rewrite Hor, Hop in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_nonpos :
  rngl_is_ordered = true →
  rngl_has_opp = true →
  ∀ a b c d, (c ≤ a ≤ 0)%F → (d ≤ b ≤ 0)%F → (a * b ≤ c * d)%F.
Proof.
intros Hor Hop *.
specialize rngl_opt_mul_le_compat_nonpos as H.
rewrite Hor, Hop in H.
apply H.
Qed.

Theorem rngl_not_le :
  rngl_is_ordered = true →
  ∀ a b, (¬ a ≤ b → a = b ∨ b ≤ a)%F.
Proof.
intros Hor *.
specialize rngl_opt_not_le as H.
rewrite Hor in H.
apply H.
Qed.

(* *)

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

Theorem rngl_mul_mul_swap :
  rngl_is_comm = true →
  ∀ n m p, (n * m * p = n * p * m)%F.
Proof.
intros Hic n m p; simpl.
do 2 rewrite <- rngl_mul_assoc.
assert (m * p = p * m)%F as H by now apply rngl_mul_comm.
rewrite H; reflexivity.
Qed.

Theorem rngl_div_div_swap :
  rngl_is_comm = true →
  rngl_has_inv = true →
  ∀ a b c,
  (a / b / c = a / c / b)%F.
Proof.
intros Hic Hin *.
unfold rngl_has_inv in Hin.
unfold rngl_div.
destruct rngl_opt_inv_or_quot as [inv_quot| ]; [ | easy ].
destruct inv_quot as [inv| quot]; [ | easy ].
now rewrite rngl_mul_mul_swap.
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

Theorem fold_rngl_sub :
  rngl_has_opp = true →
  ∀ a b, (a + - b)%F = (a - b)%F.
Proof.
intros Hro *.
unfold rngl_has_opp in Hro.
unfold rngl_opp, rngl_sub.
now destruct rngl_opt_opp_or_sous as [[| ]| ].
Qed.

Theorem fold_rngl_div :
  rngl_has_inv = true →
  ∀ a b, (a * b⁻¹)%F = (a / b)%F.
Proof.
intros Hin *.
unfold rngl_has_inv in Hin.
unfold rngl_inv, rngl_div.
now destruct rngl_opt_inv_or_quot as [[| ]| ].
Qed.

Theorem rngl_sub_diag :
  rngl_has_opp_or_sous = true →
  ∀ a, (a - a = 0)%F.
Proof.
intros Hom *.
unfold rngl_has_opp_or_sous, bool_of_option in Hom.
unfold rngl_sub.
specialize rngl_add_opp_l as H1.
unfold rngl_has_opp, rngl_opp in H1.
specialize rngl_opt_add_sub as H2.
unfold rngl_has_sous, rngl_sub in H2.
destruct rngl_opt_opp_or_sous as [opp_sous| ]; [ | easy ].
destruct opp_sous as [opp| sous]. {
  specialize (H1 eq_refl).
  rewrite rngl_add_comm.
  apply H1.
} {
  specialize (H2 0%F a).
  now rewrite rngl_add_0_l in H2.
}
Qed.

Theorem rngl_div_diag :
  rngl_has_inv_or_quot = true →
  ∀ a : T, a ≠ 0%F → (a / a = 1)%F.
Proof.
intros Hiq * Haz.
unfold rngl_has_inv_or_quot, bool_of_option in Hiq.
unfold rngl_div.
specialize rngl_mul_inv_l as H1.
unfold rngl_has_inv, rngl_inv in H1.
specialize rngl_opt_mul_inv_r as H2.
unfold rngl_has_inv, rngl_div in H2.
specialize rngl_opt_mul_div as H3.
unfold rngl_has_quot, rngl_div in H3.
destruct rngl_opt_inv_or_quot as [inv_quot| ]; [ | easy ].
destruct inv_quot as [inv| quot]. {
  specialize (H1 eq_refl).
  remember rngl_is_comm as ic eqn:Hic; symmetry in Hic.
  destruct ic. {
    rewrite rngl_mul_comm; [ | easy ].
    now apply H1.
  }
  now rewrite H2.
} {
  specialize (H3 1%F a Haz).
  now rewrite rngl_mul_1_l in H3.
}
Qed.

Theorem rngl_add_sub :
  rngl_has_opp_or_sous = true →
  ∀ a b, (a + b - b = a)%F.
Proof.
intros Hom *.
unfold rngl_has_opp_or_sous, bool_of_option in Hom.
unfold rngl_sub.
specialize rngl_add_opp_l as H1.
unfold rngl_has_opp, rngl_opp in H1.
specialize rngl_opt_add_sub as H2.
unfold rngl_has_sous, rngl_sub in H2.
destruct rngl_opt_opp_or_sous as [opp_sous| ]; [ | easy ].
destruct opp_sous as [opp| sous]; [ | apply H2 ].
specialize (H1 eq_refl).
rewrite <- rngl_add_assoc.
rewrite (rngl_add_comm b).
rewrite H1.
apply rngl_add_0_r.
Qed.

Theorem rngl_mul_div :
  rngl_has_inv_or_quot = true →
  ∀ a b : T, b ≠ 0%F → (a * b / b)%F = a.
Proof.
intros Hii a b Hbz.
unfold rngl_has_inv_or_quot, bool_of_option in Hii.
unfold rngl_div.
specialize rngl_mul_inv_l as H1.
unfold rngl_has_inv, rngl_inv in H1.
specialize rngl_opt_mul_div as H2.
unfold rngl_has_quot, rngl_div in H2.
specialize rngl_div_diag as H3.
unfold rngl_has_inv_or_quot, bool_of_option in H3.
unfold rngl_div in H3.
destruct rngl_opt_inv_or_quot as [inv_quot| ]; [ | easy ].
destruct inv_quot as [inv| quot]; [ | now apply H2 ].
specialize (H1 eq_refl).
rewrite <- rngl_mul_assoc.
remember rngl_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic. {
  rewrite (rngl_mul_comm Hic b).
  rewrite H1; [ | easy ].
  apply rngl_mul_1_r.
}
specialize (H3 eq_refl).
rewrite H3; [ | easy ].
apply rngl_mul_1_r.
Qed.

Theorem rngl_add_cancel_l :
  rngl_has_opp_or_sous = true →
  ∀ a b c, (a + b = a + c)%F → (b = c)%F.
Proof.
intros Hom * Habc.
unfold rngl_has_opp_or_sous, bool_of_option in Hom.
specialize rngl_add_opp_l as H1.
unfold rngl_has_opp, rngl_opp in H1.
specialize rngl_opt_add_sub as H2.
unfold rngl_has_sous, rngl_sub in H2.
apply (f_equal (λ x, rngl_sub x a)) in Habc.
unfold rngl_sub in Habc.
destruct rngl_opt_opp_or_sous as [opp_sous| ]; [ | easy ].
destruct opp_sous as [opp| sous]. {
  specialize (H1 eq_refl).
  do 2 rewrite (rngl_add_comm _ (opp a)) in Habc.
  do 2 rewrite rngl_add_assoc in Habc.
  rewrite H1 in Habc.
  now do 2 rewrite rngl_add_0_l in Habc.
} {
  do 2 rewrite (rngl_add_comm a) in Habc.
  now rewrite <- (H2 b a), <- (H2 c a).
}
Qed.

Theorem rngl_mul_cancel_l :
  rngl_has_inv_or_quot = true →
  ∀ a b c, a ≠ 0%F
  → (a * b = a * c)%F
  → b = c.
Proof.
intros Hiq * Haz Habc.
unfold rngl_has_inv_or_quot, bool_of_option in Hiq.
specialize rngl_mul_inv_l as H1.
unfold rngl_has_inv, rngl_inv in H1.
specialize rngl_opt_mul_div as H2.
unfold rngl_has_quot, rngl_div in H2.
specialize rngl_opt_mul_quot_r as H3.
unfold rngl_has_quot, rngl_div in H3.
remember rngl_opt_inv_or_quot as x eqn:Hx.
symmetry in Hx.
destruct x as [inv_quot| ]; [ | easy ].
destruct inv_quot as [inv| quot]. {
  specialize (H1 eq_refl).
  apply (f_equal (λ x, rngl_mul (inv a) x)) in Habc.
  do 2 rewrite rngl_mul_assoc in Habc.
  rewrite H1 in Habc; [ | easy ].
  now do 2 rewrite rngl_mul_1_l in Habc.
} {
  remember rngl_is_comm as ic eqn:Hic; symmetry in Hic.
  apply (f_equal (λ x, quot x a)) in Habc.
  destruct ic. {
    do 2 rewrite (rngl_mul_comm Hic a) in Habc.
    rewrite H2 in Habc; [ | easy ].
    rewrite H2 in Habc; [ | easy ].
    easy.
  } {
    cbn in H3.
    now do 2 rewrite (H3 _ _ Haz) in Habc.
  }
}
Qed.

Theorem rngl_add_sub_eq_l :
  rngl_has_opp_or_sous = true →
  ∀ a b c, (a + b = c → c - a = b)%F.
Proof.
intros Hom * Hab.
rewrite <- Hab.
rewrite rngl_add_comm.
now apply rngl_add_sub.
Qed.

Theorem rngl_add_sub_eq_r :
  rngl_has_opp_or_sous = true →
   ∀ a b c, (a + b = c → c - b = a)%F.
Proof.
intros Hom * Hab.
apply rngl_add_sub_eq_l; [ easy | ].
now rewrite rngl_add_comm.
Qed.

Theorem rngl_sub_compat_l : ∀ a b c,
  (a = b)%F → (a - c = b - c)%F.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_add_cancel_r :
  rngl_has_opp_or_sous = true →
  ∀ a b c, (a + c = b + c)%F → (a = b)%F.
Proof.
intros Hom * Habc.
eapply rngl_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rngl_add_sub in Habc.
Qed.

Theorem rngl_mul_0_r :
  rngl_has_opp_or_sous = true →
  ∀ a, (a * 0 = 0)%F.
Proof.
intros Hom *.
apply (rngl_add_cancel_r Hom _ _ (a * 1)%F).
rewrite <- rngl_mul_add_distr_l.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_mul_0_l :
  rngl_has_opp_or_sous = true →
  ∀ a, (0 * a = 0)%F.
Proof.
intros Hom a.
apply (rngl_add_cancel_r Hom _ _ (1 * a)%F).
rewrite <- rngl_mul_add_distr_r.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_add_move_0_r :
  rngl_has_opp = true →
  ∀ a b, (a + b = 0)%F ↔ (a = - b)%F.
Proof.
intros Hro *.
split; intros H. {
  apply rngl_sub_compat_l with (c := b) in H.
  rewrite rngl_add_sub in H; [ | now apply rngl_has_opp_has_opp_or_sous ].
  unfold rngl_sub in H.
  unfold rngl_has_opp in Hro.
  unfold rngl_opp.
  destruct rngl_opt_opp_or_sous as [x| ]; [ | easy ].
  destruct x as [x| x]; [ | easy ].
  now rewrite rngl_add_0_l in H.
} {
  rewrite H.
  now rewrite rngl_add_opp_l.
}
Qed.

Theorem rngl_mul_opp_r :
  rngl_has_opp = true →
  ∀ a b, (a * - b = - (a * b))%F.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_l a b (- b)%F) as H.
rewrite fold_rngl_sub in H; [ | easy ].
rewrite rngl_sub_diag in H; [ | now apply rngl_has_opp_has_opp_or_sous ].
rewrite rngl_mul_0_r in H; [ | now apply rngl_has_opp_has_opp_or_sous ].
symmetry in H.
rewrite rngl_add_comm in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_l :
  rngl_has_opp_or_sous = true →
  ∀ a b c, (a * (b - c) = a * b - a * c)%F.
Proof.
intros Hom *.
unfold rngl_has_opp_or_sous, bool_of_option in Hom.
unfold rngl_sub.
specialize rngl_mul_opp_r as H1.
unfold rngl_has_opp, rngl_opp in H1.
specialize rngl_opt_mul_sub_distr_l as H2.
unfold rngl_has_sous, rngl_sub in H2.
destruct rngl_opt_opp_or_sous as [opp_sous| ]; [ | easy ].
destruct opp_sous as [opp| sous]; [ | apply H2 ].
specialize (H1 eq_refl).
rewrite rngl_mul_add_distr_l.
now rewrite H1.
Qed.

Theorem rngl_div_mul :
  rngl_has_inv = true →
  ∀ a b, b ≠ 0%F → (a / b * b)%F = a.
Proof.
intros Hin * Hbz.
unfold rngl_has_inv in Hin.
unfold rngl_div.
specialize (rngl_mul_inv_l Hin) as H1.
unfold rngl_inv in H1.
destruct rngl_opt_inv_or_quot as [inv_quot| ]; [ | easy ].
destruct inv_quot as [inv| quot]; [ | easy ].
rewrite <- rngl_mul_assoc.
rewrite H1; [ | easy ].
apply rngl_mul_1_r.
Qed.

Theorem rngl_div_0_l :
  rngl_has_opp_or_sous = true →
  rngl_has_inv_or_quot = true →
  ∀ a, a ≠ 0%F → (0 / a)%F = 0%F.
Proof.
intros Hos Hiv * Haz.
remember (0 / a)%F as x eqn:Hx.
replace 0%F with (0 * a)%F in Hx. 2: {
  now apply rngl_mul_0_l.
}
subst x.
now apply rngl_mul_div.
Qed.

Theorem rngl_div_div_mul_mul :
  rngl_is_comm = true →
  rngl_has_inv = true →
  ∀ a b c d,
  b ≠ 0%F
  → d ≠ 0%F
  → (a / b = c / d)%F ↔ (a * d = b * c)%F.
Proof.
intros Hic Hin * Hbz Hdz.
specialize (rngl_has_inv_has_inv_or_quot Hin) as Hin'.
move Hin' before Hin.
split. {
  intros Habcd.
  apply (f_equal (λ x, rngl_mul x b)) in Habcd.
  rewrite rngl_div_mul in Habcd; [ | easy | easy ].
  apply (f_equal (λ x, rngl_mul x d)) in Habcd.
  rewrite (rngl_mul_comm Hic _ b) in Habcd.
  rewrite <- rngl_mul_assoc in Habcd.
  now rewrite rngl_div_mul in Habcd.
} {
  intros Habcd.
  apply (f_equal (λ x, rngl_div x d)) in Habcd.
  rewrite rngl_mul_div in Habcd; [ | easy | easy ].
  apply (f_equal (λ x, rngl_div x b)) in Habcd.
  rewrite rngl_div_div_swap in Habcd; [ | easy | easy ].
  rewrite rngl_mul_comm in Habcd; [ | easy ].
  now rewrite rngl_mul_div in Habcd.
}
Qed.

Theorem rngl_integral :
  rngl_has_opp_or_sous = true →
  (rngl_is_integral || (rngl_has_inv_or_quot && rngl_has_eqb))%bool = true →
  ∀ a b, (a * b = 0)%F → a = 0%F ∨ b = 0%F.
Proof.
intros Hmo Hdo * Hab.
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral; [ now apply rngl_integral | ].
remember rngl_has_inv as iv eqn:Hiv; symmetry in Hiv.
cbn in Hdo.
destruct iv. {
  remember rngl_has_eqb as de eqn:Hde; symmetry in Hde.
  destruct de; [ | now destruct rngl_has_inv_or_quot ].
  cbn; clear rngl_integral.
  assert (H : (a⁻¹ * a * b = a⁻¹ * 0)%F). {
    now rewrite <- rngl_mul_assoc, Hab.
  }
  rewrite rngl_mul_0_r in H; [ | easy ].
  remember (rngl_eqb a 0%F) as az eqn:Haz; symmetry in Haz.
  destruct az; [ now left; apply (rngl_eqb_eq Hde) | ].
  apply (rngl_eqb_neq Hde) in Haz.
  rewrite rngl_mul_inv_l in H; [ | easy | easy ].
  rewrite rngl_mul_1_l in H.
  now right.
} {
  cbn in Hdo.
  apply andb_prop in Hdo.
  destruct Hdo as (Hdi, Hde).
  specialize rngl_mul_div as H1.
  rewrite Hdi in H1.
  specialize (H1 eq_refl).
  remember (rngl_eqb b 0%F) as bz eqn:Hbz; symmetry in Hbz.
  destruct bz; [ now right; apply (rngl_eqb_eq Hde) | left ].
  apply (rngl_eqb_neq Hde) in Hbz.
  specialize (H1 a b Hbz) as H4.
  rewrite Hab in H4.
  rewrite <- H4.
  now apply rngl_div_0_l.
}
Qed.

Theorem rngl_sub_move_0_r :
  rngl_has_opp = true →
  ∀ a b : T, (a - b)%F = 0%F ↔ a = b.
Proof.
intros Hop *.
split; intros Hab. {
  specialize (rngl_add_opp_l Hop) as H1.
  unfold rngl_opp in H1.
  apply (rngl_add_compat_r _ _ b) in Hab.
  unfold rngl_sub in Hab.
  unfold rngl_has_opp in Hop.
  destruct rngl_opt_opp_or_sous as [opp_sous| ]; [ | easy ].
  destruct opp_sous as [opp| sous]; [ | easy ].
  rewrite <- rngl_add_assoc in Hab.
  rewrite H1 in Hab.
  now rewrite rngl_add_0_r, rngl_add_0_l in Hab.
} {
  rewrite Hab.
  apply rngl_sub_diag.
  now apply rngl_has_opp_has_opp_or_sous.
}
Qed.

Theorem rngl_mul_cancel_r :
  rngl_has_inv_or_quot = true →
  ∀ a b c, c ≠ 0%F
  → (a * c = b * c)%F
  → a = b.
Proof.
intros Hii * Hcz Hab.
assert (H : (a * c / c = b * c / c)%F) by now rewrite Hab.
rewrite rngl_mul_div in H; [ | easy | easy ].
rewrite rngl_mul_div in H; [ | easy | easy ].
easy.
Qed.

Theorem rngl_div_compat_l :
  rngl_has_inv = true →
  ∀ a b c, c ≠ 0%F → (a = b)%F → (a / c = b / c)%F.
Proof.
intros Hin a b c Hcz Hab.
now rewrite Hab.
Qed.

Theorem rngl_inv_if_then_else_distr : ∀ (c : bool) a b,
  ((if c then a else b)⁻¹ = if c then a⁻¹ else b⁻¹)%F.
Proof. now destruct c. Qed.

Theorem rngl_mul_if_then_else_distr : ∀ (x : bool) a b c d,
  ((if x then a else b) * (if x then c else d) = if x then a * c else b * d)%F.
Proof. now destruct x. Qed.

Theorem rngl_opp_0 : rngl_has_opp = true → (- 0 = 0)%F.
Proof.
intros Hro.
transitivity (0 + - 0)%F. {
  symmetry.
  apply rngl_add_0_l.
}
rewrite fold_rngl_sub; [ | easy ].
apply rngl_sub_diag.
now apply rngl_has_opp_has_opp_or_sous.
Qed.

Theorem rngl_sub_0_r :
  rngl_has_opp_or_sous = true →
  ∀ a, (a - 0 = a)%F.
Proof.
intros Hom *.
unfold rngl_has_opp_or_sous, bool_of_option in Hom.
specialize rngl_opp_0 as H1.
specialize rngl_opt_add_sub as H2.
unfold rngl_has_opp, rngl_opp in H1.
unfold rngl_has_sous, rngl_sub in H2.
unfold rngl_sub.
destruct rngl_opt_opp_or_sous as [opp_sous| ]; [ | easy ].
destruct opp_sous as [opp| sous]. {
  rewrite H1; [ | easy ].
  now apply rngl_add_0_r.
} {
  specialize (H2 a 0%F).
  now rewrite rngl_add_0_r in H2.
}
Qed.

Theorem rngl_opp_add_distr :
  rngl_has_opp = true →
  ∀ a b, (- (a + b) = - b - a)%F.
Proof.
intros Hro *.
specialize (rngl_has_opp_has_opp_or_sous Hro) as Hro'.
generalize Hro; intros Hro''.
unfold rngl_has_opp in Hro''.
apply rngl_add_cancel_l with (a := (a + b)%F); [ easy | ].
rewrite (fold_rngl_sub Hro).
rewrite rngl_sub_diag; [ | easy ].
unfold rngl_sub.
specialize (rngl_add_sub Hro') as H1.
specialize (rngl_sub_diag Hro') as H2.
unfold rngl_sub in H2.
unfold rngl_opp.
unfold rngl_has_opp_or_sous, bool_of_option in Hro'.
destruct rngl_opt_opp_or_sous as [opp_sous| ]; [ | easy ].
destruct opp_sous as [opp| sous]; [ | easy ].
rewrite rngl_add_assoc.
rewrite <- (rngl_add_assoc _ _ (opp b)).
rewrite H2, rngl_add_0_r.
now symmetry; apply H2.
Qed.

Theorem rngl_add_sub_simpl_l :
  rngl_has_opp_or_sous = true →
  ∀ a b c : T, (a + b - (a + c) = b - c)%F.
Proof.
intros Hom *.
specialize rngl_opp_add_distr as H1.
specialize (rngl_sub_diag Hom) as H2.
specialize rngl_opt_sub_sub_sub_add as H3.
unfold rngl_has_opp in H1.
unfold rngl_has_sous in H3.
unfold rngl_has_opp_or_sous, bool_of_option in Hom.
remember rngl_opt_opp_or_sous as x eqn:Hop; symmetry in Hop.
destruct x as [opp_sous| ]; [ | easy ].
destruct opp_sous as [opp| sous]. {
  specialize (H1 eq_refl).
  unfold rngl_opp in H1; rewrite Hop in H1.
  unfold rngl_sub; rewrite Hop.
  rewrite H1.
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap.
  rewrite (rngl_add_add_swap a).
  unfold rngl_sub in H2.
  rewrite Hop in H2.
  now rewrite H2, rngl_add_0_l.
}
rewrite <- H3.
rewrite rngl_add_comm.
rewrite rngl_add_sub; [ easy | ].
unfold rngl_has_opp_or_sous, bool_of_option.
now rewrite Hop.
Qed.

Theorem rngl_inv_1 :
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  (1⁻¹ = 1)%F.
Proof.
intros Hin H10.
specialize (rngl_has_inv_has_inv_or_quot Hin) as Hin'.
specialize (rngl_div_diag Hin' 1%F) as H1.
unfold rngl_div in H1.
unfold rngl_has_inv in Hin.
unfold rngl_has_inv_or_quot, bool_of_option in Hin'.
unfold rngl_inv.
remember rngl_opt_inv_or_quot as x eqn:Hx; symmetry in Hx.
destruct x as [inv_quot| ]; [ | easy ].
destruct inv_quot as [inv| quot]; [ | easy ].
rewrite rngl_mul_1_l in H1.
apply H1.
now apply rngl_1_neq_0.
Qed.

Theorem rngl_div_1_l :
  rngl_has_inv = true →
  ∀ a, (1 / a = a⁻¹)%F.
Proof.
intros Hin *.
unfold rngl_has_inv in Hin.
unfold rngl_div, rngl_inv.
destruct rngl_opt_inv_or_quot as [inv_quot| ]; [ | easy ].
destruct inv_quot as [inv| quot]; [ | easy ].
apply rngl_mul_1_l.
Qed.

Theorem rngl_div_1_r :
  rngl_has_inv_or_quot = true →
  rngl_has_1_neq_0 = true →
  ∀ a, (a / 1 = a)%F.
Proof.
intros Hid H10 *.
specialize (rngl_mul_div Hid a 1%F (rngl_1_neq_0 H10)) as H1.
now rewrite rngl_mul_1_r in H1.
Qed.

Theorem rngl_mul_move_1_r :
  rngl_has_inv = true → ∀ a b : T, b ≠ 0%F → (a * b)%F = 1%F ↔ a = (b⁻¹)%F.
Proof.
intros Hin * Hbz.
split; intros H. {
  apply rngl_div_compat_l with (c := b) in H; [ | easy | easy ].
  specialize rngl_mul_div as H1.
  unfold rngl_has_inv_or_quot, bool_of_option in H1.
  unfold rngl_div in H1.
  unfold rngl_has_inv in Hin.
  unfold rngl_div in H.
  unfold rngl_inv.
  destruct rngl_opt_inv_or_quot as [inv_quot| ]; [ | easy ].
  destruct inv_quot as [inv| quot]; [ | easy ].
  rewrite rngl_mul_1_l in H.
  now rewrite H1 in H.
} {
  rewrite H.
  now apply rngl_mul_inv_l.
}
Qed.

Theorem rngl_opp_involutive :
  rngl_has_opp = true →
  ∀ x, (- - x)%F = x.
Proof.
intros Hro *.
symmetry.
apply (rngl_add_move_0_r Hro).
rewrite (fold_rngl_sub Hro).
apply rngl_sub_diag.
now apply rngl_has_opp_has_opp_or_sous.
Qed.

Theorem rngl_inv_neq_0 :
  rngl_has_opp_or_sous = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  ∀ a, a ≠ 0%F → (a⁻¹ ≠ 0)%F.
Proof.
intros Hom Hin H10 * Haz H1.
symmetry in H1.
apply rngl_mul_move_1_r in H1; [ | easy | easy ].
rewrite rngl_mul_0_l in H1; [ | easy ].
symmetry in H1; revert H1.
now apply rngl_1_neq_0.
Qed.

Theorem rngl_inv_involutive :
  rngl_has_opp_or_sous = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  ∀ x, x ≠ 0%F → (x⁻¹⁻¹)%F = x.
Proof.
intros Hom Hin H10 * Hxz.
specialize (rngl_has_inv_has_inv_or_quot Hin) as Hin'.
move Hin' before Hin.
symmetry.
specialize (rngl_mul_div Hin') as mul_div.
specialize (rngl_mul_move_1_r Hin) as mul_move_1_r.
specialize (rngl_inv_neq_0 Hom Hin H10) as inv_neq_0.
unfold rngl_div in mul_div.
unfold rngl_inv in mul_move_1_r, inv_neq_0.
unfold rngl_has_inv in Hin.
unfold rngl_inv.
destruct rngl_opt_inv_or_quot as [inv_quot| ]; [ | easy ].
destruct inv_quot as [inv| quot]; [ | easy ].
apply mul_move_1_r. 2: {
  specialize (mul_div 1%F x Hxz).
  now rewrite rngl_mul_1_l in mul_div.
}
now apply inv_neq_0.
Qed.

Theorem rngl_mul_opp_l :
  rngl_has_opp = true →
  ∀ a b, (- a * b = - (a * b))%F.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_r (- a)%F a b) as H.
rewrite rngl_add_opp_l in H; [ | easy ].
rewrite rngl_mul_0_l in H. 2: {
  now apply rngl_has_opp_has_opp_or_sous.
}
symmetry in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_opp_opp :
  rngl_has_opp = true →
  ∀ a b, (- a * - b = a * b)%F.
Proof.
intros Hro *.
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
now apply rngl_opp_involutive.
Qed.

Theorem rngl_squ_opp_1 : rngl_has_opp = true → (-1 * -1)%F = 1%F.
Proof.
intros Hop.
rewrite rngl_mul_opp_opp; [ | easy ].
apply rngl_mul_1_l.
Qed.

Theorem rngl_opp_inj :
  rngl_has_opp = true →
  ∀ a b, (- a = - b)%F → a = b.
Proof.
intros Hro * H.
rewrite <- (rngl_opp_involutive Hro a).
rewrite H.
now apply rngl_opp_involutive.
Qed.

Theorem rngl_inv_inj :
  rngl_has_opp_or_sous = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  ∀ a b, a ≠ 0%F → b ≠ 0%F →(a⁻¹ = b⁻¹)%F → a = b.
Proof.
intros Hom Hin H10 * Haz Hbz H.
rewrite <- (rngl_inv_involutive Hom Hin H10 a); [ | easy ].
rewrite H.
now apply rngl_inv_involutive.
Qed.

Theorem rngl_inv_mul_distr :
  rngl_has_opp_or_sous = true →
  rngl_is_integral = true →
  rngl_has_inv = true →
  ∀ a b, a ≠ 0%F → b ≠ 0%F →((a * b)⁻¹ = b⁻¹ * a⁻¹)%F.
Proof.
intros Hom Hdo Hin * Haz Hbz.
specialize (rngl_has_inv_has_inv_or_quot Hin) as Hin'.
move Hin' before Hin.
specialize (rngl_mul_cancel_l Hin') as mul_cancel_l.
specialize (rngl_div_diag Hin') as div_diag.
specialize (rngl_integral Hom) as integral.
unfold rngl_div in div_diag.
rewrite Hdo in integral; cbn in integral.
specialize (integral eq_refl).
assert (Habz : (a * b)%F ≠ 0%F). {
  intros H.
  specialize (integral a b H).
  now destruct integral.
}
apply mul_cancel_l with (a := (a * b)%F); [ easy | ].
unfold rngl_has_inv in Hin.
unfold rngl_inv.
remember rngl_opt_inv_or_quot as x eqn:Hx.
symmetry in Hx.
destruct x as [inv_quot| ]; [ | easy ].
destruct inv_quot as [inv| quot]; [ | easy ].
rewrite div_diag; [ | easy ].
rewrite rngl_mul_assoc.
rewrite <- (rngl_mul_assoc a).
rewrite div_diag; [ | easy ].
rewrite rngl_mul_1_r.
now symmetry; apply div_diag.
Qed.

Theorem rngl_eq_add_0 :
  rngl_is_ordered = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → a + b = 0 → a = 0 ∧ b = 0)%F.
Proof.
intros Hor * Haz Hbz Hab.
specialize rngl_opt_le_antisymm as rngl_le_antisymm.
rewrite Hor in rngl_le_antisymm.
split. {
  apply rngl_le_antisymm in Haz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%F as ab.
  rewrite <- (rngl_add_0_r a); subst ab.
  apply rngl_add_le_compat; [ easy | now apply rngl_le_refl | easy ].
} {
  apply rngl_le_antisymm in Hbz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%F as ab.
  rewrite <- (rngl_add_0_l b); subst ab.
  apply rngl_add_le_compat; [ easy | easy | now apply rngl_le_refl ].
}
Qed.

Theorem rngl_opp_sub_distr :
  rngl_has_opp = true →
  ∀ a b, (- (a - b) = b - a)%F.
Proof.
intros Hro *.
specialize (rngl_opp_add_distr Hro) as H1.
specialize (rngl_opp_involutive Hro) as H2.
unfold rngl_sub, rngl_opp in H1.
unfold rngl_sub, rngl_opp in H2.
unfold rngl_sub, rngl_opp.
unfold rngl_has_opp in Hro.
destruct rngl_opt_opp_or_sous as [x| ]; [ | easy ].
destruct x as [opp| sous]; [ | easy ].
rewrite H1.
f_equal.
apply H2.
Qed.

Theorem rngl_sub_add_distr :
  rngl_has_opp_or_sous = true →
  ∀ a b c, (a - (b + c) = a - b - c)%F.
Proof.
intros Hom *.
specialize rngl_opp_add_distr as H1.
unfold rngl_has_opp, rngl_opp in H1.
specialize rngl_opt_sub_sub_sub_add as H2.
unfold rngl_has_sous in H2.
unfold rngl_has_opp_or_sous, bool_of_option in Hom.
remember rngl_opt_opp_or_sous as x eqn:Hop; symmetry in Hop.
destruct x as [opp_sous| ]; [ | easy ].
destruct opp_sous as [opp| sous]. {
  specialize (H1 eq_refl).
  unfold rngl_sub.
  rewrite Hop, H1.
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  apply rngl_add_add_swap.
}
symmetry; apply H2.
Qed.

Theorem rngl_sub_sub_distr :
  rngl_has_opp = true →
  ∀ a b c, (a - (b - c) = a - b + c)%F.
Proof.
intros Hom *.
specialize rngl_opp_add_distr as H1.
unfold rngl_has_opp, rngl_opp in H1.
specialize (rngl_opp_involutive Hom) as H2.
unfold rngl_opp in H2.
unfold rngl_has_opp_or_sous, bool_of_option in Hom.
remember rngl_opt_opp_or_sous as x eqn:Hop; symmetry in Hop.
destruct x as [opp_sous| ]. 2: {
  rewrite <- H2; symmetry.
  now rewrite <- H2.
}
destruct opp_sous as [opp| sous]. 2: {
  rewrite <- H2; symmetry.
  now rewrite <- H2.
}
specialize (H1 eq_refl).
unfold rngl_sub.
rewrite Hop, H1, H2.
unfold rngl_sub; rewrite Hop.
rewrite rngl_add_assoc.
apply rngl_add_add_swap.
Qed.

Theorem eq_rngl_of_nat_0 :
  rngl_characteristic = 0 →
  ∀ i, rngl_of_nat i = 0%F → i = 0.
Proof.
intros Hch * Hi.
induction i; [ easy | exfalso ].
cbn in Hi.
specialize rngl_characteristic_prop as rngl_char_prop.
rewrite Hch in rngl_char_prop.
now specialize (rngl_char_prop i) as H.
Qed.

Theorem rngl_of_nat_inj :
  rngl_has_opp_or_sous = true →
  rngl_characteristic = 0 →
  ∀ i j,
  rngl_of_nat i = rngl_of_nat j
  → i = j.
Proof.
intros Hom Hch * Hij.
revert i Hij.
induction j; intros. {
  cbn in Hij.
  now apply eq_rngl_of_nat_0 in Hij.
}
destruct i. {
  exfalso.
  symmetry in Hij.
  now apply eq_rngl_of_nat_0 in Hij.
}
f_equal.
cbn in Hij.
apply rngl_add_cancel_l in Hij; [ | easy ].
now apply IHj.
Qed.

Theorem rngl_opp_inv :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  ∀ a, a ≠ 0%F → (- a⁻¹ = (- a)⁻¹)%F.
Proof.
intros Hop Hin H10 * Haz.
specialize (rngl_has_inv_has_inv_or_quot Hin) as Hin'.
move Hin' before Hin.
assert (Hoaz : (- a)%F ≠ 0%F). {
  intros H.
  apply (f_equal rngl_opp) in H.
  rewrite rngl_opp_involutive in H; [ | easy ].
  now rewrite rngl_opp_0 in H.
}
apply (rngl_mul_cancel_l Hin' (- a)%F); [ easy | ].
specialize (rngl_opt_mul_inv_r) as mul_inv_r.
rewrite Hin in mul_inv_r; cbn in mul_inv_r.
remember rngl_is_comm as ic eqn:Hic; symmetry in Hic.
rewrite rngl_mul_opp_opp; [ | easy ].
destruct ic. {
  symmetry.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_l; [ | easy | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_l; [ | easy | easy ].
  easy.
} {
  cbn in mul_inv_r.
  rewrite fold_rngl_div; [ | easy ].
  rewrite fold_rngl_div; [ | easy ].
  rewrite mul_inv_r; [ | easy ].
  now symmetry; apply mul_inv_r.
}
Qed.

Theorem rngl_div_mul_div :
  rngl_has_inv = true →
  ∀ x y z, y ≠ 0%F → ((x / y) * (y / z))%F = (x / z)%F.
Proof.
intros Hin * Hs.
specialize (rngl_mul_inv_l Hin) as mul_inv_l.
unfold rngl_has_inv in Hin.
unfold rngl_inv in mul_inv_l.
unfold rngl_div.
remember rngl_opt_inv_or_quot as a eqn:Ha; symmetry in Ha.
destruct a as [inv_quot| ]; [ | easy ].
destruct inv_quot as [inv| quot]; [ | easy ].
rewrite rngl_mul_assoc; f_equal.
rewrite <- rngl_mul_assoc.
rewrite mul_inv_l; [ | easy ].
apply rngl_mul_1_r.
Qed.

Theorem eq_rngl_div_1 :
  rngl_has_inv_or_quot = true →
   ∀ a b, b ≠ 0%F → a = b → (a / b = 1)%F.
Proof.
intros Hiv * Hbz Hab.
subst a.
now apply rngl_div_diag.
Qed.

Theorem rngl_mul_sub_distr_r :
  rngl_has_opp_or_sous = true →
  ∀ a b c, ((a - b) * c = a * c - b * c)%F.
Proof.
intros Hom *.
specialize rngl_mul_opp_l as H1.
specialize rngl_opt_mul_sub_distr_r as H2.
unfold rngl_has_opp, rngl_opp in H1.
unfold rngl_has_sous in H2.
generalize Hom; intros Hom'.
unfold rngl_has_opp_or_sous, bool_of_option in Hom.
remember rngl_opt_opp_or_sous as x eqn:Hop; symmetry in Hop.
destruct x as [opp_sous| ]; [ | easy ].
destruct opp_sous as [opp| sous]. {
  specialize (H1 eq_refl).
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_mul_add_distr_r.
  now rewrite H1.
}
remember rngl_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic. {
  specialize rngl_opt_mul_comm as rngl_mul_comm.
  rewrite Hic in rngl_mul_comm.
  rewrite rngl_mul_comm, rngl_mul_sub_distr_l; [ | easy ].
  now rewrite (rngl_mul_comm a), (rngl_mul_comm b).
}
apply H2.
Qed.

Theorem eq_rngl_add_same_0 :
  rngl_has_opp_or_sous = true →
  (rngl_is_integral || (rngl_has_inv_or_quot && rngl_has_eqb))%bool = true →
  rngl_has_1_neq_0 = true →
  rngl_characteristic = 0 →
  ∀ a,
  (a + a = 0)%F
  → a = 0%F.
Proof.
intros Hos Hii H10 Hch * Haa.
rewrite <- (rngl_mul_1_l a) in Haa.
rewrite <- rngl_mul_add_distr_r in Haa.
apply rngl_integral in Haa; [ | easy | easy ].
destruct Haa as [Haa| Haa]; [ | easy ].
specialize rngl_characteristic_prop as char_prop.
rewrite Hch in char_prop; cbn in char_prop.
specialize (char_prop 1); cbn in char_prop.
now rewrite rngl_add_0_r in char_prop.
Qed.

Definition in_charac_0_field :=
  rngl_is_comm = true ∧
  rngl_has_opp = true ∧
  rngl_has_inv = true ∧
  rngl_has_1_neq_0 = true ∧
  rngl_is_integral = true ∧
  rngl_has_eqb = true ∧
  rngl_characteristic = 0.

End a.

(* to be able to use tactic "ring" *)

Require Import Ring_theory.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {Hic : @rngl_is_comm T ro rp = true}.
Context {Hop : @rngl_has_opp T ro = true}.

Theorem rngl_Rsub_def : ∀ x y, (x - y = x + (- y))%F.
Proof.
intros.
unfold rngl_sub.
unfold rngl_has_opp in Hop.
remember rngl_opt_opp_or_sous as a eqn:Ha; symmetry in Ha.
destruct a as [opp_sous| ]; [ | easy ].
destruct opp_sous as [opp| sous]; [ | easy ].
unfold rngl_opp.
now rewrite Ha.
Qed.

Theorem rngl_Ropp_def : ∀ x : T, (x + - x)%F = 0%F.
Proof.
intros.
rewrite fold_rngl_sub; [ | easy ].
apply rngl_sub_diag.
now apply rngl_has_opp_has_opp_or_sous.
Qed.

Definition rngl_ring_theory : ring_theory _ _ _ _ _ _ _ :=
  {| Radd_0_l := rngl_add_0_l;
     Radd_comm := rngl_add_comm;
     Radd_assoc := rngl_add_assoc;
     Rmul_1_l := rngl_mul_1_l;
     Rmul_comm := rngl_mul_comm Hic;
     Rmul_assoc := rngl_mul_assoc;
     Rdistr_l := rngl_mul_add_distr_r;
     Rsub_def := rngl_Rsub_def;
     Ropp_def := rngl_Ropp_def |}.

End a.

(* code to be added to be able to use the Coq tactic "ring"

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {Hic : @rngl_is_comm T ro rp = true}.
Context {Hop : @rngl_has_opp T ro = true}.

Require Import Ring.
Add Ring rngl_ring : (@rngl_ring_theory T ro rp Hic Hop).

(* example *)

Example a2_b2 : ∀ a b, ((a + b) * (a - b) = a * a - b * b)%F.
Proof.
intros.
ring_simplify. (* just to see what happens *)
easy.
Qed.
*)

Arguments rngl_add_opp_l {T}%type {ro rp} Hro.
Arguments rngl_sub_diag {T}%type {ro rp} Hom a%F.
Arguments rngl_add_cancel_l {T}%type {ro rp} Hom (a b c)%F.
Arguments rngl_add_sub {T}%type {ro rp} Hom (a b)%F.
Arguments rngl_inv_mul_distr {T}%type {ro rp} Hom Hin Hdo a%F b%F.
Arguments rngl_integral {T}%type {ro rp}.
Arguments rngl_le_trans {T}%type {ro rp} Hor (a b c)%F.
Arguments rngl_mul_opp_opp {T}%type {ro rp} Hro.
Arguments rngl_mul_0_l {T}%type {ro rp} Hom a%F.
Arguments rngl_mul_opp_r {T}%type {ro rp} Hro.
Arguments rngl_mul_cancel_r {T}%type {ro rp} Hii (a b c)%F.
Arguments rngl_mul_0_r {T}%type {ro rp} Hom a%F.
Arguments rngl_opp_0 {T}%type {ro rp}.
Arguments rngl_opp_add_distr {T}%type {ro rp} Hop a%F b%F.
