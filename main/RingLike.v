(* Ring-like *)
(* Algebraic structures with two operations *)
(* Allows to define all kinds of semirings, rings, fields *)
(* Allows to define semirings, rings, fields, commutative or not,
   with two classes:
     ring_like_op, holding the operations, and
     ring_like_prop, holding their properties.
   In class ring_like_prop, we can set,
     to make a semiring:
        rngl_opt_opp_or_subt = Some (inr subt) where subt is a subtraction
        rngl_opt_opp_or_subt = None otherwise
        rngl_opt_inv_or_quot = Some (inr quot) where quot is a quotient
        rngl_opt_inv_or_quot = None otherwise
     to make a ring:
        rngl_opt_opp_or_subt = Some (inl opp), where opp is the opposite
        rngl_opt_inv_or_quot = Some (inr quot) where quot is a quotient
        rngl_opt_inv_or_quot = None otherwise
     to make a field:
        rngl_opt_opp_or_subt = Some (inl opp), where opp is the opposite
        rngl_opt_inv_or_quot = Some (inl inv), where inv is the inverse
   Multiplication can be commutative or not by setting rngl_mul_is_comm
   to true or false.
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
     - with specific subtraction (subt) or not
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
    rngl_add : T → T → T;
    rngl_mul : T → T → T;
    rngl_opt_one : option T;
    rngl_opt_opp_or_subt : option (sum (T → T) (T → T → T));
    rngl_opt_inv_or_quot : option (sum (T → T) (T → T → T));
    rngl_opt_eqb : option (T → T → bool);
    rngl_opt_le : option (T → T → Prop) }.

Declare Scope ring_like_scope.
Delimit Scope ring_like_scope with L.

Definition rngl_has_1 {T} {ro : ring_like_op T} :=
  bool_of_option rngl_opt_one.

Definition rngl_has_opp_or_subt {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_opp_or_subt.

Definition rngl_has_inv_or_quot {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_inv_or_quot.

Definition rngl_has_inv_and_1_or_quot {T} {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot with
  | Some (inl _) => rngl_has_1
  | Some (inr _) => true
  | None => false
  end.

Definition rngl_has_opp {T} {R : ring_like_op T} :=
  match rngl_opt_opp_or_subt with
  | Some (inl _) => true
  | _ => false
  end.

Definition rngl_has_subt {T} {R : ring_like_op T} :=
  match rngl_opt_opp_or_subt with
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
  match rngl_opt_opp_or_subt with
  | Some (inl rngl_opp) => rngl_opp a
  | _ => rngl_zero
  end.

Definition rngl_subt {T} {ro : ring_like_op T} a b :=
  match rngl_opt_opp_or_subt with
  | Some (inr rngl_subt) => rngl_subt a b
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
  if rngl_has_opp then rngl_add a (rngl_opp b)
  else if rngl_has_subt then rngl_subt a b
  else rngl_zero.

Definition rngl_div {T} {R : ring_like_op T} a b :=
  if rngl_has_inv then rngl_mul a (rngl_inv b)
  else if rngl_has_quot then rngl_quot a b
  else rngl_zero.

Theorem rngl_has_opp_or_subt_iff {T} {R : ring_like_op T} :
  rngl_has_opp_or_subt = true
  ↔ rngl_has_opp = true ∨ rngl_has_subt = true.
Proof.
unfold rngl_has_opp_or_subt, bool_of_option.
unfold rngl_has_opp, rngl_has_subt.
destruct rngl_opt_opp_or_subt as [opp_subt| ]. 2: {
  split; [ now left | ].
  now intros [|].
}
split; [ intros _ | easy ].
now destruct opp_subt; [ left | right ].
Qed.

Theorem rngl_has_inv_or_quot_iff {T} {R : ring_like_op T} :
  rngl_has_inv_or_quot = true
  ↔ rngl_has_inv = true ∨ rngl_has_quot = true.
Proof.
unfold rngl_has_inv_or_quot, bool_of_option.
unfold rngl_has_inv, rngl_has_quot.
destruct rngl_opt_inv_or_quot as [inv_quot| ]. 2: {
  split; [ now left | ].
  now intros [|].
}
split; [ intros _ | easy ].
now destruct inv_quot; [ left | right ].
Qed.

Theorem rngl_has_inv_and_1_or_quot_iff {T} {R : ring_like_op T} :
  rngl_has_inv_and_1_or_quot = true
  ↔ rngl_has_inv = true ∧ rngl_has_1 = true ∨ rngl_has_quot = true.
Proof.
progress unfold rngl_has_inv_and_1_or_quot, bool_of_option.
progress unfold rngl_has_inv, rngl_has_quot.
destruct rngl_opt_inv_or_quot as [inv_quot| ]. 2: {
  split; [ now left | ].
  now intros [|].
}
split; [ | now intros H; destruct H, inv_quot ].
now destruct inv_quot; [ left | right ].
Qed.

Theorem rngl_has_opp_has_opp_or_subt : ∀ {T} {ro : ring_like_op T},
  rngl_has_opp = true → rngl_has_opp_or_subt = true.
Proof.
intros * Hop.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

(* could be written with List.fold_right but this module is not
   supposed to include the module List (nor Nat) *)
Fixpoint rngl_eval_polyn {T} {ro : ring_like_op T} l (x : T) :=
  match l with
  | nil => rngl_zero
  | cons a l' => rngl_add (rngl_mul (rngl_eval_polyn l' x) x) a
  end.

Definition rngl_has_eqb {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_eqb.

Definition rngl_eqb {T} {R : ring_like_op T} a b :=
  match rngl_opt_eqb with
  | Some rngl_eqb => rngl_eqb a b
  | None => false
  end.

Definition rngl_le {T} {R : ring_like_op T} a b :=
  match rngl_opt_le with
  | Some rngl_le => rngl_le a b
  | None => False
  end.

Definition rngl_is_ordered {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_le.

Definition rngl_one {T} {ro : ring_like_op T} :=
  match rngl_opt_one with
  | Some a => a
  | None => rngl_zero
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
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c)%L (at level 70, b at next level) :
  ring_like_scope.

Notation "a =? b" := (rngl_eqb a b) (at level 70) : ring_like_scope.
Notation "a ≠? b" := (negb (rngl_eqb a b)) (at level 70) : ring_like_scope.

Notation "- 1" := (rngl_opp rngl_one) : ring_like_scope.

Inductive not_applicable := NA.

Fixpoint rngl_mul_nat {T} {ro : ring_like_op T} a n :=
  match n with
  | 0 => 0%L
  | S n' => (a + rngl_mul_nat a n')%L
  end.

Class ring_like_prop T {ro : ring_like_op T} :=
  { rngl_mul_is_comm : bool;
    rngl_has_dec_le : bool;
    rngl_is_integral : bool;
    rngl_is_alg_closed : bool;
    rngl_characteristic : nat;
    rngl_add_comm : ∀ a b : T, (a + b = b + a)%L;
    rngl_add_assoc : ∀ a b c : T, (a + (b + c) = (a + b) + c)%L;
    rngl_add_0_l : ∀ a : T, (0 + a)%L = a;
    rngl_mul_assoc : ∀ a b c : T, (a * (b * c) = (a * b) * c)%L;
    (* when has 1 *)
    rngl_opt_mul_1_l :
      if rngl_has_1 then ∀ a : T, (rngl_one * a)%L = a else not_applicable;
    rngl_mul_add_distr_l : ∀ a b c : T, (a * (b + c) = a * b + a * c)%L;
    (* when multiplication is commutative *)
    rngl_opt_mul_comm :
      if rngl_mul_is_comm then ∀ a b, (a * b = b * a)%L else not_applicable;
    (* when multiplication is not commutative *)
    rngl_opt_mul_1_r :
      if rngl_mul_is_comm then not_applicable
      else if rngl_has_1 then ∀ a, (a * 1 = a)%L
      else not_applicable;
    rngl_opt_mul_add_distr_r :
      if rngl_mul_is_comm then not_applicable else
       ∀ a b c, ((a + b) * c = a * c + b * c)%L;
    (* when has opposite *)
    rngl_opt_add_opp_l :
      if rngl_has_opp then ∀ a : T, (- a + a = 0)%L else not_applicable;
    (* when has subtraction (subt) *)
    rngl_opt_add_sub :
      if rngl_has_subt then ∀ a b, (a + b - b)%L = a
      else not_applicable;
    rngl_opt_sub_add_distr :
      if rngl_has_subt then ∀ a b c, (a - (b + c) = a - b - c)%L
      else not_applicable;
    (* when has inverse *)
    rngl_opt_mul_inv_l :
      if (rngl_has_inv && rngl_has_1)%bool then
        ∀ a : T, a ≠ 0%L → (a⁻¹ * a = 1)%L
      else not_applicable;
    rngl_opt_mul_inv_r :
      if (rngl_has_inv && rngl_has_1 && negb rngl_mul_is_comm)%bool then
        ∀ a : T, a ≠ 0%L → (a / a = 1)%L
      else not_applicable;
    (* when has division (quot) *)
    rngl_opt_mul_div :
      if rngl_has_quot then ∀ a b, b ≠ 0%L → (a * b / b)%L = a
      else not_applicable;
    rngl_opt_mul_quot_r :
      if (rngl_has_quot && negb rngl_mul_is_comm)%bool then
        ∀ a b, b ≠ 0%L → (b * a / b)%L = a
      else not_applicable;
    (* when equality is calculable *)
    rngl_opt_eqb_eq :
      if rngl_has_eqb then ∀ a b : T, (a =? b)%L = true ↔ a = b
      else not_applicable;
    (* when le comparison is decidable *)
    rngl_opt_le_dec :
      if rngl_has_dec_le then ∀ a b : T, ({a ≤ b} + {¬ a ≤ b})%L
      else not_applicable;
    (* when has_no_zero_divisors *)
    rngl_opt_integral :
      if rngl_is_integral then
        ∀ a b, (a * b = 0)%L → a = 0%L ∨ b = 0%L
      else not_applicable;
    (* when algebraically closed *)
    rngl_opt_alg_closed :
      if rngl_is_alg_closed then
        ∀ l, 0 < length l → ∃ x, rngl_eval_polyn l x = 0%L
      else not_applicable;
    (* characteristic *)
    rngl_characteristic_prop :
(*
https://en.wikipedia.org/wiki/Characteristic_(algebra)#Equivalent_characterizations
      ∀ k : nat,
      (∀ a : T, rngl_mul_nat a k = 0%L)
      → ∃ m, m ≠ 0 ∧ k = m * rngl_characteristic;
...
      ∀ n : nat,
      (∀ a : T, rngl_mul_nat a n = 0%L)
      → ∃ k, k ≠ 0 ∧ n = k * rngl_characteristic;
*)
      if rngl_has_1 then
        if Nat.eqb (rngl_characteristic) 0 then
          ∀ i, rngl_mul_nat 1%L (S i) ≠ 0%L
        else
          (∀ i, 0 < i < rngl_characteristic → rngl_mul_nat 1%L i ≠ 0%L) ∧
          rngl_mul_nat 1%L rngl_characteristic = 0%L
      else not_applicable;
(*
      ∀ k : nat,
      (∀ a : T, rngl_mul_nat a k = 0%L)
      → ∃ m, m ≠ 0 ∧ k = m * rngl_characteristic;
*)
    (* when ordered *)
    rngl_opt_le_refl :
      if rngl_is_ordered then ∀ a, (a ≤ a)%L else not_applicable;
    rngl_opt_le_antisymm :
      if rngl_is_ordered then ∀ a b, (a ≤ b → b ≤ a → a = b)%L
      else not_applicable;
    rngl_opt_le_trans :
      if rngl_is_ordered then ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%L
      else not_applicable;
    rngl_opt_add_le_compat :
      if rngl_is_ordered then ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%L
      else not_applicable;
    rngl_opt_mul_le_compat_nonneg :
      if (rngl_is_ordered && rngl_has_opp)%bool then
        ∀ a b c d, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_opt_mul_le_compat_nonpos :
      if (rngl_is_ordered && rngl_has_opp)%bool then
        ∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_opt_mul_le_compat :
      if (rngl_is_ordered && negb rngl_has_opp)%bool then
        ∀ a b c d, (a ≤ c)%L → (b ≤ d)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_opt_not_le :
      if rngl_is_ordered then
        ∀ a b, (¬ a ≤ b → a = b ∨ b ≤ a)%L
      else not_applicable }.

Fixpoint rngl_power {T} {ro : ring_like_op T} a n :=
  match n with
  | O => 1%L
  | S m => (a * rngl_power a m)%L
  end.

Definition rngl_squ {T} {ro : ring_like_op T} x := (x * x)%L.

Notation "a ^ b" := (rngl_power a b) : ring_like_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* theorems *)

Theorem rngl_mul_comm :
  rngl_mul_is_comm = true →
  ∀ a b, (a * b = b * a)%L.
Proof.
intros H1 *.
specialize rngl_opt_mul_comm as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_1_l :
  rngl_has_1 = true →
  ∀ a, (1 * a = a)%L.
Proof.
intros Hon *.
specialize rngl_opt_mul_1_l as H1.
rewrite Hon in H1.
apply H1.
Qed.

Theorem rngl_mul_1_r :
  rngl_has_1 = true →
  ∀ a, (a * 1 = a)%L.
Proof.
intros Hon *.
specialize rngl_opt_mul_1_l as H1.
specialize rngl_opt_mul_1_r as H2.
rewrite Hon in H1, H2.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
now rewrite rngl_mul_comm, rngl_mul_1_l.
Qed.

Theorem rngl_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%L.
Proof.
intros x y z; simpl.
specialize rngl_opt_mul_add_distr_r as rngl_mul_add_distr_r.
remember rngl_mul_is_comm as ic eqn:Hic.
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
  ∀ x, (- x + x = 0)%L.
Proof.
intros H1 *.
specialize rngl_opt_add_opp_l as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_inv_l :
  rngl_has_1 = true →
  rngl_has_inv = true →
  ∀ a : T, a ≠ 0%L → (a⁻¹ * a = 1)%L.
Proof.
intros Hon Hiv *.
specialize rngl_opt_mul_inv_l as H.
rewrite Hiv, Hon in H.
apply H.
Qed.

Theorem rngl_mul_inv_r :
  rngl_has_1 = true →
  rngl_has_inv = true →
  ∀ a : T, a ≠ 0%L → (a * a⁻¹ = 1)%L.
Proof.
intros Hon Hiv * Haz.
specialize rngl_opt_mul_inv_r as rngl_mul_inv_r.
unfold rngl_div in rngl_mul_inv_r.
rewrite Hiv in rngl_mul_inv_r; cbn in rngl_mul_inv_r.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic. {
  rewrite (rngl_mul_comm Hic).
  now apply (rngl_mul_inv_l Hon Hiv).
}
cbn in rngl_mul_inv_r.
rewrite Hon in rngl_mul_inv_r.
now apply rngl_mul_inv_r.
Qed.

Theorem rngl_eqb_eq :
  rngl_has_eqb = true →
  ∀ a b : T, (a =? b)%L = true ↔ a = b.
Proof.
intros Heqb *.
specialize rngl_opt_eqb_eq as H.
now rewrite Heqb in H.
Qed.

Theorem rngl_eqb_neq :
  rngl_has_eqb = true →
  ∀ a b : T, (a =? b)%L = false ↔ a ≠ b.
Proof.
intros Heqb *.
split; intros Hab. {
  intros H.
  apply (rngl_eqb_eq Heqb) in H.
  congruence.
} {
  remember (a =? b)%L as x eqn:Hx.
  symmetry in Hx.
  destruct x; [ | easy ].
  exfalso; apply Hab.
  now apply rngl_eqb_eq.
}
Qed.

Theorem rngl_neqb_neq :
  rngl_has_eqb = true →
  ∀ a b : T, (a ≠? b)%L = true ↔ a ≠ b.
Proof.
intros Heqb *.
split; intros Hab. {
  intros H.
  apply (rngl_eqb_eq Heqb) in H.
  now rewrite H in Hab.
} {
  apply (rngl_eqb_neq Heqb) in Hab.
  now rewrite Hab.
}
Qed.

Theorem rngl_eqb_refl :
  rngl_has_eqb = true →
  ∀ a, (a =? a)%L = true.
Proof.
intros Heqb *.
now apply (rngl_eqb_eq Heqb).
Qed.

Theorem rngl_eq_dec : rngl_has_eqb = true → ∀ a b : T, {a = b} + {a ≠ b}.
Proof.
intros Heq *.
remember (rngl_eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ now left; apply rngl_eqb_eq | now right; apply rngl_eqb_neq ].
Qed.

Theorem rngl_le_dec :
  rngl_has_dec_le = true →
  ∀ a b : T, ({a ≤ b} + {¬ a ≤ b})%L.
Proof.
intros H1 *.
specialize rngl_opt_le_dec as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_le_refl : rngl_is_ordered = true → ∀ a, (a ≤ a)%L.
Proof.
intros Hor *.
specialize rngl_opt_le_refl as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_trans :
  rngl_is_ordered = true →
   ∀ a b c : T, (a ≤ b)%L → (b ≤ c)%L → (a ≤ c)%L.
Proof.
intros H1 *.
specialize rngl_opt_le_trans as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_add_le_compat :
  rngl_is_ordered = true →
  ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%L.
Proof.
intros H1 *.
specialize rngl_opt_add_le_compat as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_nonneg :
  rngl_is_ordered = true →
  rngl_has_opp = true →
  ∀ a b c d, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros Hor Hop *.
specialize rngl_opt_mul_le_compat_nonneg as H.
rewrite Hor, Hop in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_nonpos :
  rngl_is_ordered = true →
  rngl_has_opp = true →
  ∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros Hor Hop *.
specialize rngl_opt_mul_le_compat_nonpos as H.
rewrite Hor, Hop in H.
apply H.
Qed.

Theorem rngl_not_le :
  rngl_is_ordered = true →
  ∀ a b, (¬ a ≤ b → a = b ∨ b ≤ a)%L.
Proof.
intros Hor *.
specialize rngl_opt_not_le as H.
rewrite Hor in H.
apply H.
Qed.

(* *)

Theorem rngl_has_subt_has_no_opp :
  rngl_has_subt = true
  → rngl_has_opp = false.
Proof.
intros * Hsu.
unfold rngl_has_subt in Hsu.
unfold rngl_has_opp.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem rngl_has_opp_has_no_subt :
  rngl_has_opp = true
  → rngl_has_subt = false.
Proof.
intros * Hop.
unfold rngl_has_opp in Hop.
unfold rngl_has_subt.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem rngl_has_quot_has_no_inv :
  rngl_has_quot = true
  → rngl_has_inv = false.
Proof.
intros * Hqu.
progress unfold rngl_has_quot in Hqu.
progress unfold rngl_has_inv.
destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
now destruct iq.
Qed.

Theorem rngl_has_inv_has_no_quot :
  rngl_has_inv = true
  → rngl_has_quot = false.
Proof.
intros * Hiv.
progress unfold rngl_has_inv in Hiv.
progress unfold rngl_has_quot.
destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
now destruct iq.
Qed.

(* *)

Theorem rngl_add_0_r : ∀ a, (a + 0 = a)%L.
Proof.
intros a; simpl.
rewrite rngl_add_comm.
apply rngl_add_0_l.
Qed.

Theorem rngl_1_neq_0_iff :
  rngl_has_1 = true → rngl_characteristic ≠ 1 ↔ (1 ≠ 0)%L.
Proof.
intros Hon.
specialize rngl_characteristic_prop as H1.
(**)
rewrite Hon in H1.
(**)
split. {
  intros Hc.
  remember (Nat.eqb rngl_characteristic 0) as cz eqn:Hcz; symmetry in Hcz.
  destruct cz. {
(**)
    specialize (H1 0); cbn in H1.
(*
specialize (H1 0 (λ _, eq_refl)) as H2.
destruct H2 as (k & Hkz & Hk).
...
*)
    now rewrite rngl_add_0_r in H1.
  }
  destruct H1 as (Hbef, H1).
  destruct rngl_characteristic as [| n]; [ easy | ].
  destruct n; [ easy | ].
  specialize (Hbef 1).
  cbn in Hbef.
  rewrite rngl_add_0_r in Hbef.
  apply Hbef.
  unfold lt.
  split; [ easy | ].
  do 2 apply le_n_S.
  destruct n; [ easy | apply le_0_n ].
} {
  intros H10 Hc.
  rewrite Hc in H1; cbn in H1.
  now rewrite rngl_add_0_r in H1.
}
Qed.

Theorem rngl_add_add_swap : ∀ n m p, (n + m + p = n + p + m)%L.
Proof.
intros n m p; simpl.
do 2 rewrite <- rngl_add_assoc.
assert (m + p = p + m)%L as H by apply rngl_add_comm.
rewrite H; reflexivity.
Qed.

Theorem rngl_mul_mul_swap :
  rngl_mul_is_comm = true →
  ∀ n m p, (n * m * p = n * p * m)%L.
Proof.
intros Hic n m p; simpl.
do 2 rewrite <- rngl_mul_assoc.
assert (m * p = p * m)%L as H by now apply rngl_mul_comm.
rewrite H; reflexivity.
Qed.

Theorem rngl_div_div_swap :
  rngl_mul_is_comm = true →
  rngl_has_inv = true →
  ∀ a b c,
  (a / b / c = a / c / b)%L.
Proof.
intros Hic Hin *.
unfold rngl_div.
now rewrite Hin, rngl_mul_mul_swap.
Qed.

Theorem rngl_add_compat_l : ∀ a b c,
  (a = b)%L → (c + a = c + b)%L.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_add_compat_r : ∀ a b c,
  (a = b)%L → (a + c = b + c)%L.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem fold_rngl_sub :
  rngl_has_opp = true →
  ∀ a b, (a + - b)%L = (a - b)%L.
Proof.
intros Hro *.
now unfold rngl_sub; rewrite Hro.
Qed.

Theorem fold_rngl_div :
  rngl_has_inv = true →
  ∀ a b, (a * b⁻¹)%L = (a / b)%L.
Proof.
intros Hin *.
now unfold rngl_div; rewrite Hin.
Qed.

Theorem rngl_sub_diag :
  rngl_has_opp_or_subt = true →
  ∀ a, (a - a = 0)%L.
Proof.
intros Hos *.
remember rngl_has_opp as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_add_comm.
  now apply rngl_add_opp_l.
}
remember rngl_has_subt as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 0%L a).
  now rewrite rngl_add_0_l in H1.
}
apply rngl_has_opp_or_subt_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem rngl_subt_diag :
  rngl_has_opp_or_subt = true →
  ∀ a, rngl_subt a a = 0%L.
Proof.
intros Hos *.
specialize (rngl_sub_diag Hos a) as H1.
unfold rngl_sub in H1.
remember rngl_has_opp as op eqn:Hop; symmetry in Hop.
destruct op. {
  unfold rngl_subt.
  unfold rngl_has_opp in Hop.
  destruct rngl_opt_opp_or_subt; [ | easy ].
  now destruct s.
}
remember rngl_has_subt as su eqn:Hsu; symmetry in Hsu.
destruct su; [ easy | ].
apply rngl_has_opp_or_subt_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem rngl_sub_add :
  rngl_has_opp = true →
  ∀ a b, (a - b + b = a)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite <- rngl_add_assoc.
rewrite (rngl_add_opp_l Hop).
apply rngl_add_0_r.
Qed.

Theorem rngl_div_diag :
  rngl_has_1 = true →
  rngl_has_inv_or_quot = true →
  ∀ a : T, a ≠ 0%L → (a / a = 1)%L.
Proof.
intros Hon Hiq * Haz.
remember rngl_has_inv as ai eqn:Hai; symmetry in Hai.
destruct ai. {
  remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
  destruct ic. {
    unfold rngl_div; rewrite Hai.
    rewrite rngl_mul_comm; [ | easy ].
    now apply rngl_mul_inv_l.
  }
  specialize rngl_opt_mul_inv_r as rngl_mul_inv_r.
  rewrite Hai, Hon, Hic in rngl_mul_inv_r; cbn in rngl_mul_inv_r.
  now apply rngl_mul_inv_r.
}
remember rngl_has_quot as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize rngl_opt_mul_div as rngl_mul_div.
  rewrite Hqu in rngl_mul_div.
  specialize (rngl_mul_div 1%L a Haz).
  now rewrite rngl_mul_1_l in rngl_mul_div.
}
apply rngl_has_inv_or_quot_iff in Hiq.
destruct Hiq; congruence.
Qed.

Theorem rngl_add_sub :
  rngl_has_opp_or_subt = true →
  ∀ a b, (a + b - b = a)%L.
Proof.
intros Hom *.
remember rngl_has_opp as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite <- rngl_add_assoc.
  rewrite (rngl_add_comm b).
  now rewrite rngl_add_opp_l, rngl_add_0_r.
}
remember rngl_has_subt as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  apply H1.
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_mul_div :
  rngl_has_inv_and_1_or_quot = true →
  ∀ a b : T, b ≠ 0%L → (a * b / b)%L = a.
Proof.
intros Hii a b Hbz.
remember rngl_has_inv as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  assert (Hiq : rngl_has_inv_or_quot = true). {
    now apply rngl_has_inv_or_quot_iff; left.
  }
  assert (Hon : rngl_has_1 = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [Hii| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  progress unfold rngl_div.
  rewrite Hiv.
  rewrite <- rngl_mul_assoc.
  rewrite fold_rngl_div; [ | easy ].
  rewrite rngl_div_diag; [ | easy | easy | easy ].
  now apply rngl_mul_1_r.
}
remember rngl_has_quot as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize rngl_opt_mul_div as mul_div.
  rewrite Hqu in mul_div.
  now apply mul_div.
}
apply rngl_has_inv_and_1_or_quot_iff in Hii.
destruct Hii as [(H1, H2)|]; congruence.
Qed.

Theorem rngl_mul_div_r :
  rngl_has_1 = true →
  rngl_mul_is_comm = true →
  rngl_has_inv = true →
  ∀ a b : T,
  b ≠ 0%L
  → (b * (a / b))%L = a.
Proof.
intros Hon Hco Hiv * Hbz.
rewrite (rngl_mul_comm Hco).
unfold "/"%L.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_l Hon Hiv _ Hbz).
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_add_cancel_l :
  rngl_has_opp_or_subt = true →
  ∀ a b c, (a + b = a + c)%L → (b = c)%L.
Proof.
intros Hom * Habc.
remember rngl_has_opp as op eqn:Hop.
symmetry in Hop.
destruct op. {
  apply (f_equal (λ x, rngl_sub x a)) in Habc.
  do 2 rewrite (rngl_add_comm a) in Habc.
  unfold rngl_sub in Habc.
  rewrite Hop in Habc.
  do 2 rewrite <- rngl_add_assoc in Habc.
  rewrite fold_rngl_sub in Habc; [ | easy ].
  rewrite rngl_sub_diag in Habc; [ | easy ].
  now do 2 rewrite rngl_add_0_r in Habc.
}
remember rngl_has_subt as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 c a) as H2.
  rewrite rngl_add_comm, <- Habc in H2.
  rewrite rngl_add_comm in H2.
  now rewrite H1 in H2.
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_mul_cancel_l :
  rngl_has_inv_and_1_or_quot = true →
  ∀ a b c, a ≠ 0%L
  → (a * b = a * c)%L
  → b = c.
Proof.
intros Hii * Haz Habc.
remember rngl_has_inv as iv eqn:Hiv.
symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  apply (f_equal (λ x, rngl_mul (a⁻¹)%L x)) in Habc.
  do 2 rewrite rngl_mul_assoc in Habc.
  rewrite rngl_mul_inv_l in Habc; [ | easy | easy | easy ].
  now do 2 rewrite (rngl_mul_1_l Hon) in Habc.
}
remember rngl_has_quot as qu eqn:Hqu.
symmetry in Hqu.
destruct qu. {
  apply (f_equal (λ x, rngl_div x a)) in Habc.
  remember rngl_mul_is_comm as ic eqn:Hic.
  symmetry in Hic.
  destruct ic. {
    do 2 rewrite (rngl_mul_comm Hic a) in Habc.
    specialize rngl_opt_mul_div as mul_div.
    rewrite Hqu in mul_div.
    rewrite mul_div in Habc; [ | easy ].
    rewrite mul_div in Habc; [ | easy ].
    easy.
  } {
    specialize rngl_opt_mul_quot_r as mul_quot_r.
    rewrite Hqu, Hic in mul_quot_r.
    cbn in mul_quot_r.
    rewrite mul_quot_r in Habc; [ | easy ].
    rewrite mul_quot_r in Habc; [ | easy ].
    easy.
  }
}
apply rngl_has_inv_and_1_or_quot_iff in Hii.
destruct Hii as [(H1, H2)| ]; congruence.
Qed.

Theorem rngl_add_sub_eq_l :
  rngl_has_opp_or_subt = true →
  ∀ a b c, (a + b = c → c - a = b)%L.
Proof.
intros Hom * Hab.
rewrite <- Hab.
rewrite rngl_add_comm.
now apply rngl_add_sub.
Qed.

Theorem rngl_add_sub_eq_r :
  rngl_has_opp_or_subt = true →
   ∀ a b c, (a + b = c → c - b = a)%L.
Proof.
intros Hom * Hab.
apply rngl_add_sub_eq_l; [ easy | ].
now rewrite rngl_add_comm.
Qed.

Theorem rngl_sub_compat_l : ∀ a b c,
  (a = b)%L → (a - c = b - c)%L.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_add_cancel_r :
  rngl_has_opp_or_subt = true →
  ∀ a b c, (a + c = b + c)%L → (a = b)%L.
Proof.
intros Hom * Habc.
eapply rngl_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rngl_add_sub in Habc.
Qed.

Theorem rngl_mul_0_r :
  rngl_has_opp_or_subt = true →
  ∀ a, (a * 0 = 0)%L.
Proof.
intros Hos *.
apply (rngl_add_cancel_r Hos _ _ (a * 1)%L).
rewrite <- rngl_mul_add_distr_l.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_mul_0_l :
  rngl_has_opp_or_subt = true →
  ∀ a, (0 * a = 0)%L.
Proof.
intros Hom a.
apply (rngl_add_cancel_r Hom _ _ (1 * a)%L).
rewrite <- rngl_mul_add_distr_r.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_characteristic_1 :
  rngl_has_1 = true →
  rngl_has_opp_or_subt = true →
  rngl_characteristic = 1 →
  ∀ x, x = 0%L.
Proof.
intros Hon Hos Hch *.
specialize (rngl_characteristic_prop) as H1.
rewrite Hon, Hch in H1; cbn in H1.
destruct H1 as (_, H1).
rewrite rngl_add_0_r in H1.
assert (H : (x * 0)%L = x). {
  rewrite <- H1.
  apply (rngl_mul_1_r Hon).
}
rewrite <- H.
apply (rngl_mul_0_r Hos).
Qed.

Theorem rngl_add_move_0_r :
  rngl_has_opp = true →
  ∀ a b, (a + b = 0)%L ↔ (a = - b)%L.
Proof.
intros Hro *.
split; intros H. {
  apply rngl_sub_compat_l with (c := b) in H.
  rewrite rngl_add_sub in H; [ | now apply rngl_has_opp_or_subt_iff; left ].
  unfold rngl_sub in H.
  rewrite Hro in H.
  now rewrite rngl_add_0_l in H.
} {
  rewrite H.
  now rewrite rngl_add_opp_l.
}
Qed.

Theorem rngl_mul_opp_r :
  rngl_has_opp = true →
  ∀ a b, (a * - b = - (a * b))%L.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_l a b (- b)%L) as H.
rewrite fold_rngl_sub in H; [ | easy ].
rewrite rngl_sub_diag in H; [ | now apply rngl_has_opp_or_subt_iff; left ].
rewrite rngl_mul_0_r in H; [ | now apply rngl_has_opp_or_subt_iff; left ].
symmetry in H.
rewrite rngl_add_comm in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_l :
  rngl_has_opp = true →
  ∀ a b c, (a * (b - c) = a * b - a * c)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite rngl_mul_add_distr_l.
now rewrite rngl_mul_opp_r.
Qed.

Theorem rngl_div_mul :
  rngl_has_1 = true →
  rngl_has_inv = true →
  ∀ a b, b ≠ 0%L → (a / b * b)%L = a.
Proof.
intros Hon Hiv * Hbz.
unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_l Hon Hiv _ Hbz).
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_div_0_l :
  rngl_has_opp_or_subt = true →
  rngl_has_inv_and_1_or_quot = true →
  ∀ a, a ≠ 0%L → (0 / a)%L = 0%L.
Proof.
intros Hos Hiv * Haz.
remember (0 / a)%L as x eqn:Hx.
replace 0%L with (0 * a)%L in Hx. 2: {
  now apply rngl_mul_0_l.
}
subst x.
apply (rngl_mul_div Hiv _ _ Haz).
Qed.

Theorem rngl_div_div_mul_mul :
  rngl_has_1 = true →
  rngl_mul_is_comm = true →
  rngl_has_inv = true →
  ∀ a b c d,
  b ≠ 0%L
  → d ≠ 0%L
  → (a / b = c / d)%L ↔ (a * d = b * c)%L.
Proof.
intros Hon Hic Hiv * Hbz Hdz.
split. {
  intros Habcd.
  apply (f_equal (λ x, rngl_mul x b)) in Habcd.
  rewrite rngl_div_mul in Habcd; [ | easy | easy | easy ].
  apply (f_equal (λ x, rngl_mul x d)) in Habcd.
  rewrite (rngl_mul_comm Hic _ b) in Habcd.
  rewrite <- rngl_mul_assoc in Habcd.
  now rewrite rngl_div_mul in Habcd.
} {
  intros Habcd.
  apply (f_equal (λ x, rngl_div x d)) in Habcd.
  assert (Hiq : rngl_has_inv_and_1_or_quot = true). {
    apply rngl_has_inv_and_1_or_quot_iff.
    now left; rewrite Hiv, Hon.
  }
  rewrite rngl_mul_div in Habcd; [ | easy | easy ].
  apply (f_equal (λ x, rngl_div x b)) in Habcd.
  rewrite rngl_div_div_swap in Habcd; [ | easy | easy ].
  rewrite rngl_mul_comm in Habcd; [ | easy ].
  rewrite rngl_mul_div in Habcd; [ easy | easy | easy ].
}
Qed.

Theorem rngl_eq_mul_0_l :
  rngl_has_opp_or_subt = true →
  (rngl_is_integral || rngl_has_inv_and_1_or_quot)%bool = true →
  ∀ a b, (a * b = 0)%L → b ≠ 0%L → a = 0%L.
Proof.
intros Hos Hii * Hab Hbz.
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral; [ now apply rngl_integral in Hab; destruct Hab | ].
cbn in Hii; clear rngl_integral.
remember rngl_has_inv as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [Hii| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  apply (f_equal (λ x, (x * b⁻¹)%L)) in Hab.
  rewrite <- rngl_mul_assoc in Hab.
  rewrite rngl_mul_inv_r in Hab; [ | easy | easy | easy ].
  rewrite (rngl_mul_1_r Hon) in Hab; rewrite Hab.
  apply (rngl_mul_0_l Hos).
}
remember rngl_has_quot as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize (rngl_mul_div Hii a b Hbz) as H1.
  rewrite Hab in H1.
  now rewrite rngl_div_0_l in H1.
}
apply rngl_has_inv_and_1_or_quot_iff in Hii.
rewrite Hiv, Hqu in Hii.
now destruct Hii.
Qed.

Theorem rngl_eq_mul_0_r :
  rngl_has_opp_or_subt = true →
  (rngl_is_integral || rngl_has_inv_and_1_or_quot)%bool = true →
  ∀ a b, (a * b = 0)%L → a ≠ 0%L → b = 0%L.
Proof.
intros Hos Hii * Hab Haz.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic. {
  rewrite (rngl_mul_comm Hic) in Hab.
  now apply (rngl_eq_mul_0_l Hos Hii) in Hab.
}
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral; [ now apply rngl_integral in Hab; destruct Hab | ].
cbn in Hii; clear rngl_integral.
remember rngl_has_inv as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [Hii| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  apply (f_equal (rngl_mul a⁻¹%L)) in Hab.
  rewrite rngl_mul_assoc, (rngl_mul_0_r Hos) in Hab.
  rewrite (rngl_mul_inv_l Hon Hiv) in Hab; [ | easy ].
  now rewrite rngl_mul_1_l in Hab.
}
remember rngl_has_quot as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize rngl_opt_mul_quot_r as rngl_mul_quot_r.
  rewrite Hqu, Hic in rngl_mul_quot_r; cbn in rngl_mul_quot_r.
  specialize (rngl_mul_quot_r b a Haz) as H1.
  rewrite Hab in H1.
  now rewrite (rngl_div_0_l Hos Hii) in H1.
}
apply rngl_has_inv_and_1_or_quot_iff in Hii.
rewrite Hiv, Hqu in Hii.
now destruct Hii.
Qed.

Theorem rngl_integral :
  rngl_has_opp_or_subt = true →
  (rngl_is_integral ||
   rngl_has_inv_and_1_or_quot && rngl_has_eqb)%bool = true →
  ∀ a b, (a * b = 0)%L → a = 0%L ∨ b = 0%L.
Proof.
intros Hmo Hdo * Hab.
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral; [ now apply rngl_integral | cbn in Hdo ].
remember rngl_has_inv as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 = true). {
    remember rngl_has_inv_and_1_or_quot as iq eqn:Hiq.
    symmetry in Hiq.
    destruct iq; [ cbn in Hdo | easy ].
    apply rngl_has_inv_and_1_or_quot_iff in Hiq.
    destruct Hiq as [| Hiq]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hiq.
    congruence.
  }
  remember rngl_has_eqb as de eqn:Hde; symmetry in Hde.
  destruct de; [ | now destruct rngl_has_inv_and_1_or_quot ].
  cbn; clear rngl_integral.
  assert (H : (a⁻¹ * a * b = a⁻¹ * 0)%L). {
    now rewrite <- rngl_mul_assoc, Hab.
  }
  remember (rngl_eqb a 0%L) as az eqn:Haz; symmetry in Haz.
  destruct az; [ now left; apply (rngl_eqb_eq Hde) | ].
  apply (rngl_eqb_neq Hde) in Haz; right.
  rewrite rngl_mul_inv_l in H; [ | easy | easy | easy ].
  rewrite (rngl_mul_1_l Hon) in H; rewrite H.
  apply (rngl_mul_0_r Hmo).
} {
  apply andb_prop in Hdo.
  destruct Hdo as (Hdi, Hde).
  specialize rngl_mul_div as H1.
  rewrite Hdi in H1.
  specialize (H1 eq_refl).
  remember (rngl_eqb b 0%L) as bz eqn:Hbz; symmetry in Hbz.
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
  ∀ a b : T, (a - b)%L = 0%L ↔ a = b.
Proof.
intros Hop *.
split. {
  intros Hab.
  apply (rngl_add_compat_r _ _ b) in Hab.
  unfold rngl_sub in Hab.
  rewrite Hop in Hab.
  rewrite <- rngl_add_assoc in Hab.
  rewrite rngl_add_opp_l in Hab; [ | easy ].
  now rewrite rngl_add_0_r, rngl_add_0_l in Hab.
} {
  intros Hab.
  rewrite Hab.
  apply rngl_sub_diag.
  now apply rngl_has_opp_or_subt_iff; left.
}
Qed.

Theorem rngl_mul_cancel_r :
  rngl_has_inv_and_1_or_quot = true →
  ∀ a b c, c ≠ 0%L
  → (a * c = b * c)%L
  → a = b.
Proof.
intros Hii * Hcz Hab.
assert (H : (a * c / c = b * c / c)%L) by now rewrite Hab.
rewrite rngl_mul_div in H; [ | easy | easy ].
rewrite rngl_mul_div in H; [ | easy | easy ].
easy.
Qed.

Theorem rngl_div_compat_l :
  rngl_has_inv = true →
  ∀ a b c, c ≠ 0%L → (a = b)%L → (a / c = b / c)%L.
Proof.
intros Hin a b c Hcz Hab.
now rewrite Hab.
Qed.

Theorem rngl_inv_if_then_else_distr : ∀ (c : bool) a b,
  ((if c then a else b)⁻¹ = if c then a⁻¹ else b⁻¹)%L.
Proof. now destruct c. Qed.

Theorem rngl_mul_if_then_else_distr : ∀ (x : bool) a b c d,
  ((if x then a else b) * (if x then c else d) = if x then a * c else b * d)%L.
Proof. now destruct x. Qed.

Theorem rngl_opp_0 : rngl_has_opp = true → (- 0 = 0)%L.
Proof.
intros Hro.
transitivity (0 + - 0)%L. {
  symmetry.
  apply rngl_add_0_l.
}
rewrite fold_rngl_sub; [ | easy ].
apply rngl_sub_diag.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Theorem rngl_subt_0_r :
  rngl_has_subt = true →
  ∀ a, rngl_subt a 0%L = a.
Proof.
intros Hsu *.
specialize rngl_opt_add_sub as H1.
rewrite Hsu in H1.
unfold rngl_sub in H1.
rewrite Hsu in H1.
unfold rngl_has_subt in Hsu.
unfold rngl_has_opp in H1.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt ]; [ easy | ].
specialize (H1 a 0%L).
now rewrite rngl_add_0_r in H1.
Qed.

Theorem rngl_mul_opp_l :
  rngl_has_opp = true →
  ∀ a b, (- a * b = - (a * b))%L.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_r (- a)%L a b) as H.
rewrite rngl_add_opp_l in H; [ | easy ].
rewrite rngl_mul_0_l in H. 2: {
  now apply rngl_has_opp_or_subt_iff; left.
}
symmetry in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_r :
  rngl_has_opp = true →
  ∀ a b c, ((a - b) * c = a * c - b * c)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite rngl_mul_add_distr_r.
now rewrite rngl_mul_opp_l.
Qed.

Theorem rngl_mul_0_sub_1_comm :
  rngl_has_1 = true →
  rngl_has_opp = true →
  ∀ a, ((0 - 1) * a = a * (0 - 1))%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_mul_0_l; [ | now apply rngl_has_opp_or_subt_iff; left ].
rewrite rngl_mul_0_r; [ | now apply rngl_has_opp_or_subt_iff; left ].
now rewrite rngl_mul_1_l, rngl_mul_1_r.
Qed.

(*
Theorem rngl_sub_0_l :
  rngl_has_opp = true
  → ∀ a, (0 - a = (0 - 1) * a)%L.
Proof.
intros Hos *.
rewrite (rngl_mul_sub_distr_r Hos).
rewrite (rngl_mul_0_l Hos).
now rewrite rngl_mul_1_l.
Qed.
*)

Theorem rngl_sub_0_r :
  rngl_has_opp_or_subt = true →
  ∀ a, (a - 0 = a)%L.
Proof.
intros Hom *.
remember rngl_has_opp as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_opp_0; [ | easy ].
  apply rngl_add_0_r.
}
remember rngl_has_subt as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 a 0%L) as H2.
  now rewrite rngl_add_0_r in H2.
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_opp_add_distr :
  rngl_has_opp = true →
  ∀ a b, (- (a + b) = - b - a)%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hop'.
rewrite Hop in Hop'.
apply rngl_add_cancel_l with (a := (a + b)%L); [ now apply Hop'; left | ].
rewrite (fold_rngl_sub Hop).
rewrite rngl_sub_diag; [ | now apply Hop'; left ].
unfold rngl_sub.
rewrite Hop.
rewrite rngl_add_assoc.
do 2 rewrite (fold_rngl_sub Hop).
rewrite rngl_add_sub; [ | now apply Hop'; left ].
symmetry.
apply rngl_sub_diag.
now apply Hop'; left.
Qed.

Theorem rngl_add_sub_simpl_l :
  rngl_has_opp_or_subt = true →
  ∀ a b c : T, (a + b - (a + c) = b - c)%L.
Proof.
intros Hom *.
remember rngl_has_opp as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_opp_add_distr; [ | easy ].
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap.
  rewrite (rngl_add_add_swap a).
  rewrite fold_rngl_sub; [ | easy ].
  rewrite fold_rngl_sub; [ | easy ].
  rewrite fold_rngl_sub; [ | easy ].
  rewrite rngl_sub_diag, rngl_add_0_l; [ easy | easy ].
}
remember rngl_has_subt as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_add_distr as H1.
  rewrite Hmo in H1.
  rewrite H1.
  rewrite rngl_add_comm.
  rewrite rngl_add_sub; [ easy | easy ].
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_inv_1 :
  rngl_has_1 = true →
  rngl_has_inv = true →
  rngl_characteristic ≠ 1 →
  (1⁻¹ = 1)%L.
Proof.
intros Hon Hiv H10.
assert (Hiq : rngl_has_inv_or_quot = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
specialize (rngl_div_diag Hon) as H.
unfold rngl_div in H.
rewrite Hiv in H.
transitivity (1 * 1⁻¹)%L. {
  symmetry.
  apply (rngl_mul_1_l Hon).
}
apply H; [ easy | ].
now apply rngl_1_neq_0_iff.
Qed.

Theorem rngl_div_1_l :
  rngl_has_1 = true →
  rngl_has_inv = true →
  ∀ a, (1 / a = a⁻¹)%L.
Proof.
intros Hon Hiv *.
unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_div_1_r :
  rngl_has_1 = true →
  rngl_has_inv_or_quot = true →
  rngl_characteristic ≠ 1 →
  ∀ a, (a / 1 = a)%L.
Proof.
intros Hon Hiq H10 *.
assert (Hid : rngl_has_inv_and_1_or_quot = true). {
  apply rngl_has_inv_or_quot_iff in Hiq.
  apply rngl_has_inv_and_1_or_quot_iff.
  now destruct Hiq; [ left | right ].
}
specialize (rngl_mul_div Hid a 1%L) as H1.
rewrite (rngl_mul_1_r Hon) in H1.
now apply H1, rngl_1_neq_0_iff.
Qed.

Theorem rngl_mul_move_1_r :
  rngl_has_1 = true →
  rngl_has_inv = true →
  ∀ a b : T, b ≠ 0%L → (a * b)%L = 1%L ↔ a = (b⁻¹)%L.
Proof.
intros Hon Hiv * Hbz.
split; intros H. {
  apply rngl_div_compat_l with (c := b) in H; [ | easy | easy ].
  unfold rngl_div in H.
  rewrite Hiv in H.
  rewrite <- rngl_mul_assoc in H.
  rewrite (fold_rngl_div Hiv) in H.
  rewrite (rngl_div_diag Hon) in H; [ | | easy ]. 2: {
    now apply rngl_has_inv_or_quot_iff; left.
  }
  now rewrite rngl_mul_1_r, rngl_mul_1_l in H.
} {
  rewrite H.
  specialize (rngl_mul_inv_l Hon Hiv) as H1.
  now apply H1.
}
Qed.

Theorem rngl_opp_involutive :
  rngl_has_opp = true →
  ∀ x, (- - x)%L = x.
Proof.
intros Hro *.
symmetry.
apply (rngl_add_move_0_r Hro).
rewrite (fold_rngl_sub Hro).
apply rngl_sub_diag.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Theorem Nat_eqb_eq : ∀ a b, Nat.eqb a b = true ↔ a = b.
Proof.
intros.
split; intros Hab. {
  revert b Hab.
  induction a; intros; [ now destruct b | ].
  destruct b; [ easy | cbn in Hab ].
  now f_equal; apply IHa.
} {
  now subst b; induction a.
}
Qed.

Theorem Nat_eqb_neq : ∀ a b, Nat.eqb a b = false ↔ a ≠ b.
Proof.
intros.
split; intros Hab. {
  intros H.
  apply Nat_eqb_eq in H.
  now rewrite Hab in H.
} {
  remember (Nat.eqb a b) as ab eqn:Heab; symmetry in Heab.
  destruct ab; [ | easy ].
  now apply Nat_eqb_eq in Heab.
}
Qed.

Theorem rngl_inv_neq_0 :
  rngl_has_1 = true →
  rngl_has_opp_or_subt = true →
  rngl_has_inv = true →
  ∀ a, a ≠ 0%L → (a⁻¹ ≠ 0)%L.
Proof.
intros Hon Hom Hiv * Haz H1.
remember (Nat.eqb rngl_characteristic 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat_eqb_eq in Hch.
  now specialize (rngl_characteristic_1 Hon Hom Hch a).
}
apply Nat_eqb_neq in Hch.
symmetry in H1.
apply (rngl_mul_move_1_r Hon Hiv _ _ Haz) in H1.
rewrite (rngl_mul_0_l Hom) in H1.
symmetry in H1.
now apply rngl_1_neq_0_iff in H1.
Qed.

Theorem rngl_inv_involutive :
  rngl_has_1 = true →
  rngl_has_opp_or_subt = true →
  rngl_has_inv = true →
  ∀ x, x ≠ 0%L → (x⁻¹⁻¹)%L = x.
Proof.
intros Hon Hos Hiv * Hxz.
remember (Nat.eqb rngl_characteristic 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat_eqb_eq in Hch.
  exfalso; apply Hxz.
  apply (rngl_characteristic_1 Hon Hos Hch).
}
apply Nat_eqb_neq in Hch.
symmetry.
specialize (rngl_div_diag Hon) as div_diag.
unfold rngl_div in div_diag.
rewrite Hiv in div_diag.
specialize (rngl_mul_move_1_r Hon Hiv) as H1.
apply H1. 2: {
  rewrite fold_rngl_div; [ | easy ].
  unfold rngl_div; rewrite Hiv.
  apply div_diag; [ | easy ].
  now apply rngl_has_inv_or_quot_iff; left.
}
now apply rngl_inv_neq_0.
Qed.

Theorem rngl_mul_opp_opp :
  rngl_has_opp = true →
  ∀ a b, (- a * - b = a * b)%L.
Proof.
intros Hro *.
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
now apply rngl_opp_involutive.
Qed.

Theorem rngl_squ_opp_1 :
  rngl_has_1 = true →
  rngl_has_opp = true →
  (-1 * -1)%L = 1%L.
Proof.
intros Hon Hop.
rewrite (rngl_mul_opp_opp Hop).
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_opp_inj :
  rngl_has_opp = true →
  ∀ a b, (- a = - b)%L → a = b.
Proof.
intros Hro * H.
rewrite <- (rngl_opp_involutive Hro a).
rewrite H.
now apply rngl_opp_involutive.
Qed.

Theorem rngl_inv_inj :
  rngl_has_1 = true →
  rngl_has_opp_or_subt = true →
  rngl_has_inv = true →
  ∀ a b, a ≠ 0%L → b ≠ 0%L →(a⁻¹ = b⁻¹)%L → a = b.
Proof.
intros Hon Hom Hiv * Haz Hbz H.
rewrite <- (rngl_inv_involutive Hon Hom Hiv a); [ | easy ].
rewrite H.
now apply rngl_inv_involutive.
Qed.

Theorem rngl_inv_mul_distr :
  rngl_has_1 = true →
  rngl_has_opp_or_subt = true →
  rngl_has_inv = true →
  ∀ a b, a ≠ 0%L → b ≠ 0%L →((a * b)⁻¹ = b⁻¹ * a⁻¹)%L.
Proof.
intros Hon Hom Hiv * Haz Hbz.
assert (Hiq : rngl_has_inv_or_quot = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
assert (Hid : rngl_has_inv_and_1_or_quot = true). {
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
specialize (rngl_div_diag Hon Hiq) as div_diag.
specialize (rngl_eq_mul_0_l Hom) as integral.
assert (H : (rngl_is_integral || rngl_has_inv_and_1_or_quot)%bool = true). {
  now rewrite Hid; destruct rngl_is_integral.
}
specialize (integral H); clear H.
unfold rngl_div in div_diag.
rewrite Hiv in div_diag.
assert (Habz : (a * b)%L ≠ 0%L). {
  intros H.
  now specialize (integral a b H Hbz).
}
apply (rngl_mul_cancel_l Hid (a * b)%L _ _ Habz).
rewrite (div_diag _ Habz).
rewrite rngl_mul_assoc.
rewrite <- (rngl_mul_assoc a).
rewrite (div_diag _ Hbz).
rewrite (rngl_mul_1_r Hon).
now symmetry; apply div_diag.
Qed.

Theorem rngl_eq_add_0 :
  rngl_is_ordered = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → a + b = 0 → a = 0 ∧ b = 0)%L.
Proof.
intros Hor * Haz Hbz Hab.
specialize rngl_opt_le_antisymm as rngl_le_antisymm.
rewrite Hor in rngl_le_antisymm.
split. {
  apply rngl_le_antisymm in Haz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%L as ab.
  rewrite <- (rngl_add_0_r a); subst ab.
  apply rngl_add_le_compat; [ easy | now apply rngl_le_refl | easy ].
} {
  apply rngl_le_antisymm in Hbz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%L as ab.
  rewrite <- (rngl_add_0_l b); subst ab.
  apply rngl_add_le_compat; [ easy | easy | now apply rngl_le_refl ].
}
Qed.

Theorem rngl_opp_sub_distr :
  rngl_has_opp = true →
  ∀ a b, (- (a - b) = b - a)%L.
Proof.
intros Hro *.
unfold rngl_sub at 1.
rewrite Hro.
rewrite rngl_opp_add_distr; [ | easy ].
now rewrite rngl_opp_involutive.
Qed.

Theorem rngl_sub_add_distr :
  rngl_has_opp_or_subt = true →
  ∀ a b c, (a - (b + c) = a - b - c)%L.
Proof.
intros Hos *.
remember rngl_has_opp as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite rngl_opp_add_distr; [ | easy ].
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  apply rngl_add_add_swap.
}
remember rngl_has_subt as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_add_distr as H1.
  now rewrite Hmo in H1.
}
apply rngl_has_opp_or_subt_iff in Hos.
now destruct Hos; congruence.
Qed.

Theorem rngl_sub_sub_distr :
  rngl_has_opp = true →
  ∀ a b c, (a - (b - c) = a - b + c)%L.
Proof.
intros Hop *.
unfold rngl_sub.
rewrite Hop.
rewrite rngl_opp_add_distr; [ | easy ].
rewrite rngl_opp_involutive; [ | easy ].
unfold rngl_sub; rewrite Hop.
rewrite rngl_add_assoc.
apply rngl_add_add_swap.
Qed.

Arguments rngl_mul_nat {T ro} a%L n%nat.

Theorem eq_rngl_of_nat_0 :
  rngl_has_1 = true →
  rngl_characteristic = 0 →
  ∀ i, rngl_mul_nat 1 i = 0%L → i = 0.
Proof.
intros Hon Hch * Hi.
induction i; [ easy | exfalso ].
cbn in Hi.
specialize rngl_characteristic_prop as rngl_char_prop.
rewrite Hon, Hch in rngl_char_prop.
now specialize (rngl_char_prop i) as H.
Qed.

Theorem rngl_of_nat_inj :
  rngl_has_1 = true →
  rngl_has_opp_or_subt = true →
  rngl_characteristic = 0 →
  ∀ i j,
  rngl_mul_nat 1 i = rngl_mul_nat 1 j
  → i = j.
Proof.
intros Hon Hom Hch * Hij.
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
  rngl_has_1 = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  ∀ a, a ≠ 0%L → (- a⁻¹ = (- a)⁻¹)%L.
Proof.
intros Hon Hop Hiv * Haz.
assert (Hos : rngl_has_opp_or_subt = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hid : rngl_has_inv_and_1_or_quot = true). {
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
remember (Nat.eqb rngl_characteristic 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat_eqb_eq in Hch.
  exfalso; apply Haz.
  apply (rngl_characteristic_1 Hon Hos Hch).
}
apply Nat_eqb_neq in Hch.
assert (Hoaz : (- a)%L ≠ 0%L). {
  intros H.
  apply (f_equal rngl_opp) in H.
  rewrite rngl_opp_involutive in H; [ | easy ].
  now rewrite rngl_opp_0 in H.
}
apply (rngl_mul_cancel_l Hid (- a)%L); [ easy | ].
specialize (rngl_opt_mul_inv_r) as H2.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
rewrite Hon, Hiv in H2; cbn in H2.
rewrite rngl_mul_opp_opp; [ | easy ].
destruct ic. {
  symmetry.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_l; [ | easy | easy | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_l; [ | easy | easy | easy ].
  easy.
} {
  cbn in H2.
  rewrite fold_rngl_div; [ | easy ].
  rewrite fold_rngl_div; [ | easy ].
  rewrite H2; [ | easy ].
  now rewrite H2.
}
Qed.

Theorem rngl_div_mul_div :
  rngl_has_1 = true →
  rngl_has_inv = true →
  ∀ x y z, y ≠ 0%L → ((x / y) * (y / z))%L = (x / z)%L.
Proof.
intros Hon Hiv * Hs.
unfold rngl_div; rewrite Hiv.
rewrite rngl_mul_assoc; f_equal.
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_inv_l; [ | easy| easy | easy ].
apply (rngl_mul_1_r Hon).
Qed.

Theorem eq_rngl_div_1 :
  rngl_has_1 = true →
  rngl_has_inv_or_quot = true →
   ∀ a b, b ≠ 0%L → a = b → (a / b = 1)%L.
Proof.
intros Hon Hiv * Hbz Hab.
subst a.
apply (rngl_div_diag Hon Hiv _ Hbz).
Qed.

Theorem eq_rngl_add_same_0 :
  rngl_has_1 = true →
  rngl_has_opp_or_subt = true →
  (rngl_is_integral || rngl_has_inv_or_quot)%bool = true →
  rngl_characteristic = 0 →
  ∀ a,
  (a + a = 0)%L
  → a = 0%L.
Proof.
intros Hon Hos Hii Hch * Haa.
rewrite <- (rngl_mul_1_l Hon a) in Haa.
rewrite <- rngl_mul_add_distr_r in Haa.
specialize rngl_characteristic_prop as char_prop.
rewrite Hon, Hch in char_prop; cbn in char_prop.
specialize (char_prop 1) as H1; cbn in H1.
rewrite rngl_add_0_r in H1.
apply (rngl_eq_mul_0_r Hos) in Haa; [ easy | | easy ].
destruct rngl_is_integral; [ easy | ].
cbn in Hii |-*.
apply rngl_has_inv_or_quot_iff in Hii.
apply rngl_has_inv_and_1_or_quot_iff.
now destruct Hii; [ left | right ].
Qed.

(* *)

Theorem rngl_pow_0_l :
  rngl_has_opp_or_subt = true →
  ∀ n, (0 ^ n)%L = match n with 0 => 1%L | _ => 0%L end.
Proof.
intros Hos *.
destruct n; [ easy | cbn ].
apply (rngl_mul_0_l Hos).
Qed.

Theorem rngl_pow_0_r : ∀ a, (a ^ 0 = 1)%L.
Proof. easy. Qed.

(* *)

Record in_charac_0_field :=
  { cf_has_1 : rngl_has_1 = true;
    cf_mul_is_comm : rngl_mul_is_comm = true;
    cf_has_opp : rngl_has_opp = true;
    cf_has_inv : rngl_has_inv = true;
    cf_is_integral : rngl_is_integral = true;
    cf_has_eqb : rngl_has_eqb = true;
    cf_characteristic : rngl_characteristic = 0 }.

End a.

(* to be able to use tactic "ring" *)

Require Import Ring_theory.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hic : @rngl_mul_is_comm T ro rp = true).
Context (Hop : @rngl_has_opp T ro = true).
Context (Hon : @rngl_has_1 T ro = true).

Theorem rngl_Ropp_def : ∀ x : T, (x + - x)%L = 0%L.
Proof.
intros.
rewrite (fold_rngl_sub Hop).
apply rngl_sub_diag.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Definition rngl_ring_theory
    : ring_theory 0%L 1%L rngl_add rngl_mul rngl_sub rngl_opp eq :=
  {| Radd_0_l := rngl_add_0_l;
     Radd_comm := rngl_add_comm;
     Radd_assoc := rngl_add_assoc;
     Rmul_1_l := rngl_mul_1_l Hon;
     Rmul_comm := rngl_mul_comm Hic;
     Rmul_assoc := rngl_mul_assoc;
     Rdistr_l := rngl_mul_add_distr_r;
     Rsub_def x y := eq_sym (fold_rngl_sub Hop x y);
     Ropp_def := rngl_Ropp_def |}.

End a.

(* code to be added to be able to use the Coq tactic "ring"

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {Hic : @rngl_mul_is_comm T ro rp = true}.
Context {Hop : @rngl_has_opp T ro = true}.

Require Import Ring.
Add Ring rngl_ring : (@rngl_ring_theory T ro rp Hic Hop).

(* example *)

Example a2_b2 : ∀ a b, ((a + b) * (a - b) = a * a - b * b)%L.
Proof.
intros.
ring_simplify. (* just to see what happens *)
easy.
Qed.
*)

Arguments rngl_add_sub {T}%type {ro rp} Hom (a b)%L.
Arguments rngl_characteristic_1 {T ro rp} Hon Hos Hch x%L.
Arguments rngl_le_trans {T}%type {ro rp} Hor (a b c)%L.
Arguments rngl_mul_nat {T ro} a%L n%nat.
Arguments rngl_mul_0_r {T}%type {ro rp} Hom a%L.
Arguments rngl_subt {T ro} (a b)%L.
