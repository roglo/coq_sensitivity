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
     - archimedean or not
     - with decidable equality or not
     - with commutative multiplication or not
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
Require Import Utf8 Arith.

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
    rngl_opt_eq_dec : option (∀ a b : T, {a = b} + {a ≠ b});
    rngl_opt_leb : option (T → T → bool) }.

Declare Scope ring_like_scope.
Delimit Scope ring_like_scope with L.

Definition rngl_has_1 T {ro : ring_like_op T} :=
  bool_of_option rngl_opt_one.

Definition rngl_has_opp_or_subt T {R : ring_like_op T} :=
  bool_of_option rngl_opt_opp_or_subt.

Definition rngl_has_inv_or_quot T {R : ring_like_op T} :=
  bool_of_option rngl_opt_inv_or_quot.

Definition rngl_has_inv_and_1_or_quot T {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot with
  | Some (inl _) => rngl_has_1 T
  | Some (inr _) => true
  | None => false
  end.

Definition rngl_has_opp T {R : ring_like_op T} :=
  match rngl_opt_opp_or_subt with
  | Some (inl _) => true
  | _ => false
  end.

Definition rngl_has_subt T {R : ring_like_op T} :=
  match rngl_opt_opp_or_subt with
  | Some (inr _) => true
  | _ => false
  end.

Definition rngl_has_inv T {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot with
  | Some (inl _) => true
  | _ => false
  end.

Definition rngl_has_quot T {R : ring_like_op T} :=
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

Definition rngl_sub {T} {ro : ring_like_op T} a b :=
  if rngl_has_opp T then rngl_add a (rngl_opp b)
  else if rngl_has_subt T then rngl_subt a b
  else rngl_zero.

Definition rngl_div {T} {R : ring_like_op T} a b :=
  if rngl_has_inv T then rngl_mul a (rngl_inv b)
  else if rngl_has_quot T then rngl_quot a b
  else rngl_zero.

Theorem rngl_has_opp_or_subt_iff {T} {R : ring_like_op T} :
  rngl_has_opp_or_subt T = true
  ↔ rngl_has_opp T = true ∨ rngl_has_subt T = true.
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
  rngl_has_inv_or_quot T = true
  ↔ rngl_has_inv T = true ∨ rngl_has_quot T = true.
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
  rngl_has_inv_and_1_or_quot T = true
  ↔ rngl_has_inv T = true ∧ rngl_has_1 T = true ∨ rngl_has_quot T = true.
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
  rngl_has_opp T = true → rngl_has_opp_or_subt T = true.
Proof.
intros * Hop.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Theorem rngl_has_inv_has_inv_or_quot : ∀ {T} {ro : ring_like_op T},
  rngl_has_inv T = true → rngl_has_inv_or_quot T = true.
Proof.
intros * Hop.
now apply rngl_has_inv_or_quot_iff; left.
Qed.

Theorem rngl_has_inv_and_1_has_inv_and_1_or_quot :
  ∀ {T} {ro : ring_like_op T},
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  rngl_has_inv_and_1_or_quot T = true.
Proof.
intros * Hon Hiv.
apply rngl_has_inv_and_1_or_quot_iff.
now rewrite Hiv, Hon; left.
Qed.

Definition rngl_has_eq_dec T {R : ring_like_op T} :=
  bool_of_option rngl_opt_eq_dec.

Definition rngl_eqb {T} {R : ring_like_op T} a b :=
  match rngl_opt_eq_dec with
  | Some rngl_eq_dec =>
      match rngl_eq_dec a b with left _ => true | right _ => false end
  | None => false
  end.

Definition rngl_le {T} {R : ring_like_op T} a b :=
  match rngl_opt_leb with
  | Some rngl_leb => rngl_leb a b = true
  | None => False
  end.

Definition rngl_lt {T} {R : ring_like_op T} a b :=
  match rngl_opt_leb with
  | Some rngl_leb => rngl_leb b a = false
  | None => False
  end.

Definition rngl_leb {T} {R : ring_like_op T} a b :=
  match rngl_opt_leb with
  | Some rngl_leb => rngl_leb a b
  | None => false
  end.

Definition rngl_ltb {T} {R : ring_like_op T} a b :=
  match rngl_opt_leb with
  | Some rngl_leb => negb (rngl_leb b a)
  | None => false
  end.

Definition rngl_is_ordered T {R : ring_like_op T} :=
  bool_of_option rngl_opt_leb.

Definition rngl_one {T} {ro : ring_like_op T} :=
  match rngl_opt_one with
  | Some a => a
  | None => rngl_zero
  end.

Definition rngl_squ {T} {ro : ring_like_op T} x := rngl_mul x x.

Notation "0" := rngl_zero : ring_like_scope.
Notation "1" := rngl_one : ring_like_scope.
Notation "2" := (rngl_add rngl_one rngl_one) : ring_like_scope.
Notation "a + b" := (rngl_add a b) : ring_like_scope.
Notation "a - b" := (rngl_sub a b) : ring_like_scope.
Notation "a * b" := (rngl_mul a b) : ring_like_scope.
Notation "a / b" := (rngl_div a b) : ring_like_scope.
Notation "a ≤ b" := (rngl_le a b) : ring_like_scope.
Notation "a < b" := (rngl_lt a b) : ring_like_scope.
Notation "- a" := (rngl_opp a) : ring_like_scope.
Notation "a '⁻¹'" := (rngl_inv a) (at level 1, format "a ⁻¹") :
  ring_like_scope.
Notation "a '²'" := (rngl_squ a) (at level 1, format "a ²") :
  ring_like_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c)%L (at level 70, b at next level) :
  ring_like_scope.
Notation "a < b < c" := (a < b ∧ b < c)%L (at level 70, b at next level) :
  ring_like_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c)%L (at level 70, b at next level) :
  ring_like_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c)%L (at level 70, b at next level) :
  ring_like_scope.
Notation "a ≤ b ≤ c ≤ d" :=
  (a ≤ b ∧ b ≤ c ∧ c ≤ d)%L (at level 70, b at next level, c at next level) :
  ring_like_scope.

Notation "a =? b" := (rngl_eqb a b) (at level 70) : ring_like_scope.
Notation "a ≠? b" := (negb (rngl_eqb a b)) (at level 70) : ring_like_scope.
Notation "a ≤? b" := (rngl_leb a b) (at level 70) : ring_like_scope.
Notation "a <? b" := (rngl_ltb a b) (at level 70) : ring_like_scope.

Notation "- 1" := (rngl_opp rngl_one) : ring_like_scope.

Inductive not_applicable := NA.

Definition rngl_eval_polyn {T} {ro : ring_like_op T} l (x : T) :=
  List.fold_right (λ a acc, (acc * x + a)%L) 0%L l.

Definition mul_nat {T} (zero : T) (add : T → T → T) a n :=
  List.fold_right add zero (List.repeat a n).

Definition rngl_mul_nat {T} {ro : ring_like_op T} :=
  mul_nat 0%L rngl_add.

Definition rngl_of_nat {T} {ro : ring_like_op T} a := rngl_mul_nat 1%L a.

Class ring_like_prop T {ro : ring_like_op T} :=
  { rngl_mul_is_comm : bool;
    rngl_is_integral_domain : bool;
    rngl_is_archimedean : bool;
    rngl_is_alg_closed : bool;
    rngl_characteristic : nat;
    rngl_add_comm : ∀ a b : T, (a + b = b + a)%L;
    rngl_add_assoc : ∀ a b c : T, (a + (b + c) = (a + b) + c)%L;
    rngl_add_0_l : ∀ a : T, (0 + a)%L = a;
    rngl_mul_assoc : ∀ a b c : T, (a * (b * c) = (a * b) * c)%L;
    (* when has 1 *)
    rngl_opt_mul_1_l :
      if rngl_has_1 T then ∀ a : T, (rngl_one * a)%L = a else not_applicable;
    rngl_mul_add_distr_l : ∀ a b c : T, (a * (b + c) = a * b + a * c)%L;
    (* when multiplication is commutative *)
    rngl_opt_mul_comm :
      if rngl_mul_is_comm then ∀ a b, (a * b = b * a)%L else not_applicable;
    (* when multiplication is not commutative *)
    rngl_opt_mul_1_r :
      if rngl_mul_is_comm then not_applicable
      else if rngl_has_1 T then ∀ a, (a * 1 = a)%L
      else not_applicable;
    rngl_opt_mul_add_distr_r :
      if rngl_mul_is_comm then not_applicable else
       ∀ a b c, ((a + b) * c = a * c + b * c)%L;
    (* when has opposite *)
    rngl_opt_add_opp_diag_l :
      if rngl_has_opp T then ∀ a : T, (- a + a = 0)%L else not_applicable;
    (* when has subtraction (subt) *)
    rngl_opt_add_sub :
      if rngl_has_subt T then ∀ a b, (a + b - b)%L = a
      else not_applicable;
    rngl_opt_sub_add_distr :
      if rngl_has_subt T then ∀ a b c, (a - (b + c) = a - b - c)%L
      else not_applicable;
    (* when has inverse *)
    rngl_opt_mul_inv_diag_l :
      if (rngl_has_inv T && rngl_has_1 T)%bool then
        ∀ a : T, a ≠ 0%L → (a⁻¹ * a = 1)%L
      else not_applicable;
    rngl_opt_mul_inv_diag_r :
      if (rngl_has_inv T && rngl_has_1 T && negb rngl_mul_is_comm)%bool then
        ∀ a : T, a ≠ 0%L → (a / a = 1)%L
      else not_applicable;
    (* when has division (quot) *)
    rngl_opt_mul_div :
      if rngl_has_quot T then ∀ a b, b ≠ 0%L → (a * b / b)%L = a
      else not_applicable;
    rngl_opt_mul_quot_r :
      if (rngl_has_quot T && negb rngl_mul_is_comm)%bool then
        ∀ a b, b ≠ 0%L → (b * a / b)%L = a
      else not_applicable;
    (* when le comparison is decidable *)
    rngl_opt_le_dec :
      if rngl_is_ordered T then ∀ a b : T, ({a ≤ b} + {¬ a ≤ b})%L
      else not_applicable;
    (* when has_no_zero_divisors *)
    rngl_opt_integral :
      if rngl_is_integral_domain then
        ∀ a b, (a * b = 0)%L → a = 0%L ∨ b = 0%L
      else not_applicable;
    (* when algebraically closed *)
    rngl_opt_alg_closed :
      if rngl_is_alg_closed then
        ∀ l : list T, 1 < length l → List.last l 0%L ≠ 0%L →
        ∃ x, rngl_eval_polyn l x = 0%L
      else not_applicable;
    (* characteristic *)
    rngl_opt_characteristic_prop :
      if rngl_has_1 T then
        if Nat.eqb (rngl_characteristic) 0 then
          ∀ i, rngl_of_nat (S i) ≠ 0%L
        else
          (∀ i, 0 < i < rngl_characteristic → rngl_of_nat i ≠ 0%L) ∧
          rngl_of_nat rngl_characteristic = 0%L
      else
        not_applicable;
    (* when ordered *)
    rngl_opt_le_refl :
      if rngl_is_ordered T then ∀ a, (a ≤ a)%L else not_applicable;
    rngl_opt_le_antisymm :
      if rngl_is_ordered T then ∀ a b, (a ≤ b → b ≤ a → a = b)%L
      else not_applicable;
    rngl_opt_le_trans :
      if rngl_is_ordered T then ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%L
      else not_applicable;
    rngl_opt_add_le_compat :
      if rngl_is_ordered T then ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%L
      else not_applicable;
    rngl_opt_mul_le_compat_nonneg :
      if (rngl_is_ordered T && rngl_has_opp T)%bool then
        ∀ a b c d, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_opt_mul_le_compat_nonpos :
      if (rngl_is_ordered T && rngl_has_opp T)%bool then
        ∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_opt_mul_le_compat :
      if (rngl_is_ordered T && negb (rngl_has_opp T))%bool then
        ∀ a b c d, (a ≤ c)%L → (b ≤ d)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_opt_not_le :
      if rngl_is_ordered T then
        ∀ a b, (¬ a ≤ b → a ≠ b ∧ b ≤ a)%L
      else not_applicable;
    (* archimedean *)
    rngl_opt_archimedean :
      if (rngl_is_archimedean && rngl_is_ordered T)%bool then
        ∀ a b, (0 < a)%L → ∃ n, (b < rngl_mul_nat a n)%L
      else not_applicable }.

Arguments rngl_mul_is_comm T {ro ring_like_prop}.
Arguments rngl_characteristic T {ro ring_like_prop}.
Arguments rngl_is_archimedean T {ro ring_like_prop}.
Arguments rngl_is_integral_domain T {ro ring_like_prop}.

Definition rngl_abs {T} {ro : ring_like_op T} a :=
  if (a ≤? 0)%L then (- a)%L else a.
Definition rngl_min {T} {ro : ring_like_op T} (a b : T) :=
  if (a ≤? b)%L then a else b.
Definition rngl_max {T} {ro : ring_like_op T} (a b : T) :=
  if (a ≤? b)%L then b else a.

Fixpoint rngl_power {T} {ro : ring_like_op T} a n :=
  match n with
  | O => 1%L
  | 1 => a (* to make it accesible even if 1 ∉ T *)
  | S m => (a * rngl_power a m)%L
  end.

Notation "a ^ b" := (rngl_power a b) : ring_like_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* theorems *)

Theorem rngl_int_dom_or_inv_1_quo_and_eq_dec :
  rngl_has_inv_and_1_or_quot T = true →
  rngl_has_eq_dec T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true.
Proof.
intros Hi1 Hed.
apply Bool.orb_true_iff; right.
now rewrite Hi1, Hed.
Qed.

Theorem rngl_int_dom_or_inv_1_quo :
  rngl_has_inv T = true →
  rngl_has_1 T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T)%bool = true.
Proof.
intros Hiv Hon.
apply Bool.orb_true_iff; right.
apply rngl_has_inv_and_1_or_quot_iff; left.
now rewrite Hiv, Hon.
Qed.

Theorem fold_rngl_squ : ∀ a : T, (a * a)%L = rngl_squ a.
Proof. easy. Qed.

Theorem rngl_mul_comm :
  rngl_mul_is_comm T = true →
  ∀ a b, (a * b = b * a)%L.
Proof.
intros H1 *.
specialize rngl_opt_mul_comm as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_1_l :
  rngl_has_1 T = true →
  ∀ a, (1 * a = a)%L.
Proof.
intros Hon *.
specialize rngl_opt_mul_1_l as H1.
rewrite Hon in H1.
apply H1.
Qed.

Theorem rngl_mul_1_r :
  rngl_has_1 T = true →
  ∀ a, (a * 1 = a)%L.
Proof.
intros Hon *.
specialize rngl_opt_mul_1_l as H1.
specialize rngl_opt_mul_1_r as H2.
rewrite Hon in H1, H2.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
now rewrite rngl_mul_comm, rngl_mul_1_l.
Qed.

Theorem rngl_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%L.
Proof.
intros x y z; simpl.
specialize rngl_opt_mul_add_distr_r as rngl_mul_add_distr_r.
remember (rngl_mul_is_comm T) as ic eqn:Hic.
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

Theorem rngl_add_opp_diag_l :
  rngl_has_opp T = true →
  ∀ x, (- x + x = 0)%L.
Proof.
intros H1 *.
specialize rngl_opt_add_opp_diag_l as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_inv_diag_l :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a : T, a ≠ 0%L → (a⁻¹ * a = 1)%L.
Proof.
intros Hon Hiv *.
specialize rngl_opt_mul_inv_diag_l as H.
rewrite Hiv, Hon in H.
apply H.
Qed.

Theorem rngl_mul_inv_diag_r :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a : T, a ≠ 0%L → (a * a⁻¹ = 1)%L.
Proof.
intros Hon Hiv * Haz.
specialize rngl_opt_mul_inv_diag_r as rngl_mul_inv_diag_r.
unfold rngl_div in rngl_mul_inv_diag_r.
rewrite Hiv in rngl_mul_inv_diag_r; cbn in rngl_mul_inv_diag_r.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic. {
  rewrite (rngl_mul_comm Hic).
  now apply (rngl_mul_inv_diag_l Hon Hiv).
}
cbn in rngl_mul_inv_diag_r.
rewrite Hon in rngl_mul_inv_diag_r.
now apply rngl_mul_inv_diag_r.
Qed.

Theorem rngl_eqb_eq :
  rngl_has_eq_dec T = true →
  ∀ a b : T, (a =? b)%L = true ↔ a = b.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
clear Hed.
now destruct (rngl_eq_dec a b).
Qed.

Theorem rngl_eqb_neq :
  rngl_has_eq_dec T = true →
  ∀ a b : T, (a =? b)%L = false ↔ a ≠ b.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
clear Hed.
now destruct (rngl_eq_dec a b).
Qed.

Theorem rngl_neqb_neq :
  rngl_has_eq_dec T = true →
  ∀ a b : T, (a ≠? b)%L = true ↔ a ≠ b.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
clear Hed.
now destruct (rngl_eq_dec a b).
Qed.

Theorem rngl_eqb_refl :
  rngl_has_eq_dec T = true →
  ∀ a, (a =? a)%L = true.
Proof.
intros Heqb *.
now apply (rngl_eqb_eq Heqb).
Qed.

Theorem rngl_eq_dec : rngl_has_eq_dec T = true → ∀ a b : T, {a = b} + {a ≠ b}.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
apply rngl_eq_dec.
Qed.

Theorem rngl_eqb_sym :
  rngl_has_eq_dec T = true →
  ∀ a b, ((a =? b) = (b =? a))%L.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
destruct (rngl_eq_dec a b). {
  subst b.
  now destruct (rngl_eq_dec a a).
} {
  destruct (rngl_eq_dec b a); [ now subst b | easy ].
}
Qed.

Theorem rngl_leb_le :
  ∀ a b, (a ≤? b)%L = true ↔ (a ≤ b)%L.
Proof.
intros.
progress unfold rngl_leb.
progress unfold rngl_le.
now split; intros Hab; destruct rngl_opt_leb.
Qed.

Theorem rngl_ltb_lt :
  ∀ a b, (a <? b)%L = true ↔ (a < b)%L.
Proof.
intros.
progress unfold rngl_ltb.
progress unfold rngl_lt.
split; intros Hab. {
  destruct rngl_opt_leb; [ | easy ].
  now apply Bool.negb_true_iff.
} {
  destruct rngl_opt_leb; [ | easy ].
  now apply Bool.negb_true_iff.
}
Qed.

Theorem rngl_leb_nle :
  ∀ a b, (a ≤? b)%L = false ↔ ¬ (a ≤ b)%L.
Proof.
intros.
progress unfold rngl_leb.
progress unfold rngl_le.
split; intros Hab. {
  apply Bool.not_true_iff_false in Hab.
  now destruct rngl_opt_leb.
} {
  apply Bool.not_true_iff_false.
  now destruct rngl_opt_leb.
}
Qed.

Theorem rngl_ltb_nlt :
  ∀ a b, (a <? b)%L = false ↔ ¬ (a < b)%L.
Proof.
intros.
progress unfold rngl_ltb.
progress unfold rngl_lt.
split; intros Hab. {
  destruct rngl_opt_leb; [ | easy ].
  apply Bool.negb_false_iff in Hab.
  apply Bool.not_false_iff_true.
  easy.
} {
  destruct rngl_opt_leb; [ | easy ].
  apply Bool.negb_false_iff.
  apply Bool.not_false_iff_true in Hab.
  easy.
}
Qed.

Theorem rngl_leb_refl :
  rngl_is_ordered T = true →
  ∀ a, (a ≤? a)%L = true.
Proof.
intros Hor *.
apply rngl_leb_le.
specialize rngl_opt_le_refl as H1.
rewrite Hor in H1.
apply H1.
Qed.

Theorem rngl_le_dec :
  rngl_is_ordered T = true →
  ∀ a b : T, ({a ≤ b} + {¬ a ≤ b})%L.
Proof.
intros Hor *.
specialize rngl_opt_le_dec as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_refl : rngl_is_ordered T = true → ∀ a, (a ≤ a)%L.
Proof.
intros Hor *.
specialize rngl_opt_le_refl as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_antisymm :
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ b → b ≤ a → a = b)%L.
Proof.
intros Hor *.
specialize rngl_opt_le_antisymm as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a ≤ b)%L → (b ≤ c)%L → (a ≤ c)%L.
Proof.
intros H1 *.
specialize rngl_opt_le_trans as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_lt_iff :
  rngl_is_ordered T = true → ∀ a b, (a < b ↔ a ≤ b ∧ a ≠ b)%L.
Proof.
intros * Hor a b.
progress unfold rngl_lt.
progress unfold rngl_le.
specialize rngl_opt_not_le as H1.
specialize (rngl_le_antisymm Hor) as H2.
rewrite Hor in H1.
progress unfold rngl_le in H1.
progress unfold rngl_le in H2.
destruct rngl_opt_leb as [rngl_leb| ]; [ | easy ].
split. {
  intros Hab.
  specialize (H1 b a) as H3.
  rewrite Hab in H3.
  assert (H : false ≠ true) by easy.
  specialize (H3 H); clear H.
  split; [ easy | ].
  destruct H3; congruence.
} {
  intros (H3, H4).
  remember (rngl_leb b a) as x eqn:Hx; symmetry in Hx.
  destruct x; [ | easy ].
  now specialize (H2 _ _ H3 Hx).
}
Qed.

Theorem rngl_lt_eq_cases :
  rngl_is_ordered T = true → ∀ a b : T, (a ≤ b)%L ↔ (a < b)%L ∨ a = b.
Proof.
intros Hor *.
progress unfold rngl_lt.
progress unfold rngl_le.
specialize rngl_opt_not_le as H1.
specialize (rngl_le_antisymm Hor) as H2.
specialize (rngl_le_refl Hor) as H3.
rewrite Hor in H1.
progress unfold rngl_le in H1.
progress unfold rngl_le in H2.
progress unfold rngl_le in H3.
destruct rngl_opt_leb as [rngl_leb| ]; [ | easy ].
split. {
  intros H.
  remember (rngl_leb b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba; [ | now left ].
  now specialize (H2 _ _ H Hba); right.
} {
  intros H.
  destruct H as [H4| H4]; [ now apply H1; rewrite H4 | ].
  subst b; apply H3.
}
Qed.

Theorem rngl_lt_dec :
  rngl_is_ordered T = true →
  ∀ a b : T, ({a < b} + {¬ a < b})%L.
Proof.
intros Hor *.
specialize rngl_opt_le_dec as H1.
rewrite Hor in H1.
destruct (H1 b a) as [H2| H2]; [ right | left ]. {
  intros H3.
  apply (rngl_lt_iff Hor) in H3.
  destruct H3 as (H3, H4).
  now apply (rngl_le_antisymm Hor) in H2.
} {
  specialize rngl_opt_not_le as H3.
  rewrite Hor in H3.
  apply H3 in H2.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  destruct H2 as (H2, _).
  now apply not_eq_sym.
}
Qed.

Theorem rngl_lt_irrefl :
  rngl_is_ordered T = true → ∀ a : T, ¬ (a < a)%L.
Proof.
intros * Hor a Ha.
unfold rngl_lt in Ha.
specialize (rngl_le_refl Hor a) as H1.
unfold rngl_le in H1.
destruct rngl_opt_leb; congruence.
Qed.

Theorem rngl_lt_asymm :
  rngl_is_ordered T = true →
  ∀ a b, (a < b → ¬ b < a)%L.
Proof.
intros Hor * Hab Hba.
apply (rngl_lt_iff Hor) in Hab, Hba.
destruct Hab as (Hab, Hnab).
destruct Hba as (Hba, _).
now apply Hnab, (rngl_le_antisymm Hor).
Qed.

Theorem rngl_add_le_compat :
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%L.
Proof.
intros H1 *.
specialize rngl_opt_add_le_compat as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor *.
specialize rngl_opt_mul_le_compat_nonneg as H.
rewrite Hor, Hop in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor *.
specialize rngl_opt_mul_le_compat_nonpos as H.
rewrite Hor, Hop in H.
apply H.
Qed.

Theorem rngl_mul_le_compat :
  rngl_has_opp T = false →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ c)%L → (b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor * Hac Hbd.
specialize rngl_opt_mul_le_compat as H.
rewrite Hor, Hop in H.
now apply H.
Qed.

Theorem rngl_not_le :
  rngl_is_ordered T = true →
  ∀ a b, (¬ a ≤ b → a ≠ b ∧ b ≤ a)%L.
Proof.
intros Hor *.
specialize rngl_opt_not_le as H.
rewrite Hor in H.
apply H.
Qed.

(* *)

Theorem rngl_has_subt_has_no_opp :
  rngl_has_subt T = true
  → rngl_has_opp T = false.
Proof.
intros * Hsu.
unfold rngl_has_subt in Hsu.
unfold rngl_has_opp.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem rngl_has_opp_has_no_subt :
  rngl_has_opp T = true
  → rngl_has_subt T = false.
Proof.
intros * Hop.
unfold rngl_has_opp in Hop.
unfold rngl_has_subt.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem rngl_has_quot_has_no_inv :
  rngl_has_quot T = true
  → rngl_has_inv T = false.
Proof.
intros * Hqu.
progress unfold rngl_has_quot in Hqu.
progress unfold rngl_has_inv.
destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
now destruct iq.
Qed.

Theorem rngl_has_inv_has_no_quot :
  rngl_has_inv T = true
  → rngl_has_quot T = false.
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

Theorem rngl_add_add_swap : ∀ n m p, (n + m + p = n + p + m)%L.
Proof.
intros n m p; simpl.
do 2 rewrite <- rngl_add_assoc.
assert (m + p = p + m)%L as H by apply rngl_add_comm.
rewrite H; reflexivity.
Qed.

Theorem rngl_add_add_add_swap :
  ∀ a b c d, ((a + b) + (c + d) = (a + c) + (b + d))%L.
Proof.
intros.
do 2 rewrite <- rngl_add_assoc.
f_equal.
rewrite rngl_add_comm, rngl_add_assoc.
apply rngl_add_add_swap.
Qed.

Theorem rngl_sub_sub_swap :
  rngl_has_opp T = true →
  ∀ a b c, (a - b - c = a - c - b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
apply rngl_add_add_swap.
Qed.

Theorem rngl_add_diag :
  rngl_has_1 T = true →
  ∀ a, (a + a = 2 * a)%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_r.
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_add_diag2 :
  rngl_has_1 T = true →
  ∀ a, (a + a = a * 2)%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_l.
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_mul_mul_swap :
  rngl_mul_is_comm T = true →
  ∀ a b c, (a * b * c = a * c * b)%L.
Proof.
intros Hic *.
do 2 rewrite <- rngl_mul_assoc.
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_div_div_swap :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a b c,
  (a / b / c = a / c / b)%L.
Proof.
intros Hic Hin *.
progress unfold rngl_div.
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

Theorem rngl_add_opp_l :
  rngl_has_opp T = true →
  ∀ a b, (- a + b)%L = (b - a)%L.
Proof.
intros Hop *.
rewrite rngl_add_comm.
progress unfold rngl_sub.
now rewrite Hop.
Qed.

Theorem rngl_add_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a + - b)%L = (a - b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
now rewrite Hop.
Qed.

Theorem rngl_mul_inv_r :
  rngl_has_inv T = true →
  ∀ a b, (a * b⁻¹)%L = (a / b)%L.
Proof.
intros Hin *.
now unfold rngl_div; rewrite Hin.
Qed.

Theorem rngl_sub_diag :
  rngl_has_opp_or_subt T = true →
  ∀ a, (a - a = 0)%L.
Proof.
intros Hos *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_add_comm.
  now apply rngl_add_opp_diag_l.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
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
  rngl_has_opp_or_subt T = true →
  ∀ a, rngl_subt a a = 0%L.
Proof.
intros Hos *.
specialize (rngl_sub_diag Hos a) as H1.
unfold rngl_sub in H1.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
destruct op. {
  unfold rngl_subt.
  unfold rngl_has_opp in Hop.
  destruct rngl_opt_opp_or_subt; [ | easy ].
  now destruct s.
}
remember (rngl_has_subt T) as su eqn:Hsu; symmetry in Hsu.
destruct su; [ easy | ].
apply rngl_has_opp_or_subt_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem rngl_sub_add :
  rngl_has_opp T = true →
  ∀ a b, (a - b + b = a)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite <- rngl_add_assoc.
rewrite (rngl_add_opp_diag_l Hop).
apply rngl_add_0_r.
Qed.

Theorem rngl_div_diag :
  rngl_has_1 T = true →
  rngl_has_inv_or_quot T = true →
  ∀ a : T, a ≠ 0%L → (a / a = 1)%L.
Proof.
intros Hon Hiq * Haz.
remember (rngl_has_inv T) as ai eqn:Hai; symmetry in Hai.
destruct ai. {
  remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
  destruct ic. {
    unfold rngl_div; rewrite Hai.
    rewrite rngl_mul_comm; [ | easy ].
    now apply rngl_mul_inv_diag_l.
  }
  specialize rngl_opt_mul_inv_diag_r as rngl_mul_inv_diag_r.
  rewrite Hai, Hon, Hic in rngl_mul_inv_diag_r; cbn in rngl_mul_inv_diag_r.
  now apply rngl_mul_inv_diag_r.
}
remember (rngl_has_quot T) as qu eqn:Hqu; symmetry in Hqu.
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
  rngl_has_opp_or_subt T = true →
  ∀ a b, (a + b - b = a)%L.
Proof.
intros Hom *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite <- rngl_add_assoc.
  rewrite (rngl_add_comm b).
  now rewrite rngl_add_opp_diag_l, rngl_add_0_r.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  apply H1.
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_add_sub_assoc :
  rngl_has_opp T = true →
  ∀ a b c, (a + (b - c) = a + b - c)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
apply rngl_add_assoc.
Qed.

Theorem rngl_add_sub_swap :
  rngl_has_opp T = true →
  ∀ a b c, (a + b - c = a - c + b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
apply rngl_add_add_swap.
Qed.

Theorem rngl_mul_div :
  rngl_has_inv_and_1_or_quot T = true →
  ∀ a b : T, b ≠ 0%L → (a * b / b)%L = a.
Proof.
intros Hii a b Hbz.
remember (rngl_has_inv T) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
  assert (Hon : rngl_has_1 T = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [Hii| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  progress unfold rngl_div.
  rewrite Hiv.
  rewrite <- rngl_mul_assoc.
  rewrite rngl_mul_inv_r; [ | easy ].
  rewrite rngl_div_diag; [ | easy | easy | easy ].
  now apply rngl_mul_1_r.
}
remember (rngl_has_quot T) as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize rngl_opt_mul_div as mul_div.
  rewrite Hqu in mul_div.
  now apply mul_div.
}
apply rngl_has_inv_and_1_or_quot_iff in Hii.
destruct Hii as [(H1, H2)|]; congruence.
Qed.

Theorem rngl_mul_div_r :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a b : T,
  b ≠ 0%L
  → (a / b * b)%L = a.
Proof.
intros Hon Hiv * Hbz.
progress unfold "/"%L.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hon Hiv _ Hbz).
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_mul_div_assoc :
  rngl_has_inv T = true →
  ∀ a b c, (a * (b / c) = a * b / c)%L.
Proof.
intros Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply rngl_mul_assoc.
Qed.

Theorem rngl_add_cancel_l :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a + b = a + c)%L → (b = c)%L.
Proof.
intros Hom * Habc.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  apply (f_equal (λ x, rngl_sub x a)) in Habc.
  do 2 rewrite (rngl_add_comm a) in Habc.
  unfold rngl_sub in Habc.
  rewrite Hop in Habc.
  do 2 rewrite <- rngl_add_assoc in Habc.
  rewrite rngl_add_opp_r in Habc; [ | easy ].
  rewrite rngl_sub_diag in Habc; [ | easy ].
  now do 2 rewrite rngl_add_0_r in Habc.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
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
  rngl_has_inv_and_1_or_quot T = true →
  ∀ a b c, a ≠ 0%L
  → (a * b = a * c)%L
  → b = c.
Proof.
intros Hii * Haz Habc.
remember (rngl_has_inv T) as iv eqn:Hiv.
symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 T = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  apply (f_equal (λ x, rngl_mul (a⁻¹)%L x)) in Habc.
  do 2 rewrite rngl_mul_assoc in Habc.
  rewrite rngl_mul_inv_diag_l in Habc; [ | easy | easy | easy ].
  now do 2 rewrite (rngl_mul_1_l Hon) in Habc.
}
remember (rngl_has_quot T) as qu eqn:Hqu.
symmetry in Hqu.
destruct qu. {
  apply (f_equal (λ x, rngl_div x a)) in Habc.
  remember (rngl_mul_is_comm T) as ic eqn:Hic.
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

Theorem rngl_add_move_l :
  rngl_has_opp T = true →
  ∀ a b c, (a + b)%L = c ↔ b = (c - a)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  subst c; symmetry.
  rewrite rngl_add_comm.
  apply (rngl_add_sub Hos).
} {
  subst b.
  rewrite rngl_add_comm.
  apply (rngl_sub_add Hop).
}
Qed.

Theorem rngl_add_move_r :
  rngl_has_opp T = true →
  ∀ a b c, (a + b)%L = c ↔ a = (c - b)%L.
Proof.
intros Hop *.
rewrite rngl_add_comm.
apply (rngl_add_move_l Hop).
Qed.

Theorem rngl_sub_move_l :
  rngl_has_opp T = true →
  ∀ a b c, (a - b)%L = c ↔ (- b)%L = (c - a)%L.
Proof.
intros Hop *.
split; intros Hb. {
  apply (rngl_add_move_l Hop).
  now rewrite rngl_add_opp_r.
} {
  apply (rngl_add_move_l Hop) in Hb.
  now rewrite (rngl_add_opp_r Hop) in Hb.
}
Qed.

Theorem rngl_sub_move_r :
  rngl_has_opp T = true →
  ∀ a b c, (a - b)%L = c ↔ a = (c + b)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Ha. {
  subst c; symmetry.
  apply (rngl_sub_add Hop).
} {
  subst a.
  apply (rngl_add_sub Hos).
}
Qed.

Theorem rngl_add_sub_eq_l :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a + b = c → c - a = b)%L.
Proof.
intros Hom * Hab.
rewrite <- Hab.
rewrite rngl_add_comm.
now apply rngl_add_sub.
Qed.

Theorem rngl_add_sub_eq_r :
  rngl_has_opp_or_subt T = true →
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
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a + c = b + c)%L → (a = b)%L.
Proof.
intros Hom * Habc.
apply rngl_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rngl_add_sub in Habc.
Qed.

Theorem rngl_mul_0_r :
  rngl_has_opp_or_subt T = true →
  ∀ a, (a * 0 = 0)%L.
Proof.
intros Hos *.
apply (rngl_add_cancel_r Hos _ _ (a * 1)%L).
rewrite <- rngl_mul_add_distr_l.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_mul_0_l :
  rngl_has_opp_or_subt T = true →
  ∀ a, (0 * a = 0)%L.
Proof.
intros Hom a.
apply (rngl_add_cancel_r Hom _ _ (1 * a)%L).
rewrite <- rngl_mul_add_distr_r.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_characteristic_0 :
  rngl_has_1 T = true →
  rngl_characteristic T = 0 →
  ∀ i : nat, rngl_of_nat (S i) ≠ 0%L.
Proof.
intros Hon Hcz.
specialize (rngl_opt_characteristic_prop) as H1.
now rewrite Hon, Hcz in H1.
Qed.

Theorem rngl_characteristic_non_0 :
  rngl_has_1 T = true →
  rngl_characteristic T ≠ 0 →
  (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L) ∧
  rngl_of_nat (rngl_characteristic T) = 0%L.
Proof.
intros Hon Hcz.
specialize (rngl_opt_characteristic_prop) as H1.
apply Nat.eqb_neq in Hcz.
now rewrite Hon, Hcz in H1.
Qed.

Theorem rngl_characteristic_1 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T = 1 →
  ∀ x, x = 0%L.
Proof.
intros Hon Hos Hch *.
specialize (rngl_opt_characteristic_prop) as H1.
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

Theorem rngl_1_neq_0_iff :
  rngl_has_1 T = true → rngl_characteristic T ≠ 1 ↔ (1 ≠ 0)%L.
Proof.
intros Hon.
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1.
split. {
  intros Hc.
  remember (Nat.eqb (rngl_characteristic T) 0) as cz eqn:Hcz; symmetry in Hcz.
  destruct cz. {
    specialize (H1 0); cbn in H1.
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

Theorem rngl_1_eq_0_iff :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T = 1 ↔ (1 = 0)%L.
Proof.
intros Hon Hos.
split. {
  intros Hc.
  specialize (rngl_characteristic_1 Hon Hos Hc) as H1.
  apply H1.
} {
  intros H10.
  destruct (Nat.eq_dec (rngl_characteristic T) 1) as [H1| H1]; [ easy | ].
  now apply (rngl_1_neq_0_iff Hon) in H1.
}
Qed.

Theorem rngl_add_move_0_r :
  rngl_has_opp T = true →
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
  now rewrite rngl_add_opp_diag_l.
}
Qed.

Theorem rngl_mul_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a * - b = - (a * b))%L.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_l a b (- b)%L) as H.
rewrite rngl_add_opp_r in H; [ | easy ].
rewrite rngl_sub_diag in H; [ | now apply rngl_has_opp_or_subt_iff; left ].
rewrite rngl_mul_0_r in H; [ | now apply rngl_has_opp_or_subt_iff; left ].
symmetry in H.
rewrite rngl_add_comm in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_l :
  rngl_has_opp T = true →
  ∀ a b c, (a * (b - c) = a * b - a * c)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite rngl_mul_add_distr_l.
now rewrite rngl_mul_opp_r.
Qed.

Theorem rngl_div_mul :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a b, b ≠ 0%L → (a / b * b)%L = a.
Proof.
intros Hon Hiv * Hbz.
unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hon Hiv _ Hbz).
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_div_mul_mul_div :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a b c, (a / b * c = a * c / b)%L.
Proof.
intros Hic Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_mul_swap Hic).
Qed.

Theorem rngl_div_0_l :
  rngl_has_opp_or_subt T = true →
  rngl_has_inv_and_1_or_quot T = true →
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
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
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
  specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
  rewrite rngl_mul_div in Habcd; [ | easy | easy ].
  apply (f_equal (λ x, rngl_div x b)) in Habcd.
  rewrite rngl_div_div_swap in Habcd; [ | easy | easy ].
  rewrite rngl_mul_comm in Habcd; [ | easy ].
  rewrite rngl_mul_div in Habcd; [ easy | easy | easy ].
}
Qed.

Theorem rngl_eq_mul_0_l :
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a * b = 0)%L → b ≠ 0%L → a = 0%L.
Proof.
intros Hos Hii * Hab Hbz.
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral_domain. {
  now apply rngl_integral in Hab; destruct Hab.
}
cbn in Hii; clear rngl_integral.
remember (rngl_has_inv T) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 T = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [Hii| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  apply (f_equal (λ x, (x * b⁻¹)%L)) in Hab.
  rewrite <- rngl_mul_assoc in Hab.
  rewrite rngl_mul_inv_diag_r in Hab; [ | easy | easy | easy ].
  rewrite (rngl_mul_1_r Hon) in Hab; rewrite Hab.
  apply (rngl_mul_0_l Hos).
}
remember (rngl_has_quot T) as qu eqn:Hqu; symmetry in Hqu.
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
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a * b = 0)%L → a ≠ 0%L → b = 0%L.
Proof.
intros Hos Hii * Hab Haz.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic. {
  rewrite (rngl_mul_comm Hic) in Hab.
  now apply (rngl_eq_mul_0_l Hos Hii) in Hab.
}
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral_domain. {
  now apply rngl_integral in Hab; destruct Hab.
}
cbn in Hii; clear rngl_integral.
remember (rngl_has_inv T) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 T = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [Hii| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  apply (f_equal (rngl_mul a⁻¹%L)) in Hab.
  rewrite rngl_mul_assoc, (rngl_mul_0_r Hos) in Hab.
  rewrite (rngl_mul_inv_diag_l Hon Hiv) in Hab; [ | easy ].
  now rewrite rngl_mul_1_l in Hab.
}
remember (rngl_has_quot T) as qu eqn:Hqu; symmetry in Hqu.
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
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b, (a * b = 0)%L → a = 0%L ∨ b = 0%L.
Proof.
intros Hmo Hdo * Hab.
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral_domain; [ now apply rngl_integral | cbn in Hdo ].
remember (rngl_has_inv T) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 T = true). {
    remember (rngl_has_inv_and_1_or_quot T) as iq eqn:Hiq.
    symmetry in Hiq.
    destruct iq; [ cbn in Hdo | easy ].
    apply rngl_has_inv_and_1_or_quot_iff in Hiq.
    destruct Hiq as [| Hiq]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hiq.
    congruence.
  }
  remember (rngl_has_eq_dec T) as de eqn:Hde; symmetry in Hde.
  destruct de; [ | now destruct rngl_has_inv_and_1_or_quot ].
  cbn; clear rngl_integral.
  assert (H : (a⁻¹ * a * b = a⁻¹ * 0)%L). {
    now rewrite <- rngl_mul_assoc, Hab.
  }
  remember (rngl_eqb a 0%L) as az eqn:Haz; symmetry in Haz.
  destruct az; [ now left; apply (rngl_eqb_eq Hde) | ].
  apply (rngl_eqb_neq Hde) in Haz; right.
  rewrite rngl_mul_inv_diag_l in H; [ | easy | easy | easy ].
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
  rngl_has_opp T = true →
  ∀ a b : T, (a - b)%L = 0%L ↔ a = b.
Proof.
intros Hop *.
split. {
  intros Hab.
  apply (rngl_add_compat_r _ _ b) in Hab.
  unfold rngl_sub in Hab.
  rewrite Hop in Hab.
  rewrite <- rngl_add_assoc in Hab.
  rewrite rngl_add_opp_diag_l in Hab; [ | easy ].
  now rewrite rngl_add_0_r, rngl_add_0_l in Hab.
} {
  intros Hab.
  rewrite Hab.
  apply rngl_sub_diag.
  now apply rngl_has_opp_or_subt_iff; left.
}
Qed.

Theorem rngl_mul_cancel_r :
  rngl_has_inv_and_1_or_quot T = true →
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
  rngl_has_inv T = true →
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

Theorem rngl_opp_0 : rngl_has_opp T = true → (- 0 = 0)%L.
Proof.
intros Hro.
transitivity (0 + - 0)%L. {
  symmetry.
  apply rngl_add_0_l.
}
rewrite rngl_add_opp_r; [ | easy ].
apply rngl_sub_diag.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Theorem rngl_subt_0_r :
  rngl_has_subt T = true →
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
  rngl_has_opp T = true →
  ∀ a b, (- a * b = - (a * b))%L.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_r (- a)%L a b) as H.
rewrite rngl_add_opp_diag_l in H; [ | easy ].
rewrite rngl_mul_0_l in H. 2: {
  now apply rngl_has_opp_or_subt_iff; left.
}
symmetry in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_r :
  rngl_has_opp T = true →
  ∀ a b c, ((a - b) * c = a * c - b * c)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite rngl_mul_add_distr_r.
now rewrite rngl_mul_opp_l.
Qed.

Theorem rngl_div_add_distr_r:
  rngl_has_inv T = true →
  ∀ a b c, ((a + b) / c)%L = (a / c + b / c)%L.
Proof.
intros Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply rngl_mul_add_distr_r.
Qed.

Theorem rngl_div_sub_distr_r:
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a b c, ((a - b) / c)%L = (a / c - b / c)%L.
Proof.
intros Hop Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_sub_distr_r Hop).
Qed.

Theorem rngl_mul_0_sub_1_comm :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a, ((0 - 1) * a = a * (0 - 1))%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_mul_0_l; [ | now apply rngl_has_opp_or_subt_iff; left ].
rewrite rngl_mul_0_r; [ | now apply rngl_has_opp_or_subt_iff; left ].
now rewrite rngl_mul_1_l, rngl_mul_1_r.
Qed.

Theorem rngl_sub_0_l :
  rngl_has_opp T = true →
  ∀ a, (0 - a = - a)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
apply rngl_add_0_l.
Qed.

Theorem rngl_sub_0_r :
  rngl_has_opp_or_subt T = true →
  ∀ a, (a - 0 = a)%L.
Proof.
intros Hom *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_opp_0; [ | easy ].
  apply rngl_add_0_r.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
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
  rngl_has_opp T = true →
  ∀ a b, (- (a + b) = - b - a)%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hop'.
rewrite Hop in Hop'.
apply rngl_add_cancel_l with (a := (a + b)%L); [ now apply Hop'; left | ].
rewrite (rngl_add_opp_r Hop).
rewrite rngl_sub_diag; [ | now apply Hop'; left ].
unfold rngl_sub.
rewrite Hop.
rewrite rngl_add_assoc.
do 2 rewrite (rngl_add_opp_r Hop).
rewrite rngl_add_sub; [ | now apply Hop'; left ].
symmetry.
apply rngl_sub_diag.
now apply Hop'; left.
Qed.

Theorem rngl_add_sub_simpl_l :
  rngl_has_opp_or_subt T = true →
  ∀ a b c : T, (a + b - (a + c) = b - c)%L.
Proof.
intros Hom *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_opp_add_distr; [ | easy ].
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap.
  rewrite (rngl_add_add_swap a).
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_sub_diag, rngl_add_0_l; [ easy | easy ].
}
remember (rngl_has_subt T) as mo eqn:Hmo.
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
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 1 →
  (1⁻¹ = 1)%L.
Proof.
intros Hon Hiv H10.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
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
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a, (1 / a = a⁻¹)%L.
Proof.
intros Hon Hiv *.
unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_div_1_r :
  rngl_has_1 T = true →
  rngl_has_inv_or_quot T = true →
  rngl_characteristic T ≠ 1 →
  ∀ a, (a / 1 = a)%L.
Proof.
intros Hon Hiq H10 *.
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_or_quot_iff in Hiq.
  apply rngl_has_inv_and_1_or_quot_iff.
  now destruct Hiq; [ left | right ].
}
specialize (rngl_mul_div Hi1 a 1%L) as H1.
rewrite (rngl_mul_1_r Hon) in H1.
now apply H1, rngl_1_neq_0_iff.
Qed.

Theorem rngl_mul_move_1_r :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a b : T, b ≠ 0%L → (a * b)%L = 1%L ↔ a = (b⁻¹)%L.
Proof.
intros Hon Hiv * Hbz.
split; intros H. {
  apply rngl_div_compat_l with (c := b) in H; [ | easy | easy ].
  unfold rngl_div in H.
  rewrite Hiv in H.
  rewrite <- rngl_mul_assoc in H.
  rewrite (rngl_mul_inv_r Hiv) in H.
  rewrite (rngl_div_diag Hon) in H; [ | | easy ]. 2: {
    now apply rngl_has_inv_or_quot_iff; left.
  }
  now rewrite rngl_mul_1_r, rngl_mul_1_l in H.
} {
  rewrite H.
  specialize (rngl_mul_inv_diag_l Hon Hiv) as H1.
  now apply H1.
}
Qed.

Theorem rngl_opp_involutive :
  rngl_has_opp T = true →
  ∀ x, (- - x)%L = x.
Proof.
intros Hro *.
symmetry.
apply (rngl_add_move_0_r Hro).
rewrite (rngl_add_opp_r Hro).
apply rngl_sub_diag.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Theorem rngl_sub_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a - - b = a + b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
f_equal.
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_inv_neq_0 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a, a ≠ 0%L → (a⁻¹ ≠ 0)%L.
Proof.
intros Hon Hom Hiv * Haz H1.
remember (Nat.eqb (rngl_characteristic T) 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat.eqb_eq in Hch.
  now specialize (rngl_characteristic_1 Hon Hom Hch a).
}
apply Nat.eqb_neq in Hch.
symmetry in H1.
apply (rngl_mul_move_1_r Hon Hiv _ _ Haz) in H1.
rewrite (rngl_mul_0_l Hom) in H1.
symmetry in H1.
now apply rngl_1_neq_0_iff in H1.
Qed.

Theorem rngl_inv_involutive :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ x, x ≠ 0%L → (x⁻¹⁻¹)%L = x.
Proof.
intros Hon Hos Hiv * Hxz.
remember (Nat.eqb (rngl_characteristic T) 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat.eqb_eq in Hch.
  exfalso; apply Hxz.
  apply (rngl_characteristic_1 Hon Hos Hch).
}
apply Nat.eqb_neq in Hch.
symmetry.
specialize (rngl_div_diag Hon) as div_diag.
unfold rngl_div in div_diag.
rewrite Hiv in div_diag.
specialize (rngl_mul_move_1_r Hon Hiv) as H1.
apply H1. 2: {
  rewrite rngl_mul_inv_r; [ | easy ].
  unfold rngl_div; rewrite Hiv.
  apply div_diag; [ | easy ].
  now apply rngl_has_inv_or_quot_iff; left.
}
now apply rngl_inv_neq_0.
Qed.

Theorem rngl_mul_opp_opp :
  rngl_has_opp T = true →
  ∀ a b, (- a * - b = a * b)%L.
Proof.
intros Hro *.
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
now apply rngl_opp_involutive.
Qed.

Theorem rngl_squ_opp_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  (-1 * -1)%L = 1%L.
Proof.
intros Hon Hop.
rewrite (rngl_mul_opp_opp Hop).
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_opp_inj :
  rngl_has_opp T = true →
  ∀ a b, (- a = - b)%L → a = b.
Proof.
intros Hro * H.
rewrite <- (rngl_opp_involutive Hro a).
rewrite H.
now apply rngl_opp_involutive.
Qed.

Theorem rngl_inv_inj :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a b, a ≠ 0%L → b ≠ 0%L →(a⁻¹ = b⁻¹)%L → a = b.
Proof.
intros Hon Hom Hiv * Haz Hbz H.
rewrite <- (rngl_inv_involutive Hon Hom Hiv a); [ | easy ].
rewrite H.
now apply rngl_inv_involutive.
Qed.

Theorem rngl_inv_mul_distr :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a b, a ≠ 0%L → b ≠ 0%L →((a * b)⁻¹ = b⁻¹ * a⁻¹)%L.
Proof.
intros Hon Hom Hiv * Haz Hbz.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
assert (Hid : rngl_has_inv_and_1_or_quot T = true). {
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
specialize (rngl_div_diag Hon Hiq) as div_diag.
specialize (rngl_eq_mul_0_l Hom) as integral.
assert
  (H :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  now rewrite Hid; destruct rngl_is_integral_domain.
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

Theorem rngl_div_div :
  rngl_has_opp_or_subt T = true →
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a b c, (b ≠ 0 → c ≠ 0 → a / b / c = a / (c * b))%L.
Proof.
intros Hos Hon Hiv * Hbz Hzc.
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc; f_equal; symmetry.
now apply (rngl_inv_mul_distr Hon Hos Hiv).
Qed.

Theorem rngl_eq_add_0 :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → a + b = 0 → a = 0 ∧ b = 0)%L.
Proof.
intros Hor * Haz Hbz Hab.
split. {
  apply (rngl_le_antisymm Hor) in Haz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%L as ab.
  rewrite <- (rngl_add_0_r a); subst ab.
  apply rngl_add_le_compat; [ easy | now apply rngl_le_refl | easy ].
} {
  apply (rngl_le_antisymm Hor) in Hbz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%L as ab.
  rewrite <- (rngl_add_0_l b); subst ab.
  apply rngl_add_le_compat; [ easy | easy | now apply rngl_le_refl ].
}
Qed.

Theorem rngl_opp_sub_distr :
  rngl_has_opp T = true →
  ∀ a b, (- (a - b) = b - a)%L.
Proof.
intros Hro *.
unfold rngl_sub at 1.
rewrite Hro.
rewrite rngl_opp_add_distr; [ | easy ].
now rewrite rngl_opp_involutive.
Qed.

Theorem rngl_sub_add_distr :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a - (b + c) = a - b - c)%L.
Proof.
intros Hos *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite rngl_opp_add_distr; [ | easy ].
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  apply rngl_add_add_swap.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_add_distr as H1.
  now rewrite Hmo in H1.
}
apply rngl_has_opp_or_subt_iff in Hos.
now destruct Hos; congruence.
Qed.

Theorem rngl_sub_sub_distr :
  rngl_has_opp T = true →
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

Theorem rngl_le_0_sub :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 ≤ b - a ↔ a ≤ b)%L.
Proof.
intros * Hop Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
specialize (rngl_add_le_compat Hor) as H1.
split; intros Hab. {
  specialize (H1 0%L (b - a)%L a a Hab (rngl_le_refl Hor _)).
  rewrite <- (rngl_sub_sub_distr Hop) in H1.
  rewrite (rngl_sub_diag Hos) in H1.
  now rewrite rngl_add_0_l, (rngl_sub_0_r Hos) in H1.
} {
  specialize (H1 a b (- a)%L (- a)%L Hab (rngl_le_refl Hor _)).
  do 2 rewrite (rngl_add_opp_r Hop) in H1.
  now rewrite (rngl_sub_diag Hos) in H1.
}
Qed.

Theorem rngl_le_sub_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a - b ≤ 0 ↔ a ≤ b)%L.
Proof.
intros Hop Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
specialize (rngl_add_le_compat Hor) as H1.
split; intros Hab. {
  specialize (H1 (a - b) 0 b b Hab (rngl_le_refl Hor _))%L.
  rewrite (rngl_sub_add Hop) in H1.
  now rewrite rngl_add_0_l in H1.
} {
  specialize (H1 a b (- b) (- b) Hab (rngl_le_refl Hor _))%L.
  do 2 rewrite (rngl_add_opp_r Hop) in H1.
  now rewrite (rngl_sub_diag Hos) in H1.
}
Qed.

Theorem rngl_lt_0_sub :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < b - a ↔ a < b)%L.
Proof.
intros * Hop Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
split; intros Hab. {
  apply (rngl_lt_iff Hor) in Hab.
  apply (rngl_lt_iff Hor).
  destruct Hab as (Hab, Habz).
  split; [ now apply (rngl_le_0_sub Hop Hor) | ].
  intros H; subst b.
  now rewrite (rngl_sub_diag Hos) in Habz.
} {
  apply (rngl_lt_iff Hor) in Hab.
  apply (rngl_lt_iff Hor).
  destruct Hab as (Hab, Habz).
  split; [ now apply (rngl_le_0_sub Hop Hor) | ].
  apply not_eq_sym.
  intros H1.
  apply Habz; symmetry.
  now apply (rngl_sub_move_0_r Hop).
}
Qed.

Theorem rngl_opp_le_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (x ≤ y ↔ - y ≤ - x)%L.
Proof.
intros * Hop Hor *.
split; intros Hxy. {
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_comm, (rngl_add_opp_r Hop).
  now apply (rngl_le_0_sub Hop Hor).
} {
  apply (rngl_le_0_sub Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_add_comm.
  rewrite <- (rngl_opp_involutive Hop y).
  rewrite (rngl_add_opp_r Hop).
  now apply (rngl_le_0_sub Hop Hor).
}
Qed.

Theorem rngl_opp_lt_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (x < y ↔ - y < - x)%L.
Proof.
intros * Hop Hor *.
split; intros Hxy. {
  apply (rngl_lt_iff Hor) in Hxy.
  apply (rngl_lt_iff Hor).
  split. {
    apply (rngl_opp_le_compat Hop Hor).
    now do 2 rewrite (rngl_opp_involutive Hop).
  } {
    intros H; symmetry in H.
    apply (f_equal rngl_opp) in H.
    now do 2 rewrite (rngl_opp_involutive Hop) in H.
  }
} {
  apply (rngl_lt_iff Hor) in Hxy.
  apply (rngl_lt_iff Hor).
  split. {
    now apply (rngl_opp_le_compat Hop Hor).
  } {
    intros H; symmetry in H.
    now apply (f_equal rngl_opp) in H.
  }
}
Qed.

Theorem rngl_opp_nonneg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ - a)%L ↔ (a ≤ 0)%L.
Proof.
intros Hop Hor *.
split; intros Ha. {
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_opp_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (- a ≤ 0)%L ↔ (0 ≤ a)%L.
Proof.
intros Hop Hor *.
split; intros Ha. {
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_opp_neg_pos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (- a < 0 ↔ 0 < a)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_opp_0 Hop) at 1.
split; intros Ha. {
  now apply (rngl_opp_lt_compat Hop Hor) in Ha.
} {
  now apply (rngl_opp_lt_compat Hop Hor) in Ha.
}
Qed.

Arguments rngl_mul_nat {T ro} a%L n%nat.

Theorem rngl_mul_nat_mul_nat_1 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ a n, rngl_mul_nat a n = (a * rngl_of_nat n)%L.
Proof.
intros Hon Hos *.
induction n; cbn. {
  symmetry; apply (rngl_mul_0_r Hos).
}
rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
f_equal.
apply IHn.
Qed.

Theorem rngl_of_nat_0 : rngl_of_nat 0 = 0%L.
Proof. easy. Qed.

Theorem eq_rngl_of_nat_0 :
  rngl_has_1 T = true →
  rngl_characteristic T = 0 →
  ∀ i, rngl_of_nat i = 0%L → i = 0.
Proof.
intros Hon Hch * Hi.
destruct i; [ easy | exfalso ].
cbn in Hi.
specialize (rngl_characteristic_0 Hon Hch) as H1.
now specialize (H1 i) as H.
Qed.

Theorem rngl_of_nat_inj :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T = 0 →
  ∀ i j,
  rngl_of_nat i = rngl_of_nat j
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

Theorem rngl_mul_nat_add_r : ∀ a m n,
  rngl_mul_nat a (m + n) = (rngl_mul_nat a m + rngl_mul_nat a n)%L.
Proof.
intros.
unfold rngl_mul_nat, mul_nat.
induction m; cbn; [ now rewrite rngl_add_0_l | ].
rewrite <- rngl_add_assoc; f_equal.
apply IHm.
Qed.

Theorem rngl_mul_nat_comm :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ n a, (rngl_of_nat n * a = a * rngl_of_nat n)%L.
Proof.
intros Hon Hos *.
induction n; cbn. {
  rewrite (rngl_mul_0_r Hos).
  apply (rngl_mul_0_l Hos).
}
rewrite rngl_mul_add_distr_l.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_1_r Hon).
f_equal.
apply IHn.
Qed.

Theorem fold_rngl_mul_nat :
  ∀ a n, List.fold_right rngl_add 0%L (List.repeat a n)%L = rngl_mul_nat a n.
Proof. easy. Qed.

Theorem fold_rngl_of_nat :
  ∀ n, List.fold_right rngl_add 0%L (List.repeat 1 n)%L = rngl_of_nat n.
Proof. easy. Qed.

Theorem rngl_of_nat_add : ∀ m n,
  rngl_of_nat (m + n) = (rngl_of_nat m + rngl_of_nat n)%L.
Proof.
intros.
apply rngl_mul_nat_add_r.
Qed.

Theorem rngl_of_nat_sub :
  rngl_has_opp_or_subt T = true →
  ∀ m n : nat, n ≤ m → rngl_of_nat (m - n) = (rngl_of_nat m - rngl_of_nat n)%L.
Proof.
intros Hos * Hnm.
replace m with (n + (m - n)) at 2. 2: {
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm.
  apply Nat.add_sub.
}
rewrite rngl_of_nat_add.
symmetry.
rewrite rngl_add_comm.
apply (rngl_add_sub Hos).
Qed.

Theorem rngl_of_nat_mul :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ m n : nat, rngl_of_nat (m * n) = (rngl_of_nat m * rngl_of_nat n)%L.
Proof.
intros Hon Hos *.
induction m; cbn; [ symmetry; apply (rngl_mul_0_l Hos) | ].
do 2 rewrite fold_rngl_of_nat.
rewrite rngl_of_nat_add, rngl_mul_add_distr_r.
now rewrite (rngl_mul_1_l Hon); f_equal.
Qed.

Theorem rngl_of_nat_pow :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ a n, rngl_of_nat (a ^ n) = (rngl_of_nat a ^ n)%L.
Proof.
intros Hon Hos *.
induction n; cbn; [ apply rngl_add_0_r | ].
rewrite fold_rngl_of_nat.
destruct n. {
  cbn; f_equal.
  apply Nat.mul_1_r.
}
rewrite (rngl_of_nat_mul Hon Hos).
now f_equal.
Qed.

Theorem rngl_mul_nat_pow_comm :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ a b n, (rngl_of_nat a ^ n * b = b * rngl_of_nat a ^ n)%L.
Proof.
intros Hon Hos *.
rewrite <- (rngl_of_nat_pow Hon Hos).
apply (rngl_mul_nat_comm Hon Hos).
Qed.

Theorem rngl_of_nat_1 : rngl_of_nat 1 = 1%L.
Proof. apply rngl_add_0_r. Qed.

Theorem rngl_mul_nat_succ :
  ∀ a n, rngl_mul_nat a (S n) = (a + rngl_mul_nat a n)%L.
Proof.
intros.
rewrite <- Nat.add_1_l.
rewrite rngl_mul_nat_add_r.
now cbn; rewrite rngl_add_0_r.
Qed.

Theorem rngl_of_nat_succ :
  ∀ n, rngl_of_nat (S n) = (1 + rngl_of_nat n)%L.
Proof.
intros.
rewrite <- Nat.add_1_l.
rewrite rngl_of_nat_add.
now rewrite rngl_of_nat_1.
Qed.

(* *)

Theorem rngl_add_lt_mono :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T,
  (a < b → c + a < c + b)%L.
Proof.
intros Hos Hor * Hab.
apply (rngl_lt_iff Hor) in Hab.
destruct Hab as (Hab, Haeb).
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_add_le_compat Hor); [ | easy ].
  apply (rngl_le_refl Hor).
} {
  intros H; apply Haeb; clear Haeb.
  now apply (rngl_add_cancel_l Hos) in H.
}
Qed.

Theorem rngl_add_lt_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T,
  (a < b ↔ c + a < c + b)%L.
Proof.
intros Hop Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
split; intros Hab. {
  now apply (rngl_add_lt_mono Hos Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hab.
  rewrite (rngl_add_sub_simpl_l Hos) in Hab.
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_add_lt_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T,
  (a < b ↔ a + c < b + c)%L.
Proof.
intros Hop Hor *.
do 2 rewrite (rngl_add_comm _ c).
now apply (rngl_add_lt_mono_l Hop Hor).
Qed.

(* *)

Theorem rngl_opp_inv :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a, a ≠ 0%L → (- a⁻¹ = (- a)⁻¹)%L.
Proof.
intros Hon Hop Hiv * Haz.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hid : rngl_has_inv_and_1_or_quot T = true). {
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
remember (Nat.eqb (rngl_characteristic T) 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat.eqb_eq in Hch.
  exfalso; apply Haz.
  apply (rngl_characteristic_1 Hon Hos Hch).
}
apply Nat.eqb_neq in Hch.
assert (Hoaz : (- a)%L ≠ 0%L). {
  intros H.
  apply (f_equal rngl_opp) in H.
  rewrite rngl_opp_involutive in H; [ | easy ].
  now rewrite rngl_opp_0 in H.
}
apply (rngl_mul_cancel_l Hid (- a)%L); [ easy | ].
specialize (rngl_opt_mul_inv_diag_r) as H2.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
rewrite Hon, Hiv in H2; cbn in H2.
rewrite rngl_mul_opp_opp; [ | easy ].
destruct ic. {
  symmetry.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_diag_l; [ | easy | easy | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_diag_l; [ | easy | easy | easy ].
  easy.
} {
  cbn in H2.
  rewrite rngl_mul_inv_r; [ | easy ].
  rewrite rngl_mul_inv_r; [ | easy ].
  rewrite H2; [ | easy ].
  now rewrite H2.
}
Qed.

Theorem rngl_div_mul_div :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ x y z, y ≠ 0%L → ((x / y) * (y / z))%L = (x / z)%L.
Proof.
intros Hon Hiv * Hs.
unfold rngl_div; rewrite Hiv.
rewrite rngl_mul_assoc; f_equal.
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_inv_diag_l; [ | easy| easy | easy ].
apply (rngl_mul_1_r Hon).
Qed.

Theorem eq_rngl_div_1 :
  rngl_has_1 T = true →
  rngl_has_inv_or_quot T = true →
   ∀ a b, b ≠ 0%L → a = b → (a / b = 1)%L.
Proof.
intros Hon Hiv * Hbz Hab.
subst a.
apply (rngl_div_diag Hon Hiv _ Hbz).
Qed.

Theorem eq_rngl_add_same_0 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true →
  rngl_characteristic T = 0 →
  ∀ a,
  (a + a = 0)%L
  → a = 0%L.
Proof.
intros Hon Hos Hii Hch * Haa.
rewrite <- (rngl_mul_1_l Hon a) in Haa.
rewrite <- rngl_mul_add_distr_r in Haa.
specialize (rngl_characteristic_0 Hon Hch 1) as H1.
cbn in H1.
rewrite rngl_add_0_r in H1.
apply (rngl_eq_mul_0_r Hos) in Haa; [ easy | | easy ].
destruct rngl_is_integral_domain; [ easy | ].
cbn in Hii |-*.
apply rngl_has_inv_or_quot_iff in Hii.
apply rngl_has_inv_and_1_or_quot_iff.
now destruct Hii; [ left | right ].
Qed.

(* *)

Theorem rngl_pow_0_l :
  rngl_has_opp_or_subt T = true →
  ∀ n, (0 ^ n)%L = match n with 0 => 1%L | _ => 0%L end.
Proof.
intros Hos *.
destruct n; [ easy | ].
destruct n; [ easy | cbn ].
apply (rngl_mul_0_l Hos).
Qed.

Theorem rngl_pow_0_r : ∀ a, (a ^ 0 = 1)%L.
Proof. easy. Qed.

Theorem rngl_pow_add_r :
  rngl_has_1 T = true →
  ∀ a i j, (a ^ (i + j) = a ^ i * a ^ j)%L.
Proof.
intros Hon *.
induction i; [ symmetry; apply (rngl_mul_1_l Hon) | ].
destruct i. {
  destruct j. {
    symmetry; apply (rngl_mul_1_r Hon).
  }
  cbn in IHi |-*.
  now rewrite IHi.
}
cbn in IHi |-*.
rewrite IHi.
rewrite <- rngl_mul_assoc; f_equal.
Qed.

Theorem rngl_pow_nonzero :
  rngl_has_1 T = true →
  rngl_characteristic T ≠ 1 →
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a n, (a ≠ 0 → a ^ n ≠ 0)%L.
Proof.
intros Hon Hc1 Hos Hii * Haz.
induction n; [ now apply (rngl_1_neq_0_iff Hon) | cbn ].
intros H1; apply IHn.
destruct n; [ easy | ].
now apply (rngl_eq_mul_0_l Hos Hii) in H1.
Qed.

(* *)

Theorem rngl_mul_nonneg_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a * b)%L.
Proof.
intros * Hop Hor * Ha Hb.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 0 0 a b)%L.
assert (H : (0 ≤ 0 ≤ a)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ b)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
now rewrite (rngl_mul_0_l Hos) in H1.
Qed.

Theorem rngl_mul_nonpos_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → b ≤ 0 → 0 ≤ a * b)%L.
Proof.
intros * Hop Hor * Ha Hb.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
specialize (rngl_mul_le_compat_nonpos Hop Hor) as H1.
specialize (H1 0 0 a b)%L.
assert (H : (a ≤ 0 ≤ 0)%L) by now split; [ | apply (rngl_le_refl Hor) ].
specialize (H1 H); clear H.
assert (H : (b ≤ 0 ≤ 0)%L) by now split; [ | apply (rngl_le_refl Hor) ].
specialize (H1 H); clear H.
now rewrite (rngl_mul_0_l Hos) in H1.
Qed.

Theorem rngl_mul_nonneg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → b ≤ 0 → a * b ≤ 0)%L.
Proof.
intros * Hop Hor * Ha Hb.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 0 0 a (- b))%L.
assert (H : (0 ≤ 0 ≤ a)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ - b)%L). {
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_opp_le_compat Hop Hor) in Hb.
  now rewrite (rngl_opp_0 Hop) in Hb.
}
specialize (H1 H); clear H.
rewrite (rngl_mul_0_l Hos) in H1.
rewrite (rngl_mul_opp_r Hop) in H1.
apply (rngl_opp_le_compat Hop Hor) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
now rewrite (rngl_opp_0 Hop) in H1.
Qed.

Theorem rngl_mul_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → 0 ≤ b → a * b ≤ 0)%L.
Proof.
intros * Hop Hor * Ha Hb.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 0 0 (- a) b)%L.
assert (H : (0 ≤ 0 ≤ - a)%L). {
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ b)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
rewrite (rngl_mul_0_l Hos) in H1.
rewrite (rngl_mul_opp_l Hop) in H1.
apply (rngl_opp_le_compat Hop Hor) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
now rewrite (rngl_opp_0 Hop) in H1.
Qed.

Theorem rngl_0_le_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (0 ≤ 1)%L.
Proof.
intros Hon Hop Hor.
destruct (rngl_le_dec Hor 0%L 1%L) as [| H1]; [ easy | ].
apply (rngl_not_le Hor) in H1.
destruct H1 as (H1, H2).
specialize (rngl_mul_nonpos_nonpos Hop Hor) as H3.
specialize (H3 1 1 H2 H2)%L.
now rewrite (rngl_mul_1_l Hon) in H3.
Qed.

Theorem rngl_0_lt_inv_compat :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a → 0 < a⁻¹)%L.
Proof.
intros * Hon Hop Hiv Hor.
intros * Hza.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Haz : a ≠ 0%L). {
  intros H; subst a.
  now apply (rngl_lt_irrefl Hor) in Hza.
}
specialize (rngl_inv_neq_0 Hon Hos Hiv) as H1.
destruct (rngl_le_dec Hor 0 a⁻¹)%L as [H2| H2]. {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; symmetry in H; revert H.
  now apply H1.
}
apply (rngl_not_le Hor) in H2.
destruct H2 as (H2, H3).
specialize (rngl_mul_nonneg_nonpos Hop Hor) as H4.
assert (H : (0 ≤ a)%L) by now apply (rngl_lt_iff Hor) in Hza.
specialize (H4 _ _ H H3); clear H.
rewrite (rngl_mul_inv_diag_r Hon Hiv a Haz) in H4.
specialize (rngl_0_le_1 Hon Hop Hor) as H5.
specialize (rngl_le_antisymm Hor _ _ H4 H5) as H6.
clear H4 H5.
apply (rngl_1_eq_0_iff Hon Hos) in H6.
specialize (rngl_characteristic_1 Hon Hos H6) as H4.
exfalso; apply Haz, H4.
Qed.

Theorem rngl_inv_lt_0_compat :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, (a < 0 → a⁻¹ < 0)%L.
Proof.
intros * Hon Hop Hiv Hor.
intros * Hza.
specialize (rngl_0_lt_inv_compat Hon Hop Hiv Hor) as H2.
specialize (H2 (- a))%L.
apply (rngl_opp_lt_compat Hop Hor).
rewrite (rngl_opp_0 Hop).
rewrite (rngl_opp_inv Hon Hop Hiv); [ | now apply rngl_lt_iff ].
apply H2.
apply (rngl_opp_lt_compat Hop Hor) in Hza.
now rewrite (rngl_opp_0 Hop) in Hza.
Qed.

Theorem rngl_lt_le_incl :
  rngl_is_ordered T = true →
  ∀ a b, (a < b → a ≤ b)%L.
Proof.
intros Hor * Hab.
now apply (rngl_lt_iff Hor) in Hab.
Qed.

Theorem rngl_mul_pos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b, (0 < a → b < 0 → a * b < 0)%L.
Proof.
intros Hop Hor Hid * Hza Hbz.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_mul_nonneg_nonpos Hop Hor). {
    now apply (rngl_lt_le_incl Hor).
  } {
    now apply (rngl_lt_le_incl Hor).
  }
}
intros H.
apply (rngl_integral Hos Hid) in H.
destruct H as [H| H]. {
  subst a.
  now apply (rngl_lt_irrefl Hor) in Hza.
} {
  subst b.
  now apply (rngl_lt_irrefl Hor) in Hbz.
}
Qed.

Theorem rngl_div_le_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (b ≠ 0 → 0 ≤ a ≤ b → a / b ≤ 1)%L.
Proof.
intros * Hon Hop Hiv Hor * Hbz (Hza, Hab).
unfold rngl_div.
rewrite Hiv.
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 a b⁻¹ b b⁻¹)%L.
assert (H : (0 ≤ a ≤ b)%L) by easy.
specialize (H1 H); clear H.
assert (H : (0 ≤ b⁻¹ ≤ b⁻¹)%L). {
  split; [ | apply (rngl_le_refl Hor) ].
  apply (rngl_lt_le_incl Hor).
  apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
  apply (rngl_lt_iff Hor).
  split; [ | congruence ].
  now apply (rngl_le_trans Hor _ a).
}
specialize (H1 H); clear H.
now rewrite (rngl_mul_inv_diag_r Hon Hiv) in H1.
Qed.

Theorem rngl_square_ge_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a * a)%L.
Proof.
intros * Hop Hor *.
destruct (rngl_le_dec Hor 0%L a) as [Hap| Han]. {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
} {
  apply (rngl_not_le Hor) in Han.
  now apply (rngl_mul_nonpos_nonpos Hop Hor).
}
Qed.

Theorem rngl_squ_opp :
  rngl_has_opp T = true →
  ∀ a, rngl_squ (- a)%L = rngl_squ a.
Proof.
intros Hop *.
progress unfold rngl_squ.
apply (rngl_mul_opp_opp Hop).
Qed.

Theorem rngl_squ_abs :
  rngl_has_opp T = true →
  ∀ a, rngl_squ (rngl_abs a) = rngl_squ a.
Proof.
intros Hop *.
progress unfold rngl_abs.
destruct (a ≤? 0)%L; [ | easy ].
apply (rngl_squ_opp Hop).
Qed.

Theorem rngl_squ_add :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a b, (rngl_squ (a + b) = rngl_squ a + 2 * a * b + rngl_squ b)%L.
Proof.
intros Hic Hon *.
progress unfold rngl_squ.
rewrite rngl_mul_add_distr_l.
do 2 rewrite rngl_mul_add_distr_r.
rewrite rngl_add_assoc; f_equal.
rewrite <- rngl_add_assoc; f_equal.
rewrite <- rngl_mul_assoc.
rewrite <- (rngl_add_diag Hon); f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_squ_sub :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a b, (rngl_squ (a - b) = rngl_squ a - 2 * a * b + rngl_squ b)%L.
Proof.
intros Hop Hic Hon *.
progress unfold rngl_sub.
rewrite Hop.
rewrite (rngl_squ_add Hic Hon).
rewrite (rngl_squ_opp Hop).
f_equal; f_equal.
apply (rngl_mul_opp_r Hop).
Qed.

Theorem rngl_squ_mul :
  rngl_mul_is_comm T = true →
  ∀ a b, rngl_squ (a * b)%L = (rngl_squ a * rngl_squ b)%L.
Proof.
intros Hic *.
progress unfold rngl_squ.
do 2 rewrite rngl_mul_assoc.
f_equal.
apply (rngl_mul_mul_swap Hic).
Qed.

Theorem eq_rngl_add_square_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool =
    true →
  ∀ a b : T, (a * a + b * b = 0)%L → a = 0%L ∧ b = 0%L.
Proof.
intros * Hop Hor Hii * Hab.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
apply (rngl_eq_add_0 Hor) in Hab; cycle 1. {
  apply (rngl_square_ge_0 Hop Hor).
} {
  apply (rngl_square_ge_0 Hop Hor).
}
destruct Hab as (Ha, Hb).
split. {
  now apply (rngl_integral Hos Hii) in Ha; destruct Ha.
} {
  now apply (rngl_integral Hos Hii) in Hb; destruct Hb.
}
Qed.

Theorem rngl_le_add_le_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b ≤ c ↔ b ≤ c - a)%L.
Proof.
intros Hop Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
split; intros Habc. {
  specialize (rngl_add_le_compat Hor) as H1.
  specialize (H1 (a + b) c (- a) (- a) Habc)%L.
  specialize (H1 (rngl_le_refl Hor _)).
  do 2 rewrite (rngl_add_opp_r Hop) in H1.
  rewrite rngl_add_comm in H1.
  now rewrite (rngl_add_sub Hos) in H1.
} {
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_sub_add_distr Hos).
  now apply (rngl_le_0_sub Hop Hor).
}
Qed.

Theorem rngl_le_add_le_sub_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b ≤ c ↔ a ≤ c - b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_le_add_le_sub_l Hop Hor).
Qed.

Theorem rngl_sub_le_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a ≤ b)%L ↔ (c - b ≤ c - a)%L.
Proof.
intros Hop Hor *.
split; intros Hab. {
  progress unfold rngl_sub.
  rewrite Hop.
  apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
  now apply -> (rngl_opp_le_compat Hop Hor).
} {
  apply (rngl_opp_le_compat Hop Hor) in Hab.
  do 2 rewrite (rngl_opp_sub_distr Hop) in Hab.
  apply (rngl_add_le_compat Hor) with (c := c) (d := c) in Hab. 2: {
    apply (rngl_le_refl Hor).
  }
  now do 2 rewrite (rngl_sub_add Hop) in Hab.
}
Qed.

Theorem rngl_sub_le_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ b ↔ a - c ≤ b - c)%L.
Proof.
intros Hop Hor *.
split; intros Hab. {
  rewrite <- (rngl_opp_sub_distr Hop c a).
  rewrite <- (rngl_opp_sub_distr Hop c b).
  apply -> (rngl_opp_le_compat Hop Hor).
  now apply (rngl_sub_le_mono_l Hop Hor).
} {
  apply (rngl_add_le_compat Hor _ _ c c) in Hab. 2: {
    apply (rngl_le_refl Hor).
  }
  now do 2 rewrite (rngl_sub_add Hop) in Hab.
}
Qed.

Theorem rngl_sub_lt_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a < b)%L ↔ (c - b < c - a)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_sub.
rewrite Hop.
split; intros Hab. {
  apply (rngl_add_lt_mono_l Hop Hor).
  now apply -> (rngl_opp_lt_compat Hop Hor).
} {
  apply (rngl_add_lt_mono_l Hop Hor) in Hab.
  now apply (rngl_opp_lt_compat Hop Hor).
}
Qed.

Theorem rngl_sub_lt_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a < b)%L ↔ (a - c < b - c)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_sub.
rewrite Hop.
apply (rngl_add_lt_mono_r Hop Hor).
Qed.

Theorem rngl_add_le_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (b ≤ c ↔ a + b ≤ a + c)%L.
Proof.
intros Hop Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
split; intros Hbc. {
  apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | easy ].
}
apply (rngl_sub_le_mono_r Hop Hor) with (c := a) in Hbc.
now do 2 rewrite rngl_add_comm, (rngl_add_sub Hos) in Hbc.
Qed.

Theorem rngl_add_le_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ b ↔ a + c ≤ b + c)%L.
Proof.
intros Hop Hor *.
do 2 rewrite (rngl_add_comm _ c).
apply (rngl_add_le_mono_l Hop Hor).
Qed.

Theorem rngl_le_sub_le_add_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b ≤ c ↔ a ≤ b + c)%L.
Proof.
intros Hop Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
split; intros Habc. {
  apply (rngl_sub_le_mono_r Hop Hor _ _ b).
  now rewrite rngl_add_comm, (rngl_add_sub Hos).
} {
  apply (rngl_sub_le_mono_r Hop Hor _ _ b) in Habc.
  now rewrite rngl_add_comm, (rngl_add_sub Hos) in Habc.
}
Qed.

Theorem rngl_le_sub_le_add_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b ≤ c ↔ a ≤ c + b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_le_sub_le_add_l Hop Hor).
Qed.

Theorem rngl_lt_sub_lt_add_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b < c ↔ a < b + c)%L.
Proof.
intros Hop Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
split; intros Habc. {
  apply (rngl_sub_lt_mono_r Hop Hor _ _ b).
  now rewrite rngl_add_comm, (rngl_add_sub Hos).
} {
  apply (rngl_sub_lt_mono_r Hop Hor _ _ b) in Habc.
  now rewrite rngl_add_comm, (rngl_add_sub Hos) in Habc.
}
Qed.

Theorem rngl_nle_gt :
  rngl_is_ordered T = true →
  ∀ a b, (¬ (a ≤ b) ↔ b < a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  apply (rngl_not_le Hor) in Hab.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  now apply not_eq_sym.
} {
  intros H1.
  apply (rngl_lt_iff Hor) in Hab.
  destruct Hab as (H2, H3).
  now apply H3, (rngl_le_antisymm Hor).
}
Qed.

Theorem rngl_nlt_ge :
  rngl_is_ordered T = true →
  ∀ a b, (¬ (a < b) ↔ b ≤ a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  destruct (rngl_le_dec Hor b a) as [H1| H1]; [ easy | ].
  exfalso; apply Hab.
  now apply (rngl_nle_gt Hor).
} {
  intros H1.
  apply (rngl_lt_iff Hor) in H1.
  destruct H1 as (H2, H3).
  now apply H3, (rngl_le_antisymm Hor).
}
Qed.

Theorem rngl_lt_le_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a < b)%L → (b ≤ c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
specialize rngl_opt_le_trans as H1.
rewrite Hor in H1.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_le_trans Hor _ b); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
} {
  intros H; subst c.
  now apply (rngl_nle_gt Hor) in Hab.
}
Qed.

Theorem rngl_le_lt_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a ≤ b)%L → (b < c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
specialize rngl_opt_le_trans as H1.
rewrite Hor in H1.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_le_trans Hor _ b); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
} {
  intros H; subst c.
  now apply (rngl_nle_gt Hor) in Hbc.
}
Qed.

Theorem rngl_lt_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a < b)%L → (b < c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
apply (rngl_le_lt_trans Hor _ b); [ | easy ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_le_add_l :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → b ≤ a + b)%L.
Proof.
intros Hor * Hbz.
remember (a + b)%L as c.
rewrite <- (rngl_add_0_l b); subst c.
apply (rngl_add_le_compat Hor); [ easy | apply (rngl_le_refl Hor) ].
Qed.

Theorem rngl_le_add_r :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ b → a ≤ a + b)%L.
Proof.
intros Hor * Hbz.
rewrite rngl_add_comm.
now apply (rngl_le_add_l Hor).
Qed.

Theorem rngl_lt_add_l :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (b < a + b)%L.
Proof.
intros Hos Hor * Hbz.
apply (rngl_lt_iff Hor).
split; [ now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor) | ].
intros H.
symmetry in H.
apply (rngl_add_sub_eq_r Hos) in H.
rewrite (rngl_sub_diag Hos) in H; subst a.
revert Hbz.
apply (rngl_lt_irrefl Hor).
Qed.

Theorem rngl_lt_add_r :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < b)%L → (a < a + b)%L.
Proof.
intros Hos Hor * Hbz.
rewrite rngl_add_comm.
now apply (rngl_lt_add_l Hos Hor).
Qed.

Theorem rngl_le_sub_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ b ↔ a - b ≤ a)%L.
Proof.
intros Hop Hor *.
split; intros Hb. {
  apply (rngl_le_sub_le_add_r Hop Hor).
  now apply (rngl_le_add_r Hor).
} {
  apply (rngl_le_sub_le_add_l Hop Hor) in Hb.
  apply (rngl_add_le_mono_r Hop Hor _ _ a).
  now rewrite rngl_add_0_l.
}
Qed.

Theorem rngl_lt_add_lt_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b < c ↔ b < c - a)%L.
Proof.
intros Hop Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
rewrite rngl_add_comm.
split; intros Hab. {
  apply (rngl_sub_lt_mono_r Hop Hor _ _ a) in Hab.
  now rewrite (rngl_add_sub Hos) in Hab.
} {
  apply (rngl_sub_lt_mono_r Hop Hor _ _ a).
  now rewrite (rngl_add_sub Hos).
}
Qed.

(**)
Theorem rngl_add_lt_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a < b → c < d → a + c < b + d)%L.
Proof.
intros Hop Hor * Hab Hcd.
apply (rngl_lt_trans Hor _ (a + d)%L). {
  now apply (rngl_add_lt_mono_l Hop Hor).
} {
  now apply (rngl_add_lt_mono_r Hop Hor).
}
Qed.

Theorem rngl_lt_add_lt_sub_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b < c ↔ a < c - b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_lt_add_lt_sub_l Hop Hor).
Qed.

Theorem rngl_0_lt_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (0 < 1)%L.
Proof.
intros Hon Hop Hc1 Hor.
apply (rngl_lt_iff Hor).
split. 2: {
  apply not_eq_sym.
  now apply (rngl_1_neq_0_iff Hon).
}
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_0_lt_2 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (0 < 2)%L.
Proof.
intros Hon Hop Hc1 Hor.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
apply (rngl_le_lt_trans Hor _ 1)%L. {
  apply (rngl_0_le_1 Hon Hop Hor).
}
apply (rngl_lt_add_r Hos Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_2_neq_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (2 ≠ 0)%L.
Proof.
intros Hon Hop Hc1 Hor.
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as H5.
intros H; rewrite H in H5.
now apply (rngl_lt_irrefl Hor) in H5.
Qed.

Theorem rngl_add_nonneg_nonneg :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a + b)%L.
Proof.
intros Hor * Ha Hb.
apply (rngl_le_trans Hor _ a); [ easy | ].
now apply (rngl_le_add_r Hor).
Qed.

Theorem rngl_add_nonneg_pos :
  rngl_is_ordered T = true →
  rngl_has_opp_or_subt T = true →
  ∀ a b, (0 ≤ a)%L → (0 < b)%L → (0 < a + b)%L.
Proof.
intros Hor Hos * Hza Hzb.
apply (rngl_le_lt_trans Hor _ a); [ easy | ].
now apply (rngl_lt_add_r Hos Hor).
Qed.

Theorem rngl_add_nonpos_nonpos :
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → b ≤ 0 → a + b ≤ 0)%L.
Proof.
intros Hor * Ha Hb.
apply (rngl_le_trans Hor _ a); [ | easy ].
rewrite <- rngl_add_0_r.
apply (rngl_add_le_compat Hor); [ | easy ].
apply (rngl_le_refl Hor).
Qed.

Theorem rngl_of_nat_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ n, (0 ≤ rngl_of_nat n)%L.
Proof.
intros Hon Hop Hor *.
induction n; [ apply (rngl_le_refl Hor) | ].
rewrite rngl_of_nat_succ.
eapply (rngl_le_trans Hor); [ apply IHn | ].
apply (rngl_le_add_l Hor).
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_mul_nat_inj_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → ∀ i j, i ≤ j ↔ (rngl_mul_nat a i ≤ rngl_mul_nat a j)%L.
Proof.
intros Hop Hor * Haz *.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
revert j.
induction i; intros; cbn. {
  split; [ | intros; apply Nat.le_0_l ].
  intros H; clear H.
  induction j; [ apply (rngl_le_refl Hor) | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHj | ].
  now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor).
}
destruct j. {
  split; [ easy | cbn ].
  intros H; exfalso.
  apply (rngl_nlt_ge Hor) in H; apply H; clear H.
  eapply (rngl_lt_le_trans Hor); [ apply Haz | ].
  apply (rngl_le_add_r Hor).
  clear IHi.
  induction i; [ apply (rngl_le_refl Hor) | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHi | ].
  now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor).
}
cbn.
split; intros Hij. {
  apply Nat.succ_le_mono in Hij.
  apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
  now apply IHi.
} {
  apply -> Nat.succ_le_mono.
  apply (rngl_add_le_mono_l Hop Hor) in Hij.
  now apply IHi.
}
Qed.

Theorem rngl_mul_nat_inj_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → ∀ i j, i < j ↔ (rngl_mul_nat a i < rngl_mul_nat a j)%L.
Proof.
intros Hop Hor * Haz *.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
revert j.
induction i; intros; cbn. {
  split; intros Hj. 2: {
    destruct j; [ | apply Nat.lt_0_succ ].
    now apply (rngl_lt_irrefl Hor) in Hj.
  }
  induction j; [ easy | clear Hj ].
  cbn.
  apply (rngl_lt_le_trans Hor _ a); [ easy | ].
  apply (rngl_le_add_r Hor).
  destruct j; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_lt_le_incl Hor), IHj.
  apply Nat.lt_0_succ.
}
destruct j. {
  split; [ easy | cbn ].
  intros H; exfalso.
  apply (rngl_nle_gt Hor) in H; apply H; clear H.
  eapply (rngl_le_trans Hor); [ apply (rngl_lt_le_incl Hor), Haz | ].
  apply (rngl_le_add_r Hor).
  clear IHi.
  induction i; [ apply (rngl_le_refl Hor) | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHi | ].
  now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor).
}
cbn.
split; intros Hij. {
  apply Nat.succ_lt_mono in Hij.
  apply (rngl_add_lt_mono_l Hop Hor).
  now apply IHi.
} {
  apply -> Nat.succ_lt_mono.
  apply (rngl_add_lt_mono_l Hop Hor) in Hij.
  now apply IHi.
}
Qed.

Theorem rngl_of_nat_inj_le :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ i j, i ≤ j ↔ (rngl_of_nat i ≤ rngl_of_nat j)%L.
Proof.
intros Hon Hop Hc1 Hor *.
apply (rngl_mul_nat_inj_le Hop Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_of_nat_inj_lt :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ i j, i < j ↔ (rngl_of_nat i < rngl_of_nat j)%L.
Proof.
intros Hon Hop Hc1 Hor *.
apply (rngl_mul_nat_inj_lt Hop Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_one_sub_half :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (1 - 2⁻¹ = 2⁻¹)%L.
Proof.
intros Hon Hop Hiv Hor.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 (_ - _))%L, H1.
}
assert (Hc2 : (2 ≠ 0)%L). {
  specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as H2.
  intros H; rewrite H in H2.
  now apply (rngl_lt_irrefl Hor) in H2.
}
apply (rngl_mul_cancel_r Hi1) with (c := 2%L); [ easy | ].
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_inv_diag_l Hon Hiv); [ | easy ].
rewrite (rngl_mul_1_l Hon).
apply (rngl_add_sub Hos).
Qed.

(* abs *)

Theorem rngl_abs_0 :
  rngl_has_opp T = true →
  rngl_abs 0%L = 0%L.
Proof.
intros Hop.
progress unfold rngl_abs.
rewrite (rngl_opp_0 Hop).
now destruct (0 ≤? 0)%L.
Qed.

Theorem eq_rngl_abs_0 :
  rngl_has_opp T = true →
  ∀ a, rngl_abs a = 0%L → a = 0%L.
Proof.
intros Hop * Ha.
progress unfold rngl_abs in Ha.
destruct (a ≤? 0)%L; [ | easy ].
rewrite <- (rngl_opp_0 Hop) in Ha.
now apply (rngl_opp_inj Hop) in Ha.
Qed.

Theorem rngl_abs_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_abs 1 = 1)%L.
Proof.
intros Hon Hop Hor.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 (rngl_abs 1)%L), (H1 1%L).
}
progress unfold rngl_abs.
remember (1 ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | easy ].
apply rngl_leb_le in Hc.
apply (rngl_nlt_ge Hor) in Hc.
exfalso; apply Hc.
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_squ_0 :
  rngl_has_opp_or_subt T = true →
  (0² = 0)%L.
Proof.
intros Hos.
apply (rngl_mul_0_l Hos).
Qed.

Theorem rngl_squ_1 :
  rngl_has_1 T = true →
  (1² = 1)%L.
Proof.
intros Hon.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_leb_gt :
  rngl_is_ordered T = true →
  ∀ a b, ((a ≤? b) = false ↔ b < a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  apply rngl_leb_nle in Hab.
  apply (rngl_not_le Hor) in Hab.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  now apply not_eq_sym.
} {
  apply rngl_leb_nle.
  intros H1.
  now apply (rngl_nle_gt Hor) in Hab.
}
Qed.

Theorem rngl_ltb_ge :
  rngl_is_ordered T = true →
  ∀ a b, ((a <? b) = false ↔ b ≤ a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  apply rngl_ltb_nlt in Hab.
  now apply (rngl_nlt_ge Hor) in Hab.
} {
  apply rngl_ltb_nlt.
  intros H1.
  now apply (rngl_nlt_ge Hor) in Hab.
}
Qed.

Theorem rngl_0_le_abs :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ rngl_abs a)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az. {
  apply rngl_leb_le in Haz.
  apply (rngl_opp_le_compat Hop Hor) in Haz.
  now rewrite (rngl_opp_0 Hop) in Haz.
} {
  apply (rngl_leb_gt Hor) in Haz.
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem rngl_abs_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (- x ≤ y ≤ x ↔ rngl_abs y ≤ x)%L.
Proof.
intros * Hop Hor *.
progress unfold rngl_abs.
split. {
  intros (Hxy, Hyx).
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz; [ | easy ].
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_involutive Hop).
} {
  intros Hyx.
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz. {
    apply rngl_leb_le in Hyz.
    split. {
      apply (rngl_opp_le_compat Hop Hor) in Hyx.
      now rewrite (rngl_opp_involutive Hop) in Hyx.
    } {
      apply (rngl_le_trans Hor _ 0%L); [ easy | ].
      apply (rngl_le_trans Hor _ (- y)%L); [ | easy ].
      apply (rngl_le_0_sub Hop Hor) in Hyz.
      progress unfold rngl_sub in Hyz.
      rewrite Hop in Hyz.
      now rewrite rngl_add_0_l in Hyz.
    }
  }
  split; [ | easy ].
  apply (rngl_leb_gt Hor) in Hyz.
  apply (rngl_lt_le_incl Hor).
  apply (rngl_le_lt_trans Hor _ 0)%L; [ | easy ].
  rewrite <- (rngl_opp_0 Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_trans Hor _ y)%L.
}
Qed.

Theorem rngl_abs_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (- x < y < x ↔ rngl_abs y < x)%L.
Proof.
intros * Hop Hor *.
progress unfold rngl_abs.
split. {
  intros (Hxy, Hyx).
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz; [ | easy ].
  apply (rngl_opp_lt_compat Hop Hor).
  now rewrite (rngl_opp_involutive Hop).
} {
  intros Hyx.
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz. {
    apply rngl_leb_le in Hyz.
    split. {
      apply (rngl_opp_lt_compat Hop Hor) in Hyx.
      now rewrite (rngl_opp_involutive Hop) in Hyx.
    } {
      apply (rngl_le_lt_trans Hor _ 0%L); [ easy | ].
      apply (rngl_le_lt_trans Hor _ (- y)%L); [ | easy ].
      apply (rngl_le_0_sub Hop Hor) in Hyz.
      progress unfold rngl_sub in Hyz.
      rewrite Hop in Hyz.
      now rewrite rngl_add_0_l in Hyz.
    }
  }
  split; [ | easy ].
  apply (rngl_leb_gt Hor) in Hyz.
  apply (rngl_le_lt_trans Hor _ 0)%L; [ | easy ].
  rewrite <- (rngl_opp_0 Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_trans Hor _ y)%L.
}
Qed.

Theorem rngl_abs_opp :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, rngl_abs (- a)%L = rngl_abs a.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (- a ≤? 0)%L as c eqn:Hc; symmetry in Hc.
remember (a ≤? 0)%L as d eqn:Hd; symmetry in Hd.
destruct c. {
  apply rngl_leb_le in Hc.
  rewrite (rngl_opp_involutive Hop).
  rewrite <- (rngl_opp_0 Hop) in Hc.
  apply (rngl_opp_le_compat Hop Hor) in Hc.
  destruct d; [ | easy ].
  apply rngl_leb_le in Hd.
  apply (rngl_le_antisymm Hor) in Hd; [ | easy ].
  subst a.
  symmetry; apply (rngl_opp_0 Hop).
} {
  apply (rngl_leb_gt Hor) in Hc.
  rewrite <- (rngl_opp_0 Hop) in Hc.
  apply (rngl_opp_lt_compat Hop Hor) in Hc.
  destruct d; [ easy | ].
  apply (rngl_leb_gt Hor) in Hd.
  now apply (rngl_lt_asymm Hor) in Hd.
}
Qed.

Theorem rngl_abs_sub_comm :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, rngl_abs (a - b)%L = rngl_abs (b - a)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_abs_opp Hop Hor).
now rewrite (rngl_opp_sub_distr Hop).
Qed.

Theorem rngl_abs_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a)%L → rngl_abs a = a.
Proof.
intros Hop Hor * Hza.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az; [ | easy ].
apply rngl_leb_le in Haz.
apply (rngl_le_antisymm Hor _ _ Hza) in Haz.
subst a.
apply (rngl_opp_0 Hop).
Qed.

Theorem rngl_abs_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a : T, (a ≤ 0)%L → rngl_abs a = (- a)%L.
Proof.
intros Hop Hor * Haz.
rewrite <- (rngl_opp_involutive Hop a) at 1.
rewrite (rngl_abs_opp Hop Hor).
apply (rngl_abs_nonneg Hop Hor).
rewrite <- (rngl_opp_0 Hop).
now apply -> (rngl_opp_le_compat Hop Hor).
Qed.

Theorem rngl_0_lt_abs :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x, (x ≠ 0 → 0 < rngl_abs x)%L.
Proof.
intros Hop Hor * Hxz.
apply (rngl_lt_iff Hor).
split. 2: {
  apply not_eq_sym.
  intros H; apply Hxz; clear Hxz.
  progress unfold rngl_abs in H.
  remember (x ≤? 0)%L as xz eqn:Hxz; symmetry in Hxz.
  destruct xz; [ | easy ].
  apply (f_equal rngl_opp) in H.
  rewrite (rngl_opp_involutive Hop) in H.
  now rewrite (rngl_opp_0 Hop) in H.
}
apply (rngl_0_le_abs Hop Hor).
Qed.

Theorem rngl_abs_div :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  ∀ x y, y ≠ 0%L → rngl_abs (x / y)%L = (rngl_abs x / rngl_abs y)%L.
Proof.
intros * Hon Hop Hiv Heb Hor * Hyz.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hiq : rngl_has_inv_and_1_or_quot T = true). {
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
progress unfold rngl_abs.
remember (x ≤? _)%L as xz eqn:Hx; symmetry in Hx.
remember (y ≤? _)%L as yz eqn:Hy; symmetry in Hy.
remember (x / y ≤? _)%L as xyz eqn:Hxy; symmetry in Hxy.
destruct xz. {
  apply rngl_leb_le in Hx.
  destruct yz. {
    apply rngl_leb_le in Hy.
    destruct xyz. {
      apply rngl_leb_le in Hxy.
      progress unfold rngl_div in Hxy.
      rewrite Hiv in Hxy.
      specialize (rngl_mul_le_compat_nonpos Hop Hor) as H1.
      specialize (H1 0 0 x y⁻¹)%L.
      assert (H : (x ≤ 0 ≤ 0)%L). {
        split; [ easy | apply (rngl_le_refl Hor) ].
      }
      specialize (H1 H); clear H.
      assert (H : (y⁻¹ ≤ 0 ≤ 0)%L). {
        split; [ | apply (rngl_le_refl Hor) ].
        apply (rngl_opp_le_compat Hop Hor).
        rewrite (rngl_opp_0 Hop).
        rewrite (rngl_opp_inv Hon Hop Hiv _ Hyz).
        apply (rngl_opp_le_compat Hop Hor) in Hy.
        rewrite (rngl_opp_0 Hop) in Hy.
        apply (rngl_lt_le_incl Hor).
        apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
        apply (rngl_lt_iff Hor).
        split; [ easy | ].
        intros H.
        apply (f_equal rngl_opp) in H.
        rewrite (rngl_opp_0 Hop) in H.
        rewrite (rngl_opp_involutive Hop) in H.
        now symmetry in H.
      }
      specialize (H1 H); clear H.
      rewrite (rngl_mul_0_l Hos) in H1.
      specialize (rngl_le_antisymm Hor _ _ Hxy H1) as H2.
      apply (rngl_integral Hos) in H2. 2: {
        rewrite Hiq, Heb; cbn.
        now destruct rngl_is_integral_domain.
      }
      destruct H2 as [H2| H2]. {
        subst x.
        rewrite (rngl_div_0_l Hos Hiq _ Hyz).
        rewrite (rngl_opp_0 Hop).
        symmetry.
        apply (rngl_div_0_l Hos Hiq).
        intros H.
        apply (f_equal rngl_opp) in H.
        rewrite (rngl_opp_0 Hop) in H.
        now rewrite (rngl_opp_involutive Hop) in H.
      } {
        exfalso; revert H2.
        now apply (rngl_inv_neq_0 Hon Hos Hiv).
      }
    } {
      unfold rngl_div.
      rewrite Hiv.
      rewrite (rngl_mul_opp_l Hop).
      rewrite <- (rngl_mul_opp_r Hop).
      f_equal.
      rewrite (rngl_opp_inv Hon Hop Hiv). 2: {
        intros H.
        apply (f_equal rngl_opp) in H.
        rewrite (rngl_opp_0 Hop) in H.
        now rewrite (rngl_opp_involutive Hop) in H.
      }
      now rewrite (rngl_opp_involutive Hop).
    }
  } {
    apply (rngl_leb_gt Hor) in Hy.
    destruct xyz. {
      apply rngl_leb_le in Hxy.
      progress unfold rngl_div.
      rewrite Hiv.
      now rewrite (rngl_mul_opp_l Hop).
    } {
      apply rngl_leb_nle in Hxy.
      exfalso; apply Hxy; clear Hxy.
      progress unfold rngl_div.
      rewrite Hiv.
      apply (rngl_mul_nonpos_nonneg Hop Hor _ _ Hx).
      apply (rngl_lt_le_incl Hor).
      now apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
    }
  }
}
apply (rngl_leb_gt Hor) in Hx.
destruct yz. {
  apply rngl_leb_le in Hy.
  destruct xyz. {
    apply rngl_leb_le in Hxy.
    progress unfold rngl_div.
    rewrite Hiv.
    rewrite <- (rngl_mul_opp_r Hop).
    f_equal.
    now apply (rngl_opp_inv Hon Hop Hiv).
  } {
    apply rngl_leb_nle in Hxy.
    exfalso; apply Hxy; clear Hxy.
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_lt_le_incl Hor) in Hx.
    apply (rngl_mul_nonneg_nonpos Hop Hor _ _ Hx).
    apply (rngl_lt_le_incl Hor).
    apply (rngl_inv_lt_0_compat Hon Hop Hiv Hor).
    apply (rngl_lt_iff Hor).
    split; [ easy | congruence ].
  }
}
(* ... *)
apply rngl_leb_nle in Hy.
apply (rngl_not_le Hor) in Hy.
destruct Hy as (_, Hy).
destruct xyz; [ | easy ].
apply rngl_leb_le in Hxy.
unfold rngl_div in Hxy.
rewrite Hiv in Hxy.
assert (Hzy : (0 < y)%L). {
  apply (rngl_lt_iff Hor).
  split; [ easy | congruence ].
}
specialize (rngl_0_lt_inv_compat Hon Hop Hiv Hor _ Hzy) as Hy'.
apply (rngl_lt_le_incl Hor) in Hy'.
generalize Hx; intros Hx'.
apply (rngl_lt_le_incl Hor) in Hx'.
specialize (rngl_mul_nonneg_nonneg Hop Hor _ _ Hx' Hy') as H1.
specialize (rngl_le_antisymm Hor _ _ Hxy H1) as H2.
apply (rngl_integral Hos) in H2. 2: {
  rewrite Hiq, Heb.
  now destruct rngl_is_integral_domain.
}
destruct H2 as [H2| H2]. {
  now subst x; apply (rngl_lt_irrefl Hor) in Hx.
} {
  exfalso; revert H2.
  now apply (rngl_inv_neq_0 Hon Hos Hiv).
}
Qed.

Theorem rngl_abs_triangle :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs (a + b) ≤ rngl_abs a + rngl_abs b)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
remember (a + b ≤? 0)%L as abz eqn:Habz; symmetry in Habz.
destruct abz. {
  apply rngl_leb_le in Habz.
  destruct az. {
    apply rngl_leb_le in Haz.
    rewrite (rngl_opp_add_distr Hop).
    progress unfold rngl_sub.
    rewrite Hop.
    rewrite rngl_add_comm.
    apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
    destruct bz; [ apply (rngl_le_refl Hor) | ].
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor).
    apply (rngl_lt_trans Hor _ 0)%L; [ | easy ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_lt_compat Hop Hor).
  }
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    rewrite rngl_add_comm.
    rewrite (rngl_opp_add_distr Hop).
    progress unfold rngl_sub.
    rewrite Hop.
    apply (rngl_add_le_compat Hor); [ | apply (rngl_le_refl Hor) ].
    apply (rngl_lt_le_incl Hor).
    apply (rngl_lt_trans Hor _ 0)%L; [ | easy ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_lt_compat Hop Hor).
  }
  apply (rngl_leb_gt Hor) in Hbz.
  apply (rngl_nlt_ge Hor) in Habz.
  exfalso; apply Habz; clear Habz.
  apply (rngl_lt_le_trans Hor _ a); [ easy | ].
  apply (rngl_le_add_r Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_leb_gt Hor) in Habz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_nle_gt Hor) in Habz.
    exfalso; apply Habz; clear Habz.
    rewrite <- rngl_add_0_r.
    now apply (rngl_add_le_compat Hor).
  }
  apply (rngl_add_le_compat Hor); [ | apply (rngl_le_refl Hor) ].
  apply (rngl_le_trans Hor _ 0)%L; [ easy | ].
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  now rewrite (rngl_opp_0 Hop).
}
apply (rngl_leb_gt Hor) in Haz.
apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
destruct bz; [ | apply (rngl_le_refl Hor) ].
apply rngl_leb_le in Hbz.
apply (rngl_le_trans Hor _ 0)%L; [ easy | ].
apply (rngl_opp_le_compat Hop Hor).
rewrite (rngl_opp_involutive Hop).
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_abs_mul :
  rngl_has_opp T = true →
  rngl_has_inv_and_1_or_quot T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs (a * b) = rngl_abs a * rngl_abs b)%L.
Proof.
intros Hop Hi1 Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
remember (a * b ≤? 0)%L as abz eqn:Habz; symmetry in Habz.
destruct abz. {
  apply rngl_leb_le in Habz.
  destruct az. {
    rewrite (rngl_mul_opp_l Hop).
    apply rngl_leb_le in Haz.
    destruct bz; [ | easy ].
    rewrite (rngl_mul_opp_r Hop).
    apply rngl_leb_le in Hbz.
    specialize (rngl_mul_nonpos_nonpos Hop Hor _ _ Haz Hbz) as H1.
    apply (rngl_le_antisymm Hor _ _ Habz) in H1.
    rewrite H1.
    now do 2 rewrite (rngl_opp_0 Hop).
  }
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz; [ now rewrite (rngl_mul_opp_r Hop) | ].
  apply (rngl_leb_gt Hor) in Hbz.
  apply (rngl_nlt_ge Hor) in Habz.
  exfalso; apply Habz; clear Habz.
  apply (rngl_lt_iff Hor).
  split. {
    now apply (rngl_mul_nonneg_nonneg Hop Hor); apply (rngl_lt_le_incl Hor).
  }
  apply not_eq_sym.
  intros H1.
  apply (rngl_eq_mul_0_l Hos) in H1. {
    now subst a; apply (rngl_lt_irrefl Hor) in Haz.
  } {
    rewrite Hi1.
    now destruct (rngl_is_integral_domain T).
  } {
    intros H; subst b.
    now apply (rngl_lt_irrefl Hor) in Hbz.
  }
}
apply (rngl_leb_gt Hor) in Habz.
destruct az. {
  rewrite (rngl_mul_opp_l Hop).
  apply rngl_leb_le in Haz.
  destruct bz. {
    rewrite (rngl_mul_opp_r Hop).
    symmetry.
    apply (rngl_opp_involutive Hop).
  }
  apply (rngl_leb_gt Hor) in Hbz.
  apply (rngl_lt_iff Hor) in Hbz.
  destruct Hbz as (Hbz, Hzb).
  specialize (rngl_mul_nonpos_nonneg Hop Hor _ _ Haz Hbz) as H1.
  now apply (rngl_nlt_ge Hor) in H1.
}
apply (rngl_leb_gt Hor) in Haz.
destruct bz; [ | easy ].
apply rngl_leb_le in Hbz.
apply (rngl_lt_iff Hor) in Haz.
destruct Haz as (Haz, Hza).
specialize (rngl_mul_nonneg_nonpos Hop Hor _ _ Haz Hbz) as H1.
now apply (rngl_nlt_ge Hor) in H1.
Qed.

Theorem rngl_le_min_l :
  rngl_is_ordered T = true →
  ∀ a b, (rngl_min a b ≤ a)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ apply (rngl_le_refl Hor) | ].
apply (rngl_leb_gt Hor) in Hc.
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_le_min_r :
  rngl_is_ordered T = true →
  ∀ a b, (rngl_min a b ≤ b)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
now apply rngl_leb_le in Hc.
Qed.

Theorem rngl_le_max_l :
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ rngl_max a b)%L.
Proof.
intros Hor *.
progress unfold rngl_max.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
now apply rngl_leb_le in Hc.
Qed.

Theorem rngl_le_max_r :
  rngl_is_ordered T = true →
  ∀ a b, (b ≤ rngl_max a b)%L.
Proof.
intros Hor *.
progress unfold rngl_max.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ apply (rngl_le_refl Hor) | ].
apply (rngl_leb_gt Hor) in Hc.
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_le_abs :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (a ≤ rngl_abs a)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
apply rngl_leb_le in Hc.
apply (rngl_le_sub_0 Hop Hor).
rewrite (rngl_sub_opp_r Hop).
rewrite <- (rngl_add_0_l 0%L).
now apply (rngl_add_le_compat Hor).
Qed.

Theorem rngl_squ_sub_squ :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  ∀ a b, (rngl_squ a - rngl_squ b = (a + b) * (a - b))%L.
Proof.
intros Hop Hic *.
progress unfold rngl_squ.
rewrite rngl_mul_add_distr_r.
do 2 rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_mul_comm Hic b a).
f_equal; symmetry.
apply (rngl_sub_add Hop).
Qed.

Theorem rngl_add_squ_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a² + b²)%L.
Proof.
intros Hop Hor *.
apply (rngl_add_nonneg_nonneg Hor);
  apply (rngl_square_ge_0 Hop Hor).
Qed.

Theorem rngl_squ_inv :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a, (a ≠ 0 → (a⁻¹)² = (a²)⁻¹)%L.
Proof.
intros Hon Hos Hiv * Haz.
progress unfold rngl_squ.
now rewrite (rngl_inv_mul_distr Hon Hos Hiv).
Qed.

Theorem rngl_squ_div :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a b, (b ≠ 0)%L → (a / b)²%L = (a² / b²)%L.
Proof.
intros Hic Hon Hos Hiv * Hbz.
progress unfold rngl_div.
rewrite Hiv.
rewrite <- (rngl_squ_inv Hon Hos Hiv); [ | easy ].
apply (rngl_squ_mul Hic).
Qed.

Theorem eq_rngl_squ_0 :
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a, (a² = 0 → a = 0)%L.
Proof.
intros Hos Hii * Ha.
apply (rngl_integral Hos Hii) in Ha.
now destruct Ha.
Qed.

Theorem eq_rngl_squ_rngl_abs :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b, rngl_squ a = rngl_squ b → rngl_abs a = rngl_abs b.
Proof.
intros Hop Hic Hor Hii * Hab.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
apply (rngl_sub_move_0_r Hop) in Hab.
rewrite (rngl_squ_sub_squ Hop Hic) in Hab.
apply (rngl_integral Hos Hii) in Hab.
destruct Hab as [Hab| Hab]. {
  apply (rngl_add_move_0_r Hop) in Hab.
  subst a.
  apply (rngl_abs_opp Hop Hor).
} {
  apply -> (rngl_sub_move_0_r Hop) in Hab.
  now subst a.
}
Qed.

Theorem rngl_squ_pow_2 : ∀ a, (a² = a ^ 2)%L.
Proof. easy. Qed.

Theorem rngl_squ_eq_cases :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, (a² = b² → a = b ∨ a = -b)%L.
Proof.
intros Hic Hon Hop Hiv Hed * Hab.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_and_1_or_quot_iff.
  now rewrite Hiv, Hon; left.
}
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
apply (rngl_sub_move_0_r Hop) in Hab.
rewrite (rngl_squ_sub_squ Hop Hic) in Hab.
apply (rngl_integral Hos Hid) in Hab.
destruct Hab as [Hab| Hab]; [ right | left ]. {
  now apply (rngl_add_move_0_r Hop) in Hab.
} {
  now apply -> (rngl_sub_move_0_r Hop) in Hab.
}
Qed.

Theorem rngl_min_glb :
  ∀ a b c, (a ≤ b → a ≤ c → a ≤ rngl_min b c)%L.
Proof.
intros * Hab Hac.
progress unfold rngl_min.
now destruct (b ≤? c)%L.
Qed.

Theorem rngl_min_glb_lt :
  ∀ a b c, (a < b → a < c → a < rngl_min b c)%L.
Proof.
intros * Hab Hac.
progress unfold rngl_min.
now destruct (b ≤? c)%L.
Qed.

Theorem rngl_max_lub :
  ∀ a b c, (a ≤ c → b ≤ c → rngl_max a b ≤ c)%L.
Proof.
intros * Hac Hbc.
progress unfold rngl_max.
now destruct (a ≤? b)%L.
Qed.

Theorem rngl_max_lub_lt :
  ∀ a b c, (a < c → b < c → rngl_max a b < c)%L.
Proof.
intros * Hac Hbc.
progress unfold rngl_max.
now destruct (a ≤? b)%L.
Qed.

Theorem rngl_mul_pos_pos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (0 < a * b)%L.
Proof.
intros Hop Hor Hii * Haz Hbz.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
apply (rngl_lt_iff Hor) in Haz.
apply (rngl_lt_iff Hor) in Hbz.
apply (rngl_lt_iff Hor).
destruct Haz as (Haz, Hza).
destruct Hbz as (Hbz, Hzb).
split. {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply not_eq_sym in Hza, Hzb.
apply not_eq_sym.
intros Hab.
now apply (rngl_eq_mul_0_l Hos) in Hab.
Qed.

Theorem rngl_mul_pos_cancel_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < a → 0 < a * b ↔ 0 < b)%L.
Proof.
intros Hop Hor Hii * Ha.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
split; intros Hb. {
  apply (rngl_lt_iff Hor) in Ha.
  apply (rngl_lt_iff Hor) in Hb.
  apply (rngl_lt_iff Hor).
  destruct Ha as (Haz, Hza).
  destruct Hb as (Habz, Hzab).
  apply not_eq_sym in Hza, Hzab.
  split. {
    apply (rngl_lt_eq_cases Hor) in Habz.
    destruct Habz as [Habz| Habz]. {
      apply (rngl_nle_gt Hor) in Habz.
      apply (rngl_nlt_ge Hor).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst b.
  now rewrite (rngl_mul_0_r Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hop Hor).
}
Qed.

Theorem rngl_mul_pos_cancel_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < b → 0 < a * b ↔ 0 < a)%L.
Proof.
intros Hop Hor Hii * Ha.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
split; intros Hb. {
  apply (rngl_lt_iff Hor) in Ha.
  apply (rngl_lt_iff Hor) in Hb.
  apply (rngl_lt_iff Hor).
  destruct Ha as (Haz, Hza).
  destruct Hb as (Habz, Hzab).
  apply not_eq_sym in Hza, Hzab.
  split. {
    apply (rngl_lt_eq_cases Hor) in Habz.
    destruct Habz as [Habz| Habz]. {
      apply (rngl_nle_gt Hor) in Habz.
      apply (rngl_nlt_ge Hor).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
      now apply (rngl_lt_le_incl Hor).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst a.
  now rewrite (rngl_mul_0_l Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hop Hor).
}
Qed.

Theorem rngl_mul_lt_mono_pos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (a * b < a * c)%L.
Proof.
intros Hop Hor Hii * Ha.
split; intros Hbc. {
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
  now apply (rngl_lt_0_sub Hop Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_l Hop) in Hbc.
  apply (rngl_mul_pos_cancel_l Hop Hor Hii) in Hbc; [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_mul_lt_mono_pos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (b * a < c * a)%L.
Proof.
intros Hop Hor Hii * Ha.
split; intros Hbc. {
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii); [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hbc.
  apply (rngl_mul_pos_cancel_r Hop Hor Hii) in Hbc; [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_mul_le_mono_pos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < c)%L → (a ≤ b)%L ↔ (c * a ≤ c * b)%L.
Proof.
intros Hop Hor Hii * Hc.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
split; intros Hab. {
  apply (rngl_lt_eq_cases Hor) in Hab.
  destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_le_0_sub Hop Hor) in Hab.
  rewrite <- (rngl_mul_sub_distr_l Hop) in Hab.
  apply (rngl_nlt_ge Hor) in Hab.
  apply (rngl_nlt_ge Hor).
  intros H1; apply Hab; clear Hab.
  replace 0%L with (c * 0)%L by apply (rngl_mul_0_r Hos).
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_nle_gt Hor).
  intros H2.
  apply -> (rngl_le_0_sub Hop Hor) in H2.
  now apply (rngl_nlt_ge Hor) in H2.
}
Qed.

Theorem rngl_mul_le_mono_nonneg_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ a)%L → (b ≤ c)%L → (a * b ≤ a * c)%L.
Proof.
intros Hop Hor * Ha Hbc.
apply (rngl_lt_eq_cases Hor) in Hbc.
destruct Hbc as [Hbc| Hbc]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
apply (rngl_le_0_sub Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_nonneg_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ c → a ≤ b → a * c ≤ b * c)%L.
Proof.
intros Hop Hor * Hc Hab.
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
apply (rngl_le_0_sub Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_pos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < c)%L → (a ≤ b)%L ↔ (a * c ≤ b * c)%L.
Proof.
intros Hop Hor Hii * Hc.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
split; intros Hab. {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_le_0_sub Hop Hor) in Hab.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hab.
  apply (rngl_nlt_ge Hor) in Hab.
  apply (rngl_nlt_ge Hor).
  intros H1; apply Hab; clear Hab.
  replace 0%L with (0 * c)%L by apply (rngl_mul_0_l Hos).
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii); [ easy | ].
  apply (rngl_nle_gt Hor).
  intros H2.
  apply -> (rngl_le_0_sub Hop Hor) in H2.
  now apply (rngl_nlt_ge Hor) in H2.
}
Qed.

Theorem rngl_mul_le_mono_nonpos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ 0)%L → (b ≤ c)%L → (a * c ≤ a * b)%L.
Proof.
intros Hop Hor * Ha Hbc.
apply (rngl_lt_eq_cases Hor) in Hbc.
destruct Hbc as [Hbc| Hbc]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_mul_nonpos_nonpos Hop Hor); [ easy | ].
apply (rngl_le_sub_0 Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_nonpos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (c ≤ 0 → a ≤ b → b * c ≤ a * c)%L.
Proof.
intros Hop Hor * Hc Hab.
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_mul_nonpos_nonpos Hop Hor); [ | easy ].
apply (rngl_le_sub_0 Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_lt_mono_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c d, (0 ≤ a → a < b → 0 ≤ c → c < d → a * c < b * d)%L.
Proof.
intros Hop Hor Hii * Haz Hab Hcz Hcd.
apply (rngl_le_lt_trans Hor _ (b * c)%L). {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ | easy ].
now apply (rngl_le_lt_trans Hor _ a).
Qed.

Theorem rngl_square_le_simpl_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (0 ≤ b → a * a ≤ b * b → a ≤ b)%L.
Proof.
intros Hop Hor Hii * Hzb Hab.
destruct (rngl_le_dec Hor a 0%L) as [Haz| Haz]. {
  now apply (rngl_le_trans Hor a 0%L b).
}
apply (rngl_nle_gt Hor) in Haz.
apply (rngl_nlt_ge Hor) in Hab.
apply (rngl_nlt_ge Hor).
intros Hba; apply Hab; clear Hab.
now apply (rngl_mul_lt_mono_nonneg Hop Hor Hii).
Qed.

Theorem rngl_div_pos :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 < b → 0 ≤ a / b)%L.
Proof.
intros Hon Hop Hiv Hor * Ha Hb.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
apply (rngl_mul_le_mono_pos_l Hop Hor) with (c := b); [ | easy | ]. {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
rewrite rngl_mul_0_r; [ | now apply rngl_has_opp_or_subt_iff; left ].
rewrite (rngl_mul_inv_diag_r Hon Hiv); [ apply (rngl_0_le_1 Hon Hop Hor) | ].
apply (rngl_lt_iff Hor) in Hb.
now apply not_eq_sym.
Qed.

Theorem rngl_div_lt_pos:
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (0 < a / b)%L.
Proof.
intros Hon Hop Hiv Hor * Ha Hb.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
now apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
Qed.

Theorem rngl_le_div_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a ≤ b * c ↔ a / c ≤ b)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
split; intros Habq. {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with (c := c); [ easy | ].
  rewrite (rngl_mul_div_r Hon Hiv); [ easy | ].
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
} {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ c) in Habq; [ | easy ].
  rewrite (rngl_mul_div_r Hon Hiv) in Habq; [ easy | ].
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
Qed.

Theorem rngl_le_div_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a * c ≤ b ↔ a ≤ b / c)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
split; intros Habq. {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with (c := c); [ easy | ].
  now rewrite (rngl_mul_div_r Hon Hiv).
} {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ c) in Habq; [ | easy ].
  now rewrite (rngl_mul_div_r Hon Hiv) in Habq.
}
Qed.

Theorem rngl_lt_div_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a < b * c ↔ a / c < b)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
split; intros Habq. {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii) with (a := c); [ easy | ].
  now rewrite (rngl_mul_div_r Hon Hiv).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii c) in Habq; [ | easy ].
  now rewrite (rngl_mul_div_r Hon Hiv) in Habq.
}
Qed.

Theorem rngl_lt_div_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a * c < b ↔ a < b / c)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
split; intros Habq. {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii) with (a := c); [ easy | ].
  now rewrite (rngl_mul_div_r Hon Hiv).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii c) in Habq; [ | easy ].
  now rewrite (rngl_mul_div_r Hon Hiv) in Habq.
}
Qed.

Theorem rngl_pow_pos_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ a n, (0 < a → 0 < a ^ n)%L.
Proof.
intros Hon Hop Hiv Hc1 Hor * Hza.
induction n; cbn. {
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct n; [ easy | ].
now apply (rngl_mul_pos_pos Hop Hor Hii).
Qed.

Theorem rngl_pow_ge_1 :
  rngl_has_opp T = true →
  rngl_has_1 T = true →
  rngl_is_ordered T = true →
  ∀ a n, (1 ≤ a → 1 ≤ a ^ n)%L.
Proof.
intros Hop Hon Hor * Hza.
induction n; [ apply (rngl_le_refl Hor) | cbn ].
rewrite <- (rngl_mul_1_l Hon 1%L).
destruct n. {
  now rewrite (rngl_mul_1_l Hon).
}
apply (rngl_mul_le_compat_nonneg Hop Hor). {
  split; [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
} {
  split; [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
}
Qed.

Theorem rngl_le_0_mul :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a * b → 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0)%L.
Proof.
intros Hon Hop Hiv Hor * Hab.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_and_1_or_quot_iff.
  now rewrite Hiv, Hon; left.
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (rngl_le_dec Hor 0 a)%L as [Hza| Hza]. {
  destruct (rngl_lt_dec Hor 0 a)%L as [Hlza| Hlza]. 2: {
    apply (rngl_nlt_ge Hor) in Hlza.
    apply (rngl_le_antisymm Hor) in Hza; [ | easy ].
    subst a.
    destruct (rngl_le_dec Hor 0 b)%L as [Hzb| Hzb]; [ now left | ].
    apply (rngl_nle_gt Hor), (rngl_lt_le_incl Hor) in Hzb.
    now right.
  }
  rewrite <- (rngl_mul_0_r Hos a) in Hab.
  now left; apply (rngl_mul_le_mono_pos_l Hop Hor Hii) in Hab.
} {
  apply (rngl_nle_gt Hor) in Hza.
  right.
  rewrite <- (rngl_mul_0_l Hos b) in Hab.
  split; [ now apply (rngl_lt_le_incl Hor) | ].
  apply (rngl_nle_gt Hor) in Hza.
  apply (rngl_nlt_ge Hor).
  intros Hzb; apply Hza.
  now apply (rngl_mul_le_mono_pos_r Hop Hor Hii) in Hab.
}
Qed.

Theorem rngl_middle_sub_l :
   rngl_has_1 T = true →
   rngl_has_opp T = true →
   rngl_has_inv T = true →
   rngl_is_ordered T = true →
   ∀ a b, (((a + b) / 2 - a) = (b - a) / 2)%L.
Proof.
intros Hon Hop Hiv Hor *.
progress unfold rngl_div.
rewrite Hiv.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_add_comm.
progress unfold rngl_sub.
rewrite Hop.
rewrite <- rngl_add_assoc; f_equal.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_mul_1_r Hon a) at 2.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_mul_opp_r Hop).
f_equal.
rewrite <- (rngl_opp_involutive Hop (_ - _))%L.
f_equal.
rewrite (rngl_opp_sub_distr Hop).
apply (rngl_one_sub_half Hon Hop Hiv Hor).
Qed.

Theorem rngl_middle_sub_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (b - (a + b) / 2 = (b - a) / 2)%L.
Proof.
intros Hon Hop Hiv Hor *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
progress unfold rngl_div.
rewrite Hiv.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_add_comm.
rewrite (rngl_sub_add_distr Hos).
f_equal.
rewrite <- (rngl_mul_1_r Hon b) at 1.
rewrite <- (rngl_mul_sub_distr_l Hop).
f_equal.
apply (rngl_one_sub_half Hon Hop Hiv Hor).
Qed.

Theorem rngl_abs_le_squ_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs a ≤ rngl_abs b → a² ≤ b²)%L.
Proof.
intros Hop Hor * Hab.
progress unfold rngl_squ.
progress unfold rngl_abs in Hab.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hab.
    now apply (rngl_mul_le_compat_nonpos Hop Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Haz.
    rewrite (rngl_opp_0 Hop) in Haz.
    rewrite <- (rngl_mul_opp_opp Hop).
    apply (rngl_lt_le_incl Hor) in Hbz.
    now apply (rngl_mul_le_compat_nonneg Hop Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hbz.
    rewrite (rngl_opp_0 Hop) in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop b).
    apply (rngl_lt_le_incl Hor) in Haz.
    now apply (rngl_mul_le_compat_nonneg Hop Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor) in Haz, Hbz.
    now apply (rngl_mul_le_compat_nonneg Hop Hor).
  }
}
Qed.

Theorem rngl_abs_lt_squ_lt :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b : T, (rngl_abs a < rngl_abs b)%L → (a² < b²)%L.
Proof.
intros Hic Hop Hor Hii * Hab.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_abs_le_squ_le Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hii) in H.
rewrite H in Hab.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem rngl_squ_le_abs_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a² ≤ b² → rngl_abs a ≤ rngl_abs b)%L.
Proof.
intros Hop Hor Hii * Hab.
progress unfold rngl_squ in Hab.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop) in Hab.
    rewrite <- (rngl_mul_opp_opp Hop b) in Hab.
    apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab; [ easy | ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_le_compat Hop Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Haz.
    rewrite (rngl_opp_0 Hop) in Haz.
    rewrite <- (rngl_mul_opp_opp Hop) in Hab.
    apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab; [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hbz.
    rewrite (rngl_opp_0 Hop) in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop b) in Hab.
    now apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab.
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor) in Haz, Hbz.
    now apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab.
  }
}
Qed.

Theorem rngl_squ_lt_abs_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (a² < b²)%L → (rngl_abs a < rngl_abs b)%L.
Proof.
intros Hop Hor Hii * Hab.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply (f_equal rngl_squ) in H.
do 2 rewrite (rngl_squ_abs Hop) in H.
rewrite H in Hab.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem rngl_add_neg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a < 0)%L → (b ≤ 0)%L → (a + b < 0)%L.
Proof.
intros Hop Hor * Haz Hbz.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
eapply (rngl_lt_le_trans Hor); [ | apply Hbz ].
apply (rngl_lt_add_lt_sub_r Hop Hor).
now rewrite (rngl_sub_diag Hos).
Qed.

Theorem rngl_add_nonpos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0)%L → (b < 0)%L → (a + b < 0)%L.
Proof.
intros Hop Hor * Haz Hbz.
rewrite rngl_add_comm.
now apply (rngl_add_neg_nonpos Hop Hor).
Qed.

(* general limit using a parametrized distance *)

Definition is_gen_Cauchy_sequence {A} (dist : A → A → T) (u : nat → A) :=
  ∀ ε : T, (0 < ε)%L →
  ∃ N : nat, ∀ p q : nat, N ≤ p → N ≤ q → (dist (u p) (u q) < ε)%L.

Definition is_gen_limit_when_tending_to_inf {A} (dist : A → A → T) f l :=
  ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n → (dist l (f n) < ε)%L.

(* completeness *)

Definition rngl_dist a b := rngl_abs (a - b)%L.

Definition is_Cauchy_sequence := is_gen_Cauchy_sequence rngl_dist.

Definition is_limit_when_tending_to f a l :=
  (∀ ε, 0 < ε → ∃ η, 0 < η ∧
   ∀ x, rngl_abs (x - a) < η → rngl_abs (f x - l) < ε)%L.

Definition is_limit_when_tending_to_inf :=
  is_gen_limit_when_tending_to_inf rngl_dist.

(*
Definition is_limit_when_tending_to_inf f l :=
  ∀ ε, (0 < ε)%L → ∃ N,
  ∀ n, N ≤ n → (rngl_abs (f n - l) < ε)%L.
*)

Definition is_derivative f f' :=
  ∀ a, is_limit_when_tending_to (λ x, (f x - f a) / (x - a))%L a (f' a).

Definition is_complete :=
  ∀ u, is_Cauchy_sequence u → ∃ c, is_limit_when_tending_to_inf u c.

Definition continuous_at f a := is_limit_when_tending_to f a (f a).
Definition continuous f := ∀ a, continuous_at f a.

(* archimedianity *)

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
destruct (rngl_lt_dec Hor (rngl_abs a) 1)%L as [H1x| H1x]. {
  exists 0; cbn.
  rewrite rngl_add_0_r.
  split; [ | easy ].
  apply (rngl_0_le_abs Hop Hor).
}
destruct (rngl_lt_dec Hor 1 (rngl_abs a))%L as [Hx1| Hx1]. 2: {
  apply (rngl_nlt_ge Hor) in H1x, Hx1.
  apply (rngl_le_antisymm Hor) in H1x; [ | easy ].
  rewrite H1x.
  exists 1; cbn.
  rewrite rngl_add_0_r.
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_lt_iff Hor).
  split. 2: {
    intros H12.
    apply (f_equal (λ b, rngl_sub b 1))%L in H12.
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

(* (-1) ^ n *)

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%L
  | _ => (- 1%L)%L
  end.

(* comparison *)

Definition rngl_compare a b :=
  if (a =? b)%L then Eq
  else if (a ≤? b)%L then Lt else Gt.

Theorem rngl_compare_eq_iff :
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Eq ↔ a = b.
Proof.
intros Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
symmetry in Hab.
destruct ab. {
  split; [ | easy ].
  now apply (rngl_eqb_eq Hed) in Hab.
} {
  destruct (a ≤? b)%L. {
    split; [ easy | ].
    now apply (rngl_eqb_neq Hed) in Hab.
  } {
    split; [ easy | ].
    now apply (rngl_eqb_neq Hed) in Hab.
  }
}
Qed.

Theorem rngl_compare_lt_iff :
  rngl_is_ordered T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Lt ↔ (a < b)%L.
Proof.
intros Hor Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
remember (a ≤? b)%L as alb eqn:Halb.
symmetry in Hab, Halb.
destruct ab. {
  split; [ easy | intros H ].
  apply (rngl_eqb_eq Hed) in Hab.
  subst b.
  now apply (rngl_lt_irrefl Hor) in H.
} {
  apply (rngl_eqb_neq Hed) in Hab.
  destruct alb. {
    apply rngl_leb_le in Halb.
    split; [ | easy ].
    intros _.
    now apply (rngl_lt_iff Hor).
  } {
    split; [ easy | ].
    apply (rngl_leb_gt Hor) in Halb.
    intros H.
    now apply (rngl_lt_asymm Hor) in H.
  }
}
Qed.

Theorem rngl_compare_gt_iff :
  rngl_is_ordered T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Gt ↔ (b < a)%L.
Proof.
intros Hor Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
remember (a ≤? b)%L as alb eqn:Halb.
symmetry in Hab, Halb.
destruct ab. {
  split; [ easy | intros H ].
  apply (rngl_eqb_eq Hed) in Hab.
  subst b.
  now apply (rngl_lt_irrefl Hor) in H.
} {
  apply (rngl_eqb_neq Hed) in Hab.
  destruct alb. {
    apply rngl_leb_le in Halb.
    split; [ easy | ].
    intros H.
    now apply (rngl_nle_gt Hor) in H.
  } {
    now apply (rngl_leb_gt Hor) in Halb.
  }
}
Qed.

Theorem rngl_compare_refl :
  rngl_has_eq_dec T = true →
  ∀ a, rngl_compare a a = Eq.
Proof.
intros Hed *.
now apply (rngl_compare_eq_iff Hed).
Qed.

(* *)

Record in_charac_0_field :=
  { cf_has_1 : rngl_has_1 T = true;
    cf_mul_is_comm : rngl_mul_is_comm T = true;
    cf_has_opp : rngl_has_opp T = true;
    cf_has_inv : rngl_has_inv T = true;
    cf_has_eq_dec : rngl_has_eq_dec T = true;
    cf_characteristic : rngl_characteristic T = 0 }.

End a.

Notation "x ?= y" := (rngl_compare x y) : ring_like_scope.

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
rewrite (rngl_add_opp_r Hop).
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
     Rsub_def x y := eq_sym (rngl_add_opp_r Hop x y);
     Ropp_def := rngl_Ropp_def |}.

End a.

(* code to be added to be able to use the Coq tactic "ring"

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {Hic : @rngl_mul_is_comm T ro rp = true}.
Context {Hop : @rngl_has_opp T T ro = true}.

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

Arguments rngl_abs {T ro} a%L.
Arguments rngl_add {T ring_like_op} (a b)%L.
Arguments rngl_add_sub {T}%type {ro rp} Hom (a b)%L.
Arguments rngl_characteristic_1 {T ro rp} Hon Hos Hch x%L.
Arguments rngl_eq_dec {T ro} Hed (a b)%L.
Arguments rngl_le_add_r {T ro rp} Hor (a b)%L Hb.
Arguments rngl_le_dec {T ro rp} Hor (a b)%L.
Arguments rngl_le_trans {T}%type {ro rp} Hor (a b c)%L.
Arguments rngl_le_lt_trans {T}%type {ro rp} Hor (a b c)%L.
Arguments rngl_lt_le_trans {T}%type {ro rp} Hor (a b c)%L.
Arguments rngl_lt_dec {T ro rp} Hor (a b)%L.
Arguments rngl_min {T ro} (a b)%L.
Arguments rngl_mul {T ring_like_op} (a b)%L.
Arguments rngl_mul_nat {T ro} a%L n%nat.
Arguments rngl_mul_0_r {T}%type {ro rp} Hom a%L.
Arguments rngl_squ {T ro} x%L.
Arguments rngl_sub {T ro} (a b)%L.
Arguments rngl_subt {T ro} (a b)%L.

Arguments is_complete T {ro}.
