Require Import Utf8 Arith.

Class ring_like_op T :=
  { rngl_zero : T;
    rngl_add : T → T → T;
    rngl_mul : T → T → T;
    rngl_opt_one : option T;
    rngl_opt_opp_or_subt : option (sum (T → T) (T → T → T));
    rngl_opt_inv_or_quot : option (sum (T → T) (T → T → T));
    rngl_opt_eq_dec : option (∀ a b : T, {a = b} + {a ≠ b});
    rngl_opt_leb : option (T → T → bool) }.

Arguments rngl_opt_opp_or_subt T {ring_like_op}.
Arguments rngl_opt_inv_or_quot T {ring_like_op}.

Declare Scope ring_like_scope.
Delimit Scope ring_like_scope with L.

Definition bool_of_option {T} (x : option T) :=
  match x with
  | Some _ => true
  | None => false
  end.

Definition rngl_one {T} {ro : ring_like_op T} :=
  match rngl_opt_one with
  | Some a => a
  | None => rngl_zero
  end.

Definition rngl_has_1 T {ro : ring_like_op T} :=
  bool_of_option rngl_opt_one.

Definition rngl_has_opp_or_subt T {R : ring_like_op T} :=
  bool_of_option (rngl_opt_opp_or_subt T).

Definition rngl_has_inv_or_quot T {R : ring_like_op T} :=
  bool_of_option (rngl_opt_inv_or_quot T).

Definition rngl_is_ordered T {R : ring_like_op T} :=
  bool_of_option rngl_opt_leb.

Definition rngl_has_eq_dec T {R : ring_like_op T} :=
  bool_of_option rngl_opt_eq_dec.

Definition rngl_has_inv_and_1_or_quot T {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot T with
  | Some (inl _) => rngl_has_1 T
  | Some (inr _) => true
  | None => false
  end.

Definition rngl_has_opp T {R : ring_like_op T} :=
  match rngl_opt_opp_or_subt T with
  | Some (inl _) => true
  | _ => false
  end.

Definition rngl_has_subt T {R : ring_like_op T} :=
  match rngl_opt_opp_or_subt T with
  | Some (inr _) => true
  | _ => false
  end.

Definition rngl_has_inv T {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot T with
  | Some (inl _) => true
  | _ => false
  end.

Definition rngl_has_quot T {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot T with
  | Some (inr _) => true
  | _ => false
  end.

Definition rngl_opp {T} {R : ring_like_op T} a :=
  match rngl_opt_opp_or_subt T with
  | Some (inl rngl_opp) => rngl_opp a
  | _ => rngl_zero
  end.

Definition rngl_subt {T} {ro : ring_like_op T} a b :=
  match rngl_opt_opp_or_subt T with
  | Some (inr rngl_subt) => rngl_subt a b
  | _ => rngl_zero
  end.

Definition rngl_inv {T} {R : ring_like_op T} a :=
  match rngl_opt_inv_or_quot T with
  | Some (inl rngl_inv) => rngl_inv a
  | _ => rngl_zero
  end.

Definition rngl_quot {T} {R : ring_like_op T} a b :=
  match rngl_opt_inv_or_quot T with
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

Definition rngl_eval_polyn {T} {ro : ring_like_op T} l (x : T) :=
  List.fold_right (λ a acc, rngl_add (rngl_mul acc x) a) rngl_zero l.

Definition mul_nat {T} (zero : T) (add : T → T → T) a n :=
  List.fold_right add zero (List.repeat a n).

Definition rngl_mul_nat {T} {ro : ring_like_op T} :=
  mul_nat rngl_zero rngl_add.

Definition rngl_squ {T} {ro : ring_like_op T} x := rngl_mul x x.

Fixpoint rngl_power {T} {ro : ring_like_op T} a n :=
  match n with
  | O => rngl_one
  | S m => rngl_mul a (rngl_power a m)
  end.

Arguments rngl_power {T ro} a%_L n%_nat.

Definition rngl_of_nat {T} {ro : ring_like_op T} a := rngl_mul_nat rngl_one a.

Definition rngl_eqb {T} {R : ring_like_op T} a b :=
  match rngl_opt_eq_dec with
  | Some rngl_eq_dec =>
      match rngl_eq_dec a b with left _ => true | right _ => false end
  | None => false
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

Notation "0" := rngl_zero : ring_like_scope.
Notation "1" := rngl_one : ring_like_scope.
Notation "2" := (rngl_add rngl_one rngl_one) : ring_like_scope.
Notation "a + b" := (rngl_add a b) : ring_like_scope.
Notation "a - b" := (rngl_sub a b) : ring_like_scope.
Notation "a * b" := (rngl_mul a b) : ring_like_scope.
Notation "a / b" := (rngl_div a b) : ring_like_scope.
Notation "- a" := (rngl_opp a) : ring_like_scope.
Notation "- 1" := (rngl_opp rngl_one) : ring_like_scope.
Notation "a '⁻¹'" := (rngl_inv a) (at level 1, format "a ⁻¹") :
  ring_like_scope.
Notation "a '²'" := (rngl_squ a) (at level 1, format "a ²") :
  ring_like_scope.
Notation "a ^ b" := (rngl_power a b) : ring_like_scope.

Notation "a ≤ b" := (rngl_le a b) : ring_like_scope.
Notation "a < b" := (rngl_lt a b) : ring_like_scope.
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
Notation "a ≤ b < c ≤ d" :=
  (a ≤ b ∧ b < c ∧ c ≤ d)%L (at level 70, b at next level, c at next level) :
  ring_like_scope.

Notation "a =? b" := (rngl_eqb a b) (at level 70) : ring_like_scope.
Notation "a ≠? b" := (negb (rngl_eqb a b)) (at level 70) : ring_like_scope.
Notation "a ≤? b" := (rngl_leb a b) (at level 70) : ring_like_scope.
Notation "a <? b" := (rngl_ltb a b) (at level 70) : ring_like_scope.

Inductive not_applicable := NA.

Class ring_like_ord T {ro : ring_like_op T} :=
  { rngl_ord_le_dec : ∀ a b : T, ({a ≤ b} + {¬ a ≤ b})%L;
    rngl_ord_le_refl : ∀ a, (a ≤ a)%L;
    rngl_ord_le_antisymm : ∀ a b, (a ≤ b → b ≤ a → a = b)%L;
    rngl_ord_le_trans : ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%L;
    rngl_ord_add_le_compat : ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%L;
    rngl_ord_mul_le_compat_nonneg :
      if rngl_has_opp T then
        ∀ a b c d, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_ord_mul_le_compat_nonpos :
      if rngl_has_opp T then
        ∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_ord_mul_le_compat_non_opp :
      if negb (rngl_has_opp T) then
        ∀ a b c d, (a ≤ c)%L → (b ≤ d)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_ord_not_le : ∀ a b, (¬ a ≤ b → a ≠ b ∧ b ≤ a)%L }.

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
    rngl_opt_ord :
      if rngl_is_ordered T then ring_like_ord T
      else not_applicable;
    (* archimedean *)
    rngl_opt_archimedean :
      if (rngl_is_archimedean && rngl_is_ordered T)%bool then
        ∀ a b, (0 < a)%L → ∃ n, (b < rngl_mul_nat a n)%L
      else not_applicable }.

Definition rngl_abs {T} {ro : ring_like_op T} a :=
  if (a ≤? 0)%L then (- a)%L else a.
Definition rngl_min {T} {ro : ring_like_op T} (a b : T) :=
  if (a ≤? b)%L then a else b.
Definition rngl_max {T} {ro : ring_like_op T} (a b : T) :=
  if (a ≤? b)%L then b else a.

Arguments rngl_mul_is_comm T {ro ring_like_prop}.
Arguments rngl_characteristic T {ro ring_like_prop}.
Arguments rngl_is_archimedean T {ro ring_like_prop}.
Arguments rngl_is_integral_domain T {ro ring_like_prop}.
