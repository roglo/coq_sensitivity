(* Ring-like *)
(* Algebraic structures with two operations *)
(* Allows to define all kinds of semirings, rings, fields *)
(* Allows to define semirings, rings, fields, commutative or not,
   with two classes:
     ring_like_op, holding the operations, and
     ring_like_prop, holding their properties.
   In class ring_like_prop, we can set,
     to make a semiring:
        rngl_opt_opp = None
        rngl_opt_inv = None
     to make a ring:
        rngl_opt_opp = Some opp, where opp is the opposite function
        rngl_opt_inv = None
     to make a field:
        rngl_opt_opp = Some opp, where opp is the opposite function
        rngl_opt_inv = Some inv, where opp is the inverse function
   They can be commutative or not by setting rngl_is_comm to true or false.
   There are many other properties that are implemented here or could be
   implemented :
     - algebraically closed or not
     - archimedian or not
     - with decidable equality or not
     - commutative or not
     - complete or not
     - with some characteristic
     - finite or infinite
     - ordered or not
     - totally ordered or not
     - valuated or not
     - principal or not
     - factorial or not
     - euclidean or not
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
    rngl_opt_opp : option (T → T);
    rngl_opt_inv : option (T → T);
    rngl_opt_sous : option (T → T → T);
    rngl_opt_eucl_div : option ((T → T → T * T) * (T → nat));
    rngl_le : T → T → Prop }.

Declare Scope ring_like_scope.
Delimit Scope ring_like_scope with F.

Definition rngl_has_opp {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_opp.

Definition rngl_has_inv {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_inv.

Definition rngl_has_sous {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_sous.

Definition rngl_has_eucl_div {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_eucl_div.

Definition rngl_opp {T} {R : ring_like_op T} a :=
  match rngl_opt_opp with
  | Some rngl_opp => rngl_opp a
  | None => rngl_zero
  end.

Definition rngl_inv {T} {R : ring_like_op T} a :=
  match rngl_opt_inv with
  | Some rngl_inv => rngl_inv a
  | None => rngl_zero
  end.

Definition rngl_sous {T} {R : ring_like_op T} a b :=
  match rngl_opt_sous with
  | Some rngl_sous => rngl_sous a b
  | None => rngl_zero
  end.

Definition rngl_quo {T} {R : ring_like_op T} a b :=
  match rngl_opt_eucl_div with
  | Some (rngl_eucl_div, rngl_gauge) => fst (rngl_eucl_div a b)
  | None => rngl_zero
  end.

Definition rngl_mod {T} {R : ring_like_op T} a b :=
  match rngl_opt_eucl_div with
  | Some (rngl_eucl_div, rngl_gauge) => snd (rngl_eucl_div a b)
  | None => rngl_zero
  end.

Definition rngl_gauge {T} {R : ring_like_op T} (a : T) :=
  match rngl_opt_eucl_div with
  | Some (rngl_eucl_div, rngl_gauge) => rngl_gauge a
  | None => 0
  end.

Definition rngl_eucl_div {T} {R : ring_like_op T} a b :=
  match rngl_opt_eucl_div with
  | Some (rngl_eucl_div, rngl_gauge) => rngl_eucl_div a b
  | None => (rngl_zero, rngl_zero)
  end.

Definition rngl_sub {T} {R : ring_like_op T} a b :=
  if rngl_has_opp then rngl_add a (rngl_opp b)
  else if rngl_has_sous then rngl_sous a b
  else rngl_zero.
Definition rngl_div {T} {R : ring_like_op T} a b :=
  if rngl_has_inv then rngl_mul a (rngl_inv b)
  else if rngl_has_eucl_div then rngl_quo a b
  else rngl_zero.

Notation "0" := rngl_zero : ring_like_scope.
Notation "1" := rngl_one : ring_like_scope.
Notation "a + b" := (rngl_add a b) : ring_like_scope.
Notation "a - b" := (rngl_sub a b) : ring_like_scope.
Notation "a * b" := (rngl_mul a b) : ring_like_scope.
Notation "a / b" := (rngl_div a b) : ring_like_scope.
Notation "a ≤ b" := (rngl_le a b) : ring_like_scope.
Notation "- a" := (rngl_opp a) : ring_like_scope.
Notation "¹/ a" := (rngl_inv a) (at level 35, right associativity) :
  ring_like_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c)%F (at level 70, b at next level) :
  ring_like_scope.

Notation "- 1" := (rngl_opp rngl_one) : ring_like_scope.

Inductive not_applicable := NA.

Fixpoint rngl_of_nat {T} {ro : ring_like_op T} n :=
  match n with
  | 0 => 0%F
  | S n' => (1 + rngl_of_nat n')%F
  end.

Class ring_like_prop T {ro : ring_like_op T} :=
  { rngl_is_comm : bool;
    rngl_has_dec_eq : bool;
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
    (* when has sous *)
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
      if rngl_has_inv then ∀ a : T, a ≠ 0%F → (¹/ a * a = 1)%F
      else not_applicable;
    rngl_opt_mul_inv_r :
      if (rngl_has_inv && negb rngl_is_comm)%bool then
        ∀ a : T, a ≠ 0%F → (a / a = 1)%F
      else not_applicable;
    (* property of the euclidean division *)
    rngl_opt_eucl_div_prop :
      if rngl_has_eucl_div then
        ∀ a b q r,
        b ≠ 0%F
        → rngl_eucl_div a b = (q, r)
         → a = (b * q + r)%F ∧ rngl_gauge r < rngl_gauge b
      else not_applicable;
    rngl_opt_gauge_prop :
      if rngl_has_eucl_div then
        ∀ a b, a ≠ 0%F → b ≠ 0%F →
        rngl_gauge a ≤ rngl_gauge (a * b)%F ∧
        rngl_gauge b ≤ rngl_gauge (a * b)%F
      else
        not_applicable;
    (* when equality is decidable *)
    rngl_opt_eq_dec :
      if rngl_has_dec_eq then ∀ a b : T, {a = b} + {a ≠ b}
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
      match rngl_characteristic with
      | 0 => ∀ i, rngl_of_nat (S i) ≠ 0%F
      | n => rngl_of_nat n = 0%F
      end;
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
      else not_applicable;
    (* consistency *)
    rngl_consistent :
      rngl_has_inv = false ∨ rngl_has_eucl_div = false }.

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
  ∀ a : T, a ≠ 0%F → (¹/ a * a = 1)%F.
Proof.
intros H1 *.
specialize rngl_opt_mul_inv_l as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_eq_dec : rngl_has_dec_eq = true → ∀ a b : T, {a = b} + {a ≠ b}.
Proof.
intros Hde *.
specialize rngl_opt_eq_dec as H.
rewrite Hde in H.
apply H.
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
unfold rngl_sub.
now rewrite Hro.
Qed.

Theorem rngl_sub_diag :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a, (a - a = 0)%F.
Proof.
intros Hom *.
remember rngl_has_opp as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_add_comm.
  now apply rngl_add_opp_l.
}
remember rngl_has_sous as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 0%F a).
  now rewrite rngl_add_0_l in H1.
}
now destruct Hom.
Qed.

Theorem rngl_add_sub :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b, (a + b - b = a)%F.
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
remember rngl_has_sous as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  apply H1.
}
now destruct Hom.
Qed.

Theorem rngl_add_cancel_l :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b c, (a + b = a + c)%F → (b = c)%F.
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
  rewrite rngl_sub_diag in Habc; [ | now rewrite Hop ].
  now do 2 rewrite rngl_add_0_r in Habc.
}
remember rngl_has_sous as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 c a) as H2.
  rewrite rngl_add_comm, <- Habc in H2.
  rewrite rngl_add_comm in H2.
  now rewrite H1 in H2.
}
now destruct Hom.
Qed.

Theorem rngl_add_sub_eq_l :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b c, (a + b = c → c - a = b)%F.
Proof.
intros Hom * Hab.
rewrite <- Hab.
rewrite rngl_add_comm.
now apply rngl_add_sub.
Qed.

Theorem rngl_add_sub_eq_r :
  rngl_has_opp = true ∨ rngl_has_sous = true →
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

Theorem rngl_add_reg_r :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b c, (a + c = b + c)%F → (a = b)%F.
Proof.
intros Hom * Habc.
eapply rngl_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rngl_add_sub in Habc.
Qed.

Theorem rngl_mul_0_r :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a, (a * 0 = 0)%F.
Proof.
intros Hom *.
apply (rngl_add_reg_r Hom _ _ (a * 1)%F).
rewrite <- rngl_mul_add_distr_l.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_add_move_0_r :
  rngl_has_opp = true →
  ∀ a b, (a + b = 0)%F ↔ (a = - b)%F.
Proof.
intros Hro *.
split; intros H. {
  apply rngl_sub_compat_l with (c := b) in H.
  rewrite rngl_add_sub in H; [ | now left ].
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
  ∀ a b, (a * - b = - (a * b))%F.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_l a b (- b)%F) as H.
rewrite fold_rngl_sub in H; [ | easy ].
rewrite rngl_sub_diag in H; [ | now left ].
rewrite rngl_mul_0_r in H; [ | now left ].
symmetry in H.
rewrite rngl_add_comm in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_l :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b c, (a * (b - c) = a * b - a * c)%F.
Proof.
intros Hom *.
remember rngl_has_opp as op eqn:Hop; symmetry in Hop.
destruct op. {
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_mul_add_distr_l.
  now rewrite rngl_mul_opp_r.
}
remember rngl_has_sous as mo eqn:Hmo; symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_mul_sub_distr_l as H1.
  now rewrite Hmo in H1.
}
now destruct Hom.
Qed.

Theorem rngl_integral :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  (rngl_is_integral || (rngl_has_inv && rngl_has_dec_eq))%bool = true →
  ∀ a b, (a * b = 0)%F → a = 0%F ∨ b = 0%F.
Proof.
intros Hmo Hdo * Hab.
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral; [ now apply rngl_integral | ].
remember rngl_has_inv as iv eqn:Hiv; symmetry in Hiv.
destruct iv; [ | easy ].
remember rngl_has_dec_eq as de eqn:Hde; symmetry in Hde.
destruct de; [ | easy ].
cbn; clear rngl_integral.
assert (H : (¹/a * a * b = ¹/a * 0)%F). {
  now rewrite <- rngl_mul_assoc, Hab.
}
rewrite rngl_mul_0_r in H; [ | easy ].
destruct (rngl_eq_dec Hde a 0%F) as [Haz| Haz]; [ now left | ].
rewrite rngl_mul_inv_l in H; [ | easy | easy ].
rewrite rngl_mul_1_l in H.
now right.
Qed.

Theorem rngl_sub_move_0_r :
  rngl_has_opp = true →
  ∀ a b : T, (a - b)%F = 0%F → a = b.
Proof.
intros Hop * Hab.
apply (rngl_add_compat_r _ _ b) in Hab.
unfold rngl_sub in Hab.
rewrite Hop in Hab.
rewrite <- rngl_add_assoc in Hab.
rewrite rngl_add_opp_l in Hab; [ | easy ].
now rewrite rngl_add_0_r, rngl_add_0_l in Hab.
Qed.

(* exist in Arith, but by principle I don't want Import Arith in the
   present module *)
Theorem Nat_nlt_ge : ∀ a b, a ≤ b → not (b < a).
Proof.
intros * Hab Hba.
revert b Hab Hba.
induction a; intros; [ easy | ].
destruct b; [ easy | ].
apply le_S_n in Hab.
apply le_S_n in Hba.
now apply IHa in Hab.
Qed.

Theorem rngl_mul_inv_r :
  rngl_has_inv = true ∨
  (rngl_has_eucl_div = true ∧ rngl_has_opp = true ∧
   rngl_has_dec_eq = true ∧ rngl_is_integral = true) →
  ∀ a : T, a ≠ 0%F → (a / a = 1)%F.
Proof.
intros Hii * Haz.
remember rngl_has_inv as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  specialize rngl_opt_mul_inv_r as rngl_mul_inv_r.
  remember rngl_is_comm as ic eqn:Hic.
  symmetry in Hic.
  destruct ic. {
    unfold rngl_div.
    rewrite Hiv.
    rewrite rngl_mul_comm; [ | easy ].
    now apply rngl_mul_inv_l.
  } {
    rewrite Hiv in rngl_mul_inv_r.
    cbn in rngl_mul_inv_r.
    now apply rngl_mul_inv_r.
  }
} {
  destruct Hii as [Hii| Hii]; [ easy | ].
  specialize rngl_opt_eucl_div_prop as H1.
  specialize rngl_opt_gauge_prop as H2.
  unfold rngl_div, rngl_quo.
  destruct Hii as (Hii & Hop & Heq & Hit).
  rewrite Hii in H1, H2 |-*.
  rewrite Hiv.
  unfold rngl_has_eucl_div in Hii.
  unfold rngl_gauge in H1, H2.
  unfold rngl_eucl_div in H1.
  remember rngl_opt_eucl_div as ed eqn:Hed; symmetry in Hed.
  destruct ed as [(fdiv, fgauge)| ]; [ | easy ].
  specialize (H1 a a) as H3.
  remember (fdiv a a) as qr eqn:Hqr.
  symmetry in Hqr.
  destruct qr as (q, r); cbn.
  specialize (H3 q r Haz eq_refl).
  destruct H3 as (Haa, Hgg).
  symmetry in Haa.
  apply rngl_add_sub_eq_l in Haa; [ | now left ].
  remember (a * q)%F as x.
  replace a with (a * 1)%F in Haa by apply rngl_mul_1_r; subst x.
  rewrite <- rngl_mul_sub_distr_l in Haa; [ | now left ].
  specialize rngl_opt_eq_dec as H3.
  rewrite Heq in H3.
  specialize (H2 a (1 - q)%F Haz).
  specialize (H3 (1 - q)%F 0%F).
  destruct H3 as [H3| H3]. {
    now apply rngl_sub_move_0_r in H3.
  }
  specialize (H2 H3).
  rewrite Haa in H2.
  destruct H2 as (H2, H4).
  move H2 at bottom.
  move Hgg at bottom.
  exfalso.
  revert Hgg.
  now apply Nat_nlt_ge.
}
Qed.

Theorem fold_rngl_div :
  rngl_has_inv = true →
  ∀ a b, (a * ¹/ b)%F = (a / b)%F.
Proof.
intros Hin *.
unfold rngl_div.
now rewrite Hin.
Qed.

Theorem rngl_mul_div_l :
  rngl_has_inv = true ∨
  (rngl_has_eucl_div = true ∧ rngl_is_comm = true ∧
   rngl_has_opp = true ∧ rngl_has_dec_eq = true) →
  ∀ a b : T, b ≠ 0%F → (a * b / b)%F = a.
Proof.
intros Hii a b Hbz.
remember rngl_has_inv as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  unfold rngl_div.
  rewrite Hiv.
  rewrite <- rngl_mul_assoc.
  rewrite fold_rngl_div; [ | easy ].
  rewrite rngl_mul_inv_r; [ | now left | easy ].
  apply rngl_mul_1_r.
} {
  destruct Hii as [Hii| Hii]; [ easy | ].
  specialize rngl_opt_eucl_div_prop as H1.
  specialize rngl_opt_gauge_prop as H2.
  unfold rngl_div, rngl_quo.
  destruct Hii as (Hii & Hco & Hop & Heq).
  rewrite Hii in H1, H2 |-*.
  rewrite Hiv.
  unfold rngl_has_eucl_div in Hii.
  unfold rngl_gauge in H1, H2.
  unfold rngl_eucl_div in H1.
  remember rngl_opt_eucl_div as ed eqn:Hed; symmetry in Hed.
  destruct ed as [(fdiv, fgauge)| ]; [ | easy ].
  specialize (H1 (a * b)%F b) as H3.
  remember (fdiv (a * b)%F b) as qr eqn:Hqr.
  symmetry in Hqr.
  destruct qr as (q, r); cbn.
  specialize (H3 q r Hbz eq_refl).
  destruct H3 as (Haa, Hgg).
  symmetry in Haa.
  apply rngl_add_sub_eq_l in Haa; [ | now left ].
  rewrite rngl_mul_comm in Haa; [ | easy ].
  rewrite <- rngl_mul_sub_distr_l in Haa; [ | now left ].
  specialize rngl_opt_eq_dec as H3.
  rewrite Heq in H3.
  specialize (H2 b (a - q)%F Hbz).
  specialize (H3 (a - q)%F 0%F).
  destruct H3 as [H3| H3]. {
    now apply rngl_sub_move_0_r in H3.
  }
  specialize (H2 H3).
  rewrite Haa in H2.
  destruct H2 as (H2, H4).
  move H2 at bottom.
  move Hgg at bottom.
  exfalso.
  revert Hgg.
  now apply Nat_nlt_ge.
}
Qed.

Theorem rngl_mul_cancel_l :
  rngl_has_inv = true ∨
    rngl_has_eucl_div = true ∧ rngl_is_comm = true ∧ rngl_has_opp = true ∧
    rngl_has_dec_eq = true →
  ∀ a b c, a ≠ 0%F
  → (a * b = a * c)%F
  → b = c.
Proof.
intros Hii * Haz Hbc.
destruct Hii as [Hii| Hii]. {
  assert (H2 : (¹/ a * (a * b) = ¹/ a * (a * c))%F) by now rewrite Hbc.
  do 2 rewrite rngl_mul_assoc in H2.
  rewrite rngl_mul_inv_l in H2; [ | easy | easy ].
  now do 2 rewrite rngl_mul_1_l in H2.
} {
  assert (H : (a * b / a = a * c / a)%F) by now rewrite Hbc.
  specialize (rngl_mul_div_l (or_intror Hii)) as H1.
  rewrite rngl_mul_comm in H; [ | easy ].
  rewrite H1 in H; [ | easy ].
  rewrite rngl_mul_comm in H; [ | easy ].
  now rewrite H1 in H.
}
Qed.

Theorem rngl_mul_cancel_r :
  rngl_has_inv = true ∨
    rngl_has_eucl_div = true ∧ rngl_is_comm = true ∧ rngl_has_opp = true ∧
    rngl_has_dec_eq = true →
  ∀ a b c, c ≠ 0%F
  → (a * c = b * c)%F
  → a = b.
Proof.
intros Hii * Hcz Hab.
assert (H : (a * c / c = b * c / c)%F) by now rewrite Hab.
rewrite rngl_mul_div_l in H; [ | easy | easy ].
rewrite rngl_mul_div_l in H; [ | easy | easy ].
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
  (¹/ (if c then a else b) = if c then ¹/ a else ¹/ b)%F.
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
now apply rngl_sub_diag; left.
Qed.

Theorem rngl_sub_0_r :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a, (a - 0 = a)%F.
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
remember rngl_has_sous as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 a 0%F) as H2.
  now rewrite rngl_add_0_r in H2.
}
now destruct Hom.
Qed.

Theorem rngl_opp_add_distr :
  rngl_has_opp = true →
  ∀ a b, (- (a + b) = - b - a)%F.
Proof.
intros Hro *.
apply rngl_add_cancel_l with (a := (a + b)%F); [ now left | ].
rewrite (fold_rngl_sub Hro).
rewrite rngl_sub_diag; [ | now left ].
unfold rngl_sub.
rewrite Hro.
rewrite rngl_add_assoc.
do 2 rewrite (fold_rngl_sub Hro).
rewrite rngl_add_sub; [ | now left ].
symmetry.
now apply rngl_sub_diag; left.
Qed.

Theorem rngl_add_sub_simpl_l :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b c : T, (a + b - (a + c) = b - c)%F.
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
  rewrite rngl_sub_diag, rngl_add_0_l; [ easy | now left ].
}
remember rngl_has_sous as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_sub_sub_add as H1.
  rewrite Hmo in H1.
  rewrite <- H1.
  rewrite rngl_add_comm.
  rewrite rngl_add_sub; [ easy | ].
  destruct Hom as [Hom| Hom]; [ easy | ].
  now right.
}
now destruct Hom.
Qed.

Theorem rngl_mul_0_l :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a, (0 * a = 0)%F.
Proof.
intros Hom a.
apply (rngl_add_reg_r Hom _ _ (1 * a)%F).
rewrite <- rngl_mul_add_distr_r.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_inv_1 :
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  (¹/ 1 = 1)%F.
Proof.
intros Hin H10.
specialize rngl_mul_inv_r as H.
unfold rngl_div in H.
rewrite Hin in H.
transitivity (1 * ¹/ 1)%F. {
  symmetry.
  apply rngl_mul_1_l.
}
apply H; [ now left | ].
now apply rngl_1_neq_0.
Qed.

Theorem rngl_div_1_l :
  rngl_has_inv = true →
  ∀ a, (1 / a = ¹/ a)%F.
Proof.
intros Hin *.
unfold rngl_div.
rewrite Hin.
apply rngl_mul_1_l.
Qed.

Theorem rngl_div_1_r :
  rngl_has_inv = true ∨
    rngl_has_eucl_div = true ∧ rngl_is_comm = true ∧ rngl_has_opp = true ∧
    rngl_has_dec_eq = true →
  rngl_has_1_neq_0 = true →
  ∀ a, (a / 1 = a)%F.
Proof.
intros Hid H10 *.
specialize (rngl_mul_div_l Hid a 1%F (rngl_1_neq_0 H10)) as H1.
now rewrite rngl_mul_1_r in H1.
Qed.

Theorem rngl_mul_move_1_r :
  rngl_has_inv = true → ∀ a b : T, b ≠ 0%F → (a * b)%F = 1%F ↔ a = (¹/ b)%F.
Proof.
intros Hin * Hbz.
split; intros H. {
  apply rngl_div_compat_l with (c := b) in H; [ | easy | easy ].
  unfold rngl_div in H.
  rewrite Hin in H.
  rewrite <- rngl_mul_assoc in H.
  rewrite fold_rngl_div in H; [ | easy ].
  rewrite rngl_mul_inv_r in H; [ | now left | easy ].
  now rewrite rngl_mul_1_r, rngl_mul_1_l in H.
} {
  rewrite H.
  specialize (rngl_mul_inv_l Hin) as H1.
  now apply H1.
}
Qed.

Theorem rngl_opp_involutive :
  rngl_has_opp = true →
  ∀ x, (- - x)%F = x.
Proof.
intros Hro *.
symmetry.
specialize (rngl_sub_diag (or_introl Hro)) as H.
unfold rngl_sub in H.
rewrite Hro in H.
now apply rngl_add_move_0_r.
Qed.

Theorem rngl_inv_neq_0 :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  ∀ a, a ≠ 0%F → (¹/ a ≠ 0)%F.
Proof.
intros Hom Hin H10 * Haz H1.
symmetry in H1.
apply rngl_mul_move_1_r in H1; [ | easy | easy ].
rewrite rngl_mul_0_l in H1; [ | easy ].
symmetry in H1; revert H1.
now apply rngl_1_neq_0.
Qed.

Theorem rngl_inv_involutive :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  ∀ x, x ≠ 0%F → (¹/ ¹/ x)%F = x.
Proof.
intros Hom Hin H10 * Hxz.
symmetry.
specialize (rngl_mul_inv_r (or_introl Hin)) as H.
unfold rngl_div in H.
rewrite Hin in H.
specialize (rngl_mul_move_1_r Hin) as H1.
apply H1. 2: {
  rewrite fold_rngl_div; [ | easy ].
  apply rngl_mul_inv_r; [ now left | easy ].
}
now apply rngl_inv_neq_0.
Qed.

Theorem rngl_mul_opp_l :
  rngl_has_opp = true →
  ∀ a b, (- a * b = - (a * b))%F.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_r (- a)%F a b) as H.
rewrite rngl_add_opp_l in H; [ | easy ].
rewrite rngl_mul_0_l in H; [ | now left ].
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
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  ∀ a b, a ≠ 0%F → b ≠ 0%F →(¹/ a = ¹/ b)%F → a = b.
Proof.
intros Hom Hin H10 * Haz Hbz H.
rewrite <- (rngl_inv_involutive Hom Hin H10 a); [ | easy ].
rewrite H.
now apply rngl_inv_involutive.
Qed.

Theorem rngl_inv_mul_distr :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_integral = true →
  rngl_has_inv = true →
  ∀ a b, a ≠ 0%F → b ≠ 0%F →(¹/ (a * b) = ¹/ b * ¹/ a)%F.
Proof.
intros Hom Hdo Hin * Haz Hbz.
specialize rngl_mul_cancel_l as H1.
specialize rngl_mul_inv_r as H2.
specialize (rngl_integral Hom) as H3.
unfold rngl_div in H2.
rewrite Hdo in H3; cbn in H3.
specialize (H3 eq_refl).
assert (Habz : (a * b)%F ≠ 0%F). {
  intros H.
  specialize (H3 a b H).
  now destruct H3.
}
rewrite Hin in H2.
specialize (H2 (or_introl eq_refl)).
apply H1 with (a := (a * b)%F); [ now left | easy | ].
rewrite H2; [ | easy ].
rewrite rngl_mul_assoc.
rewrite <- (rngl_mul_assoc a).
rewrite H2; [ | easy ].
rewrite rngl_mul_1_r.
now rewrite H2.
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
unfold rngl_sub at 1.
rewrite Hro.
rewrite rngl_opp_add_distr; [ | easy ].
now rewrite rngl_opp_involutive.
Qed.

Theorem rngl_sub_add_distr :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b c, (a - (b + c) = a - b - c)%F.
Proof.
intros Hom *.
remember rngl_has_opp as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite rngl_opp_add_distr; [ | easy ].
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  apply rngl_add_add_swap.
}
remember rngl_has_sous as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_sub_sub_add as H1.
  now rewrite Hmo in H1.
}
now destruct Hom.
Qed.

Theorem rngl_sub_sub_distr :
  rngl_has_opp = true →
  ∀ a b c, (a - (b - c) = a - b + c)%F.
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
  rngl_has_opp = true ∨ rngl_has_sous = true →
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
  ∀ a, a ≠ 0%F → (- ¹/ a = ¹/ (- a))%F.
Proof.
intros Hop Hin H10 * Haz.
assert (Hoaz : (- a)%F ≠ 0%F). {
  intros H.
  apply (f_equal rngl_opp) in H.
  rewrite rngl_opp_involutive in H; [ | easy ].
  now rewrite rngl_opp_0 in H.
}
apply (rngl_mul_cancel_l (or_introl Hin) (- a)%F); [ easy | ].
specialize (rngl_opt_mul_inv_r) as H2.
remember rngl_is_comm as ic eqn:Hic; symmetry in Hic.
rewrite Hin in H2; cbn in H2.
rewrite rngl_mul_opp_opp; [ | easy ].
destruct ic. {
  symmetry.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_l; [ | easy | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_l; [ | easy | easy ].
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
  rngl_has_inv = true →
  ∀ x y z, y ≠ 0%F → ((x / y) * (y / z))%F = (x / z)%F.
Proof.
intros Hin * Hs.
unfold rngl_div; rewrite Hin.
rewrite rngl_mul_assoc; f_equal.
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_inv_l; [ | easy| easy ].
apply rngl_mul_1_r.
Qed.

Theorem rngl_div_0_l :
  rngl_has_inv = true ∧ (rngl_has_opp = true ∨ rngl_has_sous = true) ∨
    rngl_has_eucl_div = true ∧ rngl_is_comm = true ∧ rngl_has_opp = true ∧
    rngl_has_dec_eq = true →
  ∀ a, a ≠ 0%F → (0 / a)%F = 0%F.
Proof.
intros Hiv * Haz.
remember (0 / a)%F as x eqn:Hx.
replace 0%F with (0 * a)%F in Hx. 2: {
  apply rngl_mul_0_l.
  destruct Hiv as [Hiv| Hiv]; [ easy | now left ].
}
subst x.
apply rngl_mul_div_l; [ | easy ].
destruct Hiv as [Hiv| Hiv]; [ now left | now right ].
Qed.

Theorem eq_rngl_div_1 :
  rngl_has_inv = true ∨
    rngl_has_eucl_div = true ∧ rngl_has_opp = true ∧ rngl_has_dec_eq = true ∧
    rngl_is_integral = true →
   ∀ a b, b ≠ 0%F → a = b → (a / b = 1)%F.
Proof.
intros Hiv * Hbz Hab.
subst a.
now apply rngl_mul_inv_r.
Qed.

Theorem rngl_mul_sub_distr_r :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b c, ((a - b) * c = a * c - b * c)%F.
Proof.
intros Hom *.
remember rngl_has_opp as op eqn:Hop; symmetry in Hop.
destruct op. {
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_mul_add_distr_r.
  now rewrite rngl_mul_opp_l.
}
remember rngl_has_sous as mo eqn:Hmo; symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_mul_sub_distr_r as H1.
  remember rngl_is_comm as ic eqn:Hic; symmetry in Hic.
  destruct ic. {
    specialize rngl_opt_mul_comm as rngl_mul_comm.
    rewrite Hic in rngl_mul_comm.
    rewrite rngl_mul_comm, rngl_mul_sub_distr_l; [ | now right ].
    now rewrite (rngl_mul_comm a), (rngl_mul_comm b).
  } {
    rewrite Hmo in H1.
    apply H1.
  }
}
now destruct Hom.
Qed.

End a.

Arguments rngl_add_opp_l {T}%type {ro rp} Hro.
Arguments rngl_sub_diag {T}%type {ro rp} Hom a%F.
Arguments rngl_add_cancel_l {T}%type {ro rp} Hom (a b c)%F.
Arguments rngl_add_sub {T}%type {ro rp} Hom (a b)%F.
Arguments rngl_inv_mul_distr {T}%type {ro rp} Hom Hin Hdo a%F b%F.
Arguments rngl_integral {T}%type {ro rp}.
Arguments rngl_mul_opp_opp {T}%type {ro rp} Hro.
Arguments rngl_mul_0_l {T}%type {ro rp} Hom a%F.
Arguments rngl_mul_opp_r {T}%type {ro rp} Hro.
Arguments rngl_mul_cancel_r {T}%type {ro rp} Hii (a b c)%F.
Arguments rngl_mul_0_r {T}%type {ro rp} Hom a%F.
Arguments rngl_opp_0 {T}%type {ro rp}.
Arguments rngl_opp_add_distr {T}%type {ro rp} Hop a%F b%F.
