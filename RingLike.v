(* Ring-like *)
(* Algebraic structures with two operations *)
(* Allows to define all kinds of semirings, rings, fields *)
(* Allows to define semirings, rings, fields, commutative or not,
   with two classes:
     ring_like_op, holding the operations, and
     ring_like_prop, holding their properties.
   In class ring_like_prop, we can set,
     to make a ring:
        ∀ x, rngl_opt_opp x = Some _
        ∃ x, x ≠ 0 ∧ rngl_opt_inv x = None
     to make a field:
        ∀ x, rngl_opt_opp x = Some _
        ∀ x, x = 0 ∨ rngl_opt_inv x = Some _
   They can be commutative or not by setting rngl_is_comm to true or false.
   There are many other properties that are implemented here or could be
   implemented :
     - archimedian or not
     - with decidable equality or not
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
    rngl_opt_opp : T → option T;
    rngl_opt_inv : T → option T;
    rngl_opt_sous : option (T → T → T);
    rngl_opt_quot : option (T → T → T);
    rngl_le : T → T → Prop }.

Declare Scope ring_like_scope.
Delimit Scope ring_like_scope with F.

Definition map_option {T} d (x : option T) :=
  match x with
  | Some a => a
  | None => d
  end.

Arguments rngl_opt_opp {T}%type {ring_like_op} a%F.
Arguments rngl_opt_inv {T}%type {ring_like_op} a%F.

Definition rngl_opp {T} {R : ring_like_op T} a :=
  map_option rngl_zero (rngl_opt_opp a).
Definition rngl_inv {T} {R : ring_like_op T} a :=
  map_option rngl_zero (rngl_opt_inv a).

Definition rngl_opp_defined {T} {R : ring_like_op T} a :=
  bool_of_option (rngl_opt_opp a).
Definition rngl_inv_defined {T} {R : ring_like_op T} a :=
  bool_of_option (rngl_opt_inv a).

Arguments rngl_opp_defined {T}%type {R} a%F.
Arguments rngl_inv_defined {T}%type {R} a%F.

Definition rngl_is_ring {T} {R : ring_like_op T} :=
  ∀ x, rngl_opp_defined x = true.

Definition rngl_is_field {T} {R : ring_like_op T} :=
  ∀ x, x = rngl_zero ∨ rngl_inv_defined x = true.

Definition rngl_has_sous {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_sous.

Definition rngl_has_quot {T} {R : ring_like_op T} :=
  bool_of_option rngl_opt_quot.

Definition rngl_sous {T} {R : ring_like_op T} a b :=
  match rngl_opt_sous with
  | Some rngl_sous => rngl_sous a b
  | None => rngl_zero
  end.

Definition rngl_quot {T} {R : ring_like_op T} a b :=
  match rngl_opt_quot with
  | Some rngl_quot => rngl_quot a b
  | None => rngl_zero
  end.

Definition rngl_sub {T} {R : ring_like_op T} a b :=
  if rngl_opp_defined b then rngl_add a (rngl_opp b) else rngl_zero.

Definition rngl_div {T} {R : ring_like_op T} a b :=
  if rngl_inv_defined b then rngl_mul a (rngl_inv b) else rngl_zero.

Notation "0" := rngl_zero : ring_like_scope.
Notation "1" := rngl_one : ring_like_scope.
Notation "a + b" := (rngl_add a b) : ring_like_scope.
Notation "a - b" := (rngl_sub a b) : ring_like_scope.
Notation "a * b" := (rngl_mul a b) : ring_like_scope.
Notation "a / b" := (rngl_div a b) : ring_like_scope.
Notation "a ≤ b" := (rngl_le a b) : ring_like_scope.
Notation "- a" := (rngl_opp a) : ring_like_scope.
Notation "a '⁻¹'" := (rngl_inv a) (at level 35, right associativity, format "a ⁻¹") :
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
    (* properties of general opposite and general inverse *)
    rngl_opt_opp_iff :
      ∀ a b, rngl_opt_opp a = Some b ↔ (a + b = 0)%F;
    rngl_opt_inv_l_iff :
      ∀ a b, rngl_opt_inv a = Some b ↔ (b * a = 1)%F;
    rngl_opt_inv_r_iff :
      if rngl_is_comm then not_applicable
      else ∀ a b, rngl_opt_inv a = Some b ↔ (a * b = 1)%F;
    (* when has subtraction (sous) *)
    rngl_opt_add_sub :
      if rngl_has_sous then ∀ a b, (a + b - b)%F = a
      else not_applicable;
    rngl_opt_sub_sub_sub_add :
      if rngl_has_sous then ∀ a b c, ((a - b) - c = a - (b + c))%F
      else not_applicable;
(*
    rngl_opt_mul_sub_distr_l :
      if rngl_has_sous then ∀ a b c : T, (a * (b - c) = a * b - a * c)%F
      else not_applicable;
    rngl_opt_mul_sub_distr_r :
      if rngl_has_sous then
        if rngl_is_comm then not_applicable
        else ∀ a b c : T, ((a - b) * c = a * c - b * c)%F
      else not_applicable;
*)
    (* when has inverse *)
    rngl_opt_mul_inv_l :
      ∀ a, if rngl_inv_defined a then (a⁻¹ * a = 1)%F else not_applicable;
    rngl_opt_mul_inv_r :
      ∀ a,
      if (rngl_inv_defined a && negb rngl_is_comm)%bool then (a / a = 1)%F
      else not_applicable;
    (* when has division (quot) *)
    rngl_opt_mul_quot_l :
      if rngl_has_quot then
        ∀ a b, a ≠ 0%F → (a * b / a)%F = b
      else not_applicable;
    rngl_opt_mul_quot_r :
      if (rngl_has_quot && negb rngl_is_comm)%bool then
        ∀ a b, b ≠ 0%F → (a * b / b)%F = a
      else not_applicable;
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
      if rngl_is_ordered then
        ∀ a b c d, (0 ≤ a ≤ c)%F → (0 ≤ b ≤ d)%F → (a * b ≤ c * d)%F
      else not_applicable;
    rngl_opt_mul_le_compat_nonpos :
      if rngl_is_ordered then
        ∀ a b c d, (c ≤ a ≤ 0)%F → (d ≤ b ≤ 0)%F → (a * b ≤ c * d)%F
      else not_applicable;
    rngl_opt_mul_le_compat :
      if rngl_is_ordered then
        ∀ a b c d, (a ≤ c)%F → (b ≤ d)%F → (a * b ≤ c * d)%F
      else not_applicable;
    rngl_opt_not_le :
      if rngl_is_ordered then
        ∀ a b, (¬ a ≤ b → a = b ∨ b ≤ a)%F
      else not_applicable;
    (* consistency *)
    rngl_consistent : not_applicable }.

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

Theorem rngl_add_opp_l : ∀ a,
  rngl_opp_defined a = true →
  (- a + a = 0)%F.
Proof.
intros * H1.
rewrite rngl_add_comm.
apply rngl_opt_opp_iff.
unfold rngl_opp_defined in H1.
remember (rngl_opt_opp a) as b eqn:Hb.
symmetry in Hb.
destruct b as [b| ]; [ | easy ].
clear H1.
unfold rngl_opp.
now rewrite Hb.
Qed.

Theorem rngl_add_opp_r : ∀ a,
  rngl_opp_defined a = true →
  (a + - a = 0)%F.
Proof.
intros * H1.
rewrite rngl_add_comm.
now apply rngl_add_opp_l.
Qed.

Theorem rngl_sub_diag : ∀ a,
  rngl_opp_defined a = true ∨ rngl_has_sous = true →
  (a - a = 0)%F.
Proof.
intros * Hom.
remember (rngl_opp_defined a) as op eqn:Hop.
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

Theorem rngl_mul_inv_l : ∀ a,
  rngl_inv_defined a = true →
  (a⁻¹ * a = 1)%F.
Proof.
intros * H1.
specialize (rngl_opt_mul_inv_l a) as H.
now rewrite H1 in H.
Qed.

Theorem rngl_mul_inv_r : ∀ a,
  rngl_inv_defined a = true →
  (a * a⁻¹ = 1)%F.
Proof.
intros * H1.
remember rngl_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic. {
  specialize (rngl_opt_mul_inv_l a) as H.
  rewrite H1 in H.
  now rewrite rngl_mul_comm in H.
} {
  specialize (rngl_opt_mul_inv_r a) as H.
  rewrite H1, Hic in H; cbn in H.
  unfold rngl_div in H.
  now rewrite H1 in H.
}
Qed.

Theorem fold_rngl_div : ∀ a b,
  rngl_inv_defined b = true →
  (a * b⁻¹)%F = (a / b)%F.
Proof.
intros * Hin.
unfold rngl_div.
now rewrite Hin.
Qed.

Theorem rngl_mul_div_l : ∀ a b,
  rngl_inv_defined b = true ∨ rngl_has_quot = true →
  b ≠ 0%F → (a * b / b)%F = a.
Proof.
intros * Hii Hbz.
remember (rngl_inv_defined b) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  unfold rngl_div.
  rewrite Hiv.
  rewrite <- rngl_mul_assoc.
  rewrite fold_rngl_div; [ | easy ].
  unfold rngl_div; rewrite Hiv.
  rewrite rngl_mul_inv_r; [ | easy ].
  apply rngl_mul_1_r.
} {
  destruct Hii as [Hii| Hii]; [ easy | ].
  remember rngl_is_comm as ic eqn:Hic; symmetry in Hic.
  destruct ic. {
    rewrite rngl_mul_comm; [ | easy ].
    specialize rngl_opt_mul_quot_l as H1.
    rewrite Hii in H1.
    now apply H1.
  } {
    specialize rngl_opt_mul_quot_r as H1.
    rewrite Hii, Hic in H1; cbn in H1.
    now apply H1.
  }
}
Qed.

Theorem rngl_div_diag : ∀ a,
  rngl_inv_defined a = true ∨ rngl_has_quot = true →
  a ≠ 0%F →
  (a / a = 1)%F.
Proof.
intros * Hom Haz.
remember (rngl_inv_defined a) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_div.
  rewrite Hop.
  now apply rngl_mul_inv_r.
}
remember rngl_has_quot as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize (rngl_mul_div_l 1%F a (or_intror Hmo) Haz) as H1.
  now rewrite rngl_mul_1_l in H1.
}
now destruct Hom.
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
  ∀ a b c d, (0 ≤ a ≤ c)%F → (0 ≤ b ≤ d)%F → (a * b ≤ c * d)%F.
Proof.
intros Hor *.
specialize rngl_opt_mul_le_compat_nonneg as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_nonpos :
  rngl_is_ordered = true →
  ∀ a b c d, (c ≤ a ≤ 0)%F → (d ≤ b ≤ 0)%F → (a * b ≤ c * d)%F.
Proof.
intros Hor *.
specialize rngl_opt_mul_le_compat_nonpos as H.
rewrite Hor in H.
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

Theorem fold_rngl_sub : ∀ a b,
  rngl_opp_defined b = true →
  (a + - b)%F = (a - b)%F.
Proof.
intros * Hro.
unfold rngl_sub.
now rewrite Hro.
Qed.

Theorem rngl_add_sub : ∀ a b,
  rngl_opp_defined b = true ∨ rngl_has_sous = true →
  (a + b - b = a)%F.
Proof.
intros * Hom.
remember (rngl_opp_defined b) as op eqn:Hop.
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

Theorem rngl_add_cancel_l : ∀ a b c,
  rngl_opp_defined a = true ∨ rngl_has_sous = true →
  (a + b = a + c)%F → (b = c)%F.
Proof.
intros * Hom Habc.
remember (rngl_opp_defined a) as op eqn:Hop.
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

Theorem rngl_add_sub_eq_l : ∀ a b c,
  rngl_opp_defined a = true ∨ rngl_has_sous = true →
  (a + b = c → c - a = b)%F.
Proof.
intros * Hom Hab.
rewrite <- Hab.
rewrite rngl_add_comm.
now apply rngl_add_sub.
Qed.

Theorem rngl_add_sub_eq_r : ∀ a b c,
  rngl_opp_defined b = true ∨ rngl_has_sous = true →
   (a + b = c → c - b = a)%F.
Proof.
intros * Hom Hab.
apply rngl_add_sub_eq_l; [ easy | ].
now rewrite rngl_add_comm.
Qed.

Theorem rngl_sub_compat_l : ∀ a b c,
  (a = b)%F → (a - c = b - c)%F.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_add_cancel_r : ∀ a b c,
  rngl_opp_defined c = true ∨ rngl_has_sous = true →
  (a + c = b + c)%F → (a = b)%F.
Proof.
intros * Hom Habc.
eapply rngl_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rngl_add_sub in Habc.
Qed.

Theorem rngl_mul_0_r : ∀ a,
  rngl_opp_defined a = true ∨ rngl_has_sous = true →
  (a * 0 = 0)%F.
Proof.
intros * Hom.
apply (rngl_add_cancel_r _ _ (a * 1)%F); [ now rewrite rngl_mul_1_r | ].
rewrite <- rngl_mul_add_distr_l.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_mul_0_l : ∀ a,
  rngl_opp_defined a = true ∨ rngl_has_sous = true →
  (0 * a = 0)%F.
Proof.
intros * Hom.
apply (rngl_add_cancel_r _ _ (1 * a)%F); [ now rewrite rngl_mul_1_l | ].
rewrite <- rngl_mul_add_distr_r.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_add_move_0_r : ∀ a b,
  rngl_opp_defined b = true →
  (a + b = 0)%F ↔ (a = - b)%F.
Proof.
intros * Hro.
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

Theorem rngl_opt_opp_symm : ∀ a b,
  rngl_opt_opp a = Some b
  → rngl_opt_opp b = Some a.
Proof.
intros * Hab.
apply rngl_opt_opp_iff in Hab.
rewrite rngl_add_comm in Hab.
now apply rngl_opt_opp_iff in Hab.
Qed.

Theorem rngl_opt_inv_iff : ∀ a b,
  rngl_opt_inv a = Some b ↔ (a * b = 1)%F ∧ (b * a = 1)%F.
Proof.
intros.
split; intros Hab. {
  split. {
    remember rngl_is_comm as ic eqn:Hic.
    symmetry in Hic.
    destruct ic. {
      rewrite rngl_mul_comm; [ | easy ].
      now apply rngl_opt_inv_l_iff in Hab.
    } {
      specialize rngl_opt_inv_r_iff as H1.
      rewrite Hic in H1.
      now apply H1.
    }
  } {
    now apply rngl_opt_inv_l_iff.
  }
} {
  destruct Hab as (Hab, Hba).
  now apply rngl_opt_inv_l_iff.
}
Qed.

Theorem rngl_opt_inv_symm : ∀ a b,
  rngl_opt_inv a = Some b
  → rngl_opt_inv b = Some a.
Proof.
intros * Hab.
apply rngl_opt_inv_iff in Hab.
now apply rngl_opt_inv_iff.
Qed.

Theorem rngl_opp_defined_opp : ∀ a,
  rngl_opp_defined a = true
  → rngl_opp_defined (- a) = true.
Proof.
intros * Hro.
unfold rngl_opp_defined in Hro |-*.
unfold bool_of_option in Hro |-*.
remember (rngl_opt_opp a) as oa eqn:Hoa.
symmetry in Hoa.
destruct oa as [a'| ]; [ | easy ].
apply rngl_opt_opp_symm in Hoa.
remember (rngl_opt_opp (- a)) as oa eqn:Hoa'.
symmetry in Hoa'.
destruct oa as [a''| ]; [ easy | ].
apply rngl_opt_opp_symm in Hoa.
unfold rngl_opp in Hoa'.
rewrite Hoa in Hoa'.
unfold map_option in Hoa'.
apply rngl_opt_opp_symm in Hoa.
now rewrite Hoa in Hoa'.
Qed.

Theorem rngl_inv_defined_inv : ∀ a,
  rngl_inv_defined a = true
  → rngl_inv_defined (a⁻¹) = true.
Proof.
intros * Hro.
unfold rngl_inv_defined in Hro |-*.
unfold bool_of_option in Hro |-*.
remember (rngl_opt_inv a) as ia eqn:Hia.
symmetry in Hia.
destruct ia as [a'| ]; [ | easy ].
apply rngl_opt_inv_symm in Hia.
remember (rngl_opt_inv (a⁻¹)) as ia eqn:Hia'.
symmetry in Hia'.
destruct ia as [a''| ]; [ easy | ].
apply rngl_opt_inv_symm in Hia.
unfold rngl_inv in Hia'.
rewrite Hia in Hia'.
unfold map_option in Hia'.
apply rngl_opt_inv_symm in Hia.
now rewrite Hia in Hia'.
Qed.

Theorem rngl_opp_add_prop : ∀ a b a' b',
  rngl_opt_opp a = Some a' →
  rngl_opt_opp b = Some b' →
  rngl_opt_opp (a + b) = Some (b' + a')%F.
Proof.
intros * Ha Hb.
apply rngl_opt_opp_iff in Ha.
apply rngl_opt_opp_iff in Hb.
apply rngl_opt_opp_iff.
rewrite rngl_add_assoc.
rewrite <- (rngl_add_assoc a).
now rewrite Hb, rngl_add_0_r.
Qed.

Theorem rngl_inv_mul_prop : ∀ a b a' b',
  rngl_opt_inv a = Some a' →
  rngl_opt_inv b = Some b' →
  rngl_opt_inv (a * b) = Some (b' * a')%F.
Proof.
intros * Ha Hb.
apply rngl_opt_inv_l_iff in Ha.
apply rngl_opt_inv_l_iff in Hb.
apply rngl_opt_inv_l_iff.
rewrite rngl_mul_assoc.
rewrite <- (rngl_mul_assoc b').
rewrite Ha.
now rewrite rngl_mul_1_r.
Qed.

Theorem rngl_opp_involutive : ∀ a,
  rngl_opp_defined a = true →
  (- - a)%F = a.
Proof.
intros * Hro.
symmetry.
specialize (rngl_sub_diag _ (or_introl Hro)) as H.
unfold rngl_sub in H.
rewrite Hro in H.
apply rngl_add_move_0_r; [ | easy ].
now apply rngl_opp_defined_opp.
Qed.

Theorem rngl_div_compat_l : ∀ a b c,
  rngl_inv_defined c = true →
  c ≠ 0%F → (a = b)%F → (a / c = b / c)%F.
Proof.
intros Hin a b c Hcz Hab.
now rewrite Hab.
Qed.

Theorem rngl_mul_move_1_l : ∀ a b,
  rngl_inv_defined a = true → a ≠ 0%F → (a * b)%F = 1%F ↔ b = (a⁻¹)%F.
Proof.
intros * Hin Hbz.
split; intros H. {
  apply rngl_opt_inv_l_iff in H.
  apply rngl_opt_inv_symm in H.
  apply rngl_opt_inv_l_iff in H.
  apply rngl_div_compat_l with (c := a) in H; [ | easy | easy ].
  unfold rngl_div in H.
  rewrite Hin in H.
  rewrite <- rngl_mul_assoc in H.
  rewrite fold_rngl_div in H; [ | easy ].
  rewrite rngl_div_diag in H; [ | now left | easy ].
  now rewrite rngl_mul_1_r, rngl_mul_1_l in H.
} {
  rewrite H.
  now apply rngl_mul_inv_r.
}
Qed.

Theorem rngl_mul_move_1_r : ∀ a b,
  rngl_inv_defined b = true → b ≠ 0%F → (a * b)%F = 1%F ↔ a = (b⁻¹)%F.
Proof.
intros * Hin Hbz.
split; intros H. {
  apply rngl_div_compat_l with (c := b) in H; [ | easy | easy ].
  unfold rngl_div in H.
  rewrite Hin in H.
  rewrite <- rngl_mul_assoc in H.
  rewrite fold_rngl_div in H; [ | easy ].
  rewrite rngl_div_diag in H; [ | now left | easy ].
  now rewrite rngl_mul_1_r, rngl_mul_1_l in H.
} {
  rewrite H.
  now apply rngl_mul_inv_l.
}
Qed.

Theorem neq_a_0_neq_inv_a_0 : ∀ a,
  rngl_inv_defined a = true
  → a ≠ 0%F
  → (a⁻¹)%F ≠ 0%F.
Proof.
intros * Hro Haz.
specialize (rngl_div_diag _ (or_introl Hro) Haz) as H1.
unfold rngl_div in H1.
rewrite Hro in H1.
intros H3.
rewrite H3 in H1.
assert (H2 : (0 * a = 1)%F). {
  apply rngl_opt_inv_l_iff.
  apply rngl_opt_inv_symm.
  now apply rngl_opt_inv_l_iff.
}
generalize H1; intros H5.
apply rngl_opt_inv_l_iff in H5.
assert (Ha1 : a ≠ 1%F). {
  intros H; subst a.
  rewrite rngl_mul_1_l in H1.
  now symmetry in H1.
}
assert (H10 : (1 ≠ 0)%F). {
  intros H.
  rewrite <- H in H5.
  apply rngl_opt_inv_l_iff in H5.
  now rewrite rngl_mul_1_r in H5.
}
move Ha1 before Haz.
assert (H7 : (a * a ≠ 0)%F). {
  intros H7.
  generalize H7; intros H.
  remember a as z in H at 2.
  replace a with (0 + a)%F in H by apply rngl_add_0_l.
  subst z.
  rewrite rngl_mul_add_distr_r in H.
  rewrite H2 in H.
  rewrite H7 in H.
  now rewrite rngl_add_0_r in H.
}
assert (H11 : (0 * (0 * a) = 0)%F). {
  now rewrite H2, rngl_mul_1_r.
}
rewrite rngl_mul_assoc in H11.
assert (Hza : (0 * 0 ≠ a)%F). {
  now intros H; rewrite H in H11.
}
remember (0 * 0)%F as b eqn:Hb.
generalize H11; intros H12.
replace b with (b + 0)%F in H11 by apply rngl_add_0_r.
rewrite rngl_mul_add_distr_r in H11.
rewrite H12, rngl_add_0_l in H11.
congruence.
Qed.

Theorem rngl_eq_mul_1_neq_neq : ∀ a b,
  (a * b = 1)%F
  → a ≠ 0%F
  → b ≠ 0%F.
Proof.
intros * Hab Haz.
generalize Hab; intros H1.
apply rngl_opt_inv_l_iff in H1.
apply rngl_opt_inv_symm in H1.
specialize rngl_mul_move_1_l as H2.
assert (Hro : rngl_inv_defined a = true). {
  apply rngl_opt_inv_l_iff in Hab.
  apply rngl_opt_inv_symm in Hab.
  unfold rngl_inv_defined.
  now rewrite Hab.
}
specialize (proj1 (H2 a b Hro Haz) Hab) as H3.
subst b.
now apply neq_a_0_neq_inv_a_0.
Qed.

Theorem rngl_inv_involutive : ∀ a,
  rngl_inv_defined a = true →
  a ≠ 0%F →
  ((a⁻¹)⁻¹)%F = a.
Proof.
intros * Hro Haz.
specialize (rngl_div_diag _ (or_introl Hro) Haz) as H1.
unfold rngl_div in H1.
rewrite Hro in H1.
symmetry.
apply rngl_mul_move_1_r; [ | | easy ]. {
  now apply rngl_inv_defined_inv.
}
now apply neq_a_0_neq_inv_a_0.
Qed.

Theorem rngl_opp_defined_mul : ∀ a b,
  rngl_opp_defined a = true →
  rngl_opp_defined b = true →
  rngl_opp_defined (a * b) = true.
Proof.
intros * Ha Hb.
specialize (rngl_mul_add_distr_r (- a)%F a b) as H.
rewrite rngl_add_opp_l in H; [ | easy ].
rewrite rngl_mul_0_l in H; [ | now left ].
symmetry in H.
rewrite rngl_add_comm in H.
apply rngl_opt_opp_iff in H.
unfold rngl_opp_defined.
now rewrite H.
Qed.

Theorem rngl_mul_opp_l : ∀ a b,
  rngl_opp_defined a = true →
  rngl_opp_defined b = true →
  ((- a) * b = - (a * b))%F.
Proof.
intros * Ha Hb.
specialize (rngl_mul_add_distr_r (- a)%F a b) as H.
rewrite rngl_add_opp_l in H; [ | easy ].
rewrite rngl_mul_0_l in H; [ | now left ].
symmetry in H.
apply rngl_add_move_0_r in H; [ easy | ].
now apply rngl_opp_defined_mul.
Qed.

Theorem rngl_opp_mul_prop : ∀ a b a' b',
  rngl_opt_opp a = Some a' →
  rngl_opt_opp b = Some b' →
  (a * b = a' * b')%F.
Proof.
intros * Ha Hb.
generalize Ha; intros Haa.
generalize Hb; intros Hbb.
apply rngl_opt_opp_iff in Ha.
apply rngl_opt_opp_iff in Hb.
(*
generalize Ha; intros Haaz.
generalize Hb; intros Hbbz.
apply rngl_add_move_0_r in Ha. 2: {
  unfold rngl_opp_defined.
  rewrite rngl_add_comm in Ha.
  apply rngl_opt_opp_iff in Ha.
  now rewrite Ha.
}
apply rngl_add_move_0_r in Hb. 2: {
  unfold rngl_opp_defined.
  rewrite rngl_add_comm in Hb.
  apply rngl_opt_opp_iff in Hb.
  now rewrite Hb.
}
rewrite Ha, Hb.
*)
specialize (rngl_add_sub (a * b - a' * b')%F (a' * b)%F) as H1.
assert (Ha'b : rngl_opp_defined (a' * b) = true). {
  specialize (rngl_opp_defined_mul a' b) as H2.
  assert (H : rngl_opp_defined a' = true). {
    unfold rngl_opp_defined.
    apply rngl_opt_opp_symm in Haa.
    now rewrite Haa.
  }
  specialize (H2 H); clear H.
  assert (H : rngl_opp_defined b = true). {
    unfold rngl_opp_defined.
    now rewrite Hbb.
  }
  now specialize (H2 H); clear H.
}
assert (Ha'b' : rngl_opp_defined (a' * b') = true). {
  specialize (rngl_opp_defined_mul a' b') as H2.
  assert (H : rngl_opp_defined a' = true). {
    unfold rngl_opp_defined.
    apply rngl_opt_opp_symm in Haa.
    now rewrite Haa.
  }
  specialize (H2 H); clear H.
  assert (H : rngl_opp_defined b' = true). {
    unfold rngl_opp_defined.
    apply rngl_opt_opp_symm in Hbb.
    now rewrite Hbb.
  }
  now specialize (H2 H); clear H.
}
specialize (H1 (or_introl Ha'b)).
unfold rngl_sub in H1 at 1.
rewrite Ha'b in H1.
rewrite rngl_add_add_swap in H1.
unfold rngl_sub in H1 at 1.
rewrite Ha'b' in H1.
rewrite <- (rngl_add_assoc (a * b)%F) in H1.
rewrite <- rngl_mul_opp_l in H1; cycle 1. {
  unfold rngl_opp_defined.
  apply rngl_opt_opp_symm in Haa.
  now rewrite Haa.
} {
  unfold rngl_opp_defined.
  apply rngl_opt_opp_symm in Hbb.
  now rewrite Hbb.
}
rewrite <- rngl_mul_opp_l in H1; cycle 1. {
  unfold rngl_opp_defined.
  apply rngl_opt_opp_symm in Haa.
  now rewrite Haa.
} {
  unfold rngl_opp_defined.
  now rewrite Hbb.
}
rewrite <- rngl_mul_add_distr_l in H1.
rewrite (rngl_add_comm b'), Hb in H1.
rewrite rngl_mul_0_r in H1. 2: {
  left.
  apply rngl_opp_defined_opp.
  unfold rngl_opp_defined.
  apply rngl_opt_opp_symm in Haa.
  now rewrite Haa.
}
rewrite rngl_add_0_r in H1.
rewrite <- rngl_mul_add_distr_r in H1.
rewrite Ha in H1.
rewrite rngl_mul_0_l in H1. 2: {
  left.
  unfold rngl_opp_defined.
  now rewrite Hbb.
}
symmetry in H1.
unfold rngl_sub in H1.
rewrite Ha'b' in H1.
apply rngl_add_move_0_r in H1. 2: {
  now apply rngl_opp_defined_opp.
}
now rewrite rngl_opp_involutive in H1.
Qed.

Inspect 1.

...

Theorem rngl_opp_mul_prop : ∀ a b a' b',
  rngl_opt_opp a = Some a' →
  rngl_opt_opp b = Some b' →
  rngl_opt_opp (a * b) = Some (a' * b')%F.
Proof.
intros * Ha Hb.
apply rngl_opt_opp_iff in Ha.
apply rngl_opt_opp_iff in Hb.
apply rngl_opt_opp_iff.
specialize (rngl_add_sub (a * b - a' * b')%F (a' * b)%F) as H1.
...
apply rngl_add_move_0_r in Ha. 2: {
  unfold rngl_opp_defined'.
  rewrite rngl_add_comm in Ha.
  apply rngl_opt_opp_iff in Ha.
  now rewrite Ha.
}
apply rngl_add_move_0_r in Hb. 2: {
  unfold rngl_opp_defined'.
  rewrite rngl_add_comm in Hb.
  apply rngl_opt_opp_iff in Hb.
  now rewrite Hb.
}
rewrite Ha, Hb.
Search (_ * - _)%F.
...
assert (Hab : (a * b = a' * b')%F). {
Search (_ + _ = _ + _)%F.
...
assert (Hab : (a * b - a' * b' = 0)%F). {
  specialize (rngl_add_sub (a * b - a' * b')%F (a' * b)%F) as H1.
...

Theorem rngl_mul_opp_r : ∀ a b,
  rngl_opp_defined a = true →
  rngl_opp_defined b = true →
  rngl_opp_defined (a * b) = true →
  (a * - b = - (a * b))%F.
Proof.
intros * Hoa Hob Hab.
...
specialize (rngl_mul_add_distr_l a b (- b)%F) as H.
rewrite fold_rngl_sub in H; [ | easy ].
rewrite rngl_sub_diag in H; [ | now left ].
rewrite rngl_mul_0_r in H; [ | now left ].
symmetry in H.
rewrite rngl_add_comm in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_l : ∀ a b c,
  rngl_opp_defined a = true →
  rngl_opp_defined c = true →
  rngl_opp_defined (a * c) = true →
  (a * (b - c) = a * b - a * c)%F.
Proof.
intros * Hoa Hoc Hac.
unfold rngl_sub.
rewrite Hoc, Hac.
rewrite rngl_mul_add_distr_l.
now rewrite rngl_mul_opp_r.
Qed.

Theorem rngl_mul_inv_r : ∀ a,
  rngl_inv_defined a = true ∨ rngl_has_quot = true →
  a ≠ 0%F →
  (a / a = 1)%F.
Proof.
intros * Hii Haz.
remember (rngl_inv_defined a) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  specialize (rngl_opt_mul_inv_r a) as rngl_mul_inv_r.
  rewrite Hiv in rngl_mul_inv_r.
  cbn in rngl_mul_inv_r.
  remember rngl_is_comm as ic eqn:Hic.
  symmetry in Hic.
  destruct ic. {
    unfold rngl_div.
    rewrite Hiv.
    rewrite rngl_mul_comm; [ | easy ].
    now apply rngl_mul_inv_l.
  } {
    now apply rngl_mul_inv_r.
  }
} {
  destruct Hii as [Hii| Hii]; [ easy | ].
  specialize rngl_opt_mul_quot_l as H1.
  rewrite Hii in H1.
  specialize (H1 a 1%F Haz).
  now rewrite rngl_mul_1_r in H1.
}
Qed.

Theorem rngl_div_0_l : ∀ a,
  (rngl_opp_defined a = true ∨ rngl_has_sous = true) ∧
  (rngl_inv_defined a = true ∨ rngl_has_quot = true) →
  a ≠ 0%F → (0 / a)%F = 0%F.
Proof.
intros * Hiv Haz.
remember (0 / a)%F as x eqn:Hx.
replace 0%F with (0 * a)%F in Hx. 2: {
  now apply rngl_mul_0_l.
}
subst x.
now apply rngl_mul_div_l.
Qed.

Theorem rngl_integral : ∀ a b,
  rngl_is_integral = true ∨
    rngl_inv_defined a = true ∧
    (rngl_opp_defined (a⁻¹) = true ∨ rngl_has_sous = true) →
  (a * b = 0)%F → a = 0%F ∨ b = 0%F.
Proof.
intros * Hc Hab.
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral; [ now apply rngl_integral | ].
clear rngl_integral.
destruct Hc as [Hc| Hc]; [ easy | ].
destruct Hc as (Hid, Hod).
assert (H : (a⁻¹ * a * b = a⁻¹ * 0)%F). {
  now rewrite <- rngl_mul_assoc, Hab.
}
rewrite rngl_mul_inv_l in H; [ | easy ].
rewrite rngl_mul_1_l in H.
rewrite rngl_mul_0_r in H; [ | easy ].
now right.
Qed.

Theorem rngl_sub_move_0_r : ∀ a b,
  rngl_opp_defined b = true →
  (a - b)%F = 0%F → a = b.
Proof.
intros * Hop Hab.
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

Theorem rngl_div_cancel_l : ∀ a b c,
  (a = b)%F → (a / c = b / c)%F.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_mul_cancel_l : ∀ a b c,
  rngl_inv_defined a = true ∨ rngl_has_quot = true →
  a ≠ 0%F
  → (a * b = a * c)%F
  → b = c.
Proof.
intros * Hii Haz Hbc.
destruct Hii as [Hii| Hii]. {
  assert (H2 : (a⁻¹ * (a * b) = a⁻¹ * (a * c))%F) by now rewrite Hbc.
  do 2 rewrite rngl_mul_assoc in H2.
  rewrite rngl_mul_inv_l in H2; [ | easy ].
  now do 2 rewrite rngl_mul_1_l in H2.
} {
  remember rngl_is_comm as ic eqn:Hic; symmetry in Hic.
  eapply rngl_div_cancel_l with (c := a) in Hbc.
  destruct ic. {
    specialize (rngl_mul_comm Hic) as H1.
    rewrite H1 in Hbc.
    rewrite rngl_mul_div_l in Hbc; [ | now right | easy ].
    rewrite H1 in Hbc.
    rewrite rngl_mul_div_l in Hbc; [ easy | now right | easy ].
  } {
    specialize rngl_opt_mul_quot_l as H1.
    rewrite Hii in H1.
    rewrite H1 in Hbc; [ | easy ].
    now rewrite H1 in Hbc.
  }
}
Qed.

Theorem rngl_mul_cancel_r : ∀ a b c,
  rngl_inv_defined c = true ∨ rngl_has_quot = true →
  c ≠ 0%F
  → (a * c = b * c)%F
  → a = b.
Proof.
intros * Hii Hcz Hab.
assert (H : (a * c / c = b * c / c)%F) by now rewrite Hab.
rewrite rngl_mul_div_l in H; [ | easy | easy ].
rewrite rngl_mul_div_l in H; [ | easy | easy ].
easy.
Qed.

Theorem rngl_inv_if_then_else_distr : ∀ (c : bool) a b,
  ((if c then a else b)⁻¹ = if c then a⁻¹ else b⁻¹)%F.
Proof. now destruct c. Qed.

Theorem rngl_mul_if_then_else_distr : ∀ (x : bool) a b c d,
  ((if x then a else b) * (if x then c else d) = if x then a * c else b * d)%F.
Proof. now destruct x. Qed.

Theorem rngl_opp_0 : rngl_opp_defined 0 = true → (- 0 = 0)%F.
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
  rngl_opp_defined 0 = true ∨ rngl_has_sous = true →
  ∀ a, (a - 0 = a)%F.
Proof.
intros Hom *.
remember (rngl_opp_defined 0) as op eqn:Hop.
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

Arguments rngl_opt_opp {T}%type {ring_like_op} a%F.

Theorem rngl_opp_defined_add : ∀ a b a' b',
  rngl_opt_opp a = Some a'
  → rngl_opt_opp b = Some b'
  → rngl_opt_opp (a + b) = Some (b' + a')%F.
Proof.
intros * Ha Hb.
assert (Haa : (a + a' = 0)%F). {
  assert (a - (- a') = 0)%F. {
    unfold rngl_sub.
    apply rngl_opt_opp_symm in Ha.
    unfold rngl_opp_defined.
Search (rngl_opt_opp (- _)%F).
Search (rngl_opp_defined (- _)%F).
...
    rewrite Ha; cbn.
    rewrite rngl_add_comm.
Check rngl_add_move_0_r.
    apply rngl_add_move_0_r.
...
  apply rngl_add_move_0_r. {
    apply rngl_opt_opp_symm in Ha.
    unfold rngl_opp_defined.
    now rewrite Ha.
  } {
Search (- _)%F.
...

Theorem rngl_opp_add_distr : ∀ a b,
  rngl_opp_defined a = true →
  rngl_opp_defined b = true →
  (- (a + b) = - b - a)%F.
Proof.
intros * Hoa Hob *.
apply rngl_add_cancel_l with (a := (a + b)%F). {
  left.
  now apply rngl_opp_defined_add.
}
rewrite fold_rngl_sub; [ | now apply rngl_opp_defined_add ].
rewrite rngl_sub_diag; [ | now left; apply rngl_opp_defined_add ].
unfold rngl_sub.
rewrite Hoa.
rewrite rngl_add_assoc.
rewrite fold_rngl_sub; [ | easy ].
rewrite fold_rngl_sub; [ | easy ].
rewrite rngl_add_sub; [ | now left ].
symmetry.
now apply rngl_sub_diag; left.
Qed.

Theorem rngl_add_sub_simpl_l : ∀ a b c,
  rngl_opp_defined a = true →
  rngl_opp_defined c = true →
  (a + b - (a + c) = b - c)%F.
Proof.
intros * Hoa Hoc.
unfold rngl_sub.
rewrite Hoc.
rewrite rngl_opp_defined_add; [ | easy | easy ].
rewrite rngl_opp_add_distr; [ | easy | easy ].
unfold rngl_sub; rewrite Hoa.
rewrite rngl_add_assoc.
rewrite rngl_add_add_swap.
rewrite (rngl_add_add_swap a).
rewrite fold_rngl_sub; [ | easy ].
rewrite fold_rngl_sub; [ | easy ].
rewrite fold_rngl_sub; [ | easy ].
rewrite rngl_sub_diag, rngl_add_0_l; [ easy | now left ].
Qed.

Theorem rngl_inv_1 :
  rngl_inv_defined 1 = true →
  rngl_has_1_neq_0 = true →
  (1⁻¹ = 1)%F.
Proof.
intros Hin H10.
specialize rngl_mul_inv_r as H.
unfold rngl_div in H.
transitivity (1 * 1⁻¹)%F. {
  symmetry.
  apply rngl_mul_1_l.
}
specialize (H 1%F (or_introl Hin)).
rewrite Hin in H.
apply H.
now apply rngl_1_neq_0.
Qed.

Theorem rngl_div_1_l : ∀ a,
  rngl_inv_defined a = true →
  (1 / a = a⁻¹)%F.
Proof.
intros * Hin.
unfold rngl_div.
rewrite Hin.
apply rngl_mul_1_l.
Qed.

Theorem rngl_div_1_r :
  rngl_inv_defined 1 = true ∨ rngl_has_quot = true →
  rngl_has_1_neq_0 = true →
  ∀ a, (a / 1 = a)%F.
Proof.
intros Hid H10 *.
specialize (rngl_mul_div_l a 1%F Hid (rngl_1_neq_0 H10)) as H1.
now rewrite rngl_mul_1_r in H1.
Qed.

Theorem rngl_opp_defined_opp : ∀ a,
  rngl_opp_defined a = true
  → rngl_opp_defined (- a) = true.
Proof.
intros * Hro.
unfold rngl_opp_defined in Hro |-*.
unfold bool_of_option in Hro |-*.
remember (rngl_opt_opp a) as oa eqn:Hoa.
symmetry in Hoa.
destruct oa as [a'| ]; [ | easy ].
apply rngl_opt_opp_symm in Hoa.
remember (rngl_opt_opp (- a)%F) as oa eqn:Hoa'.
symmetry in Hoa'.
destruct oa as [a''| ]; [ easy | ].
apply rngl_opt_opp_symm in Hoa.
unfold rngl_opp in Hoa'.
rewrite Hoa in Hoa'.
unfold map_option in Hoa'.
apply rngl_opt_opp_symm in Hoa.
now rewrite Hoa in Hoa'.
Qed.

Theorem rngl_inv_defined_inv : ∀ a,
  rngl_inv_defined a = true
  → rngl_inv_defined (a⁻¹) = true.
Proof.
intros * Hro.
unfold rngl_inv_defined in Hro |-*.
unfold bool_of_option in Hro |-*.
remember (rngl_opt_inv a) as oa eqn:Hoa.
symmetry in Hoa.
destruct oa as [a'| ]; [ | easy ].
apply rngl_opt_inv_symm in Hoa.
remember (rngl_opt_inv (a⁻¹)%F) as oa eqn:Hoa'.
symmetry in Hoa'.
destruct oa as [a''| ]; [ easy | ].
apply rngl_opt_inv_symm in Hoa.
unfold rngl_inv in Hoa'.
rewrite Hoa in Hoa'.
unfold map_option in Hoa'.
apply rngl_opt_inv_symm in Hoa.
now rewrite Hoa in Hoa'.
Qed.

Theorem rngl_inv_neq_0 : ∀ a,
  rngl_opp_defined a = true ∨ rngl_has_sous = true →
  rngl_inv_defined a = true →
  rngl_has_1_neq_0 = true →
  a ≠ 0%F → (a⁻¹ ≠ 0)%F.
Proof.
intros * Hom Hin H10 Haz H1.
symmetry in H1.
apply rngl_mul_move_1_r in H1; [ | easy | easy ].
rewrite rngl_mul_0_l in H1; [ | easy ].
symmetry in H1; revert H1.
now apply rngl_1_neq_0.
Qed.

Theorem rngl_inv_involutive : ∀ a,
  rngl_opp_defined a = true ∨ rngl_has_sous = true →
  rngl_inv_defined a = true →
  rngl_has_1_neq_0 = true →
  a ≠ 0%F → (a⁻¹⁻¹)%F = a.
Proof.
intros * Hom Hin H10 Hxz.
symmetry.
specialize (rngl_mul_inv_r _ (or_introl Hin) Hxz) as H1.
unfold rngl_div in H1.
rewrite Hin in H1.
specialize (rngl_mul_move_1_r a (a⁻¹)%F) as H2.
assert (H : rngl_inv_defined (a⁻¹) = true). {
  now apply rngl_inv_defined_inv.
}
specialize (H2 H); clear H.
apply H2; [ | easy ].
now apply rngl_inv_neq_0.
Qed.

...

Theorem rngl_mul_opp_l : ∀ a b,
  rngl_is_ring →
  (- a * b = - (a * b))%F.
Proof.
intros * Hr.
specialize (rngl_mul_add_distr_r (- a)%F a b) as H.
rewrite rngl_add_opp_l in H; [ | easy ].
rewrite rngl_mul_0_l in H; [ | now left ].
symmetry in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_opp_opp :
  rngl_is_ring →
  ∀ a b, (- a * - b = a * b)%F.
Proof.
intros Hro *.
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
now apply rngl_opp_involutive.
Qed.

Theorem rngl_opp_inj : ∀ a b,
  rngl_opp_defined a = true →
  rngl_opp_defined b = true →
  (- a = - b)%F → a = b.
Proof.
intros * Hra Hrb Hab.
rewrite <- (rngl_opp_involutive a Hra).
rewrite Hab.
now apply rngl_opp_involutive.
Qed.

Theorem rngl_inv_inj : ∀ a b,
  (rngl_opp_defined a = true ∧ rngl_opp_defined b = true) ∨
   rngl_has_sous = true →
  rngl_inv_defined a = true →
  rngl_inv_defined b = true →
  rngl_has_1_neq_0 = true →
  a ≠ 0%F → b ≠ 0%F →(a⁻¹ = b⁻¹)%F → a = b.
Proof.
intros * Hom Hia Hib H10 Haz Hbz H.
rewrite <- (rngl_inv_involutive a); [ | | easy | easy | easy ]. 2: {
  destruct Hom as [Hom| ]; [ | now right ].
  destruct Hom; now left.
}
rewrite H.
apply rngl_inv_involutive; [ | easy | easy | easy ].
destruct Hom as [Hom| ]; [ | now right ].
destruct Hom; now left.
Qed.

Theorem rngl_inv_mul_distr : ∀ a b,
  rngl_is_ring →
  rngl_inv_defined a = true →
  rngl_inv_defined b = true →
  rngl_inv_defined (a * b) = true →
  a ≠ 0%F → b ≠ 0%F →((a * b)⁻¹ = b⁻¹ * a⁻¹)%F.
Proof.
intros * Hrn Hia Hib Haib Haz Hbz.
apply rngl_mul_cancel_l with (a := b); [ now left | easy | ].
rewrite rngl_mul_assoc.
rewrite (fold_rngl_div b b); [ | easy ].
rewrite rngl_mul_inv_r; [ | now left | easy ].
rewrite rngl_mul_1_l.
apply rngl_mul_cancel_l with (a := a); [ now left | easy | ].
rewrite rngl_mul_assoc.
rewrite (fold_rngl_div a a); [ | easy ].
rewrite rngl_mul_inv_r; [ | now left | easy ].
rewrite fold_rngl_div; [ | easy ].
apply rngl_mul_inv_r; [ now left | ].
intros H; apply rngl_integral in H; [ now destruct H | ].
right.
split; [ easy | now left ].
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

Theorem rngl_opp_sub_distr : ∀ a b,
  rngl_opp_defined a = true →
  rngl_opp_defined b = true →
  (- (a - b) = b - a)%F.
Proof.
intros * Hoa Hob.
unfold rngl_sub at 1.
rewrite Hob.
rewrite rngl_opp_add_distr; [ | easy | ]. 2: {
  now apply rngl_opp_defined_opp.
}
now rewrite rngl_opp_involutive.
Qed.

Theorem rngl_sub_add_distr : ∀ a b c,
  rngl_opp_defined b = true ∧
  rngl_opp_defined c = true ∨
  rngl_has_sous = true →
  (a - (b + c) = a - b - c)%F.
Proof.
intros * Hom.
remember rngl_has_sous as hs eqn:Hhs.
symmetry in Hhs.
destruct hs. {
  specialize rngl_opt_sub_sub_sub_add as H1.
  rewrite Hhs in H1.
  now rewrite H1.
}
destruct Hom as [Hom| ]; [ | easy ].
destruct Hom as (Hob & Hoc).
unfold rngl_sub.
rewrite Hob, Hoc.
rewrite rngl_opp_defined_add; [ | easy | easy ].
rewrite rngl_opp_add_distr; [ | easy | easy ].
unfold rngl_sub; rewrite Hob.
rewrite rngl_add_assoc.
apply rngl_add_add_swap.
Qed.

Theorem rngl_sub_sub_distr : ∀ a b c,
  rngl_opp_defined c = true →
  (a - (b - c) = a - b + c)%F.
Proof.
intros * Hoc.
...
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

Theorem eq_rngl_div_1 :
  rngl_has_inv = true ∨ rngl_has_quot = true →
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
