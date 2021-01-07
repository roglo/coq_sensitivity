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
    rngl_le : T → T → Prop;
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
    (* when has not opposite *)
    rngl_opt_add_sub :
      if rngl_has_opp then not_applicable else ∀ a b : T, (a + b - b = a)%F;
    rngl_opt_mul_0_l :
      if rngl_has_opp then not_applicable else ∀ a, (0 * a = 0)%F;
    rngl_opt_mul_0_r :
      if rngl_has_opp then not_applicable else ∀ a, (a * 0 = 0)%F;
    (* when has inverse *)
    rngl_opt_mul_inv_l :
      if rngl_has_inv then ∀ a : T, a ≠ 0%F → (¹/ a * a = 1)%F
      else not_applicable;
    rngl_opt_mul_inv_r :
      if (rngl_has_inv && negb rngl_is_comm)%bool then
        ∀ a : T, a ≠ 0%F → (a / a = 1)%F
      else not_applicable;
    (* when has no inverse but division *)
    rngl_opt_mul_div_l :
      if rngl_has_no_inv_but_div then
        ∀ a b : T, a ≠ 0%F → (a * b / a = b)%F
      else not_applicable;
    rngl_opt_mul_div_r :
      if (rngl_has_no_inv_but_div && negb rngl_is_comm)%bool then
        ∀ a b : T, b ≠ 0%F → (a * b / b = a)%F
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
      rngl_has_inv = false ∨ rngl_has_no_inv_but_div = false }.

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
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
assert (m * p = p * m)%F as H by apply rngl_mul_comm.
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

Theorem rngl_mul_inv_r :
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  ∀ a : T, a ≠ 0%F → (a / a = 1)%F.
Proof.
intros Hii * Ha.
specialize rngl_opt_mul_inv_l as rngl_mul_inv_l.
specialize rngl_opt_mul_inv_r as rngl_mul_inv_r.
specialize rngl_opt_mul_comm as rngl_mul_comm.
specialize rngl_opt_mul_div_l as rngl_mul_div_l.
unfold rngl_div in rngl_mul_inv_r, rngl_mul_div_l |-*.
destruct rngl_has_inv. {
  destruct rngl_is_comm. {
    rewrite rngl_mul_comm.
    now apply rngl_mul_inv_l.
  } {
    cbn in rngl_mul_inv_r.
    now apply rngl_mul_inv_r.
  }
} {
  destruct Hii as [Hii'| Hii']; [ easy | ].
  rewrite Hii' in rngl_mul_div_l.
  specialize (rngl_mul_div_l a 1%F Ha) as H.
  now rewrite rngl_mul_1_r in H.
}
Qed.

Theorem rngl_mul_reg_l :
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  ∀ a b c, a ≠ 0%F
  → (a * b = a * c)%F
  → b = c.
Proof.
intros Hii * Haz Hbc.
specialize rngl_opt_mul_inv_l as rngl_mul_inv_l.
specialize rngl_opt_mul_div_l as rngl_mul_div_l.
assert (H1 : (¹/ a * (a * b) = ¹/ a * (a * c))%F) by now rewrite Hbc.
assert (H2 : (a * b / a = a * c / a)%F) by now rewrite Hbc.
unfold rngl_div in H2, rngl_mul_div_l.
destruct rngl_has_inv. {
  do 2 rewrite rngl_mul_assoc in H1.
  rewrite rngl_mul_inv_l in H1; [ | easy ].
  now do 2 rewrite rngl_mul_1_l in H1.
} {
  destruct Hii as [Hii'| Hii']; [ easy | ].
  rewrite Hii' in rngl_mul_div_l.
  rewrite rngl_mul_div_l in H2; [ | easy ].
  now rewrite rngl_mul_div_l in H2.
}
Qed.

Theorem rngl_mul_reg_r :
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  ∀ a b c, c ≠ 0%F
  → (a * c = b * c)%F
  → a = b.
Proof.
intros Hii * Hcz Hab.
specialize rngl_opt_mul_inv_l as rngl_mul_inv_l.
specialize rngl_opt_mul_inv_r as rngl_mul_inv_r.
specialize rngl_opt_mul_comm as rngl_mul_comm.
specialize rngl_opt_mul_div_r as rngl_mul_div_r.
specialize rngl_opt_mul_div_l as rngl_mul_div_l.
assert (H : (a * c / c = b * c / c)%F) by now rewrite Hab.
unfold rngl_div in H, rngl_mul_inv_r.
do 2 rewrite <- rngl_mul_assoc in H.
unfold rngl_div in rngl_mul_div_l.
unfold rngl_div in rngl_mul_div_r.
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
  rewrite Hii' in rngl_mul_div_l, rngl_mul_div_r.
  destruct rngl_is_comm. {
    rewrite (rngl_mul_comm a) in H.
    rewrite (rngl_mul_comm b) in H.
    rewrite rngl_mul_div_l in H; [ | easy ].
    now rewrite rngl_mul_div_l in H.
  } {
    rewrite rngl_mul_div_r in H; [ | easy ].
    now rewrite rngl_mul_div_r in H.
  }
}
Qed.

Theorem rngl_sub_compat_l : ∀ a b c,
  (a = b)%F → (a - c = b - c)%F.
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

Theorem rngl_add_opp_l :
  rngl_has_opp = true →
 ∀ x, (- x + x = 0)%F.
Proof.
intros Hro *.
specialize rngl_opt_add_opp_l as rngl_add_opp_l.
rewrite Hro in rngl_add_opp_l.
apply rngl_add_opp_l.
Qed.

Theorem rngl_add_opp_r : ∀ x, (x - x = 0)%F.
Proof.
intros.
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

Theorem rngl_opp_0 : rngl_has_opp = true → (- 0 = 0)%F.
Proof.
intros Hro.
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
specialize (rngl_add_sub a 0%F) as H.
now rewrite rngl_add_0_r in H.
Qed.

Theorem rngl_add_move_0_r :
  rngl_has_opp = true →
  ∀ a b, (a + b = 0)%F ↔ (a = - b)%F.
Proof.
intros Hro *.
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

Theorem rngl_opp_involutive :
  rngl_has_opp = true →
  ∀ x, (- - x)%F = x.
Proof.
intros Hro *.
symmetry.
specialize rngl_add_opp_r as H.
unfold rngl_sub in H.
rewrite Hro in H.
now apply rngl_add_move_0_r.
Qed.

Theorem rngl_mul_opp_l :
  rngl_has_opp = true →
  ∀ a b, (- a * b = - (a * b))%F.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_r (- a)%F a b) as H.
rewrite rngl_add_opp_l in H; [ | easy ].
rewrite rngl_mul_0_l in H.
symmetry in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_opp_r :
  rngl_has_opp = true →
  ∀ a b, (a * - b = - (a * b))%F.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_l a b (- b)%F) as H.
rewrite fold_rngl_sub in H; [ | easy ].
rewrite rngl_add_opp_r in H.
rewrite rngl_mul_0_r in H.
symmetry in H.
rewrite rngl_add_comm in H.
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

Theorem rngl_integral :
  (rngl_is_integral || (rngl_has_inv && rngl_has_dec_eq))%bool = true →
  ∀ a b, (a * b = 0)%F → a = 0%F ∨ b = 0%F.
Proof.
intros Hdo * Hab.
specialize rngl_opt_mul_inv_l as rngl_mul_inv_l.
specialize rngl_opt_eq_dec as rngl_eq_dec.
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral; [ now apply rngl_integral | ].
destruct rngl_has_inv; [ | easy ].
destruct rngl_has_dec_eq; [ | easy ].
cbn; clear rngl_integral.
assert (H : (¹/a * a * b = ¹/a * 0)%F). {
  now rewrite <- rngl_mul_assoc, Hab.
}
rewrite rngl_mul_0_r in H.
destruct (rngl_eq_dec a 0%F) as [Haz| Haz]; [ now left | ].
rewrite rngl_mul_inv_l in H; [ | easy ].
rewrite rngl_mul_1_l in H.
now right.
Qed.

Theorem rngl_inv_mul :
  rngl_is_integral = true →
  rngl_has_inv = true →
  ∀ a b, a ≠ 0%F → b ≠ 0%F →(¹/ (a * b) = ¹/ b * ¹/ a)%F.
Proof.
intros Hdo Hin * Haz Hbz.
specialize rngl_mul_reg_l as H1.
specialize rngl_mul_inv_r as H2.
specialize rngl_integral as H3.
specialize rngl_opt_mul_div_l as rngl_mul_div_l.
specialize rngl_opt_mul_comm as rngl_mul_comm.
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
specialize rngl_opt_le_refl as rngl_le_refl.
specialize rngl_opt_le_antisymm as rngl_le_antisymm.
specialize rngl_opt_add_le_compat as rngl_add_le_compat.
rewrite Hor in rngl_le_refl, rngl_le_antisymm, rngl_add_le_compat.
split. {
  apply rngl_le_antisymm in Haz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%F as ab.
  rewrite <- (rngl_add_0_r a); subst ab.
  apply rngl_add_le_compat; [ apply rngl_le_refl | easy ].
} {
  apply rngl_le_antisymm in Hbz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%F as ab.
  rewrite <- (rngl_add_0_l b); subst ab.
  apply rngl_add_le_compat; [ easy | apply rngl_le_refl ].
}
Qed.

Theorem rngl_mul_div_l :
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  ∀ a b : T, b ≠ 0%F → (a * b / b)%F = a.
Proof.
intros Hii a b Hbz.
specialize rngl_opt_mul_div_l as rngl_mul_div_l.
specialize rngl_opt_mul_div_r as rngl_mul_div_r.
specialize rngl_opt_mul_comm as rngl_mul_comm.
specialize rngl_opt_mul_inv_l as rngl_mul_inv_l.
specialize rngl_opt_mul_inv_r as rngl_mul_inv_r.
destruct rngl_is_comm. {
  unfold rngl_div in rngl_mul_div_l |-*.
  destruct rngl_has_inv. {
    rewrite <- rngl_mul_assoc.
    rewrite (rngl_mul_comm b).
    rewrite rngl_mul_inv_l; [ | easy ].
    apply rngl_mul_1_r.
  }
  destruct Hii as [Hii| Hii]; [ easy | ].
  rewrite Hii in rngl_mul_div_l.
  rewrite rngl_mul_comm.
  now apply rngl_mul_div_l.
} {
  destruct rngl_has_no_inv_but_div. {
    cbn in rngl_mul_div_r.
    now apply rngl_mul_div_r.
  }
  destruct Hii as [Hii| Hii]; [ | easy ].
  unfold rngl_div in rngl_mul_inv_r |-*.
  rewrite Hii in rngl_mul_inv_l, rngl_mul_inv_r |-*.
  rewrite <- rngl_mul_assoc.
  rewrite rngl_mul_inv_r; [ | easy ].
  apply rngl_mul_1_r.
}
Qed.

End a.

Arguments rngl_add_opp_l {T}%type {ro rp} Hro.
Arguments rngl_add_opp_r {T}%type {ro rp} x%F.
Arguments rngl_add_reg_l {T}%type {ro rp} (a b c)%F.
Arguments rngl_add_sub {T}%type {ro rp} (a b)%F.
Arguments rngl_inv_mul {T}%type {ro rp} Hin Hdo a%F b%F.
Arguments rngl_integral {T}%type {ro rp}.
Arguments rngl_mul_opp_opp {T}%type {ro rp} Hro.
Arguments rngl_mul_0_l {T}%type {ro rp} a%F.
Arguments rngl_mul_opp_r {T}%type {ro rp} Hro.
Arguments rngl_mul_reg_r {T}%type {ro rp} Hii (a b c)%F.
Arguments rngl_mul_0_r {T}%type {ro rp} a%F.
Arguments rngl_opp_0 {T}%type {ro rp}.
