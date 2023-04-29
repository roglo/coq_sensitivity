(* ℕ is a ring-like without opposite, i.e. a semiring *)
(* ℤ/nℤ is a ring-like,
     if n is prime, has inverse, i.e. it is a field
     if n is not prime, it has neither inverse nor division, it is a ring *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Misc RingLike.

Canonical Structure nat_ring_like_op : ring_like_op nat :=
  {| rngl_zero := 0;
     rngl_one := 1;
     rngl_add := Nat.add;
     rngl_mul := Nat.mul;
     rngl_opt_opp_or_subt := Some (inr Nat.sub);
     rngl_opt_inv_or_quot := Some (inr Nat.div);
     rngl_opt_eqb := Some Nat.eqb;
     rngl_opt_le := Some Nat.le |}.

(*
Global Existing Instance nat_ring_like_op.
*)

Theorem Nat_eq_mul_0 : ∀ n m, n * m = 0 → n = 0 ∨ m = 0.
Proof. now intros; apply Nat.eq_mul_0. Qed.

Theorem nat_characteristic_prop :
  let ro := nat_ring_like_op in
  ∀ i, rngl_of_nat (S i) ≠ 0.
Proof. easy. Qed.

Theorem Nat_mul_div :
  let ro := nat_ring_like_op in
  ∀ a b, b ≠ 0%L → (a * b / b)%L = a.
Proof.
intros * Hbz.
now apply Nat.div_mul.
Qed.

Theorem Nat_mul_le_compat : ∀ a b c d,
  a ≤ c → b ≤ d → a * b ≤ c * d.
Proof.
intros * Hac Hbd.
now apply Nat.mul_le_mono.
Qed.

Theorem Nat_not_le : ∀ a b, ¬ a ≤ b → a = b ∨ b ≤ a.
Proof.
intros * Hab.
destruct (Nat.eq_dec a b) as [Heab| Heab]; [ now left | right ].
apply Nat.nle_gt in Hab.
apply Nat.nlt_ge; intros Hba.
apply Heab.
now apply Nat.le_antisymm; apply Nat.lt_le_incl.
Qed.

Theorem Nat_mul_sub_distr_l :
  let ro := nat_ring_like_op in
  ∀ a b c, (a * (b - c))%L = (a * b - a * c)%L.
Proof.
intros.
apply Nat.mul_sub_distr_l.
Qed.

Theorem Nat_opt_quot_mul :
  let ro := nat_ring_like_op in
  if rngl_has_quot then
    ∀ a b c : nat, b ≠ 0%L → c ≠ 0%L → (a / (b * c))%L = (a / b / c)%L
  else not_applicable.
Proof.
intros; cbn.
intros * Hbz Hcz.
symmetry; apply (Nat.div_div _ _ _ Hbz Hcz).
Qed.

Canonical Structure nat_ring_like_prop : ring_like_prop nat :=
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := true;
     rngl_is_integral := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Nat.add_comm;
     rngl_add_assoc := Nat.add_assoc;
     rngl_add_0_l := Nat.add_0_l;
     rngl_mul_assoc := Nat.mul_assoc;
     rngl_mul_1_l := Nat.mul_1_l;
     rngl_mul_add_distr_l := Nat.mul_add_distr_l;
     rngl_opt_mul_comm := Nat.mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := NA;
     rngl_opt_add_sub := Nat.add_sub;
     rngl_opt_sub_add_distr := Nat.sub_add_distr;
     rngl_opt_mul_sub_distr_l := Nat_mul_sub_distr_l;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := Nat_mul_div;
     rngl_opt_mul_quot_r := NA;
(*
     rngl_opt_quot_mul := Nat_opt_quot_mul;
*)
     rngl_opt_eqb_eq := Nat.eqb_eq;
     rngl_opt_le_dec := le_dec;
     rngl_opt_integral := Nat_eq_mul_0;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := nat_characteristic_prop;
     rngl_opt_le_refl := Nat.le_refl;
     rngl_opt_le_antisymm := Nat.le_antisymm;
     rngl_opt_le_trans := Nat.le_trans;
     rngl_opt_add_le_compat := Nat.add_le_mono;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := Nat_mul_le_compat;
     rngl_opt_not_le := Nat_not_le |}.

(*
Global Existing Instance nat_ring_like_prop.
*)

(*
Print nat_ring_like_op.
Existing Instance nat_ring_like_op.
Compute (7 - 3)%L.
Compute (7 - 3)%nat.
Compute (15 / 3)%L.
Compute (15 / 3)%nat.
*)
