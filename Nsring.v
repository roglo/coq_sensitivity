(* Semiring of natural *)

Require Import Utf8 Arith.
Require Import RingLike.

Definition phony_Nat_opp (x : nat) := 0.
Definition phony_Nat_inv (x : nat) := 0.

Canonical Structure nat_ring_like_op : ring_like_op nat :=
  {| rngl_zero := 0;
     rngl_one := 1;
     rngl_add := Nat.add;
     rngl_mul := Nat.mul;
     rngl_opp := phony_Nat_opp;
     rngl_inv := phony_Nat_inv |}.

Theorem Nat_eq_mul_0 : ∀ n m, n * m = 0 → n = 0 ∨ m = 0.
Proof. now intros; apply Nat.eq_mul_0. Qed.

Theorem Nat_neq_1_0 : 1 ≠ 0.
Proof. easy. Qed.

Canonical Structure nat_ring_like_prop : ring_like_prop nat :=
  {| rngl_is_comm := true;
     rngl_has_opp := false;
     rngl_has_inv := false;
     rngl_has_dec_eq := true;
     rngl_is_integral_not_provable := true;
     rngl_add_comm := Nat.add_comm;
     rngl_add_assoc := Nat.add_assoc;
     rngl_add_0_l := Nat.add_0_l;
     rngl_mul_assoc := Nat.mul_assoc;
     rngl_mul_1_l := Nat.mul_1_l;
     rngl_mul_add_distr_l := Nat.mul_add_distr_l;
     rngl_1_neq_0 := Nat_neq_1_0;
     rngl_opt_mul_comm := Nat.mul_comm;
     rngl_opt_mul_1_r := I;
     rngl_opt_mul_add_distr_r := I;
     rngl_opt_add_opp_l := I;
     rngl_opt_mul_0_l := Nat.mul_0_l;
     rngl_opt_mul_0_r := Nat.mul_0_r;
     rngl_opt_mul_inv_l := I;
     rngl_opt_mul_inv_r := I;
     rngl_opt_eq_dec := Nat.eq_dec;
     rngl_opt_is_integral := Nat_eq_mul_0 |}.

(*
Print nat_ring_like_op.
Existing Instance nat_ring_like_op.
Compute (7 - 3)%F.
Compute (7 - 3)%nat.
Compute (15 / 3)%F.
Compute (15 / 3)%nat.
*)

(* ℤn = ℤ/nℤ *)

Definition Zn n := {a : nat | a <? S (n - 1) = true}.

Theorem Zn_op_prop n r : r mod n <? S (n - 1) = true.
Proof.
intros.
apply Nat.ltb_lt.
destruct n; [ apply Nat.lt_0_1 | ].
rewrite Nat.sub_succ, Nat.sub_0_r.
now apply Nat.mod_upper_bound.
Qed.

Definition Zn_v n v : Zn n :=
  exist _ (v mod n) (Zn_op_prop n v).

Definition Zn_add n (a b : Zn n) : Zn n :=
  let r := proj1_sig a + proj1_sig b in
  exist _ (r mod n) (Zn_op_prop n r).
Definition Zn_mul n (a b : Zn n) : Zn n :=
  let r := proj1_sig a * proj1_sig b in
  exist _ (r mod n) (Zn_op_prop n r).
Definition Zn_opp n (a : Zn n) : Zn n :=
  let r := n - proj1_sig a in
  exist _ (r mod n) (Zn_op_prop n r).
Definition phony_Zn_inv n (a : Zn n) : Zn n :=
  let r := 0 in
  exist _ (r mod n) (Zn_op_prop n r).

Definition Zn_ring_like_op n : ring_like_op (Zn n) :=
  {| rngl_zero := Zn_v n 0;
     rngl_one := Zn_v n 1;
     rngl_add := Zn_add n;
     rngl_mul := Zn_mul n;
     rngl_opp := Zn_opp n;
     rngl_inv := phony_Zn_inv n |}.

Theorem Zn_eq : ∀ n (a b : Zn n), proj1_sig a = proj1_sig b → a = b.
Proof.
intros * Hab.
destruct a as (a, Ha).
destruct b as (b, Hb).
cbn in Hab.
apply eq_exist_uncurried.
exists Hab.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Section a.

Context {n : nat}.
Context (ro := Zn_ring_like_op n).
Existing Instance ro.

Theorem Zn_add_comm : ∀ (a b : Zn n), (a + b = b + a)%F.
Proof.
intros (a, Ha) (b, Hb).
apply Zn_eq; cbn.
unfold rngl_add; cbn.
now rewrite Nat.add_comm.
Qed.

Theorem Zn_add_assoc : ∀ (a b c : Zn n), (a + (b + c) = (a + b) + c)%F.
Proof.
intros.
apply Zn_eq; cbn.
destruct n; [ easy | ].
clear n.
rename n0 into n.
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.add_mod_idemp_r; [ | easy ].
now rewrite Nat.add_assoc.
Qed.

Theorem Zn_add_0_l : ∀ (a : Zn n), (0 + a = a)%F.
Proof.
intros.
apply Zn_eq; cbn.
destruct a as (a, Ha); cbn.
apply Nat.ltb_lt in Ha.
destruct n; [ now apply Nat.lt_1_r in Ha | ].
rewrite Nat.sub_succ, Nat.sub_0_r in Ha.
rewrite Nat.mod_0_l; [ | easy ].
now rewrite Nat.mod_small.
Qed.

Definition Zn_ring_like_prop : ring_like_prop nat :=
  {| rngl_is_comm := true;
     rngl_has_opp := true;
     rngl_has_inv := false; (* except if n is prime *)
     rngl_has_dec_eq := true;
     rngl_is_integral_not_provable := true;
     rngl_add_comm := Zn_add_comm;
     rngl_add_assoc := Zn_add_assoc;
     rngl_add_0_l := Zn_add_0_l;
     rngl_mul_assoc := ... Nat.mul_assoc;
     rngl_mul_1_l := Nat.mul_1_l;
     rngl_mul_add_distr_l := Nat.mul_add_distr_l;
     rngl_1_neq_0 := Nat_neq_1_0;
     rngl_opt_mul_comm := Nat.mul_comm;
     rngl_opt_mul_1_r := I;
     rngl_opt_mul_add_distr_r := I;
     rngl_opt_add_opp_l := I;
     rngl_opt_mul_0_l := Nat.mul_0_l;
     rngl_opt_mul_0_r := Nat.mul_0_r;
     rngl_opt_mul_inv_l := I;
     rngl_opt_mul_inv_r := I;
     rngl_opt_eq_dec := Nat.eq_dec;
     rngl_opt_is_integral := Nat_eq_mul_0 |}.
