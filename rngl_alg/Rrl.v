Set Nested Proofs Allowed.
Require Import Utf8 Reals.
Require Import Main.RingLike.

Canonical Structure reals_ring_like_op : ring_like_op R :=
  {| rngl_zero := R0;
     rngl_one := R1;
     rngl_add := Rplus;
     rngl_mul := Rmult;
     rngl_opt_opp_or_sous := Some (inl Ropp);
     rngl_opt_inv_or_quot := Some (inl Rinv);
     rngl_opt_eqb := None;
     rngl_opt_le := Some Rle |}.

Theorem Rplus_assoc' : ∀ a b c : R, (a + (b + c))%R = (a + b + c)%R.
Proof. intros; now rewrite Rplus_assoc. Qed.

Theorem Rmult_assoc' : ∀ a b c : R, (a * (b * c))%R = (a * b * c)%R.
Proof. intros; now rewrite Rmult_assoc. Qed.

Theorem Rcharacteristic_prop :
  let ror := reals_ring_like_op in
  ∀ i : nat, rngl_of_nat (S i) ≠ 0%L.
Proof.
intros.
assert (H : ∀ n, rngl_of_nat n = INR n). {
  intros.
  induction n; [ easy | cbn ].
  destruct n; [ apply Rplus_0_r | ].
  rewrite IHn.
  apply Rplus_comm.
}
rewrite H.
now apply not_0_INR.
Qed.

Theorem Ropt_mul_le_compat_nonneg :
  let ror := reals_ring_like_op in
  ∀ a b c d : R, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros * Hac Hbd.
now apply Rmult_le_compat.
Qed.

Theorem Ropt_mul_le_compat_nonpos :
  let ror := reals_ring_like_op in
  ∀ a b c d : R, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros * Hca Hdb; cbn.
apply Rle_trans with (r2 := (a * d)%R). {
  now apply Rmult_le_compat_neg_l.
}
rewrite (Rmult_comm a), (Rmult_comm c).
apply Rmult_le_compat_neg_l; [ | easy ].
now apply Rle_trans with (r2 := b).
Qed.

Theorem Ropt_not_le :
  let ror := reals_ring_like_op in
  ∀ a b : R, ¬ (a ≤ b)%L → a = b ∨ (b ≤ a)%L.
Proof.
intros * Hab.
cbn in Hab |-*.
apply Rnot_le_lt in Hab.
specialize (Rle_or_lt b a) as H1.
destruct H1 as [| Hba]; [ now right | left ].
now apply Rlt_asym in Hba.
Qed.

Canonical Structure reals_ring_like_prop : ring_like_prop R :=
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := false;
     rngl_is_integral := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Rplus_comm;
     rngl_add_assoc := Rplus_assoc';
     rngl_add_0_l := Rplus_0_l;
     rngl_mul_assoc := Rmult_assoc';
     rngl_mul_1_l := Rmult_1_l;
     rngl_mul_add_distr_l := Rmult_plus_distr_l;
     rngl_opt_mul_comm := Rmult_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := Rplus_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_sub_sub_add := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := Rinv_l;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eqb_eq := NA;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := Rmult_integral;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := Rcharacteristic_prop;
     rngl_opt_le_refl := Rle_refl;
     rngl_opt_le_antisymm := Rle_antisym;
     rngl_opt_le_trans := Rle_trans;
     rngl_opt_add_le_compat := Rplus_le_compat;
     rngl_opt_mul_le_compat_nonneg := Ropt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := Ropt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := Ropt_not_le |}.

(* experiment, to make, perhaps, an implementation of algebraic numbers
   where a first step is to generate all monic polynomials with values
   in ℕ; since monic, it is not required to append the coefficient 1 to
   the list representing the polynomial, so we have to generate all
   lists of nat *)

Require Import Arith.
Import List List.ListNotations.
Require Import Main.Misc Main.IterAdd Main.NatRingLike.

(* I don't know how to call that; I temporarily call it "step". It is
   a number associated with a list; the next list must have a "step"
   whose value is nat successor (next of a step 42 must have a step 43 *)
Definition step l := length l + ∑ (i = 1, length l), l.(i).

Definition generate_next_step (n : nat) := [[n]; repeat 0 (S n)].

(*
Compute (generate_next_step 0).
Compute (generate_next_step 1).
Compute (generate_next_step 2).
*)

(* I need a function where, when n = 4, should result
     [[0;0;0;0]; [0;0;1]; [0;1;0]; [1;0;0]; [0;2]; [2;0]; [3]
   i.e. 2^n lists: all lists whose "step" is 4
     Doing that, we can generate all lists of nat;
   but, perhaps with an inductive type, it could be the same?
   but not computable *)
(*
Fixpoint glop n i :=
  match n with
  | 0 => []
  | S n' => repeat n i ::
*)
