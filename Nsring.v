(* Semiring of natural *)

Require Import Utf8 Arith.
Require Import RingLike.

Definition phony_Nat_opp (x : nat) := 0.
Definition phony_Nat_inv (x : nat) := 0.

Definition nat_ring_like_op : ring_like_op nat :=
  {| rngl_zero := 0;
     rngl_one := 1;
     rngl_add := Nat.add;
     rngl_mul := Nat.mul;
     rngl_opp := phony_Nat_opp;
     rngl_inv := phony_Nat_inv |}.

Canonical Structure nat_ring_like_op.

Definition nat_ring_like_prop : ring_like_prop nat :=
  {| rngl_is_comm := true;
     rngl_has_opp := false;
     rngl_has_inv := false;
     rngl_add_comm := Nat.add_comm;
     rngl_add_assoc := Nat.add_assoc;
     rngl_add_0_l := Nat.add_0_l;
     rngl_mul_assoc := Nat.mul_assoc;
     rngl_mul_1_l := Nat.mul_1_l;
     rngl_mul_add_distr_l := Nat.mul_add_distr_l;
     rngl_c_mul_comm := Nat.mul_comm;
     rngl_nc_mul_1_r := I;
     rngl_nc_mul_add_distr_r := I;
     rngl_o_add_opp_l := I;
     rngl_no_mul_0_l := Nat.mul_0_l;
     rngl_no_mul_0_r := Nat.mul_0_r;
     rngl_i_mul_inv_l := I |}.

Canonical Structure nat_ring_like_prop.
