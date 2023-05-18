(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.

Require Import Utf8.
Require Import Main.RingLike.

Record ideal {A} (P : A → bool) := mk_I
  { i_val : A;
    i_mem : P i_val = true }.

Arguments mk_I {A P} i_val%L i_mem.

Class ideal_prop {A} {ro : ring_like_op A} (P : A → bool) := mk_ip
  { i_zero_in : P rngl_zero = true;
    i_one_in : P rngl_one = true;
    i_prop_add : ∀ a b, P a = true → P b = true → P (a + b)%L = true;
    i_prop_mul_l : ∀ a b, P b = true → P (a * b)%L = true;
    i_prop_mul_r : ∀ a b, P a = true → P (a * b)%L = true }.

(* 0 and 1 *)

Definition I_zero {A} {ro : ring_like_op A} {P : A → bool} {ip : ideal_prop P}
  : ideal P :=
  mk_I 0 i_zero_in.

Definition I_one {A} {ro : ring_like_op A} {P : A → bool} {ip : ideal_prop P}
  : ideal P :=
  mk_I 1 i_one_in.

(* addition *)

Definition I_add {A} {ro : ring_like_op A} {P : A → bool} {ip : ideal_prop P}
    (a b : ideal P)
  : ideal P :=
  mk_I (i_val P a + i_val P b)
    (i_prop_add (i_val P a) (i_val P b) (i_mem P a) (i_mem P b)).

(* multiplication *)

Definition I_mul {A} {ro : ring_like_op A} {P : A → bool} {ip : ideal_prop P}
    (a b : ideal P)
  : ideal P :=
  mk_I (i_val P a * i_val P b)
    (i_prop_mul_l (i_val P a) (i_val P b) (i_mem P b)).

(* ideal ring like op *)

Definition I_ring_like_op {A} {ro : ring_like_op A} {P : A → bool}
    (ip : ideal_prop P) : ring_like_op (ideal P) :=
  {| rngl_zero := I_zero;
     rngl_one := I_one;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_opp_or_subt := None;
     rngl_opt_inv_or_quot := None;
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.
