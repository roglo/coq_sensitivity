(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.

Require Import Utf8.
Require Import Main.RingLike.

Record ideal {T} (P : T → bool) := mk_I
  { i_val : T;
    i_mem : P i_val = true }.

Arguments mk_I {T P} i_val%L i_mem.
Arguments i_val {T P} i%L.

Class ideal_prop {T} {ro : ring_like_op T} (P : T → bool) := mk_ip
  { i_zero_in : P rngl_zero = true;
    i_one_in : P rngl_one = true;
    i_prop_add : ∀ a b, P a = true → P b = true → P (a + b)%L = true;
    i_prop_mul_l : ∀ a b, P b = true → P (a * b)%L = true;
    i_prop_mul_r : ∀ a b, P a = true → P (a * b)%L = true }.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {P : T → bool}.
Context {ip : ideal_prop P}.

(* 0 and 1 *)

Definition I_zero : ideal P := mk_I 0 i_zero_in.
Definition I_one : ideal P := mk_I 1 i_one_in.

(* addition *)

Definition I_add (a b : ideal P): ideal P :=
  mk_I (i_val a + i_val b)
    (i_prop_add (i_val a) (i_val b) (i_mem P a) (i_mem P b)).

(* multiplication *)

Definition I_mul (a b : ideal P) : ideal P :=
  mk_I (i_val a * i_val b)
    (i_prop_mul_l (i_val a) (i_val b) (i_mem P b)).

(* ideal ring like op *)

Definition I_ring_like_op : ring_like_op (ideal P) :=
  {| rngl_zero := I_zero;
     rngl_one := I_one;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_opp_or_subt := None;
     rngl_opt_inv_or_quot := None;
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

(* equality in ideals is equivalent to equality in their values,
   because the proof of their properties (i_mem), being an equality
   between booleans, is unique *)

Theorem eq_ideal_eq : ∀ (a b : ideal P), i_val a = i_val b ↔ a = b.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct a as (a, pa).
destruct b as (b, pb).
cbn in Hab.
subst b.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

(* ideal ring like prop *)

Theorem I_add_comm :
  let roi := I_ring_like_op in
  ∀ a b : ideal P, (a + b)%L = (b + a)%L.
Proof.
intros; cbn.
apply eq_ideal_eq; cbn.
apply rngl_add_comm.
Qed.

Definition I_ring_like_prop : ring_like_prop (ideal P) :=
  {| rngl_mul_is_comm := false;
     rngl_has_dec_le := false;
     rngl_is_integral := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := I_add_comm;
     rngl_add_assoc := 42;
     rngl_add_0_l := ?rngl_add_0_l;
     rngl_mul_assoc := ?rngl_mul_assoc;
     rngl_mul_1_l := ?rngl_mul_1_l;
     rngl_mul_add_distr_l := ?rngl_mul_add_distr_l;
     rngl_opt_mul_comm := ?rngl_opt_mul_comm;
     rngl_opt_mul_1_r := ?rngl_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := ?rngl_opt_mul_add_distr_r;
     rngl_opt_add_opp_l := ?rngl_opt_add_opp_l;
     rngl_opt_add_sub := ?rngl_opt_add_sub;
     rngl_opt_sub_add_distr := ?rngl_opt_sub_add_distr;
     rngl_opt_mul_inv_l := ?rngl_opt_mul_inv_l;
     rngl_opt_mul_inv_r := ?rngl_opt_mul_inv_r;
     rngl_opt_mul_div := ?rngl_opt_mul_div;
     rngl_opt_mul_quot_r := ?rngl_opt_mul_quot_r;
     rngl_opt_eqb_eq := ?rngl_opt_eqb_eq;
     rngl_opt_le_dec := ?rngl_opt_le_dec;
     rngl_opt_integral := ?rngl_opt_integral;
     rngl_opt_alg_closed := ?rngl_opt_alg_closed;
     rngl_characteristic_prop := ?rngl_characteristic_prop;
     rngl_opt_le_refl := ?rngl_opt_le_refl;
     rngl_opt_le_antisymm := ?rngl_opt_le_antisymm;
     rngl_opt_le_trans := ?rngl_opt_le_trans;
     rngl_opt_add_le_compat := ?rngl_opt_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := ?rngl_opt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := ?rngl_opt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := ?rngl_opt_mul_le_compat;
     rngl_opt_not_le := ?rngl_opt_not_le |}.
