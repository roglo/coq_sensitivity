Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import RingLike.
Open Scope Z_scope.

Record gauss_int := mk_gi { gi_r : Z; gi_i : Z }.

Definition gi_zero := mk_gi 0 0.
Definition gi_one := mk_gi 1 0.

Definition gi_add α β := mk_gi (gi_r α + gi_r β) (gi_i α + gi_i β).
Definition gi_mul α β :=
  mk_gi (gi_r α * gi_r β - gi_i α * gi_i β)
    (gi_r α * gi_i β + gi_i α * gi_r β).
Definition gi_opp α := mk_gi (- gi_r α) (- gi_i α).

Definition gi_gauge (α : gauss_int) := 0%nat.
Definition gi_eucl_div α β :=
  let d := gi_r β * gi_r β + gi_i β * gi_i β in
  let γ := (gi_r α * gi_r β + gi_i α * gi_i β) / d in
  let γ' := (gi_i α * gi_r β - gi_r α * gi_i β) / d in
  let q := mk_gi γ γ' in
  (q, gi_add α (gi_opp (gi_mul β q))).
(* but could be also
       mk_gi (γ + 1) γ', or
       mk_gi γ (γ' + 1), or
       mk_gi (γ + 1) (γ' + 1).
   It depends on gauge and the values of α and β.
 *)

Declare Scope G_scope.
Delimit Scope G_scope with G.
Notation "0" := gi_zero : G_scope.
Notation "1" := gi_one : G_scope.
Notation "- x" := (gi_opp x) : G_scope.

Definition phony_gi_le (a b : gauss_int) := False.

Canonical Structure gauss_int_ring_like_op : ring_like_op gauss_int :=
  {| rngl_zero := gi_zero;
     rngl_one := gi_one;
     rngl_add := gi_add;
     rngl_mul := gi_mul;
     rngl_opt_opp := Some gi_opp;
     rngl_opt_inv := None;
     rngl_opt_monus := None;
     rngl_opt_eucl_div := Some (gi_eucl_div, gi_gauge);
     rngl_le := phony_gi_le |}.

Print gauss_int_ring_like_op.
