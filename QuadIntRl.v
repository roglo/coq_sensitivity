Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 ZArith.
Require Import RingLike.
Open Scope Z_scope.

Record quad_int (d : Z) := mk_qi { qi_re : Z; qi_im : Z }.

Definition qi_zero {d} := mk_qi d 0 0.
Definition qi_one {d} := mk_qi d 1 0.

Definition qi_add {d} (α β : quad_int d) :=
  mk_qi d (qi_re α + qi_re β) (qi_im α + qi_im β).

Definition qi_mul {d} (α β : quad_int d) :=
  mk_qi d (qi_re α * qi_re β + d * qi_im α * qi_im β)
    (qi_re α * qi_im β + qi_im α * qi_re β).

Definition qi_opp d (α : quad_int d) := mk_qi d (- qi_re α) (- qi_im α).

Definition qi_sub d (α β : quad_int d) := qi_add α (qi_opp β).
Definition qi_conj d (α : quad_int d) := mk_qi d (qi_re α) (- qi_im α).

Declare Scope QI_scope.
Delimit Scope QI_scope with QI.
Notation "0" := qi_zero : QI_scope.
Notation "1" := qi_one : QI_scope.
Notation "- α" := (qi_opp α) : QI_scope.
Notation "α + β" := (qi_add α β) : QI_scope.
Notation "α * β" := (qi_mul α β) : QI_scope.
Notation "α - β" := (qi_sub α β) : QI_scope.

Definition qi_gauge {d} (α : quad_int d) :=
  Z.abs_nat (qi_re α * qi_re α - d * qi_im α + qi_im α)%Z.

Definition qi_eucl_div {d} (α β : quad_int d) :=
  let den := qi_re β * qi_re β + qi_im β * qi_im β in
(**)
  let γ := qi_re (α * qi_conj β)%QI / den in
  let γ' := qi_im (α * qi_conj β)%QI / den in
(*
  let γ := (qi_re α * qi_re β + qi_im α * qi_im β) / d in
  let γ' := (qi_im α * qi_re β - qi_re α * qi_im β) / d in
*)
  let q :=
    if lt_dec (qi_gauge (α - β * mk_qi d γ γ')%QI) (qi_gauge β) then
      mk_qi d γ γ'
    else if lt_dec (qi_gauge (α - β * mk_qi d (γ + 1) γ')%QI) (qi_gauge β) then
      mk_qi d (γ + 1) γ'
    else if lt_dec (qi_gauge (α - β * mk_qi d  γ (γ' + 1))%QI) (qi_gauge β) then
      mk_qi d γ (γ' + 1)
    else if
      lt_dec (qi_gauge (α - β * mk_qi d (γ + 1) (γ' + 1))%QI) (qi_gauge β)
    then
      mk_qi d (γ + 1) (γ' + 1)
    else
      0%QI
  in
  let r := (α - β * q)%QI in
  (q, r).

Definition qi_div d (α β : quad_int d) := fst (qi_eucl_div α β).

Notation "α / β" := (qi_div α β) : QI_scope.

Definition phony_qi_le {d} (a b : quad_int d) := False.

Canonical Structure quad_int_ring_like_op {d} : ring_like_op (quad_int d) :=
  {| rngl_zero := @qi_zero d;
     rngl_one := @qi_one d;
     rngl_add := @qi_add d;
     rngl_mul := @qi_mul d;
     rngl_opt_opp := Some (@qi_opp d);
     rngl_opt_inv := None;
     rngl_opt_monus := None;
     rngl_opt_eucl_div := Some (qi_eucl_div, qi_gauge);
     rngl_le := phony_qi_le |}.

Compute (mk_qi (-1) (- 36) 242 / mk_qi (-1) 50 50)%QI.
Compute (mk_qi 1 (- 36) 242 / mk_qi 1 50 50)%QI.
Compute (mk_qi (-1) 0 1 * mk_qi (-1) 0 1)%QI.
Compute (1 / mk_qi (-1) 0 1)%QI.
Compute (1 / mk_qi (-1) 0 (- 1))%QI.
Compute (mk_qi 1 22 0 / mk_qi 1 7 0)%QI.
Compute (@qi_zero 42 / @qi_zero 42)%QI.
