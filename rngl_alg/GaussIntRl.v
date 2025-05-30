Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 ZArith.
Open Scope Z_scope.

Record gauss_int := mk_gi { gi_re : Z; gi_im : Z }.

Definition gi_zero := mk_gi 0 0.
Definition gi_one := mk_gi 1 0.
Definition gi_i := mk_gi 0 1.

Definition gi_add α β := mk_gi (gi_re α + gi_re β) (gi_im α + gi_im β).
Definition gi_mul α β :=
  mk_gi (gi_re α * gi_re β - gi_im α * gi_im β)
    (gi_re α * gi_im β + gi_im α * gi_re β).
Definition gi_opp α := mk_gi (- gi_re α) (- gi_im α).

Definition gi_sub α β := gi_add α (gi_opp β).
Definition gi_conj α := mk_gi (gi_re α) (- gi_im α).

Declare Scope G_scope.
Delimit Scope G_scope with G.
Notation "0" := gi_zero : G_scope.
Notation "1" := gi_one : G_scope.
Notation "'ⁱ'" := gi_i (at level 0) : G_scope.
Notation "- α" := (gi_opp α) : G_scope.
Notation "α + β" := (gi_add α β) : G_scope.
Notation "α * β" := (gi_mul α β) : G_scope.
Notation "α - β" := (gi_sub α β) : G_scope.

Definition gi_gauge (α : gauss_int) :=
  Z.abs_nat (gi_re α * gi_re α + gi_im α + gi_im α)%Z.

Definition gi_eucl_div α β :=
  let d := gi_re β * gi_re β + gi_im β * gi_im β in
(**)
  let γ := gi_re (α * gi_conj β)%G / d in
  let γ' := gi_im (α * gi_conj β)%G / d in
(*
  let γ := (gi_re α * gi_re β + gi_im α * gi_im β) / d in
  let γ' := (gi_im α * gi_re β - gi_re α * gi_im β) / d in
*)
  let q :=
    if lt_dec (gi_gauge (α - β * mk_gi γ γ')%G) (gi_gauge β) then
      mk_gi γ γ'
    else if lt_dec (gi_gauge (α - β * mk_gi (γ + 1) γ')%G) (gi_gauge β) then
      mk_gi (γ + 1) γ'
    else if lt_dec (gi_gauge (α - β * mk_gi γ (γ' + 1))%G) (gi_gauge β) then
      mk_gi γ (γ' + 1)
    else if
      lt_dec (gi_gauge (α - β * mk_gi (γ + 1) (γ' + 1))%G) (gi_gauge β)
    then
      mk_gi (γ + 1) (γ' + 1)
    else
      0%G
  in
  let r := (α - β * q)%G in
  (q, r).

Definition gi_div α β := fst (gi_eucl_div α β).

Notation "α / β" := (gi_div α β) : G_scope.

Require Import RingLike.Core.

Canonical Structure gauss_int_ring_like_op : ring_like_op gauss_int :=
  {| rngl_zero := gi_zero;
     rngl_add := gi_add;
     rngl_mul := gi_mul;
     rngl_opt_one := Some gi_one;
     rngl_opt_opp_or_subt := Some (inl gi_opp);
     rngl_opt_inv_or_quot := Some (inr gi_div);
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := None; (* to be improved, perhaps *)
     rngl_opt_leb := None |}.

(*
Compute (mk_gi (- 36) 242 / mk_gi 50 50)%G.
*)

(* to be completed with gauss_int_ring_like_prop... *)
