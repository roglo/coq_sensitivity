(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8.

Require Import Main.RingLike.

Record ideal A {ro : ring_like_op A} := mk_I
  { i_type : A → bool;
    i_prop :
      ∀ a b, i_type a = true → i_type b = true → i_type (a * b)%L = true }.

Arguments ideal A%type {ro}.
Arguments mk_I A%type {ro}.

Definition I_zero_prop A {ro : ring_like_op A} : ∀ (a b : A),
  (a =? 0)%L = true
  → (b =? 0)%L = true
  → ((a * b) =? 0)%L = true.
intros * Ha Hb.
apply rngl_eqb_eq in Ha.
...

Arguments I_zero_prop A%type {ro}.

Definition I_zero A {ro : ring_like_op A} : ideal A :=
  mk_I A
    (λ a, (a =? 0)%L)
    (I_zero_prop A).

...

Definition I_ring_like_op A (ro : ring_like_op A) : ring_like_op (ideal A) :=
  {| rngl_zero := I_zero |}.

...
  {| rngl_zero := 0%L;
     rngl_one := 1%L;
     rngl_add := rngl_add;
     rngl_mul := rngl_mul;
     rngl_opt_opp_or_subt := None;
     rngl_opt_inv_or_quot := None;
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

(* bof, chuis pas sûr que ça soye ça *)
