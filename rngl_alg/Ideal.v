(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8.

Require Import Main.RingLike.

Definition I_ring_like_op A (ro : ring_like_op A) : ring_like_op A :=
  {| rngl_zero := 0%L;
     rngl_one := 1%L;
     rngl_add := rngl_add;
     rngl_mul := rngl_mul;
     rngl_opt_opp_or_subt := None;
     rngl_opt_inv_or_quot := None;
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

(* bof, chuis pas sûr que ça soye ça *)
