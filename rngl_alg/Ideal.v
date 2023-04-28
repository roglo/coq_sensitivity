(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8.

Require Import Main.RingLike.

Class ideal A {ro : ring_like_op A} := mk_I
  { i_type : A → bool;
    i_prop_l : ∀ a b, i_type b = true → i_type (a * b)%L = true;
    i_prop_r : ∀ a b, i_type a = true → i_type (a * b)%L = true }.

Arguments ideal A%type {ro}.
Arguments mk_I A%type {ro}.

Theorem I_zero_prop_l A {ro : ring_like_op A} {rp : ring_like_prop A}
   (Hos : rngl_has_opp_or_subt = true) (Heb : rngl_has_eqb = true) :
  ∀ (a b : A),
  (b =? 0)%L = true
  → ((a * b) =? 0)%L = true.
Proof.
intros * Hb.
apply (rngl_eqb_eq Heb) in Hb.
apply (rngl_eqb_eq Heb).
subst b.
apply (rngl_mul_0_r Hos).
Qed.

Theorem I_zero_prop_r A {ro : ring_like_op A} {rp : ring_like_prop A}
   (Hos : rngl_has_opp_or_subt = true) (Heb : rngl_has_eqb = true) :
  ∀ (a b : A),
  (a =? 0)%L = true
  → ((a * b) =? 0)%L = true.
Proof.
intros * Ha.
apply (rngl_eqb_eq Heb) in Ha.
apply (rngl_eqb_eq Heb).
subst a.
apply (rngl_mul_0_l Hos).
Qed.

Arguments I_zero_prop_l A%type {ro rp} Hos Heb (a b)%L.
Arguments I_zero_prop_r A%type {ro rp} Hos Heb (a b)%L.

Definition I_zero A {ro : ring_like_op A} {rp : ring_like_prop A}
    (Hos : rngl_has_opp_or_subt = true) (Heb : rngl_has_eqb = true) :
      ideal A :=
  mk_I A (λ a, (a =? 0)%L) (I_zero_prop_l A Hos Heb) (I_zero_prop_r A Hos Heb).

Definition I_one A {ro : ring_like_op A} {rp : ring_like_prop A} :
      ideal A :=
  mk_I A (λ a, true) (λ _ _ _, eq_refl) (λ _ _ _, eq_refl).

(*
Theorem I_add_prop_l :
  ∀ A {ro : ring_like_op A} (a b : ideal A) (c d : A),
  (i_type a || i_type b)%bool = true → (i_type a || i_type b)%bool = true.
...
*)

Definition I_add A {ro : ring_like_op A} (a b : ideal A) : ideal A :=
  mk_I A (λ c, c = ...

...

Definition I_ring_like_op A (ro : ring_like_op A) (rp : ring_like_prop A)
    (Hos : rngl_has_opp_or_subt = true) (Heb : rngl_has_eqb = true) :
      ring_like_op (ideal A) :=
  {| rngl_zero := I_zero Hos Heb;
     rngl_one := I_one;
     rngl_add := 42;
     rngl_mul := ?rngl_mul;
     rngl_opt_opp_or_subt := ?rngl_opt_opp_or_subt;
     rngl_opt_inv_or_quot := ?rngl_opt_inv_or_quot;
     rngl_opt_eqb := ?rngl_opt_eqb;
     rngl_opt_le := ?rngl_opt_le |}.

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
