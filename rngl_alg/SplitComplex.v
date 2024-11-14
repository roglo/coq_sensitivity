(* experiment *)

Set Nested Proofs Allowed.
Require Import Utf8.

Require Import Main.Misc Main.RingLike.
Require Import Main.MyVector.
Require Import Misc.

(* numbers of the form a+ib+jc+kd with i, j, k such that
     i²=-1 : complex
     j²=1  : split such that j=matrix (0 1) (1 0)
     k²=1  : split such that k=matrix (0 1) (0 -1)
*)

Class SplitComplex T := mk_sc {sre : T; sc1 : T; sc2 : T; sc3 : T}.

Declare Scope sc_scope.
Delimit Scope sc_scope with S.
Bind Scope sc_scope with SplitComplex.

Arguments mk_sc {T} (sre sc1 sc2 sc3)%_L : rename.
Arguments sre {T} a%_L : rename.
Arguments sc1 {T} a%_L : rename.
Arguments sc2 {T} a%_L : rename.
Arguments sc3 {T} a%_L : rename.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition sc_zero := mk_sc 0 0 0 0.
Definition sc_one := mk_sc 1 0 0 0.

Definition sc_add a b :=
  mk_sc (sre a + sre b) (sc1 a + sc1 b) (sc2 a + sc2 b) (sc2 a + sc2 b).

Definition sc_sub a b :=
  mk_sc (sre a - sre b) (sc1 a - sc1 b) (sc2 a - sc2 b) (sc2 a - sc2 b).

Definition sc_opp a := mk_sc (- sre a) (- sc1 a) (- sc2 a) (- sc3 a).

Definition sc_mul a b :=
  mk_sc
    (sre a * sre b - sc1 a * sc1 b + sc2 a * sc2 b + sc3 a * sc3 b)
    (sre a * sc1 b + sc1 a * sre b + sc2 a * sc3 b - sc3 a * sc2 b)
    (sre a * sc2 b + sc1 a * sc3 b + sc2 a * sre b - sc3 a * sc1 b)
    (sre a * sc3 b - sc1 a * sc2 b + sc2 a * sc1 b + sc3 a * sre b).

Definition sc_inv a b :=
...

Definition sc_opt_one := Some sc_one.

Definition sc_opt_opp_or_subt :=
  match rngl_opt_opp_or_subt T with
  | Some (inl opp) => Some (inl sc_opp)
  | Some (inr subt) => Some (inr sc_sub)
  | None => None
  end.

Definition sc_opt_inv_or_quot :
  match rngl_opt_opp_or_subt T with
  | Some (inl inv) => Some (inl sc_inv)
  | Some (inr quot) => Some (inr sc_div)
  | None => None
  end.

...

Definition sc_opt_eq_dec := 6.
Definition sc_opt_leb := 7.

Instance sc_ring_like_op : ring_like_op (SplitComplex T) :=
  {| rngl_zero := sc_zero;
     rngl_add := sc_add;
     rngl_mul := sc_mul;
     rngl_opt_one := sc_opt_one;
     rngl_opt_opp_or_subt := sc_opt_opp_or_subt;
     rngl_opt_inv_or_quot := sc_opt_inv_or_quot;
     rngl_opt_eq_dec := sc_opt_eq_dec;
     rngl_opt_leb := sc_opt_leb |}.
