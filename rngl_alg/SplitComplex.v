(* experiment *)

Set Nested Proofs Allowed.
Require Import Utf8.

Require Import RingLike.RingLike.
Require Import RingLike.Misc.
Require Import Sensitivity.MyVector.
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

(* inversible if the "r" below is not null *)
Definition sc_inv a :=
  let r := ((sre a)² + (sc1 a)² - (sc2 a)² - (sc3 a)²)%L in
  mk_sc (sre a / r) (- sc1 a / r) (- sc2 a / r) (- sc3 a / r).

Definition sc_div a b := sc_mul a (sc_inv b).

Definition sc_opt_one := Some sc_one.

Definition sc_opt_opp_or_subt :=
  match rngl_opt_opp_or_subt T with
  | Some (inl opp) => Some (inl sc_opp)
  | Some (inr subt) => Some (inr sc_sub)
  | None => None
  end.

Definition sc_opt_inv_or_quot :
  option
    ((SplitComplex T → SplitComplex T) +
     (SplitComplex T → SplitComplex T → SplitComplex T)) := None.

Definition sc_opt_eq_dec := 6.
Definition sc_opt_leb := 7.

(* y a pas, il faut que je revoie RingLike.v pour permettre
   de définir la notion d'inverse avec a * a⁻¹ = 1, mais dont
   la condition soit plus générale que a ≠ 0. En principe, on
   l'obtient en disant que "a" n'est pas un diviseur de 0.
     Il faut voir alors quel est ou quels sont les "bons"
   axiomes à mettre dans ring_like_prop pour donner la
   bonne propriété d'être un diviseur de zéro.
     Ça permettrait d'inclure sc_inv au lieu de dire systématiquement
   None pour ring_opt_inv_or_quot et on pourrait voir pour les
   matrices, aussi *)
...

Instance sc_ring_like_op : ring_like_op (SplitComplex T) :=
  {| rngl_zero := sc_zero;
     rngl_add := sc_add;
     rngl_mul := sc_mul;
     rngl_opt_one := sc_opt_one;
     rngl_opt_opp_or_subt := sc_opt_opp_or_subt;
     rngl_opt_inv_or_quot := sc_opt_inv_or_quot;
     rngl_opt_eq_dec := sc_opt_eq_dec;
     rngl_opt_leb := sc_opt_leb |}.
