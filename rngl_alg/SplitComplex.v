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

Class SplitComplex T := mk_sc {gre : T; sc1 : T; sc2 : T; sc3 : T}.

Declare Scope sc_scope.
Delimit Scope sc_scope with S.
Bind Scope sc_scope with SplitComplex.

Arguments mk_sc {T} (sc1 sc2 sc3)%_L : rename.
Arguments sc1 {T} a%_L : rename.
Arguments sc2 {T} a%_L : rename.
Arguments sc3 {T} a%_L : rename.

...

(* I'd like to use them with U={(i,j,k)} such that
     i²=-1 : complex
     j²=1  : split such that j=matrix (0 1) (1 0)
     k²=1  : split such that k=matrix (0 1) (0 -1)
  but is it a "ring-like" by itself?
*)

Declare Scope cs_scope.
Delimit Scope cs_scope with S.
Bind Scope cs_scope with ComplexSplit.

Class ComplexSplit T := mk_cs {cim : T; cs1 : T; cs2 : T}.

Arguments mk_cs {T} (cim cs1 cs2)%_L.
Arguments cim {T} a%_L : rename.
Arguments cs1 {T} a%_L : rename.
Arguments cs2 {T} a%_L : rename.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition cs_zero := mk_cs 0 0 0.

Definition cs_add a b :=
  mk_cs (cim a + cim b) (cs1 a + cs1 b) (cs2 a + cs2 b).

Definition cs_mul a b :=
... ah oui non c'est déjà foutu ...

Instance cs_ring_like_op T
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  ring_like_op (ComplexSplit T) :=
  {| rngl_zero := cs_zero;
     rngl_add := cs_add;
     rngl_mul := cs_mul;
     rngl_opt_one := gc_opt_one;
     rngl_opt_opp_or_subt := gc_opt_opp_or_subt T;
     rngl_opt_inv_or_quot := gc_opt_inv_or_quot T;
     rngl_opt_eq_dec := gc_opt_eq_dec;
     rngl_opt_leb := None |}.

