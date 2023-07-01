(* Attempt to implement rationals with the normal rationals of
   coq (library QArith) together with a field saying that the
   numerator and the denominator are coprimes. This allows to
   use normal equality instead of ==. Therefore rewrite is
   possible. *)

Set Implicit Arguments.
Require Import Utf8.

Require Import QArith.

Definition Z_pos_coprimes z p :=
  match z with
  | Z0 => if Pos.eq_dec p 1 then true else false
  | Zpos zp => if Pos.eq_dec (Pos.gcd zp p) 1 then true else false
  | Zneg zp => if Pos.eq_dec (Pos.gcd zp p) 1 then true else false
  end.

Record QG := mk_qg
  {qg_q : Q; qg_gcd : Z_pos_coprimes (Qnum qg_q) (Qden qg_q) = true}.

Theorem eq_QG_eq : ∀ q1 q2, q1 = q2 ↔ qg_q q1 = qg_q q2.
Proof.
intros.
split; intros Hq; [ now subst q2 | ].
destruct q1 as (q1, Hq1).
destruct q2 as (q2, Hq2).
cbn in Hq; subst q2.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

...

Definition QG_of_Q (q : Q) :=
  let g := Z.gcd (Qnum q) (Z.pos (Qden q)) in
  mk_qg (Qmake (Qnum q / g) (Qden q / g)).
