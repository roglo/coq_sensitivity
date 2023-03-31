(* quaternions *)

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Main.RingLike Main.MyVector.

(* with this (personal) definition of "vect_mul", the product
   of two "quaternions" (quat_mul below) is the product of
   complex numbers if vect_size = 1 and the product of normal
   quaternions if vect_size = 3 *)
Definition vect_mul {T} {ro : ring_like_op T} (u v : vector T) :=
  match vect_size u with
  | 1 => mk_vect [0%L]
  | 3 =>
      mk_vect
        [vect_el u 2 * vect_el v 3 - vect_el u 3 * vect_el v 2;
         vect_el u 3 * vect_el v 1 - vect_el u 1 * vect_el v 3;
         vect_el u 1 * vect_el v 2 - vect_el u 2 * vect_el v 1]%L
  | _ => mk_vect []
  end.

Notation "U * V" := (vect_mul U V) : V_scope.

Record quat T := mk_quat { Qre : T; Qim : vector T }.
Arguments mk_quat {T} Qre%L Qim%V.
Arguments Qre {T} q%L.
Arguments Qim {T} q%V.

Declare Scope quat_scope.
Delimit Scope quat_scope with H.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
(*
Context {rp : ring_like_prop T}.
*)

Definition quat_add '(mk_quat a₁ v₁) '(mk_quat a₂ v₂) :=
  mk_quat (a₁ + a₂) (v₁ + v₂).

Definition quat_mul '(mk_quat a₁ v₁) '(mk_quat a₂ v₂) :=
  mk_quat ((a₁ * a₂)%L - ≺ v₁ , v₂ ≻) (a₁ × v₂ + a₂ × v₁ + v₁ * v₂).

Definition Qi := mk_quat 0 (mk_vect [1; 0; 0]%L).
Definition Qj := mk_quat 0 (mk_vect [0; 1; 0]%L).
Definition Qk := mk_quat 0 (mk_vect [0; 0; 1]%L).

(* to be completed... *)
