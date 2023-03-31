(* quaternions *)

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Main.RingLike Main.MyVector.

Definition vect_comm {T} {ro : ring_like_op T} (u v : vector T) i j :=
  (vect_el u i * vect_el v j - vect_el u j * vect_el v i)%L.

(* with this (personal) definition of "vect_mul", the product
   of two "quaternions" (quat_mul below) is the product of
   normal quaternions if vect_size = 3, but also the product
   of complex numbers if vect_size = 1 *)
Definition vect_mul {T} {ro : ring_like_op T} (u v : vector T) :=
  match vect_size u with
  | 1 => mk_vect [0%L]
  | 3 => mk_vect [vect_comm u v 2 3; vect_comm u v 3 1; vect_comm u v 1 2]
  | 7 =>
      mk_vect
        [vect_comm u v 2 4 + vect_comm u v 3 7 + vect_comm u v 5 6;
         vect_comm u v 3 5 + vect_comm u v 4 1 + vect_comm u v 6 7;
         vect_comm u v 4 6 + vect_comm u v 5 2 + vect_comm u v 7 1;
         vect_comm u v 5 7 + vect_comm u v 6 3 + vect_comm u v 1 2;
         vect_comm u v 6 1 + vect_comm u v 7 4 + vect_comm u v 2 3;
         vect_comm u v 7 2 + vect_comm u v 1 5 + vect_comm u v 3 4;
         vect_comm u v 1 3 + vect_comm u v 2 6 + vect_comm u v 4 5]%L
  | _ => mk_vect []
  end.

...

map
  (λ i,
     ∑ (j = 1, n / 2), vect_comm u v ((i + j - 1) mod n + 1) (
  ) (seq 1 n).

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
