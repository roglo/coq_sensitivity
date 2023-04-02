(* quaternions *)

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Main.RingLike Main.MyVector.

Definition vect_comm {T} {ro : ring_like_op T} (u v : vector T) i j :=
  let i := (i - 1) mod vect_size u + 1 in
  let j := (j - 1) mod vect_size u + 1 in
  (vect_el u i * vect_el v j - vect_el u j * vect_el v i)%L.

(* with this (personal) definition of "vect_cross_prod", the
   product of two "quaternions" (quat_mul below) is the product
   in normal quaternions if vect_size = 3, but also the product
   in complex numbers if vect_size = 1; perhaps also the product
   in octonions (to be verified) *)

Definition vect_cross_prod {T} {ro : ring_like_op T} (u v : vector T) :=
  match vect_size u with
  | 1 =>
      (* cross product for complex *)
      mk_vect [0%L]
  | 3 =>
      (* cross product in quaternions *)
      let f i := vect_comm u v (i + 1) (i + 2) in
      mk_vect (map f (seq 1 (vect_size u)))
  | 7 =>
      (* cross product for octonions *)
      let f i :=
        (vect_comm u v (i + 1) (i + 3) +
         vect_comm u v (i + 2) (i + 6) +
         vect_comm u v (i + 4) (i + 5))%L
      in
      mk_vect (map f (seq 1 (vect_size u)))
  | _ => mk_vect []
  end.

Notation "U * V" := (vect_cross_prod U V) : V_scope.

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
