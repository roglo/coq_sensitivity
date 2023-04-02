(* quaternions *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Main.Misc Main.RingLike.
Require Import Main.IterAdd Main.MyVector.

Definition vect_comm {T} {ro : ring_like_op T} (u v : vector T) i j :=
  let i := (i - 1) mod vect_size u + 1 in
  let j := (j - 1) mod vect_size u + 1 in
  (vect_el u i * vect_el v j - vect_el u j * vect_el v i)%L.

(* with this (personal) definition of "vect_cross_prod", the
   product of two "quaternions" (quat_mul below) is the product
   in normal quaternions if vect_size = 3, but also the product
   in complex numbers if vect_size = 1; perhaps also the product
   in octonions (to be verified) *)

Definition glop i :=
  let n := 7 in
  let f i := (i - 1) mod n + 1 in
  map (λ ij, (f (fst ij), f (snd ij)))
(*
    [(i + 1, i + 2); (i + 4, i + 6); (i + 5, i + 3)].
    [(i + 2, i + 3); (i + 4, i + 6); (i + 5, i + 1)].
*)
    [(i + 1, i + 3); (i + 2, i + 6); (i + 4, i + 5)].
(**)

Compute (map glop (seq 1 7)).
Compute (fold_left (λ la lb, app la lb) (map glop (seq 1 7)) []).
Require Import Main.SortingFun.
Check isort.
Print SortingFun.
Check pair_eqb.

Definition pair_le '(a, b) '(c, d) :=
  if lt_dec a c then true
  else if lt_dec c a then false
  else if lt_dec b d then true
  else if lt_dec d b then false
  else true.

Compute (isort pair_le (fold_left (λ la lb, app la lb) (map glop (seq 1 7)) [])).
(*
     = [(1, 2); (1, 3); (1, 6); (2, 3); (2, 4); (2, 7); (3, 1); (3, 4); (3, 5); (4, 2); 
       (4, 5); (4, 6); (5, 3); (5, 6); (5, 7); (6, 1); (6, 4); (6, 7); (7, 1); (7, 2); 
       (7, 5)]
     : list (nat * nat)
*)
(*
     = [(1, 2); (1, 3); (1, 4); (2, 3); (2, 4); (2, 5); (3, 4); (3, 5); (3, 6); (4, 5); 
       (4, 6); (4, 7); (5, 1); (5, 6); (5, 7); (6, 1); (6, 2); (6, 7); (7, 1); (7, 2); 
       (7, 3)]
     : list (nat * nat)
*)

About member.

(*
Fixpoint pouet it n i d l :=
  match it with
  | 0 => []
  | S it' =>
      if le_dec (i + d) n then
        if member (pair_eqb Nat.eqb Nat.eqb) (i, i + d) l then
          pouet it' n i (d + 1) l
*)

...

1 2
1 3 / 2 6 / 4 5

0 2 / 1 5 / 3 4
3 5 / 4 2 / 0 1
0 1 / 3 5 / 4 2

1 2 / 4 6 / 5 3

Definition vect_cross_prod {T} {ro : ring_like_op T} (u v : vector T) :=
  match vect_size u with
  | 1 =>
      (* cross product for complex *)
      mk_vect [0%L]
  | 3 =>
      (* cross product for quaternions *)
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

(* TODO: find a general formula for vect_cross_prod that works
   for any vector size, not only 1, 3 and 7 *)

...

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
Context {rp : ring_like_prop T}.

Definition quat_add '(mk_quat a₁ v₁) '(mk_quat a₂ v₂) :=
  mk_quat (a₁ + a₂) (v₁ + v₂).

Definition quat_mul '(mk_quat a₁ v₁) '(mk_quat a₂ v₂) :=
  mk_quat ((a₁ * a₂)%L - ≺ v₁ , v₂ ≻) (a₁ × v₂ + a₂ × v₁ + v₁ * v₂).

Definition Qi := mk_quat 0 (mk_vect [1; 0; 0]%L).
Definition Qj := mk_quat 0 (mk_vect [0; 1; 0]%L).
Definition Qk := mk_quat 0 (mk_vect [0; 0; 1]%L).

Theorem quat_mul_1 :
  rngl_has_opp = true →
  ∀ n,
  quat_mul
    (mk_quat 0 (mk_vect (1%L :: repeat 0%L n)))
    (mk_quat 0 (mk_vect (1%L :: repeat 0%L n))) =
  mk_quat (-1)%L (mk_vect (repeat 0%L (S n))).
Proof.
intros Hop *.
assert (Hos : rngl_has_opp_or_subt = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
move Hos before Hop.
unfold vect_add; cbn.
rewrite (rngl_mul_0_l Hos).
unfold vect_dot_mul; cbn.
rewrite rngl_mul_1_l.
unfold iter_list; cbn.
rewrite rngl_add_0_l.
unfold rngl_sub; rewrite Hop.
rewrite rngl_add_0_l.
unfold vect_mul_scal_l; cbn.
unfold vect_add; cbn.
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_l.
destruct n; cbn. {
  now rewrite rngl_add_0_l.
}
f_equal. {
  rewrite (rngl_mul_0_l Hos), rngl_add_0_r.
  f_equal.
  rewrite map2_diag.
  rewrite List_fold_left_map.
  induction n; [ easy | cbn ].
  now rewrite (rngl_mul_0_l Hos), rngl_add_0_r.
}
rewrite repeat_length.
destruct n. {
  cbn.
...

(* to be completed... *)
