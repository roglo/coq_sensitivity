(* complex, quaternion, octonions ... and other sorts of "...ions" *)

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

Arguments vect_comm {T ro} (u v)%V (i j)%nat.

Definition vect_cross_mul {T} {ro : ring_like_op T} (u v : vector T) :=
  let n := vect_size u in
  let f i := ∑ (j = 1, n / 2), vect_comm u v (i + j) (i + n - j) in
  mk_vect (map f (seq 1 n)).

Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.

Compute (
  let qro := Q_ring_like_op in
  vect_cross_mul (mk_vect [1]) (mk_vect [1]))%Q.
Compute (
  let qro := Q_ring_like_op in
  vect_cross_mul (mk_vect [1;0;0]) (mk_vect [0;1;0]))%Q.
Compute (
  let qro := Q_ring_like_op in
  vect_cross_mul (mk_vect [0;1;0]) (mk_vect [1;0;0]))%Q.
Compute (
  let qro := Q_ring_like_op in
  vect_cross_mul (mk_vect [1;0;0]) (mk_vect [0;0;1]))%Q.

Notation "U * V" := (vect_cross_mul U V) : V_scope.

Record nion T := mk_nion { Qre : T; Qim : vector T }.
Arguments mk_nion {T} Qre%L Qim%V.
Arguments Qre {T} n%L.
Arguments Qim {T} n%V.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition nion_add '(mk_nion a₁ v₁) '(mk_nion a₂ v₂) :=
  mk_nion (a₁ + a₂) (v₁ + v₂).

Definition nion_opp '(mk_nion a v) :=
  mk_nion (- a) (- v).

Definition nion_mul '(mk_nion a₁ v₁) '(mk_nion a₂ v₂) :=
  mk_nion ((a₁ * a₂)%L - ≺ v₁ , v₂ ≻) (a₁ × v₂ + a₂ × v₁ + v₁ * v₂).

End a.

Declare Scope H_scope.
Delimit Scope H_scope with H.
Notation "U * V" := (nion_mul U V) : H_scope.

Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.

(* trinions: i²=-1 j²=-1 ij=0 *)
(* i and j are zero divisors *)
(* not associative: (ii)j=-j, but i(ij)=0 *)
Compute (
  let qro := Q_ring_like_op in
  let i := mk_nion 0 (mk_vect [1;0]) in
  let j := mk_nion 0 (mk_vect [0;1]) in
(**)
  (i * (j * j))%H).

(* quaternions *)
Compute (
  let qro := Q_ring_like_op in
  let i := mk_nion 0 (mk_vect [1;0;0]) in
  let j := mk_nion 0 (mk_vect [0;1;0]) in
  let k := mk_nion 0 (mk_vect [0;0;1]) in
  map (λ e, (k*e)%H) [i;j;k]).

(* i*i=-1 i*j=k i*k=-j
   j*i=-k j*j=-1 j*k=i
   k*i=j k*j=-i k*k=-1
*)

(* quintinions *)
(* ii=-1 ij=0 ik=-j+l il=0 *)
(* ji=0 jj=-1 jk=0 jl=i-k *)
Compute (
  let qro := Q_ring_like_op in
  let i := mk_nion 0 (mk_vect [1;0;0;0]) in
  let j := mk_nion 0 (mk_vect [0;1;0;0]) in
  let k := mk_nion 0 (mk_vect [0;0;1;0]) in
  let l := mk_nion 0 (mk_vect [0;0;0;1]) in
  (j*l)%H).

(* sexinions *)
Compute (
  let qro := Q_ring_like_op in
  let e1 := mk_nion 0 (mk_vect [1;0;0;0;0]) in
  let e2 := mk_nion 0 (mk_vect [0;1;0;0;0]) in
  let e3 := mk_nion 0 (mk_vect [0;0;1;0;0]) in
  let e4 := mk_nion 0 (mk_vect [0;0;0;1;0]) in
  let e5 := mk_nion 0 (mk_vect [0;0;0;0;1]) in
  map (λ e, (e5*e)%H) [e1;e2;e3;e4;e5]).

(* e1*e1=-1 e1*e2=e4 e1*e3=-e2 e1*e4=e5 e1*e5=-e3
   e2*e1=-e4 e2*e2=-1 e2*e3=e5 e2*e4=-e3 e2*e5=e1
   e3*e1=e2 e3*e2=-e5 e3*e3=-1 e3*e4=e1 e3*e5=-e4
   e4*e1=-e5 e4*e2=e3 e4*e3=-e1 e4*e4=-1 e4*e5=e2
   e5*e1=e3 e5*e2=-e1 e5*e3=e4 e5*e4=-e2 e5*e5=-1
*)

(* septinions *)
Compute (
  let qro := Q_ring_like_op in
  let e1 := mk_nion 0 (mk_vect [1;0;0;0;0;0]) in
  let e2 := mk_nion 0 (mk_vect [0;1;0;0;0;0]) in
  let e3 := mk_nion 0 (mk_vect [0;0;1;0;0;0]) in
  let e4 := mk_nion 0 (mk_vect [0;0;0;1;0;0]) in
  let e5 := mk_nion 0 (mk_vect [0;0;0;0;1;0]) in
  let e6 := mk_nion 0 (mk_vect [0;0;0;0;0;1]) in
  map (λ e, (e3*e)%H) [e1;e2;e3;e4;e5;e6]).

(* e1*e1=-1 e1*e2=0 e1*e3=-e2+e5 e1*e4=0 e1*e5=-e3+e6 e1*e6=0
   e2*e1=0 e2*e2=-1 e2*e3=0 e2*e4=-e3+e6 e2*e5=0 e2*e6=e1-e4
...
   e3*e1= e3*e2= e3*e3= e3*e4= e3*e5= e3*e6=
   e4*e1= e4*e2= e4*e3= e4*e4= e4*e5= e4*e6=
   e5*e1= e5*e2= e5*e3= e5*e4= e5*e5= e5*e6=
*)

...

(* octonions *)
...
Time Compute (
  let qro := Q_ring_like_op in
  let e1 := mk_nion 0 (mk_vect [1;0;0;0;0;0;0]) in
  let e2 := mk_nion 0 (mk_vect [0;1;0;0;0;0;0]) in
  let e3 := mk_nion 0 (mk_vect [0;0;1;0;0;0;0]) in
  let e4 := mk_nion 0 (mk_vect [0;0;0;1;0;0;0]) in
  let e5 := mk_nion 0 (mk_vect [0;0;0;0;1;0;0]) in
  let e6 := mk_nion 0 (mk_vect [0;0;0;0;0;1;0]) in
  let e7 := mk_nion 0 (mk_vect [0;0;0;0;0;0;1]) in
  (e1*e4)%H).

(*
Finished transaction in 30.245 secs (28.591u,1.65s) (successful)
*)

(* e1*e1=-1 e1*e2=e5 e1*e3=-e2 e1*e4=e6 *)

...
Theorem vect_cross_mul_anticomm :
  rngl_has_opp = true →
  rngl_mul_is_comm = true →
  ∀ u v,
  vect_size u = vect_size v
  → (u * v = - v * u)%V.
Proof.
intros Hop Hic * Huv.
unfold "*"%V; f_equal.
destruct u as (la).
destruct v as (lb); cbn - [ "/" ].
cbn in Huv.
rewrite map_length.
rewrite <- Huv.
apply map_ext_in.
intros i Hi.
unfold vect_comm.
cbn - [ "/" ].
rewrite map_length.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  apply in_seq in Hi.
  do 2 rewrite Nat.add_sub.
  easy.
}
remember (∑ (j = _, _), _) as x; subst x.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  apply in_seq in Hi.
  do 2 rewrite Nat.add_sub.
  rewrite (List_map_nth' 0%L). 2: {
    apply Nat.mod_upper_bound.
    rewrite <- Huv; flia Hi.
  }
  rewrite (List_map_nth' 0%L). 2: {
    apply Nat.mod_upper_bound.
    rewrite <- Huv; flia Hi.
  }
  unfold rngl_sub.
  rewrite Hop.
  do 2 rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_opp_involutive Hop).
  rewrite rngl_add_comm.
  rewrite (fold_rngl_sub Hop).
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_comm Hic (nth _ lb _)).
  easy.
}
rewrite <- Huv.
easy.
Qed.

Theorem nion_mul_comm_anticomm :
  rngl_has_opp = true →
  rngl_mul_is_comm = true →
  ∀ n a b,
  vect_size (Qim a) = n
  → vect_size (Qim b) = n
  → nion_mul a b = if n <? 2 then nion_mul b a else nion_opp (nion_mul b a).
Proof.
intros Hop Hic n (a, u) (b, v) Hu Hv; cbn in Hu, Hv |-*.
move b before a.
rewrite (rngl_mul_comm Hic).
rewrite (vect_dot_mul_comm Hic).
rewrite (vect_cross_mul_anticomm Hop Hic _ _); [ | congruence ].
rewrite (vect_add_comm (a × v)%V).
unfold vect_cross_mul.
replace (vect_size (- v)) with (vect_size v). 2: {
  cbn; f_equal; symmetry.
  apply map_length.
}
rewrite if_ltb_lt_dec.
rewrite Hv.
destruct (lt_dec n 2) as [Hn2| Hn2]. {
  f_equal; f_equal; f_equal.
  apply map_ext_in.
  intros i Hi.
  rewrite Nat.div_small; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  easy.
}
apply Nat.nlt_ge in Hn2.
f_equal. {
(* ah oui, non, c'est pas anticommutatif, les nionernions *)
...
    f_equal. {
      f_equal.
    apply (vect_dot_mul_comm Hic).
}
rewrite (vect_add_comm (a × v)%V).
f_equal.
rewrite (vect_cross_mul_anticomm Hop Hic _ _); [ | congruence ].
unfold vect_cross_mul.
f_equal.
replace (vect_size (- v)) with (vect_size v). 2: {
  cbn; f_equal; symmetry.
  apply map_length.
}
rewrite Hv.
destruct (lt_dec n 2) as [Hn2| Hn2]. {
  apply map_ext_in.
  intros i Hi.
  apply in_seq in Hi.
  destruct n; [ easy | ].
  destruct n; [ | flia Hn2 ].
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  easy.
}
apply Nat.nlt_ge in Hn2.
...

(* to be completed... *)
