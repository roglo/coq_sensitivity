(* complex, quaternion, octonions ... and other sorts of "...nions" *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Import Init.Nat.

Require Import Main.Misc Main.RingLike.
Require Import Main.IterAdd Main.MyVector.

Definition vect_comm {T} {ro : ring_like_op T} (u v : vector T) i j :=
  let i := (i - 1) mod vect_size u + 1 in
  let j := (j - 1) mod vect_size u + 1 in
  (vect_el u i * vect_el v j - vect_el u j * vect_el v i)%L.

Arguments vect_comm {T ro} (u v)%V (i j)%nat.

(* vector cross product in any dimension (not only 3 and 7)
   the dimension is given through the size of the input vectors u and v *)
Definition vect_cross_mul {T} {ro : ring_like_op T} (u v : vector T) :=
  let n := vect_size u in
  let f i := ∑ (j = 1, n / 2), vect_comm u v (i + j) (i + n - j) in
  mk_vect (map f (seq 1 n)).

Notation "U * V" := (vect_cross_mul U V) : V_scope.

(* generalization of quaternions
   actually represent scalars, complexes, quaternions, octonions, sedenions
   and any couple (scalar, vector) for vector of any dimension d.
     scalar → d=0
     complex → d=1
     quaternion → d=3
     octonion → d=7
     sedenion → d=15
   but any other value of d is usable. *)

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

Definition nion_conj '(mk_nion a v) :=
  mk_nion a (- v).

End a.

Declare Scope H_scope.
Delimit Scope H_scope with H.

Notation "- U" := (nion_opp U) : H_scope.
Notation "U ∗" := (nion_conj U) (at level 1, format "U ∗") : H_scope.
Notation "U * V" := (nion_mul U V) : H_scope.

Require Import ZArith.
Require Import RnglAlg.Zrl.
Open Scope Z_scope.

(* trinions: i²=-1 j²=-1 ij=0 *)
(* i and j are zero divisors *)
(* not associative: (ii)j=-j, but i(ij)=0 *)
Compute (
  let ro := Z_ring_like_op in
  let i := mk_nion 0 (mk_vect [1;0]) in
  let j := mk_nion 0 (mk_vect [0;1]) in
(**)
  (i * (j * j))%H).

(* quaternions *)
Compute (
  let ro := Z_ring_like_op in
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
  let ro := Z_ring_like_op in
  let i := mk_nion 0 (mk_vect [1;0;0;0]) in
  let j := mk_nion 0 (mk_vect [0;1;0;0]) in
  let k := mk_nion 0 (mk_vect [0;0;1;0]) in
  let l := mk_nion 0 (mk_vect [0;0;0;1]) in
  (j*l)%H).

(* sexinions *)
Compute (
  let ro := Z_ring_like_op in
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
  let ro := Z_ring_like_op in
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

(* octonions *)
(* very slow computing; I should make a version in ocaml if
   I want to test
Time Compute (
  let ro := Z_ring_like_op in
  let e1 := mk_nion 0 (mk_vect [1;0;0;0;0;0;0]) in
  let e2 := mk_nion 0 (mk_vect [0;1;0;0;0;0;0]) in
  let e3 := mk_nion 0 (mk_vect [0;0;1;0;0;0;0]) in
  let e4 := mk_nion 0 (mk_vect [0;0;0;1;0;0;0]) in
  let e5 := mk_nion 0 (mk_vect [0;0;0;0;1;0;0]) in
  let e6 := mk_nion 0 (mk_vect [0;0;0;0;0;1;0]) in
  let e7 := mk_nion 0 (mk_vect [0;0;0;0;0;0;1]) in
  (e3*e4)%H).

(*
Finished transaction in 23.527 secs (22.043u,1.48s) (successful)
*)

(* e1*e1=-1 e1*e2=e5 e1*e3=-e2 e1*e4=e6 *)
*)

Close Scope Z_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem vect_cross_mul_size :
  ∀ u v,
  vect_size u ≤ vect_size v
  → vect_size (u * v) = min (vect_size u) (vect_size v).
Proof.
intros * Huv.
unfold vect_size; cbn - [ "/" ].
rewrite List_map_seq_length.
symmetry.
do 2 rewrite fold_vect_size.
now apply Nat.min_l.
Qed.

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

Theorem nion_mul_comm :
  rngl_has_opp = true →
  rngl_mul_is_comm = true →
  ∀ n a b,
  vect_size (Qim a) = n
  → vect_size (Qim b) = n
  → n < 2
  → (a * b)%H = (b * a)%H.
Proof.
intros Hop Hic n (a, u) (b, v) Hu Hv Hn; cbn in Hu, Hv |-*.
move b before a.
rewrite (rngl_mul_comm Hic).
rewrite (vect_dot_mul_comm Hic).
rewrite (vect_cross_mul_anticomm Hop Hic _ _); [ | congruence ].
rewrite (vect_add_comm (a × v)%V).
unfold vect_cross_mul.
rewrite vect_opp_size.
rewrite Hv.
f_equal; f_equal; f_equal.
apply map_ext_in.
intros i Hi.
apply in_seq in Hi.
(*
unfold vect_comm.
rewrite vect_opp_size, Hv.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  do 2 rewrite (vect_opp_el Hop).
  unfold vect_el.
  do 2 rewrite Nat.add_sub.
  do 2 rewrite (rngl_mul_opp_l Hop).
  rewrite <- (rngl_opp_add_distr Hop).
  rewrite rngl_add_comm.
  rewrite (fold_rngl_sub Hop).
  easy.
}
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  unfold vect_el.
  do 2 rewrite Nat.add_sub.
  easy.
}
remember (∑ (j = _, _), _) as x; subst x.
symmetry.
remember (∑ (j = _, _), _) as x; subst x.
rewrite <- (rngl_opp_summation Hop).
remember (∑ (j = _, _), _) as x; subst x.
*)
rewrite Nat.div_small; [ | easy ].
rewrite rngl_summation_empty; [ | easy ].
rewrite rngl_summation_empty; [ | easy ].
easy.
Qed.

Theorem vect_dot_cross_mul_assoc :
  rngl_has_opp = true →
  ∀ n u v w,
  vect_size u = n
  → vect_size v = n
  → vect_size w = n
  → n ≤ 3
  → ≺ u * v, w ≻ = ≺ u, v * w ≻.
Proof.
intros Hop * Hu Hv Hw Hn3.
assert (Hos : rngl_has_opp_or_subt = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
move Hos before Hop.
unfold vect_dot_mul.
cbn - [ "/" ].
rewrite Hu, Hv.
rewrite map2_map_l, map2_map_r.
rewrite (map2_map_min 0 0%L).
rewrite (map2_map_min 0%L 0).
rewrite seq_length.
do 2 rewrite fold_vect_size.
rewrite Hu, Hw.
rewrite Nat.min_id.
do 2 rewrite rngl_summation_list_map.
erewrite rngl_summation_list_eq_compat. 2: {
  intros i Hi.
  apply in_seq in Hi.
  rewrite seq_nth; [ | easy ].
  easy.
}
symmetry.
erewrite rngl_summation_list_eq_compat. 2: {
  intros i Hi.
  apply in_seq in Hi.
  rewrite seq_nth; [ | easy ].
  easy.
}
symmetry.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  rewrite rngl_summation_list_empty; [ | easy ].
  rewrite rngl_summation_list_empty; [ | easy ].
  easy.
}
rewrite rngl_summation_seq_summation; [ | easy ].
rewrite rngl_summation_seq_summation; [ | easy ].
cbn - [ "/" "-" nth ].
destruct u as (la).
destruct v as (lb).
destruct w as (lc).
cbn in Hu, Hv, Hw.
rename Hu into Ha; rename Hv into Hb; rename Hw into Hc.
cbn - [ "/" "-" nth ].
unfold vect_comm.
unfold vect_el.
cbn - [ "/" "-" nth ].
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    rewrite Nat_sub_succ_1.
    rewrite Nat_sub_sub_swap.
    rewrite Nat_sub_succ_1.
    do 2 rewrite Nat.add_sub.
    rewrite Ha.
    easy.
  }
  remember (∑ (j = _, _), _) as x; subst x.
  easy.
}
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    rewrite Nat_sub_succ_1.
    rewrite Nat_sub_sub_swap.
    rewrite Nat_sub_succ_1.
    do 2 rewrite Nat.add_sub.
    rewrite Hb.
    easy.
  }
  remember (∑ (j = _, _), _) as x; subst x.
  easy.
}
symmetry.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  move Hn1 at top; subst n.
  unfold iter_seq, iter_list; cbn.
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  easy.
}
destruct (Nat.eq_dec n 2) as [Hn2| Hn2]. {
  move Hn2 at top; subst n.
  clear Hn1 Hnz.
  unfold iter_seq, iter_list; cbn.
  do 4 rewrite (rngl_sub_diag Hos).
  do 3 rewrite rngl_add_0_l.
  do 2 rewrite (rngl_mul_0_l Hos).
  do 2 rewrite (rngl_mul_0_r Hos).
  easy.
}
assert (H : n = 3) by flia Hn3 Hnz Hn1 Hn2.
clear Hn3 Hnz Hn1 Hn2.
move H at top; subst n.
unfold iter_seq, iter_list; cbn.
unfold rngl_sub; rewrite Hop.
do 8 rewrite rngl_add_0_l.
do 3 rewrite rngl_mul_add_distr_r.
do 3 rewrite rngl_mul_add_distr_l.
do 3 rewrite (rngl_mul_opp_l Hop).
do 3 rewrite (rngl_mul_opp_r Hop).
do 6 rewrite rngl_mul_assoc.
remember (_ * _ * _)%L as x eqn:Hx.
remember (_ * _ * _)%L as y eqn:Hy in |-*.
remember (_ * _ * _)%L as z eqn:Hz in |-*.
remember (_ * _ * _)%L as t eqn:Ht in |-*.
remember (_ * _ * _)%L as u eqn:Hu in |-*.
remember (_ * _ * _)%L as v eqn:Hv in |-*.
clear Hx Hy Hz Ht Hu Hv.
rewrite rngl_add_comm.
do 5 rewrite <- rngl_add_assoc.
f_equal.
rewrite (rngl_add_comm (- v)%L).
rewrite (rngl_add_comm (- t)%L).
do 6 rewrite <- rngl_add_assoc.
f_equal.
rewrite (rngl_add_comm (- y)%L).
rewrite (rngl_add_comm (- v)%L).
do 4 rewrite <- rngl_add_assoc.
f_equal.
rewrite (rngl_add_comm (- y)%L).
apply rngl_add_assoc.
Qed.

Theorem vect_cross_mul_add_distr_l :
  rngl_has_opp = true →
  ∀ n u v w,
  vect_size u = n
  → vect_size v = n
  → vect_size w = n
  → (u * (v + w))%V = (u * v + u * w)%V.
Proof.
intros Hop * Hu Hv Hw.
unfold vect_cross_mul, vect_add; cbn - [ "/" ].
f_equal.
do 2 rewrite (map2_map_min 0%L 0%L).
do 2 rewrite List_map_seq_length.
rewrite Nat.min_id.
rewrite <- seq_shift.
rewrite map_map.
do 2 rewrite fold_vect_size.
rewrite Hu, Hv, Hw, Nat.min_id.
apply map_ext_in.
intros i Hi.
apply in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
rewrite (List_map_nth' 0). 2: {
  now rewrite List_map_seq_length.
}
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0). 2: {
  now rewrite List_map_seq_length.
}
cbn - [ "/" minus ].
rewrite <- rngl_summation_add_distr.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite seq_nth; [ | easy ].
  cbn - [ "-" ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  cbn - [ "-" ].
  easy.
}
remember (∑ (j = _, _), _) as x; subst x.
symmetry.
apply rngl_summation_eq_compat.
intros j Hj.
unfold vect_comm.
cbn - [ "-" ].
do 2 rewrite Nat.add_sub.
rewrite Nat_sub_sub_swap.
do 2 rewrite Nat_sub_succ_1.
rewrite Hu.
assert (Hnz : n ≠ 0) by flia Hi.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now apply Nat.mod_upper_bound.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now apply Nat.mod_upper_bound.
}
rewrite seq_nth; [ | now apply Nat.mod_upper_bound ].
rewrite seq_nth; [ | now apply Nat.mod_upper_bound ].
cbn.
unfold vect_el.
do 2 rewrite Nat.add_sub.
remember (nth _ _ _) as x eqn:Hx.
remember (nth _ _ _) as y eqn:Hy in |-*.
remember (nth _ _ _) as z eqn:Hz in |-*.
remember (nth _ _ _) as t eqn:Ht in |-*.
remember (nth _ _ _) as a eqn:Ha in |-*.
remember (nth _ _ _) as b eqn:Hb in |-*.
do 2 rewrite rngl_mul_add_distr_l.
unfold rngl_sub.
rewrite Hop.
do 2 rewrite <- rngl_add_assoc.
f_equal.
rewrite (rngl_opp_add_distr Hop).
unfold rngl_sub; rewrite Hop.
rewrite (rngl_add_comm (- (t * a))%L).
rewrite <- rngl_add_assoc.
easy.
Qed.

Theorem vect_cross_mul_add_distr_r :
  rngl_has_opp = true →
  ∀ u v w,
  vect_size u = vect_size v
  → ((u + v) * w = u * w + v * w)%V.
Proof.
intros Hop * Huv.
unfold vect_cross_mul, vect_add; cbn - [ "/" ].
f_equal.
rewrite map2_length.
do 2 rewrite fold_vect_size.
rewrite <- Huv, Nat.min_id.
do 2 rewrite (map2_map_min 0%L 0%L).
do 2 rewrite List_map_seq_length.
rewrite Nat.min_id.
rewrite <- seq_shift.
rewrite map_map.
apply map_ext_in.
intros i Hi.
apply in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
do 2 rewrite fold_vect_size.
rewrite <- Huv, Nat.min_id.
rewrite (List_map_nth' 0). 2: {
  now rewrite List_map_seq_length.
}
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0). 2: {
  now rewrite List_map_seq_length.
}
cbn - [ "/" minus ].
rewrite <- rngl_summation_add_distr.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite seq_nth; [ | easy ].
  cbn - [ "-" ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  cbn - [ "-" ].
  easy.
}
remember (∑ (j = _, _), _) as x; subst x.
symmetry.
apply rngl_summation_eq_compat.
intros j Hj.
unfold vect_comm.
cbn - [ "-" ].
rewrite List_map_seq_length.
rewrite <- Huv.
rewrite Nat_sub_sub_swap.
do 2 rewrite Nat_sub_succ_1.
do 2 rewrite Nat.add_sub.
assert (Huz : vect_size u ≠ 0) by flia Hi.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now apply Nat.mod_upper_bound.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now apply Nat.mod_upper_bound.
}
rewrite seq_nth; [ | now apply Nat.mod_upper_bound ].
rewrite seq_nth; [ | now apply Nat.mod_upper_bound ].
cbn.
unfold vect_el.
do 2 rewrite Nat.add_sub.
remember (nth _ _ _) as x eqn:Hx.
remember (nth _ _ _) as y eqn:Hy in |-*.
remember (nth _ _ _) as z eqn:Hz in |-*.
remember (nth _ _ _) as t eqn:Ht in |-*.
remember (nth _ _ _) as a eqn:Ha in |-*.
remember (nth _ _ _) as b eqn:Hb in |-*.
do 2 rewrite rngl_mul_add_distr_r.
unfold rngl_sub.
rewrite Hop.
do 2 rewrite <- rngl_add_assoc.
f_equal.
rewrite (rngl_opp_add_distr Hop).
unfold rngl_sub; rewrite Hop.
rewrite (rngl_add_comm (- (t * b))%L).
rewrite <- rngl_add_assoc.
easy.
Qed.

Theorem vect_scal_cross_mul_assoc_l :
  rngl_has_opp_or_subt = true →
  ∀ a u v, (a × (u * v) = (a × u) * v)%V.
Proof.
intros Hos *.
unfold "×", "*"%V.
f_equal; cbn - [ "/" ].
rewrite map_length.
rewrite fold_vect_size.
rewrite map_map.
apply map_ext_in.
intros i Hi.
apply in_seq in Hi.
rewrite (rngl_mul_summation_distr_l Hos).
apply rngl_summation_eq_compat.
intros j Hj.
unfold vect_comm; cbn.
rewrite map_length.
do 2 rewrite Nat.add_sub.
rewrite fold_vect_size.
assert (Hsz : vect_size u ≠ 0) by flia Hi.
rewrite (List_map_nth' 0%L); [ | now apply Nat.mod_upper_bound ].
rewrite (List_map_nth' 0%L); [ | now apply Nat.mod_upper_bound ].
do 2 rewrite <- rngl_mul_assoc.
rewrite <- (rngl_mul_sub_distr_l Hos).
f_equal.
unfold vect_el.
do 2 rewrite Nat.add_sub.
easy.
Qed.

Theorem vect_cross_scal_mul_assoc :
  rngl_has_opp_or_subt = true →
  rngl_mul_is_comm = true →
  ∀ a u v,
  vect_size u = vect_size v
  → (u * (a × v) = a × (u * v))%V.
Proof.
intros Hos Hic * Huv.
unfold "*"%V, "×"%V.
f_equal.
cbn - [ "/" ].
rewrite map_map.
apply map_ext_in.
intros i Hi.
apply in_seq in Hi.
rewrite (rngl_mul_summation_distr_l Hos).
apply rngl_summation_eq_compat.
intros j Hj.
unfold vect_comm; cbn.
unfold vect_el.
do 2 rewrite Nat.add_sub.
assert (Huz : vect_size u ≠ 0) by flia Hi.
rewrite (List_map_nth' 0%L). 2: {
  rewrite fold_vect_size, <- Huv.
  now apply Nat.mod_upper_bound.
}
rewrite (List_map_nth' 0%L). 2: {
  rewrite fold_vect_size, <- Huv.
  now apply Nat.mod_upper_bound.
}
remember (nth _ _ _) as x eqn:Hx.
remember (nth _ _ _) as y eqn:Hy in |-*.
remember (nth _ _ _) as z eqn:Hz in |-*.
remember (nth _ _ _) as t eqn:Ht in |-*.
rewrite (rngl_mul_sub_distr_l Hos).
do 4 rewrite rngl_mul_assoc.
do 2 rewrite (rngl_mul_comm Hic a).
easy.
Qed.

Theorem vect_cross_mul_mul_r :
  rngl_has_opp = true →
  rngl_mul_is_comm = true →
  ∀ n u v w,
  n ∈ [0; 1; 3]
  → vect_size u = n
  → vect_size v = n
  → vect_size w = n
  → (u * (v * w) = ≺ u, w ≻ × v - ≺ u, v ≻ × w)%V.
Proof.
intros Hop Hic * Hn2 Hu Hv Hw.
assert (Hos : rngl_has_opp_or_subt = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
move Hos before Hop.
unfold "*"%V, vect_dot_mul, "×"%V, vect_sub, vect_add.
rewrite Hu, Hv.
cbn - [ "/" ].
f_equal.
rewrite map_map.
rewrite (map2_map_min 0%L 0%L).
do 2 rewrite map_length.
do 2 rewrite fold_vect_size.
rewrite Hv, Hw.
rewrite Nat.min_id.
rewrite <- seq_shift.
rewrite map_map.
apply map_ext_in.
intros i Hi.
apply in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
rewrite (List_map_nth' 0%L); [ | now rewrite fold_vect_size, Hv ].
rewrite (List_map_nth' 0%L); [ | now rewrite fold_vect_size, Hw ].
rewrite (fold_rngl_sub Hop).
rewrite (map2_map_min 0%L 0%L).
rewrite (map2_map_min 0%L 0%L).
do 3 rewrite fold_vect_size.
rewrite Hu, Hv, Hw, Nat.min_id.
do 2 rewrite rngl_summation_list_map.
rewrite (rngl_mul_summation_list_distr_r Hos).
rewrite (rngl_mul_summation_list_distr_r Hos).
rewrite <- (rngl_summation_list_sub_distr Hop).
rewrite rngl_summation_seq_summation; [ | flia Hi ].
symmetry.
remember (∑ (j = _, _), _) as x; subst x.
symmetry.
rewrite Nat.add_0_l.
unfold vect_comm, vect_el.
rewrite Hu, Hv.
cbn - [ "/" nth "-" ].
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite Nat_sub_succ_1.
  rewrite Nat_sub_sub_swap, Nat_sub_succ_1.
  do 2 rewrite Nat.add_sub.
  assert (Hnz : n ≠ 0) by flia Hi.
  rewrite (List_map_nth' 0). 2: {
    rewrite List_map_seq_length.
    now apply Nat.mod_upper_bound.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply Nat.mod_upper_bound.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite List_map_seq_length.
    now apply Nat.mod_upper_bound.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply Nat.mod_upper_bound.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    do 2 rewrite Nat.add_sub.
    rewrite seq_nth; [ | now apply Nat.mod_upper_bound ].
    cbn - [ "-" ].
    rewrite Nat_sub_sub_swap.
    do 2 rewrite Nat_sub_succ_1.
    easy.
  }
  remember (∑ (k = _, _), _) as x.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    do 2 rewrite Nat.add_sub.
    rewrite seq_nth; [ | now apply Nat.mod_upper_bound ].
    cbn - [ "-" ].
    rewrite Nat_sub_sub_swap.
    do 2 rewrite Nat_sub_succ_1.
    easy.
  }
  remember (∑ (k = _, _), _) as y in |-*.
  subst x y.
  easy.
}
remember (∑ (j = _, _), _) as x in |-*; subst x.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now move Hnz at top; subst n | ].
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  move Hn1 at top; subst n; clear Hnz.
  apply Nat.lt_1_r in Hi; subst i; cbn.
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_only_one.
  rewrite (rngl_mul_mul_swap Hic).
  symmetry; apply (rngl_sub_diag Hos).
}
destruct (Nat.eq_dec n 3) as [Hn3| Hn3]. {
  move Hn3 at top; subst n; clear Hnz Hn1 Hn2.
  cbn - [ "mod" ].
  rewrite rngl_summation_only_one.
  rewrite rngl_summation_only_one.
  rewrite rngl_summation_only_one.
  rewrite <- Nat.add_sub_assoc; [ | now apply -> Nat.succ_le_mono ].
  cbn - [ "mod" ].
  rewrite <- Nat.add_sub_assoc; [ | now apply -> Nat.succ_le_mono ].
  cbn - [ "mod" ].
  rewrite <- Nat.add_sub_assoc; [ | now apply -> Nat.succ_le_mono ].
  cbn - [ "mod" ].
  destruct i. {
    cbn.
    unfold iter_seq, iter_list; cbn.
    rewrite (rngl_mul_mul_swap Hic).
    rewrite (rngl_sub_diag Hos).
    rewrite (rngl_mul_mul_swap Hic).
    do 2 rewrite rngl_add_0_l.
    do 2 rewrite (rngl_mul_sub_distr_l Hos).
    rewrite (rngl_sub_sub_distr Hop).
    do 4 rewrite rngl_mul_assoc.
    rewrite (rngl_mul_mul_swap Hic _ (nth 2 (vect_list w) 0%L)).
    remember (_ * _ * _)%L as x eqn:Hx.
    remember (_ * _ * _)%L as y eqn:Hy in |-*.
    remember (_ * _ * _)%L as z eqn:Hz in |-*.
    remember (_ * _ * _)%L as t eqn:Ht in |-*.
    unfold rngl_sub; rewrite Hop.
    rewrite <- rngl_add_assoc; f_equal.
    apply rngl_add_comm.
  }
  destruct i. {
    cbn.
    unfold iter_seq, iter_list; cbn.
    do 2 rewrite (rngl_mul_sub_distr_l Hos).
    rewrite (rngl_sub_sub_distr Hop).
    do 4 rewrite rngl_mul_assoc.
    rewrite rngl_add_0_l.
    rewrite (rngl_mul_mul_swap Hic _ (nth 0 (vect_list w) 0%L)).
    rewrite (rngl_mul_mul_swap Hic _ (nth 1 (vect_list w) 0%L)).
    rewrite (rngl_mul_mul_swap Hic _ (nth 2 (vect_list w) 0%L)).
    rewrite (rngl_sub_diag Hos), rngl_add_0_r.
    remember (_ * _ * _)%L as x eqn:Hx.
    remember (_ * _ * _)%L as y eqn:Hy in |-*.
    remember (_ * _ * _)%L as z eqn:Hz in |-*.
    remember (_ * _ * _)%L as t eqn:Ht in |-*.
    unfold rngl_sub; rewrite Hop.
    rewrite rngl_add_comm.
    do 2 rewrite <- rngl_add_assoc.
    f_equal.
    now rewrite rngl_add_assoc, rngl_add_comm.
  }
  destruct i. {
    cbn.
    unfold iter_seq, iter_list; cbn.
    do 2 rewrite (rngl_mul_sub_distr_l Hos).
    rewrite (rngl_sub_sub_distr Hop).
    do 4 rewrite rngl_mul_assoc.
    rewrite rngl_add_0_l.
    rewrite (rngl_mul_mul_swap Hic _ (nth 0 (vect_list w) 0%L)).
    rewrite (rngl_mul_mul_swap Hic _ (nth 1 (vect_list w) 0%L)).
    rewrite (rngl_mul_mul_swap Hic _ (nth 2 (vect_list w) 0%L)).
    rewrite (rngl_sub_diag Hos), rngl_add_0_r.
    remember (_ * _ * _)%L as x eqn:Hx.
    remember (_ * _ * _)%L as y eqn:Hy in |-*.
    remember (_ * _ * _)%L as z eqn:Hz in |-*.
    remember (_ * _ * _)%L as t eqn:Ht in |-*.
    unfold rngl_sub; rewrite Hop.
    rewrite <- rngl_add_assoc.
    f_equal.
    apply rngl_add_comm.
  }
  flia Hi.
}
destruct Hn2 as [Hn2| Hn2]; [ now symmetry in Hn2 | ].
destruct Hn2 as [Hn2| Hn2]; [ now symmetry in Hn2 | ].
destruct Hn2 as [Hn2| Hn2]; [ now symmetry in Hn2 | ].
easy.
Qed.

Theorem vect_cross_mul_mul_l :
  rngl_has_opp = true →
  rngl_mul_is_comm = true →
  ∀ n u v w,
  n ∈ [0; 1; 3]
  → vect_size u = n
  → vect_size v = n
  → vect_size w = n
  → ((u * v) * w = ≺ u, w ≻ × v - ≺ v, w ≻ × u)%V.
Proof.
intros Hop Hic * Hn Hu Hv Hw.
rewrite (vect_cross_mul_anticomm Hop Hic). 2: {
  rewrite vect_cross_mul_size; rewrite Hu, Hv; [ | easy ].
  now rewrite Hw; apply Nat.min_l.
}
rewrite (@vect_cross_mul_mul_r Hop Hic (vect_size u)); cycle 1. {
  congruence.
} {
  rewrite vect_opp_size; congruence.
} {
  easy.
} {
  congruence.
}
do 2 rewrite (vect_opp_dot_mul_l Hop).
rewrite (vect_dot_mul_comm Hic).
unfold vect_sub.
rewrite (vect_mul_scal_l_opp_l Hop).
rewrite vect_add_comm.
f_equal.
rewrite <- (vect_mul_scal_l_opp_l Hop).
rewrite (vect_dot_mul_comm Hic).
now rewrite (rngl_opp_involutive Hop).
Qed.

Theorem nion_mul_assoc :
  rngl_has_opp = true →
  rngl_mul_is_comm = true →
  ∀ n a b c,
  n ∈ [0; 1; 3]
  → vect_size (Qim a) = n
  → vect_size (Qim b) = n
  → vect_size (Qim c) = n
  → ((a * b) * c)%H = (a * (b * c))%H.
Proof.
intros Hop Hic n (a, u) (b, v) (c, w) Hn3 Hu Hv Hw; cbn in Hu, Hv, Hw |-*.
assert (Hos : rngl_has_opp_or_subt = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
move Hos before Hop.
f_equal. {
  rewrite (rngl_mul_sub_distr_r Hos).
  rewrite (rngl_mul_sub_distr_l Hos).
  rewrite rngl_mul_assoc.
  do 2 rewrite <- (rngl_sub_add_distr Hos).
  f_equal.
  rewrite (rngl_mul_comm Hic).
  do 2 rewrite <- (vect_scal_mul_dot_mul_comm Hos).
  rewrite (vect_dot_mul_add_l n); [ | | | easy ]; cycle 1. {
    unfold vect_size; cbn.
    rewrite map2_length.
    do 2 rewrite map_length.
    do 2 rewrite fold_vect_size.
    rewrite Hv, Hu.
    apply Nat.min_id.
  } {
    unfold vect_size; cbn.
    now rewrite List_map_seq_length.
  }
  rewrite (vect_scal_mul_dot_mul_comm Hos).
  rewrite (vect_scal_mul_dot_mul_comm Hos).
  rewrite (vect_dot_mul_add_l n); [ | | | easy ]; cycle 1. {
    now rewrite vect_mul_scal_size.
  } {
    now rewrite vect_mul_scal_size.
  }
  rewrite (vect_scal_mul_dot_mul_comm Hos).
  rewrite (vect_scal_mul_dot_mul_comm Hos).
  rewrite (vect_dot_mul_add_r n); [ | easy | | ]; cycle 1. {
    rewrite vect_add_size.
    do 2 rewrite vect_mul_scal_size.
    rewrite Hw, Hv.
    apply Nat.min_id.
  } {
    rewrite vect_cross_mul_size; rewrite Hv, Hw; [ | easy ].
    apply Nat.min_id.
  }
  rewrite (vect_dot_mul_add_r n); [ | easy | | ]; cycle 1. {
    now rewrite vect_mul_scal_size.
  } {
    now rewrite vect_mul_scal_size.
  }
  do 2 rewrite (vect_dot_mul_scal_mul_comm Hos Hic).
  rewrite rngl_add_comm.
  do 3 rewrite <- rngl_add_assoc.
  f_equal; f_equal.
  rewrite rngl_add_comm.
  f_equal.
  apply (@vect_dot_cross_mul_assoc Hop n); [ easy | easy | easy | ].
  destruct Hn3 as [Hn3| Hn3]; [ now subst n | ].
  destruct Hn3 as [Hn3| Hn3]; [ now subst n; apply -> Nat.succ_le_mono | ].
  destruct Hn3 as [Hn3| Hn3]; [ now subst n; apply -> Nat.succ_le_mono | ].
  easy.
} {
  rewrite (vect_mul_scal_l_sub_distr_r Hop).
  do 4 rewrite vect_mul_scal_l_add_distr_l.
  do 4 rewrite vect_mul_scal_l_assoc.
  unfold vect_sub.
  do 9 rewrite <- vect_add_assoc.
  f_equal.
  rewrite vect_add_comm.
  rewrite (rngl_mul_comm Hic).
  do 3 rewrite <- vect_add_assoc.
  f_equal.
  rewrite vect_add_comm, <- vect_add_assoc.
  rewrite vect_add_comm.
  rewrite (vect_cross_mul_add_distr_r Hop). 2: {
    rewrite vect_mul_scal_size.
    rewrite vect_add_size.
    rewrite vect_mul_scal_size.
    rewrite vect_cross_mul_size; [ | now rewrite Hu, Hv ].
    now rewrite Hu, Hv, Nat.min_id, Nat.min_id.
  }
  do 2 rewrite (vect_scal_cross_mul_assoc_l Hos).
  do 3 rewrite <- vect_add_assoc.
  f_equal.
  rewrite (vect_cross_mul_add_distr_r Hop). 2: {
    rewrite vect_mul_scal_size.
    rewrite vect_cross_mul_size; rewrite Hu, Hv; [ | easy ].
    symmetry; apply Nat.min_id.
  }
  do 3 rewrite vect_add_assoc.
  rewrite vect_add_comm.
  rewrite vect_add_assoc.
  rewrite vect_add_comm.
  rewrite (vect_mul_scal_l_sub_distr_r Hop).
  rewrite (rngl_mul_comm Hic).
  unfold vect_sub.
  do 3 rewrite <- vect_add_assoc.
  f_equal.
  rewrite vect_add_comm; symmetry.
  rewrite vect_add_comm; symmetry.
  rewrite (@vect_cross_mul_add_distr_l Hop n); [ | easy | | ]; cycle 1. {
    now rewrite vect_mul_scal_size.
  } {
    rewrite vect_add_size.
    rewrite vect_mul_scal_size.
    rewrite Hv.
    rewrite vect_cross_mul_size; rewrite Hv, Hw; [ | easy ].
    rewrite Nat.min_id.
    apply Nat.min_id.
  }
  rewrite (vect_cross_scal_mul_assoc Hos Hic); [ | now rewrite Hu ].
  rewrite (vect_scal_cross_mul_assoc_l Hos).
  do 3 rewrite <- vect_add_assoc.
  f_equal.
  rewrite vect_add_assoc.
  rewrite (@vect_cross_mul_add_distr_l Hop n); [ | easy | | ]; cycle 1. {
    now rewrite vect_mul_scal_size.
  } {
    rewrite vect_cross_mul_size; rewrite Hv, Hw; [ | easy ].
    apply Nat.min_id.
  }
  rewrite (vect_cross_scal_mul_assoc Hos Hic); [ | congruence ].
  rewrite (vect_scal_cross_mul_assoc_l Hos).
  rewrite vect_add_comm.
  rewrite <- vect_add_assoc.
  f_equal.
  rewrite (@vect_cross_mul_mul_r Hop Hic n); [ | easy | easy | easy | easy ].
  rewrite (@vect_cross_mul_mul_l Hop Hic n); [ | easy | easy | easy | easy ].
  unfold vect_sub.
  do 2 rewrite <- vect_add_assoc.
  f_equal.
  apply vect_add_comm.
}
Qed.

Inspect 1.

...

(* to be completed... *)
