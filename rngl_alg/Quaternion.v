(* complex, quaternion, octonions ... and other sorts of "...ions" *)

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

Theorem nion_mul_assoc :
  rngl_has_opp = true →
  rngl_mul_is_comm = true →
  ∀ n a b c,
  vect_size (Qim a) = n
  → vect_size (Qim b) = n
  → vect_size (Qim c) = n
  → ((a * b) * c)%H = (a * (b * c))%H.
Proof.
intros Hop Hic n (a, u) (b, v) (c, w) Hu Hv Hw; cbn in Hu, Hv, Hw |-*.
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
destruct (Nat.eq_dec n 3) as [Hn3| Hn3]. {
  move Hn3 at top; subst n.
  clear Hn2 Hn1 Hnz.
  unfold iter_seq, iter_list; cbn.
  do 8 rewrite rngl_add_0_l.
  do 3 rewrite (rngl_mul_sub_distr_r Hos).
  do 3 rewrite (rngl_mul_sub_distr_l Hos).
  do 6 rewrite rngl_mul_assoc.
  remember (_ * _ * _)%L as x eqn:Hx.
  remember (_ * _ * _)%L as y eqn:Hy in |-*.
  remember (_ * _ * _)%L as z eqn:Hz in |-*.
  remember (_ * _ * _)%L as t eqn:Ht in |-*.
  remember (_ * _ * _)%L as u eqn:Hu in |-*.
  remember (_ * _ * _)%L as v eqn:Hv in |-*.
  clear Hx Hy Hz Ht Hu Hv
(* ouais, ça va le faire, fastoche *)
...
Search (∑ (_ ∈ _), _ = ∑ (_ ∈ _), _).
Search (≺ _ * _, _ ≻).
Search (≺ _, _ * _ ≻).
Search (map2 _ (map _ _)).
...
apply map2_length.
Qed.
  now rewrite vect_mul_scal_size.
}
...

(* to be completed... *)
