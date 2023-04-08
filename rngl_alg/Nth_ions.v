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

Definition glop i :=
  let n := 11 in
  let f i := (i - 1) mod n + 1 in
  map (λ ij, (f (fst ij), f (snd ij)))
    [(i + 1, i + 10); (i + 2, i + 9); (i + 3, i + 8); (i + 4, i + 7); (i + 5, i + 6)].

(*
Definition glop i :=
  let n := 9 in
  let f i := (i - 1) mod n + 1 in
  map (λ ij, (f (fst ij), f (snd ij)))
    [(i + 1, i + 3); (i + 2, i + 5); (i + 4, i + 8); (i + 6, i + 7)].
*)

Require Import Main.SortingFun.

Definition pair_le '(a, b) '(c, d) :=
  if lt_dec a c then true
  else if lt_dec c a then false
  else if lt_dec b d then true
  else if lt_dec d b then false
  else true.

Compute (length (isort pair_le (fold_left (λ la lb, app la lb) (map glop (seq 1 11)) []))).
Compute (isort pair_le (map (λ la, if fst la <? snd la then la else (snd la, fst la)) (fold_left (λ la lb, app la lb) (map glop (seq 1 11)) []))).
Compute (isort pair_le (fold_left (λ la lb, app la lb) (map glop (seq 1 11)) [])).
(*
     = [(1, 2); (1, 3); (1, 5); (2, 3); (2, 4); (2, 6); 
       (3, 4); (3, 5); (3, 7); (4, 1); (4, 5); (4, 6); 
       (5, 2); (5, 6); (5, 7); (6, 1); (6, 3); (6, 7); 
       (7, 1); (7, 2); (7, 4)]
*)

(* new version (experiment) *)

Definition vect_cross_mul {T} {ro : ring_like_op T} (u v : vector T) :=
  let n := vect_size u in
  let f i := ∑ (j = 1, n / 2), vect_comm u v (i + j) (i + n - j) in
  mk_vect (map f (seq 1 n)).

(*
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

(* old version *)

(* with this (personal) definition of "vect_cross_mul", the
   product of two "nionernions" (nion_mul below) is the product
   in normal nionernions if vect_size = 3, but also the product
   in complex numbers if vect_size = 1; perhaps also the product
   in octonions if vect_size = 7 (to be verified) *)

Definition vect_cross_mul {T} {ro : ring_like_op T} (u v : vector T) :=
  match vect_size u / 2 with
  | 0 =>
      (* cross product for complex *)
      mk_vect [0%L]
  | 1 =>
      (* cross product for nionernions *)
      let f i := vect_comm u v (i + 1) (i + 2) in (* Δ=1 *)
      mk_vect (map f (seq 1 (vect_size u)))
  | 2 =>
      (* cross product for sexonions *)
      let f i :=
        (vect_comm u v (i + 1) (i + 4) +  (* Δ=3 *)
         vect_comm u v (i + 2) (i + 3))%L (* Δ=1 *)
      in
      mk_vect (map f (seq 1 (vect_size u)))
  | 3 =>
      (* cross product for octonions *)
      let f i :=
        (vect_comm u v (i + 1) (i + 3) +  (* Δ=2 *)
         vect_comm u v (i + 2) (i + 6) +  (* Δ=4 *)
         vect_comm u v (i + 4) (i + 5))%L (* Δ=1 *)
      in
      mk_vect (map f (seq 1 (vect_size u)))
  | 4 =>
      let f i :=
        (vect_comm u v (i + 1) (i + 3) +  (* Δ=2 *)
         vect_comm u v (i + 2) (i + 5) +  (* Δ=3 *)
         vect_comm u v (i + 4) (i + 8) +  (* Δ=4 *)
         vect_comm u v (i + 6) (i + 7))%L (* Δ=1 *)
      in
      mk_vect (map f (seq 1 (vect_size u)))
  | 5 =>
      let f i :=
        (vect_comm u v (i + 1) (i + 4) +  (* Δ=3 *)
         vect_comm u v (i + 2) (i + 7) +  (* Δ=5 *)
         vect_comm u v (i + 3) (i + 5) +  (* Δ=2 *)
         vect_comm u v (i + 6) (i + 10) + (* Δ=4 *)
         vect_comm u v (i + 8) (i + 9))%L (* Δ=1 *)
      in
      mk_vect (map f (seq 1 (vect_size u)))
  | _ => mk_vect []
  end.

Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.

Compute (
  let qro := Q_ring_like_op in
  vect_cross_mul (mk_vect [1]) (mk_vect [1]))%Q.
Compute (
  let qro := Q_ring_like_op in
  vect_cross_mul (mk_vect [1;0;0]) (mk_vect [0;1;0]))%Q.

...

(* TODO: find a general formula for vect_cross_mul that works
   for any vector size, not only 1, 3 and 7 *)

(*
[[([1;2]]; [3;4]]; [(1,3); (2,4)]; [(1,4); (2,3)]]
Compute (
[[(1,2); (3,4); (5,6)];
 [(1,2); (3,5); (4,6)];
 [(1,2); (3,6); (4,5)];

 [(1,3); (2,4); (5,6)];
 [(1,3); (2,5); (4,6)];
 [(1,3); (2,6); (4,5)];

 [(1,4); (2,3); (5,6)];
 [(1,4); (2,5); (3,6)];
 [(1,4); (2,6); (3,5)];

 [(1,5); (2,3); (4,6)];
 [(1,5); (2,4); (3,6)];
 [(1,5); (2,6); (3,4)];

 [(1,6); (2,3); (4,5)];
 [(1,6); (2,4); (3,5)];
 [(1,6); (2,5); (3,4)]]).
*)

Fixpoint comb_elem_rest A (la : list A) :=
  match la with
  | [] => []
  | a :: lb =>
      (a, lb) :: map (λ al, (fst al, a :: snd al)) (comb_elem_rest lb)
  end.

Fixpoint pair_comb_loop A it (la : list A) : list (list (A * A)) :=
  match it with
  | 0 => []
  | S it' =>
      match la with
      | [] => []
      | a :: lb =>
          flat_map
            (λ bl,
              match pair_comb_loop it' (snd bl) with
              | [] => [[(a, fst bl)]]
              | ll' => map (λ (l : list (A * A)), (a, fst bl) :: l) ll'
              end)
            (comb_elem_rest lb)
      end
  end.

Definition pair_comb A (la : list A) := pair_comb_loop (length la) la.

Compute (pair_comb [1;2;3;4;5;6]).
Compute (pair_comb [1;2;3;4]).
Compute (pair_comb [1;2;3;4;5;6]).
Compute (pair_comb [1;2]).
Compute (pair_comb [1;2;3;4]).
Compute (pair_comb [1;2;3;4;5;6;7]).

Fixpoint glip (la : list (nat * nat)) :=
  match la with
  | [] => []
  | (a, b) :: lb => (b - a) :: glip lb
  end.

Fixpoint has_no_dup (la : list nat) :=
  match la with
  | [] => true
  | a :: lb =>
      if member Nat.eqb a lb then false
      else has_no_dup lb
  end.

Compute (pair_comb [1;2;3;4;5;6]).
Compute (map glip (pair_comb [1;2;3;4;5;6])).
Compute (map (λ i, (i, glip i)) (pair_comb [1;2;3;4;5;6])).
Compute (filter (λ ij, has_no_dup (snd ij)) (map (λ i, (i, glip i)) (pair_comb [1;2;3;4;5;6]))).

...

(*
Compute (
[[(1,2); (3,4); (5,6)];
 [(1,2); (3,5); (4,6)];
 [(1,2); (3,6); (4,5)];

 [(1,3); (2,4); (5,6)];
 [(1,3); (2,5); (4,6)];
 [(1,3); (2,6); (4,5)];

 [(1,4); (2,3); (5,6)];
 [(1,4); (2,5); (3,6)];
 [(1,4); (2,6); (3,5)];

 [(1,5); (2,3); (4,6)];
 [(1,5); (2,4); (3,6)];
 [(1,5); (2,6); (3,4)];

 [(1,6); (2,3); (4,5)];
 [(1,6); (2,4); (3,5)];
 [(1,6); (2,5); (3,4)]]).
*)

...

(*
Compute (let n := 7 in map (λ i, 2 ^ i) (seq 0 (n / 2))).
...
Compute (let n := 7 in map (λ i, (2 ^ i, (2 ^ i * 3 - 1) mod n + 1)) (seq 0 (n / 2))).
Compute (let n := 3 in map (λ i, (2 ^ i, (2 ^ i * 3 - 1) mod n + 1)) (seq 0 (n / 2))).
Compute (let n := 1 in map (λ i, (2 ^ i, (2 ^ i * 3 - 1) mod n + 1)) (seq 0 (n / 2))).
...
*)

Notation "U * V" := (vect_cross_mul U V) : V_scope.

Record nion T := mk_nion { Qre : T; Qim : vector T }.
Arguments mk_nion {T} Qre%L Qim%V.
Arguments Qre {T} q%L.
Arguments Qim {T} q%V.

Declare Scope nion_scope.
Delimit Scope nion_scope with H.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition nion_add '(mk_nion a₁ v₁) '(mk_nion a₂ v₂) :=
  mk_nion (a₁ + a₂) (v₁ + v₂).

Definition nion_mul '(mk_nion a₁ v₁) '(mk_nion a₂ v₂) :=
  mk_nion ((a₁ * a₂)%L - ≺ v₁ , v₂ ≻) (a₁ × v₂ + a₂ × v₁ + v₁ * v₂).

Definition Qi := mk_nion 0 (mk_vect [1; 0; 0]%L).
Definition Qj := mk_nion 0 (mk_vect [0; 1; 0]%L).
Definition Qk := mk_nion 0 (mk_vect [0; 0; 1]%L).

(*
End a.

Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.

Compute (
  let qro := Q_ring_like_op in
  map (λ n,
  (nion_mul
     (mk_nion 0 (mk_vect (0 :: 0 :: 1 :: repeat 0 n)))
     (mk_nion 0 (mk_vect (1 :: repeat 0 (S (S n))))))%L)
  (seq 0 10)).
*)

Theorem nion_mul_comm :
  rngl_mul_is_comm = true →
  ∀ a b, nion_mul a b = nion_mul b a.
Proof.
intros Hic (a, u) (b, v); cbn.
f_equal. {
  rewrite (rngl_mul_comm Hic).
  f_equal.
  apply (vect_dot_mul_comm Hic).
}
rewrite (vect_add_comm (a × v)%V).
f_equal.
Locate "*"%V.
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
remember (length la / 2) as n eqn:Hn; symmetry in Hn.
destruct n; [ easy | ].
destruct n. {
  f_equal.
  apply map_ext_in.
  intros i Hi.
  apply in_seq in Hi.
  unfold vect_comm; cbn.
  rewrite map_length.
  do 5 rewrite Nat.add_sub.
  rewrite <- Nat.add_sub_assoc; [ cbn | now apply -> Nat.succ_le_mono ].
  rewrite List_map_nth' with (a := 0%L). 2: {
    apply Nat.mod_upper_bound.
    rewrite <- Huv; flia Hi.
  }
  rewrite List_map_nth' with (a := 0%L). 2: {
    apply Nat.mod_upper_bound.
    rewrite <- Huv; flia Hi.
  }
  rewrite <- Huv.
  do 2 rewrite (rngl_mul_opp_l Hop).
  unfold rngl_sub at 2.
  rewrite Hop.
  rewrite rngl_add_comm.
  rewrite (rngl_opp_involutive Hop).
  rewrite (rngl_mul_comm Hic).
  unfold rngl_sub at 1.
  rewrite Hop.
  f_equal; f_equal.
  apply (rngl_mul_comm Hic).
}
destruct n. {
  f_equal.
  apply map_ext_in.
  intros i Hi.
  apply in_seq in Hi.
  unfold vect_comm; cbn.
  rewrite map_length.
  do 9 rewrite Nat.add_sub.
  rewrite <- Nat.add_sub_assoc; [ cbn | now apply -> Nat.succ_le_mono ].
  rewrite <- Nat.add_sub_assoc; [ cbn | now apply -> Nat.succ_le_mono ].
  rewrite <- Nat.add_sub_assoc; [ cbn | now apply -> Nat.succ_le_mono ].
  rewrite List_map_nth' with (a := 0%L). 2: {
    apply Nat.mod_upper_bound.
    rewrite <- Huv; flia Hi.
  }
  rewrite List_map_nth' with (a := 0%L). 2: {
    apply Nat.mod_upper_bound.
    rewrite <- Huv; flia Hi.
  }
  rewrite List_map_nth' with (a := 0%L). 2: {
    apply Nat.mod_upper_bound.
    rewrite <- Huv; flia Hi.
  }
  rewrite List_map_nth' with (a := 0%L). 2: {
    apply Nat.mod_upper_bound.
    rewrite <- Huv; flia Hi.
  }
  rewrite <- Huv.
  do 4 rewrite (rngl_mul_opp_l Hop).
  unfold rngl_sub.
  rewrite Hop.
  do 2 rewrite (rngl_opp_involutive Hop).
  f_equal; rewrite rngl_add_comm. {
    now f_equal; rewrite (rngl_mul_comm Hic).
  } {
    now f_equal; rewrite (rngl_mul_comm Hic).
  }
}
destruct n. {
(* ouais bon, ça a l'air bon, mais ça serait mieux avec une formule générale
   pour le produit vectoriel *)
...
revert lb.
induction la as [| a]; intros; cbn; [ now rewrite map2_nil_r | ].
destruct lb as [| b]; [ easy | cbn ].
rewrite rngl_add_comm; f_equal.
apply IHla.
Qed.
... ...
apply (vect_cross_mul_comm Hic).
...


Theorem nion_mul_1 :
  rngl_has_opp = true →
  ∀ n,
  nion_mul
    (mk_nion 0 (mk_vect (1%L :: repeat 0%L n)))
    (mk_nion 0 (mk_vect (1%L :: repeat 0%L n))) =
  mk_nion (-1)%L (mk_vect (repeat 0%L (S n))).
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
destruct n; cbn; [ now rewrite rngl_add_0_l | ].
f_equal. {
  rewrite (rngl_mul_0_l Hos), rngl_add_0_r.
  f_equal.
  rewrite map2_diag.
  rewrite List_fold_left_map.
  induction n; [ easy | cbn ].
  now rewrite (rngl_mul_0_l Hos), rngl_add_0_r.
}
destruct n. {
  cbn; unfold vect_comm; cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  now rewrite (rngl_sub_0_r Hos).
}
destruct n. {
  cbn; unfold vect_comm; cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  now rewrite (rngl_sub_0_r Hos).
}
destruct n. {
  cbn; unfold vect_comm; cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  rewrite (rngl_sub_0_r Hos).
  now rewrite rngl_add_0_l.
}
destruct n. {
  cbn; unfold vect_comm; cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  rewrite (rngl_sub_0_r Hos).
  now rewrite rngl_add_0_l.
}
destruct n. {
  cbn; unfold vect_comm; cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  rewrite (rngl_sub_0_r Hos).
  now do 2 rewrite rngl_add_0_l.
}
destruct n. {
  cbn; unfold vect_comm; cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  rewrite (rngl_sub_0_r Hos).
  now do 2 rewrite rngl_add_0_l.
}
destruct n. {
  cbn; unfold vect_comm; cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  rewrite (rngl_sub_0_r Hos).
  now do 3 rewrite rngl_add_0_l.
}
destruct n. {
  cbn; unfold vect_comm; cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  rewrite (rngl_sub_0_r Hos).
  now do 3 rewrite rngl_add_0_l.
}
destruct n. {
  cbn; unfold vect_comm; cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  rewrite (rngl_sub_0_r Hos).
  now do 4 rewrite rngl_add_0_l.
}
destruct n. {
  cbn; unfold vect_comm; cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  do 3 rewrite rngl_add_0_l.
  rewrite (rngl_sub_0_r Hos).
  now do 4 rewrite rngl_add_0_l.
}
destruct n. {
  cbn; unfold vect_comm; cbn.
...

(* to be completed... *)
*)
