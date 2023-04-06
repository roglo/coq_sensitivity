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

Definition glop i :=
  let n := 11 in
  let f i := (i - 1) mod n + 1 in
  map (λ ij, (f (fst ij), f (snd ij)))
    [(i + 1, i + 4); (i + 2, i + 7); (i + 3, i + 5); (i + 6, i + 10); (i + 8, i + 9)].

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

(* with this (personal) definition of "vect_cross_prod", the
   product of two "quaternions" (quat_mul below) is the product
   in normal quaternions if vect_size = 3, but also the product
   in complex numbers if vect_size = 1; perhaps also the product
   in octonions if vect_size = 7 (to be verified) *)

Definition vect_cross_prod {T} {ro : ring_like_op T} (u v : vector T) :=
  match vect_size u / 2 with
  | 0 =>
      (* cross product for complex *)
      mk_vect [0%L]
  | 1 =>
      (* cross product for quaternions *)
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

(* TODO: find a general formula for vect_cross_prod that works
   for any vector size, not only 1, 3 and 7 *)

(*
[[([1;2]]; [3;4]]; [(1,3); (2,4)]; [(1,4); (2,3)]]

[[([1;2]]; [3;4]; [5;6]];
 [([1;2]]; [3;5]; [4;6]];
 [([1;2]]; [3;6]; [4;5]];

 [([1;3]]; [2;4]; [5;6]];
 [([1;3]]; [2;5]; [4;6]];
 [([1;3]]; [2;6]; [4;5]];

 [([1;4]]; [2;3]; [5;6]];
 [([1;4]]; [2;5]; [3;6]];
 [([1;4]]; [2;6]; [3;5]];

 [([1;5]]; [2;3]; [4;6]];
 [([1;5]]; [2;4]; [3;6]];
 [([1;5]]; [2;6]; [3;4]];

 [([1;6]]; [2;3]; [4;5]];
 [([1;6]]; [2;4]; [3;5]];
 [([1;6]]; [2;5]; [3;4]];
*)

Fixpoint pouet A (a : A) (la : list A) :=
  match la with
  | [] => []
  | [b] => [[(a, b)]]
  | b :: c :: lc =>
      map (λ l, (a, b) :: l) (pouet c lc) ++
      map (λ l, (a, c) :: l) (pouet b lc)
  end.

Compute (pouet 1 [2;3;4;5;6]).

...

Fixpoint pouet A it (a : A) (la : list A) :=
  match it with
  | 0 => []
  | S it' =>
  match la with
  | [] => []
  | b :: lb =>
      match lb with
      | [] => [[(a, b)]]
      | c :: lc =>
          map (λ l, (a, b) :: l) (pouet it' c lc) ++
          map (λ l, (a, c) :: l) (pouet it' b lc) ++
          match lc with
          | [] => []
          | d :: ld =>
              map (λ l, (a, d) :: l) (pouet it' b (c :: ld)) ++
              match ld with
              | [] => []
              | e :: le =>
                  map (λ l, (a, e) :: l) (pouet it' b (c :: d :: le)) ++
...

Fixpoint pouet A it (a : A) (la : list A) :=
  match it with
  | 0 => []
  | S it' =>
  match la with
  | [] => []
  | [b] => [[(a, b)]]
  | [b; c] => []
  | b :: c :: ((d :: lc) as lb) =>
      map (λ l, (a, b) :: l) (pouet it' c lb) ++
      map (λ l, (a, c) :: l) (pouet it' b lb) ++
      map (λ l, (a, d) :: l) (pouet it' b (c :: lc))
  end
  end.

Compute (length (pouet 42 1 [2;3;4;5;6])).
Compute ((pouet 42 1 [2;3;4;5;6])).
Compute ((pouet 42 1 [2;3;4])).
...
Compute (length (pouet 1 [2;3;4;5;6])).
Compute (length (pouet 1 [2;3;4;5;6;7;8])).

...

Fixpoint glop la :=
  match l with
  | a :: la' =>
      pouet a la'

...

(*
Compute (let n := 7 in map (λ i, 2 ^ i) (seq 0 (n / 2))).
...
Compute (let n := 7 in map (λ i, (2 ^ i, (2 ^ i * 3 - 1) mod n + 1)) (seq 0 (n / 2))).
Compute (let n := 3 in map (λ i, (2 ^ i, (2 ^ i * 3 - 1) mod n + 1)) (seq 0 (n / 2))).
Compute (let n := 1 in map (λ i, (2 ^ i, (2 ^ i * 3 - 1) mod n + 1)) (seq 0 (n / 2))).
...
*)

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

(*
End a.

Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.

Compute (
  let qro := Q_ring_like_op in
  map (λ n,
  (quat_mul
     (mk_quat 0 (mk_vect (0 :: 0 :: 1 :: repeat 0 n)))
     (mk_quat 0 (mk_vect (1 :: repeat 0 (S (S n))))))%L)
  (seq 0 10)).
*)

Theorem quat_mul_comm :
  rngl_mul_is_comm = true →
  ∀ a b, quat_mul a b = quat_mul b a.
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
Theorem vect_cross_prod_anticomm :
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
apply (vect_cross_prod_comm Hic).
...


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
