(* attempt to define algebraic numbers *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List ListNotations Init.Nat.

Require Import Misc RingLike.
Require Import Polynomial Matrix Determinant.

(* Sylvester matrix *)

Section a.

Context {A : Type}.
Context {ro : ring_like_op A}.
Context {rp : ring_like_prop A}.

Definition rlap_sylvester_list_list (rla rlb : list A) : list (list A) :=
  let m := length rla - 1 in
  let n := length rlb - 1 in
  map (λ i, repeat 0%L i ++ rla ++ repeat 0%L (n - 1 - i)) (seq 0 n) ++
  map (λ i, repeat 0%L i ++ rlb ++ repeat 0%L (m - 1 - i)) (seq 0 m).

Definition rlap_sylvester_mat (rla rlb : list A) : matrix A :=
  mk_mat (rlap_sylvester_list_list rla rlb).

Definition polyn_sylvester_mat (p q : polyn A) : matrix A :=
  mk_mat (rlap_sylvester_list_list (rev (lap p)) (rev (lap q))).

Definition resultant (p q : polyn A) :=
  det (polyn_sylvester_mat p q).

Theorem glop p q :
  lap q ≠ []
  → has_polyn_prop (lap p ° lap q) = true.
Proof.
intros Hq.
destruct p as (la, pa).
destruct q as (lb, pb).
move lb before la.
cbn in Hq.
cbn - [ lap_compose ].
apply Bool.orb_true_iff in pa, pb.
apply Bool.orb_true_iff.
destruct pa as [pa| pa]. {
  now apply is_empty_list_empty in pa; subst la; left.
}
destruct pb as [pb| pb]. {
  now apply is_empty_list_empty in pb; subst lb.
}
right.
Theorem last_lap_compose :
  rngl_has_opp_or_sous = true →
  ∀ la lb,
  last (la ° lb)%lap 0%L =
    if length lb =? 0 then hd 0%L la
    else (last la 0 * last lb 0 ^ (length la - 1))%L.
Proof.
intros Hos *.
unfold lap_compose.
rewrite if_bool_if_dec.
destruct (bool_dec _) as [Hbz| Hbz]. {
  apply Nat.eqb_eq, length_zero_iff_nil in Hbz; subst lb.
  unfold rlap_compose; cbn.
  erewrite List_fold_left_ext_in. 2: {
    intros b lb Hb.
    now rewrite lap_mul_0_r, lap_add_0_l.
  }
  destruct la as [| a]; [ easy | cbn ].
  now rewrite fold_left_app.
}
apply Nat.eqb_neq in Hbz.
unfold rlap_compose; cbn.
rewrite rev_involutive.
revert lb Hbz.
induction la as [| a] using rev_ind; intros; cbn. {
  symmetry; apply (rngl_mul_0_l Hos).
}
rewrite rev_app_distr; cbn.
rewrite app_length; cbn.
rewrite Nat.add_sub, last_last.
...
rewrite fold_iter_list.
specialize iter_list_op_fun_from_d as H1.
specialize (H1 (list A) A []).
rewrite (H1 (λ a b, (a * lb + b)%lap) [a]).
...
destruct lb as [| b]; [ easy | clear Hbz; cbn ].
destruct lb as [| b2]. {
...
iter_list_op_fun_from_d:
  ∀ (T A : Type) (d : T) (op : T → T → T) (a : T) (l : list A) (f : A → T),
    (∀ x : T, op d x = x)
    → (∀ x : T, op x d = x)
      → (∀ a0 b c : T, op a0 (op b c) = op (op a0 b) c)
        → iter_list l (λ (c : T) (i : A), op c (f i)) a =
          op a (iter_list l (λ (c : T) (i : A), op c (f i)) d)
...
destruct la as [| a2] using rev_ind; intros; cbn. {
  symmetry; apply rngl_mul_1_r.
}
clear IHla.
rewrite fold_right_app; cbn.
rewrite app_length; cbn.
rewrite Nat.add_1_r; cbn.
destruct lb as [| b]. {
  cbn; rewrite (rngl_mul_0_l Hos), (rngl_mul_0_r Hos).
  erewrite List_fold_right_ext_in. 2: {
    intros b c Hb.
    now rewrite lap_mul_0_r, lap_add_0_l.
  }
  clear a.
  induction la as [| a]; cbn. 2: {
...
destruct la as [| a2] using rev_ind; intros; cbn. {
  symmetry; apply rngl_mul_1_r.
}
clear IHla.
... ...
rewrite last_lap_compose.
...
destruct la as [| a] using rev_ind; [ easy | clear IHla ].
destruct lb as [| b] using rev_ind; [ easy | clear IHlb ].
clear Hq.
rewrite last_last in pa, pb.
unfold lap_compose.
rewrite fold_right_app; cbn.
...
*)

(*
résultant (selon le X) des polynomes Q et P(Y-X)
*)

End a.

(**)
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.

Compute (
  let rla := [2;3;5] in
  let rlb := [7;11] in
  last (rlap_compose rla rlb) 0).
...
2*7²
Compute (
  let la := [7;5;3;2] in
  let lb := [11;13] in
  last (lap_compose la lb) 0).
2*13³
(*
Compute (lap_compose Q_ring_like_op [-1;1] [1;0;1]).
Compute (lap_compose Q_ring_like_op [1;0;1] [-1;1]).
*)

Definition polyn_Q_ring_like_op :=
  @polyn_ring_like_op Q Q_ring_like_op Q_ring_like_prop eq_refl eq_refl
    (n_Sn _).

Check (@polyn_sylvester_mat _ polyn_Q_ring_like_op).
Check [mk_polyn [1;0;1] eq_refl]. (* x²+1) *)

Check (@lap_compose Q Q_ring_like_op).
Check lap_compose.
.
Print fold_right.
Theorem last_list_fold_right : ∀ A B (f : B → list A → list A) a l,
  last (fold_right f a l) = a.
...
erewrite List_fold_right_ext_in. 2: {
  intros c lc Hc.
  rewrite (lap_add_comm rp); cbn.
  easy.
}
...
  destruct la as [| a] using rev_ind; [ now left | right; cbn ].
  rewrite fold_right_app; cbn.
  rewrite last_last in pa.
  cbn.
...
}
...
Definition polyn_compose {A} {ro} (p q : polyn A) :=
  mk_polyn (lap_compose ro (lap p) (lap q)) (glop p q).

Print polyn_compose.

(* p sur K[x], p' sur L[x]
   calculer p (p') dans L[x]
ah non : tous les polynômes dans L[x]
voir lap_compose.
...
   Q[x] inclus dans Q[Q[x]].
*)
...

Check [mk_polyn [1;0;1] eq_refl]. (* x²+1) *)
Check [mk_polyn [-2;0;1] eq_refl]. (* x²-2) *)
Check (@mk_polyn (polyn Q)).
(*
Theorem glop :
  (@rngl_characteristic Q Q_ring_like_op Q_ring_like_prop) ≠ 1%nat.
Proof. easy. Show Proof.
...

Check (polyn_ring_like_op Q_ring_like_prop (n_Sn _)).
Check
  (@polyn_ring_like_op Q Q_ring_like_op Q_ring_like_prop eq_refl eq_refl (n_Sn _)).
Search rngl_characteristic.

Check mk_polyn.
Search has_polyn_prop.
*)

Compute (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4;5]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl)).
Compute (mat_nrows (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4;5]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl))).
Time Compute (det (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl))).
...
Compute (det (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4;5]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl))).
...
Compute (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9]).
Compute (mat_nrows (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (mat_ncols (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (is_square_matrix (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (let m := rlap_sylvester_mat [1;2;3;4] [6;7;8] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute (let m := rlap_sylvester_mat [1;2;3] [6;7] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute (let m := rlap_sylvester_mat [2] [6;7] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute (let m := rlap_sylvester_mat [2;3] [6] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
*)
