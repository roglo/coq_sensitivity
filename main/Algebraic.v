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
  → has_polyn_prop (lap_compose ro (lap p) (lap q)) = true.
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
destruct la as [| a] using rev_ind; [ easy | clear IHla ].
destruct lb as [| b] using rev_ind; [ easy | clear IHlb ].
move b before a.
clear Hq.
rewrite last_last in pa, pb.
unfold lap_compose.
rewrite fold_right_app; cbn.
revert a b pa pb lb.
induction la as [| c]; intros; [ easy | ].
cbn.
remember (fold_right _ _ _) as lc eqn:Hlc.
Search (_ * (_ ++ _))%lap.
destruct lb as [| b']; cbn.
cbn in Hlc.
destruct lc as [| c']; cbn.
symmetry in Hlc.
...

(*
résultant (selon le X) des polynomes Q et P(Y-X)
*)

End a.

(**)
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.

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
