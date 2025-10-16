(* Polynomial.v *)

(* polynomials on a RingLike *)

Set Nested Proofs Allowed.

Require Import Stdlib.Arith.Arith.
Import List.ListNotations Init.Nat.
Require Import RingLike.Utf8.
Require Import RingLike.Core.
Require Import RingLike.PermutationFun.
Require Import RingLike.IterAdd.
Require Import RingLike.IterAnd.
Require Import RingLike.Lap_algebra.
Require Import RingLike.Polynomial_algebra.

Require Import Misc.
Require Import SortingFun.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hos : rngl_has_opp_or_psub T = true).
Context (Hed : rngl_has_eq_dec T = true).

Theorem lap_norm_idemp : ∀ la, lap_norm (lap_norm la) = lap_norm la.
Proof.
intros.
unfold lap_norm.
rewrite List.rev_involutive.
now rewrite strip_0s_idemp.
Qed.

Definition polyn_rem (pa pb : polyn T) : polyn T :=
  let lq := lap_rem (lap pa) (lap pb) in
  mk_polyn lq
    (lap_rem_is_norm Hed (lap pa) (lap pb) (lap_prop pa) (lap_prop pb)).

Definition rlap_horner {A} (zero : A) (add mul : A → A → A) rla x :=
  iter_list rla (λ accu a, add (mul accu x) a) zero.

Definition eval_rlap :=
  rlap_horner 0%L rngl_add rngl_mul.

Definition eval_lap la x :=
  eval_rlap (List.rev la) x.

Definition eval_polyn pol :=
  eval_lap (lap pol).

Definition rlap_compose rla rlb :=
  rlap_horner [] lap_add lap_mul (List.map (λ a, [a]) rla) (List.rev rlb).

Definition lap_compose la lb :=
  rlap_compose (List.rev la) (List.rev lb).

Definition polyn_compose p q :=
  polyn_of_norm_lap (lap_compose (lap p) (lap q)).

Definition monom (p : polyn T) i :=
  polyn_of_norm_lap [List.nth i (lap p) 0%L].

Theorem lap_norm_lap : ∀ p, lap_norm (lap p) = lap p.
Proof.
intros p.
apply (has_polyn_prop_lap_norm Hed).
apply lap_prop.
Qed.

Let Heo := rngl_has_eq_dec_or_is_ordered_l Hed.

Theorem lap_norm_lap_rngl_summation :
  let rol := lap_ring_like_op Heo in
  let rop := polyn_ring_like_op Hos Hed in
  ∀ b e f,
  lap_norm (lap (∑ (i = b, e), f i)) = lap_norm (∑ (i = b, e), lap (f i)).
Proof.
intros.
unfold iter_seq, iter_list.
remember (S e - b) as n eqn:Hn.
clear e Hn.
cbn.
revert b.
induction n; intros; [ easy | ].
rewrite List.seq_S; cbn.
do 2 rewrite List.fold_left_app.
cbn - [ lap_norm ].
rewrite <- (lap_add_norm_idemp_l Heo).
rewrite IHn.
rewrite (lap_add_norm_idemp_l Heo).
apply lap_norm_idemp.
Qed.

Theorem lap_norm_rngl_summation_idemp :
  let rol := lap_ring_like_op Heo in
  ∀ b e f,
  lap_norm (∑ (i = b, e), lap_norm (f i)) = lap_norm (∑ (i = b, e), f i).
Proof.
intros.
unfold iter_seq, iter_list.
remember (S e - b) as n eqn:Hn.
clear e Hn.
revert b.
induction n; intros; [ easy | ].
rewrite List.seq_S.
do 2 rewrite List.fold_left_app.
cbn - [ lap_norm ].
rewrite <- (lap_add_norm_idemp_l Heo).
rewrite IHn.
rewrite (lap_add_norm_idemp_l Heo).
rewrite (lap_add_norm_idemp_r Heo).
easy.
Qed.

Theorem lap_cons : ∀ a la, a :: la = ([a] + [0; 1]%L * la)%lap.
Proof.
intros.
destruct la as [| a2]; [ now cbn; rewrite rngl_add_0_r | cbn ].
unfold iter_seq, iter_list; cbn.
rewrite (rngl_mul_1_l).
do 2 rewrite (rngl_mul_0_l Hos), rngl_add_0_r.
do 3 rewrite rngl_add_0_l.
rewrite List.app_nil_r.
f_equal; f_equal.
rewrite (lap_convol_mul_l_succ_l Hos).
rewrite List_map2_rngl_add_0_l.
now symmetry; apply (lap_convol_mul_1_l Hos).
Qed.

End a.

Arguments polyn_norm {T ro} la%_lap.
Arguments polyn_of_const {T ro} c%_L.
Arguments polyn_of_norm_lap {T ro} la%_lap.

(* examples *)

(* polynomials of nat *)

(* commented because locally don't want to depend here on NatRingLike
Require Import RingLike.NatRingLike.

Definition nat_polyn_ring_like_op : ring_like_op (polyn nat) :=
  @polyn_ring_like_op _ nat_ring_like_op nat_ring_like_prop
    eq_refl eq_refl.

Definition nat_polyn_ring_like_prop : ring_like_prop (polyn nat) :=
  @polyn_ring_like_prop _ nat_ring_like_op nat_ring_like_prop
    eq_refl eq_refl.
*)

(* polynomials of Z *)

(* commented because locally don't want to depend here on ZArith & Zrl
Require Import ZArith.
Require Import RnglAlg.Zrl.

Definition Z_polyn_ring_like_op : ring_like_op (polyn Z) :=
  @polyn_ring_like_op Z Z_ring_like_op Z_ring_like_prop
    eq_refl eq_refl.

Definition Z_polyn_ring_like_prop : ring_like_prop (polyn Z) :=
  @polyn_ring_like_prop Z Z_ring_like_op Z_ring_like_prop
    eq_refl eq_refl.
*)

(* polynomials of Q *)

(* commented because don't want to depend here on Rational & Qrl
Require Import RnglAlg.Rational.
Require Import RnglAlg.Qrl.

Definition Q_polyn_ring_like_op : ring_like_op (polyn Q) :=
  @polyn_ring_like_op _ Q_ring_like_op Q_ring_like_prop
    eq_refl eq_refl.

Definition Q_polyn_ring_like_prop : ring_like_prop (polyn Q) :=
  @polyn_ring_like_prop _ Q_ring_like_op Q_ring_like_prop
    eq_refl eq_refl.
*)

(* polynomials of square matrices *)

(* locally don't want this module to depend on Matrix & MatRl
Require Import Matrix.
Require Import RnglAlg.MatRl.

Definition mat_polyn_ring_like_op n T ro rp eqb
  (Hop : rngl_has_opp T = true) :
    ring_like_op (polyn (square_matrix n T)) :=
  @polyn_ring_like_op _
    (mat_ring_like_op ro eqb) (@mat_ring_like_prop T ro rp Hop eqb n)
    eq_refl eq_refl.

Definition mat_polyn_ring_like_prop n T ro rp eqb
  (Hop : rngl_has_opp T = true) :
    ring_like_prop (polyn (square_matrix n T)) :=
  @polyn_ring_like_prop _
    (mat_ring_like_op ro eqb) (@mat_ring_like_prop T ro rp Hop eqb n)
    eq_refl eq_refl.
*)

(* square matrices of polynomials *)

(* locally don't want this module to depend on Matrix & MatRl
Require Import Matrix.
Require Import RnglAlg.MatRl.

Definition mat_of_polyn_ring_like_op n T
  (ro : ring_like_op T) (rp : ring_like_prop T) eqb
  (Heq : rngl_has_eq_dec T = true)
  (Hos : rngl_has_opp_or_psub T = true) :
    ring_like_op (square_matrix n (polyn T)) :=
  mat_ring_like_op (polyn_ring_like_op Heq Hos) (polyn_eqb eqb).

Theorem polyn_has_opp :
  ∀ T (ro : ring_like_op T) (rp : ring_like_prop T) Heq Hop,
  @rngl_has_opp (polyn T)
    (polyn_ring_like_op Heq (rngl_has_opp_has_opp_or_psub Hop)) = true.
Proof.
intros.
unfold rngl_has_opp in Hop |-*.
unfold polyn_ring_like_op; cbn.
unfold polyn_opt_opp_or_psub; cbn.
remember rngl_opt_opp_or_psub as os eqn:Hos; symmetry in Hos.
destruct os as [os| ]; [ | easy ].
now destruct os.
Qed.

Definition mat_of_polyn_ring_like_prop n T ro rp eqb
  (Heq : rngl_has_eq_dec T = true) (Hop : rngl_has_opp T = true) :
    ring_like_prop (square_matrix n (polyn T)) :=
  @mat_ring_like_prop _
    (polyn_ring_like_op Heq (rngl_has_opp_has_opp_or_psub Hop))
    (@polyn_ring_like_prop _ ro rp Heq (rngl_has_opp_has_opp_or_psub Hop))
    (polyn_has_opp rp Heq Hop) (polyn_eqb eqb) n.
*)
