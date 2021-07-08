(* vectors *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc.
Require Import RingLike RLsummation.

Record vector T := mk_vect
  { vect_size : nat;
    vect_el : nat → T }.

(* function extensionality for vectors *)
Axiom vector_eq : ∀ T (VA VB : vector T),
  vect_size VA = vect_size VB
  → (∀ i, vect_el VA i = vect_el VB i)
  → VA = VB.

Definition vect_of_list {T} d (l : list T) : vector T :=
  mk_vect (length l) (λ i, nth i l d).

Definition list_of_vect {T} (v : vector T) :=
  map (vect_el v) (seq 0 (vect_size v)).

(*
Compute (list_of_vect (vect_of_list 42 [3;7;2])).
Compute (vect_of_list 42 [3;7;2]).
*)

(* (-1) ^ n *)

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

Definition vect_zero n : vector T := mk_vect n (λ _, 0%F).

(* addition, subtraction of vector *)

Definition vect_add (U V : vector T) :=
  mk_vect (vect_size U) (λ i, (vect_el U i + vect_el V i)%F).
Definition vect_opp (V : vector T) :=
  mk_vect (vect_size V) (λ i, (- vect_el V i)%F).

Definition vect_sub (U V : vector T) := vect_add U (vect_opp V).

(* multiplication of a vector by a scalar *)

Definition vect_mul_scal_l s (V : vector T) :=
  mk_vect (vect_size V) (λ i, s * vect_el V i)%F.

(* dot product *)

Definition vect_dot_product (U V : vector T) :=
  Σ (i = 0, vect_size U - 1), vect_el U i * vect_el V i.

Definition vect_squ_norm (V : vector T) := vect_dot_product V V.

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%F
  | _ => (- 1%F)%F
  end.

Theorem minus_one_pow_succ :
  rngl_has_opp = true →
  ∀ i, minus_one_pow (S i) = (- minus_one_pow i)%F.
Proof.
intros Hop *.
unfold minus_one_pow.
remember (i mod 2) as k eqn:Hk; symmetry in Hk.
destruct k. {
  apply Nat.mod_divides in Hk; [ | easy ].
  destruct Hk as (k, Hk); subst i.
  rewrite <- Nat.add_1_l, Nat.mul_comm.
  now rewrite Nat.mod_add.
}
destruct k. {
  rewrite <- Nat.add_1_l.
  rewrite <- Nat.add_mod_idemp_r; [ | easy ].
  rewrite Hk; cbn.
  symmetry.
  now apply rngl_opp_involutive.
}
specialize (Nat.mod_upper_bound i 2) as H1.
assert (H : 2 ≠ 0) by easy.
specialize (H1 H); clear H.
rewrite Hk in H1.
flia H1.
Qed.

Theorem minus_one_pow_add_r :
  rngl_has_opp = true →
  ∀ i j, minus_one_pow (i + j) = (minus_one_pow i * minus_one_pow j)%F.
Proof.
intros Hop *.
revert j.
induction i; intros; [ now cbn; rewrite rngl_mul_1_l | ].
rewrite Nat.add_succ_comm.
rewrite IHi.
rewrite minus_one_pow_succ; [ | easy ].
rewrite minus_one_pow_succ; [ | easy ].
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
easy.
Qed.

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments vect_dot_product (U V)%V.

Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_product U V) (at level 35).
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.

Theorem vect_mul_scal_l_mul_assoc : ∀ (a b : T) (V : vector T),
  (a × (b × V))%V = ((a * b)%F × V)%V.
Proof.
intros.
apply vector_eq; [ easy | ].
intros; apply rngl_mul_assoc.
Qed.

Theorem vect_mul_scal_reg_r :
  rngl_has_inv = true ∨ rngl_has_quot = true →
  rngl_has_dec_eq = true →
  ∀ (V : vector T) a b,
  V ≠ vect_zero (vect_size V)
  → (a × V = b × V)%V
  → a = b.
Proof.
intros Hii Hde * Hvz Hab.
assert (Hiv : ∀ i, vect_el (a × V)%V i = vect_el (b × V)%V i). {
  intros i.
  now rewrite Hab.
}
unfold vect_mul_scal_l in Hiv.
cbn in Hiv.
assert (Hn : ¬ ∀ i, vect_el V i = 0%F). {
  intros H; apply Hvz.
  now apply vector_eq.
}
destruct (rngl_eq_dec Hde a b) as [Haeb| Haeb]; [ easy | ].
exfalso; apply Hvz; clear Hvz.
apply vector_eq; [ easy | ].
intros i; cbn.
specialize (Hiv i).
destruct (rngl_eq_dec Hde (vect_el V i) 0%F) as [Hvi| Hvi]; [ easy | ].
now apply rngl_mul_cancel_r in Hiv.
Qed.

Theorem vect_dot_mul_scal_mul_comm :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  ∀ (a : T) (U V : vector T),
  ≺ U, a × V ≻ = (a * ≺ U, V ≻)%F.
Proof.
intros Hom Hic *.
unfold vect_dot_product.
rewrite rngl_mul_summation_distr_l; [ | easy ].
apply rngl_summation_eq_compat.
intros j Hj; cbn.
do 2 rewrite rngl_mul_assoc.
f_equal.
now apply rngl_mul_comm.
Qed.

Theorem vect_scal_mul_dot_mul_comm :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ (a : T) (U V : vector T),
  ≺ a × U, V ≻ = (a * ≺ U, V ≻)%F.
Proof.
intros Hom *.
unfold vect_dot_product.
rewrite rngl_mul_summation_distr_l; [ | easy ].
apply rngl_summation_eq_compat.
intros j Hj; cbn.
symmetry; apply rngl_mul_assoc.
Qed.

Theorem vect_eq_dec :
  rngl_has_dec_eq = true →
  ∀ (U V : vector T), {U = V} + {U ≠ V}.
Proof.
intros Hde *.
destruct (Nat.eq_dec (vect_size U) (vect_size V)) as [Hss| Hss]. {
  destruct U as (su, fu).
  destruct V as (sv, fv).
  cbn in Hss; subst sv.
  rename su into n.
  induction n. {
...

intros Hde *.
destruct U as (fu, su).
destruct V as (fv, sv).
induction n; intros; [ now left; apply vector_eq | ].
set (gu := λ i, fu (Fin.R 1 i)).
set (gv := λ i, fv (Fin.R 1 i)).
specialize (IHn gu gv).
destruct IHn as [IHn| IHn]. {
  injection IHn; clear IHn; intros H1.
  destruct (rngl_eq_dec Hde (fu Fin.F1) (fv Fin.F1)) as [H2| H2]. {
    left.
    apply vector_eq; cbn.
    intros i.
    specialize (Fin_inv i) as H3.
    destruct H3 as [| (j, Hj)]; [ congruence | ].
    subst i.
    cbn in gu, gv.
    now assert (gu j = gv j) by now rewrite H1.
  }
  right.
  congruence.
}
right.
intros H1; apply IHn; clear IHn.
apply vector_eq; cbn.
intros i.
injection H1; clear H1; intros H1.
unfold gu, gv; cbn.
congruence.
Qed.

Definition vect_size {T n} (v : vector n T) := n.

End a.

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments vect_add {T}%type {ro} {n}%nat (U V)%V.
Arguments vect_sub {T ro} {n}%nat U%V V%V.
Arguments vect_opp {T ro} {n}%nat V%V.
Arguments vect_mul_scal_l {T ro} s%F {n}%nat V%V.
Arguments vect_mul_scal_reg_r {T}%type {ro rp} Hde Hii {n}%nat V%V (a b)%F.
Arguments vect_zero {T ro} n%nat.
Arguments vect_dot_product {T}%type {ro} {n}%nat (U V)%V.
Arguments vect_dot_mul_scal_mul_comm {T}%type {ro rp} Hom Hic
  {n}%nat a%F (U V)%V.
Arguments vect_scal_mul_dot_mul_comm {T}%type {ro rp} Hom {n}%nat a%F (U V)%V.
Arguments vect_eq_dec {T}%type {ro rp} _ n%nat U%V V%V.
Arguments vect_el {n}%nat {T}%type v%V UUU%nat.
Arguments vect_squ_norm {T}%type {ro} {n}%nat V%V.

Arguments minus_one_pow {T}%type {ro} n%nat.
Arguments minus_one_pow_succ {T}%type {ro rp} _ i%nat.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "U - V" := (vect_sub U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_product U V) (at level 35).
Notation "- V" := (vect_opp V) : V_scope.
