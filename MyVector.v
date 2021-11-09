(* vectors *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc.
Require Import RingLike IterAdd.

Record vector T := mk_vect
  { vect_list : list T }.

Definition vect_of_list {T} (l : list T) : vector T :=
  mk_vect l.

Definition list_of_vect {T} (v : vector T) :=
  vect_list v.

Definition empty_vect {A} : vector A := mk_vect [].

Definition vect_size {T} (v : vector T) := length (vect_list v).

Theorem fold_vect_size {T} : ∀ (V : vector T),
  length (vect_list V) = vect_size V.
Proof. easy. Qed.

Theorem mk_vect_vect_list : ∀ A (v : vector A), mk_vect (vect_list v) = v.
Proof. now intros; destruct v. Qed.

(*
Compute (list_of_vect (vect_of_list [3;7;2])).
Compute (vect_of_list [3;7;2]).
*)

Theorem vector_eq {T} (U V : vector T) :
  (∀ i, nth_error (vect_list U) i = nth_error (vect_list V) i)
  → U = V.
Proof.
intros * Huv.
destruct U as (lu).
destruct V as (lv).
cbn in Huv; f_equal.
remember (length lu) as len eqn:Hlen.
symmetry in Hlen.
revert lu lv Huv Hlen.
induction len; intros. {
  apply length_zero_iff_nil in Hlen.
  subst lu; cbn in Huv.
  destruct lv as [| a]; [ easy | exfalso ].
  now specialize (Huv 0).
}
destruct lu as [| a]; [ easy | ].
cbn in Hlen.
apply Nat.succ_inj in Hlen.
destruct lv as [| b]. {
  exfalso.
  now specialize (Huv 0).
}
specialize (Huv 0) as H1; cbn in H1.
injection H1; clear H1; intros; subst b; f_equal.
apply IHlen; [ | easy ].
intros i.
now specialize (Huv (S i)).
Qed.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

Definition vect_el d (V : vector T) i := nth i (vect_list V) d.

Theorem fold_vect_el : ∀ d (V : vector T) i,
  nth i (vect_list V) d = vect_el d V i.
Proof. easy. Qed.

Definition vect_zero n : vector T := mk_vect (repeat 0%F n).

(* addition, subtraction of vector *)

Definition vect_add (U V : vector T) :=
  mk_vect (map2 rngl_add (vect_list U) (vect_list V)).

Definition vect_opp (V : vector T) :=
  mk_vect (map rngl_opp (vect_list V)).

Definition vect_sub (U V : vector T) := vect_add U (vect_opp V).

(* multiplication of a vector by a scalar *)

Definition vect_mul_scal_l s (V : vector T) :=
  mk_vect (map (λ x, (s * x)%F) (vect_list V)).

(* dot product *)

Definition vect_dot_mul (U V : vector T) :=
  ∑ (t ∈ map2 rngl_mul (vect_list U) (vect_list V)), t.

Definition vect_squ_norm (V : vector T) := vect_dot_mul V V.

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments vect_dot_mul (U V)%V.

Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_mul U V) (at level 35).
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.

Theorem vect_mul_scal_l_mul_assoc : ∀ (a b : T) (V : vector T),
  (a × (b × V))%V = ((a * b)%F × V)%V.
Proof.
intros.
unfold vect_mul_scal_l.
f_equal; cbn.
rewrite map_map.
apply map_ext_in.
intros x Hx.
apply rngl_mul_assoc.
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
unfold vect_mul_scal_l in Hab.
injection Hab; clear Hab; intros Hab.
specialize (ext_in_map Hab) as H1.
cbn in H1.
destruct (rngl_eq_dec Hde a b) as [Haeb| Haeb]; [ easy | ].
exfalso; apply Hvz; clear Hvz.
apply vector_eq.
intros i; cbn.
destruct (lt_dec i (vect_size V)) as [Hiv| Hiv]. {
  rewrite nth_error_repeat; [ | easy ].
  rewrite nth_error_nth' with (d := 0%F); [ | easy ].
  f_equal.
  specialize (H1 (nth i (vect_list V) 0%F)) as H2.
  assert (H : nth i (vect_list V) 0%F ∈ vect_list V) by now apply nth_In.
  specialize (H2 H); clear H.
  destruct (rngl_eq_dec Hde (vect_el 0%F V i) 0%F) as [Hvi| Hvi]; [ easy | ].
  now apply rngl_mul_cancel_r in H2.
}
apply Nat.nlt_ge in Hiv.
rewrite (proj2 (nth_error_None _ _)); [ | easy ].
rewrite (proj2 (nth_error_None _ _)); [ easy | ].
now rewrite repeat_length.
Qed.

Theorem vect_dot_mul_scal_mul_comm :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  ∀ (a : T) (U V : vector T),
  ≺ U, a × V ≻ = (a * ≺ U, V ≻)%F.
Proof.
intros Hom Hic *.
unfold vect_dot_mul.
rewrite rngl_mul_summation_list_distr_l; [ | easy ].
unfold "×"; cbn.
unfold iter_list.
rewrite map2_map_r.
rewrite List_fold_left_map2.
rewrite List_fold_left_map2.
apply List_fold_left_ext_in.
intros * Hb.
f_equal.
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
unfold vect_dot_mul.
rewrite rngl_mul_summation_list_distr_l; [ | easy ].
unfold "×"; cbn.
unfold iter_list.
rewrite map2_map_l.
rewrite List_fold_left_map2.
rewrite List_fold_left_map2.
apply List_fold_left_ext_in.
intros * Hb.
f_equal; symmetry.
apply rngl_mul_assoc.
Qed.

Theorem vect_eq_dec :
  rngl_has_dec_eq = true →
  ∀ (U V : vector T), {U = V} + {U ≠ V}.
Proof.
intros Hde *.
destruct U as (lu).
destruct V as (lv).
destruct (list_eq_dec (rngl_eq_dec Hde) lu lv) as [Huv| Huv]. {
  now left; subst.
} {
  right; intros H; apply Huv; clear Huv.
  now injection H.
}
Qed.

End a.

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments vect_add {T}%type {ro} (U V)%V.
Arguments vect_sub {T ro} U%V V%V.
Arguments vect_opp {T ro} V%V.
Arguments vect_mul_scal_l {T ro} s%F V%V.
Arguments vect_mul_scal_reg_r {T}%type {ro rp} Hde Hii V%V (a b)%F.
Arguments vect_zero {T ro} n%nat.
Arguments vect_dot_mul {T}%type {ro} (U V)%V.
Arguments vect_dot_mul_scal_mul_comm {T}%type {ro rp} Hom Hic a%F (U V)%V.
Arguments vect_scal_mul_dot_mul_comm {T}%type {ro rp} Hom a%F (U V)%V.
Arguments vect_eq_dec {T}%type {ro rp} Hde U%V V%V.
Arguments vect_el {T}%type d V%V i%nat.
Arguments vect_squ_norm {T}%type {ro} V%V.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "U - V" := (vect_sub U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_mul U V) (at level 35).
Notation "- V" := (vect_opp V) : V_scope.
