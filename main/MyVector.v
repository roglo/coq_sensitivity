(* vectors *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import Init.Nat.
Import List List.ListNotations.

Require Import Misc.
Require Import RingLike IterAdd.

Record vector T := mk_vect
  { vect_list : list T }.

Definition vect_size {T} (v : vector T) := length (vect_list v).

Theorem fold_vect_size {T} : ∀ (V : vector T),
  length (vect_list V) = vect_size V.
Proof. easy. Qed.

Definition vect_el {T} {ro : ring_like_op T} (V : vector T) i :=
  nth i (vect_list V) 0%F.

Theorem vector_eq : ∀ T {ro : ring_like_op T} (U V : vector T),
  (∀ i, i < vect_size U → vect_el U i = vect_el V i)
  → vect_size U = vect_size V
  → U = V.
Proof.
intros * Heq Huv.
destruct U as (lu).
destruct V as (lv).
cbn in Heq, Huv; f_equal.
rewrite (List_map_nth_seq _ 0%F); symmetry.
rewrite (List_map_nth_seq _ 0%F); symmetry.
rewrite <- Huv.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
destruct Hi as (_, Hi); cbn in Hi.
now apply Heq.
Qed.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

Theorem fold_vect_el : ∀ (V : vector T) i,
  nth i (vect_list V) 0%F = vect_el V i.
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
Definition vect_dot_mul' (U V : vector T) :=
  ∑ (i = 0, min (vect_size U) (vect_size V) - 1),
  vect_el U i * vect_el V i.

Theorem vect_dot_mul_dot_mul' :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ U V,
  vect_dot_mul U V = vect_dot_mul' U V.
Proof.
intros Hos *.
unfold vect_dot_mul, vect_dot_mul'.
destruct U as (lu).
destruct V as (lv).
cbn.
revert lv.
induction lu as [| a]; intros. {
  cbn; rewrite rngl_summation_only_one.
  unfold iter_list; cbn.
  now symmetry; apply rngl_mul_0_l.
}
destruct lv as [| b]. {
  cbn; rewrite rngl_summation_only_one.
  unfold iter_list; cbn.
  now symmetry; apply rngl_mul_0_r.
}
cbn - [ nth ].
rewrite Nat.sub_0_r.
rewrite rngl_summation_split_first; [ | easy ].
do 2 rewrite List_nth_0_cons.
rewrite rngl_summation_list_cons.
f_equal.
destruct (Nat.eq_dec (length lu) 0) as [Huz| Huz]. {
  rewrite Huz; cbn - [ nth ].
  apply length_zero_iff_nil in Huz; subst lu.
  rewrite rngl_summation_empty; [ | easy ].
  now rewrite map2_nil_l; unfold iter_list.
}
destruct (Nat.eq_dec (length lv) 0) as [Hvz| Hvz]. {
  rewrite Hvz; cbn - [ nth ].
  apply length_zero_iff_nil in Hvz; subst lv.
  rewrite Nat.min_r; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  now rewrite map2_nil_r; unfold iter_list.
}
rewrite rngl_summation_shift. 2: {
  destruct (length lu); [ easy | ].
  destruct (length lv); [ easy | ].
  now cbn; apply -> Nat.succ_le_mono.
}
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  now do 2 rewrite List_nth_succ_cons.
}
apply IHlu.
Qed.

Definition vect_squ_norm (V : vector T) := vect_dot_mul V V.

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments vect_dot_mul (U V)%V.
Arguments vector_eq {T}%type {ro} (U V)%V.

Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_mul U V) (at level 35).
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.

Arguments vect_el {T}%type {ro} V%V i%nat.
Arguments vect_size {T}%type v%V.

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
apply vector_eq; [ | now cbn; rewrite repeat_length ].
intros i Hi; cbn.
rewrite nth_repeat.
specialize (H1 (nth i (vect_list V) 0%F)) as H2.
assert (H : nth i (vect_list V) 0%F ∈ vect_list V) by now apply nth_In.
specialize (H2 H); clear H.
destruct (rngl_eq_dec Hde (vect_el V i) 0%F) as [Hvi| Hvi]; [ easy | ].
now apply rngl_mul_cancel_r in H2.
Qed.

Theorem vect_mul_scal_size : ∀ a V, vect_size (a × V) = vect_size V.
Proof. now intros; cbn; rewrite map_length. Qed.

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
unfold vect_dot_mul; cbn.
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
Arguments vect_dot_mul' {T}%type {ro} (U V)%V.
Arguments vect_dot_mul_dot_mul' {T}%type {ro rp} Hop (U V)%V.
Arguments vect_dot_mul_scal_mul_comm {T}%type {ro rp} Hom Hic a%F (U V)%V.
Arguments vect_scal_mul_dot_mul_comm {T}%type {ro rp} Hom a%F (U V)%V.
Arguments vect_eq_dec {T}%type {ro rp} Hde U%V V%V.
Arguments vect_el {T}%type {ro} V%V i%nat.
Arguments vect_size {T}%type v%V.
Arguments vect_squ_norm {T}%type {ro} V%V.
Arguments vector_eq {T}%type {ro} (U V)%V.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "U - V" := (vect_sub U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_mul U V) (at level 35).
Notation "- V" := (vect_opp V) : V_scope.
