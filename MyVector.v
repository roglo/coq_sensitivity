(* vectors *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc.
Require Import RingLike RLsummation.

Record vector T := mk_vect
  { vect_list : list T }.

Definition vect_of_list {T} (l : list T) : vector T :=
  mk_vect l.

Definition list_of_vect {T} (v : vector T) :=
  vect_list v.

Definition vect_size {T} (v : vector T) := length (vect_list v).

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

(* (-1) ^ n *)

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

Definition vect_el V i := nth i (vect_list V) 0%F.

Definition vect_zero n : vector T := mk_vect (repeat 0%F n).

Fixpoint map2 {A B C} (f : A → B → C) la lb :=
  match la with
  | [] => []
  | a :: la' =>
      match lb with
      | [] => []
      | b :: lb' => f a b :: map2 f la' lb'
      end
  end.

Theorem map2_map_l : ∀ A B C D (f : C → B → D) g (la : list A) (lb : list B),
  map2 f (map g la) lb = map2 (λ a b, f (g a) b) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
apply IHla.
Qed.

Theorem map2_map_r : ∀ A B C D (f : A → C → D) g (la : list A) (lb : list B),
  map2 f la (map g lb) = map2 (λ a b, f a (g b)) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
apply IHla.
Qed.

Theorem List_fold_left_map2 :
  ∀ A B C D (f : A → B → A) (g : C → D → B) lc ld (a : A),
  fold_left f (map2 g lc ld) a =
  fold_left (λ b c, f b (g (fst c) (snd c))) (combine lc ld) a.
Proof.
intros.
revert ld a.
induction lc as [| c]; intros; [ easy | cbn ].
destruct ld as [| d]; [ easy | cbn ].
apply IHlc.
Qed.

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

Definition vect_dot_product (U V : vector T) :=
  Σ (t ∈ map2 rngl_mul (vect_list U) (vect_list V)), t.

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
  destruct (rngl_eq_dec Hde (vect_el V i) 0%F) as [Hvi| Hvi]; [ easy | ].
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
unfold vect_dot_product.
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
unfold vect_dot_product.
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
Arguments vect_dot_product {T}%type {ro} (U V)%V.
Arguments vect_dot_mul_scal_mul_comm {T}%type {ro rp} Hom Hic a%F (U V)%V.
Arguments vect_scal_mul_dot_mul_comm {T}%type {ro rp} Hom a%F (U V)%V.
Arguments vect_eq_dec {T}%type {ro rp} Hde U%V V%V.
Arguments vect_el {T}%type {ro} V%V i%nat.
Arguments vect_squ_norm {T}%type {ro} V%V.

Arguments minus_one_pow {T}%type {ro} n%nat.
Arguments minus_one_pow_succ {T}%type {ro rp} _ i%nat.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "U - V" := (vect_sub U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_product U V) (at level 35).
Notation "- V" := (vect_opp V) : V_scope.
