(* vectors *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
Import Init.Nat.
Import List.ListNotations.

Require Import RingLike.Core.
Require Import RingLike.IterAdd.
Require Import Misc.

Record vector T := mk_vect
  { vect_list : list T }.

Arguments mk_vect [T]%_type.
Arguments vect_list [T]%_type.

Definition vect_size {T} (v : vector T) := length (vect_list v).

Definition vect_el {T} {ro : ring_like_op T} (V : vector T) i :=
  List.nth (i - 1) (vect_list V) 0%L.

Theorem fold_vect_size {T} : ∀ (V : vector T),
  length (vect_list V) = vect_size V.
Proof. easy. Qed.

Theorem vector_eq : ∀ {T} {ro : ring_like_op T} (U V : vector T),
  (∀ i, 1 ≤ i ≤ vect_size U → vect_el U i = vect_el V i)
  → vect_size U = vect_size V
  → U = V.
Proof.
intros * Heq Huv.
destruct U as (lu).
destruct V as (lv).
cbn in Heq, Huv; f_equal.
rewrite (List_map_nth_seq 0%L); symmetry.
rewrite (List_map_nth_seq 0%L); symmetry.
rewrite <- Huv.
apply List.map_ext_in.
intros i Hi; apply List.in_seq in Hi.
destruct Hi as (_, Hi); cbn in Hi.
specialize (Heq (S i)).
rewrite Nat_sub_succ_1 in Heq.
apply Heq.
split; [ now apply -> Nat.succ_le_mono | easy ].
Qed.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem fold_vect_el : ∀ (V : vector T) i,
  List.nth i (vect_list V) 0%L = vect_el V (S i).
Proof.
intros.
unfold vect_el.
now rewrite Nat_sub_succ_1.
Qed.

Definition vect_zero n : vector T := mk_vect (List.repeat 0%L n).

(* addition, subtraction of vector *)

Definition vect_add (U V : vector T) :=
  mk_vect (List_map2 rngl_add (vect_list U) (vect_list V)).

Definition vect_opp (V : vector T) :=
  mk_vect (List.map rngl_opp (vect_list V)).

Definition vect_sub (U V : vector T) := vect_add U (vect_opp V).

(* multiplication of a vector by a scalar *)

Definition vect_mul_scal_l s (V : vector T) :=
  mk_vect (List.map (λ x, (s * x)%L) (vect_list V)).

(* dot product *)

Definition vect_dot_mul (U V : vector T) :=
  ∑ (t ∈ List_map2 rngl_mul (vect_list U) (vect_list V)), t.
Definition vect_dot_mul' (U V : vector T) :=
  ∑ (i = 1, min (vect_size U) (vect_size V)),
  vect_el U i * vect_el V i.

Theorem vect_dot_mul_dot_mul' :
  rngl_has_opp_or_subt T = true →
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
  now cbn; rewrite rngl_summation_empty.
}
destruct lv as [| b]. {
  now cbn; rewrite rngl_summation_empty.
}
cbn - [ List.nth ].
rewrite rngl_summation_shift with (s := 1). 2: {
  split; [ easy | ].
  now apply -> Nat.succ_le_mono.
}
rewrite Nat.sub_diag, Nat_sub_succ_1.
rewrite rngl_summation_split_first; [ | easy ].
do 2 rewrite List_nth_0_cons.
rewrite rngl_summation_list_cons.
f_equal.
destruct (Nat.eq_dec (length lu) 0) as [Huz| Huz]. {
  rewrite Huz; cbn - [ List.nth ].
  apply List.length_zero_iff_nil in Huz; subst lu.
  rewrite rngl_summation_empty; [ | easy ].
  now rewrite List_map2_nil_l; unfold iter_list.
}
destruct (Nat.eq_dec (length lv) 0) as [Hvz| Hvz]. {
  rewrite Hvz; cbn - [ List.nth ].
  apply List.length_zero_iff_nil in Hvz; subst lv.
  rewrite Nat.min_r; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  now rewrite List_map2_nil_r; unfold iter_list.
}
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite <- Nat.add_sub_assoc; [ | easy ].
  now do 2 rewrite List_nth_succ_cons.
}
apply IHlu.
Qed.

Definition vect_squ_norm (V : vector T) := vect_dot_mul V V.

Declare Scope V_scope.
Delimit Scope V_scope with V.
Bind Scope V_scope with vector.

Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_mul U V) (at level 35).
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "U + V" := (vect_add U V) : V_scope.
Notation "U - V" := (vect_sub U V) : V_scope.
Notation "- V" := (vect_opp V) : V_scope.

Theorem vect_mul_scal_l_assoc : ∀ (a b : T) (V : vector T),
  (a × (b × V))%V = ((a * b)%L × V)%V.
Proof.
intros.
unfold vect_mul_scal_l.
f_equal; cbn.
rewrite List.map_map.
apply List.map_ext_in.
intros x Hx.
apply rngl_mul_assoc.
Qed.

Theorem vect_mul_scal_reg_r :
  rngl_has_inv_and_1_or_quot T = true →
  rngl_has_eq_dec T = true →
  ∀ (V : vector T) a b,
  V ≠ vect_zero (vect_size V)
  → (a × V = b × V)%V
  → a = b.
Proof.
intros Hi1 Heq * Hvz Habv.
unfold vect_mul_scal_l in Habv.
injection Habv; clear Habv; intros Habv.
specialize (List.ext_in_map Habv) as H1.
cbn in H1.
remember (rngl_eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ now apply rngl_eqb_eq | ].
apply (rngl_eqb_neq Heq) in Hab.
exfalso; apply Hvz; clear Hvz.
apply vector_eq; [ | now cbn; rewrite List.repeat_length ].
intros i Hi; cbn.
rewrite List.nth_repeat.
specialize (H1 (vect_el V i)) as H2.
assert (H : vect_el V i ∈ vect_list V). {
  unfold vect_el.
  apply List.nth_In.
  rewrite fold_vect_size.
  now apply Nat_1_le_sub_lt.
}
specialize (H2 H); clear H.
remember (rngl_eqb (vect_el V i) 0%L) as vz eqn:Hvz; symmetry in Hvz.
destruct vz; [ now apply rngl_eqb_eq | ].
apply (rngl_eqb_neq Heq) in Hvz.
now apply (rngl_mul_cancel_r Hi1) in H2.
Qed.

Theorem vect_mul_scal_size : ∀ a V, vect_size (a × V) = vect_size V.
Proof. now intros; cbn; rewrite List.length_map. Qed.

Theorem vect_dot_mul_scal_mul_comm :
  rngl_has_opp_or_subt T = true →
  rngl_mul_is_comm T = true →
  ∀ (a : T) (U V : vector T),
  ≺ U, a × V ≻ = (a * ≺ U, V ≻)%L.
Proof.
intros Hom Hic *.
unfold vect_dot_mul.
rewrite rngl_mul_summation_list_distr_l; [ | easy ].
unfold "×"; cbn.
unfold iter_list.
rewrite List_map2_map_r.
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
  rngl_has_opp_or_subt T = true →
  ∀ (a : T) (U V : vector T),
  ≺ a × U, V ≻ = (a * ≺ U, V ≻)%L.
Proof.
intros Hom *.
unfold vect_dot_mul; cbn.
rewrite rngl_mul_summation_list_distr_l; [ | easy ].
unfold "×"; cbn.
unfold iter_list.
rewrite List_map2_map_l.
rewrite List_fold_left_map2.
rewrite List_fold_left_map2.
apply List_fold_left_ext_in.
intros * Hb.
f_equal; symmetry.
apply rngl_mul_assoc.
Qed.

Theorem vect_eq_dec :
  rngl_has_eq_dec T = true →
  ∀ (U V : vector T), {U = V} + {U ≠ V}.
Proof.
intros Heq *.
destruct U as (lu).
destruct V as (lv).
remember (list_eqv rngl_eqb lu lv) as uv eqn:Huv.
symmetry in Huv.
destruct uv. {
  left; f_equal.
  apply list_eqb_eq in Huv; [ easy | ].
  unfold equality.
  apply (rngl_eqb_eq Heq).
} {
  right; f_equal.
  apply list_eqb_neq in Huv. {
    intros H; apply Huv; clear Huv.
    now injection H.
  }
  unfold equality.
  apply (rngl_eqb_eq Heq).
}
Qed.

Theorem vect_mul_scal_0_l :
  rngl_has_opp_or_subt T = true →
  ∀ v, (0%L × v)%V = mk_vect (List.repeat 0%L (vect_size v)).
Proof.
intros Hos *.
unfold vect_mul_scal_l, vect_size; cbn; f_equal.
erewrite List.map_ext_in; [ | intros; apply (rngl_mul_0_l Hos) ].
destruct v as (la); cbn; symmetry.
induction la as [| a]; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem vect_add_comm :
  ∀ u v, vect_add u v = vect_add v u.
Proof.
intros.
unfold vect_add; f_equal.
destruct u as (la).
destruct v as (lb); cbn.
revert lb.
induction la as [| a]; intros; cbn; [ now rewrite List_map2_nil_r | ].
destruct lb as [| b]; [ easy | cbn ].
rewrite rngl_add_comm; f_equal.
apply IHla.
Qed.

Theorem vect_dot_mul_comm :
  rngl_mul_is_comm T = true →
  ∀ u v, ≺ u , v ≻ = ≺ v , u ≻.
Proof.
intros Hic *.
unfold vect_dot_mul.
destruct u as (la).
destruct v as (lb); cbn.
revert lb.
induction la as [| a]; intros; cbn; [ now rewrite List_map2_nil_r | ].
destruct lb as [| b]; [ easy | cbn ].
do 2 rewrite rngl_summation_list_cons.
rewrite (rngl_mul_comm Hic); f_equal.
apply IHla.
Qed.

Theorem vect_dot_mul_add_l :
  ∀ n u v w,
  vect_size u = n
  → vect_size v = n
  → vect_size w = n
  → ≺ u + v, w ≻ = (≺ u, w ≻ + ≺ v, w ≻)%L.
Proof.
intros n (la) (lb) (lc) Ha Hb Hc.
cbn in Ha, Hb, Hc.
unfold vect_dot_mul; cbn.
do 4 rewrite (List_map2_map_min 0%L 0%L).
rewrite List_length_map_seq.
rewrite Ha, Hb, Hc.
do 2 rewrite Nat.min_id.
do 3 rewrite rngl_summation_list_map.
rewrite <- rngl_summation_list_add_distr.
apply rngl_summation_list_eq_compat.
intros i Hi.
apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
rewrite List_map_nth' with (a := 0); [ | now rewrite List.length_seq ].
rewrite List.seq_nth; [ cbn | easy ].
apply rngl_mul_add_distr_r.
Qed.

Theorem vect_dot_mul_add_r :
  ∀ n u v w,
  vect_size u = n
  → vect_size v = n
  → vect_size w = n
  → ≺ u, v + w ≻ = (≺ u, v ≻ + ≺ u, w ≻)%L.
Proof.
intros n (la) (lb) (lc) Ha Hb Hc.
cbn in Ha, Hb, Hc.
unfold vect_dot_mul; cbn.
do 4 rewrite (List_map2_map_min 0%L 0%L).
rewrite List_length_map_seq.
rewrite Ha, Hb, Hc.
do 2 rewrite Nat.min_id.
do 3 rewrite rngl_summation_list_map.
rewrite <- rngl_summation_list_add_distr.
apply rngl_summation_list_eq_compat.
intros i Hi.
apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
rewrite List_map_nth' with (a := 0); [ | now rewrite List.length_seq ].
rewrite List.seq_nth; [ cbn | easy ].
apply rngl_mul_add_distr_l.
Qed.

Theorem vect_opp_size : ∀ v, vect_size (vect_opp v) = vect_size v.
Proof.
intros.
unfold vect_size; cbn.
now rewrite List.length_map.
Qed.

Theorem vect_opp_el :
  rngl_has_opp T = true →
  ∀ v i, vect_el (vect_opp v) i = (- vect_el v i)%L.
Proof.
intros Hop *; unfold vect_el; cbn.
destruct (lt_dec (i - 1) (length (vect_list v))) as [Hil| Hil]. 2: {
  apply Nat.nlt_ge in Hil.
  rewrite List.nth_overflow; [ | now rewrite List.length_map ].
  rewrite List.nth_overflow; [ | easy ].
  symmetry; apply (rngl_opp_0 Hop).
}
now rewrite (List_map_nth' 0%L).
Qed.

Theorem vect_add_size :
  ∀ u v, vect_size (u + v) = min (vect_size u) (vect_size v).
Proof.
intros.
unfold vect_size; cbn.
apply List_length_map2.
Qed.

Theorem vect_mul_scal_l_add_distr_r :
  ∀ a b u, ((a + b)%L × u)%V = (a × u + b × u)%V.
Proof.
intros.
unfold "×", vect_add; cbn; f_equal.
rewrite (List_map2_map_min 0%L 0%L).
do 2 rewrite List.length_map.
rewrite Nat.min_id.
rewrite List_map_map_seq with (d := 0%L).
rewrite fold_vect_size.
apply List.map_ext_in.
intros i Hi.
apply List.in_seq in Hi.
rewrite (List_map_nth' 0%L); [ | easy ].
rewrite (List_map_nth' 0%L); [ | easy ].
apply rngl_mul_add_distr_r.
Qed.

Theorem vect_mul_scal_l_sub_distr_r :
  rngl_has_opp T = true →
  ∀ a b u, ((a - b)%L × u)%V = (a × u - b × u)%V.
Proof.
intros Hop *.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
move Hos before Hop.
unfold "×", vect_sub, vect_add; cbn; f_equal.
rewrite (List_map2_map_min 0%L 0%L).
do 3 rewrite List.length_map.
rewrite Nat.min_id.
rewrite List_map_map_seq with (d := 0%L).
rewrite fold_vect_size.
apply List.map_ext_in.
intros i Hi.
apply List.in_seq in Hi.
rewrite (List_map_nth' 0%L); [ | easy ].
rewrite (List_map_nth' 0%L); [ | now rewrite List.length_map ].
rewrite (List_map_nth' 0%L); [ | easy ].
rewrite (rngl_mul_sub_distr_r Hop).
unfold rngl_sub.
now rewrite Hop.
Qed.

Theorem vect_mul_scal_l_add_distr_l :
  ∀ a u v, (a × (u + v) = a × u + a × v)%V.
Proof.
intros.
unfold "×", vect_add; f_equal; cbn.
rewrite (List_map2_map_min 0%L 0%L).
rewrite (List_map2_map_min 0%L 0%L).
do 2 rewrite List.length_map.
do 2 rewrite fold_vect_size.
rewrite List.map_map.
apply List.map_ext_in.
intros i Hi.
apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
rewrite (List_map_nth' 0%L). 2: {
  rewrite fold_vect_size.
  now apply Nat.min_glb_lt_iff in Hi.
}
rewrite (List_map_nth' 0%L). 2: {
  rewrite fold_vect_size.
  now apply Nat.min_glb_lt_iff in Hi.
}
apply rngl_mul_add_distr_l.
Qed.

Theorem vect_add_assoc :
  ∀ u v w, (u + (v + w) = (u + v) + w)%V.
Proof.
intros.
unfold vect_add; f_equal; cbn.
do 4 rewrite (List_map2_map_min 0%L 0%L).
do 2 rewrite List_length_map_seq.
do 3 rewrite fold_vect_size.
rewrite Nat.min_assoc.
apply List.map_ext_in.
intros i Hi.
apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
rewrite (List_map_nth' 0). 2: {
  rewrite List.length_seq.
  rewrite <- Nat.min_assoc in Hi.
  now apply Nat.min_glb_lt_iff in Hi.
}
rewrite (List_map_nth' 0). 2: {
  rewrite List.length_seq.
  now apply Nat.min_glb_lt_iff in Hi.
}
rewrite List.seq_nth. 2: {
  rewrite <- Nat.min_assoc in Hi.
  now apply Nat.min_glb_lt_iff in Hi.
}
rewrite List.seq_nth. 2: {
  now apply Nat.min_glb_lt_iff in Hi.
}
cbn.
apply rngl_add_assoc.
Qed.

Theorem vect_opp_dot_mul_l :
  rngl_has_opp T = true →
  ∀ u v, (≺ - u, v ≻ = - ≺ u, v ≻)%L.
Proof.
intros Hop *.
unfold vect_dot_mul.
rewrite (rngl_opp_summation_list Hop).
rewrite (List_map2_map_min 0%L 0%L).
rewrite (List_map2_map_min 0%L 0%L).
do 3 rewrite fold_vect_size.
rewrite vect_opp_size.
do 2 rewrite rngl_summation_list_map.
apply rngl_summation_list_eq_compat.
intros i Hi.
do 3 rewrite fold_vect_el.
rewrite (vect_opp_el Hop).
apply (rngl_mul_opp_l Hop).
Qed.

Theorem vect_mul_scal_l_opp_l :
  rngl_has_opp T = true →
  ∀ a u, ((- a)%L × u = - (a × u))%V.
Proof.
intros Hop *.
unfold vect_mul_scal_l, vect_opp; cbn.
f_equal.
rewrite List.map_map.
apply List.map_ext_in.
intros b Hb.
apply (rngl_mul_opp_l Hop).
Qed.

End a.

Declare Scope V_scope.
Delimit Scope V_scope with V.
Bind Scope V_scope with vector.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "U - V" := (vect_sub U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_mul U V) (at level 35).
Notation "- V" := (vect_opp V) : V_scope.
