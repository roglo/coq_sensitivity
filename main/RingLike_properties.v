Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import RingLike_structures.
Require Import RingLike_order.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* characteristic *)

Theorem rngl_characteristic_non_0 :
  rngl_has_1 T = true →
  rngl_characteristic T ≠ 0 →
  (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L) ∧
  rngl_of_nat (rngl_characteristic T) = 0%L.
Proof.
intros Hon Hcz.
specialize (rngl_opt_characteristic_prop) as H1.
apply Nat.eqb_neq in Hcz.
now rewrite Hon, Hcz in H1.
Qed.

(* archimedianity *)

Theorem rngl_archimedean :
  rngl_is_archimedean T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 < a)%L → ∃ n, (b < rngl_mul_nat a n)%L.
Proof.
intros Har Hor.
specialize rngl_opt_archimedean as H1.
now rewrite Har, Hor in H1.
Qed.

(* comparison *)

Definition rngl_compare a b :=
  if (a =? b)%L then Eq
  else if (a ≤? b)%L then Lt else Gt.

Theorem rngl_compare_eq_iff :
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Eq ↔ a = b.
Proof.
intros Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
symmetry in Hab.
destruct ab. {
  split; [ | easy ].
  now apply (rngl_eqb_eq Hed) in Hab.
} {
  destruct (a ≤? b)%L. {
    split; [ easy | ].
    now apply (rngl_eqb_neq Hed) in Hab.
  } {
    split; [ easy | ].
    now apply (rngl_eqb_neq Hed) in Hab.
  }
}
Qed.

Theorem rngl_compare_lt_iff :
  rngl_is_ordered T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Lt ↔ (a < b)%L.
Proof.
intros Hor Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
remember (a ≤? b)%L as alb eqn:Halb.
symmetry in Hab, Halb.
destruct ab. {
  split; [ easy | intros H ].
  apply (rngl_eqb_eq Hed) in Hab.
  subst b.
  now apply (rngl_lt_irrefl Hor) in H.
} {
  apply (rngl_eqb_neq Hed) in Hab.
  destruct alb. {
    apply rngl_leb_le in Halb.
    split; [ | easy ].
    intros _.
    now apply (rngl_lt_iff Hor).
  } {
    split; [ easy | ].
    apply (rngl_leb_gt Hor) in Halb.
    intros H.
    now apply (rngl_lt_asymm Hor) in H.
  }
}
Qed.

Theorem rngl_compare_gt_iff :
  rngl_is_ordered T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Gt ↔ (b < a)%L.
Proof.
intros Hor Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
remember (a ≤? b)%L as alb eqn:Halb.
symmetry in Hab, Halb.
destruct ab. {
  split; [ easy | intros H ].
  apply (rngl_eqb_eq Hed) in Hab.
  subst b.
  now apply (rngl_lt_irrefl Hor) in H.
} {
  apply (rngl_eqb_neq Hed) in Hab.
  destruct alb. {
    apply rngl_leb_le in Halb.
    split; [ easy | ].
    intros H.
    now apply (rngl_nle_gt Hor) in H.
  } {
    now apply (rngl_leb_gt Hor) in Halb.
  }
}
Qed.

Theorem rngl_compare_refl :
  rngl_has_eq_dec T = true →
  ∀ a, rngl_compare a a = Eq.
Proof.
intros Hed *.
now apply (rngl_compare_eq_iff Hed).
Qed.

Notation "x ?= y" := (rngl_compare x y) : ring_like_scope.

(* *)

Record charac_0_field :=
  { cf_has_1 : rngl_has_1 T = true;
    cf_mul_is_comm : rngl_mul_is_comm T = true;
    cf_has_opp : rngl_has_opp T = true;
    cf_has_inv : rngl_has_inv T = true;
    cf_has_eq_dec : rngl_has_eq_dec T = true;
    cf_characteristic : rngl_characteristic T = 0 }.

End a.

Arguments charac_0_field T%_type {ro rp}.
