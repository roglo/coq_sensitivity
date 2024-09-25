Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import RingLike_structures.
Require Import RingLike_order.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* theorems *)

Theorem fold_rngl_squ : ∀ a : T, (a * a)%L = rngl_squ a.
Proof. easy. Qed.

Theorem rngl_neqb_neq :
  rngl_has_eq_dec T = true →
  ∀ a b : T, (a ≠? b)%L = true ↔ a ≠ b.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
clear Hed.
now destruct (rngl_eq_dec a b).
Qed.

Theorem rngl_eqb_refl :
  rngl_has_eq_dec T = true →
  ∀ a, (a =? a)%L = true.
Proof.
intros Heqb *.
now apply (rngl_eqb_eq Heqb).
Qed.

Theorem rngl_eqb_sym :
  rngl_has_eq_dec T = true →
  ∀ a b, ((a =? b) = (b =? a))%L.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
destruct (rngl_eq_dec a b). {
  subst b.
  now destruct (rngl_eq_dec a a).
} {
  destruct (rngl_eq_dec b a); [ now subst b | easy ].
}
Qed.

(* *)

Arguments rngl_mul_nat {T ro} a%_L n%_nat.

Theorem rngl_of_nat_0 : rngl_of_nat 0 = 0%L.
Proof. easy. Qed.

Theorem fold_rngl_mul_nat :
  ∀ a n, List.fold_right rngl_add 0%L (List.repeat a n)%L = rngl_mul_nat a n.
Proof. easy. Qed.

Theorem rngl_min_comm :
  rngl_is_ordered T = true →
  ∀ a b, rngl_min a b = rngl_min b a.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (b ≤? a)%L as ba eqn:Hba.
symmetry in Hab, Hba.
destruct ab. {
  destruct ba; [ | easy ].
  apply rngl_leb_le in Hab, Hba.
  now apply (rngl_le_antisymm Hor).
} {
  destruct ba; [ easy | ].
  apply (rngl_leb_gt Hor) in Hab, Hba.
  now apply (rngl_lt_asymm Hor) in Hba.
}
Qed.

Theorem rngl_min_assoc :
  rngl_is_ordered T = true →
  ∀ a b c,
  rngl_min a (rngl_min b c) = rngl_min (rngl_min a b) c.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (b ≤? c)%L as bc eqn:Hbc.
symmetry in Hab, Hbc.
destruct ab. {
  destruct bc; [ | easy ].
  rewrite Hab.
  apply rngl_leb_le in Hab, Hbc.
  apply (rngl_le_trans Hor a) in Hbc; [ | easy ].
  apply rngl_leb_le in Hbc.
  now rewrite Hbc.
}
rewrite Hbc.
destruct bc; [ now rewrite Hab | ].
apply (rngl_leb_gt Hor) in Hab, Hbc.
apply (rngl_lt_le_incl Hor) in Hbc.
apply (rngl_le_lt_trans Hor c) in Hab; [ | easy ].
apply (rngl_leb_gt Hor) in Hab.
now rewrite Hab.
Qed.

Theorem rngl_min_l_iff :
  rngl_is_ordered T = true →
  ∀ a b, rngl_min a b = a ↔ (a ≤ b)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (b ≤? a)%L as ba eqn:Hba.
symmetry in Hab, Hba.
split; intros H1. {
  destruct ab; [ now apply rngl_leb_le in Hab | ].
  destruct ba; [ subst b; apply (rngl_le_refl Hor) | ].
  apply (rngl_leb_gt Hor) in Hab, Hba.
  apply (rngl_lt_le_incl Hor) in Hba.
  now apply (rngl_nlt_ge Hor) in Hba.
} {
  destruct ab; [ easy | ].
  apply rngl_leb_le in H1.
  now rewrite Hab in H1.
}
Qed.

Theorem rngl_min_r_iff :
  rngl_is_ordered T = true →
  ∀ a b, rngl_min a b = b ↔ (b ≤ a)%L.
Proof.
intros Hor *.
rewrite (rngl_min_comm Hor).
apply (rngl_min_l_iff Hor).
Qed.

Theorem rngl_min_glb_lt_iff :
  rngl_is_ordered T = true →
  ∀ a b c, (c < rngl_min a b ↔ c < a ∧ c < b)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
split; intros Hcab; [ | now destruct ab ].
destruct ab. {
  apply rngl_leb_le in Hab.
  split; [ easy | ].
  now apply (rngl_lt_le_trans Hor _ a).
}
apply (rngl_leb_gt Hor) in Hab.
split; [ | easy ].
now apply (rngl_lt_trans Hor _ b).
Qed.

Theorem rngl_min_le_iff :
  rngl_is_ordered T = true →
  ∀ a b c, (rngl_min a b ≤ c ↔ a ≤ c ∨ b ≤ c)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
split; intros Hcab. {
  now destruct ab; [ left | right ].
}
destruct ab. {
  destruct Hcab as [Hac| Hbc]; [ easy | ].
  apply rngl_leb_le in Hab.
  now apply (rngl_le_trans Hor _ b).
}
destruct Hcab as [Hac| Hbc]; [ | easy ].
apply (rngl_leb_gt Hor) in Hab.
apply (rngl_le_trans Hor _ a); [ | easy ].
now apply (rngl_lt_le_incl Hor) in Hab.
Qed.

Theorem rngl_min_lt_iff :
  rngl_is_ordered T = true →
  ∀ a b c, (rngl_min a b < c ↔ a < c ∨ b < c)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
split; intros Hcab. {
  now destruct ab; [ left | right ].
}
destruct ab. {
  destruct Hcab as [Hac| Hbc]; [ easy | ].
  apply rngl_leb_le in Hab.
  now apply (rngl_le_lt_trans Hor _ b).
}
destruct Hcab as [Hac| Hbc]; [ | easy ].
apply (rngl_leb_gt Hor) in Hab.
now apply (rngl_lt_trans Hor _ a).
Qed.

Theorem rngl_le_min_l :
  rngl_is_ordered T = true →
  ∀ a b, (rngl_min a b ≤ a)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ apply (rngl_le_refl Hor) | ].
apply (rngl_leb_gt Hor) in Hc.
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_le_min_r :
  rngl_is_ordered T = true →
  ∀ a b, (rngl_min a b ≤ b)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
now apply rngl_leb_le in Hc.
Qed.

Theorem rngl_min_le_compat_l :
  rngl_is_ordered T = true →
  ∀ a b c, (b ≤ c → rngl_min a b ≤ rngl_min a c)%L.
Proof.
intros Hor * Hbc.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (a ≤? c)%L as ac eqn:Hac.
symmetry in Hab, Hac.
destruct ab. {
  destruct ac; [ apply (rngl_le_refl Hor) | ].
  apply rngl_leb_le in Hab.
  now apply (rngl_le_trans Hor _ b).
} {
  destruct ac; [ | easy ].
  apply (rngl_leb_gt Hor) in Hab.
  now apply (rngl_lt_le_incl Hor) in Hab.
}
Qed.

Theorem rngl_le_max_l :
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ rngl_max a b)%L.
Proof.
intros Hor *.
progress unfold rngl_max.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
now apply rngl_leb_le in Hc.
Qed.

Theorem rngl_le_max_r :
  rngl_is_ordered T = true →
  ∀ a b, (b ≤ rngl_max a b)%L.
Proof.
intros Hor *.
progress unfold rngl_max.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ apply (rngl_le_refl Hor) | ].
apply (rngl_leb_gt Hor) in Hc.
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_min_glb :
  ∀ a b c, (a ≤ b → a ≤ c → a ≤ rngl_min b c)%L.
Proof.
intros * Hab Hac.
progress unfold rngl_min.
now destruct (b ≤? c)%L.
Qed.

Theorem rngl_min_glb_lt :
  ∀ a b c, (a < b → a < c → a < rngl_min b c)%L.
Proof.
intros * Hab Hac.
progress unfold rngl_min.
now destruct (b ≤? c)%L.
Qed.

Theorem rngl_max_lub :
  ∀ a b c, (a ≤ c → b ≤ c → rngl_max a b ≤ c)%L.
Proof.
intros * Hac Hbc.
progress unfold rngl_max.
now destruct (a ≤? b)%L.
Qed.

Theorem rngl_max_lub_lt :
  ∀ a b c, (a < c → b < c → rngl_max a b < c)%L.
Proof.
intros * Hac Hbc.
progress unfold rngl_max.
now destruct (a ≤? b)%L.
Qed.

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

Require Import RingLike_add RingLike_mul.

(* to be able to use tactic "ring" *)

Require Import Ring_theory.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hic : @rngl_mul_is_comm T ro rp = true).
Context (Hop : @rngl_has_opp T ro = true).
Context (Hon : @rngl_has_1 T ro = true).

Definition rngl_ring_theory
    : ring_theory 0%L 1%L rngl_add rngl_mul rngl_sub rngl_opp eq :=
  {| Radd_0_l := rngl_add_0_l;
     Radd_comm := rngl_add_comm;
     Radd_assoc := rngl_add_assoc;
     Rmul_1_l := rngl_mul_1_l Hon;
     Rmul_comm := rngl_mul_comm Hic;
     Rmul_assoc := rngl_mul_assoc;
     Rdistr_l := rngl_mul_add_distr_r;
     Rsub_def x y := eq_sym (rngl_add_opp_r Hop x y);
     Ropp_def := rngl_add_opp_diag_r Hop |}.

End a.

(* code to be added to be able to use the Coq tactic "ring"

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {Hic : @rngl_mul_is_comm T ro rp = true}.
Context {Hop : @rngl_has_opp T T ro = true}.

Require Import Ring.
Add Ring rngl_ring : (@rngl_ring_theory T ro rp Hic Hop).

(* example *)

Example a2_b2 : ∀ a b, ((a + b) * (a - b) = a * a - b * b)%L.
Proof.
intros.
ring_simplify. (* just to see what happens *)
easy.
Qed.
*)

Arguments rngl_abs {T ro} a%_L.
Arguments rngl_abs_nonneg_eq {T ro rp} Hop Hor a%_L.
Arguments rngl_add {T ring_like_op} (a b)%_L.
Arguments rngl_add_comm {T ro ring_like_prop} (a b)%_L.
Arguments rngl_add_sub {T ro rp} Hom (a b)%_L.
Arguments rngl_characteristic_1 {T ro rp} Hon Hos Hch x%_L.
Arguments rngl_div_add_distr_r {T ro rp} Hiv (a b c)%_L.
Arguments rngl_div_le_mono_pos_r {T ro rp} Hon Hop Hiv Hor Hii (a b c)%_L.
Arguments rngl_eq_dec {T ro} Hed (a b)%_L.
Arguments rngl_le_add_r {T ro rp} Hor (a b)%_L Hb.
Arguments rngl_le_dec {T ro rp} Hor (a b)%_L.
Arguments rngl_le_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_le_lt_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_le_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_dec {T ro rp} Hor (a b)%_L.
Arguments rngl_min {T ro} (a b)%_L.
Arguments rngl_mul {T ring_like_op} (a b)%_L.
Arguments rngl_mul_comm {T ro rp} Hic (a b)%_L.
Arguments rngl_mul_le_mono_pos_l {T ro rp} Hop Hor Hii (a b c)%_L.
Arguments rngl_mul_le_mono_pos_r {T ro rp} Hop Hor Hii (a b c)%_L.
Arguments rngl_mul_nat {T ro} a%_L n%_nat.
Arguments rngl_mul_0_r {T ro rp} Hom a%_L.
Arguments rngl_mul_1_r {T ro rp} Hon a%_L.
Arguments rngl_pow_squ {T ro rp} Hic Hon a%_L n%_nat.
Arguments rngl_squ {T ro} x%_L.
Arguments rngl_sub {T ro} (a b)%_L.
Arguments rngl_subt {T ro} (a b)%_L.

Arguments charac_0_field T%_type {ro rp}.
