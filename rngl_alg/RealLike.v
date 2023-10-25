Set Nested Proofs Allowed.
Require Import Utf8.
Require Import Main.RingLike.

Class real_like_prop T {ro : ring_like_op T} {rp : ring_like_prop T} :=
  { rl_has_integral_modulus : bool;
    rl_nth_root : nat → T → T;
    rl_opt_integral_modulus_prop :
      if rl_has_integral_modulus then
        ∀ a b : T, (rngl_squ a + rngl_squ b = 0 → a = 0 ∧ b = 0)%L
      else not_applicable;
    rl_nth_root_pow : ∀ n a, (0 ≤ a → rl_nth_root n a ^ n = a)%L;
    rl_nth_root_mul :
      ∀ n a b, (0 ≤ a)%L → (0 ≤ b)%L →
      (rl_nth_root n (a * b) = rl_nth_root n a * rl_nth_root n b)%L;
    rl_nth_root_inv :
      ∀ n a, (0 < a → rl_nth_root n a⁻¹ = (rl_nth_root n a)⁻¹)%L;
    rl_sqrt_nonneg : ∀ a, (0 ≤ a → 0 ≤ rl_nth_root 2 a)%L }.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition rl_sqrt a := rl_nth_root 2 a.

End a.

Notation "'√' a" := (rl_sqrt a) (at level 1, format "√ a") : ring_like_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Theorem rngl_squ_sqrt : ∀ a, (0 ≤ a)%L → rngl_squ √a = a.
Proof.
intros.
now apply (rl_nth_root_pow 2 a).
Qed.

Theorem rl_sqrt_mul :
  ∀ a b,
  (0 ≤ a)%L
  → (0 ≤ b)%L
  → rl_sqrt (a * b)%L = (rl_sqrt a * rl_sqrt b)%L.
Proof.
intros * Ha Hb.
progress unfold rl_sqrt.
now rewrite rl_nth_root_mul.
Qed.

Theorem rl_sqrt_div :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a)%L → (0 < b)%L → (√(a / b) = √a / √b)%L.
Proof.
intros Hon Hop Hiv Hor * Ha Hb.
progress unfold rngl_div.
rewrite Hiv.
rewrite rl_sqrt_mul; [ | easy | ]. 2: {
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
}
f_equal.
now apply rl_nth_root_inv.
Qed.

Theorem rl_sqrt_squ :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (√(a²))%L = rngl_abs a.
Proof.
intros Hop Hor *.
progress unfold rngl_squ.
progress unfold rngl_abs.
progress unfold rl_sqrt.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az. {
  apply rngl_leb_le in Haz.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Haz.
  rewrite <- (rngl_mul_opp_opp Hop).
  rewrite rl_nth_root_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite rngl_squ_pow_2.
  now apply rl_nth_root_pow.
} {
  apply (rngl_leb_gt Hor) in Haz.
  apply (rngl_lt_le_incl Hor) in Haz.
  rewrite rl_nth_root_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite rngl_squ_pow_2.
  now apply rl_nth_root_pow.
}
Qed.

Theorem rl_sqrt_0 :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  rl_sqrt 0%L = 0%L.
Proof.
intros Hop Hic Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rl_nth_root_pow 2 0%L (rngl_le_refl Hor _)) as H1.
rewrite <- (rngl_squ_0 Hos) in H1 at 2.
rewrite <- rngl_squ_pow_2 in H1.
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hii) in H1.
rewrite (rngl_abs_0 Hop) in H1.
rewrite (rngl_abs_nonneg Hop Hor) in H1; [ easy | ].
apply rl_sqrt_nonneg, (rngl_le_refl Hor).
Qed.

Theorem eq_rl_sqrt_0 :
  rngl_has_opp_or_subt T = true →
  ∀ a, (0 ≤ a)%L → rl_sqrt a = 0%L → a = 0%L.
Proof.
intros Hos * Hza Ha.
apply (f_equal rngl_squ) in Ha.
rewrite rngl_squ_sqrt in Ha; [ | easy ].
progress unfold rngl_squ in Ha.
now rewrite (rngl_mul_0_l Hos) in Ha.
Qed.

Theorem rl_sqrt_sqr_le_sqrt_add_sqrt :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c d,
  (√((a + b)² + (c + d)²) ≤ √(a² + c²) + √(b² + d²))%L.
Proof.
intros Hic Hon Hop Hiv Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
rewrite <- (rngl_abs_nonneg Hop Hor). 2: {
  apply (rngl_add_nonneg_nonneg Hor). {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hop Hor).
  } {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hop Hor).
  }
}
rewrite <- (rngl_abs_nonneg Hop Hor (√_))%L. 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_add_squ_nonneg Hop Hor).
}
apply (rngl_squ_le_abs_le Hop Hor Hii).
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hop Hor) ].
rewrite (rngl_squ_add Hic Hon √_)%L.
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hop Hor) ].
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hop Hor) ].
apply (rngl_le_sub_le_add_r Hop Hor).
apply -> (rngl_le_sub_le_add_l Hop Hor).
do 2 rewrite (rngl_squ_add Hic Hon)%L.
rewrite rngl_add_assoc.
rewrite (rngl_sub_add_distr Hos _ b²)%L.
rewrite (rngl_sub_sub_swap Hop _ b²)%L.
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_add_sub Hos).
rewrite rngl_add_assoc.
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_sub_sub_swap Hop).
rewrite rngl_add_add_swap.
rewrite (rngl_add_sub Hos).
rewrite <- rngl_add_assoc.
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
do 3 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_l.
apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
  apply (rngl_le_trans Hor _ 1)%L.
  apply (rngl_0_le_1 Hon Hop Hor).
  apply (rngl_le_add_r Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
eapply (rngl_le_trans Hor); [ apply (rngl_le_abs Hop Hor) | ].
rewrite <- (rngl_abs_nonneg Hop Hor). 2: {
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hop Hor).
  } {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hop Hor).
  }
}
apply (rngl_squ_le_abs_le Hop Hor Hii).
rewrite (rngl_squ_mul Hic).
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hop Hor) ].
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hop Hor) ].
(* c'est pas une formule connue, ça ? un truc chinois, chais plus *)
rewrite (rngl_squ_add Hic Hon).
do 2 rewrite (rngl_squ_mul Hic).
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_add_distr_r _ _ b²)%L.
rewrite (rngl_mul_add_distr_r _ _ d²)%L.
rewrite rngl_add_assoc.
apply (rngl_add_le_mono_r Hop Hor).
rewrite <- rngl_add_assoc.
apply (rngl_add_le_mono_l Hop Hor).
rewrite (rngl_add_comm (_ * _))%L.
rewrite (rngl_mul_comm Hic c²)%L.
do 2 rewrite <- (rngl_squ_mul Hic).
do 2 rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (2 * a * b))%L.
rewrite (rngl_mul_mul_swap Hic (2 * a))%L.
rewrite <- rngl_mul_assoc.
rewrite <- (rngl_mul_assoc 2)%L.
apply (rngl_le_0_sub Hop Hor).
rewrite (rngl_add_sub_swap Hop).
rewrite <- (rngl_squ_sub Hop Hic Hon).
apply (rngl_square_ge_0 Hop Hor).
Qed.

Theorem euclidean_distance_triangular :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ x1 y1 x2 y2 x3 y3,
  (√((x3 - x1)² + (y3 - y1)²)
   ≤ √((x2 - x1)² + (y2 - y1)²) + √((x3 - x2)² + (y3 - y2)²))%L.
Proof.
intros Hic Hon Hop Hiv Hor *.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
rewrite (rngl_add_comm √((x2 - x1)² + (y2 - y1)²))%L.
replace (x3 - x1)%L with ((x3 - x2) + (x2 - x1))%L. 2: {
  rewrite (rngl_add_sub_assoc Hop).
  now rewrite (rngl_sub_add Hop).
}
replace (y3 - y1)%L with ((y3 - y2) + (y2 - y1))%L. 2: {
  rewrite (rngl_add_sub_assoc Hop).
  now rewrite (rngl_sub_add Hop).
}
apply (rl_sqrt_sqr_le_sqrt_add_sqrt Hic Hon Hop Hiv Hor).
Qed.

End a.
