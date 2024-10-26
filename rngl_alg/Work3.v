(* File created because Work2.v became too big, but
   without any topic found for the moment *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List.ListNotations.

Require Import Main.Misc Main.RingLike.
Require Import Main.IterMax.
Require Import Main.IterAdd.
Require Import Trigo.RealLike.
Require Import Trigo.TrigoWithoutPi Trigo.TrigoWithoutPiExt.
Require Import Trigo.AngleAddLeMonoL.
Require Import Trigo.AngleAddOverflowLe.
Require Import Trigo.AngleTypeIsComplete.
Require Import Trigo.SeqAngleIsCauchy.
Require Import Trigo.AngleDivNat.
Require Import Misc.
Require Import Complex.
Require Import Work.
Require Import Work2.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem gc_mul_0_l :
  rngl_has_opp_or_subt T = true →
  ∀ z : GComplex T, (0 * z = 0)%C.
Proof.
intros Hos *.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_l.
easy.
Qed.

Theorem gc_mul_0_r :
  rngl_has_opp_or_subt T = true →
  ∀ z : GComplex T, (z * 0 = 0)%C.
Proof.
intros Hos *.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_l.
easy.
Qed.

Theorem gc_pow_mul_l :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ z1 z2 n, ((z1 * z2) ^ n = (z1 ^ n) * (z2 ^ n))%C.
Proof.
intros Hic Hop.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
progress unfold gc_pow_nat.
induction n. {
  symmetry.
  specialize (gc_opt_mul_1_l Hos) as H1.
  progress unfold rngl_has_1 in H1.
  cbn in H1 |-*.
  progress unfold rngl_one in H1.
  progress unfold rngl_one.
  cbn in H1 |-*.
  destruct (gc_opt_one T); [ apply H1 | ].
  apply (gc_mul_0_l Hos).
}
cbn.
rewrite IHn.
do 2 rewrite (gc_mul_assoc Hop).
f_equal.
do 2 rewrite <- (gc_mul_assoc Hop).
f_equal.
apply (gc_mul_comm Hic).
Qed.

Theorem gc_has_nth_root :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  rngl_is_complete T →
  ∀ z : GComplex T, ∀ n, n ≠ 0 → ∃ z', (z' ^ n)%C = z.
Proof.
intros Hic Hop Hor Hcz Har Hco.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hnz.
specialize (polar z _ _ (eq_refl _) (eq_refl)) as H1.
set (ρ := √((gre z)² + (gim z)²)%L) in H1.
set
  (θ :=
     (if (0 ≤? gim z)%L then rngl_acos (gre z / ρ)
      else (- rngl_acos (gre z / ρ))%A)) in H1.
rewrite H1.
specialize (exists_angle_div_nat Hcz Har Hco) as H2.
specialize (H2 θ n Hnz).
destruct H2 as (θ', Ht).
rewrite <- Ht.
specialize (gc_cos_sin_pow θ' n) as H3.
exists ((rl_nth_root n ρ +ℹ 0) * (rngl_cos θ' +ℹ rngl_sin θ'))%C.
rewrite (gc_pow_mul_l Hic Hop).
rewrite (gc_pow_im_0 Hos).
rewrite gc_cos_sin_pow.
rewrite rl_nth_root_pow. 2: {
  progress unfold ρ.
  apply rl_sqrt_nonneg.
  apply (rngl_add_squ_nonneg Hop Hor).
}
progress unfold gc_mul.
cbn.
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_l.
easy.
Qed.

Notation "‖ x ‖" := (gc_modl x) (at level 35, x at level 30).

Theorem gc_modl_div_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ n d, d ≠ 0%C → (0 ≤ ‖ n ‖ / ‖ d ‖)%L.
Proof.
intros Hon Hop Hiv Hor * Hz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
apply (rngl_div_nonneg Hon Hop Hiv Hor). {
  apply rl_sqrt_nonneg.
  apply (rngl_add_squ_nonneg Hop Hor).
} {
  apply (rl_sqrt_pos Hon Hos Hor).
  apply (rngl_lt_iff Hor).
  split; [ apply (rngl_add_squ_nonneg Hop Hor) | ].
  intros H1; symmetry in H1.
  cbn in Hz.
  apply (rngl_eq_add_0 Hor) in H1; cycle 1. {
    apply (rngl_squ_nonneg Hop Hor).
  } {
    apply (rngl_squ_nonneg Hop Hor).
  }
  destruct H1 as (H1, H2).
  apply (eq_rngl_squ_0 Hos Hio) in H1, H2.
  apply Hz; clear Hz.
  now apply eq_gc_eq.
}
Qed.

Theorem gc_modl_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  (‖ 0 ‖ = 0)%L.
Proof.
intros Hon Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold gc_modl.
progress unfold rl_modl.
cbn.
rewrite (rngl_squ_0 Hos).
rewrite rngl_add_0_l.
apply (rl_sqrt_0 Hon Hop Hor Hii).
Qed.

Theorem gc_mul_1_l :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ z, (1 * z)%C = z.
Proof.
intros Hon Hos.
intros.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_l.
split; apply (rngl_mul_1_l Hon).
Qed.

Theorem gc_mul_1_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ z, (z * 1)%C = z.
Proof.
intros Hon Hos.
intros.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_r.
split; apply (rngl_mul_1_r Hon).
Qed.

Theorem gc_modl_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ z, (0 ≤ ‖ z ‖)%L.
Proof.
intros Hop Hor *.
progress unfold gc_modl.
progress unfold rl_modl.
apply rl_sqrt_nonneg.
apply (rngl_add_squ_nonneg Hop Hor).
Qed.

Theorem rl_modl_opp_l :
  rngl_has_opp T = true →
  ∀ x y, rl_modl (- x) y = rl_modl x y.
Proof.
intros Hop *.
progress unfold rl_modl.
now rewrite (rngl_squ_opp Hop).
Qed.

Theorem rl_modl_opp_r :
  rngl_has_opp T = true →
  ∀ x y, rl_modl x (- y) = rl_modl x y.
Proof.
intros Hop *.
progress unfold rl_modl.
now rewrite (rngl_squ_opp Hop).
Qed.

Theorem gc_modl_opp :
  rngl_has_opp T = true →
  ∀ a : GComplex T, (‖ - a ‖ = ‖ a ‖)%L.
Proof.
intros Hop *.
progress unfold gc_modl.
cbn.
rewrite (rl_modl_opp_l Hop).
rewrite (rl_modl_opp_r Hop).
easy.
Qed.

Theorem gc_add_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a + - b = a - b)%C.
Proof.
intros Hop *.
apply eq_gc_eq.
cbn.
now do 2 rewrite (rngl_add_opp_r Hop).
Qed.

Theorem gc_add_sub :
  rngl_has_opp_or_subt T = true →
  ∀ a b, (a + b - b)%C = a.
Proof.
intros Hos *.
apply eq_gc_eq.
cbn.
now do 2 rewrite (rngl_add_sub Hos).
Qed.

Theorem gc_modl_triangular :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (‖ (a + b) ‖ ≤ ‖ a ‖ + ‖ b ‖)%L.
Proof.
intros Hic Hon Hop Hiv Hor *.
apply (rl_modl_add_le Hic Hon Hop Hiv Hor).
Qed.

Theorem gc_modl_triangular_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (‖ a ‖ ≤ ‖ a + b ‖ + ‖ b ‖)%L.
Proof.
intros Hic Hon Hop Hiv Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (gc_modl_triangular Hic Hon Hop Hiv Hor) as H1.
rewrite <- (gc_modl_opp Hop b).
eapply (rngl_le_trans Hor); [ | apply H1 ].
rewrite (gc_add_opp_r Hop).
rewrite (gc_add_sub Hos).
apply (rngl_le_refl Hor).
Qed.

Theorem gc_pow_succ_r: ∀ a n, (a ^ S n)%C = (a * a ^ n)%C.
Proof. easy. Qed.

Theorem gc_modl_mul :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, ‖ (a * b) ‖ = (‖ a ‖ * ‖ b ‖)%L.
Proof.
intros Hic Hon Hop Hor *.
progress unfold gc_modl.
cbn.
progress unfold rl_modl.
rewrite (rngl_add_comm (gim a * gre b)).
rewrite <- (Brahmagupta_Fibonacci_identity Hic Hon Hop).
apply rl_sqrt_mul; apply (rngl_add_squ_nonneg Hop Hor).
Qed.

Theorem eq_gc_modl_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, ‖ a ‖ = 0%L → a = 0%C.
Proof.
intros Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haz.
apply (eq_rl_sqrt_0 Hon Hos) in Haz. {
  apply (rl_integral_modulus_prop Hop Hor Hii) in Haz.
  now apply eq_gc_eq.
}
apply (rngl_add_squ_nonneg Hop Hor).
Qed.

Theorem gc_modl_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ‖ 1 ‖ = 1%L.
Proof.
intros Hon Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold gc_modl.
progress unfold rl_modl.
cbn.
rewrite (rngl_squ_1 Hon).
rewrite (rngl_squ_0 Hos).
rewrite rngl_add_0_r.
apply (rl_sqrt_1 Hon Hop Hor Hii).
Qed.

Theorem gc_div_1_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a, (a / 1)%C = a.
Proof.
intros Hon Hop Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  apply eq_gc_eq.
  do 2 rewrite (H1 (gre _)), (H1 (gim _)).
  easy.
}
intros.
progress unfold gc_div.
progress unfold gc_inv.
cbn.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
rewrite (rngl_div_1_r Hon Hiq Hc1).
apply eq_gc_eq.
cbn.
do 2 rewrite (rngl_mul_1_r Hon).
rewrite (rngl_opp_0 Hop).
rewrite (rngl_div_0_l Hos Hi1); [ | now apply (rngl_1_neq_0_iff Hon) ].
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
easy.
Qed.

Theorem rngl_inv_sqrt :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → (√a)⁻¹%L = √(a⁻¹)%L.
Proof.
intros Hon Hop Hiv Hor.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haz.
do 2 rewrite <- (rngl_div_1_l Hon Hiv).
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | | easy ]. 2: {
  apply (rngl_0_le_1 Hon Hop Hor).
}
f_equal; symmetry.
apply (rl_sqrt_1 Hon Hop Hor Hii).
Qed.

Theorem gc_modl_inv :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, a ≠ 0%C → ‖ a ‖⁻¹%L = ‖ a⁻¹ ‖.
Proof.
intros Hic Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haz.
progress unfold gc_modl.
cbn.
do 2 rewrite fold_rngl_squ.
progress unfold rl_modl.
remember ((gre a)² + (gim a)²)%L as ρ eqn:Hρ.
assert (Hrz : ρ ≠ 0%L). {
  intros H; apply Haz.
  subst ρ.
  apply (rl_integral_modulus_prop Hop Hor Hii) in H.
  now apply eq_gc_eq.
}
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite (rngl_squ_opp Hop).
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite <- Hρ.
rewrite (rngl_inv_sqrt Hon Hop Hiv Hor). 2: {
  apply (rngl_lt_iff Hor).
  split; [ subst ρ; apply (rngl_add_squ_nonneg Hop Hor) | easy ].
}
f_equal.
progress unfold rngl_div.
rewrite Hiv.
rewrite <- (rngl_squ_inv Hon Hos Hiv); [ | easy ].
progress unfold rngl_squ.
rewrite rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_r Hon Hiv); [ | easy ].
symmetry; apply (rngl_mul_1_l Hon).
Qed.

Theorem gc_modl_div :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, b ≠ 0%C → ‖ (a / b) ‖ = (‖ a ‖ / ‖ b ‖)%L.
Proof.
intros Hic Hon Hop Hiv Hor * Hbz.
progress unfold gc_div.
progress unfold rngl_div.
rewrite Hiv.
rewrite (gc_modl_mul Hic Hon Hop Hor).
f_equal.
symmetry.
now apply (gc_modl_inv Hic Hon Hop Hiv Hor).
Qed.

Theorem gc_div_mul :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, b ≠ 0%C → (a / b * b)%C = a.
Proof.
intros Hic Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hbz.
apply eq_gc_eq.
cbn.
do 2 rewrite fold_rngl_squ.
remember ((gre b)² + (gim b)²)%L as ρ eqn:Hρ.
progress unfold rngl_div.
rewrite Hiv.
rewrite (rngl_mul_opp_l Hop).
do 2 rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
do 2 rewrite rngl_mul_add_distr_r.
do 2 rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_sub_sub_distr Hop).
rewrite rngl_add_assoc.
do 8 rewrite (rngl_mul_mul_swap Hic _ (_ * _⁻¹))%L.
do 8 rewrite rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
do 2 rewrite <- (rngl_mul_sub_distr_r Hop).
do 3 rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_mul_mul_swap Hic _ (gim b)).
rewrite (rngl_add_sub Hos).
rewrite (rngl_mul_mul_swap Hic _ (gim b) (gre b)).
rewrite (rngl_sub_add Hop).
do 4 rewrite <- rngl_mul_assoc.
do 2 rewrite fold_rngl_squ.
do 2 rewrite <- rngl_mul_add_distr_l.
rewrite <- Hρ.
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_r Hiv).
rewrite (rngl_div_diag Hon Hiq). 2: {
  intros H; subst ρ.
  apply (rl_integral_modulus_prop Hop Hor Hii) in H.
  now apply Hbz, eq_gc_eq.
}
now do 2 rewrite (rngl_mul_1_r Hon).
Qed.

Theorem gc_summation_triangular :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  let roc := gc_ring_like_op T in
  ∀ b e (f : nat → GComplex T),
  (‖ ∑ (i = b, e), f i ‖ ≤ ∑ (i = b, e), ‖ f i ‖)%L.
Proof.
intros Hic Hon Hop Hiv Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
progress unfold iter_seq.
remember (S e - b) as n; clear e Heqn.
remember (List.seq b n) as l eqn:Hl.
clear n Hl.
progress unfold iter_list.
induction l as [| a] using List.rev_ind. {
  cbn.
  rewrite (gc_modl_0 Hon Hop Hor Hii).
  apply (rngl_le_refl Hor).
}
cbn.
do 2 rewrite List.fold_left_app.
cbn.
eapply (rngl_le_trans Hor). {
  apply (gc_modl_triangular Hic Hon Hop Hiv Hor).
}
apply (rngl_add_le_mono_r Hop Hor).
apply IHl.
Qed.

Theorem rngl_has_inv_gc_has_inv :
  rngl_mul_is_comm T = true →
  let roc := gc_ring_like_op T in
  rngl_has_inv (GComplex T) = rngl_has_inv T.
Proof.
intros Hic *.
progress unfold rngl_has_inv.
cbn.
progress unfold gc_opt_inv_or_quot.
cbn.
remember (rngl_opt_inv_or_quot T) as iq eqn:Hiq'.
symmetry in Hiq'.
destruct iq as [q| ]; [ | easy ].
destruct q; [ | easy ].
now rewrite Hic.
Qed.

Theorem rngl_inv_gc_inv :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  let roc := gc_ring_like_op T in
  ∀ a, a⁻¹%L = a⁻¹%C.
Proof.
intros Hic Hiv *.
progress unfold gc_inv.
progress unfold rngl_inv.
cbn.
progress unfold gc_opt_inv_or_quot.
cbn.
remember (rngl_opt_inv_or_quot T) as oiq eqn:Hoiq.
symmetry in Hoiq.
move Hoiq at bottom.
generalize Hiv; intros H.
progress unfold rngl_has_inv in H.
rewrite Hoiq in H.
destruct oiq; [ | easy ].
destruct s; [ clear H | easy ].
now rewrite Hic.
Qed.

Theorem rngl_add_gc_add :
  let roc := gc_ring_like_op T in
  ∀ a b, (a + b)%L = (a + b)%C.
Proof. easy. Qed.

Theorem rngl_mul_gc_mul :
  let roc := gc_ring_like_op T in
  ∀ a b, (a * b)%L = (a * b)%C.
Proof. easy. Qed.

Theorem rngl_div_gc_div :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  let roc := gc_ring_like_op T in
  ∀ a b, (a / b)%L = (a / b)%C.
Proof.
intros Hic Hiv *.
progress unfold rngl_div.
progress unfold gc_div.
progress unfold roc.
rewrite (rngl_has_inv_gc_has_inv Hic).
rewrite Hiv.
cbn.
f_equal.
apply (rngl_inv_gc_inv Hic Hiv).
Qed.

Theorem gc_eq_div_0_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  let roc := gc_ring_like_op T in
  ∀ a b,
  (a / b)%C = 0%C
  → b ≠ 0%C
  → a = 0%L.
Proof.
intros Hic Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
intros * Habz Hbz.
progress unfold gc_div in Habz.
progress unfold gc_mul in Habz.
cbn in Habz.
do 4 rewrite (rngl_mul_div_assoc Hiv) in Habz.
do 2 rewrite (rngl_mul_opp_r Hop) in Habz.
do 2 rewrite (rngl_div_opp_l Hop Hiv) in Habz.
rewrite (rngl_sub_opp_r Hop) in Habz.
rewrite (rngl_add_opp_r Hop) in Habz.
rewrite <- (rngl_div_add_distr_r Hiv) in Habz.
rewrite <- (rngl_div_sub_distr_r Hop Hiv) in Habz.
progress unfold rngl_div in Habz.
rewrite Hiv in Habz.
do 2 rewrite fold_rngl_squ in Habz.
injection Habz; clear Habz; intros Habi Habr.
assert (Hrz : ((gre b)² + (gim b)² ≠ 0)%L). {
  intros H.
  apply (rl_integral_modulus_prop Hop Hor Hii) in H.
  now apply Hbz, eq_gc_eq.
}
apply (rngl_eq_mul_0_l Hos Hii) in Habr. 2: {
  intros H.
  now apply (rngl_inv_neq_0 Hon Hos Hiv) in H.
}
apply (rngl_eq_mul_0_l Hos Hii) in Habi. 2: {
  intros H.
  now apply (rngl_inv_neq_0 Hon Hos Hiv) in H.
}
assert (Hia : gim a = 0%L). {
  rewrite rngl_add_comm in Habr.
  apply (f_equal (rngl_mul (gim b))) in Habr.
  apply (f_equal (rngl_mul (gre b))) in Habi.
  rewrite (rngl_mul_0_r Hos) in Habr, Habi.
  rewrite rngl_mul_add_distr_l in Habr.
  rewrite (rngl_mul_sub_distr_l Hop) in Habi.
  rewrite (rngl_mul_comm Hic _ (gre a * _))%L in Habr.
  rewrite (rngl_mul_assoc _ (gre a)) in Habi.
  rewrite (rngl_mul_comm Hic _ (gre a)) in Habi.
  apply (rngl_add_move_0_r Hop) in Habr.
  apply -> (rngl_sub_move_0_r Hop) in Habi.
  rewrite <- Habi in Habr.
  apply (rngl_add_move_0_r Hop) in Habr.
  do 2 rewrite (rngl_mul_comm Hic _ (gim a * _))%L in Habr.
  do 2 rewrite <- rngl_mul_assoc in Habr.
  do 2 rewrite fold_rngl_squ in Habr.
  rewrite <- (rngl_mul_add_distr_l) in Habr.
  rewrite rngl_add_comm in Habr.
  apply (rngl_eq_mul_0_l Hos Hii) in Habr; [ | easy ].
  rewrite Habr in Habi.
  rewrite (rngl_mul_0_l Hos) in Habi.
  rewrite (rngl_mul_0_r Hos) in Habi.
  now symmetry in Habi.
}
rewrite Hia in Habi, Habr.
rewrite (rngl_mul_0_l Hos) in Habi, Habr.
rewrite (rngl_sub_0_l Hop) in Habi.
rewrite rngl_add_0_r in Habr.
apply (f_equal rngl_opp) in Habi.
rewrite (rngl_opp_involutive Hop) in Habi.
rewrite (rngl_opp_0 Hop) in Habi.
apply (rngl_integral Hos Hio) in Habi, Habr.
destruct Habi as [Habi| Hbi]; [ now apply eq_gc_eq | ].
destruct Habr as [Habr| Hbr]; [ now apply eq_gc_eq | ].
now exfalso; apply Hbz, eq_gc_eq.
Qed.

Theorem rngl_0_gc_0 :
  let roc := gc_ring_like_op T in
  0%L = 0%C.
Proof. now intros; apply eq_gc_eq. Qed.

Theorem rngl_1_gc_1 :
  let roc := gc_ring_like_op T in
  1%L = 1%C.
Proof.
intros.
apply eq_gc_eq; cbn.
progress unfold rngl_one.
cbn.
progress unfold gc_opt_one.
now destruct (rngl_opt_one T).
Qed.

Theorem gc_eq_mul_0_l :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a * b = 0 → b ≠ 0 → a = 0)%C.
Proof.
intros Hic Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff in Hii.
  apply Bool.orb_true_iff.
  destruct Hii as [Hii| Hii]; [ now left | right ].
  rewrite Hii; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
intros * Hab Hbz.
apply eq_gc_eq in Hab.
cbn in Hab.
destruct Hab as (Habr, Habi).
rewrite rngl_add_comm in Habi.
assert (Hra : gre a = 0%L). {
  apply (f_equal (rngl_mul (gre b))) in Habr.
  apply (f_equal (rngl_mul (gim b))) in Habi.
  rewrite (rngl_mul_0_r Hos) in Habr, Habi.
  rewrite (rngl_mul_sub_distr_l Hop) in Habr.
  rewrite rngl_mul_add_distr_l in Habi.
  rewrite (rngl_mul_assoc _ (gim a)) in Habr.
  rewrite (rngl_mul_comm Hic _ (gim a)) in Habr.
  rewrite (rngl_mul_comm Hic _ (gim a * _))%L in Habi.
  apply -> (rngl_sub_move_0_r Hop) in Habr.
  rewrite rngl_add_comm in Habi.
  apply (rngl_add_move_0_r Hop) in Habi.
  rewrite Habi in Habr.
  apply (rngl_add_move_0_r Hop) in Habr.
  rewrite (rngl_mul_comm Hic (gre b)) in Habr.
  rewrite (rngl_mul_comm Hic (gim b)) in Habr.
  do 2 rewrite <- rngl_mul_assoc in Habr.
  rewrite <- (rngl_mul_add_distr_l) in Habr.
  do 2 rewrite fold_rngl_squ in Habr.
  apply (rngl_eq_mul_0_l Hos Hii) in Habr; [ easy | ].
  intros H; apply Hbz.
  apply (rl_integral_modulus_prop Hop Hor Hii) in H.
  now apply eq_gc_eq.
}
rewrite Hra in Habr, Habi.
rewrite (rngl_mul_0_l Hos) in Habr, Habi.
rewrite (rngl_sub_0_l Hop) in Habr.
rewrite rngl_add_0_l in Habi.
apply (f_equal rngl_opp) in Habr.
rewrite (rngl_opp_involutive Hop) in Habr.
rewrite (rngl_opp_0 Hop) in Habr.
apply (rngl_integral Hos Hio) in Habr, Habi.
destruct Habr as [Habr| Habr]; [ now apply eq_gc_eq | ].
destruct Habi as [Habi| Habi]; [ now apply eq_gc_eq | ].
now exfalso; apply Hbz, eq_gc_eq.
Qed.

Theorem gc_pow_nonzero :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a n, a ≠ 0%C → (a ^ n)%C ≠ 0%C.
Proof.
intros Hic Hon Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haz Hanz.
  apply Haz; clear Haz.
  apply eq_gc_eq; cbn.
  split; apply H1.
}
intros * Haz Hanz.
apply Haz; clear Haz.
induction n. {
  cbn in Hanz.
  apply eq_gc_eq in Hanz.
  rewrite gre_1, gim_1 in Hanz.
  destruct Hanz as (H, _).
  now apply (rngl_1_neq_0_iff Hon) in H.
}
cbn in Hanz.
destruct (gc_eq_dec Heo a 0) as [Haz| Haz]; [ easy | exfalso ].
rewrite (gc_mul_comm Hic) in Hanz.
apply (gc_eq_mul_0_l Hic Hop Hor Hii) in Hanz; [ | easy ].
now apply Haz, IHn.
Qed.

Theorem rngl_pow_gc_pow :
  let roc := gc_ring_like_op T in
  ∀ z n, (z ^ n)%L = (z ^ n)%C.
Proof. easy. Qed.

Theorem gc_modl_pow :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ z n, (‖ z ^ n ‖ = ‖ z ‖ ^ n)%L.
Proof.
intros Hic Hon Hop Hor Hii *.
induction n; cbn. {
  rewrite rngl_1_gc_1.
  apply (gc_modl_1 Hon Hop Hor Hii).
}
rewrite (gc_modl_mul Hic Hon Hop Hor).
rewrite rngl_pow_gc_pow.
now rewrite IHn.
Qed.

Theorem gc_mul_div_assoc :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a b c, (a * (b / c))%C = (a * b / c)%C.
Proof.
intros Hop Hiv.
intros.
apply eq_gc_eq; cbn.
rewrite (rngl_div_opp_l Hop Hiv).
do 4 rewrite (rngl_mul_opp_r Hop).
do 2 rewrite (rngl_sub_opp_r Hop).
do 2 rewrite (rngl_add_opp_r Hop).
do 2 rewrite fold_rngl_squ.
remember ((gre c)² + (gim c)²)%L as ρ eqn:Hρ.
do 2 rewrite rngl_mul_add_distr_l.
do 2 rewrite rngl_mul_add_distr_r.
do 2 rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_sub_distr_r Hop).
do 8 rewrite rngl_mul_assoc.
do 8 rewrite (rngl_mul_div_assoc Hiv).
do 2 rewrite (rngl_sub_sub_distr Hop).
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop).
do 4 rewrite <- (rngl_div_add_distr_r Hiv).
do 4 rewrite <- (rngl_div_sub_distr_r Hop Hiv).
do 4 rewrite <- (rngl_div_add_distr_r Hiv).
do 4 rewrite <- (rngl_add_sub_swap Hop).
rewrite rngl_add_add_swap.
split; [ easy | ].
rewrite rngl_add_add_swap.
easy.
Qed.

Theorem gc_pow_1_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ a, (a ^ 1)%C = a.
Proof.
intros Hon Hos *.
apply eq_gc_eq; cbn.
rewrite gre_1, gim_1.
do 2 rewrite (rngl_mul_1_r Hon).
do 2 rewrite (rngl_mul_0_r Hos).
now rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
Qed.

Theorem gc_pow_add_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a i j, (a ^ (i + j))%C = (a ^ i * a ^ j)%C.
Proof.
intros Hon Hop.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
do 3 rewrite <- rngl_pow_gc_pow.
rewrite <- rngl_mul_gc_mul.
induction i. {
  symmetry; cbn.
  rewrite rngl_1_gc_1.
  apply (gc_mul_1_l Hon Hos).
}
cbn in IHi |-*.
rewrite IHi.
now rewrite <- (gc_mul_assoc Hop).
Qed.

Theorem gc_mul_div :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, b ≠ 0%C → (a * b / b)%C = a.
Proof.
intros Hic Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
intros * Hbz.
apply eq_gc_eq; cbn.
do 2 rewrite fold_rngl_squ.
remember ((gre b)² + (gim b)²)%L as ρ eqn:Hρ.
rewrite (rngl_div_opp_l Hop Hiv).
do 2 rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
do 2 rewrite rngl_mul_add_distr_r.
do 2 rewrite (rngl_mul_sub_distr_r Hop).
do 8 rewrite (rngl_mul_div_assoc Hiv).
rewrite rngl_add_assoc.
rewrite (rngl_sub_sub_distr Hop).
do 2 rewrite (rngl_mul_mul_swap Hic _ (gim b) (gre b)).
rewrite (rngl_sub_add Hop).
rewrite (rngl_add_sub Hos).
do 2 rewrite <- (rngl_div_add_distr_r Hiv).
do 4 rewrite <- rngl_mul_assoc.
do 2 rewrite fold_rngl_squ.
do 2 rewrite <- rngl_mul_add_distr_l.
rewrite <- Hρ.
rewrite (rngl_mul_div Hi1). 2: {
  intros H; subst ρ.
  apply (rl_integral_modulus_prop Hop Hor Hii) in H.
  now apply Hbz, eq_gc_eq.
}
rewrite (rngl_mul_div Hi1). 2: {
  intros H; subst ρ.
  apply (rl_integral_modulus_prop Hop Hor Hii) in H.
  now apply Hbz, eq_gc_eq.
}
easy.
Qed.

Theorem gc_pow_div :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ z n, z ≠ 0%C → n ≠ 0 → (z ^ n / z = z ^ (n - 1))%C.
Proof.
intros Hic Hon Hop Hiv Hor.
intros * Hzz Hnz.
destruct n; [ easy | clear Hnz; cbn ].
rewrite Nat.sub_0_r.
rewrite (gc_mul_comm Hic).
now apply (gc_mul_div Hic Hon Hop Hiv Hor).
Qed.

Context {Hon : rngl_has_1 T = true}.
Context {Hic : rngl_mul_is_comm T = true}.
Context {Hop : rngl_has_opp T = true}.
Context {Hiv : rngl_has_inv T = true}.
Context {Hor : rngl_is_ordered T = true}.

(* to be completed
Theorem gc_opt_alg_closed :
  let roc := gc_ring_like_op T in
  let rpc := gc_ring_like_prop_not_alg_closed Hon Hic Hop Hiv Hor in
  if (rngl_has_opp T && rngl_has_inv (GComplex T) &&
      rngl_has_1 (GComplex T))%bool
  then
     ∀ l : list (GComplex T), 1 < length l → List.last l 0%L ≠ 0%L →
     ∃ x : GComplex T, rngl_eval_polyn l x = 0%L
  else not_applicable.
Proof.
intros; cbn.
rewrite Hop.
remember (rngl_has_inv (GComplex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 (GComplex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ cbn | easy ].
intros la Hla Hl1.
Theorem gc_polyn_modl_tends_to_inf_when_modl_var_tends_to_inf :
  let roc := gc_ring_like_op T in
  let rpc := gc_ring_like_prop_not_alg_closed Hon Hic Hop Hiv Hor in
  ∀ P : list (GComplex T),
  1 < length P
  → ∀ M, (0 < M)%L →
  List.nth (length P - 1) P 0%L ≠ 0%C
  → ∃ R₀, (0 < R₀)%L ∧
    ∀ z : GComplex T, (R₀ < ‖z‖)%L → (M < ‖rngl_eval_polyn P z‖)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros roc rpc * Hn1 * HM Hz.
  rewrite H1 in HM.
  now apply (rngl_lt_irrefl Hor) in HM.
}
intros roc rpc * H1len * HM Hz.
(**)
remember (List.length P - 1) as n eqn:Hn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  apply Nat.sub_0_le in Hnz.
  destruct P as [| a]; [ easy | ].
  cbn in H1len, Hnz.
  now apply Nat.nle_gt in H1len.
}
apply Nat.neq_0_lt_0 in Hnz.
(*
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  move Hn1 at top; subst n.
  destruct P as [| a]; [ easy | ].
  destruct P as [| b]; [ easy | ].
  destruct P; [ | easy ].
  clear H1len Hn Hnz.
  cbn in Hz |-*.
...
*)
remember (Max (i = 0, n - 1), ‖ P.[i] ‖ / ‖ P.[n] ‖)%L as m.
set (R₀ := (1 + M + rngl_of_nat n * m)%L).
subst m.
exists R₀.
assert (Hr : (0 < R₀)%L). {
  progress unfold R₀.
  apply (rngl_lt_le_trans Hor _ 1). {
    apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  }
  rewrite <- rngl_add_assoc.
  apply (rngl_le_add_r Hor).
  apply (rngl_add_nonneg_nonneg Hor). {
    now apply (rngl_lt_le_incl Hor) in HM.
  }
  progress unfold iter_seq.
  progress unfold iter_list.
  rewrite Nat.sub_0_r.
  rewrite <- Nat_succ_sub_succ_r; [ | easy ].
  rewrite Nat.sub_0_r.
(*
  remember (P.[n]) as d eqn:Hd.
*)
  destruct n; [ easy | clear Hnz ].
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    rewrite <- rngl_of_nat_0.
    now apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
  }
  rewrite fold_iter_list.
  rewrite fold_iter_seq'; cbn.
  rewrite Nat.sub_0_r.
  eapply (rngl_le_trans Hor). 2: {
    apply (rngl_le_max_seq_r Hor _ _ n). 2: {
      apply List.in_seq.
      split; [ easy | ].
      now rewrite Nat.sub_0_r.
    }
    intros m Hm.
    rewrite Nat.sub_0_r in Hm.
    apply (rngl_max_r_iff Hor).
    apply (rngl_div_nonneg Hon Hop Hiv Hor).
    apply (gc_modl_nonneg Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply (gc_modl_nonneg Hop Hor) | ].
    intros H; symmetry in H.
    progress replace 0%C with 0%L in H by easy.
    now apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
  }
  apply (rngl_div_nonneg Hon Hop Hiv Hor).
  apply (gc_modl_nonneg Hop Hor).
  apply (rngl_lt_iff Hor).
  split; [ apply (gc_modl_nonneg Hop Hor) | ].
  intros H; symmetry in H.
  progress replace 0%C with 0%L in H by easy.
  now apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
}
split; [ easy | ].
intros z Hrz.
assert (Hzz : z ≠ 0%C). {
  intros H; subst z.
  rewrite (gc_modl_0 Hon Hop Hor Hii) in Hrz.
  now apply (rngl_lt_asymm Hor) in Hr.
}
remember (Max (i = _, _), _) as m eqn:Hm.
assert (Hz1z : (0 < ‖ (1 / z) ‖)%L). {
  apply (rngl_lt_iff Hor).
  split; [ apply (gc_modl_nonneg Hop Hor) | ].
  intros H; symmetry in H.
  apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
  apply (f_equal (rngl_mul z)) in H.
  cbn in H.
(**)
...
  rewrite rngl_mul_0_r in H.
...
  rewrite (gc_mul_0_r Hos) in H.
  rewrite (gc_mul_comm Hic) in H.
  rewrite (gc_div_mul Hic Hon Hop Hiv Hor) in H; [ | easy ].
  apply eq_gc_eq in H.
  cbn in H.
  destruct H as (H, _).
  now apply (rngl_1_neq_0_iff Hon) in H.
}
assert (H1 : (‖ 1 / z ‖ * R₀ ≤ ‖ z ‖)%L). {
  apply (rngl_le_trans Hor _ R₀); [ | ]. 2: {
    now apply (rngl_lt_le_incl Hor) in Hrz.
  }
  apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
  rewrite (rngl_div_diag Hon Hiq). 2: {
    intros H; rewrite H in Hr.
    now apply (rngl_lt_irrefl Hor) in Hr.
  }
  rewrite (gc_modl_div Hic Hon Hop Hiv Hor); [ | easy ].
  rewrite (gc_modl_1 Hon Hop Hor Hii).
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    apply (rngl_lt_iff Hor).
    split; [ apply (gc_modl_nonneg Hop Hor) | ].
    intros H; symmetry in H.
    now apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
  }
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_le_trans Hor _ R₀); [ | now apply (rngl_lt_le_incl Hor) ].
  progress unfold R₀.
  rewrite <- rngl_add_assoc.
  apply (rngl_le_add_r Hor).
  apply (rngl_add_nonneg_nonneg Hor). {
    now apply (rngl_lt_le_incl Hor) in HM.
  }
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_of_nat_nonneg Hon Hop Hor).
  }
  subst m.
  eapply (rngl_le_trans Hor). 2: {
    apply (rngl_le_max_seq_r Hor _ _ 0). 2: {
      apply List.in_seq.
      split; [ easy | ].
      now rewrite Nat.sub_0_r, Nat.add_0_l.
    }
    intros i Hi.
    apply (rngl_max_r_iff Hor).
    now apply (gc_modl_div_nonneg Hon Hop Hiv Hor).
  }
  now apply (gc_modl_div_nonneg Hon Hop Hiv Hor).
}
assert (H2 : (‖ 1 / z ‖ * rngl_of_nat n * m ≤ ‖ z ‖)%L). {
  eapply (rngl_le_trans Hor); [ | apply H1 ].
  rewrite <- rngl_mul_assoc.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
  progress unfold R₀.
  apply (rngl_le_add_l Hor).
  apply (rngl_le_trans Hor _ 1); [ apply (rngl_0_le_1 Hon Hop Hor) | ].
  apply (rngl_le_add_r Hor).
  now apply (rngl_lt_le_incl Hor) in HM.
}
clear H1.
assert
  (H1 :
    (‖ 1 / z ‖ *
        ‖ (∑ (i = 0, n - 1), P.[i] / P.[n] * (1 / z ^ (n - 1 - i))) ‖ ≤
          ‖ z ‖)%L). {
  eapply (rngl_le_trans Hor); [ | apply H2 ].
  rewrite <- rngl_mul_assoc.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
  rewrite Hm.
  rewrite <- (rngl_summation_1 0 (n - 1)); [ | flia Hnz ].
  rewrite (rngl_mul_summation_distr_r Hos).
  eapply (rngl_le_trans Hor). {
    apply (gc_summation_triangular Hic Hon Hop Hiv Hor Hii).
  }
  apply (rngl_summation_le_compat Hor).
  intros i (_, Hi).
  rewrite (rngl_mul_1_l Hon).
  eapply (rngl_le_trans Hor). 2: {
    apply (rngl_le_max_seq_r Hor _ _ i). 2: {
      apply List.in_seq.
      split; [ easy | ].
      rewrite Nat.sub_0_r, Nat.add_0_l.
      now apply Nat.lt_succ_r.
    }
    intros j Hj.
    apply (rngl_max_r_iff Hor).
    apply (rngl_div_nonneg Hon Hop Hiv Hor).
    apply (gc_modl_nonneg Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply (gc_modl_nonneg Hop Hor) | ].
    apply not_eq_sym.
    intros H.
    now apply eq_gc_modl_0 in H.
  }
  rewrite <- (gc_modl_div Hic Hon Hop Hiv Hor); [ | easy ].
  remember (P.[i] / P.[n])%L as x eqn:Hx.
  rewrite (rngl_div_gc_div Hic Hiv) in Hx.
  rewrite <- Hx; cbn.
  rewrite (gc_modl_mul Hic Hon Hop Hor).
  rewrite (rngl_mul_comm Hic).
  destruct (rngl_eq_dec Heo (‖ x ‖) 0) as [Hxz| Hxz]. {
    rewrite Hxz.
    rewrite (rngl_mul_0_r Hos).
    apply (rngl_le_refl Hor).
  }
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_lt_iff Hor).
    split; [ | easy ].
    apply (gc_modl_nonneg Hop Hor).
  }
  rewrite (rngl_div_diag Hon Hiq); [ | easy ].
  rewrite (rngl_div_gc_div Hic Hiv).
  rewrite (gc_modl_div Hic Hon Hop Hiv Hor). 2: {
    replace (z ^ (n - 1 - i))%L with (z ^ (n - 1 - i))%C by easy.
    now apply (gc_pow_nonzero Hic Hon Hop Hor Hii).
  }
  progress unfold roc.
  rewrite rngl_1_gc_1.
  rewrite (gc_modl_1 Hon Hop Hor Hii).
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    apply (rngl_lt_iff Hor).
    split; [ apply (gc_modl_nonneg Hop Hor) | ].
    intros H; symmetry in H.
    apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
    now apply (gc_pow_nonzero Hic Hon Hop Hor Hii) in H.
  }
  rewrite (rngl_mul_1_l Hon).
  rewrite rngl_pow_gc_pow.
  rewrite (gc_modl_pow Hic Hon Hop Hor Hii).
  apply (rngl_pow_ge_1 Hop Hon Hor).
  eapply (rngl_le_trans Hor). 2: {
    apply (rngl_lt_le_incl Hor), Hrz.
  }
  progress unfold R₀.
  rewrite <- rngl_add_assoc.
  apply (rngl_le_add_r Hor).
  apply (rngl_add_nonneg_nonneg Hor). {
    now apply (rngl_lt_le_incl Hor) in HM.
  }
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_of_nat_nonneg Hon Hop Hor).
  rewrite Hm.
  (* lemma *)
  progress unfold iter_seq.
  apply (rngl_iter_max_list_nonneg Hor).
  intros j Hj.
  now apply (gc_modl_div_nonneg Hon Hop Hiv Hor).
}
clear H2.
apply (rngl_mul_le_mono_nonneg_l Hop Hor (‖ z ^ (n - 1) ‖))%L in H1. 2: {
  apply (gc_modl_nonneg Hop Hor).
}
rewrite rngl_mul_assoc in H1.
do 3 rewrite <- (gc_modl_mul Hic Hon Hop Hor) in H1.
rewrite (gc_mul_div_assoc Hop Hiv) in H1.
rewrite (gc_mul_1_r Hon Hos) in H1.
rewrite <- (gc_pow_1_r Hon Hos z) in H1 at 4.
rewrite <- (gc_pow_add_r Hon Hop) in H1.
rewrite Nat.sub_add in H1; [ | easy ].
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  move Hn1 at top; subst n.
  destruct P as [| a]; [ easy | ].
  destruct P as [| b]; [ easy | ].
  destruct P; [ | easy ].
  clear H1len Hn Hnz.
  cbn in Hz |-*.
  rewrite (gc_mul_0_l Hos).
  rewrite gc_add_0_l.
  rewrite Nat.sub_diag in H1.
  progress unfold iter_seq in H1.
  progress unfold iter_list in H1.
  cbn in H1.
  rewrite gc_add_0_l in H1.
  rewrite rngl_1_gc_1 in H1.
  rewrite (gc_mul_1_r Hon Hos) in H1.
  progress unfold roc in H1.
  rewrite rngl_1_gc_1 in H1.
  rewrite (rngl_div_gc_div Hic Hiv) in H1.
  rewrite (rngl_div_gc_div Hic Hiv) in H1.
  rewrite (gc_div_1_r Hon Hop Hiv) in H1.
  rewrite (gc_mul_1_r Hon Hos) in H1.
  rewrite Nat.sub_diag in Hm.
  rewrite iter_seq_only_one in Hm. 2: {
    apply (rngl_max_r_iff Hor); cbn.
    apply (rngl_div_nonneg Hon Hop Hiv Hor).
    apply (gc_modl_nonneg Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply (gc_modl_nonneg Hop Hor) | ].
    symmetry; intros H.
    now apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
  }
  cbn in Hm.
  rewrite <- (gc_modl_div Hic Hon Hop Hiv Hor) in Hm; [ | easy ].
  rewrite (gc_modl_mul Hic Hon Hop Hor) in H1.
  rewrite <- Hm in H1.
(**)
  subst R₀.
  rewrite rngl_of_nat_1 in Hrz.
  rewrite (rngl_mul_1_l Hon) in Hrz.
  rewrite (rngl_add_comm 1) in Hrz.
  rewrite <- rngl_add_assoc in Hrz.
  apply (rngl_add_lt_mono_r Hop Hor _ _ (1 + m))%L.
  eapply (rngl_lt_le_trans Hor); [ apply Hrz | ].
...
  rewrite <- (gc_div_mul Hic Hon Hop Hiv Hor a b); [ | easy ].
  (* lemma *)
  rewrite (gc_mul_comm Hic _ b).
  do 2 rewrite <- rngl_mul_gc_mul.
  rewrite <- rngl_add_gc_add.
  rewrite <- (rngl_div_gc_div Hic Hiv).
  rewrite <- (gc_mul_add_distr_l Hop); cbn.
  rewrite (gc_modl_mul Hic Hon Hop Hor).
  subst R₀.
  rewrite rngl_of_nat_1 in Hrz.
  rewrite (rngl_mul_1_l Hon) in Hrz.
  rewrite (rngl_add_comm 1) in Hrz.
  rewrite <- rngl_add_assoc in Hrz.
  apply (rngl_add_lt_mono_r Hop Hor _ _ (1 + m))%L.
  eapply (rngl_lt_le_trans Hor); [ apply Hrz | ].
...
  eapply (rngl_lt_le_trans Hor). 2: {
    apply (rngl_mul_le_mono_nonneg_l Hop Hor).
    apply (gc_modl_nonneg Hop Hor).
  }
...
(* ah, mais, ci-dessous n'est pas forcément vrai, si les
   P.[i] sont tous nuls (sauf P.[n] of course). Du coup,
   j'ai l'air d'un con *)
assert (Hzm : (0 < m)%L). {
  subst m.
  apply (rngl_lt_iff Hor).
  split. {
    eapply (rngl_le_trans Hor). 2: {
      apply (rngl_le_max_seq_r Hor _ _ 0). 2: {
        apply List.in_seq.
        split; [ easy | ].
        now rewrite Nat.sub_0_r, Nat.add_0_l.
      }
      intros i Hi.
      apply (rngl_max_r_iff Hor).
      now apply (gc_modl_div_nonneg Hon Hop Hiv Hor).
    }
    now apply (gc_modl_div_nonneg Hon Hop Hiv Hor).
  }
  intros H1; symmetry in H1.
  subst R₀.
  rewrite H1 in Hr, Hrz.
  rewrite (rngl_mul_0_r Hos) in Hr, Hrz.
  rewrite rngl_add_0_r in Hr, Hrz.
  specialize (eq_rngl_max_seq_0 Hor _ _ _ H1) as H2.
  cbn in H2.
  progress replace 0%C with 0%L in H2 by easy.
  assert (H : ∀ i, 0 ≤ i ≤ n - 1 → (0 ≤ ‖ P.[i] ‖ / ‖ P.[n] ‖)%L ). {
    intros * Hi.
    apply (rngl_div_nonneg Hon Hop Hiv Hor).
    apply (gc_modl_nonneg Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply (gc_modl_nonneg Hop Hor) | ].
    intros H; symmetry in H.
    now apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
  }
  specialize (H2 H); clear H.
  specialize (H2 0).
  assert (H : 0 ≤ 0 ≤ n - 1) by easy.
  specialize (H2 H); clear H.
  (* lemma ? *)
  apply (f_equal (rngl_mul (‖ P.[n] ‖))) in H2.
  rewrite (rngl_mul_0_r Hos) in H2.
  rewrite (rngl_mul_comm Hic) in H2.
  rewrite (rngl_div_mul Hon Hiv) in H2. 2: {
    intros H.
    now apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
  }
(* ouais bon, y a aucune raison que P.[0] vaille 0 *)
...
Search (_ = _ / _)%L.
apply rngl_
apply (rngl_div_0_l
...
  specialize (H1 _ _ _ H).
...
rewrite fold_left_fun_from_0 in Hmz.
destruct Hi as [Hi| Hi]. {
  subst i.
  apply IHl.
...
intros Hor * Hmz i Hi.
induction l as [| a]; [ easy | ].
destruct Hi as [Hi| Hi]. {
  subst i.
...
  rewrite (max_iter_list_cons Hor) in Hmz. 2: {
    intros j Hj.
    destruct Hj as [Hj| Hj]. {
      subst j.
      apply (rngl_max_r_iff Hor).

...

Theorem eq_rngl_max_seq_0 :
  ∀ b e (f : nat → T),
  Max (i = b, e), f i = 0%L
  → ∀ i, b ≤ i ≤ e → f i = 0%L.
Proof.
intros * Hmz i Hi.
progress unfold iter_seq in Hmz.
apply (eq_rngl_max_list_0 (List.seq b (S e - b))); [ easy | ].
apply List.in_seq.
split; [ easy | ].
flia Hi.
Qed.
... ...
specialize (eq_rngl_max_seq_0 _ _ _ H) as H1.
cbn in H1.
replace 0%C with 0%L in H1 by easy.
clear H.
(* ah bin non, faut voir... *)
...
assert (H1 : (rngl_of_nat n * m < ‖ z ‖)%L). {
  eapply (rngl_le_lt_trans Hor); [ | apply Hrz ].
  progress unfold R₀.
  apply (rngl_le_add_l Hor).
  apply (rngl_le_trans Hor _ 1). 2: {
    apply (rngl_le_add_r Hor).
    now apply (rngl_lt_le_incl Hor) in HM.
  }
  apply (rngl_0_le_1 Hon Hop Hor).
}
assert (H2 : (‖ 1 / z ‖ * rngl_of_nat n * m < ‖ z ‖)%L). {
  eapply (rngl_le_lt_trans Hor); [ | apply H1 ].
  rewrite <- rngl_mul_assoc.
  rewrite <- (rngl_mul_1_l Hon).
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii). {
    apply (rngl_mul_pos_pos Hop Hor Hii). 2: {
...
    rewrite <- rngl_of_nat_0.
...
  clear Hd.
  clear Hn Hn1 R₀ Hnz.
  induction n; [ apply (rngl_le_refl Hor) | ].
  rewrite List.seq_S; cbn.
  rewrite List.fold_left_app.
  cbn.
  eapply (rngl_le_trans Hor); [ apply IHn | ].
  apply (rngl_le_max_l Hor).
}
...
remember (List.length P) as n eqn:Hn.
(* must take
   R₀ ​= max(‖a_{n-1}/a_n‖, ‖a_{n-2}/a_n‖^(1/2), .. ‖a₀/a_n‖^(1/n)
 *)
set (R₀ := (1 + M + Max (i = 0, n - 2), (‖ P.[i] ‖ / ‖ P.[n - 1] ‖))%L).
assert (Hr : (0 < R₀)%L). {
  progress unfold R₀.
  apply (rngl_lt_le_trans Hor _ 1). {
    apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  }
  rewrite <- rngl_add_assoc.
  apply (rngl_le_add_r Hor).
  apply (rngl_add_nonneg_nonneg Hor). {
    now apply (rngl_lt_le_incl Hor) in HM.
  }
  progress unfold iter_seq.
  progress unfold iter_list.
  rewrite Nat.sub_0_r.
  rewrite <- Nat_succ_sub_succ_r; [ | easy ].
  remember (P.[n - 1]) as d eqn:Hd.
  destruct n; [ easy | ].
  rewrite Nat_sub_succ_1.
  clear Hd.
  clear Hn Hn1 R₀.
  induction n; [ apply (rngl_le_refl Hor) | ].
  rewrite List.seq_S; cbn.
  rewrite List.fold_left_app.
  cbn.
  eapply (rngl_le_trans Hor); [ apply IHn | ].
  apply (rngl_le_max_l Hor).
}
exists R₀.
split; [ easy | ].
intros z H1.
subst R₀.
assert (Hpz :
    ∀ i, i < n - 1 → (1 + M + ‖ P.[i] ‖ / ‖ P.[n - 1] ‖ < ‖ z ‖)%L). {
  intros i Hi.
  eapply (rngl_le_lt_trans Hor); [ | apply H1 ].
  apply (rngl_add_le_mono_l Hop Hor).
  eapply (rngl_le_trans Hor); [ | apply (le_max_seq_r Hor) ]. {
    apply (rngl_le_refl Hor).
  } {
    intros x Hx.
    apply (rngl_max_r_iff Hor).
    now apply (gc_modl_div_nonneg Hon Hop Hiv Hor).
  }
  rewrite Nat.sub_0_r.
  apply List.in_seq.
  split; [ easy | ].
  rewrite Nat.add_0_l.
  rewrite <- Nat_succ_sub_succ_r; [ easy | ].
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  now apply -> Nat.succ_lt_mono.
}
clear H1.
rename n into m; rename Hn into Hm.
remember (m - 1) as n eqn:Hn.
progress replace (m - 2) with (n - 1) in Hr by flia Hn.
assert (H1 :
  (‖ P.[n] * z ^ n ‖ - ∑ (k = 0, n - 1), ‖ P.[k] * z ^ k ‖ ≤
   ‖ rngl_eval_polyn P z ‖)%L). {
  apply (rngl_le_sub_le_add_r Hop Hor).
  progress unfold rngl_eval_polyn.
  progress unfold iter_seq.
  progress unfold iter_list.
  rewrite Nat.sub_0_r.
  assert (Hnz : 0 < n). {
    subst n.
    now apply Nat.lt_add_lt_sub_r.
  }
  rewrite <- Nat_succ_sub_succ_r; [ | easy ].
  rewrite Nat.sub_0_r.
  subst n.
  destruct m; [ easy | ].
  rewrite Nat_sub_succ_1 in Hz, Hnz, Hpz |-*.
  clear Hn1.
  symmetry in Hm.
  clear Hpz Hr.
  revert P Hm Hz.
  induction m; intros; [ easy | clear Hnz ].
  destruct m. {
    clear IHm.
    cbn.
    rewrite rngl_add_0_l.
    destruct P as [| a la]; [ easy | cbn ].
    destruct la as [| b]; [ easy | ].
    destruct la; [ | easy ].
    cbn in Hz |-*; clear Hm.
    (* why gc_mul_1_r and rngl_mul_1_r don't work? ... *)
    replace 1%L with (@gc_one T ro). 2: {
      apply eq_gc_eq.
      now rewrite gre_1, gim_1.
    }
    do 2 rewrite (gc_mul_1_r Hon Hos).
    rewrite (gc_mul_0_l Hos).
    rewrite gc_add_0_l.
    apply (gc_modl_triangular_2 Hic Hon Hop Hiv Hor).
  }
  specialize (IHm (Nat.lt_0_succ _)).
  destruct P as [| a]; [ easy | ].
  rewrite List_nth_succ_cons in Hz |-*.
  cbn in Hm.
  apply Nat.succ_inj in Hm.
  specialize (IHm P Hm Hz).
  rewrite gc_pow_succ_r.
  rewrite (gc_mul_comm Hic z).
  rewrite (gc_mul_assoc Hop).
  rewrite (gc_modl_mul Hic Hon Hop Hor).
  eapply (rngl_le_trans Hor). {
    apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ (‖ z ‖)) in IHm. 2: {
      apply (gc_modl_nonneg Hop Hor).
    }
    apply IHm.
  }
  rewrite rngl_mul_add_distr_r.
  remember (S m) as sm.
  cbn - [ List.nth ].
  rewrite rngl_add_0_l.
  rewrite List_nth_0_cons.
  (* why gc_mul_1_r and rngl_mul_1_r don't work? ... *)
  replace 1%L with (@gc_one T ro). 2: {
    apply eq_gc_eq.
    now rewrite gre_1, gim_1.
  }
  rewrite (gc_mul_1_r Hon Hos).
  remember (List.fold_right _ _ _) as x.
  replace 1 with (0 + 1) by easy.
  specialize fold_left_add_seq_add as H1.
  specialize (H1 (‖ a ‖)%L 0 sm 1).
  rewrite (H1 (λ c k, ‖ (List.nth k (a :: P) 0)%C * z ^ k ‖)).
  clear H1; cbn - [ gc_pow_nat ].
  rewrite (fold_left_rngl_add_fun_from_0 _ (‖ a ‖)%L).
  rewrite rngl_add_assoc.
  apply (rngl_add_le_compat Hor). {
    rewrite <- (gc_modl_mul Hic Hon Hop Hor).
    apply (gc_modl_triangular_2 Hic Hon Hop Hiv Hor).
  }
  do 2 rewrite fold_iter_list.
  rewrite (rngl_mul_summation_list_distr_r Hos).
  apply (rngl_summation_list_le_compat Hor).
  intros i Hi.
  rewrite <- (gc_modl_mul Hic Hon Hop Hor).
  rewrite <- (gc_mul_assoc Hop).
  rewrite (gc_mul_comm Hic _ z).
  rewrite <- gc_pow_succ_r.
  apply (rngl_le_refl Hor).
}
eapply (rngl_lt_le_trans Hor); [ | apply H1 ].
apply (rngl_lt_add_lt_sub_r Hop Hor).
...
*)

End a.

(* to be completed
Definition gc_ring_like_prop T
  {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T}
  {roc : ring_like_op (GComplex T)}
  (Hop : rngl_has_opp T = true) :
    @ring_like_prop (GComplex T) (gc_ring_like_op T) :=
  let Hos := rngl_has_opp_has_opp_or_subt Hop in
  let Hsu := rngl_has_opp_has_no_subt Hop in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_integral_domain := false;
     rngl_is_archimedean := false;
     rngl_is_alg_closed :=
       (rngl_has_opp T && rngl_has_inv (GComplex T) &&
        rngl_has_1 (GComplex T))%bool;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := gc_add_comm;
     rngl_add_assoc := gc_add_assoc;
     rngl_add_0_l := gc_add_0_l;
     rngl_mul_assoc := gc_mul_assoc Hop;
     rngl_opt_mul_1_l := gc_opt_mul_1_l Hos;
     rngl_mul_add_distr_l := gc_mul_add_distr_l Hop;
     rngl_opt_mul_comm := gc_opt_mul_comm;
     rngl_opt_mul_1_r := gc_opt_mul_1_r Hos;
     rngl_opt_mul_add_distr_r := gc_opt_mul_add_distr_r Hop;
     rngl_opt_add_opp_diag_l := gc_opt_add_opp_diag_l Hop;
     rngl_opt_add_sub := gc_opt_add_sub Hsu;
     rngl_opt_sub_add_distr := gc_opt_sub_add_distr Hsu;
     rngl_opt_mul_inv_diag_l := gc_opt_mul_inv_diag_l Hop;
     rngl_opt_mul_inv_diag_r := gc_opt_mul_inv_diag_r;
     rngl_opt_mul_div := gc_opt_mul_div;
     rngl_opt_mul_quot_r := gc_opt_mul_quot_r;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := (*gc_opt_alg_closed;*)NA;
(*
     rngl_characteristic_prop := gc_characteristic_prop;
     rngl_opt_le_dec := NA;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat_non_opp := NA;
     rngl_opt_not_le := NA;
*)
     rngl_opt_archimedean := NA |}.
*)
