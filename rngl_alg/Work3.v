(* File created because Work2.v became too big, but
   without any topic found for the moment *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
Import List.ListNotations.

Require Import RingLike.RingLike.
Require Import RingLike.RealLike.
Require Import RingLike.IterAdd.
Require Import RingLike.IterMax.
Require Import RingLike.Misc.

Require Import Trigo.Angle Trigo.TrigoWithoutPiExt.
Require Import Trigo.AngleAddLeMonoL.
Require Import Trigo.AngleAddOverflowLe.
Require Import Trigo.AngleTypeIsComplete.
Require Import Trigo.SeqAngleIsCauchy.
Require Import Trigo.AngleDivNat.

Require Import Misc.
Require Import Complex.
Require Import Work.
Require Import Work2.
Require Import IntermVal.

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
  is_complete T rngl_distance' →
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
  apply (rngl_add_squ_nonneg Hos Hor).
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
specialize (rngl_integral_or_inv_1_quot_eq_dec_order Hon Hiv Hor) as Hio.
apply (rngl_div_nonneg Hon Hop Hiv Hor). {
  apply rl_sqrt_nonneg.
  apply (rngl_add_squ_nonneg Hos Hor).
} {
  apply (rl_sqrt_pos Hon Hos Hor).
  apply (rngl_lt_iff Hor).
  split; [ apply (rngl_add_squ_nonneg Hos Hor) | ].
  intros H1; symmetry in H1.
  cbn in Hz.
  apply (rngl_eq_add_0 Hor) in H1; cycle 1. {
    apply (rngl_squ_nonneg Hos Hor).
  } {
    apply (rngl_squ_nonneg Hos Hor).
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
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ z, (0 ≤ ‖ z ‖)%L.
Proof.
intros Hos Hor *.
progress unfold gc_modl.
progress unfold rl_modl.
apply rl_sqrt_nonneg.
apply (rngl_add_squ_nonneg Hos Hor).
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
intros Hic Hon Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros *.
progress unfold gc_modl.
cbn.
progress unfold rl_modl.
rewrite (rngl_add_comm (gim a * gre b)).
rewrite <- (Brahmagupta_Fibonacci_identity Hic Hon Hop).
apply rl_sqrt_mul; apply (rngl_add_squ_nonneg Hos Hor).
Qed.

Theorem eq_gc_modl_0 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, ‖ a ‖ = 0%L → a = 0%C.
Proof.
intros Hon Hos Hiv Hor.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haz.
apply (eq_rl_sqrt_0 Hon Hos) in Haz. {
  apply (rl_integral_modulus_prop Hos Hor Hii) in Haz.
  now apply eq_gc_eq.
}
apply (rngl_add_squ_nonneg Hos Hor).
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
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haz.
do 2 rewrite <- (rngl_div_1_l Hon Hiv).
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | | easy ]. 2: {
  apply (rngl_0_le_1 Hon Hos Hor).
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
  apply (rl_integral_modulus_prop Hos Hor Hii) in H.
  now apply eq_gc_eq.
}
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite (rngl_squ_opp Hop).
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite <- Hρ.
rewrite (rngl_inv_sqrt Hon Hop Hiv Hor). 2: {
  apply (rngl_lt_iff Hor).
  split; [ subst ρ; apply (rngl_add_squ_nonneg Hos Hor) | easy ].
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
  apply (rl_integral_modulus_prop Hos Hor Hii) in H.
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

(*
Theorem rngl_add_gc_add :
  ∀ a b, (a + b)%L = (a + b)%C.
Proof. easy. Qed.
*)

Theorem rngl_mul_gc_mul :
  ∀ a b, (a * b)%L = (a * b)%C.
Proof. easy. Qed.

Theorem rngl_div_gc_div :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a b, (a / b)%L = (a / b)%C.
Proof.
intros Hic Hiv *.
progress unfold rngl_div.
progress unfold gc_div.
rewrite (rngl_has_inv_gc_has_inv Hic).
rewrite Hiv.
cbn.
f_equal.
apply (rngl_inv_gc_inv Hic Hiv).
Qed.

(*
Theorem gc_eq_div_0_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b,
  (a / b)%C = 0%C
  → b ≠ 0%C
  → a = 0%L.
Proof.
intros Hic Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_integral_or_inv_1_quot_eq_dec_order Hon Hiv Hor) as Hio.
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
*)

Theorem rngl_0_gc_0 : 0%L = 0%C.
Proof. now intros; apply eq_gc_eq. Qed.

Theorem rngl_1_gc_1 : 1%L = 1%C.
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
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a * b = 0 → b ≠ 0 → a = 0)%C.
Proof.
intros Hic Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_integral_or_inv_1_quot_eq_dec_order Hon Hiv Hor) as Hio.
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
  apply (rl_integral_modulus_prop Hos Hor Hii) in H.
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
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a n, a ≠ 0%C → (a ^ n)%C ≠ 0%C.
Proof.
intros Hic Hon Hop Hiv Hor.
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
apply (gc_eq_mul_0_l Hic Hon Hop Hiv Hor) in Hanz; [ | easy ].
now apply Haz, IHn.
Qed.

Theorem rngl_pow_gc_pow : ∀ z n, (z ^ n)%L = (z ^ n)%C.
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

(*
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
*)

(*
Print rngl_opt_integral.
Check is_charac_0_field.
*)

Theorem rngl_has_1_gc_has_1 :
  rngl_has_1 T = true → rngl_has_1 (GComplex T) = true.
Proof.
intros Hon.
progress unfold rngl_has_1.
cbn.
progress unfold rngl_has_1 in Hon.
progress unfold gc_opt_one.
now destruct (rngl_opt_one T).
Qed.

Theorem rngl_has_opp_or_subt_gc_has_opp_or_subt :
  rngl_has_opp_or_subt T = true → rngl_has_opp_or_subt (GComplex T) = true.
Proof.
intros Hos.
progress unfold rngl_has_opp_or_subt.
cbn.
progress unfold rngl_has_opp_or_subt in Hos.
progress unfold gc_opt_opp_or_subt.
destruct (rngl_opt_opp_or_subt T) as [s| ]; [ | easy ].
now destruct s.
Qed.

Definition is_limit_when_tending_to_inf {A} (dist : distance A) f L :=
  ∀ ε, (0 < ε)%L → ∃ R, (0 < R)%L ∧
  ∀ x, (R < x)%L → (d_dist (f x) L < ε)%L.

Definition is_limit_when_module_tending_to_inf {A} (dist : distance A) f L :=
  ∀ ε, (0 < ε)%L → ∃ R, (0 < R)%L ∧
  ∀ z, (R < ‖ z ‖)%L → (d_dist (f (‖ z ‖)) L < ε)%L.

Theorem is_limit_is_limit_module {A} :
  ∀ (dist : distance A) f L,
  is_limit_when_tending_to_inf dist f L
  → is_limit_when_module_tending_to_inf dist f L.
Proof.
intros * Hlim.
intros ε Hε.
destruct (Hlim ε Hε) as (R & HR & Hd).
exists R.
split; [ easy | ].
intros z Hz.
now apply Hd.
Qed.

Theorem rngl_div_sub_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a b c, (b ≠ 0 → (a * b - c) / b = a - c / b)%L.
Proof.
intros Hon Hop Hiv.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
intros * Hbz.
apply (rngl_mul_cancel_r Hi1 _ _ b Hbz).
rewrite (rngl_div_mul Hon Hiv _ _ Hbz).
rewrite (rngl_mul_sub_distr_r Hop).
now rewrite (rngl_div_mul Hon Hiv _ _ Hbz).
Qed.

Theorem rngl_pow_div_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a b n,
  b ≠ 0%L
  → ((a / b) ^ n = a ^ n / b ^ n)%L.
Proof.
intros Hic Hon Hos Hiv * Hbz.
progress unfold rngl_div.
rewrite Hiv.
rewrite (rngl_pow_mul_l Hic Hon).
now rewrite (rngl_inv_pow Hic Hon Hiv Hos _ _ Hbz).
Qed.

Theorem rngl_lt_neq :
  rngl_is_ordered T = true →
  ∀ a b, (a < b)%L → a ≠ b.
Proof.
intros Hor.
intros * Hab.
intros H; subst b.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem rngl_le_inv_inv :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (a⁻¹ ≤ b⁻¹)%L ↔ (b ≤ a)%L.
Proof.
intros Hon Hop Hiv Hor.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haz Hbz.
split; intros Hab. {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor a) in Hab. 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ b) in Hab. 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite (rngl_mul_inv_diag_r Hon Hiv) in Hab. 2: {
    now apply (rngl_lt_neq Hor) in Haz.
  }
  rewrite <- rngl_mul_assoc in Hab.
  rewrite (rngl_mul_inv_diag_l Hon Hiv) in Hab. 2: {
    now apply (rngl_lt_neq Hor) in Hbz.
  }
  rewrite (rngl_mul_1_l Hon) in Hab.
  rewrite (rngl_mul_1_r Hon) in Hab.
  easy.
} {
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ a); [ easy | ].
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ b); [ easy | ].
  rewrite (rngl_mul_inv_diag_r Hon Hiv). 2: {
    now apply (rngl_lt_neq Hor) in Haz.
  }
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_mul_inv_diag_l Hon Hiv). 2: {
    now apply (rngl_lt_neq Hor) in Hbz.
  }
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_1_r Hon).
  easy.
}
Qed.

(* to be completed
Theorem gc_opt_alg_closed :
  if (rngl_has_opp T && rngl_has_inv (GComplex T) &&
      rngl_has_1 (GComplex T))%bool
  then
     ∀ l : list (GComplex T), 1 < length l → List.last l 0%L ≠ 0%L →
     ∃ x : GComplex T, rngl_eval_polyn l x = 0%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
destruct op; [ | easy ].
remember (rngl_has_inv (GComplex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 (GComplex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ cbn | easy ].
intros la Hla Hl1.
(* conseil de Mistral AI *)
Theorem gc_polyn_modl_tends_to_inf_when_modl_var_tends_to_inf :
  rngl_is_archimedean T = true →
  @is_complete T ro T rngl_distance' →
  ∀ (em : excl_midd) (P : list (GComplex T)),
  1 < length P
  → let deg := length P - 1 in
  List.nth deg P 0%L ≠ 0%C
  → ∀ ε, (0 < ε)%L
  → ∃ R, (0 < R)%L ∧
    ∀ z,
    (R < ‖z‖)%L
    → (‖rngl_eval_polyn P z / (P.[deg] * z ^ deg) - 1‖ < ε)%L.
Proof.
destruct_ac.
intros Har Hco.
intros em * H1len * Hz * Hε.
specialize @lower_bound_property as H1.
specialize (H1 _ _ _ em Hop Hor Hon Hiv Har Hco).
set (f := λ z, (‖ (rngl_eval_polyn P z / (P.[deg] * z ^ deg) - 1) ‖)).
set (Im := λ v, ∃ z, v = f z).
specialize (H1 Im 0%L).
specialize (H1 (f 0%L)).
assert (Hqz : Im (f 0%L)) by now exists 0%L.
specialize (H1 Hqz).
assert (H : ∀ x, Im x → (0 ≤ x)%L). {
  intros x Hx.
  progress unfold Im in Hx.
  destruct Hx as (z, Hxz).
  subst x.
  progress unfold f.
  apply (gc_modl_nonneg Hos Hor).
}
specialize (H1 H); clear H.
destruct H1 as (m & Hm & Hzm).
progress unfold is_infimum in Hm.
progress unfold is_extremum in Hm.
destruct (is_bound _ _ _) as [Hqc| Hqc]; [ | easy ].
change (∃ R : T, (0 < R)%L ∧ ∀ z : GComplex T, (R < ‖ z ‖)%L → (f z < ε)%L).
exists m.
split. {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
Theorem gc_polyn_modl_tends_to_inf_when_modl_var_tends_to_inf :
  rngl_is_archimedean T = true →
  @is_complete T ro T (@rngl_distance T ro rp ac_op ac_or) →
  ∀ (em : excl_midd) (P : list (GComplex T)),
  1 < length P
  → let n := length P - 1 in
  List.nth n P 0%L ≠ 0%C
  → let f := λ z, ‖ (rngl_eval_polyn P z / (P.[n] * z ^ n) - 1) ‖ in
    let Im := λ v, ∃ z : GComplex T, v = f z in
    is_infimum Im 0.
Proof.
destruct_ac.
intros Har Hco.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_integral_or_inv_1_quot_eq_dec_order Hon Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros em * H1len * Hz *.
  apply (neq_neq_GComplex Hed) in Hz.
  cbn - [ rngl_zero ] in Hz.
  rewrite (H1 (gre _)), (H1 (gim _)) in Hz.
  now destruct Hz.
}
intros em * H1len * Hz *.
assert (Hzmx : ∀ x, (0 ≤ ‖ x ‖)%L) by apply (gc_modl_nonneg Hos Hor).
specialize @lower_bound_property as H1.
specialize (H1 _ _ _ em Hop Hor Hon Hiv Har Hco).
specialize (H1 Im 0%L).
specialize (H1 (f 0%L)).
assert (Hqz : Im (f 0%L)) by now exists 0%L.
specialize (H1 Hqz).
assert (H : ∀ x, Im x → (0 ≤ x)%L). {
  intros x Hx.
  progress unfold Im in Hx.
  destruct Hx as (z, Hxz).
  subst x.
  progress unfold f.
  apply (gc_modl_nonneg Hos Hor).
}
specialize (H1 H); clear H.
destruct H1 as (m & Hm & Hzm).
destruct (rngl_eq_dec Heo m 0) as [Hmz| Hmz]; [ now subst m | ].
assert (H : (0 < m)%L) by now apply (rngl_lt_iff Hor).
move H before Hzm; clear Hzm Hmz; rename H into Hzm.
exfalso.
progress unfold is_infimum in Hm.
progress unfold is_extremum in Hm.
destruct (is_bound _ _) as [Him| Him]; [ | easy ].
(* pour voir... *)
assert
  (Hnlbe :
     ∀ ε, (0 < ε)%L → bool_of_sumbool (is_lower_bound Im (m + ε)) = false). {
  intros ε Hε.
  progress unfold bool_of_sumbool.
  destruct (is_lower_bound Im (m + ε)) as [Hme| Hme]; [ exfalso | easy ].
  specialize (Hm (m + ε)%L) as H1.
  destruct (is_bound _ _) as [Hbme| Hbme]. {
    apply rngl_nlt_ge in H1.
    now apply H1, (rngl_lt_add_r Hos Hor).
  }
  clear H1.
  destruct Hbme as (x, Hx).
  apply Hx, Hme.
}
assert (H : ∀ c', if is_lower_bound Im c' then (c' ≤ m)%L else True). {
  easy.
}
move H before Hm; clear Hm; rename H into Hm.
set (U := λ z, ∑ (k = 0, n - 1), P.[k] / (P.[n] * z ^ (n - k))).
(*
assert (H :
  ∀ ε, (0 < ε)%L → ∃ R₀, (0 < R₀)%L ∧
  ∀ z, (R₀ < ‖z‖)%L → (‖ U z ‖ < ε)%L). {
*)
assert (H :
  is_limit_when_tending_to_inf rngl_distance'
    (λ x, ∑ (k = 0, n - 1), ‖ P.[k] ‖ / (‖ P.[n] ‖ * x ^ (n - k))) 0%L). {
  intros ε Hε.
  cbn - [ rngl_zero ].
  progress unfold rngl_dist.
  enough (H :
    ∃ R,
    (0 < R)%L
    ∧ ∀ x, (R < x)%L →
       (∑ (k = 0, n - 1), ‖ P.[k] ‖ / (‖ P.[n] ‖ * x ^ (n - k)) < ε)%L). {
    destruct H as (R, H).
    exists R.
    split; [ easy | ].
    intros x Hrx.
    rewrite (rngl_sub_0_r Hos).
    rewrite (rngl_abs_nonneg_eq Hop Hor); [ now apply H | ].
    apply (rngl_summation_nonneg Hor).
    intros i Hi.
    rewrite <- (rngl_div_div Hos Hon Hiv); cycle 1. {
      apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
      intros H'; rewrite H' in Hrx.
      apply (rngl_lt_le_incl Hor) in Hrx.
      now apply rngl_nlt_ge in Hrx.
    } {
      intros H'.
      now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H'.
    }
    apply (rngl_div_nonneg Hon Hop Hiv Hor). {
      apply (rngl_div_nonneg Hon Hop Hiv Hor); [ easy | ].
      apply (rngl_pow_pos_pos Hon Hos Hiv Hc1 Hor).
      now apply (rngl_lt_trans Hor _ R).
    }
    apply (rngl_lt_iff Hor).
    split; [ easy | ].
    intros H'; symmetry in H'.
    now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H'.
  }
  enough (H :
    ∃ R,
    (0 < R)%L
    ∧ ∀ x, (R < x)%L →
       (∑ (k = 0, n - 1), ‖ P.[k] ‖ / x ^ (n - k) < ε * ‖ P.[n] ‖)%L). {
    destruct H as (R, H).
    exists R.
    split; [ easy | ].
    intros x Hrx.
    destruct H as (Hzr, H).
    specialize (H x Hrx).
    apply (rngl_mul_lt_mono_pos_r Hop Hor Hii (‖ P.[n] ‖)%L). {
      apply (rngl_lt_iff Hor).
      split; [ easy | ].
      intros H'; symmetry in H'.
      now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H'.
    }
    eapply (rngl_le_lt_trans Hor); [ | apply H ].
    rewrite <- (rngl_abs_nonneg_eq Hop Hor (‖ P.[n] ‖)); [ | easy ].
    rewrite (rngl_mul_summation_distr_r Hos).
    rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
    apply (rngl_summation_le_compat Hor).
    intros i Hi.
    rewrite <- (rngl_div_div Hos Hon Hiv); cycle 1. {
      apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
      intros H'; rewrite H' in Hrx.
      apply (rngl_lt_le_incl Hor) in Hrx.
      now apply rngl_nlt_ge in Hrx.
    } {
      intros H'.
      now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H'.
    }
    rewrite (rngl_div_mul Hon Hiv). 2: {
      intros H'.
      now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H'.
    }
    apply (rngl_le_refl Hor).
  }
  set (M := Max (k = 0, n - 1), ‖ P.[k] ‖).
  enough (H :
    ∃ R,
    (0 < R)%L
    ∧ ∀ x, (R < x)%L →
       (∑ (k = 0, n - 1), M / x ^ (n - k) < ε * ‖ P.[n] ‖)%L). {
    destruct H as (R, H).
    exists R.
    split; [ easy | ].
    intros x Hrx.
    destruct H as (Hzr, H).
    specialize (H x Hrx).
    eapply (rngl_le_lt_trans Hor); [ | apply H ].
    apply (rngl_summation_le_compat Hor).
    intros i Hi.
    apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii). {
      apply (rngl_pow_pos_pos Hon Hos Hiv Hc1 Hor).
      now apply (rngl_lt_trans Hor _ R).
    }
    progress unfold M.
    apply (rngl_le_max_seq_r Hor) with (f := λ k, ‖ P.[k] ‖). {
      intros k Hk.
      now apply (rngl_max_r_iff Hor).
    }
    rewrite <- Nat_succ_sub_succ_r; [ | flia H1len ].
    do 2 rewrite Nat.sub_0_r.
    apply List.in_seq.
    split; [ easy | ].
    rewrite Nat.add_0_l.
    apply (Nat.le_lt_trans _ (n - 1)); [ easy | ].
    flia H1len.
  }
  destruct (rngl_eq_dec Heo M 0) as [Hmz| Hmz]. {
    subst M; rewrite Hmz.
    exists 1%L.
    split; [ apply (rngl_0_lt_1 Hon Hos Hc1 Hor) | ].
    intros x Hx.
    rewrite all_0_rngl_summation_0. 2: {
      intros i Hi.
      apply (rngl_div_0_l Hos Hi1).
      apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
      intros H; subst x.
      apply rngl_nle_gt in Hx.
      apply Hx.
      apply (rngl_0_le_1 Hon Hos Hor).
    }
    apply (rngl_mul_pos_pos Hos Hor Hii); [ easy | ].
    apply (rngl_lt_iff Hor).
    split ; [ easy | ].
    intros H; symmetry in H.
    now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H.
  }
  assert (HzM : (0 < M)%L). {
    apply (rngl_lt_iff Hor).
    split; [ | easy ].
    progress unfold M.
    now apply (rngl_iter_max_seq_nonneg Hor).
  }
  enough (H :
    ∃ R,
    (0 < R)%L
    ∧ ∀ x, (R < x)%L →
       (∑ (k = 0, n - 1), 1 / x ^ (n - k) < ε * ‖ P.[n] ‖ / M)%L). {
    destruct H as (R, H).
    exists R.
    split; [ easy | ].
    intros x Hrx.
    destruct H as (Hzr, H).
    specialize (H x Hrx).
    apply (rngl_mul_lt_mono_pos_r Hop Hor Hii M) in H; [ | easy ].
    rewrite (rngl_div_mul Hon Hiv) in H; [ | easy ].
    eapply (rngl_le_lt_trans Hor); [ | apply H ].
    rewrite (rngl_mul_summation_distr_r Hos).
    apply (rngl_summation_le_compat Hor).
    intros i Hi.
    rewrite (rngl_div_1_l Hon Hiv).
    rewrite (rngl_mul_comm Hic).
    rewrite (rngl_mul_inv_r Hiv).
    apply (rngl_le_refl Hor).
  }
  enough (H :
    ∃ R,
    (0 < R)%L
    ∧ ∀ x, (R < x)%L →
       (∑ (k = 1, n), 1 / x ^ k < ε * ‖ P.[n] ‖ / M)%L). {
    destruct H as (R, H).
    exists R.
    split; [ easy | ].
    intros x Hrx.
    destruct H as (Hzr, H).
    specialize (H x Hrx).
    rewrite rngl_summation_rtl.
    erewrite rngl_summation_eq_compat. 2: {
      intros i Hi.
      rewrite Nat.add_0_r.
      rewrite Nat.sub_sub_distr; [ | easy | flia Hi ].
      rewrite Nat.sub_sub_distr; [ | flia H1len | easy ].
      rewrite Nat.sub_diag.
      now rewrite Nat.add_0_l.
    }
    cbn - [ rngl_zero Nat.add ].
    rewrite (rngl_summation_shift 1) in H. 2: {
      split; [ easy | flia H1len ].
    }
    now rewrite Nat.sub_diag in H.
  }
  exists (rngl_max 1 (rngl_of_nat n / (ε * ‖ P.[n] ‖ / M))).
  split. {
    apply (rngl_max_lt_iff Hor); left.
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
  }
  intros x Hx.
  assert (Hzx : (0 < x)%L). {
    eapply (rngl_lt_trans Hor); [ | apply Hx ].
    apply (rngl_max_lt_iff Hor); left.
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
  }
  apply (rngl_le_lt_trans Hor _ (∑ (k = 1, n), 1 / x)). {
    apply (rngl_summation_le_compat Hor).
    intros i Hi.
    apply (rngl_div_le_mono_pos_l Hop Hiv Hor Hii). {
      apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
    }
    apply (rngl_le_inv_inv Hon Hop Hiv Hor); [ | easy | ]. {
      now apply (rngl_pow_pos_pos Hon Hos Hiv Hc1 Hor).
    }
    rewrite <- (rngl_pow_1_r Hon x) at 1.
    apply (rngl_pow_le_mono_r Hop Hon Hor); [ | easy ].
    eapply (rngl_le_trans Hor). 2: {
      apply (rngl_lt_le_incl Hor), Hx.
    }
    now apply (rngl_le_max_l Hor).
  }
  rewrite (rngl_summation_const Hos Hon).
  rewrite Nat_sub_succ_1.
  rewrite (rngl_mul_div_assoc Hiv).
  rewrite (rngl_mul_1_r Hon).
  apply (rngl_lt_div_l Hon Hop Hiv Hor _ _ x Hzx).
  rewrite <- (rngl_mul_div_assoc Hiv).
  rewrite (rngl_mul_comm Hic).
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_mul_pos_pos Hos Hor Hii); [ easy | ].
    apply (rngl_div_pos Hon Hop Hiv Hor); [ | easy ].
    apply (rngl_lt_iff Hor).
    split; [ apply (gc_modl_nonneg Hos Hor) | ].
    intros H; symmetry in H.
    now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H.
  }
  rewrite (rngl_mul_div_assoc Hiv).
  eapply (rngl_le_lt_trans Hor); [ | apply Hx ].
  apply (rngl_le_max_r Hor).
}
apply is_limit_is_limit_module in H.
...
  enough (H :
    ∃ R,
    (0 < R)%L
    ∧ ∀ x, (R < x)%L →
      (1 / (x - 1) * (1 - 1 / x ^ n) < ε * ‖ P.[n] ‖ / M)%L). {
    destruct H as (R, H).
    exists (rngl_max 1 R).
    split; [ now apply (rngl_max_lt_iff Hor); right | ].
    intros x Hrx.
    assert (Hzx : x ≠ 0%L). {
      intros H'; subst x.
      apply rngl_nle_gt in Hrx.
      apply Hrx.
      apply (rngl_le_trans Hor _ R).
      now apply (rngl_lt_le_incl Hor).
      apply (rngl_le_max_r Hor).
    }
    destruct H as (Hzr, H).
    specialize (H (x + 1)%L).
    assert (H' : (R < x + 1)%L). {
      apply (rngl_le_lt_trans Hor _ (R + 1)). {
        apply (rngl_le_add_r Hor).
        apply (rngl_0_le_1 Hon Hos Hor).
      }
      apply (rngl_add_lt_mono_r Hop Hor).
      eapply (rngl_le_lt_trans Hor); [ | apply Hrx ].
      apply (rngl_le_max_r Hor).
    }
    specialize (H H'); clear H'.
    rewrite (rngl_add_sub Hos) in H.
    rewrite rngl_summation_rtl.
    erewrite rngl_summation_eq_compat. 2: {
      intros i Hi.
      rewrite Nat.add_0_r.
      rewrite Nat.sub_sub_distr; [ | easy | flia Hi ].
      rewrite Nat.sub_sub_distr; [ | flia H1len | easy ].
      rewrite Nat.sub_diag.
      rewrite Nat.add_0_l, Nat.add_comm.
      rewrite (rngl_pow_add_r Hon).
      rewrite (rngl_pow_1_r Hon).
      rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | ]. 2: {
        now apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
      }
      rewrite <- (rngl_mul_inv_r Hiv).
      rewrite (rngl_inv_pow Hic Hon Hiv Hos); [ | easy ].
      rewrite <- (rngl_div_1_l Hon Hiv).
      easy.
    }
    cbn - [ rngl_zero ].
    rewrite <- (rngl_mul_summation_distr_l Hos).
    rewrite (rngl_summation_power Hic Hon Hop Hiv). 2: {
      intros H'.
      rewrite <- (rngl_div_1_r Hon Hiq Hc1) in H'.
      apply (rngl_div_div_mul_mul Hon Hic Hiv) in H'; [ | easy | ]. 2: {
        now apply (rngl_1_neq_0_iff Hon).
      }
      do 2 rewrite (rngl_mul_1_r Hon) in H'.
      rewrite <- H' in Hrx.
      apply rngl_nle_gt in Hrx.
      apply Hrx; clear Hrx.
      apply (rngl_le_max_l Hor).
    }
    rewrite <- Nat_succ_sub_succ_r; [ | flia H1len ].
    rewrite Nat.sub_0_r.
    rewrite <- (rngl_div_opp_opp Hon Hop Hiv _ (1 / x - 1)). 2: {
      intros H'.
      apply -> (rngl_sub_move_0_r Hop) in H'.
      rewrite (rngl_div_1_l Hon Hiv) in H'.
      rewrite <- (rngl_inv_1 Hon Hiv Hc1) in H'.
      apply (rngl_inv_inj Hon Hos Hiv) in H'; [ | easy | ]. 2: {
        now apply (rngl_1_neq_0_iff Hon).
      }
      rewrite H' in Hrx.
      apply rngl_nle_gt in Hrx.
      apply Hrx; clear Hrx.
      apply (rngl_le_max_l Hor).
    }
    do 2 rewrite (rngl_opp_sub_distr Hop).
    rewrite <- (rngl_div_sub_r Hon Hop Hiv _ _ _ Hzx).
    rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_div_div_r Hon Hos Hiv); [ | | easy ]. 2: {
      intros H'; apply -> (rngl_sub_move_0_r Hop) in H'.
      subst x.
      apply rngl_nle_gt in Hrx.
      apply Hrx; clear Hrx.
      apply (rngl_le_max_l Hor).
    }
    rewrite (rngl_pow_div_l Hic Hon Hos Hiv _ _ _ Hzx).
    rewrite (rngl_pow_1_l Hon).
    rewrite <- rngl_div_sub_r.
    rewrite (rngl_mul_1_l Hon).
...
    rewrite (rngl_mul_comm Hic _ x).
    rewrite (rngl_mul_div_assoc Hiv).
    rewrite rngl_mul_assoc.
    rewrite (rngl_div_1_l Hon Hiv) at 1.
    rewrite (rngl_mul_inv_diag_l Hon Hiv _ Hzx).
    rewrite (rngl_mul_1_l Hon).
...
Search ((_ - _ * _) / _)%L.
rngl_div_sub_distr_r:
  ∀ {T : Type} {ro : ring_like_op T},
    ring_like_prop T
    → rngl_has_opp T = true
      → rngl_has_inv T = true → ∀ a b c : T, ((a - b) / c)%L = (a / c - b / c)%L
Search (_ / _ - _)%L.
Search (_ / (_ / _))%L.
    rewrite (rngl_div_div_r Hon Hos Hiv).
...
    rewrite (rngl_div_1_l Hon Hiv).
    rewrite <- (rngl_inv_pow Hic Hon Hiv Hos).
... ...
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (R & Hr & Hrx).
  exists R.
  split; [ easy | ].
  intros z Hrz.
  progress unfold U.
  eapply (rngl_le_lt_trans Hor). {
    apply (gc_summation_triangular Hic Hon Hop Hiv Hor Hii).
  }
  cbn - [ rngl_add rngl_zero ].
  specialize (Hrx (‖ z ‖)%L Hrz).
  progress unfold d_dist in Hrx.
  cbn - [ rngl_add rngl_zero ] in Hrx.
  progress unfold rngl_dist in Hrx.
  rewrite (rngl_sub_0_r Hos) in Hrx.
  eapply (rngl_le_lt_trans Hor); [ | apply Hrx ].
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_summation_nonneg Hor).
    intros i Hi.
    apply (rngl_div_nonneg Hon Hop Hiv Hor). {
      apply (gc_modl_nonneg Hos Hor).
    }
    apply (rngl_mul_pos_pos Hos Hor Hii). {
      apply (rngl_lt_iff Hor).
      split; [ apply (gc_modl_nonneg Hos Hor) | ].
      intros H; symmetry in H.
      now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H.
    }
    apply (rngl_pow_pos_pos Hon Hos Hiv Hc1 Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply (gc_modl_nonneg Hos Hor) | ].
    intros H; rewrite <- H in Hrz.
    apply (rngl_lt_le_incl Hor) in Hrz.
    now apply rngl_nlt_ge in Hrz.
  }
  apply (rngl_summation_le_compat Hor).
  intros i Hi.
  rewrite (rngl_div_gc_div Hic Hiv).
  rewrite (gc_modl_div Hic Hon Hop Hiv Hor).
  rewrite (gc_modl_mul Hic Hon Hop Hor).
  rewrite rngl_pow_gc_pow. 2: {
    rewrite <- rngl_mul_gc_mul.
    intros H.
    apply (gc_integral Hic Hop Hio) in H.
    destruct H as [H| H]; [ easy | ].
    destruct H as [H| H]. {
      apply (gc_pow_nonzero Hic Hon Hop Hiv Hor) in H; [ easy | ].
      intros H'; rewrite H' in Hrz.
      rewrite (gc_modl_0 Hon Hop Hor Hii) in Hrz.
      apply (rngl_lt_le_incl Hor) in Hrz.
      now apply rngl_nlt_ge in Hrz.
    }
    cbn - [ rngl_zero ] in H.
    destruct H as [H| H]. {
      move Hz at bottom.
      apply (rngl_eq_add_0 Hor) in H; cycle 1. {
        apply (rngl_squ_nonneg Hos Hor).
      } {
        apply (rngl_squ_nonneg Hos Hor).
      }
      destruct H as (H1, H2).
      apply (eq_rngl_squ_0 Hos Hio) in H1, H2.
      apply (neq_neq_GComplex Hed) in Hz.
      now destruct Hz.
    }
    apply (rngl_eq_add_0 Hor) in H; cycle 1. {
      apply (rngl_squ_nonneg Hos Hor).
    } {
      apply (rngl_squ_nonneg Hos Hor).
    }
    destruct H as (H1, H2).
    apply (eq_rngl_squ_0 Hos Hio) in H1, H2.
    assert (H3 : (z ^ (n - i) = 0)%L) by now apply eq_gc_eq.
    set (grp := gc_ring_like_prop_not_alg_closed Hon Hic Hop Hiv Hor).
    apply rngl_pow_nonzero in H3; [ easy | | easy | | | ]. {
      now apply rngl_has_1_gc_has_1.
    } {
      now apply rngl_has_opp_or_subt_gc_has_opp_or_subt.
    } {
      apply Bool.orb_true_iff; right.
      clear - Hic Hon Hiv.
      apply rngl_has_inv_and_1_has_inv_and_1_or_quot.
      now apply rngl_has_1_gc_has_1.
      now rewrite rngl_has_inv_gc_has_inv.
    } {
      intros H; rewrite H in Hrz.
      cbn in Hrz.
      rewrite (gc_modl_0 Hon Hop Hor Hii) in Hrz.
      apply (rngl_lt_le_incl Hor) in Hrz.
      now apply rngl_nlt_ge in Hrz.
    }
  }
  rewrite (gc_modl_pow Hic Hon Hop Hor Hii).
  apply (rngl_le_refl Hor).
}
...
(* pour voir *)
assert (H : ∀ m, (0 < m)%L → ∃ z, z ≠ 0%C ∧ ‖ z ‖ = m). {
  intros a Ha.
  exists (mk_gc a 0).
  split. {
    intros H.
    injection H; clear H; intros H.
    now subst a; apply (rngl_lt_irrefl Hor) in Ha.
  }
  progress unfold gc_modl.
  cbn.
  progress unfold rl_modl.
  rewrite (rngl_squ_0 Hos).
  rewrite rngl_add_0_r.
  rewrite (rl_sqrt_squ Hon Hop Hor).
  apply (rngl_abs_nonneg_eq Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
specialize (H m Hzm).
destruct H as (z & Hmzz & Hmz).
...
assert (H : Im (m / 2)%L). {
  progress unfold Im.
  progress unfold f.
...
specialize (Him _ Hqz) as H1.
progress unfold f in H1.
...
Theorem gc_polyn_modl_tends_to_inf_when_modl_var_tends_to_inf :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ P : list (GComplex T),
  1 < length P
  → ∀ M, (0 < M)%L →
  List.nth (length P - 1) P 0%L ≠ 0%C
  → ∃ R₀, (0 < R₀)%L ∧
    ∀ z : GComplex T, (R₀ < ‖z‖)%L → (M < ‖rngl_eval_polyn P z‖)%L.
Proof.
intros Hon Hic Hop Hiv Hor.
set (rpc := gc_ring_like_prop_not_alg_closed Hon Hic Hop Hiv Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_integral_or_inv_1_quot_eq_dec_order Hon Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hn1 * HM Hz.
  rewrite H1 in HM.
  now apply (rngl_lt_irrefl Hor) in HM.
}
assert (Hosc : rngl_has_opp_or_subt (GComplex T) = true). {
  progress unfold rngl_has_opp_or_subt.
  cbn.
  progress unfold gc_opt_opp_or_subt.
  generalize Hop; intros H.
  progress unfold rngl_has_opp in H.
  destruct (rngl_opt_opp_or_subt T) as [opp| ]; [ | easy ].
  now destruct opp.
}
assert (Honc : rngl_has_1 (GComplex T) = true). {
  progress unfold rngl_has_1.
  cbn.
  progress unfold gc_opt_one.
  generalize Hon; intros H.
  progress unfold rngl_has_1 in H.
  now destruct (rngl_opt_one T).
}
assert (Hivc : rngl_has_inv (GComplex T) = true). {
  progress unfold rngl_has_inv.
  cbn.
  progress unfold gc_opt_inv_or_quot.
  rewrite Hic.
  generalize Hiv; intros H.
  progress unfold rngl_has_inv in H.
  destruct (rngl_opt_inv_or_quot T) as [inv| ]; [ | easy ].
  now destruct inv.
}
assert (Hicc : rngl_mul_is_comm (GComplex T) = true) by easy.
assert (Hi1c : rngl_has_inv_and_1_or_quot (GComplex T) = true). {
  generalize Hi1; intros Hi1'.
  generalize Hiv; intros Hiv'.
  progress unfold rngl_has_inv_and_1_or_quot in Hi1'.
  progress unfold rngl_has_inv in Hiv'.
  progress unfold rngl_has_inv_and_1_or_quot.
  cbn.
  progress unfold gc_opt_inv_or_quot.
  rewrite Hon in Hi1'.
  rewrite Honc, Hic.
  destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
  now destruct iq.
}
assert (Hc1c : rngl_characteristic (GComplex T) ≠ 1) by easy.
intros * H1len * HM Hz.
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
enough (H :
  ∃ R₀ : T,
    (0 < R₀)%L
    ∧ ∀ z : GComplex T, (R₀ < ‖ z ‖)%L →
      (M < ‖ ∑ (i = 0, n), P.[i] * z ^ i ‖)%L). {
  destruct H as (R₀, H).
  exists R₀.
  split; [ easy | ].
  intros z Hrz.
  destruct H as (Hzr, Hms).
  specialize (Hms z Hrz).
  eapply (rngl_lt_le_trans Hor); [ apply Hms | ].
  apply (rngl_eq_le_incl Hor).
  f_equal.
  symmetry.
  rewrite Hn.
  apply (rngl_eval_polyn_is_summation Hosc Honc).
  rewrite rngl_add_0_l.
  apply (rngl_mul_0_l Hosc).
}
remember (Max (i = 0, n - 1), ‖ P.[i] ‖ / ‖ P.[n] ‖)%L as m.
set (R₀ := (1 + M + rngl_of_nat n * m)%L).
subst m.
exists R₀.
assert (Hr : (0 < R₀)%L). {
  progress unfold R₀.
  apply (rngl_lt_le_trans Hor _ 1). {
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
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
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
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
    apply (gc_modl_nonneg Hos Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply (gc_modl_nonneg Hos Hor) | ].
    intros H; symmetry in H.
    now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H.
  }
  apply (rngl_div_nonneg Hon Hop Hiv Hor).
  apply (gc_modl_nonneg Hos Hor).
  apply (rngl_lt_iff Hor).
  split; [ apply (gc_modl_nonneg Hos Hor) | ].
  intros H; symmetry in H.
  now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H.
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
  split; [ apply (gc_modl_nonneg Hos Hor) | ].
  intros H; symmetry in H.
  apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H.
  apply (f_equal (rngl_mul z)) in H.
  cbn in H.
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
    split; [ apply (gc_modl_nonneg Hos Hor) | ].
    intros H; symmetry in H.
    now apply (eq_gc_modl_0 Hon Hos Hiv Hor) in H.
  }
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_le_trans Hor _ R₀); [ | now apply (rngl_lt_le_incl Hor) ].
  progress unfold R₀.
  rewrite <- rngl_add_assoc.
  apply (rngl_le_add_r Hor).
  apply (rngl_add_nonneg_nonneg Hor). {
    now apply (rngl_lt_le_incl Hor) in HM.
  }
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_of_nat_nonneg Hon Hos Hor).
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
  apply (rngl_le_trans Hor _ 1); [ apply (rngl_0_le_1 Hon Hos Hor) | ].
  apply (rngl_le_add_r Hor).
  now apply (rngl_lt_le_incl Hor) in HM.
}
clear H1.
assert (H1 : (rngl_of_nat n * m ≤ ‖ z ‖)%L). {
  eapply (rngl_le_trans Hor); [ | apply H2 ].
(* ah bin non, c'est faux *)
...
(* rien à voir avec le truc courant *)
Check rngl_archimedean.
∀ a b : T, (0 < a)%L → ∃ n : nat, (b < rngl_mul_nat a n)%L
a = π ; b = 3π/2 ;
il faudrait que 3π/2 < nπ
bin non puisque nπ vaut π ou 0
Donc mes angles ne sont pas archimédiens
(* fin du rien à voir avec le truc courant *)
...
  eapply (rngl_le_trans Hor); [ | apply H1 ].
  rewrite <- rngl_mul_assoc.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
  progress unfold R₀.
  apply (rngl_le_add_l Hor).
  apply (rngl_le_trans Hor _ 1); [ apply (rngl_0_le_1 Hon Hop Hor) | ].
  apply (rngl_le_add_r Hor).
  now apply (rngl_lt_le_incl Hor) in HM.
}
...
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
    rewrite <- rngl_pow_gc_pow.
    rewrite <- rngl_0_gc_0.
    now apply (rngl_pow_nonzero Honc Hc1c Hosc Hi1c).
  }
  rewrite rngl_1_gc_1.
  rewrite (gc_modl_1 Hon Hop Hor Hii).
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    apply (rngl_lt_iff Hor).
    split; [ apply (gc_modl_nonneg Hop Hor) | ].
    intros H; symmetry in H.
    apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
    rewrite <- rngl_0_gc_0 in H.
    now apply (rngl_pow_nonzero Honc Hc1c Hosc Hi1c) in H.
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
rewrite (rngl_mul_comm Hic) in H1.
do 3 rewrite <- (gc_modl_mul Hic Hon Hop Hor) in H1.
(**)
do 3 rewrite <- rngl_mul_gc_mul in H1.
rewrite <- rngl_pow_gc_pow in H1.
rewrite <- (rngl_div_gc_div Hic Hiv) in H1.
rewrite <- rngl_1_gc_1 in H1.
rewrite <- rngl_mul_assoc in H1.
rewrite (rngl_mul_summation_distr_r Hosc) in H1.
rewrite <- (rngl_pow_1_r Honc z) in H1 at 3.
rewrite <- (rngl_pow_add_r Honc) in H1.
rewrite Nat.sub_add in H1.
erewrite rngl_summation_eq_compat in H1. 2: {
  intros i (_, Hi).
  rewrite (rngl_mul_mul_swap Hicc).
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_mul_div_assoc Hivc).
  rewrite (rngl_mul_1_r Honc).
  rewrite (rngl_pow_div_pow Hicc Honc Hosc Hivc); [ | easy | flia ].
  rewrite Nat.sub_sub_distr; [ | easy | easy ].
  rewrite Nat.sub_diag.
  rewrite Nat.add_0_l.
  easy.
}
cbn - [ rngl_add rngl_zero ] in H1.
...
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

(* experiment; to be completed if true...
Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem glop :
  rngl_has_opp_or_subt T = true →
  ∀ a b, (a - b = b - a)%L → a = b.
Proof.
(*
intros Hos * Hab.
apply (rngl_sub_compat_l _ _ (b - a))%L in Hab.
rewrite (rngl_sub_diag Hos) in Hab.
rewrite <- (rngl_sub_add_distr Hos) in Hab.
rewrite rngl_add_comm in Hab.
rewrite (rngl_sub_add_distr Hos) in Hab.
...
*)
intros Hos * Hab.
apply (rngl_sub_compat_l _ _ a) in Hab.
rewrite <- (rngl_sub_add_distr Hos) in Hab.
rewrite rngl_add_comm in Hab.
rewrite (rngl_sub_add_distr Hos) in Hab.
rewrite (rngl_sub_diag Hos) in Hab.
symmetry in Hab.
apply (rngl_sub_compat_l _ _ b) in Hab.
rewrite <- (rngl_sub_add_distr Hos) in Hab.
rewrite <- (rngl_sub_add_distr Hos) in Hab.
rewrite rngl_add_assoc in Hab.
rewrite rngl_add_comm in Hab.
rewrite (rngl_sub_add_distr Hos) in Hab.
rewrite (rngl_sub_diag Hos) in Hab.
rewrite <- (rngl_sub_add_distr Hos) in Hab.
...
  Hab : (0 - (a + a))%L = (0 - (b + b))%L
...
intros Hos * Hab.
rewrite <- (rngl_add_sub Hos a a) in Hab at 1.
rewrite <- (rngl_sub_add_distr Hos) in Hab.
rewrite <- (rngl_add_sub Hos b b) in Hab at 2.
rewrite <- (rngl_sub_add_distr Hos) in Hab.
rewrite (rngl_add_comm b a) in Hab.
Search (_ - _ = _ - _)%L.
Check rngl_sub_compat_l.
...
apply (f_equal (λ c, b + c)%L) in Hab.
Search (_ + (_ - _))%L.
...
*)
