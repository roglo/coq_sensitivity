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

(* to be completed
Theorem gc_opt_alg_closed :
  let roc := gc_ring_like_op T in
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
Theorem gc_polyn_modl_tends_to_inf_when_modl_var_tends_to_inf :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  let roc := gc_ring_like_op T in
  ∀ P : list (GComplex T),
  1 < length P
  → ∀ M, (0 < M)%L →
  List.nth (length P - 1) P 0%L ≠ 0%C
  → ∃ R₀, (0 < R₀)%L ∧
    ∀ z : GComplex T, (R₀ < ‖z‖)%L → (M < ‖rngl_eval_polyn P z‖)%L.
Proof.
intros Hon Hic Hop Hiv Hor.
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
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hn1 * HM Hz.
  rewrite H1 in HM.
  now apply (rngl_lt_irrefl Hor) in HM.
}
intros * Hn1 * HM Hz.
(**)
remember (List.length P - 1) as n eqn:Hn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  apply Nat.sub_0_le in Hnz.
  destruct P as [| a]; [ easy | ].
  cbn in Hn1, Hnz.
  now apply Nat.nle_gt in Hn1.
}
apply Nat.neq_0_lt_0 in Hnz.
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
    replace 0%C with 0%L in H by easy.
    now apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
  }
  apply (rngl_div_nonneg Hon Hop Hiv Hor).
  apply (gc_modl_nonneg Hop Hor).
  apply (rngl_lt_iff Hor).
  split; [ apply (gc_modl_nonneg Hop Hor) | ].
  intros H; symmetry in H.
  replace 0%C with 0%L in H by easy.
  now apply (eq_gc_modl_0 Hon Hop Hiv Hor) in H.
}
split; [ easy | ].
intros z Hrz.
remember (Max (i = _, _), _) as m eqn:Hm.
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
  intros H; symmetry in H.
Search (Max (_ = _, _), _ = 0)%L.
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
