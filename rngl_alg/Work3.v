(* File created because Work2.v became too big, but
   without any topic found for the moment *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.Misc Main.RingLike.
Require Import Misc.
Require Import RealLike TrigoWithoutPi TrigoWithoutPiExt.
Require Import Complex.
Require Import Work2.
Require Import AngleAddLeMonoL.
Require Import AngleAddOverflowLe.
Require Import AngleTypeIsComplete.
Require Import SeqAngleIsCauchy.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_lim_eq_compat :
  ∀ a b f g θ,
  (∀ i, f (i + a) = g (i + b))
  → angle_lim f θ
  → angle_lim g θ.
Proof.
intros * Hfg Hf.
eapply is_limit_when_tending_to_inf_eq_compat; [ apply Hfg | easy ].
Qed.

Theorem angle_lim_opp :
  ∀ f θ, angle_lim f θ → angle_lim (λ i, (- f i)%A) (- θ).
Proof.
intros * Hft.
intros ε Hε.
specialize (Hft ε Hε).
destruct Hft as (N, HN).
exists N.
intros n Hn.
rewrite angle_eucl_dist_opp_opp.
now apply HN.
Qed.

Theorem rngl_sin_is_continuous :
  continuous angle_eucl_dist rngl_dist rngl_sin.
Proof.
destruct_ac.
intros a ε Hε.
exists ε.
split; [ easy | ].
intros x Hxa.
progress unfold rngl_dist.
eapply (rngl_le_lt_trans Hor); [ | apply Hxa ].
apply -> (rngl_abs_le Hop Hor).
split. {
  rewrite <- (rngl_opp_sub_distr Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  rewrite angle_eucl_dist_symmetry.
  apply rngl_sin_diff_le_eucl_dist.
} {
  apply rngl_sin_diff_le_eucl_dist.
}
Qed.

Theorem rngl_limit_squ_0_limit_0 :
  rngl_is_ordered T = true →
  rngl_has_opp T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ u,
  is_limit_when_tending_to_inf rngl_dist (λ i : nat, (u i)²%L) 0%L
  → is_limit_when_tending_to_inf rngl_dist u 0%L.
Proof.
intros Hor Hop Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hlim.
intros ε Hε.
specialize (Hlim ε²)%L.
assert (H : (0 < ε²)%L). {
  apply (rngl_lt_iff Hor).
  split; [ apply (rngl_squ_nonneg Hop Hor) | ].
  intros H; symmetry in H.
  apply (eq_rngl_squ_0 Hos) in H. 2: {
    rewrite Bool.orb_true_iff in Hii.
    destruct Hii as [Hii| Hii]; rewrite Hii; [ easy | ].
    rewrite Bool.orb_true_iff; right; cbn.
    apply (rngl_has_eq_dec_or_is_ordered_r Hor).
  }
  subst ε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (Hlim H); clear H.
destruct Hlim as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
progress unfold rngl_dist in HN.
progress unfold rngl_dist.
rewrite (rngl_sub_0_r Hos) in HN |-*.
rewrite (rngl_abs_nonneg_eq Hop Hor) in HN. 2: {
  apply (rngl_squ_nonneg Hop Hor).
}
apply (rngl_squ_lt_abs_lt Hop Hor Hii) in HN.
rewrite (rngl_abs_nonneg_eq Hop Hor ε) in HN; [ easy | ].
now apply (rngl_lt_le_incl Hor) in Hε.
Qed.

Theorem seq_angle_to_div_nat_has_limit :
  rngl_is_archimedean T = true →
  rngl_is_complete T →
  ∀ n θ,
  ∃ θ', angle_lim (seq_angle_to_div_nat θ n) θ'.
Proof.
intros Har Hco *.
specialize (seq_angle_to_div_nat_is_Cauchy Har n θ) as H1.
specialize (rngl_is_complete_angle_is_complete Hco) as Haco.
apply (Haco _ H1).
Qed.

(* if a sequence of angles θi has a limit θ',
   and if ∀ i, n*θi does not overflow,
   then n*θ' does not overflow either *)
Theorem angle_seq_not_overflow_has_not_overflow_limit :
  ∀ n θ θ',
  (∀ i, angle_mul_nat_overflow n (θ i) = false)
  → angle_lim θ θ'
  → (θ' < angle_straight)%A
  → (∀ m, 0 < m ≤ n → (m * θ' ≠ 0)%A)
  → angle_mul_nat_overflow n θ' = false.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  rewrite (H1 θ').
  apply angle_mul_nat_overflow_0_r.
}
intros * Hi Hlim Hts Hnt.
destruct (angle_eq_dec θ' 0) as [Htz| Htz]. {
  subst θ'.
  apply angle_mul_nat_overflow_0_r.
}
apply angle_all_add_not_overflow.
intros * Hmn.
assert (H : ∀ k, angle_lim (λ i, (k * θ i)%A) (k * θ')). {
  intros k.
  now apply angle_lim_mul.
}
move H before Hlim; clear Hlim; rename H into Hlim.
assert (H :
  ∀ m ε,
  (0 < ε)%L
  → ∃ N : nat, ∀ i, N ≤ i → (angle_eucl_dist (m * θ i) (m * θ') < ε)%L)
by apply Hlim.
move H before Hlim; clear Hlim; rename H into Hlim.
progress unfold angle_add_overflow.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite angle_add_mul_r_diag_r.
assert (H : ∀ i m, m < n → (θ i ≤ S m * θ i)%A). {
  clear m Hmn.
  intros * Hmn.
  specialize (Hi i).
  specialize (proj2 (angle_all_add_not_overflow _ _) Hi m Hmn) as H.
  progress unfold angle_add_overflow in H.
  apply Bool.not_true_iff_false in H.
  apply angle_nlt_ge in H.
  now rewrite angle_add_mul_r_diag_r in H.
}
move H before Hi; clear Hi; rename H into Hi.
assert (H : ∀ i m, 0 < m ≤ n → (θ i ≤ m * θ i)%A). {
  clear m Hmn.
  intros * (Hmz, Hmn).
  specialize (Hi i (m - 1)).
  rewrite <- Nat_succ_sub_succ_r in Hi; [ | easy ].
  rewrite Nat.sub_0_r in Hi.
  apply Hi.
  flia Hmz Hmn.
}
move H before Hi; clear Hi; rename H into Hni.
progress unfold lt in Hmn.
remember (S m) as p.
assert (H : 0 < p ≤ n) by flia Heqp Hmn.
clear m Heqp.
clear Hmn; rename H into Hmn; rename p into m.
move m before n.
assert (Hlim' :
  ∀ m ε,
  (0 < ε)%L
  → ∃ N : nat, ∀ i, N ≤ i → (angle_eucl_dist (m * (θ i - θ')) 0 < ε)%L). {
  intros p ε Hε.
  specialize (Hlim p ε Hε).
  destruct Hlim as (N, HN).
  exists N; intros j Hj.
  specialize (HN j Hj).
  rewrite angle_eucl_dist_move_0_r in HN.
  now rewrite <- angle_mul_sub_distr_l in HN.
}
generalize Hts; intros Hts_v.
apply angle_nlt_ge.
intros Hmt.
specialize (Hnt _ Hmn) as Hmtz.
set (ε1 := angle_eucl_dist (m * θ') 0).
set (ε2 := angle_eucl_dist (m * θ') θ').
set (ε3 := angle_eucl_dist θ' (m * θ' + angle_straight)).
specialize (Hlim 1 (rngl_min3 ε1 (ε2 / 2) ε3)%L) as H1.
specialize (Hlim m (rngl_min3 ε1 (ε2 / 2) ε3)%L) as H2.
assert (Hε : (0 < rngl_min3 ε1 (ε2 / 2) ε3)%L). {
  apply rngl_min_glb_lt. {
    apply rngl_min_glb_lt. {
      progress unfold ε1.
      apply (rngl_lt_iff Hor).
      split; [ apply angle_eucl_dist_nonneg | ].
      apply not_eq_sym.
      intros H.
      now apply angle_eucl_dist_separation in H.
    }
    progress unfold ε2.
    apply (rngl_div_lt_pos Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    apply (rngl_lt_iff Hor).
    split; [ apply angle_eucl_dist_nonneg | ].
    apply not_eq_sym.
    intros H.
    apply angle_eucl_dist_separation in H.
    rewrite H in Hmt.
    now apply angle_lt_irrefl in Hmt.
  }
  progress unfold ε3.
  apply (rngl_lt_iff Hor).
  split; [ apply angle_eucl_dist_nonneg | ].
  apply not_eq_sym.
  intros H.
  apply angle_eucl_dist_separation in H.
  apply angle_nle_gt in Hts.
  apply Hts; clear Hts.
  rewrite H.
  (* lemma to do *)
  rewrite angle_add_comm.
  apply angle_le_add_r.
  apply (angle_add_overflow_le_lt angle_straight).
  apply angle_le_refl.
  rewrite angle_opp_straight.
  now apply (angle_lt_trans _ θ').
}
clear Hts_v.
specialize (H1 Hε).
specialize (H2 Hε).
destruct H1 as (N1, HN1).
destruct H2 as (N2, HN2).
set (i := max N1 N2).
specialize (HN1 i (Nat.le_max_l _ _)).
specialize (HN2 i (Nat.le_max_r _ _)).
do 2 rewrite angle_mul_1_l in HN1.
specialize angle_eucl_dist_lt_angle_lt_le_lt as H1.
specialize (H1 (m * θ') (m * θ i) (θ i) θ')%A.
specialize (H1 _ _ _ eq_refl eq_refl eq_refl).
progress fold ε1 in H1.
progress fold ε2 in H1.
progress fold ε3 in H1.
generalize Hts; intros H.
apply angle_lt_le_incl in H.
specialize (H1 HN1 HN2 (conj Hmt H)); clear H.
apply angle_nle_gt in H1.
now apply H1, Hni.
Qed.

(* to be completed
(* borrowed from Complex.v *)
(* if working => replace this version in Complex.v since
   the version in Complex.v is a special case of this when
   n = 1 *)
Theorem rngl_cos_angle_div_2_pow_tending_to_1 :
  rngl_characteristic T ≠ 1 →
  rngl_is_archimedean T = true →
  ∀ n θ, rngl_is_limit_when_tending_to_inf (λ i, rngl_cos (n * (θ /₂^i))) 1%L.
Proof.
intros Hc1 Har.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros.
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ m, N ≤ m → (1 - rngl_cos (n * (θ /₂^m)) < ε)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros m Hm.
  specialize (HN m Hm).
  progress unfold rngl_dist.
  rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
    apply (rngl_le_sub_0 Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_opp_sub_distr Hop).
  easy.
}
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ m, N ≤ m →
    (1 - ε < rngl_cos_div_pow_2 (θ /₂) m)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists (S N).
  intros m Hm.
  destruct m; [ easy | ].
  apply Nat.succ_le_mono in Hm.
  specialize (HN m Hm).
Check rngl_cos_div_pow_2_eq.
Print rngl_cos_div_pow_2.
...
  rewrite rngl_cos_div_pow_2_eq.
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  easy.
}
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n →
    (1 - ε < squ_rngl_cos_div_pow_2 (θ /₂) n)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros n Hn.
  eapply (rngl_lt_le_trans Hor). 2: {
    apply rngl_cos_div_pow_2_lower_bound.
  }
  now apply HN.
}
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n →
    ((1 - rngl_cos (θ /₂)) / 2 ^ n < ε)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros n Hn.
  remember (θ /₂)%A as θ' eqn:Hθ.
  specialize (HN n Hn).
  clear N Hn.
  revert ε Hε HN.
  induction n; intros. {
    cbn in HN |-*.
    rewrite (rngl_div_1_r Hon Hiq Hc1) in HN.
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    apply (rngl_lt_sub_lt_add_r Hop Hor).
    easy.
  }
  cbn.
  apply (rngl_lt_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rngl_add_sub_assoc Hop).
  apply (rngl_add_lt_mono_l Hop Hor).
  apply IHn. {
    rewrite rngl_mul_add_distr_l.
    rewrite (rngl_mul_1_r Hon).
    apply (rngl_lt_trans Hor _ ε); [ easy | ].
    now apply (rngl_lt_add_l Hos Hor).
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_div_div Hos Hon Hiv); cycle 1. {
    apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  } {
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  }
  cbn in HN.
  now destruct n.
}
intros ε Hε.
remember ((1 - rngl_cos (θ /₂)))%L as a eqn:Ha.
specialize (int_part Hon Hop Hc1 Hor Har) as H1.
specialize (H1 (a / ε))%L.
destruct H1 as (N, HN).
exists (Nat.log2 N + 1).
intros n Hn.
apply (rngl_lt_div_l Hon Hop Hiv Hor). {
  apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite (rngl_mul_comm Hic).
apply (rngl_lt_div_l Hon Hop Hiv Hor); [ easy | ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor (_ / _))%L. 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
  rewrite (rngl_mul_0_l Hos).
  rewrite Ha.
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
eapply (rngl_lt_le_trans Hor); [ apply HN | ].
apply (Nat.pow_le_mono_r 2) in Hn; [ | easy ].
apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor) in Hn.
do 2 rewrite (rngl_of_nat_pow Hon Hos) in Hn.
cbn in Hn.
rewrite rngl_add_0_r in Hn.
eapply (rngl_le_trans Hor); [ | apply Hn ].
replace 2%L with (rngl_of_nat 2). 2: {
  cbn.
  now rewrite rngl_add_0_r.
}
rewrite <- (rngl_of_nat_pow Hon Hos).
apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
rewrite Nat.add_1_r.
apply Nat.le_succ_l.
clear HN Hn.
rewrite Nat.add_1_r.
cbn.
rewrite Nat.add_0_r.
induction N; [ easy | ].
specialize (Nat.log2_succ_or N) as H1.
destruct H1 as [H1| H1]. {
  rewrite H1.
  cbn.
  rewrite Nat.add_0_r.
  apply Nat.succ_lt_mono in IHN.
  eapply Nat.lt_le_trans; [ apply IHN | ].
  rewrite <- Nat.add_1_r.
  apply Nat.add_le_mono_l.
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.eq_add_0 in H.
  destruct H as (H, _).
  revert H.
  now apply Nat.pow_nonzero.
}
apply Nat.le_neq.
split; [ now rewrite H1 | ].
intros H2.
rewrite H1 in H2.
rewrite Nat_add_diag in H2.
rewrite <- Nat.pow_succ_r in H2; [ | easy ].
specialize (Nat.log2_spec (S N)) as H3.
specialize (H3 (Nat.lt_0_succ _)).
rewrite H1 in H3.
rewrite <- H2 in H3.
destruct H3 as (H3, H4).
now apply Nat.lt_irrefl in H4.
Qed.
*)

Definition angle_div_nat θ n θ' :=
  angle_lim (seq_angle_to_div_nat θ n) θ'.

(* to be completed
Theorem angle_div_nat_spec :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  rngl_is_complete T →
  ∀ θ n θ',
  angle_div_nat θ n θ'
  → (n = 0 ∧ θ' = 0%A) ∨ (n * θ')%A = θ.
Proof.
destruct_ac.
intros Hcz Har Hco.
intros * Hdn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  left; split; [ easy | subst n ].
  progress unfold angle_div_nat in Hdn.
  progress unfold seq_angle_to_div_nat in Hdn.
  cbn in Hdn.
  now apply angle_lim_const in Hdn.
}
right.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n; rewrite angle_mul_1_l.
  progress unfold angle_div_nat in Hdn.
  progress unfold seq_angle_to_div_nat in Hdn.
  eapply (angle_lim_eq_compat 0 0) in Hdn. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite Nat.div_1_r.
    rewrite angle_div_2_pow_mul_2_pow.
    easy.
  }
  now apply angle_lim_const in Hdn.
}
progress unfold angle_div_nat in Hdn.
rename Hdn into Hlim.
specialize (angle_lim_mul n _ _ Hlim) as H1.
enough (H2 : angle_lim (λ i, (n * seq_angle_to_div_nat θ n i)%A) θ). {
  apply (limit_unique Hon Hop Hiv Hor) with (lim1 := (n * θ')%A) in H2. {
    easy.
  } {
    apply angle_eucl_dist_is_dist.
  } {
    easy.
  }
}
clear θ' Hlim H1.
destruct (angle_eq_dec θ 0) as [Htz| Htz]. {
  subst θ.
  eapply (angle_lim_eq_compat 0 0). {
    intros i.
    rewrite Nat.add_0_r; symmetry.
    progress unfold seq_angle_to_div_nat.
    rewrite angle_0_div_2_pow.
    do 2 rewrite angle_mul_0_r.
    easy.
  }
  intros ε Hε.
  exists 0.
  intros m _.
  now rewrite angle_eucl_dist_diag.
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H2.
  intros ε Hε.
  rewrite (H2 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
move Hc1 before Hcz.
move Hii before Hco.
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
  progress unfold seq_angle_to_div_nat.
  rewrite angle_mul_nat_assoc.
  specialize (Nat.div_mod (2 ^ i) n Hnz) as H1.
  symmetry in H1.
  apply Nat.add_sub_eq_r in H1.
  rewrite <- H1.
  rewrite angle_mul_sub_distr_r; [ | now apply Nat.Div0.mod_le ].
  rewrite angle_div_2_pow_mul_2_pow.
  easy.
}
(**)
apply angle_lim_move_0_r.
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
  rewrite angle_sub_sub_swap.
  rewrite angle_sub_diag.
  rewrite angle_sub_0_l.
  easy.
}
rewrite <- angle_opp_0.
apply angle_lim_opp.
enough (H : angle_lim (λ i, (n * (θ /₂^i))%A) 0). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists (Nat.max N (Nat.log2_up (2 * n))).
  intros m Hm.
  specialize (HN m).
  assert (H : N ≤ m). {
    eapply Nat.le_trans; [ | apply Hm ].
    apply Nat.le_max_l.
  }
  specialize (HN H); clear H.
  eapply (rngl_le_lt_trans Hor); [ | apply HN ].
  assert (Hnm : Nat.log2_up (2 * n) ≤ m). {
    eapply Nat.le_trans; [ | apply Hm ].
    apply Nat.le_max_r.
  }
  apply (Nat.pow_le_mono_r 2) in Hnm; [ | easy ].
  apply angle_le_angle_eucl_dist_le. {
    eapply angle_le_trans. {
      apply angle_mul_le_mono_r. 2: {
        apply Nat.lt_le_incl.
        apply Nat.mod_upper_bound.
        apply Hnz.
      }
      apply angle_mul_nat_overflow_div_pow2.
      eapply Nat.le_trans; [ | apply Hnm ].
      apply (Nat.le_trans _ (2 * n)). {
        flia Hnz Hn1.
      }
      apply Nat.log2_log2_up_spec.
      apply Nat.neq_0_lt_0.
      flia Hnz Hn1.
    }
    apply angle_mul_div_pow2_le_straight.
    eapply Nat.le_trans; [ | apply Hnm ].
    apply Nat.log2_log2_up_spec.
    apply Nat.neq_0_lt_0.
    flia Hnz Hn1.
  } {
    apply angle_mul_div_pow2_le_straight.
    eapply Nat.le_trans; [ | apply Hnm ].
    apply Nat.log2_log2_up_spec.
    apply Nat.neq_0_lt_0.
    flia Hnz Hn1.
  }
  apply angle_mul_le_mono_r. 2: {
    apply Nat.lt_le_incl.
    now apply Nat.mod_upper_bound.
  }
  apply angle_mul_nat_overflow_div_pow2.
  eapply Nat.le_trans; [ | apply Hnm ].
  apply (Nat.le_trans _ (2 * n)). {
    flia Hnz Hn1.
  }
  apply Nat.log2_log2_up_spec.
  apply Nat.neq_0_lt_0.
  flia Hnz Hn1.
}
intros ε Hε.
enough (H :
  ∃ N, ∀ m, N ≤ m →  (1 - ε² / 2 < rngl_cos (n * (θ /₂^m)))%L). {
  destruct H as (N, HN).
  exists N.
  intros m Hm.
  specialize (HN m Hm).
  apply rngl_cos_lt_angle_eucl_dist_lt. {
    now apply (rngl_lt_le_incl Hor) in Hε.
  }
  now rewrite angle_sub_0_l.
}
About rngl_cos_angle_div_2_pow_tending_to_1.
Search rngl_is_limit_when_tending_to_inf.
Check rngl_cos_angle_mul_div_2_pow_tending_to_1.
...
specialize rngl_cos_angle_mul_div_2_pow_tending_to_1 as H1.
specialize (H1 Hc1 Har n θ).
progress unfold rngl_is_limit_when_tending_to_inf in H1.
progress unfold is_limit_when_tending_to_inf in H1.
progress unfold rngl_dist in H1.
specialize (H1 (ε² / 2))%L.
assert (Hε2 : (0 < ε² / 2)%L). {
  apply (rngl_div_lt_pos Hon Hop Hiv Hor). 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  apply (rngl_lt_iff Hor).
  split; [ apply (rngl_squ_nonneg Hop Hor) | ].
  apply not_eq_sym.
  intros H.
  apply (eq_rngl_squ_0 Hos) in H. 2: {
    rewrite Bool.orb_true_iff in Hii.
    destruct Hii as [Hii| Hii]; rewrite Hii; [ easy | ].
    rewrite Bool.orb_true_iff; right; cbn.
    apply (rngl_has_eq_dec_or_is_ordered_r Hor).
  }
  now subst ε; apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (H1 Hε2); clear Hε2.
destruct H1 as (N, HN).
exists N.
intros p Hp.
specialize (HN p Hp).
rewrite (rngl_abs_sub_comm Hop Hor) in HN.
rewrite (rngl_abs_nonneg_eq Hop Hor) in HN. 2: {
  apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
}
apply (rngl_lt_sub_lt_add_r Hop Hor) in HN.
apply (rngl_lt_sub_lt_add_l Hop Hor) in HN.
easy.
...
eapply (rngl_lt_le_trans Hor); [ apply HN | ].
...
Search (√(_ * (_ - _)))%L.
Search (√(_ * _))%L.
...
specialize (int_part Hon Hop Hc1 Hor Har) as H2.
specialize (H2 (rngl_of_nat n / rngl_min 1 ε))%L.
destruct H2 as (en, Hen).
move en before n.
rewrite (rngl_abs_nonneg_eq Hop Hor) in Hen. 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
    apply rngl_min_glb_lt; [ | easy ].
    apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  }
  apply (rngl_of_nat_nonneg Hon Hop Hor).
}
exists (Nat.log2_up en).
intros m Hm.
destruct Hen as (Hen, Hne).
apply (rngl_lt_div_l Hon Hop Hiv Hor) in Hne. 2: {
  apply rngl_min_glb_lt; [ | easy ].
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
rewrite <- (rngl_mul_min_distr_l Hop Hor Hii) in Hne. 2: {
  apply (rngl_of_nat_nonneg Hon Hop Hor).
}
rewrite (rngl_mul_1_r Hon) in Hne.
apply (rngl_min_glb_lt_iff Hor) in Hne.
destruct Hne as (Hne, Hnee).
apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor) in Hne.
rewrite Nat.add_1_r in Hne.
apply -> Nat.lt_succ_r in Hne.
apply (rngl_lt_div_l Hon Hop Hiv Hor) in Hnee; [ | easy ].
eapply (rngl_le_lt_trans Hor). {
  apply angle_eucl_dist_mul_le.
}
apply (rngl_lt_div_r Hon Hop Hiv Hor). {
  apply (rngl_lt_iff Hor).
  split; [ apply angle_eucl_dist_nonneg | ].
  intros H; symmetry in H.
  apply angle_eucl_dist_separation in H.
  now apply eq_angle_div_2_pow_0 in H.
}
apply (rngl_lt_div_r Hon Hop Hiv Hor).
...
Search (Nat.log2_up _ = 0).
Search (_ ^ _ = 0).
Search (_ → _ < _ * _).
apply Nat.
Search (
...
Search (_ * _ ≤ angle_straight)%A.
...
      specialize (Nat.le_max_r N (Nat.log2_up n)) as H1.
...
Search (angle_mul_nat_overflow _ (_ /₂^ _) = false).
...
apply angle_mul_le_mono_r.

Search (angle_eucl_dist _ _ ≤ angle_eucl_dist _ _)%L.
  apply rngl_cos_le_iff_angle_eucl_le.
...
eapply Work.angle_lim_0_le_if.
  intros i.
  split. {
...
    apply angle_mul_le_mono_r. 2: {
        apply Nat.lt_le_incl.
        apply Nat.mod_upper_bound.
        apply Hnz.
      }
...
apply (angle_lim_eq_compat 0 n) with (f := λ i, (n * (θ /₂^ i))%A). {
  intros i.
  rewrite Nat.add_0_r.
...
destruct (angle_le_dec θ angle_straight) as [Hts| Hts]. {
  eapply Work.angle_lim_0_le_if. {
    intros i.
    split. {
      apply angle_mul_le_mono_r. 2: {
        apply Nat.lt_le_incl.
        apply Nat.mod_upper_bound.
        apply Hnz.
      }
n ≤ 2 ^ i
...
Search (angle_lim _ 0).
...
  apply (angle_lim_eq_compat 0 n) with (f := λ i, (n * (θ /₂^ i))%A). {
    intros i.
    rewrite Nat.add_0_r.
...
  eapply Work.angle_lim_0_le_if. {
    intros i.
    split. {
      apply angle_mul_le_mono_r. 2: {
        apply Nat.lt_le_incl.
        apply Nat.mod_upper_bound.
        apply Hnz.
      }
...
  eapply (angle_lim_eq_compat 0 n). {
    intros i.
    rewrite Nat.add_0_r; symmetry.
    easy
...
  eapply Work.angle_lim_0_le_if. {
    intros i.
    split. {
      apply angle_mul_le_mono_r. 2: {
        apply Nat.lt_le_incl.
        now apply Nat.mod_upper_bound.
      }
...
  eapply (angle_lim_eq_compat 0 n). {
    intros i.
    rewrite Nat.add_0_r; symmetry.
(* ah, puis zut. Bon, j'y arriverai peut-être tout à l'heure *)
...
  eapply Work.angle_lim_0_le_if. {
    intros i.
    split. {
      apply angle_mul_le_mono_r. 2: {
        apply Nat.lt_le_incl.
        now apply Nat.mod_upper_bound.
      }
...
      apply angle_mul_le_mono_r; [ | apply Nat.Div0.mod_le ].
      apply angle_mul_nat_overflow_pow_div.
    }
    cbn.
    now rewrite angle_div_2_pow_mul_2_pow.
  }
...
Search (angle_lim _ 0 → angle_lim _ _).
...
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
  rewrite <- (angle_div_2_pow_mul_2_pow i θ) at 1.
  rewrite <- angle_mul_sub_distr_r. 2: {
    apply Nat.Div0.mul_div_le.
  }
  easy.
}
...
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
...
intros ε Hε.
specialize (int_part Hon Hop Hc1 Hor Har) as H2.
specialize (H2 (rngl_of_nat (2 * n) / rngl_min 1 ε))%L.
destruct H2 as (en, Hen).
move en before n.
rewrite (rngl_abs_nonneg_eq Hop Hor) in Hen. 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
    apply rngl_min_glb_lt; [ | easy ].
    apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  }
  apply (rngl_of_nat_nonneg Hon Hop Hor).
}
exists (Nat.log2_up en).
intros m Hm.
rewrite <- (angle_div_2_pow_mul_2_pow m θ) at 2.
rewrite angle_eucl_dist_symmetry.
rewrite angle_eucl_dist_move_0_r.
rewrite <- angle_mul_sub_distr_r; [ | apply Nat.Div0.mul_div_le ].
specialize (Nat.div_mod (2 ^ m) n Hnz) as H2.
symmetry in H2.
apply Nat.add_sub_eq_l in H2.
rewrite H2; clear H2.
rewrite angle_eucl_dist_symmetry.
destruct Hen as (Hen, Hne).
apply (rngl_lt_div_l Hon Hop Hiv Hor) in Hne. 2: {
  apply rngl_min_glb_lt; [ | easy ].
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
rewrite <- (rngl_mul_min_distr_l Hop Hor Hii) in Hne. 2: {
  apply (rngl_of_nat_nonneg Hon Hop Hor).
}
rewrite (rngl_mul_1_r Hon) in Hne.
apply (rngl_min_glb_lt_iff Hor) in Hne.
destruct Hne as (Hne, Hnee).
apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor) in Hne.
rewrite Nat.add_1_r in Hne.
apply -> Nat.lt_succ_r in Hne.
rewrite (rngl_of_nat_mul Hon Hos) in Hnee.
rewrite rngl_of_nat_2 in Hnee.
apply (rngl_lt_div_r Hon Hop Hiv Hor) in Hnee. 2: {
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  now apply Nat.neq_0_lt_0.
}
rewrite <- (rngl_mul_div_assoc Hiv) in Hnee.
rewrite (rngl_mul_comm Hic) in Hnee.
apply (rngl_lt_div_l Hon Hop Hiv Hor) in Hnee. 2: {
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  now rewrite Nat.add_1_r.
}
destruct (le_dec en 3) as [Hen3| Hen3]. {
  exfalso; apply Nat.nlt_ge in Hen3.
  apply Hen3; clear Hen3.
  apply (Nat.lt_le_trans _ (2 * n)); [ | easy ].
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  rewrite Nat.mul_comm; cbn.
  now do 3 apply -> Nat.succ_lt_mono.
}
apply Nat.nle_gt in Hen3.
assert (Hnm : 2 * n ≤ 2 ^ m). {
  apply (Nat.le_trans _ en); [ easy | ].
  apply (Nat.pow_le_mono_r 2) in Hm; [ | easy ].
  apply (Nat.le_trans _ (2 ^ Nat.log2_up en)); [ | easy ].
  apply Nat.log2_log2_up_spec.
  now destruct en.
}
apply (rngl_le_lt_trans Hor _ (angle_eucl_dist 0 (n * (θ /₂^ m)))). {
  apply angle_eucl_dist_le_cos_le.
  do 2 rewrite angle_sub_0_r.
  apply rngl_cos_decr.
  split. {
    apply angle_mul_le_mono_r. 2: {
      apply Nat.lt_le_incl.
      apply (Nat.mod_upper_bound _ _ Hnz).
    }
    apply angle_mul_nat_overflow_div_pow2.
    eapply Nat.le_trans. 2: {
      apply (Nat.pow_le_mono_r 2) in Hm; [ apply Hm | easy ].
    }
    apply (Nat.le_trans _ en). 2: {
      apply Nat.log2_up_spec.
      apply (Nat.le_trans _ 4); [ | easy ].
      now do 2 apply -> Nat.succ_le_mono.
    }
    apply (Nat.le_trans _ (2 * n)); [ | apply Hne ].
    now apply Nat.le_mul_l.
  }
  apply angle_mul_div_pow2_le_straight.
  apply (Nat.le_trans _ (2 ^ Nat.log2_up en)). 2: {
    now apply Nat.pow_le_mono.
  }
  eapply (Nat.le_trans _ en); [ easy | ].
  apply Nat.log2_log2_up_spec.
  now destruct en.
}
rewrite angle_eucl_dist_symmetry.
eapply (rngl_le_lt_trans Hor); [ apply angle_eucl_dist_mul_le | ].
rewrite (rngl_mul_comm Hic).
apply (rngl_lt_div_r Hon Hop Hiv Hor). {
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  now apply Nat.neq_0_lt_0.
}
eapply (rngl_le_lt_trans Hor); [ | now apply Hnee ].
eapply (rngl_le_trans Hor). {
  apply angle_eucl_dist_le_twice_twice_div_2_div_2.
}
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_le_mono_pos_l Hop Hor Hii). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite angle_0_div_2.
rewrite <- (rngl_div_1_l Hon Hiv).
...
apply (rngl_lt_le_incl Hor).
eapply (angle_eucl_dist_div_2_0_lt (ε / rngl_of_nat n))%L. {
  apply (rngl_lt_le_incl Hor).
  apply (rngl_lt_div_r Hon Hop Hiv Hor). 2: {
    rewrite (rngl_mul_0_l Hos).
    apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  }
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  now rewrite Nat.add_1_r.
}
2: {
  apply rngl_sin_div_2_pow_nat_nonneg.
  intros H; subst m.
  cbn in Hnm.
  flia Hnz Hn1 Hnm.
}
{
  rewrite (rngl_squ_sub Hop Hic Hon).
  rewrite (rngl_squ_1 Hon).
  rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_mul_comm Hic 2).
  rewrite (rngl_div_mul Hon Hiv). 2: {
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  }
  rewrite rngl_add_assoc.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_add_comm _ 1).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- rngl_add_assoc.
  rewrite <- (rngl_sub_sub_distr Hop).
  remember (1 / rngl_of_nat (en + 1))²%L as x.
  apply (rngl_le_sub_nonneg Hop Hor).
  rewrite (rngl_sub_add_distr Hos).
  rewrite (rngl_sub_sub_swap Hop).
  apply (rngl_le_0_sub Hop Hor).
(* mouais, chais pas *)
...
2: {
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite - rngl_add
2: {
...

rewrite <- angle_div_2_pow_succ_r_1.
rewrite angle_div_2_pow_succ_r_2.
Search (_ * angle_eucl_dist _ _)%L.
...
apply (rngl_lt_le_incl Hor).
apply rngl_cos_lt_angle_eucl_dist_lt. {
  apply (rngl_lt_le_incl Hor).
  apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  now rewrite Nat.add_1_r.
}
rewrite angle_sub_0_l; cbn - [ angle_div_2_pow ].
...
Search (_ - _ < rngl_cos _)%L.
Search (_ < rngl_cos (_ /₂^ _))%L.
Search (1 - _ < rngl_cos _)%L.
...
Search (angle_eucl_dist _ _ < _)%L.
...
Check angle_eucl_dist_div_2_pow_0_lt.
...
Search ( * _ < _)%L.
Search (_ < _ / _)%L.

Search (angle_eucl_dist (_ * _) _ < _)%L.
Search (angle_eucl_dist (_ * _) _)%L.
angle_eucl_dist_mul_le:
  ∀ {T : Type} {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T},
    angle_ctx T
    → ∀ (n : nat) (θ : angle T), (angle_eucl_dist (n * θ) 0 ≤ rngl_of_nat n * angle_eucl_dist θ 0)%L
Search (angle_eucl_dist (_ /₂^ _) _ < _)%L.
About angle_eucl_dist_div_2_pow_0_lt.
...
(*
 en = 2n/ε
 2n= en*ε
 n = en*ε/2
 en ≤ 2^m
 2n/ε ≤ 2^m
 2n ≤ 2^m * ε ≤ 2^m
*)
...
apply rngl_cos_lt_angle_eucl_dist_lt. {
  now apply (rngl_lt_le_incl Hor) in Hε.
}
rewrite angle_sub_0_l.
cbn.
Search (_ - _ < rngl_cos _)%L.
...
Search (_ → angle_eucl_dist _ _ < _)%L.
Search (_ → angle_eucl_dist _ _ < _)%L.
Check angle_eucl_dist_div_2_pow_0_lt.
...
(*
en = n/ε
n = ε.en

2 ^ en ≤ 2 ^ (n/ε) < 2 ^ (en + 1)
en ≤ n/ε
*)
Search (_ ^ _ ≤ _ ^ _).
Search (_ → angle_mul_nat_overflow _ (_ /₂^ _) = false).
...
Search (rngl_cos _ < rngl_cos _)%L.
apply AngleEuclDistLtAngleLtLt.quadrant_1_sin_sub_nonneg_cos_lt.
...
Search (angle_eucl_dist _ _ = angle_eucl_dist _ _).
Search (angle_eucl_dist _ 0 < _)%L.
Search (angle_eucl_dist _ _ < angle_eucl_dist _ _)%L.
...
  do 2 rewrite (angle_eucl_dist_symmetry 0).
  apply angle_dist_lt_r.
  apply angle_eucl_dist_div_2_pow_0_lt.
...
apply rngl_cos_lt_angle_eucl_dist_lt. {
  now apply (rngl_lt_le_incl Hor) in Hε.
}
apply Nat.log2_up_le_pow2 in Hm.
...
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
  progress unfold seq_angle_to_div_nat.
  rewrite angle_mul_nat_assoc.
  rewrite Nat.mul_comm.
  rewrite <- angle_mul_nat_assoc.
  easy.
}
(*2*)
...
eapply (angle_lim_eq_compat 0 (Nat.log2_up n)). {
(*
  intros i.
  rewrite Nat.add_0_r; symmetry.
  rewrite Nat.add_comm at 1.
  rewrite angle_div_2_pow_add_r.
  rewrite angle_mul_nat_assoc.
  specialize (Nat.div_mod (2 ^ (i + Nat.log2_up n)) n Hnz) as H1.
  rewrite H1.
  rewrite Nat.mul_add_distr_l.
...
*)
  intros i.
  rewrite Nat.add_0_r; symmetry.
  rewrite Nat.add_comm at 1.
  rewrite angle_div_2_pow_add_r.
  rewrite angle_mul_nat_assoc.
  rewrite Nat.pow_add_r.
enough (H : ∃ m, m < n ∧ 2 ^ Nat.log2_up n = n + m).
destruct H as (m & Hmn & H).
rewrite H.
rewrite Nat.mul_add_distr_l.
rewrite Nat.div_add_l; [ | easy ].
rewrite Nat.mul_add_distr_r.
Search ((_ + _) * _)%A.
rewrite angle_mul_add_distr_r.
rewrite Nat.mul_comm.
rewrite <- angle_mul_nat_assoc.
Search (2 ^ _ * _)%A.
rewrite angle_div_2_pow_mul_2_pow.
...
  easy.
}
remember (θ /₂^Nat.log2_up n)%A as θ' eqn:Hθ'.
...
intros * Hnz.
specialize (Nat.log2_up_spec n) as H1.
destruct n; [ easy | ].
destruct n; [ easy | ].
assert (H : 1 < S (S n)) by now apply -> Nat.succ_lt_mono.
specialize (H1 H); clear H.
apply Work.Nat_eq_div_1.
split; [ easy | ].
apply (Nat.le_lt_trans _ (S (S n))); [ | ].
Search (2 ^ Nat.log2_up _).
...2
remember (θ /₂^Nat.log2_up n)%A as θ' eqn:Hθ'.
enough (H : angle_mul_nat_overflow n θ' = false). {
  eapply (angle_lim_eq_compat 0 (Nat.log2_up n)). {
    intros i.
    rewrite Nat.add_0_r; symmetry.
    rewrite Nat.add_comm at 1.
    rewrite angle_div_2_pow_add_r.
    rewrite <- Hθ'.
    rewrite <- angle_div_2_pow_mul; [ | easy ].
    rewrite Nat.pow_add_r.
    rewrite angle_div_2_pow_mul; [ | easy ].
    rewrite angle_mul_nat_assoc.
    rewrite Nat.mul_comm.
    easy.
  }
Print seq_angle_to_div_nat.
Search (_ * _ / _).
Search (_ / _ / _).
Search (2 ^ Nat.log2_up _).
...
remember (angle_mul_nat_overflow n θ) as nt eqn:Hnt.
symmetry in Hnt.
destruct nt. 2: {
  eapply (angle_lim_eq_compat 0 0). {
    intros i.
    rewrite Nat.add_0_r; symmetry.
    rewrite <- angle_div_2_pow_mul; [ | easy ].
    rewrite fold_seq_angle_to_div_nat.
    easy.
  }
  apply (angle_div_nat_is_inf_sum_of_angle_div_2_pow Har Hcz _ _ Hnz Hnt).
}
...
Check angle_div_nat_is_inf_sum_of_angle_div_2_pow.
...1
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow as Hlim'.
specialize (Hlim' Har Hcz n θ' Hnz).
specialize angle_seq_not_overflow_has_not_overflow_limit as H2.
specialize (H2 n (seq_angle_to_div_nat θ n)).
specialize (H2 θ' (seq_angle_mul_nat_not_overflow n θ) Hlim).
assert (H : (θ' < angle_straight)%A). {
  specialize seq_angle_to_div_nat_le_straight_div_pow2_log2_pred as H3.
  clear - Hlim Hnz Hn1 Hcz.
  destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
    now rewrite Hc1 in Hcz.
  }
  clear Hcz.
  destruct_ac.
  specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
  destruct n; [ easy | clear Hnz ].
  destruct n; [ easy | clear Hn1 ].
  apply angle_lt_iff.
  split. {
    apply angle_nlt_ge.
    intros Hst.
    set (ε := angle_eucl_dist θ' angle_straight).
    specialize (Hlim ε).
    assert (H : (0 < ε)%L). {
      subst ε.
      rewrite angle_eucl_dist_is_sqrt.
      apply (rl_sqrt_pos Hon Hos Hor).
      apply (rngl_mul_pos_pos Hop Hor Hii). {
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      apply (rngl_lt_0_sub Hop Hor).
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_cos_bound | ].
      intros H.
      apply eq_rngl_cos_1 in H.
      apply -> angle_sub_move_0_r in H.
      rewrite H in Hst.
      now apply angle_lt_irrefl in Hst.
    }
    specialize (Hlim H); clear H.
    destruct Hlim as (N, HN).
    specialize (HN _ (Nat.le_refl _)).
...
      progress unfold angle_ltb in Hst.
      cbn in Hst.
      rewrite (rngl_leb_refl Hor) in Hst.
      remember (0 ≤? rngl_sin θ')%L as zt eqn:Hzt.
      symmetry in Hzt.
      destruct zt. {
        exfalso.
        apply rngl_ltb_lt in Hst.
        apply (rngl_nle_gt Hor) in Hst.
        apply Hst, rngl_cos_bound.
      }
      clear Hst.
      apply (rngl_leb_gt Hor) in Hzt.
      progress unfold angle_eucl_dist.
...
  2: {
    intros ts; subst θ'.
    progress unfold angle_lim in Hlim.
    progress unfold seq_angle_to_div_nat in Hlim.
    progress unfold is_limit_when_tending_to_inf in Hlim.
...
Theorem glop :
  ∀ u a b,
  angle_lim u a
  → (∀ i, u i ≤ b)%A
  → (a ≤ b)%A.
Proof.
destruct_ac.
intros * Hlim Hu.
specialize (Hlim (angle_eucl_dist a b)).
apply angle_nlt_ge.
intros Hba.
assert (H : (0 < angle_eucl_dist a b)%L). {
  apply (rngl_lt_iff Hor).
  split; [ apply angle_eucl_dist_nonneg | ].
  intros H; symmetry in H.
  apply angle_eucl_dist_separation in H.
  subst b.
  now apply angle_lt_irrefl in Hba.
}
specialize (Hlim H); clear H.
destruct Hlim as (N, HN).
apply angle_nle_gt in Hba.
apply Hba; clear Hba.
... ...
  apply angle_lt_iff.
  split. {
    apply (glop (seq_angle_to_div_nat θ n) θ' _ Hlim).
    intros i.
...
  assert (H : (θ' ≤ angle_straight /₂^(Nat.log2 n - 1))%A). {
Search (angle_mul_nat_overflow _ (seq_angle_to_div_nat _ _)).
assert
  (H : ∀ i, angle_mul_nat_overflow n (seq_angle_to_div_nat θ n i) = false). {
  intros i.
Search (angle_mul_nat_overflow _ (seq_angle_to_div_nat _ _ _)).
...
Search (_ → angle_mul_nat_overflow _ _ = false).
...
remember (angle_mul_nat_overflow n θ') as ao eqn:Hao.
symmetry in Hao.
destruct ao. 2: {
  specialize (Hlim' eq_refl).
  progress unfold seq_angle_to_div_nat in Hlim.
  progress unfold seq_angle_to_div_nat in Hlim'.
  eapply (angle_lim_eq_compat 0 0) in Hlim'. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite angle_div_2_pow_mul; [ | easy ].
    rewrite angle_mul_nat_assoc.
    easy.
  }
...
  induction n as (n, IHn) using lt_wf_rec; intros.
  destruct n; [ easy | clear Hnz ].
...
progress unfold seq_angle_to_div_nat in H1.
eapply (angle_lim_eq_compat 0 0) in H1. 2: {
  intros i.
  rewrite Nat.add_0_r.
  rewrite angle_mul_nat_assoc.
  easy.
}
...
Search angle_lim
progress unfold angle_lim in Hlim.
Search (_ → (_ * _ = _)%A).
...
specialize (seq_angle_mul_nat_not_overflow n θ) as H2.
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow as Hlim'.
specialize (Hlim' Har Hch n θ' Hiz).
..
angle_lim (seq_angle_to_div_nat θ n) θ'
Search (angle_lim _ _ → _).
...
Check angle_div_nat_is_inf_sum_of_angle_div_2_pow.
...
About angle_lim_seq_angle_le.
Search (angle_lim _ _ → _).
*)

(* to be completed or deleted
...
assert (H2 : is_complete _ angle_eucl_dist). {
  intros u Hu.
Check rngl_is_complete_angle_is_complete.
...
  progress unfold rngl_is_complete in Hco.
...
Theorem limit_cos_cos_limit_sin_sin :
  ∀ θ θ',
  is_limit_when_tending_to_inf rngl_dist (λ i, rngl_cos (θ i)) (rngl_cos θ')
  → is_limit_when_tending_to_inf rngl_dist (λ i, rngl_sin (θ i))
      (rngl_sin θ') ∨
    is_limit_when_tending_to_inf rngl_dist (λ i, rngl_sin (θ i))
      (- rngl_sin θ')%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hc.
  left.
  intros ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hc.
specialize (rngl_limit_limit_squ Hon Hop Hic Hiv Hor _ _ Hc) as H1.
cbn in H1.
eapply (is_limit_when_tending_to_inf_eq_compat _ rngl_dist 0 0) in H1. 2: {
  intros i; rewrite Nat.add_0_r.
  specialize (cos2_sin2_1 (θ i)) as H2.
  apply (rngl_add_move_r Hop) in H2.
  apply H2.
}
specialize (cos2_sin2_1 θ') as H2.
apply (rngl_add_move_r Hop) in H2.
rewrite H2 in H1; clear H2.
apply (rngl_limit_sub_l_limit Hop Hor) in H1.
destruct (rngl_eq_dec Heo (rngl_sin θ') 0) as [Hsz| Hsz]. {
  left.
  rewrite Hsz in H1 |-*.
  rewrite (rngl_squ_0 Hos) in H1.
  apply (rngl_limit_squ_0_limit_0 Hor Hop); [ | easy ].
  rewrite Hi1.
  apply Bool.orb_true_r.
}
destruct (rngl_lt_dec Hor 0 (rngl_sin θ')) as [Hzs| Hzs]. {
  left.
  intros ε Hε.
  specialize (rngl_sin_is_continuous θ' (rngl_sin θ') Hzs) as H2.
  destruct H2 as (δ & Hδ & H2).
  move δ before ε.
  assert (H3 : ∀ x, (angle_eucl_dist x θ' < δ)%L → (0 < rngl_sin x)%L). {
    intros * Hx.
    specialize (H2 _ Hx).
    progress unfold rngl_dist in H2.
    progress unfold rngl_abs in H2.
    rewrite (rngl_leb_sub_0 Hop Hor) in H2.
    remember (rngl_sin x ≤? rngl_sin θ')%L as xt eqn:Hxt.
    symmetry in Hxt.
    destruct xt. {
      apply rngl_leb_le in Hxt.
      rewrite (rngl_opp_sub_distr Hop) in H2.
      apply (rngl_lt_sub_lt_add_l Hop Hor) in H2.
      apply (rngl_lt_sub_lt_add_r Hop Hor) in H2.
      now rewrite (rngl_sub_diag Hos) in H2.
    } {
      apply (rngl_leb_gt Hor) in Hxt.
      now apply (rngl_lt_trans Hor _ (rngl_sin θ')).
    }
  }
  clear H2; rename H3 into H2.
  (* faut trouver un N tel que ∀ n ≥ N, d (θ n) θ' < δ *)
  (* à ce moment-là, par H2, le sinus de θ n sera toujours
     positif, ce qui devrait me simplifier la suite *)
  (* peut-être par H1 ? *)
  specialize (H1 δ²)%L.
  progress unfold rngl_dist in H1.
  cbn in H1.
  (* ouais, non, chais pas ; là, il est question de sinus de
     l'angle, pas de l'angle lui-même *)
...
  specialize (rngl_sin_is_continuous θ' ε Hε) as H2.
  destruct H2 as (δ & Hδ & H2).
  move δ before ε.
(* faut trouver un N tel que ∀ n ≥ N, sin (θ n) ≥ 0 *)
(* ou faut que ça dépende de δ, chais pas *)
(* bref c'est pas clair dans ma tête *)
...
  specialize (H1 (ε * (2 * rngl_abs (rngl_sin θ') + 1)))%L.
  assert (H : (0 < ε * (2 * rngl_abs (rngl_sin θ') + 1))%L). {
    apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
    apply (rngl_add_nonneg_pos Hor). 2: {
      apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
    }
    apply (rngl_mul_nonneg_nonneg Hop Hor). {
      apply (rngl_0_le_2 Hon Hop Hor).
    }
    apply (rngl_abs_nonneg Hop Hor).
  }
  specialize (H1 H); clear H.
  destruct H1 as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  progress unfold rngl_dist in HN.
  progress unfold rngl_dist.
  progress unfold rngl_abs in HN.
  progress unfold rngl_abs.
  rewrite (rngl_leb_sub_0 Hop Hor) in HN.
  rewrite (rngl_leb_sub_0 Hop Hor).
  remember (rngl_sin (θ n) ≤? rngl_sin θ')%L as ul eqn:Hul.
  remember ((rngl_sin (θ n))² ≤? (rngl_sin θ')²)%L as ul2 eqn:Hul2.
  generalize Hzs; intros H.
  apply (rngl_leb_gt Hor) in H.
  rewrite H in HN; clear H.
  symmetry in Hul, Hul2.
  destruct ul. {
    apply rngl_leb_le in Hul.
    rewrite (rngl_opp_sub_distr Hop).
    destruct ul2. {
      apply rngl_leb_le in Hul2.
      rewrite (rngl_opp_sub_distr Hop) in HN.
      destruct (rngl_eq_dec Heo (rngl_sin θ')² (rngl_sin (θ n))²)
          as [Htt| Htt]. {
...
      remember (rngl_sin θ' + rngl_sin (θ n))%L as x.
      destruct (rngl_le_dec Hor x 0) as [Hxz| Hxz]. {
(*
        apply (rngl_le_0_sub Hop Hor) in Hul2.
        rewrite (rngl_squ_sub_squ Hop Hic) in Hul2.
        exfalso.
...
*)
        subst x.
        exfalso.
        apply (rngl_nlt_ge Hor) in Hul2.
        apply Hul2; clear Hul2.
        apply (rngl_lt_iff Hor).
        split. {
          apply (rngl_le_0_sub Hop Hor).
          rewrite (rngl_squ_sub_squ Hop Hic).
          rewrite <- (rngl_opp_sub_distr Hop).
          rewrite (rngl_mul_opp_r Hop).
          rewrite (rngl_mul_comm Hic).
          rewrite rngl_add_comm.
          apply (rngl_opp_nonneg_nonpos Hop Hor).
          apply (rngl_mul_nonneg_nonpos Hop Hor); [ | easy ].
          now apply (rngl_le_0_sub Hop Hor).
        }
        intros H.
        apply (rngl_squ_eq_cases Hic Hon Hop Hiv Heo) in H.
        destruct H as [H| H]. {
          rewrite <- H in Hxz.
          rewrite <- (rngl_mul_2_l Hon) in Hxz.
          apply (rngl_nlt_ge Hor) in Hxz.
          apply Hxz; clear Hxz.
          apply (rngl_mul_pos_pos Hop Hor Hii); [ | easy ].
          apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
        }
Search (0 < _ * _)%L.
Search (_² = _²)%L.
...
About rngl_mul_pos_neg.
Search (_ * _ < 0)%L.
...
      apply (rngl_mul_lt_mono_pos_l Hop Hor Hii x); subst x. {
        apply (rngl_lt_le_trans Hor _ (rngl_sin θ')); [ easy | ].
        apply (rngl_le_add_r Hor).

...
    destruct lz. {
      apply rngl_leb_le in Hlz.
...
ε' = (ε / (2 * rngl_abs l + 1)))%L.
ε = ε' * (2 * rngl_abs l + 1)
  specialize (Hlim (ε * (2 * rngl_abs l + 1)))%L.
Check rngl_limit_limit_squ.
...
  intros ε Hε.
(*
  specialize (rngl_sin_is_continuous θ' ε Hε) as H2.
  destruct H2 as (δ & Hδ & H2).
  move δ before ε.
*)
  specialize (H1 ε Hε).
  cbn in H1.
  destruct H1 as (N, HN).
  exists N.
  intros n Hn.
  progress unfold rngl_dist in HN.
  progress unfold rngl_dist.
  specialize (HN n Hn).
Search is_limit_when_tending_to_inf.
...
  apply H2.
...
Theorem rngl_limit_squ_pos_limit :
  ∀ u l,
  (0 < l)%L
  → is_limit_when_tending_to_inf rngl_dist (λ i, (u i)²%L) l²%L
  → is_limit_when_tending_to_inf rngl_dist u l.
Proof.
intros * Hzl Hlim.
(* non, faux *)
... ...
  apply (rngl_limit_squ_pos_limit _ _ H1 Hzs).
...
Theorem rngl_limit_squ_limit :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ u l,
  l ≠ 0%L
  → is_limit_when_tending_to_inf rngl_dist (λ i : nat, (u i)²%L) l²%L
  → is_limit_when_tending_to_inf rngl_dist u l ∨
    is_limit_when_tending_to_inf rngl_dist u (- l)%L.
Proof.
...
  apply (rngl_limit_squ_limit Hon Hop Hiv Hor _ _ Hsz) in H1.
  destruct H1 as [H1| H1]; [ easy | ].
...
intros Hon Hop Hiv Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hlim.
  left; intros ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hlim.
destruct (rngl_eq_dec Heo l 0) as [Hlz| Hlz]. {
  subst l; left.
  rewrite (rngl_squ_0 Hos) in Hlim.
  intros ε Hε.
  specialize (Hlim ε²)%L.
  assert (H : (0 < ε²)%L). {
    apply (rngl_lt_iff Hor).
    split; [ apply (rngl_squ_nonneg Hop Hor) | ].
    intros H; symmetry in H.
    apply (eq_rngl_squ_0 Hos) in H. 2: {
      rewrite Bool.orb_true_iff; right.
      rewrite Hi1; cbn.
      apply (rngl_has_eq_dec_or_is_ordered_r Hor).
    }
    subst ε.
    now apply (rngl_lt_irrefl Hor) in Hε.
  }
  specialize (Hlim H); clear H.
  destruct Hlim as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  progress unfold rngl_dist in HN.
  progress unfold rngl_dist.
  rewrite (rngl_sub_0_r Hos) in HN |-*.
  rewrite (rngl_abs_nonneg_eq Hop Hor) in HN. 2: {
    apply (rngl_squ_nonneg Hop Hor).
  }
...
intros ε Hε.
(**)
specialize (Hlim (ε * (2 * rngl_abs l + 1)))%L.
assert (H : (0 < ε * (2 * rngl_abs l + 1))%L). {
  apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
  apply (rngl_add_nonneg_pos Hor). 2: {
    apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  }
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    apply (rngl_0_le_2 Hon Hop Hor).
  }
  apply (rngl_abs_nonneg Hop Hor).
}
specialize (Hlim H); clear H.
destruct Hlim as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
progress unfold rngl_dist in HN.
progress unfold rngl_dist.
progress unfold rngl_abs in HN.
progress unfold rngl_abs.
rewrite (rngl_leb_sub_0 Hop Hor) in HN.
rewrite (rngl_leb_sub_0 Hop Hor).
remember (u n ≤? l)%L as ul eqn:Hul.
remember ((u n)² ≤? l²)%L as ul2 eqn:Hul2.
remember (l ≤? 0)%L as lz eqn:Hlz.
symmetry in Hul, Hul2, Hlz.
destruct ul. {
  apply rngl_leb_le in Hul.
  rewrite (rngl_opp_sub_distr Hop).
  destruct ul2. {
    apply rngl_leb_le in Hul2.
    rewrite (rngl_opp_sub_distr Hop) in HN.
    destruct lz. {
      apply rngl_leb_le in Hlz.
...
    apply (rngl_le_lt_trans Hor _ (0 - u n))%L. {
      now apply (rngl_sub_le_mono_r Hop Hor).
    }
...
    rewrite (rngl_sub_0_l Hop).
    apply (rngl_le_lt_trans Hor _ 0); [ | easy ].
...
specialize (Hlim ε Hε).
destruct Hlim as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
progress unfold rngl_dist in HN.
progress unfold rngl_dist.
progress unfold rngl_abs in HN.
progress unfold rngl_abs.
rewrite (rngl_leb_sub_0 Hop Hor) in HN.
rewrite (rngl_leb_sub_0 Hop Hor).
remember (u n ≤? l)%L as ul eqn:Hul.
remember ((u n)² ≤? l²)%L as ul2 eqn:Hul2.
symmetry in Hul, Hul2.
destruct ul. {
  apply rngl_leb_le in Hul.
  rewrite (rngl_opp_sub_distr Hop).
  destruct ul2. {
    apply rngl_leb_le in Hul2.
    rewrite (rngl_opp_sub_distr Hop) in HN.
...
eapply (rngl_le_lt_trans Hor); [ | apply HN ].
do 2 rewrite (rngl_leb_sub_0 Hop Hor).
remember (u n ≤? l)%L as ul eqn:Hul.
remember ((u n)² ≤? l²)%L as ul2 eqn:Hul2.
symmetry in Hul, Hul2.
destruct ul. {
  apply rngl_leb_le in Hul.
  rewrite (rngl_opp_sub_distr Hop).
  destruct ul2. {
    apply rngl_leb_le in Hul2.
    rewrite (rngl_opp_sub_distr Hop).
    apply (rngl_le_sub_le_add_l Hop Hor).
    rewrite (rngl_add_sub_assoc Hop).
    rewrite rngl_add_comm.
    rewrite <- (rngl_add_sub_assoc Hop).
    apply (rngl_le_sub_le_add_l Hop Hor).
    apply (rngl_sub_le_compat Hop Hor); [ | easy ].
    (* ah, merde, ça marche pas *)
    (* faut pas faire de le_lt_trans *)
... ...
now apply rngl_limit_squ_limit.
...
destruct (rngl_eq_dec Hed (rngl_sin θ') 0) as [Htz| Hzt]. {
  apply eq_rngl_sin_0 in Htz.
  destruct Htz; subst θ'. {
    cbn in H1, Hc |-*.
    rewrite (rngl_squ_0 Hos) in H1.
...
intros ε Hε.
(* advice of chatgpt: we must use the continuity of the
   sinus function *)
specialize (rngl_sin_is_continuous θ' ε Hε) as H2.
destruct H2 as (δ & Hδ & H2).
move δ before ε.
(**)
  apply eq_rngl_sin_0 in Htz.
  destruct Htz; subst θ'. {
    cbn in H1, Hc, H2 |-*.
    rewrite (rngl_squ_0 Hos) in H1.
...
    specialize (Hc (√(1 - ε²)))%L.
    assert (H : (0 < √(1 - ε²))%L) by ... (* à voir... *)
    specialize (Hc H).
    destruct Hc as (N, HN).
    exists N.
    intros n Hn.
    specialize (HN n Hn).
    progress unfold rngl_dist in HN.
    progress unfold rngl_dist.
(* pfff... non, c'est pas ça, faut réfléchir... *)
...
  rewrite Htz in H1, H2 |-*.
  rewrite (rngl_squ_0 Hos) in H1.
  progress unfold is_limit_when_tending_to_inf in H1.
  specialize (H1 (δ² / 2))%L.
  assert (H : (0 < δ² / 2)%L) by ...
  specialize (H1 H); clear H.
  destruct H1 as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  progress unfold rngl_dist in HN.
  apply eq_rngl_sin_0 in Htz.
  destruct Htz; subst θ'. {
    rewrite angle_eucl_dist_is_sqrt.
    rewrite rngl_cos_sub.
    rewrite (rngl_mul_0_l Hos), rngl_add_0_r.
    cbn.
    rewrite (rngl_mul_1_l Hon).
    rewrite <- (rngl_abs_nonneg_eq Hop Hor δ). 2: {
      now apply (rngl_lt_le_incl Hor) in Hδ.
    }
    rewrite <- (rl_sqrt_squ Hon Hop Hor).
    apply (rl_sqrt_lt_rl_sqrt Hon Hop Hor). {
      apply (rngl_mul_nonneg_nonneg Hop Hor).
      apply (rngl_0_le_2 Hon Hop Hor).
      apply (rngl_le_0_sub Hop Hor).
      apply rngl_cos_bound.
    }
    rewrite (rngl_mul_comm Hic).
    apply (rngl_lt_div_r Hon Hop Hiv Hor).
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    apply (rngl_lt_sub_lt_add_r Hop Hor).
    rewrite (rngl_sub_0_r Hos) in HN.
    rewrite (rngl_abs_nonneg_eq Hop Hor) in HN. 2: {
      apply (rngl_squ_nonneg Hop Hor).
    }
    specialize (cos2_sin2_1 (θ n)) as H1.
    apply (rngl_add_move_l Hop) in H1.
    rewrite H1 in HN; clear H1.
    apply (rngl_lt_sub_lt_add_r Hop Hor) in HN.
    apply (rngl_lt_sub_lt_add_l Hop Hor) in HN.
    eapply (rngl_lt_le_trans Hor); [ apply HN | ].
    apply (rngl_squ_le_diag Hon Hop Hor).
...
2: {
Search (rngl_abs _²)%L.
    rewrite <- (rngl_squ_sqrt Hon δ) in HN.
Search (_² < _²)%L.
  specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
apply (rngl_squ_lt_abs_lt Hop Hor Hii) in HN.
Search ((√_)²)%L.
... ...
apply eq_rngl_sin_0 in Htz.
destruct Htz; subst θ'. {
  cbn.
  rewrite (rngl_mul_1_l Hon).
  cbn in Hc.
  specialize (Hc (δ / √2))%L.
...
destruct (rngl_lt_dec Hor 0 (rngl_sin θ')) as [Hzt| Hzt]. {
  ...
}
destruct (rngl_lt_dec Hor (rngl_sin θ') 0) as [Htz| Htz]. {
  ...
}
...
specialize (H1 (2 * ε))%L. (* au pif, pour l'instant *)
assert (H : (0 < 2 * ε)%L) by ...
specialize (H1 H); clear H.
destruct H1 as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
progress unfold rngl_dist in HN.
progress unfold rngl_dist.
rewrite (rngl_squ_sub_squ Hop Hic) in HN.
rewrite (rngl_abs_mul Hop Hi1 Hor) in HN.
Search (_ * _ < _ * _)%L.
eapply (rngl_lt_le_trans Hor). 2: {
  specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
  remember (rngl_abs (rngl_sin (θ n) - rngl_sin θ')) as a eqn:Ha.
Search (_ * _ ≤ _ * _)%L.
Check rngl_mul_le_mono_pos_l.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ a)%L.
...
  rewrite (rngl_mul_comm Hic).
  eapply (rngl_le_trans Hor).
  apply (rngl_lt_le_incl Hor) in HN.
  apply HN.
(* bon, c'est la merde, il faut que je réfléchisse *)
...
  apply (rngl_mul_le_mono_nonneg_l Hop Hor). 2: {

...
  apply (rngl_le_refl Hor).
}
Check rngl_mul_lt_mono_pos_l.
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii a).
...
easy.
remember (u n + l ≤? 0)%L as ul eqn:Hul.
symmetry in Hul.
destruct ul. {
  apply rngl_leb_le in Hul.
(* bon, fait chier *)
...
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
  apply (rngl_le_lt_trans Hor _ 0). {
    apply (rngl_opp_nonpos_nonneg Hop Hor).
    apply rngl_
Search (- _ ≤ 0)%L.
eapply (rngl_le_lt_trans Hor). {

...
apply (rngl_le_lt_trans Hor _ ((2 * l + 1) * rngl_abs (u n - l)))%L.
). {
eapply (rngl_le_lt_trans Hor). {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
    apply (rngl_abs_nonneg Hop Hor).
  }
  apply (rngl_lt_le_incl Hor) in HN1.
  apply HN1.
}
..
apply (rngl_le_lt_trans Hor _ (rngl_abs (u n - l))); [ | easy ].
rewrite <- (rngl_mul_1_l Hon).
...
generalize Hc; intros Hc2.
apply rngl_limit_limit_squ in Hc2.
...
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros * Hc.
intros ε Hε.
specialize (Hc ε Hε).
destruct Hc as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
progress unfold rngl_dist in HN.
progress unfold rngl_dist.
(*
rewrite <- (rngl_abs_nonneg_eq Hop Hor ε) in HN. 2: {
  now apply (rngl_lt_le_incl Hor) in Hε.
}
apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid) in HN.
rewrite (rngl_squ_sub Hop Hic Hon) in HN.
specialize (cos2_sin2_1 (θ n)) as H.
apply (rngl_add_move_r Hop) in H.
rewrite H in HN; clear H.
specialize (cos2_sin2_1 θ') as H.
apply (rngl_add_move_r Hop) in H.
rewrite H in HN; clear H.
*)
Search (rngl_sin _ - rngl_sin _)%L.
(* pfff... j'en sais rien, chais pas si c'est mieux *)
...
rngl_cos_sub_rngl_cos:
  ∀ {T : Type} {ro : ring_like_op T} {rp : ring_like_prop T} 
    {rl : real_like_prop T} {ac : angle_ctx T} (p q : angle T),
    (rngl_cos p - rngl_cos q)%L =
    (- (2 * rngl_sin (p /₂ + q /₂) * rngl_sin (p /₂ - q /₂)))%L
rngl_sin_sub_rngl_sin:
  ∀ {T : Type} {ro : ring_like_op T} {rp : ring_like_prop T} 
    {rl : real_like_prop T} {ac : angle_ctx T} (p q : angle T),
    (rngl_sin p - rngl_sin q)%L =
    (2 * rngl_cos (p /₂ + q /₂) * rngl_sin (p /₂ - q /₂))%L
...
apply (rngl_squ_lt_abs_lt Hop Hor Hii).
rewrite (rngl_squ_sub Hop Hic Hon).
...
generalize Hc; intros Hs.
move Hs before Hc.
apply limit_cos_cos_limit_sin_sin in Hs.
...
specialize (Hco (λ i, rngl_sin (u i))) as H2.
generalize Hcs; intros H.
apply rngl_is_Cauchy_angle_is_Cauchy_sin in H.
specialize (H2 H); clear H.
destruct H2 as (s, Hs).
move s before c.
generalize Hs; intros Hsi.
apply (rngl_limit_interv Hop Hor _ (-1) 1)%L in Hsi. 2: {
  intros; apply rngl_sin_bound.
}
exists (rngl_acos c).
replace s with (rngl_sin θ) in Hc. 2: {
  rewrite Hθ.
  rewrite rngl_sin_acos.
...
intros ε Hε.
(**)
specialize (Hc (ε * √2))%L.
specialize (Hs (ε * √2))%L.
assert (H : (0 < ε * √2)%L). {
  apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
  apply (rl_sqrt_pos Hon Hos Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
specialize (Hc H).
specialize (Hs H).
destruct Hc as (Nc, Hnc).
destruct Hs as (Ns, Hns).
exists (max Nc Ns).
intros n Hn.
progress unfold angle_eucl_dist.
...
progress unfold is_limit_when_tending_to_inf in Hc.
specialize (Hc (rngl_min 1 ε)).
assert (H : (0 < rngl_min 1 ε)%L) by ...
specialize (Hc H); clear H.
destruct Hc as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
rewrite angle_eucl_dist_is_sqrt.
rewrite <- (rngl_abs_nonneg_eq Hop Hor ε). 2: {
  now apply (rngl_lt_le_incl Hor) in Hε.
}
rewrite <- (rl_sqrt_squ Hon Hop Hor ε).
apply (rl_sqrt_lt_rl_sqrt Hon Hop Hor). {
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_0_le_2 Hon Hop Hor).
  apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
}
rewrite (rngl_mul_comm Hic).
apply (rngl_lt_div_r Hon Hop Hiv Hor). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
apply (rngl_lt_sub_lt_add_l Hop Hor).
apply (rngl_lt_sub_lt_add_r Hop Hor).
...
(* je pense que rngl_cos_diff_le_eucl_dist ne
   sert à rien
specialize rngl_cos_diff_le_eucl_dist as H1.
specialize (H1 θ (u n)).
rewrite angle_eucl_dist_is_sqrt in H1.
progress unfold rngl_is_limit_when_tending_to_inf in H1.
progress unfold is_limit_when_tending_to_inf in H1.
progress unfold rngl_dist in H1.
specialize (H1 (ε² / 2))%L.
...
*)
do 2 rewrite (rngl_squ_sub Hop Hic Hon).
rewrite rngl_add_assoc.
rewrite rngl_add_add_swap.
rewrite <- (rngl_add_assoc _ (rngl_cos _)²)%L.
rewrite cos2_sin2_1.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_add_swap.
rewrite <- (rngl_add_sub_swap Hop).
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop 1)%L.
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_sub_add_distr Hos).
rewrite <- rngl_cos_sub.
progress unfold rngl_dist in HN.
rewrite <- (rngl_cos_acos c) in HN; [ | easy ].
rewrite <- Hθ in HN.
eapply (rngl_lt_trans Hor); [ | apply HN ].
rewrite rngl_cos_sub_comm.
rewrite (rngl_abs_sub_comm Hop Hor).
...
specialize (Hc ε Hε).
destruct Hc as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
progress unfold angle_eucl_dist.
(*
rewrite rngl_cos_acos; [ | easy ].
rewrite rngl_sin_acos; [ | easy ].
*)
remember (rngl_acos c) as θ eqn:Hθ.
specialize rngl_cos_diff_le_eucl_dist as H1.
specialize (H1 θ (u n)).
rewrite angle_eucl_dist_is_sqrt in H1.
do 2 rewrite (rngl_squ_sub Hop Hic Hon).
rewrite rngl_add_assoc.
rewrite rngl_add_add_swap.
rewrite <- (rngl_add_assoc _ (rngl_cos _)²)%L.
rewrite cos2_sin2_1.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_add_swap.
rewrite <- (rngl_add_sub_swap Hop).
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop 1)%L.
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_sub_add_distr Hos).
rewrite <- rngl_cos_sub.
progress unfold rngl_dist in HN.
rewrite <- (rngl_cos_acos c) in HN; [ | easy ].
rewrite <- Hθ in HN.
eapply (rngl_lt_trans Hor); [ | apply HN ].
rewrite rngl_cos_sub_comm.
rewrite (rngl_abs_sub_comm Hop Hor).
(* grave ! le truc est à l'envers *)
...
destruct (angle_eq_dec θ (u n)) as [Htu| Htu]. {
  rewrite Htu, angle_sub_diag, (rngl_sub_diag Hos).
  rewrite (rngl_mul_0_r Hos).
  now rewrite (rl_sqrt_0 Hon Hop Hic Hor Hid).
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor ε). 2: {
  now apply (rngl_lt_le_incl Hor) in Hε.
}
rewrite <- (rl_sqrt_squ Hon Hop Hor ε).
apply (rl_sqrt_lt_rl_sqrt Hon Hop Hor). {
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_0_le_2 Hon Hop Hor).
  apply (rngl_le_0_sub Hop Hor), rngl_cos_bound.
}
rewrite (rngl_mul_comm Hic).
apply (rngl_lt_div_r Hon Hop Hiv Hor). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
apply (rngl_lt_sub_lt_add_l Hop Hor).
apply (rngl_lt_sub_lt_add_r Hop Hor).
progress unfold rngl_dist in HN.
specialize rngl_cos_diff_le_eucl_dist as H1.
specialize (H1 θ (u n)).
rewrite angle_eucl_dist_is_sqrt in H1.
...
rngl_cos_diff_le_eucl_dist :
  ∀ θ1 θ2 : angle T, (rngl_cos θ1 - rngl_cos θ2 ≤ angle_eucl_dist θ1 θ2)%L
(* mouais, faut voir *)
... ...
apply rngl_is_complete_angle_is_complete in Hco.
}
...
Theorem glop :
  ∀ θ1 θ2,
  (θ1 ≤ θ2 ≤ angle_right)%A
  → (rngl_cos θ1 - rngl_cos θ2 ≤ rngl_sin (θ2 - θ1))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * H12.
progress unfold angle_leb in H12.
cbn in H12.
rewrite (rngl_0_leb_1 Hon Hop Hor) in H12.
destruct H12 as (H12, H2s).
rewrite rngl_sin_sub.
(*
apply (rngl_le_sub_le_add_l Hop Hor).
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
rewrite <- (rngl_add_sub_assoc Hop).
apply (rngl_le_sub_le_add_l Hop Hor).
rewrite (rngl_sub_mul_r_diag_r Hon Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
*)
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs2; [ | easy ].
apply rngl_leb_le in Hzs2, H2s.
destruct zs1; [ | easy ].
apply rngl_leb_le in Hzs1.
apply rngl_leb_le in H12.
apply (rngl_le_sub_le_add_l Hop Hor).
rewrite (rngl_add_sub_assoc Hop).
apply (rngl_le_add_le_sub_r Hop Hor).
...
(*3*)
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite <- (rngl_add_sub_assoc Hop).
    apply (rngl_le_sub_le_add_l Hop Hor).
    rewrite (rngl_sub_mul_l_diag_l Hon Hop).
    rewrite (rngl_sub_mul_l_diag_r Hon Hop).
    destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hz2| Hz2]. {
      apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ (rngl_cos θ2)). {
        easy.
      }
      rewrite rngl_mul_assoc.
      rewrite fold_rngl_squ.
      specialize (cos2_sin2_1 θ2) as H1.
      apply (rngl_add_move_r Hop) in H1.
      rewrite H1.
      rewrite (rngl_mul_sub_distr_r Hop).
      rewrite (rngl_mul_1_l Hon).
...3
    destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hz1| Hz1]. {
      apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ (rngl_cos θ1)). {
        easy.
      }
      do 2 rewrite rngl_mul_add_distr_l.
      rewrite fold_rngl_squ.
      specialize (cos2_sin2_1 θ1) as H1.
      apply (rngl_add_move_r Hop) in H1.
      rewrite H1.
      unfold rngl_squ.
      rewrite rngl_mul_assoc.
      rewrite <- rngl_add_
...
Search (_ * _ ≤ _ * _)%L.
   apply (rngl_mul_le_mono_compat).
...
2: {
  destruct zs2; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs1.
  apply (rngl_leb_gt Hor) in Hzs2.
  apply rngl_leb_le in H12.
  rewrite (rngl_mul_comm Hic).
  apply (rngl_mul_le_compat_nonneg Hop Hor). {
    split; [ | easy ].
...
... ...
progress unfold is_complete in H2.
specialize (H2 _ H1).
destruct H2 as (θ', Hθ).
exists θ'.
apply Hθ.
...
About is_complete.
...
Search is_Cauchy_sequence.
...
assert (H2 : is_complete angle_eucl_dist). {
  progress unfold is_complete.
  intros u Hu.
...
Search is_Cauchy_sequence.
Print rngl_is_complete.
Search rngl_is_complete.
Print is_complete.
Print rngl_is_complete.
About rngl_is_complete.
...
Inspect 1.
Check angle_lim_angle_lim_mul_mul.
...

Theorem angle_div_nat_is_inf_sum_of_angle_div_2_pow' :
  rngl_is_archimedean T = true →
  rngl_characteristic T = 0 →
  ∀ n θ θ',
  n ≠ 0
  → angle_lim (seq_angle_to_div_nat θ n) θ'
  → θ = (n * θ')%A.
Proof.
destruct_ac.
intros Har Hch.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite Hc1 in Hch.
}
intros * Hiz Hlim.
(*1*)
specialize (angle_lim_angle_lim_mul_mul n _ _ Hlim) as H1.
specialize (seq_angle_mul_nat_not_overflow n θ) as H2.
enough (angle_mul_nat_overflow n θ' = false).
Search (angle_mul_nat_overflow _ _ = false → _).
...1
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow as Hlim'.
specialize (Hlim' Har Hch n θ' Hiz).
remember (angle_mul_nat_overflow n θ') as ao eqn:Hao.
symmetry in Hao.
move Hlim before Hlim'.
destruct ao. 2: {
  specialize (Hlim' eq_refl).
  progress unfold seq_angle_to_div_nat in Hlim.
  progress unfold seq_angle_to_div_nat in Hlim'.
  eapply (angle_lim_eq_compat 0 0) in Hlim'. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite angle_div_2_pow_mul; [ | easy ].
    rewrite angle_mul_nat_assoc.
    easy.
  }
  induction n as (n, IHn) using lt_wf_rec; intros.
  destruct n; [ easy | clear Hiz ].
  destruct n. {
    rewrite angle_mul_1_l.
    eapply (angle_lim_eq_compat 0 0) in Hlim. 2: {
      intros i.
      rewrite Nat.add_0_r.
      rewrite Nat.div_1_r.
      now rewrite angle_div_2_pow_mul_2_pow.
    }
    now apply angle_lim_const in Hlim.
  }
  destruct n. {
    eapply (angle_lim_eq_compat 1 0) in Hlim. 2: {
      intros i.
      rewrite Nat.add_0_r.
      rewrite Nat.pow_add_r.
      rewrite Nat.pow_1_r.
      rewrite Nat.div_mul; [ | easy ].
      rewrite Nat.add_comm.
      rewrite angle_div_2_pow_succ_r_2.
      now rewrite angle_div_2_pow_mul_2_pow.
    }
    apply angle_lim_const in Hlim.
    subst θ'; symmetry.
    apply angle_div_2_mul_2.
  }
  destruct n. {
    generalize Hlim'; intros H.
    eapply angle_same_lim_sub in H; [ | apply Hlim ].
    cbn - [ "/" ] in H.
    eapply (angle_lim_eq_compat 0 0) in H. 2: {
      intros i.
      rewrite Nat.add_0_r.
      rewrite <- angle_mul_nat_assoc.
      rewrite <- angle_mul_sub_distr_l.
      rewrite <- angle_div_2_pow_mul; [ | easy ].
      easy.
    }
...
Print angle_lim.
Print is_limit_when_tending_to_inf.
Definition nat_seq_diverges (u : nat → nat) :=
  ∀ M, ∃ N, ∀ n, N ≤ n → M < u n.

Theorem angle_lim_0_diverges_l :
  rngl_is_archimedean T = true →
  ∀ (u : nat → nat) f,
  angle_lim (λ i, (u i * f i)%A) 0
  → nat_seq_diverges u
  → (∀ i, angle_mul_nat_overflow (u i) (f i) = false)
  → angle_lim f 0.
Proof.
destruct_ac.
intros Har.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hlim Hdiv Hnov.
  intros ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hlim Hdiv Hnov.
intros ε Hε.
progress unfold angle_lim in Hlim.
progress unfold is_limit_when_tending_to_inf in Hlim.
progress unfold nat_seq_diverges in Hdiv.
specialize (int_part Hon Hop Hc1 Hor Har) as H1.
specialize (H1 (1 / ε)%L).
destruct H1 as (M, HM).
specialize (Hdiv M).
destruct Hdiv as (N, HN).
...
rewrite (rngl_abs_nonneg_eq Hop Hor) in HM. 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor); [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
}
(*
specialize (Hlim ε Hε).
specialize (Hlim 1%L).
specialize (Hlim (rngl_0_lt_1 Hon Hop Hc1 Hor)).
*)
(**)
destruct (rngl_lt_dec Hor 1 ε) as [Hε1| Hε1]. {
  specialize (Hlim (ε - 1)%L) as H1.
  assert (H : (0 < ε - 1)%L) by now apply (rngl_lt_0_sub Hop Hor).
  specialize (H1 H); clear H.
  destruct H1 as (P, HP).
  exists (max N P).
  intros n Hn.
  specialize (HN _ (Nat.max_lub_l _ _ _ Hn)) as H2.
  specialize (HP _ (Nat.max_lub_r _ _ _ Hn)) as H3.
  eapply (rngl_le_lt_trans Hor). {
    apply (angle_eucl_dist_triangular _ (u n * f n)).
  }
  replace ε with (1 + (ε - 1))%L. 2: {
    rewrite rngl_add_comm.
    apply (rngl_sub_add Hop).
  }
  apply (rngl_add_le_lt_mono Hop Hor); [ | easy ].
  rewrite angle_eucl_dist_move_0_l.
  rewrite angle_sub_mul_l_diag_r. 2: {
    intros H.
    now rewrite H in H2.
  }
...
  rewrite angle_eucl_dist_is_sqrt.
  rewrite angle_sub_0_l; cbn.
...
rewrite angle_eucl_dist_is_sqrt in HP |-*.
rewrite angle_sub_0_l in HP |-*.
cbn in HP |-*.
...
Check (Nat.le_max_r _ _ Hn).
specialize (HP n (Nat.le_max_r _ _ Hn)).
...
destruct M. {
  cbn in HM.
  rewrite rngl_add_0_r in HM.
  destruct HM as (_, HM).
  apply (rngl_lt_div_l Hon Hop Hiv Hor _ _ _ Hε) in HM.
  rewrite (rngl_mul_1_l Hon) in HM.
  specialize (Hlim 1)%L.
  specialize (rngl_0_lt_1 Hon Hop Hc1 Hor) as H.
  specialize (Hlim H); clear H.
  specialize (Hdiv (u 0)).
  destruct Hdiv as (n, Hn).
  progress unfold abs_diff in Hn.
  remember (u 0 <? u n) as b eqn:Hb.
  symmetry in Hb.
  destruct b. 2: {
    apply Nat.ltb_ge in Hb.
    flia Hb Hn.
  }
  apply Nat.ltb_lt in Hb.
  destruct Hlim as (N, HN).
...
  specialize (HN n).
...
specialize (Hlim (ε / rngl_of_nat M))%L.
assert (H : (0 < ε / rngl_of_nat M)%L). {
...
  apply (rngl_div_lt_pos Hon Hop Hiv Hor _ _ Hε).
  destruct M. {
    cbn in HM.
    destruct HM as (_, HM).
    rewrite rngl_add_0_r in HM.
    apply (rngl_lt_div_l Hon Hop Hiv Hor _ _ _ Hε) in HM.
    rewrite (rngl_mul_1_l Hon) in HM.
...
specialize (Hdiv (1 / ε)).
specialize (Hlim ε Hε).
destruct Hlim as (N, HN).
...
specialize (Hdiv N).
destruct Hdiv as (n, Hn).
... ...
apply angle_lim_0_diverges_l in H. 2: {
...
Theorem angle_div_2_pow_sub :
  ∀ n θ1 θ2,
  angle_add_overflow θ1 (- θ2) = false
  → ((θ1 - θ2) /₂^n)%A = (θ1 /₂^n - θ2 /₂^n)%A.
...
rewrite <- angle_div_2_pow_sub. 2: {
(* ah mais ça, c'est faux, en fait, parce que θ devrait être
   égal à 3θ' *)
      progress unfold angle_sub.
...
Theorem angle_div_2_pow_opp :
  ∀ i θ,
  (- (θ /₂^i) =
     match i with
     | 0 => -θ
     | S i' => angle_straight /₂^i' - θ /₂^i
     end)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq.
cbn.
...
 mk_angle (rngl_cos (θ /₂^i)) (- rngl_sin (θ /₂^i)))%A.
cbn.
revert θ.
induction i; intros; [ easy | ].
rewrite angle_div_2_pow_succ_r_2.
rewrite IHi.
...
destruct i. {
  cbn.
  progress unfold angle_sub.
Check angle_opp_div_2.
  rewrite angle_opp_div_2.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply (angle_eqb_eq Hed) in Htz; subst θ.
  rewrite angle_0_div_2.
  now rewrite angle_add_0_r.
}

  apply (angle_eqb_eq Hed) in Htz; subst θ.
  rewrite angle_0_div_2.
  rewrite angle_add_0_r.
  f_equal.
}
do 2 rewrite angle_div_2_pow_succ_r_2.
rewrite IHi.
cbn.
rewrite Nat.sub_0_r.
rewrite angle_opp_div_2.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply (angle_eqb_eq Hed) in Htz; subst θ.
  rewrite angle_0_div_2.
  rewrite angle_add_0_r.
  f_equal.
  remember (i =? 0) as iz eqn:Hiz.
  symmetry in Hiz.
  destruct iz. {
    apply Nat.eqb_eq in Hiz.
    subst i.
    cbn.
}
...
Theorem angle_div_2_pow_opp :
  ∀ i θ, (- (θ /₂^i) = ((- θ) /₂^i))%A.
Proof.
destruct_ac.
intros.
revert θ.
induction i; intros; [ easy | ].
do 2 rewrite angle_div_2_pow_succ_r_2.
rewrite IHi.
f_equal.
rewrite angle_opp_div_2.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply (angle_eqb_eq Hed) in Htz; subst θ.
  rewrite angle_0_div_2.
  now rewrite angle_add_0_r.
}
... ...
  rewrite angle_div_2_pow_opp.
  rewrite <- angle_div_2_pow_add; [ | ... ].
  rewrite angle_add_opp_r.
  easy.
}
Search (angle_lim (λ _, (_ * (_ /₂^_)))%A).
...
Search ((_ - _) /₂^_)%A.
Search (_ * (_ /₂^_))%A.
Search (angle_lim (λ _, (_ * _)%A)).
...
Search (_ * _ * _)%A.
Search (_ * _ * (_ /₂^_))%A.
...
clear Hlim' IHn.
...
Search (angle_lim _ _ → _).
...
    apply angle_lim_opp in Hlim.
    apply angle_lim_move_0_r in Hlim.
    eapply (angle_lim_eq_compat 2 0) in Hlim. 2: {
      intros i.
      rewrite Nat.add_0_r.
      rewrite (angle_sub_opp_r Hop).
      rewrite (angle_add_opp_l Hic).
      rewrite <- (angle_div_2_pow_mul_2_pow (i + 2) θ') at 1.
...
      rewrite <- angle_mul_sub_distr_r. 2: {
        rewrite Nat.mul_comm.
        now apply Nat.Div0.mul_div_le.
      }
      specialize (Nat.div_mod (2 ^ (i + 2)) 3) as H1.
      specialize (H1 (Nat.neq_succ_0 _)).
      rewrite H1 at 1.
      rewrite Nat.mul_comm.
      rewrite Nat.add_sub_swap; [ | apply Nat.le_refl ].
      rewrite Nat.sub_diag.
      rewrite Nat.add_0_l.
      easy.
    }
Search angle_lim.
...
eapply angle_lim_0_le_if in Hlim'.
...
Search (_ / _ * _).
...
Search (2 ^ _ * _)%A.
    apply angle_lim_0_le_if with (f := λ i, (3 * θ' - θ')%A) in Hlim'. 2: {
      intros i.
      split. {
        progress unfold angle_sub.
        do 2 rewrite (angle_add_comm Hic _ (- θ')%A).
        apply angle_add_le_mono_l. {
Search (angle_add_overflow _ _ = false).
...
destruct_ac.
intros Har Hch.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite Hc1 in Hch.
}
intros * Hiz Hlim.
revert θ θ' Hlim.
progress unfold seq_angle_to_div_nat in Hlim.
induction n as (n, IHn) using lt_wf_rec; intros.
destruct n; [ easy | clear Hiz ].
destruct n. {
  rewrite angle_mul_1_l.
  eapply (angle_lim_eq_compat 0 0) in Hlim. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite Nat.div_1_r.
    now rewrite angle_div_2_pow_mul_2_pow.
  }
  now apply angle_lim_const in Hlim.
}
destruct n. {
  eapply (angle_lim_eq_compat 1 0) in Hlim. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite Nat.pow_add_r.
    rewrite Nat.pow_1_r.
    rewrite Nat.div_mul; [ | easy ].
    rewrite Nat.add_comm.
    rewrite angle_div_2_pow_succ_r_2.
    now rewrite angle_div_2_pow_mul_2_pow.
  }
  apply angle_lim_const in Hlim.
  subst θ'; symmetry.
  apply angle_div_2_mul_2.
}
destruct n. {
  eapply (angle_lim_eq_compat 1 0) in Hlim. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite Nat.pow_add_r.
    cbn - [ "/" ].
    easy.
  }
...
destruct_ac.
intros Har Hch.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite Hc1 in Hch.
}
intros * Hiz Hlim.
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow as Hlim'.
(* pourquoi il faut que nθ ne déborde pas ? on est fichus ! *)
specialize (Hlim' Har Hch n θ' Hiz).
remember (angle_mul_nat_overflow n θ') as ao eqn:Hao.
symmetry in Hao.
destruct ao. {
  clear Hlim'.
  apply Bool.not_false_iff_true in Hao.
  exfalso; apply Hao; clear Hao.
Theorem seq_angle_not_mul_overflow :
  ∀ n u θ θ',
  u = seq_angle_to_div_nat θ n
  → angle_lim u θ'
  → ∀ i, angle_mul_nat_overflow n (u i) = false.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros * Hu Hlim i.
  rewrite (H1 (u i)).
  apply angle_mul_nat_overflow_0_r.
}
intros * Hu Hlim i.
rewrite Hu.
progress unfold seq_angle_to_div_nat.
destruct (lt_dec (2 ^ i) n) as [Hni| Hni]. {
  rewrite Nat.div_small; [ | easy ].
  rewrite angle_mul_0_l.
  apply angle_mul_nat_overflow_0_r.
}
apply Nat.nlt_ge in Hni.
remember (angle_mul_nat_overflow (2 ^ i / n) θ) as b eqn:Hb.
symmetry in Hb.
destruct b. 2: {
  rewrite <- angle_div_2_pow_mul; [ | easy ].
  now apply angle_mul_nat_overflow_div_pow2.
}
apply angle_all_add_not_overflow.
intros m Hmi.
assert (Hnz : n ≠ 0) by flia Hmi.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply (angle_eqb_eq Hed) in Htz.
  subst θ.
  rewrite angle_0_div_pow2.
  rewrite angle_mul_0_r.
  apply angle_add_not_overflow_comm.
  apply angle_add_overflow_0_r.
}
apply (angle_eqb_neq Hed) in Htz.
(**)
destruct m. {
  rewrite angle_mul_0_l.
  apply angle_add_overflow_0_r.
}
destruct m. {
  rewrite angle_mul_1_l.
  now apply angle_add_overflow_pow2_div_mul_pow2_diag.
}
... ...
now apply angle_add_overflow_pow2_div_mul_pow2_mul.
destruct m. {
...
Search (angle_add_overflow _ _ = false).
...
(*
  specialize (angle_mul_add_overflow_mul_div_pow2 n (S i) θ) as H1.
  assert (H : n < 2 ^ S i). {
    apply (Nat.le_lt_trans _ (2 ^ i)); [ easy | ].
    cbn; rewrite Nat.add_0_r.
    remember (2 ^ i) as x.
    destruct x; [ | cbn; flia ].
    symmetry in Heqx.
    now apply Nat.pow_nonzero in Heqx.
  }
  specialize (H1 H); clear H.
  cbn in H1.
*)
...
destruct n; [ easy | clear Hnz ].
destruct n. {
  apply Nat.lt_1_r in Hmi; subst m.
  rewrite angle_mul_0_l.
  apply angle_add_overflow_0_r.
}
destruct n. {
  destruct m. {
    rewrite angle_mul_0_l.
    apply angle_add_overflow_0_r.
  }
  destruct m; [ clear Hmi | flia Hmi ].
  rewrite angle_mul_1_l.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  progress unfold angle_leb.
  remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
  remember (0 ≤? rngl_sin (u i + u i))%L as zsm eqn:Hzsm.
  symmetry in Hzs, Hzsm.
  rewrite Hu in Hzs, Hzsm.
  progress unfold seq_angle_to_div_nat in Hzs.
  progress unfold seq_angle_to_div_nat in Hzsm.
  rewrite Hzs, Hzsm.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    destruct zsm; [ | easy ].
    apply rngl_leb_le in Hzsm.
    apply rngl_leb_le.
    rewrite (angle_add_diag Hon Hos) in Hzsm |-*.
    rewrite rngl_sin_mul_2_l in Hzsm.
    rewrite rngl_cos_mul_2_l'.
    apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
    remember (rngl_cos (u i)) as x eqn:Hx.
    rewrite Hu in Hx.
    progress unfold seq_angle_to_div_nat in Hx.
    rewrite <- Hx.
    destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
      destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
        rewrite Hu.
        progress unfold seq_angle_to_div_nat.
        apply eq_rngl_sin_0.
        destruct Hxz as [Hxz| Hxz]. {
          rewrite Hxz in Hx; cbn in Hx; subst x.
          exfalso; apply (rngl_nlt_ge Hor) in H2.
          apply H2; clear H2.
          rewrite Hxz.
          apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
        } {
          rewrite Hxz in Hx; cbn in Hx; subst x.
          exfalso; clear H1 H2 Hzs.
          destruct i; [ cbn in Hni; flia Hni | ].
          rewrite angle_div_2_pow_succ_r_1.
          rewrite angle_mul_nat_div_2.
          now apply (angle_div_2_not_straight Hc1).
          rewrite Nat.pow_succ_r'.
          rewrite Nat.mul_comm.
          rewrite Nat.div_mul; [ | easy ].
          apply angle_mul_nat_overflow_pow_div.
        }
      }
      exfalso.
      rewrite Hu in Hxz.
      progress unfold seq_angle_to_div_nat in Hxz.
      apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
      apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2%L). {
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      now rewrite rngl_mul_0_r.
    }
    (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
    apply rngl_2_x2_sub_1_le_x.
    rewrite <- Hx in Hzsm.
    split; [ easy | ].
    subst x; apply rngl_cos_bound.
  }
  apply (rngl_leb_gt Hor) in Hzs.
  apply (rngl_nle_gt Hor) in Hzs.
  exfalso.
  apply Hzs; clear Hzs.
  destruct i; [ cbn in Hni; flia Hni | ].
  rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
  apply rngl_sin_div_2_nonneg.
}
destruct n. {
  destruct m. {
    rewrite angle_mul_0_l.
    apply angle_add_overflow_0_r.
  }
  apply Nat.succ_lt_mono in Hmi.
  destruct m. {
    clear Hmi.
    rewrite angle_mul_1_l.
    progress unfold angle_add_overflow.
    apply angle_ltb_ge.
    progress unfold angle_leb.
    remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
    remember (0 ≤? rngl_sin (u i + u i))%L as zsm eqn:Hzsm.
    symmetry in Hzs, Hzsm.
    rewrite Hu in Hzs, Hzsm.
    progress unfold seq_angle_to_div_nat in Hzs.
    progress unfold seq_angle_to_div_nat in Hzsm.
    rewrite Hzs, Hzsm.
    destruct zs. {
      apply rngl_leb_le in Hzs.
      destruct zsm; [ | easy ].
      apply rngl_leb_le in Hzsm.
      apply rngl_leb_le.
      rewrite (angle_add_diag Hon Hos) in Hzsm |-*.
      rewrite rngl_sin_mul_2_l in Hzsm.
      rewrite rngl_cos_mul_2_l'.
      apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
      remember (rngl_cos (u i)) as x eqn:Hx.
      rewrite Hu in Hx.
      progress unfold seq_angle_to_div_nat in Hx.
      rewrite <- Hx in Hzsm |-*.
      destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
        destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
          rewrite Hu in Hxz.
          progress unfold seq_angle_to_div_nat in Hxz.
          apply eq_rngl_sin_0 in Hxz.
          destruct Hxz as [Hxz| Hxz]. {
            rewrite Hxz in Hx; cbn in Hx; subst x.
            exfalso; apply (rngl_nlt_ge Hor) in H2.
            apply H2.
            apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
          } {
            rewrite Hxz in Hx; cbn in Hx; subst x.
            exfalso; clear H1 H2 Hzs.
            destruct i; [ cbn in Hni; flia Hni | ].
            rewrite angle_div_2_pow_succ_r_1 in Hxz.
            rewrite angle_mul_nat_div_2 in Hxz.
            now apply (angle_div_2_not_straight Hc1) in Hxz.
            rewrite Nat.pow_succ_r'.
            rewrite Nat.mul_comm.
            apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i * 2 / 2)). {
              apply Nat.div_le_compat_l.
              split; [ easy | apply Nat.le_succ_diag_r ].
            }
            rewrite Nat.div_mul; [ | easy ].
            apply angle_mul_nat_overflow_pow_div.
          }
        }
        exfalso.
        rewrite Hu in Hxz.
        progress unfold seq_angle_to_div_nat in Hxz.
        apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
        apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2%L). {
          apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
        }
        now rewrite rngl_mul_0_r.
      }
      (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
      apply rngl_2_x2_sub_1_le_x.
      split; [ easy | ].
      subst x; apply rngl_cos_bound.
    }
    apply (rngl_leb_gt Hor) in Hzs.
    apply (rngl_nle_gt Hor) in Hzs.
    exfalso.
    apply Hzs; clear Hzs.
    apply rngl_sin_nonneg_angle_le_straight.
    apply angle_mul_div_pow2_le_straight.
    eapply Nat.le_trans; [ now apply Nat.Div0.div_mul_le | ].
    apply Nat.Div0.div_le_upper_bound; [ easy | ].
    apply Nat.mul_le_mono_r.
    now do 2 apply -> Nat.succ_le_mono.
  }
  apply Nat.succ_lt_mono in Hmi.
  apply Nat.lt_1_r in Hmi; subst m.
(**)
  destruct i; [ cbn in Hni; flia Hni | ].
  destruct i; [ cbn in Hni; flia Hni | ].
  rewrite angle_div_2_pow_succ_r_1.
  remember (2 ^ S (S i) / 3) as n eqn:Hn.
...
  rewrite angle_mul_nat_div_2. {
    rewrite angle_mul_nat_div_2. {
      apply angle_add_overflow_div_2_div_2.
    }
destruct i. {
  cbn.
  rewrite Bool.orb_false_r.
  do 2 rewrite angle_add_0_r.
  apply angle_add_overflow_div_2_div_2.
}
destruct i. {
  cbn.
  rewrite Bool.orb_false_r.
  do 2 rewrite angle_add_0_r.
  rewrite angle_add_div_2_diag.
  apply angle_add_overflow_div_2_div_2.
}
destruct i. {
  cbn - [ angle_mul_nat angle_div_2_pow ].
  rewrite Bool.orb_false_r.
  rewrite angle_mul_1_l.
  apply angle_mul_nat_overflow_distr_add_overflow.
(* ça peut parfaitement déborder *)
...
Search (angle_add_overflow (_ * _) (_ * _)).
...
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_succ_r_2.
Search (_ * (_ /₂^_))%A.
rewrite <- angle_div_2_pow_mul.
Inspect 5.
...
Search (_ * (_ /₂))%A.
Inspect 3.
Search (_ * (_ /₂^_))%A.
rewrite <- angle_div_2_pow_mul.
...
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  progress unfold angle_leb.
  remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
  remember (0 ≤? rngl_sin (u i + 2 * u i))%L as zsm eqn:Hzsm.
  symmetry in Hzs, Hzsm.
  destruct zs. {
    destruct zsm; [ | easy ].
    apply rngl_leb_le in Hzs, Hzsm.
    apply rngl_leb_le.
...
Search (_ * (_ /₂^_))%A.
rewrite <- angle_div_2_pow_mul.
...
remember (u i) as θ1 eqn:Hθ1.
      rename θ' into θ''.
      change_angle_sub_r θ1 angle_straight.
      rename θ'' into θ'.
      rename Hθ' into Hui; symmetry in Hui.
      rewrite Hui in Hzcu, Hzs.
      progress sin_cos_add_sub_straight_hyp T Hzs.
      progress sin_cos_add_sub_straight_hyp T Hzcu.
...
      rewrite Hu in Hzcu, Hzs.
      progress unfold seq_angle_to_div_nat in Hzcu.
      progress unfold seq_angle_to_div_nat in Hzs.
      destruct i; [ cbn in Hni; flia Hni | ].
      destruct i; [ cbn in Hni; flia Hni | ].
      remember (2 ^ S (S i) / 3 * (θ /₂^S (S i)))%A as θ1 eqn:H1.
      symmetry in H1.
      generalize H1; intros H2.
      apply angle_div_2_pow_mul_nat_if in H1.
      apply (angle_mul_nat_not_overflow_le_l 3) in H1. 2: {
        apply Nat.div_le_lower_bound. 2: {
          rewrite Nat.mul_comm.
          now apply Nat.Div0.mul_div_le.
        }
        intros H.
        apply Nat.div_small_iff in H; [ | easy ].
        now apply Nat.nle_gt in H.
      }
      apply Bool.not_true_iff_false in H1.
      apply H1; clear H1.
      progress unfold angle_mul_nat_overflow.
      apply Bool.orb_true_iff.
      left; cbn.
      rewrite angle_add_0_r.
      progress unfold angle_add_overflow.
      progress unfold angle_ltb.
      rewrite angle_add_assoc.
      generalize Hzs; intros H.
      apply (rngl_leb_gt Hor) in H.
      rewrite H; clear H.
      remember (0 ≤? rngl_sin _)%L as zs3 eqn:Hzs3.
      symmetry in Hzs3.
      destruct zs3; [ easy | ].
      apply (rngl_leb_gt Hor) in Hzs3.
      apply rngl_ltb_lt.
...
      rename θ' into θ''.
      change_angle_sub_r θ1 angle_straight.
      rename θ'' into θ'.
      remember (2 ^ S (S i) / 3 * (θ /₂^S (S i)))%A as θ2 eqn:H2.
      move Hθ' at top; subst θ2.
      do 2 rewrite angle_add_assoc in Hzs3.
      do 2 rewrite angle_add_assoc.
      progress sin_cos_add_sub_straight_hyp T Hzs.
      progress sin_cos_add_sub_straight_hyp T Hzs3.
      progress sin_cos_add_sub_straight_hyp T Hzs3.
      progress sin_cos_add_sub_straight_hyp T Hzcu.
      progress sin_cos_add_sub_straight_goal T.
      progress sin_cos_add_sub_straight_goal T.
      rewrite (rngl_add_opp_l Hop).
      apply (rngl_lt_sub_0 Hop Hor).
(* c'est faux, ça ; c'est fou, ça *)
...
rewrite (angle_add_opp_l Hic).
        rewrite <- angle_opp_add_distr.
        rewrite (angle_right_add_right Hon Hop).
        progress unfold angle_add_overflow.
        rewrite angle_add_opp_r.
        rewrite <- angle_opp_add_distr.
        progress unfold angle_ltb.
        rewrite rngl_sin_opp.
        rewrite (rngl_sin_add_straight_l Hon Hop).
        rewrite (rngl_opp_involutive Hop).
        cbn.
        specialize (rngl_0_le_1 Hon Hop Hor) as H1.
        apply rngl_leb_le in H1.
        rewrite H1; clear H1.
        specialize (rngl_opp_1_lt_0 Hon Hop Hor Hc1) as H1.
        apply (rngl_leb_gt Hor) in H1.
        now rewrite H1.
      }
...
apply (rngl_mul_pos_neg Hop Hor Hid).
...
      destruct (rngl_le_dec Hor 0 (rngl_cos (u i))) as [Hzcu| Hzcu]. {
        apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
        destruct Hzsm as [(H1, H2)| (H1, H2)]. {
          apply (rngl_le_0_mul Hon Hop Hiv Hor) in H1.
          destruct H1 as [| (H1, H3)]; [ easy | ].
          exfalso; apply (rngl_nlt_ge Hor) in H1.
          apply H1; clear H1.
          apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
        }
        apply (rngl_le_antisymm Hor) in Hzcu; [ | easy ].
        apply eq_rngl_cos_0 in Hzcu.
        destruct Hzcu as [Hzcu| Hzcu]. {
          rewrite Hzcu; cbn.
          apply (rngl_0_le_1 Hon Hop Hor).
        }
        exfalso.
        clear H1 H2 Hmi.
        rewrite Hu in Hzcu.
        progress unfold seq_angle_to_div_nat in Hzcu.
        destruct i; [ cbn in Hni; flia Hni | ].
        destruct i; [ cbn in Hni; flia Hni | ].
        apply angle_div_2_pow_mul_nat_if in Hzcu.
        apply (angle_mul_nat_not_overflow_le_l 3) in Hzcu. 2: {
          apply Nat.div_le_lower_bound. 2: {
            rewrite Nat.mul_comm.
            now apply Nat.Div0.mul_div_le.
          }
          intros H.
          apply Nat.div_small_iff in H; [ | easy ].
          now apply Nat.nle_gt in H.
        }
        apply Bool.not_true_iff_false in Hzcu.
        apply Hzcu; clear Hzcu.
        progress unfold angle_mul_nat_overflow.
        apply Bool.orb_true_iff.
        left; cbn.
        rewrite angle_add_0_r.
        rewrite (angle_add_opp_l Hic).
        rewrite <- angle_opp_add_distr.
        rewrite (angle_right_add_right Hon Hop).
        progress unfold angle_add_overflow.
        rewrite angle_add_opp_r.
        rewrite <- angle_opp_add_distr.
        progress unfold angle_ltb.
        rewrite rngl_sin_opp.
        rewrite (rngl_sin_add_straight_l Hon Hop).
        rewrite (rngl_opp_involutive Hop).
        cbn.
        specialize (rngl_0_le_1 Hon Hop Hor) as H1.
        apply rngl_leb_le in H1.
        rewrite H1; clear H1.
        specialize (rngl_opp_1_lt_0 Hon Hop Hor Hc1) as H1.
        apply (rngl_leb_gt Hor) in H1.
        now rewrite H1.
      }
      apply (rngl_nle_gt Hor) in Hzcu.
rewrite Hu.
progress unfold seq_angle_to_div_nat.
...
remember (0 ≤? 1)%L as b eqn:Hb.
symmetry in Hb.
destruct b. 2: {
rewrite (rngl_opp_0 Hop).
rewrite (rngl_leb_refl Hor).
remember (0 ≤? - 1)%L as b eqn:Hb.
symmetry in Hb.
destruct b; [ exfalso | easy ].
apply rngl_leb_le in Hb.
apply (rngl_nlt_ge Hor) in Hb.
apply Hb; clear Hb.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
...
rewrite angle_add_opp_r.
rewrite <- angle_opp_add_distr.
rewrite angle_add_opp_r.
rewrite (angle_right_add_right Hon Hop).
...
rewrite <- angle_div_2_pow_mul in Hzcu; cycle 1. {
  apply Nat.neq_succ_0.
} {
...
apply eq_angle_eq in Hzcu.
remember (5 * (θ /₂^4))%A as x.
injection Hzcu; clear Hzcu; intros Hc Hs; subst x.
...
(* 5θ/16 = 3π/2 *)
(* θ = 16.3π/(2.5) = 24π/5 *)
(* θ = 24π/5 = (20π+4π)/5 = 4π/5 *)
(* oui, mais 24π/5 et 4π/5 ne sont pas égaux, ils sont équivalents ;
   cf les nombres rationels où c'est pareil pour 1/2 et 2/4 *)
(* 5θ/16 = 24π/16 = 3π/2 ⇒ 24π/5 est racine *)
(* 5θ/16 = 20π/16/5 = 4π/16 = π/4 ⇒ 4π/5 n'est pas racine *)
...
          rewrite angle_div_2_pow_succ_r_1 in Hzcu.
...
progress unfold angle_add_overflow.
apply angle_ltb_ge.
progress unfold angle_leb.
rewrite <- angle_mul_succ_l.
remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
remember (0 ≤? rngl_sin (S m * u i))%L as zsm eqn:Hzsm.
symmetry in Hzs, Hzsm.
destruct zs. {
  apply rngl_leb_le in Hzs.
  destruct zsm; [ | easy ].
  apply rngl_leb_le in Hzsm.
  apply rngl_leb_le.
(**)
  destruct n; [ easy | clear Hnz ].
  destruct n. {
    apply Nat.lt_1_r in Hmi; subst m.
    rewrite angle_mul_1_l.
    apply (rngl_le_refl Hor).
  }
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      apply (rngl_le_refl Hor).
    }
    destruct m; [ clear Hmi | flia Hmi ].
    rewrite rngl_sin_mul_2_l in Hzsm.
    rewrite rngl_cos_mul_2_l'.
    apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
    remember (rngl_cos (u i)) as x eqn:Hx.
    destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
      destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
        apply eq_rngl_sin_0 in Hxz.
        destruct Hxz as [Hxz| Hxz]. {
          rewrite Hxz in Hx; cbn in Hx; subst x.
          exfalso; apply (rngl_nlt_ge Hor) in H2.
          apply H2.
          apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
        } {
          rewrite Hxz in Hx; cbn in Hx; subst x.
          exfalso; clear H1 H2 Hzs.
          rewrite Hu in Hxz.
          progress unfold seq_angle_to_div_nat in Hxz.
          destruct i; [ cbn in Hni; flia Hni | ].
          rewrite angle_div_2_pow_succ_r_1 in Hxz.
          rewrite angle_mul_nat_div_2 in Hxz.
          now apply (angle_div_2_not_straight Hc1) in Hxz.
          rewrite Nat.pow_succ_r'.
          rewrite Nat.mul_comm.
          rewrite Nat.div_mul; [ | easy ].
          apply angle_mul_nat_overflow_pow_div.
        }
      }
      exfalso.
      apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
      apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2%L). {
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      now rewrite rngl_mul_0_r.
    }
    (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
    apply rngl_2_x2_sub_1_le_x.
    split; [ easy | ].
    subst x; apply rngl_cos_bound.
  }
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      apply (rngl_le_refl Hor).
    }
    destruct m. {
      rewrite rngl_sin_mul_2_l in Hzsm.
      apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
      remember (rngl_cos (u i)) as x eqn:Hx.
      destruct Hzsm as [(H1, Hzsm)| (H1, H2)]. 2: {
        destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
          apply eq_rngl_sin_0 in Hxz.
          destruct Hxz as [Hxz| Hxz]. {
            rewrite Hxz in Hx; cbn in Hx; subst x.
            exfalso; apply (rngl_nlt_ge Hor) in H2.
            apply H2.
            apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
          } {
            rewrite Hxz in Hx; cbn in Hx; subst x.
            exfalso; clear H1 H2 Hzs.
            rewrite Hu in Hxz.
            progress unfold seq_angle_to_div_nat in Hxz.
            destruct i; [ cbn in Hni; flia Hni | ].
            rewrite angle_div_2_pow_succ_r_1 in Hxz.
            rewrite angle_mul_nat_div_2 in Hxz.
            now apply (angle_div_2_not_straight Hc1) in Hxz.
            rewrite Nat.pow_succ_r'.
            rewrite Nat.mul_comm.
            apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i * 2 / 2)). 2: {
              rewrite Nat.div_mul; [ | easy ].
              apply angle_mul_nat_overflow_pow_div.
            }
            now apply Nat.div_le_compat_l.
          }
        }
        exfalso.
        apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
        apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2%L). {
          apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
        }
        now rewrite rngl_mul_0_r.
      }
      (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
      rewrite rngl_cos_mul_2_l'.
      subst x.
      apply rngl_2_x2_sub_1_le_x.
      split; [ easy | apply rngl_cos_bound ].
    }
    destruct m; [ clear Hmi | flia Hmi ].
(* ui = 2π/3 + ε ⇒ 3ui = 3ε ⇒ marche pas *)
progress unfold seq_angle_to_div_nat in Hu.
(* oui, mais est-ce que ui peut être égal à 2π/3+ε ? Si ça se
   trouve, non ! *)
...
destruct i; [ cbn in Hni; flia Hni | ].
destruct i; [ cbn in Hni; flia Hni | ].
destruct i. {
  clear Hni.
  rewrite Hu in Hzs, Hzsm |-*.
  cbn - [ angle_mul_nat ] in Hzsm, Hzs |-*.
  rewrite angle_mul_1_l in Hzsm, Hzs |-*.
...
}
destruct i. {
  clear Hni.
  rewrite Hu in Hzs, Hzsm |-*.
  cbn - [ angle_mul_nat ] in Hzsm, Hzs |-*.
...
(*
    replace 3 with (1 + 2) in Hzsm |-* by easy.
    rewrite (angle_mul_add_distr_r Hon Hop) in Hzsm |-*.
    rewrite angle_mul_1_l in Hzsm |-*.
    remember (2 * u i)%A as x.
    cbn in Hzsm |-*; subst x.
...
*)
cbn.
cbn in Hzsm.
remember (rngl_sin (u i)) as s eqn:Hs.
remember (rngl_cos (u i)) as c eqn:Hc.
do 2 rewrite (rngl_mul_0_r Hos) in Hzsm |-*.
rewrite (rngl_sub_0_r Hos) in Hzsm |-*.
rewrite rngl_add_0_r in Hzsm |-*.
do 2 rewrite (rngl_mul_1_r Hon) in Hzsm |-*.
...
Search (rngl_cos _ ≤ rngl_cos _)%L.
Check quadrant_1_rngl_cos_add_le_cos_l.
replace 3 with (1 + 2) by easy.
rewrite (angle_mul_add_distr_r Hon Hop).
rewrite angle_mul_1_l.
apply quadrant_1_rngl_cos_add_le_cos_l; try easy.
(* aïe aïe aïe *)
...
Search (0 ≤ rngl_sin _ → _)%L.
apply rngl_cos_le_anticompat_when_sin_nonneg; try easy.
...
    destruct m; [ clear Hmi | flia Hmi ].
    rewrite rngl_sin_mul_2_l in Hzsm.
    rewrite rngl_cos_mul_2_l'.
    apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
    remember (rngl_cos (u i)) as x eqn:Hx.
    destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
...
  destruct (rngl_le_dec Hor 0 (rngl_cos (u i))) as [Hzc| Hcz]. {
    destruct (rngl_le_dec Hor 0 (rngl_sin (m * u i)%A)) as [Hsmu| Hsmu]. {
      destruct (rngl_le_dec Hor 0 (rngl_cos (m * u i)%A)) as [Hcmu| Hcmu]. {
        cbn - [ rngl_cos ].
        now apply quadrant_1_rngl_cos_add_le_cos_l.
      }
      apply (rngl_nle_gt Hor) in Hcmu.
      cbn.
      eapply (rngl_le_trans Hor). {
        apply (rngl_le_sub_nonneg Hop Hor).
        now apply (rngl_mul_nonneg_nonneg Hop Hor).
      }
      apply (rngl_le_0_sub Hop Hor).
      rewrite (rngl_sub_mul_r_diag_l Hon Hop).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      apply (rngl_le_0_sub Hop Hor).
      apply rngl_cos_bound.
    }
    apply (rngl_nle_gt Hor) in Hsmu.
    destruct (rngl_le_dec Hor (rngl_cos (m * u i)) 0) as [Hcmu| Hcmu]. {
      apply (rngl_lt_eq_cases Hor) in Hzc.
      destruct Hzc as [Hzc| Hzc]. {
        exfalso.
        apply (rngl_nlt_ge Hor) in Hzsm.
        apply Hzsm; clear Hzsm.
        cbn.
        apply (rngl_add_nonpos_neg Hop Hor). {
          now apply (rngl_mul_nonneg_nonpos Hop Hor).
        }
        now apply (rngl_mul_pos_neg Hop Hor Hid).
      }
      symmetry in Hzc.
      apply eq_rngl_cos_0 in Hzc.
      destruct Hzc as [Hzc| Hzc]. {
        rewrite Hzc in Hsmu, Hcmu.
        destruct m; [ now apply (rngl_lt_irrefl Hor) in Hsmu | ].
        destruct m. {
          exfalso.
          apply (rngl_nle_gt Hor) in Hsmu.
          apply Hsmu; clear Hsmu.
          rewrite angle_mul_1_l.
          apply (rngl_0_le_1 Hon Hop Hor).
        }
(*
        destruct m. {
          exfalso.
          apply (rngl_nle_gt Hor) in Hsmu.
          apply Hsmu; clear Hsmu.
          rewrite <- (angle_add_diag Hon Hos).
          rewrite (angle_right_add_right Hon Hop).
          apply (rngl_le_refl Hor).
        }
*)
        rewrite Hu in Hzc.
        progress unfold seq_angle_to_div_nat in Hzc.
        destruct i. {
          cbn in Hzc.
          destruct n; [ easy | ].
          destruct n; [ flia Hmi | ].
          rewrite Nat.div_small in Hzc; [ | flia ].
          rewrite angle_mul_0_l in Hzc.
          symmetry in Hzc.
          now apply (angle_right_neq_0 Hc1) in Hzc.
        }
        destruct i. {
          cbn in Hzc.
          destruct n; [ easy | ].
          destruct n; [ flia Hmi | ].
          destruct n; [ flia Hmi | ].
          rewrite Nat.div_small in Hzc; [ | flia ].
          rewrite angle_mul_0_l in Hzc.
          symmetry in Hzc.
          now apply (angle_right_neq_0 Hc1) in Hzc.
        }
        cbn - [ div Nat.pow ] in Hzc.
        apply angle_div_4_not_right in Hzc; [ easy | easy | ].
        intros H.
        apply eq_angle_eq in H.
        remember (_ * _)%A as x eqn:Hx in H.
        injection H; clear H; intros Hs Hc; subst x.
        (*
        rewrite rngl_cos_cos_mul in Hc.
        rewrite rngl_sin_sin_mul in Hs.
        *)
        remember (2 ^ S (S i) / n) as s eqn:Hsn.
        symmetry in Hsn.
        destruct s. {
          apply Nat.div_small_iff in Hsn; [ | easy ].
          now apply Nat.nle_gt in Hsn.
        }
        destruct s. {
          cbn in Hc, Hs.
          rewrite (rngl_mul_1_r Hon) in Hc, Hs.
          rewrite (rngl_mul_0_r Hos) in Hc, Hs.
          rewrite (rngl_sub_0_r Hos) in Hc.
          rewrite rngl_add_0_r in Hs.
          apply eq_rngl_cos_1 in Hc.
          now apply eq_angle_div_2_pow_0 in Hc.
        }
        destruct s. {
          rewrite rngl_cos_mul_2_l in Hc.
          rewrite rngl_sin_mul_2_l in Hs.
          rewrite <- rngl_mul_assoc in Hs.
          apply (rngl_eq_mul_0_r Hos Hii) in Hs.
          2: apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
          apply (rngl_integral Hos Hid) in Hs.
          destruct Hs as [Hs| Hs]. {
            rewrite Hs in Hc.
            apply eq_rngl_sin_0 in Hs.
            destruct Hs as [Hs| Hs]. {
              rewrite Hs in Hzc.
              do 2 rewrite angle_0_div_2 in Hzc.
              rewrite angle_mul_0_r in Hzc.
              symmetry in Hzc.
              now apply (angle_right_neq_0 Hc1) in Hzc.
            }
            clear Hzc Hc.
            destruct i. {
              cbn in Hni, Hsn.
              apply Nat_div_less_small_iff in Hsn; [ | easy ].
              cbn in Hsn.
              rewrite Nat.add_0_r in Hsn.
              flia Hmi Hni Hsn.
            }
            cbn in Hs.
            now apply (angle_div_2_not_straight Hc1) in Hs.
          }
          rewrite Hs in Hc.
          rewrite (rngl_squ_0 Hos) in Hc.
          rewrite (rngl_sub_0_l Hop) in Hc.
          symmetry in Hc.
          apply (rngl_add_move_0_r Hop) in Hc.
          apply (rngl_eq_add_0 Hor) in Hc; cycle 1. {
            apply (rngl_0_le_1 Hon Hop Hor).
          } {
            apply (rngl_squ_nonneg Hop Hor).
          }
          destruct Hc as (Hc, _).
          now apply (rngl_1_neq_0_iff Hon) in Hc.
        }
        destruct m. {
          rewrite <- (angle_add_diag Hon Hos) in Hsmu.
          rewrite (angle_right_add_right Hon Hop) in Hsmu.
          cbn in Hsmu.
          now apply (rngl_lt_irrefl Hor) in Hsmu.
        }
        destruct s. {
          apply Nat_div_less_small_iff in Hsn; [ | easy ].
          cbn - [ "*" "^" ] in Hsn.
          destruct i; [ cbn in Hsn; flia Hsn | ].
          destruct i; [ cbn in Hsn; flia Hsn | ].
          destruct i. {
            destruct n; [ easy | clear Hnz ].
            destruct n; [ flia Hmi | ].
            do 2 apply Nat.succ_lt_mono in Hmi.
            destruct n; [ flia Hmi | ].
            destruct n; [ cbn in Hsn; flia Hsn | ].
            destruct n; [ cbn in Hsn; flia Hsn | ].
            destruct n. {
              cbn in Hsn.
              destruct m. {
...
do 2 rewrite Nat.add_0_r in H.
apply eq_angle_mul_0 in H.
destruct H as [H| H]. {
  apply Nat.div_small_iff in H; [ | flia Hmi ].
  now apply Nat.nle_gt in H.
}
destruct H as (Hc, Hs).
cbn in Hc.
...
        clear Hzs.
        rewrite Hu in Hzsm.
        progress unfold seq_angle_to_div_nat in Hzsm.
        cbn - [ Nat.pow "*"%A ] in Hzsm.
        rewrite Hzc in Hzsm.
        destruct m. {
          apply (rngl_nlt_ge Hor) in Hzsm.
          apply Hzsm; clear Hzsm.
          replace 3 with (2 + 1) by easy.
          rewrite (angle_mul_add_distr_r Hon Hop).
          rewrite <- (angle_add_diag Hon Hos).
          rewrite (angle_right_add_right Hon Hop).
          rewrite (rngl_sin_add_straight_l Hon Hop).
          rewrite angle_mul_1_l.
          cbn.
          apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
        }
        destruct m. {
          clear Hzsm Hsmu Hcmu.
          destruct i. {
            cbn in Hni.
            replace n with 4 in H by flia Hmi Hni.
            cbn in H.
            now rewrite angle_add_0_r in H.
          }
          destruct i. {
            cbn in H, Hzc, Hni.
            remember (8 / n) as m eqn:Hm.
            symmetry in Hm.
            destruct m. {
              apply Nat.div_small_iff in Hm; [ | flia Hmi ].
              now apply Nat.nle_gt in Hm.
            }
            destruct m. {
              rewrite angle_mul_1_l in H.
              now apply (eq_angle_div_2_0) in H.
            }
            destruct m. {
              now rewrite angle_div_2_mul_2 in H.
            }
            apply Nat_div_less_small_iff in Hm; [ | flia Hmi ].
            flia Hm Hmi.
          }
          destruct i. {
            cbn in H, Hzc, Hni.
            remember (16 / n) as m eqn:Hm.
            symmetry in Hm.
            destruct m. {
              apply Nat.div_small_iff in Hm; [ | flia Hmi ].
              now apply Nat.nle_gt in Hm.
            }
            destruct m. {
              rewrite angle_mul_1_l in H.
              apply (eq_angle_div_2_0) in H.
              now apply (eq_angle_div_2_0) in H.
            }
            destruct m. {
              rewrite angle_div_2_mul_2 in H.
              now apply (eq_angle_div_2_0) in H.
            }
            destruct m. {
              apply Nat_div_less_small_iff in Hm; [ | flia Hmi ].
              cbn - [ "*" ] in Hm.
              destruct n; [ flia Hm | ].
              destruct n; [ flia Hm | ].
              destruct n; [ flia Hm | ].
              destruct n; [ flia Hm | ].
              destruct n; [ flia Hm | ].
              destruct n. {
                cbn in Hm.
apply eq_angle_mul_0 in H.
...
(*
θ = 8π/3 = (6π+2π)/3 = 2π/3
θ/2 = π/3
θ/2/2 = π/6
3*(θ/2/2) = π/2
*)
...
              rewrite Nat.mul_add_distr_l in Hm.
cbn in Hm.
flia Hni Hm.
...
              rewrite angle_div_2_mul_2 in H.
              now apply (eq_angle_div_2_0) in H.
            }
            apply Nat_div_less_small_iff in Hm; [ | flia Hmi ].
            flia Hm Hmi.
          }
...
Theorem angle_eq_mul_0_r :
  ∀ n θ, (n * θ)%A = 0%A → n mod 2 = 1 → ((n - 1) * θ = angle_straight)%A.
Proof.
destruct_ac.
intros * Hnt Hnz.
rewrite angle_mul_sub_distr_r. 2: {
  rewrite <- Hnz.
  now apply Nat.mod_le.
}
rewrite angle_mul_1_l.
rewrite Hnt.
rewrite (angle_sub_0_l Hon Hos).
specialize (Nat.div_mod n 2 (Nat.neq_succ_0 _)) as H1.
rewrite Hnz in H1.
rewrite H1 in Hnt.
(* ah, fait chier *)
...
apply (angle_opp_inj Hop).
rewrite angle_opp_involutive.
Search (- angle_straight)%A.
Search (n mod _ ≠ 0).
rewrite
rewrite angle_opp_straight.
... ...
apply angle_eq_mul_0_r in H. 2: {
  intros H'.
  apply Nat.div_small_iff in H'; [ | flia Hmi ].
  now apply Nat.nlt_ge in Hni.
}
...
  rewrite H' in Hzc.
  rewrite angle_mul_0_l in Hzc.
  symmetry in Hzc.
  now apply (angle_right_neq_0 Hc1) in Hzc.
}
...
apply (f_equal (λ θ, (2 * θ)%A)) in H.
symmetry in H.
rewrite <- (angle_add_diag Hon Hos) in H.
rewrite angle_straight_add_straight in H.
symmetry in H.
apply angle_eq_mul_0_r in H; [ | easy ].
cbn - [ div Nat.pow ] in H.
rewrite angle_add_0_r in H.
Search (_ * _ = angle_straight)%A.
...

destruct n; [ easy | ].
(* mmmm... mais ça, c'est faux, ça *)
...
Search (_ * (_ /₂))%A.
rewrite angle_mul_nat_div_2 in Hzc. 2: {
...
          destruct i. {
            cbn in Hzc.
            destruct n; [ easy | ].
            destruct n; [ flia Hmi | ].
            destruct n; [ flia Hmi | ].
            destruct n; [ flia Hmi | ].
...
            rewrite Nat.div_small in Hzc; [ | flia ].
            rewrite angle_mul_0_l in Hzc.
            symmetry in Hzc.
            now apply (angle_right_neq_0 Hc1) in Hzc.
          }
...
Search (angle_right = 0)%A.
Search (angle_straight = 0)%A.
destruct n; [ flia Hmi | ].
destruct n; [ flia Hmi | ].
...
          rewrite Hzc in *.
          clear Hzs.
          replace 4 with (2 + 2) by easy.
          rewrite (angle_mul_add_distr_r Hon Hop).
          rewrite <- (angle_add_diag Hon Hos).
          rewrite (angle_right_add_right Hon Hop).
          rewrite angle_straight_add_straight.
          cbn.
          exfalso.
          replace 3 with (1 + 2) in Hsmu, Hcmu by easy.
          rewrite (angle_mul_add_distr_r Hon Hop) in Hsmu, Hcmu.
          rewrite <- (angle_add_diag Hon Hos) in Hsmu, Hcmu.
          rewrite (angle_right_add_right Hon Hop) in Hsmu, Hcmu.
          rewrite angle_mul_1_l in Hsmu, Hcmu.
          clear Hsmu Hcmu.
...
        cbn in Hzsm |-*.
        rewrite Hzc in Hzsm |-*.
        cbn in Hzsm |-*.
...
Search (_ * _ ≤ _)%L.
apply rngl_le_div_r; try easy.
...
      apply (rngl_le_sub_le_add_l Hop Hor).
      remember (rngl_cos (u i) * rngl_cos (m * u i))%L as x eqn:Hx.
apply rngl_le_sub_nonneg.
      apply (rngl_le_trans Hor _ (rngl_cos (u i) * rngl_cos (m * u i))
...
(*
apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
cbn - [ rngl_cos ].
apply quadrant_1_rngl_cos_add_le_cos_l; try easy. (* faut voir les cas cos *)
*)
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy. (* ça dépend *)
...
  apply rngl_cos_le_anticompat_when_sin_nonneg; [ easy | easy | ].
  rewrite Hu.
...
Theorem angle_lim_seq_angle_not_mul_overflow :
  ∀ n θ θ',
  angle_lim (seq_angle_to_div_nat θ n) θ'
  → angle_mul_nat_overflow n θ' = false.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 θ').
  apply (angle_mul_nat_overflow_0_r Hon Hos).
}
intros * Hlim.
progress unfold seq_angle_to_div_nat in Hlim.
apply (angle_all_add_not_overflow n θ').
intros m Hm.
progress unfold angle_add_overflow.
apply angle_ltb_ge.
progress unfold angle_leb.
rewrite <- angle_mul_succ_l.
remember (0 ≤? rngl_sin θ')%L as zs eqn:Hzs.
remember (0 ≤? rngl_sin (S m * θ'))%L as zsm eqn:Hzsm.
symmetry in Hzs, Hzsm.
(**)
destruct zsm. 2: {
  destruct zs; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs.
  apply (rngl_leb_gt Hor) in Hzsm.
  apply rngl_leb_le.
...
destruct zsm. {
  apply rngl_leb_le in Hzsm.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    apply rngl_leb_le.
    specialize (angle_lim_seq_angle_le n θ θ' Hlim) as Htt.
    assert (Hts : (θ' ≤ angle_straight)%A). {
      now apply rngl_sin_nonneg_angle_le_straight.
    }
    specialize (Htt Hts).
    cbn - [ rngl_cos ].
    destruct (rngl_le_dec Hor 0 (rngl_cos θ')) as [Hzc| Hzc]. {
      destruct (rngl_le_dec Hor 0 (rngl_sin (m * θ'))) as [Hzm| Hzm]. {
        apply rngl_cos_le_cos_add1; try easy.
        now right; right; left.
      }
      apply (rngl_nle_gt Hor) in Hzm.
      cbn - [ rngl_sin ] in Hzsm.
(* c'est faux : m*θ'=-ε ; mais peut-être qu'avec Htt et Hts je peux
   m'en sortir ; aucune idée si j'ai une chance *)
(**)
      exfalso.
      revert n Hlim Hm.
      revert θ' Hzs Hzsm Htt Hts Hzc Hzm.
      induction m; intros. {
        rewrite angle_mul_0_l in Hzm.
        now apply (rngl_lt_irrefl Hor) in Hzm.
      }
      destruct n; [ easy | ].
      apply Nat.succ_lt_mono in Hm.
...
      revert m Hm Hzsm Hzm.
      revert θ' Hzs Htt Hzc Hts Hlim.
      induction n; intros; [ easy | ].
      destruct m. {
        rewrite angle_mul_0_l, angle_add_0_r.
        apply (rngl_le_refl Hor).
      }
      apply Nat.succ_lt_mono in Hm.
      destruct (Nat.eq_dec (S m) n) as [Hsmn| Hsmn]. {
        subst n.
(* ouais, bon, ça sert à rien *)
...
      }
      apply IHn; try easy.
      flia Hm Hsmn.
    }
...
      specialize (IHn _ Hm).
      cbn - [ rngl_sin ] in Hzm.
...
}
now apply H1.
...
specialize (angles_lim_le (λ i, 2 ^ i / n * (θ /₂^i)) (λ _, θ))%A as H1.
specialize (H1 θ' θ)%A.
cbn in H1.
assert (Htt : (θ' ≤ θ)%A). {
  apply H1; [ | easy | ]. 2: {
    intros ε Hε.
    exists 0.
    intros p _.
    now rewrite angle_eucl_dist_diag.
  }
  intros.
Theorem seq_angle_to_div_nat_le :
  ∀ i n θ, (2 ^ i / n * (θ /₂^i) ≤ θ)%A.
Proof.
... ...
  apply seq_angle_to_div_nat_le.
}
...
      specialize (Hlim (angle_eucl_dist θ' 0)).
      assert (Htz : (0 < angle_eucl_dist θ' 0)%L). {
        apply (rngl_lt_iff Hor).
        split; [ apply angle_eucl_dist_nonneg | ].
        intros H; symmetry in H.
        apply angle_eucl_dist_separation in H.
        subst θ'.
        rewrite angle_mul_0_r in Hzm.
        now apply (rngl_lt_irrefl Hor) in Hzm.
      }
      specialize (Hlim Htz).
      destruct Hlim as (N, HN).
      specialize (HN N (le_refl _)).
...
specialize (angle_eucl_dist_triangular) as H1.
specialize (H1 θ' (2 ^ N / n * (θ /₂^N)) 0)%A.
exfalso.
apply (rngl_nlt_ge Hor) in H1.
apply H1; clear H1.
rewrite angle_eucl_dist_symmetry.
eapply (rngl_le_lt_trans Hor); [ | apply HN ].
(* ah bin non *)
...
Search (rngl_cos _ ≤ rngl_cos _)%L.
apply angle_add_overflow_le_lemma_4 with (θ2 := (m * θ')%A); try easy.
apply quadrant_1_rngl_cos_add_le_cos_l.
Check seq_angle_to_div_nat_le.
... ...
Theorem seq_angle_to_div_nat_le :
  ∀ i n θ, (2 ^ i / n * (θ /₂^i) ≤ θ)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%A), (H1 θ).
  apply angle_le_refl.
}
intros.
progress unfold angle_leb.
remember (0 ≤? rngl_sin (2 ^ i / n * (θ /₂^i)))%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs2, Hzs.
destruct zs2. {
  clear Hzs2.
  destruct zs; [ | easy ].
  apply rngl_leb_le in Hzs.
  apply rngl_leb_le.
  destruct i. {
    cbn.
    destruct n; [ apply rngl_cos_bound | ].
    destruct n. {
      rewrite Nat.div_1_r.
      rewrite angle_mul_1_l.
      apply (rngl_le_refl Hor).
    }
    rewrite Nat.div_small; [ | now apply -> Nat.succ_lt_mono ].
    rewrite angle_mul_0_l.
    apply rngl_cos_bound.
  }
  destruct n; [ apply rngl_cos_bound | ].
  destruct n. {
    rewrite Nat.div_1_r.
    rewrite angle_div_2_pow_mul_2_pow.
    apply (rngl_le_refl Hor).
  }
  apply (rngl_le_trans Hor _ (rngl_cos (2 ^ S i / 2 * (θ /₂^S i)))). {
    rewrite Nat.pow_succ_r'.
    rewrite Nat.mul_comm.
    rewrite Nat.div_mul; [ | easy ].
    rewrite angle_div_2_pow_succ_r_2.
    rewrite angle_div_2_pow_mul_2_pow.
    now apply rngl_cos_le_cos_div_2.
  }
  apply rngl_cos_decr.
  split. {
    apply angle_mul_le_mono_r. {
      rewrite Nat.pow_succ_r'.
      rewrite Nat.mul_comm.
      rewrite Nat.div_mul; [ | easy ].
      rewrite angle_div_2_pow_succ_r_2.
      apply angle_mul_nat_overflow_pow_div.
    }
    apply Nat.div_le_compat_l.
    split; [ easy | ].
    now do 2 apply -> Nat.succ_le_mono.
  }
  rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
  apply angle_div_2_le_straight.
}
destruct zs. {
  exfalso.
  apply (rngl_leb_gt Hor) in Hzs2.
  apply rngl_leb_le in Hzs.
  apply (rngl_nle_gt Hor) in Hzs2.
  apply Hzs2; clear Hzs2.
  revert n θ Hzs.
  induction i; intros. {
    cbn.
    destruct n; [ apply (rngl_le_refl Hor) | ].
    destruct n. {
      rewrite Nat.div_1_r.
      now rewrite angle_mul_1_l.
    }
    rewrite Nat.div_small; [ | now do 2 apply -> Nat.succ_le_mono ].
    apply (rngl_le_refl Hor).
  }
  rewrite angle_div_2_pow_succ_r_2.
  eapply (rngl_le_trans Hor). {
    apply (IHi n (θ /₂)%A).
    apply rngl_sin_div_2_nonneg.
  }
(*
destruct n; [ apply (rngl_le_refl Hor) | ].
destruct n. {
  do 2 rewrite Nat.div_1_r.
  rewrite <- angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
  rewrite -> angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
}
*)
  remember (θ ≤? angle_right)%A as tr eqn:Htr.
  symmetry in Htr.
  destruct tr. {
    apply rngl_sin_incr.
    split. {
      apply angle_mul_le_mono_r. {
        destruct n; [ easy | ].
        apply angle_mul_nat_not_overflow_le_l with (n := 2 ^ S i). {
          rewrite <- Nat.div_1_r.
          apply Nat.div_le_compat_l.
          split; [ easy | ].
          now apply -> Nat.succ_le_mono.
        }
        rewrite Nat.pow_succ_r'.
        apply angle_mul_nat_overflow_angle_div_2_mul_2_div_2.
        apply angle_mul_nat_overflow_pow_div.
      }
      destruct n; [ easy | ].
      apply Nat.div_le_mono; [ easy | ].
      apply Nat.pow_le_mono_r; [ easy | ].
      apply Nat.le_succ_diag_r.
    }
    destruct n; [ apply angle_right_nonneg | ].
    destruct n. {
      rewrite Nat.div_1_r.
      rewrite <- angle_div_2_pow_succ_r_2.
      now rewrite angle_div_2_pow_mul_2_pow.
    }
...
(*
  rewrite <- (angle_mul_1_l Hon Hos angle_right).
  rewrite <- angle_straight_div_2.
*)
  rewrite <- angle_div_2_pow_succ_r_2.
(*
  rewrite angle_div_2_pow_succ_r_1.
*)
  apply angle_le_trans with (θ2 := (2 ^ S i * (θ /₂^S i))%A). {
(*
    rewrite <- (angle_mul_1_l Hon Hos (2 ^ S i * _)).
*)
    apply angle_mul_le_mono_r. {
      apply angle_mul_nat_overflow_pow_div.
    }
    rewrite <- (Nat.div_1_r (2 ^ S i)) at 2.
    apply Nat.div_le_compat_l.
    split; [ easy | ].
    now apply -> Nat.succ_le_mono.
  }
  rewrite angle_div_2_pow_mul_2_pow.
(* rahhhh... fait chier *)
...
  apply angle_le_trans with (θ2 := 0%A).
Search (_ * _ ≤ _ * _)%A.
...
Show.
Check seq_angle_to_div_nat_le.
Search (_ → angle_mul_nat_overflow _ _ = false).
...
(*
...
Search (_ * (_ /₂^_))%A.
Search (rngl_cos (_ * _)).
(* faire un Fixpoint, comme pour rngl_cos_div_pow_2 *)
...
Search rngl_cos_div_pow_2.
rngl_cos_div_pow_2_eq:
  ∀ (θ : angle T) (n : nat), rngl_cos (θ /₂^S n) = rngl_cos_div_pow_2 (θ /₂) n
...
Search (_ * _)%A.
rewrite rngl
Search (rngl_cos _ ≤ rngl_cos _)%L.
Check rngl_cos_le_cos_add1.
remember ((2 ^ i / n * (θ /₂^i)))%A as θ' eqn:Hθ'.
destruct (rngl_le_dec Hor 0 (rngl_cos θ')) as [Hsc| Hsc].
specialize (rngl_cos_le_cos_add1 θ' (θ - θ')) as H1.
Search (_ + (_ - _))%A.
Search (_ - _ + _)%A.
rewrite angle_add_comm in H1.
rewrite angle_sub_add in H1.
apply H1; try easy; [ now right; right; left | ].
(* θ' ≤ θ ? *)
...
Search (0 ≤ rngl_sin (_ - _))%L.
apply rngl_sin_sub_nonneg; try easy.
...
rewrite angle
rewrite angle_add_0_r in H1.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
apply rngl_cos_le_anticompat_when_sin_nonneg; try easy.
...
  apply rngl_cos_decr.
  split. {
progress unfold angle_leb.
apply rngl_leb_le in Hzs2, Hzs.
rewrite Hzs2, Hzs.
    destruct i. {
      cbn.
      rewrite <- (angle_mul_1_l Hon Hos θ) at 2.
      apply angle_mul_le_mono_r; [ easy | ].
      destruct n; [ easy | ].
      apply Nat.Div0.div_le_upper_bound; [ easy | ].
      cbn.
      now apply -> Nat.succ_le_mono.
    }
    cbn.
    rewrite Nat.add_0_r.
    destruct i. {
      cbn.
Search (_ * (_ /₂))%A.
rewrite angle_mul_nat_div_2.
...
  destruct i. {
    destruct n; [ apply rngl_cos_bound | ].
    remember (S n) as sn; cbn; subst sn.
*)
...
Theorem glop :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
intros * Hzs1 Hzc1 Hzs12.
cbn.
(* non, c'est faux, ça, suffit que θ2 = 2π-ε *)
... ...
now apply glop.
Search (0 ≤ rngl_sin (_ + _))%L.
specialize (rngl_sin_nonneg_add_nonneg θ' (m * θ') Hzs Hzsm) as H1.
      apply angle_add_overflow_le_lemma_111; try easy. {
        now right; right; left.
      }
      rewrite angle_add_comm in Hzsm.
      apply rngl_sin_add_nonneg_sin_nonneg with (θ2 := θ'); [ | easy ].
      progress unfold angle_add_overflow.
      apply angle_ltb_ge.
      progress unfold angle_leb.
      apply rngl_leb_le in Hzsm.
      rewrite Hzsm.
...
Search (0 ≤ rngl_sin (_ + _))%L.
Search (rngl_cos (_ + _) ≤ rngl_cos _)%L.
...
    apply rngl_cos_decr.
    split; [ | now apply rngl_sin_nonneg_angle_le_straight ].
    progress unfold angle_leb.
    rewrite Hzs.
    apply rngl_leb_le in Hzsm.
    rewrite Hzsm.
    apply rngl_leb_le.
...
destruct n; [ easy | ].
destruct n. {
  cbn.
  rewrite Bool.orb_false_r.
  rewrite angle_add_0_r.
  progress unfold angle_lim in Hlim.
  progress unfold is_limit_when_tending_to_inf in Hlim.
  progress unfold angle_add_overflow.
  progress unfold angle_ltb.
  remember (0 ≤? rngl_sin (θ' + θ'))%L as zsa eqn:Hzsa.
  remember (0 ≤? rngl_sin θ')%L as zs eqn:Hzs.
  symmetry in Hzsa, Hzs.
  destruct zsa. {
    apply rngl_leb_le in Hzsa.
    destruct zs. {
      apply rngl_leb_le in Hzs.
      apply (rngl_ltb_ge Hor).
      destruct (rngl_le_dec Hor 0 (rngl_cos θ')) as [Hzc| Hzc]. {
        apply angle_add_overflow_le_lemma_111; try easy.
        now right; right; left.
      }
      apply (rngl_nle_gt Hor) in Hzc.
      remember (θ' =? angle_straight)%A as ts eqn:Hts.
      symmetry in Hts.
      destruct ts. {
        apply (angle_eqb_eq Hed) in Hts.
        subst θ'.
        clear Hzc Hzs Hzsa.
...
        apply angle_add_overflow_le_lemma_2; try easy. {
          intros H.
          apply eq_rngl_cos_opp_1 in H.
          subst θ'.
cbn in *.
Search (rngl_cos (_ + _) ≤ rngl_cos _)%L.
...
apply angle_add_overflow_le_lemma_111; try easy.
apply angle_add_overflow_le_lemma_1 with (θ2 := θ'); try easy.
apply quadrant_1_rngl_cos_add_le_cos_l; try easy.
...
}
... ...
now apply angle_lim_seq_angle_not_mul_overflow in Hlim.
... ...
destruct ao. 2: {
  specialize (Hlim' eq_refl).
  progress unfold seq_angle_to_div_nat in Hlim.
  progress unfold seq_angle_to_div_nat in Hlim'.
  set (θi := λ i, (2 ^ i / n * (θ /₂^i))%A).
  set (θ'i := λ i, (2 ^ i / n * (n * θ' /₂^i))%A).
  progress fold θi in Hlim.
  progress fold θ'i in Hlim'.
  move Hlim before Hlim'.
  move θ'i before θi.
...
(*
...
  clear Hlim'.
  destruct n; [ easy | ].
  apply (angle_mul_nat_overflow_succ_l_true Hon Hos) in Hao.
...
  apply Bool.not_false_iff_true in Hao.
  exfalso; apply Hao; clear Hao Hlim'.
(**)
  progress unfold seq_angle_to_div_nat in Hlim.
...
Theorem glop :
  ∀ n θ u,
  angle_lim u θ
  → (∀ i, angle_mul_nat_overflow n (u i) = false)
  → angle_mul_nat_overflow n θ = false.
Proof.
destruct_ac.
intros * Hlim Hov.
induction n; [ easy | ].
apply (angle_mul_nat_overflow_succ_l_false Hon Hos).
split. {
  apply IHn.
  intros i.
  specialize (Hov i).
  now apply (angle_mul_nat_overflow_succ_l_false Hon Hos) in Hov.
}
progress unfold angle_lim in Hlim.
progress unfold is_limit_when_tending_to_inf in Hlim.
... ...
apply (glop n) in Hlim; [ easy | ].
intros i.
clear Hlim Hiz.
induction n; [ easy | ].
cbn - [ div ].
destruct n; [ easy | ].
set (u := seq_angle_to_div_nat θ).
cbn in IHn.
destruct n. {
  clear IHn.
  cbn - [ u ].
  rewrite Bool.orb_false_iff.
  rewrite angle_add_0_r.
  split; [ | easy ].
  apply angle_add_diag_not_overflow; [ easy | ].
  progress unfold u; cbn - [ div ].
  progress unfold seq_angle_to_div_nat.
  induction i. {
    cbn.
    apply (angle_straight_pos Hc1).
  }
  cbn - [ div ].
  rewrite Nat.add_0_r.
  rewrite Nat_add_diag.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  rewrite angle_mul_nat_div_2. 2: {
    apply angle_mul_nat_overflow_pow_div.
  }
  apply (angle_div_2_lt_straight Hc1).
}
...
  apply angle_div_2_add_not_overflow.
  cbn in Haov.
Print angle_add_overflow.
Print angle_mul_nat_overflow.
...
Check angle_mul_overflow.
...
2: {
Search (angle_add_overflow _ (S _ * _)).
Search (angle_add_overflow (S _ * _) _).
cbn in Haov.
Search (angle_add_overflow _ (_ + _)).
...
symmetry.
apply angle_div_2_add_not_overflow.
... ...
rewrite angle_mul_nat_div_2.
Search (_ /₂ < angle_straight)%A.
...
Search (0 ≤ angle_straight)%A.
Search (0 < angle_straight)%A.
    apply angle_straight_nonneg.
...
apply rngl_mul_neg_neg.
...
  apply rngl_leb_nle in Hzst.
  apply Hzst; clear Hzst; cbn.
...
  cbn.
  apply (rngl_le_trans Hor _ (rngl_cos θ * rngl_cos θ)). {
    apply (rngl_le_sub_nonneg Hop Hor).
    apply (rngl_mul_diag_nonneg Hop Hor).
  }
...
apply rngl_mul_non
...
  apply (rngl_mul_nonneg_r).
...
  apply (rngl_le_sub_le_add_r Hop Hor).
Search (_ ≤ _ + _)%L.
...
Search (_ → angle_add_overflow _ _ = false).
Theorem glip :
  ∀ θ i,
  angle_add_overflow (seq_angle_to_div_nat θ 2 i)
    (seq_angle_to_div_nat θ 2 i) = false.
Proof.
destruct_ac.
intros.
induction i. {
  cbn.
  apply angle_add_overflow_0_r.
}
cbn - [ div ].
Theorem seq_angle_to_div_nat_succ_r :
  ∀ θ n i,
  seq_angle_to_div_nat θ n (S i) = 0%A.
Proof.
intros.
progress unfold seq_angle_to_div_nat.
cbn.
rewrite Nat.add_0_r.
Search ((_ + _) / _).
(* ah la la la la... ça a pas l'air simple, c't'histoire *)
...
  revert θ' Hlim.
  induction n; intros; [ easy | clear Hiz ].
  destruct n; [ easy | ].
  specialize (IHn (Nat.neq_succ_0 _)).
  destruct n. {
    cbn.
    rewrite angle_add_0_r.
    rewrite Bool.orb_false_r.
    clear IHn.
    progress unfold seq_angle_to_div_nat in Hlim.
    progress unfold angle_lim in Hlim.
    progress unfold is_limit_when_tending_to_inf in Hlim.
...
  rewrite (angle_mul_nat_overflow_succ_l_false Hon Hos).
...
  progress unfold seq_angle_to_div_nat in Hlim.
  progress unfold angle_lim in Hlim.
  progress unfold is_limit_when_tending_to_inf in Hlim.
*)
...
} {
  specialize (Hlim' eq_refl).
  move Hao before Hiz.
(**)
  progress unfold seq_angle_to_div_nat in Hlim.
  progress unfold seq_angle_to_div_nat in Hlim'.
  set (θi := λ i, (2 ^ i / n * (θ /₂^i))%A).
  set (θ'i := λ i, (2 ^ i / n * (n * θ /₂^i))%A).
  progress fold θi in Hlim.
  progress fold θ'i in Hlim'.
...
  assert
      (H :
       angle_lim (λ i, (n * (θi i))%A) θ'). {
    progress unfold angle_lim in Hlim'.
    progress unfold angle_lim.
    progress unfold is_limit_when_tending_to_inf in Hlim'.
    progress unfold is_limit_when_tending_to_inf.
    intros ε Hε.
    specialize (Hlim' ε Hε).
    destruct Hlim' as (N, HN).
    exists N.
    intros m Hm.
    specialize (HN m Hm).
    rewrite angle_div_2_pow_mul in HN; [ | easy | easy ].
    rewrite (angle_mul_nat_assoc Hon Hop) in HN.
    rewrite Nat.mul_comm in HN.
    rewrite <- (angle_mul_nat_assoc Hon Hop) in HN.
    easy.
  }
  clear Hlim'; rename H into Hlim'.
...
  set (u := seq_angle_to_div_nat) in Hlim, Hlim'.
  assert (H :
    ∀ ε, (0 < ε)%L →
    ∃ N, ∀ p, N ≤ p → (angle_eucl_dist (u θ n p) (u (n * θ')%A n p) < ε)%L). {
    intros ε Hε.
    assert (Hε2 : (0 < ε / 2)%L). {
      apply (rngl_lt_div_r Hon Hop Hiv Hor).
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      now rewrite (rngl_mul_0_l Hos).
    }
    specialize (Hlim (ε / 2) Hε2)%L.
    specialize (Hlim' (ε / 2) Hε2)%L.
    destruct Hlim as (N, HN).
    destruct Hlim' as (N', HN').
    exists (max N N').
    intros p Hp.
    assert (H : N ≤ p) by flia Hp.
    specialize (HN _ H); clear H.
    assert (H : N' ≤ p) by flia Hp.
    specialize (HN' _ H); clear H.
    specialize (angle_eucl_dist_triangular) as H1.
    specialize (H1 (u θ n p) θ' (u (n * θ')%A n p)).
    rewrite (angle_eucl_dist_symmetry θ') in H1.
    eapply (rngl_le_lt_trans Hor); [ apply H1 | ].
    specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as H2.
    rewrite (rngl_add_diag2 Hon) in H2.
    rewrite (rngl_mul_div Hi1) in H2. 2: {
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    rewrite H2.
    now apply (rngl_add_lt_compat Hop Hor).
  }
  remember (θ <? n * θ')%A as tt' eqn:Htt'.
  symmetry in Htt'.
  destruct tt'. {
    exfalso.
    remember (n * θ' - θ)%A as Δθ eqn:Hdt.
    apply angle_add_move_l in Hdt.
    specialize (H 1%L).
    assert (H1 : (0 < 1)%L) by apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
    specialize (H H1); clear H1.
    destruct H as (N, HN).
    specialize (HN N (Nat.le_refl _)).
    rewrite <- Hdt in HN.
    progress unfold u in HN.
    progress unfold seq_angle_to_div_nat in HN.
...
  remember (θ =? n * θ')%A as tt eqn:Htt.
  symmetry in Htt.
  destruct tt; [ now apply angle_eqb_eq in Htt | ].
  apply (angle_eqb_neq Hed) in Htt; exfalso.
Search (_ <? _)%A.
...
    specialize (HN' _ H).
    specialize (HN (Nat.le_max_l _ _)).
  specialize (HN' (Nat.le_max_r _ _)).
  progress unfold angle_eucl_dist in HN.
  progress unfold angle_eucl_dist in HN'.
  set (m := max N N') in HN, HN'.
...
  specialize (Hlim 1%L).
  specialize (H1 1%L).
  assert (H : (0 < 1)%L) by apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  specialize (Hlim H).
  specialize (H1 H); clear H.
  destruct Hlim as (N, HN).
  destruct H1 as (N', HN').
  specialize (HN (max N N')).
  specialize (HN' (max N N')).
  specialize (HN (Nat.le_max_l _ _)).
  specialize (HN' (Nat.le_max_r _ _)).
  progress unfold angle_eucl_dist in HN.
  progress unfold angle_eucl_dist in HN'.
  set (m := max N N') in HN, HN'.
...
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
progress unfold is_angle_limit_when_tending_to_inf in Hlim.
progress unfold is_gen_limit_when_tending_to_inf in Hlim.
progress unfold seq_angle_to_div_nat in Hlim.
assert
  (H :
    ∀ ε : T, (0 < ε)%L →
      ∃ N : nat, ∀ n : nat, N ≤ n →
      (angle_dist θ θ' < ε)%L). {
  intros ε Hε.
  specialize (Hlim ε Hε).
  destruct Hlim as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  specialize (Nat.div_mod_eq (2 ^ n) i) as H1.
  symmetry in H1.
  apply Nat.add_sub_eq_r in H1.
  apply (f_equal rngl_of_nat) in H1.
  rewrite (rngl_of_nat_mul Hon Hos) in H1.
  symmetry in H1.
  apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
    intros Hi.
    now apply (eq_rngl_of_nat_0 Hon Hch) in Hi.
  }
...
Fixpoint rngl_to_nat :
  ∀ a,
...
Check rngl_mul_move_l.
Check rngl_mul_move_r.
...
Search (_ * _ = _)%L.
...
Search (_ = _ * _)%L.
...
Search ((_ * _) * _)%A.
progress unfold angle_dist in HN.
Search (rngl_cos (_ * _)%A).
Inspect 8.
...
rat_is_inf_sum_of_inv_rad_pow.
...
intros Hic Hon Hop Har Hed Hch * Hiz Hlim.
destruct_ac.
revert θ θ' Hlim.
induction i; intros; [ easy | ].
clear Hiz.
destruct i. {
  clear IHi; cbn.
  rewrite angle_add_0_r.
  progress unfold seq_angle_to_div_nat in Hlim.
  assert (H : is_angle_limit_when_tending_to_inf (λ _, θ) θ'). {
    intros ε Hε.
    specialize (Hlim ε Hε).
    destruct Hlim as (N, HN).
    exists N.
    intros n Hn.
    specialize (HN n Hn).
    rewrite Nat.div_1_r in HN.
    now rewrite angle_div_2_pow_mul_2_pow in HN.
  }
  clear Hlim; rename H into Hlim.
  progress unfold is_angle_limit_when_tending_to_inf in Hlim.
  specialize (angle_dist_is_dist Hic) as H1.
  specialize (gen_limit_unique Hon Hop Hiv Hor _ _ H1) as H2.
  specialize (H2 (λ _, θ) θ' θ Hlim).
  symmetry.
  apply H2.
  intros ε Hε.
  exists 0.
  intros n Hn.
  now rewrite dist_refl.
}
specialize (IHi (Nat.neq_succ_0 _)).
(**)
destruct i. {
  clear IHi; cbn.
  rewrite angle_add_0_r.
  progress unfold seq_angle_to_div_nat in Hlim.
  assert (H : is_angle_limit_when_tending_to_inf (λ _, θ) (2 * θ')%A). {
    intros ε Hε.
enough (H2ε : (0 < 2 * ε)%L).
    specialize (Hlim (2 * ε)%L H2ε).
    destruct Hlim as (N, HN).
    exists (N - 1). (* au pif *)
    intros n Hn.
    apply Nat.le_sub_le_add_r in Hn.
    specialize (HN (n + 1) Hn).
    rewrite Nat.add_1_r in HN.
    rewrite Nat.pow_succ_r in HN; [ | easy ].
    rewrite Nat.mul_comm in HN.
    rewrite Nat.div_mul in HN; [ | easy ].
    cbn in HN.
    rewrite (angle_div_2_pow_mul_2_pow Hic) in HN.
    progress unfold angle_dist in HN.
    progress unfold angle_dist.
    rewrite rngl_cos_mul_2_l.
    rewrite rngl_sin_mul_2_l.
...
    rewrite Nat.mul_div in HN.
    rewrite Nat.pow_add_r in HN.
    rewrite
Search (_ ^ (_ + _)).
    rewrite Nat.add_
    destruct n. {
...
    rewrite angle_div_2_pow_mul_2_pow in HN.
...
remember (S n) as sn; cbn; subst sn.
rewrite angle_add_comm.
apply (angle_sub_move_r Hic).
apply IHn.
progress unfold seq_angle_to_div_nat.
progress unfold seq_angle_to_div_nat in Hlim.
...
Search (rngl_of_nat _ = 0%L).
  rewrite rngl_of_nat_succ.
...
intros Hic Hon Hop Har Hed * Hnz Hlim.
(*
progress unfold is_angle_upper_limit_when_tending_to_inf in Hlim.
Check rat_is_inf_sum_of_inv_rad_pow.
*)
move Hos before Hed.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
move Hi1 before Hos.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
move Hid before Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 _) in Hnz.
}
move Hc1 before Hid.
move α before θ.
specialize (rat_is_inf_sum_of_inv_rad_pow Hic Hon Hop Hiv Har) as H1.
specialize (H1 2 1 n (le_refl _) Hnz).
progress unfold is_limit_when_tending_to_inf in H1.
progress unfold seq_converging_to_rat in H1.
progress unfold seq_angle_to_div_nat.
Search angle_dist.
...
progress unfold angle_lt in Hα.
progress unfold angle_compare in Hα.
progress unfold rngl_compare in Hα.
cbn in Hα.
rewrite (rngl_leb_refl Hor) in Hα.
remember (0 ≤? rngl_sin α)%L as zs eqn:Hzs; symmetry in Hzs.
destruct zs. {
  apply rngl_leb_le in Hzs.
  remember (rngl_cos α =? 1)%L as ce1 eqn:Hce1; symmetry in Hce1.
  destruct ce1; [ easy | ].
  apply (rngl_eqb_neq Hed) in Hce1.
  remember (rngl_cos α ≤? 1)%L as cl1 eqn:Hcl1; symmetry in Hcl1.
  destruct cl1; [ clear Hα | easy ].
  apply rngl_leb_le in Hcl1.
  specialize (H1 (rngl_sin (angle_div_2 Hiv Hc2 Hor α))).
  assert (H : (0 < rngl_sin (angle_div_2 Hiv Hc2 Hor α))%L). {
    progress unfold angle_div_2.
    cbn.
    rewrite <- (rl_sqrt_0 Hor Hop Hic Hid).
    apply (rl_sqrt_lt_rl_sqrt Hic Hop). {
      apply (rngl_le_refl Hor).
    }
    apply (rngl_div_lt_pos Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    apply (rngl_lt_0_sub Hop Hor).
    now apply (rngl_lt_iff Hor).
  }
  specialize (H1 H); clear H.
  destruct H1 as (N, HN).
  exists N. (* au pif *)
  intros m Hm.
...
rewrite (rngl_squ_mul Hic) in H2.
rewrite <- rngl_squ
Search (√_ * √_)%L.
Search (√_)%L.
...
apply (rngl_mul_le_compat Hop Hor) with (b := √b%L) (d := √a%L).
apply (rngl_
Search (_ * _ < _ * _)%Z.
...
apply (rngl_mul_lt_mono_pos_r Hop Hor Hi1) with (a := √(
...
apply rl_sqrt_lt_rl_sqrt.
Search (_ < √ _)%L.
Search (rngl_squ _ < rngl_squ _)%L.
Search (rngl_squ _ ≤ rngl_squ _)%L.
Search (rngl_abs (√ _))%L.
Search (√ 0)%L.
...
    apply rngl_div_lt_pos.
...

Definition angle_div_nat θ n :=
  {| rngl_cos := 1; rngl_sin := 0;
     rngl_cos2_sin2 := 42 |}%L.
...
*)

(* to be completed
Theorem all_gc_has_nth_root :
  rngl_is_archimedean T = true →
  rngl_characteristic T = 0 →
  rl_has_integral_modulus T = true →
  ∀ n, n ≠ 0 → ∀ z : GComplex T, ∃ x : GComplex T, gc_power_nat x n = z.
Proof.
destruct_ac.
intros Har Hch Him * Hnz *.
specialize (polar Him z) as H1.
set (ρ := √((gre z)² + (gim z)²)%L).
set
  (θ :=
     (if (0 ≤? gim z)%L then rngl_acos Hor (gre z / ρ)%L
      else angle_opp (rngl_acos Hor (gre z / ρ)%L))).
specialize (H1 ρ θ eq_refl eq_refl).
set (ρ' := rl_nth_root n ρ).
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow as H2.
specialize (H2 Har Hch).
remember (seq_angle_to_div_nat θ n) as θi eqn:Hθi.
progress unfold seq_angle_to_div_nat in Hθi.
...
set (θ' := angle_div_nat θ n).
exists (mk_gc (ρ' * cos θ') (ρ' * sin θ')).
...
assert (Hre : (-1 ≤ gre z / ρ ≤ 1)%L). {
  subst ρ.
... ...
apply rl_sqrt_div_squ_squ.
}
...
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hiz| Hiz]. {
  rewrite (rngl_cos_acos Htr).
...
  rewrite (rngl_mul_div_r Hon Hic Hiv). 2: {
    subst ρ.
    progress unfold rl_sqrt.
    progress unfold rl_pow.
    rewrite if_bool_if_dec.
    destruct (Sumbool.sumbool_of_bool _) as [H2| H2]. {
      apply (rngl_eqb_eq Heb) in H2.
      generalize Hmi; intros H.
      progress unfold rl_has_integral_modulus in H.
      remember (rl_opt_mod_intgl_prop T) as mi eqn:Hmi1.
      symmetry in Hmi1.
      destruct mi as [mi| ]; [ clear H | easy ].
      apply mi in H2.
      apply (neq_neq_GComplex Heb) in Hz.
      cbn in Hz.
      now destruct Hz.
    }
    apply (rngl_eqb_neq Heb) in H2.
    apply (rl_exp_neq_0 Hon Hop Hiv H10 Htr).
  }
...
Theorem rl_sin_acos {T} {ro : ring_like_op T} {rp : ring_like_prop T}
  {rl : real_like_prop T} :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_has_eq_dec T = true →
  rngl_is_ordered = true →
  rl_has_trigo = true →
  ∀ x, (-1 ≤ x ≤ 1)%L →
  rl_sin (rngl_acos x) = rl_sqrt (1%L - rngl_squ x).
Proof.
intros * Hon Hop Hiv Hc2 Heb Hor Htr * Hx1.
specialize (rl_cos2_sin2 Htr (rngl_acos x)) as H1.
rewrite (rngl_cos_acos Htr _ Hx1) in H1.
apply (rngl_add_sub_eq_l Hos) in H1.
rewrite H1.
rewrite (rl_sqrt_squ Hon Hop Hiv Hc2 Heb Hor Htr).
(* acos est dans [0,Π[, donc sin est >0 *)
...
Theorem rl_sin_acos {T} {ro : ring_like_op T} {rp : ring_like_prop T}
  {rl : real_like_prop T} :
  ∀ x, rl_sin (rngl_acos x) = rl_sqrt (1 - rngl_squ x)%L.
... ...
rewrite rl_sin_acos.
...
rewrite (rl_cos_atan2 Htr).
rewrite <- Hρ.
rewrite (rngl_mul_div_r Hon Hic Hiv). 2: {
  subst ρ.
  progress unfold rl_sqrt.
  progress unfold rl_pow.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H2| H2]. {
    apply (rngl_eqb_eq Heb) in H2.
    generalize Hmi; intros H.
    progress unfold rl_has_integral_modulus in H.
    remember (rl_opt_mod_intgl_prop T) as mi eqn:Hmi1.
    symmetry in Hmi1.
    destruct mi as [mi| ]; [ clear H | easy ].
    apply mi in H2.
    apply (neq_neq_GComplex Heb) in Hz.
    cbn in Hz.
    now destruct Hz.
  }
  apply (rngl_eqb_neq Heb) in H2.
  apply (rl_exp_neq_0 Hon Hop Hiv H10 Htr).
}
Check rl_cos_atan2.
Theorem rl_sin_atan2 {T} {ro : ring_like_op T} {rp : ring_like_prop T}
  {rl : real_like_prop T} :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_has_eq_dec T = true →
  rngl_is_ordered = true →
  rl_has_trigo = true →
  ∀ x y, rl_sin (rl_atan2 y x) = (y / rl_sqrt (rngl_squ x + rngl_squ y))%L.
Proof.
intros * Hon Hop Hiv Hc2 Heb Hor Htr *.
specialize (rl_cos2_sin2 Htr (rl_atan2 y x)) as H1.
rewrite (rl_cos_atan2 Htr) in H1.
apply (rngl_add_sub_eq_l Hos) in H1.
remember (rl_sqrt _) as ρ eqn:Hρ.
...
specialize (rl_cos2_sin2 Htr (rngl_acos x)) as H1.
rewrite (rngl_cos_acos Htr) in H1.
apply (rngl_add_sub_eq_l Hos) in H1.
rewrite H1.
rewrite (rl_sqrt_squ Hon Hop Hiv Hc2 Heb Hor Hle Htr).
(* acos est dans [0,Π[, donc sin est >0 *)
...

Theorem polyn_modl_tends_tow_inf_when_var_modl_tends_tow_inf {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T} :
  let roc := gc_ring_like_op T in
  rngl_has_opp T = true →
  rngl_has_inv (GComplex T) = true →
  rngl_has_1 (GComplex T) = true →
  ∀ la, 1 < length la → llast la 0%L ≠ 0%L →
  ∀ mz, ∃ z₀, ∀ z, (gc_modl z₀ ≤ gc_modl z →
  mz ≤ gc_modl (rngl_eval_polyn la z))%L.
Proof.
intros * Hop Hivc Honc * Hla Hl1 *.
...
*)

(* to be completed
Theorem gc_opt_alg_closed :
  let ro := gc_ring_like_op T in
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
     rngl_opt_alg_closed := gc_opt_alg_closed;
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
     rngl_opt_archimedean := NA |}.
*)
