(* File created because Complex.v became too big, but
   without any topic found for the moment *)

Set Nested Proofs Allowed.
Require Import Stdlib.ZArith.ZArith.
Require Import Init.Nat.
Import List.ListNotations.

Require Import RingLike.Utf8.
Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.IterAdd.
Require Import RingLike.Misc.
Require Import RingLike.Utils.

Require Import TrigoWithoutPi.Core.
Require Import TrigoWithoutPi.AngleDiv2Add.
Require Import TrigoWithoutPi.AngleAddOverflowEquiv.
Require Import TrigoWithoutPi.SeqAngleIsCauchy.
Require Import TrigoWithoutPi.TacChangeAngle.

Require Import Misc.
Require Import Complex.
Require Import NewtonBinomial.
Require Import AngleAddOverflowEquiv.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Theorem gc_pow_im_0 :
  rngl_has_opp_or_psub T = true →
  ∀ n x, (mk_gc x 0%L ^ n)%C = (mk_gc (x ^ n) 0)%C.
Proof.
intros Hos *.
progress unfold gc_pow_nat.
induction n; [ easy | ].
rewrite rngl_pow_succ_r; cbn.
rewrite IHn.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
now rewrite (rngl_mul_0_l Hos).
Qed.

End a.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

(* *)

Theorem angle_div_2_pow_mul_le_angle :
  ∀ n i θ, n ≤ 2 ^ i → (n * (θ /₂^i) ≤ θ)%A.
Proof.
intros * Hni.
destruct (le_dec (2 ^ i) n) as [Hin| Hin]. {
  apply Nat.le_antisymm in Hin; [ | easy ].
  subst n.
  rewrite angle_div_2_pow_mul_2_pow.
  apply angle_le_refl.
}
apply Nat.nle_gt in Hin.
clear Hni; rename Hin into Hni.
revert n θ Hni.
induction i; intros. {
  cbn in Hni.
  apply Nat.lt_1_r in Hni; subst n; cbn.
  apply angle_nonneg.
}
destruct (lt_dec n (2 ^ i)) as [Hin| Hin]. {
  rewrite angle_div_2_pow_succ_r_2.
  apply (angle_le_trans _ (θ /₂)); [ now apply IHi | ].
  apply angle_div_2_le.
}
apply Nat.nlt_ge in Hin.
assert (H1 : n = 2 ^ i + n mod 2 ^ i). {
  specialize (Nat.div_mod n (2 ^ i)) as H1.
  assert (H : 2 ^ i ≠ 0) by now apply Nat.pow_nonzero.
  specialize (H1 H); clear H.
  rewrite (Nat_div_less_small 1) in H1; [ now rewrite Nat.mul_1_r in H1 | ].
  now rewrite Nat.mul_1_l.
}
rewrite H1.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_pow_succ_r_2 at 1.
rewrite angle_div_2_pow_mul_2_pow.
apply angle_le_trans with (θ2 := (θ /₂ + θ /₂)%A). {
  apply angle_add_le_mono_l; [ apply angle_add_overflow_div_2_div_2 | ].
  rewrite angle_div_2_pow_succ_r_2.
  apply IHi.
  apply Nat.mod_upper_bound.
  now apply Nat.pow_nonzero.
}
rewrite angle_add_div_2_diag.
apply angle_le_refl.
Qed.

Theorem rngl_cos_mul_2_l' :
  ∀ θ, rngl_cos (2 * θ) = (2 * (rngl_cos θ)² - 1)%L.
Proof.
destruct_ac.
intros.
rewrite rngl_cos_mul_2_l.
specialize (cos2_sin2_1 θ) as H1.
apply (rngl_add_sub_eq_l Hos) in H1.
rewrite <- H1.
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_add_sub_swap Hop).
f_equal; symmetry.
apply rngl_mul_2_l.
Qed.

Theorem angle_add_overflow_pow2_div_mul_pow2_diag :
  ∀ n i θ,
  1 < n ≤ 2 ^ i
  → angle_add_overflow (2 ^ i / n * (θ /₂^i)) (2 ^ i / n * (θ /₂^i)) =
      false.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%A).
  apply angle_add_overflow_0_l.
}
intros * (Hmi, Hni).
assert (Hnz : n ≠ 0) by flia Hmi.
rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2.
progress unfold angle_ltb.
remember (seq_angle_to_div_nat θ n) as u eqn:Hu.
remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
symmetry in Hzs.
rewrite Hu in Hzs.
progress unfold seq_angle_to_div_nat in Hzs.
rewrite Hzs.
destruct zs. {
  apply rngl_leb_le in Hzs.
  remember (0 ≤? rngl_sin (u i + u i))%L as zsm eqn:Hzsm.
  symmetry in Hzsm.
  rewrite Hu in Hzsm.
  progress unfold seq_angle_to_div_nat in Hzsm.
  rewrite Hzsm.
  destruct zsm; [ | easy ].
  apply rngl_leb_le in Hzsm.
  apply (rngl_ltb_ge Hor).
  rewrite <- angle_mul_2_l in Hzsm |-*.
  rewrite rngl_sin_mul_2_l in Hzsm.
  rewrite rngl_cos_mul_2_l'.
  apply (rngl_le_0_mul Hop Hiq Hto) in Hzsm.
  remember (rngl_cos (u i)) as x eqn:Hx.
  rewrite Hu in Hx.
  progress unfold seq_angle_to_div_nat in Hx.
  rewrite <- Hx.
  destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
    destruct (rngl_eqb_dec (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
      apply (rngl_eqb_eq Heo) in Hxz.
      rewrite Hu in Hxz.
      progress unfold seq_angle_to_div_nat in Hxz.
      apply eq_rngl_sin_0 in Hxz.
      destruct Hxz as [Hxz| Hxz]. {
        rewrite Hxz in Hx; cbn in Hx; subst x.
        exfalso; apply (rngl_nlt_ge Hor) in H2.
        apply H2; clear H2.
        rewrite Hxz.
        apply (rngl_0_lt_1 Hos Hc1 Hto).
      } {
        rewrite Hxz in Hx; cbn in Hx; subst x.
        exfalso; clear H1 H2 Hzs.
        revert Hxz.
        apply fold_not.
        destruct n; [ easy | clear Hnz ].
        apply Nat.succ_lt_mono in Hmi.
        destruct n; [ flia Hmi | clear Hmi ].
        destruct n. {
          destruct i; [ cbn in Hni; flia Hni | ].
          rewrite Nat.pow_succ_r'.
          rewrite Nat.mul_comm.
          rewrite Nat.div_mul; [ | easy ].
          rewrite angle_div_2_pow_succ_r_2.
          rewrite angle_div_2_pow_mul_2_pow.
          now apply (angle_div_2_not_straight Hc1).
        }
        destruct i; [ cbn in Hni; flia Hni | ].
        rewrite angle_div_2_pow_succ_r_2.
        specialize angle_div_2_pow_mul_le_angle as H1.
        specialize (H1 (2 ^ S i / S (S (S n))) i (θ /₂)%A).
        assert (H : 2 ^ S i / S (S (S n)) ≤ 2 ^ i). {
          rewrite Nat.pow_succ_r'.
          apply Nat.Div0.div_le_upper_bound.
          apply Nat.mul_le_mono_r.
          now do 2 apply -> Nat.succ_le_mono.
        }
        specialize (H1 H); clear H.
        intros Hxz.
        rewrite Hxz in H1.
        apply angle_nlt_ge in H1.
        apply H1.
        apply (angle_div_2_lt_straight Hc1).
      }
    }
    apply (rngl_eqb_neq Heo) in Hxz.
    exfalso.
    rewrite Hu in Hxz.
    progress unfold seq_angle_to_div_nat in Hxz.
    apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
    apply (rngl_mul_le_mono_pos_l Hop Hiq Hto 2). {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    now rewrite rngl_mul_0_r.
  }
  (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
  apply (rngl_2_x2_sub_1_le_x Hop Hiq Hto).
  rewrite <- Hx in Hzsm.
  split; [ easy | ].
  subst x; apply rngl_cos_bound.
}
apply (rngl_leb_gt_iff Hto) in Hzs.
apply (rngl_nle_gt Hor) in Hzs.
exfalso.
apply Hzs; clear Hzs.
destruct i; [ cbn in Hni; flia Hni Hmi | ].
apply rngl_sin_nonneg_angle_le_straight.
apply angle_mul_div_pow2_le_straight.
eapply Nat.le_trans; [ now apply Nat.Div0.div_mul_le | ].
apply Nat.Div0.div_le_upper_bound.
now apply Nat.mul_le_mono_r.
Qed.

Theorem rngl_mul_if_then_else_distr_l :
  ∀ (v : bool) a b c,
  ((a * if v then b else c) = (if v then a * b else a * c))%L.
Proof. now intros; destruct v. Qed.

Theorem rngl_add_if_then_else_distr_r :
  ∀ (v : bool) a b c,
  ((if v then a else b) + c = if v then a + c else b + c)%L.
Proof. intros; now destruct v. Qed.

Theorem rngl_if_then_else_eq_compat :
  ∀ {A} (u : bool) (a b c d : A),
  (u = true → a = c)
  → (u = false → b = d)
  → ((if u then a else b) = (if u then c else d))%L.
Proof.
intros * Ht Hf.
now destruct u; [ apply Ht | apply Hf ].
Qed.

Theorem gre_summation :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ b e (f : nat → GComplex T),
  gre (∑ (i = b, e), f i)%L = (∑ (i = b, e), gre (f i))%L.
Proof.
intros Hic Hop.
intros.
progress unfold iter_seq.
progress unfold iter_list.
remember (S e - b) as len eqn:Hlen.
clear e Hlen.
cbn.
revert b.
induction len; intros; [ easy | cbn ].
rewrite fold_left_rngl_add_fun_from_0.
rewrite rngl_add_0_l.
rewrite <- IHlen.
rewrite fold_left_op_fun_from_d with (d := 0%L); cycle 1.
apply gc_add_0_l.
intros; cbn.
specialize gc_add_comm as H1; cbn in H1.
rewrite H1; clear H1.
apply gc_add_0_l.
apply gc_add_assoc.
cbn.
f_equal.
apply rngl_add_0_l.
Qed.

Theorem gim_summation :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ b e (f : nat → GComplex T),
  gim (∑ (i = b, e), f i)%L = (∑ (i = b, e), gim (f i))%L.
Proof.
intros Hic Hop.
intros.
progress unfold iter_seq.
progress unfold iter_list.
remember (S e - b) as len eqn:Hlen.
clear e Hlen.
cbn.
revert b.
induction len; intros; [ easy | cbn ].
rewrite fold_left_rngl_add_fun_from_0.
rewrite rngl_add_0_l.
rewrite <- IHlen.
rewrite fold_left_op_fun_from_d with (d := 0%L); cycle 1.
apply gc_add_0_l.
intros; cbn.
specialize gc_add_comm as H1; cbn in H1.
rewrite H1; clear H1.
apply gc_add_0_l.
apply gc_add_assoc.
cbn.
f_equal.
apply rngl_add_0_l.
Qed.

Theorem gre_1 : (gre 1 = 1%L).
Proof. easy. Qed.

Theorem gim_1 : (gim 1 = 0%L).
Proof. easy. Qed.

Theorem gc_pow_re_0 :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ n y,
  (mk_gc 0 y ^ n =
     if Nat.even n then
       mk_gc ((minus_one_pow (n / 2)) * (y ^ n))%L 0
     else
       mk_gc 0 ((minus_one_pow (n / 2)) * (y ^ n))%L)%C.
Proof.
intros Hic Hop.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
remember (Nat.even n) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply Nat.even_spec in Hb.
  destruct Hb as (m, Hm).
  subst n.
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
  progress unfold gc_pow_nat.
  induction m; cbn. {
    rewrite rngl_mul_1_l.
    now apply eq_gc_eq.
  }
  rewrite IHm.
  progress unfold gc_mul.
  cbn.
  do 4 rewrite (rngl_mul_0_l Hos).
  do 2 rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_mul_0_r Hos).
  do 2 rewrite rngl_add_0_r.
  rewrite (rngl_opp_0 Hop).
  rewrite (rngl_mul_0_r Hos).
  f_equal.
  do 4 rewrite rngl_mul_assoc.
  rewrite <- (rngl_mul_opp_l Hop).
  f_equal.
  rewrite (rngl_mul_comm Hic).
  rewrite <- (rngl_mul_opp_l Hop).
  rewrite <- rngl_mul_assoc.
  f_equal.
  symmetry.
  apply (minus_one_pow_succ Hop).
} {
  destruct n; [ easy | ].
  apply (f_equal negb) in Hb.
  rewrite Nat.even_succ in Hb.
  cbn in Hb.
  rewrite Nat.negb_odd in Hb.
  apply Nat.even_spec in Hb.
  destruct Hb as (m, Hm).
  subst n.
  rewrite <- Nat.add_1_r.
  rewrite Nat.mul_comm, Nat.div_add_l; [ | easy ].
  rewrite Nat.div_small; [ | easy ].
  rewrite Nat.add_0_r.
  progress unfold gc_pow_nat.
  induction m; cbn. {
    rewrite rngl_mul_1_l.
    rewrite rngl_mul_1_r.
    apply eq_gc_eq; cbn.
    do 2 rewrite (rngl_mul_0_l Hos).
    rewrite (rngl_mul_0_r Hos).
    rewrite (rngl_sub_0_r Hos).
    rewrite rngl_mul_1_r.
    rewrite rngl_add_0_r.
    easy.
  }
  rewrite IHm.
  progress unfold gc_mul.
  cbn.
  do 4 rewrite (rngl_mul_0_l Hos).
  do 2 rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_mul_0_r Hos).
  do 2 rewrite rngl_add_0_r.
  rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_opp_0 Hop).
  f_equal.
  rewrite <- (rngl_mul_opp_r Hop).
  rewrite <- (rngl_mul_opp_l Hop).
  do 4 rewrite rngl_mul_assoc.
  f_equal.
  rewrite (rngl_mul_comm Hic).
  rewrite <- rngl_mul_assoc.
  f_equal.
  symmetry.
  apply (minus_one_pow_succ Hop).
}
Qed.

Theorem gre_rngl_of_nat : ∀ n, gre (rngl_of_nat n) = rngl_of_nat n.
Proof.
intros.
induction n; [ easy | ].
do 2 rewrite rngl_of_nat_succ.
now cbn; rewrite IHn.
Qed.

Theorem gim_rngl_of_nat : ∀ n, gim (rngl_of_nat n) = 0%L.
Proof.
intros.
induction n; [ easy | ].
rewrite rngl_of_nat_succ.
cbn; rewrite IHn.
apply rngl_add_0_l.
Qed.

Theorem rngl_cos_sin_nx :
  ∀ n θ,
  rngl_cos (n * θ) =
    (∑ (i = 0, n),
       if Nat.even i then
         minus_one_pow (i / 2) * rngl_of_nat (binomial n i) *
         (rngl_cos θ) ^ (n - i) * (rngl_sin θ) ^ i
       else 0)%L ∧
  rngl_sin (n * θ) =
    (∑ (i = 0, n),
       if Nat.odd i then
         minus_one_pow (i / 2) * rngl_of_nat (binomial n i) *
         (rngl_cos θ) ^ (n - i) * (rngl_sin θ) ^ i
       else 0)%L.
Proof.
destruct_ac.
intros.
specialize (@newton_binomial) as H1.
set (gro := gc_ring_like_op T).
set (grp := gc_ring_like_prop_not_alg_closed Hic Hop Hiv Hto).
specialize (H1 (GComplex T)).
specialize (H1 gro grp).
assert (Hosc : rngl_has_opp_or_psub (GComplex T) = true). {
  progress unfold rngl_has_opp_or_psub in Hos.
  progress unfold rngl_has_opp_or_psub.
  cbn.
  progress unfold gc_opt_opp_or_psub.
  generalize Hos; intros Hos'; clear Hos.
  destruct (rngl_opt_opp_or_psub T) as [s| ]; [ | easy ].
  now destruct s.
}
specialize (H1 Hic Hosc n).
specialize (H1 (mk_gc (rngl_cos θ) 0)).
specialize (H1 (mk_gc 0 (rngl_sin θ))).
cbn - [ rngl_add rngl_zero ] in H1.
remember (∑ (k = _, _), _) as x in H1.
cbn in H1; subst x.
progress unfold gc_add in H1.
cbn - [ rngl_add rngl_zero ] in H1.
rewrite rngl_add_0_r in H1.
rewrite rngl_add_0_l in H1.
progress unfold gro in H1.
specialize (gc_cos_sin_pow θ n) as H2.
progress unfold gc_pow_nat in H2.
rewrite H2 in H1; clear H2.
apply eq_gc_eq in H1.
cbn - [ rngl_add rngl_zero ] in H1.
rewrite (gre_summation Hic Hop) in H1.
rewrite (gim_summation Hic Hop) in H1.
destruct H1 as (Hc, Hs).
split. {
  rewrite Hc.
  apply rngl_summation_eq_compat.
  intros * (_, Hi).
  specialize (gc_pow_im_0 Hos) as H1.
  progress unfold gc_pow_nat in H1.
  rewrite H1.
  specialize (gc_pow_re_0 Hic Hop) as H2.
  progress unfold gc_pow_nat in H2.
  rewrite H2.
  cbn - [ "/" ].
  do 2 rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_sub_0_r Hos).
  rewrite rngl_add_0_r.
  rewrite gre_rngl_of_nat.
  rewrite gim_rngl_of_nat.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_sub_0_r Hos).
  remember (Nat.even i) as ei eqn:Hei.
  symmetry in Hei.
  destruct ei. {
    cbn - [ "/" "*" ].
    rewrite rngl_mul_assoc.
    f_equal.
    rewrite (rngl_mul_comm Hic).
    apply rngl_mul_assoc.
  } {
    cbn - [ "/" "*" ].
    apply (rngl_mul_0_r Hos).
  }
} {
  rewrite Hs.
  apply rngl_summation_eq_compat.
  intros * (_, Hi).
  cbn - [ "/" "*" ].
  rewrite gre_rngl_of_nat.
  rewrite gim_rngl_of_nat.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_sub_0_r Hos).
  rewrite rngl_add_0_l.
  specialize (gc_pow_im_0 Hos) as H1.
  progress unfold gc_pow_nat in H1.
  rewrite H1.
  specialize (gc_pow_re_0 Hic Hop) as H2.
  progress unfold gc_pow_nat in H2.
  rewrite H2.
  cbn - [ "/" ].
  rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_mul_0_l Hos).
  rewrite rngl_add_0_l.
  rewrite <- Nat.negb_even.
  remember (Nat.even i) as ei eqn:Hei.
  symmetry in Hei.
  destruct ei. {
    cbn - [ "/" "*" ].
    apply (rngl_mul_0_r Hos).
  } {
    cbn - [ "/" "*" ].
    rewrite rngl_mul_assoc.
    f_equal.
    rewrite (rngl_mul_comm Hic).
    apply rngl_mul_assoc.
  }
}
Qed.

Theorem rngl_cos_nx :
  ∀ n θ,
  rngl_cos (n * θ) =
    (∑ (i = 0, n),
       if Nat.even i then
         minus_one_pow (i / 2) * rngl_of_nat (binomial n i) *
         (rngl_cos θ) ^ (n - i) * (rngl_sin θ) ^ i
       else 0)%L.
Proof.
intros.
apply rngl_cos_sin_nx.
Qed.

Theorem rngl_sin_nx :
  ∀ n θ,
  rngl_sin (n * θ) =
    (∑ (i = 0, n),
       if Nat.odd i then
         minus_one_pow (i / 2) * rngl_of_nat (binomial n i) *
         (rngl_cos θ) ^ (n - i) * (rngl_sin θ) ^ i
       else 0)%L.
Proof.
intros.
apply rngl_cos_sin_nx.
Qed.

Theorem angle_right_div_2_lt :
  ∀ θ,
  (rngl_cos θ < rngl_sin θ)%L
  → (0 ≤ rngl_sin θ)%L
  → (0 ≤ rngl_cos θ)%L
  → (angle_right /₂ < θ)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hcs Hs Hc.
  rewrite (H1 (rngl_cos _)) in Hcs.
  rewrite (H1 (rngl_sin _)) in Hcs.
  now apply rngl_lt_irrefl in Hcs.
}
intros * Hcs Hs Hc.
progress unfold angle_ltb.
cbn.
rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
apply rngl_leb_le in Hs; rewrite Hs.
apply rngl_leb_le in Hs.
specialize (rngl_0_le_1 Hos Hto) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
rewrite rngl_mul_1_l.
specialize rl_sqrt_half_nonneg as Hzs.
generalize Hzs; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply (rngl_ltb_lt Heo).
specialize (rngl_cos_div_2 angle_right) as H1.
cbn - [ rngl_cos ] in H1.
specialize (rngl_0_le_1 Hos Hto) as H2.
apply rngl_leb_le in H2.
rewrite H2 in H1; clear H2.
rewrite rngl_mul_1_l in H1.
cbn - [ angle_div_2 ] in H1.
rewrite rngl_add_0_r in H1.
rewrite <- H1.
apply quadrant_1_sin_sub_pos_cos_lt; try easy. {
  now rewrite rngl_sin_right_div_2.
} {
  now rewrite rngl_cos_right_div_2.
} {
  cbn - [ angle_div_2 ].
  rewrite rngl_sin_right_div_2.
  rewrite rngl_cos_right_div_2.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hiq Hto). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  apply (rl_sqrt_half_pos Hc1).
}
Qed.

Theorem rngl_sin_7_right_div_2 :
  rngl_sin (7 * (angle_right /₂)) = (- √(1 / 2))%L.
Proof.
replace 7 with (2 + 5) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite rngl_sin_add_right_l.
apply rngl_cos_5_right_div_2.
Qed.

Theorem rngl_cos_7_right_div_2 :
  rngl_cos (7 * (angle_right /₂)) = √(1 / 2)%L.
Proof.
destruct_ac.
replace 7 with (2 + 5) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite rngl_cos_add_right_l.
apply (rngl_opp_inj Hop).
rewrite (rngl_opp_involutive Hop).
apply rngl_sin_5_right_div_2.
Qed.

Theorem quadrant_1_angle_lt_3_angle_right_div_2 :
  rngl_characteristic T ≠ 1 →
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → (0 ≤ rngl_cos θ)%L
  → (θ < 3 * (angle_right /₂))%A.
Proof.
destruct_ac.
intros Hc1 * Hs Hc.
progress unfold angle_ltb.
apply rngl_leb_le in Hs.
rewrite Hs.
apply rngl_leb_le in Hs.
rewrite rngl_sin_3_right_div_2.
rewrite rngl_cos_3_right_div_2.
specialize rl_sqrt_half_nonneg as Hzs.
generalize Hzs; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply (rngl_ltb_lt Heo).
apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
apply (rngl_opp_neg_pos Hop Hto).
apply (rl_sqrt_half_pos Hc1).
Qed.

Theorem quadrant_4_angle_lt_5_angle_right_div_2 :
  ∀ θ,
  (rngl_sin θ < 0)%L
  → (0 ≤ rngl_cos θ)%L
  → (5 * (angle_right /₂) < θ)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hs Hc.
  rewrite (H1 (rngl_sin _)) in Hs.
  now apply rngl_lt_irrefl in Hs.
}
intros * Hs Hc.
progress unfold angle_ltb.
rewrite rngl_sin_5_right_div_2.
rewrite rngl_cos_5_right_div_2.
rewrite (rngl_leb_0_opp Hop Hto).
generalize Hs; intros H.
apply (rngl_leb_gt_iff Hto) in H.
rewrite H; clear H.
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz; [ easy | ].
apply (rngl_ltb_lt Heo).
apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
apply (rngl_opp_neg_pos Hop Hto).
apply (rl_sqrt_half_pos Hc1).
Qed.

Theorem quadrant_3_angle_lt_5_angle_right_div_2 :
  ∀ θ,
  (rngl_sin θ < rngl_cos θ)%L
  → (rngl_sin θ < 0)%L
  → (rngl_cos θ < 0)%L
  → (5 * (angle_right /₂) < θ)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hsc Hs Hc.
  rewrite (H1 (rngl_sin _)), (H1 (rngl_cos _)) in Hsc.
  now apply rngl_lt_irrefl in Hsc.
}
intros * Hsc Hs Hc.
progress unfold angle_ltb.
rewrite rngl_sin_5_right_div_2.
rewrite (rngl_leb_0_opp Hop Hto).
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz. {
  exfalso.
  apply rngl_leb_le in Hsz.
  apply (rngl_nlt_ge Hor) in Hsz.
  apply Hsz; clear Hsz.
  apply (rl_sqrt_half_pos Hc1).
}
apply (rngl_leb_gt_iff Hto) in Hs.
rewrite Hs.
apply (rngl_leb_gt_iff Hto) in Hs.
apply (rngl_ltb_lt Heo).
rewrite rngl_cos_5_right_div_2.
change_angle_add_r θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hc.
progress sin_cos_add_sub_straight_hyp T Hs.
progress sin_cos_add_sub_straight_hyp T Hsc.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_0_sub Hop Hor).
rewrite <- rngl_cos_right_div_2.
apply quadrant_1_sin_sub_pos_cos_lt; try easy. {
  now apply rngl_lt_le_incl in Hs.
} {
  apply rngl_sin_div_2_nonneg.
} {
  apply rngl_cos_div_2_nonneg; cbn.
  apply (rngl_0_le_1 Hos Hto).
} {
  cbn.
  specialize (rngl_0_le_1 Hos Hto) as H2.
  apply rngl_leb_le in H2.
  rewrite H2; clear H2.
  rewrite rngl_mul_1_l.
  rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hiq Hto). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  apply (rl_sqrt_half_pos Hc1).
}
Qed.

Theorem quadrant_4_angle_lt_7_angle_right_div_2 :
  ∀ θ,
  (rngl_cos θ < - rngl_sin θ)%L
  → (rngl_sin θ < 0)%L
  → (0 ≤ rngl_cos θ)%L
  → (θ < 7 * (angle_right /₂))%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hcs Hs Hc.
  rewrite (H1 (rngl_sin _)) in Hs.
  now apply rngl_lt_irrefl in Hs.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hcs Hs Hc.
progress unfold angle_ltb.
generalize Hs; intros H.
apply (rngl_leb_gt_iff Hto) in H.
rewrite H; clear H.
rewrite rngl_sin_7_right_div_2.
rewrite rngl_cos_7_right_div_2.
rewrite (rngl_leb_0_opp Hop Hto).
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz. {
  exfalso.
  apply rngl_leb_le in Hsz.
  apply (rngl_nlt_ge Hor) in Hsz.
  apply Hsz; clear Hsz.
  apply (rl_sqrt_half_pos Hc1).
}
apply (rngl_ltb_lt Heo).
change_angle_opp θ.
progress sin_cos_opp_hyp T Hc.
progress sin_cos_opp_hyp T Hs.
progress sin_cos_opp_hyp T Hcs.
rewrite (rngl_opp_involutive Hop) in Hcs.
cbn.
rewrite <- rngl_cos_right_div_2.
apply quadrant_1_sin_sub_pos_cos_lt; try easy. {
  now apply rngl_lt_le_incl in Hs.
} {
  now rewrite rngl_sin_right_div_2.
} {
  now rewrite rngl_cos_right_div_2.
} {
  cbn.
  specialize (rngl_0_le_1 Hos Hto) as H2.
  apply rngl_leb_le in H2.
  rewrite H2; clear H2.
  rewrite rngl_mul_1_l.
  rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hiq Hto). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  apply (rl_sqrt_half_pos Hc1).
}
Qed.

Theorem quadrant_2_angle_right_div_2_lt :
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → (rngl_cos θ < 0)%L
  → (angle_right /₂ < θ)%A.
Proof.
destruct_ac.
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hs Hc.
progress unfold angle_ltb.
specialize (rngl_sin_div_2_nonneg angle_right) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
apply rngl_leb_le in Hs.
rewrite Hs.
apply rngl_leb_le in Hs.
apply (rngl_ltb_lt Heo); cbn.
specialize (rngl_0_le_1 Hos Hto) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
rewrite rngl_mul_1_l.
rewrite rngl_add_0_r.
now apply (rngl_lt_le_trans Hor _ 0).
Qed.

Theorem quadrant_2_angle_lt_3_angle_right_div_2 :
  ∀ θ,
  (- rngl_cos θ < rngl_sin θ)%L
  → (0 ≤ rngl_sin θ)%L
  → (rngl_cos θ < 0)%L
  → (θ < 3 * (angle_right /₂))%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hcs Hs Hc.
  rewrite (H1 (- _)%L), (H1 (rngl_sin _)) in Hcs.
  now apply rngl_lt_irrefl in Hcs.
}
intros * Hcs Hs Hc.
specialize rl_sqrt_half_nonneg as Hzs.
progress unfold angle_ltb.
apply rngl_leb_le in Hs.
rewrite Hs.
apply rngl_leb_le in Hs.
rewrite rngl_sin_3_right_div_2.
rewrite rngl_cos_3_right_div_2.
generalize Hzs; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply (rngl_ltb_lt Heo).
change_angle_sub_l θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hc.
progress sin_cos_add_sub_straight_hyp T Hs.
progress sin_cos_add_sub_straight_hyp T Hcs.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_0_sub Hop Hor).
specialize (rngl_cos_div_2 angle_right) as H1.
cbn - [ rngl_cos ] in H1.
specialize (rngl_0_le_1 Hos Hto) as H2.
apply rngl_leb_le in H2.
rewrite H2 in H1; clear H2.
rewrite rngl_mul_1_l in H1.
cbn - [ angle_div_2 ] in H1.
rewrite rngl_add_0_r in H1.
rewrite <- H1.
apply quadrant_1_sin_sub_pos_cos_lt; try easy. {
  now rewrite rngl_sin_right_div_2.
} {
  now rewrite rngl_cos_right_div_2.

} {
  cbn - [ angle_div_2 ].
  rewrite rngl_sin_right_div_2.
  rewrite rngl_cos_right_div_2.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hiq Hto). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  apply (rl_sqrt_half_pos Hc1).
}
Qed.

Theorem quadrant_3_angle_lt_7_angle_right_div_2 :
  ∀ θ,
  (rngl_sin θ < 0)%L
  → (rngl_cos θ < 0)%L
  → (θ < 7 * (angle_right /₂))%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hs Hc.
  rewrite (H1 (rngl_sin _)) in Hs.
  now apply rngl_lt_irrefl in Hs.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hs Hc.
change_angle_add_r θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hc.
progress sin_cos_add_sub_straight_hyp T Hs.
progress unfold angle_ltb.
rewrite rngl_sin_sub_straight_r.
rewrite (rngl_leb_0_opp Hop Hto).
generalize Hs; intros H.
apply (rngl_leb_gt_iff Hto) in H.
rewrite H; clear H.
rewrite rngl_sin_7_right_div_2.
rewrite (rngl_leb_0_opp Hop Hto).
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz. {
  exfalso.
  apply rngl_leb_le in Hsz.
  apply (rngl_nlt_ge Hor) in Hsz.
  apply Hsz; clear Hsz.
  apply (rl_sqrt_half_pos Hc1).
}
apply (rngl_ltb_lt Heo).
rewrite rngl_cos_sub_straight_r.
rewrite rngl_cos_7_right_div_2.
apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
now apply (rngl_opp_neg_pos Hop Hto).
Qed.

Theorem rngl_cos_mul_2_neg_if :
  ∀ θ,
  (rngl_cos (2 * θ) < 0)%L
  → (angle_right /₂ < θ < 3 * (angle_right /₂))%A ∨
    (5 * (angle_right /₂) < θ < 7 * (angle_right /₂))%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * H2.
  rewrite (H1 (rngl_cos _)) in H2.
  now apply rngl_lt_irrefl in H2.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hcz.
rewrite rngl_cos_mul_2_l in Hcz.
apply -> (rngl_lt_sub_0 Hop Hto) in Hcz.
apply (rngl_squ_lt_abs_lt Hop Hiq Hto) in Hcz.
destruct (rngl_leb_dec 0 (rngl_sin θ)) as [Hs| Hs]. {
  apply rngl_leb_le in Hs.
  rewrite (rngl_abs_nonneg_eq Hop Hor (rngl_sin _)) in Hcz; [ | easy ].
  left.
  destruct (rngl_leb_dec 0 (rngl_cos θ)) as [Hc| Hc]. {
    apply rngl_leb_le in Hc.
    rewrite (rngl_abs_nonneg_eq Hop Hor (rngl_cos _)) in Hcz; [ | easy ].
    split; [ now apply angle_right_div_2_lt | ].
    now apply quadrant_1_angle_lt_3_angle_right_div_2.
  } {
    apply rngl_leb_nle in Hc.
    apply (rngl_nle_gt_iff Hto) in Hc.
    rewrite (rngl_abs_nonpos_eq Hop Hto) in Hcz. 2: {
      now apply rngl_lt_le_incl in Hc.
    }
    split. {
      now apply quadrant_2_angle_right_div_2_lt.
    } {
      now apply quadrant_2_angle_lt_3_angle_right_div_2.
    }
  }
} {
  apply rngl_leb_nle in Hs.
  apply (rngl_nle_gt_iff Hto) in Hs.
  rewrite (rngl_abs_nonpos_eq Hop Hto (rngl_sin _)) in Hcz. 2: {
    now apply rngl_lt_le_incl in Hs.
  }
  right.
  destruct (rngl_leb_dec 0 (rngl_cos θ)) as [Hc| Hc]. {
    apply rngl_leb_le in Hc.
    rewrite (rngl_abs_nonneg_eq Hop Hor (rngl_cos _)) in Hcz; [ | easy ].
    split. {
      now apply quadrant_4_angle_lt_5_angle_right_div_2.
    } {
      now apply quadrant_4_angle_lt_7_angle_right_div_2.
    }
  }
  apply rngl_leb_nle in Hc.
  apply (rngl_nle_gt_iff Hto) in Hc.
  rewrite (rngl_abs_nonpos_eq Hop Hto) in Hcz. 2: {
    now apply rngl_lt_le_incl in Hc.
  }
  apply (rngl_opp_lt_compat Hop Hto) in Hcz.
  split. {
    now apply quadrant_3_angle_lt_5_angle_right_div_2.
  } {
    now apply quadrant_3_angle_lt_7_angle_right_div_2.
  }
}
Qed.

Theorem rngl_sin_mul_2_neg_if :
  ∀ θ,
  (rngl_sin (2 * θ) < 0)%L
  → (angle_right < θ < angle_straight)%A ∨
    (3 * angle_right < θ)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * H2.
  rewrite (H1 (rngl_sin _)) in H2.
  now apply rngl_lt_irrefl in H2.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hsz.
rewrite rngl_sin_mul_2_l in Hsz.
apply (rngl_lt_mul_0_if Hos Hto) in Hsz.
destruct Hsz as [(H2sz, Hzc)| (Hz2s, Hcz)]. {
  apply (rngl_lt_mul_0_if Hos Hto) in H2sz.
  destruct H2sz as [(H, _)| (_, Hcz)]. {
    exfalso.
    apply (rngl_nle_gt Hor) in H.
    apply H; clear H.
    apply (rngl_0_le_2 Hos Hto).
  }
  right.
  change_angle_opp θ.
  progress sin_cos_opp_hyp T Hzc.
  progress sin_cos_opp_hyp T Hcz.
  rewrite <- (angle_opp_involutive (_ * _)).
  apply angle_opp_lt_compat_if. {
    intros H; subst θ.
    now apply rngl_lt_irrefl in Hcz.
  }
  progress unfold angle_ltb.
  cbn - [ angle_mul_nat ].
  generalize Hcz; intros H.
  apply rngl_lt_le_incl in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  rewrite (rngl_leb_0_opp Hop Hto).
  remember (rngl_sin (_ * _) ≤? 0)%L as s3 eqn:Hs3.
  symmetry in Hs3.
  destruct s3; [ | easy ].
  apply (rngl_ltb_lt Heo).
  apply (rngl_le_lt_trans Hor _ 0); [ | easy ].
  cbn.
  do 3 rewrite (rngl_mul_0_l Hos).
  do 2 rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_opp_0 Hop).
  rewrite rngl_add_0_r.
  do 2 rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_opp_0 Hop).
  apply (rngl_le_refl Hor).
}
apply (rngl_mul_pos_cancel_l Hop Hiq Hto) in Hz2s. 2: {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
left.
change_angle_sub_r θ angle_right.
progress sin_cos_add_sub_right_hyp T Hcz.
progress sin_cos_add_sub_right_hyp T Hz2s.
split. {
  progress unfold angle_ltb.
  rewrite rngl_sin_add_right_r.
  rewrite rngl_cos_add_right_r.
  cbn.
  specialize (rngl_0_le_1 Hos Hto) as H2.
  apply rngl_leb_le in H2.
  rewrite H2.
  generalize Hz2s; intros H.
  apply rngl_lt_le_incl in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply (rngl_ltb_lt Heo).
  now apply (rngl_opp_neg_pos Hop Hto).
}
apply angle_lt_iff.
split. {
  progress unfold angle_leb.
  rewrite rngl_sin_add_right_r.
  rewrite rngl_cos_add_right_r.
  generalize Hz2s; intros H.
  apply rngl_lt_le_incl in H.
  apply rngl_leb_le in H.
  rewrite H; clear H; cbn.
  rewrite (rngl_leb_refl Hor).
  rewrite (rngl_leb_opp_r Hop Hto).
  rewrite (rngl_opp_involutive Hop).
  apply rngl_leb_le.
  apply rngl_sin_bound.
}
intros H.
apply angle_add_move_r in H.
rewrite angle_straight_sub_right in H.
subst θ.
now apply rngl_lt_irrefl in Hz2s.
Qed.

Theorem rngl_cos_div_pow2_2_pos :
  rngl_characteristic T ≠ 1 →
  ∀ θ, (0 < rngl_cos (θ /₂^2))%L.
Proof.
destruct_ac.
intros Hc1 *.
rewrite angle_div_2_pow_succ_r_1.
cbn - [ angle_div_2_pow ].
remember (0 ≤? _)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. 2: {
  exfalso.
  apply Bool.not_true_iff_false in Hzs.
  apply Hzs; clear Hzs.
  apply rngl_leb_le.
  apply rl_sqrt_nonneg.
  apply rngl_1_sub_cos_div_2_nonneg.
}
rewrite rngl_mul_1_l.
(* lemma to do, perhaps *)
apply rngl_le_neq.
split. {
  apply rl_sqrt_nonneg.
  apply rngl_1_add_cos_div_2_nonneg.
}
intros H; symmetry in H.
apply (eq_rl_sqrt_0 Hos) in H. 2: {
  apply (rngl_div_nonneg Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply (rngl_le_opp_l Hop Hto).
  apply rngl_cos_bound.
}
(* lemma? *)
apply (f_equal (λ a, rngl_mul a 2)) in H.
rewrite (rngl_div_mul Hiv) in H. 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
rewrite (rngl_mul_0_l Hos) in H.
(* lemma? *)
rewrite rngl_add_comm in H.
apply (rngl_add_move_0_r Hop) in H.
apply eq_rngl_cos_opp_1 in H.
cbn in H.
now apply (angle_div_2_not_straight Hc1) in H.
Qed.

Theorem rngl_cos_div_pow2_2_nonneg :
  ∀ θ, (0 ≤ rngl_cos (θ /₂^2))%L.
Proof.
destruct_ac.
intros.
rewrite angle_div_2_pow_succ_r_1.
cbn - [ angle_div_2_pow ].
remember (0 ≤? _)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. 2: {
  exfalso.
  apply Bool.not_true_iff_false in Hzs.
  apply Hzs; clear Hzs.
  apply rngl_leb_le.
  apply rl_sqrt_nonneg.
  apply rngl_1_sub_cos_div_2_nonneg.
}
rewrite rngl_mul_1_l.
apply rl_sqrt_nonneg.
apply rngl_1_add_cos_div_2_nonneg.
Qed.

Theorem rngl_cos_div_pow2_nonneg :
  ∀ n θ, 2 ≤ n → (0 ≤ rngl_cos (θ /₂^n))%L.
Proof.
intros * H2n.
destruct n; [ easy | ].
rewrite angle_div_2_pow_succ_r_1.
apply rngl_cos_div_2_nonneg.
apply Nat.succ_le_mono in H2n.
destruct n; [ easy | clear H2n ].
rewrite angle_div_2_pow_succ_r_1.
apply rngl_sin_div_2_nonneg.
Qed.

Theorem angle_div_2_pow_mul_pow_sub :
  ∀ i j θ, j ≤ i → (2 ^ (i - j) * (θ /₂^i) = θ /₂^j)%A.
Proof.
intros * Hji.
replace i with (j + (i - j)) at 1 by flia Hji.
rewrite angle_div_2_pow_add_r.
apply angle_div_2_pow_mul_2_pow.
Qed.

(* first n binary digits of a/b with a≤b *)
Fixpoint binary_div n a b :=
  match n with
  | 0 => []
  | S n' => a / b :: binary_div n' (2 * (a mod b)) b
  end.

Fixpoint old_rank_fst_loop it k a b :=
  match it with
  | 0 => (0, 0)
  | S it' =>
      if a / b =? k then (0, a)
      else
        let (r, a') := old_rank_fst_loop it' k (2 * (a mod b)) b in
        (S r, a')
  end.

Definition old_rank_fst_0 a b := fst (old_rank_fst_loop b 0 a b).
Definition old_rank_fst_1 a b := fst (old_rank_fst_loop b 1 a b).

(* work only if a < b *)
(* "a" recursively remains less than "b" *)
Fixpoint rank_fst_loop it k a b :=
  match it with
  | 0 => (0, 0)
  | S it' =>
      if 2 * a / b =? k then (0, a)
      else
        let (r, a') := rank_fst_loop it' k ((2 * a) mod b) b in
        (S r, a')
  end.

Fixpoint new_rank_fst_loop it a b :=
  match it with
  | 0 => 0
  | S it' =>
      if 2 * a / b =? 0 then 0
      else S (new_rank_fst_loop it' ((2 * a) mod b) b)
  end.

(* rank starting at 0 for the first binary digit of a/b with a<b *)
Definition rank_fst_0 a b := fst (rank_fst_loop b 0 a b).
Definition rank_fst_1 a b := fst (rank_fst_loop b 1 a b).
Definition fst_1_len a b :=
  fst (rank_fst_loop b 0 (snd (rank_fst_loop b 1 a b)) b).
Definition new_fst_1_len b :=
  new_rank_fst_loop b (2 ^ (Nat.log2_up b - 1) mod b) b.

Definition inv_ub_num n := 2 ^ S (fst_1_len 1 n) - 1.
Definition inv_ub_den_pow2 n := rank_fst_1 1 n + fst_1_len 1 n + 1.

Definition rank_fst_1_inv n := Nat.log2_up n - 1.
(*
Compute (map (λ n, (n, inv_ub_num n, inv_ub_den_pow2 n)) (seq 1 10)).
Compute (map (λ n, (n, rank_fst_1 1 n, rank_fst_1_inv n)) (seq 1 66)).
Compute (map (λ n, (n, rank_fst_1 1 n, rank_fst_1_inv n)) [3;5;6;7]).
Compute (map (λ n, (n, inv_ub_num n, inv_ub_den_pow2 n)) [3;4;5;6;7;9]).
Compute
  (map (λ n, (inv_ub_num n, 2 ^ inv_ub_den_pow2 n / n + 1)) (seq 1 50)).
*)

Theorem fst_let :
  ∀ B C D E (a : B * C) (f : B → D) (g : C → E),
  fst (let (b, c) := a in (f b, g c)) = f (fst a).
Proof. now intros; destruct a. Qed.

Theorem fst_if :
  ∀ B C (a : bool) (b c : B * C),
  fst (if a then b else c) = if a then fst b else fst c.
Proof. now intros; destruct a. Qed.

Theorem snd_let :
  ∀ B C D E (a : B * C) (f : B → D) (g : C → E),
  snd (let (b, c) := a in (f b, g c)) = g (snd a).
Proof. now intros; destruct a. Qed.

Theorem snd_if :
  ∀ B C (a : bool) (b c : B * C),
  snd (if a then b else c) = if a then snd b else snd c.
Proof. now intros; destruct a. Qed.

Theorem fold_rank_fst_0 :
  ∀ a b, fst (rank_fst_loop b 0 a b) = rank_fst_0 a b.
Proof. easy. Qed.

Theorem fold_rank_fst_1 :
  ∀ a b, fst (rank_fst_loop b 1 a b) = rank_fst_1 a b.
Proof. easy. Qed.

Theorem fst_rank_fst_loop_succ :
  ∀ it k a b,
  fst (rank_fst_loop (S it) k a b) =
    if 2 * a / b =? k then 0
    else S (fst (rank_fst_loop it k ((2 * a) mod b) b)).
Proof.
intros.
cbn - [ "*" ].
rewrite fst_if, fst_let.
now destruct (2 * a / b =? k).
Qed.

Theorem snd_rank_fst_loop_succ :
  ∀ it k a b,
  snd (rank_fst_loop (S it) k a b) =
    if 2 * a / b =? k then a
    else snd (rank_fst_loop it k ((2 * a) mod b) b).
Proof.
intros.
cbn - [ "*" ].
rewrite snd_if, snd_let.
now destruct (2 * a / b =? k).
Qed.

Theorem rank_fst_1_succ_r :
  ∀ a b,
  rank_fst_1 a (S b) =
    if 2 * a / S b =? 1 then 0
    else S (fst (rank_fst_loop b 1 ((2 * a) mod S b) (S b))).
Proof.
intros.
progress unfold rank_fst_1.
now rewrite fst_rank_fst_loop_succ.
Qed.

Theorem Nat_neq_div :
  ∀ k a b : nat, b ≠ 0 → a / b ≠ k ↔ a < k * b ∨ S k * b ≤ a.
Proof.
intros * Hbz.
split; intros Habk. {
  destruct (lt_dec a (k * b)) as [Ha| Ha]; [ now left | right ].
  apply Nat.nlt_ge in Ha.
  apply Nat.nlt_ge.
  intros H.
  apply Habk; clear Habk.
  apply Nat_div_less_small_iff; [ easy | ].
  split; [ easy | ].
  now rewrite Nat.add_1_r.
} {
  intros Hab.
  subst k.
  destruct Habk as [Habk| Habk]. {
    apply Nat.nle_gt in Habk.
    apply Habk.
    rewrite Nat.mul_comm.
    now apply Nat.Div0.mul_div_le.
  }
  rewrite <- Nat.add_1_r in Habk.
  rewrite Nat.mul_add_distr_r in Habk.
  rewrite Nat.mul_1_l in Habk.
  apply Nat.nlt_ge in Habk.
  apply Habk; clear Habk.
  specialize (Nat.div_mod a b Hbz) as H1.
  rewrite H1 at 1.
  rewrite Nat.mul_comm.
  apply Nat.add_lt_mono_l.
  now apply Nat.mod_upper_bound.
}
Qed.

Theorem Nat_neq_div_1 : ∀ a b, b ≠ 0 → a / b ≠ 1 ↔ a < b ∨ 2 * b ≤ a.
Proof.
intros * Hbz.
specialize (Nat_neq_div 1 a b Hbz) as H1.
now rewrite Nat.mul_1_l in H1.
Qed.

Theorem fst_rank_fst_loop_mul_diag :
  ∀ it k a b c,
  c ≠ 0
  → fst (rank_fst_loop it k (c * a) (c * b)) =
    fst (rank_fst_loop it k a b).
Proof.
intros * Hcz.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  subst b.
  rewrite Nat.mul_0_r.
  revert a.
  induction it; intros; [ easy | ].
  cbn - [ "*" ].
  destruct k; [ easy | ].
  do 2 rewrite fst_let.
  f_equal.
  rewrite Nat.mul_assoc, (Nat.mul_comm 2).
  rewrite <- Nat.mul_assoc.
  apply IHit.
}
revert a.
induction it; intros; [ easy | ].
cbn - [ "*" ].
rewrite Nat.mul_assoc, (Nat.mul_comm 2), <- Nat.mul_assoc.
rewrite Nat.Div0.div_mul_cancel_l; [ | easy ].
destruct (2 * a / b =? k); [ easy | ].
do 2 rewrite fst_let.
f_equal.
rewrite Nat.Div0.mul_mod_distr_l.
apply IHit.
Qed.

Theorem Nat_eq_log2 :
  ∀ a n, a ≠ 0 ∧ Nat.log2 a = n ↔ 2 ^ n ≤ a < 2 ^ (n + 1).
Proof.
intros.
split. {
  intros (Haz, Han).
  apply Nat.neq_0_lt_0 in Haz.
  specialize (Nat.log2_spec a Haz) as H1.
  now rewrite Han, <- (Nat.add_1_r n) in H1.
} {
  intros Ha.
  specialize (Nat.pow_nonzero 2 n (Nat.neq_succ_0 _)) as H1.
  split; [ flia Ha H1 | ].
  apply Nat.le_antisymm. 2: {
    rewrite <- (Nat.log2_pow2 n); [ | easy ].
    now apply Nat.log2_le_mono.
  }
  apply Nat.lt_succ_r.
  apply (Nat.pow_lt_mono_r_iff 2); [ easy | ].
  rewrite <- (Nat.add_1_r n).
  eapply Nat.lt_le_trans; [ | apply Ha ].
  apply Nat.lt_succ_r.
  apply Nat.log2_spec.
  flia Ha H1.
}
Qed.

Theorem Nat_eq_log2_up_succ :
  ∀ a n, Nat.log2_up a = S n ↔ S (2 ^ n) ≤ a ≤ 2 ^ S n.
Proof.
intros.
split; intros Ha. {
  destruct a; [ easy | ].
  destruct a; [ easy | ].
  cbn in Ha.
  apply Nat.succ_inj in Ha.
  specialize (Nat.log2_iter_spec a 0 1 0 eq_refl (Nat.lt_0_succ _)) as H1.
  rewrite Ha in H1.
  cbn - [ "^" ] in H1.
  rewrite Nat.add_1_r in H1.
  flia H1.
}
progress unfold Nat.log2_up.
remember (1 ?= a) as a1 eqn:Ha1.
symmetry in Ha1.
destruct a1. {
  apply Nat.compare_eq in Ha1; subst a.
  specialize (Nat.pow_nonzero 2 n (Nat.neq_succ_0 _)) as H1.
  flia Ha H1.
} {
  f_equal.
  apply Nat.compare_lt_iff in Ha1.
  destruct a; [ easy | cbn ].
  clear Ha1.
  apply Nat_eq_log2.
  rewrite Nat.add_1_r.
  flia Ha.
} {
  apply Nat.compare_gt_iff in Ha1.
  now apply Nat.lt_1_r in Ha1; subst a.
}
Qed.

Theorem Nat_eq_log2_up :
  ∀ a n, a ≠ 0 →
  Nat.log2_up a = n ↔ 2 ^ n / 2 < a ≤ 2 ^ n.
Proof.
intros * Haz.
destruct n. {
  apply Nat.neq_0_lt_0 in Haz.
  specialize (Nat.log2_up_null a) as H1; cbn.
  split; intros Ha; [ | now apply H1 ].
  split; [ easy | apply H1, Ha ].
}
rewrite Nat.pow_succ_r' at 1.
rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
apply Nat_eq_log2_up_succ.
Qed.

Theorem rank_fst_1_log2_up_lemma :
  ∀ m n,
  2 ^ m - m < n
  → 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n))) < m + n.
Proof.
intros * Hmn.
revert m Hmn.
induction n; intros; [ flia Hmn | ].
cbn - [ "/" "mod" "*" "^" ].
rewrite fst_if, fst_let.
cbn - [ "/" "mod" "*" "^" ].
rewrite <- Nat.pow_succ_r'.
remember (2 ^ S m / (m + S n) =? 1) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2. {
  apply Nat.eqb_eq in Hn2.
  apply Nat_eq_div_1 in Hn2.
  rewrite Nat.add_0_r.
  destruct Hn2 as (Hn2, Hn3).
  rewrite Nat.pow_succ_r' in Hn3.
  now apply Nat.mul_lt_mono_pos_l in Hn3.
}
apply Nat.eqb_neq in Hn2.
apply Nat_neq_div_1 in Hn2; [ | flia ].
destruct Hn2 as [Hn2| Hn2]. {
  rewrite Nat.mod_small; [ | easy ].
  do 2 rewrite <- Nat.add_succ_comm.
  apply IHn.
  rewrite Nat.pow_succ_r' in Hn2 |-*.
  specialize (Nat.pow_gt_lin_r 2 m (Nat.lt_succ_diag_r _)) as H1.
  flia Hmn Hn2 H1.
}
rewrite Nat.pow_succ_r' in Hn2.
specialize (Nat.pow_gt_lin_r 2 m (Nat.lt_succ_diag_r _)) as H1.
flia Hmn Hn2 H1.
Qed.

Theorem rank_fst_1_log2_up_lemma_2 :
  ∀ m n,
  2 ^ m - m < n
  → m + n ≤ 2 ^ (m + S (fst (rank_fst_loop n 1 (2 ^ m) (m + n)))).
Proof.
intros * Hmn.
revert m Hmn.
induction n; intros; [ flia Hmn | ].
cbn - [ "/" "mod" "*" "^" ].
rewrite fst_if, fst_let.
cbn - [ "/" "mod" "*" "^" ].
rewrite <- Nat.pow_succ_r'.
remember (2 ^ S m / (m + S n) =? 1) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2. {
  apply Nat.eqb_eq in Hn2.
  apply Nat_eq_div_1 in Hn2.
  now rewrite Nat.add_1_r.
}
apply Nat.eqb_neq in Hn2.
apply Nat_neq_div_1 in Hn2; [ | flia ].
destruct Hn2 as [Hn2| Hn2]. {
  rewrite Nat.mod_small; [ | easy ].
  do 2 rewrite <- Nat.add_succ_comm.
  apply IHn.
  rewrite Nat.pow_succ_r' in Hn2 |-*.
  specialize (Nat.pow_gt_lin_r 2 m (Nat.lt_succ_diag_r _)) as H1.
  flia Hmn Hn2 H1.
}
rewrite Nat.pow_succ_r' in Hn2.
specialize (Nat.pow_gt_lin_r 2 m (Nat.lt_succ_diag_r _)) as H1.
flia Hmn Hn2 H1.
Qed.

Theorem rank_fst_1_log2_up : ∀ n, 2 ≤ n → rank_fst_1 1 n = Nat.log2_up n - 1.
Proof.
intros * H2n.
rewrite <- (Nat.add_sub _ 1).
f_equal; symmetry.
apply Nat_eq_log2_up; [ flia H2n | ].
rewrite Nat.add_1_r.
split. {
  apply Nat.Div0.div_lt_upper_bound.
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  progress unfold rank_fst_1.
  now apply (rank_fst_1_log2_up_lemma 0).
}
progress unfold rank_fst_1.
apply (rank_fst_1_log2_up_lemma_2 0); apply H2n.
Qed.

Theorem snd_rank_pow2_fst_rank_lemma :
  ∀ m n,
  2 ^ m - m < n
  → snd (rank_fst_loop n 1 (2 ^ m) (m + n)) =
    2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n))).
Proof.
intros * Hmn.
revert m Hmn.
induction n; intros; [ easy | ].
cbn - [ "*" ].
rewrite <- Nat.pow_succ_r'.
remember (2 ^ S m / (m + S n) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1; [ now cbn; rewrite Nat.add_0_r | ].
apply Nat.eqb_neq in Hn1.
apply Nat_neq_div_1 in Hn1; [ | flia ].
rewrite snd_let, fst_let.
destruct Hn1 as [Hn1| Hn1]. {
  rewrite Nat.mod_small; [ | easy ].
  rewrite <- Nat.add_succ_comm.
  rewrite <- Nat.add_succ_comm.
  apply IHn.
  apply (Nat.add_lt_mono_r _ _ (S m)).
  rewrite Nat.sub_add. 2: {
    eapply Nat.le_lt_trans; [ apply Nat.le_succ_diag_r | ].
    now apply Nat.pow_gt_lin_r.
  }
  now rewrite Nat.add_comm, Nat.add_succ_comm.
}
rewrite Nat.pow_succ_r' in Hn1.
apply Nat.mul_le_mono_pos_l in Hn1; [ flia Hmn Hn1 | easy ].
Qed.

Theorem snd_rank_pow2_fst_rank :
  ∀ n, 2 ≤ n
  → snd (rank_fst_loop n 1 1 n) = 2 ^ fst (rank_fst_loop n 1 1 n).
Proof.
intros * Hn.
now apply (snd_rank_pow2_fst_rank_lemma 0).
Qed.

Theorem snd_rank_fst_loop_1_log2_up :
  ∀ n, 2 ≤ n → snd (rank_fst_loop n 1 1 n) = 2 ^ (Nat.log2_up n - 1).
Proof.
intros * H2n.
rewrite snd_rank_pow2_fst_rank; [ | easy ].
rewrite fold_rank_fst_1.
now rewrite rank_fst_1_log2_up.
Qed.

Theorem Nat_le_add_le_sub_l_iff : ∀ n m p, n ≤ m → n + p ≤ m ↔ p ≤ m - n.
Proof.
intros * Hnm.
split; intros Hn; [ apply Nat.le_add_le_sub_l, Hn | ].
apply Nat.add_le_mono_l with (p := n) in Hn.
eapply Nat.le_trans; [ apply Hn | ].
rewrite Nat.add_comm.
now rewrite Nat.sub_add.
Qed.

Theorem Nat_pow2_log2 :
  ∀ n, n ≠ 0 → 2 ^ S (Nat.log2 n) = 2 ^ Nat.log2_up (S n).
Proof.
intros * Hnz.
now destruct n.
Qed.

(* find k and m such n = 2^k * m where m is odd *)
Fixpoint extract_pow2_loop it n :=
  match it with
  | 0 => (0, 0)
  | S it' =>
      if n mod 2 =? 0 then
        let (p, r) := extract_pow2_loop it' (n / 2) in
        (S p, r)
      else
        (0, n)
  end.

Definition extract_pow2 n := extract_pow2_loop n n.

Theorem snd_extract_pow2_loop :
  ∀ it n, n ≠ 0 → n ≤ it → Nat.Odd (snd (extract_pow2_loop it n)).
Proof.
intros * Hnz Hit.
revert n Hnz Hit.
induction it; intros; [ now apply Nat.le_0_r in Hit | ].
cbn - [ "/" "mod" ].
rewrite snd_if, snd_let.
cbn - [ "/" "mod" ].
remember (n mod 2 =? 0) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2. 2: {
  apply Nat.eqb_neq in Hn2.
  destruct (Nat.Even_or_Odd n) as [H1| H1]; [ | easy ].
  exfalso; apply Hn2; clear Hn2.
  progress unfold Nat.Even in H1.
  destruct H1 as (m, Hm); subst n.
  rewrite Nat.mul_comm.
  now apply Nat.Div0.mod_mul.
}
apply Nat.eqb_eq in Hn2.
apply Nat.Div0.mod_divides in Hn2.
destruct Hn2 as (m, Hm).
rewrite Hm, Nat.mul_comm, Nat.div_mul; [ | easy ].
apply IHit; [ | flia Hit Hm ].
now intros H; subst m.
Qed.

Theorem snd_extract_pow2_is_odd :
  ∀ n, n ≠ 0 → Nat.Odd (snd (extract_pow2 n)).
Proof.
intros * Hnz.
progress unfold extract_pow2.
now apply snd_extract_pow2_loop.
Qed.

Theorem extract_pow2_enough_iter :
  ∀ n it1 it2,
  n ≠ 0
  → n ≤ it1
  → n ≤ it2
  → extract_pow2_loop it1 n = extract_pow2_loop it2 n.
Proof.
intros * Hnz Hit1 Hit2.
revert n Hnz it2 Hit1 Hit2.
induction it1; intros; [ now apply Nat.le_0_r in Hit1 | ].
destruct it2; [ now apply Nat.le_0_r in Hit2 | ].
cbn - [ "mod" "/" ].
remember (n mod 2 =? 0) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2; [ | easy ].
apply Nat.eqb_eq in Hn2.
apply Nat.Div0.mod_divides in Hn2.
destruct Hn2 as (c, Hc).
rewrite Hc.
rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
rewrite IHit1 with (it2 := it2); [ easy | | | ]. {
  now intros H; rewrite H, Nat.mul_0_r in Hc.
} {
  flia Hit1 Hc.
} {
  flia Hit2 Hc.
}
Qed.

Theorem pow2_add_l_log2_le_mul_pow2_sub1 :
  ∀ n, n ≠ 0 → 2 ^ (Nat.log2_up n + n) ≤ n * (2 ^ S n - 1).
Proof.
intros * Hnz.
induction n; intros; [ easy | clear Hnz ].
specialize (Nat.log2_up_succ_or n) as H1.
destruct H1 as [H1| H1]. {
  rewrite H1.
  apply Nat_pow2_log2_up_succ in H1.
  rewrite Nat.add_succ_l, Nat.pow_succ_r'.
  rewrite Nat.pow_add_r, H1.
  do 3 rewrite Nat.pow_succ_r'.
  specialize (Nat.pow_gt_lin_r 2 n Nat.lt_1_2) as H2.
  flia H2.
}
rewrite H1.
rewrite Nat.add_succ_r.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ subst n; cbn; flia | ].
specialize (IHn Hnz).
rewrite Nat.pow_succ_r'.
apply (Nat.mul_le_mono_l _ _ 2) in IHn.
eapply Nat.le_trans; [ apply IHn | ].
do 3 rewrite Nat.pow_succ_r'.
specialize (Nat.pow_gt_lin_r 2 n Nat.lt_1_2) as H2.
flia H2.
Qed.

End a.
