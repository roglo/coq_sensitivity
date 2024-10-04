(* File created because Complex.v became too big, but
   without any topic found for the moment *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Init.Nat.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike Main.IterAdd.
Require Import Misc.
Require Import RealLike TrigoWithoutPi TrigoWithoutPiExt.
Require Import AngleAddOverflowLe AngleAddLeMonoL.
Require Import AngleLeSubAdd AngleDiv2Add.
Require Import TacChangeAngle.
Require Import Complex.
Require Import NewtonBinomial.
Require Import AngleAddOverflowEquiv.
Require Import AngleAddOverflowEquiv3.
Require Import SeqAngleIsCauchy.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Theorem gc_power_im_0 :
  rngl_has_opp_or_subt T = true →
  ∀ n x, (mk_gc x 0%L ^ n)%C = (mk_gc (x ^ n) 0)%C.
Proof.
intros Hos *.
progress unfold gc_power_nat.
induction n. {
  cbn; progress unfold rngl_one.
  cbn; progress unfold gc_opt_one.
  now destruct (rngl_opt_one T).
}
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

Theorem angle_mul_nat_overflow_pow2_div_angle_mul :
  ∀ n i θ,
  angle_mul_nat_overflow (2 ^ i / n) (n * (θ /₂^i)) = false.
Proof.
destruct_ac.
intros.
(* lemma to do *)
apply Bool.not_true_iff_false.
intros H1.
apply angle_mul_nat_overflow_true_assoc in H1.
apply Bool.not_false_iff_true in H1.
apply H1; clear H1.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). {
  rewrite Nat.mul_comm.
  apply Nat.Div0.mul_div_le.
}
apply angle_mul_nat_overflow_pow_div.
Qed.

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

Theorem angle_add_lt_mono_l :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (θ2 < θ3)%A → (θ1 + θ2 < θ1 + θ3)%A.
Proof.
intros * H13 H23.
apply angle_lt_iff.
split. {
  apply angle_add_le_mono_l; [ easy | ].
  now apply angle_lt_le_incl in H23.
}
intros H.
apply (f_equal (λ θ, (θ - θ1)%A)) in H.
do 2 rewrite angle_add_comm, angle_add_sub in H.
subst θ3.
now apply angle_lt_irrefl in H23.
Qed.

Theorem angle_add_lt_mono_r :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → (θ1 < θ2)%A → (θ1 + θ3 < θ2 + θ3)%A.
Proof.
intros * H23 H12.
do 2 rewrite (angle_add_comm _ θ3).
apply angle_add_not_overflow_comm in H23.
now apply angle_add_lt_mono_l.
Qed.

Theorem angle_div_2_pow_mul_lt_angle :
  ∀ n i θ, θ ≠ 0%A → n < 2 ^ i → (n * (θ /₂^i) < θ)%A.
Proof.
intros * Htz Hni.
revert n θ Hni Htz.
induction i; intros. {
  cbn in Hni.
  apply Nat.lt_1_r in Hni; subst n; cbn.
  apply angle_lt_iff.
  split; [ apply angle_nonneg | ].
  now intros H; apply Htz; symmetry.
}
destruct (lt_dec n (2 ^ i)) as [Hin| Hin]. {
  rewrite angle_div_2_pow_succ_r_2.
  apply (angle_lt_le_trans _ (θ /₂)). {
    apply IHi; [ easy | ].
    intros H.
    now apply eq_angle_div_2_0 in H.
  }
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
apply angle_lt_le_trans with (θ2 := (θ /₂ + θ /₂)%A). {
  apply angle_add_lt_mono_l; [ apply angle_add_overflow_div_2_div_2 | ].
  rewrite angle_div_2_pow_succ_r_2.
  apply IHi. {
    apply Nat.mod_upper_bound.
    now apply Nat.pow_nonzero.
  }
  intros H.
  now apply eq_angle_div_2_0 in H.
}
rewrite angle_add_div_2_diag.
apply angle_le_refl.
Qed.

Theorem angle_add_overflow_pow2_div_mul_pow2_diag :
  ∀ n i θ,
  1 < n ≤ 2 ^ i
  → angle_add_overflow (2 ^ i / n * (θ /₂^i)) (2 ^ i / n * (θ /₂^i)) =
      false.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%A).
  apply angle_add_overflow_0_l.
}
intros * (Hmi, Hni).
assert (Hnz : n ≠ 0) by flia Hmi.
progress unfold angle_add_overflow.
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
  rewrite angle_add_diag in Hzsm |-*.
  rewrite rngl_sin_mul_2_l in Hzsm.
  rewrite rngl_cos_mul_2_l'.
  apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
  remember (rngl_cos (u i)) as x eqn:Hx.
  rewrite Hu in Hx.
  progress unfold seq_angle_to_div_nat in Hx.
  rewrite <- Hx.
  destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
    destruct (rngl_eq_dec Heo (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
      rewrite Hu in Hxz.
      progress unfold seq_angle_to_div_nat in Hxz.
      apply eq_rngl_sin_0 in Hxz.
      destruct Hxz as [Hxz| Hxz]. {
        rewrite Hxz in Hx; cbn in Hx; subst x.
        exfalso; apply (rngl_nlt_ge Hor) in H2.
        apply H2; clear H2.
        rewrite Hxz.
        apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
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
    exfalso.
    rewrite Hu in Hxz.
    progress unfold seq_angle_to_div_nat in Hxz.
    apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
    apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2). {
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

Theorem binomial_0_r : ∀ n, binomial n 0 = 1.
Proof. now intros; destruct n. Qed.

Theorem binomial_succ_l :
  ∀ n k,
  binomial (S n) k =
    match k with
    | 0 => 1
    | S k' => binomial n k' + binomial n k
    end.
Proof. easy. Qed.

Theorem gre_summation :
  rngl_has_opp T = true →
  let roc := gc_ring_like_op T in
  ∀ b e (f : nat → GComplex T),
  gre (∑ (i = b, e), f i)%L = (∑ (i = b, e), gre (f i))%L.
Proof.
intros Hop.
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
set (rop := gc_ring_like_prop_not_alg_closed Hop).
specialize gc_add_comm as H1; cbn in H1.
rewrite H1; clear H1.
apply gc_add_0_l.
apply gc_add_assoc.
cbn.
f_equal.
apply rngl_add_0_l.
Qed.

Theorem gim_summation :
  rngl_has_opp T = true →
  let roc := gc_ring_like_op T in
  ∀ b e (f : nat → GComplex T),
  gim (∑ (i = b, e), f i)%L = (∑ (i = b, e), gim (f i))%L.
Proof.
intros Hop.
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
set (rop := gc_ring_like_prop_not_alg_closed Hop).
specialize gc_add_comm as H1; cbn in H1.
rewrite H1; clear H1.
apply gc_add_0_l.
apply gc_add_assoc.
cbn.
f_equal.
apply rngl_add_0_l.
Qed.

Theorem gre_1 :
  let roc := gc_ring_like_op T in
  (gre 1 = 1%L).
Proof.
intros.
cbn; progress unfold rngl_one.
cbn; progress unfold gc_opt_one.
now destruct (rngl_opt_one T).
Qed.

Theorem gim_1 :
  let roc := gc_ring_like_op T in
  (gim 1 = 0%L).
Proof.
intros.
cbn; progress unfold rngl_one.
cbn; progress unfold gc_opt_one.
now destruct (rngl_opt_one T).
Qed.

Theorem gc_power_re_0 :
  ∀ n y,
  (mk_gc 0 y ^ n =
     if Nat.even n then
       mk_gc ((minus_one_pow (n / 2)) * (y ^ n))%L 0
     else
       mk_gc 0 ((minus_one_pow (n / 2)) * (y ^ n))%L)%C.
Proof.
destruct_ac.
intros.
remember (Nat.even n) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply Nat.even_spec in Hb.
  destruct Hb as (m, Hm).
  subst n.
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
  progress unfold gc_power_nat.
  induction m; cbn. {
    rewrite (rngl_mul_1_l Hon).
    apply eq_gc_eq.
    cbn; progress unfold rngl_one.
    cbn; progress unfold gc_opt_one.
    now destruct (rngl_opt_one T).
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
  progress unfold gc_power_nat.
  induction m; cbn. {
    rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_mul_1_r Hon).
    apply eq_gc_eq; cbn.
    rewrite gre_1, gim_1.
    do 2 rewrite (rngl_mul_0_l Hos).
    rewrite (rngl_mul_0_r Hos).
    rewrite (rngl_sub_0_r Hos).
    rewrite (rngl_mul_1_r Hon).
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

Theorem gre_rngl_of_nat :
  let gro := gc_ring_like_op T : ring_like_op (GComplex T) in
  ∀ n, gre (rngl_of_nat n) = rngl_of_nat n.
Proof.
intros.
induction n; [ easy | ].
do 2 rewrite rngl_of_nat_succ.
cbn; rewrite IHn.
f_equal.
progress unfold gro.
now rewrite gre_1.
Qed.

Theorem gim_rngl_of_nat :
  let gro := gc_ring_like_op T : ring_like_op (GComplex T) in
  ∀ n, gim (rngl_of_nat n) = 0%L.
Proof.
intros.
induction n; [ easy | ].
rewrite rngl_of_nat_succ.
cbn; rewrite IHn.
progress unfold gro.
rewrite gim_1.
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
specialize (H1 (GComplex T)).
specialize (H1 gro).
specialize (H1 (gc_ring_like_prop_not_alg_closed Hop)).
assert (Honc : rngl_has_1 (GComplex T) = true). {
  progress unfold rngl_has_1 in Hon.
  progress unfold rngl_has_1.
  cbn.
  progress unfold gc_opt_one.
  now destruct (rngl_opt_one T).
}
assert (Hosc : rngl_has_opp_or_subt (GComplex T) = true). {
  progress unfold rngl_has_opp_or_subt in Hos.
  progress unfold rngl_has_opp_or_subt.
  cbn.
  progress unfold gc_opt_opp_or_subt.
  destruct rngl_opt_opp_or_subt as [s| ]; [ | easy ].
  now destruct s.
}
specialize (H1 Hic Honc Hosc n).
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
progress unfold gc_power_nat in H2.
rewrite H2 in H1; clear H2.
apply eq_gc_eq in H1.
cbn - [ rngl_add rngl_zero ] in H1.
rewrite (gre_summation Hop) in H1.
rewrite (gim_summation Hop) in H1.
destruct H1 as (Hc, Hs).
split. {
  rewrite Hc.
  apply rngl_summation_eq_compat.
  intros * (_, Hi).
  specialize (gc_power_im_0 Hos) as H1.
  progress unfold gc_power_nat in H1.
  rewrite H1.
  specialize gc_power_re_0 as H2.
  progress unfold gc_power_nat in H2.
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
  specialize (gc_power_im_0 Hos) as H1.
  progress unfold gc_power_nat in H1.
  rewrite H1.
  specialize gc_power_re_0 as H2.
  progress unfold gc_power_nat in H2.
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

Theorem angle_lim_0_le_if :
  ∀ f g,
  (∀ i, (f i ≤ g i ≤ angle_straight)%A)
  → angle_lim g 0
  → angle_lim f 0.
Proof.
destruct_ac.
intros * Hfg Hg.
intros ε Hε.
specialize (Hg ε Hε).
destruct Hg as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
eapply (rngl_le_lt_trans Hor); [ | apply HN ].
apply (rngl_cos_le_iff_angle_eucl_le (g n)).
apply rngl_cos_decr.
apply Hfg.
Qed.

Theorem angle_le_eucl_dist_le :
  ∀ θ1 θ2,
  (θ1 ≤ θ2 ≤ angle_straight)%A
  → (angle_eucl_dist θ1 θ2 ≤ angle_eucl_dist θ2 0)%L.
Proof.
intros * H12.
rewrite (angle_eucl_dist_symmetry θ2).
apply angle_dist_le_r; [ easy | ].
split; [ apply angle_nonneg | easy ].
Qed.

Theorem angle_same_lim_sub :
  ∀ u v θ, angle_lim u θ → angle_lim v θ → angle_lim (λ i, (u i - v i)%A) 0.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hu Hv ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hu Hv.
intros ε Hε.
assert (Hε2 : (0 < ε / 2)%L). {
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  now rewrite (rngl_mul_0_l Hos).
}
specialize (Hu _ Hε2)%L.
specialize (Hv _ Hε2)%L.
destruct Hu as (M, HM).
destruct Hv as (N, HN).
exists (max M N).
intros n Hn.
specialize (rngl_div_add_distr_r Hiv ε ε 2) as H2.
rewrite <- (rngl_mul_2_r Hon) in H2.
rewrite (rngl_mul_div Hi1) in H2. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite H2.
rewrite <- angle_eucl_dist_move_0_r.
eapply (rngl_le_lt_trans Hor). {
  apply (angle_eucl_dist_triangular _ θ).
}
rewrite (angle_eucl_dist_symmetry θ).
specialize (HM _ (Nat.max_lub_l _ _ _ Hn)).
specialize (HN _ (Nat.max_lub_r _ _ _ Hn)).
now apply (rngl_add_lt_compat Hop Hor).
Qed.

Theorem angle_sub_mul_l_diag_r :
  ∀ n θ, n ≠ 0 → (n * θ - θ)%A = ((n - 1) * θ)%A.
Proof.
intros * Hnz.
rewrite angle_mul_sub_distr_r. 2: {
  apply Nat.le_succ_l.
  now apply Nat.neq_0_lt_0.
}
now rewrite angle_mul_1_l.
Qed.

Theorem Nat_add_mul_r_diag_r : ∀ a b, a + b * a = (1 + b) * a.
Proof. easy. Qed.

Theorem angle_right_div_2_lt :
  ∀ θ,
  (rngl_cos θ < rngl_sin θ)%L
  → (0 ≤ rngl_sin θ)%L
  → (0 ≤ rngl_cos θ)%L
  → (angle_right /₂ < θ)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hcs Hs Hc.
  rewrite (H1 (rngl_cos _)) in Hcs.
  rewrite (H1 (rngl_sin _)) in Hcs.
  now apply (rngl_lt_irrefl Hor) in Hcs.
}
intros * Hcs Hs Hc.
progress unfold angle_ltb.
cbn.
rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
apply rngl_leb_le in Hs; rewrite Hs.
apply rngl_leb_le in Hs.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
rewrite (rngl_mul_1_l Hon).
specialize rl_sqrt_half_nonneg as Hzs.
generalize Hzs; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_ltb_lt.
specialize (rngl_cos_div_2 angle_right) as H1.
cbn - [ rngl_cos ] in H1.
specialize (rngl_0_le_1 Hon Hop Hor) as H2.
apply rngl_leb_le in H2.
rewrite H2 in H1; clear H2.
rewrite (rngl_mul_1_l Hon) in H1.
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
  apply (rngl_mul_pos_pos Hop Hor Hii). {
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
apply rngl_ltb_lt.
apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
apply (rngl_opp_neg_pos Hop Hor).
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
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hs Hc.
  rewrite (H1 (rngl_sin _)) in Hs.
  now apply (rngl_lt_irrefl Hor) in Hs.
}
intros * Hs Hc.
progress unfold angle_ltb.
rewrite rngl_sin_5_right_div_2.
rewrite rngl_cos_5_right_div_2.
rewrite (rngl_leb_0_opp Hop Hor).
generalize Hs; intros H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz; [ easy | ].
apply rngl_ltb_lt.
apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
apply (rngl_opp_neg_pos Hop Hor).
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hsc Hs Hc.
  rewrite (H1 (rngl_sin _)), (H1 (rngl_cos _)) in Hsc.
  now apply (rngl_lt_irrefl Hor) in Hsc.
}
intros * Hsc Hs Hc.
progress unfold angle_ltb.
rewrite rngl_sin_5_right_div_2.
rewrite (rngl_leb_0_opp Hop Hor).
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz. {
  exfalso.
  apply rngl_leb_le in Hsz.
  apply (rngl_nlt_ge Hor) in Hsz.
  apply Hsz; clear Hsz.
  apply (rl_sqrt_half_pos Hc1).
}
apply (rngl_leb_gt Hor) in Hs.
rewrite Hs.
apply (rngl_leb_gt Hor) in Hs.
apply rngl_ltb_lt.
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
  now apply (rngl_lt_le_incl Hor) in Hs.
} {
  apply rngl_sin_div_2_nonneg.
} {
  now apply (rngl_lt_le_incl Hor) in Hc.
} {
  apply rngl_cos_div_2_nonneg; cbn.
  apply (rngl_0_le_1 Hon Hop Hor).
} {
  cbn.
  specialize (rngl_0_le_1 Hon Hop Hor) as H2.
  apply rngl_leb_le in H2.
  rewrite H2; clear H2.
  rewrite (rngl_mul_1_l Hon).
  rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii). {
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hcs Hs Hc.
  rewrite (H1 (rngl_sin _)) in Hs.
  now apply (rngl_lt_irrefl Hor) in Hs.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hcs Hs Hc.
progress unfold angle_ltb.
generalize Hs; intros H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
rewrite rngl_sin_7_right_div_2.
rewrite rngl_cos_7_right_div_2.
rewrite (rngl_leb_0_opp Hop Hor).
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz. {
  exfalso.
  apply rngl_leb_le in Hsz.
  apply (rngl_nlt_ge Hor) in Hsz.
  apply Hsz; clear Hsz.
  apply (rl_sqrt_half_pos Hc1).
}
apply rngl_ltb_lt.
change_angle_opp θ.
progress sin_cos_opp_hyp T Hc.
progress sin_cos_opp_hyp T Hs.
progress sin_cos_opp_hyp T Hcs.
rewrite (rngl_opp_involutive Hop) in Hcs.
cbn.
rewrite <- rngl_cos_right_div_2.
apply quadrant_1_sin_sub_pos_cos_lt; try easy. {
  now apply (rngl_lt_le_incl Hor) in Hs.
} {
  now rewrite rngl_sin_right_div_2.
} {
  now rewrite rngl_cos_right_div_2.
} {
  cbn.
  specialize (rngl_0_le_1 Hon Hop Hor) as H2.
  apply rngl_leb_le in H2.
  rewrite H2; clear H2.
  rewrite (rngl_mul_1_l Hon).
  rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii). {
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
apply rngl_ltb_lt; cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
rewrite (rngl_mul_1_l Hon).
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hcs Hs Hc.
  rewrite (H1 (- _)%L), (H1 (rngl_sin _)) in Hcs.
  now apply (rngl_lt_irrefl Hor) in Hcs.
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
apply rngl_ltb_lt.
change_angle_sub_l θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hc.
progress sin_cos_add_sub_straight_hyp T Hs.
progress sin_cos_add_sub_straight_hyp T Hcs.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_0_sub Hop Hor).
specialize (rngl_cos_div_2 angle_right) as H1.
cbn - [ rngl_cos ] in H1.
specialize (rngl_0_le_1 Hon Hop Hor) as H2.
apply rngl_leb_le in H2.
rewrite H2 in H1; clear H2.
rewrite (rngl_mul_1_l Hon) in H1.
cbn - [ angle_div_2 ] in H1.
rewrite rngl_add_0_r in H1.
rewrite <- H1.
apply quadrant_1_sin_sub_pos_cos_lt; try easy. {
  now rewrite rngl_sin_right_div_2.
} {
  now apply (rngl_lt_le_incl Hor) in Hc.
} {
  now rewrite rngl_cos_right_div_2.

} {
  cbn - [ angle_div_2 ].
  rewrite rngl_sin_right_div_2.
  rewrite rngl_cos_right_div_2.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii). {
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
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hs Hc.
  rewrite (H1 (rngl_sin _)) in Hs.
  now apply (rngl_lt_irrefl Hor) in Hs.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hs Hc.
change_angle_add_r θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hc.
progress sin_cos_add_sub_straight_hyp T Hs.
progress unfold angle_ltb.
rewrite rngl_sin_sub_straight_r.
rewrite (rngl_leb_0_opp Hop Hor).
generalize Hs; intros H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
rewrite rngl_sin_7_right_div_2.
rewrite (rngl_leb_0_opp Hop Hor).
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz. {
  exfalso.
  apply rngl_leb_le in Hsz.
  apply (rngl_nlt_ge Hor) in Hsz.
  apply Hsz; clear Hsz.
  apply (rl_sqrt_half_pos Hc1).
}
apply rngl_ltb_lt.
rewrite rngl_cos_sub_straight_r.
rewrite rngl_cos_7_right_div_2.
apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
now apply (rngl_opp_neg_pos Hop Hor).
Qed.

Theorem rngl_cos_mul_2_neg_if :
  ∀ θ,
  (rngl_cos (2 * θ) < 0)%L
  → (angle_right /₂ < θ < 3 * (angle_right /₂))%A ∨
    (5 * (angle_right /₂) < θ < 7 * (angle_right /₂))%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * H2.
  rewrite (H1 (rngl_cos _)) in H2.
  now apply (rngl_lt_irrefl Hor) in H2.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hcz.
rewrite rngl_cos_mul_2_l in Hcz.
apply -> (rngl_lt_sub_0 Hop Hor) in Hcz.
apply (rngl_squ_lt_abs_lt Hop Hor Hii) in Hcz.
destruct (rngl_le_dec Hor 0 (rngl_sin θ)) as [Hs| Hs]. {
  rewrite (rngl_abs_nonneg_eq Hop Hor (rngl_sin _)) in Hcz; [ | easy ].
  left.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hc| Hc]. {
    rewrite (rngl_abs_nonneg_eq Hop Hor (rngl_cos _)) in Hcz; [ | easy ].
    split; [ now apply angle_right_div_2_lt | ].
    now apply quadrant_1_angle_lt_3_angle_right_div_2.
  } {
    apply (rngl_nle_gt Hor) in Hc.
    rewrite (rngl_abs_nonpos_eq Hop Hor) in Hcz. 2: {
      now apply (rngl_lt_le_incl Hor) in Hc.
    }
    split. {
      now apply quadrant_2_angle_right_div_2_lt.
    } {
      now apply quadrant_2_angle_lt_3_angle_right_div_2.
    }
  }
} {
  apply (rngl_nle_gt Hor) in Hs.
  rewrite (rngl_abs_nonpos_eq Hop Hor (rngl_sin _)) in Hcz. 2: {
    now apply (rngl_lt_le_incl Hor) in Hs.
  }
  right.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hc| Hc]. {
    rewrite (rngl_abs_nonneg_eq Hop Hor (rngl_cos _)) in Hcz; [ | easy ].
    split. {
      now apply quadrant_4_angle_lt_5_angle_right_div_2.
    } {
      now apply quadrant_4_angle_lt_7_angle_right_div_2.
    }
  }
  apply (rngl_nle_gt Hor) in Hc.
  rewrite (rngl_abs_nonpos_eq Hop Hor) in Hcz. 2: {
    now apply (rngl_lt_le_incl Hor) in Hc.
  }
  apply (rngl_opp_lt_compat Hop Hor) in Hcz.
  split. {
    now apply quadrant_3_angle_lt_5_angle_right_div_2.
  } {
    now apply quadrant_3_angle_lt_7_angle_right_div_2.
  }
}
Qed.

Theorem angle_opp_lt_compat_if :
  ∀ θ1 θ2,
  (θ1 ≠ 0)%A
  → (θ1 < θ2)%A
  → (- θ2 < - θ1)%A.
Proof.
destruct_ac.
intros * H1z H12.
progress unfold angle_ltb in H12.
progress unfold angle_ltb.
cbn.
do 2 rewrite (rngl_leb_0_opp Hop Hor).
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
symmetry in Hzs1, Hs1z.
symmetry in Hzs2, Hs2z.
destruct s2z. {
  destruct s1z; [ | easy ].
  apply rngl_leb_le in Hs1z.
  apply rngl_leb_le in Hs2z.
  apply rngl_ltb_lt.
  destruct zs2. {
    destruct zs1; [ | easy ].
    apply rngl_leb_le in Hzs1.
    apply rngl_leb_le in Hzs2.
    apply rngl_ltb_lt in H12.
    apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
    apply eq_rngl_sin_0 in Hzs1.
    destruct Hzs1; subst θ1; [ easy | clear H1z ].
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_cos_bound | ].
    intros H2; symmetry in H2.
    apply eq_rngl_cos_opp_1 in H2; subst θ2.
    now apply (rngl_lt_irrefl Hor) in H12.
  }
  apply (rngl_leb_gt Hor) in Hzs2.
  destruct zs1; [ | now apply rngl_ltb_lt in H12 ].
  apply rngl_leb_le in Hzs1.
  apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
  apply eq_rngl_sin_0 in Hzs1.
  destruct Hzs1; subst θ1; [ easy | clear H1z ].
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  intros Hc; symmetry in Hc.
  apply eq_rngl_cos_opp_1 in Hc; subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
apply (rngl_leb_gt Hor) in Hs2z.
destruct zs2. 2: {
  apply (rngl_leb_gt Hor) in Hzs2.
  now apply (rngl_lt_asymm Hor) in Hzs2.
}
clear Hzs2.
destruct zs1; [ | easy ].
destruct s1z; [ | easy ].
exfalso.
apply rngl_leb_le in Hzs1, Hs1z.
apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
apply eq_rngl_sin_0 in Hzs1.
destruct Hzs1; subst θ1; [ easy | ].
apply rngl_ltb_lt in H12.
apply (rngl_nle_gt Hor) in H12.
apply H12, rngl_cos_bound.
Qed.

Theorem angle_le_antisymm : ∀ θ1 θ2, (θ1 ≤ θ2)%A → (θ2 ≤ θ1)%A → θ1 = θ2.
Proof.
destruct_ac.
intros * H12 H21.
progress unfold angle_leb in H12.
progress unfold angle_leb in H21.
apply eq_angle_eq.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_cos θ1)%L as zc1 eqn:Hzc1.
remember (0 ≤? rngl_cos θ2)%L as zc2 eqn:Hzc2.
symmetry in Hzs1, Hzs2, Hzc1, Hzc2.
destruct zs1. 2: {
  destruct zs2; [ easy | ].
  apply rngl_leb_le in H12, H21.
  apply (rngl_le_antisymm Hor) in H12; [ clear H21 | easy ].
  rewrite H12; f_equal.
  apply (rngl_leb_gt Hor) in Hzs1, Hzs2.
  (* lemma? *)
  change_angle_opp θ1.
  progress sin_cos_opp_hyp T Hzs1.
  change_angle_opp θ2.
  progress sin_cos_opp_hyp T Hzs2.
  cbn in H12 |-*.
  f_equal.
  apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
  specialize (rngl_sin_nonneg_cos_le_sin_le θ1 θ2 Hzs1 Hzs2) as H1.
  specialize (rngl_sin_nonneg_cos_le_sin_le θ2 θ1 Hzs2 Hzs1) as H2.
  rewrite H12 in H1, H2.
  specialize (H1 (rngl_le_refl Hor _)).
  specialize (H2 (rngl_le_refl Hor _)).
  cbn in Hzc1.
  rewrite Hzc1 in H1, H2.
  now destruct zc1; apply (rngl_le_antisymm Hor).
}
destruct zs2; [ | easy ].
apply rngl_leb_le in H12, H21.
apply (rngl_le_antisymm Hor) in H12; [ clear H21 | easy ].
rewrite H12; f_equal.
apply rngl_leb_le in Hzs1, Hzs2.
specialize (rngl_sin_nonneg_cos_le_sin_le θ1 θ2 Hzs1 Hzs2) as H1.
specialize (rngl_sin_nonneg_cos_le_sin_le θ2 θ1 Hzs2 Hzs1) as H2.
rewrite H12 in H1, H2.
specialize (H1 (rngl_le_refl Hor _)).
specialize (H2 (rngl_le_refl Hor _)).
cbn in Hzc2.
rewrite Hzc2 in H1, H2.
now destruct zc2; apply (rngl_le_antisymm Hor).
Qed.

Theorem angle_opp_le_compat_if :
  ∀ θ1 θ2,
  (θ1 ≠ 0)%A
  → (θ1 ≤ θ2)%A
  → (- θ2 ≤ - θ1)%A.
Proof.
intros * H1z H12.
destruct (angle_lt_dec θ1 θ2) as [Hl12| Hl12]. {
  specialize (angle_opp_lt_compat_if θ1 θ2 H1z Hl12) as H1.
  now apply angle_lt_le_incl in H1.
}
apply angle_nlt_ge in Hl12.
apply angle_le_antisymm in H12; [ | easy ].
subst θ2.
apply angle_le_refl.
Qed.

Theorem rngl_sin_mul_2_neg_if :
  ∀ θ,
  (rngl_sin (2 * θ) < 0)%L
  → (angle_right < θ < angle_straight)%A ∨
    (3 * angle_right < θ)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * H2.
  rewrite (H1 (rngl_sin _)) in H2.
  now apply (rngl_lt_irrefl Hor) in H2.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hsz.
rewrite rngl_sin_mul_2_l in Hsz.
apply (rngl_lt_mul_0_if Hop Hor) in Hsz.
destruct Hsz as [(H2sz, Hzc)| (Hz2s, Hcz)]. {
  apply (rngl_lt_mul_0_if Hop Hor) in H2sz.
  destruct H2sz as [(H, _)| (_, Hcz)]. {
    exfalso.
    apply (rngl_nle_gt Hor) in H.
    apply H; clear H.
    apply (rngl_0_le_2 Hon Hop Hor).
  }
  right.
  change_angle_opp θ.
  progress sin_cos_opp_hyp T Hzc.
  progress sin_cos_opp_hyp T Hcz.
  rewrite <- (angle_opp_involutive (_ * _)).
  apply angle_opp_lt_compat_if. {
    intros H; subst θ.
    now apply (rngl_lt_irrefl Hor) in Hcz.
  }
  progress unfold angle_ltb.
  cbn - [ angle_mul_nat ].
  generalize Hcz; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  rewrite (rngl_leb_0_opp Hop Hor).
  remember (rngl_sin (_ * _) ≤? 0)%L as s3 eqn:Hs3.
  symmetry in Hs3.
  destruct s3; [ | easy ].
  apply rngl_ltb_lt.
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
apply (rngl_mul_pos_cancel_l Hop Hor Hii) in Hz2s. 2: {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
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
  specialize (rngl_0_le_1 Hon Hop Hor) as H2.
  apply rngl_leb_le in H2.
  rewrite H2.
  generalize Hz2s; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_ltb_lt.
  now apply (rngl_opp_neg_pos Hop Hor).
}
apply angle_lt_iff.
split. {
  progress unfold angle_leb.
  rewrite rngl_sin_add_right_r.
  rewrite rngl_cos_add_right_r.
  generalize Hz2s; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H; cbn.
  rewrite (rngl_leb_refl Hor).
  rewrite (rngl_leb_opp_r Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  apply rngl_leb_le.
  apply rngl_sin_bound.
}
intros H.
apply angle_add_move_r in H.
rewrite angle_straight_sub_right in H.
subst θ.
now apply (rngl_lt_irrefl Hor) in Hz2s.
Qed.

Theorem angle_div_2_pow_mul_neq_0 :
  ∀ n i θ,
  θ ≠ 0%A
  → 0 < n < 2 ^ i
  → (n * (θ /₂^i) ≠ 0)%A.
Proof.
intros * Htz Hni.
revert θ n Htz Hni.
induction i; intros. {
  cbn in Hni.
  flia Hni.
}
destruct (lt_dec n (2 ^ i)) as [Hn2i| Hn2i]. {
  rewrite angle_div_2_pow_succ_r_2.
  apply IHi; [ | flia Hni Hn2i ].
  intros H.
  now apply eq_angle_div_2_0 in H.
}
apply Nat.nlt_ge in Hn2i.
replace n with ((n - 2 ^ i) + 2 ^ i) by flia Hn2i.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_pow_succ_r_2 at 2.
rewrite angle_div_2_pow_mul_2_pow.
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. 2: {
  apply angle_mul_nat_overflow_div_pow2.
  cbn in Hni.
  flia Hni.
}
assert (Hnii : n - 2 ^ i < 2 ^ i) by (cbn in Hni; flia Hni).
intros H.
remember ((n - 2 ^ i) * (θ /₂^i))%A as θ' eqn:Hθ'.
assert (Htt : (θ' /₂ < θ /₂)%A). {
  apply angle_div_2_lt_compat.
  rewrite Hθ'.
  now apply angle_div_2_pow_mul_lt_angle.
}
apply (angle_add_lt_mono_l (θ' /₂)) in Htt. 2: {
  apply angle_add_overflow_div_2_div_2.
}
rewrite H in Htt.
apply angle_nle_gt in Htt.
apply Htt; clear Htt.
apply angle_nonneg.
Qed.

Theorem angle_mul_mul_div_2 :
  ∀ m n θ,
  angle_mul_nat_overflow n θ = false
  → (m * ((n * θ) /₂))%A = (m * n * (θ /₂))%A.
Proof.
intros * Haov.
rewrite <- angle_mul_nat_assoc.
f_equal.
symmetry.
now apply angle_mul_nat_div_2.
Qed.

Theorem angle_add_straight_r_le_straight :
  ∀ θ,
  (angle_straight ≤ θ)%A
  → (θ + angle_straight ≤ angle_straight)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros * Hst.
  rewrite (H1 (_ + _)%A).
  apply angle_nonneg.
}
intros * Hst.
progress unfold angle_leb in Hst.
progress unfold angle_leb.
cbn in Hst.
rewrite (rngl_leb_refl Hor) in Hst.
rewrite rngl_sin_add_straight_r.
rewrite rngl_cos_add_straight_r.
cbn.
rewrite (rngl_leb_refl Hor).
rewrite (rngl_leb_0_opp Hop Hor).
destruct (rngl_le_dec Hor 0 (rngl_sin θ)) as [Hzt| Htz]. {
  generalize Hzt; intros H.
  apply rngl_leb_le in H.
  rewrite H in Hst; clear H.
  apply rngl_leb_le in Hst.
  specialize (proj1 (rngl_cos_bound θ)) as H1.
  apply (rngl_le_antisymm Hor) in H1; [ | easy ].
  apply eq_rngl_cos_opp_1 in H1; subst θ; cbn.
  rewrite (rngl_leb_refl Hor).
  apply rngl_leb_le.
  rewrite (rngl_opp_involutive Hop).
  apply (rngl_opp_1_le_1 Hon Hop Hor Hc1).
}
apply (rngl_nle_gt Hor) in Htz.
destruct (rngl_le_dec Hor (rngl_sin θ) 0) as [Hzt| Hzt]. {
  generalize Hzt; intros H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_leb_le.
  apply -> (rngl_opp_le_compat Hop Hor).
  apply rngl_cos_bound.
}
now apply (rngl_lt_le_incl Hor) in Htz.
Qed.

Theorem angle_add_overflow_pow2_div_mul_pow2_mul_when_lt_straight :
  ∀ m n i θ,
  m < n ≤ 2 ^ i
  → (θ < angle_straight)%A
  → angle_add_overflow
      (seq_angle_to_div_nat θ n i)
      (m * seq_angle_to_div_nat θ n i) =
      false.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  progress unfold seq_angle_to_div_nat.
  rewrite (H1 (_ * _)%A).
  apply angle_add_overflow_0_l.
}
intros * (Hmi, Hni) Hts.
assert (Hnz : n ≠ 0) by flia Hmi.
progress unfold seq_angle_to_div_nat.
apply angle_add_overflow_le with (θ2 := θ). {
  rewrite <- (angle_div_2_pow_mul_2_pow i θ) at 2.
  rewrite angle_mul_nat_assoc.
  apply angle_mul_le_mono_r. {
    apply angle_mul_nat_overflow_pow_div.
  }
  eapply Nat.le_trans; [ now apply Nat.Div0.div_mul_le | ].
  apply Nat.Div0.div_le_upper_bound.
  apply Nat.mul_le_mono_r.
  now apply Nat.lt_le_incl in Hmi.
}
clear m Hmi.
apply angle_add_not_overflow_comm.
apply angle_add_overflow_lt_straight_le_straight; [ easy | ].
destruct i. {
  cbn in Hni.
  apply Nat.le_1_r in Hni.
  destruct Hni as [| Hni]; [ easy | subst n; cbn ].
  rewrite angle_add_0_r.
  now apply angle_lt_le_incl in Hts.
}
destruct n; [ easy | clear Hnz ].
destruct n. {
  rewrite Nat.div_1_r.
  rewrite angle_div_2_pow_mul_2_pow.
  now apply angle_lt_le_incl in Hts.
}
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2; [ apply angle_div_2_le_straight | ].
apply angle_mul_nat_overflow_div_pow2.
apply Nat.Div0.div_le_upper_bound.
rewrite Nat.pow_succ_r'.
apply Nat.mul_le_mono_r.
now do 2 apply -> Nat.succ_le_mono.
Qed.

Theorem angle_div_2_pow_succ_mul_lt_straight :
  rngl_characteristic T ≠ 1 →
  ∀ n i θ,
  n ≤ 2 ^ i
  → (n * (θ /₂^S i) < angle_straight)%A.
Proof.
intros Hc1 * Hni.
apply (angle_add_diag_not_overflow Hc1).
apply angle_mul_nat_overflow_distr_add_overflow.
rewrite Nat_add_diag.
rewrite angle_div_2_pow_succ_r_1.
apply angle_mul_nat_overflow_mul_2_div_2.
now apply angle_mul_nat_overflow_div_pow2.
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
rewrite (rngl_mul_1_l Hon).
(* lemma to do, perhaps *)
apply (rngl_lt_iff Hor).
split. {
  apply rl_sqrt_nonneg.
  apply rngl_1_add_cos_div_2_nonneg.
}
intros H; symmetry in H.
apply (eq_rl_sqrt_0 Hon Hos) in H. 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
}
(* lemma? *)
apply (f_equal (λ a, rngl_mul a 2)) in H.
rewrite (rngl_div_mul Hon Hiv) in H. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite (rngl_mul_0_l Hos) in H.
(* lemma? *)
rewrite rngl_add_comm in H.
apply (rngl_add_move_0_r Hop) in H.
apply (eq_rngl_cos_opp_1) in H.
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
rewrite (rngl_mul_1_l Hon).
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

Theorem Nat_pow2_log2_diag_pow2_up_log2_diag :
  ∀ n, 2 ^ Nat.log2 n = n ↔ 2 ^ Nat.log2_up n = n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply Nat.neq_0_lt_0 in Hnz.
split; intros Hn. {
  rewrite <- Hn at 2; symmetry; f_equal.
  apply Nat.log2_log2_up_exact; [ easy | ].
  now exists (Nat.log2 n).
} {
  rewrite <- Hn at 2; f_equal.
  apply Nat.log2_log2_up_exact; [ easy | ].
  now exists (Nat.log2_up n).
}
Qed.

Theorem Nat_pow2_log2_succ :
  ∀ n, Nat.log2 (S n) = S (Nat.log2 n) ↔ n ≠ 0 ∧ 2 ^ Nat.log2 (S n) = S n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply Nat.neq_0_lt_0 in Hnz.
split; intros Hn. {
  split; [ now intros H; subst n | ].
  apply Nat.log2_eq_succ_iff_pow2 in Hn; [ | easy ].
  destruct Hn as (m, Hm); rewrite Hm.
  now rewrite Nat.log2_pow2.
} {
  destruct Hn as (_, Hn).
  apply Nat.log2_eq_succ_iff_pow2; [ easy | ].
  now exists (Nat.log2 (S n)).
}
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

Theorem S_if :
  ∀ (a : bool) b c,
  S (if a then b else c) = if a then S b else S c.
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

Theorem Nat_sub_mul_l_diag_l : ∀ a b, a * b - a = a * (b - 1).
Proof.
intros.
now rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
Qed.

Theorem Nat_sub_mul_l_diag_r : ∀ a b, a * b - b = (a - 1) * b.
Proof.
intros.
now rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
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

Theorem Nat_lt_sub_lt_add_r_iff : ∀ n m p, p ≤ n → n - p < m ↔ n < m + p.
Proof.
intros * Hpm.
split; intros Hn; [ apply Nat.lt_sub_lt_add_r, Hn | ].
apply Nat.add_lt_mono_r with (p := p).
now rewrite Nat.sub_add.
Qed.

Theorem Nat_pow2_log2 :
  ∀ n, n ≠ 0 → 2 ^ S (Nat.log2 n) = 2 ^ Nat.log2_up (S n).
Proof.
intros * Hnz.
now destruct n.
Qed.

(* to be cleaned *)
Theorem Nat_log2_up_pow2_sub_1 :
  ∀ n, n ≠ 1 → Nat.log2_up (2 ^ n - 1) = n.
Proof.
intros * Hn1.
specialize (Nat.log2_up_succ_or (2 ^ n - 1)) as H1.
destruct H1 as [H1| H1]. 2: {
  rewrite <- Nat.sub_succ_l in H1. 2: {
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  rewrite Nat_sub_succ_1 in H1.
  rewrite <- H1.
  now apply Nat.log2_up_pow2.
}
rewrite <- Nat.sub_succ_l in H1. 2: {
  apply Nat.neq_0_lt_0.
  now apply Nat.pow_nonzero.
}
rewrite Nat_sub_succ_1 in H1.
rewrite Nat.log2_up_pow2 in H1; [ | easy ].
symmetry in H1.
destruct n; [ easy | ].
apply Nat.succ_inj in H1.
apply Nat_eq_log2_up in H1. {
  rewrite Nat.pow_succ_r' in H1.
  destruct H1 as (H1, H2).
  specialize (Nat.pow_nonzero 2 n (Nat.neq_succ_0 _)) as H3.
  remember (2 ^ n) as m eqn:Hm.
  destruct m; [ easy | ].
  exfalso.
  apply Nat.nlt_ge in H2.
  apply H2; clear H2.
  apply Nat.lt_add_lt_sub_r.
  rewrite <- Nat_add_diag.
  apply Nat.add_lt_mono_l.
  destruct m; [ | flia ].
  cbn in H1.
  symmetry in Hm.
  destruct n; [ easy | ].
  rewrite Nat.pow_succ_r' in Hm.
  flia Hm.
}
rewrite Nat.pow_succ_r'.
specialize (Nat.pow_nonzero 2 n (Nat.neq_succ_0 _)) as H3.
flia H3.
Qed.

Theorem Nat_eq_pow_1 : ∀ a b, a ^ b = 1 → a = 1 ∨ b = 0.
Proof.
intros * Hab.
destruct b; [ now right | left ].
cbn in Hab.
now apply Nat.eq_mul_1 in Hab.
Qed.

Theorem Geoffroy_1 :
  ∀ a b na nb,
  1 < a
  → 1 < b
  → na = Nat.log2_up a
  → nb = Nat.log2_up b
  → 2 ^ (na + nb - 2) < a * b ≤ 2 ^ (na + nb).
Proof.
intros * H1a H1b Hna Hnb.
specialize (Nat.log2_up_spec _ H1a) as Ha.
specialize (Nat.log2_up_spec _ H1b) as Hb.
rewrite <- Hna in Ha.
rewrite <- Hnb in Hb.
rewrite PeanoNat.pred_of_minus in Ha, Hb.
split. {
  replace 2 with (1 + 1) at 2 by easy.
  rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub_swap. 2: {
    rewrite Hna.
    replace 1 with (Nat.log2_up 2) by easy.
    now apply Nat.log2_up_le_mono.
  }
  rewrite <- Nat.add_sub_assoc. 2: {
    rewrite Hnb.
    replace 1 with (Nat.log2_up 2) by easy.
    now apply Nat.log2_up_le_mono.
  }
  rewrite Nat.pow_add_r.
  now apply Nat.mul_lt_mono.
}
rewrite Nat.pow_add_r.
now apply Nat.mul_le_mono.
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

Theorem Nat_div_not_small_iff :
  ∀ a b, b ≠ 0 → a / b ≠ 0 ↔ b ≤ a.
Proof.
intros * Hbz.
split; intros H1. {
  apply Nat.nlt_ge; intros H; apply H1.
  now apply Nat.div_small_iff.
} {
  apply Nat.nlt_ge in H1; intros H; apply H1.
  now apply Nat.div_small_iff.
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
