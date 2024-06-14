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

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_pow_1_l : rngl_has_1 T = true → ∀ n, (1 ^ n = 1)%L.
Proof.
intros Hon *.
induction n; [ easy | cbn ].
rewrite IHn.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_pow_mul_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a b n, ((a * b) ^ n = a ^ n * b ^ n)%L.
Proof.
intros Hic Hon *.
induction n; cbn. {
  symmetry; apply (rngl_mul_1_l Hon).
}
do 2 rewrite <- rngl_mul_assoc.
f_equal.
rewrite IHn.
rewrite (rngl_mul_comm Hic).
rewrite <- rngl_mul_assoc.
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_pow_mul_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a m n, (a ^ (m * n) = (a ^ m) ^ n)%L.
Proof.
intros Hic Hon *.
revert n.
induction m; intros. {
  symmetry; apply (rngl_pow_1_l Hon).
}
rewrite rngl_pow_succ_r.
cbn.
rewrite (rngl_pow_add_r Hon).
rewrite IHm.
symmetry.
apply (rngl_pow_mul_l Hic Hon).
Qed.

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
  angle_mul_nat_overflow (2 ^ i / n) (n * (θ / ₂^i)) = false.
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
  now apply Nat.mul_div_le.
}
apply angle_mul_nat_overflow_pow_div.
Qed.

Theorem angle_div_pow2_1 : ∀ θ, (θ / ₂^1 = θ / ₂)%A.
Proof. easy. Qed.

Theorem angle_add_overflow_mul_div_pow2 :
  ∀ n i θ,
  n < 2 ^ i
  → angle_add_overflow (θ / ₂^i) (n * (θ / ₂^i)) = false.
Proof.
destruct_ac.
intros * Hni.
revert θ n Hni.
induction i; intros. {
  cbn in Hni.
  apply Nat.succ_le_mono in Hni.
  apply Nat.le_0_r in Hni; subst n.
  apply angle_add_overflow_0_r.
}
destruct (le_dec (S n) (2 ^ i)) as [Hsni| Hsni]. {
  rewrite angle_div_2_pow_succ_r_2.
  now apply IHi.
}
apply Nat.nle_gt in Hsni.
apply -> Nat.le_succ_l in Hni.
apply -> Nat.lt_succ_r in Hsni.
assert (H1 : n = 2 ^ i + n mod 2 ^ i). {
  specialize (Nat.div_mod n (2 ^ i)) as H1.
  assert (H : 2 ^ i ≠ 0) by now apply Nat.pow_nonzero.
  specialize (H1 H); clear H.
  rewrite (Nat_div_less_small 1) in H1; [ now rewrite Nat.mul_1_r in H1 | ].
  now rewrite Nat.mul_1_l.
}
rewrite H1.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_pow_succ_r_2 at 2.
rewrite angle_div_2_pow_mul_2_pow.
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. 2: {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)).
  apply Nat.lt_le_incl, Nat.mod_upper_bound.
  now apply Nat.pow_nonzero.
  apply angle_mul_nat_overflow_pow_div.
}
apply angle_add_not_overflow_move_add. 2: {
  rewrite <- angle_div_2_add_not_overflow. 2: {
    apply IHi.
    apply Nat.mod_upper_bound.
    now apply Nat.pow_nonzero.
  }
  apply angle_add_overflow_div_2_div_2.
}
apply angle_add_overflow_div_2_div_2.
Qed.

Theorem angle_mul_nat_overflow_div_pow2 :
  ∀ n i θ,
  n ≤ 2 ^ i
  → angle_mul_nat_overflow n (θ / ₂^i) = false.
Proof.
intros * Hni.
revert i θ Hni.
induction n; intros; [ easy | ].
rewrite angle_mul_nat_overflow_succ_l.
apply Bool.orb_false_iff.
split. {
  apply IHn.
  apply (Nat.le_trans _ (S n)); [ | easy ].
  apply Nat.le_succ_diag_r.
}
now apply angle_add_overflow_mul_div_pow2.
Qed.

Theorem angle_mul_div_pow2_le_straight :
  ∀ n i θ,
  2 * n ≤ 2 ^ i
  → (n * (θ / ₂^i) ≤ angle_straight)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%A).
  apply angle_nonneg.
}
intros * Hni.
revert θ.
induction i; intros. {
  cbn in Hni.
  rewrite Nat.add_0_r in Hni.
  destruct n; [ apply (angle_straight_nonneg Hc1) | ].
  cbn in Hni.
  apply Nat.succ_le_mono in Hni.
  rewrite <- Nat.add_succ_comm in Hni; cbn in Hni.
  easy.
}
destruct (le_dec (2 * n) (2 ^ i)) as [Hni1| Hni1]. {
  rewrite angle_div_2_pow_succ_r_2.
  now apply IHi.
}
apply Nat.nle_gt in Hni1.
clear IHi.
rewrite Nat.pow_succ_r' in Hni.
apply Nat.mul_le_mono_pos_l in Hni; [ | easy ].
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. 2: {
  now apply angle_mul_nat_overflow_div_pow2.
}
apply angle_div_2_le_straight.
Qed.

Theorem angle_div_2_pow_mul_le_angle :
  ∀ n i θ, n ≤ 2 ^ i → (n * (θ / ₂^i) ≤ θ)%A.
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
  apply (angle_le_trans _ (θ / ₂)); [ now apply IHi | ].
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
apply angle_le_trans with (θ2 := (θ / ₂ + θ / ₂)%A). {
  apply angle_add_le_mono_l; cycle 1. {
    apply angle_add_overflow_div_2_div_2.
  } {
    rewrite angle_div_2_pow_succ_r_2.
    apply IHi.
    apply Nat.mod_upper_bound.
    now apply Nat.pow_nonzero.
  }
  apply angle_add_overflow_le with (θ2 := (θ / ₂)%A). 2: {
    apply angle_add_overflow_div_2_div_2.
  }
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
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ1 θ3 = false
  → (θ2 < θ3)%A → (θ1 + θ2 < θ1 + θ3)%A.
Proof.
intros * H12 H13 H23.
apply angle_lt_iff.
split. {
  apply angle_add_le_mono_l; [ easy | easy | ].
  now apply angle_lt_le_incl in H23.
}
intros H.
apply (f_equal (λ θ, (θ - θ1)%A)) in H.
do 2 rewrite angle_add_comm, angle_add_sub in H.
subst θ3.
now apply angle_lt_irrefl in H23.
Qed.

Theorem angle_div_2_pow_mul_lt_angle :
  ∀ n i θ, θ ≠ 0%A → n < 2 ^ i → (n * (θ / ₂^i) < θ)%A.
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
  apply (angle_lt_le_trans _ (θ / ₂)). {
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
apply angle_lt_le_trans with (θ2 := (θ / ₂ + θ / ₂)%A). {
  apply angle_add_lt_mono_l; cycle 1. {
    apply angle_add_overflow_div_2_div_2.
  } {
    rewrite angle_div_2_pow_succ_r_2.
    apply IHi. {
      apply Nat.mod_upper_bound.
      now apply Nat.pow_nonzero.
    }
    intros H.
    now apply eq_angle_div_2_0 in H.
  }
  apply angle_add_overflow_le with (θ2 := (θ / ₂)%A). 2: {
    apply angle_add_overflow_div_2_div_2.
  }
  rewrite angle_div_2_pow_succ_r_2.
  apply angle_lt_le_incl.
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
  → angle_add_overflow (2 ^ i / n * (θ / ₂^i)) (2 ^ i / n * (θ / ₂^i)) =
      false.
Proof.
destruct_ac.
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
    destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
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
        specialize (H1 (2 ^ S i / S (S (S n))) i (θ / ₂)%A).
        assert (H : 2 ^ S i / S (S (S n)) ≤ 2 ^ i). {
          rewrite Nat.pow_succ_r'.
          apply Nat.div_le_upper_bound; [ easy | ].
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
destruct i; [ cbn in Hni; flia Hni Hmi | ].
apply rngl_sin_nonneg_angle_le_straight.
apply angle_mul_div_pow2_le_straight.
eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
apply Nat.div_le_upper_bound; [ easy | ].
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

Theorem angle_lim_move_0_r :
  ∀ f θ, angle_lim f θ → angle_lim (λ i, (f i - θ)%A) 0%A.
Proof.
intros * Hlim.
progress unfold angle_lim in Hlim.
progress unfold angle_lim.
intros ε Hε.
specialize (Hlim ε Hε).
destruct Hlim as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
now rewrite angle_eucl_dist_move_0_r in HN.
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
specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as H2.
rewrite (rngl_add_diag2 Hon) in H2.
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

Theorem angle_add_mul_r_diag_r : ∀ n θ, (θ + n * θ)%A = (S n * θ)%A.
Proof. easy. Qed.

Theorem angle_right_div_2_lt :
  ∀ θ,
  (rngl_cos θ < rngl_sin θ)%L
  → (0 ≤ rngl_sin θ)%L
  → (0 ≤ rngl_cos θ)%L
  → (angle_right / ₂ < θ)%A.
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
  rngl_sin (7 * (angle_right / ₂)) = (- √(1 / 2))%L.
Proof.
replace 7 with (2 + 5) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite rngl_sin_add_right_l.
apply rngl_cos_5_right_div_2.
Qed.

Theorem rngl_cos_7_right_div_2 :
  rngl_cos (7 * (angle_right / ₂)) = √(1 / 2)%L.
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
  → (θ < 3 * (angle_right / ₂))%A.
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
  → (5 * (angle_right / ₂) < θ)%A.
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
rewrite (rngl_leb_opp_r Hop Hor), (rngl_opp_0 Hop).
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
  → (5 * (angle_right / ₂) < θ)%A.
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
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
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
  → (θ < 7 * (angle_right / ₂))%A.
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
rewrite (rngl_leb_opp_r Hop Hor), (rngl_opp_0 Hop).
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
  → (angle_right / ₂ < θ)%A.
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
  → (θ < 3 * (angle_right / ₂))%A.
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
  → (θ < 7 * (angle_right / ₂))%A.
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
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
generalize Hs; intros H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
rewrite rngl_sin_7_right_div_2.
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
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
  → (angle_right / ₂ < θ < 3 * (angle_right / ₂))%A ∨
    (5 * (angle_right / ₂) < θ < 7 * (angle_right / ₂))%A.
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
do 2 rewrite (rngl_leb_opp_r Hop Hor), (rngl_opp_0 Hop).
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
  rewrite (rngl_leb_opp_r Hop Hor).
  rewrite (rngl_opp_0 Hop).
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
  → (n * (θ / ₂^i) ≠ 0)%A.
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
remember ((n - 2 ^ i) * (θ / ₂^i))%A as θ' eqn:Hθ'.
assert (Htt : (θ' / ₂ < θ / ₂)%A). {
  apply angle_div_2_lt_compat.
  rewrite Hθ'.
  now apply angle_div_2_pow_mul_lt_angle.
}
apply (angle_add_lt_mono_l (θ' / ₂)) in Htt; cycle 1. {
  apply angle_add_overflow_div_2_div_2.
} {
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
  → (m * ((n * θ) / ₂))%A = (m * n * (θ / ₂))%A.
Proof.
intros * Haov.
rewrite <- angle_mul_nat_assoc.
f_equal.
symmetry.
now apply angle_mul_nat_div_2.
Qed.

Theorem angle_le_sub_diag :
  ∀ θ1 θ2,
  (θ2 ≤ θ1)%A
  → (θ1 - θ2 ≤ θ1)%A.
Proof.
destruct_ac.
intros * H21.
progress unfold angle_leb in H21.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin (θ1 - θ2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hzs2, Hzs12.
destruct zs12. {
  destruct zs1; [ | easy ].
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs1, Hzs2, Hzs12, H21.
  apply rngl_leb_le.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    rewrite <- (angle_sub_add θ1 θ2) at 1.
    assert (Hzc2 : (0 ≤ rngl_cos θ2)%L). {
      now apply (rngl_le_trans Hor _ (rngl_cos θ1)).
    }
    apply quadrant_1_rngl_cos_add_le_cos_l; [ easy | easy | cbn | easy ].
    rewrite (rngl_mul_opp_r Hop), (rngl_sub_opp_r Hop).
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  cbn.
  rewrite (rngl_mul_opp_r Hop), (rngl_sub_opp_r Hop).
  apply (rngl_le_sub_le_add_l Hop Hor).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_le_trans Hor _ 0). {
    apply (rngl_lt_le_incl Hor) in Hc1z.
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ easy | ].
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply (rngl_leb_gt Hor) in Hzs12.
destruct zs2. 2: {
  destruct zs1; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs1, Hzs2.
  apply rngl_leb_le in H21.
  apply rngl_leb_le.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    exfalso.
    assert (Hzc1 : (0 ≤ rngl_cos θ1)%L). {
      now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
    }
    change_angle_add_r θ1 angle_right.
    rewrite angle_sub_sub_swap in Hzs12.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    progress sin_cos_add_sub_right_hyp T H21.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    change_angle_add_r θ2 angle_right.
    rewrite angle_sub_sub_distr in Hzs12.
    progress sin_cos_add_sub_right_hyp T Hzc2.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T H21.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    apply (rngl_opp_lt_compat Hop Hor) in Hzs12.
    rewrite (rngl_opp_0 Hop) in Hzs12.
    rewrite <- rngl_sin_sub_anticomm in Hzs12.
    apply (rngl_nlt_ge Hor) in H21.
    apply H21; clear H21.
    apply rngl_sin_incr_lt.
    split. {
      progress unfold angle_ltb.
      generalize Hzc1; intros H.
      apply rngl_leb_le in H.
      rewrite H; clear H.
      generalize Hzc2; intros H.
      apply rngl_leb_le in H.
      rewrite H; clear H.
      apply rngl_ltb_lt.
      apply quadrant_1_sin_sub_pos_cos_lt; try easy; cycle 1.
      now apply (rngl_lt_le_incl Hor) in Hzs1.
      now apply (rngl_lt_le_incl Hor) in Hzs2.
    }
    progress unfold angle_leb.
    generalize Hzc2; intros H.
    apply rngl_leb_le in H.
    rewrite H; clear H; cbn.
    specialize (rngl_0_le_1 Hon Hop Hor) as H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    apply rngl_leb_le.
    now apply (rngl_lt_le_incl Hor) in Hzs2.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    exfalso.
    change_angle_add_r θ1 angle_right.
    rewrite angle_sub_sub_swap in Hzs12.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T H21.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    change_angle_add_r θ2 angle_straight.
    rewrite angle_sub_sub_distr in Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    progress sin_cos_add_sub_straight_hyp T H21.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; cbn.
    rewrite (rngl_mul_opp_r Hop), (rngl_sub_opp_r Hop).
    apply (rngl_lt_le_incl Hor) in Hzs1, Hc2z, Hzs2.
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  change_angle_add_r θ1 angle_straight.
  rewrite angle_sub_sub_swap in Hzs12 |-*.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T H21.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  progress sin_cos_add_sub_straight_goal T.
  change_angle_add_r θ2 angle_straight.
  rewrite angle_sub_sub_distr in Hzs12 |-*.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_hyp T H21.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_l Hop) in H21.
  apply -> (rngl_le_sub_0 Hop Hor) in H21.
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
  now apply rngl_sin_sub_nonneg.
}
apply rngl_leb_le in Hzs2.
destruct zs1. {
  exfalso.
  apply rngl_leb_le in Hzs1, H21.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply rngl_sin_sub_nonneg.
}
clear H21.
apply (rngl_leb_gt Hor) in Hzs1.
apply rngl_leb_le.
rewrite <- (angle_sub_add θ1 θ2) at 2.
apply rngl_cos_le_cos_add; [ | easy | ].
now apply (rngl_lt_le_incl Hor) in Hzs12.
now rewrite angle_sub_add.
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
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
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

Theorem angle_le_add_r :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (θ1 ≤ θ1 + θ2)%A.
Proof.
intros * Haov.
progress unfold angle_add_overflow in Haov.
apply Bool.not_true_iff_false in Haov.
now apply angle_nlt_ge in Haov.
Qed.

Theorem angle_le_pow2_log2 :
  ∀ n θ1 θ2,
  n ≠ 0
  → angle_mul_nat_overflow n θ1 = false
  → (n * θ1 ≤ θ2
  → θ1 ≤ θ2 / ₂^Nat.log2 n)%A.
Proof.
intros * Hnz Haov Hn.
apply Nat.neq_0_lt_0 in Hnz.
rewrite <- (angle_div_2_pow_mul_2_pow (Nat.log2 n) θ1).
rewrite <- angle_div_2_pow_mul. 2: {
  apply (angle_mul_nat_not_overflow_le_l _ n); [ | easy ].
  now apply Nat.log2_spec.
}
apply angle_div_2_pow_le.
apply (angle_le_trans _ (n * θ1)); [ | easy ].
apply angle_mul_le_mono_r; [ easy | ].
now apply Nat.log2_spec.
Qed.

Theorem seq_angle_to_div_nat_div_2_le_straight_div_pow2_log2 :
  ∀ n i θ,
  n ≠ 0
  → (seq_angle_to_div_nat θ n i / ₂ ≤ angle_straight / ₂^Nat.log2 n)%A.
Proof.
intros * Hnz.
progress unfold seq_angle_to_div_nat.
assert (Hin : 2 ^ i / n ≤ 2 ^ i). {
  apply Nat.div_le_upper_bound; [ easy | ].
  (* lemma *)
  rewrite Nat.mul_comm.
  apply Nat_mul_le_pos_r.
  destruct n; [ easy | ].
  now apply -> Nat.succ_le_mono.
}
rewrite <- angle_mul_nat_div_2. 2: {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)); [ easy | ].
  apply angle_mul_nat_overflow_pow_div.
}
rewrite <- angle_div_2_pow_succ_r_1.
apply angle_le_pow2_log2; [ easy | | ]. {
  apply Bool.not_true_iff_false.
  intros H.
  apply angle_mul_nat_overflow_true_assoc in H.
  apply Bool.not_false_iff_true in H.
  apply H; clear H.
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). {
    now apply Nat.mul_div_le.
  }
  rewrite angle_div_2_pow_succ_r_2.
  apply angle_mul_nat_overflow_pow_div.
}
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. 2: {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)); [ easy | ].
  apply angle_mul_nat_overflow_pow_div.
}
rewrite angle_mul_nat_div_2; [ apply angle_div_2_le_straight | ].
(* lemma *)
apply Bool.not_true_iff_false.
intros H.
apply angle_mul_nat_overflow_true_assoc in H.
apply Bool.not_false_iff_true in H.
apply H; clear H.
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). 2: {
  apply angle_mul_nat_overflow_pow_div.
}
now apply Nat.mul_div_le.
Qed.

Theorem angle_le_pow2_pred :
  ∀ n θ1 θ2,
  n ≠ 0
  → (θ1 / ₂ ≤ θ2 / ₂^n)%A
  → (θ1 ≤ θ2 / ₂^(n-1))%A.
Proof.
intros * Hnz H12.
destruct n; [ easy | clear Hnz ].
rewrite Nat_sub_succ_1.
specialize (angle_mul_le_mono_l _ _ H12 2) as H1.
rewrite angle_div_2_pow_succ_r_1 in H1.
do 2 rewrite angle_div_2_mul_2 in H1.
apply H1.
rewrite <- (Nat.mul_1_r 2).
now apply angle_mul_nat_overflow_mul_2_div_2.
Qed.

Theorem seq_angle_to_div_nat_le_straight_div_pow2_log2_pred :
  ∀ n i θ,
  n ≠ 1
  → (seq_angle_to_div_nat θ n i ≤ angle_straight / ₂^(Nat.log2 n - 1))%A.
Proof.
intros * Hn1.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  apply angle_nonneg.
}
specialize seq_angle_to_div_nat_div_2_le_straight_div_pow2_log2 as H1.
specialize (H1 n i θ Hnz).
apply angle_le_pow2_pred; [ | easy ].
intros H.
apply Nat.log2_null in H.
destruct n; [ easy | ].
apply Nat.succ_le_mono in H.
apply Nat.le_0_r in H.
now subst n.
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
  eapply le_trans; [ now apply Nat.div_mul_le | ].
  apply Nat.div_le_upper_bound; [ easy | ].
  apply Nat.mul_le_mono_r.
  now apply Nat.lt_le_incl in Hmi.
}
clear m Hmi.
(*
clear Hts.
(*
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n.
  rewrite Nat.div_1_r.
  rewrite angle_div_2_pow_mul_2_pow.
(* ah merde *)
...
*)
eapply angle_add_overflow_le_lt. {
  apply seq_angle_to_div_nat_le_straight_div_pow2_log2_pred.
}
...
*)
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
apply Nat.div_le_upper_bound; [ easy | ].
rewrite Nat.pow_succ_r'.
apply Nat.mul_le_mono_r.
now do 2 apply -> Nat.succ_le_mono.
Qed.

Theorem angle_div_2_pow_succ_mul_lt_straight :
  rngl_characteristic T ≠ 1 →
  ∀ n i θ,
  n ≤ 2 ^ i
  → (n * (θ / ₂^S i) < angle_straight)%A.
Proof.
intros Hc1 * Hni.
apply (angle_add_diag_not_overflow Hc1).
apply angle_mul_nat_overflow_distr_add_overflow.
rewrite Nat_add_diag.
rewrite angle_div_2_pow_succ_r_1.
apply angle_mul_nat_overflow_mul_2_div_2.
now apply angle_mul_nat_overflow_div_pow2.
Qed.

Theorem rngl_cos_div_pow2_2_nonneg :
  ∀ θ, (0 ≤ rngl_cos (θ / ₂^2))%L.
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
  ∀ n θ, 2 ≤ n → (0 ≤ rngl_cos (θ / ₂^n))%L.
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

Theorem Nat_pow2_log2_up_succ :
  ∀ n, Nat.log2_up (S n) = S (Nat.log2_up n) ↔ 2 ^ Nat.log2_up n = n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
destruct (Nat.eq_dec n 1) as [H| H]; [ now subst n | ].
apply Nat.neq_0_lt_0 in Hnz.
assert (Hn1 : 1 < n). {
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  now apply -> Nat.succ_lt_mono.
}
clear H.
split; intros Hn. {
  rewrite Nat.log2_up_eqn in Hn; [ | now apply -> Nat.succ_lt_mono ].
  apply Nat.succ_inj in Hn.
  cbn in Hn.
  apply Nat.log2_log2_up_exact in Hn; [ | easy ].
  destruct Hn as (m, Hm); subst n.
  now rewrite Nat.log2_up_pow2.
} {
  specialize (Nat.log2_up_succ_or n) as H1.
  destruct H1 as [H1| H1]; [ easy | ].
  exfalso.
  rewrite <- Hn in H1 at 1.
  rewrite Nat.log2_up_succ_pow2 in H1; [ | easy ].
  specialize (Nat.log2_up_eqn n Hn1) as H2.
  rewrite <- H1 in H2.
  apply Nat.succ_inj in H2.
  rewrite <- Hn in H2 at 2.
  rewrite Nat.log2_pred_pow2 in H2; [ | now apply Nat.log2_up_pos ].
  destruct (Nat.log2_up n); [ now cbn in Hn; subst n | ].
  cbn in H2.
  now apply Nat.neq_succ_diag_l in H2.
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
  ∀ i j θ, j ≤ i → (2 ^ (i - j) * (θ / ₂^i) = θ / ₂^j)%A.
Proof.
intros * Hji.
replace i with (j + (i - j)) at 1 by flia Hji.
rewrite angle_div_2_pow_add_r.
apply angle_div_2_pow_mul_2_pow.
Qed.

Theorem seq_angle_to_div_nat_3_le :
  ∀ i θ, (seq_angle_to_div_nat θ 3 i ≤ 3 * (θ / ₂^3))%A.
Proof.
intros.
(* θ/3 ≤ 3(θ/8)
   1/3 ≤ 3/8
   8 ≤ 9 *)
progress unfold seq_angle_to_div_nat.
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i. {
  cbn - [ angle_mul_nat angle_div_2_pow ].
  rewrite angle_mul_1_l.
  replace 3 with (2 + 1) at 2 by easy.
  rewrite angle_mul_add_distr_r.
  rewrite angle_mul_1_l.
  remember (θ / ₂^3)%A as θ' eqn:Hθ.
  rewrite Hθ at 2.
  rewrite angle_div_2_pow_succ_r_1 in Hθ; subst θ'.
  rewrite angle_div_2_mul_2.
  rewrite <- (angle_add_0_r (θ / ₂^2)) at 1.
  apply angle_add_le_mono_l; [ | | apply angle_nonneg ].
  apply angle_add_overflow_0_r.
  apply angle_add_overflow_div_2_div_2.
}
rewrite <- (angle_div_2_pow_mul_pow_sub (3 + i) 3); [ | apply Nat.le_add_r ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm.
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. 2: {
  replace (S (S (S i))) with (3 + i) by easy.
  rewrite Nat.pow_add_r.
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.mul_assoc.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ (3 + i))). {
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply angle_mul_nat_overflow_pow_div.
Qed.

Theorem seq_angle_to_div_nat_4_le :
  ∀ i θ, (seq_angle_to_div_nat θ 4 i ≤ 3 * (θ / ₂^3))%A.
Proof.
intros.
progress unfold seq_angle_to_div_nat.
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i. {
  cbn - [ angle_mul_nat angle_div_2_pow ].
  rewrite angle_mul_1_l.
  replace 3 with (2 + 1) at 2 by easy.
  rewrite angle_mul_add_distr_r.
  rewrite angle_mul_1_l.
  remember (θ / ₂^3)%A as θ' eqn:Hθ.
  rewrite Hθ at 2.
  rewrite angle_div_2_pow_succ_r_1 in Hθ; subst θ'.
  rewrite angle_div_2_mul_2.
  rewrite <- (angle_add_0_r (θ / ₂^2)) at 1.
  apply angle_add_le_mono_l; [ | | apply angle_nonneg ].
  apply angle_add_overflow_0_r.
  apply angle_add_overflow_div_2_div_2.
}
rewrite <- (angle_div_2_pow_mul_pow_sub (3 + i) 3); [ | apply Nat.le_add_r ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm.
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. 2: {
  replace (S (S (S i))) with (3 + i) by easy.
  rewrite Nat.pow_add_r.
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.mul_assoc.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ (3 + i))). {
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply angle_mul_nat_overflow_pow_div.
Qed.

Theorem seq_angle_to_div_nat_5_le :
  ∀ i θ, (seq_angle_to_div_nat θ 5 i ≤ 7 * (θ / ₂^5))%A.
Proof.
intros.
(* 1/5 = 1/8 + 1/16 + 1/128 + ... *)
(* 1/5 < 1/8 + 1/16 + 1/32 = 7/32 *)
progress unfold seq_angle_to_div_nat.
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i. {
  rewrite (Nat_div_less_small 1); [ | cbn; flia ].
  rewrite angle_mul_1_l.
  rewrite <- (angle_div_2_pow_mul_pow_sub 5); [ | cbn; flia ].
  apply angle_mul_le_mono_r; [ | cbn; flia ].
  apply angle_mul_nat_overflow_div_pow2; cbn; flia.
}
destruct i. {
  rewrite (Nat_div_less_small 3); [ | cbn; flia ].
  rewrite <- (angle_div_2_pow_mul_pow_sub 5); [ | cbn; flia ].
  rewrite angle_mul_nat_assoc.
  apply angle_mul_le_mono_r; [ | cbn; flia ].
  apply angle_mul_nat_overflow_div_pow2; cbn; flia.
}
rewrite <- (angle_div_2_pow_mul_pow_sub (5 + i) 5); [ | apply Nat.le_add_r ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm.
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. 2: {
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.mul_assoc.
  replace (S (S (S (S (S i))))) with (5 + i) by easy.
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ (5 + i))). {
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply angle_mul_nat_overflow_pow_div.
Qed.

Theorem seq_angle_to_div_nat_6_le :
  ∀ i θ, (seq_angle_to_div_nat θ 6 i ≤ 3 * (θ / ₂^4))%A.
Proof.
intros.
(* 1/6 = 1/8 + 1/32 + 1/128 + ... *)
(* 1/6 < 1/8 + 1/16 = 3/16 *)
progress unfold seq_angle_to_div_nat.
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i. {
  rewrite (Nat_div_less_small 1); [ | cbn; flia ].
  rewrite angle_mul_1_l.
  rewrite <- (angle_div_2_pow_mul_pow_sub 4); [ | cbn; flia ].
  apply angle_mul_le_mono_r. 2: {
    now cbn; do 2 apply -> Nat.succ_le_mono.
  }
  apply angle_mul_nat_overflow_div_pow2; cbn; flia.
}
rewrite <- (angle_div_2_pow_mul_pow_sub (4 + i) 4); [ | apply Nat.le_add_r ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm.
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. 2: {
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.mul_assoc.
  replace (S (S (S (S i)))) with (4 + i) by easy.
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ (4 + i))). {
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply angle_mul_nat_overflow_pow_div.
Qed.

Theorem seq_angle_to_div_nat_7_le :
  ∀ i θ, (seq_angle_to_div_nat θ 7 i ≤ 3 * (θ / ₂^4))%A.
Proof.
(* same proof as seq_angle_to_div_nat_6_le *)
intros.
progress unfold seq_angle_to_div_nat.
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i. {
  rewrite (Nat_div_less_small 1); [ | cbn; flia ].
  rewrite angle_mul_1_l.
  rewrite <- (angle_div_2_pow_mul_pow_sub 4); [ | cbn; flia ].
  apply angle_mul_le_mono_r. 2: {
    now cbn; do 2 apply -> Nat.succ_le_mono.
  }
  apply angle_mul_nat_overflow_div_pow2; cbn; flia.
}
rewrite <- (angle_div_2_pow_mul_pow_sub (4 + i) 4); [ | apply Nat.le_add_r ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm.
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. 2: {
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.mul_assoc.
  replace (S (S (S (S i)))) with (4 + i) by easy.
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ (4 + i))). {
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply angle_mul_nat_overflow_pow_div.
Qed.

Theorem seq_angle_to_div_nat_8_le :
  ∀ i θ, (seq_angle_to_div_nat θ 8 i ≤ 3 * (θ / ₂^4))%A.
Proof.
(* same proof as seq_angle_to_div_nat_6_le *)
intros.
progress unfold seq_angle_to_div_nat.
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i. {
  rewrite (Nat_div_less_small 1); [ | cbn; flia ].
  rewrite angle_mul_1_l.
  rewrite <- (angle_div_2_pow_mul_pow_sub 4); [ | cbn; flia ].
  apply angle_mul_le_mono_r. 2: {
    now cbn; do 2 apply -> Nat.succ_le_mono.
  }
  apply angle_mul_nat_overflow_div_pow2; cbn; flia.
}
rewrite <- (angle_div_2_pow_mul_pow_sub (4 + i) 4); [ | apply Nat.le_add_r ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm.
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. 2: {
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.mul_assoc.
  replace (S (S (S (S i)))) with (4 + i) by easy.
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ (4 + i))). {
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply angle_mul_nat_overflow_pow_div.
Qed.

Theorem seq_angle_to_div_nat_9_le :
  ∀ i θ, (seq_angle_to_div_nat θ 9 i ≤ 15 * (θ / ₂^7))%A.
Proof.
intros.
progress unfold seq_angle_to_div_nat.
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i; [ apply angle_nonneg | ].
destruct i. {
  rewrite (Nat_div_less_small 1); [ | cbn; flia ].
  rewrite angle_mul_1_l.
  eapply (angle_le_trans _ (2 ^ 3 * (θ / ₂^7))). {
    replace 7 with (4 + 3) by easy.
    rewrite angle_div_2_pow_add_r.
    rewrite angle_div_2_pow_mul_2_pow.
    apply angle_le_refl.
  }
  apply angle_mul_le_mono_r; [ | cbn; flia ].
  apply angle_mul_nat_overflow_div_pow2; cbn; flia.
}
destruct i. {
  rewrite (Nat_div_less_small 3); [ | cbn; flia ].
  eapply (angle_le_trans _ (3 * (2 ^ 2 * (θ / ₂^7)))). {
    replace 7 with (5 + 2) by easy.
    rewrite angle_div_2_pow_add_r.
    rewrite angle_div_2_pow_mul_2_pow.
    apply angle_le_refl.
  }
  rewrite angle_mul_nat_assoc.
  apply angle_mul_le_mono_r; [ | cbn; flia ].
  apply angle_mul_nat_overflow_div_pow2; cbn; flia.
}
destruct i. {
  rewrite (Nat_div_less_small 7); [ | cbn; flia ].
  eapply (angle_le_trans _ (7 * (2 ^ 1 * (θ / ₂^7)))). {
    replace 7 with (6 + 1) by easy.
    rewrite angle_div_2_pow_add_r.
    rewrite angle_div_2_pow_mul_2_pow.
    apply angle_le_refl.
  }
  rewrite Nat.pow_1_r.
  rewrite angle_mul_nat_assoc.
  apply angle_mul_le_mono_r; [ | cbn; flia ].
  apply angle_mul_nat_overflow_div_pow2; cbn; flia.
}
replace (S (S (S (S (S (S (S i))))))) with (7 + i) by easy.
rewrite <- (angle_div_2_pow_mul_pow_sub (7 + i) 7); [ | apply Nat.le_add_r ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm.
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. 2: {
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.mul_assoc.
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ (7 + i))). {
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; cbn; flia.
}
apply angle_mul_nat_overflow_pow_div.
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
(*
Definition old_fst_1_len a b :=
  fst (old_rank_fst_loop b 0 (snd (old_rank_fst_loop b 1 a b)) b).
*)

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
(*
Print rank_fst_loop.
Compute (map (λ b,
  (2 ^ (Nat.log2_up b - 1),
   snd (rank_fst_loop b 1 1 b))
) (seq 0 33)).
Compute (map (λ b,
let a := 1 in
Nat.eqb
(
  fst_1_len a b)
(
  new_fst_1_len b
)
) (seq 0 80)).

(* j'aimerais pouvoir traiter a/b et non pas seulement 1/b dans
   ce nouveau new_fst_1_len, histoire d'être plus général, mais
   bon, si j'y arrive pas, c'est peut-être pas si grave, chais
   pas *)
...
*)

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

Theorem Nat_eq_div_1 : ∀ a b, a / b = 1 ↔ b ≤ a < 2 * b.
Proof.
intros.
split; intros Hab. {
  destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
  apply Nat_div_less_small_iff in Hab; [ | easy ].
  now rewrite Nat.mul_1_l in Hab.
} {
  apply Nat_div_less_small.
  now rewrite Nat.mul_1_l.
}
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
    now apply Nat.mul_div_le.
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
rewrite Nat.div_mul_cancel_l; [ | easy | easy ].
destruct (2 * a / b =? k); [ easy | ].
do 2 rewrite fst_let.
f_equal.
rewrite Nat.mul_mod_distr_l; [ | easy | easy ].
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
  eapply lt_le_trans; [ | apply Ha ].
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
apply plus_minus. (* y a-t-il une version plus moderne ? *)
apply Nat_eq_log2_up; [ flia H2n | ].
split. {
  apply Nat.div_lt_upper_bound; [ easy | ].
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  progress unfold rank_fst_1.
  rename H2n into Hn.
  now apply (rank_fst_1_log2_up_lemma 0).
}
progress unfold rank_fst_1.
rewrite (Nat.add_1_l (fst _)).
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

(*
Theorem rank_fst_loop_enough_iter :
  ∀ k it1 it2 a b,
  k ≤ 1
  → a < b
  → 1 < b
  → b ≤ it1
  → b ≤ it2
  → rank_fst_loop it1 k a b = rank_fst_loop it2 k a b.
Proof.
intros * Hk1 Hab H1b Hit1 Hit2.
(*
Compute (map (λ b,
  let k := 2 in
  let a := 2 in
  let it1 := b + 7 in
  let it2 := b + 2 in
  rank_fst_loop it1 k a b = rank_fst_loop it2 k a b
) (seq 3 20)).
(* ok *)
...
*)
revert a Hab.
induction it1; intros; [ now apply Nat.le_0_r in Hit1; subst b | ].
destruct it2; [ now apply Nat.le_0_r in Hit2; subst b | ].
cbn - [ "*" ].
remember (2 * a / b =? k) as abk eqn:Habk.
symmetry in Habk.
destruct abk; [ easy | ].
apply Nat.eqb_neq in Habk.
apply Nat_neq_div in Habk.
destruct Habk as [Habk| Habk]. {
  destruct k; [ easy | ].
  destruct k; [ | flia Hk1 ].
  rewrite Nat.mul_1_l in Habk.
  clear Hk1 Hab.
  rewrite Nat.mod_small; [ | easy ].
  destruct (Nat.eq_dec b (S it1)) as [Hb1| Hb1]. {
...
Search (rank_fst_loop _ _ (2 * _)).
Theorem fst_rank_fst_loop_1_twice :
  ∀ it a b,
  a ≠ 0
  → 2 * a < b ≤ it
  → fst (rank_fst_loop it 1 a b) = S (fst (rank_fst_loop it 1 (2 * a) b)).
Proof.
intros * Haz Hit.
(*
Compute (
  let a := 1 in
map (λ b,
  let it := b in
  let k := 1 in
  fst (rank_fst_loop it k a b) = S (fst (rank_fst_loop it k (2 * a) b))
) (seq (2 * a + 1) 40)).
(* ok *)
*)
induction it; [ flia Hit | ].
cbn - [ "*" ].
remember (2 * (2 * a) / b =? 1) as abk2 eqn:Habk2.
symmetry in Habk2.
destruct abk2. {
  apply Nat.eqb_eq in Habk2.
  apply Nat_eq_div_1 in Habk2.
  remember (2 * a / b =? 1) as abk eqn:Habk.
  symmetry in Habk.
  destruct abk. {
    apply Nat.eqb_eq in Habk.
    apply Nat_eq_div_1 in Habk.
    flia Habk2 Habk.
  }
  apply Nat.eqb_neq in Habk.
  apply Nat_neq_div_1 in Habk; [ | flia Hit ].
  rewrite fst_let; f_equal.
  cbn - [ "*" ].
  destruct Habk as [Habk| Habk]. {
    rewrite Nat.mod_small; [ | easy ].
    clear Hit IHit.
    destruct Habk2 as (H1, _).
    rename Habk into H2.
    induction it; intros; [ easy | ].
    cbn - [ "*" ].
    rewrite (Nat_div_less_small 1); [ easy | flia H1 H2 ].
  }
  flia Hit Habk.
}
apply Nat.eqb_neq in Habk2.
apply Nat_neq_div_1 in Habk2; [ | flia Hit ].
rewrite fst_if, fst_let, fst_let.
rewrite Nat.div_small; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
cbn - [ "*" ].
f_equal.
destruct Habk2 as [Habk2| Habk2]. {
  rewrite Nat.mod_small; [ | easy ].
(*
Compute (
  let a := 1 in
map (λ b,
  let it := b - 1 in
  fst (rank_fst_loop it 1 (2 * a) b) = S (fst (rank_fst_loop it 1 (2 * (2 * a)) b))
) (seq (4 * a + 1) 80)).
(* bin oui, pourtant ça marche *)
*)
  destruct (Nat.eq_dec b (S it)) as [Hbi| Hbi]. {
    subst b.
Compute (
let a := 1 in
map (λ it,
  fst (rank_fst_loop it 1 (2 * a) (S it)) = S (fst (rank_fst_loop it 1 (2 * (2 * a)) (S it)))
) (seq 4 20)).
(* ah zut, hein *)
...
  clear Hit1 IHit1.
  destruct it1; [ flia Htab Hab | ].
  do 2 apply Nat.succ_le_mono in Hit2.
  destruct it2. {
    apply Nat.le_0_r in Hit2; subst it1.
    destruct a; [ easy | ].
    apply Nat.succ_lt_mono in Hab.
    now apply Nat.lt_1_r in Hab; subst a.
  }
  cbn - [ "*" "/" "mod" ].
  remember (_ =? 0) as z eqn:Hz.
  symmetry in Hz.
  destruct z; [ easy | ].
  apply Nat.eqb_neq in Hz.
  apply Nat_div_not_small_iff in Hz; [ | easy ].
(* pas l'air simple *)
...

Theorem rank_fst_1_1_pow2 : ∀ n, rank_fst_1 1 (2 ^ S n) = n.
Proof.
intros.
(*
Compute (map (λ n,
  rank_fst_1 1 (2 ^ S n) = n
) (seq 0 10)).
...
ok *)
progress unfold rank_fst_1.
...
rewrite Nat.pow_succ_r'.
Compute (map (λ n,
  rank_fst_1 1 (2 * n) =
  S (rank_fst_1 1 n)
) (seq 0 20)).
Theorem fst_rank_fst_loop_twice :
  ∀ n, 1 < n → rank_fst_1 1 (2 * n) = S (rank_fst_1 1 n).
Proof.
intros * Hn.
progress unfold rank_fst_1.
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hn.
cbn - [ "*" "/" "mod" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" ].
rewrite Nat.mul_1_r.
remember (2 / S n =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  apply Nat.succ_le_mono in Hn1.
  apply Nat.le_1_r in Hn1.
  now destruct Hn1; subst n.
}
apply Nat.eqb_neq in Hn1.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
apply Nat.succ_lt_mono in Hn1.
clear Hn; rename Hn1 into Hn.
(**)
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hn.
cbn - [ "*" "/" "mod" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" ].
progress replace (2 * 2) with 4 by easy.
remember (4 / S (S n) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  destruct n; [ easy | clear Hn ].
  do 3 apply Nat.succ_le_mono in Hn1.
  apply Nat.le_1_r in Hn1.
  now destruct Hn1; subst n.
}
apply Nat.eqb_neq in Hn1.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
do 2 apply Nat.succ_lt_mono in Hn1.
clear Hn; rename Hn1 into Hn.
(*
Theorem glop :
  ∀ m n,
  2 < n
  → fst (rank_fst_loop (2 * (m + n)) 1 1 (2 * (m + n))) =
    S m + fst (rank_fst_loop n 1 (2 ^ m) (m + n)).
Proof.
Admitted.
now apply (glop 2).
...
*)
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hn.
cbn - [ "*" "/" "mod" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" ].
progress replace (2 * 4) with 8 by easy.
remember (8 / S (S (S n)) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  destruct n; [ easy | clear Hn ].
  destruct n; [ flia Hn2 | clear Hn2 ].
  do 4 (destruct n; [ easy | ]).
  now do 8 apply Nat.succ_le_mono in Hn1.
}
apply Nat.eqb_neq in Hn1.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
do 3 apply Nat.succ_lt_mono in Hn1.
clear Hn; rename Hn1 into Hn.
(*
Theorem glop :
  ∀ m n,
  2 ^ m - m < n
  → fst (rank_fst_loop (2 * (m + n)) 1 1 (2 * (m + n))) =
    S m + fst (rank_fst_loop n 1 (2 ^ m) (m + n)).
Proof.
Admitted.
now apply (glop 3).
...
*)
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hn.
cbn - [ "*" "/" "mod" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" ].
progress replace (2 * 8) with 16 by easy.
remember (16 / S (S (S (S n))) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  do 5 (destruct n; [ flia Hn | ]).
  clear Hn.
  do 9 apply Nat.succ_le_mono in Hn1.
  do 8 (destruct n; [ easy | ]).
  do 7 apply Nat.succ_le_mono in Hn1.
  flia Hn1.
}
apply Nat.eqb_neq in Hn1.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
do 4 apply Nat.succ_lt_mono in Hn1.
clear Hn; rename Hn1 into Hn.
Theorem glop :
  ∀ m n,
  2 ^ m - m < n
  → fst (rank_fst_loop (2 * (m + n)) 1 1 (2 * (m + n))) =
    S m + fst (rank_fst_loop n 1 (2 ^ m) (m + n)).
Proof.
intros * Hmn.
Search (rank_fst_loop (2 * _)).
...
revert m Hmn.
induction n; intros; [ easy | ].
rewrite <- Nat.add_succ_comm.
cbn - [ "*" "/" "mod" "^" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" "^" ].
rewrite <- Nat.pow_succ_r'.
remember (2 ^ S m / S (m + n) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  rewrite Nat.add_0_r.
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  rewrite Nat.pow_succ_r' in Hn1, Hn2.
  apply (Nat.add_lt_mono_r _ _ m) in Hmn.
  rewrite Nat.sub_add in Hmn. 2: {
    apply (le_trans _ (S m)); [ | now apply Nat.pow_gt_lin_r ].
    apply Nat.le_succ_diag_r.
  }
  rewrite Nat.mul_comm.
  cbn - [ "/" "mod" "^" ].
  rewrite Nat.div_small; [ | flia Hn1 Hn2 ].
  rewrite Nat.mod_small; [ | flia Hn1 Hn2 ].
  cbn - [ "/" "mod" "^" ].
  rewrite fst_let, fst_if, fst_let.
  cbn - [ "/" "mod" "^" ].
  remember (4 / _ =? 1) as n3 eqn:Hn3.
  symmetry in Hn3.
  destruct n3. {
    apply Nat.eqb_eq in Hn3.
    apply Nat_eq_div_1 in Hn3.
    destruct m; [ easy | exfalso ].
    destruct Hn3 as (Hn3, Hn4).
    cbn in Hn3.
    rewrite Nat.add_succ_r in Hmn.
    rewrite Nat.add_succ_l in Hmn, Hn1, Hn2, Hn4.
    rewrite (Nat.add_comm n) in Hmn.
    destruct m. {
      cbn in Hmn, Hn1, Hn2, Hn3, Hn4.
      do 2 apply Nat.succ_lt_mono in Hmn.
      destruct n; [ easy | flia Hn3 ].
    }
    flia Hn3.
  }
  apply Nat.eqb_neq in Hn3.
  apply Nat_neq_div_1 in Hn3.
  destruct Hn3 as [Hn3| Hn3]. {
    destruct m. {
      cbn in Hmn, Hn1, Hn2, Hn3.
      do 2 apply Nat.succ_lt_mono in Hmn.
      destruct n; [ | flia Hn3 ].
      flia Hn2.
    }
    flia Hn3.
  }
  destruct m. {
    cbn in Hmn, Hn1, Hn2, Hn3.
    apply Nat.succ_lt_mono in Hmn.
    destruct n; [ easy | ].
    destruct n; [ | flia Hn1 ].
    flia Hn3.
  }
  rewrite Nat.mod_small; [ | easy ].
  f_equal; f_equal.
(* ah merde faut réfléchir *)
...
  cbn - [ "*" "/" "mod" "^" ].
  rewrite Nat.mul_comm.
  cbn - [ "/" "mod" "^" ].
  rewrite 
  rewrite Nat_add_diag.
...
destruct m. {
  cbn - [ "*" "/" "mod" ].
...
}
rewrite IHn. 2: {
  rewrite Nat.pow_succ_r'.
  apply (Nat.add_lt_mono_r _ _ (S m)) in Hmn.
  apply (Nat.add_lt_mono_r _ _ (S (S m))).
  rewrite Nat.sub_add in Hmn. 2: {
    apply (le_trans _ (S (S m))); [ | now apply Nat.pow_gt_lin_r ].
    apply Nat.le_succ_diag_r.
  }
  rewrite Nat.sub_add. 2: {
    apply (le_trans _ (2 ^ S m)); [ now apply Nat.pow_gt_lin_r | ].
    rewrite <- Nat_add_diag.
    apply Nat.le_add_r.
  }
  (* ah bin non c'est faux *)
...
Search (_ ≤ _ ^ _).
    apply Nat.pow_gt_lin_r.
... ...
now apply (glop 4).
...
m = 4     12   2^m-m
m = 3     5    2^m-m
m = 2     2    2^m-m
...
progress unfold rank_fst_1.
destruct n; [ easy | ].
Search (rank_fst_1 _ (2 * _)).
...
destruct n; [ easy | ].
...
specialize rank_fst_1_1_pow2_lemma as H1.
replace 2 with (2 ^ 1) at 2 by easy.
apply (H1 (2 ^ n) 0 n); [ easy | ].
now rewrite Nat.sub_0_r.
Qed.
*)

(*
Theorem fst_rank_fst_loop_pow2_succ_lemma :
  ∀ m n,
  fst (rank_fst_loop n 1 (2 ^ S m) (2 ^ (m + n) + 1)) = n.
Proof.
intros.
Compute (map (λ m, map (λ n,
  fst (rank_fst_loop n 1 (2 ^ S m) (2 ^ (m + n) + 1)) = n
) (seq 0 10)) (seq 0 10)).
(* no *)
...
revert m.
induction n; intros; [ easy | ].
cbn - [ "*" "^" ].
assert (Hmn : 2 ^ S m < 2 ^ (m + S n) + 1). {
  rewrite <- (Nat.add_succ_comm m).
  rewrite Nat.pow_add_r.
  eapply le_lt_trans; [ | now apply Nat.lt_add_pos_r ].
  apply Nat_mul_le_pos_r.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite Nat.div_small; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
cbn - [ "*" "^" ].
rewrite fst_let; f_equal.
rewrite <- (Nat.add_succ_comm m).
rewrite <- Nat.pow_succ_r'.
apply IHn.
Qed.
*)

(*
Theorem fst_rank_fst_loop_pow2_succ :
  ∀ n, fst (rank_fst_loop (n + 1) 1 1 (2 ^ n + 1)) = n + 1.
Proof.
intros.
rewrite Nat.add_1_r.
cbn.
assert (Hn : 2 < 2 ^ n + 1). {
  rewrite <- Nat.add_1_r at 1.
  apply Nat.add_lt_mono_r.
...
  apply Nat.lt_add_pos_l.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite Nat.div_small; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
cbn.
rewrite fst_let; f_equal.
apply (fst_rank_fst_loop_pow2_succ_lemma 0 n).
Qed.
*)

(*
Theorem fst_rank_fst_loop_diag :
  ∀ it n, n ≠ 0 → fst (rank_fst_loop it 1 n n) = 0.
Proof.
intros * Hnz.
destruct it; [ easy | ].
cbn - [ "*" ].
rewrite Nat.div_mul; [ | easy ].
rewrite Nat.mod_mul; [ | easy ].
cbn - [ "*" ].
rewrite fst_let.
...
now rewrite Nat.div_same.
Qed.
*)

(*
Theorem fst_rank_fst_loop_eq_succ_lemma :
  ∀ it a b n,
  a ≠ 0
  → Nat.log2_up b = n + it
  → 2 ^ n * a < b
  → fst (rank_fst_loop it 1 (2 ^ n * a) b) =
    S (fst (rank_fst_loop it 1 (2 ^ S n * a) b)).
Proof.
intros * Haz Hb Hab.
revert a b n Haz Hb Hab.
induction it; intros. {
  exfalso.
  apply Nat.nle_gt in Hab.
  apply Hab; clear Hab.
  rewrite Nat.add_0_r in Hb.
  destruct a; [ easy | ].
  destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
  rewrite Nat.mul_succ_r.
  apply (le_trans _ (2 ^ n)); [ | apply Nat_le_add_l ].
  subst n.
  apply Nat.log2_log2_up_spec.
  now apply Nat.neq_0_lt_0.
}
cbn - [ "*" ].
remember (2 ^ n * a / b =? 1) as ab eqn:H.
symmetry in H.
destruct ab. {
  apply Nat.eqb_eq in H.
  apply Nat_eq_div_1 in H.
  destruct H as (H, _).
  now apply Nat.nlt_ge in H.
}
clear H.
...
rewrite fst_let, fst_if.
f_equal.
cbn - [ "*" ].
rewrite fst_let.
rewrite Nat.mod_small; [ | easy ].
rewrite Nat.mul_assoc.
remember (2 * 2 ^ n * a / b =? 1) as abs eqn:Habs.
symmetry in Habs.
destruct abs. {
  destruct it; [ easy | ].
  cbn - [ "*" ].
  now rewrite Habs.
}
apply Nat.eqb_neq in Habs.
apply Nat_neq_div_1 in Habs.
destruct Habs as [Habs| Habs]. {
  rewrite <- Nat.mul_assoc in Habs.
  apply Nat.mul_le_mono_pos_l in Habs; [ | easy ].
  now apply Nat.nlt_ge in Habs.
}
rewrite Nat.mod_small; [ | easy ].
rewrite Nat.mul_assoc.
rewrite <- Nat.add_succ_comm in Hb.
rewrite <- Nat.pow_succ_r' in Habs |-*.
now apply IHit.
Qed.
*)

(*
Theorem fst_rank_fst_loop_eq_succ :
  ∀ it a b,
  0 < a < b
  → Nat.log2_up b ≤ it
  → fst (rank_fst_loop it 1 a b) = S (fst (rank_fst_loop it 1 (2 * a) b)).
Proof.
intros * Hzab Hit.
Compute (map (λ b,
  let a := 1 in
  let it := Nat.log2_up b in
  fst (rank_fst_loop it 1 a b) = S (fst (rank_fst_loop it 1 (2 * a) b))
) (seq 2 20)).
...
revert a Hzab.
induction it; intros. {
  apply Nat.le_0_r in Hit.
  apply Nat.log2_up_null in Hit.
  flia Hit Hzab.
}
cbn - [ "*" ].
remember (2 * a / b =? 1) as ab eqn:Hab.
symmetry in Hab.
destruct ab. {
  apply Nat.eqb_eq in Hab.
  apply Nat_eq_div_1 in Hab.
...
  exfalso.
...
destruct ab; [ now rewrite Nat.div_small in Hab | ].
rewrite fst_let; f_equal.
remember (2 * a / b =? 1) as ab2 eqn:Hab2.
symmetry in Hab2.
destruct ab2. {
  rewrite Nat.mod_small; [ | easy ].
  cbn - [ "*" ].
  destruct it; [ easy | ].
  cbn - [ "*" ].
  now rewrite Hab2.
}
rewrite fst_let.
rewrite Nat.mod_small; [ | easy ].
apply Nat.eqb_neq in Hab2.
apply Nat_neq_div_1 in Hab2.
destruct Hab2 as [Hab2| Hab2]. {
  apply Nat.mul_le_mono_pos_l in Hab2; [ | easy ].
  now apply Nat.nlt_ge in Hab2.
}
rewrite Nat.mod_small; [ | easy ].
destruct (Nat.eq_dec (Nat.log2_up b) (S it)) as [Hbs| Hbs]. 2: {
  apply IHit; [ flia Hit Hbs | ].
  split; [ | easy ].
  now apply Nat.mul_pos_pos.
}
rewrite Nat.mul_assoc.
specialize (fst_rank_fst_loop_eq_succ_lemma it a b 1) as H1.
assert (H : a ≠ 0) by flia Hzab.
specialize (H1 H Hbs Hab2); clear H.
rewrite Nat.pow_1_r in H1.
apply H1.
Qed.
*)

(*
Theorem fst_rank_fst_loop_pow2_mul :
  ∀ p m a b it,
  0 < a
  → 2 ^ S (p + m) * a < b
  → b ≤ 2 ^ S (S (p + m)) * a
  → Nat.log2_up b = p + it
  → m = fst (rank_fst_loop it 1 (2 ^ S (S p) * a) b).
Proof.
intros * Hza Hmab Hbma Hit.
revert p m Hmab Hbma Hit.
induction it; intros. {
  cbn.
  rewrite Nat.add_0_r in Hit.
  apply Nat_eq_log2_up in Hit; [ | now intros H1; subst b ].
  destruct Hit as (Hpb, Hbp).
  destruct m; [ easy | exfalso ].
  apply Nat.nle_gt in Hmab.
  apply Hmab; clear Hmab.
  eapply le_trans; [ apply Hbp | ].
  apply (le_trans _ (2 ^ p * a)); [ now apply Nat_mul_le_pos_r | ].
  apply Nat.mul_le_mono_r.
  apply Nat.pow_le_mono_r; [ easy | ].
  rewrite <- Nat.add_succ_r.
  apply Nat.le_add_r.
}
cbn - [ "*" "^" ].
rewrite fst_if, fst_let.
cbn - [ "*" "^" ].
remember (2 ^ S (S p) * a / b =? 1) as pab eqn:Hpab.
symmetry in Hpab.
destruct pab. {
  apply Nat.eqb_eq in Hpab.
  apply Nat_eq_div_1 in Hpab.
  destruct Hpab as (Hbpa, Hpab).
  rewrite Nat.pow_succ_r' in Hpab.
  rewrite <- Nat.mul_assoc in Hpab.
  apply Nat.mul_lt_mono_pos_l in Hpab; [ | easy ].
...
  destruct m; [ easy | exfalso ].
  apply Nat.nle_gt in Hmab.
  apply Hmab; clear Hmab.
  eapply le_trans; [ apply Hbpa | ].
  apply Nat.mul_le_mono_r.
  apply Nat.pow_le_mono_r; [ easy | ].
  rewrite Nat.add_succ_r.
  do 2 apply -> Nat.succ_le_mono.
  apply Nat.le_add_r.
}
apply Nat.eqb_neq in Hpab.
apply Nat_neq_div_1 in Hpab.
destruct Hpab as [Hpab| Hpab]. {
  rewrite Nat.pow_succ_r' in Hpab.
  rewrite <- Nat.mul_assoc in Hpab.
  apply Nat.mul_le_mono_pos_l in Hpab; [ | easy ].
  exfalso.
  apply Nat.nle_gt in Hmab.
  apply Hmab; clear Hmab.
  eapply le_trans; [ apply Hpab | ].
  apply Nat.mul_le_mono_r.
  apply Nat.pow_le_mono_r; [ easy | ].
  apply -> Nat.succ_le_mono.
  apply Nat.le_add_r.
}
rewrite Nat.mod_small; [ | easy ].
destruct m. {
  rewrite Nat.add_0_r in Hbma.
  now apply Nat.nle_gt in Hpab.
}
f_equal.
rewrite Nat.mul_assoc.
rewrite <- Nat.pow_succ_r'.
rewrite <- Nat.add_succ_comm in Hit, Hbma, Hmab.
now apply IHit.
Qed.
*)

(*
Theorem two_pow_mul_fst_rank_fst_loop :
  ∀ m n,
  m ≠ 0
  → 2 ^ m - (2 + m) < n
  → 2 ^ (m + fst (rank_fst_loop (S n) 1 (2 ^ (1 + m)) (2 + m + n))) <
      2 + m + n.
Proof.
intros * Hmz Hn.
(* devrait pouvoir se prouver...
   auquel cas, l'hypothèse m ≠ 0 serait inutile
clear Hmz.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  subst m.
  cbn in Hn.
  cbn - [ "/" "mod" "*" ].
  rewrite Nat.mul_1_r.
  rewrite Nat.div_small; [ | flia Hn ].
  rewrite Nat.mod_small; [ | flia Hn ].
  rewrite fst_if, fst_let.
  cbn - [ "/" "mod" "*" ].
  rewrite <- Nat.pow_succ_r'.
Search (_ ^ S _).
...
  destruct n; [ easy | ].
  cbn - [ "/" "mod" "*" ].
  rewrite fst_if, fst_let.
  cbn - [ "/" "mod" "*" ].
  remember (2 * 2 / S (S (S n)) =? 1) as n2 eqn:Hn2.
  symmetry in Hn2.
  destruct n2; [ cbn; flia | ].
  apply Nat.eqb_neq in Hn2.
  apply Nat_neq_div_1 in Hn2.
  destruct Hn2 as [Hn2| Hn2]; [ flia Hn2 | ].
  rewrite Nat.mod_small; [ | easy ].
  cbn - [ "/" "mod" "*" ].
...
*)
destruct m; [ easy | clear Hmz ].
rewrite Nat.pow_add_r.
revert m Hn.
induction n; intros; [ easy | ].
remember (S n) as n'.
cbn - [ "/" "mod" "*" ].
subst n'.
rewrite Nat.mul_assoc.
progress replace (2 * 2) with 4 by easy.
rewrite Nat.add_succ_r.
rewrite <- (Nat.add_1_l (m + n)).
progress replace (S (S (S (1 + (m + n))))) with (4 + m + n) by easy.
remember (4 * 2 ^ m / (4 + m + n) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
...
  cbn; flia Hn1.
}
rewrite fst_let.
apply Nat.eqb_neq in Hn1.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ cbn in Hn, Hn1; flia Hn Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
progress replace (2 * 2 ^ m * 2) with (2 ^ S (S m)). 2: {
  rewrite Nat.pow_succ_r', <- Nat.mul_assoc.
  f_equal.
  now rewrite Nat.pow_succ_r', Nat.mul_comm.
}
progress replace 4 with (2 ^ 2) at 1 by easy.
rewrite <- (Nat.pow_add_r 2 2).
do 2 rewrite <- Nat.pow_succ_r'.
progress replace (S (2 + m)) with (1 + S (S m)) by easy.
progress replace (4 + m) with (2 + S (S m)) by easy.
rewrite <- Nat.pow_add_r.
rewrite <- Nat.add_succ_comm.
rewrite Nat.pow_add_r.
apply IHn.
do 2 rewrite Nat.pow_succ_r'.
rewrite Nat.pow_succ_r' in Hn.
rewrite Nat.mul_assoc.
progress replace (2 * 2) with 4 by easy.
do 2 rewrite <- Nat.add_succ_comm.
apply Nat.le_lt_add_lt with (m := 4 + m) (n := 4 + m); [ easy | ].
rewrite (Nat.add_comm n).
rewrite Nat.sub_add; [ easy | ].
clear.
induction m; [ cbn; flia | ].
rewrite Nat.add_succ_r.
apply Nat.succ_le_mono in IHm.
eapply le_trans; [ apply IHm | ].
cbn.
specialize (Nat.pow_nonzero 2 m (Nat.neq_succ_0 _)) as H1.
flia IHm H1.
Qed.
*)

(*
Theorem le_fst_rank_fst_loop :
  ∀ m n,
  2 ^ m - 2 * m < 2 * n
  → m + n ≤ 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n))).
Proof.
intros * Hn.
revert m Hn.
induction n; intros; [ easy | ].
cbn - [ "*" ].
remember (2 ^ m / (m + S n) =? 1) as mn eqn:Hmn.
symmetry in Hmn.
destruct mn. {
  cbn.
  rewrite Nat.add_0_r.
  apply Nat.eqb_eq in Hmn.
...
  now apply Nat_eq_div_1 in Hmn.
}
rewrite fst_let.
apply Nat.eqb_neq in Hmn.
apply Nat_neq_div_1 in Hmn.
destruct Hmn as [Hmn| Hmn]; [ flia Hn Hmn | ].
rewrite Nat.mod_small; [ | easy ].
do 2 rewrite <- Nat.add_succ_comm.
rewrite <- Nat.pow_succ_r'.
apply IHn.
rewrite Nat.pow_succ_r'.
rewrite <- Nat.mul_sub_distr_l.
apply Nat.mul_lt_mono_pos_l; [ easy | ].
apply Nat.le_lt_add_lt with (m := S m) (n := S m); [ easy | ].
rewrite Nat.sub_add; [ | now apply Nat.pow_gt_lin_r ].
now rewrite <- Nat.add_succ_comm, Nat.add_comm.
Qed.
*)

(*
Theorem snd_rank_fst_loop :
  ∀ m n it,
  n ≤ S m + it
  → 2 ^ m < n
  → snd (rank_fst_loop it 1 (2 ^ S m) n) = 2 ^ Nat.log2_up n.
Proof.
intros * Hit Hmn.
revert m n Hit Hmn.
induction it; intros. {
  exfalso.
  rewrite Nat.add_0_r in Hit.
  apply Nat.nle_gt in Hmn.
  apply Hmn; clear Hmn.
  apply (le_trans _ (S m)); [ easy | ].
  now apply Nat.pow_gt_lin_r.
}
cbn - [ "*" "^" ].
remember (2 ^ S m / n =? 1) as mn1 eqn:Hmn1.
symmetry in Hmn1.
destruct mn1. {
  symmetry; cbn - [ "^" ].
  f_equal.
...
  apply Nat_eq_log2_up; [ flia Hmn | ].
  apply Nat.eqb_eq in Hmn1.
  apply Nat_eq_div_1 in Hmn1.
  split; [ | easy ].
  rewrite Nat.pow_succ_r'.
  now rewrite Nat.mul_comm, Nat.div_mul.
}
rewrite snd_let.
apply Nat.eqb_neq in Hmn1.
apply Nat_neq_div_1 in Hmn1.
destruct Hmn1 as [Hmn1| Hmn1]. {
  rewrite Nat.pow_succ_r' in Hmn1.
  apply Nat.mul_le_mono_pos_l in Hmn1; [ | easy ].
  now apply Nat.nlt_ge in Hmn1.
}
rewrite Nat.mod_small; [ | easy ].
rewrite <- Nat.pow_succ_r'.
rewrite <- Nat.add_succ_comm in Hit.
now apply IHit.
Qed.
*)

(*
Theorem snd_rank_fst_1 :
  ∀ it n,
  n ≠ 0
  → n ≤ it
  → snd (rank_fst_loop it 1 1 n) = 2 ^ Nat.log2_up n.
Proof.
intros * Hnz Hit.
destruct it; [ now apply Nat.le_0_r in Hit | ].
cbn - [ "*" ].
remember (1 / n =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  symmetry; cbn.
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (H, _).
  apply Nat.le_1_r in H.
...
  destruct H; [ easy | now subst n].
}
rewrite snd_let.
apply Nat.eqb_neq in Hn1.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hnz Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
rewrite Nat.mul_1_r.
now apply (snd_rank_fst_loop 0).
Qed.
*)

(*
Theorem snd_rank_fst_1_2_succ :
  ∀ it n,
  0 < n
  → n ≤ it
  → snd (rank_fst_loop it 1 2 (S n)) = 2 ^ Nat.log2_up (S n).
Proof.
intros * Hn2 Hit.
destruct it; [ now apply Nat.le_0_r in Hit; subst n | ].
cbn - [ "*" "/" "mod" ].
remember (2 / S n =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (H, _).
  apply Nat.succ_le_mono in H.
  apply Nat.le_1_r in H.
...
  now destruct H; subst n.
}
rewrite snd_let.
apply Nat.eqb_neq in Hn1.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn2 Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
progress replace (2 * 2) with (2 ^ 2) by easy.
rewrite (snd_rank_fst_loop 1); [ easy | | easy ].
now apply -> Nat.succ_le_mono.
Qed.
*)

Theorem Nat_le_add_le_sub_l_iff : ∀ n m p, n ≤ m → n + p ≤ m ↔ p ≤ m - n.
Proof.
intros * Hnm.
split; intros Hn; [ apply Nat.le_add_le_sub_l, Hn | ].
apply Nat.add_le_mono_l with (p := n) in Hn.
eapply le_trans; [ apply Hn | ].
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

(*
Theorem lt_snd_rank_fst_loop :
  ∀ m n,
  2 ^ m - S m < n
  → m + n < snd (rank_fst_loop n 1 (2 ^ S m) (S m + n)).
Proof.
intros * Hmn.
revert m Hmn.
induction n; intros; [ easy | ].
cbn - [ "*" "/" "mod" "^" ].
remember (2 ^ S m / S (m + S n) =? 1) as mn1 eqn:Hmn1.
symmetry in Hmn1.
destruct mn1. {
  cbn - [ "^" ].
  apply Nat.eqb_eq in Hmn1.
  apply Nat_eq_div_1 in Hmn1.
...
  eapply lt_le_trans; [ | apply Hmn1 ].
  apply Nat.lt_succ_diag_r.
}
rewrite snd_let.
apply Nat.eqb_neq in Hmn1.
apply Nat_neq_div_1 in Hmn1.
destruct Hmn1 as [Hmn1| Hmn1]. {
  rewrite Nat.pow_succ_r' in Hmn1.
  flia Hmn Hmn1.
}
rewrite Nat.mod_small; [ | easy ].
rewrite <- Nat.add_succ_comm.
rewrite <- Nat.pow_succ_r'.
apply IHn.
apply (Nat.add_lt_mono_r _ _ (S (S m))).
rewrite Nat.sub_add; [ flia Hmn1 | ].
apply Nat.lt_succ_r.
apply -> Nat.succ_lt_mono.
now apply Nat.pow_gt_lin_r.
Qed.
*)

Theorem Nat_pow2_log2 :
  ∀ n, n ≠ 0 → 2 ^ S (Nat.log2 n) = 2 ^ Nat.log2_up (S n).
Proof.
intros * Hnz.
now destruct n.
Qed.

(*
Theorem snd_rank_fst_loop_interval :
  ∀ m n,
  2 ^ m / 2 - m < n
  → m + n ≤ snd (rank_fst_loop n 1 (2 ^ m) (m + n)) < 2 * (m + n).
Proof.
intros * Hn.
revert m Hn.
induction n; intros; [ easy | ].
cbn - [ "*" ].
rewrite snd_if, snd_let.
cbn - [ "*" ].
remember (2 ^ m / (m + S n) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
...
  flia Hn1.
}
apply Nat.eqb_neq in Hn1.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]. 2: {
  rewrite Nat.mod_small; [ | easy ].
  rewrite <- Nat.add_succ_comm.
  rewrite <- Nat.pow_succ_r'.
  apply IHn.
  rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
  apply (Nat.add_lt_mono_r _ _ (S m)).
  rewrite Nat.add_comm, Nat.add_succ_comm in Hn1.
  rewrite Nat.sub_add; [ easy | ].
  now apply Nat.pow_gt_lin_r.
}
apply (Nat.add_lt_mono_r _ _ m) in Hn.
rewrite Nat.sub_add in Hn. 2: {
  apply Nat.div_le_lower_bound; [ easy | ].
  (* lemma *)
  clear.
  induction m; [ easy | ].
  cbn - [ "*" ].
  apply Nat.mul_le_mono_l.
  destruct m; [ easy | ].
  apply (le_trans _ (2 * S m)); [ | easy ].
  rewrite <- Nat_add_diag.
  flia.
}
destruct m; [ cbn in Hn1; flia Hn1 | ].
rewrite Nat.pow_succ_r', Nat.mul_comm, Nat.div_mul in Hn; [ | easy ].
rewrite Nat.pow_succ_r', Nat.add_comm in Hn1.
apply Nat.mul_le_mono_pos_l in Hn1; [ | easy ].
now apply Nat.nlt_ge in Hn1.
Qed.
*)

(*
Theorem pow2_snd_rank_fst_loop_le :
  ∀ m n,
  2 ^ m / 2 - m < n
  → snd (rank_fst_loop n 1 (2 ^ m) (m + n)) < m + n
  → 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n))) ≤ m + n.
Proof.
intros * Hn Hn1.
revert m Hn Hn1.
induction n; intros; [ easy | ].
cbn - [ "*" ].
rewrite fst_if, fst_let.
cbn - [ "*" ] in Hn1.
rewrite snd_if, snd_let in Hn1.
remember (2 ^ m / (m + S n) =? 1) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2. {
  cbn; rewrite Nat.add_0_r.
...
  now apply Nat.lt_le_incl.
}
apply Nat.eqb_neq in Hn2.
apply Nat_neq_div_1 in Hn2.
destruct Hn2 as [Hn2| Hn2]. {
  exfalso; apply Nat.nle_gt in Hn.
  apply Hn; clear Hn.
  apply Nat.le_add_le_sub_r.
  apply Nat.div_le_lower_bound; [ easy | ].
  now rewrite Nat.add_comm.
}
rewrite Nat.mod_small in Hn1; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
do 2 rewrite <- Nat.add_succ_comm.
rewrite <- Nat.add_succ_comm in Hn1.
rewrite <- Nat.pow_succ_r'.
rewrite <- Nat.pow_succ_r' in Hn1.
apply IHn; [ | easy ].
rewrite Nat.pow_succ_r', Nat.mul_comm, Nat.div_mul; [ | easy ].
rewrite Nat.add_comm, Nat.add_succ_comm in Hn2.
apply (Nat.add_lt_mono_r _ _ (S m)).
rewrite Nat.sub_add; [ easy | ].
now apply Nat.pow_gt_lin_r.
Qed.
*)

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

(*
Theorem fst_1_len_log2_up :
  ∀ n, fst_1_len 1 n = Nat.log2_up (inv_ub_num n) - 1.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
progress unfold inv_ub_num.
rewrite Nat_log2_up_pow2_sub_1; [ now rewrite Nat_sub_succ_1 | ].
intros H1.
apply Nat.succ_inj in H1.
progress unfold fst_1_len in H1.
destruct n; [ easy | clear Hnz ].
remember (rank_fst_loop (S n) 0) as f.
cbn - [ "-" "*" "/" "mod" ] in H1.
subst f.
remember (1 / S n =? 1) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2. {
  cbn - [ "-" "*" "/" "mod" ] in H1.
  apply Nat.eqb_eq in Hn2.
...
  rewrite Hn2 in H1.
  cbn - [ "-" "*" "/" "mod" ] in H1.
  now rewrite fst_let in H1.
}
apply Nat.eqb_neq in Hn2.
apply Nat_neq_div_1 in Hn2.
destruct Hn2 as [Hn2| Hn2]; [ flia Hn2 | ].
rewrite Nat.mod_small in H1; [ | easy ].
rewrite snd_let in H1.
rewrite Nat.mul_1_r in H1.
cbn - [ "-" "*" "/" "mod" ] in H1.
rewrite fst_if, fst_let in H1.
cbn - [ "-" "*" "/" "mod" ] in H1.
remember (snd (rank_fst_loop n 1 2 (S n)) / S n =? 0) as n3 eqn:Hn3.
symmetry in Hn3.
destruct n3; [ clear H1 | easy ].
apply Nat.eqb_eq in Hn3.
apply Nat.div_small_iff in Hn3; [ | easy ].
apply Nat.nle_gt in Hn3.
apply Hn3; clear Hn3.
apply Nat.succ_lt_mono in Hn2.
rewrite snd_rank_fst_1_2_succ; [ | easy | easy ].
apply Nat.log2_up_spec.
now apply -> Nat.succ_lt_mono.
Qed.
*)

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
rewrite pred_of_minus in Ha, Hb.
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

(*
Theorem eq_fst_rank_fst_loop_0 :
  ∀ it k a b,
  fst (rank_fst_loop it k a b) = 0
  ↔ it = 0 ∨ a / b = k.
Proof.
intros.
destruct it. {
  split; [ now intros; left | easy ].
}
cbn - [ "*" ]; rewrite fst_if, fst_let; cbn - [ "*" ].
remember (a / b =? k) as abk eqn:Habk.
symmetry in Habk.
destruct abk. {
  apply Nat.eqb_eq in Habk.
...
  split; [ now intros; right | easy ].
}
apply Nat.eqb_neq in Habk.
split; [ easy | ].
now intros [H| H].
Qed.
*)

(*
Theorem inv_ub_num_gt_1 :
  ∀ n, 1 < n → 1 < inv_ub_num n.
Proof.
intros * Hn1.
progress unfold inv_ub_num.
apply Nat.lt_add_lt_sub_r.
cbn - [ "*" ].
rewrite <- (Nat.mul_1_r 2) at 1.
apply Nat.mul_lt_mono_pos_l; [ easy | ].
progress unfold fst_1_len.
destruct n; [ easy | ].
remember (snd _) as x.
cbn - [ "*" "/" "mod" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" ].
remember (x / S n =? 0) as xn eqn:Hxn.
symmetry in Hxn.
destruct xn. {
  exfalso.
  subst x; apply Nat.eqb_eq in Hxn.
  apply Nat.div_small_iff in Hxn; [ | easy ].
  apply Nat.nlt_ge in Hxn.
  apply Hxn; clear Hxn.
  apply -> Nat.succ_lt_mono.
  cbn - [ "*" "/" "mod" ].
  rewrite snd_if, snd_let.
  cbn - [ "*" "/" "mod" ].
...
  rewrite Nat.div_small; [ | flia Hn1 ].
  rewrite Nat.mod_small; [ | flia Hn1 ].
  cbn.
  apply (lt_snd_rank_fst_loop 0).
  cbn; flia Hn1.
}
rewrite Nat.pow_succ_r'.
apply Nat.lt_1_mul_pos; [ easy | ].
apply Nat.neq_0_lt_0.
now apply Nat.pow_nonzero.
Qed.
*)

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
  now apply Nat.mod_mul.
}
apply Nat.eqb_eq in Hn2.
apply Nat.mod_divides in Hn2; [ | easy ].
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
apply Nat.mod_divides in Hn2; [ | easy ].
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
eapply le_trans; [ apply IHn | ].
do 3 rewrite Nat.pow_succ_r'.
specialize (Nat.pow_gt_lin_r 2 n Nat.lt_1_2) as H2.
flia H2.
Qed.

Theorem Nat_log2_up_lt_twice : ∀ n, n ≠ 0 → 2 ^ Nat.log2_up n < 2 * n.
Proof.
intros * Hnz.
destruct n; [ easy | clear Hnz ].
specialize (Nat.log2_up_succ_or n) as H1.
destruct H1 as [H1| H1]. {
  rewrite H1.
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply Nat_pow2_log2_up_succ in H1.
  now rewrite H1.
}
rewrite H1.
destruct n; [ now cbn | ].
specialize (Nat.log2_up_spec (S (S n))) as H2.
assert (H : 1 < S (S n)) by flia.
specialize (H2 H); clear H.
destruct H2 as (H2, H3).
rewrite <- Nat.sub_1_r in H2.
rewrite H1 in H2.
rewrite Nat.pow_sub_r in H2; [ | easy | ]. 2: {
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.log2_up_null in H.
  apply Nat.succ_le_mono in H.
  now apply Nat.le_0_r in H; subst n.
}
rewrite Nat.pow_1_r in H2.
apply Nat.nle_gt.
intros H4.
apply Nat.nle_gt in H2.
apply H2; clear H2.
apply Nat.div_le_lower_bound; [ easy | ].
now rewrite H1 in H3.
Qed.

End a.
