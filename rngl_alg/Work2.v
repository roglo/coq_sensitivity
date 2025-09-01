(* File created because Work.v became too big, but
   without any topic found for the moment *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 ZArith.
Require Import Init.Nat.
Import List.ListNotations.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.

Require Import TrigoWithoutPi.TacChangeAngle.
Require Import TrigoWithoutPi.Angle TrigoWithoutPi.TrigoWithoutPiExt.
Require Import TrigoWithoutPi.Angle_order.
Require Import TrigoWithoutPi.AngleDiv2.
Require Import TrigoWithoutPi.AngleDiv2Add.
Require Import TrigoWithoutPi.SeqAngleIsCauchy.
Require Import TrigoWithoutPi.AngleAddOverflowLe.
Require Import TrigoWithoutPi.AngleAddLeMonoL.

Require Import Misc.
Require Import AngleEuclDistLtAngleLtLt.
Require Import Complex.
Require Import Work.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition nth_rest_of_div n a b := a * 2 ^ n mod b.
Definition nth_bit_of_div n a b := 2 * nth_rest_of_div n a b / b.

Theorem nth_rest_of_div_lt :
  ∀ n a b,
  b ≠ 0
  → nth_rest_of_div n a b < b.
Proof.
intros * Hbz.
now apply Nat.mod_upper_bound.
Qed.

Theorem Nat_mod_sub :
  ∀ a b c, c ≠ 0 → b * c ≤ a → (a - b * c) mod c = a mod c.
Proof.
intros * Hcz Hbca.
remember (a - b * c) as d eqn:Hd.
assert (H : a = d + b * c) by flia Hd Hbca.
subst a.
symmetry.
apply Nat.Div0.mod_add.
Qed.

Theorem eq_fst_rank_fst_loop_iff :
  ∀ it k a b u,
  a < b
  → fst (rank_fst_loop it k a b) = u ↔
    u ≤ it ∧ (∀ t, t < u → nth_bit_of_div t a b ≠ k) ∧
      (it = u ∨ nth_bit_of_div u a b = k).
Proof.
intros * Hab.
split; intros H1. {
  revert it a Hab H1.
  induction u; intros. {
    split; [ easy | ].
    split; [ easy | ].
    destruct it; [ now left | right ].
    progress unfold nth_bit_of_div.
    progress unfold nth_rest_of_div.
    cbn - [ "*" ] in H1 |-*.
    rewrite fst_if, fst_let in H1.
    cbn - [ "*" ] in H1.
    rewrite Nat.mul_1_r.
    rewrite Nat.mod_small; [ | easy ].
    apply Nat.eqb_eq.
    apply Bool.not_false_iff_true.
    now intros H; rewrite H in H1.
  }
  destruct (Nat.eq_dec it (S u)) as [Hiu| Hiu]. {
    subst it.
    split; [ easy | ].
    split; [ | now left ].
    intros * Ht.
    cbn - [ "*" ] in H1.
    rewrite fst_if, fst_let in H1.
    cbn - [ "*" ] in H1.
    remember (2 * a / b =? k) as abk eqn:Habk.
    symmetry in Habk.
    destruct abk; [ easy | ].
    apply Nat.succ_inj in H1.
    apply IHu in H1; [ | apply Nat.mod_upper_bound; flia Hab ].
    destruct H1 as (_ & H1 & H2).
    apply Nat.eqb_neq in Habk.
    progress unfold nth_bit_of_div.
    progress unfold nth_rest_of_div.
    destruct t. {
      rewrite Nat.mul_1_r.
      now rewrite Nat.mod_small.
    }
    apply Nat.succ_lt_mono in Ht.
    progress unfold nth_bit_of_div in H1.
    progress unfold nth_rest_of_div in H1.
    rewrite Nat.pow_succ_r', Nat.mul_assoc.
    rewrite (Nat.mul_comm a).
    rewrite <- Nat.Div0.mul_mod_idemp_l.
    now apply H1.
  }
  destruct it; [ easy | ].
  cbn - [ "*" ] in H1.
  rewrite fst_if, fst_let in H1.
  cbn - [ "*" ] in H1.
  remember (2 * a / b =? k) as abk eqn:Habk.
  symmetry in Habk.
  destruct abk; [ easy | ].
  apply Nat.succ_inj in H1.
  apply IHu in H1; [ | apply Nat.mod_upper_bound; flia Hab ].
  destruct H1 as (H1 & H2 & H3).
  split; [ flia H1 | ].
  apply Nat.eqb_neq in Habk.
  split. {
    intros t Ht.
    progress unfold nth_bit_of_div.
    progress unfold nth_rest_of_div.
    destruct t. {
      rewrite Nat.mul_1_r.
      now rewrite Nat.mod_small.
    }
    apply Nat.succ_lt_mono in Ht.
    progress unfold nth_bit_of_div in H2.
    progress unfold nth_rest_of_div in H2.
    rewrite Nat.pow_succ_r', Nat.mul_assoc.
    rewrite (Nat.mul_comm a).
    rewrite <- Nat.Div0.mul_mod_idemp_l.
    now apply H2.
  }
  destruct H3 as [H3| H3]; [ now subst it | right ].
  progress unfold nth_bit_of_div in H3.
  progress unfold nth_rest_of_div in H3.
  progress unfold nth_bit_of_div.
  progress unfold nth_rest_of_div.
  rewrite Nat.pow_succ_r', Nat.mul_assoc.
  rewrite (Nat.mul_comm a).
  now rewrite <- Nat.Div0.mul_mod_idemp_l.
}
destruct H1 as (H1 & H2 & H3).
destruct H3 as [H3| H3]. 2: {
  progress unfold nth_bit_of_div in H2.
  progress unfold nth_bit_of_div in H3.
  revert a u Hab H1 H2 H3.
  induction it; intros. {
    now apply Nat.le_0_r in H1; subst u.
  }
  cbn - [ "*" ].
  rewrite fst_if, fst_let.
  cbn - [ "*" ].
  destruct u. {
    cbn - [ "*" ] in H3.
    progress unfold nth_rest_of_div in H3.
    rewrite Nat.mul_1_r in H3.
    rewrite Nat.mod_small in H3; [ | easy ].
    now rewrite H3, Nat.eqb_refl.
  }
  apply Nat.succ_le_mono in H1.
  progress unfold nth_rest_of_div in H3.
  cbn - [ "*" ] in H3.
  remember (2 * a / b =? k) as abk eqn:Habk.
  symmetry in Habk.
  destruct abk. {
    exfalso.
    apply Nat.eqb_eq in Habk.
    apply Nat_div_less_small_iff in Habk. 2: {
      intros Hb; subst b k; cbn in H2.
      now apply (H2 0).
    }
    apply Nat_div_less_small_iff in H3; [ | flia Hab ].
    rewrite <- Nat.pow_succ_r' in H3.
    progress unfold nth_rest_of_div in H2.
    specialize (H2 0 (Nat.lt_0_succ _)) as H4.
    rewrite Nat.mul_1_r in H4.
    rewrite Nat.mod_small in H4; [ | easy ].
    apply Nat_neq_div in H4; [ | flia Habk ].
    flia H4 Habk.
  }
  f_equal.
  apply Nat.eqb_neq in Habk.
  destruct (lt_dec (2 * a) b) as [H2ab| H2ab]. {
    rewrite Nat.mod_small; [ | easy ].
    progress unfold nth_rest_of_div in H2.
    apply IHit; [ easy | easy | | ]. {
      intros t Ht.
      progress unfold nth_rest_of_div.
      apply Nat.succ_lt_mono in Ht.
      specialize (H2 (S t) Ht) as H4.
      now rewrite (Nat.mul_comm _ a), <- Nat.mul_assoc.
    }
    progress unfold nth_rest_of_div.
    rewrite (Nat.mul_comm _ a).
    now rewrite <- Nat.mul_assoc.
  }
  apply Nat.nlt_ge in H2ab.
  rewrite (Nat_mod_less_small 1). 2: {
    rewrite Nat.mul_1_l.
    split; [ easy | ].
    now apply Nat.mul_lt_mono_pos_l.
  }
  rewrite Nat.mul_1_l.
  apply IHit; [ flia Hab | easy | | ]. {
    intros t Ht.
    progress unfold nth_rest_of_div in H2.
    progress unfold nth_rest_of_div.
    rewrite <- Nat.Div0.mul_mod_idemp_l.
    specialize (Nat_mod_sub (2 * a) 1 b) as H.
    rewrite Nat.mul_1_l in H.
    rewrite H; [ clear H | flia Hab | easy ].
    rewrite Nat.Div0.mul_mod_idemp_l.
    rewrite (Nat.mul_comm _ a), <- Nat.mul_assoc.
    rewrite <- Nat.pow_succ_r'.
    apply Nat.succ_lt_mono in Ht.
    now apply H2.
  }
  progress unfold nth_rest_of_div in H2.
  progress unfold nth_rest_of_div.
  rewrite <- Nat.Div0.mul_mod_idemp_l.
  specialize (Nat_mod_sub (2 * a) 1 b) as H.
  rewrite Nat.mul_1_l in H.
  rewrite H; [ clear H | flia Hab | easy ].
  rewrite Nat.Div0.mul_mod_idemp_l.
  now rewrite (Nat.mul_comm _ a), <- Nat.mul_assoc.
}
subst u; clear H1.
revert a Hab H2.
induction it; intros; [ easy | ].
cbn - [ "*" ].
rewrite fst_if, fst_let.
cbn - [ "*" ].
remember (2 * a / b =? k) as abk eqn:Habk.
symmetry in Habk.
destruct abk. {
  exfalso.
  apply Nat.eqb_eq in Habk.
  progress unfold nth_bit_of_div in H2.
  progress unfold nth_rest_of_div in H2.
  specialize (H2 0 (Nat.lt_0_succ _)) as H3.
  rewrite Nat.mul_1_r in H3.
  now rewrite Nat.mod_small in H3.
}
f_equal.
apply IHit; [ apply Nat.mod_upper_bound; flia Hab | ].
intros t Ht.
apply Nat.succ_lt_mono in Ht.
progress unfold nth_bit_of_div in H2.
progress unfold nth_bit_of_div.
progress unfold nth_rest_of_div in H2.
progress unfold nth_rest_of_div.
specialize (H2 (S t) Ht) as H3.
rewrite Nat.pow_succ_r', Nat.mul_assoc, (Nat.mul_comm a) in H3.
now rewrite Nat.Div0.mul_mod_idemp_l.
Qed.

Theorem pow2_den_le_mul_num :
  ∀ n,
  2 ≤ n
  → 2 ^ inv_ub_den_pow2 n ≤ n * inv_ub_num n.
Proof.
intros * H2n.
(* This theorem states that
     2 ^ bn ≤ n * an
   and it is required to prove that
     θi ≤ an * (θ / 2^bn)
   where
     an = 2 ^ (un + 1) - 1
     bn = log2_up n + un
   with
     un = length of the first sequence of 1s in the binary
          decomposition of 1/n
   1/n = 0.0.............01......10...
           <- log2_up n -><- un ->
     an = 11........1
           <- un n ->

   Then we need to equivalently prove that
     2 ^ (log2_up n + un) ≤ n * (2 ^ (un + 1) - 1)
   that we can rewrite as
     n ≤ (2 * n - 2 ^ log2_up n) * 2 ^ un n
   we can compute "len n" with
     un = fn (2 ^ (log2_up n - 1))
   with
     fn i = position of the 1st zero in the binary
            decomposition of 1/a

     fn(i) = | i              if 2i/n = 0
             | fn((2i) mod n) otherwize

    we must also prove that fn terminates
 *)
assert (H1ln : 1 ≤ Nat.log2_up n). {
  apply Nat.log2_up_lt_pow2; [ flia H2n | ].
  cbn; flia H2n.
}
progress unfold inv_ub_den_pow2.
rewrite rank_fst_1_log2_up; [ | easy ].
rewrite Nat.add_shuffle0.
rewrite Nat.sub_add; [ | easy ].
progress unfold inv_ub_num.
progress unfold fst_1_len.
rewrite snd_rank_fst_loop_1_log2_up; [ | easy ].
set (fn := λ i, fst (rank_fst_loop n 0 i n)).
set (un := fn (2 ^ (Nat.log2_up n - 1))).
fold (fn (2 ^ (Nat.log2_up n - 1))).
fold un.
rewrite Nat.pow_add_r.
rewrite Nat.pow_succ_r'.
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
apply Nat.le_add_le_sub_r.
apply Nat_le_add_le_sub_l_iff. {
  rewrite Nat.mul_assoc.
  apply Nat.mul_le_mono_r.
  destruct n; [ easy | ].
  rewrite <- Nat_pow2_log2; [ | flia H2n ].
  rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_r.
  apply (Nat.le_trans _ n); [ | apply Nat.le_succ_diag_r ].
  apply Nat.log2_spec; flia H2n.
}
rewrite Nat.mul_assoc.
rewrite <- Nat.mul_sub_distr_r.
rewrite (Nat.mul_comm n).
set (x := 2 * n - 2 ^ Nat.log2_up n).
subst un fn.
cbn - [ "*" ].
remember (fst _) as m eqn:Hm.
symmetry in Hm.
apply eq_fst_rank_fst_loop_iff in Hm. 2: {
  rewrite Nat.sub_1_r.
  now apply Nat.log2_up_spec.
}
destruct Hm as (Hm1 & Hm2 & Hm3).
clear Hm1 Hm2.
destruct Hm3 as [Hm3|Hm3]. {
  subst m x.
  rewrite <- (Nat.mul_1_l n) at 1.
  apply Nat.mul_le_mono. 2: {
    apply Nat.lt_le_incl.
    now apply Nat.pow_gt_lin_r.
  }
  assert (H : n ≠ 0) by flia H2n.
  specialize (Nat_log2_up_lt_twice n H) as H1; clear H.
  flia H1.
}
apply Nat.div_small_iff in Hm3; [ | flia H2n ].
clear H1ln.
(**)
subst x.
rewrite Nat.mul_sub_distr_r.
apply Nat.le_add_le_sub_r.
apply Nat_le_add_le_sub_l_iff. {
  specialize (Nat.pow_nonzero 2 m (Nat.neq_succ_0 _)) as H1.
  rewrite Nat.mul_comm.
  destruct (2 ^ m); [ easy | flia ].
}
rewrite (Nat.mul_comm 2), <- Nat.mul_assoc.
rewrite <- (Nat.mul_1_r n) at 3.
rewrite <- Nat.mul_sub_distr_l.
rewrite <- Nat.pow_succ_r'.
rewrite <- Nat.pow_add_r.
progress unfold nth_rest_of_div in Hm3.
rewrite <- Nat.pow_add_r in Hm3.
(**)
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  subst m.
  rewrite Nat.add_0_r in Hm3 |-*.
  rewrite Nat.mul_1_r.
  rewrite Nat.mod_small in Hm3. 2: {
    rewrite Nat.sub_1_r.
    now apply Nat.log2_up_spec.
  }
  rewrite <- Nat.pow_succ_r' in Hm3.
  rewrite <- Nat.sub_succ_l in Hm3. 2: {
    destruct n; [ easy | ].
    destruct n; [ flia H2n | cbn; flia ].
  }
  rewrite Nat_sub_succ_1 in Hm3.
  now apply Nat.lt_le_incl.
}
rewrite <- Nat.add_sub_swap in Hm3. 2: {
  destruct n; [ easy | ].
  destruct n; [ flia H2n | cbn; flia ].
}
rewrite <- (Nat.sub_add 1 (_ + _)). 2: {
  destruct n; [ easy | ].
  destruct n; [ flia H2n | cbn; flia ].
}
rewrite Nat.pow_add_r, Nat.pow_1_r, Nat.mul_comm.
remember (2 ^ (Nat.log2_up n + m - 1)) as p eqn:Hp.
destruct (lt_dec p n) as [Hpn| Hpn]. {
  rewrite Nat.mod_small in Hm3; [ | easy ].
  eapply Nat.le_trans; [ apply Nat.lt_le_incl, Hm3 | ].
  rewrite Nat.pow_succ_r'.
  specialize (Nat.pow_nonzero 2 m (Nat.neq_succ_0 _)) as H1.
  destruct (2 ^ m); [ easy | flia ].
}
apply Nat.nlt_ge in Hpn.
rewrite Nat.Div0.mod_eq in Hm3.
rewrite Nat.mul_sub_distr_l in Hm3.
apply Nat.lt_sub_lt_add_l in Hm3.
rewrite (Nat.mul_comm _ (_ * _)) in Hm3.
rewrite <- Nat.mul_assoc in Hm3.
rewrite <- (Nat.mul_1_r n) in Hm3 at 3.
rewrite <- Nat.mul_add_distr_l in Hm3.
eapply Nat.le_trans; [ apply Nat.lt_le_incl, Hm3 | ].
apply Nat.mul_le_mono_l.
apply Nat.le_add_le_sub_r.
rewrite <- Nat.add_assoc.
progress replace (1 + 1) with (1 * 2) by easy.
rewrite <- Nat.mul_add_distr_r.
rewrite Nat.mul_comm.
rewrite Nat.pow_succ_r'.
apply Nat.mul_le_mono_l.
rewrite Nat.add_1_r.
apply Nat.le_succ_l.
apply Nat.Div0.div_lt_upper_bound.
rewrite Hp.
rewrite Nat.add_sub_swap. 2: {
  destruct n; [ easy | ].
  destruct n; [ flia H2n | cbn; flia ].
}
rewrite Nat.pow_add_r.
apply Nat.mul_lt_mono_pos_r; [ now apply Nat.neq_0_lt_0, Nat.pow_nonzero | ].
rewrite Nat.sub_1_r.
now apply Nat.log2_up_spec.
Qed.

(* upper bound of θi (seq_angle i) independant from i *)
Theorem seq_angle_to_div_nat_le :
  ∀ n i θ,
  n ≠ 1
  → (seq_angle_to_div_nat θ n i ≤
       inv_ub_num n * (θ /₂^inv_ub_den_pow2 n))%A.
Proof.
intros * Hn1.
progress unfold seq_angle_to_div_nat.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  apply angle_nonneg.
}
destruct (lt_dec (2 ^ i) n) as [Hin| Hin]. {
  rewrite Nat.div_small; [ | easy ].
  apply angle_nonneg.
}
apply Nat.nlt_ge in Hin.
assert (H1ln : 1 ≤ Nat.log2_up n). {
  apply Nat.log2_up_lt_pow2; [ flia Hnz | ].
  cbn; flia Hnz Hn1.
}
destruct (le_dec i (inv_ub_den_pow2 n)) as [Hni| Hni]. {
  rewrite <- (angle_div_2_pow_mul_pow_sub (inv_ub_den_pow2 n) i); [ | easy ].
  rewrite angle_mul_nat_assoc.
  apply angle_mul_le_mono_r. {
    eapply angle_mul_nat_not_overflow_le_l. 2: {
      apply angle_mul_nat_overflow_pow_div.
    }
    progress unfold inv_ub_num.
    progress unfold inv_ub_den_pow2.
    rewrite rank_fst_1_log2_up; [ | flia Hn1 Hnz ].
    rewrite <- Nat.add_sub_swap; [ | easy ].
    rewrite Nat.sub_add; [ | flia H1ln ].
    apply Nat.le_sub_le_add_r.
    eapply Nat.le_trans; [ | apply Nat.le_add_r ].
    apply Nat.pow_le_mono_r; [ easy | ].
    rewrite <- Nat.add_1_l.
    now apply Nat.add_le_mono_r.
  }
  rewrite Nat.pow_sub_r; [ | easy | easy ].
  rewrite <- Nat.Lcm0.divide_div_mul_exact. 2: {
    exists (2 ^ (inv_ub_den_pow2 n - i)).
    rewrite <- Nat.pow_add_r.
    now rewrite Nat.sub_add.
  }
  (* (2^i/n * 2^bn)/2^i ≤ an *)
  apply Nat.Div0.div_le_upper_bound.
  (* 2^i/n * 2^bn ≤ 2^i * an *)
  rewrite Nat.mul_comm.
  (* 2^bn * (2^i/n) ≤ 2^i * an *)
  eapply Nat.le_trans; [ apply Nat.Div0.div_mul_le | ].
  (* (2^bn * 2^i) / n ≤ 2^i * an *)
  apply Nat.Div0.div_le_upper_bound.
  (* 2^bn * 2^i ≤ n * (2^i * an) *)
  rewrite Nat.mul_assoc.
  rewrite Nat.mul_shuffle0.
  apply Nat.mul_le_mono_r.
  (* 2^bn ≤ n * an *)
  apply pow2_den_le_mul_num; flia Hn1 Hnz.
} {
  apply Nat.nle_gt in Hni.
  rewrite <- (angle_div_2_pow_mul_pow_sub i (inv_ub_den_pow2 n)). 2: {
    now apply Nat.lt_le_incl in Hni.
  }
  rewrite angle_mul_nat_assoc.
  apply angle_mul_le_mono_r. {
    eapply angle_mul_nat_not_overflow_le_l. 2: {
      apply angle_mul_nat_overflow_pow_div.
    }
    progress unfold inv_ub_num.
    progress unfold inv_ub_den_pow2.
    progress unfold inv_ub_den_pow2 in Hni.
    rewrite rank_fst_1_log2_up; [ | flia Hn1 Hnz ].
    rewrite rank_fst_1_log2_up in Hni; [ | flia Hn1 Hnz ].
    rewrite <- Nat.add_sub_swap; [ | easy ].
    rewrite Nat.sub_add; [ | flia H1ln ].
    rewrite Nat.mul_sub_distr_r.
    rewrite <- Nat.pow_add_r.
    rewrite Nat.add_comm.
    rewrite Nat.sub_add_distr.
    rewrite <- (Nat.add_1_r (fst_1_len _ _)).
    rewrite Nat.add_assoc, Nat.sub_add; [ | flia Hni ].
    rewrite Nat.mul_1_l.
    apply Nat.le_sub_le_add_r.
    eapply Nat.le_trans; [ | apply Nat.le_add_r ].
    apply Nat.pow_le_mono_r; [ easy | ].
    flia Hni H1ln.
  }
  rewrite Nat.pow_sub_r; [ | easy | now apply Nat.lt_le_incl ].
  (* 2^i/n ≤ an * (2^i / 2^bn) *)
  rewrite <- Nat.Lcm0.divide_div_mul_exact. 2: {
    exists (2 ^ (i - inv_ub_den_pow2 n)).
    rewrite <- Nat.pow_add_r.
    apply Nat.lt_le_incl in Hni.
    now rewrite Nat.sub_add.
  }
  (* 2^i/n ≤ an * 2^i / 2^bn *)
  apply Nat.div_le_lower_bound; [ now apply Nat.pow_nonzero | ].
  (* 2^bn * (2^i/n) ≤ an * 2^i *)
  eapply Nat.le_trans; [ apply Nat.Div0.div_mul_le | ].
  (* (2^bn * 2^i) / n ≤ an * 2^i *)
  apply Nat.Div0.div_le_upper_bound.
  (* 2^bn * 2^i ≤ n * (an * 2^i) *)
  rewrite Nat.mul_assoc.
  apply Nat.mul_le_mono_r.
  apply pow2_den_le_mul_num; flia Hn1 Hnz.
}
Qed.

Theorem angle_add_mul_r_diag_r : ∀ n θ, (θ + n * θ)%A = (S n * θ)%A.
Proof. easy. Qed.

Theorem fold_seq_angle_to_div_nat :
  ∀ θ n i, (2 ^ i / n * (θ /₂^i))%A = seq_angle_to_div_nat θ n i.
Proof. easy. Qed.

Theorem Nat_pow2_succ_le_pow2_log2_up :
  ∀ n i,
  2 ^ i < n
  → 2 ^ S i ≤ 2 ^ Nat.log2_up n.
Proof.
intros * Hin.
apply Nat.pow_le_mono_r; [ easy | ].
apply Nat.le_succ_l.
generalize Hin; intros Hni.
apply Nat.lt_le_incl in Hni.
apply Nat.log2_up_le_mono in Hni.
rewrite Nat.log2_up_pow2 in Hni; [ | easy ].
apply Nat.lt_eq_cases in Hni.
destruct Hni as [Hni| Hni]; [ easy | ].
subst i.
exfalso.
apply Nat.nle_gt in Hin.
apply Hin; clear Hin.
destruct (le_dec n 1) as [Hn1| Hn1]. {
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  flia Hn1.
}
apply Nat.nle_gt in Hn1.
now apply Nat.log2_up_spec.
Qed.

Theorem Nat_pow2_le_pow2_mul_pow2_div :
  ∀ n i,
  0 < n ≤ 2 ^ i
  → 2 ^ i ≤ 2 ^ Nat.log2_up n * (2 ^ i / n).
Proof.
intros * (Hnz, Hni).
revert n Hnz Hni.
induction i; intros. {
  now replace n with 1 by (cbn in Hni; flia Hnz Hni).
}
rewrite Nat.pow_succ_r' at 1.
destruct (le_dec n (2 ^ i)) as [Hn2i| Hn2i]. {
  eapply Nat.le_trans. {
    apply Nat.mul_le_mono_l.
    apply IHi; [ apply Hnz | easy ].
  }
  rewrite Nat.mul_comm.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  apply Nat.div_le_lower_bound; [ flia Hnz | ].
  rewrite Nat.mul_comm.
  rewrite (Nat.mul_comm _ 2).
  rewrite <- Nat.mul_assoc.
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_le_mono_l.
  rewrite Nat.mul_comm.
  apply Nat.Div0.mul_div_le; flia Hnz.
}
apply Nat.nle_gt in Hn2i.
rewrite (Nat_div_less_small 1). 2: {
  rewrite Nat.mul_1_l.
  split; [ easy | ].
  rewrite Nat.pow_succ_r'.
  now apply Nat.mul_lt_mono_pos_l.
}
rewrite Nat.mul_1_r.
clear Hni.
clear IHi Hnz.
rewrite <- Nat.pow_succ_r'.
now apply Nat_pow2_succ_le_pow2_log2_up.
Qed.

Theorem angle_add_overflow_mul_by_lt :
  ∀ n i θ θ',
  n ≤ 2 ^ i
  → θ' = seq_angle_to_div_nat θ n i
  → ∀ m, m < n
  → angle_add_overflow θ' (m * θ') = false.
Proof.
intros * Hni Hθ' * Hm.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n.
  apply Nat.lt_1_r in Hm; subst m.
  cbn.
  apply angle_add_overflow_0_r.
}
destruct (lt_dec m 2) as [Hm2| Hm2]. {
  destruct m; [ apply angle_add_overflow_0_r | ].
  destruct m; [ | flia Hm2 ].
  rewrite angle_mul_1_l.
  subst θ'.
  now apply angle_add_overflow_pow2_div_mul_pow2_diag.
}
apply Nat.nlt_ge in Hm2.
rewrite <- angle_add_overflow_equiv2.
progress unfold angle_add_overflow2.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite angle_add_mul_r_diag_r.
rewrite Hθ'.
progress unfold seq_angle_to_div_nat at 2.
rewrite angle_mul_nat_assoc.
specialize (seq_angle_to_div_nat_le n i θ Hn1) as H2.
eapply angle_le_trans; [ apply H2 | clear H2 ].
destruct (le_dec i (inv_ub_den_pow2 n)) as [Hii| Hii]. {
  rewrite <- (angle_div_2_pow_mul_pow_sub (inv_ub_den_pow2 n) i); [ | easy ].
  rewrite angle_mul_nat_assoc.
  apply angle_mul_le_mono_r. {
    apply (angle_mul_nat_not_overflow_le_l _ (2 ^ inv_ub_den_pow2 n)). 2: {
      apply angle_mul_nat_overflow_pow_div.
    }
    rewrite Nat.pow_sub_r; [ | easy | easy ].
    eapply Nat.le_trans; [ apply Nat.Div0.div_mul_le | ].
    apply Nat.Div0.div_le_upper_bound.
    apply Nat.mul_le_mono_r.
    eapply Nat.le_trans; [ apply Nat.Div0.div_mul_le; flia Hm | ].
    apply Nat.Div0.div_le_upper_bound.
    now apply Nat.mul_le_mono_r.
  }
  rewrite Nat.pow_sub_r; [ | easy | easy ].
  rewrite <- Nat.Lcm0.divide_div_mul_exact. 2: {
    exists (2 ^ (inv_ub_den_pow2 n - i)).
    rewrite <- Nat.pow_add_r.
    now rewrite Nat.sub_add.
  }
  apply Nat.div_le_lower_bound; [ now apply Nat.pow_nonzero | ].
  progress unfold inv_ub_num.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
  apply Nat.le_sub_le_add_r.
  progress unfold inv_ub_den_pow2.
  rewrite <- Nat.add_assoc, Nat.add_1_r.
  rewrite Nat.pow_add_r.
  eapply Nat.le_trans; [ | apply Nat.le_add_r ].
  rewrite Nat.mul_assoc.
  apply Nat.mul_le_mono_r.
  rewrite rank_fst_1_log2_up; [ | flia Hm Hn1 ].
  eapply Nat.le_trans. 2: {
    apply Nat.mul_le_mono_r.
    apply Nat.mul_le_mono_r.
    assert (H : 2 ≤ S m) by flia Hm2.
    apply H.
  }
  rewrite Nat.mul_shuffle0.
  rewrite <- Nat.pow_succ_r'.
  rewrite <- Nat.sub_succ_l. 2: {
    destruct n; [ easy | ].
    destruct n; [ flia Hn1 | cbn; flia ].
  }
  rewrite Nat_sub_succ_1.
  apply Nat_pow2_le_pow2_mul_pow2_div.
  split; [ flia Hm | easy ].
} {
  apply Nat.nle_gt in Hii.
  generalize Hii; intros Hii'.
  apply Nat.lt_le_incl in Hii'.
  rewrite <- (angle_div_2_pow_mul_pow_sub i (inv_ub_den_pow2 n)); [ | easy ].
  rewrite angle_mul_nat_assoc.
  apply angle_mul_le_mono_r. {
    apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). 2: {
      apply angle_mul_nat_overflow_pow_div.
    }
    eapply Nat.le_trans; [ apply Nat.Div0.div_mul_le; flia Hm | ].
    apply Nat.Div0.div_le_upper_bound.
    now apply Nat.mul_le_mono_r.
  }
  rewrite Nat.pow_sub_r; [ | easy | easy ].
  rewrite <- Nat.Lcm0.divide_div_mul_exact. 2: {
    exists (2 ^ (i - inv_ub_den_pow2 n)).
    rewrite <- Nat.pow_add_r.
    now rewrite Nat.sub_add.
  }
  apply Nat.Div0.div_le_upper_bound.
  progress unfold inv_ub_num.
  rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
  apply Nat.le_sub_le_add_r.
  progress unfold inv_ub_den_pow2.
  rewrite <- Nat.add_assoc, Nat.add_1_r.
  rewrite Nat.pow_add_r.
  eapply Nat.le_trans; [ | apply Nat.le_add_r ].
  rewrite (Nat.mul_comm (2 ^ rank_fst_1 _ _)).
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  rewrite rank_fst_1_log2_up; [ | flia Hm Hn1 ].
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm _ (S m)).
  eapply Nat.le_trans. 2: {
    apply Nat.mul_le_mono_r.
    apply Nat.mul_le_mono_r.
    assert (H : 2 ≤ S m) by flia Hm2.
    apply H.
  }
  rewrite <- Nat.pow_succ_r'.
  rewrite <- Nat.sub_succ_l. 2: {
    destruct n; [ easy | ].
    destruct n; [ flia Hn1 | cbn; flia ].
  }
  rewrite Nat_sub_succ_1.
  apply Nat_pow2_le_pow2_mul_pow2_div.
  split; [ flia Hm | easy ].
}
Qed.

Theorem seq_angle_mul_nat_not_overflow :
  ∀ n θ i,
  angle_mul_nat_overflow n (seq_angle_to_div_nat θ n i) = false.
Proof.
intros.
apply angle_all_add_not_overflow.
intros m Hm.
destruct (lt_dec (2 ^ i) n) as [Hin| Hni]. {
  progress unfold seq_angle_to_div_nat.
  rewrite Nat.div_small; [ | easy ].
  apply angle_add_overflow_0_l.
}
apply Nat.nlt_ge in Hni.
now apply (angle_add_overflow_mul_by_lt n i θ).
Qed.

(**)

Theorem dist_diag : ∀ A dist (a : A), is_dist dist → dist a a = 0%L.
Proof.
intros * Hd.
now apply (dist_separation Hd).
Qed.

Theorem rngl_squ_lt_squ_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a * b = b * a → 0 ≤ a → a < b → a² < b²)%L.
Proof.
intros Hop Hor Hid.
intros * Habc Hza Hab.
apply (rngl_abs_lt_squ_lt Hop Hor Hid _ _ Habc).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
rewrite (rngl_abs_nonneg_eq Hop Hor); [ easy | ].
apply (rngl_le_trans Hor _ a); [ easy | ].
now apply (rngl_lt_le_incl Hor) in Hab.
Qed.

Theorem rngl_lt_cos_lt_cos_div2 :
  ∀ a b θ,
  (2 * b² ≤ a + 1)%L
  → (0 ≤ rngl_sin θ)%L
  → (a < rngl_cos θ)%L
  → (b < rngl_cos (θ /₂))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hba Hzs Hc.
  rewrite (H1 a) in Hc.
  rewrite (H1 (rngl_cos _)) in Hc.
  now apply (rngl_lt_irrefl Hor) in Hc.
}
intros * Hba Hzs Hc.
cbn.
apply rngl_leb_le in Hzs.
rewrite Hzs.
rewrite (rngl_mul_1_l Hon).
destruct (rngl_lt_dec Hor b 0) as [Hblz| Hbgz]. {
  eapply (rngl_lt_le_trans Hor _ 0); [ easy | ].
  apply rl_sqrt_nonneg.
  apply rngl_1_add_cos_div_2_nonneg.
}
apply (rngl_nlt_ge_iff Hor) in Hbgz.
rewrite <- (rngl_abs_nonneg_eq Hop Hor b); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_). 2: {
  apply rl_sqrt_nonneg.
  apply rngl_1_add_cos_div_2_nonneg.
}
apply (rngl_squ_lt_abs_lt Hon Hop Hiq Hor).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply rngl_1_add_cos_div_2_nonneg.
}
apply -> (rngl_lt_div_r Hon Hop Hiv Hor). 2: {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
rewrite (rngl_mul_comm Hic).
apply (rngl_lt_sub_lt_add_l Hop Hor).
eapply (rngl_le_lt_trans Hor); [ | apply Hc ].
now apply (rngl_le_sub_le_add_r Hop Hor).
Qed.

Theorem rngl_lt_add_cos_lt_add_cos_div2 :
  ∀ a b θ,
  (2 * (1 - b)² ≤ 2 - a)%L
  → (0 ≤ rngl_sin θ)%L
  → (1 < a + rngl_cos θ)%L
  → (1 < b + rngl_cos (θ /₂))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hba Hzs Ha.
apply (rngl_lt_sub_lt_add_l Hop Hor).
apply (rngl_lt_cos_lt_cos_div2 (1 - a)%L); [ | easy | ]. {
  now rewrite <- (rngl_add_sub_swap Hop).
} {
  now apply (rngl_lt_sub_lt_add_l Hop Hor).
}
Qed.

Theorem rngl_cos_sin_twice_lemma_1 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin (2 * θ1) < 0)%L
  → (rngl_sin (2 * θ2) < 0)%L
  → (rngl_cos (2 * θ1) ≤ rngl_cos (2 * θ2))%L
  → (rngl_cos θ2 ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzs21 Hzs22 H12.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs1 Hzs2 Hzs21 Hzs22 H12.
rewrite rngl_sin_mul_2_l in Hzs21, Hzs22.
rewrite <- rngl_mul_assoc in Hzs21, Hzs22.
apply (rngl_lt_mul_0_if Hos Hor) in Hzs21, Hzs22.
destruct Hzs21 as [(H, _)| (_, Hzs21)]. {
  exfalso; apply rngl_nle_gt in H; apply H.
  apply (rngl_0_le_2 Hon Hos Hiq Hor).
}
destruct Hzs22 as [(H, _)| (_, Hzs22)]. {
  exfalso; apply rngl_nle_gt in H; apply H.
  apply (rngl_0_le_2 Hon Hos Hiq Hor).
}
apply (rngl_lt_mul_0_if Hos Hor) in Hzs21, Hzs22.
destruct Hzs21 as [(H, _)| (_, Hzs21)]. {
  now apply rngl_nle_gt in H.
}
destruct Hzs22 as [(H, _)| (_, Hzs22)]. {
  now apply rngl_nle_gt in H.
}
do 2 rewrite rngl_cos_mul_2_l' in H12.
apply (rngl_sub_le_mono_r Hop Hor) in H12.
apply (rngl_mul_le_mono_pos_l Hon Hop Hiq Hor) in H12. 2: {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
apply (rngl_squ_le_abs_le Hon Hop Hiq Hor) in H12.
apply (rngl_lt_le_incl Hor) in Hzs21, Hzs22.
rewrite (rngl_abs_nonpos_eq Hop Hor) in H12; [ | easy ].
rewrite (rngl_abs_nonpos_eq Hop Hor) in H12; [ | easy ].
now apply (rngl_opp_le_compat Hop Hor) in H12.
Qed.

Theorem rngl_cos_sin_twice_lemma_2 :
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (2 * θ1))%L
  → (0 ≤ rngl_sin (2 * θ2))%L
  → (rngl_cos (2 * θ2) ≤ rngl_cos (2 * θ1))%L
  → (rngl_cos θ2 ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzs21 Hzs22 H12.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs1 Hzs2 Hzs21 Hzs22 H12.
rewrite rngl_sin_mul_2_l in Hzs21, Hzs22.
rewrite <- rngl_mul_assoc in Hzs21, Hzs22.
apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzs21, Hzs22.
destruct Hzs21 as [(_, Hzs21)| (H, _)]. 2: {
  exfalso; apply rngl_nlt_ge in H; apply H.
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
destruct Hzs22 as [(_, Hzs22)| (H, _)]. 2: {
  exfalso; apply rngl_nlt_ge in H; apply H.
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzs21, Hzs22.
destruct Hzs21 as [(_, Hzs21)| (H1, H2)]. 2: {
  now apply rngl_nlt_ge in H1.
}
destruct Hzs22 as [(_, Hzs22)| (H1, H2)]. 2: {
  apply (rngl_le_antisymm Hor) in H1; [ | easy ].
  symmetry in H1.
  apply eq_rngl_sin_0 in H1.
  destruct H1; subst θ2. {
    exfalso; apply rngl_nlt_ge in H2; apply H2.
    apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
  }
  apply rngl_cos_bound.
}
do 2 rewrite rngl_cos_mul_2_l' in H12.
apply (rngl_sub_le_mono_r Hop Hor) in H12.
apply (rngl_mul_le_mono_pos_l Hon Hop Hiq Hor) in H12. 2: {
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
apply (rngl_squ_le_abs_le Hon Hop Hiq Hor) in H12.
rewrite (rngl_abs_nonneg_eq Hop Hor) in H12; [ | easy ].
rewrite (rngl_abs_nonneg_eq Hop Hor) in H12; [ | easy ].
easy.
Qed.

Theorem rngl_cos_sin_twice_lemma_3 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (2 * θ1))%L
  → (rngl_sin (2 * θ2) < 0)%L
  → θ1 ≠ angle_straight
  → (rngl_cos θ2 ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzs21 Hzs22 Ht1.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs1 Hzs2 Hzs21 Hzs22 Ht1.
rewrite rngl_sin_mul_2_l in Hzs21, Hzs22.
rewrite <- rngl_mul_assoc in Hzs21, Hzs22.
apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzs21.
apply (rngl_lt_mul_0_if Hos Hor) in Hzs22.
destruct Hzs21 as [(_, Hzs21)| (H, _)]. 2: {
  exfalso; apply rngl_nlt_ge in H; apply H.
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
}
destruct Hzs22 as [(H, _)| (_, Hzs22)]. {
  exfalso; apply rngl_nle_gt in H; apply H.
  apply (rngl_0_le_2 Hon Hos Hiq Hor).
}
apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzs21.
apply (rngl_lt_mul_0_if Hos Hor) in Hzs22.
destruct Hzs21 as [(_, Hzs21)| (H1, H2)]. 2: {
  apply (rngl_le_antisymm Hor) in H1; [ | easy ].
  symmetry in H1.
  apply eq_rngl_sin_0 in H1.
  destruct H1; subst θ1; [ | easy ].
  exfalso; apply rngl_nlt_ge in H2; apply H2.
  apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
}
destruct Hzs22 as [(H1, _)| (_, Hzs22)]. {
  now apply rngl_nle_gt in H1.
}
apply (rngl_lt_le_incl Hor) in Hzs22.
now apply (rngl_le_trans Hor _ 0).
Qed.

Theorem quadrant_1_2_rngl_cos_add_l_le_rngl_cos :
  ∀ θ1 θ2 : angle T,
  (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hs1 Hs2 Hs12.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
  apply (rngl_lt_le_incl Hor) in Hs1.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
    now apply quadrant_1_rngl_cos_add_le_cos_l.
  }
  apply (rngl_nle_gt_iff Hor) in Hzc2.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hs2.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_goal T.
  apply (rngl_le_0_add Hos Hor); [ | easy ].
  apply (rngl_lt_le_incl Hor) in Hzc2.
  apply rngl_sin_add_nonneg; try easy.
}
apply (rngl_nle_gt_iff Hor) in Hzc1.
destruct (rngl_eq_dec Heo (rngl_cos θ1) (-1)) as [Hco1| Hco1]. 2: {
  generalize Hzc1; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply (rngl_lt_le_incl Hor) in Hs1.
  now apply angle_add_overflow_le_lemma_2.
}
apply eq_rngl_cos_opp_1 in Hco1.
rewrite Hco1 in Hs1.
now apply (rngl_lt_irrefl Hor) in Hs1.
Qed.

Theorem angle_le_0_r : ∀ θ, (θ ≤ 0 ↔ θ = 0)%A.
Proof.
destruct_ac.
intros.
split; intros H; [ | subst θ; apply angle_le_refl ].
progress unfold angle_leb in H.
cbn in H.
rewrite (rngl_leb_refl Hor) in H.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; [ | easy ].
apply rngl_leb_le in H.
apply (rngl_le_antisymm Hor) in H; [ | apply rngl_cos_bound ].
now apply eq_rngl_cos_1 in H.
Qed.

Theorem eq_angle_mul_0_iff :
  ∀ n θ,
  angle_mul_nat_overflow n θ = false
  → (n * θ = 0)%A
  ↔ n = 0 ∨ θ = 0%A.
Proof.
intros * Hov.
split. 2: {
  intros [H| H]. {
    subst n.
    apply angle_mul_0_l.
  } {
    subst θ.
    apply angle_mul_0_r.
  }
}
intros Hnt.
specialize (proj2 (angle_all_add_not_overflow _ _) Hov) as H.
clear Hov; rename H into Hov.
assert (∀ m, m < n → (θ ≤ θ + m * θ)%A). {
  intros * Hmn.
  specialize (Hov _ Hmn).
  rewrite <- angle_add_overflow_equiv2 in Hov.
  progress unfold angle_add_overflow2 in Hov.
  apply Bool.not_true_iff_false in Hov.
  now apply angle_nlt_ge in Hov.
}
clear Hov; rename H into Hov.
move Hov after Hnt.
destruct n; [ now left | right ].
specialize (Hov n (Nat.lt_succ_diag_r _)) as H1.
rewrite <- angle_mul_succ_l in H1.
rewrite Hnt in H1.
now apply angle_le_0_r in H1.
Qed.

Theorem rngl_leb_0_sqrt :
  ∀ a, (0 ≤ a)%L → (0 ≤? √a)%L = true.
Proof.
intros * Hza.
apply rngl_leb_le.
now apply rl_sqrt_nonneg.
Qed.

Theorem rngl_acos_decr :
  ∀ a b, (-1 ≤ a < b ≤ 1)%L → (rngl_acos b < rngl_acos a)%A.
Proof.
destruct_ac.
intros * (H1a & Hab & Hb1).
assert (H1a1 : (-1 ≤ a ≤ 1)%L). {
  apply (rngl_lt_le_incl Hor) in Hab.
  split; [ easy | ].
  now apply (rngl_le_trans Hor _ b).
}
assert (H1b1 : (-1 ≤ b ≤ 1)%L). {
  apply (rngl_lt_le_incl Hor) in Hab.
  split; [ | easy ].
  now apply (rngl_le_trans Hor _ a).
}
progress unfold angle_ltb.
rewrite rngl_cos_acos; [ | easy ].
rewrite rngl_cos_acos; [ | easy ].
rewrite rngl_sin_acos; [ | easy ].
rewrite rngl_sin_acos; [ | easy ].
rewrite rngl_leb_0_sqrt. 2: {
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_squ_le_1 Hon Hop Hor).
}
rewrite rngl_leb_0_sqrt. 2: {
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_squ_le_1 Hon Hop Hor).
}
now apply rngl_ltb_lt.
Qed.

Theorem rngl_acos_bound : ∀ a, (0 ≤ rngl_acos a ≤ angle_straight)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros.
progress unfold rngl_acos.
progress fold Hor.
destruct (rngl_le_dec Hor a² 1) as [Ha1| H1a]. {
  progress unfold angle_leb.
  cbn.
  rewrite (rngl_leb_refl Hor).
  rewrite rngl_leb_0_sqrt; [ | now apply (rngl_le_0_sub Hop Hor) ].
  split. {
    apply rngl_leb_le.
    now apply (rngl_between_opp_1_and_1 Hon Hop Hiq Hor) in Ha1.
  } {
    apply rngl_leb_le.
    now apply (rngl_between_opp_1_and_1 Hon Hop Hiq Hor) in Ha1.
  }
} {
  split; [ apply angle_le_refl | ].
  apply angle_straight_nonneg.
}
Qed.

Theorem eq_rngl_acos_0 :
  ∀ a, (-1 ≤ a ≤ 1)%L → rngl_acos a = 0%A → a = 1%L.
Proof.
destruct_ac.
intros * H1a1 Haz.
progress unfold rngl_acos in Haz.
progress fold Hor in Haz.
destruct (rngl_le_dec Hor a² 1) as [Ha1| H1a]; [ now injection Haz | ].
exfalso; apply H1a.
now apply (rngl_squ_le_1 Hon Hop Hor) in H1a1.
Qed.

Theorem rngl_sin_nonneg_is_pos :
  ∀ θ,
  θ ≠ 0%A
  → θ ≠ angle_straight
  → (0 ≤ rngl_sin θ)%L
  → (0 < rngl_sin θ)%L.
Proof.
intros * Hz Hs Hsz.
destruct_ac.
apply (rngl_le_neq Hor).
split; [ easy | ].
intros H; symmetry in H.
apply eq_rngl_sin_0 in H.
now destruct H.
Qed.

Theorem rngl_lt_0_sin :
  ∀ θ,
  (0 < θ < angle_straight)%A
  → (0 < rngl_sin θ)%L.
Proof.
destruct_ac.
intros * (Hzt, Hts).
progress unfold angle_ltb in Hzt.
progress unfold angle_ltb in Hts.
cbn in Hzt, Hts.
rewrite (rngl_leb_refl Hor) in Hzt, Hts.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; [ | easy ].
apply rngl_leb_le in Hzs.
apply rngl_ltb_lt in Hzt, Hts.
apply rngl_sin_nonneg_is_pos; [ | | easy ]. {
  intros H; subst θ.
  now apply (rngl_lt_irrefl Hor) in Hzt.
} {
  intros H; subst θ.
  now apply (rngl_lt_irrefl Hor) in Hts.
}
Qed.

Theorem is_Cauchy_sequence_eq_compat :
  ∀ A (dist : A → A → T) a b f g,
  (∀ i, f (i + a) = g (i + b))
  → is_Cauchy_sequence dist f
  → is_Cauchy_sequence dist g.
Proof.
intros * Hfg Hf.
intros ε Hε.
specialize (Hf ε Hε).
destruct Hf as (N, HN).
exists (N + max a b).
intros p q Hnp Hnq.
specialize (HN (p - b + a) (q - b + a)).
assert (Hp : N ≤ p - b + a) by flia Hnp.
assert (Hq : N ≤ q - b + a) by flia Hnq.
specialize (HN Hp Hq).
do 2 rewrite Hfg in HN.
rewrite Nat.sub_add in HN; [ | flia Hnp ].
rewrite Nat.sub_add in HN; [ | flia Hnq ].
easy.
Qed.

Theorem rngl_sin_incr_lt :
  ∀ θ1 θ2,
  (θ1 < θ2 ≤ angle_right)%A
  → (rngl_sin θ1 < rngl_sin θ2)%L.
Proof.
destruct_ac.
intros * (H12, H2s).
progress unfold angle_ltb in H12.
progress unfold angle_leb in H2s.
cbn in H2s.
specialize (rngl_0_le_1 Hon Hos Hiq Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1 in H2s; clear H1.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs2; [ | easy ].
destruct zs1; [ | easy ].
apply rngl_leb_le in Hzs1, Hzs2, H2s.
apply rngl_ltb_lt in H12.
apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy.
apply (rngl_le_trans Hor _ (rngl_cos θ2)); [ easy | ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_squ_le_diag :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a ≤ 1 → a² ≤ a)%L.
Proof.
intros Hon Hop Hor * Ha.
rewrite <- (rngl_mul_1_r Hon a) at 2.
now apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor).
Qed.

Theorem rngl_limit_sub_l_limit :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a u l,
  is_limit_when_seq_tends_to_inf rngl_dist (λ i, (a - u i)%L) (a - l)%L
  → is_limit_when_seq_tends_to_inf rngl_dist u l.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hlim.
intros ε Hε.
specialize (Hlim ε Hε).
destruct Hlim as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
cbn in HN.
progress unfold rngl_dist in HN.
rewrite (rngl_sub_sub_swap Hop) in HN.
rewrite (rngl_sub_sub_distr Hop) in HN.
rewrite (rngl_sub_diag Hos) in HN.
rewrite rngl_add_0_l in HN.
now rewrite (rngl_abs_sub_comm Hop Hor) in HN.
Qed.

End a.
