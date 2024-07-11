(* File created because Work.v became too big, but
   without any topic found for the moment *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Init.Nat.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike.
Require Import Misc.
Require Import RealLike TrigoWithoutPi TrigoWithoutPiExt.
Require Import AngleAddLeMonoL.
Require Import AngleAddOverflowLe.
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
now apply Nat.mod_add.
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
    rewrite <- Nat.mul_mod_idemp_l; [ | flia Hab ].
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
    rewrite <- Nat.mul_mod_idemp_l; [ | flia Hab ].
    now apply H2.
  }
  destruct H3 as [H3| H3]; [ now subst it | right ].
  progress unfold nth_bit_of_div in H3.
  progress unfold nth_rest_of_div in H3.
  progress unfold nth_bit_of_div.
  progress unfold nth_rest_of_div.
  rewrite Nat.pow_succ_r', Nat.mul_assoc.
  rewrite (Nat.mul_comm a).
  rewrite <- Nat.mul_mod_idemp_l; [ easy | flia Hab ].
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
    rewrite <- Nat.mul_mod_idemp_l; [ | flia Hab ].
    specialize (Nat_mod_sub (2 * a) 1 b) as H.
    rewrite Nat.mul_1_l in H.
    rewrite H; [ clear H | flia Hab | easy ].
    rewrite Nat.mul_mod_idemp_l; [ | flia Hab ].
    rewrite (Nat.mul_comm _ a), <- Nat.mul_assoc.
    rewrite <- Nat.pow_succ_r'.
    apply Nat.succ_lt_mono in Ht.
    now apply H2.
  }
  progress unfold nth_rest_of_div in H2.
  progress unfold nth_rest_of_div.
  rewrite <- Nat.mul_mod_idemp_l; [ | flia Hab ].
  specialize (Nat_mod_sub (2 * a) 1 b) as H.
  rewrite Nat.mul_1_l in H.
  rewrite H; [ clear H | flia Hab | easy ].
  rewrite Nat.mul_mod_idemp_l; [ | flia Hab ].
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
rewrite Nat.mul_mod_idemp_l; [ easy | flia Hab ].
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
  apply (le_trans _ n); [ | apply Nat.le_succ_diag_r ].
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
  eapply le_trans; [ apply Nat.lt_le_incl, Hm3 | ].
  rewrite Nat.pow_succ_r'.
  specialize (Nat.pow_nonzero 2 m (Nat.neq_succ_0 _)) as H1.
  destruct (2 ^ m); [ easy | flia ].
}
apply Nat.nlt_ge in Hpn.
rewrite Nat.mod_eq in Hm3; [ | flia H2n ].
rewrite Nat.mul_sub_distr_l in Hm3.
apply Nat.lt_sub_lt_add_l in Hm3.
rewrite (Nat.mul_comm _ (_ * _)) in Hm3.
rewrite <- Nat.mul_assoc in Hm3.
rewrite <- (Nat.mul_1_r n) in Hm3 at 3.
rewrite <- Nat.mul_add_distr_l in Hm3.
eapply le_trans; [ apply Nat.lt_le_incl, Hm3 | ].
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
apply Nat.div_lt_upper_bound; [ flia H2n | ].
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
       inv_ub_num n * (θ / ₂^inv_ub_den_pow2 n))%A.
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
  rewrite <- Nat.divide_div_mul_exact; [ | now apply Nat.pow_nonzero | ]. 2: {
    exists (2 ^ (inv_ub_den_pow2 n - i)).
    rewrite <- Nat.pow_add_r.
    now rewrite Nat.sub_add.
  }
  (* (2^i/n * 2^bn)/2^i ≤ an *)
  apply Nat.div_le_upper_bound; [ now apply Nat.pow_nonzero | ].
  (* 2^i/n * 2^bn ≤ 2^i * an *)
  rewrite Nat.mul_comm.
  (* 2^bn * (2^i/n) ≤ 2^i * an *)
  eapply le_trans; [ now apply Nat.div_mul_le | ].
  (* (2^bn * 2^i) / n ≤ 2^i * an *)
  apply Nat.div_le_upper_bound; [ easy | ].
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
  rewrite <- Nat.divide_div_mul_exact; [ | now apply Nat.pow_nonzero | ]. 2: {
    exists (2 ^ (i - inv_ub_den_pow2 n)).
    rewrite <- Nat.pow_add_r.
    apply Nat.lt_le_incl in Hni.
    now rewrite Nat.sub_add.
  }
  (* 2^i/n ≤ an * 2^i / 2^bn *)
  apply Nat.div_le_lower_bound; [ now apply Nat.pow_nonzero | ].
  (* 2^bn * (2^i/n) ≤ an * 2^i *)
  eapply le_trans; [ now apply Nat.div_mul_le | ].
  (* (2^bn * 2^i) / n ≤ an * 2^i *)
  apply Nat.div_le_upper_bound; [ easy | ].
  (* 2^bn * 2^i ≤ n * (an * 2^i) *)
  rewrite Nat.mul_assoc.
  apply Nat.mul_le_mono_r.
  apply pow2_den_le_mul_num; flia Hn1 Hnz.
}
Qed.

Theorem angle_add_overflow_mul_by_lt_2 :
  ∀ i θ θ',
  2 ≤ 2 ^ i
  → θ' = seq_angle_to_div_nat θ 2 i
  → ∀ m : nat, m < 2
  → angle_add_overflow θ' (m * θ') = false.
Proof.
intros * Hni Hθ' * Hm.
destruct m; [ apply angle_add_overflow_0_r | ].
apply Nat.succ_lt_mono in Hm.
apply Nat.lt_1_r in Hm; subst m.
rewrite angle_mul_1_l.
destruct i; [ now apply Nat.succ_le_mono in Hni | ].
subst θ'.
progress unfold seq_angle_to_div_nat.
rewrite Nat.pow_succ_r'.
rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
rewrite angle_div_2_pow_succ_r_2.
rewrite angle_div_2_pow_mul_2_pow.
apply angle_add_overflow_div_2_div_2.
Qed.

Theorem angle_add_overflow_mul_by_lt_3 :
  ∀ i θ θ',
  3 ≤ 2 ^ i
  → θ' = seq_angle_to_div_nat θ 3 i
  → ∀ m : nat, m < 3
  → angle_add_overflow θ' (m * θ') = false.
Proof.
intros * Hni Hθ' * Hm.
destruct m; [ apply angle_add_overflow_0_r | ].
progress unfold angle_add_overflow.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite angle_add_mul_r_diag_r.
rewrite Hθ'.
progress unfold seq_angle_to_div_nat.
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). 2: {
    apply angle_mul_nat_overflow_pow_div.
  }
  destruct i; [ now apply Nat.succ_le_mono in Hni | ].
  destruct i; [ now do 2 apply Nat.succ_le_mono in Hni | ].
  eapply le_trans; [ now apply Nat.div_mul_le | ].
  apply Nat.div_le_upper_bound; [ easy | ].
  now apply Nat.mul_le_mono_r.
}
(* lemma *)
rewrite Nat.mul_comm.
apply Nat_mul_le_pos_r.
now apply -> Nat.succ_le_mono.
Qed.

Theorem angle_add_overflow_mul_by_lt_4 :
  ∀ i θ θ',
  4 ≤ 2 ^ i
  → θ' = seq_angle_to_div_nat θ 4 i
  → ∀ m : nat, m < 4
  → angle_add_overflow θ' (m * θ') = false.
Proof.
intros * Hni Hθ' * Hm.
destruct m; [ apply angle_add_overflow_0_r | ].
progress unfold angle_add_overflow.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite angle_add_mul_r_diag_r.
rewrite Hθ'.
progress unfold seq_angle_to_div_nat.
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). 2: {
    apply angle_mul_nat_overflow_pow_div.
  }
  destruct i; [ now apply Nat.succ_le_mono in Hni | ].
  destruct i; [ now do 2 apply Nat.succ_le_mono in Hni | ].
  rewrite Nat.pow_succ_r', (Nat.mul_comm 2).
  rewrite Nat.pow_succ_r', (Nat.mul_comm 2).
  rewrite <- Nat.mul_assoc.
  rewrite Nat.div_mul; [ | easy ].
  rewrite Nat.mul_comm.
  now apply Nat.mul_le_mono_l.
}
(* lemma *)
rewrite Nat.mul_comm.
apply Nat_mul_le_pos_r.
now apply -> Nat.succ_le_mono.
Qed.

Theorem angle_add_overflow_mul_by_lt_5 :
  ∀ i θ θ',
  5 ≤ 2 ^ i
  → θ' = seq_angle_to_div_nat θ 5 i
  → ∀ m, m < 5
  → angle_add_overflow θ' (m * θ') = false.
Proof.
intros * Hni Hθ' * Hm.
destruct m; [ apply angle_add_overflow_0_r | ].
apply Nat.succ_lt_mono in Hm.
progress unfold angle_add_overflow.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite angle_add_mul_r_diag_r.
rewrite Hθ'.
progress unfold seq_angle_to_div_nat at 2.
rewrite angle_mul_nat_assoc.
assert (H : 5 ≠ 1) by easy.
specialize (seq_angle_to_div_nat_le 5 i θ H) as H2; clear H.
eapply angle_le_trans; [ apply H2 | ].
destruct (lt_dec i 5) as [Hi5| Hi5]. {
  clear - Hni Hi5 Hm.
  destruct i; [ now cbn in Hni; apply Nat.succ_le_mono in Hni | ].
  destruct i; [ now cbn in Hni; do 2 apply Nat.succ_le_mono in Hni | ].
  destruct i; [ now cbn in Hni; do 4 apply Nat.succ_le_mono in Hni | ].
  destruct i. {
    rewrite (Nat_div_less_small 1); [ | cbn; flia ].
    rewrite Nat.mul_1_r.
    rewrite <- (angle_div_2_pow_mul_2_pow 2 θ) at 2.
    rewrite angle_div_2_pow_mul. 2: {
      now apply angle_mul_nat_overflow_div_pow2.
    }
    rewrite <- angle_div_2_pow_add_r.
    rewrite angle_mul_nat_assoc.
    apply angle_mul_le_mono_r. 2: {
      now cbn; do 7 apply -> Nat.succ_le_mono.
    }
    apply (angle_mul_nat_not_overflow_le_l _ (2 ^ 5)). {
      remember (S (S m)) as m'; cbn; subst m'.
      destruct m; [ now do 8 apply -> Nat.succ_le_mono | ].
      destruct m; [ now do 12 apply -> Nat.succ_le_mono | ].
      destruct m; [ now do 16 apply -> Nat.succ_le_mono | ].
      destruct m; [ now do 20 apply -> Nat.succ_le_mono | ].
      now do 4 apply Nat.succ_lt_mono in Hm.
    }
    now apply angle_mul_nat_overflow_div_pow2.
  }
  destruct i. {
    rewrite (Nat_div_less_small 3); [ | cbn; flia ].
    rewrite <- (angle_div_2_pow_mul_2_pow 1 θ) at 2.
    rewrite angle_div_2_pow_mul. 2: {
      now apply angle_mul_nat_overflow_div_pow2.
    }
    rewrite <- angle_div_2_pow_add_r.
    rewrite angle_mul_nat_assoc.
    apply angle_mul_le_mono_r. 2: {
      now do 7 apply -> Nat.succ_le_mono.
    }
    rewrite Nat.pow_1_r.
    apply (angle_mul_nat_not_overflow_le_l _ (2 ^ 5)). {
      rewrite <- Nat.mul_assoc.
      remember (S (S m)) as m'; cbn; subst m'.
      destruct m; [ now do 12 apply -> Nat.succ_le_mono | ].
      destruct m; [ now do 18 apply -> Nat.succ_le_mono | ].
      destruct m; [ now do 24 apply -> Nat.succ_le_mono | ].
      destruct m; [ now do 30 apply -> Nat.succ_le_mono | ].
      now do 4 apply Nat.succ_lt_mono in Hm.
    }
    now apply angle_mul_nat_overflow_div_pow2.
  }
  now do 5 apply Nat.succ_lt_mono in Hi5.
}
apply Nat.nlt_ge in Hi5.
rewrite <- (angle_div_2_pow_mul_pow_sub i 5); [ | easy ].
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). 2: {
    apply angle_mul_nat_overflow_pow_div.
  }
  eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
  apply Nat.div_le_upper_bound; [ easy | ].
  apply Nat.mul_le_mono_r.
  now apply -> Nat.succ_le_mono.
}
clear Hni Hθ' H2.
induction i; [ easy | ].
apply Nat.succ_le_mono in Hi5.
rewrite Nat.sub_succ.
destruct (Nat.eq_dec i 4) as [Hi4| Hi4]. {
  subst i; cbn.
  now do 7 apply -> Nat.succ_le_mono.
}
assert (H : 5 ≤ i) by flia Hi5 Hi4.
clear Hi4 Hi5; rename H into Hi5.
specialize (IHi Hi5).
rewrite <- Nat.sub_succ.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.pow_succ_r'.
rewrite Nat.mul_comm.
rewrite Nat.mul_shuffle0.
rewrite <- Nat.mul_assoc.
eapply le_trans; [ apply Nat.mul_le_mono_l, IHi | ].
rewrite Nat.mul_assoc.
rewrite (Nat.mul_comm 2).
rewrite <- Nat.mul_assoc.
apply Nat.mul_le_mono_l.
rewrite Nat.pow_succ_r'.
now apply Nat.div_mul_le.
Qed.

Theorem angle_add_overflow_mul_by_lt_6 :
  ∀ i θ θ',
  6 ≤ 2 ^ i
  → θ' = seq_angle_to_div_nat θ 6 i
  → ∀ m, m < 6
  → angle_add_overflow θ' (m * θ') = false.
Proof.
intros * Hni Hθ' * Hm.
destruct m; [ apply angle_add_overflow_0_r | ].
apply Nat.succ_lt_mono in Hm.
progress unfold angle_add_overflow.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite angle_add_mul_r_diag_r.
rewrite Hθ'.
progress unfold seq_angle_to_div_nat at 2.
rewrite angle_mul_nat_assoc.
assert (H : 6 ≠ 1) by easy.
specialize (seq_angle_to_div_nat_le 6 i θ H) as H2; clear H.
eapply angle_le_trans; [ apply H2 | clear H2 ].
destruct (lt_dec i 4) as [Hi4| Hi4]. {
  destruct i; [ now cbn in Hni; apply Nat.succ_le_mono in Hni | ].
  destruct i; [ now cbn in Hni; do 2 apply Nat.succ_le_mono in Hni | ].
  destruct i; [ now cbn in Hni; do 4 apply Nat.succ_le_mono in Hni | ].
  do 3 apply Nat.succ_lt_mono in Hi4.
  apply Nat.lt_1_r in Hi4; subst i.
  clear Hni.
  rewrite (Nat_div_less_small 1); [ | cbn; flia ].
  rewrite Nat.mul_1_r.
  rewrite <- (angle_div_2_pow_mul_2_pow 1 θ) at 2.
  rewrite angle_div_2_pow_mul. 2: {
    now apply angle_mul_nat_overflow_div_pow2.
  }
  rewrite <- angle_div_2_pow_add_r.
  rewrite angle_mul_nat_assoc.
  apply angle_mul_le_mono_r. 2: {
    now cbn; do 3 apply -> Nat.succ_le_mono.
  }
  replace (1 + 3) with 4 by easy.
  rewrite Nat.pow_1_r.
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ 4)). 2: {
    now apply angle_mul_nat_overflow_div_pow2.
  }
  destruct m; [ now do 4 apply -> Nat.succ_le_mono | ].
  destruct m; [ now do 6 apply -> Nat.succ_le_mono | ].
  destruct m; [ now do 8 apply -> Nat.succ_le_mono | ].
  destruct m; [ now do 10 apply -> Nat.succ_le_mono | ].
  do 4 apply Nat.succ_lt_mono in Hm.
  apply Nat.lt_1_r in Hm; subst m; cbn.
  now do 12 apply -> Nat.succ_le_mono.
}
apply Nat.nlt_ge in Hi4.
rewrite <- (angle_div_2_pow_mul_pow_sub i 4); [ | easy ].
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). 2: {
    apply angle_mul_nat_overflow_pow_div.
  }
  eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
  apply Nat.div_le_upper_bound; [ easy | ].
  apply Nat.mul_le_mono_r.
  destruct m; [ now apply -> Nat.succ_le_mono | ].
  destruct m; [ now apply -> Nat.succ_le_mono | ].
  destruct m; [ now apply -> Nat.succ_le_mono | ].
  destruct m; [ now apply -> Nat.succ_le_mono | ].
  destruct m; [ now apply -> Nat.succ_le_mono | ].
  now do 5 apply Nat.succ_lt_mono in Hm.
}
clear Hni Hθ'.
induction i; [ easy | ].
apply Nat.succ_le_mono in Hi4.
rewrite Nat.sub_succ.
destruct (Nat.eq_dec i 3) as [Hi3| Hi3]. {
  subst i; cbn.
  now do 3 apply -> Nat.succ_le_mono.
}
assert (H : 4 ≤ i) by flia Hi4 Hi3.
clear Hi3 Hi4; rename H into Hi4.
specialize (IHi Hi4).
rewrite <- Nat.sub_succ.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.pow_succ_r'.
rewrite (Nat.mul_comm 2).
rewrite Nat.mul_assoc.
rewrite Nat.mul_comm.
eapply le_trans; [ apply Nat.mul_le_mono_l, IHi | ].
rewrite Nat.mul_comm.
rewrite <- Nat.mul_assoc.
apply Nat.mul_le_mono_l.
rewrite Nat.mul_comm.
eapply le_trans; [ now apply Nat.div_mul_le | ].
now rewrite Nat.pow_succ_r'.
Qed.

Theorem angle_add_overflow_mul_by_lt_7 :
  ∀ i θ θ',
  7 ≤ 2 ^ i
  → θ' = seq_angle_to_div_nat θ 7 i
  → ∀ m, m < 7
  → angle_add_overflow θ' (m * θ') = false.
Proof.
intros * Hni Hθ' * Hm.
destruct m; [ apply angle_add_overflow_0_r | ].
progress unfold angle_add_overflow.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite angle_add_mul_r_diag_r.
rewrite Hθ'.
progress unfold seq_angle_to_div_nat at 2.
rewrite angle_mul_nat_assoc.
assert (H : 7 ≠ 1) by easy.
specialize (seq_angle_to_div_nat_le 7 i θ H) as H2; clear H.
eapply angle_le_trans; [ apply H2 | clear H2 ].
assert (Hm4 : S (S m) * 2 ≤ 2 ^ 4). {
  destruct m; [ now do 4 apply -> Nat.succ_le_mono | ].
  destruct m; [ now do 6 apply -> Nat.succ_le_mono | ].
  destruct m; [ now do 8 apply -> Nat.succ_le_mono | ].
  destruct m; [ now do 10 apply -> Nat.succ_le_mono | ].
  destruct m; [ now do 12 apply -> Nat.succ_le_mono | ].
  destruct m; [ now do 14 apply -> Nat.succ_le_mono | ].
  now do 7 apply Nat.succ_lt_mono in Hm.
}
destruct (lt_dec i 4) as [Hi4| Hi4]. {
  destruct i; [ now apply Nat.succ_le_mono in Hni | ].
  destruct i; [ now do 2 apply Nat.succ_le_mono in Hni | ].
  destruct i; [ now do 4 apply Nat.succ_le_mono in Hni | ].
  do 3 apply Nat.succ_lt_mono in Hi4.
  apply Nat.lt_1_r in Hi4; subst i.
  clear Hni.
  rewrite (Nat_div_less_small 1); [ | cbn; flia ].
  rewrite <- (angle_div_2_pow_mul_2_pow 1 θ) at 2.
  rewrite angle_div_2_pow_mul. 2: {
    now apply angle_mul_nat_overflow_div_pow2.
  }
  rewrite <- angle_div_2_pow_add_r.
  rewrite angle_mul_nat_assoc.
  apply angle_mul_le_mono_r. 2: {
    now do 3 apply -> Nat.succ_le_mono.
  }
  rewrite Nat.pow_1_r, <- Nat.mul_assoc.
  rewrite Nat.mul_1_l.
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ 4)); [ easy | ].
  now apply angle_mul_nat_overflow_div_pow2.
}
apply Nat.nlt_ge in Hi4.
rewrite <- (angle_div_2_pow_mul_pow_sub i 4); [ | easy ].
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). 2: {
    apply angle_mul_nat_overflow_pow_div.
  }
  eapply le_trans; [ now apply Nat.div_mul_le | ].
  apply Nat.div_le_upper_bound; [ easy | ].
  now apply Nat.mul_le_mono_r.
}
clear Hni Hθ'.
induction i; [ easy | ].
apply Nat.succ_le_mono in Hi4.
destruct (Nat.eq_dec i 3) as [Hi3| Hi3]. {
  subst i; cbn.
  now do 3 apply -> Nat.succ_le_mono.
}
assert (H : 4 ≤ i) by flia Hi4 Hi3.
clear Hi4 Hi3; rename H into Hi4.
specialize (IHi Hi4).
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.pow_succ_r'.
rewrite (Nat.mul_comm 2).
rewrite Nat.mul_assoc.
rewrite Nat.mul_comm.
eapply le_trans; [ apply Nat.mul_le_mono_l, IHi | ].
rewrite Nat.mul_assoc, (Nat.mul_comm 2).
rewrite <- Nat.mul_assoc.
apply Nat.mul_le_mono_l.
rewrite Nat.pow_succ_r'.
now apply Nat.div_mul_le.
Qed.

Theorem fold_seq_angle_to_div_nat :
  ∀ θ n i, (2 ^ i / n * (θ / ₂^i))%A = seq_angle_to_div_nat θ n i.
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
  eapply le_trans. {
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
  apply Nat.mul_div_le; flia Hnz.
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
progress unfold angle_add_overflow.
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
    eapply le_trans. {
      apply Nat.div_mul_le.
      now apply Nat.pow_nonzero.
    }
    apply Nat.div_le_upper_bound; [ now apply Nat.pow_nonzero | ].
    apply Nat.mul_le_mono_r.
    eapply le_trans; [ apply Nat.div_mul_le; flia Hm | ].
    apply Nat.div_le_upper_bound; [ flia Hm | ].
    now apply Nat.mul_le_mono_r.
  }
  rewrite Nat.pow_sub_r; [ | easy | easy ].
  rewrite <- Nat.divide_div_mul_exact; cycle 1. {
    now apply Nat.pow_nonzero.
  } {
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
  eapply le_trans; [ | apply Nat.le_add_r ].
  rewrite Nat.mul_assoc.
  apply Nat.mul_le_mono_r.
  rewrite rank_fst_1_log2_up; [ | flia Hm Hn1 ].
  eapply le_trans. 2: {
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
    eapply le_trans; [ apply Nat.div_mul_le; flia Hm | ].
    apply Nat.div_le_upper_bound; [ flia Hm | ].
    now apply Nat.mul_le_mono_r.
  }
  rewrite Nat.pow_sub_r; [ | easy | easy ].
  rewrite <- Nat.divide_div_mul_exact; cycle 1. {
    now apply Nat.pow_nonzero.
  } {
    exists (2 ^ (i - inv_ub_den_pow2 n)).
    rewrite <- Nat.pow_add_r.
    now rewrite Nat.sub_add.
  }
  apply Nat.div_le_upper_bound; [ now apply Nat.pow_nonzero | ].
  progress unfold inv_ub_num.
  rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
  apply Nat.le_sub_le_add_r.
  progress unfold inv_ub_den_pow2.
  rewrite <- Nat.add_assoc, Nat.add_1_r.
  rewrite Nat.pow_add_r.
  eapply le_trans; [ | apply Nat.le_add_r ].
  rewrite (Nat.mul_comm (2 ^ rank_fst_1 _ _)).
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  rewrite rank_fst_1_log2_up; [ | flia Hm Hn1 ].
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm _ (S m)).
  eapply le_trans. 2: {
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
  ∀ n i θ,
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

Theorem angle_eucl_dist_add_cancel_l :
  ∀ θ1 θ2 θ3,
  angle_eucl_dist (θ1 + θ2) (θ1 + θ3) = angle_eucl_dist θ2 θ3.
Proof.
intros.
rewrite angle_eucl_dist_move_0_l.
rewrite angle_sub_add_distr.
rewrite angle_add_sub_swap.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
symmetry.
apply angle_eucl_dist_move_0_l.
Qed.

Theorem angle_eucl_dist_mul_le :
  ∀ n θ,
  (angle_eucl_dist (n * θ) 0 ≤ rngl_of_nat n * angle_eucl_dist θ 0)%L.
Proof.
intros.
destruct_ac.
intros.
induction n. {
  rewrite angle_eucl_dist_diag.
  cbn; rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_refl Hor).
}
rewrite rngl_of_nat_succ.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_1_l Hon).
rewrite <- (angle_eucl_dist_sub_l_diag θ).
rewrite <- angle_eucl_dist_opp_opp.
rewrite angle_opp_sub_distr.
cbn.
rewrite angle_add_sub_swap.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
eapply (rngl_le_trans Hor). {
  apply angle_eucl_dist_triangular with (θ2 := 0%A).
}
rewrite <- angle_opp_0 at 2.
rewrite angle_eucl_dist_opp_opp.
rewrite rngl_add_comm.
rewrite angle_eucl_dist_symmetry.
now apply (rngl_add_le_mono_l Hop Hor).
Qed.

Theorem angle_eucl_dist_mul_mul_le :
  ∀ n θ1 θ2,
  (angle_eucl_dist (n * θ1) (n * θ2) ≤
     rngl_of_nat n * (angle_eucl_dist θ1 0 + angle_eucl_dist θ2 0))%L.
Proof.
destruct_ac.
intros.
eapply (rngl_le_trans Hor). {
  eapply (rngl_le_trans Hor). {
    apply angle_eucl_dist_triangular with (θ2 := 0%A).
  }
  rewrite (angle_eucl_dist_symmetry 0%A).
  eapply (rngl_add_le_compat Hor); apply angle_eucl_dist_mul_le.
}
rewrite rngl_mul_add_distr_l.
apply (rngl_le_refl Hor).
Qed.

Theorem angle_lim_angle_lim_mul_mul :
  ∀ n θ θ',
  angle_lim θ θ'
  → angle_lim (λ i, n * θ i)%A (n * θ').
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros * Hlim ε Hε.
  exists 0.
  intros m Hm.
  rewrite (H1 (n * θ m)%A).
  rewrite (H1 (n * θ')%A).
  now rewrite angle_eucl_dist_diag.
}
intros * Hlim.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  intros ε Hε.
  exists 0.
  intros m Hm.
  do 2 rewrite angle_mul_0_l.
  now rewrite angle_eucl_dist_diag.
}
intros ε Hε.
specialize (Hlim (ε / rngl_of_nat n)%L).
assert (Hεz : (0 < ε / rngl_of_nat n)%L). {
  apply (rngl_div_lt_pos Hon Hop Hiv Hor); [ easy | ].
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  now apply Nat.neq_0_lt_0.
}
specialize (Hlim Hεz).
destruct Hlim as (N, Hlim).
exists N.
intros m Hm.
specialize (Hlim m Hm).
rewrite angle_eucl_dist_move_0_r in Hlim.
rewrite angle_eucl_dist_move_0_r.
rewrite <- angle_mul_sub_distr_l.
eapply (rngl_le_lt_trans Hor); [ apply angle_eucl_dist_mul_le | ].
apply (rngl_lt_div_r Hon Hop Hiv Hor) in Hlim. 2: {
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
  now apply Nat.neq_0_lt_0.
}
now rewrite <- (rngl_mul_nat_comm Hon Hos) in Hlim.
Qed.

Theorem rngl_lt_cos_lt_cos_div2 :
  ∀ a b θ,
  (2 * b² ≤ a + 1)%L
  → (0 ≤ rngl_sin θ)%L
  → (a < rngl_cos θ)%L
  → (b < rngl_cos (θ / ₂))%L.
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
apply (rngl_nlt_ge Hor) in Hbgz.
rewrite <- (rngl_abs_nonneg_eq Hop Hor b); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_). 2: {
  apply rl_sqrt_nonneg.
  apply rngl_1_add_cos_div_2_nonneg.
}
apply (rngl_squ_lt_abs_lt Hop Hor Hii).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply rngl_1_add_cos_div_2_nonneg.
}
apply -> (rngl_lt_div_r Hon Hop Hiv Hor). 2: {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
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
  → (1 < b + rngl_cos (θ / ₂))%L.
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

Theorem angle_eucl_dist_div_2_0_lt :
  ∀ a b θ,
  (0 ≤ b)%L
  → ((a / 2)² + (1 - b² / 2)² ≤ 1)%L
  → (0 ≤ rngl_sin θ)%L
  → (angle_eucl_dist θ 0 < a)%L
  → (angle_eucl_dist (θ / ₂) 0 < b)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzb Hab Hzs Hd.
  rewrite (H1 (angle_eucl_dist _ _)) in Hd.
  rewrite (H1 a) in Hd.
  now apply (rngl_lt_irrefl Hor) in Hd.
}
assert (H2z : (2 ≠ 0)%L) by apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
intros * Hzb Hab Hzs Hd.
assert (Hza : (0 ≤ a)%L). {
  eapply (rngl_le_trans Hor). 2: {
    apply (rngl_lt_le_incl Hor) in Hd.
    apply Hd.
  }
  apply angle_eucl_dist_nonneg.
}
move Hza after Hzb.
rewrite angle_eucl_dist_is_sqrt.
rewrite angle_sub_0_l.
rewrite rngl_cos_opp.
rewrite angle_eucl_dist_is_sqrt in Hd.
rewrite angle_sub_0_l in Hd.
rewrite rngl_cos_opp in Hd.
rewrite <- (rngl_abs_nonneg_eq Hop Hor b); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_). 2: {
  apply rl_sqrt_nonneg.
  rewrite <- one_sub_squ_cos_add_squ_sin.
  apply (rngl_add_squ_nonneg Hop Hor).
}
apply (rngl_squ_lt_abs_lt Hop Hor Hii).
rewrite (rngl_squ_sqrt Hon). 2: {
  rewrite <- one_sub_squ_cos_add_squ_sin.
  apply (rngl_add_squ_nonneg Hop Hor).
}
rewrite (rngl_mul_comm Hic).
apply (rngl_lt_div_r Hon Hop Hiv Hor). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
apply (rngl_lt_sub_lt_add_r Hop Hor).
rewrite <- (rngl_abs_nonneg_eq Hop Hor a) in Hd; [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_) in Hd. 2: {
  apply rl_sqrt_nonneg.
  rewrite <- one_sub_squ_cos_add_squ_sin.
  apply (rngl_add_squ_nonneg Hop Hor).
}
apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid) in Hd.
rewrite (rngl_squ_sqrt Hon) in Hd. 2: {
  rewrite <- one_sub_squ_cos_add_squ_sin.
  apply (rngl_add_squ_nonneg Hop Hor).
}
rewrite (rngl_mul_comm Hic) in Hd.
apply (rngl_lt_div_r Hon Hop Hiv Hor) in Hd. 2: {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
apply (rngl_lt_sub_lt_add_r Hop Hor) in Hd.
apply (rngl_lt_add_cos_lt_add_cos_div2 (a² / 2))%L; [ | easy | easy ].
apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii _ _ 2). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_div Hi1); [ | easy ].
rewrite (rngl_div_sub_distr_r Hop Hiv).
rewrite (rngl_div_diag Hon Hiq); [ | easy ].
rewrite (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite <- (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
now apply (rngl_le_add_le_sub_l Hop Hor).
Qed.

Theorem angle_eucl_dist_div_2_pow_0_lt :
  ∀ n a b θ,
  (0 ≤ a ≤ b * 2^n)%L
  → ((a * 2 ^ n)² + (1 - b² / 2)² ≤ 1)%L
  → ((a * 2 ^ n)² ≤ rngl_of_nat 3)%L
  → (0 ≤ rngl_sin θ)%L
  → (angle_eucl_dist θ 0 < a)%L
  → (angle_eucl_dist (θ / ₂^n) 0 < b)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hab Hab2 Ha3 Hzs Hd.
  rewrite (H1 (angle_eucl_dist _ _)) in Hd.
  rewrite (H1 a) in Hd.
  now apply (rngl_lt_irrefl Hor) in Hd.
}
intros * Hab Hab2 Ha3 Hzs Hd.
revert a b θ Hd Hzs Hab Hab2 Ha3.
induction n; intros. {
  rewrite rngl_pow_0_r in Hab.
  rewrite (rngl_mul_1_r Hon) in Hab.
  cbn.
  eapply (rngl_lt_le_trans Hor); [ apply Hd | easy ].
}
rewrite angle_div_2_pow_succ_r_1.
apply (angle_eucl_dist_div_2_0_lt (a * 2^S n))%L. {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ (2 ^ S n)). {
    apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  now apply (rngl_le_trans Hor _ a).
} {
  rewrite rngl_pow_succ_r, (rngl_mul_comm Hic 2).
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_div Hi1); [ | apply (rngl_2_neq_0 Hon Hop Hc1 Hor) ].
  eapply (rngl_le_trans Hor); [ | apply Hab2 ].
  apply (rngl_add_le_mono_r Hop Hor).
  do 2 rewrite (rngl_squ_mul Hic).
  apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
    apply (rngl_squ_nonneg Hop Hor).
  }
  do 2 rewrite (rngl_pow_squ Hic Hon).
  apply (rngl_pow_le_mono_r Hop Hon Hor). {
    apply (rngl_le_add_l Hor).
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  apply Nat.mul_le_mono_l.
  apply Nat.le_succ_diag_r.
} {
  destruct n; [ easy | ].
  now apply rngl_sin_div_2_pow_nat_nonneg.
} {
  apply (IHn a); [ easy | easy | | | ]; cycle 2.  {
    eapply (rngl_le_trans Hor); [ | apply Ha3 ].
    apply (rngl_abs_le_squ_le Hop Hor).
    do 2 rewrite (rngl_abs_mul Hop Hi1 Hor).
    apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
      apply (rngl_abs_nonneg Hop Hor).
    }
    rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
      apply (rngl_lt_le_incl Hor).
      apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
      apply (rngl_lt_le_incl Hor).
      apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    apply (rngl_pow_le_mono_r Hop Hon Hor); [ | apply Nat.le_succ_diag_r ].
    apply (rngl_le_add_l Hor).
    apply (rngl_0_le_1 Hon Hop Hor).
  } {
    split; [ easy | ].
    rewrite <- rngl_mul_assoc.
    rewrite <- (rngl_pow_add_r Hon).
    rewrite <- (rngl_mul_1_r Hon a) at 1.
    apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
    apply (rngl_pow_ge_1 Hop Hon Hor).
    apply (rngl_le_add_l Hor).
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  do 2 rewrite (rngl_squ_mul Hic).
  replace (2 ^ S n)²%L with (2 * 2 ^ S (2 * n))%L. 2: {
    rewrite <- rngl_pow_succ_r.
    rewrite (rngl_pow_squ Hic Hon 2 (S n)).
    f_equal; flia.
  }
  rewrite (rngl_mul_comm Hic 2).
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_div Hi1). 2: {
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_squ_sub Hop Hic Hon).
  rewrite (rngl_squ_1 Hon).
  rewrite (rngl_mul_1_r Hon).
  rewrite rngl_add_assoc.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_add_comm _ 1).
  rewrite <- (rngl_add_sub_swap Hop).
  apply (rngl_le_sub_le_add_r Hop Hor).
  rewrite <- rngl_add_assoc.
  apply (rngl_add_le_mono_l Hop Hor).
  apply (rngl_le_add_le_sub_l Hop Hor).
  rewrite (rngl_mul_comm Hic 2).
  rewrite <- rngl_mul_assoc.
  rewrite <- (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_squ_mul Hic).
  progress unfold rngl_squ at 1.
  rewrite <- rngl_mul_assoc.
  apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
    apply (rngl_squ_nonneg Hop Hor).
  }
  progress replace (2 ^ S (2 * n) * 2 - (2 ^ n)²)%L
  with (rngl_of_nat 3 * (2 ^ n)²)%L. 2: {
    progress unfold rngl_squ at 2.
    rewrite (rngl_mul_comm Hic _ 2).
    rewrite <- rngl_pow_succ_r.
    progress replace (S (S (2 * n))) with (n + (n + 2)) by flia.
    rewrite (rngl_pow_add_r Hon).
    rewrite <- (rngl_mul_sub_distr_l Hop).
    rewrite (rngl_pow_add_r Hon).
    rewrite <- (rngl_mul_1_r Hon (2 ^ n)) at 4.
    rewrite <- (rngl_mul_sub_distr_l Hop).
    rewrite rngl_mul_assoc.
    rewrite fold_rngl_squ.
    rewrite (rngl_mul_comm Hic).
    f_equal; cbn.
    rewrite rngl_mul_add_distr_r.
    rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_mul_1_r Hon).
    do 3 rewrite rngl_add_assoc.
    rewrite (rngl_add_sub Hos).
    now rewrite rngl_add_0_r.
  }
  progress replace (2 ^ S (2 * n))²%L with (2 ^ 2 * ((2 ^ n)²)²)%L. 2: {
    symmetry.
    progress unfold rngl_squ.
    rewrite rngl_mul_assoc.
    do 4 rewrite <- (rngl_pow_add_r Hon).
    f_equal; flia.
  }
  progress unfold rngl_squ at 2.
  do 2 rewrite rngl_mul_assoc.
  apply (rngl_mul_le_mono_nonneg_r Hop Hor). {
    apply (rngl_squ_nonneg Hop Hor).
  }
  rewrite <- rngl_mul_assoc.
  rewrite <- (rngl_squ_pow_2 Hon).
  rewrite <- (rngl_squ_mul Hic).
  rewrite <- rngl_pow_succ_r.
  rewrite <- (rngl_squ_mul Hic).
  easy.
}
Qed.

Theorem angle_sub_le_mono_l :
  ∀ θ2 θ3 θ1,
  angle_add_overflow θ3 (- θ1) = false
  → θ1 ≠ 0%A
  → (θ1 ≤ θ2)%A
  → (θ3 - θ2 ≤ θ3 - θ1)%A.
Proof.
intros * Hov H1z H12.
apply angle_add_le_mono_l; [ easy | ].
now apply angle_opp_le_compat_if.
Qed.

Theorem angle_mul_opp : ∀ n θ, (- (n * θ) = n * (- θ))%A.
Proof.
intros.
induction n; cbn; [ apply angle_opp_0 | ].
rewrite angle_opp_add_distr.
rewrite IHn.
apply angle_add_comm.
Qed.

(* to be completed
(* if a sequence of angles θi has a limit θ',
   and if ∀ i, n*θi does not overflow,
   then n*θ' does not overflow either *)
Theorem angle_seq_not_overflow_has_not_overflow_limit :
  ∀ n θ θ',
  (∀ i, angle_mul_nat_overflow n (θ i) = false)
  → angle_lim θ θ'
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
intros * Hi Hlim.
apply angle_all_add_not_overflow.
intros * Hmn.
assert (H : ∀ k, angle_lim (λ i, (k * θ i)%A) (k * θ')). {
  intros k.
  now apply (angle_lim_angle_lim_mul_mul).
}
move H before Hlim; clear Hlim; rename H into Hlim.
assert (H :
  ∀ k ε,
  (0 < ε)%L
  → ∃ N : nat, ∀ i, N ≤ i → (angle_eucl_dist (k * θ i) (k * θ') < ε)%L)
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
assert (Him : ∀ i, (θ i ≤ S m * θ i)%A) by now intros i; apply Hi.
move Him before Hi.
move m before n.
apply angle_nlt_ge.
intros Hmt.
move Hmt before Him; move m after n.
Print angle_lim.
(* not sure it is useful, but it seems to be true, so I'm trying
   to prove it as an exercise *)
(* it says that all terms of our sequence are less than the limit;
   but warning: it does not mean that the sequence is always
   increasing, it can oscillate *)
(* I have another idea: perhaps there is another sequence still converging
   to θ', but whose terms are always greater than θ' ? *)
Theorem glop :
  ∀ n i θ θ',
  angle_lim (seq_angle_to_div_nat θ n) θ'
  → (seq_angle_to_div_nat θ n i ≤ θ')%A.
Proof.
intros * Hlim.
progress unfold seq_angle_to_div_nat in Hlim.
progress unfold seq_angle_to_div_nat.
(*2*)
destruct (lt_dec (2 ^ i) n) as [Hin| Hin]. {
  rewrite Nat.div_small; [ | easy ].
  apply angle_nonneg.
}
apply Nat.nlt_ge in Hin.
destruct n; [ apply angle_nonneg | ].
destruct n. {
  rewrite Nat.div_1_r.
  rewrite angle_div_2_pow_mul_2_pow.
  apply (angle_lim_eq_compat 0 0 _ (λ i, θ)) in Hlim. 2: {
    intros j.
    rewrite Nat.add_0_r, Nat.div_1_r.
    apply angle_div_2_pow_mul_2_pow.
  }
  apply angle_lim_const in Hlim.
  subst θ'.
  apply angle_le_refl.
}
destruct n. {
  destruct i; [ cbn in Hin; flia Hin | ].
  rewrite Nat.pow_succ_r', Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
  eapply (angle_lim_eq_compat 1 0) in Hlim. 2: {
    intros j.
    rewrite Nat.add_1_r.
    rewrite Nat.pow_succ_r'.
    rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
    rewrite angle_div_2_pow_succ_r_2.
    rewrite angle_div_2_pow_mul_2_pow.
    now rewrite Nat.add_0_r.
  }
  apply angle_lim_const in Hlim.
  subst θ'.
  apply angle_le_refl.
}
destruct n. {
  specialize (Nat.div_mod (2 ^ i) 3 (Nat.neq_succ_0 _)) as H1.
  (* 2^i/n, c'est les i premières decimales binaires de 1/n *)
(* et si j'essayais ça, et après je l'applique avec n=3 *)
Theorem angle_mul_le_mono_l_iff :
  ∀ n θ1 θ2,
  n ≠ 0
  → angle_mul_nat_overflow n θ1 = false
  → angle_mul_nat_overflow n θ2 = false
  → (n * θ1 ≤ n * θ2)%A
  → (θ1 ≤ θ2)%A.
Proof.
intros * Hnz Hov1 Hov2 H12.
(*1*)
destruct (angle_eq_dec θ1 0) as [H1z| H1z]. {
  subst θ1.
  apply angle_nonneg.
}
...
apply (angle_sub_le_mono_l _ (n * θ2)) in H12.
3: {
  intros H1.
(*1*)
  clear θ2 Hov2 H12.
  apply H1z; clear H1z.
  revert θ1 Hov1 H1.
  induction n; intros; [ easy | clear Hnz ].
(*2*)
  cbn in H1.
  rewrite angle_add_comm in H1.
  cbn in Hov1.
  destruct n. {
    cbn in H1.
    now rewrite angle_add_0_l in H1.
  }
  specialize (IHn (Nat.neq_succ_0 _)).
  apply Bool.orb_false_iff in Hov1.
  destruct Hov1 as (Hov, Hmov).
...2
  cbn in Hov1.
  destruct n; [ now rewrite angle_mul_1_l in H1 | ].
  specialize (IHn (Nat.neq_succ_0 _)).
  apply Bool.orb_false_iff in Hov1.
  destruct Hov1 as (Hov, Hmov).
...1
  apply eq_angle_mul_0 in H1.
  destruct H1 as [H1| (Hc, Hs)]; [ easy | ].
...
2: {
  rewrite angle_mul_opp.
Search (angle_add_overflow (_ * _) (_ * _)).
...1
intros * Hnz Hov H12.
induction n; [ easy | clear Hnz ].
(*
Search (_ + _ ≤ _ + _)%A.
(* mmm... soit je démontre _+_≤_+_ → _≤_, soit j'écris sous la
   forme 0≤θ2-θ1... faut réfléchir *)
*)
destruct n. {
  cbn in H12.
  now do 2 rewrite angle_add_0_r in H12.
}
destruct n. {
  clear IHn. (* useless *)
Check angle_mul_le_mono_l.
...
Check angle_add_le_mono_l.
  apply (angle_add_le_mono_r _ _ (- θ1))%A in H12.
...
Search (_ + _ ≤ _ + _)%A.
...
Check angle_mul_le_mono_l.
apply (angle_mul_le_mono_l_iff 3).
Search (angle_mul_nat_overflow _ _ = false).
Search (_ * _ ≤ _ * _)%A.
(* Ah oui, mais il faudrait démontrer angle_lim_seq_angle_not_mul_overflow.
   Il y a un début loin ci-dessous mais pas fini *)
...
(* il me semble que si on fait 2^i/n + 1 à la place de 2^i/n, ça
   converge aussi par valeurs supérieures, mais le test avec des
   entiers au lieu d'angles n'a pas l'air de confirmer;
   donc faut voir: mais avec des entiers relatifs avec lesquels on
   peut monter beaucoup plus haut pour θ, ça marche peut-être *)
(* bon, du coup, j'essaie de voir si la suite avec 2^i/n + 1,
   est bien, comme je le pense, toujours supérieure à sa limite *)
(* donc essai du même théorème, mais avec ça *)
(* (et il faudra que je prouve que c'est bien une suite de Cauchy *)
Theorem glop :
  rngl_is_archimedean T = true →
  ∀ n i θ θ',
  angle_lim (λ i, ((2 ^ i / n + 1) * (θ / ₂^i))%A) θ'
  → (θ' ≤ (2 ^ i / n + 1) * (θ / ₂^i))%A.
Proof.
destruct_ac.
intros Har.
intros * Hlim.
destruct (lt_dec (2 ^ i) n) as [Hin| Hin]. {
  rewrite Nat.div_small; [ | easy ].
  rewrite Nat.add_0_l, angle_mul_1_l.
  eapply (angle_lim_eq_compat 0 0) in Hlim. 2: {
    intros j.
    rewrite Nat.add_0_r.
    rewrite angle_mul_add_distr_r.
    rewrite angle_mul_1_l.
    rewrite angle_add_comm.
    easy.
  }
  rewrite <- (angle_add_0_l θ') in Hlim.
  apply angle_lim_add_add_if in Hlim. 2: {
    intros ε Hε.
    specialize (rngl_archimedean Har Hor) as H1.
    specialize (H1 ε (angle_eucl_dist (θ / ₂^i) 0) Hε).
    destruct H1 as (N, HN).
    rewrite (rngl_mul_nat_mul_nat_1 Hon Hos) in HN.
    exists (N + i).
    intros m Hm.
    remember (m - (N + i)) as p eqn:Hp.
    assert (H : m = i + (p + N)) by flia Hm Hp.
    subst m.
    clear Hm Hp.
    apply (angle_eucl_dist_div_2_pow_0_lt _ (ε * rngl_of_nat N * 2 ^ i)%L).
(* bof, c'est compliqué *)
...
Search (_ / _ = _ → _)%L.
...
Check rngl_lt_add_cos_lt_add_cos_div2.
Search (_ < _ / _)%L.
...
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_1_r Hon).
Check rngl_lt_add_cos_lt_add_cos_div2.
...
(* previous version *)
Theorem angle_eucl_dist_div_2_0_lt :
  ∀ a θ,
  (angle_eucl_dist θ 0 < a * 2)%L
  → (angle_eucl_dist (θ / ₂) 0 < a)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hd.
  rewrite (H1 (angle_eucl_dist _ _)) in Hd.
  rewrite (H1 (_ * _)%L) in Hd.
  now apply (rngl_lt_irrefl Hor) in Hd.
}
intros * Hd.
rewrite angle_eucl_dist_is_sqrt.
rewrite angle_sub_0_l.
rewrite rngl_cos_opp.
(*1*)
cbn.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  rewrite (rngl_mul_1_l Hon).
...1
rewrite angle_eucl_dist_is_sqrt in Hd.
rewrite angle_sub_0_l in Hd.
rewrite rngl_cos_opp in Hd.
apply (rngl_mul_lt_mono_pos_r Hop Hor Hii 2%L). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
eapply (rngl_le_lt_trans Hor); [ | apply Hd ].
Search (1 - rngl_cos _)%L.
Search (1 - rngl_cos (_ / ₂))%L.
Search (rngl_cos (_ / ₂))%L.
cbn.
rewrite rngl_cos_div_2.
...
progress unfold angle_eucl_dist.
...
Search (_ / ₂^(_ + _))%A.
...
(* un truc comme ça : *)
Theorem glop :
  angle_eucl_dist (θ / ₂^n) 0 ≤ 2 ^ n * angle_eucl_dist θ 0.
...
  angle_eucl_dist (θ / ₂^n) 0 ≤ angle_eucl_dist θ 0.
...
    set (ε' := (ε / rngl_of_nat n)%L).
    specialize (H1 ε' (angle_eucl_dist (θ / ₂^i) 0)).
    assert (H : (0 < ε')%L) by ...
    specialize (H1 H); clear H.
    destruct H1 as (N, HN).
    rewrite (rngl_mul_nat_mul_nat_1 Hon Hos) in HN.
    subst ε'.
(* peut-être qu'il faut que je reparte de Hlim, en le décalant
   avec angle_lim_eq_compat et en faisant intervenir n et N d'une
   manière ou d'une autre *)
...
    specialize (H1 ε (angle_eucl_dist (θ / ₂^i) 0) Hε).
    destruct H1 as (m, Hm).
....
Search (rngl_mul_nat (_ / _)).
progress unfold rngl_mul_nat in H1.
Search mul_nat.
About rngl_mul_nat.
...
    set (ε' := rngl_mul_nat ε m) in Hm.
...
    exists i.
    intros j Hij.
(* ah, chais pas, faut voir *)
...
Search rngl_is_archimedean.
angle_div_nat_is_inf_sum_of_angle_div_2_pow:
  ∀ (T : Type) (ro : ring_like_op T) (rp : ring_like_prop T) 
    (rl : real_like_prop T) (ac : angle_ctx T),
    rngl_is_archimedean T = true
    → rngl_characteristic T = 0
      → ∀ (n : nat) (θ : angle T),
          n ≠ 0
          → angle_mul_nat_overflow n θ = false
            → angle_lim (seq_angle_to_div_nat (n * θ) n) θ
...
Search (angle_lim (angle_div_2_pow _)).
Search (angle_lim _ 0).
...
    rewrite Nat.div_small; [ | ].
    apply angle_div_2_pow_mul_2_pow.
...
(* ça, c'est le test que la suite avec 2^i/n + 1 est bien
   toujours supérieure à sa limite; ça a l'air d'être vrai
   pour une simulation avec un θ assez grand, mais faut voir *)
Compute (map (λ n,
let m := Z.of_nat n in
let θ := 500000000000%Z in
pair (θ / m)%Z (
  map (λ i,
let j := Z.of_nat i in
(**)
Z.leb (
(**)
  ((2 ^ j / m + 1) * (θ / 2 ^ j))%Z
(**)
) (θ / m)
(**)
) (seq 0 20)
)
) (seq 3 20)).
...
Compute (map (λ i,
   2 ^ i / 3
) (seq 0 12)).
...
  destruct i; [ cbn in Hin; flia Hin | ].
  destruct i; [ cbn in Hin; flia Hin | clear Hin ].
  specialize (Nat.div_mod (2 ^ S (S i)) 3 (Nat.neq_succ_0 _)) as H1.
...2
(*1*)
revert n θ θ' Hlim.
induction i; intros. {
  cbn.
  destruct n; [ apply angle_nonneg | ].
  destruct n. {
    rewrite Nat.div_1_r.
    rewrite angle_mul_1_l.
    apply (angle_lim_eq_compat 0 0 _ (λ i, θ)) in Hlim. 2: {
      intros j.
      rewrite Nat.add_0_r, Nat.div_1_r.
      apply angle_div_2_pow_mul_2_pow.
    }
    apply angle_lim_const in Hlim.
    subst θ'.
    apply angle_le_refl.
  }
  rewrite Nat.div_small; [ | flia ].
  apply angle_nonneg.
}
Search (_ * _ ≤ _)%A.
apply angle_div_2_pow_mul_le_angle.
rewrite Nat.pow_succ_r'.
...1
revert i θ θ' Hlim.
induction n; intros; [ apply angle_nonneg | ].
destruct n. {
  rewrite Nat.div_1_r.
  rewrite angle_div_2_pow_mul_2_pow.
  apply (angle_lim_eq_compat 0 0 _ (λ i, θ)) in Hlim. 2: {
    intros j.
    rewrite Nat.add_0_r, Nat.div_1_r.
    apply angle_div_2_pow_mul_2_pow.
  }
  apply angle_lim_const in Hlim.
  subst θ'.
  apply angle_le_refl.
}
eapply angle_le_trans.
apply angle_mul_div_succ_succ_le.
apply IHn.
(* chiasse *)
...
assert (H : ∀ i : nat, False). {
  intros.
  specialize (Hi i _ Hmn) as H1.
  move Hmt before H1.
  destruct (angle_lt_dec θ' (θ i)) as [Hθθ| Hθθ]. {
    assert (Hddd :
      (angle_eucl_dist (S m * θ') (S m * θ i) ≤
         angle_eucl_dist (S m * θ') θ' +
         angle_eucl_dist θ' (θ i) +
         angle_eucl_dist (θ i) (S m * θ i))%L). {
      eapply (rngl_le_trans Hor). {
        apply (angle_eucl_dist_triangular _ (θ i)).
      }
      apply (rngl_add_le_mono_r Hop Hor).
      apply angle_eucl_dist_triangular.
    }
    move Hθθ after H1.
    set (ε := (angle_eucl_dist θ' (θ i) / rngl_of_nat 4)%L).
...
  assert (Hdd : ∀ i : nat, ∃ ε : T, ∃ N, ∀ j, N < j → False). {
    intros.
    set (ε := (angle_eucl_dist θ' (θ m) / rngl_of_nat 4)%L).
    exists ε.
    specialize (Hlim (S m) ε) as H2.
    assert (Hε : (0 < ε)%L) by admit.
    specialize (H2 Hε).
    destruct H2 as (N, H2).
    specialize (H2 (S N) (Nat.le_succ_diag_r _)).
    rewrite angle_eucl_dist_symmetry in H2.
    exists (max N (S m)).
    intros j Hj.
(* ouais, bon, chais pas, ça a l'air d'être du n'importe quoi, de toutes
   façons *)
...

  assert (Hdd : ∀ i : nat, False). {
    intros.
    set (ε := (angle_eucl_dist θ' (θ i) / rngl_of_nat 4)%L).
    specialize (Hddd i) as H2.
specialize (Hlim (S m) ε) as H3.
...
...
  set (ε := (angle_eucl_dist θ' (θ m) / rngl_of_nat 4)%L).
  specialize (angle_eucl_dist_triangular θ' (S m * θ') (θ m)) as H2.
  specialize (angle_eucl_dist_triangular (S m * θ') (S m * θ m) (θ m)) as H3.
...
specialize (angle_eucl_dist_mul_le (S m) (θ' - θ (S m))) as H1.
rewrite angle_mul_sub_distr_l in H1.
do 2 rewrite <- angle_eucl_dist_move_0_l in H1.
specialize (angle_eucl_dist_triangular (θ (S m)) (S m * θ (S m)) θ') as H2.
specialize (angle_eucl_dist_triangular (S m * θ (S m)) (S m * θ') θ') as
  H3.
remember (angle_eucl_dist (S m * θ (S m)) (S m * θ')) as a eqn:Ha.
remember (angle_eucl_dist (θ (S m)) θ') as b eqn:Hb.
remember (angle_eucl_dist (S m * θ (S m)) θ') as c eqn:Hc.
remember (angle_eucl_dist (θ (S m)) (S m * θ (S m))) as d eqn:Hd.
remember (angle_eucl_dist (S m * θ') θ') as e eqn:He.
move H2 before H3.
move H1 before H2.
assert (H : (a ≤ rngl_of_nat (S m) * (b + a + e))%L).
(* aucun intérêt *)
...
apply (rngl_nlt_ge Hor) in H3.
apply H3; clear H3.
apply (rngl_add_lt_mono_l Hop Hor _ _ d).
eapply (rngl_lt_le_trans Hor); [ | apply H2 ].
  apply <- (rngl_add_lt_mono_l).
  apply H2.
}
...
apply (rngl_nlt_ge Hor) in H1.
apply H1; clear H1.
specialize (angle_eucl_dist_triangular (θ m) (S m * θ m) θ') as H1.
apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ (rngl_of_nat (S m))) in H1. 2: {
  rewrite <- rngl_of_nat_0.
  now apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
}
eapply (rngl_le_lt_trans Hor); [ apply H1 | clear H1 ].
specialize (angle_eucl_dist_triangular (S m * θ m) (S m * θ') θ') as H1.
eapply (rngl_lt_le_trans Hor). 2: {
  apply (rngl_le_sub_le_add_r Hop Hor) in H1.
  apply H1.
}
apply (rngl_lt_add_lt_sub_l Hop Hor).
remember (angle_eucl_dist (S m * θ m) θ') as x eqn:Hx.
(* ah oui mais non, je dis des conneries *)
...
specialize angle_eucl_dist_triangular as H1.
(* voir sur papier *)
set (ε₁ := angle_eucl_dist θ' (S m * θ')).
(**)
assert (Hε₁z : (0 < ε₁)%L). {
  progress unfold ε₁.
  apply (rngl_lt_iff Hor).
  split; [ apply angle_eucl_dist_nonneg | ].
  apply not_eq_sym.
  intros H.
  apply angle_eucl_dist_separation in H.
  rewrite <- H in Hmt.
  now apply angle_lt_irrefl in Hmt.
}
specialize (Hlim n ε₁ Hε₁z) as H2.
destruct H2 as (N, H2).
(* for all i≥N
   by triangular
     d (S m * θ i, S m * θ') ≤
       d (S m * θ i, θ i) + d (θ i, θ') + d (θ', S m * θ')
   by definition ε₁
     d (S m * θ i, S m * θ') ≤ d (S m * θ i, θ i) + d (θ i, θ') + ε₁
   by H2
     d (S m * θ i, S m * θ') ≤ d (S m * θ i, θ i) + ε₁ + ε₁ *)
(*
   by angle_eucl_dist_mul_mul_le
     S m * (d (θ i, 0) + d (θ', 0)) ≤ d (S m * θ i, θ i) + ε₁ + ε₁ *)
(* euh, en fait, non, l'inégalité est dans l'autre sens *)
(* voir sur papier *)
Inspect 4.
set (ε := angle_eucl_dist (θ N) (S m * θ')).
specialize (H2 N (Nat.le_refl _)) as H3.
(* by triangular
     d (S m * θ', θ') ≤ d (S m * θ', θ N) + d (θ N, θ')
   by H3
     d (S m * θ', θ') ≤ d (S m * θ', θ N) + d (S m * θ', θ')
   donc
     d (S m * θ', θ') ≤ d (S m * θ', θ N) + d (S m * θ', θ')
   donc
     0 ≤ d (S m * θ', θ N)
bon chais pas
*)
...

Theorem angle_add_overflow_pow2_div_mul_pow2_mul :
  ∀ m n i θ,
  m < n ≤ 2 ^ i
  → angle_add_overflow
      (seq_angle_to_div_nat θ n i)
      (m * seq_angle_to_div_nat θ n i) =
      false.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  progress unfold seq_angle_to_div_nat.
  rewrite (H1 (_ * _)%A).
  apply angle_add_overflow_0_l.
}
intros * (Hmi, Hni).
assert (Hnz : n ≠ 0) by flia Hmi.
(**)
remember (θ <? angle_straight)%A as ts eqn:Hts.
symmetry in Hts.
destruct ts. {
  now apply angle_add_overflow_pow2_div_mul_pow2_mul_when_lt_straight.
}
apply angle_ltb_ge in Hts.
(**)
progress unfold seq_angle_to_div_nat.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n.
  apply Nat.lt_1_r in Hmi; subst m.
  rewrite angle_mul_0_l.
  apply angle_add_overflow_0_r.
}
move Hn1 before Hnz.
remember (2 ^ i / n * (θ / ₂^i))%A as θ' eqn:Hθ'.
assert (Hts' : (θ' ≤ angle_straight / ₂^(Nat.log2 n - 1))%A). {
  subst θ'.
  now apply seq_angle_to_div_nat_le_straight_div_pow2_log2_pred.
}
assert (Hts'' : (θ' < angle_straight)%A). {
  rewrite Hθ'.
  destruct n; [ easy | clear Hnz ].
  destruct i. {
    cbn in Hni.
    apply Nat.succ_le_mono in Hni.
    now apply Nat.le_0_r in Hni; subst n.
  }
  apply (angle_div_2_pow_succ_mul_lt_straight Hc1).
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_le_mono_r.
  apply -> Nat.succ_le_mono.
  destruct n; [ easy | ].
  now apply -> Nat.succ_le_mono.
}
assert (Hts''' : (θ' / ₂ ≤ angle_straight / ₂^Nat.log2 n)%A). {
  subst θ'.
  now apply seq_angle_to_div_nat_div_2_le_straight_div_pow2_log2.
}
apply angle_add_not_overflow_equiv.
progress unfold angle_add_not_overflow2.
split. {
(*
  specialize seq_angle_to_div_nat_le_straight_div_pow2_log2_pred as H1.
  specialize (H1 n i (m * θ)%A Hn1).
  progress unfold seq_angle_to_div_nat in H1.
  specialize (angle_le_pow2_pred (S n) (m * θ')%A) as H2.
  rewrite Nat_sub_succ_1 in H2.
  generalize Hts'; intros H.
  specialize (angle_mul_le_mono_r m (S n)) as H1.
  specialize (H1 θ').
Search (_ * _ ≤ _ * _)%A.
*)
  eapply angle_le_trans. {
    apply angle_add_le_mono_r; cycle 2. {
      apply Hts'''.
    } {
      apply angle_add_overflow_div_2_div_2.
    }
    remember (Nat.log2 n) as p eqn:Hp.
    symmetry in Hp.
    destruct p. {
      apply Nat.log2_null in Hp.
      flia Hnz Hn1 Hp.
    }
    cbn.
    apply angle_add_overflow_div_2_div_2.
  }
...
  specialize (H1 θ' (Nat.neq_succ_0 _)).
...
apply angle_add_not_overflow_equiv3.
progress unfold angle_add_not_overflow3.
...
progress unfold angle_add_overflow.
apply angle_ltb_ge.
...
Theorem angle_mul_nat_not_overflow_mul_comm :
  ∀ m n θ,
  angle_mul_nat_overflow m (n * θ) = false
  → angle_mul_nat_overflow n (m * θ) = false.
Proof.
intros * Haov.
apply Bool.not_true_iff_false in Haov.
apply Bool.not_true_iff_false.
intros H; apply Haov; clear Haov.
apply angle_mul_nat_overflow_true_assoc in H.
Search (angle_mul_nat_overflow (_ * _)).
...
angle_mul_nat_overflow_true_assoc:
  ∀ (T : Type) (ro : ring_like_op T) (rp : ring_like_prop T),
    angle_ctx T
    → ∀ (m n : nat) (θ : angle T),
        angle_mul_nat_overflow m (n * θ) = true
        → angle_mul_nat_overflow (m * n) θ = true
Search angle_mul_nat_overflow.
apply angle_mul_nat_not_overflow_le_l.
... ...
apply angle_mul_nat_overflow_mul_comm.
apply angle_mul_nat_overflow_pow2_div_angle_mul.
}
...
  rewrite angle_mul_nat_div_2. 2: {
Search (angle_mul_nat_overflow _ (_ * _)).
apply angle_mul_nat_overflow_true_assoc.
...
    apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)); [ easy | ].
      apply Nat.div_le_upper_bound; [ easy | ].
      (* lemma *)
      rewrite Nat.mul_comm.
      apply Nat_mul_le_pos_r.
      destruct n; [ easy | ].
      now apply -> Nat.succ_le_mono.
    }
...
  eapply angle_le_trans; [ | apply angle_lt_le_incl, Hts' ].
  rewrite Hθ'.
  rewrite angle_mul_nat_assoc.
  rewrite Nat.mul_comm.
  rewrite <- angle_mul_nat_assoc.
...
  apply angle_mul_le_mono_l. 2: {
    apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). {
      apply Nat.div_le_upper_bound; [ easy | ].
      (* lemma *)
      rewrite Nat.mul_comm.
      apply Nat_mul_le_pos_r.
      destruct n; [ easy | ].
      now apply -> Nat.succ_le_mono.
    }
    apply angle_mul_nat_overflow_pow_div.
  }
...
Search (_ * (_ / ₂^_))%A.
  rewrite angle_div_2_pow_succ_r_1.
Search (_ * (_ / ₂))%A.
rewrite angle_mul_nat_div_2.
rewrite <- angle_div_2_pow_mul.
...
  eapply angle_le_trans. {
    rewrite angle_div_2_pow_succ_r_1.
    rewrite <- angle_div_2_pow_1.
    apply angle_div_2_pow_mul_le_angle.
  }
                           }
Search (_ * (_ / ₂^_) ≤ _)%A.
angle_div_2_pow_mul_le_angle: ∀ (n i : nat) (θ : angle T), n ≤ 2 ^ i → (n * (θ / ₂^i) ≤ θ)%A
...
    apply angle_div_mul_le.

  apply angle_le_trans with (θ2 := (θ / ₂^i)%A). 2: {
...
    apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i / 2 ^ Nat.log2 n)). {
      apply Nat.div_le_upper_bound; [ easy | ].
      rewrite Nat.mul_comm.
Search (2 ^ Nat.log2 _).
...
      apply Nat_mul_le_pos_r.
    apply angle_mul_nat_overflow_pow_div.
  }
...
  apply angle_le_trans with (θ2 := (θ / ₂^i)%A). 2: {
  eapply angle_le_trans. 2: {
...
    rewrite angle_div_2_pow_succ_r_2.
    now apply angle_div_2_pow_mul_le_angle.
  }
(* ah bin non *)
...
  rewrite angle_div_2_pow_succ_r_1.
  rewrite <- angle_div_2_pow_mul. 2: {
...
Search (angle_mul_nat_overflow (_ / _)).
Search (angle_mul_nat_overflow _ _ = false).
Search ((_ * _) / ₂)%A.
...
apply angle_le_pow2_log2; [ easy | | ]. {
  (* lemma *)
  apply Bool.not_true_iff_false.
  intros H.
  apply angle_mul_nat_overflow_true_assoc in H.
  apply Bool.not_false_iff_true in H.
  apply H; clear H.
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). {
    now apply Nat.mul_div_le.
  }
  apply angle_mul_nat_overflow_pow_div.
}
rewrite <- Hθ'.
(* bah non *)
...
Search (_ / ₂^_ ≤ _ / ₂^_)%A.
Search (_ / ₂^_ < _ / ₂^_)%A.
...
Search (angle_mul_nat_overflow _ _ = false).
...
  apply (angle_mul_nat_overflow_le_r _ θ2).
...
apply glop.
...
(*
  destruct n; [ easy | clear Hnz ].
  destruct i. {
    cbn in Hni.
    apply Nat.succ_le_mono in Hni.
    now apply Nat.le_0_r in Hni; subst n.
  }
*)
About angle_div_2_pow_succ_mul_lt_straight.
Theorem angle_div_2_pow_mul_div_pow2_mul_pow2_log2 :
  ∀ n i θ, n ≤ 2 ^ i → (n * (θ / ₂^i) ≤ 2 ^ Nat.log2_up n * (θ / ₂^i))%A.
Proof.
intros * Hni.
destruct (le_dec n 1) as [Hn1| Hn1]. {
  destruct n; [ apply angle_nonneg | ].
  apply Nat.succ_le_mono, Nat.le_0_r in Hn1; subst n.
  do 2 rewrite angle_mul_1_l.
  apply angle_le_refl.
}
apply Nat.nle_gt in Hn1.
apply angle_mul_le_mono_r; [ | now apply Nat.log2_up_spec ].
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). 2: {
  apply angle_mul_nat_overflow_pow_div.
}
apply Nat.pow_le_mono_r; [ easy | ].
apply Nat.log2_up_le_mono in Hni.
now rewrite Nat.log2_up_pow2 in Hni.
Qed.
eapply angle_le_lt_trans.
apply angle_div_2_pow_mul_div_pow2_mul_pow2_log2. 2: {
Search (Nat.log2_up (_ / _)).
...
Check Nat_pow2_log2_eq.
Search (2 ^ Nat.log2_up _).
Search (_ < _ / ₂^_)%A.
  ============================
  (2 ^ S i / S n * (θ / ₂^S i) < angle_straight / ₂^Nat.log2_up (S n))%A
  ============================
  (2 ^ Nat.log2_up (2 ^ S i / S n) * (θ / ₂^S i) < angle_straight / ₂^Nat.log2_up (S n))%A
...
  specialize Nat_pow2_log2_eq as H1.
  specialize (H1 n).
  rewrite (proj1 H1).
  specialize (proj1 H1) as H2.
rewrite H2.
...
Check (Nat.log2_up_succ_or n).
  remember (2 ^ S i / S n) as p eqn:Hp.
Check Nat_pow2_log2_eq.
  destruct (Nat.eq_dec (2 ^ Nat.log2_up
...
  apply (f_equal (λ i, 2 ^ i)) in H1.
  rewrite Nat.pow_succ_r' in H1.
  rewrite Hn in H1.
Search (2 ^ Nat.log2_up _).
specialize (Nat.log2_log2_up_spec n Hnz) as H2.
rewrite <- H1 in H2.
rewrite Hn in H2.
...
Search (S (Nat.log2 _)).
...
specialize (Nat.le_log2_up_succ_log2 n) as H2.
apply Nat.le_antisymm in H1.
...
Search Nat.log2_up.
specialize (Nat.log2_spec n) as H2.
specialize (Nat.log2_log2_up_spec n) as H2.
...
apply (f_equal (λ i, 2 ^ i)) in H1.
rewrite Nat.pow_succ_r' in H1.
rewrite Hn in H1.
Search (2 ^ Nat.log2_up _).
...
Search (S (Nat.log2 _)).
...
  specialize (Nat.log2_spec_alt n) as H2.
  rewrite Hn in H2.
  specialize (Nat.log2_lt_pow2 n) as H3.
  specialize (Nat.log2_log2_up_exact n) as H4.
  rewrite <- H1 in H4.
Check Nat.log2_up_pow2.
...
Compute (let n := 9 in (n = 2 ^ Nat.log2 n, Nat.log2_up (S n) = S (Nat.log2_up n))).
(* ouais, c'est juste *)
...
Search Nat.log2.
Nat.log2_log2_up_exact:
  ∀ a : nat, 0 < a → Nat.log2 a = Nat.log2_up a ↔ (∃ b : nat, a = 2 ^ b)
Nat.log2_lt_pow2: ∀ a b : nat, 0 < a → a < 2 ^ b ↔ Nat.log2 a < b
...
  specialize (Nat.log2_up_succ_or n) as H1.
  destruct H1 as [H1| H1]. {
    rewrite H1.
Search (2 ^ S (Nat.log2_up _)).
...
Search (2 ^ Nat.log2_up _).
Search (Nat.log2_up _).
  ∀ a : nat,
    Nat.log2_up (S a) = S (Nat.log2_up a) ∨ Nat.log2_up (S a) = Nat.log2_up a
...
angle_div_2_pow_succ_mul_lt_straight is not universe polymorphic
Arguments angle_div_2_pow_succ_mul_lt_straight _ (n i)%nat_scope
  θ%angle_scope _
angle_div_2_pow_succ_mul_lt_straight is opaque
Expands to: Constant RnglAlg.Work.a.angle_div_2_pow_succ_mul_lt_straight

..
  apply (angle_div_2_pow_succ_mul_lt_straight Hc1).
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_le_mono_r.
  apply -> Nat.succ_le_mono.
  destruct n; [ easy | ].
  now apply -> Nat.succ_le_mono.
...
apply angle_add_not_overflow_equiv3.
progress unfold angle_add_not_overflow3.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]; [ now subst m; left | ].
destruct m; [ easy | clear Hmz ].
destruct m. {
  right.
  rewrite angle_mul_1_l.
  apply (angle_lt_le_trans _ angle_straight); [ easy | ].
  rewrite <- angle_opp_straight.
  apply angle_opp_le_compat_if; [ | now apply angle_lt_le_incl ].
  intros H; move H at top; subst θ'.
  symmetry in Hθ'.
  apply angle_div_2_pow_mul_neq_0 in Hθ'; [ easy | | ]. {
    intros H; subst θ.
    apply angle_nlt_ge in Hts.
    apply Hts; clear Hts.
    apply (angle_straight_pos Hc1).
  }
  split. {
    apply Nat.div_str_pos.
    split; [ | easy ].
    now apply Nat.neq_0_lt_0.
  }
  apply Nat.div_lt; [ | easy ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
destruct m. {
  right.
...
apply angle_add_overflow_le with (θ2 := θ). 2: {
  rewrite <- (angle_div_2_pow_mul_2_pow i θ).
  rewrite Hθ'.
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
(* contre-exemple :
    θ = 3π/2 ; n = 2 ; i = 2 ; θ' = 4/2 * θ/4 = π/2
    θ' + θ = π/2+3π/2 = 2π
*)
...
apply angle_add_not_overflow_comm.
apply (angle_add_overflow_lt_le (- θ')). 2: {
  rewrite angle_opp_involutive.
  apply angle_le_refl.
}
rewrite <- (angle_opp_involutive θ).
apply angle_opp_lt_compat_if. {
  rewrite Hθ'.
  apply angle_div_2_pow_mul_neq_0. {
    intros H; subst θ.
    apply angle_nlt_ge in Hts.
    apply Hts, (angle_straight_pos Hc1).
  }
  split. {
    apply Nat.div_str_pos.
    split; [ now apply Nat.neq_0_lt_0 | easy ].
  }
  apply Nat.div_lt. {
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  now apply -> Nat.succ_lt_mono.
}
(* contre-exemple :
    θ = 3π/2 ; n = 2 ; i = 2 ; θ' = 4/2 * θ/4 = π/2 ; -θ = π/2
   exemple :
    θ = 3π/2 ; n = 4 ; i = 2 ; θ' = 4/4 * θ/4 = 3π/8 ; -θ = π/2
*)
...
apply (angle_lt_le_trans _ angle_straight); [ easy | ].
(* aïe aïe aïe aïe... *)
...
angle_div_2_pow_mul_neq_0: ∀ (n i : nat) (θ : angle T), θ ≠ 0%A → 0 < n < 2 ^ i → (n * (θ / ₂^i))%A ≠ 0%A
  intros H.
Search (_ * _ = 0)%A.
...
apply angle_add_overflow_lt_straight_le_straight; [ easy | ].
...
(**)
apply angle_add_not_overflow_comm.
apply angle_add_not_overflow_equiv3.
progress unfold angle_add_not_overflow3.
progress unfold seq_angle_to_div_nat.
progress unfold angle_ltb.
remember (2 ^ i / n * (θ / ₂^i))%A as θ' eqn:Hθ'.
cbn.
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
destruct (angle_eq_dec θ' 0) as [Htz| Htz]; [ now left | right ].
remember (0 ≤? rngl_sin (m * θ'))%L as zsm eqn:Hzsm.
remember (rngl_sin θ' ≤? 0)%L as sz eqn:Hsz.
symmetry in Hzsm, Hsz.
destruct zsm. {
  destruct sz; [ | easy ].
  apply rngl_leb_le in Hzsm, Hsz.
  apply rngl_ltb_lt.
  destruct m. {
    cbn.
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_cos_bound | ].
    intros H.
    now apply eq_rngl_cos_1 in H.
  }
  destruct i; [ cbn in Hni; flia Hmi Hni | ].
  enough (Hθ : (2 ^ S i / n * (θ / ₂^S i) < angle_straight)%A). {
    rewrite <- Hθ' in Hθ.
    apply (rngl_nlt_ge Hor) in Hsz.
    exfalso; apply Hsz; clear Hsz.
    apply (rngl_lt_iff Hor).
    split. {
      apply rngl_sin_nonneg_angle_le_straight.
      now apply angle_lt_le_incl in Hθ.
    }
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    move H at top.
    destruct H; [ easy | subst θ' ].
    now apply angle_lt_irrefl in Hθ.
  }
  apply (angle_div_2_pow_succ_mul_lt_straight Hc1).
  apply Nat.div_le_upper_bound; [ flia Hmi | ].
  destruct n; [ easy | ].
  destruct n; [ flia Hmi | ].
  cbn; flia.
}
apply (rngl_leb_gt Hor) in Hzsm.
destruct i. {
  cbn in Hni.
  apply Nat.le_1_r in Hni.
  destruct Hni; [ easy | subst n ].
  apply Nat.lt_1_r in Hmi; subst m.
  cbn in Hzsm.
  now apply (rngl_lt_irrefl Hor) in Hzsm.
}
destruct sz. {
  exfalso.
  apply rngl_leb_le in Hsz.
  apply (rngl_nlt_ge Hor) in Hsz.
  apply Hsz; clear Hsz.
  apply (rngl_lt_iff Hor).
  split. {
    apply rngl_sin_nonneg_angle_le_straight.
    rewrite Hθ'.
    apply angle_lt_le_incl.
    apply (angle_div_2_pow_succ_mul_lt_straight Hc1).
    apply Nat.div_le_upper_bound; [ flia Hmi | ].
    destruct n; [ easy | ].
    destruct n. {
      apply Nat.lt_1_r in Hmi; subst m.
      cbn in Hzsm.
      now apply (rngl_lt_irrefl Hor) in Hzsm.
    }
    rewrite Nat.pow_succ_r'.
    apply Nat.mul_le_mono_r.
    now do 2 apply -> Nat.succ_le_mono.
  }
  intros H; symmetry in H.
  apply eq_rngl_sin_0 in H.
  move H at top.
  destruct H; [ easy | subst θ' ].
  symmetry in Hθ'.
  enough (Hθ : (2 ^ S i / n * (θ / ₂^S i) < angle_straight)%A). {
    rewrite Hθ' in Hθ.
    now apply angle_lt_irrefl in Hθ.
  }
  apply (angle_div_2_pow_succ_mul_lt_straight Hc1).
  apply Nat.div_le_upper_bound; [ flia Hmi | ].
  destruct n; [ easy | ].
  destruct n. {
    apply Nat.lt_1_r in Hmi; subst m.
    cbn in Hzsm.
    now apply (rngl_lt_irrefl Hor) in Hzsm.
  }
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_le_mono_r.
  now do 2 apply -> Nat.succ_le_mono.
}
apply (rngl_leb_gt Hor) in Hsz.
apply rngl_ltb_lt.
apply (rngl_nle_gt Hor).
intros Hcc.
apply (rngl_nle_gt Hor) in Hzsm.
apply Hzsm; clear Hzsm.
destruct (le_dec (m * 2) n) as [Hmn| Hmn]. {
  rewrite Hθ'.
  rewrite angle_mul_nat_assoc.
  apply rngl_sin_nonneg_angle_le_straight.
  apply angle_lt_le_incl.
  apply (angle_div_2_pow_succ_mul_lt_straight Hc1).
  eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_assoc.
  now apply Nat.mul_le_mono_r.
}
apply Nat.nle_gt in Hmn.
Check angle_add_overflow_pow2_div_mul_pow2_mul_when_lt_straight.
...
destruct i. {
  exfalso.
  cbn in Hni.
  destruct n; [ easy | clear Hnz ].
  destruct n; [ now apply Nat.lt_1_r in Hmi; subst m | ].
  do 2 apply Nat.succ_le_mono in Hni.
  apply Nat.le_0_r in Hni; subst n.
  cbn in Hθ'.
  rewrite angle_add_0_r in Hθ'; subst θ'.
  destruct m; [ easy | ].
  apply Nat.succ_lt_mono in Hmi.
  apply Nat.lt_1_r in Hmi; subst m.
  now apply Nat.lt_irrefl in Hmn.
}
destruct i. {
  cbn in Hni.
  destruct n; [ easy | clear Hnz ].
  destruct n; [ now apply Nat.lt_1_r in Hmi; subst m | ].
  destruct n; [ flia Hmi Hmn | ].
  destruct n. {
    destruct m; [ flia Hmn | ].
    destruct m; [ flia Hmn | ].
    do 2 apply Nat.succ_lt_mono in Hmi.
    apply Nat.lt_1_r in Hmi; subst m.
    cbn - [ angle_div_2_pow ] in Hθ'.
    rewrite angle_add_0_r in Hθ'; subst θ'.
    rewrite angle_div_2_pow_succ_r_1.
    rewrite angle_div_2_mul_2.
    apply rngl_sin_div_2_nonneg.
  }
  do 4 apply Nat.succ_le_mono in Hni.
  apply Nat.le_0_r in Hni; subst n.
  cbn - [ angle_div_2_pow ] in Hθ'.
  rewrite angle_add_0_r in Hθ'; subst θ'.
  destruct m; [ flia Hmn | ].
  destruct m; [ flia Hmn | ].
  destruct m. {
    rewrite angle_div_2_pow_succ_r_1.
    rewrite angle_div_2_mul_2.
    apply rngl_sin_div_2_nonneg.
  }
  do 3 apply Nat.succ_lt_mono in Hmi.
  apply Nat.lt_1_r in Hmi; subst m.
  clear Hmn.
  exfalso.
  apply (rngl_nlt_ge Hor) in Hcc.
  apply Hcc; clear Hcc.
  apply (rngl_lt_le_trans Hor _ 0); [ | now apply rngl_cos_div_pow2_nonneg ].
  remember (θ / ₂^2)%A as θ' eqn:Hθ'.
  rewrite rngl_cos_nx.
  progress unfold iter_seq.
  rewrite Nat.sub_0_r.
  progress unfold iter_list.
  cbn - [ "-" "/" binomial ].
  rewrite rngl_add_0_l, rngl_add_0_r, rngl_add_0_r.
  rewrite Nat.sub_0_r.
  cbn - [ "-" "/" binomial ].
  do 3 rewrite (rngl_mul_1_r Hon).
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_same; [ | easy ].
  cbn - [ "/" binomial ].
  do 3 rewrite (rngl_mul_opp_l Hop).
  do 2 rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_1_r Hon).
  cbn.
  rewrite rngl_add_0_r.
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_mul_swap Hic).
  rewrite rngl_mul_assoc.
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  do 2 rewrite fold_rngl_squ.
  specialize (rngl_cos_div_pow2_2_nonneg θ) as Hzc.
  rewrite <- Hθ' in Hzc.
  (* lemma *)
  rewrite (rngl_mul_comm Hic).
  apply (rngl_mul_pos_neg Hop Hor Hid). {
    apply (rngl_lt_iff Hor).
    split; [ easy | ].
    intros H; symmetry in H.
    apply eq_rngl_cos_0 in H.
    move H at top.
    destruct H; subst θ'. {
      rewrite <- angle_straight_div_2 in Hθ'.
      apply angle_div_2_eq_compat in Hθ'.
      symmetry in Hθ'.
      now apply (angle_div_2_not_straight Hc1) in Hθ'.
    }
    apply (rngl_nle_gt Hor) in Hsz.
    apply Hsz; clear Hsz; cbn.
    apply (rngl_opp_1_le_0 Hon Hop Hor).
  }
  apply (rngl_lt_sub_0 Hop Hor).
  specialize (cos2_sin2_1 θ') as H1.
  apply (rngl_add_move_l Hop) in H1.
  rewrite H1.
  rewrite (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_1_r Hon).
  apply (rngl_lt_add_lt_sub_r Hop Hor).
  rewrite (rngl_add_mul_r_diag_r Hon).
Notation "3" := (1 + 2)%L : ring_like_scope.
Notation "4" := (1 + 3)%L : ring_like_scope.
Show.
  (* lemma *)
  rewrite (rngl_mul_comm Hic).
  apply (rngl_lt_div_r Hon Hop Hiv Hor). {
    apply (rngl_add_nonneg_pos Hor).
    apply (rngl_0_le_1 Hon Hop Hor).
    apply (rngl_add_nonneg_pos Hor).
    apply (rngl_0_le_1 Hon Hop Hor).
    apply (rngl_add_nonneg_pos Hor).
    apply (rngl_0_le_1 Hon Hop Hor).
    apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  }
  rewrite Hθ'.
Search (rngl_cos (_ / ₂)).
...
Search ((_ / ₂^_) = angle_right)%A.
Search (angle_right = (_ / ₂^_))%A.
...
Search (rngl_cos _ ≤ 0)%L.
...
destruct (rngl_le_dec Hor 0 (rngl_cos θ')) as [Hzc| Hcz]. {
...
  replace 3 with (1 + 2) by easy.
  rewrite angle_mul_add_distr_r.
  rewrite angle_mul_1_l.
  remember (2 * θ')%A as θ''; cbn; subst θ''.
  rewrite rngl_cos_mul_2_l, rngl_sin_mul_2_l. θ''. θ''.
  rewrite rngl_cos_mul_2_l, rngl_sin_mul_2_l θ''.
  rewrite rngl_cos_mul_2_l, rngl_sin_mul_2_l θ''.
  rewrite rngl_cos_mul_2_l, rngl_sin_mul_2_l
  rewrite rngl_cos_mul_2_l, rngl_sin_mul_2_l
  rewrite (rngl_mul_sub_distr_l Hop).
...
  cbn.
  rewrite (rngl_mul_0_r Hos), (rngl_sub_0_r Hos).
  rewrite (rngl_mul_0_r Hos), rngl_add_0_r.
  do 2 rewrite (rngl_mul_1_r Hon).
...
  remember (2 * θ')%A as θ''.
  cbn; subst θ''.
cbn.
Search (rngl_cos (3 * _)).
...
  cbn - [ angle_div_2_pow ].
...
Search (rngl_cos (_ / ₂^_)).
...
destruct i. {
  cbn in Hni.
  apply Nat.le_1_r in Hni.
  destruct Hni as [| Hni]; [ easy | subst n ].
  apply Nat.lt_1_r in Hmi; subst m; cbn.
  apply angle_add_overflow_0_r.
}
destruct i. {
  cbn in Hni.
  destruct n; [ easy | clear Hnz ].
  destruct n. {
    cbn.
    apply Nat.lt_1_r in Hmi; subst m; cbn.
    apply angle_add_overflow_0_r.
  }
  destruct n; [ | flia Hni ].
  destruct m; [ apply angle_add_overflow_0_r | ].
  destruct m; [ | flia Hmi ].
  cbn.
  do 2 rewrite angle_add_0_r.
  apply angle_add_overflow_div_2_div_2.
}
destruct i. {
  cbn in Hni.
  destruct n; [ easy | clear Hnz ].
  destruct n. {
    cbn.
    apply Nat.lt_1_r in Hmi; subst m; cbn.
    apply angle_add_overflow_0_r.
  }
  destruct n. {
    destruct m; [ apply angle_add_overflow_0_r | ].
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat ].
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    now do 2 apply Nat.succ_lt_mono in Hmi.
  }
  destruct n. {
    destruct m; [ apply angle_add_overflow_0_r | ].
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat ].
      rewrite angle_mul_1_l.
      apply angle_add_overflow_div_2_div_2.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat ].
      rewrite angle_mul_1_l.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    now do 3 apply Nat.succ_lt_mono in Hmi.
  }
  do 4 apply Nat.succ_le_mono in Hni.
  apply Nat.le_0_r in Hni; subst n.
  progress unfold seq_angle_to_div_nat.
  cbn - [ angle_mul_nat ].
  rewrite angle_mul_1_l.
  destruct m; [ apply angle_add_overflow_0_r | ].
  destruct m. {
    rewrite angle_mul_1_l.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct m. {
    rewrite angle_div_2_mul_2.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct m. {
    rewrite <- angle_div_2_pow_1.
    rewrite <- angle_div_2_pow_1.
    rewrite <- angle_div_2_pow_add_r.
    now apply angle_add_overflow_mul_div_pow2.
  }
  now do 4 apply Nat.succ_lt_mono in Hmi.
}
destruct n; [ easy | clear Hnz ].
destruct n. {
  apply Nat.lt_1_r in Hmi; subst m.
  apply angle_add_overflow_0_r.
}
destruct i. {
  destruct m; [ apply angle_add_overflow_0_r | ].
  apply Nat.succ_lt_mono in Hmi.
(**)
  cbn in Hni.
  do 2 apply Nat.succ_le_mono in Hni.
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_2.
      replace 4 with (2 ^ 2) by easy.
      rewrite angle_div_2_pow_mul_2_pow.
      apply angle_add_overflow_div_2_div_2.
    }
    now apply Nat.succ_lt_mono in Hmi.
  }
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    now do 2 apply Nat.succ_lt_mono in Hmi.
  }
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_mul_div_pow2; cbn.
      apply Nat.lt_succ_diag_r.
    }
    now do 3 apply Nat.succ_lt_mono in Hmi.
  }
(**)
  do 5 apply Nat.succ_le_mono in Hni.
  destruct m. {
    rewrite angle_mul_1_l.
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_pow2; cbn.
    now do 2 apply -> Nat.succ_lt_mono.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_pow2; cbn.
    now do 3 apply -> Nat.succ_lt_mono.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_pow2; cbn.
    now do 4 apply -> Nat.succ_lt_mono.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_pow2; cbn.
    now do 5 apply -> Nat.succ_lt_mono.
  }
  do 8 apply Nat.succ_lt_mono in Hmi.
  destruct n; [ easy | ].
  apply Nat.succ_lt_mono in Hmi.
  destruct n; [ easy | ].
  destruct n. {
    apply Nat.lt_1_r in Hmi; subst m.
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_pow2; cbn.
    now do 6 apply -> Nat.succ_lt_mono.
  }
  do 3 apply Nat.succ_le_mono in Hni.
  apply Nat.le_0_r in Hni; subst n.
  progress unfold seq_angle_to_div_nat.
  cbn - [ angle_mul_nat angle_div_2_pow ].
  rewrite angle_mul_1_l.
  apply angle_add_overflow_mul_div_pow2; cbn.
  now do 6 apply -> Nat.succ_lt_mono.
}
destruct i. {
  destruct m; [ apply angle_add_overflow_0_r | ].
  apply Nat.succ_lt_mono in Hmi.
(**)
  cbn in Hni.
  do 2 apply Nat.succ_le_mono in Hni.
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_2.
      replace 4 with (2 ^ 2) by easy.
      rewrite angle_div_2_pow_mul_2_pow.
      apply angle_add_overflow_div_2_div_2.
    }
    now apply Nat.succ_lt_mono in Hmi.
  }
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      rewrite angle_div_2_pow_succ_r_1.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_mul_nat_div_2; [ apply angle_add_overflow_div_2_div_2 | ].
      apply angle_mul_nat_overflow_div_pow2; cbn.
      now do 5 apply -> Nat.succ_le_mono.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
Check angle_add_overflow_lt_straight_le_straight.
About angle_add_overflow_lt_straight_le_straight.
...
apply (angle_add_overflow_lt_le angle_straight).
(* par exemple *)
(* ça pourrait être un lemme de
   angle_add_overflow_lt_straight_le_straight *)
...
      apply angle_add_overflow_lt_straight_le_straight. 2: {
rewrite angle_mul_nat_assoc.
apply angle_mul_div_pow2_le_straight.
cbn.
(* ouille aïe *)
Search (_ * _ < angle_straight)%A.
Search (_ * _ ≤ angle_straight)%A.
...
progress unfold angle_add_overflow.
apply angle_ltb_ge.
rewrite angle_add_mul_r_diag_r.
replace 5 with (2 * 2 + 1) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_mul_1_l.
rewrite <- angle_mul_nat_assoc.
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_div_2_mul_2.
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_div_2_mul_2.
do 2 rewrite <- angle_div_2_pow_succ_r_1.
rewrite angle_mul_add_distr_l.
replace 3 with (2 + 1) at 4 by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_mul_1_l.
rewrite angle_add_assoc.
apply angle_add_le_mono_r. {
  do 3 rewrite angle_div_2_pow_succ_r_1.
  apply angle_add_overflow_div_2_div_2.
} {
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  rewrite <- angle_add_assoc.
  apply angle_add_le_mono_l. {
...
Search (angle_add_overflow (_ * (_ / ₂^_))).
...
Search ((_ / ₂^_) + (_ / ₂^_))%A.
...
Check quadrant_3_angle_lt_5_angle_right_div_2.
Theorem quadrant_4_angle_lt_5_angle_right_div_2 :
...
      rewrite angle_mul_nat_assoc.
      rewrite Nat.mul_comm.
      rewrite <- angle_mul_nat_assoc.
      rewrite angle_div_2_pow_succ_r_1 at 2.
      rewrite angle_div_2_mul_2.
progress unfold angle_add_overflow.
apply angle_ltb_ge.
...
Search (angle_add_overflow (_ * (_ / ₂^_))).
...
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    now do 2 apply Nat.succ_lt_mono in Hmi.
  }
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_mul_div_pow2; cbn.
      apply Nat.lt_succ_diag_r.
    }
    now do 3 apply Nat.succ_lt_mono in Hmi.
  }
(**)
  do 5 apply Nat.succ_le_mono in Hni.
  destruct m. {
    rewrite angle_mul_1_l.
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_pow2; cbn.
    now do 2 apply -> Nat.succ_lt_mono.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_pow2; cbn.
    now do 3 apply -> Nat.succ_lt_mono.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_pow2; cbn.
    now do 4 apply -> Nat.succ_lt_mono.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_pow2; cbn.
    now do 5 apply -> Nat.succ_lt_mono.
  }
  do 8 apply Nat.succ_lt_mono in Hmi.
  destruct n; [ easy | ].
  apply Nat.succ_lt_mono in Hmi.
  destruct n; [ easy | ].
  destruct n. {
    apply Nat.lt_1_r in Hmi; subst m.
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_pow2; cbn.
    now do 6 apply -> Nat.succ_lt_mono.
  }
  do 3 apply Nat.succ_le_mono in Hni.
  apply Nat.le_0_r in Hni; subst n.
  progress unfold seq_angle_to_div_nat.
  cbn - [ angle_mul_nat angle_div_2_pow ].
  rewrite angle_mul_1_l.
  apply angle_add_overflow_mul_div_pow2; cbn.
  now do 6 apply -> Nat.succ_lt_mono.
}
...
specialize angle_add_overflow_pow2_div_mul_pow2_mul_when_lt_straight as H1.
specialize (H1 m n i (θ / ₂)%A).
assert (H : m < n ≤ 2 ^ i) by easy.
specialize (H1 H); clear H.
assert (H : (θ / ₂ < angle_straight)%A) by apply (angle_div_2_lt_straight Hc1).
specialize (H1 H); clear H.
progress unfold seq_angle_to_div_nat in H1.
progress unfold seq_angle_to_div_nat.
...
destruct m. {
  rewrite angle_mul_0_l.
  apply angle_add_overflow_0_r.
}
destruct m. {
  rewrite angle_mul_1_l.
  destruct i. {
    cbn in Hni.
    now apply Nat.nlt_ge in Hni.
  }
  specialize angle_div_2_pow_mul_le_angle as H1.
  specialize (H1 (2 ^ S i / n) i (θ / ₂)%A).
  assert (H : 2 ^ S i / n ≤ 2 ^ i). {
    destruct n; [ easy | ].
    destruct n; [ flia Hmi Hni | ].
    apply Nat.div_le_upper_bound; [ easy | ].
    rewrite Nat.pow_succ_r; [ | easy ].
    apply Nat.mul_le_mono_r.
    now do 2 apply -> Nat.succ_le_mono.
  }
  specialize (H1 H); clear H.
  rewrite <- angle_div_2_pow_succ_r_2 in H1.
  progress unfold seq_angle_to_div_nat.
  apply angle_add_overflow_diag. 2: {
    intros H.
    rewrite H in H1.
    apply angle_nlt_ge in H1.
    apply H1.
    now apply angle_div_2_lt_straight.
  }
  apply rngl_sin_nonneg_angle_le_straight.
  eapply angle_le_trans; [ apply H1 | ].
  apply angle_div_2_le_straight.
}
destruct m. {
  apply angle_add_not_overflow_equiv.
  progress unfold seq_angle_to_div_nat.
  split. {
    remember (2 ^ i / n * (θ / ₂^i))%A as θ' eqn:Hθ'.
    rewrite angle_mul_2_div_2.
    destruct (angle_lt_dec θ' angle_straight) as [Hts| Hts]. {
      rewrite Hts.
      rewrite <- (angle_div_2_mul_2 θ') at 2.
      rewrite angle_add_mul_r_diag_r.
      rewrite Hθ'.
      rewrite angle_mul_mul_div_2. 2: {
        apply angle_mul_nat_overflow_div_pow2.
        apply Nat.div_le_upper_bound; [ easy | ].
        destruct n; [ easy | cbn ].
        apply Nat.le_add_r.
      }
      rewrite <- angle_div_2_pow_succ_r_1.
      destruct (Nat.eq_dec n 3) as [Hn3| Hn3]. {
        subst n; clear Hnz Hmi.
        specialize (Nat.div_mod (2 ^ i) 3 (Nat.neq_succ_0 _)) as H1.
        symmetry in H1.
        apply Nat.add_sub_eq_r in H1.
        rewrite <- H1.
        rewrite angle_mul_sub_distr_r; [ | now apply Nat.mod_le ].
        rewrite angle_div_2_pow_succ_r_2 at 1.
        rewrite angle_div_2_pow_mul_2_pow.
        apply (angle_le_trans _ (θ / ₂)); [ | apply angle_div_2_le_straight ].
        apply angle_le_sub_diag.
        rewrite angle_div_2_pow_succ_r_1.
        rewrite angle_mul_nat_div_2. 2: {
          apply angle_mul_nat_overflow_div_pow2.
          now apply Nat.mod_le.
        }
        apply angle_div_2_le_compat.
        apply angle_div_2_pow_mul_le_angle.
        now apply Nat.mod_le.
      }
      assert (H : 3 < n) by flia Hmi Hn3.
      (* perhaps, the case n=3 above could be included here *)
      move H before Hmi; clear Hmi Hn3; rename H into H3n.
      apply angle_mul_div_pow2_le_straight.
      rewrite Nat.pow_succ_r'.
      apply Nat.mul_le_mono_l.
      eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
      apply Nat.div_le_upper_bound; [ easy | ].
      apply Nat.mul_le_mono_r.
      now apply Nat.lt_le_incl in H3n.
    }
    generalize Hts; intros H.
    apply Bool.not_true_iff_false in H.
    rewrite H; clear H.
    apply angle_nlt_ge in Hts.
    rewrite angle_add_assoc.
    apply angle_add_straight_r_le_straight.
    exfalso.
    apply angle_nlt_ge in Hts.
    apply Hts; clear Hts.
    subst θ'.
    destruct i; [ cbn in Hni; flia Hmi Hni | ].
    apply (angle_le_lt_trans _ (2 ^ i * (θ / ₂^S i)))%A. 2: {
      rewrite angle_div_2_pow_succ_r_2.
      rewrite angle_div_2_pow_mul_2_pow.
      apply (angle_div_2_lt_straight Hc1).
    }
    apply angle_mul_le_mono_r. {
      apply angle_mul_nat_overflow_div_pow2.
      apply Nat.pow_le_mono_r; [ easy | ].
      apply Nat.le_succ_diag_r.
    }
    apply Nat.div_le_upper_bound; [ easy | ].
    rewrite Nat.pow_succ_r'.
    apply Nat.mul_le_mono_r.
    now apply Nat.lt_le_incl in Hmi.
  } {
    destruct (angle_eq_dec θ 0) as [Htz| Htz]. {
      subst θ; left.
      rewrite angle_0_div_pow2.
      apply angle_mul_0_r.
    }
    right.
    rewrite angle_add_mul_r_diag_r.
    intros Htt.
    rewrite angle_mul_nat_assoc in Htt.
    revert Htt.
    apply angle_div_2_pow_mul_neq_0; [ easy | ].
    split. {
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.div_str_pos.
      split; [ | easy ].
      now apply Nat.neq_0_lt_0.
    }
    apply (le_lt_trans _ (3 * (2 ^ i / 3))). 2: {
      specialize (Nat.div_mod (2 ^ i) 3 (Nat.neq_succ_0 _)) as H1.
      symmetry in H1.
      apply Nat.add_sub_eq_r in H1.
      rewrite <- H1.
      apply Nat.sub_lt; [ now apply Nat.mod_le | ].
      apply Nat.neq_0_lt_0.
      clear Hni H1.
      induction i; [ easy | ].
      intros H; apply IHi; clear IHi.
      rewrite Nat.pow_succ_r' in H.
      apply Nat.mod_divide in H; [ | easy ].
      apply Nat.gauss in H; [ | easy ].
      now apply Nat.mod_divide.
    }
    apply Nat.mul_le_mono_l.
    apply Nat.div_le_compat_l.
    easy.
  }
}
destruct m. {
  apply angle_add_not_overflow_equiv.
  split. {
...
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. {
  apply rngl_sin_div_2_nonneg.
}
apply angle_mul_nat_overflow_div_pow2.
apply Nat.div_le_upper_bound; [ easy | ].
rewrite Nat.pow_succ_r'.
apply Nat.mul_le_mono_r.
now apply Nat.lt_le_incl in Hmi.
...
rewrite <- angle_mul_mul_div_2.
...
rewrite
  destruct n; [ easy | clear Hnz ].
  destruct n; [ flia Hmi | ].
  destruct n; [ flia Hmi | clear Hmi ].
  destruct n. {
    destruct i; [ apply (rngl_le_refl Hor) | ].
    destruct i; [ apply (rngl_le_refl Hor) | ].
    destruct i. {
      cbn - [ angle_mul_nat ].
      rewrite angle_mul_1_l.
      apply rngl_sin_div_2_nonneg.
    }
...
  apply rngl_leb_le.
  apply rngl_leb_le in Hzsa.
  apply (rngl_lt_eq_cases Hor); right.
...
  apply (angle_le_trans _ θ'); [ easy | ].
(**)
  progress unfold angle_leb.
  progress unfold angle_leb in Hts.
  cbn in Hts.
  rewrite (rngl_leb_refl Hor) in Hts.
...
  rewrite angle_add_comm.
  apply angle_le_add_r.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
Search (angle_add_overflow _ (_ / ₂)).
Search (2 * (_ / ₂))%A.
  rewrite <- (angle_div_2_mul_2 θ') at 1.
  apply angle_add_overflow_div_2_div_2.
...
      rewrite <- H1.
      apply Nat.sub_lt; [ now apply Nat.mod_le | ].
      apply Nat.neq_0_lt_0.
      clear Hni H1.
      induction i; [ easy | ].
      intros H; apply IHi; clear IHi.
      rewrite Nat.pow_succ_r' in H.
      apply Nat.mod_divide in H; [ | easy ].
      apply Nat.gauss in H; [ | easy ].
      now apply Nat.mod_divide.
...
destruct (Nat.eq_dec (Nat.gcd n 2) 0) as [Hn2| Hn2]. 2: {
  apply neq_pow2_3_mul_lemma.
  specialize (Nat.mod_upper_bound n 2 (Nat.neq_succ_0 _)) as H1.
  remember (n mod 2) as a.
  destruct a; [ easy | ].
  destruct a; [ easy | ].
  now do 2 apply Nat.succ_lt_mono in H1.
}
replace 3 with (2 + 1) by easy.
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_1_l.
intros Hmn.
symmetry in Hmn.
apply Nat.add_sub_eq_l in Hmn.
revert n Hn2 Hmn.
induction m; intros. {
  cbn - [ "*" ] in Hmn.
  now destruct n.
}
rewrite Nat.pow_succ_r' in Hmn.
rewrite <- Nat.mul_sub_distr_l in Hmn.
specialize (IHm n).
...
intros * Hmn.
(**)
revert m Hmn.
induction n; intros. {
  cbn in Hmn.
  now apply Nat.pow_nonzero in Hmn.
}
destruct m. {
  rewrite Nat.pow_0_r in Hmn.
  symmetry in Hmn.
  now apply Nat.eq_mul_1 in Hmn.
}
replace 3 with (2 + 1) in Hmn by easy.
rewrite Nat.mul_add_distr_r in Hmn.
rewrite Nat.mul_1_l in Hmn.
symmetry in Hmn.
apply Nat.add_sub_eq_l in Hmn.
rewrite Nat.pow_succ_r' in Hmn.
rewrite <- Nat.mul_sub_distr_l in Hmn.
...
  symmetry in Hc.
  revert c Hc.
  induction i; intros. {
    rewrite Nat.pow_0_r in Hc.
    now apply Nat.eq_mul_1 in Hc.
  }
  rewrite Nat.pow_succ_r' in Hc.
  replace 3 with (2 + 1) in Hc by easy.
  rewrite Nat.mul_add_distr_r in Hc.
  rewrite Nat.mul_1_l in Hc.
  apply Nat.add_sub_eq_l in Hc.
  rewrite <- Nat.mul_sub_distr_l in Hc.
... ...
  apply neq_pow2_3_mul in Hc.
...
(*
specialize (glop (3 * (2 ^ i / n)) i θ Htz) as H1.
rewrite Htt in H1.
*)
destruct (Nat.eq_dec n 3) as [Hn3| Hn3]. {
  subst n.
  clear Hnz Hmi.
...
  assert (H : 3 * (2 ^ i / 3) < 2 ^ i). {
    clear Hni H1 Htt.
    specialize (Nat.div_mod (2 ^ i) 3 (Nat.neq_succ_0 _)) as H1.
    symmetry in H1.
    apply Nat.add_sub_eq_r in H1.
    rewrite <- H1.
    apply Nat.sub_lt; [ now apply Nat.mod_le | ].
    apply Nat.neq_0_lt_0.
    intros H.
    apply Nat.mod_divides in H; [ | easy ].
    destruct H as (c, Hc).
...
  }
  specialize (H1 H); clear H.
...
Search (_ / _ < _).
    eapply Nat.le_lt_trans. {
      apply (Nat.div_mul_le _ _ _ Hnz).
    }
apply Nat.div_lt_upper_bound; [ easy | ].
...
    cbn - [ "/" ].
    do 2 rewrite Nat.add_0_r.
....
(* ouais, ça va pas forcément le faire, ça dépend de n mais
   "glop" peut se révéler utile *)
...
  eapply Nat.lt_le_trans. {
    apply (Nat.div_mul_le _ _ _ Hnz).
  }
  apply (Nat.div_lt_upper_bound _ _ _ Hnz).

apply Nat.mul_lt_mono_nonneg.
...
    specialize (Nat.div_mod (2 ^ i) n Hnz) as H1.
    symmetry in H1.
    apply Nat.add_sub_eq_r in H1.
...
    destruct n; [ easy | clear Hnz ].
    apply Nat.succ_lt_mono in Hmi.
    destruct n; [ easy | ].
    apply Nat.succ_lt_mono in Hmi.
    destruct n; [ easy | clear Hmi ].
    destruct n. {
      specialize (Nat.div_mod (2 ^ i) 3) as H1.
      specialize (H1 (Nat.neq_succ_0 _)).
      symmetry in H1.
      apply Nat.add_sub_eq_r in H1.
      rewrite <- H1 in Htt; clear H1.
      rewrite angle_mul_sub_distr_r in Htt; [ | now apply Nat.mod_le ].
      rewrite angle_div_2_pow_mul_2_pow in Htt.
      apply -> angle_sub_move_0_r in Htt.
..
      destruct i; [ cbn in Hni; flia Hni | ].
      destruct i; [ cbn in Hni; flia Hni | ].
      cbn - [ "/" "*" ] in Htt.
...
      apply eq_angle_mul_0 in Htt.
      destruct Htt as [Htt| Htt]. {
        apply Nat.eq_add_0 in Htt.
        destruct Htt as (H1, H2).
        apply Nat.div_small_iff in H1; [ | easy ].
        now apply Nat.nle_gt in H1.
      }
      destruct Htt as (H1, H2).
Search (rngl_cos (_ * _)).
Print rngl_cos_mul.
... ...
  }
  destruct (angle_lt_dec θ' angle_straight) as [Hts| Hts]. {
    rewrite Hts.
...
    apply eq_angle_mul_0 in Htt.
    destruct Htt as [| Htt]; [ easy | ].
    destruct Htt as (Hc, _).
    subst θ'.
    rewrite angle_mul_nat_assoc in Hc.
    rewrite rngl_cos_nx in Hc.
    cbn - [ "/" "-" binomial ] in Hc.
...
(**)
  destruct i. {
    cbn in Hni.
    flia Hmi Hni.
  }
  progress unfold seq_angle_to_div_nat.
  remember (2 ^ S i / n * (θ / ₂^S i))%A as θi eqn:Hi.
  remember (θi =? angle_straight)%A as is eqn:His.
  symmetry in His.
  destruct is. {
    apply (angle_eqb_eq Hed) in His.
    rewrite His.
    rewrite <- angle_add_diag.
    rewrite angle_straight_add_straight.
    apply angle_add_overflow_0_r.
  }
  apply (angle_eqb_neq Hed) in His.
  specialize angle_div_2_pow_mul_le_angle as H1.
  specialize (H1 (3 * (2 ^ S i / n)) (S i) θ).
  assert (H : 3 * (2 ^ S i / n) ≤ 2 ^ S i). {
    clear - Hmi.
    destruct n; [ flia Hmi | ].
    apply Nat.succ_lt_mono in Hmi.
    destruct n; [ flia Hmi | ].
    apply Nat.succ_lt_mono in Hmi.
    destruct n; [ now apply Nat.lt_irrefl in Hmi | clear Hmi ].
    remember (2 ^ S i) as j eqn:Hj.
    clear i Hj.
    eapply le_trans; [ | now apply (Nat.mul_div_le _ 3) ].
    apply Nat.mul_le_mono_l.
    apply Nat.div_le_compat_l.
    split; [ easy | ].
    now do 3 apply -> Nat.succ_le_mono.
  }
  specialize (H1 H); clear H.
  rewrite <- angle_mul_nat_assoc in H1.
  rewrite <- Hi in H1.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  rewrite angle_add_mul_r_diag_r.
  progress unfold angle_leb in H1.
  progress unfold angle_leb.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  remember (0 ≤? rngl_sin θi)%L as zsi eqn:Hzsi.
  remember (0 ≤? rngl_sin (3 * θi))%L as zsi3 eqn:Hzsi3.
  symmetry in Hzs, Hzsi, Hzsi3.
  move zsi before zs; move zsi3 before zsi.
  destruct zsi. {
    destruct zsi3; [ | easy ].
    apply rngl_leb_le in Hzsi3, Hzsi.
    apply rngl_leb_le.
    destruct zs. {
      apply rngl_leb_le in Hzs, H1.
      move Hzsi before Hzs.
      apply rngl_sin_sub_nonneg_if; [ now right | easy | easy | ].
      rewrite angle_sub_mul_l_diag_r; [ | easy ].
      cbn - [ rngl_sin angle_mul_nat ].
      apply (rngl_nlt_ge Hor).
      intros H2.
      apply (rngl_nlt_ge Hor) in H1.
      apply H1; clear H1.
      rename H2 into H1.
      assert (Hci : (rngl_cos θi ≤ 0)%L). {
        apply (rngl_nlt_ge Hor).
        intros H.
        apply (rngl_nle_gt Hor) in H1.
        apply H1; clear H1.
        rewrite rngl_sin_mul_2_l.
        apply (rngl_lt_le_incl Hor) in H.
        apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
        apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
        apply (rngl_0_le_2 Hon Hop Hor).
      }
      generalize H1; intros H.
      apply rngl_sin_mul_2_neg_if in H.
      destruct H as [(H2, H3)| H2]. {
...
      apply (rngl_nle_gt Hor).
      intros Hcc.
      assert (Hc2i : (0 ≤ rngl_cos (2 * θi))%L). {
        apply (rngl_nlt_ge Hor).
        intros H4.
        apply rngl_cos_mul_2_neg_if in H4.
        destruct H4 as [(H4, H5)| (H4, H5)]. {
...
apply (rngl_lt_0_sub Hop Hor).
specialize (rngl_cos_div_2 angle_right) as H1.
cbn - [ rngl_cos ] in H1.
specialize (rngl_0_le_1 Hon Hop Hor) as H2.
apply rngl_leb_le in H2.
...
...
(* pas sûr : par exemple si π/2 < θi < 3π/4
   oui, mais dans ce cas, sin(3*θi), peut-il être positif ? *)
rewrite rngl_sin_nx in Hzsi3.
progress unfold iter_seq in Hzsi3.
progress unfold iter_list in Hzsi3.
rewrite Nat.sub_0_r in Hzsi3.
cbn - [ "/" binomial "-" ] in Hzsi3.
do 2 rewrite rngl_add_0_l in Hzsi3.
rewrite rngl_add_0_r in Hzsi3.
rewrite Nat.div_small in Hzsi3; [ | easy ].
rewrite (Nat_div_less_small 1) in Hzsi3; [ | cbn; flia ].
rewrite (rngl_mul_1_r Hon) in Hzsi3.
cbn - [ "^" ] in Hzsi3.
rewrite (rngl_mul_1_l Hon) in Hzsi3.
do 2 rewrite (rngl_mul_1_r Hon) in Hzsi3.
rewrite rngl_add_0_r in Hzsi3.
rewrite (rngl_mul_1_r Hon) in Hzsi3.
rewrite (rngl_mul_opp_l Hop) in Hzsi3.
rewrite (rngl_mul_1_l Hon) in Hzsi3.
rewrite (rngl_add_opp_r Hop) in Hzsi3.
(* pfff, chais pas *)
...
        replace 3 with (2 + 1) in Hzsi3 by easy.
        rewrite angle_mul_add_distr_r in Hzsi3.
        rewrite angle_mul_1_l in Hzsi3.
        cbn - [ "*"%A ] in Hzsi3.
Search (rngl_sin (_ * _)).
        rewrite rngl_sin_mul_2_l in Hzsi3.
        rewrite rngl_cos_mul_2_l in Hzsi3.
...
        rewrite rngl_cos_mul_2_l'.
...
        rewrite rngl_cos_mul_2_l.
        apply (rngl_le_0_sub Hop Hor).
...
      replace 3 with (2 + 1) by easy.
      rewrite angle_mul_add_distr_r.
      rewrite angle_mul_1_l.
      cbn - [ "*"%A ].
...
      replace 3 with (2 + 1) in Hzsi3 by easy.
      rewrite angle_mul_add_distr_r in Hzsi3.
      rewrite angle_mul_1_l in Hzsi3.
...
  Hzs : (0 ≤ rngl_sin θ)%L
  Hzsi : (0 ≤ rngl_sin θi)%L
  Hzsi3 : (0 ≤ rngl_sin (2 * θi + θi))%L
  H1 : (rngl_cos θ ≤ rngl_cos (3 * θi))%L
  ============================
  (0 ≤ rngl_sin (2 * θi))%L
...
      apply rngl_sin_add_nonneg_sin_nonneg in Hzsi3; [ easy | ].
...
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
...
(*
θi ≤ 2 * (π / 3)
sauf que je sais pas diviser un angle par 3...
θi ≤ π

1/3 = 0,010101...
1/3 = 1/4+1/16+1/64
1/3 = 5/16 + 1/64
3*5/16 = 15/16
θi ≤ 2π*15/16
1/3 ≤ 1/4+1/8 = 3/8
montrer θi ≤ 3 (π / 4)
du coup on aurait π/4 ≤ θi
...
*)
  assert (H2 : (θi ≤ 3 * (angle_straight / ₂^2))%A) by ...
  eapply angle_le_trans.
apply H2.
apply angle_mul_le_mono_l.
(* pas gagné *)
...
  apply angle_mul_nat_overflow_distr_add_overflow.
  rewrite Nat_add_mul_r_diag_r.
  replace (1 + 2) with 3 by easy.
...
  apply angle_all_add_not_overflow.
  intros m Hm.
  destruct m. {
...
eapply angle_mul_nat_overflow_le_r.
...
  apply angle_add_overflow_diag. 2: {
    intros H.
    rewrite H in H1.
    apply angle_nlt_ge in H1.
    apply H1.
    now apply angle_div_2_lt_straight.
  }
  apply rngl_sin_nonneg_angle_le_straight.
  eapply angle_le_trans; [ apply H1 | ].
  apply angle_div_2_le_straight.
...
progress unfold angle_add_overflow.
apply angle_ltb_ge.
rewrite <- angle_mul_succ_l.
progress unfold seq_angle_to_div_nat.
progress unfold angle_leb.
(*
do 2 rewrite rngl_cos_nx.
do 3 rewrite rngl_sin_nx.
remember (rngl_cos (θ / ₂^i)) as c eqn:Hc.
remember (rngl_sin (θ / ₂^i)) as s eqn:Hs.
...
*)
remember (seq_angle_to_div_nat θ n) as u eqn:Hu.
remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
symmetry in Hzs.
rewrite Hu in Hzs.
progress unfold seq_angle_to_div_nat in Hzs.
rewrite Hzs.
destruct zs. {
  apply rngl_leb_le in Hzs.
  remember (0 ≤? rngl_sin (S m * u i))%L as zsm eqn:Hzsm.
  symmetry in Hzsm.
  rewrite Hu in Hzsm.
  progress unfold seq_angle_to_div_nat in Hzsm.
  rewrite Hzsm.
  destruct zsm; [ | easy ].
  apply rngl_leb_le in Hzsm.
  apply rngl_leb_le.
  rewrite angle_mul_nat_assoc.
  do 2 rewrite rngl_cos_nx.
  remember (∑ (j = _, _), _) as x; subst x.
  remember (∑ (j = _, _ / _), _) as x; subst x.
  remember (rngl_cos (θ / ₂^i)) as c eqn:Hc.
  remember (rngl_sin (θ / ₂^i)) as s eqn:Hs.
  move s before c.
  destruct m. {
    rewrite Nat.mul_1_l.
    apply (rngl_le_refl Hor).
  }
  destruct m. {
Search (binomial (_ + _)).
Search (binomial (_ * _)).
Search binomial.
  rewrite rngl_sin_nx in Hzsm.
  remember (∑ (j = _, _), _) as x in Hzsm; subst x.
  progress unfold iter_seq in Hzsm.
  progress unfold iter_list in Hzsm.
  rewrite Nat.sub_0_r in Hzsm.
  cbn in Hzsm.
  do 2 rewrite rngl_add_0_l in Hzsm.
  do 2 rewrite rngl_add_0_r in Hzsm.
  rewrite (rngl_mul_1_l Hon) in Hzsm.
  do 2 rewrite (rngl_mul_1_r Hon) in Hzsm.
  rewrite rngl_sin_nx in Hzsm.
  rewrite rngl_cos_nx in Hzsm.
  remember (∑ (j = _, _), _) as x in Hzsm; subst x.
  rewrite <- Hc, <- Hs in Hzsm.
...
  remember (∑ (j = _, _), _) as x in Hzs; subst x.
  remember (rngl_cos (θ / ₂^i)) as c eqn:Hc.
  remember (rngl_sin (θ / ₂^i)) as s eqn:Hs.
  move s before c.
...
  erewrite rngl_summation_eq_compat. 2: {
    intros j (_, Hj).
    erewrite rngl_if_then_else_eq_compat; cycle 1. {
      intros H1.
      remember (∑ (k = _, _), _) as x in |-*.
      remember (∑ (k = _, _), _) as y in |-*.
...
Search ((if _ then _ else _) = (if _ then _ else _)).
... ...
  rewrite angle_add_diag in Hzsm |-*.
  rewrite rngl_sin_mul_2_l in Hzsm.
  rewrite rngl_cos_mul_2_l'.
  apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
  remember (rngl_cos (u i)) as x eqn:Hx.
  rewrite Hu in Hx.
  progress unfold seq_angle_to_div_nat in Hx.
  rewrite <- Hx.
...
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
*)

(* to be completed
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
  → ((θ1 - θ2) / ₂^n)%A = (θ1 / ₂^n - θ2 / ₂^n)%A.
...
rewrite <- angle_div_2_pow_sub. 2: {
(* ah mais ça, c'est faux, en fait, parce que θ devrait être
   égal à 3θ' *)
      progress unfold angle_sub.
...
Theorem angle_div_2_pow_opp :
  ∀ i θ,
  (- (θ / ₂^i) =
     match i with
     | 0 => -θ
     | S i' => angle_straight / ₂^i' - θ / ₂^i
     end)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq.
cbn.
...
 mk_angle (rngl_cos (θ / ₂^i)) (- rngl_sin (θ / ₂^i)))%A.
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
  ∀ i θ, (- (θ / ₂^i) = ((- θ) / ₂^i))%A.
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
Search (angle_lim (λ _, (_ * (_ / ₂^_)))%A).
...
Search ((_ - _) / ₂^_)%A.
Search (_ * (_ / ₂^_))%A.
Search (angle_lim (λ _, (_ * _)%A)).
...
Search (_ * _ * _)%A.
Search (_ * _ * (_ / ₂^_))%A.
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
        now apply Nat.mul_div_le.
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
    eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
    apply Nat.div_le_upper_bound; [ easy | ].
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
Search (_ * (_ / ₂^_))%A.
rewrite <- angle_div_2_pow_mul.
Inspect 5.
...
Search (_ * (_ / ₂))%A.
Inspect 3.
Search (_ * (_ / ₂^_))%A.
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
Search (_ * (_ / ₂^_))%A.
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
      remember (2 ^ S (S i) / 3 * (θ / ₂^S (S i)))%A as θ1 eqn:H1.
      symmetry in H1.
      generalize H1; intros H2.
      apply angle_div_2_pow_mul_nat_if in H1.
      apply (angle_mul_nat_not_overflow_le_l 3) in H1. 2: {
        apply Nat.div_le_lower_bound. 2: {
          rewrite Nat.mul_comm.
          now apply Nat.mul_div_le.
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
      remember (2 ^ S (S i) / 3 * (θ / ₂^S (S i)))%A as θ2 eqn:H2.
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
            now apply Nat.mul_div_le.
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
remember (5 * (θ / ₂^4))%A as x.
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
Search (_ * (_ / ₂))%A.
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
specialize (angles_lim_le (λ i, 2 ^ i / n * (θ / ₂^i)) (λ _, θ))%A as H1.
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
  ∀ i n θ, (2 ^ i / n * (θ / ₂^i) ≤ θ)%A.
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
specialize (H1 θ' (2 ^ N / n * (θ / ₂^N)) 0)%A.
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
  ∀ i n θ, (2 ^ i / n * (θ / ₂^i) ≤ θ)%A.
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
remember (0 ≤? rngl_sin (2 ^ i / n * (θ / ₂^i)))%L as zs2 eqn:Hzs2.
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
  apply (rngl_le_trans Hor _ (rngl_cos (2 ^ S i / 2 * (θ / ₂^S i)))). {
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
    apply (IHi n (θ / ₂)%A).
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
  apply angle_le_trans with (θ2 := (2 ^ S i * (θ / ₂^S i))%A). {
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
Search (_ * (_ / ₂^_))%A.
Search (rngl_cos (_ * _)).
(* faire un Fixpoint, comme pour rngl_cos_div_pow_2 *)
...
Search rngl_cos_div_pow_2.
rngl_cos_div_pow_2_eq: ∀ (θ : angle T) (n : nat), rngl_cos (θ / ₂^S n) = rngl_cos_div_pow_2 (θ / ₂) n
...
Search (_ * _)%A.
rewrite rngl
Search (rngl_cos _ ≤ rngl_cos _)%L.
Check rngl_cos_le_cos_add1.
remember ((2 ^ i / n * (θ / ₂^i)))%A as θ' eqn:Hθ'.
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
      apply Nat.div_le_upper_bound; [ easy | ].
      cbn.
      now apply -> Nat.succ_le_mono.
    }
    cbn.
    rewrite Nat.add_0_r.
    destruct i. {
      cbn.
Search (_ * (_ / ₂))%A.
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
  set (θi := λ i, (2 ^ i / n * (θ / ₂^i))%A).
  set (θ'i := λ i, (2 ^ i / n * (n * θ' / ₂^i))%A).
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
Search (_ / ₂ < angle_straight)%A.
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
  set (θi := λ i, (2 ^ i / n * (θ / ₂^i))%A).
  set (θ'i := λ i, (2 ^ i / n * (n * θ / ₂^i))%A).
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

Theorem Cauchy_sin_cos_Cauchy_angle :
  ∀ u,
  rngl_is_Cauchy_sequence (λ i, rngl_cos (u i))
  → rngl_is_Cauchy_sequence (λ i, rngl_sin (u i))
  → is_Cauchy_sequence angle_eucl_dist u.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hcc Hcs.
  intros ε Hε.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hcc Hcs.
intros ε Hε.
assert (Hε2 : (0 < √(ε² / 2))%L). {
  apply (rl_sqrt_pos Hon Hos Hor).
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  rewrite (rngl_mul_0_l Hos).
  progress unfold rngl_squ.
  now apply (rngl_mul_pos_pos Hop Hor Hii).
}
specialize (Hcc _ Hε2).
specialize (Hcs _ Hε2).
destruct Hcc as (cn, Hcc).
destruct Hcs as (sn, Hcs).
move sn before cn.
exists (max cn sn).
intros p q Hp Hq.
progress unfold angle_eucl_dist.
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hop Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor ε)%L. 2: {
  now apply (rngl_lt_le_incl Hor) in Hε.
}
apply (rngl_squ_lt_abs_lt Hop Hor Hii).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hop Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
specialize (Hcc p q).
specialize (Hcs p q).
assert (H : cn ≤ p) by now apply Nat.max_lub_l in Hp.
specialize (Hcc H); clear H.
assert (H : cn ≤ q) by now apply Nat.max_lub_l in Hq.
specialize (Hcc H); clear H.
assert (H : sn ≤ p) by now apply Nat.max_lub_r in Hp.
specialize (Hcs H); clear H.
assert (H : sn ≤ q) by now apply Nat.max_lub_r in Hq.
specialize (Hcs H); clear H.
progress unfold rngl_dist in Hcc.
progress unfold rngl_dist in Hcs.
apply (rngl_lt_le_incl Hor) in Hε2.
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L in Hcc, Hcs; [ | easy | easy ].
apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid) in Hcc, Hcs.
assert (Hzε2 : (0 ≤ ε² / 2)%L). {
  apply (rngl_le_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_squ_nonneg Hop Hor).
}
rewrite (rngl_squ_sqrt Hon) in Hcc, Hcs; [ | easy | easy ].
specialize (rngl_div_add_distr_r Hiv ε² ε² 2)%L as H1.
rewrite (rngl_add_diag2 Hon) in H1.
rewrite (rngl_mul_div Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite H1.
rewrite (rngl_squ_sub_comm Hop) in Hcc, Hcs.
now apply (rngl_add_lt_compat Hop Hor).
Qed.

(* to be completed
Theorem seq_angle_to_div_nat_is_Cauchy :
  ∀ n θ,
  is_Cauchy_sequence angle_eucl_dist
    (seq_angle_to_div_nat θ n).
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  intros ε Hε.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros.
set (u := λ i, (2 ^ i / n * angle_div_2_pow θ i)%A).
apply Cauchy_sin_cos_Cauchy_angle. {
  progress unfold seq_angle_to_div_nat.
  enough (H :
    ∀ ε, (0 < ε)%L →
    ∃ N : nat,
      ∀ p q : nat,
      N ≤ p
      → N ≤ q
      → (rngl_abs (rngl_sin (u p / ₂ + u q / ₂)) < ε / 2)%L). {
  intros ε Hε.
  progress unfold rngl_dist.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros p q Hp Hq.
  specialize (HN p q Hp Hq).
  progress fold (u p).
  progress fold (u q).
  rewrite rngl_cos_sub_rngl_cos.
  rewrite (rngl_abs_opp Hop Hor).
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_abs_mul Hop Hi1 Hor).
  replace (rngl_abs 2) with 2%L. 2: {
    symmetry; apply (rngl_abs_nonneg_eq Hop Hor).
    apply (rngl_0_le_2 Hon Hop Hor).
  }
  rewrite (rngl_mul_comm Hic).
  apply (rngl_lt_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_abs_mul Hop Hi1 Hor).
  remember (rngl_sin _)%L as s eqn:Hs.
  eapply (rngl_le_lt_trans Hor _ (rngl_abs s * 1))%L. {
    apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
      apply (rngl_abs_nonneg Hop Hor).
    }
    clear s Hs HN.
    remember (rngl_sin _) as s eqn:Hs.
    progress unfold rngl_abs.
    remember (s ≤? 0)%L as sz eqn:Hsz.
    symmetry in Hsz; subst s.
    destruct sz. {
      apply (rngl_opp_le_compat Hop Hor).
      rewrite (rngl_opp_involutive Hop).
      apply rngl_sin_bound.
    }
    apply rngl_sin_bound.
  }
  rewrite (rngl_mul_1_r Hon).
  easy.
}
intros ε Hε.
...
set (u := seq_angle_to_div_nat θ n).
...

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
     rngl_opt_le_dec := NA;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := gc_opt_alg_closed;
     rngl_characteristic_prop := gc_characteristic_prop;
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
