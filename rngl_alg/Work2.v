(* File created because Work.v became too big, but
   without any topic found for the moment *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike.
Require Import Misc.
Require Import RealLike TrigoWithoutPi TrigoWithoutPiExt.
Require Import AngleAddLeMonoL.
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

(* to be completed
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
(*
   1/n = 0.0.............01.........10...
           <- log2_up n -><- len n ->
     an = 1.........11
          <- len n ->
     bn = log2_up n + len n
   1/n = 0.0.............01.........10...
  2^bn =   10............00.........0
     an =                111111111111
     an =               100.........0 - 1
      n =  1..............
           <- log2_up n ->
n * an =   11...
    mouais, enfin, chais pas...

ça voudrait dire que n * an ≥ 2 ^ bn + 2 ^ (bn-1) ?
*)
Compute (map (λ n,
  Nat.leb
  (2 ^ inv_ub_den_pow2 n + 2 ^ (inv_ub_den_pow2 n - 9))
  (n * inv_ub_num n)
) (seq 2 256)).
(* peut-être une piste, là, si
    2^bn + 2^(bn-2*log2_up n) ≤ n an
 *)
Compute (map (λ n,
  Nat.leb
  (2 ^ inv_ub_den_pow2 n + 2 ^ (inv_ub_den_pow2 n - 2 * Nat.log2_up n))
  (n * inv_ub_num n)
) (seq 2 200)).
(*
apply (le_trans _ ((2 ^ inv_ub_den_pow2 n + 2 ^ (inv_ub_den_pow2 n - 2 * Nat.log2_up n)))).
flia.
rewrite Nat.pow_sub_r; [ | easy | ].
*)
Compute (map (λ n,
  Nat.leb
  (2 * Nat.log2_up n)
  (inv_ub_den_pow2 n)
) (seq 0 80)).
(* ah, chiasse de pute *)
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
(**)
Compute (map (λ n,
Nat.ltb
  (2 ^ (Nat.log2_up n + fst_1_len 1 n)) (n * (2 ^ S (fst_1_len 1 n) - 1))
) (seq 2 60)).
(* ok *)
Search (Nat.log2_up _ < Nat.log2_up _).
(**)
(*
apply Nat.lt_le_incl.
apply Nat.log2_up_lt_cancel.
(*
Compute (map (λ n,
Nat.ltb
  (Nat.log2_up (2 ^ (Nat.log2_up n + fst_1_len 1 n)))
  (Nat.log2_up (n * (2 ^ S (fst_1_len 1 n) - 1)))
) (seq 2 80)).
(* ok *)
*)
rewrite Nat.log2_up_pow2; [ | easy ].
apply Nat.eq_le_incl.
rewrite <- Nat.add_1_r.
(*
Compute (map (λ n,
Nat.eqb
  (Nat.log2_up n + fst_1_len 1 n + 1)
  (Nat.log2_up (n * (2 ^ S (fst_1_len 1 n) - 1)))
) (seq 2 200)).
(* ok *)
*)
specialize (Nat.log2_up_succ_or n) as H1.
destruct H1 as [H1| H1]. {
  apply Nat_pow2_log2_up_succ in H1.
  rewrite <- H1 at 3.
  rewrite Nat.mul_comm.
  rewrite Nat.log2_up_mul_pow2; [ | | easy ]. 2: {
    apply Nat.lt_add_lt_sub_r.
    rewrite Nat.add_0_l.
    progress unfold lt.
    rewrite Nat.pow_succ_r'.
    apply Nat_mul_le_pos_r.
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  rewrite <- Nat.add_assoc; f_equal.
  rewrite Nat.add_1_r; symmetry.
  apply Nat_log2_up_pow2_sub_1.
  intros H.
  apply Nat.succ_inj in H.
Theorem neq_fst_1_len_0 : ∀ n, 2 ≤ n → fst_1_len 1 n ≠ 0.
Proof.
intros * H2n.
progress unfold fst_1_len.
rewrite snd_rank_fst_loop_1_log2_up; [ | easy ].
induction n; [ easy | ].
apply Nat.succ_le_mono in H2n.
cbn - [ "*" "/" "mod" "^" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" "^" ].
remember (_ =? 0) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1; [ exfalso | easy ].
apply Nat.eqb_eq in Hn1.
apply Nat.div_small_iff in Hn1; [ | easy ].
apply Nat.nle_gt in Hn1.
apply Hn1; clear Hn1.
rewrite Nat.pow_sub_r; [ | easy | ].
rewrite Nat.pow_1_r.
Search (_ * (_ / _)).
(* ah, fait chier, pourtant ce théorème est vrai *)
...
specialize (Nat.log2_up_spec (S n)) as H1.
eapply le_trans; [ apply H1; flia H2n | ].
...
*)
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
(**)
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
(**)
rewrite <- Nat.add_sub_swap in Hm3. 2: {
  destruct n; [ easy | ].
  destruct n; [ flia H2n | cbn; flia ].
}
(**)
rewrite <- (Nat.sub_add 1 (_ + _)). 2: {
  destruct n; [ easy | ].
  destruct n; [ flia H2n | cbn; flia ].
}
rewrite Nat.pow_add_r, Nat.pow_1_r, Nat.mul_comm.
remember (2 ^ (Nat.log2_up n + m - 1)) as p eqn:Hp.
rewrite <- Nat.add_sub_assoc in Hp; [ | flia Hmz ].
destruct (lt_dec p n) as [Hpn| Hpn]. {
  rewrite Nat.mod_small in Hm3; [ | easy ].
  eapply le_trans; [ apply Nat.lt_le_incl, Hm3 | ].
  rewrite Nat.pow_succ_r'.
  specialize (Nat.pow_nonzero 2 m (Nat.neq_succ_0 _)) as H1.
  destruct (2 ^ m); [ easy | flia ].
}
apply Nat.nlt_ge in Hpn.
rewrite Nat.pow_add_r in Hp.
...
rewrite <- (Nat.log2_up_pow2 m) in Hp; [ | easy ].
rewrite Nat.pow_succ_r'.
Search (Nat.log2_up _ + Nat.log2_up _).
Search (Nat.log2_up (_ * _)).
...
rewrite (Nat_mod_less_small 1) in Hm3. 2: {
  rewrite Nat.mul_1_l.
  split; [ easy | ].
...
rewrite Nat.pow_sub_r in Hm3; [ | easy | ]. 2: {
  destruct n; [ easy | ].
  destruct n; [ flia H2n | cbn; flia ].
}
rewrite Nat.pow_1_r in Hm3.
remember (2 ^ (Nat.log2_up n + m)) as p eqn:Hp.
...
assert (H : p mod 2 = 0). {
  apply Nat.mod_divides; [ easy | ].
  rewrite Hp.
  destruct n; [ easy | ].
  destruct n; [ flia H2n | ].
  cbn - [ "*" ].
  now exists (2 ^ (Nat.log2_iter n 0 1 0 + m)).
}
apply Nat.mod_divides in H; [ | easy ].
destruct H as (q, H); move H at top; subst p.
rewrite (Nat.mul_comm _ q), Nat.div_mul in Hm3; [ | easy ].
...
destruct (lt_dec (p / 2) n) as [Hp2n| Hp2n]. {
  rewrite Nat.mod_small in Hm3; [ | easy ].
  apply (Nat.add_lt_mono_r _ _ (p mod 2)) in Hm3.
  rewrite <- Nat.div_mod in Hm3; [ | apply Nat.neq_succ_0 ].
  eapply le_trans. {
    apply Nat.lt_le_incl, Hm3.
  }
...
(* en faisant ça à la main, en augmentant m : *)
(*
  H2n : 2 ≤ n
  Hm3 : 2 * nth_rest_of_div m (2 ^ (Nat.log2_up n - 1)) n < n
  ============================
  n ≤ (2 * n - 2 ^ Nat.log2_up n) * 2 ^ m
*)
destruct m. {
  exfalso.
  cbn - [ "*" ] in Hm3.
  apply Nat.nle_gt in Hm3.
  apply Hm3; clear Hm3.
  rewrite <- Nat.pow_succ_r'.
  rewrite <- Nat_succ_sub_succ_r. 2: {
    destruct n; [ easy | ].
    destruct n; [ flia H2n | now cbn ].
  }
  rewrite Nat.sub_0_r.
  now apply Nat.log2_up_spec.
}
(*
  H2n : 2 ≤ n
  Hm3 : 2 * nth_rest_of_div (S m) (2 ^ (Nat.log2_up n - 1)) n < n
  ============================
  n ≤ (2 * n - 2 ^ Nat.log2_up n) * 2 ^ S m
*)
destruct m. {
  rewrite Nat.pow_1_r.
  cbn - [ "*" ] in Hm3.
  rewrite <- Nat.pow_succ_r' in Hm3.
  rewrite <- Nat_succ_sub_succ_r in Hm3. 2: {
    destruct n; [ easy | ].
    destruct n; [ flia H2n | now cbn ].
  }
  rewrite Nat.sub_0_r in Hm3.
  rewrite (Nat_mod_less_small 1) in Hm3. 2: {
    rewrite Nat.mul_1_l.
    split; [ now apply Nat.log2_up_spec | ].
    apply Nat_log2_up_lt_twice; flia H2n.
  }
  flia Hm3.
}
(*
  H2n : 2 ≤ n
  Hm3 : 2 * nth_rest_of_div (S (S m)) (2 ^ (Nat.log2_up n - 1)) n < n
  ============================
  n ≤ (2 * n - 2 ^ Nat.log2_up n) * 2 ^ S (S m)
*)
destruct m. {
  progress replace (2 ^ 2) with 4 by easy.
  cbn - [ "*" ] in Hm3.
  rewrite <- Nat.pow_succ_r' in Hm3.
  rewrite <- Nat_succ_sub_succ_r in Hm3. 2: {
    destruct n; [ easy | ].
    destruct n; [ flia H2n | now cbn ].
  }
  rewrite Nat.sub_0_r in Hm3.
  rewrite (Nat_mod_less_small 1 (_ ^ _)) in Hm3. 2: {
    rewrite Nat.mul_1_l.
    split; [ now apply Nat.log2_up_spec | ].
    apply Nat_log2_up_lt_twice; flia H2n.
  }
  rewrite Nat.mul_1_l in Hm3.
  destruct (lt_dec (2 ^ S (Nat.log2_up n)) (3 * n)) as [H3n| H3n]. {
    rewrite Nat.mod_small in Hm3; [ flia Hm3 | ].
    rewrite Nat.mul_sub_distr_l.
    apply Nat_lt_sub_lt_add_r_iff. {
      apply Nat.mul_le_mono_l.
      now apply Nat.log2_up_spec.
    }
    rewrite <- (Nat.mul_1_l n) at 2.
    rewrite <- Nat.mul_add_distr_r.
    progress replace (1 + 2) with 3 by easy.
    now rewrite <- Nat.pow_succ_r'.
  }
  apply Nat.nlt_ge in H3n.
  rewrite (Nat_mod_less_small 1) in Hm3; [ flia Hm3 | ].
  rewrite Nat.mul_1_l.
  rewrite Nat.mul_sub_distr_l.
  rewrite Nat.pow_succ_r' in H3n.
  split. {
    apply Nat.le_add_le_sub_r.
    rewrite <- (Nat.mul_1_l n) at 1.
    now rewrite <- Nat.mul_add_distr_r.
  }
  apply Nat_lt_sub_lt_add_r_iff; [ flia H3n | ].
  rewrite <- Nat.mul_add_distr_r.
  progress replace (1 + 1 + 2) with (2 * 2) by easy.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply Nat_log2_up_lt_twice; flia H2n.
}
(*
  H2n : 2 ≤ n
  Hm3 : 2 * nth_rest_of_div (S (S (S m))) (2 ^ (Nat.log2_up n - 1)) n < n
  ============================
  n ≤ (2 * n - 2 ^ Nat.log2_up n) * 2 ^ S (S (S m))
*)
destruct m. {
  progress replace (2 ^ 3) with 8 by easy.
  cbn - [ "*" ] in Hm3.
  rewrite <- Nat.pow_succ_r' in Hm3.
  rewrite <- Nat_succ_sub_succ_r in Hm3. 2: {
    destruct n; [ easy | ].
    destruct n; [ flia H2n | now cbn ].
  }
  rewrite Nat.sub_0_r in Hm3.
  rewrite (Nat_mod_less_small 1 (_ ^ _)) in Hm3. 2: {
    rewrite Nat.mul_1_l.
    split; [ now apply Nat.log2_up_spec | ].
    apply Nat_log2_up_lt_twice; flia H2n.
  }
  rewrite Nat.mul_1_l in Hm3.
  destruct (lt_dec (2 ^ S (Nat.log2_up n)) (3 * n)) as [H3n| H3n]. {
    rewrite (Nat.mod_small (_ * (_ - _))) in Hm3. 2: {
      rewrite Nat.mul_sub_distr_l.
      apply Nat_lt_sub_lt_add_r_iff. {
        apply Nat.mul_le_mono_l.
        now apply Nat.log2_up_spec.
      }
      rewrite <- (Nat.mul_1_l n) at 2.
      rewrite <- Nat.mul_add_distr_r.
      progress replace (1 + 2) with 3 by easy.
      now rewrite <- Nat.pow_succ_r'.
    }
    destruct (lt_dec (4 * 2 ^ Nat.log2_up n) (5 * n)) as [H5n| H5n]. {
      clear H3n.
      rewrite Nat.mod_small in Hm3; [ flia H5n | ].
      rewrite Nat.mul_assoc.
      rewrite Nat.mul_sub_distr_l.
      apply Nat_lt_sub_lt_add_r_iff. {
        apply Nat.mul_le_mono_l.
        now apply Nat.log2_up_spec.
      }
      rewrite <- (Nat.mul_1_l n) at 2.
      progress replace (2 * 2) with 4 by easy.
      now rewrite <- Nat.mul_add_distr_r.
    }
    apply Nat.nlt_ge in H5n.
    rewrite (Nat_mod_less_small 1) in Hm3. 2: {
      rewrite Nat.pow_succ_r' in H3n.
      rewrite Nat.mul_1_l.
      rewrite Nat.mul_assoc.
      rewrite Nat.mul_sub_distr_l.
      split; [ | flia H3n ].
      apply Nat.le_add_le_sub_r.
      rewrite <- (Nat.mul_1_l n) at 1.
      progress replace (2 * 2) with 4 by easy.
      now rewrite <- Nat.mul_add_distr_r.
    }
    rewrite Nat.pow_succ_r' in H3n.
    flia H3n.
  }
  apply Nat.nlt_ge in H3n.
  rewrite Nat.pow_succ_r' in H3n.
  rewrite (Nat_mod_less_small 1 (_ * (_ - _))) in Hm3. 2: {
    split; [ flia H3n | ].
    apply Nat.mul_lt_mono_pos_l; [ easy | ].
    assert (H : n ≠ 0) by flia H2n.
    specialize (Nat_log2_up_lt_twice n H) as H1; clear H.
    flia H1.
  }
  rewrite Nat.mul_1_l in Hm3.
  apply Nat.nlt_ge; intros H.
  assert (H4n : 7 * n ≤ 4 * 2 ^ Nat.log2_up n) by flia H.
  apply Nat.nle_gt in H; apply H; clear H.
  rewrite (Nat_mod_less_small 1) in Hm3; [ flia Hm3 | ].
  rewrite Nat.mul_1_l.
  rewrite Nat.mul_sub_distr_l.
  split. 2: {
    apply Nat_lt_sub_lt_add_r_iff. {
      apply Nat.mul_le_mono_l.
      rewrite Nat.mul_sub_distr_l.
      apply Nat_le_add_le_sub_l_iff. {
        apply Nat.mul_le_mono_l.
        now apply Nat.log2_up_spec.
      }
      rewrite <- (Nat.mul_1_l n) at 2.
      now rewrite <- Nat.mul_add_distr_r.
    }
    rewrite Nat.mul_assoc.
    rewrite <- Nat.mul_add_distr_r.
    apply Nat.mul_lt_mono_pos_l; [ flia | ].
    assert (H : n ≠ 0) by flia H2n.
    specialize (Nat_log2_up_lt_twice n H) as H1; clear H.
    flia H1.
  }
  apply Nat.le_add_le_sub_l.
  rewrite Nat.mul_assoc.
  rewrite Nat.mul_sub_distr_l.
  apply Nat.le_add_le_sub_l.
  rewrite <- (Nat.mul_1_l n) at 3.
  do 2 rewrite <- Nat.mul_add_distr_r.
  easy.
}
(*
  H2n : 2 ≤ n
  Hm3 : 2 * nth_rest_of_div (S (S (S (S m)))) (2 ^ (Nat.log2_up n - 1)) n < n
  ============================
  n ≤ (2 * n - 2 ^ Nat.log2_up n) * 2 ^ S (S (S (S m)))
*)
...
unfold x in Hn4.
rewrite Nat.mul_sub_distr_l in Hn4.
rewrite Nat.mul_assoc in Hn4.
replace (4 * 2) with 8 in Hn4 by easy.
replace 4 with (2 * 2) in Hn4 at 2 by easy.
rewrite <- Nat.mul_assoc in Hn4.
do 2 rewrite <- Nat.pow_succ_r' in Hn4.
apply Nat.lt_sub_lt_add_r in Hn4.
rewrite Nat.add_comm in Hn4.
apply Nat_lt_sub_lt_add_r_iff in Hn4; [ | flia ].
rewrite <- (Nat.mul_1_l n) in Hn4 at 2.
rewrite <- Nat.mul_sub_distr_r in Hn4.
replace (8 - 1) with 7 in Hn4 by easy.
...
    rewrite Nat.mod_small in Hm3. 2: {
      rewrite Nat.mul_sub_distr_l.
      apply Nat_lt_sub_lt_add_r_iff. {
        apply Nat.mul_le_mono_l.
        now apply Nat.log2_up_spec.
      }
      rewrite <- (Nat.mul_1_l n) at 2.
      rewrite <- Nat.mul_add_distr_r.
      replace (1 + 2) with 3 by easy.
...
  apply Nat.log2_up_le_pow2; [ easy | cbn ].
  destruct m; [ | flia ].
...
  destruct y. {
    exfalso.
    clear H1.
    apply eq_fst_rank_fst_loop_iff in Hy.
    destruct Hy as (_ & Hy1 & Hy2).
    destruct Hy2 as [Hy2| Hy2]. {
      subst n.
      cbn in x; subst x.
      flia Hn4.
    }
...
    progress unfold nth_bit_of_div in Hy2.
    cbn - [ "*" ] in Hy2.
    rewrite <- Nat.pow_succ_r' in Hy2.
    rewrite <- Nat_succ_sub_succ_r in Hy2; [ | easy ].
    rewrite Nat.sub_0_r in Hy2.
    rewrite (Nat_mod_less_small 1 (2 ^ _)) in Hy2. 2: {
      rewrite Nat.mul_1_l.
      split; [ now apply Nat.log2_up_spec | ].
      apply Nat_log2_up_lt_twice; flia H2n.
    }
    rewrite Nat.mul_1_l in Hy2.
    rewrite (Nat_mod_less_small 0) in Hy2. 2: {
      split; [ easy | ].
      rewrite Nat.mul_sub_distr_l.
      apply Nat_lt_sub_lt_add_r_iff. {
        apply Nat.mul_le_mono_l.
        now apply Nat.log2_up_spec.
      }
      rewrite Nat.add_0_l.
      rewrite <- Nat.mul_add_distr_r.
      replace (1 + 2) with 3 by easy.
...
      apply Nat.lt_add_lt_sub_r.
      rewrite Nat.mul_1_l.
      split. {
        rewrite Nat.mul_sub_distr_l.
        apply Nat.le_add_le_sub_r.
        rewrite <- (Nat.mul_1_l n) at 1.
        rewrite <- Nat.mul_add_distr_r.
        replace (1 + 2) with 3 by easy.
...
        eapply le_trans. {
          apply Nat.mul_le_mono_l.
          now apply Nat.log2_up_spec.
        }
...
      split; [ now apply Nat.log2_up_spec | ].
      apply Nat_log2_up_lt_twice; flia H2n.
    }
    flia Hy2 Hn4.
...
    apply eq_fst_rank_fst_loop_2 in Hy.
    destruct Hy as [Hy| Hy]. {
      destruct Hy as (H1 & H2 & H3); subst n.
      flia Hn8 Hn4.
    }
    destruct Hy as (H1 & _ & H3 & H4).
    apply Nat_div_not_small_iff in H3; [ | flia H1 ].
    apply Nat.div_small_iff in H4; [ | flia H1 ].
    cbn - [ "*" ] in H3, H4.
    rewrite <- Nat.pow_succ_r' in H3, H4.
    rewrite <- Nat_succ_sub_succ_r in H3; [ | easy ].
    rewrite <- Nat_succ_sub_succ_r in H4; [ | easy ].
    rewrite Nat.sub_0_r in H3, H4.
    rewrite (Nat_mod_less_small 1) in H4. 2: {
      rewrite Nat.mul_1_l.
      split; [ easy | ].
      apply Nat.mul_lt_mono_pos_l; [ easy | ].
      apply Nat.mod_upper_bound; flia H1.
    }
    rewrite Nat.mul_1_l in H4.
    rewrite (Nat_mod_less_small 1) in H4. 2: {
      rewrite Nat.mul_1_l.
      split; [ now apply Nat.log2_up_spec | ].
      apply Nat_log2_up_lt_twice; flia H1.
    }
    rewrite Nat.mul_1_l in H4.
    rewrite (Nat_mod_less_small 1) in H3. 2: {
      rewrite Nat.mul_1_l.
      split; [ now apply Nat.log2_up_spec | ].
      apply Nat_log2_up_lt_twice; flia H1.
    }
    rewrite Nat.mul_sub_distr_l in H4.
    apply Nat.lt_sub_lt_add_l in H4.
    rewrite <- (Nat.mul_1_l n) in H4 at 4.
    rewrite <- Nat.mul_add_distr_r in H4.
    progress replace (2 + 1) with 3 in H4 by easy.
    rewrite Nat.mul_assoc in H4.
    rewrite Nat.mul_sub_distr_l in H4.
    apply Nat.lt_sub_lt_add_l in H4.
    rewrite <- Nat.mul_add_distr_r in H4.
    progress replace (2 * 2 + 3) with 7 in H4 by easy.
    flia Hn4 H4.
  }
  rewrite Nat.pow_succ_r'.
  specialize (Nat.pow_nonzero 2 y (Nat.neq_succ_0 _)) as H2.
  flia H2.
}
apply Nat.nle_gt in Hn8.
(* bon, ouais, faut trouver une loi, quoi *)
...
Compute (map (λ n,
  2 ^ S (Nat.log2_up (S n) - 1) < S n
) (seq 0 20)).

    eapply le_lt_trans; [ | apply Hn2 ].
    subst x.
    rewrite Nat.mul_sub_distr_l.
    rewrite <- Nat.pow_succ_r'.
    apply Nat.le_add_le_sub_l.
    rewrite <- Nat_succ_sub_succ_r. 2: {
      apply Nat.neq_0_lt_0.
      intros H.
      apply Nat.log2_up_null in H.
      flia H2n H.
    }
    rewrite Nat.sub_0_r.
    rewrite Nat.pow_succ_r'.
    remember (2 ^ _) as x eqn:Hx.
    progress replace (2 * x + x) with (3 * x) by flia.
    rewrite Nat.mul_assoc.
    progress replace (2 * 2) with 4 by easy.
    subst x.
    specialize (Nat.log2_up_spec (S n) H2n) as H1.
    rewrite <- Nat.sub_1_r in H1.
    destruct H1 as (H1, H2).
    apply Nat.nlt_ge; intros H3.
    apply Nat.nle_gt in H1.
    apply H1; clear H1.
    rewrite Nat.pow_sub_r; [ | easy | easy ].
    rewrite Nat.pow_1_r.
    apply Nat.div_le_lower_bound; [ easy | ].
    apply Nat.nlt_ge.
    intros H1; move H1 after H2.
    apply Nat.nle_gt in H3.
    apply H3; clear H3.
Search (_ ≤ _ / _).
...
Search (_ / _ ≤ _).


    rewrite Nat.pow_sub_r in H1; [ | easy | easy ].
    rewrite Nat.pow_1_r in H1.
...  remember (
...
    apply (Nat.mul_lt_mono_pos_r 2) in H1; [ | easy ].
eapply le_lt_trans in H1. 2: {
Search (_ * (_ / _)).
apply Nat.div_mul_le.
rewrite Nat.
Search (_ / _ < _).
...
    flia H1 H1ln.
Search (Nat.pred _ = _).
Search (_ = Nat.pred _).
...
Search (2 ^ Nat.log2_up _ ≤ _).
Search (2 ^ Nat.log2_up _ < _).
Check Nat.log2_up_spec.
...
Search (Nat.log2_up _ < _).
Check Nat.log2_up_lt_lin.
eapply le_trans.
apply Nat.lt_le_incl.
apply Nat.mul_lt_mono_pos_l; [ easy | ].
Search (2 ^ Nat.log2_up _ ≤ _).
Search (2 ^ Nat.log2_up _).
apply Nat.log2_up_lt_lin.
Check Nat.log2_up_spec.
...
destruct (lt_dec n (2 * x)) as [Hn2| Hn2]. {
  subst un fn.
  cbn - [ "*" ].
  destruct n; [ easy | ].
  cbn - [ "*" "/" "mod" "^" Nat.log2_up ].
  rewrite fst_if, fst_let.
  cbn - [ "*" "/" "mod" "^" Nat.log2_up ].
  rewrite <- Nat.pow_succ_r'.
  remember (_ =? 0) as n1 eqn:Hn1.
  symmetry in Hn1.
  destruct n1. {
    apply Nat.eqb_eq in Hn1.
    apply Nat.div_small_iff in Hn1; [ | easy ].
    exfalso.
    apply Nat.nlt_ge in Hn1.
    apply Hn1; clear Hn1.
    eapply lt_le_trans; [ apply Hn2 | ].
    subst x.
    rewrite Nat.mul_sub_distr_l.
    rewrite <- Nat.pow_succ_r'.
    apply Nat.le_sub_le_add_l.
    rewrite <- Nat_succ_sub_succ_r. 2: {
      apply Nat.neq_0_lt_0.
      intros H.
      apply Nat.log2_up_null in H.
      flia H2n H.
    }
    rewrite Nat.sub_0_r.
    rewrite Nat.pow_succ_r'.
    remember (2 ^ _) as x eqn:Hx.
    progress replace (2 * x + S x) with (3 * x + 1) by flia.
    rewrite Nat.mul_assoc.
    progress replace (2 * 2) with 4 by easy.
...
  rewrite (Nat_div_less_small 1). 2: {
    split. {
      rewrite Nat.mul_1_l.
      eapply le_trans; [ apply Nat.lt_le_incl, Hn2 | ].
      rewrite Nat.pow_succ_r'.
      apply Nat.mul_le_mono_l.
      subst x.
...
    rewrite <- (Nat.mul_1_r 2) at 1.
    apply Nat.mul_le_mono_l.
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
...
    cbn - [ "*" "/" "mod" "^" ].
    rewrite Nat.pow_succ_r'.
    eapply le_trans; [ apply Nat.lt_le_incl, Hn2 | ].
    rewrite Nat.mul_comm.
    apply Nat.mul_le_mono_l.
    rewrite <- (Nat.mul_1_r 2) at 1.
    apply Nat.mul_le_mono_l.
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
...
  eapply le_trans; [ apply Nat.lt_le_incl, Hn2 | ].
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_l.
  destruct n; [ easy | ].
  cbn - [ "*" "/" "mod" "^" ].
  rewrite fst_if, fst_let.
  cbn - [ "*" "/" "mod" "^" ].
  rewrite <- Nat.pow_succ_r'.
...
rewrite (Nat.mul_comm n).
  set (an := 2 ^ S un - 1).
  set (bn := Nat.log2_up n + un).
assert (∃ i, i < Nat.log2_up n ∧ n / 2 ^ S i ≤ x < n / 2 ^ i). {
  subst x.
...
remember (Nat.log2_up n) as m eqn:Hm.
(*
Compute (map (λ n, map (λ m,
  if m <=? Nat.log2_up n then
    Nat.leb
    (2 ^ (m + fst (rank_fst_loop n 0 (2 ^ (m - 1)) n)))
    (n * (2 ^ S (fst (rank_fst_loop n 0 (2 ^ (m - 1)) n)) - 1))
  else true
) (seq 2 20)) (seq 2 60)).
(* ouais, bon, faut voir : *)
*)
Theorem glop :
  ∀ m n,
  m ≤ Nat.log2_up n
  → 2 ≤ n
  → 2 ^ (m + fst (rank_fst_loop n 0 (2 ^ (m - 1)) n)) ≤
    n * (2 ^ S (fst (rank_fst_loop n 0 (2 ^ (m - 1)) n)) - 1).
Proof.
intros * Hmn Hn.
(*1*)
destruct n; [ easy | ].
apply Nat.succ_le_mono in Hn.
cbn - [ "*" "/" "mod" "^" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" "^" ].
rewrite <- Nat.pow_succ_r'.
destruct (lt_dec 0 m) as [Hmz| Hmz]. 2: {
  replace m with 0 by flia Hmz.
  cbn - [ "*" "/" "mod" "^" ].
  rewrite Nat.pow_1_r.
  remember (2 / S n =? 0) as n2 eqn:Hn2.
  symmetry in Hn2.
  destruct n2; [ cbn; flia | ].
  apply Nat.eqb_neq in Hn2.
  apply Nat_div_not_small_iff in Hn2; [ | easy ].
  replace n with 1 by flia Hn Hn2.
  cbn; flia.
}
rewrite <- Nat_succ_sub_succ_r; [ | easy ].
rewrite Nat.sub_0_r.
remember (2 ^ m / S n =? 0) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat.div_small_iff in Hn1; [ | easy ].
  cbn.
  rewrite Nat.add_0_r, Nat.mul_1_r.
  now apply Nat.lt_le_incl.
}
apply Nat.eqb_neq in Hn1.
apply Nat_div_not_small_iff in Hn1; [ | easy ].
generalize Hmn; intros H1.
apply (Nat.pow_le_mono_r 2) in H1; [ | easy ].
rewrite (Nat_mod_less_small 1). 2: {
  split; [ now rewrite Nat.mul_1_l | ].
  eapply le_lt_trans; [ apply H1 | ].
  rewrite <- Nat_pow2_log2; [ | flia Hn ].
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply (le_lt_trans _ n); [ | easy ].
  now apply Nat.log2_spec.
}
rewrite Nat.mul_1_l.
clear H1 Hn1.
(*
Theorem pow2_den_le_mul_num_lemma :
  ∀ p m n,
  0 < m ≤ Nat.log2_up (S p + n)
  → 2 ^ (m + (S p + fst (rank_fst_loop n 0 (2 ^ (p + m) - (2 ^ S p - 1) * (S p + n)) (S p + n)))) ≤
    (S p + n) * (2 ^ (S (S p) + fst (rank_fst_loop n 0 (2 ^ (p + m) - (2 ^ S p - 1) * (S p + n)) (S p + n))) - 1).
Proof.
intros * (Hmz, Hmn).
Admitted.
specialize (pow2_den_le_mul_num_lemma 0 m n) as H1.
rewrite Nat.mul_1_l in H1.
now apply H1.
*)
destruct n; [ easy | clear Hn ].
cbn - [ "*" "/" "mod" "^" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" "^" ].
remember (_ =? 0) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat.div_small_iff in Hn1; [ | easy ].
  cbn.
  rewrite Nat.mul_sub_distr_l in Hn1.
  apply Nat.lt_sub_lt_add_l in Hn1.
  rewrite <- Nat.pow_succ_r' in Hn1.
  rewrite <- (Nat.add_1_r m) in Hn1.
  eapply le_trans; [ apply Nat.lt_le_incl, Hn1 | ].
  flia.
}
apply Nat.eqb_neq in Hn1.
apply Nat_div_not_small_iff in Hn1; [ | easy ].
rewrite (Nat_mod_less_small 1). 2: {
  split; [ now rewrite Nat.mul_1_l | ].
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply Nat_lt_sub_lt_add_r_iff; [ flia Hn1 | ].
  generalize Hmn; intros H1.
  apply (Nat.pow_le_mono_r 2) in H1; [ | easy ].
  eapply le_lt_trans; [ apply H1 | ].
  rewrite <- Nat_pow2_log2; [ | easy ].
  rewrite Nat.pow_succ_r'.
  rewrite Nat_add_diag.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply (le_lt_trans _ (S n)); [ | easy ].
  now apply Nat.log2_spec.
}
rewrite Nat.mul_1_l.
rewrite Nat.mul_sub_distr_l in Hn1.
apply Nat_le_add_le_sub_l_iff in Hn1; [ | flia Hn1 ].
rewrite <- (Nat.mul_1_l (S (S n))) in Hn1 at 2.
rewrite <- Nat.mul_add_distr_r in Hn1.
progress replace (2 + 1) with 3 in Hn1 by easy.
rewrite <- Nat.pow_succ_r' in Hn1.
rewrite Nat.mul_sub_distr_l.
rewrite <- Nat.sub_add_distr.
rewrite <- (Nat.mul_1_l (S (S n))) at 2 6.
rewrite <- Nat.mul_add_distr_r.
progress replace (2 + 1) with 3 by easy.
rewrite <- Nat.pow_succ_r'.
clear Hn1.
(*
Theorem pow2_den_le_mul_num_lemma :
  ∀ p m n,
  0 < m ≤ Nat.log2_up (S p + n)
  → 2 ^ (m + (S p + fst (rank_fst_loop n 0 (2 ^ (p + m) - (2 ^ S p - 1) * (S p + n)) (S p + n)))) ≤
    (S p + n) * (2 ^ (S (S p) + fst (rank_fst_loop n 0 (2 ^ (p + m) - (2 ^ S p - 1) * (S p + n)) (S p + n))) - 1).
Proof.
intros * (Hmz, Hmn).
Admitted.
now apply (pow2_den_le_mul_num_lemma 1).
*)
destruct n. {
  cbn in Hmn.
  replace m with 1 by flia Hmn Hmz.
  cbn; flia.
}
cbn - [ "*" "/" "mod" "^" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" "^" ].
remember (_ =? 0) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat.div_small_iff in Hn1; [ | easy ].
  cbn.
  rewrite Nat.mul_sub_distr_l in Hn1.
  apply Nat.lt_sub_lt_add_l in Hn1.
  rewrite <- Nat.pow_succ_r' in Hn1.
  rewrite <- (Nat.add_1_r m) in Hn1.
  rewrite <- Nat.add_succ_r in Hn1.
  eapply le_trans; [ apply Nat.lt_le_incl, Hn1 | ].
  flia.
}
apply Nat.eqb_neq in Hn1.
apply Nat_div_not_small_iff in Hn1; [ | easy ].
rewrite (Nat_mod_less_small 1). 2: {
  split; [ now rewrite Nat.mul_1_l | ].
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply Nat_lt_sub_lt_add_r_iff; [ flia Hn1 | ].
  generalize Hmn; intros H1.
  rewrite <- (Nat.mul_1_l (S (S (S n)))) at 1.
  rewrite <- Nat.mul_add_distr_r.
  progress replace (1 + 3) with (2 * 2) by easy.
  rewrite <- Nat.mul_assoc.
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply (Nat.pow_le_mono_r 2) in H1; [ | easy ].
  eapply le_lt_trans; [ apply H1 | ].
  rewrite <- Nat_pow2_log2; [ | easy ].
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply (le_lt_trans _ (S (S n))); [ | easy ].
  now apply Nat.log2_spec.
}
rewrite Nat.mul_1_l.
rewrite Nat.mul_sub_distr_l in Hn1.
apply Nat_le_add_le_sub_l_iff in Hn1; [ | flia Hn1 ].
rewrite Nat.mul_assoc in Hn1.
rewrite <- (Nat.mul_1_l (S (S (S n)))) in Hn1 at 2.
rewrite <- Nat.mul_add_distr_r in Hn1.
progress replace (2 * 3 + 1) with 7 in Hn1 by easy.
rewrite <- Nat.pow_succ_r' in Hn1.
rewrite Nat.mul_sub_distr_l.
rewrite <- Nat.sub_add_distr.
rewrite <- (Nat.mul_1_l (S (S (S n)))) at 2 6.
rewrite Nat.mul_assoc.
rewrite <- Nat.mul_add_distr_r.
progress replace (2 * 3 + 1) with 7 by easy.
rewrite <- Nat.pow_succ_r'.
clear Hn1.
(*
Theorem pow2_den_le_mul_num_lemma :
  ∀ p m n,
  0 < m ≤ Nat.log2_up (S p + n)
  → 2 ^ (m + (S p + fst (rank_fst_loop n 0 (2 ^ (p + m) - (2 ^ S p - 1) * (S p + n)) (S p + n)))) ≤
    (S p + n) * (2 ^ (S (S p) + fst (rank_fst_loop n 0 (2 ^ (p + m) - (2 ^ S p - 1) * (S p + n)) (S p + n))) - 1).
Proof.
intros * (Hmz, Hmn).
Admitted.
now apply (pow2_den_le_mul_num_lemma 2).
*)
destruct n. {
  cbn in Hmn.
  destruct m; [ easy | clear Hmz ].
  destruct m; [ cbn; flia | ].
  destruct m; [ cbn; flia | flia Hmn ].
}
cbn - [ "*" "/" "mod" "^" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" "^" ].
remember (_ =? 0) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat.div_small_iff in Hn1; [ | easy ].
  cbn.
  rewrite Nat.mul_sub_distr_l in Hn1.
  apply Nat.lt_sub_lt_add_l in Hn1.
  rewrite <- Nat.pow_succ_r' in Hn1.
  rewrite <- (Nat.add_1_r m) in Hn1.
  do 2 rewrite <- Nat.add_succ_r in Hn1.
  eapply le_trans; [ apply Nat.lt_le_incl, Hn1 | ].
  flia.
}
apply Nat.eqb_neq in Hn1.
apply Nat_div_not_small_iff in Hn1; [ | easy ].
rewrite (Nat_mod_less_small 1). 2: {
  split; [ now rewrite Nat.mul_1_l | ].
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply Nat_lt_sub_lt_add_r_iff; [ flia Hn1 | ].
  generalize Hmn; intros H1.
  rewrite <- (Nat.mul_1_l (S (S (S (S n))))) at 1.
  rewrite <- Nat.mul_add_distr_r.
  do 2 rewrite Nat.pow_succ_r'.
  progress replace (1 + 7) with (2 * 2 * 2) by easy.
  do 2 rewrite <- Nat.mul_assoc.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply (Nat.pow_le_mono_r 2) in H1; [ | easy ].
  eapply le_lt_trans; [ apply H1 | ].
  rewrite <- Nat_pow2_log2; [ | easy ].
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply (le_lt_trans _ (S (S (S n)))); [ | easy ].
  now apply Nat.log2_spec.
}
rewrite Nat.mul_1_l.
rewrite Nat.mul_sub_distr_l in Hn1.
apply Nat_le_add_le_sub_l_iff in Hn1; [ | flia Hn1 ].
rewrite Nat.mul_assoc in Hn1.
rewrite <- (Nat.mul_1_l (S (S (S (S n))))) in Hn1 at 2.
rewrite <- Nat.mul_add_distr_r in Hn1.
progress replace (2 * 7 + 1) with 15 in Hn1 by easy.
rewrite <- Nat.pow_succ_r' in Hn1.
rewrite Nat.mul_sub_distr_l.
rewrite <- Nat.sub_add_distr.
rewrite <- (Nat.mul_1_l (S (S (S (S n))))) at 2 6.
rewrite Nat.mul_assoc.
rewrite <- Nat.mul_add_distr_r.
progress replace (2 * 7 + 1) with 15 by easy.
rewrite <- Nat.pow_succ_r'.
clear Hn1.
(* bon, voir si on peut faire un lemme général *)
Theorem pow2_den_le_mul_num_lemma :
  ∀ p m n,
  0 < m ≤ Nat.log2_up (S p + n)
  → 2 ^ (m + (S p + fst (rank_fst_loop n 0 (2 ^ (p + m) - (2 ^ S p - 1) * (S p + n)) (S p + n)))) ≤
    (S p + n) * (2 ^ (S (S p) + fst (rank_fst_loop n 0 (2 ^ (p + m) - (2 ^ S p - 1) * (S p + n)) (S p + n))) - 1).
Proof.
intros * (Hmz, Hmn).
revert p Hmn.
induction n; intros. {
  cbn - [ "*" "^" ].
  rewrite Nat.add_0_r in Hmn |-*.
  rewrite Nat.mul_sub_distr_l.
  rewrite Nat.mul_1_r.
  apply Nat.le_add_le_sub_l.
  rewrite Nat.pow_add_r.
  eapply le_trans. {
    apply Nat.add_le_mono_l.
    apply Nat.mul_le_mono_r.
    apply (Nat.pow_le_mono_r 2) in Hmn; [ | easy ].
    apply Hmn.
  }
  clear m Hmz Hmn.
  rewrite <- Nat.pow_add_r.
  rewrite <- (Nat.sub_add 1 (2 ^ S (S p))). 2: {
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
  rewrite Nat.add_comm.
  apply Nat.add_le_mono_r.
  now apply pow2_add_l_log2_le_mul_pow2_sub1.
}
rewrite <- Nat.add_succ_comm in Hmn.
specialize (IHn (S p) Hmn).
cbn - [ "*" "/" "mod" "^" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" "^" ].
remember (_ =? 0) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  rewrite Nat.add_0_r.
  rewrite Nat.mul_sub_distr_l.
  rewrite Nat.mul_1_r.
  apply Nat.le_add_le_sub_l.
  rewrite Nat.pow_add_r.
  eapply le_trans. {
    apply Nat.add_le_mono_l.
    apply Nat.mul_le_mono_r.
    apply (Nat.pow_le_mono_r 2) in Hmn; [ | easy ].
    apply Hmn.
  }
  apply Nat.eqb_eq in Hn1.
  apply Nat.div_small_iff in Hn1; [ | easy ].
Compute (map (λ n, map (λ p,
(p,
  Nat.leb
    (S (p + S n) + 2 ^ Nat.log2_up (S (S p) + n) * 2 ^ S p)
    (S (p + S n) * 2 ^ S (S p))
)
) (seq 0 7)) (seq 0 12)).
(* donc ça va pas *)
(* ouais, chais pas *)
(* peut-être que Hn1 est contradictoire, qui sait ? *)
rewrite Nat.mul_sub_distr_l in Hn1.
apply Nat.lt_sub_lt_add_l in Hn1.
rewrite Nat.mul_assoc in Hn1.
rewrite <- (Nat.mul_1_l (S (p + S n))) in Hn1 at 2.
rewrite <- Nat.mul_add_distr_r in Hn1.
rewrite Nat.mul_sub_distr_l in Hn1.
rewrite Nat.mul_1_r in Hn1.
do 2 rewrite <- Nat.pow_succ_r' in Hn1.
replace (2 ^ S (S p) - 2 + 1) with (2 ^ S (S p) - 1) in Hn1. 2: {
  enough (H : 2 ≤ 2 ^ S (S p)); [ flia H | ].
  rewrite <- (Nat.pow_1_r 2) at 1.
  apply Nat.pow_le_mono_r; [ easy | flia ].
}
rewrite Nat.mul_sub_distr_r, Nat.mul_1_l in Hn1.
apply Nat.lt_add_lt_sub_r in Hn1.
do 2 rewrite <- Nat.add_succ_l in Hn1.
  rewrite <- Nat.pow_add_r.
  rewrite <- (Nat.sub_add 1 (2 ^ S (S p))). 2: {
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
  rewrite Nat.add_comm.
  apply Nat.add_le_mono_r.
  rewrite <- Nat.add_succ_l.
  remember (S p) as q.
  clear p Heqq IHn.
  rewrite Nat.add_succ_comm.
  remember (S n) as p.
  clear n Heqp Hmn.
  rewrite (Nat.add_comm q).
  rename q into n.
  rename m into q.
  rename p into m.
Theorem new_pow2_add_l_log2_le_mul_pow2_sub1 :
  ∀ m n, 2 ^ (Nat.log2_up (m + n) + n) ≤ (m + n) * (2 ^ S n - 1).
Proof.
intros.
Compute (map (λ n,
  let m := 7 in
  Nat.leb
    (2 ^ (Nat.log2_up (m + n) + n))
    ((m + n) * (2 ^ S n - 1))
) (seq 2 13)).
(* ah bin non *)
... ...
apply new_pow2_add_l_log2_le_mul_pow2_sub1.
...
  now apply pow2_add_l_log2_le_mul_pow2_sub1.
...
(*
  eapply le_trans. 2: {
    apply Nat.add_le_mul. {
      destruct p; [ cbn in Hmn; flia Hmz Hmn | flia ].
    }
    apply (lt_le_trans _ 2); [ easy | ].
    rewrite Nat.pow_succ_r'.
    rewrite <- (Nat.mul_1_r 2) at 1.
    apply Nat.mul_le_mono_l.
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
Compute (map (λ m, map (λ p,
  if m <=? Nat.log2_up (S p) then
Nat.leb
  (S p + 2 ^ Nat.log2_up (S p) * 2 ^ S p) (S p + 2 ^ S (S p))
  else true
) (seq 1 10)) (seq 0 20)).
(* not ok *)
...
  apply Nat.add_le_mono_l.
  rewrite (Nat.pow_succ_r' _ (S p)).
  apply Nat.mul_le_mono_r.
  (* marche pas *)
...
*)
  eapply le_trans. {
    apply Nat.add_le_mul. {
      destruct p; [ cbn in Hmn; flia Hmz Hmn | flia ].
    }
    rewrite Nat.pow_succ_r'.
    apply (lt_le_trans _ 2); [ easy | ].
    rewrite <- (Nat.mul_1_l 2) at 1.
    apply Nat.mul_le_mono. {
      apply Nat.neq_0_lt_0.
      now apply Nat.pow_nonzero.
    }
    apply Nat_mul_le_pos_r.
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  apply Nat.mul_le_mono_l.
  rewrite (Nat.pow_succ_r' _ (S p)).
  apply Nat.mul_le_mono_r.
  (* marche pas *)
...
Compute (map (λ p,
  2 * (2 * 2 ^ p) ≤ S p * (2 * (2 * 2 ^ p) - 1)
) (seq 0 10)).
...
    do 2 rewrite Nat.add_0_r.
    destruct p; [ easy | ].
    cbn.
    specialize (Nat.pow_nonzero 2 p (Nat.neq_succ_0 _)) as H1.
    destruct p; [ cbn; flia | ].
...

  destruct m; [ cbn; flia | ].
  destruct m; [ cbn; flia | flia Hmn ].
... ...
now apply (pow2_den_le_mul_num_lemma 3).
...1
intros * Hmn Hn.
revert m Hmn.
induction n; intros; [ easy | ].
cbn - [ "*" "/" "mod" "^" ].
rewrite fst_if, fst_let.
cbn - [ "*" "/" "mod" "^" ].
rewrite <- Nat.pow_succ_r'.
destruct (lt_dec 0 m) as [Hmz| Hmz]. 2: {
  replace m with 0 by flia Hmz.
  cbn - [ "*" "/" "mod" "^" ].
  rewrite Nat.pow_1_r.
  remember (2 / S n =? 0) as n2 eqn:Hn2.
  symmetry in Hn2.
  destruct n2; [ cbn; flia | ].
  apply Nat.eqb_neq in Hn2.
  apply Nat_div_not_small_iff in Hn2; [ | easy ].
  replace n with 1 by flia Hn Hn2.
  cbn; flia.
}
rewrite <- Nat_succ_sub_succ_r; [ | easy ].
rewrite Nat.sub_0_r.
remember (2 ^ m / S n =? 0) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2. {
  apply Nat.eqb_eq in Hn2.
  apply Nat.div_small_iff in Hn2; [ | easy ].
  cbn.
  rewrite Nat.add_0_r, Nat.mul_1_r.
  now apply Nat.lt_le_incl.
}
apply Nat.eqb_neq in Hn2.
apply Nat_div_not_small_iff in Hn2; [ | easy ].
rewrite <- Nat.add_succ_comm.
(* cul de sac *)
...
Search (_ ^ _ mod _).
rewrite <- Nat_mod_pow_mod.
...
apply (Nat.pow_le_mono_r 2) in Hmn; [ | easy ].
exfalso.
apply Nat.nlt_ge in Hmn.
apply Hmn; clear Hmn.
eapply lt_le_trans; [ | apply Hn2 ].
(* ah non, c'est faux *)
...
rewrite <- Nat_pow2_log2 in Hmn; [ | flia Hn ].
...
rewrite (Nat_mod_less_small 1).
...
rewrite Nat.pow_add_r.
rewrite Nat.pow_succ_r'.
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
apply Nat.le_add_le_sub_r.
apply Nat_le_add_le_sub_l. {
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
(*
rewrite <- Nat_add_diag.
rewrite <- Nat_sub_sub_distr; [ | apply Nat.log2_up_spec; flia H2n ].
*)
(**)
...
progress unfold fst_1_len.
rewrite snd_rank_fst_loop_1_log2_up; [ | easy ].
rewrite fold_rank_fst_0.
Compute (map (λ n,
(n,
  rank_fst_0 (2 ^ (Nat.log2_up n - 1)) n,
  binary_div 10 1 n,
  binary_div 10 (2 ^ (Nat.log2_up n - 1)) n
)
) (seq 1 20)).
...
Print rank_fst_0.
Print rank_fst_loop.
...
progress unfold rank_fst_0.
clear H1ln.
...
(**)
destruct n; [ easy | ].
cbn - [ "*" "/" "mod" "^" ].
apply Nat.succ_le_mono in H2n.
rewrite <- Nat.pow_succ_r'.
rewrite <- Nat_succ_sub_succ_r. 2: {
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.log2_up_null in H.
  flia H2n H.
}
rewrite Nat.sub_0_r.
remember (_ / _ =? 0) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat.div_small_iff in Hn1; [ | easy ].
  exfalso.
  apply Nat.nle_gt in Hn1.
  apply Hn1; clear Hn1.
  apply Nat.log2_up_spec.
  flia H2n.
}
apply Nat.eqb_neq in Hn1.
apply Nat_div_not_small_iff in Hn1; [ | easy ].
rewrite fst_let.
rewrite (Nat_mod_less_small 1). 2: {
  rewrite Nat.mul_1_l.
  split; [ easy | ].
  cbn - [ "*" ].
  eapply Nat.le_lt_trans; [ | apply Nat.log2_up_spec; flia ].
  apply Nat.pow_le_mono_r; [ easy | ].
  rewrite <- Nat.sub_1_r.
  rewrite Nat.log2_up_double; [ | easy ].
  now rewrite Nat_sub_succ_1.
}
rewrite Nat.mul_1_l.
clear Hn1.
(**)
destruct n; [ easy | ].
cbn - [ "*" "/" "mod" "^" Nat.log2_up ].
apply Nat.succ_le_mono in H2n.
remember (_ / _ =? 0) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat.div_small_iff in Hn1; [ | easy ].
  apply Nat.nlt_ge.
  intros H.
  apply Nat.nle_gt in Hn1.
  apply Hn1; clear Hn1.
  rewrite Nat.mul_sub_distr_l.
  apply Nat.le_add_le_sub_r.
  rewrite <- (Nat.mul_1_l (S (S n))) at 1.
  rewrite <- Nat.mul_add_distr_r.
  cbn - [ "*" Nat.log2_up ].
  rewrite <- Nat.pow_succ_r'.
  apply Nat.nlt_ge.
  intros Hn1.
  apply Nat.nle_gt in H.
  apply H; clear H.
  cbn - [ "*" "/" "mod" "^" Nat.log2_up ].
  rewrite Nat.pow_1_r.
  rewrite Nat.mul_sub_distr_r.
  apply Nat.le_add_le_sub_r.
  apply Nat_le_add_le_sub_l; [ flia | ].
  rewrite (Nat.mul_comm 2), <- Nat.mul_assoc.
  rewrite <- (Nat.mul_1_r (S (S n))) at 3.
  rewrite <- Nat.mul_sub_distr_l.
  replace (2 * 2 - 1) with 3 by easy.
  rewrite (Nat.mul_comm _ 3).
  eapply le_trans; [ | apply Nat.lt_le_incl, Hn1 ].
  now rewrite Nat.mul_comm, Nat.pow_succ_r'.
}
apply Nat.eqb_neq in Hn1.
apply Nat_div_not_small_iff in Hn1; [ | easy ].
rewrite fst_let.
(* ¡ que bordel ! *)
...
  apply Nat.log2_up_spec.
  flia H2n.
}
apply Nat.eqb_neq in Hn1.
apply Nat_div_not_small_iff in Hn1; [ | easy ].
rewrite fst_let.
rewrite (Nat_mod_less_small 1). 2: {
  rewrite Nat.mul_1_l.
  split; [ easy | ].
  cbn - [ "*" ].
  eapply Nat.le_lt_trans; [ | apply Nat.log2_up_spec; flia ].
  apply Nat.pow_le_mono_r; [ easy | ].
  rewrite <- Nat.sub_1_r.
  rewrite Nat.log2_up_double; [ | easy ].
  now rewrite Nat_sub_succ_1.
}
rewrite Nat.mul_1_l.
(**)
...
Check Nat.log2_up_spec.
Search (2 ^ Nat.log2_up _ ≤ _).
Search (2 ^ Nat.log2_up _ < _).
...
  cbn - [ "*" "/" "mod" "^" ].
  rewrite Nat.mul_1_r.
  apply Nat.le_add_le_sub_r.
  apply Nat_le_add_le_sub_l; [ flia | ].
  rewrite <- Nat_add_diag, Nat.add_sub.
  eapply le_trans; [ | apply Nat.lt_le_incl, Hn1 ].
...
  apply Nat.le_sub_le_add_r.
  rewrite Nat.add_comm.
  apply Nat.le_sub_le_add_r.
...
assert (H : n ≤ (n - (2 ^ Nat.log2_up n - n)) * 2 ^ new_fst_1_len n).
  progress unfold new_fst_1_len.
(* ouais, bof, et puis ce "mod n", là, il gêne, il n'est utile que pour
   le cas n=1, mais on s'en fout puisque 2≤n *)
(* et puis ce new_rank_fst_loop, c'est bien joli, mais chais pas si ça
   apporte grand chose *)
(* bon, c'est juste rank_fst_loop spécialisé pour k=0 et où on ne
   considère que fst *)
Print new_rank_fst_loop.
Print rank_fst_loop.
(* donc, chais pas si c'est un vrai progrès *)
Search (snd (rank_fst_loop _ _ _ _)).
(* ah oui, en fait, si, parce que dans la version avec fst_1_len, on
   ne voit pas apparaître 2^(Nat.log2_up n - 1), c'est bizarre *)
(* je comprends pas bien *)
...
Search (_ - (_ - _)).
Compute (map (λ a, pair a ((2 * a - 2 ^ Nat.log2_up a) * 2)) (seq 0 20)).
Compute (map (λ n,
  Nat.leb n ((2 * n - 2 ^ Nat.log2_up n) * 2 ^ fst_1_len 1 n)
) (seq 0 80)).
(* ok *)
Compute (map (λ n,
pair n (
  Nat.leb n ((2 * n - 2 ^ Nat.log2_up n))
)
) (seq 0 80)).
(* not ok *)
Compute (binary_div 20 1 17).
Compute (map (λ n,
if snd (extract_pow2 n) =? 1 then (0, true)
else
pair n
(Nat.eqb
  (
   fst_1_len 1 n)
   (fst_1_len 1 (snd (extract_pow2 n))))
) (seq 0 80)).
  rewrite <- Nat_add_diag.
  rewrite <- Nat_sub_sub_distr. 2: {
    apply Nat.log2_up_spec.
    flia Hnz Hn1.
  }
Compute (map (λ a, pair a (2 ^ Nat.log2_up a - a)) (seq 0 20)).
...
  rewrite Nat.add_sub_swap.
  rewrite <- Nat.sub_add_assoc.
...
Compute (map (λ n,
pair n
  (
    2 ^ fst_1_len 1 n,
    2 ^ fst_1_len 1 (snd (extract_pow2 n)))
) (seq 0 80)).
...
Compute (map (λ n,
pair n
  ((2 * n - 2 ^ Nat.log2_up n),
    2 ^ fst_1_len 1 n,
    2 ^ fst_1_len 1 (snd (extract_pow2 n) + 1))
) (seq 0 80)).
...
Compute (map (λ n,
  (2 ^ fst_1_len 1 n)
) (seq 0 80)).
Compute (map (λ n,
  ((2 * n - 2 ^ Nat.log2_up n))
) (seq 0 80)).
...
apply Nat.log2_log
...
  rewrite fst_1_len_log2_up.
(*
  remember (inv_ub_num n) as an eqn:Han.
*)
  rewrite Nat.add_sub_assoc. 2: {
    apply Nat.neq_0_lt_0.
    intros H.
    apply Nat.log2_up_null in H.
    apply Nat.le_1_r in H.
    progress unfold inv_ub_num in H.
    destruct H as [H| H]. {
      apply Nat.sub_0_le in H.
      apply Nat.le_1_r in H.
      destruct H as [H| H]; [ now apply Nat.pow_nonzero in H | ].
      apply Nat_eq_pow_1 in H.
      now destruct H.
    }
    apply Nat_sub_add_eq_l in H. {
      symmetry in H; cbn - [ "^" ] in H.
      rewrite <- (Nat.pow_1_r 2) in H at 2.
      apply Nat.pow_inj_r in H; [ | easy ].
      apply Nat.succ_inj in H.
      progress unfold fst_1_len in H.
      destruct n; [ easy | clear Hnz ].
      remember (snd _) as x.
      cbn - [ "*" "/" "mod" ] in H.
      rewrite fst_if, fst_let in H.
      cbn - [ "*" "/" "mod" ] in H.
      remember (x / S n =? 0) as n2 eqn:Hn2.
      symmetry in Hn2.
      destruct n2; [ clear H | easy ].
      apply Nat.eqb_eq in Hn2.
      apply Nat.div_small_iff in Hn2; [ | easy ].
      subst x.
      exfalso.
      apply Nat.nlt_ge in Hn2.
      apply Hn2; clear Hn2.
      apply -> Nat.succ_lt_mono.
      cbn - [ "*" "/" "mod" ].
      rewrite snd_if, snd_let.
      cbn - [ "*" "/" "mod" ].
      remember (1 / S n =? 1) as n2 eqn:Hn2.
      symmetry in Hn2.
      destruct n2. 2: {
        apply Nat.eqb_neq in Hn2.
        apply Nat_neq_div_1 in Hn2.
        destruct Hn2 as [Hn2| Hn2]; [ flia Hn2 | ].
        rewrite Nat.mod_small; [ | easy ].
        apply (lt_snd_rank_fst_loop 0).
        cbn; flia Hn1.
      }
      apply Nat.eqb_eq in Hn2.
      apply Nat_eq_div_1 in Hn2.
      easy.
    }
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
(*
  rewrite Nat.sub_1_r.
  apply Nat.lt_le_incl.
Search (2 ^ pred _).
  apply Nat.log2_up_spec.
Search (_ - 1 = pred _).
Search (2 ^ Nat.log2_up _).
rewrite Nat.mul_comm.
Check Nat.log2_up_spec.
...
Search (Nat.log2_up _ + Nat.log2_up _).
Nat.log2_up_mul_below: ∀ a b : nat, 0 < a → 0 < b → Nat.log2_up a + Nat.log2_up b ≤ S (Nat.log2_up (a * b))
...
*)
rewrite Nat.mul_comm.
Compute (map (λ n,
  Nat.leb
    (2 ^ (Nat.log2_up n + Nat.log2_up (inv_ub_num n) - 1))
    (n * inv_ub_num n)
) (seq 0 100)).
(* ok *)
Compute (map (λ n,
let m := snd (extract_pow2 n) in
  Nat.leb
    (2 ^ (Nat.log2_up n + Nat.log2_up (inv_ub_num m) - 1))
    (n * inv_ub_num n)
) (seq 0 100)).
Compute (map (λ n,
  Nat.eqb (inv_ub_num n) (inv_ub_num (snd (extract_pow2 n)))
) (seq 0 80)).
Compute (map (λ n,
  Nat.leb (inv_ub_num n) (inv_ub_num (snd (extract_pow2 n)))
) (seq 0 80)).
(* ah ! ça peut le faire *)
set (m := snd (extract_pow2 n)).
replace (inv_ub_num n) with (inv_ub_num m). 2: {
  subst m.
Theorem inv_ub_num_snd_extract_pow2 :
  ∀ n, inv_ub_num (snd (extract_pow2 n)) = inv_ub_num n.
Proof.
intros.
progress unfold inv_ub_num.
f_equal; f_equal; f_equal.
Theorem fst_1_len_1_snd_extract_pow2 :
  ∀ n, fst_1_len 1 (snd (extract_pow2 n)) = fst_1_len 1 n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
remember (extract_pow2 n) as km eqn:Hkm.
symmetry in Hkm.
destruct km as (k, m).
progress unfold extract_pow2 in Hkm.
remember n as it eqn:H in n.
assert (Hit : n ≤ it) by now subst n.
clear H.
rewrite (extract_pow2_enough_iter n n it) in Hkm; [ | easy | easy | easy ].
clear Hnz; cbn.
revert k n m Hkm Hit.
induction it; intros. {
  apply Nat.le_0_r in Hit; subst n.
  cbn in Hkm.
  now injection Hkm; intros; subst m.
}
cbn - [ "/" "mod" ] in Hkm.
remember (n mod 2 =? 0) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2; [ | now injection Hkm; clear Hkm; intros; subst m ].
apply Nat.eqb_eq in Hn2.
remember (extract_pow2_loop it (n / 2)) as km eqn:Hkm'.
symmetry in Hkm'.
destruct km as (k', m').
injection Hkm; clear Hkm; intros; subst k m'.
rename k' into k.
generalize Hkm'; intros Hkm.
apply IHit in Hkm. 2: {
  apply Nat.mod_divides in Hn2; [ | easy ].
  destruct Hn2 as (c, Hc); subst n.
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
  flia Hit.
}
rewrite Hkm.
(**)
clear - Hn2.
apply Nat.mod_divides in Hn2; [ | easy ].
destruct Hn2 as (c, Hc); subst n.
rename c into n.
rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
symmetry.
progress unfold fst_1_len.
Compute (map (λ n,
  snd (rank_fst_loop (n * 2) 1 1 (n * 2)) =
  2 * snd (rank_fst_loop n 1 1 n)
) (seq 0 20)).
Theorem glop :
  ∀ n,
  snd (rank_fst_loop (n * 2) 1 1 (n * 2)) =
  2 * snd (rank_fst_loop n 1 1 n).
Proof.
intros.
destruct n; [ easy | ].
cbn - [ "*" "/" "mod" ].
(**)
remember (1 / S n =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1; [ now destruct n | ].
apply Nat.eqb_neq in Hn1.
rewrite snd_let.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
apply Nat.succ_lt_mono in Hn1.
rewrite Nat.mul_1_r.
(*
Theorem glop :
  ∀ m n,
  2 ^ (m - 1) - m < n
  → snd (rank_fst_loop ((m + n) * 2) 1 1 ((m + n) * 2)) =
    2 * snd (rank_fst_loop n 1 (2 ^ m) (m + n)).
Admitted.
now apply (glop 1).
*)
destruct n; [ easy | clear Hn1 ].
cbn - [ "*" "/" "mod" ].
remember (2 / S (S n) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1; [ now destruct n | ].
apply Nat.eqb_neq in Hn1.
rewrite snd_let.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
do 2 apply Nat.succ_lt_mono in Hn1.
progress replace (2 * 2) with 4 by easy.
(*
Theorem glop :
  ∀ m n,
  2 ^ (m - 1) - m < n
  → snd (rank_fst_loop ((m + n) * 2) 1 1 ((m + n) * 2)) =
    2 * snd (rank_fst_loop n 1 (2 ^ m) (m + n)).
Admitted.
now apply (glop 2).
*)
destruct n; [ easy | clear Hn1 ].
cbn - [ "*" "/" "mod" ].
remember (4 / S (S (S n)) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  destruct n; [ easy | ].
  do 4 apply Nat.succ_le_mono in Hn1.
  now apply Nat.le_0_r in Hn1; subst n.
}
apply Nat.eqb_neq in Hn1.
rewrite snd_let.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
do 3 apply Nat.succ_lt_mono in Hn1.
progress replace (2 * 4) with 8 by easy.
rename Hn1 into Hn.
(*
Theorem glop :
  ∀ m n,
  2 ^ (m - 1) - m < n
  → snd (rank_fst_loop ((m + n) * 2) 1 1 ((m + n) * 2)) =
    2 * snd (rank_fst_loop n 1 (2 ^ m) (m + n)).
Admitted.
now apply (glop 3).
*)
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hn.
cbn - [ "*" "/" "mod" ].
remember (8 / S (S (S (S n))) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  do 4 (destruct n; [ easy | ]).
  do 8 apply Nat.succ_le_mono in Hn1.
  now apply Nat.le_0_r in Hn1; subst n.
}
apply Nat.eqb_neq in Hn1.
rewrite snd_let.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
do 4 apply Nat.succ_lt_mono in Hn1.
progress replace (2 * 8) with 16 by easy.
clear Hn; rename Hn1 into Hn.
(*
Theorem glop :
  ∀ m n,
  2 ^ (m - 1) - m < n
  → snd (rank_fst_loop ((m + n) * 2) 1 1 ((m + n) * 2)) =
    2 * snd (rank_fst_loop n 1 (2 ^ m) (m + n)).
Admitted.
now apply (glop 4).
*)
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hn.
cbn - [ "*" "/" "mod" ].
remember (16 / S (S (S (S (S n)))) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  do 4 (destruct n; [ flia Hn | ]).
  clear Hn Hn2.
  do 9 apply Nat.succ_le_mono in Hn1.
  do 7 (destruct n; [ easy | ]).
  do 6 apply Nat.succ_lt_mono in Hn1.
  now apply Nat.lt_1_r in Hn1; subst n.
}
apply Nat.eqb_neq in Hn1.
rewrite snd_let.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
do 5 apply Nat.succ_lt_mono in Hn1.
progress replace (2 * 16) with 32 by easy.
clear Hn; rename Hn1 into Hn.
(*
  Hn : 11 < n
  ============================
  snd (rank_fst_loop (S (S (S (S (S n)))) * 2) 1 1 (S (S (S (S (S n)))) * 2)) =
  2 * snd (rank_fst_loop n 1 32 (S (S (S (S (S n))))))
*)
(*
Theorem glop :
  ∀ m n,
  2 ^ (m - 1) - m < n
  → snd (rank_fst_loop ((m + n) * 2) 1 1 ((m + n) * 2)) =
    2 * snd (rank_fst_loop n 1 (2 ^ m) (m + n)).
Admitted.
now apply (glop 5).
*)
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hn.
cbn - [ "*" "/" "mod" ].
remember (32 / S (S (S (S (S (S n))))) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  do 11 (destruct n; [ flia Hn | ]).
  clear Hn Hn2.
  do 17 apply Nat.succ_le_mono in Hn1.
  do 16 (destruct n; [ easy | ]).
  do 15 apply Nat.succ_lt_mono in Hn1.
  easy.
}
apply Nat.eqb_neq in Hn1.
rewrite snd_let.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
do 6 apply Nat.succ_lt_mono in Hn1.
progress replace (2 * 32) with 64 by easy.
clear Hn; rename Hn1 into Hn.
(*
  Hn : 26 < n
  ============================
  snd (rank_fst_loop (S (S (S (S (S (S n))))) * 2) 1 1 (S (S (S (S (S (S n))))) * 2)) =
  2 * snd (rank_fst_loop n 1 64 (S (S (S (S (S (S n)))))))
*)
(*
Theorem glop :
  ∀ m n,
  2 ^ (m - 1) - m < n
  → snd (rank_fst_loop ((m + n) * 2) 1 1 ((m + n) * 2)) =
    2 * snd (rank_fst_loop n 1 (2 ^ m) (m + n)).
Admitted.
now apply (glop 6).
*)
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hn.
cbn - [ "*" "/" "mod" ].
remember (64 / S (S (S (S (S (S (S n)))))) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  do 26 (destruct n; [ flia Hn | ]).
  clear Hn Hn2.
  do 33 apply Nat.succ_le_mono in Hn1.
  do 32 (destruct n; [ easy | ]).
  do 31 apply Nat.succ_lt_mono in Hn1.
  easy.
}
apply Nat.eqb_neq in Hn1.
rewrite snd_let.
apply Nat_neq_div_1 in Hn1.
destruct Hn1 as [Hn1| Hn1]; [ flia Hn Hn1 | ].
rewrite Nat.mod_small; [ | easy ].
do 7 apply Nat.succ_lt_mono in Hn1.
progress replace (2 * 64) with 128 by easy.
clear Hn; rename Hn1 into Hn.
(*
  Hn : 57 < n
  ============================
  snd (rank_fst_loop (S (S (S (S (S (S (S n)))))) * 2) 1 1 (S (S (S (S (S (S (S n)))))) * 2)) =
  2 * snd (rank_fst_loop n 1 128 (S (S (S (S (S (S (S n))))))))
*)
Theorem glop :
  ∀ m n,
  2 ^ (m - 1) - m < n
  → snd (rank_fst_loop ((m + n) * 2) 1 1 ((m + n) * 2)) =
    2 * snd (rank_fst_loop n 1 (2 ^ m) (m + n)).
Proof.
intros * Hmn.
revert m Hmn.
induction n; intros; [ easy | ].
(**)
cbn - [ "*" ].
rewrite snd_if, snd_let.
cbn - [ "*" ].
remember (2 ^ m / (m + S n) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. 2: {
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]. 2: {
    rewrite Nat.mod_small; [ | easy ].
    rewrite <- Nat.add_succ_comm.
    rewrite <- Nat.pow_succ_r'.
    apply IHn.
    rewrite Nat_sub_succ_1.
    apply (Nat.add_lt_mono_r _ _ (S m)).
    rewrite Nat.sub_add; [ | now apply Nat.pow_gt_lin_r ].
    now rewrite Nat.add_comm, Nat.add_succ_comm.
  }
  apply (Nat.add_lt_mono_r _ _ m) in Hmn.
  rewrite Nat.sub_add in Hmn. 2: {
    destruct m; [ easy | ].
    rewrite Nat_sub_succ_1.
    now apply Nat.pow_gt_lin_r.
  }
  rewrite Nat.pow_sub_r in Hmn; [ | easy | ]. 2: {
    destruct m; [ cbn in Hn1; flia Hn1 | flia ].
  }
  rewrite Nat.pow_1_r in Hmn.
  rewrite (Nat_mod_less_small 1). 2: {
    rewrite Nat.mul_1_l.
    split. {
      eapply Nat.le_trans; [ | apply Hn1 ].
      flia.
    }
    rewrite (Nat.add_comm m).
    eapply le_lt_trans. 2: {
      apply (Nat.mul_lt_mono_pos_l 2) in Hmn; [ | easy ].
      apply Hmn.
    }
    destruct m; [ cbn in Hn1; flia Hn1 | ].
    rewrite Nat.pow_succ_r'.
    rewrite (Nat.mul_comm _ (2 ^ m)), Nat.div_mul; [ | easy ].
    now rewrite Nat.mul_comm.
  }
  exfalso.
  apply Nat.nle_gt in Hmn.
  apply Hmn; clear Hmn.
  rewrite Nat.add_comm in Hn1.
  now apply Nat.div_le_lower_bound.
}
apply Nat.eqb_eq in Hn1.
apply Nat_eq_div_1 in Hn1.
(* mouais... faut voir... *)
clear Hmn. (* je crois *)
destruct Hn1 as (Hn1, Hn2).
rewrite <- Nat.pow_succ_r'.
rewrite <- Nat.add_succ_comm.
clear IHn.
(**)
Compute (map (λ n,
  let m := 1 in
if m + S n <=? 2 ^m then
  if 2 ^ m <? 2 * (m + S n) then
  snd (rank_fst_loop ((S m + n) * 2) 1 1 ((S m + n) * 2)) = 2 ^ S m
  else 6 = 6
else (7 = 7)
) (seq 0 70)).
(* ok *)
Print rank_fst_loop.
...
revert n Hn1 Hn2.
induction m; intros. {
  cbn in Hn1.
  apply Nat.succ_le_mono in Hn1.
  now apply Nat.le_0_r in Hn1; subst n.
}
rewrite Nat.add_succ_comm.
...
specialize (IHm (S n)) as H1.
rewrite Nat.add_succ_comm in Hn1.
specialize (H1 Hn1).
...
rewrite (IHm (S n)).
(* caca *)
... si ça marche pas, reprendre ici
(**)
Theorem glop :
  ∀ p m n,
  p + m + S n ≤ 2 ^ (p + m)
  → 2 ^ (p + m) < 2 * (p + m + S n)
  → snd (rank_fst_loop ((S (p + m) + n) * 2) 1 1 ((S (p + m) + n) * 2)) =
    2 ^ (S (p + m)).
Proof.
intros * Hn1 Hn2.
Admitted.
... ...
now apply (glop 0).
...
destruct m. {
  cbn in Hn1.
  apply Nat.succ_le_mono in Hn1.
  now apply Nat.le_0_r in Hn1; subst n.
}
destruct m. {
  cbn in Hn1.
  do 2 apply Nat.succ_le_mono in Hn1.
  now apply Nat.le_0_r in Hn1; subst n.
}
destruct m. {
  cbn in Hn1.
  do 3 apply Nat.succ_le_mono in Hn1.
  apply Nat.le_1_r in Hn1.
  now destruct Hn1; subst n.
}
destruct m. {
  cbn in Hn1.
  destruct n; [ cbn in Hn2; flia Hn2 | ].
  do 3 (destruct n; [ easy | ]).
  do 8 apply Nat.succ_le_mono in Hn1.
  now apply Nat.le_0_r in Hn1; subst n.
}
destruct m. {
  cbn in Hn1.
  do 4 (destruct n; [ cbn in Hn2; flia Hn2 | ]).
  do 7 (destruct n; [ easy | ]).
  do 16 apply Nat.succ_le_mono in Hn1.
  now apply Nat.le_0_r in Hn1; subst n.
}
(*
Theorem glop :
  ∀ p m n,
  p + m + S n ≤ 2 ^ (p + m)
  → 2 ^ (p + m) < 2 * (p + m + S n)
  → snd (rank_fst_loop ((S p + m + n) * 2) 1 1 ((S p + m + n) * 2)) =
    2 ^ (S p + m).
Proof.
Admitted.
now apply (glop 5).
*)
destruct m. {
  cbn in Hn1.
  do 11 (destruct n; [ cbn in Hn2; flia Hn2 | ]).
  clear Hn2.
  do 15 (destruct n; [ easy | ]).
  do 32 apply Nat.succ_le_mono in Hn1.
  now apply Nat.le_0_r in Hn1; subst n.
}
(*
Theorem glop :
  ∀ p m n,
  p + m + S n ≤ 2 ^ (p + m)
  → 2 ^ (p + m) < 2 * (p + m + S n)
  → snd (rank_fst_loop ((S p + m + n) * 2) 1 1 ((S p + m + n) * 2)) =
    2 ^ (S p + m).
Proof.
Admitted.
now apply (glop 6).
...
*)
destruct m. {
  cbn in Hn1.
  do 26 (destruct n; [ cbn in Hn2; flia Hn2 | ]).
  clear Hn2.
  do 31 (destruct n; [ easy | ]).
  do 64 apply Nat.succ_le_mono in Hn1.
  now apply Nat.le_0_r in Hn1; subst n.
}
(*
Theorem glop :
  ∀ p m n,
  p + m + S n ≤ 2 ^ (p + m)
  → 2 ^ (p + m) < 2 * (p + m + S n)
  → snd (rank_fst_loop ((S p + m + n) * 2) 1 1 ((S p + m + n) * 2)) =
    2 ^ (S p + m).
Proof.
Admitted.
now apply (glop 7).
*)
destruct m. {
  cbn in Hn1.
  do 57 (destruct n; [ cbn in Hn2; flia Hn2 | ]).
  clear Hn2.
  do 63 (destruct n; [ easy | ]).
  do 128 apply Nat.succ_le_mono in Hn1.
  now apply Nat.le_0_r in Hn1; subst n.
}
...
Theorem glop :
  ∀ p m n,
  p + m + S n ≤ 2 ^ (p + m)
  → 2 ^ (p + m) < 2 * (p + m + S n)
  → snd (rank_fst_loop ((S (p + m) + n) * 2) 1 1 ((S (p + m) + n) * 2)) =
    2 ^ (S (p + m)).
Proof.
intros * Hn1 Hn2.
...
now apply (glop 8).
...
destruct n. {
  rewrite Nat.add_0_r.
  remember (S m * 2) as x eqn:Hx.
  cbn in  Hx; subst x.
  remember (S (m * 2)) as x eqn:Hx.
  cbn - [ "*" "/" "mod" "^" ].
  rewrite snd_if, snd_let.
  rewrite Nat.div_small; [ | subst x; flia ].
  rewrite Nat.mod_small; [ | subst x; flia ].
  cbn - [ "/" "mod" "^" ].
  subst x.
Search (rank_fst_loop _ _ (2 * _)).
...
  destruct m; [ easy | ].
cbn.
  destruct m; [ easy | ].
  destruct m; [ easy | ].
cbn.
...
cbn in Hmn, Hn1.
flia Hmn Hn1.
  destruct m. {
... ...
now apply (glop 7).
(* essayer avec les itérations prédédentes *)
...
Theorem glop :
  ∀ k n, fst_1_len 1 (n * 2 ^ k) = fst_1_len 1 n.
Proof.
intros.
revert n.
induction k; intros; [ f_equal; apply Nat.mul_1_r | ].
rewrite Nat.pow_succ_r', Nat.mul_assoc.
rewrite IHk.
...
clear T ro rp rl ac.
... ...
apply (glop 1).
...
induction n; [ easy | ].
...
apply (IHit k).
(* ah non, mais c'est pauet-être pas perdu pour autant *)
...
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
remember (extract_pow2 n) as km eqn:Hkm.
symmetry in Hkm.
destruct km as (k, m).
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  subst m.
  specialize (snd_extract_pow2_is_odd n Hnz) as H1.
  rewrite Hkm in H1.
  cbn in H1.
  apply Nat.Even_succ in H1.
  apply Nat.even_spec in H1.
  now rewrite Nat.even_1 in H1.
}
cbn - [ "*" ].
(* y a-t-il une démo de ça sur le Web ? *)
progress unfold fst_1_len.
rewrite snd_rank_fst_1; [ | easy | easy ].
rewrite snd_rank_fst_1; [ | easy | easy ].
Compute (map (λ n,
(n,
  fst (rank_fst_loop n 0 (2 ^ Nat.log2_up n) n)
)
) (seq 0 128)).
(* à 2^n+1, ça devient n, on dirait, puis ça diminue, et quand ça atteint
   1, c'est stable jusqu'à 2^(n+1) compris *)
...
Compute (map (λ n,
(n,
  binary_div 10 (2 ^ Nat.log2_up n) n
)
) (seq 0 128)).
Compute (map (λ n,
let m := snd (extract_pow2 n) in
(n,
  fst (rank_fst_loop m 0 (2 ^ Nat.log2_up m) m)
)
) (seq 0 128)).
Compute (map (λ n,
let m := 2 * n + 1 in
(n,
  fst (rank_fst_loop m 0 (2 ^ Nat.log2_up m) m)
)
) (seq 0 64)).
...
(* voir si on peut pas faire un enough_iter pour rank_fst_loop
   et voir si ça résoudrait le problème *)
Theorem rank_fst_loop_0_enough_iter :
  ∀ it1 it2 a b,
  b ≠ 0
  → b ≤ it1
  → b ≤ it2
  → rank_fst_loop it1 0 a b = rank_fst_loop it2 0 a b.
Proof.
intros * Hbz Hit1 Hit2.
destruct it1; [ now apply Nat.le_0_r in Hit1; subst b | ].
destruct it2; [ now apply Nat.le_0_r in Hit2; subst b | ].
cbn - [ "*" ].
remember (a / b =? 0) as abk eqn:Habk.
symmetry in Habk.
destruct abk; [ easy | ].
apply Nat.eqb_neq in Habk.
remember (a mod b) as a' eqn:Ha'.
specialize (Nat.mod_upper_bound a b Hbz) as Hab.
rewrite <- Ha' in Hab.
clear a Habk Ha'.
rename a' into a; move a after b.
clear Hbz.
revert a b Hab Hit1 Hit2.
revert it2.
induction it1; intros. {
  replace a with 0 by flia Hab Hit1.
  replace b with 1 by flia Hab Hit1.
  now destruct it2; cbn.
}
destruct it2. {
  replace a with 0 by flia Hab Hit2.
  replace b with 1 by flia Hab Hit2.
  easy.
}
cbn - [ "*" ].
remember (2 * a / b =? 0) as ab eqn:Htab.
symmetry in Htab.
destruct ab; [ easy | ].
apply Nat.eqb_neq in Htab.
apply Nat_div_not_small_iff in Htab; [ | flia Hab ].
rewrite (Nat_mod_less_small 1). 2: {
  split; [ now rewrite Nat.mul_1_l | ].
  now apply Nat.mul_lt_mono_pos_l.
}
rewrite Nat.mul_1_l.
destruct (Nat.eq_dec b (S it1)) as [Hb1| Hb1]. {
  subst b.
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
  rewrite Nat.mod_small.
...
  flia Hit2 Hit1 Hba Hab.
... ...
rewrite (IHit1 it2).
...
intros * Hbz Hit1 Hit2.
revert it2 Hit2.
revert a b Hbz Hit1.
induction it1; intros; [ now apply Nat.le_0_r in Hit1; subst b | ].
(**)
destruct it2; [ now apply Nat.le_0_r in Hit2; subst b | ].
cbn - [ "*" ].
remember (a / b =? 0) as abk eqn:Habk.
symmetry in Habk.
destruct abk; [ easy | ].
apply Nat.eqb_neq in Habk.
...
rewrite Nat.mod_small. 2: {
  apply Nat.nle_gt; intros H; apply Habk; clear Habk.
...
(**)
remember (rank_fst_loop it1 k _ _) as ra1 eqn:Hra1.
remember (rank_fst_loop it2 k _ _) as ra2 eqn:Hra2.
symmetry in Hra1, Hra2.
destruct ra1 as (r1, a1).
destruct ra2 as (r2, a2).
move it2 before b.
move r1 before it2; move r2 before r1.
move a1 before r2; move a2 before a1.
...
destruct (Nat.eq_dec b (S it1)) as [Hb1| Hb1]. {
  destruct b; [ easy | ].
  apply Nat.succ_inj in Hb1; subst it1.
  clear Hit1 Hbz.
  apply Nat.succ_le_mono in Hit2.
  clear IHit1.
  revert b Hit2 Habk.
  induction it2; intros; [ now apply Nat.le_0_r in Hit2; subst b | ].
  cbn - [ "*" "/" "mod" ].
  (* peut-être qu'il faudrait ajouter que k=0 ou 1 ? *)
  remember (2 * (a mod S b) / S b =? k) as abk eqn:Hasbk.
  symmetry in Hasbk.
  destruct abk. {
    apply Nat.eqb_eq in Hasbk.
    destruct b; [ easy | ].
    cbn - [ "*" "/" "mod" ].
    now rewrite Hasbk, Nat.eqb_refl.
  }
  apply Nat.eqb_neq in Hasbk.
  destruct (Nat.eq_dec b (S it2)) as [Hb2| Hb2]. {
    destruct b; [ easy | ].
    apply Nat.succ_inj in Hb2; subst it2.
    clear Hit2.
    cbn - [ "*" "/" "mod" ].
    remember (_ =? k) as k' eqn:H1.
    symmetry in H1.
    destruct k'; [ now apply Nat.eqb_eq in H1 | easy ].
  }
  rewrite Nat.mul_mod_idemp_r; [ | easy ].
  rewrite IHit2; [ | flia Hit2 Hb2 | easy ].
...
  remember (rank_fst_loop _ _ _ _) as x eqn:Hx.
...
  remember (a / S b =? k) as abk eqn:Habk.
  symmetry in Habk.
  destruct abk. 2: {
    rewrite Nat.add_0_r.
    remember (rank_fst_loop b _ _ _) as r1 eqn:Hr1.
    symmetry in Hr1.
    destruct r1 as (r1, a1).
    destruct it2; [ easy | ].
    cbn - [ "/" "mod" ].
    rewrite Habk.
    rewrite Nat.add_0_r.
    remember (rank_fst_loop it2 _ _ _) as r2 eqn:Hr2.
    symmetry in Hr2.
    destruct r2 as (r2, a2).
    specialize (IHit1 k (a mod S b + a mod S b)).
    specialize (IHit1 b).
...
destruct b; [ easy | ].
apply Nat.succ_le_mono in Hit1, Hit2.
rewrite IHit1 with (it2 := it2).
...
  remember (rank_fst_loop it1 _ _ _) as r1 eqn:Hr1.
  symmetry in Hr1.
  destruct r1 as (r1, a1).
  destruct b; [ easy | clear Hbz ].
  destruct it2; [ easy | ].
  cbn - [ "/" "mod" ].
  rewrite Habk.
  rewrite Nat.add_0_r.
  remember (rank_fst_loop it2 _ _ _) as r2 eqn:Hr2.
  symmetry in Hr2.
  destruct r2 as (r2, a2).
  specialize (IHit1 k (a mod S b + a mod S b)).
  specialize (IHit1 (S b)).
......
...
Compute (map (λ n,
  let mk := extract_pow2 n in
  let m := snd mk in
(
Nat.eqb
  (snd (rank_fst_loop m 0 (2 ^ Nat.log2_up m) m) * 2 ^ fst mk)
  (snd (rank_fst_loop n 0 (2 ^ Nat.log2_up n) n))
)
) (seq 0 200)).
(* ok *)
...
Theorem exercice :
  ∀ n k m,
  extract_pow2 n = (k, m)
  → snd (rank_fst_loop n 0 (2 ^ Nat.log2_up n) n) =
    snd (rank_fst_loop m 0 (2 ^ Nat.log2_up m) m) * 2 ^ k.
Proof.
intros * Hmk.
progress unfold extract_pow2 in Hmk.
remember n as it eqn:H in n.
assert (Hit : n ≤ it) by now subst n.
clear H.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  cbn in Hmk |-*.
  now injection Hmk; clear Hmk; intros; subst m k.
}
rewrite (extract_pow2_enough_iter n n it) in Hmk; [ | easy | easy | easy ].
Compute (map (λ n,
  binary_div 10 (2 ^ Nat.log2_up n) n
) (seq 0 20)).
Compute (map (λ n,
  let '(m, k) := extract_pow2_loop n n in
(n,
  binary_div 10 (2 ^ Nat.log2_up m) m
)
) (seq 0 20)).
(**)
revert n m k Hmk Hit Hnz.
induction it; intros; [ now apply Nat.le_0_r in Hit | ].
destruct n; [ easy | clear Hnz ].
apply Nat.succ_le_mono in Hit.
cbn - [ "/" "mod" ] in Hmk.
remember (S n mod 2 =? 0) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2. 2: {
  injection Hmk; clear Hmk; intros; subst m k.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
  assert (Hni : 1 * S n ≤ 2 ^ Nat.log2_up (S n) < 2 * S n). {
    rewrite Nat.mul_1_l.
    split. {
      apply Nat.log2_up_spec.
      apply -> Nat.succ_lt_mono.
      now apply Nat.neq_0_lt_0.
    }
    specialize (Nat.log2_up_spec (S n)) as H2.
    assert (H : 1 < S n) by flia Hnz.
    specialize (H2 H); clear H.
    destruct H2 as (H2, H3).
    apply (Nat.mul_lt_mono_pos_l 2) in H2; [ | easy ].
    rewrite <- Nat.pow_succ_r' in H2.
    rewrite (Nat.lt_succ_pred 0) in H2; [ easy | ].
    apply Nat.log2_up_pos.
    flia Hnz.
  }
  apply Nat.eqb_neq in Hn2.
  cbn - [ "*" "/" "mod" ].
  rewrite snd_if, snd_let.
  cbn - [ "*" "/" "mod" ].
  rewrite (Nat_div_less_small 1); [ | easy ].
  rewrite (Nat_mod_less_small 1); [ | easy ].
  cbn - [ "*" ].
  now rewrite Nat.mul_1_r.
}
apply Nat.eqb_eq in Hn2.
remember (extract_pow2_loop it (S n / 2)) as km eqn:Hkm.
symmetry in Hkm.
destruct km as (k', m').
injection Hmk; clear Hmk; intros; subst k m'.
(**)
Search rank_fst_loop.
apply IHit; [ | | easy ].
...
generalize Hkm; intros H.
apply IHit in H.
cbn - [ "*" "/" "mod" ].
rewrite snd_if, snd_let.
cbn - [ "*" "/" "mod" ].
assert (Hni : 1 * S n ≤ 2 ^ Nat.log2_up (S n) < 2 * S n). {
  rewrite Nat.mul_1_l.
  split. {
    apply Nat.log2_up_spec.
    apply -> Nat.succ_lt_mono.
    destruct n; [ easy | flia ].
  }
  specialize (Nat.log2_up_spec (S n)) as H2.
  assert (H1 : 1 < S n) by (destruct n; [ easy | flia ]).
  specialize (H2 H1); clear H1.
  destruct H2 as (H2, H3).
  apply (Nat.mul_lt_mono_pos_l 2) in H2; [ | easy ].
  rewrite <- Nat.pow_succ_r' in H2.
  rewrite (Nat.lt_succ_pred 0) in H2; [ easy | ].
  apply Nat.log2_up_pos.
  destruct n; [ easy | flia ].
}
rewrite (Nat_div_less_small 1); [ | easy ].
rewrite (Nat_mod_less_small 1); [ | easy ].
cbn - [ "*" ].
rewrite Nat.mul_1_l.
rewrite <- Nat.pow_succ_r'.
rewrite <- (IHit n).
...
apply IHit.
...
  rewrite (IHit _ m k); [ | | | easy ]. 2: {
...
  cbn - [ "*" "/" "mod" ].
  rewrite snd_if, snd_let.
  cbn - [ "*" "/" "mod" ].
  remember (extract_pow2_loop it n) as mk eqn:Hmk.
  symmetry in Hmk.
  destruct mk as (m, k).
  rewrite (IHit _ m k); [ | easy | | easy ]. 2: {
...
Search (snd (rank_fst_loop _ _ (2 ^ _) _)).
...
revert it m k Hmk Hit.
induction n; intros; [ easy | clear Hnz ].
destruct it; [ easy | ].
apply Nat.succ_le_mono in Hit.
cbn - [ "*" "/" "mod" "^" ] in Hmk |-*.
rewrite snd_if, snd_let.
cbn - [ "*" "/" "mod" "^" ].
remember (S n mod 2 =? 0) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2. {
  apply Nat.eqb_eq in Hn2.
  apply Nat.mod_divides in Hn2; [ | easy ].
  destruct Hn2 as (c, Hc).
  rewrite Hc, Nat.mul_comm, Nat.div_mul in Hmk; [ | easy ].
  rewrite Hc.
  rewrite Nat.log2_up_double.
  rewrite Nat.pow_succ_r'.
  rewrite Nat.div_mul_cancel_l; [ | | easy ].
  remember (extract_pow2_loop it c) as nc eqn:Hnc.
  symmetry in Hnc.
  destruct nc as (m', k').
  injection Hmk; clear Hmk; intros; subst m k'.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    subst n.
    symmetry in Hc.
    now apply Nat.eq_mul_1 in Hc.
  }
...
  apply IHn in Hnc.
...
  cbn - [ "/" ] in Hmk.
...
Compute (map (λ n,
  let mk := extract_pow2 n in
  let m := snd mk in
(n,
pair
(*
pair_eqb Nat.eqb Nat.eqb
*)
  (rank_fst_loop m 0 (2 ^ Nat.log2_up m) m)
  (rank_fst_loop n 0 (2 ^ Nat.log2_up n) n)
)
) (seq 0 20)).
...
(* essayer de voir la sémantique de
     fst (rank_fst_loop m 0 (2 ^ Nat.log2_up m) m)
   et de son copain *)
...
Search (fst (rank_fst_loop _ 0 (2 ^ _) _)).
Search (snd (rank_fst_loop _ 0 (2 ^ _) _)).
...
specialize (le_fst_rank_fst_loop (Nat.log2_up m)) as H1.
specialize (H1 (m - Nat.log2_up m)).
rewrite Nat.add_sub_assoc in H1.
rewrite Nat.add_comm, Nat.add_sub in H1.
...
le_fst_rank_fst_loop:
  ∀ m n : nat, 2 ^ m - 2 * m < 2 * n → m + n ≤ 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n)))
pow2_snd_rank_fst_loop_le:
  ∀ m n : nat,
    2 ^ m / 2 - m < n
    → snd (rank_fst_loop n 1 (2 ^ m) (m + n)) < m + n → 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n))) ≤ m + n
...
assert (snd (rank_fst_loop m 1 1 m) = 1).
...
assert (snd (rank_fst_loop n 1 1 n) = 2 ^ k).
...
do 2 rewrite fst_1_len_log2_up.
f_equal.
Print inv_ub_num.
... ...
Compute (map (λ n,
   Nat.eqb (inv_ub_num (snd (extract_pow2 n))) (inv_ub_num n)
) (seq 0 50)).
Compute (map (λ n,
  Nat.eqb (fst_1_len 1 (snd (extract_pow2 n))) (fst_1_len 1 n)
) (seq 0 200)).
(* ok *)
Compute (map (λ n,
let kn1 :=
  rank_fst_loop (snd (extract_pow2 n)) 0
    (snd (rank_fst_loop (snd (extract_pow2 n)) 1 1 (snd (extract_pow2 n))))
    (snd (extract_pow2 n)) in
let kn2 := rank_fst_loop n 0 (snd (rank_fst_loop n 1 1 n)) n in
pair (snd kn1) (snd kn2)
) (seq 0 50)).
(* non *)
... ...
apply (le_trans _ (2 ^ (Nat.log2_up n + Nat.log2_up (inv_ub_num m) - 1))). {
  apply Nat.pow_le_mono_r; [ easy | ].
  apply Nat.sub_le_mono_r.
  apply Nat.add_le_mono_l.
  apply Nat.log2_up_le_mono.
  clear - m.
assert (m mod 2 = 1) by admit.
  subst m.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
  replace n with (S (n - 1)) at 2 by flia Hnz.
  cbn - [ "*" "/" "mod" "^" ].
  replace (S (n - 1)) with n by flia Hnz.
  rewrite snd_if, snd_let.
  cbn - [ "*" "/" "mod" "^" ].
  remember (n mod 2 =? 0) as n2 eqn:Hn2.
  symmetry in Hn2.
  destruct n2; [ | easy ].
  apply Nat.eqb_eq in Hn2.
...
  apply Nat.mod_divides in Hn2; [ | easy ].
  destruct Hn2 as (m, Hm).
  rewrite Hm at 2.
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
...
clear i Hin Hni.
clear Hn1.
Compute (binary_div 10 1 7).
Compute (map (λ n,
  (n, extract_pow2 n)
) (seq 0 50)).
Compute (map (λ n,
  Nat.leb (inv_ub_num n) (2 * n)
) (seq 0 50)).
(* oui *)
Compute (map (λ n,
  (Nat.leb (snd (extract_pow2 n)) n)
) (seq 0 30)).
(* toujours inférieur à n, normal *)
Compute (map (λ n,
  Nat.leb (inv_ub_num n) (2 ^ (snd (extract_pow2 n)) + 1)
) (seq 0 20)).
(* oui, il semble, mais on ne peut pas aller loin *)
Compute (map (λ a, (a, map (λ b,
  let na := Nat.log2_up a in
  let nb := Nat.log2_up b in
  if a =? 2 ^ na - 1 then
  if a <=? 2 * b then
  Nat.b2n (
    (Nat.ltb (2 ^ (na + nb - 1)) (a * b)) &&
    (Nat.leb (a * b) (2 ^ (na + nb))))
  else 1
  else 1
) (seq 0 20))) (seq 0 10)).
(* pas ok *)
(* (a,b) (3,5) ne fonctionne pas *)
...
inv_ub_num n
  1/n = 0.0000011110
  fst_1_len 1 n = 4
  inv_ub_num n = 31
  (* enfin, je crois : ce serait pas mal de vérifier avec binary_div *)
...
Print fst_1_len.
destruct n; [ easy | ].
destruct n; [ cbn; flia | ].
cbn - [ "*" "^" ].
...
progress unfold inv_ub_num.
progress unfold fst_1_len.
remember (rank_fst_loop n 0) as x.
replace n with (S (n - 1)) at 2 6 by flia Hnz.
cbn - [ "*" "/" "mod" "^" ].
rewrite snd_if, snd_let.
cbn - [ "*" "/" "mod" "^" ].
rewrite Nat.div_small; [ | flia Hnz Hn1 ].
rewrite Nat.mod_small; [ | flia Hnz Hn1 ].
cbn - [ "*" "/" "mod" "^" ].
rewrite Nat.mul_1_r.
specialize (snd_rank_fst_loop 0) as H1.
cbn in H1.
replace (S (n - 1)) with n by flia Hnz Hn1.
rewrite H1; [ | flia | flia Hnz Hn1 ].
(* mmm... ça devient trop compliqué *)
...
Theorem Geoffroy_2 :
  ∀ a b na nb,
  1 < a
  → 1 < b
  → na = Nat.log2_up a
  → nb = Nat.log2_up b
  → a = 2 ^ na - 1
  → a ≤ 2 * b
  → 2 ^ (na + nb - 1) < a * b ≤ 2 ^ (na + nb).
Proof.
intros * H1a H1b Hna Hnb Hnaa Hnba.
specialize (Nat.log2_up_spec _ H1a) as Ha.
specialize (Nat.log2_up_spec _ H1b) as Hb.
rewrite <- Hna in Ha.
rewrite <- Hnb in Hb.
rewrite pred_of_minus in Ha, Hb.
specialize (Geoffroy_1 a b na nb H1a H1b Hna Hnb) as H1.
split; [ | easy ].
(* faux, en fait, il y a des contre exemples *)
...
assert (H1a : 1 < inv_ub_num n). {
  apply inv_ub_num_gt_1.
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  now apply -> Nat.succ_lt_mono.
}
assert (H1n : 1 < n) by flia Hn1 Hnz.
rewrite Nat.add_comm.
apply Nat.lt_le_incl.
(*
Print inv_ub_num.
Compute (map (λ n,
  Nat.leb
    ((inv_ub_num n + 1) / 2) n
) (seq 0 200)).
Compute (map (λ n,
  Nat.leb
    ((inv_ub_num n + 1)) (2 * n)
) (seq 0 200)).
...
a = inv_ub_num n
b = n
...
a ≤ 2 * b
...
Compute (map (λ n,
  pair (inv_ub_num n) (2 ^ S (Nat.log2_up n) - 1)
) (seq 0 20)).
*)
(**)
remember (Nat.log2_up (inv_ub_num n)) as na eqn:Hna.
remember (Nat.log2_up n) as nb eqn:Hnb.
remember (inv_ub_num n) as a eqn:Ha.
remember n as b eqn:Hb.
move a before n.
move b before a.
move na before b.
move nb before na.
(* (a,b) = (3,5) n'est pas censé marcher *)
rewrite Hna, Hnb.
replace a with 3.
replace b with 5.
cbn.
(* donc, c'est bien ça ; c'est faux *)
...
apply Geoffroy_2; [ easy | easy | easy | easy | | ].
rewrite Hna, Ha.
progress unfold inv_ub_num.
f_equal.
f_equal.
rewrite fst_1_len_log2_up.
rewrite Nat_log2_up_pow2_sub_1; [ easy | ].
Search (S (_ - S _)).
rewrite <- Nat_succ_sub_succ_r.
rewrite Nat_sub_succ_1.
...
Check Geoffroy_2.
...
apply Geoffroy_2; [ easy | easy | easy | easy | | ].
Compute (map (λ n,
  Nat.eqb (inv_ub_num n) (2 ^ Nat.log2_up (inv_ub_num n) - 1)
) (seq 0 200)).
Compute (map (λ n,
  Nat.leb (inv_ub_num n) (2 * n)
) (seq 0 200)).
(*
Check Geoffroy_1.
Compute (map (λ a, (a, map (λ b,
  let na := Nat.log2_up a in
  let nb := Nat.log2_up b in
  Nat.b2n (
    Nat.ltb (2 ^ (na + nb - 2)) (a * b) &&
    Nat.leb (a * b) (2 ^ (na + nb)))
) (seq 0 20))) (seq 0 10)).
(* ok *)
*)
Check Geoffroy_2.
Compute (map (λ a, (a, map (λ b,
  let na := Nat.log2_up a in
  let nb := Nat.log2_up b in
  if a =? 2 ^ na - 1 then
  if a <=? 2 * b then
  Nat.b2n (
    (Nat.ltb (2 ^ (na + nb - 1)) (a * b)) &&
    (Nat.leb (a * b) (2 ^ (na + nb))))
  else 1
  else 1
) (seq 0 20))) (seq 0 10)).
(* pas ok *)
(* (a,b) (3,5) ne fonctionne pas *)
Check Geoffroy_2.
Compute
  (let a := 3 in let b := 5 in
   let na := Nat.log2_up a in
   let nb := Nat.log2_up b in
   (
    (Nat.eqb a (2 ^ na - 1),
     Nat.leb a (2 * b)),
     2 ^ (na + nb - 1) < a * b ≤ 2 ^ (na + nb))).
...
Compute (map (λ a, (a, map (λ b,
  let na := Nat.log2_up a in
  let nb := Nat.log2_up b in
  Nat.b2n (
    (Nat.leb (2 ^ (na + nb - 1)) (a * b)) &&
    (Nat.leb (a * b) (2 ^ (na + nb))))
) (seq 0 20))) (seq 0 20)).
...
a = inv_ub_num n
b = n
...
(**)
  rewrite Nat.pow_sub_r; [ | easy | ]. 2: {
    apply Nat.neq_0_lt_0.
    intros H.
    apply Nat.eq_add_0 in H.
    destruct H as (H, _).
    apply Nat.log2_up_null in H.
    destruct n; [ easy | ].
    destruct n; [ easy | ].
    now apply Nat.succ_le_mono in H.
  }
  rewrite Nat.pow_1_r.
  apply Nat.div_le_upper_bound; [ easy | ].
(**)
...
specialize (H1 eq_refl).
assert (H : 2 ^ (Nat.log2_up n - 1) < inv_ub_num n). {
Compute (map (λ n,
  Nat.ltb
    (2 ^ (Nat.log2_up n - 1)) (inv_ub_num n)
) (seq 0 40)).
(* chiasse *)
...
progress unfold inv_ub_num in H1 at 1.
Search fst_1_len.
rewrite fst_1_len_log2_up in H1.
Search (Nat.log2_up (2 ^ _ - _)).
...
Theorem Nat_log2_up_mul :
  ∀ a b,
  (a = 0 ↔ b = 0)
  → Nat.log2_up a + Nat.log2_up b = Nat.log2_up (a * b).
Proof.
intros * Hab.
destruct (le_dec a 1) as [H1a| H1a]. {
  destruct a; [ now cbn; rewrite (proj1 Hab) | ].
  destruct a; [ now cbn; rewrite Nat.add_0_r | ].
  now apply Nat.succ_le_mono in H1a.
}
destruct (le_dec b 1) as [H1b| H1b]. {
  destruct b; [ now cbn; rewrite (proj2 Hab) | ].
  destruct b; [ now rewrite Nat.mul_1_r, Nat.add_0_r | ].
  now apply Nat.succ_le_mono in H1b.
}
apply Nat.nle_gt in H1a, H1b.
apply Nat.le_antisymm; [ | now apply Nat.log2_up_mul_above ].
...
apply (Nat.pow_le_mono_r_iff 2); [ easy | ].
rewrite Nat.pow_add_r.
eapply le_trans. 2: {
  apply Nat.log2_up_spec.
  apply Nat.lt_1_mul_pos; [ flia Haz Ha1 | flia Hbz ].
}
(* ah bin non *)
...
  apply Nat.pow_le_mono_r; [ easy | ].
Search (Nat.log2_up (_ * _)).
Search (2 ^ Nat.log2_up _).
...
eapply le_trans. 2: {
  apply Nat.log2_up_spec.
...
}
Nat.log2_up_spec: ∀ a : nat, 1 < a → 2 ^ Nat.pred (Nat.log2_up a) < a ≤ 2 ^ Nat.log2_up a
...
Search (_ ^ Nat.log2_up _).
Search (_ ^ (_ * _)).
rewrite Nat.pow_mul_r.
(* cf Theorem glop below for all the comment and the analysis I've made *)
... ...
rewrite Nat_log2_up_mul.
Compute (map (λ n,
  Nat.leb
  (2 ^ Nat.log2_up (n * inv_ub_num n)) (2 * (inv_ub_num n * n))
) (seq 0 50)).
(* vrai *)
Check Nat.log2_up_spec.
  apply
    (Nat.le_trans _ (2 * 2 ^ Nat.pred (Nat.log2_up (inv_ub_num n * n)))). 2: {
    apply Nat.mul_le_mono_l.
    apply Nat.lt_le_incl.
    apply Nat.log2_up_spec.
    eapply (lt_le_trans _ n); [ flia Hnz Hn1 | ].
    rewrite Nat.mul_comm.
    apply Nat_mul_le_pos_r.
    apply Nat.neq_0_lt_0.
    progress unfold inv_ub_num.
    intros H.
    apply Nat.sub_0_le in H.
    apply Nat.le_1_r in H.
    destruct H as [H| H]; [ now apply Nat.pow_nonzero in H | ].
    apply Nat_eq_pow_1 in H.
    now destruct H.
  }
  rewrite <- Nat.pow_succ_r'.
  rewrite Nat.succ_pred. 2: {
    intros H.
    apply Nat.log2_up_null in H.
    apply Nat.le_1_r in H.
    destruct H as [H| H]. {
      apply Nat.eq_mul_0 in H.
      destruct H as [H| H]; [ | easy ].
      progress unfold inv_ub_num in H.
      apply Nat.sub_0_le in H.
      apply Nat.le_1_r in H.
      destruct H as [H| H]; [ now apply Nat.pow_nonzero in H | ].
      apply Nat_eq_pow_1 in H.
      now destruct H.
    }
    now apply Nat.eq_mul_1 in H.
  }
  now rewrite Nat.mul_comm.
}
...
Check Nat.log2_up_spec.
rewrite <- (Nat_sub_succ_1 (Nat.log2_up _)).
eapply le_trans. {
  rewrite <- pred_of_minus.
  apply Nat.lt_le_incl.
  apply Nat.log2_up_spec.
  ...
}
rewrite Nat.pred_succ.
rewrite Nat.log2_up_succ_pow2; [ | easy ].
rewrite Nat.pow_succ_r'.
apply Nat.mul_le_mono_l.
Search (2 ^ Nat.log2_up _).
...
Compute (map (λ n,
  Nat.leb
    (2 ^ (Nat.log2_up n + Nat.log2_up (inv_ub_num n)))
    (2 * (inv_ub_num n * n))
) (seq 0 50)).
(* ça a l'air vrai, sauf pour n=0, mais ce cas-là, c'est pas grave *)
Print inv_ub_num.
(* mais si on fait la méthode suivante, ça ne marche plus *)
  apply (le_trans _ (2 ^ S (Nat.log2_up (n * inv_ub_num n)))). {
    apply Nat.pow_le_mono_r; [ easy | ].
    apply Nat.log2_up_mul_below; [ flia Hnz | ].
    apply Nat.neq_0_lt_0.
    intros H.
    progress unfold inv_ub_num in H.
    apply Nat.sub_0_le in H.
    apply Nat.le_1_r in H.
    destruct H as [H| H]; [ now apply Nat.pow_nonzero in H | ].
    apply Nat_eq_pow_1 in H.
    now destruct H.
  }
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_le_mono_l.
Compute (map (λ n,
  Nat.leb
  (2 ^ Nat.log2_up (n * inv_ub_num n)) (inv_ub_num n * n)
) (seq 0 30)).
(* ah bin non, c'est faux, on est d'accord *)
...
progress unfold inv_ub_num.
rewrite Nat_log2_up_pow2_sub_1.
rewrite Nat.pow_add_r.
rewrite Nat.mul_assoc.
...
Compute (map (λ n,
  Nat.leb
    (2 ^ (Nat.log2_up n + Nat.log2_up (inv_ub_num n))) (2 * (inv_ub_num n * n))
) (seq 0 60)).
(* ok, si n≠0 *)
Compute (map (λ n,
Nat.eqb
(
  Nat.add
    (Nat.log2_up n)
    (Nat.log2_up (inv_ub_num n))
) (
  Nat.log2_up
    (n * inv_ub_num n)
)
) (seq 0 130)).
(* ah bin ils ont même l'air égaux ! *)
Compute (map (λ n,
    (n * inv_ub_num n)
) (seq 0 40)).
(*
Search inv_ub_num.
progress unfold inv_ub_num at 1.
Search (Nat.log2_up _ + Nat.log2_up _).
Search (Nat.log2 _ + Nat.log2 _).
*)
Search (Nat.log2_up (_ - _)).
...
Theorem glop :
  ∀ a b, (a = 0 ↔ b = 0) → Nat.log2_up a + Nat.log2_up b = Nat.log2_up (a * b).
Proof.
intros * (Hab, Hba).
(* c'est pas toujours vrai, if faut une condition, laquelle a l'air
   vraie dans notre cas, mais pourquoi ? *)
(* inv_ub_num est une (puissance de 2) moins 1 *)
apply Nat.le_antisymm; [ | now apply Nat.log2_up_mul_above ].
(*
Compute (map (λ a, (a, map (λ b,
  Nat.b2n (
  Nat.eqb (Nat.log2_up a + Nat.log2_up b) (Nat.log2_up (a * b))
)
) (seq 0 35))) (seq 0 35)).
Compute (map (λ a, (a, map (λ b,
  if b =? inv_ub_num a then 3
  else
    Nat.b2n (
    Nat.eqb (Nat.log2_up a + Nat.log2_up b) (Nat.log2_up (a * b)))
) (seq 0 35))) (seq 0 35)).
Compute (map (λ n,
pair
    n
    (inv_ub_num n)
) (seq 0 130)).
Compute (map (λ n,
(
    (Nat.log2_up n)
,
    (Nat.log2_up (inv_ub_num n))
,
    (Nat.log2_up (n * inv_ub_num n))
)
) (seq 0 130)).
*)
Print inv_ub_num.
Search (Nat.log2_up (_ + _)).
Search (Nat.log2_up (_ - _)).
...
Nat_log2_up_pow2_sub_1: ∀ n : nat, n ≠ 1 → Nat.log2_up (2 ^ n - 1) = n
log2_up (inv_ub_num n) = log2_up (2 ^ (p + 1) - 1) = p + 1
...
n * inv_ub_num n = n * (2 ^ (p + 1) - 1) = n * 2 ^ (p+1) - n
log2_up (n * inv_ub_num n) = l2u (n * (2 ^ (p + 1) - 1)) =
  (log2_up (n * 2 ^ (p+1) - n))
...
inv_ub_num n est une "puissance de 2" moins 1
...
vrai si a est une puissance de 2
a≥9 faux (0) si
   b≥3 (a-9)+(b-3)=i     0≤i≤0
   b≥5 (a-9)+(b-5)=i     0≤i≤2
   b≥9 (a-9)+(b-9)=i     0≤i≤4
   a=9 b=14
   b≥17 (a-9)+(b-17)=i   0≤i≤6
   a=9 24≤b≤28
   b≥33 ...
...
    0 1 2 3 4 5 6 7 8 9  11  13  15  17  19  21  23  25  27  29  31  33
                       10  12  14  16  18  20  22  24  26  28  30  32  34

0   1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
1   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
2   0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
3   0 1 1 1 1 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 0 0
4   0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
5   0 1 1 0 1 0 0 1 1 0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 0 0
6   0 1 1 1 1 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 0 0
7   0 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
8   0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
9   0 1 1 0 1 0 0 0 1 0 0 0 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 0 0
10  0 1 1 0 1 0 0 1 1 0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 0 0
11  0 1 1 1 1 0 1 1 1 0 0 0 1 1 1 1 1 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 0 0
12  0 1 1 1 1 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 0 0
13  0 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
14  0 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
15  0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
16  0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
17  0 1 1 0 1 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0
18  0 1 1 0 1 0 0 0 1 0 0 0 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 0 0
19  0 1 1 0 1 0 0 1 1 0 0 0 0 0 1 1 1 0 0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 0 0
20  0 1 1 0 1 0 0 1 1 0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 0 0
21  0 1 1 0 1 0 0 1 1 0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 0 0
22  0 1 1 1 1 0 1 1 1 0 0 0 1 1 1 1 1 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 0 0
23  0 1 1 1 1 0 1 1 1 0 0 0 1 1 1 1 1 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 0 0
24  0 1 1 1 1 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 0 0
25  0 1 1 1 1 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 0 0
26  0 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
27  0 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
28  0 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
29  0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
30  0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
31  0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1
32  0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
33  0 1 1 0 1 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0
34  0 1 1 0 1 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0
...
    0 1 2 3 4 5 6 7 8 9  11  13  15  17  19  21  23  25  27  29  31  33
                       10  12  14  16  18  20  22  24  26  28  30  32  34

0   1 3 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
1   1 1 1 3 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
2   0 1 1 3 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
3   0 1 1 3 1 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 0 0
4   0 1 1 3 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
5   0 1 1 0 1 0 0 3 1 0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 0 0
6   0 1 1 3 1 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 0 0
7   0 1 1 3 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
8   0 1 1 3 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
9   0 1 1 0 1 0 0 0 1 0 0 0 0 0 0 3 1 0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 0 0
10  0 1 1 0 1 0 0 3 1 0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 0 0
11  0 1 1 3 1 0 1 1 1 0 0 0 1 1 1 1 1 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 0 0
12  0 1 1 3 1 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 0 0
13  0 1 1 3 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
14  0 1 1 3 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
15  0 1 1 3 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
16  0 1 1 3 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
17  0 1 1 0 1 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3 1 0 0
18  0 1 1 0 1 0 0 0 1 0 0 0 0 0 0 3 1 0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 0 0
19  0 1 1 0 1 0 0 3 1 0 0 0 0 0 1 1 1 0 0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 0 0
20  0 1 1 0 1 0 0 3 1 0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 0 0
21  0 1 1 0 1 0 0 3 1 0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 0 0
22  0 1 1 3 1 0 1 1 1 0 0 0 1 1 1 1 1 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 0 0
23  0 1 1 3 1 0 1 1 1 0 0 0 1 1 1 1 1 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 0 0
24  0 1 1 3 1 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 0 0
25  0 1 1 3 1 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 0 0
26  0 1 1 3 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
27  0 1 1 3 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
28  0 1 1 3 1 1 1 1 1 0 1 1 1 1 1 1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
29  0 1 1 3 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
30  0 1 1 3 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
31  0 1 1 3 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1
32  0 1 1 3 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
33  0 1 1 0 1 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0
34  0 1 1 0 1 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3 1 0 0
...
apply Nat.nlt_ge.
intros H1.
...
destruct a; [ now rewrite Hab | clear Hab ].
cbn.
destruct a; [ now rewrite Nat.add_0_r | ].
destruct a. {
  cbn; rewrite Nat.add_0_r.
  rewrite Nat_add_diag.
  rewrite Nat.log2_up_double; [ easy | ].
  apply Nat.neq_0_lt_0.
  intros H.
  now specialize (Hba H).
}
destruct a. {
  cbn.
  rewrite Nat.add_0_r.
  destruct b; [ now specialize (Hba eq_refl) | clear Hba ].
  cbn.
...
Search (Nat.log2_up _ + Nat.log2_up _).
  eapply le_trans. {
    apply Nat.pow_le_mono_r; [ easy | ].
    apply Nat.log2_up_mul_below; [ flia Hnz | ].
    apply Nat.neq_0_lt_0.
    intros H.
    progress unfold inv_ub_num in H.
    apply Nat.sub_0_le in H.
    apply Nat.le_1_r in H.
    destruct H as [H| H]; [ now apply Nat.pow_nonzero in H | ].
    apply Nat_eq_pow_1 in H.
    now destruct H.
  }
Compute (map (λ n,
  Nat.leb
    (2 ^ S (Nat.log2_up (n * inv_ub_num n)))
    (2 * (inv_ub_num n * n))
) (seq 0 30)).
(* plus ok *)
...
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_le_mono_l.
(* ah bin non, c'est faux, ça, c'est le contraire ! *)
...
Check lt_snd_rank_fst_loop.
Search (_ < snd _).
Compute (map (λ n,
  Nat.ltb n (snd (rank_fst_loop (S n) 1 1 (S n)))
) (seq 0 20)).
(* a l'air bon *)
...
Print rank_fst_loop.
Compute (map (λ n,
  fst_1_len 1 n
) (seq 1 40)).

      rewrite fst_1_len_log2_up in H.
      apply Nat.sub_0_le in H.
      apply Nat.le_1_r in H.
      progress unfold inv_ub_num in H.
      destruct H as [H| H]. {
        apply Nat.log2_up_null in H.
        apply Nat.le_sub_le_add_r in H.
        cbn - [ "^" ] in H.
        rewrite <- (Nat.mul_1_r 2) in H at 2.
        rewrite Nat.pow_succ_r' in H.
        apply Nat.mul_le_mono_pos_l in H; [ | easy ].
        apply Nat.le_1_r in H.
        destruct H as [H| H]; [ now apply Nat.pow_nonzero in H | ].
        apply Nat_eq_pow_1 in H.
        destruct H; [ easy | ].
(**)
(* ça tourne en rond *)
...
  H : fst_1_len 1 n = 0
  ============================
  False
...
        rewrite fst_1_len_log2_up in H.
        apply Nat.sub_0_le in H.
        apply Nat.le_1_r in H.
        progress unfold inv_ub_num in H.
        destruct H as [H| H]. {
          apply Nat.log2_up_null in H.
          apply Nat.le_sub_le_add_r in H.
...
  H : 2 ^ S (fst_1_len 1 n) ≤ 1 + 1
  ============================
  False
...
        progress unfold fst_1_len in H.
        destruct n; [ easy | cbn in H ].
destruct n; [ easy | cbn in H ].
Search (fst_1_len _ _ = 0).
    }
...
      destruct H as [H| H]; [ now apply Nat.pow_nonzero in H | ].
      apply Nat_eq_pow_1 in H.
      now destruct H.
...
  rewrite Nat.pow_sub_r; [ | easy | ].
  rewrite Nat.pow_1_r.
  apply Nat.div_le_upper_bound; [ easy | ].
  Search (Nat.log2_up _ ≤ Nat.log2_up _).
  apply Nat.lt_le_incl.
  Search (Nat.log2_up _ < Nat.log2_up _).
  apply Nat.log2_up_lt_cancel.
  rewrite Nat.log2_up_pow2.
  eapply le_lt_trans.
  Search (Nat.log2_up _ + Nat.log2_up _).
apply Nat.log2_up_mul_below; [ flia Hnz | ].
...
  progress unfold inv_ub_num.
  progress unfold inv_ub_den_pow2.
  rewrite fst_1_len_log2_up.
  rewrite rank_fst_1_log2_up.
  remember (inv_ub_num n) as a eqn:Ha.
  rewrite Nat.add_sub_assoc.
  apply (le_trans _ (2 ^ Nat.log2_up (n * a - 1))). {
    apply Nat.pow_le_mono_r; [ easy | ].
progress unfold inv_ub_num in Ha.
rewrite fst_1_len_log2_up in Ha.
(* bon, chais pas, chuis parti en couille, là *)
...
    apply (le_trans _ (Nat.log2_up n + Nat.log2_up a)); [ flia | ].
...
  rewrite <- Nat.sub_succ_l.
  rewrite Nat_sub_succ_1.
...
  rewrite Nat.pow_add_r.
  rewrite Nat.mul_comm.


Search (2 ^ Nat.log2_up _).
rewrite <-
  rewrite Nat.pow_add_r.
...
Search (fst (rank_fst_loop _ _ _ _) = 0).
Search (fst_1_len _ _ = 0).
...
specialize (H2 (2 ^ n - 1)).
destruct n; [ easy | ].
destruct n; [ easy | clear Hn1 ].
assert (H : 0 < 2 ^ S (S n) - 1) by ...
specialize (H2 H); clear H.
destruct H2 as (H2, H3).
apply Nat.succ_le_mono in H3.
rewrite H1 in H3.
...
apply Nat.succ_inj.
rewrite <- H1.
rewrite <- Nat.sub_succ_l. 2: {
  apply Nat.neq_0_lt_0.
  now apply Nat.pow_nonzero.
}
rewrite Nat_sub_succ_1.
Search (Nat.log2_up (2 ^ _)).
rewrite Nat.log2_up_pow2; [ | easy ].
...
apply (Nat.pow_inj_r 2); [ easy | ].
apply Nat_pow2_log2_up_succ in H1.
Search (_ ^ _ = _ ^ _).
...
apply Nat.succ_inj.
rewrite <- H1.
Check Nat_pow2_log2_up_succ.
...
Search (Nat.log2_up _ = Nat.log2_up _).
apply Nat.log2_up_same.
...
apply Nat.le_antisymm. 2: {
Search (_ ≤ Nat.log2_up _).
...
intros * Hn1.
induction n; intros; [ easy | ].
rewrite Nat.pow_succ_r'.
rewrite <- Nat_add_diag.
rewrite <- Nat.add_sub_assoc. 2: {
  apply Nat.neq_0_lt_0.
  now apply Nat.pow_nonzero.
}
apply Nat.le_antisymm. {
  eapply le_trans.
  apply Nat.log2_up_add_le.
...
destruct n; [ easy | clear Hn1 ].
...
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
...
  remember (inv_ub_num n) as m eqn:Hm.
  symmetry in Hm.
  destruct m. {
    cbn.
    progress unfold inv_ub_num in Hm.
    apply Nat.sub_0_le in Hm.
    apply Nat.le_1_r in Hm.
    destruct Hm as [Hm| Hm]; [ now apply Nat.pow_nonzero in Hm | ].
    cbn in Hm; flia Hm.
  }
  rewrite <- Hm.
  progress unfold inv_ub_num.
...
  specialize (Nat.log2_up_succ_or m) as H1.
  destruct H1 as [H1| H1]. {
progress unfold inv_ub_num in Hm.
...
    rewrite H1.
    apply Nat_pow2_log2_up_succ in H1.
Search ( 2 ^ Nat.log2 _).
...
...
Compute (map (λ n,
(n,
  Nat.leb (2 ^ inv_ub_den_pow2 n) (inv_ub_num n * n)
)
) (seq 0 30)).
(* a l'air toujours vrai, à condition que n ≠ 0 *)
...
  progress unfold inv_ub_den_pow2.
  progress unfold inv_ub_num.
rewrite rank_fst_1_log2_up.
...
Compute (map (λ n,
  let m := Nat.log2_up n in
(n,
  2 ^ (rank_fst_1 1 n + m) ≤ (2 ^ S m - 1) * n
)
) (seq 1 15)).
Compute (map (λ n,
(n,
Nat.leb (fst_1_len 1 n)
(Nat.log2 n)
)
) (seq 2 30)).
Print fst_1_len.
Compute (map (λ n,
  Nat.leb
  (2 ^ (rank_fst_1 1 n + fst_1_len 1 n))
  ((2 ^ S (Nat.log2  n) - 1) * n)
) (seq 1 20)).
(* oui mais non, il faudrait que Nat.log2 n ≤ fst_1_len 1 n *)
...
Search rank_fst_1.
rewrite rank_fst_1_log2_up.
clear i Hin Hni.
...
(*
  rewrite rank_fst_1_log2_up.
*)
  rewrite Nat.pow_add_r.
  rewrite Nat.mul_sub_distr_r.
  rewrite Nat.mul_1_l.
  apply Nat.le_add_le_sub_r.
(**)
  clear - Hnz.
  progress unfold rank_fst_1.
  progress unfold fst_1_len.
  destruct n; [ easy | clear Hnz ].
  cbn - [ "-" "*" "/" "mod" "^" ].
  do 2 rewrite fst_if, fst_let.
  rewrite snd_if, snd_let.
  cbn - [ "-" "*" "/" "mod" "^" ].
  remember (1 / S n =? 1) as n1 eqn:Hn1.
  symmetry in Hn1.
  destruct n1. {
    cbn - [ "-" "*" "/" "mod" ].
    apply Nat.eqb_eq in Hn1.
    apply Nat_eq_div_1 in Hn1.
    replace n with 0 by flia Hn1.
    cbn; flia.
  }
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
  rewrite Nat.mod_small; [ | easy ].
  apply Nat.succ_lt_mono in Hn1.
  rename Hn1 into Hn.
  rewrite Nat.mul_1_r.
  rewrite (Nat_mod_less_small 1). 2: {
    rewrite Nat.mul_1_l.
    now apply (snd_rank_fst_loop_interval 1).
  }
  rewrite Nat.mul_1_l.
  remember (snd _ / _ =? 0) as n1 eqn:Hn1.
  symmetry in Hn1.
  destruct n1. {
    apply Nat.eqb_eq in Hn1.
    apply Nat.div_small_iff in Hn1; [ | easy ].
    cbn - [ "*" ].
    do 2 rewrite Nat.mul_1_r.
    rewrite <- (Nat_add_diag (S n)).
    apply Nat.add_le_mono_r.
    rewrite <- Nat.pow_succ_r'.
    now apply (pow2_snd_rank_fst_loop_le 1).
  }
  clear Hn1.
  rewrite <- Nat.pow_add_r.
  rewrite Nat.add_succ_l.
  rewrite (Nat.add_succ_r (fst _)).
  rewrite snd_rank_fst_1_2_succ; [ | easy | easy ].
  remember (rank_fst_loop n 1 2 (S n)) as x.
  remember (fst (rank_fst_loop _ _ _ _)) as y.
Compute (map (λ n,
  2 ^ Nat.log2_up n - n
) (seq 0 20)).
...
Search (2 ^ S _).
specialize fst_rank_fst_loop_eq_succ as H1.
rewrite <- H1.
specialize fst_rank_fst_loop_eq_succ_lemma as H1.
...
Compute (map (λ n,
(
  Nat.leb (S n) (snd (rank_fst_loop n 1 2 (S n))) &&
  Nat.leb (snd (rank_fst_loop n 1 2 (S n))) ((1 + 1) * S n)
)%bool
) (seq 1 40)).
...
  apply Nat_le_add_le_sub_l. {
    rewrite Nat.pow_succ_r'.
    rewrite Nat.mul_shuffle0.
    apply Nat.mul_le_mono_r.
(*
    clear Hn1 Hin Hni.
*)
    specialize (Nat.log2_up_succ_or n) as H1.
    destruct H1 as [H1| H1]. {
      apply Nat_pow2_log2_up_succ in H1.
      rewrite <- H1 at 2.
      rewrite <- Nat.pow_succ_r'.
      apply Nat.pow_le_mono_r; [ easy | ].
      rewrite rank_fst_1_log2_up.
      apply Nat.le_log2_up_succ_log2.
    }
    destruct n; [ easy | clear Hnz ].
    cbn in H1.
    rewrite rank_fst_1_log2_up.
    rewrite <- H1.
    rewrite Nat.pow_succ_r'.
    apply Nat.mul_le_mono_l.
    specialize (Nat.log2_iter_spec n 0 1 0) as H2.
    specialize (H2 eq_refl (Nat.lt_0_succ _)).
    remember (Nat.log2_iter n 0 1 0) as x eqn:Hx.
    cbn in H2.
    now rewrite <- (Nat.add_1_r n).
  }
  clear.
(*
Compute (map (λ n,
  Nat.leb n (2 ^ S (fst_1_len 1 n) * n - 2 ^ rank_fst_1 1 n * 2 ^ fst_1_len 1 n))
(seq 0 40)).
*)
  rewrite Nat.mul_comm.
  rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_assoc.
  rewrite <- Nat.mul_sub_distr_r.
(**)
rewrite Nat.mul_sub_distr_r.
apply Nat.le_add_le_sub_r.
...
  rewrite (Nat.mul_comm n).
  progress unfold rank_fst_1.
  progress unfold fst_1_len.
(*
  ============================
  n ≤ (2 * n - 2 ^ fst (rank_fst_loop n 1 1 n)) * 2 ^ fst_1_len 1 n
*)
  destruct n; [ easy | ].
  cbn - [ "-" "*" "/" "mod" ].
  remember (1 / S n =? 1) as n1 eqn:Hn1.
  symmetry in Hn1.
  destruct n1. {
    apply Nat.eqb_eq in Hn1.
    apply Nat_eq_div_1 in Hn1.
    replace n with 0 by flia Hn1.
    cbn; flia.
  }
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
  rewrite Nat.mod_small; [ | easy ].
  apply Nat.succ_lt_mono in Hn1.
  rewrite Nat.mul_1_r.
  rename Hn1 into Hn.
  rewrite fst_let, snd_let.
  rewrite fst_if, fst_let.
  cbn - [ "-" "*" "/" "mod" "^" ].
  remember (snd _ / S n =? 0) as n2 eqn:Hn2.
  symmetry in Hn2.
  destruct n2. {
    apply Nat.eqb_eq in Hn2.
    apply Nat.div_small_iff in Hn2; [ | easy ].
    rewrite Nat.mul_1_r.
(**)
    destruct n; [ easy | clear Hn ].
    cbn - [ "-" "*" "/" "mod" "^" ] in Hn2 |-*.
    remember (2 / S (S n) =? 1) as n1 eqn:Hn1.
    symmetry in Hn1.
    destruct n1. {
      apply Nat.eqb_eq in Hn1.
      apply Nat_eq_div_1 in Hn1.
      cbn in Hn2.
      flia Hn1 Hn2.
    }
    rewrite snd_let in Hn2.
    rewrite fst_let.
    apply Nat.eqb_neq in Hn1.
    apply Nat_neq_div_1 in Hn1.
    destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
    rewrite Nat.mod_small in Hn2; [ | easy ].
    rewrite Nat.mod_small; [ | easy ].
    do 2 apply Nat.succ_lt_mono in Hn1.
    rename Hn1 into Hn.
    progress replace (2 * 2) with 4 in Hn2 by easy.
    progress replace (2 * 2) with 4 by easy.
(**)
    destruct n; [ easy | clear Hn ].
    cbn - [ "-" "*" "/" "mod" "^" ] in Hn2 |-*.
...
    remember (2 / S (S n) =? 1) as n1 eqn:Hn1.
    symmetry in Hn1.
    destruct n1. {
      apply Nat.eqb_eq in Hn1.
      apply Nat_eq_div_1 in Hn1.
      cbn in Hn2.
      flia Hn1 Hn2.
    }
    rewrite snd_let in Hn2.
    rewrite fst_let.
    apply Nat.eqb_neq in Hn1.
    apply Nat_neq_div_1 in Hn1.
    destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
    rewrite Nat.mod_small in Hn2; [ | easy ].
    rewrite Nat.mod_small; [ | easy ].
    do 2 apply Nat.succ_lt_mono in Hn1.
    rename Hn1 into Hn.
...
Compute (map (λ n,
  snd (rank_fst_loop n 1 2 (S n)) < S n
(*
  S n ≤ 2 * S n - 2 ^ S (fst (rank_fst_loop n 1 2 (S n)))
*)
) (seq 0 12)).
...
(*
  Hn : 0 < n
  ============================
  S n ≤ (2 * S n - 2 ^ S (fst (rank_fst_loop n 1 2 (S n)))) * 2 ^ fst_1_len 1 (S n)
*)
...
(*
Theorem glop :
  ∀ m n,
  2 ^ m / 2 - m < n
  → m + n
      ≤ (2 * (m + n) - 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n)))) *
        2 ^ fst_1_len 1 (m + n).
clear T ro rp rl ac.
Admitted.
now apply (glop 1).
...
*)
  destruct n; [ easy | clear Hn ].
  cbn - [ "-" "*" "/" "mod" "^" ].
  remember (2 / S (S n) =? 1) as n1 eqn:Hn1.
  symmetry in Hn1.
  destruct n1. {
    apply Nat.eqb_eq in Hn1.
    apply Nat_eq_div_1 in Hn1.
    replace n with 0 by flia Hn1.
    cbn; flia.
  }
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
  rewrite Nat.mod_small; [ | easy ].
  progress replace (2 * 2) with 4 by easy.
  do 2 apply Nat.succ_lt_mono in Hn1.
  rename Hn1 into Hn.
  rewrite fst_let.
(*
  Hn : 0 < n
  ============================
  S (S n)
  ≤ (2 * S (S n) - 2 ^ S (fst (let (r, a') := rank_fst_loop n 1 4 (S (S n)) in (S r, a')))) *
    2 ^ fst_1_len 1 (S (S n))
*)
(*
Theorem glop :
  ∀ m n,
  2 ^ m / 2 - m < n
  → m + n
      ≤ (2 * (m + n) - 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n)))) *
        2 ^ fst_1_len 1 (m + n).
clear T ro rp rl ac.
Admitted.
now apply (glop 2).
...
*)
  destruct n; [ easy | clear Hn ].
  cbn - [ "-" "*" "/" "mod" "^" ].
  remember (4 / S (S (S n)) =? 1) as n1 eqn:Hn1.
  symmetry in Hn1.
  destruct n1. {
    apply Nat.eqb_eq in Hn1.
    apply Nat_eq_div_1 in Hn1.
    destruct Hn1 as (Hn1, _).
    do 3 apply Nat.succ_le_mono in Hn1.
    apply Nat.le_1_r in Hn1.
    destruct Hn1; subst n; cbn; flia.
  }
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
  rewrite Nat.mod_small; [ | easy ].
  progress replace (2 * 4) with 8 by easy.
  do 3 apply Nat.succ_lt_mono in Hn1.
  rename Hn1 into Hn.
  rewrite fst_let.
(*
  Hn : 1 < n
  ============================
  S (S (S n))
  ≤ (2 * S (S (S n)) - 2 ^ S (S (fst (let (r, a') := rank_fst_loop n 1 8 (S (S (S n))) in (S r, a'))))) *
    2 ^ fst_1_len 1 (S (S (S n)))
*)
(*
Theorem glop :
  ∀ m n,
  2 ^ m / 2 - m < n
  → m + n
      ≤ (2 * (m + n) - 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n)))) *
        2 ^ fst_1_len 1 (m + n).
clear T ro rp rl ac.
Admitted.
now apply (glop 3).
...
*)
  destruct n; [ easy | ].
  apply Nat.succ_lt_mono in Hn.
  cbn - [ "-" "*" "/" "mod" "^" ].
  remember (8 / S (S (S (S n))) =? 1) as n1 eqn:Hn1.
  symmetry in Hn1.
  destruct n1. {
    apply Nat.eqb_eq in Hn1.
    apply Nat_eq_div_1 in Hn1.
    destruct Hn1 as (Hn1, _).
    destruct n; [ easy | clear Hn ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn; flia | ].
    do 7 apply Nat.succ_le_mono in Hn1.
    apply Nat.le_1_r in Hn1.
(*
Time destruct Hn1; subst n; cbn.
Finished transaction in 0.456 secs (0.456u,0.s) (successful)
*)
    destruct Hn1; subst n; cbn; flia.
  }
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]. {
    destruct n; [ easy | flia Hn1 ].
  }
  rewrite Nat.mod_small; [ | easy ].
  progress replace (2 * 8) with 16 by easy.
  do 4 apply Nat.succ_lt_mono in Hn1.
  clear Hn; rename Hn1 into Hn.
  rewrite fst_let.
(*
  Hn : 4 < n
  ============================
  S (S (S (S n)))
  ≤ (2 * S (S (S (S n))) -
     2 ^ S (S (S (fst (let (r, a') := rank_fst_loop n 1 16 (S (S (S (S n)))) in (S r, a')))))) *
    2 ^ fst_1_len 1 (S (S (S (S n))))
*)
(*
Theorem glop :
  ∀ m n,
  2 ^ m / 2 - m < n
  → m + n
      ≤ (2 * (m + n) - 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n)))) *
        2 ^ fst_1_len 1 (m + n).
clear T ro rp rl ac.
Admitted.
now apply (glop 4).
...
*)
  destruct n; [ easy | ].
  apply Nat.succ_lt_mono in Hn.
  cbn - [ "-" "*" "/" "mod" "^" ].
  remember (16 / S (S (S (S (S n)))) =? 1) as n1 eqn:Hn1.
  symmetry in Hn1.
  destruct n1. {
    apply Nat.eqb_eq in Hn1.
    apply Nat_eq_div_1 in Hn1.
    destruct Hn1 as (Hn1, _).
    destruct n; [ easy | apply Nat.succ_lt_mono in Hn ].
    destruct n; [ easy | apply Nat.succ_lt_mono in Hn ].
    destruct n; [ easy | apply Nat.succ_lt_mono in Hn ].
    destruct n; [ easy | clear Hn ].
    do 9 apply Nat.succ_le_mono in Hn1.
    do 8 (destruct n; [ cbn; flia | ]).
    flia Hn1.
  }
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]. {
    destruct n; [ easy | ].
    destruct n; [ flia Hn | ].
    destruct n; [ flia Hn | ].
    destruct n; [ flia Hn | flia Hn1 ].
  }
  rewrite Nat.mod_small; [ | easy ].
  progress replace (2 * 16) with 32 by easy.
  do 5 apply Nat.succ_lt_mono in Hn1.
  clear Hn; rename Hn1 into Hn.
  rewrite fst_let.
(*
  Hn : 11 < n
  ============================
  S (S (S (S (S n))))
  ≤ (2 * S (S (S (S (S n)))) - 2 ^ S (S (S (S (S (fst (rank_fst_loop n 1 32 (S (S (S (S (S n)))))))))))) *
    2 ^ fst_1_len 1 (S (S (S (S (S n)))))
*)
(*
Theorem le_sub_fst_rank_fst_loop :
  ∀ m n,
  2 ^ m / 2 - m < n
  → m + n
      ≤ (2 * (m + n) - 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n)))) *
        2 ^ fst_1_len 1 (m + n).
Proof.
(*
intros * Hmn.
revert m Hmn.
induction n; intros; [ easy | ].
cbn - [ "-" "*" "/" "mod" "^" ].
remember (2 ^ m / (m + S n) =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  apply Nat_eq_div_1 in Hn1.
  destruct Hn1 as (Hn1, Hn2).
  cbn - [ "*" ].
  rewrite Nat.add_0_r.
  apply (Nat.mul_lt_mono_pos_r 2) in Hmn; [ | easy ].
  rewrite Nat.mul_sub_distr_r in Hmn.
(* l'important, c'est Hn2 *)
Compute (map (λ m,
map (λ n,
(*
if m + S n <=? 2 ^ m then
*)
  if 2 ^ m <? 2 * (m + S n) then
  Nat.leb (m + S n) ((2 * (m + S n) - 2 ^ m) * 2 ^ fst_1_len 1 (m + S n))
  else true
(*
else true
*)
) (seq 0 25)
) (seq 0 20)).
...
(* bon, y a un truc qui va pas, dans ce théorème ; l'hypothèse
   2 ^ m / 2 - m < n c'est peut-être elle qui déconne *)
...
  specialize (IHn (S m)) as H1.
  rewrite Nat.add_succ_comm in H1.
  cbn - [ "*" "/" ] in H1.
Compute (map (λ n,
  let m := 0 in
  fst (rank_fst_loop n 1 (2 * 2 ^ m) (m + S n))) (seq 0 10)).
...
  assert (H : 2 ^ S m / 2 - S m < n). {
    rewrite Nat.pow_succ_r'.
    rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
    apply (Nat.mul_lt_mono_pos_r 2) in Hmn; [ | easy ].
    rewrite Nat.mul_sub_distr_r in Hmn.
...
  eapply le_trans; [ apply Hn1 | ].
...
  cbn - [  "mod" "^" ].
    destruct n; [ easy | apply Nat.succ_lt_mono in Hn ].
    destruct n; [ easy | apply Nat.succ_lt_mono in Hn ].
    destruct n; [ easy | apply Nat.succ_lt_mono in Hn ].
    destruct n; [ easy | clear Hn ].
    do 9 apply Nat.succ_le_mono in Hn1.
    do 8 (destruct n; [ cbn; flia | ]).
    flia Hn1.
  }
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]. {
    destruct n; [ easy | ].
    destruct n; [ flia Hn | ].
    destruct n; [ flia Hn | ].
    destruct n; [ flia Hn | flia Hn1 ].
  }
  rewrite Nat.mod_small; [ | easy ].
  progress replace (2 * 16) with 32 by easy.
  do 5 apply Nat.succ_lt_mono in Hn1.
  clear Hn; rename Hn1 into Hn.
  rewrite fst_let.
...
*)
clear T ro rp rl ac.
Admitted.
now apply (le_sub_fst_rank_fst_loop 5).
*)
  destruct n; [ easy | ].
  apply Nat.succ_lt_mono in Hn.
  cbn - [ "-" "*" "/" "mod" "^" ].
  remember (32 / S (S (S (S (S (S n))))) =? 1) as n1 eqn:Hn1.
  symmetry in Hn1.
destruct n1; [ admit | ].
(*
  destruct n1. {
    apply Nat.eqb_eq in Hn1.
    apply Nat_eq_div_1 in Hn1.
    destruct Hn1 as (Hn1, Hn2).
    do 11 (destruct n; [ easy | apply Nat.succ_lt_mono in Hn ]).
    do 12 apply Nat.succ_le_mono in Hn1.
... trop long
    do 8 (destruct n; [ cbn; flia | ]).
    flia Hn1.
  }
*)
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]. {
    destruct n; [ easy | ].
    do 10 (destruct n; [ flia Hn | ]).
    flia Hn1.
  }
  rewrite Nat.mod_small; [ | easy ].
  progress replace (2 * 32) with 64 by easy.
  do 6 apply Nat.succ_lt_mono in Hn1.
  clear Hn; rename Hn1 into Hn.
  rewrite fst_let.
Theorem le_sub_fst_rank_fst_loop :
  ∀ m n,
  2 ^ m / 2 - m < n
  → m + n
      ≤ (2 * (m + n) - 2 ^ (m + fst (rank_fst_loop n 1 (2 ^ m) (m + n)))) *
        2 ^ fst_1_len 1 (m + n).
Proof.
clear T ro rp rl ac.
... ...
apply (le_sub_fst_rank_fst_loop 6).
cbn.
...
(*
  assert (H : 1 ≤ 2 ^ Nat.log2_up n / n ≤ 2). {
    destruct n; [ easy | ].
    destruct n; [ easy | ].
    specialize (Nat.log2_up_spec (S (S n))) as H1.
    assert (H : 1 < S (S n)) by now apply -> Nat.succ_lt_mono.
    specialize (H1 H); clear H.
    destruct H1 as (H1, H2).
    apply Nat_eq_div_1.
...
    split; [ easy | ].
    rewrite <- Nat_pow2_log2; [ | now apply Nat.neq_0_lt_0 ].
    rewrite Nat.pow_succ_r'.
    apply Nat.mul_lt_mono_pos_l; [ easy | ].
    apply Nat.lt_succ_r.
    now apply Nat.log2_spec.
  }
  clear Hsr; rename H into Hsr.
  apply Nat_eq_div_1 in Hsr.
...
*)
  progress unfold fst_1_len.
  destruct n; [ easy | ].
  cbn - [ "*" "/" "mod" ].
  rewrite fst_if, snd_if.
  rewrite fst_let, snd_let.
  cbn - [ "*" "/" "mod" ].
  remember (1 / S n =? 1) as n1 eqn:Hn1.
  symmetry in Hn1.
  destruct n1. {
    apply Nat.eqb_eq in Hn1.
    apply Nat_eq_div_1 in Hn1.
    destruct Hn1 as (Hn1, H12).
    apply Nat.succ_le_mono in Hn1.
    apply Nat.le_0_r in Hn1; subst n.
    cbn.
    now apply -> Nat.succ_le_mono.
  }
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
  rewrite Nat.mod_small; [ | easy ].
  apply Nat.succ_lt_mono in Hn1.
  rewrite Nat.mul_1_r.
  remember (snd (rank_fst_loop _ _ _ _) / _ =? 0) as sr eqn:Hsr.
  symmetry in Hsr.
  destruct sr. {
    exfalso.
    apply Nat.eqb_eq in Hsr.
    apply Nat.div_small_iff in Hsr; [ | easy ].
    apply -> Nat.lt_succ_r in Hsr.
    apply Nat.nlt_ge in Hsr.
    apply Hsr; clear Hsr.
    now apply (lt_snd_rank_fst_loop 0).
  }
  rewrite snd_rank_fst_1_2_succ in Hsr; [ | easy | easy ].
  apply Nat.eqb_neq in Hsr.
  rewrite snd_rank_fst_1_2_succ; [ | easy | easy ].
  rewrite <- Nat_pow2_log2; [ | now apply Nat.neq_0_lt_0 ].
(*
  rewrite <- Nat_pow2_log2 in Hsr; [ | now apply Nat.neq_0_lt_0 ].
*)
  rewrite (Nat_mod_less_small 1). 2: {
    rewrite Nat.mul_1_l.
    cbn - [ "*" ].
    specialize (Nat.log2_spec n Hn1) as H1.
    split; [ easy | ].
    apply Nat.mul_lt_mono_pos_l; [ easy | ].
    now apply Nat.lt_succ_r.
  }
(*
  do 2 rewrite Nat.pow_succ_r'.
  rewrite <- Nat.mul_sub_distr_l.
*)
  rewrite Nat.mul_1_l.
(*
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm _ 2).
  rewrite Nat.mul_assoc.
  progress replace (2 * 2) with 4 by easy.
*)
  rewrite Nat_pow2_log2; [ | now apply Nat.neq_0_lt_0 ].
  assert (2 ^ Nat.log2_up (S n) / S n = 1). {
    specialize (Nat.log2_up_spec (S n)) as H1.
    assert (H : 1 < S n) by now apply -> Nat.succ_lt_mono.
    specialize (H1 H); clear H.
    destruct H1 as (H1, H2).
    apply Nat_eq_div_1.
    split; [ easy | ].
    rewrite <- Nat_pow2_log2; [ | now apply Nat.neq_0_lt_0 ].
    rewrite Nat.pow_succ_r'.
    apply Nat.mul_lt_mono_pos_l; [ easy | ].
    apply Nat.lt_succ_r.
    now apply Nat.log2_spec.
  }
  clear Hsr; rename H into Hsr.
  apply Nat_eq_div_1 in Hsr.
(*
  remember (2 ^ Nat.log2_up (S n)) as x eqn:Hx.
  remember (S n) as m eqn:Hm.
*)
(**)
apply Nat.succ_lt_mono.
apply -> Nat.succ_lt_mono.
Search (rank_fst_loop _ _ (2 * _)).
Check fst_rank_fst_loop_eq_succ.
Compute (map (λ n,
  (n, fst (rank_fst_loop n 0 (2 * (2 ^ Nat.log2_up (S n) - S n)) (S n)))) (seq 0 30)).
...
Theorem fst_rank_fst_loop_0_eq_0 :
  ∀ it a b : nat,
  0 < a < b
  → Nat.log2_up b ≤ it
  → fst (rank_fst_loop it 0 a b) = 0.
(*
Compute (map (λ b,
  let a := 1 in
  let it := Nat.log2_up b + 1 in
  fst (rank_fst_loop it 0 a b) = 0) (seq 2 12)).
*)
clear T ro rp rl ac.
...
rewrite fst_rank_fst_loop_0_eq_0.
...
rewrite <- fst_rank_fst_loop_eq_succ
...
apply -> Nat.le_succ_r.
destruct n; [ cbn; flia | ].
cbn - [ "*" "/" "mod" "^" Nat.log2_up ].
remember (_ / _ =? 0) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  cbn - [ "*" "/" "mod" "^" Nat.log2_up ].
  
...
Compute (map (λ n,
  S n
  ≤ (2 * S n - 2 ^ Nat.log2_up (S n)) *
    2 ^ S (fst (rank_fst_loop n 0 (2 * (2 ^ Nat.log2_up (S n) - S n)) (S n)))) (seq 0 20)).
...
  rewrite Nat.pow_succ_r' in Hsr.
Search (2 ^ fst _).
(* ouais, bof *)
...
specialize (Nat.log2_up_spec (S n)) as H1.
...
  rewrite <- Nat_pow2_log2; [ | now apply Nat.neq_0_lt_0 ].
...
apply (le_trans _ (S it)); [ easy | ].
apply Nat.le_succ_diag_r.
Qed.
rewrite snd_rank_fst_1_2; [ | | ].
(*
Compute (map (λ n,
  (2 ^ S (Nat.log2 n), snd (rank_fst_loop n 1 2 (S n)))) (seq 0 40)).
Compute (map (λ n,
  (2 ^ Nat.log2_up (S n), snd (rank_fst_loop n 1 2 (S n)))) (seq 0 40)).
...
Compute (map (λ n,
  Nat.eqb (2 ^ S (Nat.log2 n)) (snd (rank_fst_loop n 1 2 (S n)))) (seq 0 40)).
Compute (map (λ n,
  Nat.eqb (2 ^ Nat.log2_up (S n)) (snd (rank_fst_loop n 1 2 (S n)))) (seq 0 40)).
...
Compute (map (λ n,
  (2 ^ Nat.log2_up n, snd (rank_fst_loop n 1 2 n))) (seq 0 40)).
...
*)
...
  clear. (* seems true inconditionnally *)
  destruct n; [ now cbn; apply -> Nat.succ_le_mono | ].
(**)
  cbn - [ "*" "/" "mod" "^" Nat.log2 ].
(**)
  rewrite fst_if, snd_if, fst_let, snd_let, S_if.
(*
  rewrite fst_if, fst_let.
*)
  cbn - [ "*" "/" "mod" "^" Nat.log2 ].
  remember (2 / S (S n) =? 1) as n1 eqn:Hn1.
  symmetry in Hn1.
  destruct n1. {
    apply Nat.eqb_eq in Hn1.
    apply Nat_eq_div_1 in Hn1.
    destruct Hn1 as (Hn1, Hn2).
    do 2 apply Nat.succ_le_mono in Hn1.
    apply Nat.le_0_r in Hn1; subst n.
    cbn; flia.
  }
  apply Nat.eqb_neq in Hn1.
  apply Nat_neq_div_1 in Hn1.
  destruct Hn1 as [Hn1| Hn1]; [ flia Hn1 | ].
  rewrite (Nat.mod_small 2); [ | easy ].
  do 2 apply Nat.succ_lt_mono in Hn1.
  progress replace (2 * 2) with 4 by easy.
  remember (_ =? 0) as tsr eqn:Htsr.
  symmetry in Htsr.
  destruct tsr. {
    apply Nat.eqb_eq in Htsr.
    apply Nat.div_small_iff in Htsr; [ | easy ].
    rewrite Nat.pow_1_r.
    rewrite Nat.mul_sub_distr_r.
    rewrite Nat.mul_shuffle0.
    progress replace (2 * 2) with 4 by easy.
    rewrite (Nat.mul_comm _ 2).
    rewrite <- Nat.pow_succ_r'.
    apply Nat.le_add_le_sub_r.
    apply Nat_le_add_le_sub_l; [ flia | ].
    rewrite Nat_sub_mul_l_diag_r.
    cbn - [ "*" "^" Nat.log2 ].
    specialize (Nat.log2_succ_or n) as H1.
    destruct H1 as [H1| H1]. {
      apply Nat_pow2_log2_succ in H1.
      destruct H1 as (_, H1).
      do 2 rewrite Nat.pow_succ_r'.
      rewrite H1.
      rename Hn1 into Hnz.
      destruct (Nat.eq_dec n 1) as [Hn1| Hn1]; [ now subst n; flia | ].
      move Hn1 before Hnz.
Compute (
  map (λ n,
    if 2 ^ Nat.log2 (S n) =? S n then
      (2 * (snd (rank_fst_loop n 1 4 (S (S n))) mod S (S n)), S (S n))
    else
      (0, 0))
    (seq 0 12)).
exfalso.
apply Nat.nle_gt in Htsr.
apply Htsr; clear Htsr.
apply Nat.le_succ_l.
specialize (lt_snd_rank_fst_loop 1 n Hnz) as H2.
cbn in H2.
eapply lt_le_trans; [ apply H2 | ].
remember (snd (rank_fst_loop n 1 4 (S (S n)))) as x eqn:Hx.
rewrite <- Nat.mul_mod_distr_l; [ | easy | easy ].
Compute (map (λ n,
  (2 ^ S (Nat.log2 (S n)), snd (rank_fst_loop n 1 4 (S (S n))))) (seq 0 40)).
...
Search (_ * (_ mod _)).
Search (rank_fst_loop _ _ (2 ^ _)).
remember (snd (rank_fst_loop n 1 4 (S (S n)))) as x eqn:Hx.
eapply (le_trans _ (S x)). {
  apply Nat.succ_lt_mono in H2.
  now apply Nat.lt_le_incl.
}
Search (S _ ≤ _).
apply N
...
Compute (map (λ n,
  if 2 ^ Nat.log2 (S n) =? S n then
    Some (S (S n) ≤ 2 * (snd (rank_fst_loop n 1 4 (S (S n))) mod S (S n)))
  else
    None) (seq 2 40)).
...
progress replace 4 with (2 ^ 2) in Htsr by easy.
Search (rank_fst_loop _ _ _ (2 ^ _ + 1)).
...
Theorem rank_snd_1_1_pow2_lemma :
  ∀ it m n,
  m ≤ n
  → 2 ^ n - m ≤ it
  → snd (rank_fst_loop it 1 (2 ^ m) (2 ^ n)) =
      if m =? n then 2 ^ m else 0.
Proof.
(*
Compute (
   let m := 2 in
   let it := 24 in
   map (λ n, snd (rank_fst_loop it 1 (2 ^ m) (2 ^ n))) (seq 0 12)).
*)
intros * Hmn Hit.
revert m n Hmn Hit.
induction it; intros. {
  apply Nat.le_0_r in Hit.
  apply Nat.sub_0_le in Hit.
  exfalso.
  apply Nat.nlt_ge in Hit.
  apply Hit; clear Hit.
  apply (Nat.le_lt_trans _ n); [ easy | ].
  now apply Nat.pow_gt_lin_r.
}
cbn - [ "*" ].
remember (2 ^ m / 2 ^ n =? 1) as mn eqn:Hmn1.
symmetry in Hmn1.
destruct mn. {
  apply Nat.eqb_eq in Hmn1.
  apply Nat_eq_div_1 in Hmn1.
  destruct Hmn1 as (Hnm, Hmn1).
  apply Nat.pow_le_mono_r_iff in Hnm; [ | easy ].
  apply Nat.le_antisymm in Hnm; [ subst m | easy ].
  now rewrite Nat.eqb_refl.
}
clear T ro rp rl ac.
...
progress replace 4 with (2 ^ 2) in Htsr by easy.
rewrite <- H1 in Htsr at 1.
rewrite rank_snd_1_1_pow2_lemma in Htsr.
...
Search (_ ^ _ ≤ _ ^ _).
rank_fst_1_1_pow2_lemma:
  ∀ it m n : nat,
    m ≤ n → 2 ^ n - m ≤ it → m + fst (rank_fst_loop it 1 (2 ^ m) (2 ^ n)) = n
      rewrite H1.
      rewrite Nat.mul_assoc.
      progress replace (2 * 2) with 4 by easy.
      destruct n; [ cbn; flia | ].
...
clear Htsr.
remember (S n) as m.
clear n Hn1 Heqm.
rename m into n.
Compute (map (λ m,
  let n := 2 ^ m in
  Nat.leb (4 * n) (3 * S n)) (seq 0 10)).

...
rewrite <- (Nat.add_1_r (S n)).
...
    destruct n; [ easy | clear Hn1 ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn in Htsr; flia Htsr | ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn in Htsr; flia Htsr | ].
    destruct n; [ cbn in Htsr; flia Htsr | ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn; flia | ].
    destruct n; [ cbn; flia | ].
...
Print rank_fst_loop.
Theorem snd_rank_fst_loop_le_2_den :
  ∀ it a b, a < 2 * b → snd (rank_fst_loop it 1 a b) mod b ≤ 2 * b.
Proof.
intros * Hab.
revert a Hab.
induction it; intros. {
  destruct b; [ easy | cbn ].
  now rewrite Nat.sub_diag.
}
cbn - [ "*" ].
rewrite snd_if, snd_let.
cbn - [ "*" ].
remember (a / b =? 1) as ab1 eqn:Hab1.
symmetry in Hab1.
destruct ab1. {
  apply (le_trans _ b); [ | flia ].
  apply Nat.lt_le_incl, Nat.mod_upper_bound.
  flia Hab.
}
apply Nat.eqb_neq in Hab1.
apply Nat_neq_div_1 in Hab1.
destruct Hab1 as [Hab1| Hab1]; [ now apply Nat.nlt_ge in Hab1 | ].
rewrite (Nat.mod_small a); [ | easy ].
apply IHit.
now apply Nat.mul_lt_mono_pos_l.
Qed.
specialize (snd_rank_fst_loop_le_2_den n 4 (S (S n))) as H1.
assert (H : 4 < 2 * S (S n)) by flia Hn1.
specialize (H1 H); clear H.
remember (snd _ mod S (S n)) as x.
(* le H1 sert strictement à rien *)
(* donc le théorème ci-dessus non plus *)
...
Compute (map (λ n,
  (n,
   Nat.leb (S (S n)) (4 * S (S n) - 2 ^ S (S (Nat.log2 (S n)))))) (seq 0 20)).
...
rewrite Nat.mod_small in Htsr. 2: {
  destruct n; [ easy | ].
  cbn - [ "*" "/" "mod" ].
  remember (4 / S (S (S n)) =? 1) as n4 eqn:Hn4.
  symmetry in Hn4.
  destruct n4. {
    exfalso.
    apply Nat.eqb_eq in Hn4.
    apply Nat_eq_div_1 in Hn4.
    destruct Hn4 as (Hn4, Hn5).
    do 3 apply Nat.succ_le_mono in Hn4.
    destruct n. {
      cbn in Htsr, Hn5.
      (* donc faux *)
...
remember (snd _) as x.
Compute (
  map (λ n,
    let x := 3 in
    (Nat.ltb (2 * (x mod S (S n))) (S (S n)),
     x < S (S n))) (seq 1 20)).
...
Search (snd _ mod _).
Print rank_fst_loop.
Compute (map (λ n,
  snd (rank_fst_loop n 1 4 (S (S n))) < S (S n)) (seq 0 40)).
...
Compute (map (λ n,
  (n, Nat.ltb
     (2 * (snd (rank_fst_loop n 1 4 (S (S n))) mod S (S n)))
     (S (S n)),
   Nat.leb (S (S n)) (4 * S (S n) - 2 ^ S (S (Nat.log2 (S n)))))) (seq 0 20)).
...
Compute (map (λ n,
  Nat.leb
  (S n)
  ((2 * S n - 2 ^ Nat.log2_up (S n)) *
    2
    ^ S
        (fst
           (rank_fst_loop n 0 (2 * (snd (rank_fst_loop n 1 2 (S n)) mod S n))
              (S n))))) (seq 0 40)).

apply Nat.eqb_neq in Hsr.
cbn - [ "*" "mod" "^" ].
...
Compute (map (λ n,
  Nat.ltb n (snd (rank_fst_loop n 1 2 (S n)))) (seq 1 40)).
Print rank_fst_loop.
Compute (map (λ n,
  (Nat.leb (snd (rank_fst_loop n 1 2 (S n))) n)) (seq 1 40)).
Compute (map (λ n,
  (Nat.leb (snd (rank_fst_loop n 1 2 (S n))) n,
   Nat.leb (S n) (2 * S n - 2 ^ Nat.log2_up (S n)))) (seq 0 40)).

...
Compute (map (λ n, Nat.leb (S n) (2 * S n - 2 ^ Nat.log2_up (S n))) (seq 0 40)).
...
Search (if (if _ then _ else _) then _ else _).
Theorem if_if :
  ∀ A (a b c : bool) (d e : A),
  (if (if a then b else c) then d else e) =
  (if a then if b then d else e else if c then d else e).
clear T ro rp rl ac.
rewrite if_if.
...
Compute
(map (λ n, Nat.leb n
  ((2 * n - 2 ^ Nat.log2_up n) * 2 ^ fst_1_len 1 n)) (seq 0 40)).
...
Check Nat.log2_up_spec.
specialize (Nat.log2_up_spec (S n)) as H2.
assert (H : 1 < S n) by flia Hnz.
specialize (H2 H); clear H.
rewrite H1 in H2.
...
Check Nat.le_log2_up_succ_log2.
Search Nat.log2.
...
    generalize H1; intros H2.
    symmetry in H2.
    apply Nat_eq_log2_up in H2; [ | easy ].
    destruct H2 as (H2, H3).
    rewrite H1 in H2, H3.
...
    apply (Nat.mul_lt_mono_pos_l 2) in H2; [ | easy ].
Search (_ * (_ / _)).
    specialize (Nat.div_mul_le (2 ^ Nat.log2_up (S n)) 2 2) as H4.
    specialize (H4 (Nat.neq_succ_0 _)).
...
    eapply le_trans; [ | apply Nat.lt_le_incl, H2 ].

eapply le_trans; [ apply H1 | ].
rewrite Nat.mul_comm in H1.
...
Search (_ / _ < _).
apply Nat.div_lt_upper_bound in
Search (Nat.log2_up).
...
Search Nat.log2_up.
    specialize Nat.log2_up_spec as H1.
Search (2 ^ Nat.log2_up _ ≤ _).
Nat_pow2_log2_up_succ: ∀ n : nat, Nat.log2_up (S n) = S (Nat.log2_up n) ↔ 2 ^ Nat.log2 n = n
...
    destruct n; [ easy | clear Hnz ].
Search (Nat.log2_up (S _)).
...
Compute (
  map (λ n, Nat.leb (2 ^ Nat.log2_up n) (2 * n)) (seq 1 40)).
ok
...
Search (_ + _ ≤ _).
Search (_ + _ < _).
Search (_ - _ ≤ _).
Check Nat.lt_add_lt_sub_l.
Check Nat.le_add_le_sub_l.
...
Check Nat.le_sub_le_add_r.
...
Search (_ + _ ≤ _ ↔ _).
Search (_ → _ + _ ≤ _).
  rewrite Nat.add_comm.
  apply Nat.le_add_le_sub_l.
  apply Nat.le_sub_le_add_r.
  remember (fst_1_len 1 n) as m eqn:Hm.
...
Compute (
  let m := 4 in
map (λ m,
  map (λ n, Nat.leb (2 ^ Nat.log2_up n * 2 ^ m) (2 ^ S m * n - n)) (seq 1 20))
(seq 4 12)).

...
Search (2 ^ Nat.log2_up _).
Compute (
  map (λ n,
    Nat.leb (2 ^ Nat.log2_up n * 2 ^ fst_1_len 1 n) (2 ^ S (fst_1_len 1 n) * n - n)) (seq 1 20)).

...
...
Compute (
  map (λ n, Nat.leb (2 ^ inv_ub_den_pow2 n) (inv_ub_num n * n)) (seq 1 20)).
Compute (
  let n := 31 in
  map (λ i, Nat.leb (2 ^ inv_ub_den_pow2 n * 2 ^ i) (n * (2 ^ i * inv_ub_num n))) (seq 0 15)).
...
Compute (
  let n := 4 in
  map (λ i, 2 ^ i / n * 2 ^ inv_ub_den_pow2 n ≤ 2 ^ i * inv_ub_num n)
   (seq 0 10)).
Compute (
  let n := 9 in
  map (λ i, Nat.leb (2 ^ i / n * 2 ^ inv_ub_den_pow2 n) (2 ^ i * inv_ub_num n))
   (seq 0 12)).
...
  apply (Nat.pow_le_mono_r_iff 2) in Hni; [ | easy ].
Search (_ ^ (_ - _)).
...
  progress unfold inv_ub_den_pow2 in Hni.
  progress unfold inv_ub_den_pow2.
  rewrite rank_fst_1_log2_up in Hni |-*.
  rewrite Nat.pow_add_r in Hni.
...
Compute (
  let n := 5 in
  map (λ i, (i ≤ inv_ub_den_pow2 n, 2 ^ i / n * 2 ^ (inv_ub_den_pow2 n - i) ≤ inv_ub_num n))
    (seq 1 12)).
...
Search (_ - _ ≤ _).
...
  apply Nat.le_sub_le_add_l.
Search (_ ≤ _ + _).

  apply Nat_le_add_l.

Search (_ ≤ S _).
Search (inv_ub_num).
Search (inv_ub_den_pow2).
...

rewrite <- (angle_div_2_pow_mul_pow_sub (inv_ub_den_pow2 n) i).
rewrite <- (angle_div_2_pow_mul_pow_sub i (inv_ub_den_pow2 n)).

progress unfold inv_ub_den_pow2 in Hni.
rewrite rank_fst_1_log2_up in Hni.
...
rewrite <- (angle_div_2_pow_mul_pow_sub (inv_ub_den_pow2 n) i).
...
rewrite <- (angle_div_2_pow_mul_pow_sub (inv_ub_den_pow2 n + i) (inv_ub_den_pow2 n)). 2: {
  progress unfold inv_ub_den_pow2.
...
destruct i. {
  cbn - [ "^" ].
  rewrite Nat.div_small; [ | cbn; flia Hnz Hn1 ].
  apply angle_nonneg.
}
rewrite <- (angle_div_2_pow_mul_pow_sub (1 + i) (inv_ub_den_pow2 n)). 2: {
  progress unfold inv_ub_den_pow2.
...
rewrite <- (angle_div_2_pow_mul_pow_sub (5 + i) 5); [ | apply Nat.le_add_r ].
  ============================
  (2 ^ S (S (S (S (S i)))) / 5 * (θ / ₂^S (S (S (S (S i))))) ≤ 7 * (θ / ₂^5))%A
...
intros * Hn1.
progress unfold seq_angle_to_div_nat.
progress unfold inv_ub_num.
progress unfold inv_ub_den_pow2.
rewrite rank_fst_1_log2_up.
rewrite angle_div_2_pow_add_r.
progress unfold fst_1_len.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  apply angle_nonneg.
}
rewrite snd_rank_fst_1; [ | easy | easy ].
rewrite fold_rank_fst_0.
destruct i. {
  cbn - [ "^" ].
  rewrite Nat.div_small; [ | cbn; flia Hnz Hn1 ].
  apply angle_nonneg.
}
rewrite <- (angle_div_2_pow_mul_pow_sub (5 + S i) (S i)); [ | ].
...
Compute (map (λ n, (n, rank_fst_0 (2 ^ Nat.log2_up n) n)) (seq 0 40)).
Compute (map (λ n, (n, 2 ^ S (rank_fst_0 (2 ^ Nat.log2_up n) n) - 1)) (seq 0 40)).
Compute (let n := 5 in
  (2 ^ S (rank_fst_0 (2 ^ Nat.log2_up n) n) - 1,
   2^Nat.log2_up n, 2^rank_fst_0 (2 ^ Nat.log2_up n) n)).
...
1/5 = 0.0011001100...
    ≤ 0.00111
          ^^^ = 7
            ^ position = 5
log2 5 = 3
...
θ/2^3/2^2
Inspect 20.
Theorem seq_angle_to_div_nat_5_le' :
  ∀ i θ, (2 ^ i / 5 * (θ / ₂^i) ≤ 7 * (θ / ₂^5))%A.
Proof.
intros.
...
  ============================
  (2 ^ i / 5 * (θ / ₂^i) ≤ 7 * (θ / ₂^5))%A
  ============================
  (2 ^ i / 5 * (θ / ₂^i) ≤ (2^3-1) * (θ / ₂^3 / ₂^2))%A
...
Compute (binary_div 20 64 33).
Compute (binary_div 20 64 38).
Compute (binary_div 20 32 17).
...
Compute (map (λ n, (fst_1_len 1 n)) (seq 0 40)).
Compute (map (λ n, (n, fst_1_len 1 n)) (seq 0 20)).
Print rank_fst_loop.
Print fst_1_len.
Compute (map (λ b, (b, snd (rank_fst_loop b 1 1 b))) (seq 0 20)).
Compute (map (λ n, snd (rank_fst_loop n 1 1 n) = 2 ^ Nat.log2_up n) (seq 0 30)).
Inspect 3.
Search rank_fst_loop.
...
Compute (map (λ n, (fst_1_len 1 n)) (seq 0 20)).
Compute (map (λ n, (n, fst_1_len 1 n)) (seq 0 20)).
Compute (map (λ a, (a, map (λ b, snd (rank_fst_loop b 1 a b)) (seq a 20))) (seq 0 10)).
Compute (map (λ n, (2 ^ rank_fst_1 1 n, 2 * n)) (seq 0 20)).
...
destruct (Nat.log2_up_succ_or n) as [Hn| Hn]. {
  apply Nat_pow2_log2_up_succ in Hn.
(*
  Hn : 2 ^ Nat.log2 n = n
  ============================
  rank_fst_1 1 n = Nat.log2_up n
*)
  rewrite <- Hn.
  rewrite rank_fst_1_1_pow2.
  now rewrite Nat.log2_up_pow2.
}
assert (Hn2 : 2 ^ Nat.log2 n ≠ n). {
  intros H.
  specialize (Nat_pow2_log2_up_succ n) as H1.
  apply H1 in H.
  rewrite Hn in H.
  symmetry in H.
  now apply Nat.neq_succ_diag_l in H.
}
clear Hn.
(*
  Hn2 : 2 ^ Nat.log2 n ≠ n
  ============================
  rank_fst_1 1 n = Nat.log2_up n
*)
Theorem rank_fst_1_1_pow2_log2_up :
  ∀ n, rank_fst_1 1 n = rank_fst_1 1 (2 ^ Nat.log2_up n).
Proof.
intros.
progress unfold rank_fst_1.
Theorem glop :
  ∀ n,
  n ≠ 0
  → fst (rank_fst_loop n 1 1 n) =
    fst (rank_fst_loop (2 ^ Nat.log2_up n) 1 1 n).
Proof.
intros * Hnz.
induction n; [ easy | clear Hnz ].
(**)
cbn - [ "/" "mod" "*" Nat.log2_up ].
remember (1 / S n =? 1) as sn eqn:Hsn.
symmetry in Hsn.
destruct sn. {
  apply Nat.eqb_eq in Hsn.
  destruct n; [ easy | ].
  now rewrite Nat.div_small in Hsn.
}
apply Nat.eqb_neq in Hsn.
rewrite fst_let.
destruct n; [ easy | clear Hsn ].
specialize (IHn (Nat.neq_succ_0 _)).
rewrite Nat.mod_small; [ | flia ].
cbn - [ rank_fst_loop Nat.log2_up ].
(**)
replace (S (S n)) with (n + 2) by flia.
(*
  ============================
  S (fst (rank_fst_loop (S n) 1 2 (n + 2))) =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 2)) 1 1 (n + 2))
*)
Theorem glop :
  ∀ m n,
  fst (rank_fst_loop (n + 2 ^ m - m) 1 (2 ^ (m + 1)) (n + 2 ^ m + 1)) + m + 1 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 2 ^ m + 1)) 1 1 (n + 2 ^ m + 1)).
Proof.
intros.
revert m.
induction n; intros. {
  cbn.
  rewrite (Nat.add_1_r (2 ^ m)).
  rewrite Nat.log2_up_succ_pow2; [ | easy ].
  rewrite (Nat.add_1_r m).
  rewrite Nat.pow_succ_r'.
  rewrite <- (Nat.add_1_r (2 ^ m)).
  rewrite fst_rank_fst_loop_1_mul_2_add_1; [ | now apply Nat.pow_nonzero ].
  rewrite Nat.add_0_l; symmetry.
(*
Compute (map (λ m, fst (rank_fst_loop (2 * 2 ^ m) 1 1 (2 ^ m + 1)) = m + 1) (seq 0 13)).
Compute (map (λ m, binary_div 20 1 (2 ^ m + 1)) (seq 0 13)).
*)
(*
  ============================
  fst (rank_fst_loop (2 * 2 ^ m) 1 1 (2 ^ m + 1)) = m + 1
...
rank_fst_1_1_pow2_lemma:
  ∀ it m n : nat,
    m ≤ n → 2 ^ n - m ≤ it → m + fst (rank_fst_loop it 1 (2 ^ m) (2 ^ n)) = n
...
*)
Theorem glop :
  ∀ n, fst (rank_fst_loop (2 ^ S n) 1 1 (2 ^ n + 1)) = n + 1.
Proof.
intros.
specialize (fst_rank_fst_loop_pow2_succ n) as H1.
Theorem glop :
  ∀ it1 it2 a b,
  0 < a ≤ b
  → Nat.log2_up b < it1
  → Nat.log2_up b < it2
  → fst (rank_fst_loop it1 1 a b) =
    fst (rank_fst_loop it2 1 a b).
Proof.
intros * Hzab Hit1 Hit2.
destruct (Nat.eq_dec a b) as [Heab| Heab]. {
  subst b.
  rewrite fst_rank_fst_loop_diag; [ | flia Hzab ].
  rewrite fst_rank_fst_loop_diag; [ | flia Hzab ].
  easy.
}
assert (H : 0 < a < b) by flia Hzab Heab.
clear Hzab Heab.
rename H into Hzab.
move Hzab after Hit1.
(**)
revert a b it2 Hzab Hit1 Hit2.
induction it1; intros; [ now apply Nat.le_0_r in Hit1 | ].
cbn - [ "*" ].
remember (a / b =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  now rewrite Nat.div_small in Hn1.
}
rewrite fst_let.
rewrite Nat.mod_small; [ | easy ].
destruct it2; [ now apply Nat.le_0_r in Hit2 | ].
apply -> Nat.lt_succ_r in Hit1.
apply -> Nat.lt_succ_r in Hit2.
cbn - [ "*" ].
rewrite Hn1.
rewrite fst_let.
rewrite Nat.mod_small; [ | easy ].
f_equal.
destruct (lt_dec (2 * a) b) as [Htab| Htab]. {
  destruct (Nat.eq_dec (Nat.log2_up b) it1) as [Hc1| Hc1]. 2: {
    destruct (Nat.eq_dec (Nat.log2_up b) it2) as [Hc2| Hc2]. 2: {
      apply IHit1; [ flia Hzab Htab | flia Hit1 Hc1 | flia Hit2 Hc2 ].
    }
    remember (it1 - it2) as n eqn:Hn.
    assert (it1 = it2 + n). {
      symmetry.
      apply Nat_sub_add_eq_l; [ | easy ].
      now subst it2.
    }
    subst it1; rename it2 into it.
    assert (Hnz : n ≠ 0). {
      intros H; subst n.
      now rewrite Nat.add_0_r in Hc1.
    }
    clear Hn IHit1 Hit1 Hn1 Hc1.
    clear Hit2.
    revert it Hc2.
    revert a Hzab Htab.
    destruct n; intros; [ easy | clear Hnz ].
destruct Hzab as (Hza, Hab1).
move it before a.
clear - Hza Hab1 Hc2.
(*
  Hza : 0 < a
  Hab1 : a < b
  Hc2 : Nat.log2_up b = it
  ============================
  fst (rank_fst_loop (it + S n) 1 (2 * a) b) = fst (rank_fst_loop it 1 (2 * a) b)
*)
    rewrite Nat.add_succ_r.
    cbn - [ "*" ].
    remember (2 * a / b =? 1) as ab eqn:Hab.
    symmetry in Hab.
    destruct ab. {
      cbn - [ "*" ].
      destruct it; [ easy | ].
      cbn - [ "*" ].
      now rewrite Hab.
    }
    rewrite fst_let.
    apply Nat.eqb_neq in Hab.
    apply Nat_neq_div_1 in Hab.
    destruct Hab as [Hab| Hab]. {
      apply Nat.mul_le_mono_pos_l in Hab; [ | easy ].
      now apply Nat.nlt_ge in Hab.
    }
    move Hab before Hab1.
    rewrite Nat.mod_small; [ | easy ].
    specialize fst_rank_fst_loop_eq_succ as H1.
    rewrite (H1 it (2 * a)); [ | | now rewrite Hc2 ]. 2: {
      split; [ | easy ].
      now apply Nat.mul_pos_pos.
    }
    f_equal.
    destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
      now subst n; rewrite Nat.add_0_r.
    }
    destruct n; [ easy | ].
clear - Hza Hab Hc2.
(*
  Hza : 0 < a
  Htab : 2 * a < b
  Hc2 : Nat.log2_up b = it
  ============================
  fst (rank_fst_loop (it + S n) 1 (2 * (2 * a)) b) = fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
    rewrite <- Nat.add_succ_comm.
    cbn - [ "*" ].
    remember (2 * (2 * a) / b =? 1) as ab2 eqn:Hab2.
    symmetry in Hab2.
    destruct ab2. {
      cbn - [ "*" ].
      destruct it; [ easy | ].
      cbn - [ "*" ].
      now rewrite Hab2.
    }
    rewrite fst_let.
    apply Nat.eqb_neq in Hab2.
    apply Nat_neq_div_1 in Hab2.
    destruct Hab2 as [Hab2| Hab2]. {
      apply Nat.mul_le_mono_pos_l in Hab2; [ | easy ].
      now apply Nat.nlt_ge in Hab2.
    }
    move Hab2 before Hab.
    rewrite Nat.mod_small; [ | easy ].
    destruct n. {
      rewrite Nat.add_0_r.
      symmetry.
      specialize fst_rank_fst_loop_eq_succ as H1.
      rewrite H1; [ easy | | now rewrite Hc2 ].
      split; [ | easy ].
      apply Nat.mul_pos_pos; [ easy | ].
      now apply Nat.mul_pos_pos.
    }
clear - Hc2 Hza Hab2.
(*
  Hza : 0 < a
  Hab2 : 2 * (2 * a) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * a))) b)) = fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
    rewrite <- Nat.add_succ_comm.
    cbn - [ "*" ].
    rewrite fst_if, S_if, fst_let.
    cbn - [ "*" ].
    remember (2 * (2 * (2 * a)) / b =? 1) as ab3 eqn:Hab3.
    symmetry in Hab3.
    destruct ab3. {
      cbn - [ "*" ].
      destruct it. {
        exfalso.
        apply Nat.log2_up_null in Hc2.
        flia Hza Hc2 Hab2.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small; [ | easy ].
      rewrite Nat.div_small; [ | easy ].
      rewrite fst_if, fst_let.
      cbn - [ "*" ].
      destruct it; [ easy | ].
      cbn - [ "*" ].
      now rewrite Hab3.
    }
    apply Nat.eqb_neq in Hab3.
    apply Nat_neq_div_1 in Hab3.
    destruct Hab3 as [Hab3| Hab3]. {
      apply Nat.mul_le_mono_pos_l in Hab3; [ | easy ].
      now apply Nat.nlt_ge in Hab3.
    }
    move Hab3 before Hab2.
    rewrite Nat.mod_small; [ | easy ].
    destruct n. {
      rewrite Nat.add_0_r.
      symmetry.
      specialize fst_rank_fst_loop_eq_succ as H1.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split; [ | easy ].
        apply Nat.mul_pos_pos; [ easy | ].
        now apply Nat.mul_pos_pos.
      }
      f_equal.
      apply H1; [ | now rewrite Hc2 ].
      split; [ | easy ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      now apply Nat.mul_pos_pos.
    }
clear - Hc2 Hza Hab3.
(*
  Hza : 0 < a
  Hab3 : 2 * (2 * (2 * a)) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * (2 * a)))) b))) = fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
    rewrite <- Nat.add_succ_comm.
    cbn - [ "*" ].
    rewrite fst_if, S_if, fst_let, S_if.
    cbn - [ "*" ].
    remember (2 * (2 * (2 * (2 * a))) / b =? 1) as ab4 eqn:Hab4.
    symmetry in Hab4.
    destruct ab4. {
      cbn - [ "*" ].
      destruct it. {
        apply Nat.log2_up_null in Hc2.
        flia Hza Hab3 Hc2.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab3 ].
        flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab3 ].
        flia.
      }
      rewrite fst_if.
      cbn - [ "*" ].
      rewrite fst_let.
      f_equal; symmetry.
      destruct it. {
        apply Nat_eq_log2_up in Hc2; [ | flia Hab3 ].
        cbn in Hc2.
        flia Hza Hc2 Hab3.
      }
      cbn - [ "*" ].
      rewrite fst_if, fst_let.
      rewrite Nat.mod_small; [ | easy ].
      rewrite Nat.div_small; [ | easy ].
      cbn - [ "*" ].
      destruct it; [ easy | ].
      f_equal.
      cbn - [ "*" ].
      now rewrite Hab4.
    }
    apply Nat.eqb_neq in Hab4.
    apply Nat_neq_div_1 in Hab4.
    destruct Hab4 as [Hab4| Hab4]. {
      apply Nat.mul_le_mono_pos_l in Hab4; [ | easy ].
      now apply Nat.nlt_ge in Hab4.
    }
    move Hab4 before Hab3.
    rewrite Nat.mod_small; [ | easy ].
    destruct n. {
      rewrite Nat.add_0_r.
      symmetry.
      specialize fst_rank_fst_loop_eq_succ as H1.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split. {
          apply Nat.mul_pos_pos; [ easy | ].
          now apply Nat.mul_pos_pos.
        }
        eapply Nat.le_lt_trans; [ | apply Hab3 ].
        flia.
      }
      f_equal.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split; [ | easy ].
        apply Nat.mul_pos_pos; [ easy | ].
        apply Nat.mul_pos_pos; [ easy | ].
        now apply Nat.mul_pos_pos.
      }
      f_equal.
      apply H1; [ | now rewrite Hc2 ].
      split; [ | easy ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      now apply Nat.mul_pos_pos.
    }
clear - Hc2 Hza Hab4.
(*
  Hza : 0 < a
  Hab4 : 2 * (2 * (2 * (2 * a))) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (S (S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * (2 * (2 * a))))) b)))) =
  fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
    rewrite <- Nat.add_succ_comm.
    cbn - [ "*" ].
    rewrite fst_if, S_if, fst_let, S_if, S_if.
    cbn - [ "*" ].
    remember (2 * (2 * (2 * (2 * (2 * a)))) / b =? 1) as ab5 eqn:Hab5.
    symmetry in Hab5.
    destruct ab5. {
      cbn - [ "*" ].
      destruct it. {
        apply Nat.log2_up_null in Hc2.
        flia Hza Hab4 Hc2.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab4 ]; flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab4 ]; flia.
      }
      rewrite fst_if, fst_let.
      cbn - [ "*" ].
      f_equal; symmetry.
      destruct it. {
        apply Nat_eq_log2_up in Hc2; [ | flia Hab4 ].
        cbn in Hc2.
        flia Hza Hc2 Hab4.
      }
      cbn - [ "*" ].
      rewrite fst_if, fst_let.
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab4 ]; flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab4 ]; flia.
      }
      cbn - [ "*" ].
      f_equal.
      destruct it. {
        apply Nat_eq_log2_up in Hc2; [ | flia Hab4 ].
        cbn in Hc2.
        flia Hza Hc2 Hab4.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small; [ | easy ].
      rewrite Nat.div_small; [ | easy ].
      rewrite fst_if, fst_let.
      cbn - [ "*" ].
      f_equal.
      destruct it; [ easy | ].
      cbn - [ "*" ].
      now rewrite Hab5.
    }
    apply Nat.eqb_neq in Hab5.
    apply Nat_neq_div_1 in Hab5.
    destruct Hab5 as [Hab5| Hab5]. {
      apply Nat.mul_le_mono_pos_l in Hab5; [ | easy ].
      now apply Nat.nlt_ge in Hab5.
    }
    move Hab5 before Hab4.
    rewrite Nat.mod_small; [ | easy ].
    destruct n. {
      rewrite Nat.add_0_r.
      symmetry.
      specialize fst_rank_fst_loop_eq_succ as H1.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split; [ | flia Hab4 ].
        apply Nat.mul_pos_pos; [ easy | ].
        now apply Nat.mul_pos_pos.
      }
      f_equal.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split; [ | flia Hab4 ].
        apply Nat.mul_pos_pos; [ easy | ].
        apply Nat.mul_pos_pos; [ easy | ].
        now apply Nat.mul_pos_pos.
      }
      f_equal.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split; [ | easy ].
        apply Nat.mul_pos_pos; [ easy | ].
        apply Nat.mul_pos_pos; [ easy | ].
        apply Nat.mul_pos_pos; [ easy | ].
        now apply Nat.mul_pos_pos.
      }
      f_equal.
      apply H1; [ | now rewrite Hc2 ].
      split; [ | easy ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      now apply Nat.mul_pos_pos.
    }
clear - Hc2 Hza Hab5.
(*
  Hza : 0 < a
  Hab5 : 2 * (2 * (2 * (2 * (2 * a)))) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (S (S (S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * (2 * (2 * (2 * a)))))) b))))) =
  fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
    rewrite <- Nat.add_succ_comm.
    cbn - [ "*" ].
    rewrite fst_if, S_if, fst_let, S_if, S_if, S_if.
    cbn - [ "*" ].
    remember (2 * (2 * (2 * (2 * (2 * (2 * a))))) / b =? 1) as ab6 eqn:Hab6.
    symmetry in Hab6.
    destruct ab6. {
      cbn - [ "*" ].
      destruct it. {
        apply Nat.log2_up_null in Hc2.
        flia Hza Hab5 Hc2.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      rewrite fst_if, fst_let.
      cbn - [ "*" ].
      f_equal; symmetry.
      destruct it. {
        apply Nat_eq_log2_up in Hc2; [ | flia Hab5 ].
        cbn in Hc2.
        flia Hza Hc2 Hab5.
      }
      cbn - [ "*" ].
      rewrite fst_if, fst_let.
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      cbn - [ "*" ].
      f_equal.
      destruct it. {
        apply Nat_eq_log2_up in Hc2; [ | flia Hab5 ].
        cbn in Hc2.
        flia Hza Hc2 Hab5.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      rewrite fst_if, fst_let.
      cbn - [ "*" ].
      f_equal.
...
(*
clear - Hza Hmab Hbma Hit Hab5.
*)
(*
  Hza : 0 < a
  Hmab : 2 ^ S (S (S (S (S m)))) * a < b
  Hbma : b ≤ 2 ^ S (S (S (S (S (S m))))) * a
  Hit : Nat.log2_up b = S (S (S (S it)))
  Hab5 : 32 * a < b
  ============================
  m = fst (rank_fst_loop it 1 (64 * a) b)
*)
  destruct it. {
    apply Nat_eq_log2_up in Hc2; [ | flia Hab5 ].
    cbn in Hc2.
    flia Hza Hc2 Hab5.
  }
  cbn - [ "*" ].
  rewrite fst_if, fst_let.
  cbn - [ "*" ].
  remember ((64 * a) / b =? 1) as ab6 eqn:Hab6.
  symmetry in Hab6.
  destruct ab6. {
    apply Nat.eqb_eq in Hab6.
    apply Nat_eq_div_1 in Hab6.
    destruct Hab6 as (Hab6, _).
    destruct m; [ easy | exfalso ].
    apply Nat.nle_gt in Hmab.
    apply Hmab; clear Hmab.
    eapply le_trans; [ apply Hab6 | ].
    apply Nat.mul_le_mono_r.
    progress replace 64 with (2 ^ 6) by easy.
    apply Nat.pow_le_mono_r; [ easy | flia ].
  }
  apply Nat.eqb_neq in Hab6.
  apply Nat_neq_div_1 in Hab6.
  destruct Hab6 as [Hab6| Hab6]. {
    progress replace 64 with (2 * 32) in Hab6 by easy.
    rewrite <- Nat.mul_assoc in Hab6.
    apply Nat.mul_le_mono_pos_l in Hab6; [ | easy ].
    now apply Nat.nlt_ge in Hab6.
  }
  clear Hab5.
  rewrite Nat.mod_small; [ | easy ].
  rewrite Nat.mul_assoc.
  progress replace (2 * 64) with 128 by easy.
  destruct m. {
    progress replace (2 ^ 6) with 64 in Hbma by easy.
    now apply Nat.nlt_ge in Hbma.
  }
  f_equal.
... ...
progress replace 128 with (2 ^ S (S 5)) by easy.
apply glop; try easy.
...
(*
  Hza : 0 < a
  Hmab : 2 ^ S (S (S (S (S (S m))))) * a < b
  Hbma : b ≤ 2 ^ S (S (S (S (S (S (S m)))))) * a
  Hit : Nat.log2_up b = S (S (S (S (S it))))
  Hab6 : 64 * a < b
  ============================
  m = fst (rank_fst_loop it 1 (128 * a) b)
*)
(*
  Hza : 0 < a
  Hmab : 2 ^ S (S (S (S (S m)))) * a < b
  Hbma : b ≤ 2 ^ S (S (S (S (S (S m))))) * a
  Hit : Nat.log2_up b = S (S (S (S it)))
  Hab5 : 32 * a < b
  ============================
  m = fst (rank_fst_loop it 1 (64 * a) b)
*)
(*
  Hza : 0 < a
  Hmab : 2 ^ S (S (S (S m))) * a < b
  Hbma : b ≤ 2 ^ S (S (S (S (S m)))) * a
  Hit : Nat.log2_up b = S (S (S it))
  Hab4 : 16 * a < b
  ============================
  m = fst (rank_fst_loop it 1 (32 * a) b)
*)
(*
  Hza : 0 < a
  Hmab : 2 ^ S (S (S m)) * a < b
  Hbma : b ≤ 2 ^ S (S (S (S m))) * a
  Hit : Nat.log2_up b = S (S it)
  Hab3 : 8 * a < b
  ============================
  m = fst (rank_fst_loop it 1 (16 * a) b)
*)
(*
  Hza : 0 < a
  Hmab : 2 ^ S m * a < b
  Hbma : b ≤ 2 ^ S (S m) * a
  Hit : Nat.log2_up b = it
  ============================
  m = fst (rank_fst_loop it 1 (4 * a) b)
*)
...
clear - Hc2 Hza Hab2.
(*
  Hza : 0 < a
  Hab2 : 2 * (2 * a) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * a))) b)) = fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
    rewrite <- Nat.add_succ_comm.
    cbn - [ "*" ].
    rewrite fst_if, S_if, fst_let.
    cbn - [ "*" ].
    remember (2 * (2 * (2 * a)) / b =? 1) as ab3 eqn:Hab3.
    symmetry in Hab3.
    destruct ab3. {
      cbn - [ "*" ].
      destruct it. {
        exfalso.
        apply Nat.log2_up_null in Hc2.
        flia Hza Hc2 Hab2.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small; [ | easy ].
      rewrite Nat.div_small; [ | easy ].
      rewrite fst_if, fst_let.
      cbn - [ "*" ].
      destruct it; [ easy | ].
      cbn - [ "*" ].
      now rewrite Hab3.
    }
    apply Nat.eqb_neq in Hab3.
    apply Nat_neq_div_1 in Hab3.
    destruct Hab3 as [Hab3| Hab3]. {
      apply Nat.mul_le_mono_pos_l in Hab3; [ | easy ].
      now apply Nat.nlt_ge in Hab3.
    }
    move Hab3 before Hab2.
    rewrite Nat.mod_small; [ | easy ].
    destruct n. {
      rewrite Nat.add_0_r.
      symmetry.
      specialize fst_rank_fst_loop_eq_succ as H1.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split; [ | easy ].
        apply Nat.mul_pos_pos; [ easy | ].
        now apply Nat.mul_pos_pos.
      }
      f_equal.
      apply H1; [ | now rewrite Hc2 ].
      split; [ | easy ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      now apply Nat.mul_pos_pos.
    }
clear - Hc2 Hza Hab3.
(*
  Hza : 0 < a
  Hab3 : 2 * (2 * (2 * a)) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * (2 * a)))) b))) = fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
    rewrite <- Nat.add_succ_comm.
    cbn - [ "*" ].
    rewrite fst_if, S_if, fst_let, S_if.
    cbn - [ "*" ].
    remember (2 * (2 * (2 * (2 * a))) / b =? 1) as ab4 eqn:Hab4.
    symmetry in Hab4.
    destruct ab4. {
      cbn - [ "*" ].
      destruct it. {
        apply Nat.log2_up_null in Hc2.
        flia Hza Hab3 Hc2.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab3 ].
        flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab3 ].
        flia.
      }
      rewrite fst_if.
      cbn - [ "*" ].
      rewrite fst_let.
      f_equal; symmetry.
      destruct it. {
        exfalso.
        apply Nat_log2_up_1 in Hc2.
        subst b.
        flia Hza Hab3.
      }
      cbn - [ "*" ].
      rewrite fst_if, fst_let.
      rewrite Nat.mod_small; [ | easy ].
      rewrite Nat.div_small; [ | easy ].
      cbn - [ "*" ].
      destruct it; [ easy | ].
      f_equal.
      cbn - [ "*" ].
      now rewrite Hab4.
    }
    apply Nat.eqb_neq in Hab4.
    apply Nat_neq_div_1 in Hab4.
    destruct Hab4 as [Hab4| Hab4]. {
      apply Nat.mul_le_mono_pos_l in Hab4; [ | easy ].
      now apply Nat.nlt_ge in Hab4.
    }
    move Hab4 before Hab3.
    rewrite Nat.mod_small; [ | easy ].
    destruct n. {
      rewrite Nat.add_0_r.
      symmetry.
      specialize fst_rank_fst_loop_eq_succ as H1.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split. {
          apply Nat.mul_pos_pos; [ easy | ].
          now apply Nat.mul_pos_pos.
        }
        eapply Nat.le_lt_trans; [ | apply Hab3 ].
        flia.
      }
      f_equal.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split; [ | easy ].
        apply Nat.mul_pos_pos; [ easy | ].
        apply Nat.mul_pos_pos; [ easy | ].
        now apply Nat.mul_pos_pos.
      }
      f_equal.
      apply H1; [ | now rewrite Hc2 ].
      split; [ | easy ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      now apply Nat.mul_pos_pos.
    }
clear - Hc2 Hza Hab4.
(*
  Hza : 0 < a
  Hab4 : 2 * (2 * (2 * (2 * a))) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (S (S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * (2 * (2 * a))))) b)))) =
  fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
    rewrite <- Nat.add_succ_comm.
    cbn - [ "*" ].
    rewrite fst_if, S_if, fst_let, S_if, S_if.
    cbn - [ "*" ].
    remember (2 * (2 * (2 * (2 * (2 * a)))) / b =? 1) as ab5 eqn:Hab5.
    symmetry in Hab5.
    destruct ab5. {
      cbn - [ "*" ].
      destruct it. {
        apply Nat.log2_up_null in Hc2.
        flia Hza Hab4 Hc2.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab4 ]; flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab4 ]; flia.
      }
      rewrite fst_if, fst_let.
      cbn - [ "*" ].
      f_equal; symmetry.
      destruct it. {
        apply Nat_log2_up_1 in Hc2.
        subst b.
        flia Hza Hab4.
      }
      cbn - [ "*" ].
      rewrite fst_if, fst_let.
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab4 ]; flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab4 ]; flia.
      }
      cbn - [ "*" ].
      f_equal.
      destruct it. {
        exfalso.
        apply Nat_log2_up_2 in Hc2.
        destruct Hc2; subst b; flia Hza Hab4.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small; [ | easy ].
      rewrite Nat.div_small; [ | easy ].
      rewrite fst_if, fst_let.
      cbn - [ "*" ].
      f_equal.
      destruct it; [ easy | ].
      cbn - [ "*" ].
      now rewrite Hab5.
    }
    apply Nat.eqb_neq in Hab5.
    apply Nat_neq_div_1 in Hab5.
    destruct Hab5 as [Hab5| Hab5]. {
      apply Nat.mul_le_mono_pos_l in Hab5; [ | easy ].
      now apply Nat.nlt_ge in Hab5.
    }
    move Hab5 before Hab4.
    rewrite Nat.mod_small; [ | easy ].
    destruct n. {
      rewrite Nat.add_0_r.
      symmetry.
      specialize fst_rank_fst_loop_eq_succ as H1.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split; [ | flia Hab4 ].
        apply Nat.mul_pos_pos; [ easy | ].
        now apply Nat.mul_pos_pos.
      }
      f_equal.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split; [ | flia Hab4 ].
        apply Nat.mul_pos_pos; [ easy | ].
        apply Nat.mul_pos_pos; [ easy | ].
        now apply Nat.mul_pos_pos.
      }
      f_equal.
      rewrite H1; [ | | now rewrite Hc2 ]. 2: {
        split; [ | easy ].
        apply Nat.mul_pos_pos; [ easy | ].
        apply Nat.mul_pos_pos; [ easy | ].
        apply Nat.mul_pos_pos; [ easy | ].
        now apply Nat.mul_pos_pos.
      }
      f_equal.
      apply H1; [ | now rewrite Hc2 ].
      split; [ | easy ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.mul_pos_pos; [ easy | ].
      now apply Nat.mul_pos_pos.
    }
clear - Hc2 Hza Hab5.
(*
  Hza : 0 < a
  Hab5 : 2 * (2 * (2 * (2 * (2 * a)))) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (S (S (S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * (2 * (2 * (2 * a)))))) b))))) =
  fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
(*
  Hza : 0 < a
  Hab4 : 2 * (2 * (2 * (2 * a))) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (S (S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * (2 * (2 * a))))) b)))) =
  fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
(*
  Hza : 0 < a
  Hab3 : 2 * (2 * (2 * a)) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * (2 * a)))) b))) = fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
(*
  Hza : 0 < a
  Hab2 : 2 * (2 * a) < b
  Hc2 : Nat.log2_up b = it
  ============================
  S (fst (rank_fst_loop (it + S n) 1 (2 * (2 * (2 * a))) b)) = fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
(*
  Hza : 0 < a
  Htab : 2 * a < b
  Hc2 : Nat.log2_up b = it
  ============================
  fst (rank_fst_loop (it + S n) 1 (2 * (2 * a)) b) = fst (rank_fst_loop it 1 (2 * (2 * a)) b)
*)
(*
  Hza : 0 < a
  Hab1 : a < b
  Hc2 : Nat.log2_up b = it
  ============================
  fst (rank_fst_loop (it + S n) 1 (2 * a) b) = fst (rank_fst_loop it 1 (2 * a) b)
*)
specialize (fst_rank_fst_loop_add_l 4 a b it n Hza) as H1.
assert (H : 2 ^ 5 * a < b). {
  now do 4 rewrite Nat.mul_assoc in Hab5.
}
specialize (H1 H Hc2); clear H.
do 6 rewrite Nat.mul_assoc.
easy.
}
...
    rewrite <- Nat.add_succ_comm.
    cbn - [ "*" ].
    rewrite fst_if, S_if, fst_let, S_if, S_if, S_if.
    cbn - [ "*" ].
    remember (2 * (2 * (2 * (2 * (2 * (2 * a))))) / b =? 1) as ab6 eqn:Hab6.
    symmetry in Hab6.
    destruct ab6. {
      cbn - [ "*" ].
      destruct it. {
        apply Nat.log2_up_null in Hc2.
        flia Hza Hab5 Hc2.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      rewrite fst_if, fst_let.
      cbn - [ "*" ].
      f_equal; symmetry.
      destruct it. {
        apply Nat_log2_up_1 in Hc2.
        subst b.
        flia Hza Hab5.
      }
      cbn - [ "*" ].
      rewrite fst_if, fst_let.
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      cbn - [ "*" ].
      f_equal.
      destruct it. {
        exfalso.
        apply Nat_log2_up_2 in Hc2.
        destruct Hc2; subst b; flia Hza Hab5.
      }
      cbn - [ "*" ].
      rewrite Nat.mod_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      rewrite Nat.div_small. 2: {
        eapply Nat.le_lt_trans; [ | apply Hab5 ]; flia.
      }
      rewrite fst_if, fst_let.
      cbn - [ "*" ].
      f_equal.
...
Compute (map (λ n, (n, Nat.log2_up n)) (seq 1 20)).
...
Theorem glop :
  ∀ it a b,
  0 < a ≤ b
  → Nat.log2_up b ≤ it
  → fst (rank_fst_loop it 1 a b) =
    fst (rank_fst_loop (Nat.log2_up b) 1 a b).
Proof.
intros * (Haz, Hab) Hit.
destruct (Nat.eq_dec a b) as [Heab| Heab]. {
  subst b.
  apply Nat.neq_0_lt_0 in Haz.
  rewrite fst_rank_fst_loop_diag; [ | easy ].
  now rewrite fst_rank_fst_loop_diag.
}
specialize (Nat_le_neq_lt _ _ Hab Heab) as H.
clear Hab Heab.
rename H into Hab.
move Hab after Hit.
revert a b Haz Hab Hit.
induction it; intros; cbn - [ "*" ]. {
  apply Nat.le_0_r in Hit.
  apply Nat.log2_up_null in Hit.
  apply Nat.le_1_r in Hit.
  flia Haz Hab Hit.
}
remember (a / b =? 1) as n1 eqn:Hn1.
symmetry in Hn1.
destruct n1. {
  apply Nat.eqb_eq in Hn1.
  now rewrite Nat.div_small in Hn1.
}
rewrite fst_let.
rewrite Nat.mod_small; [ | easy ].
remember (Nat.log2_up b) as c eqn:Hc.
symmetry in Hc.
destruct c. {
  apply Nat.log2_up_null in Hc.
  apply Nat.le_1_r in Hc.
  destruct Hc; subst b; [ easy | flia Haz Hab ].
}
cbn - [ "*" ].
rewrite Nat.mod_small; [ | easy ].
rewrite fst_if.
cbn - [ "*" ].
rewrite fst_let.
rewrite Hn1; f_equal.
apply Nat.succ_le_mono in Hit.
destruct it; [ now apply Nat.le_0_r in Hit; subst c | ].
cbn - [ "*" ].
rewrite fst_if, fst_let.
cbn - [ "*" ].
(**)
destruct (lt_dec b 3) as [Hb3| Hb3]. {
  destruct b; [ easy | ].
  destruct b; [ easy | ].
  destruct b. {
    destruct a; [ easy | ].
    destruct a; [ | flia Hab ].
    rewrite Nat.mul_1_r.
    rewrite Nat.div_same; [ | easy ].
    now destruct c.
  }
  flia Hb3.
}
apply Nat.nlt_ge in Hb3.
apply Nat.eqb_neq in Hn1.
remember (2 * a / b =? 1) as n2 eqn:Hn2.
symmetry in Hn2.
destruct n2. {
  generalize Hn2; intros Hn2v.
  apply Nat.eqb_eq in Hn2.
  apply Nat_eq_div_1 in Hn2.
  destruct Hn2 as (Hn2, _).
  destruct c; [ easy | ].
  cbn - [ "*" ].
  now rewrite Hn2v.
}
apply Nat.eqb_neq in Hn2.
destruct it. {
  cbn - [ "*" ].
  destruct c. {
    exfalso.
    apply (f_equal (λ i, 2 ^ i)) in Hc.
    cbn - [ Nat.log2_up ] in Hc.
    specialize Nat.log2_log2_up_spec as H1.
    assert (H : 0 < b) by flia Haz Hab.
    specialize (H1 _ H); clear H.
    rewrite Hc in H1.
    flia Hb3 H1.
  }
  destruct c; [ | flia Hit ].
  cbn - [ "*" ].
  now apply Nat.eqb_neq in Hn2; rewrite Hn2.
}
cbn - [ "*" ].
rewrite Nat.mul_mod_idemp_r; [ | flia Hab ].
rewrite fst_if, fst_let, S_if.
cbn - [ "*" ].
remember (2 * ((2 * a) mod b) / b =? 1) as n3 eqn:Hn3.
symmetry in Hn3.
destruct n3. {
  destruct c. {
    exfalso.
    apply (f_equal (λ i, 2 ^ i)) in Hc.
    cbn - [ Nat.log2_up ] in Hc.
    specialize Nat.log2_log2_up_spec as H1.
    assert (H : 0 < b) by flia Haz Hab.
    specialize (H1 _ H); clear H.
    rewrite Hc in H1.
    flia Hb3 H1.
  }
  cbn - [ "*" ].
  rewrite fst_if.
  apply Nat.eqb_neq in Hn2; rewrite Hn2.
  rewrite fst_let.
  destruct c; [ easy | ].
  do 2 apply Nat.succ_le_mono in Hit.
  cbn - [ "*" ].
  now rewrite Hn3.
}
destruct it. {
  cbn - [ "*" ].
  destruct c. {
    exfalso.
    apply (f_equal (λ i, 2 ^ i)) in Hc.
    cbn - [ Nat.log2_up ] in Hc.
    specialize Nat.log2_log2_up_spec as H1.
    assert (H : 0 < b) by flia Haz Hab.
    specialize (H1 _ H); clear H.
    rewrite Hc in H1.
    flia Hb3 H1.
  }
  destruct c. {
    exfalso.
    destruct b; [ easy | ].
    destruct b; [ easy | ].
    destruct b. {
      destruct a; [ easy | ].
      destruct a; [ easy | flia Hab ].
    }
    destruct b. {
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | flia Hab ].
    }
    destruct b. {
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | flia Hab ].
    }
    apply (f_equal (λ i, 2 ^ i)) in Hc.
    cbn - [ Nat.log2_up ] in Hc.
    specialize Nat.log2_log2_up_spec as H1.
    specialize (H1 (S (S (S (S (S b))))) (Nat.lt_0_succ _)).
    rewrite Hc in H1.
    flia H1.
  }
  destruct c; [ | flia Hit ].
  cbn - [ "*" ].
  apply Nat.eqb_neq in Hn2; rewrite Hn2.
  rewrite fst_let, fst_if, S_if.
  now rewrite Hn3.
}
cbn - [ "*" ].
rewrite Nat.mul_mod_idemp_r; [ | flia Hab ].
rewrite fst_if, fst_let, S_if, S_if.
cbn - [ "*" ].
rewrite Nat.mul_assoc.
replace (2 * 2) with 4 by easy.
remember (2 * ((4 * a) mod b) / b =? 1) as n4 eqn:Hn4.
symmetry in Hn4.
destruct n4. {
  specialize Nat.log2_log2_up_spec as H1.
  assert (H : 0 < b) by flia Hb3.
  specialize (H1 _ H); clear H.
  rewrite Hc in H1.
  destruct c; [ cbn in H1; flia Hb3 H1 | ].
  destruct c. {
    exfalso.
    cbn in H1.
    destruct (Nat.eq_dec b 3) as [Hb3'| Hb3']. {
      subst b.
      clear it IHit Hc Hit H1 Hb3 Hn1.
      destruct a; [ easy | clear Haz ].
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      flia Hab.
    }
    destruct (Nat.eq_dec b 4) as [Hb4| Hb4]. {
      subst b.
      now rewrite (Nat.mul_comm 4), Nat.mod_mul in Hn4.
    }
    flia Hb3 H1 Hb3' Hb4.
  }
  cbn - [ "*" ].
  apply Nat.eqb_neq in Hn2; rewrite Hn2, Hn3.
  do 2 rewrite fst_let.
  destruct c; [ easy | ].
  cbn - [ "*" ].
  rewrite fst_if, fst_let, S_if, S_if.
  cbn - [ "*" ].
  rewrite Nat.mul_mod_idemp_r; [ | flia Hab ].
  rewrite Nat.mul_assoc.
  replace (2 * 2) with 4 by easy.
  now rewrite Hn4.
}
destruct it. {
  cbn - [ "*" ].
  destruct c. {
    exfalso.
    apply (f_equal (λ i, 2 ^ i)) in Hc.
    cbn - [ Nat.log2_up ] in Hc.
    specialize Nat.log2_log2_up_spec as H1.
    assert (H : 0 < b) by flia Haz Hab.
    specialize (H1 _ H); clear H.
    rewrite Hc in H1.
    flia Hb3 H1.
  }
  destruct c. {
    exfalso.
    destruct b; [ easy | ].
    destruct b; [ easy | ].
    destruct b. {
      destruct a; [ easy | ].
      destruct a; [ easy | flia Hab ].
    }
    destruct b. {
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | flia Hab ].
    }
    destruct b. {
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | flia Hab ].
    }
    apply (f_equal (λ i, 2 ^ i)) in Hc.
    cbn - [ Nat.log2_up ] in Hc.
    specialize Nat.log2_log2_up_spec as H1.
    specialize (H1 (S (S (S (S (S b))))) (Nat.lt_0_succ _)).
    rewrite Hc in H1.
    flia H1.
  }
  destruct c. {
    exfalso.
    clear Hit.
    destruct b; [ easy | ].
    destruct b; [ easy | ].
    destruct b; [ easy | clear Hb3 ].
    destruct b; [ easy | ].
    destruct b; [ easy | ].
    destruct a; [ easy | clear Haz ].
    destruct a. {
      clear Hab Hn1 Hn2 Hn3.
      rewrite Nat.mod_small in Hn4; [ | flia ].
      destruct b; [ easy | ].
      destruct b; [ easy | ].
      destruct b; [ easy | ].
      destruct b; [ easy | ].
      rewrite Nat.div_small in Hn4; [ clear Hn4 | flia ].
Search (Nat.log2_up (S _)).
      destruct b; [ easy | ].
      destruct b; [ easy | ].
...
  destruct c; [ | flia Hit ].
  cbn - [ "*" ].
  apply Nat.eqb_neq in Hn2; rewrite Hn2.
  rewrite fst_let, fst_if, S_if.
  now rewrite Hn3.
}
cbn - [ "*" ].
...
cbn - [ "*" ].
rewrite Nat.mul_mod_idemp_r; [ | flia Hab ].
rewrite fst_if, fst_let, S_if.
cbn - [ "*" ].
remember (2 * ((2 * a) mod b) / b =? 1) as n3 eqn:Hn3.
symmetry in Hn3.
destruct n3. {
...
rewrite Nat.div_small. 2: {
  apply (le_lt_trans _ (2 * (2 * a))). {
    apply Nat.mul_le_mono_l.
    apply Nat.mod_le; flia Hab.
  }
...
Compute (
  let a := 2 in
  map (λ b, let it := Nat.log2_up b + 3 in
  fst (rank_fst_loop it 1 a b) =
  fst (rank_fst_loop (Nat.log2_up b) 1 a b)) (seq 1 40)).
...
Compute (
  let a := 9 in
  map (λ n, let it := Nat.log2_up n + 7 in
  fst (rank_fst_loop it 1 a n) =
  fst (rank_fst_loop (Nat.log2_up n) 1 a n)) (seq a 40)).
...
destruct n; [ easy | ].
cbn - [ "*" ].
...
destruct n; [ easy | ].
rewrite Nat.div_small. 2: {
  apply Nat.lt_add_pos_l.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite Nat.mod_small. 2: {
  apply Nat.lt_add_pos_l.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
cbn.
rewrite fst_let.
rewrite <- Nat.add_1_r; f_equal.
destruct it. {
  cbn.
...
cbn.
rewrite Nat.add_0_r.
...
2 * 2 ^ m / (2 ^ m + 1)
... ...
specialize (glop 0 n) as H1.
cbn in H1.
progress replace (n + 1 - 0) with (n + 1) in H1 by flia.
progress replace (n + 1 + 1) with (n + 2) in H1 by flia.
rewrite Nat.add_1_r in H1.
rewrite <- Nat.add_succ_l in H1.
rewrite Nat.add_0_r in H1.
rewrite <- (Nat.add_1_r n).
apply H1.
...
cbn - [ "/" "mod" "*" Nat.log2_up ].
rewrite fst_if, fst_let, S_if.
remember (2 / (n + 2) =? 1) as sn eqn:Hsn.
symmetry in Hsn.
destruct sn. {
  apply Nat.eqb_eq in Hsn.
  destruct n; [ easy | ].
  rewrite Nat.div_small in Hsn; [ easy | flia ].
}
apply Nat.eqb_neq in Hsn.
destruct n; [ easy | clear Hsn ].
rewrite Nat.mod_small; [ | flia ].
(**)
replace (S (S n)) with (n + 2) in IHn by flia.
replace (S n + 2) with (n + 3) by flia.
do 3 rewrite <- Nat.add_1_r.
rewrite <- Nat.add_assoc.
replace (1 + 1) with 2 by easy.
replace (2 * 2) with 4 by easy.
(*
  ============================
  fst (rank_fst_loop (n + 1) 1 4 (n + 3)) + 2 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 3)) 1 1 (n + 3))
...
specialize (glop 1 n) as H1.
cbn in H1.
progress replace (n + 2 - 1) with (n + 1) in H1 by flia.
progress replace (n + 2 + 1) with (n + 3) in H1 by flia.
rewrite <- Nat.add_assoc in H1.
apply H1.
*)
replace (n + 1) with (S n) by now rewrite Nat.add_comm.
cbn - [ "/" "mod" "*" Nat.log2_up ].
remember (4 / (n + 3) =? 1) as sn eqn:Hsn.
cbn - [ "/" "mod" "*" Nat.log2_up ].
symmetry in Hsn.
destruct sn. {
  apply Nat.eqb_eq in Hsn.
  do 2 (destruct n; [ easy | ]).
  rewrite Nat.div_small in Hsn; [ easy | flia ].
}
apply Nat.eqb_neq in Hsn.
do 2 (destruct n; [ easy | ]).
clear Hsn.
rewrite Nat.mod_small; [ | flia ].
progress replace (S (S n) + 2) with (n + 4) in IHn by flia.
progress replace (S (S n) + 3) with (n + 5) by flia.
rewrite fst_let.
do 3 rewrite <- Nat.add_1_r.
do 2 rewrite <- Nat.add_assoc.
replace (1 + 1) with 2 by easy.
replace (1 + 2) with 3 by easy.
replace (2 * 4) with 8 by easy.
(*
  fst (rank_fst_loop (n + 2)) 1 8 (n + 5)) + 3 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 5)) 1 1 (n + 5))
...
specialize (glop 2 n) as H1.
cbn in H1.
progress replace (n + 4 - 2) with (n + 2) in H1 by flia.
progress replace (n + 4 + 1) with (n + 5) in H1 by flia.
rewrite <- Nat.add_assoc in H1.
apply H1.
*)
replace (n + 2) with (S (n + 1)) by flia.
cbn - [ "/" "mod" "*" Nat.log2_up ].
rewrite fst_if, fst_let.
cbn - [ "/" "mod" "*" Nat.log2_up ].
remember (8 / (n + 5) =? 1) as sn eqn:Hsn.
symmetry in Hsn.
destruct sn. {
  apply Nat.eqb_eq in Hsn.
  do 4 (destruct n; [ easy | ]).
  rewrite Nat.div_small in Hsn; [ easy | flia ].
}
apply Nat.eqb_neq in Hsn.
do 4 (destruct n; [ easy | ]).
clear Hsn.
rewrite Nat.mod_small; [ | flia ].
progress replace (S (S (S (S n))) + 4) with (n + 8) in IHn by flia.
progress replace (S (S (S (S n))) + 5) with (n + 9) by flia.
progress replace (S (S (S (S n))) + 1) with (n + 5) by flia.
rewrite <- Nat.add_1_r.
rewrite <- Nat.add_assoc.
replace (1 + 3) with 4 by easy.
replace (2 * 8) with 16 by easy.
(*
  ============================
  fst (rank_fst_loop (n + 5) 1 16 (n + 9)) + 4 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 9)) 1 1 (n + 9))
...
specialize (glop 3 n) as H1.
cbn in H1.
progress replace (n + 8 - 3) with (n + 5) in H1 by flia.
progress replace (n + 8 + 1) with (n + 9) in H1 by flia.
rewrite <- Nat.add_assoc in H1.
apply H1.
*)
replace (n + 5) with (S (n + 4)) by flia.
cbn - [ "/" "mod" "*" Nat.log2_up ].
rewrite fst_if, fst_let.
cbn - [ "/" "mod" "*" Nat.log2_up ].
replace (2 * 8) with 16 by easy.
remember (16 / (n + 9) =? 1) as sn eqn:Hsn.
symmetry in Hsn.
destruct sn. {
  apply Nat.eqb_eq in Hsn.
  do 8 (destruct n; [ easy | ]).
  rewrite Nat.div_small in Hsn; [ easy | flia ].
}
apply Nat.eqb_neq in Hsn.
do 8 (destruct n; [ easy | ]).
clear Hsn.
rewrite Nat.mod_small; [ | flia ].
replace (S (S (S (S (S (S (S (S n))))))) + 4) with (n + 12) by flia.
replace (2 * 16) with 32 by easy.
replace (S (S (S (S (S (S (S (S n))))))) + 9) with (n + 17) by flia.
progress replace (S (S (S (S (S (S (S (S n))))))) + 8) with (n + 16) in IHn
  by flia.
(*
  ============================
  fst (rank_fst_loop (n + 12) 1 32 (n + 17)) + 5 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 17)) 1 1 (n + 17))
*)
...
specialize (glop 4 n) as H1.
cbn in H1.
progress replace (n + 16 - 4) with (n + 12) in H1 by flia.
progress replace (n + 16 + 1) with (n + 17) in H1 by flia.
rewrite Nat.add_1_r in H1.
rewrite <- Nat.add_succ_l in H1.
apply H1.
...
  m = 4
  fst (rank_fst_loop (n + 2 ^ m - m) 1 (2 ^ (m + 1)) (n + 2 ^ m + 1)) + m + 1 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 2 ^ m + 1)) 1 1 (n + 2 ^ m + 1))
...
  m = 3
  fst (rank_fst_loop (n + 2 ^ m - m) 1 (2 ^ (m + 1)) (n + 2 ^ m + 1)) + m + 1 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 2 ^ m + 1)) 1 1 (n + 2 ^ m + 1))
...
  m = 2
  fst (rank_fst_loop (n + 2 ^ m - m) 1 (2 ^ (m + 1)) (n + 2 ^ m + 1)) + m + 1 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 2 ^ m + 1)) 1 1 (n + 2 ^ m + 1)).
...
...
...
  fst (rank_fst_loop (n + 12) 1 32 (n + 17)) + 5 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 2 ^ 4 + 1)) 1 1 (n + 2 ^ 4 + 1))
...
  fst (rank_fst_loop (n + 5) 1 16 (n + 9)) + 4 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 2 ^ 3 + 1)) 1 1 (n + 2 ^ 3 + 1))
...
  fst (rank_fst_loop (n + 2) 1 8 (n + 5)) + 3 =
  fst (rank_fst_loop (2 ^ Nat.log2_up (n + 2 ^ 2 + 1)) 1 1 (n + 2 ^ 2 + 1)).
...
(**)
...
induction n; [ easy | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
cbn - [ "/" "mod" "*" ].
remember (1 / S n =? 1) as sn1 eqn:Hsn1.
symmetry in Hsn1.
destruct sn1. {
  apply Nat.eqb_eq in Hsn1; cbn.
  destruct n; [ reflexivity | exfalso ].
  now rewrite Nat.div_small in Hsn1.
}
rewrite fst_let.
apply Nat.eqb_neq in Hsn1.
destruct n; [ easy | clear Hnz ].
clear Hsn1.
rewrite Nat.mod_1_l; [ | flia ].
rewrite Nat.mul_1_r.
destruct (Nat.log2_up_succ_or (S (S n))) as [Hn| Hn]. {
  now apply Nat_pow2_log2_up_succ in Hn.
}
rewrite <- Hn.
Search (Nat.log2_up (S _)).
...
specialize (rank_fst_1_1_pow2_lemma (S n) 1) as H1.
specialize (H1 (Nat.log2 (S (S n)))).
rewrite Nat.pow_1_r in H1.
rewrite <- Nat.add_1_l.
rewrite H1; cycle 1. {
easy.
    rewrite < Hn.
    apply Nat.neq_0_lt_0.

...
  replace 2 with (2 ^ 1) at 1 by easy.
  specialize
  apply (H1 (2 ^ S n) 0 n); [ easy | ].
now rewrite Nat.sub_0_r.
Check rank_fst_1_1_pow2.
  rewrite rank_fst_1_1_pow2.
  now rewrite Nat.log2_up_pow2.
...
Theorem glop :
  ∀ a b i,
  0 < a < b
  → rank_fst_1 a b = i
    ↔ (∀ j, j < i → nth j (binary_div b a b) 0 = 0) ∧
       nth i (binary_div b a b) 0 = 1.
Proof.
intros * (Haz, Hab).
(*
destruct (Nat.eq_dec b 1) as [Hb1| Hb1]. {
  subst b.
  now apply Nat.lt_1_r in Hab; subst a.
}
*)
split. {
  intros Habi.
  split. {
    intros j Hji.
    revert i Habi Hji.
    induction j; intros. {
      destruct i; [ easy | clear Hji ].
      replace b with (S (b - 1)) at 1 by flia Hab.
      cbn - [ "/" "mod" "*" ].
      remember (a / b =? 0) as abz eqn:Habz.
      symmetry in Habz.
      destruct abz; cbn - [ "*" ]; [ easy | exfalso ].
      apply Nat.eqb_neq in Habz.
      apply Habz; clear Habz.
      now apply Nat.div_small.
    }
    destruct b; [ easy | ].
    cbn - [ "/" "mod" "*" ].
    apply Nat.div_small in Hab.
    apply Nat.eqb_eq in Hab.
    rewrite Hab.
    cbn - [ "/" "mod" "*" ].
(* mouais, ça va déconner *)
... ...
apply glop.
...
specialize rank_fst_1_1_pow2_lemma as H1.
specialize (H1 (2 ^ Nat.log2_up n) 0 (Nat.log2_up n)).
cbn in H1.
rewrite H1; [ clear H1 | easy | now rewrite Nat.sub_0_r ].
...
  ============================
  fst (rank_fst_loop n 1 1 n) = Nat.log2_up n
...
Qed.
... ...
rewrite rank_fst_1_1_pow2_log2_up.
... ...
progress unfold rank_fst_1.
...
...
(* suite possible de enough_iter *)
...
Search (_ < _ ^ _).
  specialize (Nat.pow_gt_lin_r 2 n) as H1.
Compute (map (λ n, (n, 2 ^ Nat.log2 n)) (seq 1 20)).
...
  destruct n; [ easy | cbn ].
  destruct n; [ easy | cbn ].
  destruct n; [ easy | cbn ].
...
  rewrite Hn.
  rewrite <- IHn.
  progress unfold rank_fst_1.
  rewrite fst_rank_fst_loop_succ.
  remember (1 / S n =? 1) as b eqn:Hb.
  symmetry in Hb.
  destruct b. {
    apply Nat.eqb_eq in Hb.
    destruct n; [ easy | ].
    rewrite Nat.div_small in Hb; [ easy | flia ].
  }
  apply Nat.eqb_neq in Hb.
  f_equal.
  rewrite Nat.mod_1_l. 2: {
    destruct n; [ easy | flia ].
  }
  rewrite Nat.mul_1_r.
  generalize Hn; intros H1.
  apply Nat_pow2_log2_up_succ in H1.
Print rank_fst_loop.
...
Theorem glop :
  ∀ it a n,
  fst (rank_fst_loop it 1 a (2 ^ n)) = n.
Proof.
intros.
Compute (
map (λ a, (a,
  map (λ n, pair (fst (rank_fst_loop (2 ^ n) 1 a (2 ^ n))) (n - Nat.log2 a)) (seq 0 10)))
(seq 1 20)).
(* c'est pas bon *)
...
... ...
rewrite <- H1, glop.
rewrite H1.
...
  map (λ n, Nat.eqb (fst (rank_fst_loop n 1 a (2 ^ n))) (n + 2 ^ Nat.log2_up a)) (seq 0 10)).
...
Theorem glop :
  ∀ n, inv_ub_num n = 2 ^ inv_ub_den_pow2 n / n + 1.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
progress unfold inv_ub_den_pow2.
(*
remember (fst_1_len 1 n) as len eqn:Hlen.
symmetry in Hlen.
*)
rewrite Nat.add_comm.
symmetry.
(*
apply Nat.add_sub_eq_nz. 2: {
  progress unfold inv_ub_num.
  rewrite <- Nat.sub_add_distr.
  rewrite Nat.pow_succ_r'.
  cbn - [ "*" ].
  rewrite Nat_sub_mul_l_diag_l.
  symmetry.
  apply Nat_div_less_small_iff; [ easy | ].
  split. {
...
*)
apply Nat.add_sub_eq_nz. {
  intros H.
  apply Nat.div_small_iff in H; [ | easy ].
  apply Nat.nle_gt in H.
  apply H; clear H.
  rewrite Nat.pow_add_r.
  rewrite <- (Nat.mul_1_r n) at 1.
  apply Nat.mul_le_mono. 2: {
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
Compute (map (λ n, Nat.eqb (Nat.log2_up n) (rank_fst_1 1 n)) (seq 1 200)).
Compute (map (λ n, (2 ^ (rank_fst_1 1 n))) (seq 1 200)).
(*
Compute (map (λ n, n ≤ 2 ^ (rank_fst_1 1 n)) (seq 1 40)).
Compute (map (λ n, Nat.leb n (2 ^ (rank_fst_1 1 n))) (seq 1 200)).
seems good
*)
  progress unfold rank_fst_1.
Print rank_fst_loop.
...
  induction n; [ easy | clear Hnz ].
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    subst n.
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  specialize (IHn Hnz).
  rewrite fst_rank_fst_loop_succ.
  remember (1 / S n =? 1) as b eqn:Hb.
  symmetry in Hb.
  destruct b. {
    apply Nat.eqb_eq in Hb.
    destruct n; [ easy | ].
    rewrite Nat.div_small in Hb; [ easy | flia ].
  }
  apply Nat.eqb_neq in Hb.
  rewrite Nat.mod_1_l. 2: {
    destruct n; [ easy | flia ].
  }
  rewrite Nat.mul_1_r.
Print rank_fst_loop.
...
  rewrite fst_1_len_succ in Hlen.
...
apply Nat.succ_le_mono in Hnm.
specialize (IHn _ Hnm) as H1.
...
Theorem glop :
  ∀ m n,
  n ≤ m
  → n ≤ 2 ^ fst (rank_fst_loop m 1 1 n).
Proof.
intros * Hnm.
revert m Hnm.
induction n; intros; [ easy | ].
destruct m; [ easy | ].
rewrite fst_rank_fst_loop_succ.
remember (1 / S n =? 1) as b eqn:Hb.
symmetry in Hb.
destruct b. {
  apply Nat.eqb_eq in Hb.
  destruct n; [ easy | ].
  rewrite Nat.div_small in Hb; [ easy | flia ].
}
apply Nat.eqb_neq in Hb.
rewrite Nat.mod_1_l. 2: {
  destruct n; [ easy | flia ].
}
rewrite Nat.mul_1_r.
apply Nat.succ_le_mono in Hnm.
specialize (IHn _ Hnm) as H1.
Compute (
  map (λ n,
  let m := n in
  S n <=? 2 ^ S (fst (rank_fst_loop m 1 2 (S n))))
  (seq 1 40)).
...
apply Nat.succ_le_mono in H1.
eapply le_trans; [ apply H1 | ].
Compute (
  map (λ n,
  let m := n in
  S (2 ^ fst (rank_fst_loop m 1 1 n)) <=? 2 ^ S (fst (rank_fst_loop m 1 2 (S n))))
  (seq 1 40)).

...
Compute (map (λ n, n ≤ 2 ^ (rank_fst_1 1 n + fst_1_len 1 n)) (seq 1 40)).
... ...
rewrite glop.
rewrite angle_mul_add_distr_r.
rewrite angle_mul_1_l.
remember (inv_ub_den_pow2 n) as bn eqn:Hbn.
...
(*
Compute (map (λ n, (n, fst_1_len 1 n)) [130]).
Compute (binary_div 40 1 239).
Compute (map (λ n, inv_ub_num n = 2 ^ inv_ub_den_pow2 n / n + 1) [239]).
*)
progress unfold inv_ub_num.
(*
progress unfold inv_ub_den_pow2.
*)
...
  destruct n; [ easy | ].
...
Theorem inv_ub_den_pow2_succ :
  ∀ n, inv_ub_den_pow2 (S n) = 42.
Proof.
intros.
progress unfold inv_ub_den_pow2.
rewrite rank_fst_1_succ_r.
...
  progress unfold rank_fst_1.
  destruct n; [ easy | ].
  destruct n; [ cbn; flia | ].
  destruct n; [ easy | ].
  destruct n; [ cbn; flia | ].
  destruct n; [ cbn; flia | ].
  destruct n; [ cbn; flia | ].
  destruct n; [ cbn; flia | ].
  destruct n; [ cbn; flia | ].
  destruct n. {
    cbn.
...
apply Nat.sub_add_eq_r.
rewrite <- Nat.add_assoc.
rewrite Nat_add_mul_l_diag_
...
progress unfold fst_1_len.
progress unfold rank_fst_1.
cbn.
rewrite Nat.add_0_r.
...
rewrite Nat.pow_succ_r'.
rewrite Nat.pow_add_r.
remember (2 ^ fst_1_len 1 n) as x eqn:Hx.
...
(*
progress unfold inv_ub_den_pow2.
progress unfold fst_1_len.
*)
rewrite Nat.pow_succ_r'.
induction n; [ easy | ].
cbn - [ "/" ].
rewrite Nat.add_0_r.
...
intros * Hn1.
progress unfold inv_ub_num.
progress unfold inv_ub_den_pow2.
cbn.
rewrite Nat.pow_add_r.
rewrite Nat.add_0_r.
progress unfold fst_1_len.
progress unfold rank_fst_1.
...
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
...
Compute (binary_div 10 1 5).
Compute (inv_ub_num 5 / 2).
Compute (2 ^ (inv_ub_den_pow2 5 - 1) / 5).
Compute
  (map (λ n, (inv_ub_num n / 2, 2 ^ (inv_ub_den_pow2 n - 1) / n)) (seq 2 50)).
Compute
  (map (λ n, (inv_ub_num n, 2 ^ (inv_ub_den_pow2 n - 1) / n * 2 + 1)) (seq 2 50)).
Compute
  (map (λ n, (inv_ub_num n, 2 ^ inv_ub_den_pow2 n / n + 1)) (seq 2 50)).
...
an/2 = 2^(bn-1)/n
an = 2^(bn-1)/n*2+1
an = 2^bn/n+1
...
Compute (map (λ n, inv_ub_num n) (seq 1 10)).
Compute (map (λ n, inv_ub_den_pow2 n) (seq 1 10)).
Compute (map (λ n, 2 ^ (inv_ub_den_pow2 n)) (seq 3 10)).
Compute (map (λ n, inv_ub_num n + 1) (seq 3 10)).
...
     = [8; 8; 32; 16; 16; 16; 128; 64; 32; 32]
     : list nat
     = [4; 4; 8; 4; 4; 4; 16; 8; 4; 4]
     : list nat
...
Compute (map (λ n, (2 ^ (inv_ub_den_pow2 n) - 1) / n = inv_ub_num n) (seq 1 10)).
intros.
progress unfold inv_ub_den_pow2.
progress unfold inv_ub_num.
remember (fst_1_len n) as r1 eqn:Hr1.
...
progress unfold inv_ub_num.
progress unfold inv_ub_den_pow2.
remember (rank_fst_1 1 n) as r1 eqn:Hr1.
remember (fst_1_len 1 n) as l1 eqn:Hl1.
move l1 before r1.
(*
progress unfold rank_snd_0 in Hrz.
progress unfold rank_fst_1 in Hr1.
*)
rewrite angle_mul_sub_distr_r. 2: {
  apply Nat.neq_0_lt_0.
  now apply Nat.pow_nonzero.
}
rewrite angle_mul_1_l.
rewrite <- Nat.add_succ_r.
rewrite angle_div_2_pow_add_r at 1.
rewrite angle_div_2_pow_mul_2_pow.
Compute (map (λ n, binary_div 10 1 n) (seq 3 10)).
Compute (map (λ n, (n, inv_ub_num n, inv_ub_den_pow2 n)) (seq 3 10)).
...
destruct (lt_dec (2 ^ i) n) as [Hin| Hin]. {
  rewrite Nat.div_small; [ | easy ].
  apply angle_nonneg.
}
apply Nat.nlt_ge in Hin.
...
destruct (le_dec (inv_ub_den_pow2 n) i) as [Hii| Hii]. {
Theorem glop :
  ∀ a b i j θ,
  j ≤ i
  → (a * θ ≤ b * (θ / ₂^(i-j)))%A
  → (a * (θ / ₂^i) ≤ b * (θ / ₂^j))%A.
Proof.
intros * Hji Hab.
...
  apply glop; [ easy | ].
  progress unfold inv_ub_den_pow2 in Hii.
...
Compute (map (λ n, (n, inv_ub_num n, inv_ub_den_pow2 n)) (seq 3 10)).
Compute (map (λ n, inv_ub_num n) (seq 3 10)).
Compute (map (λ n, inv_ub_den_pow2 n) (seq 3 10)).
Compute (map (λ n, binary_div 10 1 n) (seq 3 10)).
Compute (binary_div 10 1 5).
(* inv_ub_num n is the number formed with this:
     we take the first range of 1s in 1/n in binary,
       e.g. 1/5 = 0.00110011.. this first range is 11
            1/9 = 0.00011100.. this first range is 111
     and take 2 times this number minus 1; in other
     words, this number with another 1 concatenated.
     In the first example, 111, i.e. 7. In the second
     one, 1111, i.e. 15.
   inv_ub_den_pow2 n is the rank of the first 0 in the
     second range of 0s, after the dot, starting at 1
       e.g. 1/5 = 0.00110011.. i.e. 5
            1/9 = 0.00011100.. i.e. 7
...
     = [3; 3; 7; 3; 3; 3; 15; 7; 3; 3]
     : list nat
*)
destruct i. {
  cbn in Hin.
  apply Nat.le_1_r in Hin.
  destruct Hin; [ subst n | easy ].
  apply angle_nonneg.
}
destruct i. {
  cbn in Hin.
  rewrite Nat.pow_1_r.
  destruct n; [ apply angle_nonneg | ].
  destruct n; [ easy | ].
  do 2 apply Nat.succ_le_mono in Hin.
  apply Nat.le_0_r in Hin; subst n.
  rewrite Nat.div_same; [ | easy ].
  rewrite angle_mul_1_l; cbn.
  rewrite angle_add_0_r.
  rewrite angle_add_assoc.
  rewrite angle_add_div_2_diag.
  apply angle_le_add_r.
  apply angle_add_overflow_div_2_div_2.
}
destruct i. {
  cbn in Hin.
  destruct n; [ apply angle_nonneg | ].
  destruct n; [ easy | ].
  do 2 apply Nat.succ_le_mono in Hin.
  destruct n. {
    cbn.
    rewrite angle_add_0_r.
    rewrite angle_add_assoc.
    apply angle_le_add_r.
    rewrite angle_add_div_2_diag.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct n. {
    cbn.
    do 2 rewrite angle_add_0_r.
    rewrite angle_add_assoc.
    rewrite angle_add_div_2_diag.
    apply angle_le_add_r.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct n. {
    cbn.
    do 2 rewrite angle_add_0_r.
    rewrite angle_add_assoc.
    rewrite angle_add_div_2_diag.
    apply angle_le_add_r.
    apply angle_add_overflow_div_2_div_2.
  }
  now do 2 apply Nat.succ_le_mono in Hin.
}
destruct i. {
  cbn in Hin.
  destruct n; [ apply angle_nonneg | ].
  destruct n; [ easy | ].
  do 2 apply Nat.succ_le_mono in Hin.
  destruct n. {
    cbn.
    do 2 rewrite angle_add_0_r.
    do 3 rewrite angle_add_assoc.
    do 2 rewrite angle_add_div_2_diag.
    rewrite <- angle_add_assoc.
    do 2 rewrite angle_add_div_2_diag.
    apply angle_le_add_r.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct n. {
    cbn.
...
induction n; [ apply angle_nonneg | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
destruct (Nat.eq_dec n 1) as [H| H]. {
  subst n.
  destruct i; [ apply angle_nonneg | ].
  rewrite Nat.pow_succ_r', Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
  cbn.
  rewrite angle_add_0_r.
  rewrite angle_add_assoc.
  rewrite angle_add_div_2_diag.
  apply angle_le_add_r.
  apply angle_add_overflow_div_2_div_2.
}
clear Hn1; rename H into Hn1.
specialize (IHn Hn1).
destruct (lt_dec (2 ^ i) (S n)) as [Hin| Hin]. {
  rewrite Nat.div_small; [ | easy ].
  apply angle_nonneg.
}
apply Nat.nlt_ge in Hin.
cbn - [ "/" ].
rewrite Nat.add_0_r.
...
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ subst n; apply angle_nonneg | ].
assert (Hn : 1 < n). {
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  now apply -> Nat.succ_lt_mono.
}
destruct (lt_dec (2 ^ i) n) as [Hin| Hin]. {
  rewrite Nat.div_small; [ | easy ].
  apply angle_nonneg.
}
apply Nat.nlt_ge in Hin.
destruct i; [ now apply Nat.nlt_ge in Hin | ].
destruct i. {
  cbn.
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  destruct n. {
    rewrite Nat.div_same; [ | easy ].
    rewrite angle_mul_1_l.
    cbn.
    rewrite angle_add_0_r.
    rewrite angle_add_assoc.
    rewrite angle_add_div_2_diag.
    apply angle_le_add_r.
    apply angle_add_overflow_div_2_div_2.
  }
  rewrite Nat.div_small; [ | now do 2 apply -> Nat.succ_lt_mono ].
  apply angle_nonneg.
}
clear Hn1 Hnz.
induction n; [ easy | ].
...
destruct n; [ now apply Nat.lt_irrefl in Hn | clear Hn ].
destruct n. {
  rewrite Nat.pow_succ_r', Nat.mul_comm, Nat.div_mul; [ | easy ].
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
  cbn.
  rewrite angle_add_0_r.
  rewrite angle_add_assoc.
  rewrite angle_add_div_2_diag.
  apply angle_le_add_r.
  apply angle_add_overflow_div_2_div_2.
}
assert (H : 1 < S (S n)) by now apply -> Nat.succ_lt_mono.
specialize (IHn H); clear H.
assert (H : S (S n) ≤ 2 ^ S (S i)). {
  eapply le_trans; [ | apply Hin ].
  apply Nat.le_succ_diag_r.
}
specialize (IHn H); clear H.
...
destruct n; [ apply seq_angle_to_div_nat_3_le | ].
destruct n; [ apply seq_angle_to_div_nat_4_le | ].
destruct n; [ apply seq_angle_to_div_nat_5_le | ].
destruct n; [ apply seq_angle_to_div_nat_6_le | ].
destruct n; [ apply seq_angle_to_div_nat_7_le | ].
destruct n; [ apply seq_angle_to_div_nat_8_le | ].
destruct n; [ apply seq_angle_to_div_nat_9_le | ].
...
  cbn - [ "/" "*" "^" angle_div_2_pow ].
  destruct i. {
    cbn.
...
progress unfold inv_ub_num.
progress unfold rank_snd_0.
Print rank_fst_loop.
Theorem rank_fst_loop_succ :
  ∀ it k a b,
  rank_fst_loop (S it) k a b =
    if 2 * a / b =? k then (0, a)
    else let (r, a') := rank_fst_loop it k ((2 * a) mod b) b in (S r, a').
Proof. easy. Qed.
rewrite rank_fst_loop_succ.
...
rewrite <- (angle_div_2_pow_mul_pow_sub (4 + i) 4); [ | apply Nat.le_add_r ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm.
rewrite angle_mul_nat_assoc.
apply angle_mul_le_mono_r. 2: {
  apply Nat.div_le_upper_bound; [ easy | ].
  rewrite Nat.mul_assoc.
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r.
  now do 16 apply -> Nat.succ_le_mono.
}
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ (4 + i))). {
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r.
  now do 3 apply -> Nat.succ_le_mono.
}
apply angle_mul_nat_overflow_pow_div.
Qed.
*)

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
specialize (seq_angle_to_div_nat_5_le i θ) as H2.
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
specialize (seq_angle_to_div_nat_6_le i θ) as H2.
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
specialize (seq_angle_to_div_nat_7_le i θ) as H2.
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

(* to be completed
Theorem angle_add_overflow_mul_by_lt :
  ∀ n i θ θ',
  n ≤ 2 ^ i
  → θ' = seq_angle_to_div_nat θ n i
  → ∀ m, m < n
  → angle_add_overflow θ' (m * θ') = false.
Proof.
intros * Hni Hθ' * Hm.
progress unfold angle_add_overflow.
apply angle_ltb_ge.
rewrite angle_add_mul_r_diag_r.
rewrite Hθ'.
progress unfold seq_angle_to_div_nat.
...
intros * Hni Hθ' * Hm.
destruct m; [ apply angle_add_overflow_0_r | ].
progress unfold angle_add_overflow.
apply angle_ltb_ge.
rewrite angle_add_mul_r_diag_r.
rewrite Hθ'.
progress unfold seq_angle_to_div_nat at 2.
rewrite angle_mul_nat_assoc.
...
specialize (seq_angle_to_div_nat_7_le i θ) as H2.
eapply angle_le_trans; [ apply H2 | clear H2 ].
assert (Hm4 : S (S m) * 2 ≤ 2 ^ 4). {
...
*)

(* to be completed
Theorem angle_mul_nat_not_overflow :
  ∀ n i θ,
  n ≤ 2 ^ i
  → angle_mul_nat_overflow n (seq_angle_to_div_nat θ n i) = false.
Proof.
intros * Hni.
apply angle_all_add_not_overflow.
intros m Hm.
remember (seq_angle_to_div_nat θ n i) as θ' eqn:Hθ'.
progress unfold seq_angle_to_div_nat in Hθ'.
Check angle_add_overflow_mul_by_lt_7.
destruct m; [ apply angle_add_overflow_0_r | ].
progress unfold angle_add_overflow.
apply angle_ltb_ge.
rewrite angle_add_mul_r_diag_r.
rewrite Hθ'.
rewrite angle_mul_nat_assoc.
Check seq_angle_to_div_nat_7_le.
...
specialize (seq_angle_to_div_nat_7_le i θ) as H2.
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
...
progress unfold angle_add_overflow.
apply angle_ltb_ge.
rewrite angle_add_mul_r_diag_r.
...
intros * Hni.
apply angle_all_add_not_overflow.
intros m Hm.
destruct n; [ easy | ].
destruct n. {
  apply Nat.lt_1_r in Hm; subst m.
  rewrite angle_mul_0_l.
  apply angle_add_overflow_0_r.
}
destruct n; [ now apply (angle_add_overflow_mul_by_lt_2 i θ) | ].
destruct n; [ now apply (angle_add_overflow_mul_by_lt_3 i θ) | ].
destruct n; [ now apply (angle_add_overflow_mul_by_lt_4 i θ) | ].
destruct n; [ now apply (angle_add_overflow_mul_by_lt_5 i θ) | ].
destruct n; [ now apply (angle_add_overflow_mul_by_lt_6 i θ) | ].
destruct n; [ now apply (angle_add_overflow_mul_by_lt_7 i θ) | ].
Inspect 17.
...
destruct n; [ now apply (angle_add_overflow_mul_by_lt_9 i θ) | ].
destruct n; [ now apply (angle_add_overflow_mul_by_lt_8 i θ) | ].
destruct n. {
  destruct m; [ apply angle_add_overflow_0_r | ].
  apply Nat.succ_lt_mono in Hm.
  destruct m. {
...
Inspect 10.
(* la règle, c'est que quand on écrit 1/n en base 2, qui s'écrit sous la forme
     0.000011110... ou plutôt 0. un certain nombre de 0, un certain nombre de 1, puis un 0
   on peut le maximiser par
     0.000011111... ou plutôt 0. un certain nombre de 0, un certain nombre de 1, puis un autre 1
*)
...
seq_angle_to_div_nat_3_le : ∀ (i : nat) (θ : angle T), (seq_angle_to_div_nat θ 3 i ≤ 3 * (θ / ₂^3))%A
0.0101010101010 1/4+1/8 = 3/8 ok
seq_angle_to_div_nat_5_le : ∀ (i : nat) (θ : angle T), (seq_angle_to_div_nat θ 5 i ≤ 7 * (θ / ₂^5))%A
0.0011001100110 1/8+1/16+1/32 = 7/32 ok
seq_angle_to_div_nat_6_le : ∀ (i : nat) (θ : angle T), (seq_angle_to_div_nat θ 6 i ≤ 3 * (θ / ₂^4))%A
0.0010101010101 1/8+1/16 = 3/16 ok
seq_angle_to_div_nat_7_le : ∀ (i : nat) (θ : angle T), (seq_angle_to_div_nat θ 7 i ≤ 3 * (θ / ₂^4))%A
0.0010010010010 1/8+1/16 = 3/16 ok
...
(* 1/n = 1/(2^Nat.log2 n-1) + ... *)
(* 1/n-1/(2^Nat.log2 n-1) = (2^Nat.log2 n - S n)/(n * (2^Nat.log2 n - 1)) *)
...
apply (angle_mul_le_mono_l) with (n := S m) in H1. 2: {
  eapply angle_mul_nat_not_overflow_le_l. 2: {
    apply angle_mul_nat_overflow_pow_div.
  }
  apply Nat.le_succ_l.
  apply (Nat.lt_trans _ n); [ easy | ].
(* bin non, of course *)
...
progress unfold angle_leb in H1.
progress unfold angle_leb.
...
rewrite <- (angle_mul_1_l θ') at 1.
apply angle_mul_le_mono_r; [ | now apply -> Nat.succ_le_mono ].
...
specialize (angle_mul_le_mono_l _ _ H1 (S m)) as H2.
...
assert
  (H :
     angle_mul_nat_overflow m (angle_straight / ₂^(Nat.log2 n - 1)) =
       false). {
  eapply angle_mul_nat_not_overflow_le_l. 2: {
    apply angle_mul_nat_overflow_pow_div.
  }
  specialize Nat.log2_spec as H3.
  rewrite Nat.pow_sub_r; [ | easy | ]. 2: {
    apply Nat.log2_le_pow2; [ now destruct n | cbn ].
    destruct n; [ easy | ].
    destruct n; [ easy | ].
    now do 2 apply -> Nat.succ_le_mono.
  }
  rewrite Nat.pow_1_r.
  apply Nat.div_le_lower_bound; [ easy | ].
(**)
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  destruct n; [ cbn; flia Hm | ].
  destruct n. {
    cbn.
    (* faux *)
...
  remember (Nat.log2 n) as p eqn:Hp.
  symmetry in Hp.
  destruct p. {
    apply Nat.log2_null in Hp.
    destruct n; [ easy | ].
    apply Nat.succ_le_mono in Hp.
    apply Nat.le_0_r in Hp.
    now subst n.
  }
  rewrite Nat.pow_succ_r'.
...
    destruct n; [ easy | ].
    destruct n; [ easy | ].
    specialize (Nat.log2_succ_or (S n)) as H4.
    destruct H4 as [H4| H4]. {
      rewrite H4.
      now apply -> Nat.succ_le_mono.
    }
    rewrite H4.
    specialize (Nat_pow2_log2_up_eq (S n)) as H5.
    specialize (Nat_pow2_log2_eq (S n)) as H6.
    cbn - [ Nat.log2 ] in H6.
Search (Nat.log2 (S _)).
...
Search Nat.log2.
...
Search (_ < _ ^ _).
Search (_ ^ (_ - _)).
...
Search (_ ≤ _ ^ _).
...
eapply angle_le_trans; [ apply H1 | ].
...
specialize (angle_div_2_pow_succ_mul_lt_straight Hc1) as H1.
destruct i. {
  cbn in Hni.
  destruct n; [ easy | ].
  apply Nat.succ_le_mono in Hni.
  now apply Nat.le_0_r in Hni; subst n.
}
specialize (H1 (2 ^ S i / n) i).
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