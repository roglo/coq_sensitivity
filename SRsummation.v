(* summations on ar semiring *)

Require Import Utf8 Arith.
Require Import Semiring Misc.
Import List List.ListNotations.

Notation "'Σ' ( i = b , e ) , g" :=
  (iterate b e (λ c i, (c + g)%Srng) 0%Srng)
  (at level 45, i at level 0, b at level 60, e at level 60) : semiring_scope.

Notation "'Σ' ( i = b , e ) , g" :=
  (iterate b e (λ c i, (c + g)%Rng) 0%Rng)
  (at level 45, i at level 0, b at level 60, e at level 60) : ring_scope.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so := rng_semiring).
Context {sp : @semiring_prop T (@rng_semiring T ro)}.
Context {rp : @ring_prop T ro}.
Existing Instance so.

Theorem fold_left_srng_add_fun_from_0 : ∀ a l (f : nat → _),
  (fold_left (λ c i, c + f i) l a =
   a + fold_left (λ c i, c + f i) l 0)%Srng.
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply srng_add_0_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite srng_add_0_l.
apply srng_add_assoc.
Qed.

Theorem all_0_srng_summation_0 : ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i = 0%Srng)
  → (Σ (i = b, e), f i = 0)%Srng.
Proof.
intros * Hz.
unfold iterate.
remember (S e - b) as n eqn:Hn.
revert b Hz Hn.
induction n; intros; [ easy | cbn ].
rewrite fold_left_srng_add_fun_from_0.
rewrite IHn; [ | | flia Hn ]. {
  rewrite Hz; [ | flia Hn ].
  rewrite srng_add_0_l.
  now rewrite srng_add_0_l.
}
intros i Hi.
apply Hz; flia Hi.
Qed.

Theorem rng_opp_add_distr : ∀ a b, (- (a + b) = - a - b)%Rng.
Proof.
intros.
apply (rng_add_reg_l _ _ (b + a)%Rng).
unfold rng_sub.
rewrite srng_add_assoc.
do 3 rewrite fold_rng_sub.
rewrite rng_add_sub.
rewrite srng_add_comm.
now do 2 rewrite rng_add_opp_r.
Qed.

Theorem rng_opp_summation : ∀ b e f,
  ((- Σ (i = b, e), f i) = Σ (i = b, e), (- f i))%Rng.
Proof.
intros.
unfold iterate.
remember (S e - b) as len.
clear e Heqlen.
revert b.
induction len; intros; [ apply rng_opp_0 | ].
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite fold_left_app; cbn.
rewrite <- IHlen.
now rewrite rng_opp_add_distr.
Qed.

Theorem srng_summation_split_first : ∀ b k g,
  b ≤ k
  → (Σ (i = b, k), g i)%Srng = (g b + Σ (i = S b, k), g i)%Srng.
Proof.
intros * Hbk.
unfold iterate.
remember (S k - b) as len eqn:Hlen.
replace (S k - S b) with (len - 1) by flia Hlen.
assert (H : len ≠ 0) by flia Hlen Hbk.
clear k Hbk Hlen.
rename H into Hlen.
destruct len; [ easy | cbn ].
rewrite srng_add_0_l, Nat.sub_0_r.
apply fold_left_srng_add_fun_from_0.
Qed.

Theorem srng_summation_split_last : ∀ b k g,
  b ≤ k
  → (Σ (i = b, k), g i = Σ (i = S b, k), g (i - 1) + g k)%Srng.
Proof.
intros * Hbk.
unfold iterate.
remember (S k - S b) as len eqn:Hlen.
rewrite Nat.sub_succ in Hlen.
replace (S k - b) with (S len) by flia Hbk Hlen.
replace k with (b + len) by flia Hbk Hlen.
rewrite <- seq_shift.
rewrite List_fold_left_map.
rewrite List_seq_succ_r.
rewrite fold_left_app.
cbn; f_equal.
apply List_fold_left_ext_in.
intros i c Hi.
now rewrite Nat.sub_0_r.
Qed.

Theorem srng_summation_rtl : ∀ g b k,
  (Σ (i = b, k), g i = Σ (i = b, k), g (k + b - i)%nat)%Srng.
Proof.
intros g b k.
destruct (le_dec (S k) b) as [Hkb| Hkb]. {
  unfold iterate.
  cbn - [ "-" ].
  now replace (S k - b) with 0 by flia Hkb.
}
apply Nat.nle_gt in Hkb.
apply -> Nat.lt_succ_r in Hkb.
unfold iterate.
remember (S k - b) as len eqn:Hlen.
replace k with (b + len - 1) by flia Hkb Hlen.
clear Hlen Hkb.
revert b.
induction len; intros; [ easy | ].
rewrite List_seq_succ_r at 1; cbn.
rewrite fold_left_app; cbn.
symmetry.
rewrite fold_left_srng_add_fun_from_0.
rewrite srng_add_comm.
f_equal; [ | rewrite srng_add_0_l; f_equal; flia ].
rewrite IHlen.
rewrite <- seq_shift.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros j c Hj.
apply in_seq in Hj.
f_equal; f_equal; flia.
Qed.

Theorem srng_summation_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i = h i)%Srng)
  → (Σ (i = b, k), g i = Σ (i = b, k), h i)%Srng.
Proof.
intros * Hgh.
unfold iterate.
remember (S k - b) as len eqn:Hlen.
assert (∀ i, b ≤ i < b + len → g i = h i). {
  intros i Hi.
  apply Hgh; flia Hlen Hi.
}
clear k Hgh Hlen.
rename H into Hb.
revert b Hb.
induction len; intros; [ easy | cbn ].
do 2 rewrite srng_add_0_l.
rewrite fold_left_srng_add_fun_from_0; symmetry.
rewrite fold_left_srng_add_fun_from_0; symmetry.
f_equal; [ apply Hb; flia | ].
apply IHlen.
intros i Hi.
apply Hb.
flia Hi.
Qed.

Theorem srng_summation_empty : ∀ g b k,
  k < b → (Σ (i = b, k), g i = 0)%Srng.
Proof.
intros * Hkb.
unfold iterate.
now replace (S k - b) with 0 by flia Hkb.
Qed.

Theorem srng_summation_succ_succ : ∀ b k g,
  (Σ (i = S b, S k), g i = Σ (i = b, k), g (S i))%Srng.
Proof.
intros b k g.
unfold iterate.
rewrite Nat.sub_succ.
remember (S k - b)%nat as len; clear Heqlen.
rewrite <- seq_shift.
now rewrite List_fold_left_map.
Qed.

Theorem srng_summation_add_distr : ∀ g h b k,
  (Σ (i = b, k), (g i + h i) =
   Σ (i = b, k), g i + Σ (i = b, k), h i)%Srng.
Proof.
intros g h b k.
destruct (le_dec b k) as [Hbk| Hbk]. {
  revert b Hbk.
  induction k; intros. {
    apply Nat.le_0_r in Hbk; subst b; cbn.
    now do 3 rewrite srng_add_0_l.
  }
  rewrite (srng_summation_split_last b); [ | easy ].
  rewrite (srng_summation_split_last b); [ | easy ].
  rewrite (srng_summation_split_last b); [ | easy ].
  do 2 rewrite srng_add_assoc; f_equal.
  rewrite srng_add_add_swap; f_equal.
  destruct (eq_nat_dec b (S k)) as [Hbek| Hbek]. {
    subst b.
    rewrite srng_summation_empty; [ | flia ].
    rewrite srng_summation_empty; [ | flia ].
    rewrite srng_summation_empty; [ | flia ].
    symmetry; apply srng_add_0_l.
  }
  do 3 rewrite srng_summation_succ_succ.
  rewrite srng_summation_eq_compat
    with (h := λ i, (g i + h i)%Srng). 2: {
    intros * Hi.
    now rewrite Nat.sub_succ, Nat.sub_0_r.
  }
  rewrite IHk; [ | flia Hbk Hbek ].
  now f_equal; apply srng_summation_eq_compat; intros i Hi;
    rewrite Nat.sub_succ, Nat.sub_0_r.
}
apply Nat.nle_gt in Hbk.
rewrite srng_summation_empty; [ | easy ].
rewrite srng_summation_empty; [ | easy ].
rewrite srng_summation_empty; [ | easy ].
symmetry; apply srng_add_0_l.
Qed.

Theorem srng_summation_split : ∀ j g b k,
  b ≤ S j ≤ S k
  → (Σ (i = b, k), g i = Σ (i = b, j), g i + Σ (i = j+1, k), g i)%Srng.
Proof.
intros * (Hbj, Hjk).
unfold iterate.
remember (S j - b) as len1 eqn:Hlen1.
remember (S k - b) as len2 eqn:Hlen2.
move len2 before len1.
replace (S k - (j + 1)) with (len2 - len1) by flia Hlen1 Hlen2 Hbj.
replace (j + 1) with (b + len1) by flia Hlen1 Hbj.
assert (Hll : len1 ≤ len2) by flia Hlen1 Hlen2 Hjk.
clear - sp Hll.
revert b len2 Hll.
induction len1; intros. {
  now cbn; rewrite srng_add_0_l, Nat.add_0_r, Nat.sub_0_r.
}
destruct len2; [ flia Hll | ].
apply Nat.succ_le_mono in Hll; cbn.
rewrite srng_add_0_l.
rewrite (fold_left_srng_add_fun_from_0 (g b)).
rewrite (fold_left_srng_add_fun_from_0 (g b)).
rewrite <- srng_add_assoc; f_equal.
replace len2 with (len1 + (len2 - len1)) at 1 by flia Hll.
rewrite seq_app, fold_left_app.
rewrite fold_left_srng_add_fun_from_0.
now rewrite Nat.add_succ_comm.
Qed.

End in_ring.
