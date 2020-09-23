(* summations on ar semiring *)

Require Import Utf8 Arith.
Require Import Semiring Misc.
Import List.

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, (c + g)%Srng) (seq b (S e - b)) 0%Srng)
  (at level 45, i at level 0, b at level 60, e at level 60) : semiring_scope.

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, (c + g)%Rng) (seq b (S e - b)) 0%Rng)
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

Theorem srng_summation_split_first : ∀ g b k,
  b ≤ k
  → (Σ (i = b, k), g i)%Srng = (g b + Σ (i = S b, k), g i)%Srng.
Proof.
intros g b k Hbk.
remember (S k - b) as len eqn:Hlen.
replace (S k - S b) with (len - 1) by flia Hlen.
assert (H : len ≠ 0) by flia Hlen Hbk.
clear k Hbk Hlen.
rename H into Hlen.
revert b.
induction len; intros; [ easy | clear Hlen ].
destruct len; [ apply srng_add_comm | ].
remember (S len) as slen; cbn; subst slen.
rewrite Nat.sub_0_r.
rewrite srng_add_0_l.
apply fold_left_srng_add_fun_from_0.
Qed.

Theorem srng_summation_rtl : ∀ g b k,
  (Σ (i = b, k), g i = Σ (i = b, k), g (k + b - i)%nat)%Srng.
Proof.
intros g b k.
destruct (le_dec (S k) b) as [Hkb| Hkb]. {
  cbn - [ "-" ].
  now replace (S k - b) with 0 by flia Hkb.
}
apply Nat.nle_gt in Hkb.
apply -> Nat.lt_succ_r in Hkb.
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

End in_ring.
