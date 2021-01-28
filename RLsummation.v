(* summations on a ring-like (semiring, ring, field) *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith Permutation.
Require Import Misc RingLike.
Import List List.ListNotations.

Notation "'Σ' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c + g)%F) 0%F)
  (at level 45, i at level 0, b at level 60, e at level 60) :
    ring_like_scope.

Notation "'Σ' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c + g)%F) 0%F)
  (at level 45, i at level 0, l at level 60) :
     ring_like_scope.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

Theorem fold_left_rngl_add_fun_from_0 : ∀ a l (f : nat → _),
  (fold_left (λ c i, c + f i) l a =
   a + fold_left (λ c i, c + f i) l 0)%F.
Proof.
intros.
apply fold_left_op_fun_from_d. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem all_0_rngl_summation_0 : ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i = 0%F)
  → (Σ (i = b, e), f i = 0)%F.
Proof.
intros * Hz.
apply iter_seq_all_d; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_split_first : ∀ b k g,
  b ≤ k
  → (Σ (i = b, k), g i)%F = (g b + Σ (i = S b, k), g i)%F.
Proof.
intros * Hbk.
apply iter_seq_split_first; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_split_last : ∀ b k g,
  b ≤ k
  → (Σ (i = b, k), g i = Σ (i = S b, k), g (i - 1)%nat + g k)%F.
Proof.
intros * Hbk.
now apply iter_seq_split_last.
Qed.

Theorem rngl_summation_split : ∀ j g b k,
  b ≤ S j ≤ S k
  → (Σ (i = b, k), g i = Σ (i = b, j), g i + Σ (i = j+1, k), g i)%F.
Proof.
intros * Hbjk.
apply iter_seq_split; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i = h i)%F)
  → (Σ (i = b, k), g i = Σ (i = b, k), h i)%F.
Proof.
intros * Hgh.
now apply iter_seq_eq_compat.
Qed.

Theorem rngl_summation_succ_succ : ∀ b k g,
  (Σ (i = S b, S k), g i = Σ (i = b, k), g (S i))%F.
Proof.
intros b k g.
apply iter_seq_succ_succ.
Qed.

Theorem rngl_summation_empty : ∀ g b k,
  k < b → (Σ (i = b, k), g i = 0)%F.
Proof.
intros * Hkb.
now apply iter_seq_empty.
Qed.

Theorem rngl_summation_add_distr : ∀ g h b k,
  (Σ (i = b, k), (g i + h i) =
   Σ (i = b, k), g i + Σ (i = b, k), h i)%F.
Proof.
intros g h b k.
apply iter_seq_distr. {
  apply rngl_add_0_l.
} {
  apply rngl_add_comm.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_shift : ∀ b g k,
  b ≤ k
  → (Σ (i = b, k), g i =
     Σ (i = 0, k - b), g (b + i)%nat)%F.
Proof.
intros b g k Hbk.
now apply iter_shift.
Qed.

Theorem rngl_opp_summation :
  rngl_has_opp = true →
  ∀ b e f, ((- Σ (i = b, e), f i) = Σ (i = b, e), (- f i))%F.
Proof.
intros Hro *.
apply iter_seq_inv. {
  now apply rngl_opp_0.
} {
  intros.
  rewrite fold_rngl_sub; [ | easy ].
  rewrite rngl_add_comm.
  now apply rngl_opp_add_distr.
}
Qed.

Theorem rngl_summation_rtl : ∀ g b k,
  (Σ (i = b, k), g i = Σ (i = b, k), g (k + b - i)%nat)%F.
Proof.
intros g b k.
destruct (le_dec (S k) b) as [Hkb| Hkb]. {
  unfold iter_seq.
  cbn - [ "-" ].
  now replace (S k - b) with 0 by flia Hkb.
}
apply Nat.nle_gt in Hkb.
apply -> Nat.lt_succ_r in Hkb.
unfold iter_seq, iter_list.
remember (S k - b) as len eqn:Hlen.
replace k with (b + len - 1) by flia Hkb Hlen.
clear Hlen Hkb.
revert b.
induction len; intros; [ easy | ].
rewrite List_seq_succ_r at 1; cbn.
rewrite fold_left_app; cbn.
symmetry.
rewrite fold_left_rngl_add_fun_from_0.
rewrite rngl_add_comm.
f_equal; [ | rewrite rngl_add_0_l; f_equal; flia ].
rewrite IHlen.
rewrite <- seq_shift.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros j c Hj.
apply in_seq in Hj.
f_equal; f_equal; flia.
Qed.

Theorem mul_iter_seq_distr_l : ∀ A a b e f (add mul : A → A → A) d
    (mul_add_distr_l : ∀ y z, mul a (add y z) = add (mul a y) (mul a z)),
  mul a (iter_seq b e (λ c i, add c (f i)) d) =
  iter_seq b e (λ c i, add c (mul a (f i))) (mul a d).
Proof.
intros.
unfold iter_seq, iter_list.
remember (S e - b) as n eqn:Hn.
clear e Hn.
revert b d.
induction n; intros; [ easy | ].
rewrite List_seq_succ_r.
do 2 rewrite fold_left_app; cbn.
rewrite <- IHn.
apply mul_add_distr_l.
Qed.

Theorem rngl_mul_summation_distr_l : ∀ a b e f,
  (a * (Σ (i = b, e), f i) = Σ (i = b, e), a * f i)%F.
Proof.
intros.
rewrite mul_iter_seq_distr_l; [ | apply rngl_mul_add_distr_l ].
now rewrite rngl_mul_0_r.
Qed.

Theorem rngl_mul_summation_distr_r : ∀ a b e f,
  ((Σ (i = b, e), f i) * a = Σ (i = b, e), f i * a)%F.
Proof.
intros.
unfold iter_seq, iter_list.
remember (S e - b) as n eqn:Hn.
revert e a b Hn.
induction n; intros; [ now apply rngl_mul_0_l | cbn ].
do 2 rewrite rngl_add_0_l.
rewrite fold_left_rngl_add_fun_from_0; symmetry.
rewrite fold_left_rngl_add_fun_from_0; symmetry.
rewrite rngl_mul_add_distr_r.
rewrite (IHn e); [ easy | flia Hn ].
Qed.

Theorem rngl_summation_only_one : ∀ g n, (Σ (i = n, n), g i = g n)%F.
Proof.
intros g n.
unfold iter_seq.
rewrite Nat.sub_succ_l; [ idtac | reflexivity ].
rewrite Nat.sub_diag; simpl.
apply rngl_add_0_l.
Qed.

Theorem rngl_summation_summation_exch : ∀ g k,
  (Σ (j = 0, k), (Σ (i = 0, j), g i j) =
   Σ (i = 0, k), Σ (j = i, k), g i j)%F.
Proof.
intros g k.
induction k; [ easy | ].
rewrite rngl_summation_split_last; [ | apply Nat.le_0_l ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
cbn.
rewrite IHk.
symmetry.
rewrite rngl_summation_split_last; [ | flia ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
cbn.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_summation_split_last; [ | flia Hi ].
  rewrite rngl_summation_succ_succ.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat.sub_succ, Nat.sub_0_r.
  }
  easy.
}
cbn.
rewrite rngl_summation_add_distr.
rewrite <- rngl_add_assoc.
f_equal.
symmetry.
rewrite rngl_summation_split_last; [ | flia ].
rewrite rngl_summation_succ_succ.
rewrite rngl_summation_only_one.
f_equal.
apply rngl_summation_eq_compat.
intros i Hi.
now rewrite Nat.sub_succ, Nat.sub_0_r.
Qed.

Theorem rngl_summation_summation_exch' : ∀ g k l,
  (Σ (j = 0, k), (Σ (i = 0, l), g i j) =
   Σ (i = 0, l), Σ (j = 0, k), g i j)%F.
Proof.
intros.
revert l.
induction k; intros. {
  unfold iter_seq, iter_list.
  cbn; do 3 rewrite rngl_add_0_l.
  apply List_fold_left_ext_in.
  intros i c Hi.
  now rewrite rngl_add_0_l.
}
rewrite rngl_summation_split_last; [ | flia ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat.sub_succ, Nat.sub_0_r.
  }
  easy.
}
cbn.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_summation_split_last; [ | flia ].
  rewrite rngl_summation_succ_succ.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat.sub_succ, Nat.sub_0_r.
  }
  easy.
}
cbn.
rewrite IHk.
apply rngl_summation_add_distr.
Qed.

Theorem fold_left_add_seq_add : ∀ b len i g,
  fold_left (λ (c : T) (j : nat), (c + g i j)%F)
    (seq (b + i) len) 0%F =
  fold_left (λ (c : T) (j : nat), (c + g i (i + j)%nat)%F)
    (seq b len) 0%F.
Proof.
intros.
revert b i.
induction len; intros; [ easy | cbn ].
do 2 rewrite rngl_add_0_l.
rewrite fold_left_rngl_add_fun_from_0; symmetry.
rewrite fold_left_rngl_add_fun_from_0; symmetry.
f_equal; [ now rewrite Nat.add_comm | ].
now rewrite <- IHlen.
Qed.

Theorem rngl_summation_summation_shift : ∀ g k,
  (Σ (i = 0, k), (Σ (j = i, k), g i j) =
   Σ (i = 0, k), Σ (j = 0, k - i), g i (i + j)%nat)%F.
Proof.
intros g k.
apply rngl_summation_eq_compat; intros i Hi.
unfold iter_seq, iter_list.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ | now destruct Hi ].
now rewrite <- fold_left_add_seq_add, Nat.add_0_l.
Qed.

Theorem rngl_summation_ub_add_distr : ∀ a b f,
  (Σ (i = 0, a + b), f i)%F = (Σ (i = 0, a), f i + Σ (i = S a, a + b), f i)%F.
Proof.
intros.
rewrite (rngl_summation_split a); [ | flia ].
now rewrite Nat.add_1_r.
Qed.

Theorem rngl_summation_summation_distr : ∀ a b f,
  (Σ (i = 0, a), Σ (j = 0, b), f i j)%F =
  (Σ (i = 0, (S a * S b - 1)%nat), f (i / S b)%nat (i mod S b))%F.
Proof.
intros.
revert b.
induction a; intros. {
  unfold iter_seq at 1, iter_list at 1.
  cbn - [ "mod" "/" ].
  rewrite rngl_add_0_l, Nat.add_sub.
  apply rngl_summation_eq_compat.
  intros i Hi.
  rewrite Nat.div_small; [ | flia Hi ].
  rewrite Nat.mod_small; [ easy | flia Hi ].
}
rewrite rngl_summation_split_last; [ | flia ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat.sub_succ, Nat.sub_0_r.
  }
  easy.
}
remember (S a) as x.
cbn - [ "mod" "/" ]; subst x.
rewrite IHa.
rewrite Nat.sub_0_r.
rewrite (Nat.add_comm b).
rewrite rngl_summation_ub_add_distr.
rewrite (rngl_summation_split_last _ (S a * S b)); [ | cbn; flia ].
rewrite (rngl_summation_shift 1); [ | cbn; flia ].
rewrite <- rngl_add_assoc.
f_equal. {
  apply rngl_summation_eq_compat.
  intros i Hi.
  now rewrite (Nat.add_comm 1 i), Nat.add_sub.
} {
  rewrite Nat.div_mul; [ | easy ].
  rewrite Nat.mod_mul; [ | easy ].
  destruct b. {
    unfold iter_seq at 1, iter_list at 1.
    cbn - [ "mod" "/" ].
    rewrite rngl_add_0_l.
    rewrite rngl_summation_empty; [ | flia ].
    now rewrite rngl_add_0_r.
  }
  rewrite (rngl_summation_shift (S (S a * S (S b)))); [ | flia ].
  replace (S a * S (S b) + S b - S (S a * S (S b))) with b. 2: {
    cbn.
    rewrite <- Nat.add_succ_l.
    rewrite Nat.sub_add_distr.
    now do 2 rewrite Nat.add_sub.
  }
  rewrite rngl_summation_split_first; [ | flia ].
  f_equal.
  rewrite rngl_summation_succ_succ.
  apply rngl_summation_eq_compat.
  intros i Hi.
  rewrite Nat.add_succ_comm.
  rewrite Nat.div_add_l; [ | easy ].
  rewrite (Nat.div_small (S i)); [ | flia Hi ].
  f_equal; [ symmetry; apply Nat.add_0_r | ].
  rewrite Nat_mod_add_l_mul_r; [ | easy ].
  symmetry.
  apply Nat.mod_small; flia Hi.
}
Qed.

Theorem rngl_summation_list_cons : ∀ A (a : A) la f,
  (Σ (i ∈ a :: la), f i = f a + Σ (i ∈ la), f i)%F.
Proof.
intros.
apply iter_list_cons. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_list_permut : ∀ A (l1 l2 : list A) f,
  Permutation l1 l2
  → (Σ (i ∈ l1), f i = Σ (i ∈ l2), f i)%F.
Proof.
intros * Hl.
apply iter_list_permut; [ | | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_comm.
} {
  apply rngl_add_assoc.
}
Qed.

End a.

Arguments rngl_mul_summation_distr_l {T ro rp} a b e f.
Arguments rngl_mul_summation_distr_r {T ro rp} a b e f.
