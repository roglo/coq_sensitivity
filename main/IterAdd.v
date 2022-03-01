(* summations on a ring-like (semiring, ring, field) *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith Permutation.
Require Import Misc RingLike.
Import List List.ListNotations.

Notation "'∑' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c + g)%F) 0%F)
  (at level 45, i at level 0, b at level 60, e at level 60).

Notation "'∑' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c + g)%F) 0%F)
  (at level 45, i at level 0, l at level 60).

Notation "'nat_∑' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c + g)) 0)
  (at level 45, i at level 0, b at level 60, e at level 60).

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.
Context {Hom : rngl_has_opp = true ∨ rngl_has_sous = true}.

Theorem fold_left_rngl_add_fun_from_0 : ∀ A a l (f : A → _),
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

Theorem all_0_rngl_summation_list_0 : ∀ A l (f : A → T),
  (∀ i, i ∈ l → f i = 0%F)
  → ∑ (i ∈ l), f i = 0%F.
Proof.
intros * Hz.
apply iter_list_all_d; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem all_0_rngl_summation_0 : ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i = 0%F)
  → ∑ (i = b, e), f i = 0%F.
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

Theorem rngl_summation_list_split_first : ∀ A (l : list A) d f,
  l ≠ []
  → ∑ (i ∈ l), f i = (f (hd d l) + ∑ (i ∈ tl l), f i)%F.
Proof.
intros * Hlz.
apply iter_list_split_first; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_list_split_last : ∀ A (l : list A) d f,
  l ≠ []
  → ∑ (i ∈ l), f i = (∑ (i ∈ removelast l), f i + f (last l d))%F.
Proof.
intros * Hlz.
now apply iter_list_split_last.
Qed.

Theorem rngl_summation_list_split : ∀ A (l : list A) f n,
  ∑ (i ∈ l), f i = (∑ (i ∈ firstn n l), f i + ∑ (i ∈ skipn n l), f i)%F.
Proof.
intros.
rewrite <- firstn_skipn with (n := n) (l := l) at 1.
unfold iter_list.
rewrite fold_left_app.
now rewrite fold_left_rngl_add_fun_from_0.
Qed.

Theorem rngl_summation_split_first : ∀ b k g,
  b ≤ k
  → ∑ (i = b, k), g i = (g b + ∑ (i = S b, k), g i)%F.
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
  → (∑ (i = b, k), g i = ∑ (i = S b, k), g (i - 1)%nat + g k)%F.
Proof.
intros * Hbk.
now apply iter_seq_split_last.
Qed.

Theorem rngl_summation_split : ∀ j g b k,
  b ≤ S j ≤ S k
  → (∑ (i = b, k), g i = ∑ (i = b, j), g i + ∑ (i = j+1, k), g i)%F.
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

Theorem rngl_summation_split3 : ∀ j g b k,
  b ≤ j ≤ k
  → ∑ (i = b, k), g i =
       (∑ (i = S b, j), g (i - 1)%nat + g j + ∑ (i = j + 1, k), g i)%F.
Proof.
intros * Hj.
apply iter_seq_split3; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
(*
rewrite rngl_summation_split with (j := j); [ | flia Hj ].
now rewrite rngl_summation_split_last.
*)
Qed.

Theorem rngl_summation_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i = h i)%F)
  → (∑ (i = b, k), g i = ∑ (i = b, k), h i)%F.
Proof.
intros * Hgh.
now apply iter_seq_eq_compat.
Qed.

Theorem rngl_summation_list_eq_compat : ∀ A g h (l : list A),
  (∀ i, i ∈ l → (g i = h i)%F)
  → (∑ (i ∈ l), g i = ∑ (i ∈ l), h i)%F.
Proof.
intros * Hgh.
now apply iter_list_eq_compat.
Qed.

Theorem rngl_summation_succ_succ : ∀ b k g,
  (∑ (i = S b, S k), g i = ∑ (i = b, k), g (S i))%F.
Proof.
intros b k g.
apply iter_seq_succ_succ.
Qed.

Theorem rngl_summation_list_empty : ∀ A g (l : list A),
  l = [] → ∑ (i ∈ l), g i = 0%F.
Proof.
intros * Hl.
now apply iter_list_empty.
Qed.

Theorem rngl_summation_empty : ∀ g b k,
  k < b → (∑ (i = b, k), g i = 0)%F.
Proof.
intros * Hkb.
now apply iter_seq_empty.
Qed.

Theorem rngl_summation_add_distr : ∀ g h b k,
  (∑ (i = b, k), (g i + h i) =
   ∑ (i = b, k), g i + ∑ (i = b, k), h i)%F.
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

Theorem rngl_summation_shift : ∀ s b g k,
  s ≤ b ≤ k
  → ∑ (i = b, k), g i = ∑ (i = b - s, k - s), g (s + i)%nat.
Proof.
intros s b g k Hbk.
now apply (iter_shift s).
Qed.

Theorem rngl_summation_rshift : ∀ b e f,
  ∑ (i = b, e), f i = ∑ (i = S b, S e), f (i - 1)%nat.
Proof.
intros.
rewrite rngl_summation_succ_succ.
apply rngl_summation_eq_compat.
intros i Hi.
now rewrite Nat_sub_succ_1.
Qed.

Theorem rngl_opp_summation :
  rngl_has_opp = true →
  ∀ b e f, ((- ∑ (i = b, e), f i) = ∑ (i = b, e), (- f i))%F.
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
  (∑ (i = b, k), g i = ∑ (i = b, k), g (k + b - i)%nat)%F.
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
rewrite seq_S at 1; cbn.
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

Theorem mul_iter_list_distr_l : ∀ A B a (la : list B) f
    (add mul : A → A → A) d
    (mul_add_distr_l : ∀ y z, mul a (add y z) = add (mul a y) (mul a z)),
  mul a (iter_list la (λ c i, add c (f i)) d) =
  iter_list la (λ c i, add c (mul a (f i))) (mul a d).
Proof.
intros.
clear Hom.
unfold iter_list.
revert d.
induction la as [| a1]; intros; [ easy | cbn ].
rewrite IHla.
f_equal.
apply mul_add_distr_l.
Qed.

Theorem rngl_mul_summation_list_distr_l : ∀ A a (la : list A) f,
  (a * (∑ (i ∈ la), f i) = ∑ (i ∈ la), a * f i)%F.
Proof.
intros.
rewrite mul_iter_list_distr_l; [ | apply rngl_mul_add_distr_l ].
now rewrite rngl_mul_0_r.
Qed.

Theorem rngl_mul_summation_distr_l : ∀ a b e f,
  (a * (∑ (i = b, e), f i) = ∑ (i = b, e), a * f i)%F.
Proof.
intros.
apply rngl_mul_summation_list_distr_l.
Qed.

Theorem rngl_mul_summation_distr_r : ∀ a b e f,
  ((∑ (i = b, e), f i) * a = ∑ (i = b, e), f i * a)%F.
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

Theorem rngl_summation_list_only_one : ∀ A g (a : A),
  (∑ (i ∈ [a]), g i = g a)%F.
Proof.
intros.
unfold iter_list; cbn.
apply rngl_add_0_l.
Qed.

Theorem rngl_summation_only_one : ∀ g n, (∑ (i = n, n), g i = g n)%F.
Proof.
intros g n.
unfold iter_seq.
rewrite Nat.sub_succ_l; [ idtac | reflexivity ].
rewrite Nat.sub_diag; simpl.
apply rngl_add_0_l.
Qed.

Theorem rngl_summation_summation_exch : ∀ g k,
  (∑ (j = 0, k), (∑ (i = 0, j), g i j) =
   ∑ (i = 0, k), ∑ (j = i, k), g i j)%F.
Proof.
intros g k.
induction k; [ easy | ].
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat_sub_succ_1.
}
cbn.
rewrite IHk.
symmetry.
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat_sub_succ_1.
}
cbn.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_summation_split_last; [ | flia Hi ].
  rewrite rngl_summation_succ_succ.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat_sub_succ_1.
  }
  easy.
}
cbn.
rewrite rngl_summation_add_distr.
rewrite <- rngl_add_assoc.
f_equal.
symmetry.
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_succ_succ.
rewrite rngl_summation_only_one.
f_equal.
apply rngl_summation_eq_compat.
intros i Hi.
now rewrite Nat_sub_succ_1.
Qed.

Theorem rngl_summation_summation_exch' : ∀ g k l,
  (∑ (j = 0, k), (∑ (i = 0, l), g i j) =
   ∑ (i = 0, l), ∑ (j = 0, k), g i j)%F.
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
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat_sub_succ_1.
  }
  easy.
}
cbn.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_summation_split_last; [ | easy ].
  rewrite rngl_summation_succ_succ.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat_sub_succ_1.
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
  (∑ (i = 0, k), (∑ (j = i, k), g i j) =
   ∑ (i = 0, k), ∑ (j = 0, k - i), g i (i + j)%nat)%F.
Proof.
intros g k.
apply rngl_summation_eq_compat; intros i Hi.
unfold iter_seq, iter_list.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ | now destruct Hi ].
now rewrite <- fold_left_add_seq_add, Nat.add_0_l.
Qed.

Theorem rngl_summation_ub_add_distr : ∀ a b f,
  (∑ (i = 0, a + b), f i)%F = (∑ (i = 0, a), f i + ∑ (i = S a, a + b), f i)%F.
Proof.
intros.
rewrite (rngl_summation_split a); [ | flia ].
now rewrite Nat.add_1_r.
Qed.

Theorem rngl_summation_ub_mul_distr : ∀ a b f,
  ∑ (k = 1, a * b), f k = ∑ (i = 1, a), ∑ (j = 1, b), f (b * (i - 1) + j)%nat.
Proof.
intros.
destruct a. {
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  easy.
}
destruct b. {
  rewrite Nat.mul_comm; cbn.
  rewrite rngl_summation_empty; [ | easy ].
  now symmetry; apply all_0_rngl_summation_0.
}
rewrite (rngl_summation_shift 1); [ | cbn; flia ].
symmetry.
rewrite (rngl_summation_shift 1); [ | cbn; flia ].
rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite (rngl_summation_shift 1); [ | flia ].
  rewrite Nat_sub_succ_1.
  remember (S b) as b'; cbn; subst b'.
  easy.
}
symmetry.
induction a. {
  cbn.
  rewrite Nat.add_0_r, Nat.sub_0_r.
  rewrite rngl_summation_only_one.
  rewrite Nat.add_0_l.
  now rewrite Nat.mul_0_r.
}
rewrite Nat.mul_succ_l.
rewrite Nat.add_sub_swap; [ | cbn; flia ].
rewrite rngl_summation_ub_add_distr.
rewrite IHa.
symmetry.
do 3 rewrite Nat_sub_succ_1.
rewrite <- Nat.add_1_r at 1.
rewrite rngl_summation_ub_add_distr.
f_equal.
rewrite Nat.add_1_r at 1.
rewrite rngl_summation_only_one.
replace (S (S a * S b - 1)) with (S a * S b) by (cbn; flia).
replace (S a * S b - 1 + S b) with (S a * S b + b) by (cbn; flia).
symmetry.
rewrite (rngl_summation_shift (S a * S b)); [ | flia ].
rewrite Nat.sub_diag.
rewrite Nat.add_sub_swap; [ | easy ].
rewrite Nat.sub_diag, Nat.add_0_l.
apply rngl_summation_eq_compat.
intros i Hi.
f_equal; flia.
Qed.

Theorem rngl_summation_summation_distr : ∀ a b f,
  (∑ (i = 0, a), ∑ (j = 0, b), f i j)%F =
  (∑ (i = 0, (S a * S b - 1)%nat), f (i / S b)%nat (i mod S b))%F.
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
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat_sub_succ_1.
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
symmetry.
rewrite (rngl_summation_shift 1); [ | cbn; flia ].
symmetry.
rewrite Nat.sub_diag.
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
  symmetry.
  rewrite (rngl_summation_shift (S (S a * S (S b)))); [ | flia ].
  symmetry.
  rewrite Nat.sub_diag.
  replace (S a * S (S b) + S b - S (S a * S (S b))) with b. 2: {
    cbn.
    rewrite <- Nat.add_succ_l.
    rewrite Nat.sub_add_distr.
    now do 2 rewrite Nat.add_sub.
  }
  rewrite rngl_summation_split_first; [ | easy ].
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
  (∑ (i ∈ a :: la), f i = f a + ∑ (i ∈ la), f i)%F.
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

Theorem rngl_summation_list_app : ∀ A (la lb : list A) f,
  ∑ (i ∈ la ++ lb), f i = (∑ (i ∈ la), f i + ∑ (i ∈ lb), f i)%F.
Proof.
intros.
rewrite iter_list_app.
unfold iter_list.
apply fold_left_rngl_add_fun_from_0.
Qed.

Theorem rngl_summation_list_permut : ∀ A (l1 l2 : list A) f,
  Permutation l1 l2
  → (∑ (i ∈ l1), f i = ∑ (i ∈ l2), f i)%F.
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

Theorem rngl_summation_seq_summation : ∀ b len f,
  len ≠ 0
  → (∑ (i ∈ seq b len), f i = ∑ (i = b, b + len - 1), f i)%F.
Proof.
intros * Hlen.
unfold iter_seq.
f_equal; f_equal.
flia Hlen.
Qed.

Theorem rngl_summation_map_seq : ∀ A start len (f : A → T) g,
  (∑ (i ∈ map g (seq start len)), f i =
   ∑ (i ∈ seq start len), f (g i))%F.
Proof.
intros.
revert start.
induction len; intros; [ easy | cbn ].
rewrite rngl_summation_list_cons.
rewrite rngl_summation_list_cons.
f_equal.
apply IHlen.
Qed.

Theorem rngl_summation_mul_summation : ∀ bi bj ei ej f g,
  ((∑ (i = bi, ei), f i) * (∑ (j = bj, ej), g j))%F =
  ∑ (i = bi, ei), (∑ (j = bj, ej), f i * g j).
Proof.
intros.
unfold iter_seq.
remember (S ei - bi) as leni eqn:Hi.
remember (S ej - bj) as lenj eqn:Hj.
clear ei ej Hi Hj.
(* lemma for summation_list to do *)
induction leni. {
  rewrite rngl_summation_list_empty; [ symmetry | easy ].
  rewrite rngl_summation_list_empty; [ symmetry | easy ].
  now apply rngl_mul_0_l.
}
rewrite seq_S.
do 2 rewrite rngl_summation_list_app.
do 2 rewrite rngl_summation_list_only_one.
rewrite rngl_mul_add_distr_r.
rewrite IHleni; f_equal.
now apply rngl_mul_summation_list_distr_l.
Qed.

Theorem rngl_summation_list_change_var :
  ∀ A B (f : A → B) (g : B → _) l,
  ∑ (i ∈ l), g (f i) = ∑ (j ∈ map f l), g j.
Proof.
intros.
unfold iter_list.
rewrite List_fold_left_map.
now apply rngl_summation_list_eq_compat.
Qed.

Theorem rngl_summation_change_var : ∀ A b e f g (h : _ → A),
  (∀ i, b ≤ i ≤ e → g (h i) = i)
  → ∑ (i = b, e), f i = ∑ (i ∈ map h (seq b (S e - b))), f (g i).
Proof.
intros * Hgh.
rewrite rngl_summation_map_seq.
unfold iter_seq.
apply rngl_summation_list_eq_compat.
intros i Hi.
apply in_seq in Hi.
rewrite Hgh; [ easy | ].
flia Hi.
Qed.

Theorem rngl_summation_permut : ∀ n l1 l2,
  Permutation l1 l2
  → length l1 = n
  → length l2 = n
  → ∑ (i = 0, n - 1), nth i l1 0 = ∑ (i = 0, n - 1), nth i l2 0.
Proof.
intros * Hl H1 H2.
destruct n. {
  apply length_zero_iff_nil in H1.
  apply length_zero_iff_nil in H2.
  now subst l1 l2.
}
rewrite Nat_sub_succ_1.
revert n H1 H2.
induction Hl; intros; [ easy | | | ]. {
  cbn in H1, H2.
  apply Nat.succ_inj in H1.
  apply Nat.succ_inj in H2.
  rewrite rngl_summation_split_first; [ symmetry | easy ].
  rewrite rngl_summation_split_first; [ symmetry | easy ].
  destruct n; [ easy | ].
  do 2 rewrite rngl_summation_succ_succ.
  now rewrite IHHl.
} {
  destruct n; [ easy | ].
  cbn in H1, H2.
  do 2 apply Nat.succ_inj in H1.
  do 2 apply Nat.succ_inj in H2.
  rewrite rngl_summation_split_first; [ symmetry | easy ].
  rewrite rngl_summation_split_first; [ symmetry | easy ].
  rewrite rngl_summation_split_first; [ symmetry | flia ].
  rewrite rngl_summation_split_first; [ symmetry | flia ].
  do 2 rewrite rngl_add_assoc.
  do 2 rewrite rngl_summation_succ_succ.
  f_equal; [ apply rngl_add_comm | ].
  apply rngl_summation_eq_compat.
  intros i Hi; cbn.
  destruct i; [ flia Hi | easy ].
} {
  specialize (Permutation_length Hl2) as H3.
  rewrite H2 in H3.
  rewrite IHHl1; [ | easy | easy ].
  now rewrite IHHl2.
}
Qed.

End a.

Arguments all_0_rngl_summation_0 {T}%type {ro rp} (b e)%nat (f g)%function.
Arguments all_0_rngl_summation_list_0 {T}%type {ro rp} A%type l%list.
Arguments rngl_summation_list_split_first {T}%type {ro rp} A%type l%list.
Arguments rngl_mul_summation_list_distr_l {T ro rp} Hom A%type a la%list.
Arguments rngl_mul_summation_distr_l {T ro rp} Hom a b e f.
Arguments rngl_mul_summation_distr_r {T ro rp} Hom a b e f.
Arguments rngl_opp_summation {T}%type {ro rp} Hop (b e)%nat.
Arguments rngl_summation_add_distr {T}%type {ro rp} _ _ (b k)%nat.
Arguments rngl_summation_change_var {T ro rp} A%type (b e)%nat.
Arguments rngl_summation_list_app {T}%type {ro rp} A%type (la lb)%list.
Arguments rngl_summation_list_cons {T ro rp} A%type_scope a la%list.
Arguments rngl_summation_list_only_one {T}%type {ro rp} A%type.
Arguments rngl_summation_list_permut {T}%type {ro rp} A%type (l1 l2)%list.
Arguments rngl_summation_list_split {T}%type {ro rp} A%type l%list _ n%nat.
Arguments rngl_summation_map_seq {T ro rp} A%type (start len)%nat.
Arguments rngl_summation_mul_summation {T}%type {ro rp} Hom (bi bj ei ej)%nat.
Arguments rngl_summation_only_one {T}%type {ro rp} g%function n%nat.
Arguments rngl_summation_permut {T}%type {ro rp} n%nat (l1 l2)%list.
Arguments rngl_summation_rtl {T}%type {ro rp} _ (b k)%nat.
Arguments rngl_summation_shift {T}%type {ro} (s b)%nat _%function k%nat_scope.
Arguments rngl_summation_split {T}%type {ro rp} j%nat g%function (b k)%nat.
Arguments rngl_summation_split_first {T}%type {ro rp} (b k)%nat.
Arguments rngl_summation_split3 {T}%type {ro rp} j%nat_scope _ (b k)%nat_scope.
Arguments rngl_summation_summation_distr {T}%type {ro rp} (a b)%nat.
Arguments rngl_summation_summation_exch' {T}%type {ro rp} _ (k l)%nat.
Arguments rngl_summation_ub_mul_distr {T}%type {ro rp} (a b)%nat.
