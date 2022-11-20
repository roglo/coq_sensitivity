(* summations on a ring-like (semiring, ring, field) *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc RingLike PermutationFun.

Notation "'∑' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c + g)%F) 0%F)
  (at level 45, i at level 0, b at level 60, e at level 60,
   right associativity,
   format "'[hv  ' ∑  ( i  =  b ,  e ) ,  '/' '[' g ']' ']'").

Notation "'∑' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c + g)%F) 0%F)
  (at level 45, i at level 0, l at level 60,
   right associativity,
   format "'[hv  ' ∑  ( i  ∈  l ) ,  '/' '[' g ']' ']'").

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.
Context {Hom : rngl_has_opp_or_sous = true}.

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

Theorem rngl_summation_list_add_distr :
  ∀ A g h (l : list A),
  (∑ (i ∈ l), (g i + h i) =
  (∑ (i ∈ l), g i) + ∑ (i ∈ l), h i)%F.
Proof.
intros Hic *.
apply iter_list_distr. {
  apply rngl_add_0_l.
} {
  apply rngl_add_comm.
} {
  apply rngl_add_assoc.
}
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
apply iter_seq_rtl. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_comm.
} {
  apply rngl_add_assoc.
}
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

Theorem mul_iter_list_distr_r : ∀ A B a (la : list B) f
    (add mul : A → A → A) d
    (mul_add_distr_r : ∀ y z, mul (add y z) a = add (mul y a) (mul z a)),
  mul (iter_list la (λ c i, add c (f i)) d) a =
  iter_list la (λ c i, add c (mul (f i) a)) (mul d a).
Proof.
intros.
clear Hom.
unfold iter_list.
revert d.
induction la as [| a1]; intros; [ easy | cbn ].
rewrite IHla.
f_equal.
apply mul_add_distr_r.
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

Theorem rngl_mul_summation_list_distr_r : ∀ A a (la : list A) f,
  ((∑ (i ∈ la), f i) * a = ∑ (i ∈ la), f i * a)%F.
Proof.
intros.
rewrite mul_iter_list_distr_r; [ | intros; apply rngl_mul_add_distr_r ].
now rewrite rngl_mul_0_l.
Qed.

Theorem rngl_mul_summation_distr_r : ∀ a b e f,
  ((∑ (i = b, e), f i) * a = ∑ (i = b, e), f i * a)%F.
Proof.
intros.
apply rngl_mul_summation_list_distr_r.
Qed.

Theorem rngl_summation_list_only_one : ∀ A g (a : A),
  (∑ (i ∈ [a]), g i = g a)%F.
Proof.
intros.
unfold iter_list; cbn.
apply rngl_add_0_l.
Qed.

Theorem rngl_summation_only_one : ∀ g n, ∑ (i = n, n), g i = g n.
Proof.
intros g n.
apply iter_seq_only_one, rngl_add_0_l.
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

Theorem rngl_summation_list_concat : ∀ A (ll : list (list A)) (f : A → T),
  ∑ (a ∈ concat ll), f a = ∑ (l ∈ ll), ∑ (a ∈ l), f a.
Proof.
intros.
induction ll as [| l]; cbn. {
  rewrite rngl_summation_list_empty; [ | easy ].
  now rewrite rngl_summation_list_empty.
}
rewrite rngl_summation_list_app.
rewrite rngl_summation_list_cons.
f_equal.
apply IHll.
Qed.

Theorem rngl_summation_summation_list_flat_map : ∀ A B la (f : A → list B) g,
  (∑ (a ∈ la), ∑ (b ∈ f a), g b) = ∑ (b ∈ flat_map f la), g b.
Proof.
intros.
induction la as [| a]; cbn. {
  now apply rngl_summation_list_empty.
}
rewrite rngl_summation_list_cons.
rewrite rngl_summation_list_app.
f_equal; apply IHla.
Qed.

Theorem rngl_summation_summation_list_swap : ∀ A B la lb (f : A → B → T),
  ∑ (a ∈ la), (∑ (b ∈ lb), f a b) =
  ∑ (b ∈ lb), (∑ (a ∈ la), f a b).
Proof.
intros.
induction la as [| a]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  erewrite rngl_summation_list_eq_compat. 2: {
    intros b Hb.
    now rewrite rngl_summation_list_empty.
  }
  now rewrite all_0_rngl_summation_list_0.
}
rewrite rngl_summation_list_cons.
symmetry.
erewrite rngl_summation_list_eq_compat. 2: {
  intros b Hb.
  now rewrite rngl_summation_list_cons.
}
cbn.
rewrite rngl_summation_list_add_distr.
now f_equal.
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

Theorem rngl_summation_list_permut : ∀ A (eqb : A → _),
  equality eqb →
  ∀ (la lb : list A) f,
  permutation eqb la lb
  → (∑ (i ∈ la), f i = ∑ (i ∈ lb), f i)%F.
Proof.
intros * Heqb * Hl.
apply (iter_list_permut Heqb); [ | | | | easy ]. {
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
now apply iter_list_seq.
Qed.

Theorem rngl_summation_list_mul_summation_list :
  ∀ A B li lj (f : A → T) (g : B → T),
  ((∑ (i ∈ li), f i) * (∑ (j ∈ lj), g j))%F =
  ∑ (i ∈ li), (∑ (j ∈ lj), f i * g j).
Proof.
intros.
induction li as [| ai]. {
  rewrite rngl_summation_list_empty; [ symmetry | easy ].
  rewrite rngl_summation_list_empty; [ symmetry | easy ].
  now apply rngl_mul_0_l.
}
do 2 rewrite rngl_summation_list_cons.
rewrite rngl_mul_add_distr_r.
rewrite IHli.
now rewrite rngl_mul_summation_list_distr_l.
Qed.

Theorem rngl_summation_mul_summation : ∀ bi bj ei ej f g,
  ((∑ (i = bi, ei), f i) * (∑ (j = bj, ej), g j))%F =
  ∑ (i = bi, ei), (∑ (j = bj, ej), f i * g j).
Proof.
intros.
apply rngl_summation_list_mul_summation_list.
Qed.

Theorem rngl_summation_list_map :
  ∀ A B (f : A → B) (g : B → _) l,
  ∑ (j ∈ map f l), g j = ∑ (i ∈ l), g (f i).
Proof.
intros.
unfold iter_list.
rewrite List_fold_left_map.
now apply rngl_summation_list_eq_compat.
Qed.

Theorem rngl_summation_list_change_var : ∀ A B (l : list A) f g (h : _ → B),
  (∀ i, i ∈ l → g (h i) = i)
  → ∑ (i ∈ l), f i = ∑ (i ∈ map h l), f (g i).
Proof.
intros * Hgh.
rewrite rngl_summation_list_map.
apply rngl_summation_list_eq_compat.
intros i Hi.
now rewrite Hgh.
Qed.

Theorem rngl_summation_change_var : ∀ A b e f g (h : _ → A),
  (∀ i, b ≤ i ≤ e → g (h i) = i)
  → ∑ (i = b, e), f i = ∑ (i ∈ map h (seq b (S e - b))), f (g i).
Proof.
intros * Hgh.
apply rngl_summation_list_change_var.
intros i Hi.
apply in_seq in Hi.
apply Hgh.
flia Hi.
Qed.

Theorem rngl_summation_le_compat :
  rngl_is_ordered = true →
  ∀ b e g h,
  (∀ i, b ≤ i ≤ e → (g i ≤ h i)%F)
  → (∑ (i = b, e), g i ≤ ∑ (i = b, e), h i)%F.
Proof.
intros Hor * Hgh.
unfold iter_seq.
remember (S e - b) as n eqn:Hn.
revert b Hn Hgh.
induction n as [| n IHn]; intros; [ now apply rngl_le_refl | ].
unfold iter_list; cbn.
do 2 rewrite rngl_add_0_l.
rewrite fold_left_rngl_add_fun_from_0.
remember (g b + _)%F as x.
rewrite fold_left_rngl_add_fun_from_0.
subst x.
apply rngl_add_le_compat; [ easy | apply Hgh; flia Hn | ].
apply IHn; [ flia Hn | ].
intros i Hbie.
apply Hgh; flia Hbie.
Qed.

Theorem rngl_summation_filter : ∀ A l f (g : A → T),
  ∑ (a ∈ filter f l), g a = ∑ (a ∈ l), if f a then g a else 0%F.
Proof.
intros.
induction l as [| b]; [ easy | cbn ].
rewrite rngl_summation_list_cons.
remember (f b) as fb eqn:Hfb; symmetry in Hfb.
destruct fb. {
  rewrite rngl_summation_list_cons; f_equal.
  apply IHl.
} {
  rewrite rngl_add_0_l.
  apply IHl.
}
Qed.

End a.

Arguments all_0_rngl_summation_0 {T}%type {ro rp} (b e)%nat (f g)%function.
Arguments all_0_rngl_summation_list_0 {T}%type {ro rp} A%type l%list.
Arguments rngl_summation_list_split_first {T}%type {ro rp} A%type l%list.
Arguments rngl_mul_summation_list_distr_l {T ro rp}.
Arguments rngl_mul_summation_list_distr_r {T ro rp}.
Arguments rngl_mul_summation_distr_l {T ro rp} a b e f.
Arguments rngl_mul_summation_distr_r {T ro rp} a b e f.
Arguments rngl_opp_summation {T}%type {ro rp} Hop (b e)%nat.
Arguments rngl_summation_add_distr {T}%type {ro rp} _ _ (b k)%nat.
Arguments rngl_summation_change_var {T ro} A%type (b e)%nat.
Arguments rngl_summation_eq_compat {T ro} _ _ (b k)%nat.
Arguments rngl_summation_filter {T ro rp} A%type l%list.
Arguments rngl_summation_list_app {T}%type {ro rp} A%type (la lb)%list.
Arguments rngl_summation_list_change_var {T ro} (A B)%type l%list.
Arguments rngl_summation_list_concat {T ro rp} A%type ll%list.
Arguments rngl_summation_list_cons {T ro rp} A%type a la%list.
Arguments rngl_summation_list_map {T ro} (_ _)%type.
Arguments rngl_summation_list_mul_summation_list {T ro rp}.
Arguments rngl_summation_list_only_one {T}%type {ro rp} A%type.
Arguments rngl_summation_list_permut {T ro rp} [A]%type _ _ (la lb)%list.
Arguments rngl_summation_list_split {T}%type {ro rp} A%type l%list _ n%nat.
Arguments rngl_summation_mul_summation {T}%type {ro rp} (bi bj ei ej)%nat.
Arguments rngl_summation_only_one {T}%type {ro rp} g%function n%nat.
Arguments rngl_summation_rtl {T}%type {ro rp} _ (b k)%nat.
Arguments rngl_summation_shift {T}%type {ro} (s b)%nat _%function k%nat.
Arguments rngl_summation_split {T}%type {ro rp} j%nat g%function (b k)%nat.
Arguments rngl_summation_split_first {T}%type {ro rp} (b k)%nat.
Arguments rngl_summation_split3 {T}%type {ro rp} j%nat _ (b k)%nat.
Arguments rngl_summation_summation_distr {T}%type {ro rp} (a b)%nat.
Arguments rngl_summation_summation_exch {T ro rp} g k%nat.
Arguments rngl_summation_summation_list_flat_map {T ro rp} (A B)%type la%list.
Arguments rngl_summation_summation_list_swap {T ro rp} (_ _)%type (_ _)%list.
