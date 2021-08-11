(* products on a ring-like (semiring, ring, field) *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith Permutation.
Require Import Misc RingLike.
Import List List.ListNotations.

Notation "'∏' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c * g)%F) 1%F)
  (at level 35, i at level 0, b at level 60, e at level 60).

Notation "'∏' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c * g)%F) 1%F)
  (at level 35, i at level 0, l at level 60).

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.
Existing Instance ro.

Theorem fold_left_rngl_mul_fun_from_1 : ∀ A a l (f : A → _),
  (fold_left (λ c i, c * f i) l a =
   a * fold_left (λ c i, c * f i) l 1)%F.
Proof.
intros.
apply fold_left_op_fun_from_d. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem all_1_rngl_product_1 : ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i = 1%F)
  → ∏ (i = b, e), f i = 1%F.
Proof.
intros * Hz.
apply iter_seq_all_d; [ | | | easy ]. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem all_1_rngl_product_list_1 : ∀ A (l : list A) f,
  (∀ i, i ∈ l → f i = 1%F)
  → ∏ (i ∈ l), f i = 1%F.
Proof.
intros * Hz.
apply iter_list_all_d; [ | | | easy ]. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_split_first : ∀ b k g,
  b ≤ k
  → ∏ (i = b, k), g i = (g b * ∏ (i = S b, k), g i)%F.
Proof.
intros * Hbk.
apply iter_seq_split_first; [ | | | easy ]. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_split_last : ∀ b k g,
  b ≤ k
  → ∏ (i = b, k), g i = (∏ (i = S b, k), g (i - 1)%nat * g k)%F.
Proof.
intros * Hbk.
now apply iter_seq_split_last.
Qed.

Theorem rngl_product_split : ∀ j g b k,
  b ≤ S j ≤ S k
  → ∏ (i = b, k), g i = ((∏ (i = b, j), g i) * (∏ (i = j+1, k), g i))%F.
Proof.
intros * Hbjk.
apply iter_seq_split; [ | | | easy ]. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_split3 : ∀ j g b k,
  b ≤ j ≤ k
  → ∏ (i = b, k), g i =
       (∏ (i = S b, j), g (i - 1)%nat * g j * ∏ (i = j + 1, k), g i)%F.
Proof.
intros * Hj.
rewrite rngl_product_split with (j := j); [ | flia Hj ].
now rewrite rngl_product_split_last.
Qed.

Theorem rngl_product_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i = h i)%F)
  → (∏ (i = b, k), g i = ∏ (i = b, k), h i)%F.
Proof.
intros * Hgh.
now apply iter_seq_eq_compat.
Qed.

Theorem rngl_product_list_eq_compat : ∀ A g h (l : list A),
  (∀ i, i ∈ l → (g i = h i)%F)
  → (∏ (i ∈ l), g i = ∏ (i ∈ l), h i)%F.
Proof.
intros * Hgh.
now apply iter_list_eq_compat.
Qed.

Theorem rngl_product_list_cons : ∀ A (a : A) la f,
  (∏ (i ∈ a :: la), f i = f a * ∏ (i ∈ la), f i)%F.
Proof.
intros.
unfold iter_list; cbn.
rewrite rngl_mul_1_l.
now apply fold_left_rngl_mul_fun_from_1.
Qed.

Theorem rngl_product_succ_succ : ∀ b k g,
  (∏ (i = S b, S k), g i = ∏ (i = b, k), g (S i))%F.
Proof.
intros b k g.
apply iter_seq_succ_succ.
Qed.

Theorem rngl_product_succ_succ' : ∀ b k g,
  (∏ (i = S b, S k), g (i - 1)%nat = ∏ (i = b, k), g i)%F.
Proof.
intros.
symmetry.
now rewrite <- iter_seq_succ_succ'.
Qed.

Theorem rngl_product_empty : ∀ g b k,
  k < b → (∏ (i = b, k), g i = 1)%F.
Proof.
intros * Hkb.
now apply iter_seq_empty.
Qed.

Theorem rngl_product_list_mul_distr :
  rngl_is_comm = true →
  ∀ A g h (l : list A),
  (∏ (i ∈ l), (g i * h i) =
  (∏ (i ∈ l), g i) * ∏ (i ∈ l), h i)%F.
Proof.
intros Hic *.
apply iter_list_distr. {
  apply rngl_mul_1_l.
} {
  now apply rngl_mul_comm.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_mul_distr :
  rngl_is_comm = true →
  ∀ g h b k,
  (∏ (i = b, k), (g i * h i) =
  (∏ (i = b, k), g i) * ∏ (i = b, k), h i)%F.
Proof.
intros Hic g h b k.
now apply rngl_product_list_mul_distr.
Qed.

Theorem rngl_product_shift : ∀ b g k,
  b ≤ k
  → (∏ (i = b, k), g i =
     ∏ (i = 0, k - b), g (b + i)%nat)%F.
Proof.
intros b g k Hbk.
now apply iter_shift.
Qed.

Theorem rngl_product_list_integral :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  ∀ A (l : list A) f,
  (∏ (i ∈ l), f i)%F = 0%F
  → ∃ i, i ∈ l ∧ f i = 0%F.
Proof.
intros Hom Hin H10 * Hz.
induction l as [| a]; [ now apply rngl_1_neq_0 in Hz | ].
unfold iter_list in Hz; cbn in Hz.
rewrite rngl_mul_1_l in Hz.
rewrite (fold_left_op_fun_from_d 1%F) in Hz; cycle 1. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
rewrite fold_iter_list in Hz.
apply rngl_integral in Hz; [ | easy | now rewrite Hin ].
destruct Hz as [Hz| Hz]. {
  exists a.
  split; [ now left | easy ].
}
destruct (IHl Hz) as (i & Hil & Hfi).
exists i.
split; [ now right | easy ].
Qed.

Theorem rngl_product_integral :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  ∀ b e f,
  (∏ (i = b, e), f i = 0)%F
  → ∃ i, b ≤ i ≤ e ∧ f i = 0%F.
Proof.
intros Hom Hin H10 * Hz.
apply rngl_product_list_integral in Hz; [ | easy | easy | easy ].
destruct Hz as (i & His & Hfi).
apply in_seq in His.
exists i.
split; [ flia His | easy ].
Qed.

Theorem rngl_product_list_permut :
  rngl_is_comm = true →
  ∀ A (l1 l2 : list A) f,
  Permutation l1 l2
  → (∏ (i ∈ l1), f i = ∏ (i ∈ l2), f i)%F.
Proof.
intros Hic * Hl.
apply iter_list_permut; [ | | | | easy ]. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  now apply rngl_mul_comm.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_inv_product_list :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  ∀ A (l : list A) f,
  (∀ i, i ∈ l → f i ≠ 0%F)
  → ((∏ (i ∈ l), f i)⁻¹ = ∏ (i ∈ rev l), ((f i)⁻¹))%F.
Proof.
intros Hom Hin H10 Hit * Hnz.
unfold iter_list.
induction l as [| a]; [ now apply rngl_inv_1 | cbn ].
rewrite rngl_mul_1_l.
rewrite (fold_left_op_fun_from_d 1%F); cycle 1. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
rewrite rngl_inv_mul_distr; [ | easy | easy | easy | | ]; cycle 1. {
  now apply Hnz; left.
} {
  intros H1.
  rewrite fold_iter_list in H1.
  specialize (rngl_product_list_integral Hom Hit H10) as H2.
  specialize (H2 A l f H1).
  destruct H2 as (i & Hil & Hfi).
  now revert Hfi; apply Hnz; right.
}
rewrite IHl. 2: {
  intros i Hi.
  now apply Hnz; right.
}
symmetry.
apply fold_left_app.
Qed.

Theorem rngl_inv_product :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i ≠ 0%F)
  → ((∏ (i = b, e), f i)⁻¹ = ∏ (i = b, e), ((f (b + e - i)%nat)⁻¹))%F.
Proof.
intros Hom Hin H10 Hit * Hnz.
unfold iter_seq.
rewrite rngl_inv_product_list; [ | easy | easy | easy | easy | ]. 2: {
  intros i Hi.
  apply in_seq in Hi.
  apply Hnz; flia Hi.
}
unfold iter_list.
remember (S e - b) as len eqn:Hlen.
destruct len; [ easy | ].
replace e with (b + len) in Hnz |-* by flia Hlen.
clear e Hlen.
revert b Hnz.
induction len; intros. {
  cbn.
  do 2 rewrite rngl_mul_1_l.
  now rewrite Nat.add_0_r, Nat.add_sub.
}
symmetry.
rewrite seq_S at 1.
symmetry.
remember (S len) as sl; cbn; subst sl.
rewrite fold_left_app.
rewrite fold_left_app.
rewrite IHlen. 2: {
  intros i Hi.
  apply Hnz; flia Hi.
}
cbn - [ "-" ].
do 2 rewrite rngl_mul_1_l.
replace (b + (b + S len) - (b + S len)) with b by flia.
f_equal.
replace (S (b + S (b + len)) - S b) with (S (b + len)) by flia.
replace (b + (b + S len) - b) with (S (b + len)) by flia.
rewrite <- seq_shift.
rewrite List_fold_left_map; cbn.
apply List_fold_left_ext_in.
intros c d Hc.
f_equal; f_equal; f_equal.
flia.
Qed.

Theorem rngl_inv_product_list_comm :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  ∀ A (l : list A) f,
  (∀ i, i ∈ l → f i ≠ 0%F)
  → ((∏ (i ∈ l), f i)⁻¹ = ∏ (i ∈ l), (( f i)⁻¹))%F.
Proof.
intros Hom Hic Hin H10 Hit * Hnz.
rewrite rngl_inv_product_list; [ | easy | easy | easy | easy | easy ].
apply rngl_product_list_permut; [ easy | ].
symmetry.
apply Permutation_rev.
Qed.

Theorem rngl_inv_product_comm :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i ≠ 0%F)
  → ((∏ (i = b, e), f i)⁻¹ = ∏ (i = b, e), ((f i)⁻¹))%F.
Proof.
intros Hom Hic Hin H10 Hit * Hnz.
apply rngl_inv_product_list_comm; try easy.
intros i Hi.
apply in_seq in Hi.
apply Hnz; flia Hi.
Qed.

Theorem rngl_product_div_distr :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  ∀ b e f g,
  (∀ i, b ≤ i ≤ e → g i ≠ 0%F)
  → (∏ (i = b, e), (f i / g i))%F =
    ((∏ (i = b, e), f i) / (∏ (i = b, e), g i))%F.
Proof.
intros Hom Hic Hin H10 Hit * Hg.
unfold rngl_div.
rewrite Hin.
rewrite rngl_product_mul_distr; [ | easy ].
f_equal; symmetry.
now apply rngl_inv_product_comm.
Qed.

Theorem rngl_product_seq_product : ∀ b len f,
  len ≠ 0
  → (∏ (i ∈ seq b len), f i = ∏ (i = b, b + len - 1), f i)%F.
Proof.
intros * Hlen.
unfold iter_seq.
f_equal; f_equal.
flia Hlen.
Qed.

Theorem rngl_product_1_opp_1 :
  rngl_has_opp = true →
  ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i = 1%F ∨ f i = (-1)%F)
  → (∏ (i = b, e), f i = 1)%F ∨ (∏ (i = b, e), f i = -1)%F.
Proof.
intros Hop * Hf.
unfold iter_seq.
remember (S e - b) as len eqn:Hlen.
destruct len; [ now left | ].
assert (H : ∀ i, b ≤ i ≤ b + len → f i = 1%F ∨ f i = (-1)%F). {
  intros i Hi.
  apply Hf.
  flia Hlen Hi.
}
move H before Hf; clear Hf; rename H into Hf.
replace e with (b + len) by flia Hlen.
clear e Hlen.
revert b Hf.
induction len; intros. {
  cbn.
  unfold iter_list; cbn.
  rewrite rngl_mul_1_l.
  apply Hf; flia.
}
remember (S len) as x; cbn; subst x.
rewrite rngl_product_list_cons.
specialize (Hf b) as H1.
assert (H : b ≤ b ≤ b + S len) by flia.
specialize (H1 H); clear H.
specialize (IHlen (S b)) as H2.
assert (H : ∀ i, S b ≤ i ≤ S b + len → f i = 1%F ∨ f i = (-1)%F). {
  intros i Hi.
  apply Hf.
  flia Hi.
}
specialize (H2 H); clear H.
destruct H1 as [H1| H1]; rewrite H1. {
  now rewrite rngl_mul_1_l.
} {
  destruct H2 as [H2| H2]; rewrite H2; [ right | left ]. {
    rewrite rngl_mul_opp_l; [ | easy ].
    now rewrite rngl_mul_1_l.
  } {
    rewrite rngl_mul_opp_opp; [ | easy ].
    apply rngl_mul_1_l.
  }
}
Qed.

Theorem rngl_product_only_one : ∀ g n, (∏ (i = n, n), g i = g n)%F.
Proof.
intros g n.
unfold iter_seq.
rewrite Nat.sub_succ_l; [ idtac | reflexivity ].
rewrite Nat.sub_diag; simpl.
apply rngl_mul_1_l.
Qed.

Theorem rngl_product_permut :
  rngl_is_comm = true →
  ∀ n l1 l2,
  Permutation l1 l2
  → length l1 = n
  → length l2 = n
  → ∏ (i = 0, n - 1), nth i l1 0 = ∏ (i = 0, n - 1), nth i l2 0.
Proof.
intros Hic * Hl H1 H2.
destruct n. {
  apply length_zero_iff_nil in H1.
  apply length_zero_iff_nil in H2.
  now subst l1 l2.
}
rewrite Nat.sub_succ, Nat.sub_0_r.
revert n H1 H2.
induction Hl; intros; [ easy | | | ]. {
  cbn in H1, H2.
  apply Nat.succ_inj in H1.
  apply Nat.succ_inj in H2.
  rewrite rngl_product_split_first; [ symmetry | flia ].
  rewrite rngl_product_split_first; [ symmetry | flia ].
  destruct n; [ easy | ].
  do 2 rewrite rngl_product_succ_succ.
  now rewrite IHHl.
} {
  destruct n; [ easy | ].
  cbn in H1, H2.
  do 2 apply Nat.succ_inj in H1.
  do 2 apply Nat.succ_inj in H2.
  rewrite rngl_product_split_first; [ symmetry | flia ].
  rewrite rngl_product_split_first; [ symmetry | flia ].
  rewrite rngl_product_split_first; [ symmetry | flia ].
  rewrite rngl_product_split_first; [ symmetry | flia ].
  do 2 rewrite rngl_mul_assoc.
  do 2 rewrite rngl_product_succ_succ.
  f_equal; [ now apply rngl_mul_comm | ].
  apply rngl_product_eq_compat.
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

Arguments all_1_rngl_product_1 {T}%type {ro rp} (b e)%nat.
Arguments rngl_product_div_distr {T}%type {ro rp} _ _ _ _ _ (b e)%nat.
Arguments rngl_inv_product {T}%type {ro rp} _ _ _ _ (b e)%nat f.
Arguments rngl_inv_product_comm {T}%type {ro rp} _ _ _ _ _ (b e)%nat f.
Arguments rngl_inv_product_list {T}%type {ro rp} _ _ _ _ {A}%type l%list.
Arguments rngl_product_list_mul_distr {T}%type {ro rp} _ A%type.
Arguments rngl_product_list_permut {T}%type {ro rp} _ A%type (l1 l2)%list.
Arguments rngl_product_mul_distr {T}%type {ro rp} _ (g h)%function (b k)%nat.
Arguments rngl_product_split {T}%type {ro rp} j%nat g%function (b k)%nat.
Arguments rngl_product_succ_succ {T}%type {ro} (b k)%nat g%function.
Arguments rngl_product_integral {T}%type {ro rp} _ _ _ (b e)%nat f%function.
Arguments rngl_product_list_integral {T}%type {ro rp} _ _ _ A%type l%list.
Arguments rngl_product_split_first {T}%type {ro rp} (b k)%nat g%function.
Arguments rngl_product_split3 {T}%type {ro rp} j%nat _ (b k)%nat.
Arguments rngl_product_1_opp_1 {T}%type {ro rp} _ (b e)%nat (f g)%function.
Arguments rngl_product_permut {T}%type {ro rp} Hic n%nat (l1 l2)%list.
Arguments rngl_product_only_one {T}%type {ro rp} g%function n%nat.
