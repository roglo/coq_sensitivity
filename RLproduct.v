(* products on a ring-like (semiring, ring, field) *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Require Import Misc RingLike.
Import List List.ListNotations.

Notation "'Π' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c * g)%F) 1%F)
  (at level 35, i at level 0, b at level 60, e at level 60) :
     ring_like_scope.

Notation "'Π' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c * g)%F) 1%F)
  (at level 35, i at level 0, l at level 60) :
     ring_like_scope.

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
  → (Π (i = b, e), f i = 1)%F.
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

Theorem rngl_product_split_first : ∀ b k g,
  b ≤ k
  → (Π (i = b, k), g i)%F = (g b * Π (i = S b, k), g i)%F.
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
  → (Π (i = b, k), g i = (Π (i = S b, k), g (i - 1)%nat) * g k)%F.
Proof.
intros * Hbk.
now apply iter_seq_split_last.
Qed.

Theorem rngl_product_split : ∀ j g b k,
  b ≤ S j ≤ S k
  → (Π (i = b, k), g i = (Π (i = b, j), g i) * (Π (i = j+1, k), g i))%F.
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

Theorem rngl_product_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i = h i)%F)
  → (Π (i = b, k), g i = Π (i = b, k), h i)%F.
Proof.
intros * Hgh.
now apply iter_seq_eq_compat.
Qed.

Theorem rngl_product_list_eq_compat : ∀ A g h (l : list A),
  (∀ i, i ∈ l → (g i = h i)%F)
  → (Π (i ∈ l), g i = Π (i ∈ l), h i)%F.
Proof.
intros * Hgh.
now apply iter_list_eq_compat.
Qed.

Theorem rngl_product_list_cons : ∀ A (a : A) la f,
  (Π (i ∈ a :: la), f i = f a * Π (i ∈ la), f i)%F.
Proof.
intros.
unfold iter_list; cbn.
rewrite rngl_mul_1_l.
now apply fold_left_rngl_mul_fun_from_1.
Qed.

Theorem rngl_product_succ_succ : ∀ b k g,
  (Π (i = S b, S k), g i = Π (i = b, k), g (S i))%F.
Proof.
intros b k g.
apply iter_seq_succ_succ.
Qed.

Theorem rngl_product_empty : ∀ g b k,
  k < b → (Π (i = b, k), g i = 1)%F.
Proof.
intros * Hkb.
now apply iter_seq_empty.
Qed.

Theorem rngl_product_mul_distr :
  rngl_is_comm = true →
  ∀ g h b k,
  (Π (i = b, k), (g i * h i) =
   (Π (i = b, k), g i) * Π (i = b, k), h i)%F.
Proof.
intros Hic g h b k.
apply iter_seq_distr. {
  apply rngl_mul_1_l.
} {
  specialize rngl_opt_mul_comm as rngl_mul_comm.
  rewrite Hic in rngl_mul_comm.
  apply rngl_mul_comm.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_shift : ∀ b g k,
  b ≤ k
  → (Π (i = b, k), g i =
     Π (i = 0, k - b), g (b + i)%nat)%F.
Proof.
intros b g k Hbk.
now apply iter_shift.
Qed.

Theorem rngl_product_list_opt_integral :
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  ∀ A (l : list A) f,
  (Π (i ∈ l), f i)%F = 0%F
  → ∃ i, i ∈ l ∧ f i = 0%F.
Proof.
intros Hin H10 * Hz.
specialize rngl_opt_1_neq_0 as rngl_1_neq_0.
specialize rngl_opt_integral as rngl_integral.
rewrite H10 in rngl_1_neq_0.
rewrite Hin in rngl_integral.
induction l as [| a]; [ easy | ].
cbn in Hz.
rewrite rngl_mul_1_l in Hz.
rewrite (fold_left_op_fun_from_d 1%F) in Hz; cycle 1. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
rewrite fold_iter_list in Hz.
apply rngl_integral in Hz.
destruct Hz as [Hz| Hz]. {
  exists a.
  split; [ now left | easy ].
}
destruct (IHl Hz) as (i & Hil & Hfi).
exists i.
split; [ now right | easy ].
Qed.

Theorem rngl_product_opt_integral :
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  ∀ b e f,
  (Π (i = b, e), f i = 0)%F
  → ∃ i, b ≤ i ≤ e ∧ f i = 0%F.
Proof.
intros Hin H10 * Hz.
apply rngl_product_list_opt_integral in Hz; [ | easy | easy ].
destruct Hz as (i & His & Hfi).
apply in_seq in His.
exists i.
split; [ flia His | easy ].
Qed.

(*  a version without commutativity, but inverted product would be better *)
Theorem rngl_inv_product :
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i ≠ 0%F)
  → ((¹/ Π (i = b, e), f i) = Π (i = b, e), (¹/ f i))%F.
Proof.
intros Hic Hin H10 Hit * Hnz.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
specialize rngl_opt_integral as rngl_integral.
rewrite Hit in rngl_integral.
unfold iter_seq, iter_list.
remember (S e - b) as len.
destruct len; [ now apply rngl_inv_1 | ].
replace e with (b + len) in Hnz by flia Heqlen.
clear e Heqlen.
revert b Hnz.
induction len; intros. {
  cbn.
  now do 2 rewrite rngl_mul_1_l.
}
rewrite List_seq_succ_r.
do 2 rewrite fold_left_app.
rewrite <- IHlen. 2: {
  intros i Hi.
  apply Hnz; flia Hi.
}
rewrite fold_left_op_fun_from_d with (d := 1%F); cycle 1. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
symmetry.
rewrite fold_left_op_fun_from_d with (d := 1%F); cycle 1. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
symmetry; cbn.
do 3 rewrite rngl_mul_1_l.
rewrite rngl_mul_comm.
apply rngl_inv_mul_distr; [ easy | easy | apply Hnz; flia | ].
clear IHlen.
revert b Hnz.
induction len; intros; [ apply Hnz; flia | ].
rewrite List_seq_succ_r.
rewrite fold_left_app.
cbn - [ seq ].
intros Hzz.
apply rngl_integral in Hzz.
destruct Hzz as [Hzz| Hzz]. {
  revert Hzz.
  apply IHlen.
  intros i Hi.
  apply Hnz; flia Hi.
} {
  revert Hzz.
  apply Hnz; flia.
}
Qed.

End a.

Arguments rngl_inv_product {T}%type {ro rp} _ _ _ _ (b e)%nat f.
