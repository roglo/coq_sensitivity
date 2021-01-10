(* products on a ring-like (semiring, ring, field) *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Require Import Misc RingLike.
Import List List.ListNotations.

Notation "'Π' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c * g)%F) 1%F)
  (at level 35, i at level 0, b at level 60, e at level 60) :
     ring_like_scope.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.
Existing Instance ro.

Theorem fold_left_rngl_mul_fun_from_1 : ∀ a l (f : nat → _),
  (fold_left (λ c i, c * f i) l a =
   a * fold_left (λ c i, c * f i) l 1)%F.
Proof.
intros.
apply iter_seq_op_fun_from_d. {
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

End a.
