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

Theorem rngl_product_opt_integral :
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  ∀ b e f,
  (Π (i = b, e), f i = 0)%F
  → ∃ i, b ≤ i ≤ e ∧ f i = 0%F.
Proof.
intros Hin H10 * Hz.
unfold iter_seq in Hz.
remember (S e - b) as len eqn:Hlen in Hz.
destruct len. {
  cbn in Hz.
  specialize rngl_opt_1_neq_0 as rngl_1_neq_0.
  now rewrite H10 in rngl_1_neq_0.
}
replace e with (b + len) by flia Hlen.
clear e Hlen.
revert b Hz.
induction len; intros. {
  cbn in Hz.
  rewrite rngl_mul_1_l in Hz.
  exists b.
  now rewrite Nat.add_0_r.
}
rewrite List_seq_succ_r in Hz.
rewrite fold_left_app in Hz.
remember (S len) as s; cbn in Hz; subst s.
specialize rngl_opt_integral as rngl_integral.
rewrite Hin in rngl_integral.
apply rngl_integral in Hz.
destruct Hz as [Hz| Hz]. {
  apply IHlen in Hz.
  destruct Hz as (i, Hi).
  exists i.
  split; [ flia Hi | easy ].
} {
  exists (b + S len).
  split; [ flia | easy ].
}
Qed.

(* à voir...
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
unfold iter_seq.
remember (S e - b) as len.
destruct len; [ now apply rngl_inv_1 | ].
replace e with (b + len) in Hnz by flia Heqlen.
clear e Heqlen.
revert b Hnz.
induction len; intros. {
  cbn.
  now do 2 rewrite rngl_mul_1_l.
}
rewrite List_seq_succ_r; cbn.
do 2 rewrite rngl_mul_1_l.
rewrite fold_left_app; cbn.
rewrite fold_left_app; cbn.
rewrite iter_seq_op_fun_from_d with (d := 1%F).
...
rewrite <- IHlen.
rewrite rngl_inv_mul_distr; [ | easy | easy | | ]. {
  specialize rngl_opt_mul_comm as rngl_mul_comm.
  rewrite Hic in rngl_mul_comm.
  apply rngl_mul_comm.
}
...intros Hic Hin H10 Hit * Hnz.
unfold iter_seq.
remember (S e - b) as len.
clear e Heqlen.
revert b.
induction len; intros; [ now apply rngl_inv_1 | ].
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite fold_left_app; cbn.
rewrite <- IHlen.
rewrite rngl_inv_mul_distr; [ | easy | easy | | ]. {
  specialize rngl_opt_mul_comm as rngl_mul_comm.
  rewrite Hic in rngl_mul_comm.
  apply rngl_mul_comm.
}
...
rewrite rngl_inv_mul_distr; [ | easy | easy | | ]; cycle 1. {
now rewrite inv_op_distr.
...
intros Hin H10 Hit * Hnz.
apply iter_seq_inv. {
  now apply rngl_inv_1.
} {
Check iter_seq_inv.
  intros a c.
  rewrite rngl_inv_mul_distr; [ | easy | easy | | ]; cycle 1. {
...
*)

End a.
