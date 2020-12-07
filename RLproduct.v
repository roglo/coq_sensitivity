(* products on a ring-like (semiring, ring, field) *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Require Import Misc RingLike.
Import List List.ListNotations.

Notation "'Π' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c * g)%F) 1%F)
  (at level 45, i at level 0, b at level 60, e at level 60) :
     ring_like_scope.

Section in_ring.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.
Existing Instance ro.

Theorem fold_left_rngl_mul_fun_from_1 : ∀ a l (f : nat → _),
  (fold_left (λ c i, c * f i) l a =
   a * fold_left (λ c i, c * f i) l 1)%F.
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply rngl_mul_1_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite rngl_mul_1_l.
apply rngl_mul_assoc.
Qed.

Theorem rngl_product_split_first : ∀ b k g,
  b ≤ k
  → (Π (i = b, k), g i)%F = (g b * Π (i = S b, k), g i)%F.
Proof.
intros * Hbk.
unfold iter_seq.
remember (S k - b) as len eqn:Hlen.
replace (S k - S b) with (len - 1) by flia Hlen.
assert (H : len ≠ 0) by flia Hlen Hbk.
clear k Hbk Hlen.
rename H into Hlen.
destruct len; [ easy | cbn ].
rewrite rngl_mul_1_l, Nat.sub_0_r.
apply fold_left_rngl_mul_fun_from_1.
Qed.

Theorem rngl_product_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i = h i)%F)
  → (Π (i = b, k), g i = Π (i = b, k), h i)%F.
Proof.
intros * Hgh.
unfold iter_seq.
remember (S k - b) as len eqn:Hlen.
assert (∀ i, b ≤ i < b + len → g i = h i). {
  intros i Hi.
  apply Hgh; flia Hlen Hi.
}
clear k Hgh Hlen.
rename H into Hb.
revert b Hb.
induction len; intros; [ easy | cbn ].
do 2 rewrite rngl_mul_1_l.
rewrite fold_left_rngl_mul_fun_from_1; symmetry.
rewrite fold_left_rngl_mul_fun_from_1; symmetry.
f_equal; [ apply Hb; flia | ].
apply IHlen.
intros i Hi.
apply Hb.
flia Hi.
Qed.

Theorem rngl_product_succ_succ : ∀ b k g,
  (Π (i = S b, S k), g i = Π (i = b, k), g (S i))%F.
Proof.
intros b k g.
apply iter_succ_succ.
Qed.

End in_ring.
