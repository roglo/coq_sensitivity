(* Theorems of general usage, which could be (or not) in Coq library *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith (*Psatz Sorted Permutation Decidable*).
Require Import Main.Misc.
(*
Import List List.ListNotations.
Arguments length {A}.

Global Hint Resolve Nat.le_0_l : core.
Global Hint Resolve Nat.lt_0_succ : core.
Global Hint Resolve Nat.lt_succ_diag_r : core.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "n !" := (fact n) (at level 1, format "n !").
Notation "x '∈' l" := (List.In x l) (at level 70).
Notation "x '∉' l" := (¬ List.In x l) (at level 70).

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x < y < z" := (x < y ∧ y < z)%nat (at level 70, y at next level).

Notation "∃! x .. y , p" :=
  (ex (unique (λ x, .. (ex (unique (λ y, p))) ..)))
    (at level 200, x binder, right associativity)
  : type_scope.

Notation "x ≠? y" := (negb (Nat.eqb x y)) (at level 70) : nat_scope.
*)

Theorem Nat_div_interv : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a / b = n.
Proof.
intros * Hn.
revert a b Hn.
induction n; intros.
-rewrite Nat.mul_0_l, Nat.mul_1_l in Hn.
 now apply Nat.div_small.
-specialize (IHn (a - b) b) as H1.
 assert (H : n * b ≤ a - b < (n + 1) * b). {
   destruct Hn as (H2, H3).
   assert (Hba : b ≤ a). {
     eapply Nat.le_trans; [ | apply H2 ].
     apply Nat.le_add_r.
   }
   split.
   -apply (Nat.add_le_mono_r _ _ b).
    replace (n * b + b) with (S n * b) by apply Nat.add_comm.
    rewrite Nat.sub_add; [ apply H2 | easy ].
   -apply (Nat.add_lt_mono_r _ _ b).
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.add_1_r in H3; cbn in H3.
    rewrite Nat.add_1_r; cbn.
    now rewrite Nat.add_assoc, Nat.add_shuffle0 in H3.
 }
 specialize (H1 H); clear H.
 assert (H : b ≤ a). {
   apply (Nat.mul_le_mono_pos_l _ _ (S n)); [ easy | ].
   eapply le_trans; [ apply Hn | apply Nat.le_add_r ].
 }
 destruct b.
 +now do 2 rewrite Nat.mul_0_r in Hn.
 +replace a with (S b + (a - S b)); cycle 1. {
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite Nat_div_add_same_l; [ | easy ].
  rewrite Nat.add_1_l.
  now f_equal.
Qed.
