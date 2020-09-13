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

(*
Theorem fold_left_rng_add_fun_from_0 {A} {ro : ring_op A} (so := rng_semiring) {sp : semiring_prop A} :
  ∀ a l (f : nat → _),
  (fold_left (λ c i, c + f i) l a =
   a + fold_left (λ c i, c + f i) l 0)%Rng.
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply srng_add_0_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite srng_add_0_l.
apply srng_add_assoc.
Qed.

Theorem all_0_ring_summation_0 : ∀ T (ro : ring_op T) (so := rng_semiring) {sp : semiring_prop T} b e f,
  (∀ i, b ≤ i ≤ e → f i = 0%Rng)
  → (Σ (i = b, e), f i = 0)%Rng.
Proof.
intros * sp * Hz.
remember (S e - b) as n eqn:Hn.
revert b Hz Hn.
induction n; intros; [ easy | cbn ].
rewrite fold_left_rng_add_fun_from_0.
rewrite IHn; [ | | flia Hn ]. {
  rewrite Hz; [ | flia Hn ].
  rewrite srng_add_0_l.
  now rewrite srng_add_0_l.
}
intros i Hi.
apply Hz; flia Hi.
Qed.
*)

Theorem fold_left_srng_add_fun_from_0 {A} {so : semiring_op A} {sp : semiring_prop A} :
  ∀ a l (f : nat → _),
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

Theorem all_0_srng_summation_0 : ∀ T {so : semiring_op T} {sp : semiring_prop T} b e f,
  (∀ i, b ≤ i ≤ e → f i = 0%Srng)
  → (Σ (i = b, e), f i = 0)%Srng.
Proof.
intros * sp * Hz.
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

Theorem rng_opp_summation :
  ∀ T (ro : ring_op T) (so := rng_semiring),
  ∀ {rp : ring_prop T} {sp : semiring_prop T},
  ∀ b e f,
  ((- Σ (i = b, e), f i) = Σ (i = b, e), (- f i))%Rng.
Proof.
intros.
remember (S e - b) as len.
clear e Heqlen.
revert b.
induction len; intros; cbn; [ apply rng_opp_0 | ].
...
