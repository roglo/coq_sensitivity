Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith (*Bool*).
(*
Require Import Permutation.
Import List List.ListNotations.
*)

Require Import (*Misc*) RingLike Matrix.
(*
Require Import RLsummation RLproduct.
Require Import Pigeonhole.
Import matrix_Notations.
Import Init.Nat.
*)

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

Definition is_permut_fun f n :=
  (∀ i, i < n → f i < n) ∧
  (∀ i j, i < n → j < n → f i = f j → i = j).

Definition is_permut {n} (σ : vector n nat) := is_permut_fun (vect_el σ) n.

Definition transposition i j k :=
  if Nat.eq_dec k i then j
  else if Nat.eq_dec k j then i
  else k.

Definition vect_swap_elem n (v : vector n nat) i j :=
  mk_vect n (λ k, vect_el v (transposition i j k)).

Theorem vect_el_permut_ub : ∀ n (σ : vector n nat) i,
  is_permut σ → i < n → vect_el σ i < n.
Proof.
intros * Hp Hin.
destruct Hp as (Hp1, Hp2).
now apply Hp1.
Qed.

Theorem transposition_lt : ∀ i j k n,
  i < n
  → j < n
  → k < n
  → transposition i j k < n.
Proof.
intros * Hi Hj Hk.
unfold transposition.
destruct (Nat.eq_dec k i); [ easy | ].
now destruct (Nat.eq_dec k j).
Qed.

Theorem vect_swap_elem_is_permut : ∀ n (σ : vector n nat) p q,
  p < n
  → q < n
  → is_permut σ
  → is_permut (vect_swap_elem σ p q).
Proof.
intros * Hp Hq Hσ.
split; cbn. {
  intros i Hi.
  apply vect_el_permut_ub; [ easy | ].
  now apply transposition_lt.
} {
  intros * Hi Hj Hij.
  unfold transposition in Hij.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
      subst i j.
      now apply Hσ.
    }
    apply Nat.neq_sym in Hjq.
    now apply Hσ in Hij.
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
      subst i j.
      now apply Hσ.
    }
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ congruence | ].
    apply Nat.neq_sym in Hjp.
    now apply Hσ in Hij.
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
    now apply Hσ in Hij.
  }
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
    now apply Hσ in Hij.
  }
  now apply Hσ in Hij.
}
Qed.

End a.
