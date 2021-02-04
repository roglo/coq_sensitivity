Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith (*Bool*).
(*
Require Import Permutation.
Import List List.ListNotations.
*)

Require Import Misc RingLike Matrix.
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

Definition mat_permut_fun_rows n (σ : nat → nat) (M : matrix n n T) :=
  mk_mat n n (λ i j, mat_el M (σ i) j).

Definition mat_permut_rows n (σ : vector n nat) (M : matrix n n T) :=
  mat_permut_fun_rows (vect_el σ) M.

(*
   Canonical Permutations.

   The permutations are built this way. The k-th permutation is a
   vector of size n where
   - the first value is k/fact(n-1)
   - the rest is the (k mod fact(n-1))-th permutation of n-1 values
     (from 0 to n-2) where
     * all values less than the first value (k/fact(n-1)) are unchanged
     * all values greater or equal to it are increased by 1
   Example. For n=4 and k=0
   - first value: 0
   - rest: shift of 0;1;2 by 1, i.e. 1;2;3
   Result : 0;1;2;3
   Other example. For n=4 and k=13
   - first value: 13/3! = 13/6 = 2
   - rest: k' = 13 mod 3! = 13 mod 6 = 1 for n'=3, resulting 0;2;1
     0 and 1 are not shifted (both < 2), 2 is shifted, resulting 0;3;1
     final result: 2;0;3;1
  *)

Definition canon_permut_fun {n} (σ_n : nat → vector n nat) k j :=
  match j with
  | 0 => k / fact n
  | S j' =>
      vect_el (σ_n (k mod fact n)) j' +
      Nat.b2n (k / fact n <=? vect_el (σ_n (k mod fact n)) j')
  end.

Fixpoint canon_permut n k : vector n nat :=
  match n with
  | 0 => mk_vect 0 (λ _, 0)
  | S n' => mk_vect (S n') (canon_permut_fun (canon_permut n') k)
  end.

Fixpoint canon_permut_inv n k (j : nat) :=
  match n with
  | 0 => 0
  | S n' =>
      if lt_dec j (k / fact n') then
        S (canon_permut_inv n' (k mod fact n') j)
      else if lt_dec (k / fact n') j then
        S (canon_permut_inv n' (k mod fact n') (j - 1))
      else 0
  end.

Definition nat_of_canon_permut_sub_vect n (v : vector n nat) n' :=
  let d := vect_el v 0 in
  mk_vect n' (λ i, vect_el v (S i) - Nat.b2n (d <? vect_el v (S i))).

Fixpoint nat_of_canon_permut n (v : vector n nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      let d := vect_el v 0 in
      d * fact n' +
      nat_of_canon_permut (nat_of_canon_permut_sub_vect v n')
  end.

Theorem vect_el_nat_of_canon_permut_ub : ∀ n (v : vector (S n) nat) i,
  is_permut v
  → i < n
  → vect_el (nat_of_canon_permut_sub_vect v n) i < n.
Proof.
intros * (Hvn, Hn) Hin.
destruct n; [ easy | ].
cbn - [ "<?" ].
remember (vect_el v 0 <? vect_el v (S i)) as b eqn:Hb.
symmetry in Hb.
specialize (Hvn (S i)) as H1.
specialize (Hn 0 (S i) (Nat.lt_0_succ _)) as H2.
assert (H : S i < S (S n)) by flia Hin.
specialize (H1 H); specialize (H2 H); clear H.
destruct b; cbn; [ flia H1 | ].
rewrite Nat.sub_0_r.
apply Nat.ltb_ge in Hb.
destruct (Nat.eq_dec (vect_el v (S i)) (S n)) as [Hvi| Hvi]; [ | flia H1 Hvi ].
specialize (Hvn 0 (Nat.lt_0_succ _)) as H3.
flia Hb H1 H2 H3 Hvi.
Qed.

Theorem vect_el_nat_of_canon_permut_injective : ∀ n (v : vector (S n) nat) i j,
  is_permut v
  → i < n
  → j < n
  → vect_el (nat_of_canon_permut_sub_vect v n) i =
    vect_el (nat_of_canon_permut_sub_vect v n) j
  → i = j.
Proof.
intros * (Hvn, Hn) Hin Hjn Hij.
destruct (Nat.eq_dec i j) as [H| H]; [ easy | exfalso ].
revert Hij; rename H into Hij.
destruct n; [ easy | ].
cbn - [ "<?" ].
remember (vect_el v 0 <? vect_el v (S i)) as bi eqn:Hbi.
remember (vect_el v 0 <? vect_el v (S j)) as bj eqn:Hbj.
symmetry in Hbi, Hbj.
move bj before bi.
destruct bi; cbn. {
  apply Nat.ltb_lt in Hbi.
  destruct bj; cbn. {
    apply Nat.ltb_lt in Hbj.
    apply Nat.succ_lt_mono in Hin.
    apply Nat.succ_lt_mono in Hjn.
    specialize (Hn (S i) (S j) Hin Hjn) as Hs.
    assert (H : S i ≠ S j) by flia Hij.
    intros H'.
    apply H, Hs.
    flia Hbi Hbj H'.
  } {
    apply Nat.ltb_ge in Hbj.
    apply Nat.succ_lt_mono in Hjn.
    specialize (Hn 0 (S j) (Nat.lt_0_succ _) Hjn) as H1.
    flia Hbi Hbj H1.
  }
} {
  apply Nat.ltb_ge in Hbi.
  destruct bj; cbn. {
    apply Nat.ltb_lt in Hbj.
    apply Nat.succ_lt_mono in Hin.
    specialize (Hn 0 (S i) (Nat.lt_0_succ _) Hin) as H1.
    flia Hbi Hbj H1.
  } {
    apply Nat.ltb_ge in Hbj.
    apply Nat.succ_lt_mono in Hin.
    apply Nat.succ_lt_mono in Hjn.
    specialize (Hn (S i) (S j) Hin Hjn) as Hs.
    assert (H : S i ≠ S j) by flia Hij.
    intros H'.
    apply H, Hs.
    flia H'.
  }
}
Qed.

Theorem nat_of_canon_permut_upper_bound : ∀ n (v : vector n nat),
  is_permut v
  → nat_of_canon_permut v < fact n.
Proof.
intros * (Hvn, Hn).
revert v Hvn Hn.
induction n; intros; [ cbn; flia | ].
cbn.
rewrite Nat.add_comm.
apply Nat.add_lt_le_mono. {
  apply IHn. {
    intros i Hi.
    now apply vect_el_nat_of_canon_permut_ub.
  } {
    intros i j Hi Hj.
    now apply vect_el_nat_of_canon_permut_injective.
  }
}
apply Nat.mul_le_mono_r.
specialize (Hvn 0 (Nat.lt_0_succ _)).
flia Hvn.
Qed.

Theorem permut_nat_of_canon_permut : ∀ n v,
  is_permut v
  → canon_permut n (nat_of_canon_permut v) = v.
Proof.
intros * (Hvn, Hn).
revert v Hvn Hn.
induction n; intros; [ now apply vector_eq | ].
apply vector_eq.
intros j Hj; cbn.
destruct j. {
  cbn; clear Hj.
  rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
  rewrite <- Nat.add_0_r; f_equal.
  apply Nat.div_small.
  apply nat_of_canon_permut_upper_bound.
  split. {
    intros i Hi.
    now apply vect_el_nat_of_canon_permut_ub.
  } {
    intros i j Hi Hj.
    now apply vect_el_nat_of_canon_permut_injective.
  }
}
cbn.
remember (nat_of_canon_permut (nat_of_canon_permut_sub_vect v n)) as k eqn:Hk.
symmetry in Hk.
rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
rewrite Nat_mod_add_l_mul_r; [ | apply fact_neq_0 ].
assert (Hkn : k < fact n). {
  rewrite <- Hk.
  apply nat_of_canon_permut_upper_bound.
  split. {
    intros i Hi.
    now apply vect_el_nat_of_canon_permut_ub.
  } {
    intros i m Hi Hm.
    now apply vect_el_nat_of_canon_permut_injective.
  }
}
rewrite Nat.div_small; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
rewrite Nat.add_0_r.
remember (vect_el v 0 <=? vect_el (canon_permut n k) j) as b eqn:Hb.
symmetry in Hb.
assert (H1 : ∀ i, i < n → vect_el (nat_of_canon_permut_sub_vect v n) i < n). {
  intros i Hi.
  now apply vect_el_nat_of_canon_permut_ub.
}
assert
(H2 : ∀ i j : nat,
    i < n
    → j < n
    → vect_el (nat_of_canon_permut_sub_vect v n) i =
      vect_el (nat_of_canon_permut_sub_vect v n) j
    → i = j). {
  intros i m Hi Hm Him.
  now apply vect_el_nat_of_canon_permut_injective in Him.
}
destruct b. {
  apply Nat.leb_le in Hb; cbn.
  rewrite <- Hk in Hb |-*.
  rewrite IHn in Hb |-*; [ | easy | easy | easy | easy ].
  cbn - [ "<?" ] in Hb |-*.
  remember (vect_el v 0 <? vect_el v (S j)) as b1 eqn:Hb1.
  symmetry in Hb1.
  destruct b1. {
    apply Nat.ltb_lt in Hb1; cbn.
    apply Nat.sub_add; flia Hb1.
  } {
    apply Nat.ltb_ge in Hb1; exfalso.
    cbn in Hb.
    rewrite Nat.sub_0_r in Hb.
    apply Nat.le_antisymm in Hb; [ | easy ].
    symmetry in Hb.
    now specialize (Hn 0 (S j) (Nat.lt_0_succ _) Hj Hb).
  }
} {
  apply Nat.leb_gt in Hb; cbn.
  rewrite Nat.add_0_r.
  rewrite <- Hk in Hb |-*.
  remember (vect_el v 0 <? vect_el v (S j)) as b1 eqn:Hb1.
  symmetry in Hb1.
  destruct b1. {
    rewrite IHn in Hb; [ | easy | easy ].
    cbn - [ "<?" ] in Hb.
    rewrite Hb1 in Hb; cbn in Hb.
    apply Nat.ltb_lt in Hb1.
    flia Hb1 Hb.
  } {
    rewrite IHn; [ | easy | easy ].
    cbn - [ "<?" ].
    rewrite Hb1; cbn.
    apply Nat.sub_0_r.
  }
}
Qed.

Theorem nat_of_canon_permut_injective : ∀ n (σ₁ σ₂ : vector n nat),
  is_permut σ₁
  → is_permut σ₂
  → nat_of_canon_permut σ₁ = nat_of_canon_permut σ₂
  → σ₁ = σ₂.
Proof.
intros * Hσ₁ Hσ₂ Hσσ.
apply (f_equal (canon_permut n)) in Hσσ.
rewrite permut_nat_of_canon_permut in Hσσ; [ | easy ].
rewrite permut_nat_of_canon_permut in Hσσ; [ | easy ].
easy.
Qed.

End a.
