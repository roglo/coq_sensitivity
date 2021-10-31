(* permutations of sequences of natural numbers between 1 and n *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Require Import Permutation.
Import List List.ListNotations.

Require Import Misc RingLike MyVector.
Require Import RLproduct.
Require Import Pigeonhole.

Definition comp {A B C} (f : B → C) (g : A → B) x := f (g x).

Definition comp_list (la lb : list nat) :=
  map (λ i, nth i la 0) lb.

Definition permut_comp (σ₁ σ₂ : vector nat) :=
  mk_vect (comp_list (vect_list σ₁) (vect_list σ₂)).

(*
Compute (comp_list [0;2;1] [2;1;0]).
Compute (map (comp (λ i, nth i [0;2;1] 0) (λ i, nth i [2;1;0] 0)) [0;1;2]).
*)

Notation "σ₁ ° σ₂" := (permut_comp σ₁ σ₂) (at level 40).

Notation "'Comp' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, comp c g) (λ i, i))
  (at level 35, i at level 0, l at level 60).

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

Definition is_permut_fun f n :=
  (∀ i, i < n → f i < n) ∧
  (∀ i j, i < n → j < n → f i = f j → i = j).

Definition vect_vect_nat_el (V : vector (vector nat)) i : vector nat :=
  nth i (vect_list V) empty_vect.

Definition is_permut_vect (σ : vector nat) :=
  is_permut_fun (vect_el 0 σ) (vect_size σ).

Definition is_permut_fun_bool f n :=
  (⋀ (i = 1, n), (f (i - 1) <? n)) &&
  (⋀ (i = 1, n), (⋀ (j = 1, n), ((f (i - 1) ≠? f (j - 1)) || (i =? j)))).

Definition is_permut_vect_bool (σ : vector nat) :=
  is_permut_fun_bool (vect_el 0 σ) (vect_size σ).

Theorem is_permut_fun_is_permut_fun_bool : ∀ f n,
  is_permut_fun f n ↔ is_permut_fun_bool f n = true.
Proof.
intros.
split. {
  intros (H1, H2).
  unfold is_permut_fun_bool.
  apply andb_true_iff.
  split. {
    rewrite iter_seq_all_d; [ easy | easy | | | ]. {
      apply andb_true_r.
    } {
      apply andb_assoc.
    } {
      intros i Hi.
      specialize (H1 (i - 1)) as H3.
      assert (H : i - 1 < n) by flia Hi.
      specialize (H3 H); clear H.
      now apply Nat.ltb_lt in H3.
    }
  } {
    rewrite iter_seq_all_d; [ easy | easy | | | ]. {
      apply andb_true_r.
    } {
      apply andb_assoc.
    } {
      intros i Hi.
      rewrite iter_seq_all_d; [ easy | easy | | | ]. {
        apply andb_true_r.
      } {
        apply andb_assoc.
      } {
        intros j Hj.
        apply orb_true_iff.
        specialize (H2 (i - 1) (j - 1)) as H3.
        assert (H : i - 1 < n) by flia Hi.
        specialize (H3 H); clear H.
        assert (H : j - 1 < n) by flia Hj.
        specialize (H3 H); clear H.
        destruct (Nat.eq_dec (f (i - 1)) (f (j - 1))) as [H4| H4]. {
          specialize (H3 H4); right.
          apply Nat.eqb_eq.
          flia Hi Hj H3.
        } {
          left.
          apply negb_true_iff.
          now apply Nat.eqb_neq.
        }
      }
    }
  }
} {
  intros Hb.
  unfold is_permut_fun_bool in Hb.
  apply andb_true_iff in Hb.
  destruct Hb as (H1, H2).
  split. {
    intros i Hi.
    specialize (and_seq_true_iff _ H1) as H3.
    cbn - [ "<?" ] in H3.
    specialize (H3 (i + 1)).
    assert (H : 1 ≤ i + 1 ≤ n) by flia Hi.
    specialize (H3 H); clear H.
    rewrite Nat.add_sub in H3.
    now apply Nat.ltb_lt in H3.
  } {
    intros i j Hi Hj Hij.
    specialize (and_seq_true_iff _ H2) as H3.
    cbn in H3.
    specialize (H3 (i + 1)).
    assert (H : 1 ≤ i + 1 ≤ n) by flia Hi.
    specialize (H3 H); clear H.
    rewrite Nat.add_sub, Hij in H3.
    specialize (and_seq_true_iff _ H3) as H4.
    cbn in H4.
    specialize (H4 (j + 1)).
    assert (H : 1 ≤ j + 1 ≤ n) by flia Hj.
    specialize (H4 H); clear H.
    apply orb_true_iff in H4.
    rewrite Nat.add_sub in H4.
    destruct H4 as [H4| H4]. {
      apply negb_true_iff in H4.
      now apply Nat.eqb_neq in H4.
    } {
      apply Nat.eqb_eq in H4.
      do 2 rewrite Nat.add_1_r in H4.
      now apply Nat.succ_inj in H4.
    }
  }
}
Qed.

Theorem is_permut_vect_is_permut_vect_bool : ∀ v,
  is_permut_vect v ↔ is_permut_vect_bool v = true.
Proof.
intros.
unfold is_permut_vect.
apply is_permut_fun_is_permut_fun_bool.
Qed.

Fixpoint permut_fun_inv_loop f i j :=
  match i with
  | 0 => 42
  | S i' => if Nat.eq_dec (f i') j then i' else permut_fun_inv_loop f i' j
  end.

Definition permut_vect_inv (σ : vector nat) :=
  mk_vect
    (map (permut_fun_inv_loop (vect_el 0 σ) (vect_size σ))
       (seq 0 (vect_size σ))).

Definition transposition i j k :=
  if k =? i then j else if k =? j then i else k.

Definition swap_elem (f : nat → nat) i j k :=
  f (transposition i j k).

Definition vect_swap_elem {A} d (v : vector A) i j :=
  mk_vect
    (map (λ k, vect_el d v (transposition i j k))
       (seq 0 (length (vect_list v)))).

Theorem permut_fun_inv_loop_ext_in : ∀ f g i j,
  (∀ k, k < i → f k = g k)
  → permut_fun_inv_loop f i j = permut_fun_inv_loop g i j.
Proof.
intros * Hfg.
revert j.
induction i; intros; [ easy | cbn ].
destruct (Nat.eq_dec (f i) j) as [Hf| Hf]. {
  destruct (Nat.eq_dec (g i) j) as [Hg| Hg]; [ easy | ].
  specialize (Hfg i (Nat.lt_succ_diag_r _)); congruence.
}
destruct (Nat.eq_dec (g i) j) as [Hg| Hg]. {
  specialize (Hfg i (Nat.lt_succ_diag_r _)); congruence.
}
apply IHi.
intros k Hk.
apply Hfg; flia Hk.
Qed.

Theorem is_permut_eq_compat : ∀ n f g,
  (∀ i, i < n → f i = g i)
  → is_permut_fun f n
  → is_permut_fun g n.
Proof.
intros * Hfg (H1, H2).
split. {
  intros i Hi.
  rewrite <- Hfg; [ now apply H1 | easy ].
} {
  intros i j Hi Hj Hgij.
  apply H2; [ easy | easy | ].
  rewrite Hfg; [ | easy ].
  now rewrite Hfg.
}
Qed.

Theorem permut_ub : ∀ n f i,
  is_permut_fun f n → i < n → f i < n.
Proof.
intros * Hp Hin.
now apply Hp.
Qed.

Theorem transposition_lt : ∀ i j k n,
  i < n
  → j < n
  → k < n
  → transposition i j k < n.
Proof.
intros * Hi Hj Hk.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i); [ easy | ].
now destruct (Nat.eq_dec k j).
Qed.

Theorem transposition_out : ∀ i j k, k ≠ i → k ≠ j → transposition i j k = k.
Proof.
intros * Hi Hj.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i) as [H| H]; [ easy | clear H ].
now destruct (Nat.eq_dec k j).
Qed.

Theorem transposition_id : ∀ i k, transposition i i k = k.
Proof.
intros.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
now destruct (Nat.eq_dec k i).
Qed.

Theorem transposition_1 : ∀ i j, transposition i j i = j.
Proof.
intros.
unfold transposition.
now rewrite Nat.eqb_refl.
Qed.

Theorem transposition_2 : ∀ i j, transposition i j j = i.
Proof.
intros.
unfold transposition.
rewrite Nat.eqb_refl.
rewrite if_eqb_eq_dec.
now destruct (Nat.eq_dec j i).
Qed.

Theorem transposition_comm : ∀ i j k, transposition i j k = transposition j i k.
Proof.
intros.
unfold transposition.
do 4 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i) as [Hki| Hki]. {
  destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ congruence | easy ].
} {
  destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ congruence | easy ].
}
Qed.

Theorem vect_swap_elem_is_permut : ∀ n σ p q,
  p < n
  → q < n
  → is_permut_fun σ n
  → is_permut_fun (swap_elem σ p q) n.
Proof.
intros * Hp Hq Hσ.
split; cbn. {
  intros i Hi.
  unfold swap_elem.
  apply permut_ub; [ easy | ].
  now apply transposition_lt.
} {
  intros * Hi Hj Hij.
  unfold swap_elem in Hij.
  unfold transposition in Hij.
  do 4 rewrite if_eqb_eq_dec in Hij.
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

(*
   Canonical Permutations.

   The symmetric group is built this way. The k-th permutation is a
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

(*
Definition fin_of_nat_mod_fact a n :=
  @Fin.of_nat_lt (a mod n!) n!
     (Nat.mod_upper_bound a n! (fact_neq_0 n)).

Definition sym_gr_fun n (σ_n : Fin.t n! → nat → nat) k j : nat :=
  match j with
  | 0 => k / n!
  | S j' =>
      σ_n (fin_of_nat_mod_fact k n) j' +
      Nat.b2n (k / n! <=? σ_n (fin_of_nat_mod_fact k n) j')
  end.
*)

Definition sym_gr_fun n (σ_n : nat → nat → nat) k j : nat :=
  match j with
  | 0 => k / n!
  | S j' => σ_n (k mod n!) j' + Nat.b2n (k / n! <=? σ_n (k mod n!) j')
  end.

Fixpoint mk_canon_sym_gr n : nat → nat → nat :=
  match n with
  | 0 => λ _ _, 0
  | S n' => sym_gr_fun n' (mk_canon_sym_gr n')
  end.

(*
Fixpoint list_of_truc n (f : nat → nat) :=
  match n with
  | 0 => []
  | S n' => list_of_truc n' f ++ [f n']
  end.

Fixpoint list_of_machin n (f : nat → nat → nat) k :=
  match k with
  | 0 => []
  | S k' => list_of_machin n f k' ++ [list_of_truc n (f k')]
  end.

Definition list_of_bidule n (f : nat → nat → nat → nat) :=
  list_of_machin n (f n) n!.

Compute (list_of_bidule 3 mk_canon_sym_gr).
Compute (list_of_bidule 4 mk_canon_sym_gr).
*)

Definition mk_canon_sym_gr_vect n : vector (vector nat) :=
  mk_vect
    (map (λ k, mk_vect (map (mk_canon_sym_gr n k) (seq 0 n))) (seq 0 n!)).

(*
Compute map (vect_list (T := nat)) (vect_list (mk_canon_sym_gr_vect 4)).
*)

Definition is_sym_gr n (f : nat → nat → nat) :=
  (∀ i j, i < n! → j < n! → (∀ k, k < n → f i k = f j k) → i = j) ∧
  (∀ i, i < n! → is_permut_fun (f i) n).

Definition is_sym_gr_vect n (vv : vector (vector nat)) :=
  (∀ i, i < vect_size vv →
   vect_size (vect_el empty_vect vv i) = n ∧
   is_permut_vect (vect_el empty_vect vv i)) ∧
  (∀ i j, i < vect_size vv → j < vect_size vv →
   vect_el empty_vect vv i = vect_el empty_vect vv j → i = j) ∧
  (∀ v, vect_size v = n → is_permut_vect v → v ∈ vect_list vv).

Definition is_sym_gr_bool n (f : nat → nat → nat) :=
  ⋀ (i = 1, n!), ⋀ (j = 1, n!),
     (negb (⋀ (k = 1, n), (f (i - 1) (k - 1) =? f (j - 1) (k - 1))) ||
      (i =? j)) &&
  ⋀ (i = 1, n!), is_permut_fun_bool (f (i - 1)) n.

Theorem sym_gr_vect_elem : ∀ n sg,
  is_sym_gr_vect n sg →
  (∀ σ, vect_size σ = n ∧ is_permut_vect σ ↔ σ ∈ vect_list sg).
Proof.
intros * Hsg σ.
split. {
  intros (Hs, Hp).
  now apply Hsg.
} {
  intros Hσ.
  apply In_nth with (d := empty_vect) in Hσ.
  destruct Hσ as (i & Hi & Hσ).
  subst σ.
  now apply Hsg.
}
Qed.

(* *)

Definition permut_prop n v :=
  vect_size v = n ∧ is_permut_vect v.
Definition permut_prop_bool n v :=
  (vect_size v =? n) && is_permut_vect_bool v.

Definition nat_and_permut_prop n '(i, v) :=
  i < S n ∧ vect_size v = n ∧ is_permut_vect v.
Definition nat_and_permut_prop_bool n '(i, v) :=
   (i <? S n) && (vect_size v =? n) && is_permut_vect_bool v.

Definition permut n :=
  {u : vector nat | permut_prop_bool n u = true}.
Definition nat_and_permut n :=
  {iv : nat * vector nat | nat_and_permut_prop_bool n iv = true}.

Theorem permut_prop_permut_prop_bool : ∀ n v,
  permut_prop n v ↔ permut_prop_bool n v = true.
Proof.
intros.
split; intros Hφ. {
  destruct Hφ as (H1 & H2).
  apply andb_true_iff.
  apply Nat.eqb_eq in H1.
  now apply is_permut_fun_is_permut_fun_bool in H2.
} {
  apply andb_true_iff in Hφ.
  destruct Hφ as (H1, H2).
  apply Nat.eqb_eq in H1.
  now apply is_permut_fun_is_permut_fun_bool in H2.
}
Qed.

Theorem nat_and_permut_prop_nat_and_permut_prop_bool : ∀ n iv,
  nat_and_permut_prop n iv ↔ nat_and_permut_prop_bool n iv = true.
Proof.
intros n (i, v).
split; intros Hφ'. {
  destruct Hφ' as (H1 & H2 & H3).
  unfold nat_and_permut_prop_bool.
  apply andb_true_iff.
  split. {
    apply andb_true_iff.
    split; [ now apply Nat.ltb_lt | now apply Nat.eqb_eq ].
  } {
    now apply is_permut_fun_is_permut_fun_bool.
  }
} {
  apply andb_true_iff in Hφ'.
  destruct Hφ' as (H1, H3).
  apply andb_true_iff in H1.
  destruct H1 as (H1, H2).
  apply Nat.ltb_lt in H1.
  apply Nat.eqb_eq in H2.
  split; [ easy | ].
  split; [ easy | ].
  now apply is_permut_fun_is_permut_fun_bool.
}
Qed.

(* *)

Definition vect_eqb A eqb (u v : vector A) :=
  list_eqb eqb (vect_list u) (vect_list v).

Definition rank_of_permut_in_sym_gr (sg : vector (vector nat)) σ :=
  unsome 0 (List_find_nth (vect_eqb Nat.eqb σ) (vect_list sg)).

(*
Compute (mk_canon_sym_gr_vect 4).
Compute (rank_of_permut_in_sym_gr (mk_canon_sym_gr_vect 4) (mk_vect [0;1;3;2])).
Compute (rank_of_permut_in_sym_gr (mk_canon_sym_gr_vect 4) (mk_vect [2;3;0;1])).
Compute (rank_of_permut_in_sym_gr (mk_canon_sym_gr_vect 4) (mk_vect [2;3;0])).
Compute (rank_of_permut_in_sym_gr (mk_canon_sym_gr_vect 0) (mk_vect [2;3;0])).
*)

Theorem vect_eqb_eq : ∀ u v, vect_eqb Nat.eqb u v = true → u = v.
Proof.
intros * Huv.
unfold vect_eqb in Huv.
destruct u as (u).
destruct v as (v).
cbn in Huv; f_equal.
now apply list_eqb_eq.
Qed.

Theorem vect_eqb_neq : ∀ u v, vect_eqb Nat.eqb u v = false → u ≠ v.
Proof.
intros * Huv.
destruct u as (u).
destruct v as (v).
intros H.
injection H; clear H; intros H.
revert H.
now apply list_eqb_neq.
Qed.

Theorem rank_of_permut_in_sym_gr_lt : ∀ n sg v,
  n ≠ 0
  → is_sym_gr_vect n sg
  → rank_of_permut_in_sym_gr sg v < vect_size sg.
Proof.
intros * Hnz Hsg.
unfold rank_of_permut_in_sym_gr.
unfold unsome.
remember (List_find_nth _ _) as i eqn:Hi; symmetry in Hi.
destruct i as [i| ]; [ now apply List_find_nth_Some_lt in Hi | ].
clear Hi.
destruct (lt_dec 0 (vect_size sg)) as [Hs| Hs]; [ easy | ].
apply Nat.nlt_ge in Hs; exfalso.
apply Nat.le_0_r in Hs.
destruct Hsg as (Hsg & Hinj & Hsurj).
specialize (Hsurj (mk_vect (seq 0 n))) as H1.
cbn in H1; rewrite seq_length in H1.
specialize (H1 eq_refl).
assert (H : is_permut_vect (mk_vect (seq 0 n))). {
  split; cbn; rewrite seq_length. {
    intros i Hin.
    now rewrite seq_nth.
  } {
    intros i j Hi Hj Hij.
    rewrite seq_nth in Hij; [ | easy ].
    now rewrite seq_nth in Hij.
  }
}
specialize (H1 H); clear H.
apply length_zero_iff_nil in Hs.
now rewrite Hs in H1.
Qed.

Theorem vect_el_rank_of_permut_in_sym_gr : ∀ sg v n,
  is_sym_gr_vect n sg
  → is_permut_vect v
  → vect_size v = n
  → vect_el empty_vect sg (rank_of_permut_in_sym_gr sg v) = v.
Proof.
intros * Hsg Hp Hs.
unfold rank_of_permut_in_sym_gr, unsome.
remember (List_find_nth _ _) as i eqn:Hi; symmetry in Hi.
destruct i as [i| ]. {
  apply List_find_nth_Some with (d := empty_vect) in Hi.
  destruct Hi as (Hji, Hi).
  now apply vect_eqb_eq in Hi.
}
assert (H : v ∉ vect_list sg). {
  intros H.
  apply In_nth with (d := empty_vect) in H.
  destruct H as (j & Hj & Hjv).
  specialize (List_find_nth_None empty_vect _ _ Hi Hj) as H.
  apply vect_eqb_neq in H.
  now symmetry in Hjv.
}
exfalso; apply H.
now apply Hsg.
Qed.

Theorem rank_of_permut_in_sym_gr_vect_el : ∀ n sg i,
  n ≠ 0
  → is_sym_gr_vect n sg
  → i < vect_size sg
  → rank_of_permut_in_sym_gr sg (vect_el empty_vect sg i) = i.
Proof.
intros * Hnz Hsg Hi.
unfold rank_of_permut_in_sym_gr, unsome.
remember (List_find_nth _ _) as j eqn:Hj; symmetry in Hj.
destruct j as [j| ]. {
  apply List_find_nth_Some with (d := empty_vect) in Hj.
  destruct Hj as (Hji, Hj).
  apply vect_eqb_eq in Hj.
  rewrite fold_vect_el in Hj.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  apply Hinj; [ | easy | easy ].
  destruct (lt_dec j (vect_size sg)) as [Hjs| Hjs]; [ easy | exfalso ].
  apply Nat.nlt_ge in Hjs.
  unfold vect_el in Hj at 2.
  rewrite nth_overflow in Hj; [ | easy ].
  specialize (Hsg i Hi) as H1.
  destruct H1 as (H1, H2).
  now rewrite Hj in H1; cbn in H1; subst n.
}
specialize (List_find_nth_None empty_vect _ _ Hj Hi) as H1.
now apply vect_eqb_neq in H1.
Qed.

(* *)

Theorem vect_size_of_empty_sym_gr : ∀ sg,
  is_sym_gr_vect 0 sg → vect_size sg = 1.
Proof.
intros * Hsg.
destruct Hsg as (Hsg & Hinj & Hsurj).
specialize (Hsurj empty_vect eq_refl) as H1.
assert (H : is_permut_vect empty_vect) by easy.
specialize (H1 H); clear H.
apply (In_nth _ _ empty_vect) in H1.
destruct H1 as (i & Hil & Hi).
unfold vect_el in Hi.
rewrite fold_vect_size in Hil.
destruct (Nat.eq_dec (vect_size sg) 0) as [Hvz| Hvz]. {
  now rewrite Hvz in Hil.
}
destruct (Nat.eq_dec (vect_size sg) 1) as [Hv1| Hv1]; [ easy | ].
specialize (Hsg 0) as H1.
specialize (Hsg 1) as H2.
specialize (Hinj 0 1) as H3.
assert (H : 0 < vect_size sg) by flia Hvz.
specialize (H1 H); specialize (H3 H); clear H.
assert (H : 1 < vect_size sg) by flia Hvz Hv1.
specialize (H2 H); specialize (H3 H); clear H.
destruct H1 as (H4, H5).
destruct H2 as (H6, H7).
enough (H : vect_el empty_vect sg 0 = vect_el empty_vect sg 1). {
  now apply H3 in H.
}
unfold vect_size in H4, H6.
apply length_zero_iff_nil in H4, H6.
unfold vect_el in H4, H6 |-*.
remember (nth 0 (vect_list sg) empty_vect) as x eqn:Hx.
remember (nth 1 (vect_list sg) empty_vect) as y eqn:Hy.
symmetry in Hx, Hy.
destruct x as (x).
destruct y as (y).
cbn in H4, H6.
now subst x y.
Qed.

Theorem vect_size_of_sym_gr_1 : ∀ sg,
  is_sym_gr_vect 1 sg → vect_size sg = 1.
Proof.
intros * Hsg.
destruct Hsg as (Hsg & Hinj & Hsurj); cbn.
destruct sg as (lv); cbn in *.
destruct lv as [| v1]. {
  specialize (Hsurj (mk_vect [0]) eq_refl).
  assert (H : is_permut_vect (mk_vect [0])). {
    split. {
      intros i Hi.
      apply Nat.lt_1_r in Hi; subst i.
      cbn; flia.
    }
    intros i j Hi Hj.
    cbn in Hi, Hj.
    now apply Nat.lt_1_r in Hi, Hj; subst i j; cbn.
  }
  now specialize (Hsurj H); clear H.
}
destruct lv as [| v2]; [ easy | exfalso ].
specialize (Hinj 0 1).
specialize (Hsg 0) as H1.
specialize (Hsg 1) as H2.
cbn in Hinj, H1, H2.
assert (H : 0 < S (S (length lv))) by flia.
specialize (Hinj H); specialize (H1 H); clear H.
assert (H : 1 < S (S (length lv))) by flia.
specialize (Hinj H); specialize (H2 H); clear H.
destruct H2 as (H3, H4).
destruct H1 as (H1, H2).
assert (H : v1 = v2). {
  destruct v1 as (la).
  destruct v2 as (lb).
  cbn in H1, H3.
  destruct la as [| a]; [ easy | ].
  destruct la; [ clear H1 | easy ].
  destruct lb as [| b]; [ easy | ].
  destruct lb; [ clear H3 | easy ].
  destruct H4 as (H3, H4).
  destruct H2 as (H1, H2).
  specialize (H1 0 Nat.lt_0_1); cbn in H1.
  specialize (H3 0 Nat.lt_0_1); cbn in H3.
  now apply Nat.lt_1_r in H1, H3; subst a b.
}
now specialize (Hinj H).
Qed.

Definition permut_but_highest n σ :=
  mk_vect
    (map (λ i, vect_el 0 σ (if vect_el 0 σ i =? n then n else i))
       (seq 0 n)).

(* seems useless... *)
Theorem permut_but_highest_prop : ∀ n σ,
   vect_size σ = S (S n) ∧ is_permut_vect σ
   → vect_size (permut_but_highest (S n) σ) = S n ∧
      is_permut_vect (permut_but_highest (S n) σ).
Proof.
intros * (Hsσ, Hσ).
split. {
  unfold permut_but_highest; cbn.
  now rewrite map_length, seq_length.
}
split. {
  intros i Hi.
  unfold permut_but_highest in Hi; cbn in Hi.
  rewrite map_length, seq_length in Hi.
  unfold permut_but_highest; cbn - [ seq ].
  rewrite map_length, seq_length.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (vect_el 0 σ i) (S n)) as [H1| H1]. {
    destruct Hσ as (H2 & H3).
    specialize (H3 (S n) i).
    assert (H : S n < vect_size σ) by flia Hsσ.
    specialize (H3 H); clear H.
    assert (H : i < vect_size σ) by flia Hsσ Hi.
    specialize (H3 H); clear H.
    rewrite H1 in H3.
    rewrite Hsσ in H2.
    specialize (H2 (S n) (Nat.lt_succ_diag_r _)).
    assert (H : vect_el 0 σ (S n) ≠ S n). {
      intros H; specialize (H3 H); flia H3 Hi.
    }
    flia H2 H.
  } {
    destruct Hσ as (H2 & H3).
    specialize (H2 i).
    assert (H : i < vect_size σ) by flia Hsσ Hi.
    specialize (H2 H); clear H.
    flia Hsσ H2 H1.
  }
} {
  intros i j Hi Hj Hij.
  unfold permut_but_highest in Hi, Hj, Hij.
  cbn - [ seq ] in Hi, Hj, Hij.
  rewrite map_length, seq_length in Hi, Hj.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l, if_eqb_eq_dec in Hij.
  apply Hσ; [ flia Hsσ Hi | flia Hsσ Hj | ].
  destruct Hσ as (H2, H3).
  rewrite Hsσ in H2.
  destruct (Nat.eq_dec (vect_el 0 σ i) (S n)) as [Hin| Hin]. {
    destruct (Nat.eq_dec (vect_el 0 σ j) (S n)) as [H| H]; [ congruence | ].
    apply H3 in Hij; [ | flia Hsσ | flia Hj Hsσ ].
    flia Hj Hij.
  } {
    destruct (Nat.eq_dec (vect_el 0 σ j) (S n)) as [H| H]; [ | congruence ].
    apply H3 in Hij; [ | flia Hi Hsσ | flia Hsσ ].
    flia Hi Hij.
  }
}
Qed.

Definition last_and_permut_of_vect n σ :=
  (vect_el 0 σ n, permut_but_highest n σ).

Definition vect_of_last_and_permut n a :=
  let '(i, v) := a in
    mk_vect
      (map
         (λ j,
          if j =? n then i
          else if vect_el 0 v j =? i then n
          else vect_el 0 v j)
         (seq 0 (S n))).

Theorem vect_of_last_and_permut_of_its_inverse : ∀ n x,
  vect_size x = S n
  → is_permut_vect x
  → vect_of_last_and_permut n (last_and_permut_of_vect n x) = x.
Proof.
intros n (l) Hv Hp; cbn in Hv.
unfold is_permut_vect in Hp; cbn in Hp.
unfold vect_el in Hp; cbn in Hp.
rewrite Hv in Hp; cbn in Hp.
destruct Hp as (Hp1, Hp2).
unfold vect_of_last_and_permut.
unfold last_and_permut_of_vect.
unfold permut_but_highest.
f_equal.
cbn - [ seq ].
rewrite (seq_S n).
cbn - [ seq ].
rewrite map_app.
cbn - [ seq ].
rewrite Nat.eqb_refl.
erewrite map_ext_in. 2: {
  intros i Hi; apply in_seq in Hi.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i (S n)) as [H1| H1]; [ flia Hi H1 | ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  easy.
}
replace (nth n l 0) with (last l 0). 2: {
  now rewrite List_last_nth, Hv, Nat_sub_succ_1.
}
rewrite app_removelast_last with (d := 0). 2: {
  now intros H; rewrite H in Hv.
}
f_equal.
rewrite List_map_nth_seq with (d := 0).
replace (length (removelast l)) with n. 2: {
  destruct l using rev_ind; [ easy | ].
  rewrite removelast_last.
  rewrite app_length, Nat.add_1_r in Hv.
  now apply Nat.succ_inj in Hv.
}
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i n) as [H| H]; [ flia Hi H | clear H ].
destruct (Nat.eq_dec (nth i l 0) n) as [H1| H1]. {
  destruct (Nat.eq_dec (nth n l 0) (last l 0)) as [H2| H2]. {
    rewrite <- H1.
    destruct l as [| a] using rev_ind; [ easy | ].
    rewrite removelast_last.
    rewrite app_nth1; [ easy | ].
    rewrite app_length in Hv.
    rewrite Nat.add_1_r in Hv.
    apply Nat.succ_inj in Hv.
    now rewrite Hv.
  }
  destruct l as [| a] using rev_ind; [ easy | ].
  rewrite app_length, Nat.add_1_r in Hv.
  apply Nat.succ_inj in Hv.
  rewrite app_nth2 in H2; [ | flia Hv ].
  now rewrite Hv, Nat.sub_diag, last_last in H2.
}
destruct (Nat.eq_dec (nth i l 0) (last l 0)) as [H2| H2]. {
  destruct l as [| a] using rev_ind; [ easy | ].
  rewrite app_length in Hv.
  rewrite Nat.add_1_r in Hv.
  apply Nat.succ_inj in Hv.
  rewrite removelast_last.
  rewrite app_nth1 in H1; [ | now rewrite <- Hv in Hi ].
  rewrite app_nth1 in H2; [ | now rewrite <- Hv in Hi ].
  rewrite last_last in H2.
  specialize (Hp2 i n).
  assert (H : i < S n) by flia Hv Hi.
  specialize (Hp2 H (Nat.lt_succ_diag_r _)); clear H.
  rewrite app_nth1 in Hp2; [ | flia Hv Hi ].
  rewrite app_nth2 in Hp2; [ | flia Hv ].
  rewrite Hv, Nat.sub_diag in Hp2.
  cbn in Hp2.
  specialize (Hp2 H2).
  flia Hp2 Hi.
}
destruct l as [| a] using rev_ind; [ easy | ].
rewrite app_length in Hv.
rewrite Nat.add_1_r in Hv.
apply Nat.succ_inj in Hv.
rewrite removelast_last.
rewrite app_nth1; [ easy | flia Hv Hi ].
Qed.

Theorem last_and_permut_of_vect_el_of_its_inverse : ∀ n y,
  vect_size (snd y) = n
  → is_permut_vect (snd y)
  → last_and_permut_of_vect n (vect_of_last_and_permut n y) = y.
Proof.
intros n (i, v) Hv Hp; cbn in Hv, Hp.
unfold vect_of_last_and_permut.
unfold last_and_permut_of_vect, permut_but_highest.
cbn - [ seq ].
f_equal. {
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia ].
  rewrite seq_nth; [ | flia ].
  now rewrite Nat.eqb_refl.
} {
  destruct v as (l); cbn in Hv.
  f_equal.
  rewrite List_map_nth_seq with (d := 0).
  rewrite Hv.
  apply map_ext_in.
  intros j Hj; apply in_seq in Hj.
  destruct Hj as (_, Hj); cbn in Hj.
  cbn - [ seq ].
  rewrite (@List_map_nth' _ _ 0 _ _ _ j). 2: {
    rewrite seq_length; flia Hj.
  }
  rewrite seq_nth; [ | flia Hj ].
  rewrite Nat.add_0_l.
  do 3 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec j n) as [H| H]; [ flia Hj H | clear H ].
  destruct (Nat.eq_dec (nth j l 0) i) as [H1| H1]. {
    rewrite <- if_eqb_eq_dec, Nat.eqb_refl.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia ].
    rewrite seq_nth; [ | flia ].
    now rewrite Nat.eqb_refl.
  }
  destruct (Nat.eq_dec (nth j l 0) n) as [H2| H2]. {
    destruct Hp as (Hp1, Hp2); cbn in Hp1, Hp2.
    specialize (Hp1 j).
    rewrite Hv, H2 in Hp1.
    specialize (Hp1 Hj).
    flia Hp1.
  }
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj ].
  rewrite seq_nth; [ | flia Hj ].
  rewrite Nat.add_0_l.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec j n) as [H| H]; [ flia Hj H | clear H ].
  rewrite if_eqb_eq_dec.
  now destruct (Nat.eq_dec (nth j l 0) i).
}
Qed.


Theorem last_and_permut_of_vect_is_nat_and_permut_prop_bool : ∀ n v,
  permut_prop_bool (S n) v = true
  → nat_and_permut_prop_bool n (last_and_permut_of_vect n v) = true.
Proof.
intros * Hv.
apply nat_and_permut_prop_nat_and_permut_prop_bool.
apply permut_prop_permut_prop_bool in Hv.
unfold permut_prop in Hv.
unfold nat_and_permut_prop.
destruct Hv as (Hv, Hp).
unfold is_permut_vect in Hp; cbn in Hp.
unfold vect_el in Hp; cbn in Hp.
rewrite Hv in Hp; cbn in Hp.
destruct Hp as (Hp1, Hp2).
unfold vect_of_last_and_permut.
unfold last_and_permut_of_vect, permut_but_highest.
cbn - [ seq ].
rewrite map_length, seq_length.
split; [ apply Hp1; flia | ].
split; [ easy | ].
unfold is_permut_vect.
cbn - [ seq ].
rewrite map_length, seq_length.
unfold vect_el.
cbn - [ seq ].
eapply is_permut_eq_compat. {
  intros i Hi; symmetry.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  easy.
}
split. {
  intros i Hi.
  rewrite if_eqb_eq_dec.
  unfold vect_el.
  destruct (Nat.eq_dec (nth i (vect_list v) 0) n) as [H1| H1].  {
    specialize (Hp2 i n) as H2.
    assert (H : i < S n) by flia Hi.
    specialize (H2 H (Nat.lt_succ_diag_r _)); clear H.
    assert (H3 : vect_el 0 v i ≠ vect_el 0 v n). {
      intros H; specialize (H2 H); flia Hi H2.
    }
    unfold vect_el in H3.
    rewrite H1 in H3.
    apply Nat.neq_sym in H3.
    apply Nat_le_neq_lt; [ | easy ].
    apply Nat.lt_succ_r.
    apply Hp1, Nat.lt_succ_diag_r.
  } {
    apply Nat_le_neq_lt; [ | easy ].
    apply Nat.lt_succ_r.
    apply Hp1; flia Hi.
  }
} {
  intros i j Hi Hj Hij.
  do 2 rewrite if_eqb_eq_dec in Hij.
  unfold vect_el in Hij.
  destruct (Nat.eq_dec (nth i (vect_list v) 0) n) as [H1| H1]. {
    destruct (Nat.eq_dec (nth j (vect_list v) 0) n) as [H2| H2]. {
      apply Hp2; [ flia Hv Hi | flia Hv Hj | ].
      unfold vect_el; congruence.
    }
    apply Hp2 in Hij; [ flia Hj Hij | flia Hv | flia Hj Hv ].
  }
  destruct (Nat.eq_dec (nth j (vect_list v) 0) n) as [H2| H2]. {
    apply Hp2 in Hij; [ flia Hi Hij | flia Hv Hi | flia Hv ].
  }
  apply Hp2; [ flia Hv Hi | flia Hv Hj | ].
  unfold vect_el; congruence.
}
Qed.

Theorem vect_of_last_and_permut_is_permut_proop_bool : ∀ n iv,
  nat_and_permut_prop_bool n iv = true
 → permut_prop_bool (S n) (vect_of_last_and_permut n iv) = true.
Proof.
intros n (i, v) Hp.
apply permut_prop_permut_prop_bool.
apply nat_and_permut_prop_nat_and_permut_prop_bool in Hp.
destruct Hp as (Hi & Hv & Hp).
unfold permut_prop, vect_of_last_and_permut.
cbn - [ seq ].
rewrite map_length, seq_length.
split; [ easy | ].
unfold is_permut_vect.
cbn - [ seq ].
rewrite map_length, seq_length.
unfold vect_el.
cbn - [ seq ].
eapply is_permut_eq_compat. {
  intros j Hj; symmetry.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  do 2 rewrite if_eqb_eq_dec.
  easy.
}
split. {
  intros j Hj.
  destruct (Nat.eq_dec j n) as [Hjn| Hjn]; [ easy | ].
  destruct (Nat.eq_dec (nth j (vect_list v) 0) i) as [H1| H1]; [ flia | ].
  destruct Hp as (Hp1, Hp2).
  rewrite Hv in Hp1, Hp2.
  unfold vect_el in Hp1.
  assert (H : j < n) by flia Hj Hjn.
  specialize (Hp1 j H) as H2; clear H.
  flia H2.
} {
  intros j k Hj Hk Hjk.
  destruct (Nat.eq_dec j n) as [Hjn| Hjn]. {
    destruct (Nat.eq_dec k n) as [Hkn| Hkn]; [ congruence | ].
    symmetry in Hjk.
    destruct (Nat.eq_dec (nth k (vect_list v) 0) i) as [H| H]; [ | easy ].
    rename H into Hki.
    move Hjk at top; subst i; clear Hi.
    subst j; clear Hj.
    destruct Hp as (Hp1, Hp2).
    rewrite Hv in Hp1.
    specialize (Hp1 k) as H1.
    assert (H : k < n) by flia Hk Hkn.
    specialize (H1 H); clear H.
    unfold vect_el in H1.
    rewrite Hki in H1.
    flia H1.
  }
  destruct (Nat.eq_dec (nth j (vect_list v) 0) i) as [Hji| Hji]. {
    destruct (Nat.eq_dec k n) as [Hkn| Hkn]. {
      move Hjk at top; subst i.
      destruct Hp as (Hp1, Hp2).
      rewrite Hv in Hp1.
      specialize (Hp1 j) as H1.
      assert (H : j < n) by flia Hj Hjn.
      specialize (H1 H); clear H.
      unfold vect_el in H1.
      rewrite Hji in H1.
      flia H1.
    }
    destruct (Nat.eq_dec (nth k (vect_list v) 0) i) as [Hki| Hki]. {
      destruct Hp as (Hp1, Hp2).
      rewrite Hv in Hp1, Hp2.
      apply Hp2; [ flia Hj Hjn | flia Hk Hkn | unfold vect_el; congruence ].
    }
    symmetry in Hjk.
    destruct Hp as (Hp1, Hp2).
    rewrite Hv in Hp1.
    specialize (Hp1 k) as H1.
    assert (H : k < n) by flia Hk Hkn.
    specialize (H1 H); clear H.
    unfold vect_el in H1.
    rewrite Hjk in H1.
    flia H1.
  }
  destruct (Nat.eq_dec k n) as [Hkn| Hkn]; [ easy | ].
  destruct (Nat.eq_dec (nth k (vect_list v) 0) i) as [Hki| Hki]. {
    destruct Hp as (Hp1, Hp2).
    rewrite Hv in Hp1.
    specialize (Hp1 j) as H1.
    assert (H : j < n) by flia Hj Hjn.
    specialize (H1 H); clear H.
    unfold vect_el in H1.
    rewrite Hjk in H1.
    flia H1.
  }
  apply Hp; [ rewrite Hv; flia Hj Hjn | rewrite Hv; flia Hk Hkn | easy ].
}
Qed.

Definition nat_and_permut_of_permut n (x : permut (S n)) : nat_and_permut n :=
  exist (λ iv : nat * vector nat, nat_and_permut_prop_bool n iv = true)
    (last_and_permut_of_vect n (proj1_sig x))
    (last_and_permut_of_vect_is_nat_and_permut_prop_bool n (proj1_sig x)
       (proj2_sig x)).

Definition permut_of_nat_and_permut n (y : nat_and_permut n) : permut (S n) :=
  exist (λ u : vector nat, permut_prop_bool (S n) u = true)
     (vect_of_last_and_permut n (proj1_sig y))
     (vect_of_last_and_permut_is_permut_proop_bool n (proj1_sig y)
       (proj2_sig y)).

(* not sure it is useful *)
Theorem nat_and_permut_of_permut_of_its_inverse : ∀ n x,
  @nat_and_permut_of_permut n (permut_of_nat_and_permut x) = x.
Proof.
intros.
unfold nat_and_permut_of_permut, permut_of_nat_and_permut.
specialize
  (proj2 (nat_and_permut_prop_nat_and_permut_prop_bool n (proj1_sig x)))
  as H1.
destruct x as (iv, Hp); cbn in H1 |-*.
specialize (H1 Hp).
destruct iv as (i, v).
unfold nat_and_permut_prop in H1.
destruct H1 as (H1 & H2 & H3).
apply eq_exist_uncurried.
exists (last_and_permut_of_vect_el_of_its_inverse (i, v) H2 H3).
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

(* not sure it is useful *)
Theorem permut_of_nat_and_permut_of_its_inverse : ∀ n y,
  @permut_of_nat_and_permut n (nat_and_permut_of_permut y) = y.
Proof.
intros.
unfold nat_and_permut_of_permut, permut_of_nat_and_permut.
specialize (proj2 (permut_prop_permut_prop_bool (S n) (proj1_sig y))) as H1.
destruct y as (u, Hp); cbn in H1 |-*.
specialize (H1 Hp).
unfold permut_prop in H1.
destruct H1 as (H1 & H2).
apply eq_exist_uncurried.
exists (vect_of_last_and_permut_of_its_inverse H1 H2).
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Definition permut_of_fin_t n sg (Hsg : is_sym_gr_vect (S n) sg)
    (kpk : fin_t (vect_size sg)) : permut (S n) :=
  let (k, pk) := kpk in
  exist (λ u, permut_prop_bool (S n) u = true)
    (vect_el empty_vect sg k)
    (proj1 (permut_prop_permut_prop_bool (S n) (vect_el empty_vect sg k))
       (proj1 Hsg k (proj1 (Nat.ltb_lt k (vect_size sg)) pk))).

Theorem glop : ∀ n sg, is_sym_gr_vect n sg → vect_size sg = n!.
Proof.
intros * Hsg.
destruct n; [ now apply vect_size_of_empty_sym_gr | ].
revert sg Hsg.
induction n; intros; [ now apply vect_size_of_sym_gr_1 | ].
(**)
set (gv := λ vpv : permut (S (S n)),
  let (v, _) := vpv in
  exist (λ a, (a <? vect_size sg) = true)
    (rank_of_permut_in_sym_gr sg v)
    (proj2 (Nat.ltb_lt (rank_of_permut_in_sym_gr sg v) (vect_size sg))
       (rank_of_permut_in_sym_gr_lt v (Nat.neq_succ_0 (S n)) Hsg))).
fold (fin_t (vect_size sg)) in gv.
assert (Hfgv : ∀ x, permut_of_fin_t Hsg (gv x) = x). {
  intros (v, pv).
  unfold permut_of_fin_t, gv.
  specialize (proj2 (permut_prop_permut_prop_bool (S (S n)) v) pv) as H1.
  destruct H1 as (Hv, Hp).
  apply eq_exist_uncurried.
  exists (vect_el_rank_of_permut_in_sym_gr Hsg Hp Hv).
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
}
assert (Hgfv : ∀ y, gv (permut_of_fin_t Hsg y) = y). {
  intros (k, pk).
  unfold permut_of_fin_t, gv.
  specialize (proj1 (Nat.ltb_lt k (vect_size sg)) pk) as H1.
  apply eq_exist_uncurried.
  exists (rank_of_permut_in_sym_gr_vect_el (Nat.neq_succ_0 (S n)) Hsg H1).
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
}
destruct Hsg as (Hsg & Hinj & Hsurj).
assert
  (Hiφ' : ∀ i, i < vect_size sg →
   nat_and_permut_prop_bool (S n)
     (last_and_permut_of_vect (S n) (vect_el empty_vect sg i)) = true). {
  intros i His.
  apply nat_and_permut_prop_nat_and_permut_prop_bool.
  split. {
    specialize (Hsg i His) as H1.
    destruct H1 as (H1, H2).
    unfold is_permut_vect in H2.
    rewrite H1 in H2.
    destruct H2 as (H2, H3).
    apply H2; flia.
  }
  split. {
    unfold permut_but_highest; cbn; f_equal.
    now rewrite map_length, seq_length.
  } {
    unfold is_permut_vect.
    unfold is_permut_fun.
    replace (vect_size (permut_but_highest _ _)) with (S n). 2: {
      now cbn; rewrite map_length, seq_length.
    }
    split. {
      intros j Hj.
      unfold permut_but_highest; cbn - [ seq ].
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ | easy ].
      rewrite Nat.add_0_l.
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec _ _) as [Hvn| Hvn]. {
        specialize (Hsg i His) as H1.
        destruct H1 as (H1 & H2 & H3).
        rewrite H1 in H2, H3.
        specialize (H2 (S n) (Nat.lt_succ_diag_r _)).
        specialize (H3 j (S n)).
        assert (H : j < S (S n)) by flia Hj.
        specialize (H3 H); clear H.
        assert (H : S n < S (S n)) by flia.
        specialize (H3 H); clear H.
        rewrite Hvn in H3.
        apply Nat.nle_gt; intros H4.
        assert (H : S n = vect_el 0 (vect_el empty_vect sg i) (S n)). {
          flia H4 H2.
        }
        specialize (H3 H); clear H.
        rewrite H3 in Hj; flia Hj.
      }
      specialize (Hsg i His) as H1.
      destruct H1 as (H1 & H2 & H3).
      rewrite H1 in H2, H3.
      specialize (H2 j).
      assert (H : j < S (S n)) by flia Hj.
      specialize (H2 H); clear H.
      flia Hvn H2.
    } {
      intros j k Hj Hk Hjk.
      unfold permut_but_highest in Hjk.
      cbn - [ seq ] in Hjk.
      rewrite (List_map_nth' 0) in Hjk; [ | now rewrite seq_length ].
      rewrite (List_map_nth' 0) in Hjk; [ | now rewrite seq_length ].
      rewrite seq_nth in Hjk; [ | easy ].
      rewrite seq_nth in Hjk; [ | easy ].
      do 2 rewrite Nat.add_0_l in Hjk.
      do 2 rewrite if_eqb_eq_dec in Hjk.
      destruct (Nat.eq_dec _ _) as [Hjn| Hjn] in Hjk. {
        destruct (Nat.eq_dec _ _) as [Hkn| Hkn] in Hjk. {
          specialize (Hsg i His) as H1.
          destruct H1 as (H1 & H2 & H3).
          rewrite H1 in H2, H3.
          apply H3; [ flia Hj | flia Hk | ].
          congruence.
        }
        specialize (Hsg i His) as H1.
        destruct H1 as (H1 & H2 & H3).
        rewrite H1 in H2, H3.
        enough (H : k = S n) by flia Hk H.
        apply H3; [ flia Hk | flia | easy ].
      } {
        destruct (Nat.eq_dec _ _) as [Hkn| Hkn] in Hjk. {
          specialize (Hsg i His) as H1.
          destruct H1 as (H1 & H2 & H3).
          rewrite H1 in H2, H3.
          enough (H : j = S n) by flia Hj H.
          apply H3; [ flia Hj | flia | ].
          congruence.
        }
        specialize (Hsg i His) as H1.
        destruct H1 as (H1 & H2 & H3).
        rewrite H1 in H2, H3.
        apply H3; [ flia Hj | flia Hk | easy ].
      }
    }
  }
}
assert (Hzφ' :
  nat_and_permut_prop_bool (S n)
    (last_and_permut_of_vect (S n) (vect_el empty_vect sg 0)) = true). {
  destruct (Nat.eq_dec (vect_size sg) 0) as [Hsz| Hsz]. {
    exfalso.
    specialize (Hsurj (mk_vect (seq 0 (S (S n))))) as H1.
    cbn - [ seq ] in H1.
    rewrite seq_length in H1.
    specialize (H1 eq_refl).
    assert (H : is_permut_vect (mk_vect (seq 0 (S (S n))))). {
      split. {
        intros i Hi; cbn in Hi; rewrite seq_length in Hi.
        cbn - [ seq ].
        rewrite seq_length.
        now rewrite seq_nth.
      } {
        intros i j Hi Hj Hij.
        cbn - [ seq ] in Hi, Hj, Hij.
        rewrite seq_length in Hi, Hj.
        now do 2 rewrite seq_nth in Hij.
      }
    }
    specialize (H1 H); clear H.
    destruct sg as (lv).
    cbn - [ seq ] in Hsz, H1.
    apply length_zero_iff_nil in Hsz.
    now rewrite Hsz in H1.
  }
  apply nat_and_permut_prop_nat_and_permut_prop_bool.
  apply Nat.neq_0_lt_0 in Hsz.
  split. {
    specialize (Hsg 0 Hsz) as H1.
    destruct H1 as (H1 & H2 & H3).
    rewrite H1 in H2, H3.
    apply H2; flia.
  }
  split. {
    unfold permut_but_highest; cbn.
    now rewrite map_length, seq_length.
  } {
    unfold permut_but_highest.
    split. {
      cbn - [ seq ]; rewrite map_length, seq_length.
      intros i Hi.
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ | easy ].
      rewrite Nat.add_0_l.
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec _ _) as [Hsi| Hsi]. {
        specialize (Hsg 0 Hsz) as H1.
        destruct H1 as (H1 & H2 & H3).
        rewrite H1 in H2, H3.
        specialize (H2 (S n) (Nat.lt_succ_diag_r _)).
        specialize (H3 i (S n)).
        assert (H : i < S (S n)) by flia Hi.
        specialize (H3 H); clear H.
        assert (H : S n < S (S n)) by flia.
        specialize (H3 H); clear H.
        rewrite Hsi in H3.
        apply Nat.nle_gt; intros H4.
        assert (H : S n = vect_el 0 (vect_el empty_vect sg 0) (S n)). {
          flia H4 H2.
        }
        specialize (H3 H); clear H.
        rewrite H3 in Hi; flia Hi.
      } {
        specialize (Hsg 0 Hsz) as H1.
        destruct H1 as (H1 & H2 & H3).
        rewrite H1 in H2, H3.
        specialize (H2 i).
        assert (H : i < S (S n)) by flia Hi.
        specialize (H2 H).
        flia H2 Hsi.
      }
    } {
      cbn - [ seq ]; rewrite map_length, seq_length.
      intros i j Hi Hj Hij.
      rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
      rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
      rewrite seq_nth in Hij; [ | easy ].
      rewrite seq_nth in Hij; [ | easy ].
      do 2 rewrite Nat.add_0_l in Hij.
      do 2 rewrite if_eqb_eq_dec in Hij.
      destruct (Nat.eq_dec _ _) as [Hjn| Hjn] in Hij. {
        destruct (Nat.eq_dec _ _) as [Hkn| Hkn] in Hij. {
          specialize (Hsg 0 Hsz) as H1.
          destruct H1 as (H1 & H2 & H3).
          rewrite H1 in H2, H3.
          apply H3; [ flia Hi | flia Hj | ].
          congruence.
        }
        specialize (Hsg 0 Hsz) as H1.
        destruct H1 as (H1 & H2 & H3).
        rewrite H1 in H2, H3.
        specialize (H3 (S n) j).
        assert (H : S n < S (S n)) by flia.
        specialize (H3 H); clear H.
        assert (H : j < S (S n)) by flia Hj.
        specialize (H3 H Hij); clear H.
        rewrite H3 in Hj; flia Hj.
      } {
        destruct (Nat.eq_dec _ _) as [Hkn| Hkn] in Hij. {
          specialize (Hsg 0 Hsz) as H1.
          destruct H1 as (H1 & H2 & H3).
          rewrite H1 in H2, H3.
          specialize (H3 i (S n)).
          assert (H : i < S (S n)) by flia Hi.
          specialize (H3 H); clear H.
          assert (H : S n < S (S n)) by flia.
          specialize (H3 H Hij); clear H.
          rewrite H3 in Hi; flia Hi.
        }
        specialize (Hsg 0 Hsz) as H1.
        destruct H1 as (H1 & H2 & H3).
        rewrite H1 in H2, H3.
        apply H3; [ flia Hi | flia Hj | easy ].
      }
    }
  }
}
set (fnv := λ H1 : fin_t (S (S n))!,
  let (i, p) := H1 in
  match lt_dec i (vect_size sg) with
  | left His =>
      exist (λ iv : nat * vector nat, nat_and_permut_prop_bool (S n) iv = true)
        (last_and_permut_of_vect (S n) (vect_el empty_vect sg i))
        (Hiφ' i His)
  | right _ =>
      exist (λ iv : nat * vector nat, nat_and_permut_prop_bool (S n) iv = true)
        (last_and_permut_of_vect (S n) (vect_el empty_vect sg 0)) Hzφ'
  end).
...
assert (Hinj : FinFun.Injective φp). {
  unfold FinFun.Injective.
  intros x y Hxy.
  apply (f_equal φp') in Hxy.
  now do 2 rewrite Hy in Hxy.
}
assert (Hsurj : FinFun.Surjective φp). {
  unfold FinFun.Surjective.
  intros y.
  exists (φp' y).
  apply Hx.
}
specialize (proj1 (FinFun.Surjective_list_carac φp) Hsurj) as H1.
specialize FinFun.Injective_list_carac as H2.
specialize (H2 (vector_1 (S (S n))) (nat_and_permut (S n))).
assert (H : ListDec.decidable_eq (vector_1 (S (S n)))). {
  intros x y.
  unfold vector_1 in x, y.
  unfold Decidable.decidable.
  destruct x as (x, Px).
  destruct y as (y, Py).
  remember (vect_eqb Nat.eqb x y) as b eqn:Hb; symmetry in Hb.
  destruct b; [ left | right ]. {
    apply vect_eqb_eq in Hb.
    subst y.
    apply eq_exist_uncurried.
    exists eq_refl; cbn.
    apply (Eqdep_dec.UIP_dec Bool.bool_dec).
  } {
    apply vect_eqb_neq in Hb.
    intros H; apply Hb; clear Hb; rename H into Hb.
    now injection Hb.
  }
}
specialize (proj1 (H2 H φp) Hinj) as H3; clear H H2.
...
unfold vector_1 in H3.
Search FinFun.Injective.
...
assert (H1 : FinFun.Bijective φp) by now exists φp'.
move IHn at bottom.
unfold φ_prop_bool in Hy.
unfold nat_and_permut_prop_bool in Hx.
move Hsg at bottom.
Print is_sym_gr_vect.
...
Search FinFun.Bijective.
Search FinFun.Injective.
Search FinFun.Surjective.
...
assert (∀ x, x ∈ vect_list vv → φ' (φ x) = x). {
  intros x Hx.
  apply (sym_gr_vect_elem Hsg) in Hx.
  now apply Hφ'φ.
}
move H before Hφ'φ; clear Hφ'φ; rename H into Hφ'φ.
...
(* ma méthode *)
...
assert
  (Hll1 : ∀ n sg s, is_sym_gr_vect (S (S n)) sg →
   length (select_in_list_vect (S n) (vect_list sg) s) ≤ vect_size sg). {
  clear sg Hsg n IHn.
  intros * Hsg.
  unfold select_in_list_vect.
  rewrite List_length_filter_negb; [ rewrite fold_vect_size; flia | ].
(* faudrait peut-être que j'utilise NoDup, tout simplement, dans ma définition
   de Hinj ? *)
  destruct Hsg as (Hsg & Hinj & Hsurj).
  clear - Hinj.
  unfold vect_el, vect_size in Hinj.
  remember (vect_list sg) as ll; clear sg Heqll.
  now apply NoDup_nth in Hinj.
}
assert
  (Hsgv : ∀ n sg s,
   vect_size (smaller_sym_gr_by_rem_biggest_at n sg s) =
   length (select_in_list_vect n (vect_list sg) s)). {
  intros.
  unfold smaller_sym_gr_by_rem_biggest_at; cbn.
  rewrite map_map.
  now rewrite map_length.
}
assert
  (Hss : ∀ n sg s, s < S (S n) → is_sym_gr_vect (S (S n)) sg →
   is_sym_gr_vect (S n) (smaller_sym_gr_by_rem_biggest_at (S n) sg s)). {
  clear n sg IHn Hsg.
  intros n sg s Hs Hsg.
  split. {
    intros i Hi; cbn.
    split. {
      unfold smaller_sym_gr_by_rem_biggest_at; cbn; rewrite map_map.
      rewrite (List_map_nth' empty_vect). 2: {
        destruct Hsg as (Hsg & Hinj & Hsurj).
        destruct sg as (lv); cbn in Hsg, Hinj, Hsurj |-*.
        destruct lv as [| v1]. {
          specialize (Hsg 0); cbn in Hsg.
          now destruct Hsg as (H2, H3).
        }
        destruct lv as [| v2]. {
          unfold smaller_sym_gr_by_rem_biggest_at.
          unfold select_in_list_vect in Hi; cbn in Hi.
          now rewrite map_map, map_length in Hi.
        }
        unfold smaller_sym_gr_by_rem_biggest_at.
        unfold select_in_list_vect in Hi; cbn in Hi.
        now rewrite map_map, map_length in Hi.
      }
      cbn.
      rewrite butn_length.
      destruct Hsg as (Hsg & Hinj & Hsurj).
      unfold smaller_sym_gr_by_rem_biggest_at in Hi; cbn in Hi.
      rewrite map_length in Hi.
      assert
        (Hss : ∀ j, j < vect_size sg →
         length (vect_list (nth j (vect_list sg) empty_vect)) = S (S n)). {
        intros j Hj.
        now specialize (Hsg j Hj) as H2.
      }
      unfold select_in_list_vect.
      unfold vect_el.
      specialize List_list_length_nth_filter as H2.
      specialize (H2 _ (map (@vect_list nat) (vect_list sg))).
      specialize (H2 (S (S n))).
      rewrite map_length, fold_vect_size in H2.
      specialize (H2 (λ l, nth s l 0 =? S n)).
      assert
        (H : ∀ j, j < vect_size sg →
         length (nth j (map (vect_list (T:=nat)) (vect_list sg)) []) =
         S (S n)). {
        intros j Hj.
        specialize (Hss j Hj).
        now rewrite (List_map_nth' empty_vect).
      }
      specialize (H2 H); clear H.
      specialize (H2 i).
      rewrite List_filter_map in H2.
      rewrite map_length in H2, Hi.
      fold (select_in_list_vect (S n) (vect_list sg) s) in H2 |-*.
      specialize (H2 Hi).
      rewrite (List_map_nth' empty_vect) in H2; [ | easy ].
      rewrite H2.
      now apply Nat.ltb_lt in Hs; rewrite Hs.
    }
    destruct Hsg as (Hsg & Hinj & Hsurj).
    rewrite map_map.
    rewrite (List_map_nth' empty_vect). 2: {
      unfold smaller_sym_gr_by_rem_biggest_at in Hi; cbn in Hi.
      now rewrite map_map, map_length in Hi.
    }
    unfold smaller_sym_gr_by_rem_biggest_at in Hi.
    cbn in Hi.
    rewrite map_map, map_length in Hi.
    unfold is_permut_vect; cbn.
    rewrite butn_length.
    assert
      (Hl :
       length
         (vect_list
            (nth i (select_in_list_vect (S n) (vect_list sg) s) empty_vect)) =
        S (S n)). {
      intros.
      unfold select_in_list_vect.
      specialize List_length_filter_nth as H2.
      specialize (H2 (vector nat)).
      specialize (H2 empty_vect).
      specialize (H2 (vect_list sg)).
      specialize (H2 _ _ Hi).
      destruct H2 as (k & Hkl & Hk & Hik & Hij).
      rewrite Hik.
      rewrite fold_vect_size.
      rewrite fold_vect_el in Hik |-*.
      now specialize (Hsg k Hkl).
    }
    rewrite Hl.
    apply Nat.ltb_lt in Hs; rewrite Hs; cbn.
    apply Nat.ltb_lt in Hs.
    split. {
      intros j Hj; cbn.
      specialize List_length_filter_nth as H2.
      specialize (H2 (vector nat)).
      specialize (H2 empty_vect).
      specialize (H2 (vect_list sg)).
      specialize (H2 _ _ Hi).
      destruct H2 as (k & Hkl & Hk & Hik & Hij).
      unfold select_in_list_vect in Hl |-*.
      rewrite Hik in Hl |-*.
      rewrite fold_vect_el in Hl |-*.
      specialize (Hsg k Hkl) as H2.
      destruct H2 as (H2, H3).
      destruct H3 as (H4, H5).
      rewrite H2 in H4, H5.
      apply Nat.eqb_eq in Hk.
      rewrite fold_vect_el in Hk.
      remember (vect_el empty_vect sg k) as lv eqn:Hlv.
      unfold vect_el in H4.
      unfold vect_el in Hk, H5.
      remember (vect_list lv) as la eqn:Hla.
      clear - Hl H5 H4 Hk Hs.
      unfold butn.
      rewrite (@List_split_at_pos _ s 0 la) in Hk; [ | now rewrite Hl ].
      rewrite app_nth2 in Hk; [ | rewrite firstn_length; flia ].
      rewrite firstn_length in Hk.
      rewrite Nat.min_l in Hk; [ | flia Hs Hl ].
      rewrite Nat.sub_diag in Hk; cbn in Hk.
      specialize (H5 s j Hs) as H6.
      destruct (lt_dec j (S (S n))) as [Hjn| Hjn]. 2: {
        apply Nat.nlt_ge in Hjn.
        rewrite nth_overflow; [ flia | ].
        rewrite app_length, firstn_length, skipn_length.
        rewrite Hl, Nat.min_l; [ | flia Hs ].
        flia Hjn Hs.
      }
      rewrite Hk in H6.
      specialize (H6 Hjn).
      rewrite List_app_nth, if_ltb_lt_dec, firstn_length.
      rewrite Nat.min_l; [ | rewrite Hl; flia Hs ].
      destruct (lt_dec j s) as [Hjs| Hjs]. {
        rewrite List_nth_firstn; [ | easy ].
        specialize (H4 j Hjn) as H1.
        destruct (Nat.eq_dec (S n) (nth j la 0)) as [Hnj| Hnj]. {
          specialize (H6 Hnj); flia H6 Hjs.
        }
        flia H1 Hnj.
      } {
        apply Nat.nlt_ge in Hjs.
        rewrite List_nth_skipn.
        replace (j - s + S s) with (S j) by flia Hjs.
        specialize (H4 (S j)) as H1.
        destruct (Nat.eq_dec (S n) (nth j la 0)) as [Hnj| Hnj]. {
          specialize (H6 Hnj); subst s.
          destruct (lt_dec (S j) (S (S n))) as [Hss| Hss]. {
            specialize (H1 Hss).
            specialize (H5 j (S j) Hjn Hss) as H2.
            rewrite <- Hnj in H2.
            destruct (Nat.eq_dec (S n) (nth (S j) la 0)) as [Hsss| Hsss]. {
              specialize (H2 Hsss); flia H2.
            }
            flia H1 Hsss.
          } {
            apply Nat.nlt_ge in Hss.
            rewrite nth_overflow; [ flia | ].
            now rewrite Hl.
          }
        } {
          destruct (lt_dec (S j) (S (S n))) as [Hss| Hss]. {
            specialize (H1 Hss).
            specialize (H5 s (S j) Hs Hss) as H2.
            rewrite Hk in H2.
            destruct (Nat.eq_dec (S n) (nth (S j) la 0)) as [Hsss| Hsss]. {
              specialize (H2 Hsss); flia H2 Hjs.
            }
            flia H1 Hsss.
          } {
            apply Nat.nlt_ge in Hss.
            rewrite nth_overflow; [ flia | ].
            now rewrite Hl.
          }
        }
      }
    } {
      intros j k Hj Hk Hjk; cbn in Hjk.
      specialize List_length_filter_nth as H2.
      specialize (H2 (vector nat)).
      specialize (H2 empty_vect).
      specialize (H2 (vect_list sg)).
      specialize (H2 (λ v, vect_el 0 v s =? S n)).
      fold (select_in_list_vect (S n) (vect_list sg) s) in H2; cbn in H2.
      specialize (H2 _ Hi).
      destruct H2 as (p & Hpl & Hp & Hip & Hij).
      rewrite Hip in Hjk.
      specialize (Hsg p) as H2.
      specialize (H2 Hpl).
      destruct H2 as (H2, H3).
      destruct H3 as (H3, H4).
      rewrite H2 in H3, H4.
      apply Nat.succ_lt_mono in Hj, Hk.
      do 2 rewrite nth_butn in Hjk.
      remember (s <=? j) as bj eqn:Hbj; symmetry in Hbj.
      remember (s <=? k) as bk eqn:Hbk; symmetry in Hbk.
      move bk before bj.
      do 3 rewrite fold_vect_el in Hjk; cbn in Hjk.
      specialize (H4 (j + Nat.b2n bj) (k + Nat.b2n bk)).
      assert (H : j + Nat.b2n bj < S (S n)). {
        destruct bj; cbn; flia Hj.
      }
      specialize (H4 H); clear H.
      assert (H : k + Nat.b2n bk < S (S n)). {
        destruct bk; cbn; flia Hk.
      }
      specialize (H4 H); clear H.
      specialize (H4 Hjk).
      rewrite Nat.add_comm in H4; symmetry in H4.
      rewrite Nat.add_comm in H4; symmetry in H4.
      destruct bj, bk; [ now apply Nat.succ_inj | | | easy ]. {
        apply Nat.leb_le in Hbj.
        apply Nat.leb_gt in Hbk.
        cbn in H4; flia Hbj Hbk H4.
      } {
        apply Nat.leb_gt in Hbj.
        apply Nat.leb_le in Hbk.
        cbn in H4; flia Hbj Hbk H4.
      }
    }
  }
  split. {
    intros i j Hi Hj Hij.
    unfold smaller_sym_gr_by_rem_biggest_at in Hij.
    cbn in Hij.
    rewrite map_map in Hij.
    rewrite (List_map_nth' empty_vect) in Hij; [ | now rewrite <- Hsgv ].
    rewrite (List_map_nth' empty_vect) in Hij; [ | now rewrite <- Hsgv ].
    injection Hij; clear Hij; intros Hij.
    destruct Hsg as (Hsg & Hinj & Hsurj).
    specialize List_length_filter_nth as H2.
    specialize (H2 (vector nat)).
    specialize (H2 empty_vect).
    specialize (H2 (vect_list sg)).
    specialize (H2 (λ v, vect_el 0 v s =? S n)).
    fold (select_in_list_vect (S n) (vect_list sg) s) in H2; cbn in H2.
    rewrite Hsgv in Hi, Hj.
    specialize (H2 _ Hi) as H3.
    specialize (H2 _ Hj) as H4.
    destruct H3 as (i' & Hil & Hin & Hii' & Hi').
    destruct H4 as (j' & Hjl & Hjn & Hjj' & Hj').
    rewrite Hii', Hjj' in Hij.
    do 2 rewrite fold_vect_el in Hij.
    specialize (Hinj i' j' Hil Hjl) as H3.
    apply Nat.eqb_eq in Hin, Hjn.
    assert (H' : vect_el empty_vect sg i' = vect_el empty_vect sg j'). {
      move Hin at bottom; move Hjn at bottom.
      rewrite fold_vect_el in Hin, Hjn.
      destruct (vect_el empty_vect sg i') as (la).
      destruct (vect_el empty_vect sg j') as (lb).
      cbn in Hin, Hjn.
      f_equal.
      cbn in Hij.
      unfold butn in Hij.
      rewrite (@List_split_at_pos _ s 0 la). 2: {
        apply List_nth_neq_default with (d := 0).
        now intros H; rewrite H in Hin.
      }
      rewrite (@List_split_at_pos _ s 0 lb). 2: {
        apply List_nth_neq_default with (d := 0).
        now intros H; rewrite H in Hjn.
      }
      rewrite Hin, Hjn.
      apply List_app_eq_app' in Hij. 2: {
        do 2 rewrite firstn_length.
        rewrite Nat.min_l. 2: {
          apply Nat.lt_le_incl.
          apply List_nth_neq_default with (d := 0).
          now intros H; rewrite H in Hin.
        }
        rewrite Nat.min_l. 2: {
          apply Nat.lt_le_incl.
          apply List_nth_neq_default with (d := 0).
          now intros H; rewrite H in Hjn.
        }
        easy.
      }
      destruct Hij as (Hij1, Hij2).
      now rewrite Hij1, Hij2.
    }
    specialize (H3 H').
    now rewrite Hi', Hj', H3.
  } {
    intros v Hv Hp.
    unfold smaller_sym_gr_by_rem_biggest_at; cbn.
    rewrite map_map.
    apply in_map_iff.
    unfold select_in_list_vect.
    destruct Hp as (Hp1, Hp2).
    rewrite Hv in Hp1, Hp2.
    destruct Hsg as (Hsg & Hinj & Hsurj).
    remember (vect_list v) as l.
    exists (mk_vect (firstn s l ++ S n :: skipn s l)); subst l.
    cbn - [ skipn ].
    split. {
      rewrite butn_app. 2: {
        rewrite firstn_length.
        symmetry; apply Nat.min_l.
        rewrite fold_vect_size, Hv; flia Hs.
      }
      cbn.
      rewrite firstn_skipn.
      now destruct v.
    }
    set (lv := firstn s (vect_list v) ++ S n :: skipn s (vect_list v)).
    specialize (Hsurj (mk_vect lv)) as H2.
    unfold lv in H2; cbn in H2.
    rewrite app_length in H2; cbn in H2.
    rewrite <- Nat.add_succ_comm in H2; cbn in H2.
    rewrite <- app_length in H2.
    rewrite firstn_skipn in H2.
    rewrite fold_vect_size, Hv in H2.
    specialize (H2 eq_refl).
    fold lv in H2.
    assert (H : is_permut_vect (mk_vect lv)). {
      unfold is_permut_vect, is_permut_fun.
      cbn - [ vect_el ].
      unfold lv.
      rewrite app_length; cbn.
      rewrite <- Nat.add_succ_comm; cbn.
      rewrite <- app_length.
      rewrite firstn_skipn.
      rewrite fold_vect_size, Hv.
      split. {
        intros i Hi.
        rewrite List_app_nth, firstn_length, fold_vect_size, Hv.
        rewrite if_ltb_lt_dec.
        destruct (lt_dec i (min s (S n))) as [Hisn| Hisn]. {
          rewrite List_nth_firstn; [ | flia Hisn ].
          rewrite fold_vect_el.
          transitivity (S n); [ | flia ].
          apply Hp1; flia Hisn.
        } {
          apply Nat.nlt_ge in Hisn.
          apply Nat.min_le in Hisn.
          destruct Hisn as [Hisn| Hisn]. {
            rewrite Nat.min_l; [ | flia Hisn Hi ].
            destruct (Nat.eq_dec i s) as [His| His]. {
              subst s; rewrite Nat.sub_diag; cbn; flia.
            }
            replace (i - s) with (S (i - S s)) by flia Hisn His; cbn.
            rewrite List_nth_skipn.
            replace (i - S s + s) with (i - 1) by flia Hisn His.
            rewrite fold_vect_el.
            specialize (Hp1 (i - 1)) as H1.
            assert (H : i - 1 < S n) by flia Hi.
            specialize (H1 H); clear H.
            flia H1.
          } {
            rewrite Nat.min_l; [ | flia Hs ].
            replace i with (S n) by flia Hi Hisn.
            destruct (Nat.eq_dec s (S n)) as [Hssn| Hssn]. {
              subst s; rewrite Nat.sub_diag; cbn; flia.
            }
            rewrite Nat.sub_succ_l; [ cbn | flia Hs Hssn ].
            rewrite List_nth_skipn.
            rewrite Nat.sub_add; [ | flia Hs Hssn ].
            rewrite fold_vect_el.
            specialize (Hp1 n (Nat.lt_succ_diag_r _)) as H1.
            flia H1.
          }
        }
      } {
        intros i j Hi Hj Hij.
        do 2 rewrite List_app_nth in Hij.
        rewrite firstn_length, fold_vect_size, Hv in Hij.
        rewrite Nat.min_l in Hij; [ | flia Hs ].
        do 2 rewrite if_ltb_lt_dec in Hij.
        destruct (lt_dec i s) as [His| His]. {
          rewrite List_nth_firstn in Hij; [ | easy ].
          destruct (lt_dec j s) as [Hjs| Hjs]. {
            rewrite List_nth_firstn in Hij; [ | easy ].
            do 2 rewrite fold_vect_el in Hij.
            apply Hp2; [ flia His Hs | flia Hjs Hs | easy ].
          }
          apply Nat.nlt_ge in Hjs.
          destruct (Nat.eq_dec j s) as [Hjes| Hjes]. {
            subst s.
            rewrite Nat.sub_diag in Hij; cbn in Hij.
            rewrite fold_vect_el in Hij.
            specialize (Hp1 i) as H1.
            assert (H : i < S n) by flia His Hs.
            specialize (H1 H); clear H.
            rewrite Hij in H1; flia H1.
          }
          replace (j - s) with (S (j - S s)) in Hij by flia Hjs Hjes.
          cbn in Hij.
          rewrite List_nth_skipn in Hij.
          replace (j - S s + s) with (j - 1) in Hij by flia Hjs Hjes.
          apply Hp2 in Hij; [ | flia His Hs | flia Hj ].
          flia His Hjs Hij Hjes.
        } {
          apply Nat.nlt_ge in His.
          destruct (lt_dec j s) as [Hjs| Hjs]. {
            rewrite List_nth_firstn in Hij; [ | easy ].
            rewrite fold_vect_el in Hij.
            destruct (Nat.eq_dec i s) as [Hies| Hies]. {
              subst s; rewrite Nat.sub_diag in Hij; cbn in Hij.
              specialize (Hp1 j) as H1.
              assert (H : j < S n) by flia Hjs Hs.
              specialize (H1 H); clear H.
              rewrite <- Hij in H1; flia H1.
            }
            replace (i - s) with (S (i - S s)) in Hij by flia His Hies.
            cbn in Hij.
            rewrite List_nth_skipn in Hij.
            replace (i - S s + s) with (i - 1) in Hij by flia His Hies.
            rewrite fold_vect_el in Hij.
            apply Hp2 in Hij; [ | flia Hi | flia Hjs Hs ].
            flia His Hjs Hij Hies.
          }
          apply Nat.nlt_ge in Hjs.
          destruct (Nat.eq_dec i s) as [Hies| Hies]. {
            subst i; rewrite Nat.sub_diag in Hij.
            remember (nth (j - s)) as f; cbn in Hij; subst f.
            destruct (Nat.eq_dec s j) as [Hiej| Hiej]; [ easy | ].
            replace (j - s) with (S (j - S s)) in Hij by flia Hjs Hiej.
            cbn in Hij.
            rewrite List_nth_skipn in Hij.
            replace (j - S s + s) with (j - 1) in Hij by flia Hjs Hiej.
            rewrite fold_vect_el in Hij.
            specialize (Hp1 (j - 1)) as H1.
            assert (H : j - 1 < S n) by flia Hj.
            specialize (H1 H); clear H.
            rewrite <- Hij in H1; flia H1.
          }
          destruct (Nat.eq_dec j s) as [Hjes| Hjes]. {
            subst j; rewrite Nat.sub_diag in Hij.
            remember (nth (i - s)) as f; cbn in Hij; subst f.
            destruct (Nat.eq_dec s i) as [Hiej| Hiej]; [ easy | ].
            replace (i - s) with (S (i - S s)) in Hij by flia His Hiej.
            cbn in Hij.
            rewrite List_nth_skipn in Hij.
            replace (i - S s + s) with (i - 1) in Hij by flia His Hiej.
            rewrite fold_vect_el in Hij.
            specialize (Hp1 (i - 1)) as H1.
            assert (H : i - 1 < S n) by flia Hi.
            specialize (H1 H); clear H.
            rewrite <- Hij in H1; flia H1.
          }
          replace (i - s) with (S (i - S s)) in Hij by flia His Hies.
          replace (j - s) with (S (j - S s)) in Hij by flia Hjs Hjes.
          cbn in Hij.
          do 2 rewrite List_nth_skipn in Hij.
          replace (i - S s + s) with (i - 1) in Hij by flia His Hies.
          replace (j - S s + s) with (j - 1) in Hij by flia Hjs Hjes.
          do 2 rewrite fold_vect_el in Hij.
          apply Hp2 in Hij; [ | flia Hi | flia Hj ].
          flia Hij His Hjs Hies Hjes.
        }
      }
    }
    apply filter_In.
    unfold lv; cbn.
    split. {
      apply Hsurj; [ cbn | easy ].
      rewrite app_length; cbn.
      rewrite firstn_length, skipn_length.
      rewrite fold_vect_size.
      rewrite min_l; [ | flia Hs Hv ].
      rewrite Hv; flia Hs.
    } {
      rewrite app_nth2; [ | rewrite firstn_length; flia ].
      rewrite firstn_length, fold_vect_size, Hv.
      rewrite Nat.min_l; [ | flia Hs ].
      rewrite Nat.sub_diag; cbn.
      apply Nat.eqb_refl.
    }
  }
}
assert
  (Hsv : ∀ s, s < S (S n) →
   vect_size (smaller_sym_gr_by_rem_biggest_at (S n) sg s) = (S n)!). {
  intros s Hs.
  now apply IHn, Hss.
}
assert
  (Hvs : ∀ v s,
   s < S (S n)
   → is_permut_vect v
   → vect_size v = S n
   → mk_vect (insert_at s (vect_list v) (S n)) ∈ vect_list sg). {
  intros * Hsn Hv Hs.
  remember (mk_vect (insert_at s (vect_list v) (S n))) as v' eqn:Hv'.
  remember (rank_of_permut_in_sym_gr sg v') as i eqn:Hi.
  assert (Hs' : vect_size v' = S (S n)). {
    rewrite Hv'; cbn.
    unfold insert_at.
    rewrite app_length; cbn.
    rewrite firstn_length, skipn_length.
    rewrite fold_vect_size, Hs.
    rewrite Nat.min_l; flia Hsn.
  }
  assert (Hv'p : is_permut_vect v'). {
    split. {
      intros j Hj; move j before i.
      rewrite Hs' in Hj |-*.
      rewrite Hv'.
      unfold insert_at; cbn.
      rewrite List_app_nth.
      rewrite firstn_length, fold_vect_size, Hs.
      rewrite Nat.min_l; [ | flia Hsn ].
      rewrite if_ltb_lt_dec.
      destruct Hv as (Hv1, Hv2).
      rewrite Hs in Hv1, Hv2.
      destruct (lt_dec j s) as [Hjs| Hjs]. {
        rewrite List_nth_firstn; [ | easy ].
        rewrite fold_vect_el.
        assert (H : j < S n) by flia Hjs Hsn.
        specialize (Hv1 j H) as H1.
        flia H1.
      } {
        apply Nat.nlt_ge in Hjs.
        destruct (Nat.eq_dec s j) as [Hsj| Hsj]. {
          subst j; rewrite Nat.sub_diag; cbn; flia.
        }
        replace (j - s) with (S (j - S s)) by flia Hjs Hsj; cbn.
        rewrite List_nth_skipn.
        replace (j - S s + s) with (j - 1) by flia Hjs Hsj.
        rewrite fold_vect_el.
        assert (H : j - 1 < S n) by flia Hj.
        specialize (Hv1 (j - 1) H) as H1.
        flia H1.
      }
    } {
      intros j k Hj Hk Hjk.
      rewrite Hs' in Hj, Hk.
      rewrite Hv' in Hjk; cbn in Hjk.
      unfold insert_at in Hjk.
      do 2 rewrite List_app_nth in Hjk.
      rewrite firstn_length, fold_vect_size, Hs in Hjk.
      rewrite Nat.min_l in Hjk; [ | flia Hsn ].
      do 2 rewrite if_ltb_lt_dec in Hjk.
      destruct Hv as (Hv1, Hv2).
      rewrite Hs in Hv1, Hv2.
      destruct (lt_dec j s) as [Hjs| Hjs]. {
        rewrite List_nth_firstn in Hjk; [ | easy ].
        rewrite fold_vect_el in Hjk.
        destruct (lt_dec k s) as [Hks| Hks]. {
          rewrite List_nth_firstn in Hjk; [ | easy ].
          rewrite fold_vect_el in Hjk.
          apply Hv2; [ flia Hjs Hsn | flia Hks Hsn | easy ].
        } {
          apply Nat.nlt_ge in Hks.
          destruct (Nat.eq_dec k s) as [Hsk| Hsk]. {
            subst k; rewrite Nat.sub_diag in Hjk; cbn in Hjk.
            assert (H : j < S n) by flia Hjs Hsn.
            specialize (Hv1 j H) as H1; clear H.
            rewrite Hjk in H1; flia H1.
          }
          replace (k - s) with (S (k - S s)) in Hjk by flia Hks Hsk; cbn in Hjk.
          rewrite List_nth_skipn in Hjk.
          replace (k - S s + s) with (k - 1) in Hjk by flia Hks Hsk.
          rewrite fold_vect_el in Hjk.
          apply Hv2 in Hjk; [ | flia Hjs Hsn | flia Hk ].
          flia Hjs Hks Hjk Hsk.
        }
      } {
        apply Nat.nlt_ge in Hjs.
        destruct (Nat.eq_dec j s) as [Hsj| Hsj]. {
          subst j; rewrite Nat.sub_diag in Hjk.
          remember (nth (k - s)) as f; cbn in Hjk; subst f.
          symmetry in Hjk.
          destruct (lt_dec k s) as [Hks| Hks]. {
            rewrite List_nth_firstn in Hjk; [ | easy ].
            rewrite fold_vect_el in Hjk.
            assert (H : k < S n) by flia Hks Hsn.
            specialize (Hv1 k H) as H1; clear H.
            rewrite Hjk in H1; flia H1.
          }
          apply Nat.nlt_ge in Hks.
          destruct (Nat.eq_dec s k) as [Hsk| Hsk]; [ easy | ].
          replace (k - s) with (S (k - S s)) in Hjk by flia Hks Hsk.
          cbn in Hjk.
          rewrite List_nth_skipn in Hjk.
          rewrite fold_vect_el in Hjk.
          replace (k - S s + s) with (k - 1) in Hjk by flia Hks Hsk.
          assert (H : k - 1 < S n) by flia Hk.
          specialize (Hv1 (k - 1) H) as H1.
          rewrite Hjk in H1; flia H1.
        }
        replace (j - s) with (S (j - S s)) in Hjk by flia Hjs Hsj.
        remember (nth (k - s)) as f; cbn in Hjk; subst f.
        rewrite List_nth_skipn in Hjk.
        replace (j - S s + s) with (j - 1) in Hjk by flia Hjs Hsj.
        rewrite fold_vect_el in Hjk.
        destruct (lt_dec k s) as [Hks| Hks]. {
          rewrite List_nth_firstn in Hjk; [ | easy ].
          rewrite fold_vect_el in Hjk.
          apply Hv2 in Hjk; [ | flia Hj | flia Hks Hsn ].
          flia Hjs Hks Hjk Hsj.
        } {
          apply Nat.nlt_ge in Hks.
          destruct (Nat.eq_dec k s) as [Hsk| Hsk]. {
            subst k; rewrite Nat.sub_diag in Hjk; cbn in Hjk.
            assert (H : j - 1 < S n) by flia Hj.
            specialize (Hv1 (j - 1) H) as H1; clear H.
            rewrite Hjk in H1; flia H1.
          }
          replace (k - s) with (S (k - S s)) in Hjk by flia Hks Hsk; cbn in Hjk.
          rewrite List_nth_skipn in Hjk.
          replace (k - S s + s) with (k - 1) in Hjk by flia Hks Hsk.
          rewrite fold_vect_el in Hjk.
          apply Hv2 in Hjk; [ | flia Hj | flia Hk ].
          flia Hjk Hjs Hsj Hks Hsk.
        }
      }
    }
  }
  specialize (vect_el_rank_of_permut_in_sym_gr Hsg Hv'p Hs') as H1.
  rewrite <- Hi in H1.
  rewrite <- H1.
  unfold vect_el.
  apply nth_In.
  rewrite fold_vect_size.
  rewrite Hi.
  now apply rank_of_permut_in_sym_gr_lt with (n := S (S n)).
}
...
Check sub_sg_rank_of_sg_rank.
...
Fixpoint Intersect A (la lb : list A) :=
  match la with
  | a :: la' => a ∈ lb ∨ Intersect la' lb
  | [] => False
  end.
Definition is_partition_of A (s : list A) (p : list (list A)) :=
  Permutation (concat p) s ∧
  ∀ i j d, Intersect (nth i p d) (nth j p d) → i = j.
Print remove.
Print List_find_nth.
set
  (f := λ n i,
   let s :=
     unsome 42
       (List_find_nth (Nat.eqb n)
          (vect_list (vect_el empty_vect sg i)))
   in
   s).
...
Compute (let n := 2 in map (λ i, f n i) (seq 0 (n + 1)!)).
...
assert
  (∀ sg', is_sym_gr_vect (S n) sg' →
   is_partition_of (map (vect_list (T := nat)) (vect_list sg))
     (map (λ i, (map (λ v, insert (vect_list v) i) sg') (seq 0 (S (S n)))))).
...
assert
  (Hk : ∀ v s1 s2, s1 < S (S n) → s2 < S (S n) →
   is_permut_vect v → vect_size v = S n →
   mk_vect (insert (vect_list v) s1) = mk_vect (insert (vect_list v) s2) →
   s1 = s2).
...

(* *)

Definition is_sym_gr_vect n (vv : vector (vector nat)) :=
  vect_size vv = n! ∧
  (∀ i, i < n! → vect_size (vect_el empty_vect vv i) = n) ∧
  is_sym_gr n (λ i, vect_el 0 (vect_el empty_vect vv i)).

Record sym_gr_vect n :=
  { sg_vect : vector (vector nat);
    sg_prop : is_sym_gr_vect n sg_vect }.

(* rank in canon symmetric group *)

Definition sub_permut (f : nat → nat) i :=
  f (S i) - Nat.b2n (f 0 <? f (S i)).

Fixpoint rank_of_permut_in_canon_sym_gr n (f : nat → nat) : nat :=
  match n with
  | 0 => 0
  | S n' => f 0 * n'! + rank_of_permut_in_canon_sym_gr n' (sub_permut f)
  end.

Theorem rank_of_permut_in_canon_sym_gr_eq_compat : ∀ n f g,
  (∀ i, i < n → f i = g i)
  → rank_of_permut_in_canon_sym_gr n f = rank_of_permut_in_canon_sym_gr n g.
Proof.
intros * Hfg.
revert f g Hfg.
induction n; intros; [ easy | cbn ].
rewrite Hfg; [ f_equal | flia ].
apply IHn.
intros i Hi.
unfold sub_permut.
rewrite Hfg; [ f_equal | flia Hi ].
rewrite Hfg; [ f_equal | flia Hi ].
Qed.

Definition rank_of_permut_in_canon_sym_gr_vect n (v : vector nat) : nat :=
  rank_of_permut_in_canon_sym_gr n (vect_el 0 v).

Theorem permut_elem_ub : ∀ n k i,
  k < n!
  → i < n
  → mk_canon_sym_gr n k i < n.
Proof.
intros * Hkn Hin.
revert k i Hkn Hin.
induction n; intros; [ easy | cbn ].
unfold sym_gr_fun.
destruct i. {
  rewrite Nat_fact_succ, Nat.mul_comm in Hkn.
  apply Nat.div_lt_upper_bound; [ | easy ].
  apply fact_neq_0.
}
apply Nat.succ_lt_mono in Hin.
remember (k / fact n <=? mk_canon_sym_gr n (k mod n!) i) as b eqn:Hb.
symmetry in Hb.
destruct b. {
  cbn; rewrite Nat.add_1_r.
  apply -> Nat.succ_lt_mono.
  apply IHn; [ | easy ].
  apply Nat.mod_upper_bound, fact_neq_0.
}
cbn; rewrite Nat.add_0_r.
apply Nat.leb_gt in Hb.
etransitivity; [ apply Hb | ].
rewrite Nat_fact_succ, Nat.mul_comm in Hkn.
apply Nat.div_lt_upper_bound; [ | easy ].
apply fact_neq_0.
Qed.

Fixpoint canon_sym_gr_inv n k (j : nat) :=
  match n with
  | 0 => 0
  | S n' =>
      if lt_dec j (k / n'!) then
        S (canon_sym_gr_inv n' (k mod n'!) j)
      else if lt_dec (k / n'!) j then
        S (canon_sym_gr_inv n' (k mod n'!) (j - 1))
      else 0
  end.

Theorem canon_sym_gr_inv_sym_gr : ∀ n k i,
  i < n
  → k < fact n
  → canon_sym_gr_inv n k (mk_canon_sym_gr n k i) = i.
Proof.
intros * Hi Hkn.
revert k i Hi Hkn.
induction n; intros; [ flia Hi | ].
destruct i. {
  clear Hi; cbn.
  remember (k / fact n) as p eqn:Hp.
  destruct (lt_dec p p) as [H| H]; [ flia H | easy ].
}
apply Nat.succ_lt_mono in Hi.
cbn.
remember (k / fact n) as p eqn:Hp.
remember (mk_canon_sym_gr n (k mod fact n) i) as q eqn:Hq.
move q before p.
remember (p <=? q) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply Nat.leb_le in Hb; cbn.
  destruct (lt_dec (q + 1) p) as [Hpq| Hqp]; [ flia Hb Hpq | ].
  apply Nat.nlt_ge in Hqp.
  destruct (lt_dec p (q + 1)) as [Hpq| Hpq]; [ | flia Hb Hpq ].
  clear Hpq Hqp.
  f_equal.
  rewrite Nat.add_sub.
  rewrite Hq.
  apply IHn; [ easy | ].
  apply Nat.mod_upper_bound, fact_neq_0.
} {
  apply Nat.leb_gt in Hb; cbn.
  rewrite Nat.add_0_r.
  destruct (lt_dec q p) as [H| H]; [ clear H | flia Hb H ].
  f_equal.
  rewrite Hq.
  apply IHn; [ easy | ].
  apply Nat.mod_upper_bound, fact_neq_0.
}
Qed.

Theorem mk_canon_sym_gr_inj1 : ∀ n k i j,
  k < fact n
  → i < n
  → j < n
  → mk_canon_sym_gr n k i = mk_canon_sym_gr n k j
  → i = j.
Proof.
intros * Hk Hi Hj Hij.
cbn in Hij.
assert (Hnz : n ≠ 0) by flia Hi.
rewrite <- canon_sym_gr_inv_sym_gr with (n := n) (k := k); [ | easy | easy ].
symmetry.
rewrite <- canon_sym_gr_inv_sym_gr with (n := n) (k := k); [ | easy | easy ].
now f_equal.
Qed.

Theorem mk_canon_sym_gr_inj2 : ∀ n i j,
  i < n!
  → j < n!
  → (∀ k, k < n → mk_canon_sym_gr n i k = mk_canon_sym_gr n j k)
  → i = j.
Proof.
intros * Hin Hjn Hij.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  apply Nat.lt_1_r in Hin, Hjn; congruence.
}
revert i j Hin Hjn Hij.
induction n; intros; [ easy | clear Hnz ].
destruct (Nat.eq_dec (i / n!) (j / n!)) as [Hijd| Hijd]. 2: {
  now specialize (Hij 0 (Nat.lt_0_succ _)).
}
destruct (Nat.eq_dec (i mod n!) (j mod n!)) as [Hijm| Hijm]. {
  specialize (Nat.div_mod i n! (fact_neq_0 _)) as Hi.
  specialize (Nat.div_mod j n! (fact_neq_0 _)) as Hj.
  congruence.
}
destruct n; [ now do 2 rewrite Nat.div_1_r in Hijd | ].
specialize (IHn (Nat.neq_succ_0 _)).
exfalso; apply Hijm; clear Hijm.
apply IHn. {
  apply Nat.mod_upper_bound, fact_neq_0.
} {
  apply Nat.mod_upper_bound, fact_neq_0.
}
intros k Hk.
cbn - [ fact ] in Hij |-*.
specialize (Hij (S k)) as H1.
assert (H : S k < S (S n)) by flia Hk.
specialize (H1 H); clear H.
cbn - [ fact ] in H1.
rewrite Hijd in H1.
unfold Nat.b2n in H1.
do 2 rewrite if_leb_le_dec in H1.
remember (sym_gr_fun n (mk_canon_sym_gr n) (i mod (S n)!) k) as x eqn:Hx.
remember (sym_gr_fun n (mk_canon_sym_gr n) (j mod (S n)!) k) as y eqn:Hy.
destruct (le_dec (j / (S n)!) x) as [Hjx| Hjx]. {
  destruct (le_dec (j / (S n)!) y) as [Hjy| Hjy]. {
    now apply Nat.add_cancel_r in H1.
  }
  apply Nat.nle_gt in Hjy.
  flia Hjx Hjy H1.
} {
  destruct (le_dec (j / (S n)!) y) as [Hjy| Hjy]. {
    apply Nat.nle_gt in Hjx.
    flia Hjx Hjy H1.
  }
  now apply Nat.add_cancel_r in H1.
}
Qed.

Theorem sym_gr_elem_is_permut : ∀ n k,
  k < n!
  → is_permut_fun (mk_canon_sym_gr n k) n.
Proof.
intros * Hkn.
split. {
  intros i Hi.
  now apply permut_elem_ub.
} {
  intros * Hi Hj Hij.
  now apply mk_canon_sym_gr_inj1 in Hij.
}
Qed.

Theorem mk_canon_is_permut_vect : ∀ n k,
  k < n!
  → is_permut_vect n (vect_vect_nat_el (mk_canon_sym_gr_vect n) k).
Proof.
intros * Hkn.
unfold mk_canon_sym_gr_vect; cbn - [ fact map seq ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite Nat.add_0_l.
unfold is_permut_vect, vect_el.
cbn - [ seq fact nth ].
split; [ now rewrite map_length, seq_length | ].
split. {
  intros i Hi.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ cbn | easy ].
  now apply permut_elem_ub.
} {
  intros * Hi Hj Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  now apply mk_canon_sym_gr_inj1 in Hij.
}
Qed.

(*
Definition canon_sym_gr n :=
  {| sg_vect := mk_canon_sym_gr_vect n;
     sg_prop := canon_sym_gr_prop n |}.
*)

(*
Compute map list_of_vect (list_of_vect (mk_canon_sym_gr 4)).
*)

(*
Compute (rank_of_permut_in_sym_gr (vect_el (mk_canon_sym_gr 4) 12)).
*)

Theorem sub_permut_elem_ub : ∀ n f i,
  is_permut_fun f (S n)
  → i < n
  → sub_permut f i < n.
Proof.
intros * (Hvn, Hn) Hin.
destruct n; [ easy | ].
cbn - [ "<?" ].
unfold sub_permut.
remember (f 0 <? f (S i)) as b eqn:Hb.
symmetry in Hb.
specialize (Hvn (S i)) as H1.
specialize (Hn 0 (S i) (Nat.lt_0_succ _)) as H2.
assert (H : S i < S (S n)) by flia Hin.
specialize (H1 H); specialize (H2 H); clear H.
destruct b; cbn; [ flia H1 | ].
rewrite Nat.sub_0_r.
apply Nat.ltb_ge in Hb.
specialize (Hvn 0 (Nat.lt_0_succ _)) as H3.
flia Hb H1 H2 H3.
Qed.

Theorem sub_mk_canon_sym_gr_inj1 : ∀ n f i j,
  is_permut_fun f (S n)
  → i < n
  → j < n
  → sub_permut f i = sub_permut f j
  → i = j.
Proof.
intros * (Hvn, Hn) Hin Hjn Hij.
destruct (Nat.eq_dec i j) as [H| H]; [ easy | exfalso ].
revert Hij; rename H into Hij.
destruct n; [ easy | ].
cbn - [ "<?" ].
unfold sub_permut.
remember (f 0 <? f (S i)) as bi eqn:Hbi.
remember (f 0 <? f (S j)) as bj eqn:Hbj.
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

Theorem rank_of_permut_upper_bound : ∀ n f,
  is_permut_fun f n
  → rank_of_permut_in_canon_sym_gr n f < n!.
Proof.
intros * (Hvn, Hn).
revert f Hvn Hn.
induction n; intros; cbn; [ flia | ].
rewrite Nat.add_comm.
apply Nat.add_lt_le_mono. {
  apply IHn. {
    intros i Hi.
    now apply sub_permut_elem_ub.
  } {
    intros i j Hi Hj.
    now apply sub_mk_canon_sym_gr_inj1 with (n := n).
  }
}
apply Nat.mul_le_mono_r.
specialize (Hvn 0 (Nat.lt_0_succ _)).
flia Hvn.
Qed.

Theorem permut_in_canon_sym_gr_of_its_rank : ∀ n f,
  is_permut_fun f n
  → ∀ i, i < n
  → mk_canon_sym_gr n (rank_of_permut_in_canon_sym_gr n f) i = f i.
Proof.
intros * (Hvn, Hn) * Hin.
revert i f Hin Hvn Hn.
induction n; intros; [ easy | cbn ].
destruct i. {
  cbn.
  rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
  rewrite <- Nat.add_0_r; f_equal.
  apply Nat.div_small.
  apply rank_of_permut_upper_bound.
  split. {
    intros i Hi.
    now apply sub_permut_elem_ub.
  } {
    intros i j Hi Hj.
    now apply sub_mk_canon_sym_gr_inj1 with (n := n).
  }
}
cbn.
remember (rank_of_permut_in_canon_sym_gr n (sub_permut f)) as k eqn:Hk.
symmetry in Hk.
rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
rewrite Nat_mod_add_l_mul_r; [ | apply fact_neq_0 ].
assert (Hkn : k < fact n). {
  rewrite <- Hk.
  apply rank_of_permut_upper_bound.
  split. {
    intros j Hj.
    now apply sub_permut_elem_ub.
  } {
    intros j m Hj Hm.
    now apply sub_mk_canon_sym_gr_inj1 with (n := n).
  }
}
rewrite Nat.div_small; [ | easy ].
rewrite Nat.mod_small; [ | easy ].
rewrite Nat.add_0_r.
unfold Nat.b2n.
rewrite if_leb_le_dec.
assert (H1 : ∀ i, i < n → sub_permut f i < n). {
  intros j Hj.
  now apply sub_permut_elem_ub.
}
assert
(H2 : ∀ i j : nat,
    i < n
    → j < n
    → sub_permut f i = sub_permut f j
    → i = j). {
  intros j m Hi Hm Him.
  now apply sub_mk_canon_sym_gr_inj1 with (n := n) in Him.
}
destruct (le_dec (f 0) (mk_canon_sym_gr n k i)) as [Hb| Hb]. {
  rewrite <- Hk in Hb |-*.
  unfold sub_permut in Hb.
  apply Nat.succ_lt_mono in Hin.
  rewrite IHn in Hb |-*; [ | easy | easy | easy | easy | easy | easy ].
  unfold sub_permut.
  unfold Nat.b2n in Hb |-*.
  rewrite if_ltb_lt_dec in Hb |-*.
  destruct (lt_dec (f 0) (f (S i))) as [Hb1| Hb1]. {
    apply Nat.sub_add; flia Hb1.
  } {
    exfalso.
    cbn in Hb.
    rewrite Nat.sub_0_r in Hb.
    apply Nat.nlt_ge in Hb1.
    apply Nat.le_antisymm in Hb; [ | easy ].
    symmetry in Hb.
    apply Nat.succ_lt_mono in Hin.
    now specialize (Hn 0 (S i) (Nat.lt_0_succ _) Hin Hb).
  }
} {
  apply Nat.nle_gt in Hb.
  rewrite Nat.add_0_r.
  rewrite <- Hk in Hb |-*.
  unfold sub_permut in Hb.
  apply Nat.succ_lt_mono in Hin.
  rewrite IHn; [ | easy | easy | easy ].
  unfold sub_permut, Nat.b2n.
  rewrite IHn in Hb; [ | easy | easy | easy ].
  unfold Nat.b2n in Hb.
  rewrite if_ltb_lt_dec in Hb |-*.
  destruct (lt_dec (f 0) (f (S i))) as [Hzi| Hzi]; [ | apply Nat.sub_0_r ].
  flia Hzi Hb.
}
Qed.

Theorem rank_of_permut_of_rank : ∀ n k,
  k < n!
  → rank_of_permut_in_canon_sym_gr n (mk_canon_sym_gr n k) = k.
Proof.
intros * Hkn.
revert k Hkn.
induction n; intros; [ now apply Nat.lt_1_r in Hkn | cbn ].
specialize (Nat.div_mod k (fact n) (fact_neq_0 _)) as H1.
rewrite Nat.mul_comm in H1.
replace (k / fact n * fact n) with (k - k mod fact n) by flia H1.
rewrite <- Nat.add_sub_swap; [ | apply Nat.mod_le, fact_neq_0 ].
apply Nat.add_sub_eq_r; f_equal.
clear H1.
rewrite <- (IHn (k mod fact n)) at 1. 2: {
  apply Nat.mod_upper_bound, fact_neq_0.
}
apply rank_of_permut_in_canon_sym_gr_eq_compat.
intros i Hi.
symmetry.
cbn.
apply Nat.add_sub_eq_r.
f_equal.
rewrite Nat.add_comm.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec (k / n!) (mk_canon_sym_gr n (k mod n!) i)) as [Hkc| Hkc]. {
  cbn.
  rewrite if_leb_le_dec.
  now destruct (le_dec (k / n!) (mk_canon_sym_gr n (k mod n!) i)).
}
cbn.
remember (mk_canon_sym_gr n _ i) as x eqn:Hx.
symmetry in Hx.
destruct x; [ easy | ].
rewrite if_leb_le_dec.
destruct (le_dec (k / n!) x) as [H| H]; [ | easy ].
flia Hkc H.
Qed.

Theorem canon_sym_gr_elem_injective : ∀ n i j,
  i < fact n
  → j < fact n
  → mk_canon_sym_gr n i = mk_canon_sym_gr n j
  → i = j.
Proof.
intros * Hi Hj Hij.
apply (f_equal (@rank_of_permut_in_canon_sym_gr n)) in Hij.
rewrite rank_of_permut_of_rank in Hij; [ | easy ].
rewrite rank_of_permut_of_rank in Hij; [ | easy ].
easy.
Qed.

Theorem canon_sym_gr_prop : ∀ n, is_sym_gr n (mk_canon_sym_gr n).
Proof.
intros.
split. {
  intros i j Hi Hj Hij.
  cbn in Hij.
  now apply canon_sym_gr_elem_injective in Hij.
} {
  intros i Hi.
  now apply sym_gr_elem_is_permut.
}
Qed.

Theorem rank_of_permut_injective : ∀ n f g,
  is_permut_fun f n
  → is_permut_fun g n
  → rank_of_permut_in_canon_sym_gr n f = rank_of_permut_in_canon_sym_gr n g
  → ∀ i, i < n → f i = g i.
Proof.
intros * Hσ₁ Hσ₂ Hσσ i Hi.
apply (f_equal (mk_canon_sym_gr n)) in Hσσ.
apply (f_equal (λ f, f i)) in Hσσ.
rewrite permut_in_canon_sym_gr_of_its_rank in Hσσ; [ | easy | easy ].
rewrite permut_in_canon_sym_gr_of_its_rank in Hσσ; [ | easy | easy ].
easy.
Qed.

Theorem canon_sym_gr_vect_prop : ∀ n,
  is_sym_gr_vect n (mk_canon_sym_gr_vect n).
Proof.
intros.
split. {
  now cbn; rewrite map_length, seq_length.
}
split. {
  intros i Hi; cbn.
  rewrite (List_map_nth' 0); [ cbn | now rewrite seq_length ].
  now rewrite map_length, seq_length.
}
split. {
  intros i j Hi Hj Hij.
  cbn in Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  apply (f_equal (@rank_of_permut_in_canon_sym_gr n)) in Hij.
  unfold vect_el in Hij.
  cbn in Hij.
  erewrite rank_of_permut_in_canon_sym_gr_eq_compat in Hij. 2: {
    intros k Hk.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    now rewrite seq_nth.
  }
  symmetry in Hij.
  erewrite rank_of_permut_in_canon_sym_gr_eq_compat in Hij. 2: {
    intros k Hk.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    now rewrite seq_nth.
  }
  symmetry in Hij.
  rewrite rank_of_permut_of_rank in Hij; [ | easy ].
  rewrite rank_of_permut_of_rank in Hij; [ | easy ].
  easy.
} {
  intros i Hi.
  eapply is_permut_eq_compat. {
    intros k Hk.
    symmetry.
    unfold vect_el; cbn.
    rewrite (List_map_nth' 0); [ cbn | now rewrite seq_length ].
    rewrite (List_map_nth' 0); [ cbn | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite seq_nth; [ | easy ].
    now do 2 rewrite Nat.add_0_l.
  }
  now apply sym_gr_elem_is_permut.
}
Qed.

(* signatures *)

Definition δ i j u v :=
  if i <? j then (rngl_of_nat v - rngl_of_nat u)%F else 1%F.

Definition ε_fun f n :=
  ((∏ (i = 1, n), ∏ (j = 1, n), δ i j (f (i - 1)%nat) (f (j - 1)%nat)) /
   (∏ (i = 1, n), ∏ (j = 1, n), δ i j i j))%F.

Definition ε n (p : vector nat) := ε_fun (vect_el 0 p) n.

(* signature of the k-th permutation of the symmetric group *)

Fixpoint ε_permut n k :=
  match n with
  | 0 => 1%F
  | S n' => (minus_one_pow (k / fact n') * ε_permut n' (k mod fact n'))%F
  end.

(* alternative version of signature of a permutation
   using only signs: ws = with sign *)

Definition sign_diff u v := if v <? u then 1%F else (-1)%F.
Definition abs_diff u v := if v <? u then u - v else v - u.

Definition ε_fun_ws f n :=
  (∏ (i = 1, n), ∏ (j = 1, n),
   if i <? j then sign_diff (f (j - 1)%nat) (f (i - 1)%nat) else 1)%F.

Definition ε_ws n (p : vector nat) := ε_fun_ws (vect_el 0 p) n.

(* equality of both definitions of ε: ε and ε_ws *)

Theorem rngl_product_product_if : ∀ b e f,
  (∏ (i = b, e), ∏ (j = b, e), if i <? j then f i j else 1)%F =
  (∏ (i = b, e), ∏ (j = i + 1, e), f i j)%F.
Proof.
intros.
apply rngl_product_eq_compat.
intros i Hi.
rewrite (rngl_product_split i); [ | flia Hi ].
rewrite all_1_rngl_product_1. 2: {
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [H| H]; [ flia Hj H | easy ].
}
rewrite rngl_mul_1_l.
apply rngl_product_eq_compat.
intros j Hj.
rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [H| H]; [ easy | flia Hj H ].
Qed.

Theorem rngl_of_nat_sub :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ i j,
  i < j
  → (rngl_of_nat j - rngl_of_nat i)%F = rngl_of_nat (j - i).
Proof.
intros Hom * Hij.
revert j Hij.
induction i; intros; cbn. {
  rewrite rngl_sub_0_r; f_equal; [ | easy ].
  now destruct j.
}
destruct j; [ easy | cbn ].
rewrite rngl_add_sub_simpl_l; [ | easy ].
apply IHi.
now apply Nat.succ_lt_mono in Hij.
Qed.

Theorem rngl_of_nat_add : ∀ a b,
  (rngl_of_nat a + rngl_of_nat b)%F = rngl_of_nat (a + b).
Proof.
intros.
induction a; [ apply rngl_add_0_l | ].
now cbn; rewrite <- rngl_add_assoc; f_equal.
Qed.

Theorem rngl_of_nat_mul :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b, (rngl_of_nat a * rngl_of_nat b)%F = rngl_of_nat (a * b).
Proof.
intros Hom *.
induction a; [ now apply rngl_mul_0_l | cbn ].
rewrite rngl_mul_add_distr_r.
rewrite rngl_mul_1_l.
rewrite IHa.
apply rngl_of_nat_add.
Qed.

Theorem rngl_product_rngl_of_nat :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ n, (∏ (i = 1, n), rngl_of_nat i)%F = rngl_of_nat (fact n).
Proof.
intros Hom *.
induction n. {
  rewrite rngl_product_empty; [ | flia ].
  symmetry; apply rngl_add_0_r.
}
rewrite rngl_product_split_last; [ | flia ].
rewrite rngl_product_succ_succ.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat_sub_succ_1.
}
rewrite IHn.
rewrite Nat_fact_succ.
rewrite Nat.mul_comm.
now apply rngl_of_nat_mul.
Qed.

Theorem rngl_sub_is_mul_sign_abs :
  rngl_has_opp = true →
  ∀ a b,
  (rngl_of_nat a - rngl_of_nat b)%F =
  (sign_diff a b * rngl_of_nat (abs_diff a b))%F.
Proof.
intros Hop *.
unfold sign_diff, abs_diff.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec b a) as [Hba| Hba]. {
  rewrite rngl_mul_1_l.
  apply rngl_of_nat_sub; [ now left | easy ].
} {
  apply Nat.nlt_ge in Hba.
  destruct (Nat.eq_dec a b) as [Hab| Hab]. {
    subst b.
    rewrite rngl_sub_diag, Nat.sub_diag; cbn; [ | now left ].
    symmetry.
    now apply rngl_mul_0_r; left.
  }
  rewrite <- rngl_opp_sub_distr; [ | easy ].
  rewrite rngl_of_nat_sub; [ | now left | flia Hba Hab ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
}
Qed.

Theorem rngl_product_change_var : ∀ A b e f g (h : _ → A),
  (∀ i, b ≤ i ≤ e → g (h i) = i)
  → (∏ (i = b, e), f i = ∏ (i ∈ map h (seq b (S e - b))), f (g i))%F.
Proof.
intros * Hgh.
unfold iter_seq, iter_list.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros i c Hi.
f_equal; f_equal; symmetry.
apply Hgh.
apply in_seq in Hi.
flia Hi.
Qed.

Theorem fun_find_prop : ∀ f n i,
  (∀ i j, i < n → j < n → f i = f j → i = j)
  → i < n
  → permut_fun_inv_loop f n (f i) = i.
Proof.
intros * Hp2 Hin.
revert i Hin.
induction n; intros; [ easy | cbn ].
destruct (Nat.eq_dec (f n) (f i)) as [Hfni| Hfni]. {
  apply Hp2; [ flia | easy | easy ].
}
rename Hin into Hisn.
assert (Hin : i < n). {
  destruct (Nat.eq_dec n i) as [H| H]; [ now subst n | ].
  flia Hisn H.
}
clear Hisn.
apply IHn; [ | easy ].
intros j k Hj Hk Hjk.
apply Hp2; [ flia Hj | flia Hk | easy ].
Qed.

Theorem permut_fun_inv_loop_fun : ∀ f n,
  is_permut_fun f n
  → ∀ i, i < n
  → permut_fun_inv_loop f n (f i) = i.
Proof.
intros * (Hp1, Hp2) * Hin.
apply fun_find_prop; [ | easy ].
intros j k Hj Hk Hjk.
now apply Hp2.
Qed.

Theorem permut_fun_inv_loop_fun' : ∀ f n,
  (∀ i j, i < n → j < n → f i = f j → i = j)
  → ∀ i, i < n
  → permut_fun_inv_loop f n (f i) = i.
Proof.
intros * Hp2 * Hin.
apply fun_find_prop; [ | easy ].
intros j k Hj Hk Hjk.
now apply Hp2.
Qed.

Definition permut_fun_inv_loop' f n i :=
  let '(x, x') :=
    pigeonhole_fun (S n) (λ j, if Nat.eq_dec j n then i else f j)
  in
  if Nat.eq_dec x n then x' else x.

Theorem fun_find_permut_fun_inv_loop' : ∀ f n,
  is_permut_fun f n
  → ∀ i, i < n
  → permut_fun_inv_loop f n i = permut_fun_inv_loop' f n i.
Proof.
intros * (Hfub, Hinj) * Hin.
unfold permut_fun_inv_loop'.
remember (pigeonhole_fun _ _) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (j, j').
unfold pigeonhole_fun in Hxx.
remember (find_dup _ _) as fd eqn:Hfd.
symmetry in Hfd.
destruct fd as [(x, x')| ]. {
  injection Hxx; clear Hxx; intros; subst x x'.
  apply find_dup_some in Hfd.
  destruct Hfd as (Hij & la1 & la2 & la3 & Hfd).
  destruct (Nat.eq_dec j n) as [Hjn| Hjn]. {
    subst j.
    destruct (Nat.eq_dec j' n) as [Hin'| Hin']. {
      subst j'; clear Hij.
      exfalso.
      revert Hfd.
      apply List_seq_nothing_after_last.
    }
    subst i.
    apply fun_find_prop; [ easy | ].
    assert (H : j' ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right; right.
      now apply in_app_iff; right; left.
    }
    apply in_seq in H.
    flia Hin' H.
  }
  destruct (Nat.eq_dec j' n) as [Hjn'| Hjn']. {
    subst j' i.
    apply fun_find_prop; [ easy | ].
    assert (H : j ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right.
      now left.
    }
    apply in_seq in H.
    flia Hjn H.
  }
  apply Hinj in Hij; cycle 1. {
    assert (H : j ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right.
      now left.
    }
    apply in_seq in H.
    flia Hjn H.
  } {
    assert (H : j' ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right; right.
      now apply in_app_iff; right; left.
    }
    apply in_seq in H.
    flia Hjn' H.
  }
  subst j'.
  exfalso.
  specialize (seq_NoDup (S n) 0) as H1.
  rewrite Hfd in H1.
  apply NoDup_app_remove_l in H1.
  rewrite app_comm_cons in H1.
  specialize (proj1 (NoDup_app_iff _ _) H1) as (_ & _ & H2).
  specialize (H2 j (or_introl eq_refl)).
  apply H2.
  now left.
}
injection Hxx; clear Hxx; intros; subst j j'.
apply find_dup_none in Hfd.
replace (if Nat.eq_dec _ _ then _ else _) with 0. 2: {
  now destruct (Nat.eq_dec 0 n).
}
specialize (proj1 (NoDup_map_iff 0 _ _) Hfd) as H1.
rewrite seq_length in H1.
assert
  (H2 : ∀ j k,
   j < S n
   → k < S n
   → (if Nat.eq_dec j n then i else f j) = (if Nat.eq_dec k n then i else f k)
   → j = k). {
  intros j k Hj Hk.
  specialize (H1 j k Hj Hk).
  now do 2 rewrite seq_nth in H1.
}
clear H1; rename H2 into H1.
apply not_NoDup_map_f_seq with (b := n) in Hfd; [ easy | flia | ].
intros j Hj.
destruct (Nat.eq_dec j n) as [Hjn| Hjn]; [ easy | ].
apply Hfub.
flia Hj Hjn.
Qed.

(* the proof that "vect_el σ (vect_el (permut_vect_inv σ) i) = i"
   is proven by the pigeonhole principle *)

Theorem pigeonhole' : ∀ f n,
  (∀ i, i < n → f i < n)
  → (∀ i j, i < n → j < n → f i = f j → i = j)
  → ∀ i, i < n
  → ∀ j, j = permut_fun_inv_loop' f n i
  → j < n ∧ f j = i.
Proof.
intros * Hp1 Hp2 * Hin * Hj.
subst j.
unfold permut_fun_inv_loop'.
remember (pigeonhole_fun _ _) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (x, x').
specialize pigeonhole as H1.
specialize (H1 (S n) n).
specialize (H1 (λ j, if Nat.eq_dec j n then i else f j)).
specialize (H1 (Nat.lt_succ_diag_r n)).
cbn in H1.
assert (H : ∀ j, j < S n → (if Nat.eq_dec j n then i else f j) < n). {
  intros j Hj.
  destruct (Nat.eq_dec j n) as [Hjn| Hjn]; [ now subst j | ].
  apply Hp1; flia Hj Hjn.
}
specialize (H1 H x x' Hxx); clear H.
destruct H1 as (Hxn & Hx'n & Hxx' & H1).
destruct (Nat.eq_dec x n) as [H2| H2]. {
  subst x.
  destruct (Nat.eq_dec x' n) as [H2| H2]; [ now subst x' | ].
  split; [ flia Hx'n H2 | easy ].
} {
  destruct (Nat.eq_dec x' n) as [H3| H3]. {
    split; [ flia Hxn H2 | easy ].
  }
  apply Hp2 in H1; [ easy | flia Hxn H2 | flia Hx'n H3 ].
}
Qed.

Theorem fun_permut_fun_inv_loop : ∀ f n,
  is_permut_fun f n
  → ∀ i, i < n
  → f (permut_fun_inv_loop f n i) = i.
Proof.
intros * (Hp1, Hp2) * Hin.
rewrite fun_find_permut_fun_inv_loop'; [ | easy | easy ].
apply (proj2 (pigeonhole' f Hp1 Hp2 Hin eq_refl)).
Qed.

Theorem permut_fun_inv_loop_is_permut : ∀ n f,
  is_permut_fun f n
  → is_permut_fun (permut_fun_inv_loop f n) n.
Proof.
intros * Hp.
destruct Hp as (Hp1, Hp2).
split. {
  intros i Hin; cbn.
  rewrite fun_find_permut_fun_inv_loop'; [ | easy | easy ].
  unfold permut_fun_inv_loop'.
  remember (pigeonhole_fun _ _) as xx eqn:Hxx.
  symmetry in Hxx; destruct xx as (x, x').
  destruct (Nat.eq_dec x n) as [Hxn| Hxn]. {
    subst x.
    unfold pigeonhole_fun in Hxx.
    remember (find_dup _ _) as fd eqn:Hfd; symmetry in Hfd.
    destruct fd as [(x, n')| ]. {
      injection Hxx; clear Hxx; intros; subst x x'.
      apply find_dup_some in Hfd.
      destruct Hfd as (Hij & la1 & la2 & la3 & Hfd).
      exfalso.
      revert Hfd.
      apply List_seq_nothing_after_last.
    }
    now injection Hxx; clear Hxx; intros; subst n x'.
  } {
    unfold pigeonhole_fun in Hxx.
    remember (find_dup _ _) as fd eqn:Hfd; symmetry in Hfd.
    destruct fd as [(n'', n')| ]. {
      injection Hxx; clear Hxx; intros; subst x x'.
      apply find_dup_some in Hfd.
      destruct Hfd as (Hij & la1 & la2 & la3 & Hfd).
      destruct (Nat.eq_dec n'' n) as [Hn''n| Hn''n]; [ now subst n'' | ].
      destruct (Nat.eq_dec n' n) as [Hn'n| Hn'n]. {
        subst n'.
        now apply List_sorted_in_seq in Hfd.
      }
      assert (H : n' ∈ seq 0 (S n)). {
        rewrite Hfd.
        apply in_app_iff; right; right.
        now apply in_app_iff; right; left.
      }
      apply in_seq in H.
      apply List_sorted_in_seq in Hfd.
      apply (Nat.lt_le_trans _ n'); [ easy | flia H ].
    }
    injection Hxx; clear Hxx; intros; subst x x'.
    flia Hin.
  }
}
intros i j Hi Hj Hij.
cbn in Hij.
rewrite fun_find_permut_fun_inv_loop' in Hij; [ | easy | easy ].
rewrite fun_find_permut_fun_inv_loop' in Hij; [ | easy | easy ].
unfold permut_fun_inv_loop' in Hij.
remember (pigeonhole_fun _ _) as xx eqn:Hxx in Hij.
remember (pigeonhole_fun _ _) as yy eqn:Hyy in Hij.
symmetry in Hxx; destruct xx as (x, x').
symmetry in Hyy; destruct yy as (y, y').
move y before x; move y' before x'.
unfold pigeonhole_fun in Hxx, Hyy.
remember (find_dup _ _) as fdi eqn:Hfdi in Hxx.
remember (find_dup _ _) as fdj eqn:Hfdj in Hyy.
symmetry in Hfdi, Hfdj.
move fdj before fdi.
move Hfdj before Hfdi.
destruct fdi as [(x1, x2)| ]. {
  injection Hxx; clear Hxx; intros; subst x1 x2.
  apply find_dup_some in Hfdi.
  destruct Hfdi as (Hij1 & la1 & la2 & la3 & Hfdi).
  destruct (Nat.eq_dec x n) as [Hxn| Hxn]. {
    subst x.
    now apply List_seq_nothing_after_last in Hfdi.
  }
  destruct fdj as [(x1, x2)| ]. {
    injection Hyy; clear Hyy; intros; subst x1 x2.
    apply find_dup_some in Hfdj.
    destruct Hfdj as (Hij2 & lb1 & lb2 & lb3 & Hfdj).
    destruct (Nat.eq_dec y n) as [Hyn| Hyn]; subst y. {
      now apply List_seq_nothing_after_last in Hfdj.
    }
    clear Hyn.
    destruct (Nat.eq_dec x' n) as [Hx'n| Hx'n]. {
      subst x'.
      destruct (Nat.eq_dec y' n) as [Hy'n| Hy'n]; [ congruence | ].
      apply Hp2 in Hij2; cycle 1. {
        assert (H : x ∈ seq 0 (S n)). {
          rewrite Hfdi.
          now apply in_app_iff; right; left.
        }
        apply in_seq in H; cbn in H; flia Hxn H.
      } {
        assert (H : y' ∈ seq 0 (S n)). {
          rewrite Hfdj.
          apply in_app_iff; right; right.
          now apply in_app_iff; right; left.
        }
        apply in_seq in H; cbn in H; flia Hy'n H.
      }
      subst y'.
      apply List_sorted_in_seq in Hfdj.
      now apply Nat.lt_irrefl in Hfdj.
    }
    apply Hp2 in Hij1; cycle 1. {
      assert (H : x ∈ seq 0 (S n)). {
        rewrite Hfdi.
        now apply in_app_iff; right; left.
      }
      apply in_seq in H; cbn in H; flia Hxn H.
    } {
      assert (H : x' ∈ seq 0 (S n)). {
        rewrite Hfdi.
        apply in_app_iff; right; right.
        now apply in_app_iff; right; left.
      }
      apply in_seq in H; cbn in H; flia Hx'n H.
    }
    subst x'.
    apply List_sorted_in_seq in Hfdi.
    now apply Nat.lt_irrefl in Hfdi.
  }
  apply find_dup_none in Hfdj.
  exfalso; revert Hfdj.
  apply not_NoDup_map_f_seq with (b := n); [ flia | ].
  intros k Hk.
  destruct (Nat.eq_dec k n) as [Hkn| Hkn]; [ easy | ].
  apply Hp1; flia Hk Hkn.
}
apply find_dup_none in Hfdi.
exfalso; revert Hfdi.
apply not_NoDup_map_f_seq with (b := n); [ flia | ].
intros k Hk.
destruct (Nat.eq_dec k n) as [Hkn| Hkn]; [ easy | ].
apply Hp1; flia Hk Hkn.
Qed.

Theorem permut_fun_without_last : ∀ n i (a : _ → nat),
  is_permut_fun a (S n)
  → i = permut_fun_inv_loop a (S n) n
  → ∃ b,
     is_permut_fun b n ∧
     map a (seq 0 i ++ seq (S i) (n - i)) = map b (seq 0 n).
Proof.
intros * Hp Hi.
exists (λ j, if lt_dec j i then a j else a (j + 1)).
split. 2: {
  destruct n. {
    cbn in Hi; cbn.
    destruct (Nat.eq_dec (a 0) 0) as [Haz| Haz]; [ now subst i | exfalso ].
    apply Haz.
    destruct Hp as (Hp1, Hp2).
    enough (H : a 0 < 1) by flia H.
    apply Hp1; flia.
  }
  destruct (Nat.eq_dec (a (S n)) (S n)) as [Han| Han]. {
    remember (S n) as sn; cbn in Hi; subst sn.
    rewrite Han in Hi.
    destruct (Nat.eq_dec (S n) (S n)) as [H| H]; [ clear H | easy ].
    subst i.
    rewrite Nat.sub_diag; cbn.
    f_equal.
    rewrite app_nil_r.
    apply map_ext_in.
    intros i Hi.
    apply in_seq in Hi.
    now destruct (lt_dec i (S n)).
  }
  destruct (Nat.eq_dec i (S n)) as [Hsni| Hsni]. {
    rewrite Hsni, Nat.sub_diag.
    cbn; f_equal.
    rewrite app_nil_r.
    apply map_ext_in.
    intros j Hj.
    destruct (lt_dec j (S n)) as [Hjsn| Hjsn]; [ easy | ].
    exfalso; apply Hjsn; clear Hjsn.
    now apply in_seq in Hj.
  }
  symmetry.
  rewrite (List_seq_cut i). 2: {
    apply in_seq.
    split; [ flia | cbn ].
    enough (H : i < S (S n)) by flia Hsni H.
    rewrite Hi.
    apply permut_ub; [ | flia ].
    now apply permut_fun_inv_loop_is_permut.
  }
  symmetry; cbn - [ "-" ].
  rewrite Nat.sub_0_r, Nat.sub_succ.
  rewrite Nat.sub_succ_l. 2: {
    assert (H : i < S (S n)). {
      rewrite Hi.
      apply permut_ub; [ | flia ].
      now apply permut_fun_inv_loop_is_permut.
    }
    flia Hsni H.
  }
  do 2 rewrite map_app.
  f_equal. {
    apply map_ext_in_iff.
    intros j Hj.
    destruct (lt_dec j i) as [Hji| Hji]; [ easy | ].
    now apply in_seq in Hj.
  }
  cbn.
  destruct (lt_dec i i) as [H| H]; [ now apply lt_irrefl in H | clear H ].
  rewrite Nat.add_1_r; f_equal.
  rewrite <- seq_shift.
  rewrite map_map.
  apply map_ext_in_iff.
  intros j Hj.
  rewrite Nat.add_1_r.
  destruct (lt_dec j i) as [Hji| Hji]; [ | easy ].
  apply in_seq in Hj.
  flia Hj Hji.
}
split. {
  intros j Hj.
  assert (Hin : a i = n). {
    rewrite Hi.
    apply fun_permut_fun_inv_loop; [ easy | flia ].
  }
  destruct (lt_dec j i) as [Hji| Hji]. {
    destruct (Nat.eq_dec (a j) n) as [Hajn| Hajn]. {
      rewrite <- Hajn in Hin.
      apply Hp in Hin; [ flia Hji Hin | | flia Hj ].
      rewrite Hi.
      apply permut_ub; [ | flia ].
      now apply permut_fun_inv_loop_is_permut.
    }
    enough (H : a j < S n) by flia Hajn H.
    apply Hp; flia Hj.
  }
  apply Nat.nlt_ge in Hji.
  destruct Hp as (Hp1, Hp2).
  apply Nat.succ_lt_mono in Hj.
  specialize (Hp1 _ Hj) as H1.
  rewrite Nat.add_1_r.
  destruct (Nat.eq_dec (a (S j)) n) as [Hajn| Hajn]. {
    rewrite <- Hajn in Hin.
    apply Hp2 in Hin; [ flia Hin Hji | flia Hj Hji | easy ].
  }
  flia H1 Hajn.
}
intros j k Hj Hk Hjk.
destruct (lt_dec j i) as [Hji| Hji]. {
  destruct (lt_dec k i) as [Hki| Hki]. {
    apply Hp in Hjk; [ easy | flia Hj | flia Hk ].
  }
  apply Nat.nlt_ge in Hki.
  apply Hp in Hjk; [ flia Hji Hki Hjk | flia Hj | flia Hk ].
}
destruct (lt_dec k i) as [Hki| Hki]. {
  apply Hp in Hjk; [ | flia Hj | flia Hk ].
  apply Nat.nlt_ge in Hji.
  flia Hji Hki Hjk.
}
apply Hp in Hjk; [ flia Hjk | flia Hj | flia Hk ].
Qed.

Theorem permut_fun_Permutation : ∀ f n,
  is_permut_fun f n
  → Permutation (map f (seq 0 n)) (seq 0 n).
Proof.
intros a n * Hp.
symmetry.
revert a Hp.
induction n; intros; [ easy | ].
rewrite seq_S at 1.
remember (permut_fun_inv_loop a (S n) n) as i eqn:Hi.
remember (seq 0 n) as s eqn:Hs.
rewrite (List_seq_cut i); subst s. 2: {
  subst i.
  apply in_seq.
  split; [ flia | ].
  apply permut_ub; [ | flia ].
  now apply permut_fun_inv_loop_is_permut.
}
rewrite Nat.sub_0_r; cbn.
rewrite map_app; cbn.
rewrite Hi at 2.
rewrite fun_permut_fun_inv_loop; [ | easy | flia ].
apply Permutation_elt.
rewrite app_nil_r.
rewrite <- map_app.
destruct (permut_fun_without_last Hp Hi) as (g & Hpg & Hg).
rewrite Hg.
now apply IHn.
Qed.

Theorem rngl_product_change_list :
  rngl_is_comm = true →
  ∀ A (la lb : list A) f,
  Permutation la lb
  → (∏ (i ∈ la), f i = ∏ (i ∈ lb), f i)%F.
Proof.
intros Hic * P.
induction P; [ easy | | | ]. {
  rewrite rngl_product_list_cons; [ | easy ].
  rewrite rngl_product_list_cons; [ | easy ].
  now rewrite IHP.
} {
  do 4 (rewrite rngl_product_list_cons; [ | easy ]).
  do 2 rewrite rngl_mul_assoc.
  f_equal.
  now apply rngl_mul_comm.
} {
  etransitivity; [ apply IHP1 | apply IHP2 ].
}
Qed.

Theorem rngl_product_product_div_eq_1 :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  rngl_has_dec_eq = true →
  ∀ n f g,
  (∀ i j, i < n → j < n → g i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), (f i j / g i j)))%F = 1%F
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), f i j))%F =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), g i j))%F.
Proof.
intros Hom Hic Hid Hin H10 Hde * Hg Hs.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
remember (∏ (i ∈ _), _)%F as a eqn:Ha in |-*.
remember (∏ (i ∈ _), _)%F as b eqn:Hb in |-*.
destruct (rngl_eq_dec Hde b 0%F) as [Hbz| Hbz]. {
  rewrite Hbz in Hb |-*; clear Hbz; subst a; symmetry in Hb.
  apply rngl_product_list_integral in Hb; [ | easy | easy | easy ].
  destruct Hb as (i & His & Hb).
  apply rngl_product_list_integral in Hb; [ | easy | easy | easy ].
  destruct Hb as (j & Hjs & Hb).
  move j before i.
  exfalso; revert Hb.
  apply in_seq in His.
  apply in_seq in Hjs.
  now apply Hg.
}
apply rngl_mul_cancel_r with (c := (b⁻¹)%F); [ now left | | ]. {
  intros Hbiz.
  apply (f_equal (rngl_mul b)) in Hbiz.
  rewrite fold_rngl_div in Hbiz; [ | easy ].
  rewrite rngl_mul_inv_r in Hbiz; [ | now left | easy ].
  rewrite rngl_mul_0_r in Hbiz; [ | easy ].
  now apply rngl_1_neq_0 in Hbiz.
}
remember (_ * _)%F as c.
rewrite fold_rngl_div; [ | easy ].
rewrite rngl_mul_inv_r; [ | now left | easy ].
subst c b.
rewrite rngl_inv_product_list; [ | easy | easy | easy | easy | ]. 2: {
  intros i Hi H1.
  apply rngl_product_list_integral in H1; [ | easy | easy | easy ].
  destruct H1 as (j & Hjs & Hijz).
  exfalso.
  revert Hijz.
  apply in_seq in Hi.
  apply in_seq in Hjs.
  now apply Hg.
}
subst a.
erewrite rngl_product_list_permut with (l1 := rev _); [ | easy | ]. 2: {
  symmetry; apply Permutation_rev.
}
rewrite <- rngl_product_list_mul_distr; [ | easy ].
erewrite rngl_product_list_eq_compat. 2 :{
  intros i Hi.
  rewrite rngl_inv_product_list; [ | easy | easy | easy | easy | ]. 2: {
    intros j Hj.
    apply in_seq in Hi.
    apply in_seq in Hj.
    now apply Hg.
  }
  erewrite rngl_product_list_permut with (l1 := rev _); [ | easy | ]. 2: {
    symmetry; apply Permutation_rev.
  }
  rewrite <- rngl_product_list_mul_distr; [ | easy ].
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    rewrite fold_rngl_div; [ | easy ].
    easy.
  }
  easy.
}
easy.
Qed.

Theorem rngl_product_product_by_swap :
  rngl_is_comm = true →
  ∀ n f,
  (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n), f i j)%F =
  ((∏ (i ∈ seq 0 n), f i i) *
   (∏ (i ∈ seq 0 (n - 1)), ∏ (j = i + 1, n - 1), (f i j * f j i)))%F.
Proof.
intros Hic *.
induction n. {
  unfold iter_seq, iter_list; cbn.
  now rewrite rngl_mul_1_l.
}
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; unfold iter_list; cbn.
  now rewrite rngl_mul_1_l, rngl_mul_1_r.
}
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n; unfold iter_seq, iter_list; cbn.
  do 5 rewrite rngl_mul_1_l.
  repeat rewrite <- rngl_mul_assoc.
  f_equal; symmetry.
  rewrite rngl_mul_comm; [ | easy ].
  now rewrite rngl_mul_assoc.
}
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite seq_S.
  rewrite iter_list_app.
  unfold iter_list at 1; cbn.
  easy.
}
cbn - [ seq ].
rewrite Nat.sub_0_r.
rewrite rngl_product_list_mul_distr; [ | easy ].
rewrite seq_S.
rewrite iter_list_app.
unfold iter_list at 1; cbn.
rewrite IHn.
rewrite iter_list_app; cbn.
rewrite iter_list_app; cbn.
unfold iter_list at 4 6; cbn.
do 3 rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_mul_comm Hic (f n n)).
do 2 rewrite rngl_mul_assoc.
f_equal.
symmetry.
rewrite rngl_product_seq_product; [ | easy ].
cbn - [ seq ].
rewrite rngl_product_split_last; [ | flia Hnz ].
rewrite rngl_product_shift; [ | flia Hnz Hn1 ].
rewrite Nat.sub_add; [ | flia Hnz ].
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz Hn1 ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1), Nat.add_sub.
  rewrite Nat.add_1_r.
  rewrite Nat.sub_succ.
  apply in_seq in Hi.
  replace (n - i) with (S (n - i - 1)) by flia Hnz Hn1 Hi.
  rewrite seq_S.
  replace (S i + (n - i - 1)) with n by flia Hnz Hn1 Hi.
  unfold iter_list.
  rewrite fold_left_app.
  cbn - [ seq ].
  rewrite fold_iter_list.
  easy.
}
cbn - [ seq "-" ].
symmetry.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite Nat.add_1_r.
  rewrite Nat.sub_succ.
  now rewrite Nat_sub_sub_swap.
}
cbn - [ seq "-" ].
rewrite rngl_product_list_mul_distr; [ | easy ].
do 2 rewrite <- rngl_mul_assoc.
f_equal.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.sub_diag.
unfold iter_list at 4; cbn.
rewrite rngl_mul_1_l.
rewrite rngl_product_seq_product; [ | easy ].
cbn - [ seq ].
rewrite rngl_product_split_last; [ | flia Hnz ].
rewrite rngl_product_shift; [ | flia Hnz Hn1 ].
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz Hn1 ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1), Nat.add_sub.
  easy.
}
rewrite rngl_product_list_mul_distr; [ | easy ].
symmetry.
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
do 3 rewrite <- rngl_mul_assoc.
f_equal.
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
f_equal.
symmetry.
rewrite rngl_product_seq_product; [ | easy ].
cbn - [ seq ].
rewrite rngl_product_split_last; [ | flia Hnz ].
rewrite rngl_product_shift; [ | flia Hnz Hn1 ].
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz Hn1 ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1), Nat.add_sub.
  easy.
}
easy.
Qed.

Theorem permut_swap_mul_cancel : ∀ n σ f,
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  is_permut_fun σ n
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → ∀ i j, i < n → j < n →
    (((if σ i <? σ j then f i j else 1) / (if i <? j then f i j else 1)) *
     ((if σ j <? σ i then f j i else 1) / (if j <? i then f j i else 1)))%F =
    1%F.
Proof.
intros * Hic Hin H10 Hp Hfij Hfijnz * Hlin Hljn.
do 4 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ i) (σ j)) as [H1| H1]. {
  destruct (lt_dec (σ j) (σ i)) as [H| H]; [ flia H1 H | clear H ].
  destruct (lt_dec i j) as [H3| H3]. {
    destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
    rewrite Hfij.
    rewrite rngl_mul_inv_r; [ | now left | ]. 2: {
      apply Hfijnz; [ easy | easy | flia H3 ].
    }
    rewrite rngl_mul_1_l.
    apply rngl_mul_inv_r; [ now left | now apply rngl_1_neq_0 ].
  }
  destruct (lt_dec j i) as [H4| H4]. {
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | now left | easy ].
    rewrite rngl_div_1_l; [ | easy ].
    rewrite fold_rngl_div; [ | easy ].
    apply rngl_mul_inv_r; [ now left | ].
    apply Hfijnz; [ easy | easy | flia H4 ].
  }
  exfalso.
  apply Nat.nlt_ge in H3.
  apply Nat.nlt_ge in H4.
  apply Nat.le_antisymm in H3; [ | easy ].
  subst j; flia H1.
}
destruct (lt_dec (σ j) (σ i)) as [H2| H2]. {
  destruct (lt_dec i j) as [H3| H3]. {
    destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | now left | easy ].
    rewrite rngl_div_1_l; [ | easy ].
    rewrite rngl_mul_comm; [ | easy ].
    rewrite fold_rngl_div; [ | easy ].
    apply rngl_mul_inv_r; [ now left | ].
    apply Hfijnz; [ easy | easy | flia H3 ].
  }
  destruct (lt_dec j i) as [H4| H4]. {
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | now left | easy ].
    rewrite rngl_mul_1_l.
    apply rngl_mul_inv_r; [ now left | ].
    apply Hfijnz; [ easy | easy | flia H4 ].
  }
  exfalso.
  apply Nat.nlt_ge in H3.
  apply Nat.nlt_ge in H4.
  apply Nat.le_antisymm in H3; [ | easy ].
  subst j; flia H2.
}
apply Nat.nlt_ge in H1.
apply Nat.nlt_ge in H2.
apply Nat.le_antisymm in H1; [ | easy ].
destruct (lt_dec i j) as [H3| H3]. {
  destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
  apply Hp in H1; [ flia H1 H3 | easy | easy ].
}
destruct (lt_dec j i) as [H4| H4]. {
  apply Hp in H1; [ flia H1 H4 | easy | easy ].
}
rewrite rngl_div_1_r; [ | now left | easy ].
apply rngl_mul_1_l.
Qed.

Theorem product_product_if_permut_div :
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_has_inv = true →
  ∀ n σ f,
  is_permut_fun σ n
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n),
      ((if σ i <? σ j then f i j else 1) / (if i <? j then f i j else 1)))%F =
     1%F.
Proof.
intros Hic H10 Hin * Hp Hfij Hfijnz.
rewrite rngl_product_product_by_swap; [ | easy ].
rewrite all_1_rngl_product_list_1; [ | easy | ]. 2: {
  intros i Hi.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec _ _) as [H| H]; [ flia H | clear H ].
  destruct (lt_dec _ _) as [H| H]; [ flia H | clear H ].
  apply rngl_div_1_r; [ now left | easy ].
}
rewrite rngl_mul_1_l.
apply all_1_rngl_product_list_1; [ easy | ].
intros i Hi.
apply all_1_rngl_product_list_1; [ easy | ].
intros j Hj.
apply in_seq in Hi.
apply in_seq in Hj.
apply (@permut_swap_mul_cancel n); try easy; [ flia Hi | flia Hj ].
Qed.

Theorem product_product_if_permut :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  rngl_has_dec_eq = true →
  ∀ n σ f,
  is_permut_fun σ n
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), if σ i <? σ j then f i j else 1))%F =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), if i <? j then f i j else 1))%F.
Proof.
intros Hom Hic Hid Hin H10 Hed * Hp Hfij Hfijnz.
apply rngl_product_product_div_eq_1; try easy. {
  intros i j Hi Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | now apply rngl_1_neq_0 ].
  apply Hfijnz; [ easy | easy | flia Hij ].
}
now apply product_product_if_permut_div.
Qed.

Theorem ε_ws_ε_fun :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ σ n,
  is_permut_fun σ n
  → ε_fun σ n = ε_fun_ws σ n.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hp.
unfold ε_fun, ε_fun_ws, δ.
rewrite rngl_product_product_if.
rewrite rngl_product_product_if.
rewrite rngl_product_product_if.
rewrite <- rngl_product_div_distr; try easy; [ | now left | ]. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_of_nat_sub; [ | now left | flia Hj ].
    easy.
  }
  cbn.
  destruct (Nat.eq_dec i n) as [Hein| Hein]. {
    subst i.
    rewrite rngl_product_empty; [ now apply rngl_1_neq_0 | flia ].
  }
  rewrite rngl_product_shift; [ | flia Hi Hein ].
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    replace (i + 1 + j - i) with (S j) by flia.
    easy.
  }
  cbn - [ rngl_of_nat ].
  erewrite <- rngl_product_succ_succ.
  replace (S (n - (i + 1))) with (n - i) by flia Hi Hein.
  rewrite rngl_product_rngl_of_nat; [ | now left ].
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  now apply fact_neq_0 in H.
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite <- rngl_product_div_distr; try easy; [ now left | ].
  intros j Hj.
  intros H.
  apply rngl_sub_move_0_r in H; [ | easy ].
  apply rngl_of_nat_inj in H; [ | now left | easy ].
  flia Hj H.
}
cbn.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_sub_is_mul_sign_abs; [ | easy ].
    rewrite rngl_sub_is_mul_sign_abs; [ | easy ].
    replace (sign_diff j i) with 1%F. 2: {
      unfold sign_diff.
      rewrite if_ltb_lt_dec.
      destruct (lt_dec i j) as [H| H]; [ easy | flia Hj H ].
    }
    rewrite rngl_mul_1_l.
    replace (rngl_of_nat (abs_diff j i)) with (rngl_of_nat (j - i)). 2: {
      unfold abs_diff.
      rewrite if_ltb_lt_dec.
      destruct (lt_dec i j) as [H| H]; [ easy | flia Hj H ].
    }
    easy.
  }
  easy.
}
cbn.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    unfold rngl_div.
    rewrite Hin.
    rewrite <- rngl_mul_assoc.
    easy.
  }
  cbn.
  rewrite rngl_product_mul_distr; [ | easy ].
  easy.
}
cbn.
rewrite rngl_product_mul_distr; [ | easy ].
rewrite <- rngl_mul_1_r; f_equal.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite fold_rngl_div; [ | easy ].
    easy.
  }
  cbn.
  rewrite rngl_product_div_distr; try easy; [ now left | ].
  intros j Hj.
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
cbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  rewrite rngl_product_empty; [ easy | flia ].
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  replace n with (S (n - 1)) at 1 2 by flia Hnz.
  rewrite Nat.add_1_r at 1 2.
  rewrite rngl_product_succ_succ.
  rewrite rngl_product_succ_succ.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat_sub_succ_1.
  }
  cbn - [ "-" ].
  easy.
}
cbn - [ "-" ].
erewrite rngl_product_shift; [ | flia Hnz ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1).
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite Nat.add_sub.
    easy.
  }
  remember (iter_seq _ _ _ _) as x.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat.add_1_r, Nat.sub_succ.
  }
  subst x.
  easy.
}
cbn.
rewrite rngl_product_div_distr; try easy; [ | now left | ]. 2: {
  intros i Hi H.
  apply (rngl_product_integral (or_introl Hop) Hit H10) in H.
  destruct H as (j & Hj & Hji).
  apply eq_rngl_of_nat_0 in Hji; [ | easy ].
  flia Hj Hji.
}
apply eq_rngl_div_1; [ now left | | ]. {
  intros H.
  apply (rngl_product_integral (or_introl Hop) Hit H10) in H.
  destruct H as (i & Hi & H).
  apply (rngl_product_integral (or_introl Hop) Hit H10) in H.
  destruct H as (j & Hj & H).
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
rewrite <- rngl_product_product_if; symmetry.
rewrite <- rngl_product_product_if; symmetry.
(* changt de var *)
rewrite rngl_product_change_var with (g := permut_fun_inv_loop σ n) (h := σ). 2: {
  intros i Hi.
  destruct Hp as (Hp1, Hp2).
  rewrite fun_find_prop; [ easy | easy | flia Hi Hnz ].
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_var with (g := permut_fun_inv_loop σ n) (h := σ). 2: {
    intros j Hj.
    destruct Hp as (Hp1, Hp2).
    rewrite fun_find_prop; [ easy | easy | flia Hj Hnz ].
  }
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    apply in_map_iff in Hj.
    destruct Hj as (k & Hk & Hsk).
    apply in_seq in Hsk.
    rewrite fun_permut_fun_inv_loop; [ | easy | ]. 2: {
      destruct Hp as (Hp1, Hp2).
      rewrite <- Hk.
      apply Hp1.
      flia Hsk Hi Hnz.
    }
    apply in_map_iff in Hi.
    destruct Hi as (l & Hl & Hsl).
    apply in_seq in Hsl.
    rewrite fun_permut_fun_inv_loop; [ | easy | ]. 2: {
      destruct Hp as (Hp1, Hp2).
      rewrite <- Hl.
      apply Hp1.
      easy.
    }
    easy.
  }
  cbn - [ "-" "<?" ].
  easy.
}
cbn - [ "-" "<?" ].
rewrite Nat.sub_0_r.
rewrite rngl_product_list_permut with (l2 := seq 0 n); [ | easy | ]. 2: {
  now apply permut_fun_Permutation.
}
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_list with (lb := seq 0 n); [ | easy | ]. 2: {
    now apply permut_fun_Permutation.
  }
  easy.
}
cbn - [ "<?" ].
rewrite product_product_if_permut; try easy; cycle 1. {
  now left.
} {
  now apply permut_fun_inv_loop_is_permut.
} {
  intros.
  unfold abs_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]. {
    destruct (lt_dec j i) as [Hji| Hji]; [ flia Hij Hji | easy ].
  } {
    destruct (lt_dec j i) as [Hji| Hji]; [ easy | ].
    now replace i with j by flia Hij Hji.
  }
} {
  intros * Hi Hj Hij H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  unfold abs_diff in H.
  rewrite if_ltb_lt_dec in H.
  destruct (lt_dec i j) as [Hlij| Hlij]; flia Hij Hlij H.
}
rewrite rngl_product_seq_product; [ | easy ].
rewrite Nat.add_0_l.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_seq_product; [ | easy ].
  rewrite Nat.add_0_l.
  easy.
}
cbn - [ "<?" ].
unfold abs_diff.
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
do 3 rewrite if_ltb_lt_dec.
now destruct (lt_dec i j).
Qed.

Theorem ε_ws_ε :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n (p : vector nat),
  is_permut_vect n p
  → ε n p = ε_ws n p.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hp.
apply ε_ws_ε_fun; try easy.
now destruct Hp as (Hp1, Hp2).
Qed.

Definition permut_fun_swap (p q : nat) (σ : nat → nat) :=
  λ i, σ (transposition p q i).

(*
Definition permut_swap {n} (p q : nat) (σ : vector nat) :=
  mk_vect n (permut_fun_swap p q (vect_el σ)).
*)

Theorem permut_swap_fun_is_permut : ∀ p q σ n,
  p < n
  → q < n
  → is_permut_fun σ n
  → is_permut_fun (permut_fun_swap p q σ) n.
Proof.
intros * Hp Hq Hσ.
unfold permut_fun_swap.
split. {
  intros i Hi.
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i p) as [Hip| Hip]; [ now apply Hσ | ].
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]; [ now apply Hσ | ].
  now apply Hσ.
} {
  intros i j Hi Hj Hs.
  unfold transposition in Hs.
  do 4 rewrite if_eqb_eq_dec in Hs.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
      apply Hσ in Hs; [ congruence | easy | easy ].
    } {
      apply Hσ in Hs; [ congruence | easy | easy ].
    }
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
      apply Hσ in Hs; [ congruence | easy | easy ].
    }
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
      apply Hσ in Hs; [ congruence | easy | easy ].
    }
    apply Hσ in Hs; [ congruence | easy | easy ].
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
    apply Hσ in Hs; [ congruence | easy | easy ].
  }
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
    apply Hσ in Hs; [ congruence | easy | easy ].
  }
  apply Hσ in Hs; [ congruence | easy | easy ].
}
Qed.

Theorem transposition_is_permut : ∀ p q n,
  p < n → q < n → is_permut_fun (transposition p q) n.
Proof.
intros * Hp Hq.
split. {
  intros i Hi.
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i p) as [Hip| Hip]; [ easy | ].
  now destruct (Nat.eq_dec i q).
} {
  intros i j Hi Hj Hs.
  unfold transposition in Hs.
  do 4 rewrite if_eqb_eq_dec in Hs.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; congruence.
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; congruence.
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ easy | ].
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ easy | ].
  easy.
}
Qed.

(*
Theorem transposition_is_permut_vect : ∀ n p q,
  p < n
  → q < n
  → is_permut_vect (mk_vect (transposition p q)).
Proof.
intros.
now apply transposition_is_permut.
Qed.
*)

Theorem is_permut_map : ∀ f n,
  is_permut_fun f n
  → is_permut_fun (λ i, nth i (map f (seq 0 n)) 0) n.
Proof.
intros * Hf.
destruct Hf as (Hf, Hff).
split. {
  intros i Hi.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  now apply Hf.
} {
  intros i j Hi Hj Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  now apply Hff.
}
Qed.

Theorem transposition_signature_lt :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n p q,
  p < q
  → q < n
  → ε n (mk_vect (map (transposition p q) (seq 0 n))) = (-1)%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hpq Hq.
rewrite ε_ws_ε; try easy. 2: {
  split; cbn; [ now rewrite map_length, seq_length | ].
  unfold vect_el; cbn.
  apply is_permut_map.
  apply transposition_is_permut; [ | easy ].
  now transitivity q.
}
unfold ε_ws; cbn.
unfold ε_fun_ws.
cbn - [ "<?" ].
unfold sign_diff.
rewrite rngl_product_shift; [ | flia Hq ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hq ].
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite (Nat.add_comm 1 j), Nat.add_sub.
    rewrite (Nat.add_comm 1 i), Nat.add_sub.
    rewrite Nat_ltb_mono_r.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi Hq ].
    rewrite seq_nth; [ | flia Hi Hq ].
    rewrite Nat.add_0_l.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj Hq ].
    rewrite seq_nth; [ | flia Hj Hq ].
    rewrite Nat.add_0_l.
    easy.
  }
  easy.
}
cbn - [ "<?" ].
rewrite (rngl_product_split3 p); [ | flia Hpq Hq ].
cbn - [ "<?" ].
assert (Hp : p < n) by now transitivity q.
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  apply all_1_rngl_product_1.
  intros j Hj.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) j) as [Hij| Hij]; [ | easy ].
  destruct (lt_dec (transposition p q (i - 1)) (transposition p q j))
    as [Htij| Htij]; [ easy | ].
  exfalso; apply Htij; clear Htij.
  rewrite transposition_out; [ | flia Hi | flia Hpq Hi ].
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ flia Hpq Hi | ].
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ flia Hpq Hi | easy ].
}
rewrite rngl_mul_1_l.
rewrite transposition_1.
rewrite (rngl_product_split3 p); [ | flia Hpq Hq ].
rewrite if_ltb_lt_dec.
destruct (lt_dec p p) as [H| H]; [ flia H | clear H ].
rewrite rngl_mul_1_r.
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec p (i - 1)) as [H| H]; [ flia Hi H | easy ].
}
rewrite rngl_mul_1_l.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec p i) as [H| H]; [ clear H | flia Hi H ].
  easy.
}
cbn - [ "<?" ].
rewrite <- rngl_product_mul_distr; [ | easy ].
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite transposition_2.
rewrite if_ltb_lt_dec.
destruct (lt_dec q p) as [H| H]; [ flia Hpq H | clear H ].
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite if_ltb_lt_dec.
destruct (lt_dec q q) as [H| H]; [ flia H | clear H ].
rewrite rngl_mul_1_r.
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec q (i - 1)) as [H| H]; [ flia Hi H | easy ].
}
rewrite rngl_mul_1_l.
do 2 rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
rewrite rngl_mul_assoc.
rewrite <- rngl_product_mul_distr; [ | easy ].
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec q i) as [H| H]; [ clear H | flia Hi H ].
  rewrite rngl_mul_assoc.
  rewrite transposition_out; [ | flia Hpq Hi | flia Hi ].
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec p i) as [H| H]; [ clear H | flia Hpq Hi H ].
  rewrite rngl_mul_1_l.
  destruct (lt_dec q i) as [H| H]; [ clear H | flia Hi H ].
  rewrite rngl_mul_1_l.
  apply all_1_rngl_product_1.
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
  rewrite transposition_out; [ | flia Hpq Hi Hij | flia Hi Hij ].
  rewrite if_ltb_lt_dec.
  now destruct (lt_dec i j).
}
rewrite rngl_mul_1_l.
rewrite all_1_rngl_product_1; [ apply rngl_mul_1_l | ].
intros i Hi.
rewrite transposition_out; [ | flia Hi | flia Hi ].
rewrite if_ltb_lt_dec.
destruct (lt_dec q (i - 1)) as [H| H]; [ flia Hi H | clear H ].
rewrite (rngl_product_split3 p); [ | flia Hp ].
rewrite transposition_1.
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) p) as [H| H]; [ flia Hi H | clear H ].
rewrite rngl_mul_1_r.
rewrite all_1_rngl_product_1. 2: {
  intros j Hj.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) (j - 1)) as [H| H]; [ flia Hi Hj H | easy ].
}
rewrite rngl_mul_1_l.
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) q) as [H| H]; [ clear H | flia Hi H ].
rewrite transposition_2.
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) p) as [H| H]; [ flia Hi H | clear H ].
rewrite rngl_mul_mul_swap; [ | easy ].
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
rewrite rngl_sqr_opp_1; [ | easy ].
rewrite rngl_mul_1_r.
rewrite (all_1_rngl_product_1 (q + 1)). 2: {
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) j) as [H| H]; [ clear H | flia Hi Hj H ].
  rewrite transposition_out; [ | flia Hpq Hj | flia Hj ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) j) as [H| H]; [ easy | flia Hi Hj H ].
}
rewrite rngl_mul_1_r.
apply all_1_rngl_product_1.
intros j Hj.
rewrite transposition_out; [ | flia Hj | flia Hj ].
do 2 rewrite if_ltb_lt_dec.
now destruct (lt_dec (i - 1) (j - 1)).
Qed.

Theorem transposition_signature :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n p q,
  p ≠ q
  → p < n
  → q < n
  → ε n (mk_vect (map (transposition p q) (seq 0 n))) = (-1)%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hpq Hp Hq.
destruct (lt_dec p q) as [Hpq'| Hpq']. {
  now apply transposition_signature_lt.
}
apply Nat.nlt_ge in Hpq'.
assert (H : q < p) by flia Hpq Hpq'.
rewrite <- transposition_signature_lt with (p := q) (q := p) (n := n); try easy.
f_equal; f_equal.
apply map_ext_in.
intros i Hi.
apply transposition_comm.
Qed.

(* ε (σ₁ ° σ₂) = ε σ₁ * ε σ₂ *)

Theorem signature_comp_fun_expand_1 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_fun g n
  → (∏ (i = 1, n),
        (∏ (j = 1, n), δ i j (f (g (i - 1)%nat)) (f (g (j - 1)%nat))) /
      ∏ (i = 1, n), (∏ (j = 1, n), δ i j (g (i - 1)%nat) (g (j - 1)%nat)))%F =
    (∏ (i = 1, n), (∏ (j = 1, n), δ i j (f (i - 1)%nat) (f (j - 1)%nat)) /
      ∏ (i = 1, n), (∏ (j = 1, n), δ i j i j))%F
  → ε_fun (comp f g) n = (ε_fun f n * ε_fun g n)%F.
Proof.
intros Hop Hin H10 Hit Hch * Hp2 Hs.
unfold ε_fun, comp; cbn.
rewrite <- Hs; symmetry.
apply rngl_div_mul_div; [ easy | ].
intros Hij.
apply rngl_product_integral in Hij; [ | now left | easy | easy ].
destruct Hij as (i & Hi & Hij).
apply rngl_product_integral in Hij; [ | now left | easy | easy ].
destruct Hij as (j & Hj & Hij).
unfold δ in Hij.
rewrite if_ltb_lt_dec in Hij.
destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 ].
apply rngl_sub_move_0_r in Hij; [ | easy ].
apply rngl_of_nat_inj in Hij; [ | now left | easy ].
destruct Hp2 as (Hp21, Hp22).
apply Hp22 in Hij; [ flia Hi Hj Hlij Hij | flia Hj | flia Hi ].
Qed.

Theorem signature_comp_fun_expand_2_1 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_fun g n
  → (∏ (i = 1, n),
      (∏ (j = 1, n), δ i j (f (g (i - 1)%nat)) (f (g (j - 1)%nat))) /
     ∏ (i = 1, n), (∏ (j = 1, n), δ i j (g (i - 1)%nat) (g (j - 1)%nat)))%F =
    (∏ (i = 1, n),
      (∏ (j = 1, n),
       (if i <? j then
         (rngl_of_nat (f (g (j - 1)%nat)) - rngl_of_nat (f (g (i - 1)%nat))) /
         (rngl_of_nat (g (j - 1)%nat) - rngl_of_nat (g (i - 1)%nat))
       else 1)))%F.
Proof.
intros Hop Hin Hic H10 Hit Hch * Hp2.
unfold rngl_div; rewrite Hin.
rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
  intros i Hi Hij.
  apply rngl_product_integral in Hij; [ | now left | easy | easy ].
  destruct Hij as (j & Hj & Hij).
  unfold δ in Hij.
  rewrite if_ltb_lt_dec in Hij.
  destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
  apply rngl_sub_move_0_r in Hij; [ | easy ].
  apply rngl_of_nat_inj in Hij; [ | now left | easy ].
  apply Hp2 in Hij; [ flia Hi Hj Hlij Hij | flia Hj | flia Hi ].
}
erewrite <- rngl_product_mul_distr; [ | easy ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
    intros j Hj Hij.
    unfold δ in Hij.
    rewrite if_ltb_lt_dec in Hij.
    destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
    apply rngl_sub_move_0_r in Hij; [ | easy ].
    apply rngl_of_nat_inj in Hij; [ | now left | easy ].
    apply Hp2 in Hij; [ flia Hi Hj Hlij Hij | flia Hj | flia Hi ].
  }
  erewrite <- rngl_product_mul_distr; [ | easy ].
  easy.
}
cbn - [ "<?" ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    move j before i.
    unfold δ.
    rewrite rngl_inv_if_then_else_distr.
    rewrite rngl_mul_if_then_else_distr.
    rewrite fold_rngl_div; [ | easy ].
    rewrite rngl_inv_1; [ | easy | easy ].
    rewrite rngl_mul_1_l.
    easy.
  }
  easy.
}
cbn - [ "<?" ].
unfold rngl_div; rewrite Hin.
easy.
Qed.

Theorem signature_comp_fun_expand_2_2 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f,
  (∏ (i = 1, n), (∏ (j = 1, n), δ i j (f (i - 1)%nat) (f (j - 1)%nat)) /
   ∏ (i = 1, n), (∏ (j = 1, n), δ i j i j))%F =
  (∏ (i = 1, n),
   (∏ (j = 1, n),
    (if i <? j then
      (rngl_of_nat (f (j - 1)%nat) - rngl_of_nat (f (i - 1)%nat)) /
      rngl_of_nat (j - i)
     else 1)))%F.
Proof.
intros Hop Hin Hic H10 Hit Hch *.
unfold rngl_div; rewrite Hin.
rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
  intros i Hi Hij.
  apply rngl_product_integral in Hij; [ | now left | easy | easy ].
  destruct Hij as (j & Hj & Hij).
  unfold δ in Hij.
  rewrite if_ltb_lt_dec in Hij.
  destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
  apply rngl_sub_move_0_r in Hij; [ | easy ].
  apply rngl_of_nat_inj in Hij; [ | now left | easy ].
  flia Hlij Hij.
}
erewrite <- rngl_product_mul_distr; [ | easy ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
    intros j Hj Hij.
    unfold δ in Hij.
    rewrite if_ltb_lt_dec in Hij.
    destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
    apply rngl_sub_move_0_r in Hij; [ | easy ].
    apply rngl_of_nat_inj in Hij; [ | now left | easy ].
    flia Hlij Hij.
  }
  erewrite <- rngl_product_mul_distr; [ | easy ].
  easy.
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    move j before i.
    unfold δ.
    rewrite rngl_inv_if_then_else_distr.
    rewrite rngl_mul_if_then_else_distr.
    rewrite fold_rngl_div; [ | easy ].
    rewrite rngl_inv_1; [ | easy | easy ].
    rewrite rngl_mul_1_l.
    easy.
  }
  easy.
}
unfold rngl_div; rewrite Hin.
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
f_equal; f_equal.
apply rngl_of_nat_sub; [ now left | easy ].
Qed.

Theorem signature_comp_fun_changement_of_variable :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_fun f n
  → is_permut_fun g n
  → (∏ (i = 1, n),
     (∏ (j = 1, n),
      (if i <? j then
         (rngl_of_nat (f (g (j - 1)%nat)) - rngl_of_nat (f (g (i - 1)%nat))) /
         (rngl_of_nat (g (j - 1)%nat) - rngl_of_nat (g (i - 1)%nat))
       else 1)))%F =
    (∏ (i = 1, n),
     (∏ (j = 1, n),
      (if i <? j then
         (rngl_of_nat (f (j - 1)%nat) - rngl_of_nat (f (i - 1)%nat)) /
         rngl_of_nat (j - i)
       else 1)))%F.
Proof.
intros Hop Hin Hic Hde H10 Hit Hch * Hp1 Hp2.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
rewrite rngl_product_shift; [ | flia Hnz ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    now rewrite (Nat.add_comm 1), Nat.add_sub.
  }
  easy.
}
cbn - [ "<?" ].
rewrite rngl_product_change_var with (g := permut_fun_inv_loop g n) (h := g). 2: {
  intros i Hi.
  rewrite fun_find_prop; [ easy | apply Hp2 | flia Hi Hnz ].
}
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1, Nat.sub_0_r.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hnz ].
  rewrite rngl_product_change_var with
      (g := permut_fun_inv_loop g n) (h := g). 2: {
    intros j Hj.
    rewrite fun_find_prop; [ easy | apply Hp2 | flia Hj Hnz ].
  }
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1, Nat.sub_0_r.
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    rewrite (Nat.add_comm _ 1).
    rewrite Nat_ltb_mono_l.
    rewrite fun_permut_fun_inv_loop; [ | apply Hp2 | ]. 2: {
      apply in_map_iff in Hi.
      destruct Hi as (k & Hk & Hkn).
      apply in_seq in Hkn.
      rewrite <- Hk.
      now apply Hp2.
    }
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite fun_permut_fun_inv_loop; [ | apply Hp2 | ]. 2: {
      apply in_map_iff in Hj.
      destruct Hj as (k & Hk & Hkn).
      apply in_seq in Hkn.
      rewrite <- Hk.
      now apply Hp2.
    }
    easy.
  }
  easy.
}
cbn - [ "<?" ].
erewrite rngl_product_list_eq_compat. 2: {
  intros j Hj.
  erewrite rngl_product_change_list; [ | easy | ]. 2: {
    now apply permut_fun_Permutation.
  }
  easy.
}
cbn - [ "<?" ].
erewrite rngl_product_change_list; [ | easy | ]. 2: {
  now apply permut_fun_Permutation.
}
symmetry.
rewrite rngl_product_shift; [ | flia Hnz ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite Nat_ltb_mono_l.
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite Nat.add_comm, Nat.add_sub.
    do 2 rewrite Nat.add_1_r.
    cbn - [ "<?" ].
    easy.
  }
  easy.
}
unfold iter_seq.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1, Nat.sub_0_r.
symmetry.
rewrite product_product_if_permut; try easy. {
  apply rngl_product_list_eq_compat.
  intros i Hi.
  apply rngl_product_list_eq_compat.
  intros j Hj.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
  f_equal.
  apply rngl_of_nat_sub; [ now left | easy ].
} {
  now left.
} {
  now apply permut_fun_inv_loop_is_permut.
} {
  intros i j.
  destruct (Nat.eq_dec i j) as [Hij| Hij]; [ now subst j | ].
  rewrite <- rngl_opp_sub_distr; [ | easy ].
  unfold rngl_div.
  rewrite Hin.
  rewrite rngl_mul_opp_l; [ | easy ].
  rewrite <- rngl_mul_opp_r; [ | easy ].
  f_equal.
  rewrite rngl_opp_inv; [ | easy | easy | easy | ]. 2: {
    intros H.
    apply rngl_sub_move_0_r in H; [ | easy ].
    apply Hij; symmetry.
    apply rngl_of_nat_inj in H; [ easy | now left | easy ].
  }
  now rewrite rngl_opp_sub_distr.
} {
  intros * Hi Hj Hij.
  unfold rngl_div.
  rewrite Hin.
  intros H.
  apply rngl_integral in H; [ | now left | now rewrite Hit ].
  destruct H as [H| H]. {
    apply rngl_sub_move_0_r in H; [ | easy ].
    apply rngl_of_nat_inj in H; [ | now left | easy ].
    apply Hij; symmetry.
    now apply Hp1 in H.
  } {
    revert H.
    apply rngl_inv_neq_0; [ now left | easy | easy | ].
    intros H.
    apply rngl_sub_move_0_r in H; [ | easy ].
    apply rngl_of_nat_inj in H; [ | now left | easy ].
    now apply Hij; symmetry.
  }
}
Qed.

Theorem signature_comp_fun :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_fun f n
  → is_permut_fun g n
  → ε_fun (comp f g) n = (ε_fun f n * ε_fun g n)%F.
Proof.
intros Hop Hin Hic Hde H10 Hit Hch * Hp1 Hp2.
apply signature_comp_fun_expand_1; try easy.
rewrite signature_comp_fun_expand_2_1; try easy.
rewrite signature_comp_fun_expand_2_2; try easy.
now apply signature_comp_fun_changement_of_variable.
Qed.

Theorem signature_comp :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n (σ₁ σ₂ : vector nat),
  is_permut_vect n σ₁
  → is_permut_vect n σ₂
  → ε n (σ₁ ° σ₂) = (ε n σ₁ * ε n σ₂)%F.
Proof.
intros Hop Hin Hic Hde H10 Hit Hch * Hp1 Hp2.
unfold ε.
destruct Hp1 as (Hp1, Hp'1).
destruct Hp2 as (Hp2, Hp'2).
rewrite <- signature_comp_fun; try easy.
unfold comp, "°".
unfold ε_fun; f_equal.
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
cbn; unfold comp_list.
rewrite (List_map_nth' 0); [ | rewrite fold_vect_size; flia Hp2 Hi ].
rewrite (List_map_nth' 0); [ | rewrite fold_vect_size; flia Hp2 Hj ].
easy.
Qed.

Theorem transposition_involutive : ∀ p q i,
  transposition p q (transposition p q i) = i.
Proof.
intros.
unfold transposition.
do 4 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i p) as [Hip| Hip]. {
  destruct (Nat.eq_dec q p) as [Hqp| Hqp]; [ congruence | ].
  destruct (Nat.eq_dec q q) as [H| H]; [ congruence | easy ].
}
destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
  destruct (Nat.eq_dec p p) as [H| H]; [ congruence | easy ].
}
destruct (Nat.eq_dec i p) as [H| H]; [ easy | clear H ].
destruct (Nat.eq_dec i q) as [H| H]; [ easy | clear H ].
easy.
Qed.

Theorem transposition_injective : ∀ p q i j,
  transposition p q i = transposition p q j
  → i = j.
Proof.
intros * Hpq.
apply (f_equal (transposition p q)) in Hpq.
now do 2 rewrite transposition_involutive in Hpq.
Qed.

(*
Theorem swap_elem_involutive : ∀ f p q,
  swap_elem (swap_elem f p q) p q = f.
Proof.
intros.
Print fin_fun_ext.
Theorem my_false : ∀ A (f g : nat → A), f = g.
Proof.
intros.
apply fin_fun_ext with (n := 0).
easy.
Print fin_fun_ext.
...
apply fin_fun_ext with (n := n).
intros i Hi.
unfold swap_elem.
rewrite transposition_involutive.
...
apply vector_eq.
intros i Hi; cbn.
unfold swap_elem.
now rewrite transposition_involutive.
Qed.
*)

(*
Theorem vect_swap_elem_injective : ∀ (u v : vector nat) p q,
  vect_swap_elem u p q = vect_swap_elem v p q
  → u = v.
Proof.
intros * Huv.
apply (f_equal (λ u, vect_swap_elem u p q)) in Huv.
now do 2 rewrite vect_swap_elem_involutive in Huv.
Qed.
*)

(* i such that vect_el (permut n k) i = j *)

(*
Definition sym_gr_elem_swap_with_0 p n k :=
  vect_swap_elem (vect_el (mk_canon_sym_gr_vect n) k) 0 p.
*)

(* k' such that permut_swap_with_0 p n k = permut n k' *)

Definition sym_gr_elem_swap_last (p q : nat) n k :=
  vect_swap_elem 0
    (vect_swap_elem 0 (vect_vect_nat_el (mk_canon_sym_gr_vect n) k) p (n - 2))
    q (n - 1).

(* *)

Theorem ε_permut_succ : ∀ n k,
  k < fact (S n)
  → ε_permut (S n) k =
     (minus_one_pow (k / fact n) * ε_permut n (k mod fact n))%F.
Proof. easy. Qed.

Theorem sym_gr_succ_values : ∀ n k σ σ',
  σ = sym_gr_fun n (mk_canon_sym_gr n) k
  → σ' = mk_canon_sym_gr n (k mod n!)
  → ∀ i,
    σ i =
    match i with
    | 0 => k / fact n
    | S i' => if σ' i' <? k / fact n then σ' i' else σ' i' + 1
    end.
Proof.
intros * Hσ Hσ' i.
destruct i; [ now subst σ | ].
subst σ; cbn - [ "<?" ].
subst σ'; cbn - [ "<?" ].
rewrite Nat.leb_antisym.
unfold Nat.b2n.
rewrite if_ltb_lt_dec.
rewrite negb_if.
rewrite if_ltb_lt_dec.
destruct (lt_dec _ _) as [H1| H1]; [ | easy ].
apply Nat.add_0_r.
Qed.

Theorem sym_gr_vect_succ_values : ∀ (n k : nat) (σ σ' : nat → nat),
  k < (S n)!
  → σ = vect_el 0 (vect_vect_nat_el (mk_canon_sym_gr_vect (S n)) k)
  → σ' = vect_el 0 (vect_vect_nat_el (mk_canon_sym_gr_vect n) (k mod n!))
  → ∀ i : nat, i < S n →
    σ i =
      match i with
      | 0 => k / n!
      | S i' => if σ' i' <? k / n! then σ' i' else σ' i' + 1
      end.
Proof.
intros * Hkn Hσ Hσ' i Hin.
unfold mk_canon_sym_gr_vect in Hσ.
cbn - [ map fact seq ] in Hσ.
rewrite (List_map_nth' 0) in Hσ; [ | now rewrite seq_length ].
rewrite seq_nth in Hσ; [ | easy ].
rewrite Nat.add_0_l in Hσ.
rewrite Hσ.
unfold vect_el.
cbn - [ "<?" nth seq ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite Nat.add_0_l.
destruct i; [ easy | ].
subst σ; cbn - [ "<?" ].
subst σ'; cbn - [ "<?" ].
rewrite Nat.leb_antisym.
unfold Nat.b2n.
rewrite if_ltb_lt_dec.
rewrite negb_if.
rewrite if_ltb_lt_dec.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  apply Nat.mod_upper_bound, fact_neq_0.
}
cbn - [ fact map seq "<?" ].
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hin ].
rewrite seq_nth; [ | apply Nat.mod_upper_bound, fact_neq_0 ].
rewrite seq_nth; [ | flia Hin ].
do 2 rewrite Nat.add_0_l.
destruct (lt_dec _ _); [ apply Nat.add_0_r | easy ].
Qed.

(* equality of ε of sym_gr elem and ε_permut *)

Theorem ε_of_sym_gr_permut_succ :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n k,
  k < (S n)!
  → ε (S n) (vect_vect_nat_el (mk_canon_sym_gr_vect (S n)) k) =
    (minus_one_pow (k / n!) *
     ε n (vect_vect_nat_el (mk_canon_sym_gr_vect n) (k mod n!)))%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hkn.
rewrite ε_ws_ε; try easy; [ | now apply mk_canon_is_permut_vect ].
unfold ε_ws, ε_fun_ws.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold ε, ε_fun.
  subst n.
  apply Nat.lt_1_r in Hkn.
  subst k; cbn.
  unfold iter_seq, iter_list; cbn.
  repeat rewrite rngl_mul_1_l.
  rewrite rngl_div_1_l; [ | easy ].
  now symmetry; apply rngl_inv_1.
}
rewrite rngl_product_succ_succ.
rewrite rngl_product_split_first; [ | flia ].
rewrite Nat.sub_diag.
f_equal. {
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    replace (1 <? 1 + i) with (0 <? i) by easy.
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  cbn - [ "<?" mk_canon_sym_gr_vect ].
  rewrite rngl_product_split_first; [ | flia ].
  replace (0 <? 0) with false by easy.
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec 0 i) as [H| H]; [ clear H | flia Hi H ].
    easy.
  }
  cbn - [ mk_canon_sym_gr_vect ].
  remember (vect_el 0 (vect_vect_nat_el (mk_canon_sym_gr_vect (S n)) k))
    as σ eqn:Hσ.
  remember
    (vect_el 0 (vect_vect_nat_el (mk_canon_sym_gr_vect n) (k mod n!)))
    as σ' eqn:Hσ'.
  specialize (sym_gr_vect_succ_values Hkn Hσ Hσ') as H1.
  unfold sign_diff.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite H1; [ | flia ].
    easy.
  }
  cbn - [ "<?" ].
  rewrite rngl_product_shift; [ | flia Hnz ].
  remember (k / fact n) as x eqn:Hx.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? _ then _ else _) with
      (if x <? σ' i + 1 then 1%F else (-1)%F). 2: {
      rewrite (Nat.add_1_l i).
      rewrite H1; [ | flia Hi Hnz ].
      do 3 rewrite if_ltb_lt_dec.
      destruct (lt_dec (σ' i) x) as [H2| H2]; [ | easy ].
      destruct (lt_dec x (σ' i)) as [H| H]; [ flia H H2 | clear H ].
      destruct (lt_dec x (σ' i + 1)) as [H3| H3]; [ | easy ].
      flia H2 H3.
    }
    easy.
  }
  cbn - [ "<?" ].
  assert (Hp' : is_permut_fun σ' n). {
    rewrite Hσ'.
    apply mk_canon_is_permut_vect.
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  assert (Hp : is_permut_fun σ (S n)). {
    rewrite Hσ.
    now apply mk_canon_is_permut_vect.
  }
  rewrite rngl_product_change_var with (g := permut_fun_inv_loop σ' n) (h := σ').
  2: {
    intros i (_, Hi).
    apply fun_find_prop; [ | flia Hnz Hi ].
    apply Hp'.
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_list_eq_compat. 2: {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite fun_permut_fun_inv_loop; [ easy | easy | ].
    now rewrite <- Hji; apply Hp'.
  }
  cbn - [ "<?" seq ].
  rewrite rngl_product_change_list with (lb := seq 0 n); [ | easy | ]. 2: {
    now apply permut_fun_Permutation.
  }
  rewrite rngl_product_seq_product; [ | easy ].
  rewrite Nat.add_0_l.
  destruct (Nat.eq_dec x 0) as [Hxz| Hxz]. {
    move Hxz at top; subst x.
    cbn - [ "<?" ].
    apply all_1_rngl_product_1.
    intros i (_, Hi).
    now rewrite Nat.add_comm.
  }
  rewrite (rngl_product_split (x - 1)). 2: {
    split; [ flia | ].
    apply -> Nat.succ_le_mono.
    enough (H : x < S n) by flia H Hnz.
    replace x with (σ 0). 2: {
      rewrite H1; [ easy | flia ].
    }
    apply Hp; flia.
  }
  remember (∏ (i = _, _), _)%F as y eqn:Hy.
  rewrite all_1_rngl_product_1. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec x (i + 1)) as [H2| H2]; [ easy | ].
    flia Hi H2.
  }
  subst y; rewrite rngl_mul_1_r.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? i + 1 then 1%F else _) with (-1)%F. 2: {
      rewrite if_ltb_lt_dec.
      destruct (lt_dec x (i + 1)) as [H| H]; [ | easy ].
      flia Hi H Hxz.
    }
    easy.
  }
  cbn.
  destruct x; [ easy | clear Hxz ].
  rewrite Nat_sub_succ_1.
  clear Hx H1.
  induction x; cbn. {
    unfold iter_seq, iter_list; cbn.
    apply rngl_mul_1_l.
  }
  rewrite rngl_product_split_last; [ | flia ].
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  rewrite IHx.
  symmetry.
  rewrite minus_one_pow_succ; [ | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
}
rewrite ε_ws_ε; try easy. 2: {
  apply mk_canon_is_permut_vect.
  apply Nat.mod_upper_bound.
  apply fact_neq_0.
}
unfold ε_ws, ε_fun_ws.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_succ_succ.
  rewrite rngl_product_split_first; [ | flia ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (S i) 1) as [H| H]; [ flia H | clear H ].
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    replace (S i <? S j) with (i <? j) by easy.
    now do 2 rewrite Nat_sub_succ_1.
  }
  easy.
}
cbn - [ mk_canon_sym_gr "<?" fact map vect_vect_nat_el ].
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
move j before i.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
remember (vect_el 0 (vect_vect_nat_el (mk_canon_sym_gr_vect (S n)) k))
  as σ eqn:Hσ.
remember (vect_el 0 (vect_vect_nat_el (mk_canon_sym_gr_vect n) (k mod n!)))
  as σ' eqn:Hσ'.
rewrite (sym_gr_vect_succ_values Hkn Hσ Hσ'); [ | flia Hj ].
rewrite (sym_gr_vect_succ_values Hkn Hσ Hσ'); [ | flia Hi ].
destruct j; [ flia Hj | ].
destruct i; [ flia Hi | ].
rewrite Nat_sub_succ_1.
rewrite Nat_sub_succ_1.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' j) (k / fact n)) as [Hsfj| Hsfj]. {
  destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]; [ easy | ].
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i + 1) (σ' j)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsi1j Hsij.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsij Hsfj Hsfi.
}
destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]. {
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsij Hsfj Hsfi.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsi1j Hsij.
}
unfold sign_diff.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' i + 1) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
  flia Hsi1j Hsij.
}
destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
flia Hsi1j Hsij.
Qed.

(*
Theorem ε_of_sym_gr_permut_succ :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n k,
  k < (S n)!
  → ε (vect_el (mk_canon_sym_gr_vect (S n)) k) =
    (minus_one_pow (k / n!) *
     ε (vect_el (mk_canon_sym_gr_vect n) (k mod n!)))%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hkn.
rewrite ε_ws_ε; try easy; [ | now apply sym_gr_elem_is_permut ].
unfold ε_ws, ε_fun_ws.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold ε, ε_fun.
  subst n.
  apply Nat.lt_1_r in Hkn.
  subst k; cbn.
  unfold iter_seq, iter_list; cbn.
  repeat rewrite rngl_mul_1_l.
  rewrite rngl_div_1_l; [ | easy ].
  now symmetry; apply rngl_inv_1.
}
rewrite rngl_product_succ_succ.
rewrite rngl_product_split_first; [ | flia ].
rewrite Nat.sub_diag.
f_equal. {
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    replace (1 <? 1 + i) with (0 <? i) by easy.
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  cbn - [ "<?" mk_canon_sym_gr ].
  rewrite rngl_product_split_first; [ | flia ].
  replace (0 <? 0) with false by easy.
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec 0 i) as [H| H]; [ clear H | flia Hi H ].
    easy.
  }
  cbn - [ mk_canon_sym_gr ].
  remember (mk_canon_sym_gr (S n) k) as σ eqn:Hσ.
  remember (mk_canon_sym_gr n (k mod fact n)) as σ' eqn:Hσ'.
  specialize (sym_gr_succ_values Hσ Hσ') as H1.
  unfold sign_diff.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite H1.
    replace i with (S (i - 1)) at 1 by flia Hi.
    easy.
  }
  cbn - [ "<?" ].
  remember (k / fact n) as x eqn:Hx.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite <- Nat.sub_succ_l; [ | easy ].
    rewrite Nat_sub_succ_1.
    rewrite H1.
    replace i with (S (i - 1)) at 1 by flia Hi.
    easy.
  }
  cbn - [ "<?" ].
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  cbn - [ "<?" ].
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? _ then _ else _) with
      (if x <? σ' i + 1 then 1%F else (-1)%F). 2: {
      do 3 rewrite if_ltb_lt_dec.
      destruct (lt_dec (σ' i) x) as [H2| H2]; [ | easy ].
      destruct (lt_dec x (σ' i)) as [H| H]; [ flia H H2 | clear H ].
      destruct (lt_dec x (σ' i + 1)) as [H3| H3]; [ | easy ].
      flia H2 H3.
    }
    easy.
  }
  cbn - [ "<?" ].
  assert (Hp' : is_permut_fun σ' n). {
    rewrite Hσ'.
    apply sym_gr_elem_is_permut.
    apply Nat.mod_upper_bound.
    apply fact_neq_0.
  }
  assert (Hp : is_permut_fun σ (S n)). {
    rewrite Hσ.
    now apply sym_gr_elem_is_permut.
  }
  rewrite rngl_product_change_var with (g := permut_fun_inv_loop σ' n) (h := σ').
  2: {
    intros i (_, Hi).
    apply fun_find_prop; [ | flia Hnz Hi ].
    apply Hp'.
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_list_eq_compat. 2: {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite fun_permut_fun_inv_loop; [ easy | easy | ].
    now rewrite <- Hji; apply Hp'.
  }
  cbn - [ "<?" seq ].
  rewrite rngl_product_change_list with (lb := seq 0 n); [ | easy | ]. 2: {
    now apply permut_fun_Permutation.
  }
  rewrite rngl_product_seq_product; [ | easy ].
  rewrite Nat.add_0_l.
  destruct (Nat.eq_dec x 0) as [Hxz| Hxz]. {
    move Hxz at top; subst x.
    cbn - [ "<?" ].
    apply all_1_rngl_product_1; [ easy | ].
    intros i (_, Hi).
    now rewrite Nat.add_comm.
  }
  rewrite (rngl_product_split (x - 1)). 2: {
    split; [ flia | ].
    apply -> Nat.succ_le_mono.
    enough (H : x < S n) by flia H Hnz.
    replace x with (σ 0) by now rewrite H1.
    apply Hp; flia.
  }
  remember (∏ (i = _, _), _)%F as y eqn:Hy.
  rewrite all_1_rngl_product_1; [ | easy | ]. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec x (i + 1)) as [H2| H2]; [ easy | ].
    flia Hi H2.
  }
  subst y; rewrite rngl_mul_1_r.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? i + 1 then 1%F else _) with (-1)%F. 2: {
      rewrite if_ltb_lt_dec.
      destruct (lt_dec x (i + 1)) as [H| H]; [ | easy ].
      flia Hi H Hxz.
    }
    easy.
  }
  cbn.
  destruct x; [ easy | clear Hxz ].
  rewrite Nat_sub_succ_1.
  clear Hx H1.
  induction x; cbn. {
    unfold iter_seq, iter_list; cbn.
    apply rngl_mul_1_l.
  }
  rewrite rngl_product_split_last; [ | flia ].
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  rewrite IHx.
  symmetry.
  rewrite minus_one_pow_succ; [ | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
}
rewrite ε_ws_ε; try easy. 2: {
  apply sym_gr_elem_is_permut.
  apply Nat.mod_upper_bound.
  apply fact_neq_0.
}
unfold ε_ws, ε_fun_ws.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_succ_succ.
  rewrite rngl_product_split_first; [ | flia ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (S i) 1) as [H| H]; [ flia H | clear H ].
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    replace (S i <? S j) with (i <? j) by easy.
    now do 2 rewrite Nat_sub_succ_1.
  }
  easy.
}
cbn - [ mk_canon_sym_gr "<?" ].
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
move j before i.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
remember (mk_canon_sym_gr (S n) k) as σ eqn:Hσ.
remember (mk_canon_sym_gr n (k mod n!)) as σ' eqn:Hσ'.
move σ' before σ.
do 2 rewrite (sym_gr_succ_values Hσ Hσ').
destruct j; [ flia Hj | ].
destruct i; [ flia Hi | ].
rewrite Nat_sub_succ_1.
rewrite Nat_sub_succ_1.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' j) (k / fact n)) as [Hsfj| Hsfj]. {
  destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]; [ easy | ].
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i + 1) (σ' j)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsi1j Hsij.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsij Hsfj Hsfi.
}
destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]. {
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsij Hsfj Hsfi.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsi1j Hsij.
}
unfold sign_diff.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' i + 1) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
  flia Hsi1j Hsij.
}
destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
flia Hsi1j Hsij.
Qed.
*)

Theorem ε_of_permut_ε :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n k,
  k < fact n
  → ε n (vect_vect_nat_el (mk_canon_sym_gr_vect n) k) = ε_permut n k.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hkn.
revert k Hkn.
induction n; intros. {
  cbn; unfold ε, ε_fun; cbn.
  unfold iter_seq, iter_list; cbn.
  apply rngl_div_1_r; [ now left | easy ].
}
rewrite ε_of_sym_gr_permut_succ; try easy.
cbn.
f_equal.
apply IHn.
apply Nat.mod_upper_bound.
apply fact_neq_0.
Qed.

Theorem permut_vect_inv_is_permut : ∀ n (σ : vector nat),
  is_permut_vect n σ
  → is_permut_vect n (permut_vect_inv n σ).
Proof.
intros * (Hp1, Hp2).
specialize (permut_fun_inv_loop_is_permut Hp2) as H1.
split; [ now cbn; rewrite map_length, seq_length | ].
unfold permut_vect_inv, vect_el; cbn.
eapply is_permut_eq_compat. {
  intros i Hi.
  symmetry.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  easy.
}
easy.
Qed.

Theorem canon_sym_gr_inv_upper_bound : ∀ n k j,
  k < fact n
  → j < n
  → canon_sym_gr_inv n k j < n.
Proof.
intros * Hkn Hjn.
revert k j Hkn Hjn.
induction n; intros; [ easy | ].
cbn.
destruct (lt_dec j (k / fact n)) as [Hjkn| Hjkn]. {
  apply -> Nat.succ_lt_mono.
  destruct n. {
    cbn in Hkn.
    apply Nat.lt_1_r in Hkn; subst k.
    now cbn in Hjkn.
  }
  destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
    subst j.
    clear Hjn.
    exfalso; apply Nat.nle_gt in Hjkn; apply Hjkn; clear Hjkn.
    rewrite Nat_fact_succ in Hkn.
    rewrite Nat.mul_comm in Hkn.
    apply Nat.lt_succ_r.
    apply Nat.div_lt_upper_bound; [ | easy ].
    apply fact_neq_0.
  } {
    apply IHn; [ | flia Hjn Hjsn ].
    apply Nat.mod_upper_bound, fact_neq_0.
  }
} {
  apply Nat.nlt_ge in Hjkn.
  destruct (lt_dec (k / fact n) j) as [Hknj| Hknj]; [ | flia ].
  apply -> Nat.succ_lt_mono.
  destruct n. {
    now apply Nat.lt_1_r in Hjn; subst j.
  }
  apply IHn; [ | flia Hjn Hknj ].
  apply Nat.mod_upper_bound, fact_neq_0.
}
Qed.

Theorem sym_gr_sym_gr_inv : ∀ n k j,
  j < n
  → k < fact n
  → mk_canon_sym_gr n k (canon_sym_gr_inv n k j) = j.
Proof.
intros * Hjn Hkn.
revert j k Hjn Hkn.
induction n; intros; [ easy | cbn ].
destruct (lt_dec j (k / fact n)) as [Hjkn| Hjkn]. {
  cbn.
  destruct n. {
    rewrite Nat.div_1_r in Hjkn; cbn in Hkn.
    flia Hkn Hjkn.
  }
  destruct (lt_dec k (fact (S n))) as [Hksn| Hksn]. {
    now rewrite Nat.div_small in Hjkn.
  }
  apply Nat.nlt_ge in Hksn.
  destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
    subst j.
    clear Hjn.
    exfalso; apply Nat.nle_gt in Hjkn; apply Hjkn; clear Hjkn.
    rewrite Nat_fact_succ in Hkn.
    rewrite Nat.mul_comm in Hkn.
    apply Nat.lt_succ_r.
    apply Nat.div_lt_upper_bound; [ | easy ].
    apply fact_neq_0.
  }
  rewrite IHn; [ | flia Hjn Hjsn | ]. 2: {
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  remember (k / fact (S n) <=? j) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ exfalso | apply Nat.add_0_r ].
  apply Nat.leb_le in Hb.
  flia Hjkn Hb.
} {
  apply Nat.nlt_ge in Hjkn.
  destruct (lt_dec (k / fact n) j) as [Hkj| Hkj]. 2: {
    apply Nat.nlt_ge in Hkj; cbn.
    now apply Nat.le_antisymm.
  }
  clear Hjkn.
  destruct j; [ easy | ].
  rewrite Nat_sub_succ_1; cbn.
  destruct n; [ flia Hjn | ].
  apply Nat.succ_lt_mono in Hjn.
  rewrite IHn; [ | easy | ]. 2: {
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  remember (k / fact (S n) <=? j) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ apply Nat.add_1_r | exfalso ].
  apply Nat.leb_nle in Hb.
  now apply Nat.succ_le_mono in Hkj.
}
Qed.

Theorem canon_sym_gr_surjective : ∀ n k j,
  k < fact n
  → j < n
  → ∃ i : nat, i < n ∧ mk_canon_sym_gr n k i = j.
Proof.
intros * Hkn Hjn.
exists (canon_sym_gr_inv n k j).
destruct n; [ easy | ].
split. {
  cbn.
  destruct (lt_dec j (k / fact n)) as [Hjk| Hjk]. {
    apply -> Nat.succ_lt_mono.
    destruct n. {
      now apply Nat.lt_1_r in Hkn; subst k.
    }
    destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
      subst j; clear Hjn.
      apply Nat.nle_gt in Hjk.
      exfalso; apply Hjk; clear Hjk.
      rewrite Nat_fact_succ in Hkn.
      rewrite Nat.mul_comm in Hkn.
      apply Nat.lt_succ_r.
      apply Nat.div_lt_upper_bound; [ | easy ].
      apply fact_neq_0.
    }
    apply canon_sym_gr_inv_upper_bound; [ | flia Hjn Hjsn ].
    apply Nat.mod_upper_bound, fact_neq_0.
  } {
    apply Nat.nlt_ge in Hjk.
    destruct (lt_dec (k / fact n) j) as [Hkj| Hkj]; [ | flia ].
    apply -> Nat.succ_lt_mono.
    destruct n. {
      apply Nat.lt_1_r in Hkn; subst k.
      flia Hjn Hkj.
    }
    apply canon_sym_gr_inv_upper_bound; [ | flia Hjn Hkj ].
    apply Nat.mod_upper_bound, fact_neq_0.
  }
}
now apply sym_gr_sym_gr_inv.
Qed.

Theorem comp_is_permut : ∀ n (σ₁ σ₂ : nat → nat),
  is_permut_fun σ₁ n
  → is_permut_fun σ₂ n
  → is_permut_fun (comp σ₁ σ₂) n.
Proof.
intros * Hp1 Hp2.
split. {
  intros i Hi.
  now apply Hp1, Hp2.
} {
  intros i j Hi Hj Hc.
  apply Hp2; [ easy | easy | ].
  apply Hp1; [ now apply Hp2 | now apply Hp2 | easy ].
}
Qed.

Theorem comp_list_is_permut : ∀ n l,
  (∀ σ, σ ∈ l → is_permut_fun σ n)
  → is_permut_fun (Comp (σ ∈ l), σ) n.
Proof.
intros * Hl.
induction l as [| σ]; [ easy | ].
rewrite iter_list_cons; [ | easy | easy | easy ].
apply comp_is_permut. 2: {
  apply IHl.
  intros σ' Hσ'.
  now apply Hl; right.
}
now apply Hl; left.
Qed.

(*
Theorem is_permut_comp : ∀ n (u v : vector nat),
  is_permut_vect u → is_permut_vect v → is_permut_vect (u ° v).
Proof.
intros * Hu Hv.
split. {
  intros i Hi.
  cbn; unfold comp.
  now apply Hu, Hv.
} {
  intros i j Hi Hj Huv.
  apply Hu in Huv; [ | now apply Hv | now apply Hv ].
  now apply Hv in Huv.
}
Qed.
*)

(*
Theorem ε_1_opp_1 :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n (σ : vector n nat), is_permut_vect σ → ε σ = 1%F ∨ ε σ = (-1)%F.
Proof.
intros Hic Hop Hiv H10 Hit Hed Hch * Hσ.
rewrite ε_ws_ε; try easy.
unfold ε_ws.
unfold ε_fun_ws.
apply rngl_product_1_opp_1; [ easy | ].
intros i Hi.
apply rngl_product_1_opp_1; [ easy | ].
intros j Hj.
unfold sign_diff.
rewrite if_ltb_lt_dec.
rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]. {
  now destruct (lt_dec _ _) as [Hvv| Hvv]; [ left | right ].
}
now left.
Qed.
*)

(*
Theorem ε_square :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n (σ : vector n nat), is_permut_vect σ → (ε σ * ε σ = 1)%F.
Proof.
intros Hic Hop Hiv H10 Hit Hed Hch * Hσ.
specialize (ε_1_opp_1) as H1.
specialize (H1 Hic Hop Hiv H10 Hit Hed Hch).
specialize (H1 n σ Hσ).
destruct H1 as [H1| H1]; rewrite H1. {
  apply rngl_mul_1_l.
} {
  rewrite rngl_mul_opp_opp; [ | easy ].
  apply rngl_mul_1_l.
}
Qed.
*)

End a.

Arguments δ {T}%type {ro} (i j u v)%nat.
Arguments ε {T}%type {ro} n%nat p%V.
Arguments ε_fun {T}%type {ro} f%function n%nat.
Arguments ε_ws {T}%type {ro} n.
Arguments ε_fun_ws {T}%type {ro} f%function n%nat.
Arguments sign_diff {T}%type {ro} (u v)%nat.

Arguments ε_permut {T}%type {ro} (n k)%nat.
Arguments ε_of_sym_gr_permut_succ {T}%type {ro rp} _ _ _ _ _ _ _ (n k)%nat.
Arguments ε_of_permut_ε {T}%type {ro rp} _ _ _ _ _ _ _ n%nat [k]%nat.
Arguments ε_ws_ε {T}%type {ro rp} _ _ _ _ _ _ _ n%nat p%V.
Arguments ε_ws_ε_fun {T}%type {ro rp} _ _ _ _ _ _ _ [σ]%function [n]%nat.
Arguments rngl_product_change_list {T}%type {ro rp} _ [A]%type [la lb]%list
  f%function.
Arguments signature_comp {T}%type {ro rp} _ _ _ _ _ _ _ [n]%nat [σ₁ σ₂].
Arguments transposition_signature {T}%type {ro rp} _ _ _ _ _ _ _ (n p q)%nat.
(*
Arguments ε_1_opp_1 {T}%type {ro rp} _ _ _ _ _ _ _ [n]%nat [σ].
Arguments ε_square {T}%type {ro rp} _ _ _ _ _ _ _ [n]%nat [σ].
*)
