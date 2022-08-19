(* trying to prove that det(AB)=det(A)det(B) *)

(* there are several proofs of that, none of them being simple *)
(* here, trying to prove it by the Cauchy-Binet Formula *)
(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)

(* det(AB)= ∑ 1≤j1<j2<⋯<jm≤n det(Aj1j2…jm)det(Bj1j2…jm)
   where A is a m×n matrix, B a n×m matrix
   Aj1j2…jm denotes the m×m matrix consisting of columns j1,j2,…,jm of A.
   Bj1j2…jm denotes the m×m matrix consisting of rows j1,j2,…,jm of B. *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations Init.Nat.

Require Import Misc RingLike.
Require Import PermutationFun SortingFun SortRank.
Require Import IterAdd IterMul IterAnd Pigeonhole.
Require Import Matrix PermutSeq Signature.
Require Import Determinant.
Require Import NatRingLike.
Import matrix_Notations.

(* binomial *)
(* code borrowed from my work "coq_euler_prod_form" *)

Fixpoint binomial n k :=
  match k with
  | 0 => 1
  | S k' =>
      match n with
      | 0 => 0
      | S n' => binomial n' k' + binomial n' k
     end
  end.

Theorem binomial_0_l : ∀ n, n ≠ 0 → binomial 0 n = 0.
Proof. now intros * Hnz; induction n. Qed.

Theorem binomial_0_r : ∀ n, binomial n 0 = 1.
Proof. now intros; induction n. Qed.

Theorem binomial_1_r : ∀ n, binomial n 1 = n.
Proof.
intros.
induction n; [ easy | cbn ].
now rewrite IHn, binomial_0_r.
Qed.

Theorem binomial_out : ∀ n k, n < k → binomial n k = 0.
Proof.
intros * Hnk.
revert k Hnk.
induction n; intros; [ now destruct k | cbn ].
destruct k; [ flia Hnk | ].
apply Nat.succ_lt_mono in Hnk.
rewrite IHn; [ | easy ].
rewrite Nat.add_0_l.
apply IHn; flia Hnk.
Qed.

Theorem binomial_diag : ∀ n, binomial n n = 1.
Proof.
intros.
induction n; [ easy | cbn ].
rewrite IHn.
now rewrite binomial_out.
Qed.

(* end borrowed code *)

Theorem binomial_succ_succ : ∀ n k,
  binomial (S n) (S k) = binomial n k + binomial n (S k).
Proof. easy. Qed.

Theorem binomial_neq_0 : ∀ n k, k ≤ n → binomial n k ≠ 0.
Proof.
intros * Hkn.
revert k Hkn.
induction n; intros; [ now apply Nat.le_0_r in Hkn; subst k | ].
destruct k; [ easy | cbn ].
apply Nat.succ_le_mono in Hkn.
intros H1.
apply Nat.eq_add_0 in H1.
destruct H1 as (H1, _).
now revert H1; apply IHn.
Qed.

(* all lists [j1;j2;...jm] such that 0≤j1<j2<...<jm<n for some m and n *)

Fixpoint sls1n (i n k : nat) {struct n} : list (list nat) :=
  match k with
  | 0 => [[]]
  | S k' =>
      match n with
      | 0 => []
      | S n' => map (λ l : list nat, i :: l) (sls1n (S i) n' k') ++ sls1n (S i) n' k
      end
  end.

Definition sub_lists_of_seq_1_n := sls1n 1.

(*
Compute (let '(n,k) := (5,3) in sub_lists_of_seq_1_n n k).
*)

Fixpoint rsls1n i n k (t : list nat) : nat :=
  match k with
  | 0 => 0
  | S k' =>
      match n with
      | 0 => 0
      | S n' =>
          match t with
          | [] => 0
          | a :: t' =>
              if a =? i then rsls1n (S i) n' k' t'
              else binomial n' k' + rsls1n (S i) n' k t
          end
      end
  end.

Definition rank_of_sub_lists_of_seq_1_n := rsls1n 1.

(*
Compute (let '(n,k) := (7,5) in let ll := sub_lists_of_seq_1_n n k in map (rank_of_sub_lists_of_seq_1_n n k) ll).
*)

Theorem sls1n_length : ∀ i n k,
  length (sls1n i n k) = binomial n k.
Proof.
intros.
revert i k.
induction n; intros; [ now destruct k | ].
destruct k; [ easy | cbn ].
rewrite app_length, map_length.
now rewrite IHn, IHn.
Qed.

Theorem sub_lists_of_seq_1_n_length : ∀ k n,
  length (sub_lists_of_seq_1_n n k) = binomial n k.
Proof.
intros.
unfold sub_lists_of_seq_1_n.
apply sls1n_length.
Qed.

Theorem sls1n_bounds : ∀ i n k t,
  t ∈ sls1n i n k
  → ∀ a, a ∈ t → i ≤ a ≤ i + n.
Proof.
intros * Ht * Hat.
revert i k t Ht Hat.
induction n; intros. {
  destruct k; [ cbn in Ht | easy ].
  destruct Ht; [ now subst t | easy ].
}
destruct k; cbn in Ht. {
  destruct Ht; [ now subst t | easy ].
}
apply in_app_iff in Ht.
destruct Ht as [Ht| Ht]. 2: {
  specialize (IHn (S i) (S k) t Ht Hat).
  flia IHn.
}
apply in_map_iff in Ht.
destruct Ht as (l & Hln & Hl); subst t.
destruct Hat as [Hat| Hat]; [ subst a; flia | ].
specialize (IHn (S i) k l Hl Hat).
flia IHn.
Qed.

Theorem in_sls1n_iff : ∀ i n k t,
  t ∈ sls1n i n k
  ↔ k = 0 ∧ t = [] ∨
    sorted Nat.ltb t ∧ length t = k ∧ (∀ j, j ∈ t → i ≤ j < i + n).
Proof.
intros.
split. {
  intros Ht.
  destruct k. {
    left.
    split; [ easy | ].
    now destruct n; destruct Ht.
  }
  right.
  revert i k t Ht.
  induction n; intros; [ easy | ].
  cbn in Ht.
  apply in_app_iff in Ht.
  destruct Ht as [Ht| Ht]. 2: {
    specialize (IHn _ k t Ht).
    split; [ easy | ].
    split; [ easy | ].
    intros j Hj.
    destruct IHn as (_ & _ & IHn).
    specialize (IHn _ Hj).
    flia IHn.
  }
  apply in_map_iff in Ht.
  destruct Ht as (t' & H & Ht); subst t.
  rename t' into t; cbn.
  destruct k. {
    destruct n. {
      destruct Ht; [ subst t | easy ].
      split; [ easy | ].
      split; [ easy | ].
      intros j Hj.
      destruct Hj; [ subst j; flia | easy ].
    }
    cbn in Ht.
    destruct Ht; [ subst t | easy ].
    split; [ easy | ].
    split; [ easy | ].
    intros j Hj.
    destruct Hj; [ subst j; flia | easy ].
  }
  specialize (IHn _ _ _ Ht).
  destruct IHn as (Hs & Htk & Htb).
  split. {
    apply (sorted_cons_iff Nat_ltb_trans).
    split; [ easy | ].
    intros a Ha.
    apply Nat.ltb_lt.
    apply sls1n_bounds with (a := a) in Ht; [ flia Ht | easy ].
  }
  split; [ now f_equal | ].
  intros j Hj.
  destruct Hj as [Hj| Hj]; [ subst j; flia | ].
  specialize (Htb _ Hj); flia Htb.
} {
  intros * Hs.
  destruct Hs as [Hs| Hs]. {
    destruct Hs; subst k t.
    now destruct n; left.
  }
  destruct Hs as (Hs & Htk & Hbnd).
  revert i k t Hs Htk Hbnd.
  induction n; intros; cbn. {
    destruct k. {
      apply length_zero_iff_nil in Htk; subst t.
      now left.
    }
    exfalso.
    destruct t as [| a]; [ easy | ].
    specialize (Hbnd _ (or_introl eq_refl)).
    flia Hbnd.
  }
  destruct k. {
    apply length_zero_iff_nil in Htk; subst t.
    now left.
  }
  destruct t as [| a]; [ easy | cbn in Htk ].
  apply Nat.succ_inj in Htk.
  apply in_app_iff.
  destruct (Nat.eq_dec a i) as [Hai| Hai]. {
    subst a; left.
    apply in_map_iff.
    exists t.
    split; [ easy | ].
    apply IHn; [ | easy | ]. 2: {
      intros j Hj.
      specialize (Hbnd _ (or_intror Hj)).
      rewrite <- Nat.add_succ_comm in Hbnd.
      split; [ | easy ].
      destruct (Nat.eq_dec i j) as [Hij| Hij]; [ | flia Hbnd Hij ].
      subst j; exfalso; clear Hbnd.
      apply (sorted_cons_iff Nat_ltb_trans) in Hs.
      destruct Hs as (Hs & Ht).
      destruct t as [| a]; [ easy | ].
      destruct Hj as [Hj| Hj]. {
        subst a.
        specialize (Ht _ (or_introl eq_refl)).
        now rewrite Nat.ltb_irrefl in Ht.
      }
      specialize (Ht _ (or_intror Hj)).
      now rewrite Nat.ltb_irrefl in Ht.
    }
    cbn in Hs.
    now apply (sorted_cons_iff Nat_ltb_trans) in Hs.
  }
  right.
  apply IHn; [ easy | now cbn; f_equal | ].
  intros j Hj.
  destruct Hj as [Hj| Hj]. {
    subst j.
    specialize (Hbnd a (or_introl eq_refl)).
    flia Hbnd Hai.
  }
  specialize (Hbnd a (or_introl eq_refl)) as H1.
  specialize (Hbnd _ (or_intror Hj)) as H2.
  cbn in Hs.
  apply (sorted_cons_iff Nat_ltb_trans) in Hs.
  destruct Hs as (Hs & Ht).
  specialize (Ht j Hj).
  apply Nat.ltb_lt in Ht.
  flia Ht H1 H2.
}
Qed.

Theorem in_sub_lists_of_seq_1_n_length : ∀ n k t,
  t ∈ sub_lists_of_seq_1_n n k → length t = k.
Proof.
intros * Ht.
unfold sub_lists_of_seq_1_n in Ht.
apply in_sls1n_iff in Ht.
destruct Ht as [(Hk, Ht)| Ht]; [ now subst k t | easy ].
Qed.

(* *)

Theorem sub_lists_of_seq_1_n_bounds : ∀ n k t,
  t ∈ sub_lists_of_seq_1_n n k
  → ∀ a, a ∈ t → 1 ≤ a ≤ n.
Proof.
intros * Ht a Hat.
unfold sub_lists_of_seq_1_n in Ht.
apply in_sls1n_iff in Ht.
destruct Ht as [(Hk, Ht)| Ht]; [ now subst t | ].
destruct Ht as (Hs & H & Ht); subst k.
specialize (Ht _ Hat).
split; [ easy | ].
now apply Nat.lt_succ_r.
Qed.

(* *)

Theorem sub_lists_of_seq_1_n_0_r : ∀ n, sub_lists_of_seq_1_n n 0 = [[]].
Proof. now intros; destruct n. Qed.

Theorem sls1n_out : ∀ i n k,
  n < k
  → sls1n i n k = [].
Proof.
intros * Hnk.
revert i k Hnk.
induction n; intros; cbn; [ now destruct k | ].
destruct k; [ easy | ].
apply Nat.succ_lt_mono in Hnk.
rewrite IHn; [ | flia Hnk ].
apply IHn.
now apply Nat.lt_lt_succ_r.
Qed.

Theorem sub_lists_of_seq_1_n_out : ∀ n k,
  n < k
  → sub_lists_of_seq_1_n n k = [].
Proof.
intros * Hnk.
now apply sls1n_out.
Qed.

Theorem sls1n_inj : ∀ i n k u v,
  u < binomial n k
  → v < binomial n k
  → nth u (sls1n i n k) [] = nth v (sls1n i n k) []
  → u = v.
Proof.
intros * Hu Hv Huv.
revert i u v k Hu Hv Huv.
induction n; intros; cbn in Huv. {
  destruct k; [ apply Nat.lt_1_r in Hu, Hv; congruence | easy ].
}
destruct k; [ apply Nat.lt_1_r in Hu, Hv; congruence | ].
destruct (lt_dec u (binomial n k)) as [Hub| Hub]. {
  rewrite app_nth1 in Huv; [ | now rewrite map_length, sls1n_length ].
  rewrite (List_map_nth' []) in Huv; [ | now rewrite sls1n_length ].
  destruct (lt_dec v (binomial n k)) as [Hvb| Hvb]. {
    rewrite app_nth1 in Huv; [ | now rewrite map_length, sls1n_length ].
    rewrite (List_map_nth' []) in Huv; [ | now rewrite sls1n_length ].
    injection Huv; clear Huv; intros Huv.
    now apply IHn in Huv.
  }
  apply Nat.nlt_ge in Hvb.
  rewrite app_nth2 in Huv; [ | now rewrite map_length, sls1n_length ].
  rewrite map_length, sls1n_length in Huv.
  specialize sls1n_bounds as H1.
  specialize (H1 (S i) n (S k)).
  remember (sls1n (S i) n (S k)) as la eqn:Hla.
  remember (v - binomial n k) as j eqn:Hj.
  specialize (H1 (nth j la [])).
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. 2: {
    apply Nat.nlt_ge in Hjla.
    now rewrite nth_overflow with (n := j) in Huv.
  }
  assert (H : nth j la [] ∈ la) by now apply nth_In.
  specialize (H1 H); clear H.
  rewrite <- Huv in H1.
  specialize (H1 _ (or_introl eq_refl)).
  flia H1.
}
apply Nat.nlt_ge in Hub.
rewrite app_nth2 in Huv; [ | now rewrite map_length, sls1n_length ].
rewrite map_length, sls1n_length in Huv.
destruct (lt_dec v (binomial n k)) as [Hvb| Hvb]. {
  rewrite app_nth1 in Huv; [ | now rewrite map_length, sls1n_length ].
  rewrite (List_map_nth' []) in Huv; [ | now rewrite sls1n_length ].
  specialize sls1n_bounds as H1.
  specialize (H1 (S i) n (S k)).
  remember (sls1n (S i) n (S k)) as la eqn:Hla.
  remember (u - binomial n k) as j eqn:Hj.
  specialize (H1 (nth j la [])).
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. 2: {
    apply Nat.nlt_ge in Hjla.
    now rewrite nth_overflow with (n := j) in Huv.
  }
  assert (H : nth j la [] ∈ la) by now apply nth_In.
  specialize (H1 H); clear H.
  rewrite Huv in H1.
  specialize (H1 _ (or_introl eq_refl)).
  flia H1.
}
apply Nat.nlt_ge in Hvb.
rewrite app_nth2 in Huv; [ | now rewrite map_length, sls1n_length ].
rewrite map_length, sls1n_length in Huv.
apply IHn in Huv; [ | cbn in Hu; flia Hu Hub | cbn in Hv; flia Hv Hvb ].
flia Huv Hub Hvb.
Qed.

Theorem rsls1n_out : ∀ i n k t,
  n < k
  → rsls1n i n k t = 0.
Proof.
intros * Hnk.
revert i t k Hnk.
induction n; intros; [ now destruct k | ].
destruct k; [ easy | ].
apply Nat.succ_lt_mono in Hnk; cbn.
destruct t as [| a]; [ easy | ].
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec a i) as [Hai| Hai]; [ now apply IHn | ].
rewrite binomial_out; [ | easy ].
apply IHn.
now apply Nat.lt_lt_succ_r.
Qed.

Theorem rank_of_sub_lists_of_seq_1_n_out : ∀ n k t,
  n < k
  → rank_of_sub_lists_of_seq_1_n n k t = 0.
Proof.
intros * Hnk.
now apply rsls1n_out.
Qed.

(*
Compute (
  let n := 7 in
  let i := 1 in
  let t := [3;5;6] in
  let k := length t in
  rsls1n i n k t ≤ binomial n k
).
Compute (
  let n := 6 in
  let t := [3;4;5] in
  let k := length t in
(
  map
    (λ i,
(
     member (list_eqb Nat.eqb) t (sls1n i n k),
     rsls1n i n k t < binomial n k
)
    ) (seq 0 10)
)
).
*)

Theorem rsls1n_ub : ∀ i n k t,
  t ∈ sls1n i n k
  → rsls1n i n k t < binomial n k.
Proof.
intros * Ht.
revert i k t Ht.
induction n; intros; [ now destruct k; cbn | ].
cbn in Ht |-*.
destruct k; cbn; [ easy | cbn ].
apply in_app_iff in Ht.
destruct Ht as [Ht| Ht]. {
  apply in_map_iff in Ht.
  destruct Ht as (t' & H & Ht); subst t.
  rename t' into t.
  rewrite Nat.eqb_refl.
  apply Nat.lt_lt_add_r.
  now apply IHn.
}
destruct t as [| a]. {
  exfalso; clear IHn.
  revert i Ht.
  induction n; intros. {
    destruct k; [ now destruct Ht | easy ].
  }
  cbn in Ht.
  apply in_app_iff in Ht.
  destruct Ht as [Ht| Ht]. {
    apply in_map_iff in Ht.
    now destruct Ht as (t & H & _).
  }
  now apply IHn with (i := S i).
}
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec a i) as [Hai| Hai]. {
  subst a.
  specialize (sls1n_bounds _ n _ _ Ht _ (or_introl eq_refl)) as H1.
  flia H1.
}
apply Nat.add_lt_mono_l.
now apply IHn.
Qed.

Theorem rank_of_sub_lists_of_seq_1_n_ub : ∀ n k t,
  t ∈ sub_lists_of_seq_1_n n k
  → rank_of_sub_lists_of_seq_1_n n k t < binomial n k.
Proof.
intros * Ht.
now apply rsls1n_ub.
Qed.

Theorem eq_nth_sls1n_nil : ∀ i n k j,
  j < length (sls1n i n k)
  → nth j (sls1n i n k) [] = []
  → k = 0.
Proof.
intros * Hjl Hjs.
destruct k; [ easy | exfalso ].
revert k i j Hjl Hjs.
induction n; intros; cbn in Hjs, Hjl; [ easy | ].
destruct (lt_dec j (length (sls1n (S i) n k))) as [Hjb| Hjb]. {
  rewrite app_nth1 in Hjs; [ | now rewrite map_length ].
  now rewrite (List_map_nth' []) in Hjs.
} {
  apply Nat.nlt_ge in Hjb.
  rewrite app_nth2 in Hjs; [ | now rewrite map_length ].
  rewrite map_length in Hjs.
  apply IHn in Hjs; [ easy | ].
  rewrite app_length, map_length in Hjl.
  flia Hjl Hjb.
}
Qed.

Theorem rsls1n_of_nth_sls1n : ∀ i n k j,
  j < binomial n k
  → rsls1n i n k (nth j (sls1n i n k) []) = j.
Proof.
intros * Hj.
revert i k j Hj.
induction n; intros. {
  destruct k; [ now apply Nat.lt_1_r in Hj | easy ].
}
destruct k; [ now apply Nat.lt_1_r in Hj | ].
cbn in Hj |-*.
destruct (lt_dec j (binomial n k)) as [Hjk| Hjk]. {
  rewrite app_nth1; [ | now rewrite map_length, sls1n_length ].
  rewrite (List_map_nth' []); [ | now rewrite sls1n_length ].
  rewrite Nat.eqb_refl.
  now apply IHn.
}
apply Nat.nlt_ge in Hjk.
rewrite app_nth2; rewrite map_length, sls1n_length; [ | easy ].
remember (j - binomial n k) as m eqn:Hm.
remember (nth m (sls1n (S i) n (S k)) []) as t eqn:Ht; symmetry in Ht.
destruct t as [| a]. {
  apply eq_nth_sls1n_nil in Ht; [ easy | ].
  subst m; rewrite sls1n_length.
  flia Hj Hjk.
}
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec a i) as [Hai| Hai]. 2: {
  rewrite <- Ht, Hm.
  rewrite IHn; [ | flia Hj Hjk ].
  rewrite Nat.add_sub_assoc; [ | easy ].
  now rewrite Nat.add_comm, Nat.add_sub.
}
subst a.
specialize (sls1n_bounds (S i) n (S k) (i :: t)) as H1.
rewrite <- Ht in H1.
remember (sls1n (S i) n (S k)) as ll eqn:Hll.
assert (H : nth m ll [] ∈ ll). {
  apply nth_In; rewrite Hll, sls1n_length.
  flia Hj Hjk Hm.
}
specialize (H1 H i); clear H.
rewrite Ht in H1.
specialize (H1 (or_introl eq_refl)).
flia H1.
Qed.

Theorem rank_of_sub_lists_of_seq_1_n_of_nth : ∀ n k i,
  i < binomial n k
  → rank_of_sub_lists_of_seq_1_n n k (nth i (sub_lists_of_seq_1_n n k) []) = i.
Proof.
intros * Hi.
now apply rsls1n_of_nth_sls1n.
Qed.

Theorem nth_rsls1n_sls1n : ∀ i n k t,
  sorted Nat.ltb t
  → length t = k
  → (∀ j, j ∈ t → i ≤ j < i + n)
  → nth (rsls1n i n k t) (sls1n i n k) [] = t.
Proof.
intros * Hs Htk Hbnd.
revert i k t Hs Htk Hbnd.
induction n; intros; cbn. {
  destruct k. {
    now apply length_zero_iff_nil in Htk; subst t.
  }
  destruct t as [| a]; [ easy | exfalso ].
  specialize (Hbnd _ (or_introl eq_refl)).
  flia Hbnd.
}
destruct k. {
  now apply length_zero_iff_nil in Htk; subst t.
}
destruct t as [| a]; [ easy | cbn in Htk ].
apply Nat.succ_inj in Htk.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec a i) as [Hai| Hai]. {
  subst a.
  assert (Ht : t ∈ sls1n (S i) n k). {
    apply in_sls1n_iff; right.
    split; [ now apply sorted_cons in Hs | ].
    split; [ easy | ].
    intros j Hj.
    specialize (Hbnd _ (or_intror Hj)) as H2.
    apply (sorted_cons_iff Nat_ltb_trans) in Hs.
    destruct Hs as (Hs & Ht).
    specialize (Ht j Hj).
    apply Nat.ltb_lt in Ht.
    flia Ht H2.
  }
  rewrite app_nth1. 2: {
    rewrite map_length, sls1n_length.
    now apply rsls1n_ub.
  }
  rewrite (List_map_nth' []). 2: {
    rewrite sls1n_length.
    now apply rsls1n_ub.
  }
  f_equal.
  clear Ht.
  apply IHn; [ | easy | ]. 2: {
    intros j Hj.
    specialize (Hbnd _ (or_intror Hj)).
    rewrite <- Nat.add_succ_comm in Hbnd.
    split; [ | easy ].
    destruct (Nat.eq_dec i j) as [Hsij| Hsij]; [ | flia Hbnd Hsij ].
    subst i; exfalso; clear Hbnd.
    apply (sorted_cons_iff Nat_ltb_trans) in Hs.
    destruct Hs as (Hs & Ht).
    destruct t as [| a]; [ easy | ].
    specialize (Ht _ (or_introl eq_refl)) as Ht.
    apply Nat.ltb_lt in Ht.
    destruct Hj as [Hj| Hj]; [ now subst a; apply Nat.lt_irrefl in Ht | ].
    apply (sorted_cons_iff Nat_ltb_trans) in Hs.
    destruct Hs as (Hs & Ht').
    specialize (Ht' _ Hj).
    apply Nat.ltb_lt in Ht'.
    flia Ht Ht'.
  }
  now apply sorted_cons in Hs.
}
rewrite app_nth2. 2: {
  rewrite map_length, sls1n_length; flia.
}
rewrite map_length, sls1n_length.
rewrite Nat.add_comm, Nat.add_sub.
apply IHn; [ easy | now cbn; f_equal | ].
intros j Hj.
destruct Hj as [Hj| Hj]. {
  subst j.
  specialize (Hbnd a (or_introl eq_refl)).
  flia Hbnd Hai.
}
specialize (Hbnd a (or_introl eq_refl)) as H1.
specialize (Hbnd _ (or_intror Hj)) as H2.
apply (sorted_cons_iff Nat_ltb_trans) in Hs.
destruct Hs as (Hs & Ht).
specialize (Ht _ Hj).
apply Nat.ltb_lt in Ht.
flia Ht H1 H2.
Qed.

Theorem nth_of_rank_of_sub_lists_of_seq_1_n : ∀ n k t,
  sorted Nat.ltb t
  → length t = k
  → (∀ i, i ∈ t → 1 ≤ i ≤ n)
  → nth (rank_of_sub_lists_of_seq_1_n n k t) (sub_lists_of_seq_1_n n k) [] =
    t.
Proof.
intros * Hs Htk Hlt.
apply nth_rsls1n_sls1n; [ easy | easy | ].
intros j Hj.
specialize (Hlt j Hj).
split; [ easy | ].
now apply Nat.lt_succ_r.
Qed.

Theorem sls1n_0_r : ∀ i n, sls1n i n 0 = [[]].
Proof. now intros; destruct n. Qed.

Theorem sls1n_1_r : ∀ i n, sls1n i n 1 = map (λ j, [j]) (seq i n).
Proof.
intros.
revert i.
induction n; intros; [ easy | cbn ].
rewrite sls1n_0_r; cbn.
f_equal.
apply IHn.
Qed.

Theorem sls1n_diag : ∀ i n, sls1n i n n = [seq i n].
Proof.
intros.
revert i.
induction n; intros; [ easy | ].
cbn; rewrite IHn; cbn.
f_equal.
now apply sls1n_out.
Qed.

Theorem sub_lists_of_seq_1_n_1_r : ∀ n,
  sub_lists_of_seq_1_n n 1 = map (λ i, [i]) (seq 1 n).
Proof.
intros.
apply sls1n_1_r.
Qed.

Theorem sub_lists_of_seq_1_n_diag : ∀ n,
  sub_lists_of_seq_1_n n n = [seq 1 n].
Proof.
intros.
apply sls1n_diag.
Qed.

Theorem sls1n_are_correct : ∀ i k n t,
  k ≠ 0
  → t ∈ sls1n i n k
  → t ≠ [].
Proof.
intros * Hkz Ht Htz; subst t.
destruct k; [ easy | clear Hkz ].
revert i Ht.
induction n; intros; [ easy | cbn in Ht ].
apply in_app_iff in Ht.
destruct Ht as [Ht| Ht]; [ | now apply IHn in Ht ].
apply in_map_iff in Ht.
now destruct Ht as (x & Hx & Hxn).
Qed.

Theorem sub_lists_of_seq_1_n_are_correct : ∀ k n t,
  k ≠ 0 → t ∈ sub_lists_of_seq_1_n n k → t ≠ [].
Proof.
intros * Hkz Ht.
now apply sls1n_are_correct in Ht.
Qed.

Theorem sls1n_are_sorted : ∀ i n k la,
  la ∈ sls1n i n k
  → sorted Nat.ltb la.
Proof.
intros * Hla.
apply in_sls1n_iff in Hla.
destruct Hla as [(H1,H2) | Ht]; [ now subst k la | easy ].
Qed.

Theorem sub_lists_of_seq_1_n_are_sorted : ∀ n k ll,
  ll = sub_lists_of_seq_1_n n k
  → ∀ l, l ∈ ll → sorted Nat.ltb l.
Proof.
intros * Hll * Hl.
subst ll.
now apply sls1n_are_sorted in Hl.
Qed.

Theorem sub_list_of_seq_1_n_has_no_dup :
  ∀ m n l, l ∈ sub_lists_of_seq_1_n m n → NoDup l.
Proof.
intros * Hs.
specialize (sub_lists_of_seq_1_n_are_sorted m n) as H1.
specialize (H1 _ eq_refl _ Hs).
clear - H1.
induction l as [| a]; [ constructor | ].
constructor. {
  intros Hal.
  specialize (sorted_extends Nat_ltb_trans H1 a Hal) as H2.
  now rewrite Nat.ltb_irrefl in H2.
}
apply IHl.
now apply sorted_cons in H1.
Qed.

Theorem sub_lists_of_seq_1_n_is_inj : ∀ n k ll,
  ll = sub_lists_of_seq_1_n n k
  → ∀ i j, i < length ll → j < length ll →
   nth i ll [] = nth j ll [] → i = j.
Proof.
intros * Hll * Hi Hj Hij.
rewrite Hll in Hi, Hj.
rewrite sub_lists_of_seq_1_n_length in Hi, Hj.
specialize rank_of_sub_lists_of_seq_1_n_of_nth as H1.
specialize (H1 n k i Hi).
specialize rank_of_sub_lists_of_seq_1_n_of_nth as H2.
specialize (H2 n k j Hj).
congruence.
Qed.

Theorem sub_lists_of_seq_1_n_is_surj : ∀ n k ll,
  ll = sub_lists_of_seq_1_n n k
  → (∀ l, l ∈ ll → ∃ i, nth i ll [] = l).
Proof.
intros * Hll * Hl.
specialize (sub_lists_of_seq_1_n_are_sorted n k Hll l Hl) as Hsort.
specialize nth_of_rank_of_sub_lists_of_seq_1_n as H1.
specialize (H1 n k l Hsort).
assert (H : length l = k). {
  apply (in_sub_lists_of_seq_1_n_length n).
  now rewrite <- Hll.
}
specialize (H1 H); clear H.
rewrite <- Hll in H1.
exists (rank_of_sub_lists_of_seq_1_n n k l).
apply H1.
intros i Hi.
apply (sub_lists_of_seq_1_n_bounds _ k l); [ | easy ].
now rewrite <- Hll.
Qed.

Theorem sub_lists_of_seq_1_n_prop : ∀ n k ll,
  ll = sub_lists_of_seq_1_n n k
  → (∀ l, l ∈ ll → sorted Nat.ltb l) ∧
    (∀ i j, i < length ll → j < length ll →
     nth i ll [] = nth j ll [] → i = j) ∧
    (∀ l, l ∈ ll → ∃ i, nth i ll [] = l).
Proof.
intros * Hll.
split. {
  intros l Hl.
  now apply (sub_lists_of_seq_1_n_are_sorted n k Hll).
}
split. {
  now apply (sub_lists_of_seq_1_n_is_inj n k).
} {
  now apply (sub_lists_of_seq_1_n_is_surj n k).
}
Qed.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

(* submatrix with list rows jl *)
Definition mat_select_rows (jl : list nat) (M : matrix T) :=
  mk_mat (map (λ i, map (λ j, mat_el M i j) (seq 1 (mat_ncols M))) jl).

(* submatrix with list cols jl *)
Definition mat_select_cols (jl : list nat) (M : matrix T) :=
  ((mat_select_rows jl M⁺)⁺)%M.

End a.

Arguments mat_select_rows {T ro} jl%list M%M.
Arguments mat_select_cols {T ro} jl%list M%M.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

(* https://fr.wikipedia.org/wiki/Formule_de_Binet-Cauchy *)
(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)

Theorem mat_select_rows_nrows : ∀ (A : matrix T) kl,
  mat_nrows (mat_select_rows kl A) = length kl.
Proof.
intros; cbn.
apply map_length.
Qed.

Theorem mat_select_rows_ncols : ∀ (A : matrix T) kl,
  kl ≠ []
  → mat_ncols (mat_select_rows kl A) = mat_ncols A.
Proof.
intros * Hkl; cbn.
destruct kl as [| k]; [ easy | ].
now cbn; rewrite List_map_seq_length.
Qed.

Theorem mat_select_cols_nrows : ∀ (A : matrix T) kl,
  kl ≠ []
  → mat_ncols A ≠ 0
  → mat_nrows (mat_select_cols kl A) = mat_nrows A.
Proof.
intros * Hlk Hcz; cbn.
rewrite List_map_seq_length.
rewrite mat_select_rows_ncols; [ | easy ].
rewrite mat_transp_ncols.
now apply Nat.eqb_neq in Hcz; rewrite Hcz.
Qed.

Theorem mat_select_cols_el : ∀ M i j jl,
  1 ≤ i ≤ mat_nrows M
  → 1 ≤ j ≤ length jl
  → (∀ j, 1 ≤ j ≤ length jl → 1 ≤ jl.(j) ≤ mat_ncols M)
  → mat_el (mat_select_cols jl M) i j = mat_el M i jl.(j).
Proof.
intros * Hi Hj Hjl.
assert (Hjlz : jl ≠ []). {
  intros H; rewrite H in Hj; cbn in Hj; flia Hj.
}
cbn.
rewrite map_length.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length, mat_select_rows_ncols; [ | easy ].
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]; [ | flia Hi ].
  specialize (Hjl _ Hj); flia Hjl Hcz.
}
rewrite seq_nth. 2: {
  rewrite mat_select_rows_ncols; [ | easy ].
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]; [ | flia Hi ].
  specialize (Hjl _ Hj); flia Hjl Hcz.
}
rewrite Nat.add_comm, Nat.add_sub.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj ].
rewrite seq_nth; [ | flia Hj ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite (List_map_nth' 0); [ | flia Hj ].
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length, mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]; [ | flia Hi ].
  specialize (Hjl _ Hj); flia Hjl Hcz.
}
rewrite seq_nth. 2: {
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]; [ | flia Hi ].
  specialize (Hjl _ Hj); flia Hjl Hcz.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  specialize (Hjl _ Hj); flia Hjl.
}
rewrite Nat.add_comm, Nat.add_sub.
rewrite seq_nth; [ | specialize (Hjl _ Hj); flia Hjl ].
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
rewrite Nat.add_comm, Nat.sub_add; [ | now specialize (Hjl _ Hj) ].
rewrite seq_nth; [ | flia Hi ].
now rewrite Nat.add_comm, Nat.sub_add.
Qed.

Theorem mat_select_rows_is_square : ∀ kl (A : matrix T),
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_nrows A)
  → is_square_matrix (mat_select_rows kl A) = true.
Proof.
intros * Ha Hca Hkc.
destruct (Nat.eq_dec (length kl) 0) as [Hnz| Hnz]. {
  apply length_zero_iff_nil in Hnz; subst kl.
  now cbn; rewrite iter_list_empty.
}
apply is_scm_mat_iff.
apply is_scm_mat_iff in Ha.
destruct Ha as (Hcra, Hcla).
split. {
  rewrite mat_select_rows_nrows.
  unfold mat_ncols; cbn.
  intros Hc.
  destruct kl as [| k]; [ easy | exfalso ].
  clear Hnz; cbn in Hc.
  rewrite List_map_seq_length in Hc.
  now rewrite Hca in Hc.
} {
  intros l Hl.
  rewrite mat_select_rows_nrows.
  cbn in Hl.
  apply in_map_iff in Hl.
  destruct Hl as (a & Hal & Ha).
  subst l.
  now rewrite List_map_seq_length.
}
Qed.

Theorem mat_select_cols_is_square : ∀ kl (A : matrix T),
  is_correct_matrix A = true
  → mat_nrows A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_ncols A)
  → is_square_matrix (mat_select_cols kl A) = true.
Proof.
intros * Ha Hca Hkc.
destruct (Nat.eq_dec (mat_ncols A) 0) as [Hcz| Hcz]. {
  apply is_scm_mat_iff in Ha.
  destruct Ha as (Hcr & Hc).
  rewrite Hcr in Hca; [ | easy ].
  symmetry in Hca; apply length_zero_iff_nil in Hca; subst kl.
  now cbn; rewrite iter_list_empty.
}
unfold mat_select_cols.
apply mat_transp_is_square.
apply mat_select_rows_is_square. {
  now apply mat_transp_is_corr.
} {
  rewrite mat_transp_ncols.
  now apply Nat.eqb_neq in Hcz; rewrite Hcz.
} {
  now rewrite mat_transp_nrows.
}
Qed.

Theorem det_mat_swap_rows_with_rows : in_charac_0_field →
  ∀ p q A jl,
  is_correct_matrix A = true
  → (∀ k, k ∈ jl → 1 ≤ k ≤ mat_nrows A)
  → mat_ncols A = length jl
  → 1 ≤ p ≤ length jl
  → 1 ≤ q ≤ length jl
  → p ≠ q
  → det (mat_swap_rows p q (mat_select_rows jl A)) =
    (- det (mat_select_rows jl A))%F.
Proof.
intros Hif * Hcm Hro Hco Hp Hq Hpq.
apply determinant_alternating; [ easy | easy | | | ]. {
  now rewrite mat_select_rows_nrows.
} {
  now rewrite mat_select_rows_nrows.
}
now apply mat_select_rows_is_square.
Qed.

Definition swap n p q := list_swap_elem 0 (seq 0 n) p q.

Theorem swap_length : ∀ n p q, length (swap n p q) = n.
Proof.
intros.
unfold swap, list_swap_elem.
rewrite List_map_seq_length.
apply seq_length.
Qed.

(* *)

(* which transpositions to do for transforming {0..n-1} into p *)
Definition nat_transp_list p := transp_list Nat.eqb (seq 0 (length p)) p.

(* à voir
Inductive Member A : A → list A → Prop :=
  | ext_hd : ∀ a l, Member a (a :: l)
  | ext_tl : ∀ a b l, a ≠ b → Member a l → Member a (b :: l).

Inductive Transposition A : list A → list A → A → A → Prop :=
  | transp_1 :
      ∀ a b c la lb, Transposition la lb b c → Transposition (a :: la) (a :: lb) b c
  | transp_2 :
      ∀ a b la lb,
      a ≠ b
      → Member b (a :: la)
      → Member a (b :: lb)
      → Transposition (a :: la) (b :: lb) a b.

Example transposition_1 : Transposition [1;2;3] [1;3;2] 2 3.
Proof.
constructor.
constructor; [ easy | | ]. {
  constructor; [ easy | constructor ].
} {
  constructor; [ easy | constructor ].
}
Qed.

Example transposition_2 : Transposition [1;2;3] [2;1;3] 1 2.
Proof.
constructor; [ easy | | ]. {
  constructor; [ easy | constructor ].
} {
  constructor; [ easy | constructor ].
}
Qed.

Example transposition_3 : Transposition [1;2;3] [2;3;1] 1 2.
Proof.
constructor; [ easy | | ]. {
  constructor; [ easy | constructor ].
} {
  constructor; [ easy | constructor ].

}
Qed.
*)

(*
Compute (transp_list Nat.eqb [3;2;1] [1;2;3]).
Print transp_loop.
Compute (transp_list Nat.eqb [1;2;0] [0;1;2]).
Compute (map (λ la, (la, seq 0 (length la), transp_list Nat.eqb la (seq 0 (length la)))) (canon_sym_gr_list_list 3)).
Compute (map (λ lb, (seq 0 (length lb), lb, transp_list Nat.eqb (seq 0 (length lb)) lb)) (canon_sym_gr_list_list 3)).
Compute (map (λ lb, (seq 0 (length lb), lb, transp_list Nat.eqb (seq 0 (length lb)) lb)) (canon_sym_gr_list_list 4)).
Compute (map (λ lb, length (transp_list Nat.eqb (seq 0 (length lb)) lb)) (canon_sym_gr_list_list 5)).

Fixpoint nb_nfit i l :=
  match l with
  | [] => 0
  | j :: l' => (if i =? j then 0 else 1) + nb_nfit (S i) l'
  end.

Fixpoint transp_loop' it i (p : list nat) :=
  match it with
  | 0 => []
  | S it' =>
      match p with
      | [] => []
      | j :: l =>
          if i =? j then transp_loop' it' (S i) l
          else (i, j) :: transp_loop' it' i (list_swap_elem 0 p 0 (j - i))
      end
  end.

(* works only if p is a permutation of {0..n-1} *)
Definition transp_list' p := transp_loop' (length p + nb_nfit 0 p) 0 p.

Compute (map (λ p, (p, nat_transp_list p, transp_list' p)) (canon_sym_gr_list_list 3)).
(* ([1; 2; 0], [(0, 1); (1, 2)], [(0, 1); (0, 2)]) *)
Compute (map (λ p, (p, rev (nat_transp_list p), transp_list' p)) (canon_sym_gr_list_list 3)).
(* ([1; 2; 0], [(1, 2); (0, 1)], [(0, 1); (0, 2)]) *)
Compute (map (λ p, (p, transp_list Nat.eqb p (seq 0 (length p)), transp_list' p)) (canon_sym_gr_list_list 3)).
(* ([1; 2; 0], [(0, 2); (1, 2)], [(0, 1); (0, 2)]) *)
Compute (map (λ p, (p, rev (transp_list Nat.eqb p (seq 0 (length p))), transp_list' p)) (canon_sym_gr_list_list 3)).
(* ([1; 2; 0], [(1, 2); (0, 2)], [(0, 1); (0, 2)]) *)
...
*)

Notation "'Comp' n ( i ∈ l ) , g" :=
  (iter_list l (λ c i, c ° g) (seq 0 n))
  (at level 35, i at level 0, l at level 60, n at level 0).

(* seems to work; property to prove:
Compute (map (λ p, (p, Comp (length p) (ij ∈ nat_transp_list p), swap (length p) (fst ij) (snd ij))) (canon_sym_gr_list_list 4)).
Compute (map (λ p, list_eqb Nat.eqb p (Comp (length p) (ij ∈ nat_transp_list p), swap (length p) (fst ij) (snd ij))) (canon_sym_gr_list_list 5)).
*)

Theorem swap_id : ∀ n k, swap n k k = seq 0 n.
Proof.
intros.
unfold swap, list_swap_elem.
erewrite map_ext_in. 2: {
  rewrite seq_length.
  intros i Hi.
  apply in_seq in Hi.
  rewrite transposition_id.
  now rewrite seq_nth.
}
rewrite seq_length.
induction n; [ easy | ].
rewrite seq_S; cbn.
rewrite map_app; cbn; f_equal.
apply IHn.
Qed.

Theorem ε_seq : ∀ sta len, ε (seq sta len) = 1%F.
Proof.
intros.
destruct (Nat.eq_dec len 0) as [Hnz| Hnz]. {
  subst len; cbn.
  unfold ε; cbn.
  unfold iter_seq, iter_list; cbn.
  now do 2 rewrite rngl_mul_1_l.
}
unfold ε.
rewrite seq_length.
unfold sign_diff.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite seq_nth; [ | flia Hj Hnz ].
    rewrite seq_nth; [ | flia Hi Hnz ].
    replace (if _ <? _ then _ else _) with 1%F. 2: {
      symmetry.
      rewrite if_ltb_lt_dec.
      destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
      apply Nat.add_lt_mono_l with (p := sta) in Hij.
      now apply Nat.compare_gt_iff in Hij; rewrite Hij.
    }
    easy.
  }
  easy.
}
apply all_1_rngl_product_1.
intros i Hi.
now apply all_1_rngl_product_1.
Qed.

Theorem ε_swap_id : ∀ n k, ε (swap n k k) = 1%F.
Proof.
intros.
rewrite swap_id.
apply ε_seq.
Qed.

Theorem is_square_matrix_map : ∀ A B (f : list A → list B) ll n,
  mat_nrows (mk_mat ll) = n
  → (∀ la, la ∈ ll → length (f la) = n)
  → is_square_matrix (mk_mat (map f ll)) = true.
Proof.
intros * Hr Hf.
apply is_scm_mat_iff; cbn in Hr |-*.
rewrite map_length.
split. {
  intros Hc.
  unfold mat_ncols in Hc; cbn in Hc.
  apply length_zero_iff_nil in Hc.
  destruct ll as [| l]; [ easy | exfalso ].
  cbn in Hc.
  specialize (Hf l (or_introl eq_refl)).
  now rewrite Hc, <- Hr in Hf.
} {
  intros l Hl.
  apply in_map_iff in Hl.
  destruct Hl as (a & Hfa & Ha).
  subst l.
  now rewrite Hr, Hf.
}
Qed.

Theorem fold_left_mk_mat : ∀ A (M : matrix T) (f : _ → A → _) l,
  fold_left (λ M a, mk_mat (f (mat_list_list M) a)) l M =
  mk_mat (fold_left f l (mat_list_list M)).
Proof.
intros.
destruct M as (ll); cbn.
revert ll.
induction l as [| a]; intros; [ easy | cbn ].
apply IHl.
Qed.

(*
Theorem transp_loop_nil : ∀ it i, transp_loop it i [] = [].
Proof. intros; now destruct it. Qed.
*)

Theorem nth_list_swap_elem : ∀ A (d : A) i j l,
  i < length l
  → j < length l
  → nth j (list_swap_elem d l i j) d = nth i l d.
Proof.
intros * Hil Hjl.
unfold list_swap_elem.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
now rewrite transposition_2.
Qed.

(*
Theorem transp_loop_seq : ∀ it sta len,
  transp_loop it sta (seq sta len) = [].
Proof.
intros.
revert sta len.
induction it; intros; cbn; [ easy | ].
destruct len; [ easy | cbn ].
rewrite Nat.eqb_refl.
apply IHit.
Qed.

Theorem transp_loop_app_seq_gen : ∀ it s i la,
  transp_loop it (s + i) la = transp_loop (it + i) s (seq s i ++ la).
Proof.
intros.
revert i s la.
induction it; intros. {
  cbn.
  revert s la.
  induction i; intros; [ easy | cbn ].
  rewrite Nat.eqb_refl.
  apply IHi.
}
cbn - [ seq "=?" ].
destruct la as [| a]. {
  rewrite app_nil_r.
  destruct i; [ easy | cbn ].
  rewrite Nat.eqb_refl.
  symmetry; apply transp_loop_seq.
}
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (s + i) a) as [Hia| Hia]. {
  subst a.
  rewrite List_app_cons, app_assoc, <- seq_S; cbn.
  rewrite Nat.eqb_refl.
  rewrite <- Nat.add_succ_r.
  rewrite IHit.
  rewrite Nat.add_succ_r; cbn.
  now rewrite Nat.eqb_refl.
}
remember (seq s i ++ a :: la) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; [ now destruct i | ].
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec s b) as [Hsb| Hsb]. 2: {
  destruct i. {
    do 2 rewrite Nat.add_0_r.
    cbn in Hlb.
    now injection Hlb; clear Hlb; intros; subst b lb.
  }
  cbn in Hlb.
  now injection Hlb; clear Hlb; intros.
}
subst b.
clear IHit.
revert it s a la lb Hia Hlb.
induction i; intros. {
  rewrite Nat.add_0_r in Hia.
  cbn in Hlb.
  now injection Hlb; clear Hlb; intros; subst a lb.
}
cbn in Hlb.
injection Hlb; clear Hlb; intros Hlb.
subst lb.
rewrite (Nat.add_succ_r it).
cbn - [ list_swap_elem seq "=?" ].
remember (seq (S s) i ++ a :: la) as lb eqn:Hb.
symmetry in Hb.
destruct lb as [| b]; [ now destruct i | ].
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (S s) b) as [Hsb| Hsb]. {
  subst b.
  rewrite <- Nat.add_succ_comm in Hia |-*.
  now apply IHi.
}
rewrite <- Nat.add_succ_comm, Nat.add_comm.
f_equal. {
  destruct i. {
    cbn in Hb.
    now injection Hb; clear Hb; intros; subst b lb.
  }
  cbn in Hb.
  now injection Hb; clear Hb; intros.
}
destruct i. {
  cbn in Hb.
  rewrite Nat.add_0_l, Nat.add_0_r.
  now injection Hb; clear Hb; intros; subst b lb.
}
cbn in Hb.
now injection Hb; clear Hb; intros; subst b lb.
Qed.

Theorem transp_loop_app_seq : ∀ it i la,
  transp_loop it i la = transp_loop (it + i) 0 (seq 0 i ++ la).
Proof.
intros.
now rewrite <- transp_loop_app_seq_gen.
Qed.
*)

Theorem list_swap_elem_id : ∀ A (d : A) l i, list_swap_elem d l i i = l.
Proof.
intros.
unfold list_swap_elem.
rewrite List_map_nth_seq with (d := d).
apply map_ext_in.
intros j Hj.
now rewrite transposition_id.
Qed.

Theorem List_fold_left_max : ∀ a b la lb,
  a ≤ b
  → Max (i ∈ la), i ≤ Max (i ∈ lb), i
  → fold_left max la a ≤ fold_left max lb b.
Proof.
intros * Hab Hm.
unfold iter_list in Hm.
rewrite List_fold_left_ext_in with (g := max) in Hm by easy.
rewrite List_fold_left_ext_in with (g := max) (l := lb) in Hm by easy.
rewrite fold_left_max_from_0.
rewrite fold_left_max_from_0 with (l := lb).
now apply Nat.max_le_compat.
Qed.

Theorem le_fold_left_max : ∀ a b la,
  a ≤ b ∨ (∃ c, c ∈ la ∧ a ≤ c)
  ↔ a ≤ fold_left max la b.
Proof.
intros.
split. {
  intros Hab.
  revert a b Hab.
  induction la as [| c]; intros. {
    destruct Hab as [Hab| Hab]; [ easy | ].
    now destruct Hab.
  }
  cbn.
  apply IHla.
  destruct Hab as [Hab| Hab]. {
    left.
    transitivity b; [ easy | ].
    apply Nat.le_max_l.
  }
  destruct Hab as (d & Hd & Had).
  destruct Hd as [Hd| Hd]. {
    subst d; left.
    transitivity c; [ easy | ].
    apply Nat.le_max_r.
  }
  right.
  now exists d.
} {
  intros Hab.
  revert a b Hab.
  induction la as [| c]; intros; [ now left | ].
  cbn in Hab.
  apply IHla in Hab.
  destruct Hab as [Hab| Hab]. {
    destruct (le_dec b c) as [Hbc| Hbc]. {
      rewrite Nat.max_r in Hab; [ | easy ].
      right.
      exists c.
      split; [ now left | easy ].
    }
    apply Nat.nle_gt, Nat.lt_le_incl in Hbc.
    rewrite Nat.max_l in Hab; [ | easy ].
    now left.
  }
  destruct Hab as (d & Hd & Had).
  right.
  exists d.
  split; [ now right | easy ].
}
Qed.

Theorem fold_left_max_le : ∀ a b la,
  (∀ c, c ∈ a :: la → c ≤ b)
  → fold_left max la a ≤ b.
Proof.
intros * Hc.
revert a Hc.
induction la as [| d]; intros; [ now apply Hc; left | cbn ].
apply IHla.
intros c Hcad.
destruct Hcad as [Hcad| Hcla]. {
  subst c.
  apply Hc.
  destruct (le_dec a d) as [H1| H1]. {
    rewrite Nat.max_r; [ | easy ].
    now right; left.
  }
  apply Nat.nle_gt, Nat.lt_le_incl in H1.
  rewrite Nat.max_l; [ | easy ].
  now left.
}
apply Hc.
now right; right.
Qed.

(*
Theorem in_transp_loop_bounds : ∀ it k l i j,
  (i, j) ∈ transp_loop it k l
  → k ≤ i < k + length l ∧ j ≤ Max (u ∈ l), u.
Proof.
intros * Hij.
revert i j k l Hij.
induction it; intros; [ easy | cbn in Hij ].
destruct l as [| v]; [ easy | ].
rewrite if_eqb_eq_dec in Hij.
destruct (Nat.eq_dec k v) as [Hkv| Hkv]. {
  subst v.
  specialize (IHit _ _ _ _ Hij) as H1.
  destruct H1 as ((H1, H2), H3).
  rewrite Nat.add_succ_comm in H2.
  split. {
    split; [ | easy ].
    destruct (Nat.eq_dec (S k) i) as [Hkij| Hkij]; [ | flia H1 Hkij ].
    rewrite <- Hkij.
    apply Nat.le_succ_diag_r.
  }
  rewrite iter_list_cons'.
  etransitivity; [ apply H3 | ].
  unfold iter_list at 2.
  rewrite fold_left_max_from_0.
  rewrite fold_iter_list.
  apply Nat.le_max_r.
}
destruct Hij as [Hij| Hij]. {
  injection Hij; clear Hij; intros; subst k v; cbn.
  split. {
    split; [ easy | flia ].
  }
  rewrite iter_list_cons'.
  unfold iter_list.
  rewrite fold_left_max_from_0.
  rewrite fold_iter_list.
  apply Nat.le_max_l.
}
specialize (IHit _ _ _ _ Hij) as H1.
destruct H1 as (H1, H2).
split. {
  now rewrite list_swap_elem_length in H1.
}
etransitivity; [ apply H2 | ].
unfold iter_list.
rewrite List_fold_left_ext_in with (g := max) by easy.
remember (fold_left max (list_swap_elem _ _ _ _) _) as x.
rewrite List_fold_left_ext_in with (g := max) by easy; subst x.
remember (v :: l) as l'.
remember (v - k) as x.
clear; rename l' into l.
rename x into i.
assert (H : ∀ i a l,
  fold_left max (list_swap_elem 0 l 0 i) a ≤ fold_left max l a). {
  clear l i.
  intros.
  apply fold_left_max_le.
  intros * Hc.
  destruct Hc as [Hc| Hc]. {
    subst c.
    now apply le_fold_left_max; left.
  }
  unfold list_swap_elem in Hc.
  apply in_map_iff in Hc.
  destruct Hc as (b & Hbc & Hb).
  apply in_seq in Hb; destruct Hb as (_, Hb); cbn in Hb.
  subst c.
  destruct (lt_dec i (length l)) as [Hil| Hil]. 2: {
    apply Nat.nlt_ge in Hil.
    unfold transposition.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
      now rewrite nth_overflow.
    }
    destruct (Nat.eq_dec b i) as [H| H]; [ flia H Hb Hil | ].
    apply le_fold_left_max.
    right.
    exists (nth b l 0).
    split; [ | easy ].
    now apply nth_In.
  }
  apply le_fold_left_max.
  right.
  exists (nth (transposition 0 i b) l 0).
  split; [ | easy ].
  apply nth_In.
  apply transposition_lt; [ flia Hb | easy | easy ].
}
apply H.
Qed.

Theorem in_transp_list_bounds : ∀ i j l,
  (i, j) ∈ transp_list l
  → i < length l ∧ j ≤ Max (u ∈ l), u.
Proof.
intros * Hij.
unfold transp_list in Hij.
specialize (in_transp_loop_bounds) as H1.
specialize (H1 _ _ _ _ _ Hij).
now destruct H1 as ((_, H1), H2).
Qed.
*)

Theorem app_seq_swap_permut_seq : ∀ i j l,
  permut_seq (seq 0 i ++ j :: l)
  → i < j
  → permut_seq (seq 0 i ++ list_swap_elem 0 (j :: l) 0 (j - i)).
Proof.
(*
intros * Hp Hilj.
unfold permut_seq.
rewrite app_length, seq_length, list_swap_elem_length.
rewrite seq_app, Nat.add_0_l.
apply (permutation_app_head Nat.eqb_eq).
unfold permut_seq in Hp.
rewrite app_length, seq_length, seq_app, Nat.add_0_l in Hp.
apply (permutation_app_inv_l Nat.eqb_eq) in Hp.
Search (permut_seq (list_swap_elem _ _ _ _)).
rewrite <- list_swap_elem_length with (d := 0) (p := 0) (q := j - i).
Check list_swap_elem_permut_seq.
...
Definition permut_seq l := permutation Nat.eqb l (seq 0 (length l)).
Search permut_seq.
...
rewrite app_length, seq_length in Hp; cbn in Hp.
Search (seq _ (_ + _)).
...
*)
intros * Hp Hilj.
apply permut_seq_iff.
split. {
  intros k Hk.
  rewrite app_length, seq_length, list_swap_elem_length; cbn.
  apply in_app_or in Hk.
  destruct Hk as [Hk| Hk]; [ apply in_seq in Hk; flia Hk | ].
  unfold list_swap_elem in Hk.
  rewrite in_map_iff in Hk.
  destruct Hk as (u & Huk & Hu).
  subst k.
  apply in_seq in Hu; cbn in Hu.
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec u 0) as [Huz| Huz]. {
    subst u.
    apply permut_seq_iff in Hp.
    destruct Hp as (Hpp, Hpl).
    rewrite app_length, seq_length in Hpp; cbn in Hpp.
    specialize (Hpp (nth (j - i) (j :: l) 0)) as H2.
    apply H2; clear H2.
    apply in_or_app.
    right; right.
    rewrite Nat_succ_sub_succ_r; [ cbn | easy ].
    apply nth_In.
    specialize (Hpp j) as H2.
    assert (H : j ∈ seq 0 i ++ j :: l). {
      apply in_or_app.
      now right; left.
    }
    specialize (H2 H); clear H.
    cbn in H2.
    flia H2 Hilj.
  }
  destruct (Nat.eq_dec u (j - i)) as [Huj| Huj]. {
    subst u; cbn; flia Hu.
  }
  destruct u; [ easy | ].
  cbn.
  apply permut_seq_iff in Hp.
  destruct Hp as (Hpp, Hpl).
  rewrite app_length, seq_length in Hpp; cbn in Hpp.
  apply Hpp, in_or_app.
  destruct (lt_dec (nth u l 0) i) as [Hui| Hui]. {
    now left; apply in_seq.
  }
  right.
  apply Nat.nlt_ge in Hui.
  destruct (Nat.eq_dec (nth u l 0) j) as [Hnuj| Hnuj]. {
    now rewrite Hnuj; left.
  }
  right.
  apply nth_In.
  destruct Hu as (_, Hu).
  now apply Nat.succ_lt_mono.
} {
  apply nat_NoDup.
  rewrite app_length, seq_length, list_swap_elem_length.
  cbn - [ list_swap_elem ].
  intros u v Hu Hv Huv.
  destruct (lt_dec u i) as [Hui| Hui]. {
    rewrite app_nth1 in Huv; [ | now rewrite seq_length ].
    rewrite seq_nth in Huv; [ | easy ].
    rewrite Nat.add_0_l in Huv.
    destruct (lt_dec v i) as [Hvi| Hvi]. {
      rewrite app_nth1 in Huv; [ | now rewrite seq_length ].
      rewrite seq_nth in Huv; [ | easy ].
      easy.
    }
    apply Nat.nlt_ge in Hvi; exfalso.
    rewrite app_nth2 in Huv; [ | now rewrite seq_length ].
    rewrite seq_length in Huv.
    rewrite Huv in Hui.
    apply Nat.nle_gt in Hui.
    apply Hui; clear Hui.
    unfold list_swap_elem.
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length; cbn; flia Hv.
    }
    rewrite seq_nth; [ | cbn; flia Hv ].
    rewrite Nat.add_0_l.
    unfold transposition.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (v - i) 0) as [Hviz| Hviz]. {
      rewrite Nat_succ_sub_succ_r; [ | easy ].
      rewrite List_nth_succ_cons.
      apply Nat.sub_0_le in Hviz.
      apply Nat.le_antisymm in Hvi; [ subst v | easy ].
      clear Hviz Hv.
      rewrite Nat.sub_diag in Huv.
      unfold list_swap_elem in Huv.
      rewrite (List_map_nth' 0) in Huv; [ | now rewrite seq_length; cbn ].
      rewrite seq_nth in Huv; [ | now cbn ].
      unfold transposition in Huv.
      rewrite Nat.eqb_refl in Huv.
      rewrite Nat_succ_sub_succ_r in Huv; [ | easy ].
      rewrite List_nth_succ_cons in Huv.
      rewrite <- Huv.
      apply permut_seq_iff in Hp.
      destruct Hp as (Hpp, Hpl).
      rewrite app_length, seq_length in Hpp; cbn in Hpp.
      assert (Hj : j ∈ seq (S i) (length l)). {
        apply in_seq.
        split; [ easy | cbn ].
        rewrite <- Nat.add_succ_r.
        apply (Hpp j).
        now apply in_or_app; right; left.
      }
      assert (Hul : u ∈ l). {
        rewrite Huv.
        apply nth_In.
        apply in_seq in Hj.
        flia Hj.
      }
      assert (Hus : u ∉ seq 0 i). {
        intros H.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply Hnjl in H.
        now apply H; right.
      }
      apply Nat.nlt_ge; intros H; apply Hus; clear Hus.
      now apply in_seq.
    }
    destruct (Nat.eq_dec (v - i) (j - i)) as [Hvji| Hvji]. {
      now apply Nat.lt_le_incl.
    }
    rewrite Nat_succ_sub_succ_r; [ | flia Hvi Hviz ].
    rewrite List_nth_succ_cons.
    apply permut_seq_iff in Hp.
    destruct Hp as (Hpp, Hpl).
    rewrite app_length, seq_length in Hpp; cbn in Hpp.
    unfold list_swap_elem in Huv.
    rewrite (List_map_nth' 0) in Huv. 2: {
      rewrite seq_length; cbn; flia Hv.
    }
    rewrite seq_nth in Huv; [ | cbn; flia Hv ].
    unfold transposition in Huv.
    rewrite Nat.add_0_l in Huv.
    rewrite Nat_succ_sub_succ_r in Huv at 1; [ | flia Hviz ].
    replace (S (v - S i) =? 0) with false in Huv by easy.
    apply Nat.eqb_neq in Hvji; rewrite Hvji in Huv.
    rewrite Nat_succ_sub_succ_r in Huv at 1; [ | flia Hviz ].
    rewrite List_nth_succ_cons in Huv.
    rewrite <- Huv.
    assert (Hul : u ∈ l). {
      rewrite Huv.
      apply nth_In.
      flia Hv Hviz.
    }
    assert (Hus : u ∉ seq 0 i). {
      intros H.
      apply NoDup_app_iff in Hpl.
      destruct Hpl as (Hil & Hjl & Hnjl).
      apply Hnjl in H.
      now apply H; right.
    }
    apply Nat.nlt_ge; intros H; apply Hus; clear Hus.
    now apply in_seq.
  }
  apply Nat.nlt_ge in Hui.
  rewrite app_nth2 in Huv; [ | now rewrite seq_length ].
  rewrite seq_length in Huv.
  destruct (lt_dec v i) as [Hvi| Hvi]. 2: {
    apply Nat.nlt_ge in Hvi.
    rewrite app_nth2 in Huv; [ | now rewrite seq_length ].
    rewrite seq_length in Huv.
    unfold list_swap_elem in Huv.
    rewrite (List_map_nth' 0) in Huv; [ | rewrite seq_length; cbn; flia Hu ].
    rewrite (List_map_nth' 0) in Huv; [ | rewrite seq_length; cbn; flia Hv ].
    rewrite seq_nth in Huv; [ | cbn; flia Hu ].
    rewrite seq_nth in Huv; [ | cbn; flia Hv ].
    do 2 rewrite Nat.add_0_l in Huv.
    unfold transposition in Huv.
    do 4 rewrite if_eqb_eq_dec in Huv.
    destruct (Nat.eq_dec (u - i) 0) as [Huiz| Huiz]. {
      apply Nat.sub_0_le in Huiz.
      apply Nat.le_antisymm in Huiz; [ | easy ].
      subst u; clear Hu Hui.
      destruct (Nat.eq_dec (v - i) 0) as [Hviz| Hviz]. {
        apply Nat.sub_0_le in Hviz.
        now apply Nat.le_antisymm.
      }
      destruct (Nat.eq_dec (v - i) (j - i)) as [Hvij| Hvij]. {
        rewrite <- Hvij in Huv.
        rewrite Nat_succ_sub_succ_r in Huv; [ | flia Hviz Hvi ].
        rewrite List_nth_succ_cons in Huv.
        rewrite List_nth_0_cons in Huv.
        assert (H : v = j) by flia Hvij Hviz.
        subst v; clear Hvij Hviz.
        apply permut_seq_iff in Hp.
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        assert (Hul : j ∈ l). {
          rewrite <- Huv.
          apply nth_In.
          flia Hv Hilj.
        }
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        easy.
      }
      apply permut_seq_iff in Hp.
      destruct Hp as (Hpp, Hpl).
      rewrite app_length, seq_length in Hpp; cbn in Hpp.
      apply NoDup_app_iff in Hpl.
      destruct Hpl as (Hil & Hjl & Hnjl).
      apply Nat.neq_sym in Hvij.
      apply (NoDup_nat _ Hjl) in Huv; [ easy | cbn | cbn; flia Hv ].
      specialize (Hpp j) as H1.
      assert (H : j ∈ seq 0 i ++ j :: l). {
        now apply in_or_app; right; left.
      }
      specialize (H1 H); clear H.
      flia H1.
    }
    destruct (Nat.eq_dec (u - i) (j - i)) as [Huji| Huji]. {
      rewrite List_nth_0_cons in Huv.
      assert (H : u = j) by flia Huji Huiz.
      subst u.
      clear Hui Huji Huiz Hui.
      destruct (Nat.eq_dec (v - i) 0) as [Hviz| Hviz]. {
        assert (H : v = i) by flia Hviz Hvi; subst v.
        clear Hvi Hviz Hv.
        rewrite Nat_succ_sub_succ_r in Huv; [ | easy ].
        rewrite List_nth_succ_cons in Huv.
        assert (Hul : j ∈ l). {
          rewrite Huv.
          apply nth_In.
          flia Hu Hilj.
        }
        apply permut_seq_iff in Hp.
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        easy.
      }
      destruct (Nat.eq_dec (v - i) (j - i)) as [Hvji| Hvji]. {
        flia Hvji Hviz.
      }
      rewrite Nat_succ_sub_succ_r in Huv; [ | flia Hviz ].
      rewrite List_nth_succ_cons in Huv.
      assert (Hul : j ∈ l). {
        rewrite Huv.
        apply nth_In.
        flia Hv Hviz.
      }
      apply permut_seq_iff in Hp.
      destruct Hp as (Hpp, Hpl).
      rewrite app_length, seq_length in Hpp; cbn in Hpp.
      apply NoDup_app_iff in Hpl.
      destruct Hpl as (Hil & Hjl & Hnjl).
      apply NoDup_cons_iff in Hjl.
      easy.
    } {
      rewrite Nat_succ_sub_succ_r in Huv; [ | flia Hui Huiz ].
      rewrite List_nth_succ_cons in Huv.
      destruct (Nat.eq_dec (v - i) 0) as [Hviz| Hviz]. {
        assert (H : v = i) by flia Hviz Hvi; subst v.
        clear Hvi Hviz Hv.
        rewrite (@Nat_succ_sub_succ_r j i) in Huv; [ | easy ].
        rewrite List_nth_succ_cons in Huv.
        apply permut_seq_iff in Hp.
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        destruct Hjl as (Hjl & Hl).
        apply (NoDup_nat _ Hl) in Huv; cycle 1. {
          flia Hu Huiz.
        } {
          specialize (Hpp j) as H1.
          assert (H : j ∈ seq 0 i ++ j :: l). {
            now apply in_or_app; right; left.
          }
          specialize (H1 H); clear H.
          flia H1 Hilj.
        }
        flia Huiz Huv Hilj Huji.
      }
      destruct (Nat.eq_dec (v - i) (j - i)) as [Hvji| Hvji]. {
        cbn in Huv.
        assert (H : v = j) by flia Hviz Hvji; subst v.
        clear Hvji Hviz.
        assert (Hul : j ∈ l). {
          rewrite <- Huv.
          apply nth_In.
          flia Hu Huiz.
        }
        apply permut_seq_iff in Hp.
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        easy.
      } {
        rewrite (@Nat_succ_sub_succ_r v i) in Huv; [ | flia Hviz ].
        rewrite List_nth_succ_cons in Huv.
        apply permut_seq_iff in Hp.
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        destruct Hjl as (Hjl & Hl).
        apply (NoDup_nat _ Hl) in Huv; cycle 1. {
          flia Hu Huiz.
        } {
          flia Hv Hviz.
        }
        flia Huv Hui Hvi Huiz Hviz.
      }
    }
  } {
    exfalso.
    clear Hv.
    rewrite app_nth1 in Huv; [ | now rewrite seq_length ].
    rewrite seq_nth in Huv; [ | easy ].
    rewrite Nat.add_0_l in Huv.
    rewrite <- Huv in Hvi; clear Huv.
    unfold list_swap_elem in Hvi.
    rewrite (List_map_nth' 0) in Hvi. 2: {
      rewrite seq_length; cbn; flia Hu.
    }
    rewrite seq_nth in Hvi; [ | cbn; flia Hu ].
    rewrite Nat.add_0_l in Hvi.
    apply permut_seq_iff in Hp.
    destruct Hp as (Hpp, Hpl).
    rewrite app_length, seq_length in Hpp; cbn in Hpp.
    apply NoDup_app_iff in Hpl.
    destruct Hpl as (Hil & Hjl & Hnjl).
    remember (nth _ _ _) as k eqn:Hk.
    assert (H1 : k ∈ seq 0 i) by now apply in_seq.
    apply Hnjl in H1; apply H1; clear H1.
    rewrite Hk.
    apply nth_In; cbn.
    unfold transposition.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (u - i) 0) as [Huiz| Huiz]. {
      specialize (Hpp j) as H1.
      assert (H : j ∈ seq 0 i ++ j :: l). {
        now apply in_or_app; right; left.
      }
      specialize (H1 H); clear H.
      flia H1.
    }
    destruct (Nat.eq_dec (u - i) (j - i)) as [Huji| Huji]; [ easy | ].
    flia Hu.
  }
}
Qed.

(*
Theorem nb_nfit_app : ∀ i la lb,
  nb_nfit i (la ++ lb) = nb_nfit i la + nb_nfit (i + length la) lb.
Proof.
intros.
revert i lb.
induction la as [| j]; intros; [ now rewrite Nat.add_0_r | cbn ].
now rewrite IHla, Nat.add_assoc, Nat.add_succ_comm.
Qed.

Theorem permut_eq_iter_list_transp_loop : ∀ l it i,
  permut_seq (seq 0 i ++ l)
  → length l + nb_nfit i l ≤ it
  → fold_left (λ l t, l ° swap (length l) (fst t) (snd t))
      (transp_loop it i l) (seq 0 i ++ l) = seq 0 (i + length l).
Proof.
intros * Hp Hit.
revert l i Hp Hit.
induction it; intros; cbn. {
  apply Nat.le_0_r in Hit.
  apply Nat.eq_add_0 in Hit.
  destruct Hit as (Hl & Hnf).
  apply length_zero_iff_nil in Hl; subst l.
  now rewrite app_nil_r, Nat.add_0_r.
}
destruct l as [| j]. {
  now cbn; rewrite app_nil_r, Nat.add_0_r.
}
cbn in Hit.
apply Nat.succ_le_mono in Hit.
rewrite if_eqb_eq_dec in Hit |-*.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  rewrite List_app_cons, app_assoc, <- seq_S.
  rewrite List_cons_length, <- Nat.add_succ_comm.
  apply IHit; [ now rewrite seq_S, <- app_assoc | easy ].
} {
  remember (list_swap_elem 0 (j :: l) 0 (j - i)) as la eqn:Hla.
  assert (Hilj : i < j). {
    apply Nat.nle_gt.
    intros Hc.
    destruct Hp as (Hpp, Hpl).
    specialize (NoDup_nat _ Hpl i j) as H2.
    rewrite app_length, seq_length in H2.
    cbn in H2.
    assert (H : i < i + S (length l)) by flia.
    specialize (H2 H); clear H.
    assert (H : j < i + S (length l)) by flia Hc.
    specialize (H2 H); clear H.
    rewrite app_nth2 in H2; [ | now rewrite seq_length; unfold ge ].
    rewrite seq_length, Nat.sub_diag in H2; cbn in H2.
    rewrite app_nth1 in H2; [ | rewrite seq_length; flia Hij Hc ].
    rewrite seq_nth in H2; [ | flia Hij Hc ].
    now specialize (H2 eq_refl).
  }
  move Hilj before Hij.
  assert (Hji : j - S i < length l). {
    destruct Hp as (Hpp, Hpl).
    specialize (Hpp j) as H2.
    rewrite app_length, seq_length in H2.
    assert (H : j ∈ seq 0 i ++ j :: l). {
      now apply in_or_app; right; left.
    }
    specialize (H2 H); clear H; cbn in H2.
    flia H2 Hilj.
  }
  move Hji before Hilj.
  assert (Hpa : permut_seq (seq 0 i ++ la)). {
    rewrite Hla.
    now apply app_seq_swap_permut_seq.
  }
  specialize (IHit la i Hpa) as H1.
  assert (H : length la + nb_nfit i la ≤ it). {
    rewrite Hla, list_swap_elem_length, List_cons_length.
    rewrite Nat.add_succ_comm.
    etransitivity; [ | apply Hit ].
    apply Nat.add_le_mono_l.
    apply -> Nat.succ_le_mono.
    cbn - [ nth ].
    rewrite <- seq_shift, map_map.
    erewrite map_ext_in. 2: {
      intros u Hu.
      rewrite Nat_succ_sub_succ_r; [ | easy ].
      unfold transposition.
      cbn - [ nth ].
      replace (nth _ _ _) with (if u =? j - S i then j else nth u l 0). 2: {
        do 2 rewrite if_eqb_eq_dec.
        now destruct (Nat.eq_dec u (j - S i)).
      }
      easy.
    }
    enough (H :
      nb_nfit (S i)
        (map (λ u, if u =? j - S i then j else nth u l 0)
           (seq 0 (length l))) <
      nb_nfit (S i) l). {
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec i (nth _ _ _)) as [H2| H2]; [ flia H | easy ].
    }
    remember (λ u, if _ =? _ then _ else _) as f1 eqn:Hf1.
    remember (length l) as len eqn:Hlen.
    rewrite List_map_nth_seq with (la := l) (d := 0).
    subst len f1.
    rewrite List_seq_cut with (i := j - S i); [ | now apply in_seq ].
    rewrite Nat.sub_0_r; cbn.
    do 2 rewrite map_app.
    cbn; rewrite Nat.eqb_refl.
    erewrite map_ext_in. 2: {
      intros k Hk.
      apply in_seq in Hk.
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec k (j - S i)) as [H| H]; [ flia Hk H | ].
      easy.
    }
    do 2 rewrite nb_nfit_app.
    apply Nat.add_lt_mono_l.
    rewrite List_map_seq_length.
    rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
    cbn; rewrite Nat.eqb_refl, Nat.add_0_l.
    erewrite map_ext_in. 2: {
      intros k Hk.
      apply in_seq in Hk.
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec k (j - S i)) as [H| H]; [ flia Hk H | ].
      easy.
    }
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec j (nth (j - S i) l 0)) as [Hjji| Hjji]; [ | flia ].
    exfalso.
    destruct Hp as (Hpp, Hpl).
    apply NoDup_app_iff in Hpl.
    destruct Hpl as (Hil & Hjl & Hnjl).
    apply NoDup_cons_iff in Hjl.
    destruct Hjl as (H2, H3); apply H2.
    rewrite Hjji.
    apply nth_In; flia Hji.
  }
  specialize (H1 H); clear H.
  clear IHit.
  set (g := λ l t, l ° swap (length l) (fst t) (snd t)) in H1 |-*.
  rewrite List_cons_length.
  replace (length la) with (S (length l)) in H1. 2: {
    rewrite Hla.
    now rewrite list_swap_elem_length.
  }
  cbn.
  unfold g at 2.
  rewrite app_length, seq_length.
  cbn.
  unfold "°".
  enough
    (H : seq 0 i ++ la =
     map (λ i0 : nat, nth i0 (seq 0 i ++ j :: l) 0) (swap (i + S (length l)) i j)). {
    now rewrite <- H.
  }
  symmetry.
  rewrite Hla.
  unfold swap.
  unfold list_swap_elem.
  rewrite map_map.
  rewrite seq_length.
  rewrite List_cons_length.
  rewrite List_seq_cut with (i := i). 2: {
    apply in_seq.
    split; [ easy | ].
    flia.
  }
  rewrite Nat.sub_0_r.
  cbn - [ nth seq ].
  rewrite map_app.
  cbn - [ nth seq ].
  f_equal. {
    rewrite List_map_nth_seq with (d := 0).
    rewrite seq_length.
    apply map_ext_in.
    intros k Hk; apply in_seq in Hk.
    rewrite seq_nth; [ | easy ].
    replace (i + S (length l) - S i) with (length l) by flia Hji.
    rewrite Nat.add_0_l.
    unfold transposition.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec k i) as [H| H]; [ flia Hk H | clear H ].
    destruct (Nat.eq_dec k j) as [H| H]; [ flia Hk Hilj H | clear H ].
    remember (seq 0 i ++ j :: l) as x.
    rewrite app_nth1; subst x; [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite app_nth1; [ | now rewrite seq_length ].
    now apply seq_nth.
  }
  cbn - [ nth ].
  f_equal. {
    rewrite transposition_1.
    remember (seq 0 i ++ j :: l) as x.
    rewrite app_nth2; subst x. 2: {
      rewrite seq_length.
      now apply Nat.lt_le_incl.
    }
    rewrite seq_length.
    replace (i + S (length l) - S i) with (length l) by flia Hji.
    replace (i :: seq (S i) (length l)) with (seq i (S (length l))) by easy.
    rewrite app_nth2. 2: {
      rewrite seq_length; unfold ge.
      rewrite seq_nth; [ | flia Hji ].
      flia Hilj.
    }
    rewrite seq_length.
    f_equal.
    rewrite seq_nth; [ now rewrite Nat.add_comm, Nat.add_sub | ].
    flia Hji.
  }
  replace (i + S (length l) - S i) with (length l) by flia Hji.
  symmetry.
  rewrite <- seq_shift, map_map.
  symmetry.
  rewrite List_map_seq.
  apply map_ext_in.
  intros k Hk; apply in_seq in Hk; destruct Hk as (_, Hk); cbn in Hk.
  rewrite List_app_cons, app_assoc, <- seq_S, <- seq_app.
  rewrite (Nat.add_succ_comm _ (length l)).
  unfold transposition.
  replace (S k =? 0) with false by easy.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S i + k) i) as [H| H]; [ flia H | clear H ].
  destruct (Nat.eq_dec (S i + k) j) as [Hsikj| Hsikj]. {
    rewrite seq_nth; [ | flia ].
    rewrite app_nth2; [ | now rewrite seq_length; unfold ge ].
    rewrite seq_length, Nat.sub_diag.
    rewrite List_nth_0_cons.
    rewrite <- Hsikj.
    replace (S i + k - i) with (S k) by flia.
    now rewrite Nat.eqb_refl; cbn.
  }
  rewrite seq_nth. 2: {
    rewrite Nat.add_succ_comm.
    apply Nat.add_lt_mono_l.
    now apply -> Nat.succ_lt_mono.
  }
  rewrite Nat.add_0_l.
  rewrite app_nth2; [ | rewrite seq_length; flia ].
  rewrite seq_length.
  replace (S i + k - i) with (S k) by flia.
  rewrite List_nth_succ_cons.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S k) (j - i)) as [Hskji| Hskji]. {
    replace k with (j - S i) in Hsikj by flia Hskji.
    now rewrite Nat.add_comm, Nat.sub_add in Hsikj.
  }
  now rewrite List_nth_succ_cons.
}
Qed.

Theorem permut_eq_iter_list_transp : ∀ l,
  permut_seq l
  → iter_list (transp_list l) (λ l t, l ° swap (length l) (fst t) (snd t)) l =
    seq 0 (length l).
Proof.
intros * Hp.
unfold iter_list.
unfold transp_list.
specialize permut_eq_iter_list_transp_loop as H1.
specialize (H1 l (length l + nb_nfit 0 l) 0).
apply (H1 Hp (le_refl _)).
Qed.
*)

Theorem permut_list_max : ∀ l,
  permut_seq l
  → Max (i ∈ l), i = length l - 1.
Proof.
intros * Hp.
remember (length l) as n eqn:Hn.
symmetry in Hn.
revert l Hp Hn.
induction n; intros. {
  now apply length_zero_iff_nil in Hn; subst l.
}
rewrite Nat_sub_succ_1.
specialize permut_without_highest as H1.
specialize (H1 n l).
assert (H : permut_seq_with_len (S n) l) by easy.
specialize (H1 H); clear H.
destruct H1 as (j & Hj & Hjn & Hpj & Hpjl).
specialize (nth_split _ 0 Hj) as H1.
destruct H1 as (l1 & l2 & Hll & Hlj).
rewrite Hjn in Hll.
rewrite Hll.
rewrite max_list_app, max_list_cons.
rewrite (Nat.max_comm n).
rewrite Nat.max_assoc.
rewrite <- max_list_app.
assert (Hb : butn j l = l1 ++ l2). {
  unfold butn.
  rewrite Hll.
  rewrite firstn_app.
  rewrite Hlj, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite <- Hlj, firstn_all.
  rewrite List_app_cons, app_assoc, skipn_app.
  rewrite app_length, Nat.add_1_r, Nat.sub_diag.
  rewrite skipn_O.
  replace (S (length l1)) with (length (l1 ++ [n])). 2: {
    now rewrite app_length, Nat.add_1_r.
  }
  now rewrite skipn_all, app_assoc, app_nil_r.
}
rewrite Hb in Hpj, Hpjl.
rewrite IHn; [ | easy | easy ].
apply Nat.max_r; flia.
Qed.

Theorem list_swap_elem_firstn_skipn : ∀ A (d : A) i j l,
  i < j < length l
  → list_swap_elem d l i j =
     firstn i l ++ [nth j l d] ++
     firstn (j - S i) (skipn (S i) l) ++ [nth i l d] ++ skipn (S j) l.
Proof.
intros * Hij.
unfold list_swap_elem.
replace (length l) with (i + (length l - i)) by flia Hij.
rewrite seq_app, map_app.
f_equal. {
  erewrite map_ext_in. 2: {
    intros k Hk; apply in_seq in Hk; cbn in Hk; destruct Hk as (_, Hk).
    unfold transposition.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec k i) as [H| H]; [ flia Hk H | clear H ].
    destruct (Nat.eq_dec k j) as [H| H]; [ flia Hij Hk H | clear H ].
    easy.
  }
  assert (Hi : i < length l) by flia Hij.
  clear j Hij.
  symmetry.
  now apply List_firstn_map_nth_seq.
}
rewrite Nat_succ_sub_succ_r; [ | flia Hij ].
cbn - [ skipn ].
f_equal. {
  unfold transposition.
  now rewrite Nat.eqb_refl.
}
replace (length l - S i) with ((j - S i) + (length l - j)) by flia Hij.
rewrite seq_app, map_app.
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
f_equal. {
  symmetry.
  rewrite List_firstn_map_nth_seq with (d := d). 2: {
    rewrite skipn_length; flia Hij.
  }
  symmetry.
  rewrite <- List_seq_shift', map_map.
  apply map_ext_in.
  intros k Hk; apply in_seq in Hk; cbn in Hk; destruct Hk as (_, Hk).
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S i + k) i) as [H| H]; [ flia H | clear H ].
  destruct (Nat.eq_dec (S i + k) j) as [H| H]; [ flia H Hk | clear H ].
  now rewrite List_nth_skipn, Nat.add_comm.
}
rewrite <- List_seq_shift', map_map.
rewrite Nat_succ_sub_succ_r; [ | easy ].
cbn - [ skipn ].
rewrite Nat.add_0_r, transposition_2; f_equal.
rewrite <- seq_shift, map_map.
symmetry.
erewrite map_ext_in. 2: {
  intros k Hk; apply in_seq in Hk; cbn in Hk; destruct Hk as (_, Hk).
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (j + S k) i) as [H| H]; [ flia H | clear H ].
  destruct (Nat.eq_dec (j + S k) j) as [H| H]; [ flia H | clear H ].
  rewrite Nat.add_comm, Nat.add_succ_comm.
  easy.
}
apply List_skipn_map_nth_seq.
Qed.

Theorem skipn_cons_skipn_succ : ∀ A (d : A) l i,
  i < length l
  → skipn i l = nth i l d :: skipn (S i) l.
Proof.
intros * Hi.
revert i Hi.
induction l as [| j]; intros; [ easy | cbn ].
destruct i; [ easy | ].
cbn in Hi.
apply Nat.succ_lt_mono in Hi.
now apply IHl.
Qed.

(*
Theorem transp_loop_enough_iter : ∀ it1 it2 i p,
  permut_seq (seq 0 i ++ p)
  → length p + nb_nfit i p ≤ it1
  → length p + nb_nfit i p ≤ it2
  → transp_loop it1 i p = transp_loop it2 i p.
Proof.
intros * Hp Hit1 Hit2.
revert i p Hp it2 Hit1 Hit2.
induction it1; intros; cbn. {
  apply Nat.le_0_r, Nat.eq_add_0 in Hit1.
  destruct Hit1 as (H1, H2).
  apply length_zero_iff_nil in H1; subst p.
  symmetry; apply transp_loop_nil.
}
destruct p as [| j l]. {
  symmetry; apply transp_loop_nil.
}
cbn in Hit1, Hit2.
rewrite if_eqb_eq_dec in Hit1, Hit2 |-*.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j; cbn.
  destruct it2; [ cbn in Hit2; flia Hit2 | ].
  cbn in Hit1, Hit2 |-*.
  apply Nat.succ_le_mono in Hit1, Hit2.
  rewrite Nat.eqb_refl.
  apply IHit1; [ | easy | easy ].
  now rewrite seq_S, <- app_assoc.
}
assert (Hilj : i < j). {
  apply Nat.nle_gt.
  intros Hc.
  destruct Hp as (Hpp, Hpl).
  specialize (NoDup_nat _ Hpl i j) as H2.
  rewrite app_length, seq_length in H2.
  cbn in H2.
  assert (H : i < i + S (length l)) by flia.
  specialize (H2 H); clear H.
  assert (H : j < i + S (length l)) by flia Hc.
  specialize (H2 H); clear H.
  rewrite app_nth2 in H2; [ | now rewrite seq_length; unfold ge ].
  rewrite seq_length, Nat.sub_diag in H2; cbn in H2.
  rewrite app_nth1 in H2; [ | rewrite seq_length; flia Hij Hc ].
  rewrite seq_nth in H2; [ | flia Hij Hc ].
  now specialize (H2 eq_refl).
}
move Hilj before Hij.
assert (Hjil : j < i + S (length l)). {
  destruct Hp as (Hpa, Hpn).
  rewrite app_length, seq_length in Hpa.
  specialize (Hpa j) as H1.
  now apply H1, in_or_app; right; left.
}
move Hjil before Hilj.
cbn in Hit1, Hit2.
destruct it2; [ flia Hit2 | ].
cbn - [ list_swap_elem ].
apply Nat.succ_le_mono in Hit1, Hit2.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i j) as [H| H]; [ flia Hij H | clear H ].
f_equal.
rewrite Nat.add_succ_r in Hit1, Hit2.
assert
  (H : nb_nfit i (list_swap_elem 0 (j :: l) 0 (j - i)) ≤ nb_nfit (S i) l). {
  clear Hij it1 it2 IHit1 Hit1 Hit2.
  cbn - [ nth ].
  rewrite Nat_succ_sub_succ_r; [ | easy ].
  rewrite List_nth_succ_cons.
  rewrite <- seq_shift, map_map.
  erewrite map_ext_in. 2: {
    intros k Hk.
    unfold transposition.
    replace (nth _ _ _) with (if k =? j - S i then j else nth k l 0). 2: {
      cbn.
      do 2 rewrite if_eqb_eq_dec.
      now destruct (Nat.eq_dec k (j - S i)).
    }
    easy.
  }
  rewrite if_eqb_eq_dec.
  remember (if Nat.eq_dec _ _ then _ else _) as x eqn:Hx.
  rewrite List_seq_cut with (i := j - S i). 2: {
    apply in_seq.
    split; [ easy | ].
    flia Hilj Hjil.
  }
  rewrite Nat.sub_0_r, Nat.add_0_l.
  rewrite map_app; cbn.
  rewrite Nat.eqb_refl.
  rewrite nb_nfit_app.
  rewrite List_map_seq_length.
  rewrite (Nat.add_comm (S i)), Nat.sub_add; [ | easy ].
  cbn; rewrite Nat.eqb_refl, Nat.add_0_l.
  specialize nth_split as H1.
  specialize (H1 _ (j - S i) l 0).
  assert (H : j - S i < length l) by flia Hjil Hilj.
  specialize (H1 H); clear H.
  destruct H1 as (l1 & l2 & Hll & Hl1l).
  rewrite Hll at 2.
  rewrite nb_nfit_app.
  subst x.
  destruct (Nat.eq_dec i (nth (j - S i) l 0)) as [Hjsi| Hjsi]. {
    rewrite Nat.add_0_l.
    apply Nat.add_le_mono. {
      erewrite map_ext_in. 2: {
        intros k Hk; apply in_seq in Hk.
        destruct Hk as (_, Hk); cbn in Hk.
        erewrite if_eqb_eq_dec.
        destruct (Nat.eq_dec k (j - S i)) as [H| H]; [ flia Hk H | ].
        rewrite Hll at 1.
        rewrite app_nth1; [ | now rewrite Hl1l ].
        easy.
      }
      rewrite <- Hl1l.
      now rewrite <- List_map_nth_seq.
    }
    rewrite Hl1l, (Nat.add_comm (S i)).
    rewrite Nat.sub_add; [ | easy ].
    rewrite <- List_seq_shift', map_map.
    erewrite map_ext_in. 2: {
      intros k Hk; apply in_seq in Hk.
      destruct Hk as (_, Hk); cbn in Hk.
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec (S (j - S i) + k) _) as [H| H]; [ flia H | clear H ].
      rewrite Hll at 1.
      rewrite app_nth2 at 1; [ | rewrite Hl1l; flia Hk ].
      rewrite Hl1l.
      replace (_ - _) with (S k) by flia.
      rewrite List_nth_succ_cons.
      easy.
    }
    replace (length l - S (j - S i)) with (length l2). 2: {
      rewrite Hll.
      rewrite app_length, Hl1l.
      cbn; flia.
    }
    rewrite <- List_map_nth_seq.
    rewrite Hll.
    rewrite app_nth2; [ | now rewrite Hl1l; unfold ge ].
    rewrite Hl1l, Nat.sub_diag.
    rewrite List_nth_0_cons.
    rewrite <- Hjsi; cbn; flia.
  }
  rewrite Nat.add_comm, <- Nat.add_assoc.
  apply Nat.add_le_mono. {
    erewrite map_ext_in. 2: {
      intros k Hk; apply in_seq in Hk.
      destruct Hk as (_, Hk); cbn in Hk.
      erewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec k (j - S i)) as [H| H]; [ flia Hk H | ].
      rewrite Hll at 1.
      rewrite app_nth1; [ | now rewrite Hl1l ].
      easy.
    }
    rewrite <- Hl1l.
    now rewrite <- List_map_nth_seq.
  }
  rewrite Hl1l, (Nat.add_comm (S i)).
  rewrite Nat.sub_add; [ | easy ].
  rewrite <- List_seq_shift', map_map.
  erewrite map_ext_in. 2: {
    intros k Hk; apply in_seq in Hk.
    destruct Hk as (_, Hk); cbn in Hk.
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (S (j - S i) + k) _) as [H| H]; [ flia H | clear H ].
    rewrite Hll at 1.
    rewrite app_nth2 at 1; [ | rewrite Hl1l; flia Hk ].
    rewrite Hl1l.
    replace (_ - _) with (S k) by flia.
    rewrite List_nth_succ_cons.
    easy.
  }
  replace (length l - S (j - S i)) with (length l2). 2: {
    rewrite Hll.
    rewrite app_length, Hl1l.
    cbn; flia.
  }
  rewrite <- List_map_nth_seq.
  rewrite Hll.
  rewrite app_nth2; [ | now rewrite Hl1l; unfold ge ].
  rewrite Hl1l, Nat.sub_diag.
  rewrite List_nth_0_cons; cbn.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec j (nth (j - S i) l 0)) as [Hjjsi| Hjjsi]. 2: {
    now rewrite Nat.add_comm.
  }
  exfalso.
  rewrite <- Hjjsi in Hll.
  destruct Hp as (Hpa, Hpn).
  apply NoDup_app_iff in Hpn.
  destruct Hpn as (Hni & Hnjl & Hsjl).
  apply NoDup_cons_iff in Hnjl.
  destruct Hnjl as (H2, H3); apply H2.
  rewrite Hjjsi.
  apply nth_In; flia Hjil Hilj.
}
apply IHit1; cycle 1. {
  rewrite list_swap_elem_length.
  cbn - [ list_swap_elem ].
  etransitivity; [ | apply Hit1 ].
  apply -> Nat.succ_le_mono.
  now apply Nat.add_le_mono_l.
} {
  rewrite list_swap_elem_length.
  cbn - [ list_swap_elem ].
  etransitivity; [ | apply Hit2 ].
  apply -> Nat.succ_le_mono.
  now apply Nat.add_le_mono_l.
}
now apply app_seq_swap_permut_seq.
Qed.

Theorem nb_nfit_succ_le : ∀ i j l, nb_nfit (S i) l ≤ nb_nfit i (j :: l).
Proof. cbn; flia. Qed.

Theorem eq_transp_loop_cons : ∀ it i j k p l,
  transp_loop it k p = (i, j) :: l
  → (∀ u, k + u < i → nth u p 0 = k + u) ∧
    nth (i - k) p 0 = j ∧
    k ≤ i ≤ it + k.
Proof.
intros * Hp *.
revert p k l Hp.
induction it; intros; [ easy | ].
cbn in Hp.
destruct p as [| a la]; [ easy | ].
rewrite if_eqb_eq_dec in Hp.
destruct (Nat.eq_dec k a) as [Hka| Hka]. {
  subst a.
  specialize (IHit la (S k) l Hp) as H1.
  destruct H1 as (H1 & H2 & H3).
  split. {
    intros u Hu.
    destruct u; [ now rewrite Nat.add_0_r | cbn ].
    rewrite <- Nat.add_succ_comm in Hu |-*.
    now apply H1.
  }
  specialize in_transp_loop_bounds as H4.
  specialize (H4 it (S k) la i j).
  rewrite Hp in H4.
  specialize (H4 (or_introl eq_refl)).
  split; [ now rewrite Nat_succ_sub_succ_r | ].
  rewrite <- Nat.add_succ_comm in H3.
  split; [ flia H3 | easy ].
}
injection Hp; clear Hp; intros Hp H1 H2; subst a k.
split; [ flia | ].
split; [ now rewrite Nat.sub_diag; cbn | flia ].
Qed.

Theorem eq_transp_list_cons : ∀ la lb i j,
  transp_list la = (i, j) :: lb
  → (∀ k, k < i → nth k la 0 = k) ∧ nth i la 0 = j.
Proof.
intros * Hla.
unfold transp_list in Hla.
specialize eq_transp_loop_cons as H1.
specialize (H1 (length la + nb_nfit 0 la) i j 0 la lb Hla).
rewrite Nat.sub_0_r in H1.
now destruct H1 as (H1 & H2 & H3).
Qed.
*)

Theorem list_swap_elem_comp_swap : ∀ l i j,
  i < length l
  → j < length l
  → list_swap_elem 0 l i j = l ° swap (length l) i j.
Proof.
intros * Hi Hj.
apply List_eq_iff.
unfold "°" at 1.
rewrite list_swap_elem_length, map_length, swap_length.
split; [ easy | ].
intros d k.
unfold swap.
revert i j k Hi Hj.
induction l as [| n]; intros; [ easy | ].
cbn in Hi, Hj |-*.
destruct k. {
  remember (transposition i j 0) as m eqn:Hm.
  symmetry in Hm.
  destruct m; [ easy | ].
  rewrite <- seq_shift.
  destruct (lt_dec m (length l)) as [Hml| Hml]. 2: {
    apply Nat.nlt_ge in Hml.
    unfold transposition in Hm.
    do 2 rewrite if_eqb_eq_dec in Hm.
    destruct (Nat.eq_dec 0 i) as [Hiz| Hiz]; [ flia  Hj Hm Hml | ].
    destruct (Nat.eq_dec 0 j) as [Hjz| Hjz]; [ flia  Hi Hm Hml | ].
    easy.
  }
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  now rewrite seq_nth.
}
rewrite seq_length.
rewrite map_map.
rewrite <- seq_shift.
do 2 rewrite map_map.
destruct (lt_dec k (length l)) as [Hkl| Hkl]. 2: {
  apply Nat.nlt_ge in Hkl.
  rewrite nth_overflow; [ | now rewrite List_map_seq_length ].
  rewrite nth_overflow; [ | now rewrite List_map_seq_length ].
  easy.
}
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ cbn | easy ].
remember (transposition i j (S k)) as m eqn:Hm.
symmetry in Hm.
destruct m; [ easy | ].
destruct (lt_dec m (length l)) as [Hml| Hml]. 2: {
  apply Nat.nlt_ge in Hml.
  unfold transposition in Hm.
  do 2 rewrite if_eqb_eq_dec in Hm.
  destruct (Nat.eq_dec (S k) i) as [Hiz| Hiz]; [ flia  Hj Hm Hml | ].
  destruct (Nat.eq_dec (S k) j) as [Hjz| Hjz]; [ flia  Hi Hm Hml | ].
  apply Nat.succ_inj in Hm; subst m.
  now apply Nat.nlt_ge in Hml.
}
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
now rewrite seq_nth.
Qed.

(*
Theorem all_comb_inv_loop_cons : ∀ n a l,
  all_comb_inv_loop n (a :: l) = pred a + n * all_comb_inv_loop n l.
Proof. easy. Qed.

Theorem all_comb_inv_loop_ub : ∀ n l,
  n ≠ 0
  → (∀ i, i < length l → nth i l 0 ≤ n)
  → all_comb_inv_loop n l < n ^ length l.
Proof.
intros * Hnz Hnl.
revert n Hnz Hnl.
induction l as [| a]; intros; cbn; [ easy | ].
apply Nat_lt_lt_add_mul. 2: {
  specialize (Hnl 0 (Nat.lt_0_succ _)); cbn in Hnl.
  flia Hnl Hnz.
}
apply IHl; [ easy | ].
intros i Hi.
specialize (Hnl (S i)).
assert (H : S i < length (a :: l)) by now cbn; flia Hi.
now specialize (Hnl H).
Qed.
*)

Theorem all_comb_inv_ub : ∀ n l,
  n ≠ 0
  → (∀ i, i < length l → nth i l 0 ≤ n)
  → all_comb_inv n l < n ^ length l.
Proof.
intros * Hnz Hnl.
induction l as [| a]; cbn; [ easy | ].
rewrite Nat.add_comm.
rewrite Nat.mul_comm.
rewrite (Nat.mul_comm n).
apply Nat_lt_lt_add_mul. {
  specialize (Hnl 0 (Nat.lt_0_succ _)).
  cbn in Hnl.
  flia Hnz Hnl.
}
apply IHl.
intros i Hi.
specialize (Hnl (S i)).
assert (H : S i < length (a :: l)) by now cbn; flia Hi.
now specialize (Hnl H).
Qed.

Theorem nth_concat_same_length : ∀ A m n (lll : list (list (list A))) i,
  (∀ ll, ll ∈ lll → length ll = m)
  → (∀ ll, ll ∈ lll → ∀ l, l ∈ ll → length l = n)
  → i < length lll * m
  → length (nth i (concat lll) []) = n.
Proof.
intros * Hlll Hll Hi.
revert i Hi.
induction lll as [| ll1]; intros; [ easy | cbn ].
destruct (lt_dec i (length ll1)) as [Hill| Hill]. {
  rewrite app_nth1; [ | easy ].
  apply Hll with (ll := ll1); [ now left | ].
  now apply nth_In.
}
apply Nat.nlt_ge in Hill.
rewrite app_nth2; [ | easy ].
apply IHlll. {
  intros ll2 Hll2.
  now apply Hlll; right.
} {
  intros ll2 Hll2 l Hl.
  apply Hll with (ll := ll2); [ now right | easy ].
} {
  cbn in Hi.
  rewrite Hlll; [ | now left ].
  rewrite Hlll in Hill; [ | now left ].
  flia Hi Hill.
}
Qed.

Theorem nth_list_prodn_same_length : ∀ A n (ll : list (list A)) i,
  (∀ l, l ∈ ll → length l = n)
  → i < n ^ length ll
  → length (nth i (list_prodn ll) []) = length ll.
Proof.
intros * Hll Hi.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  destruct ll as [| l]. {
    now apply Nat.lt_1_r in Hi; subst i.
  }
  now rewrite Nat.pow_0_l in Hi.
}
revert n i Hnz Hi Hll.
induction ll as [| l]; intros. {
  destruct i; [ easy | now destruct i ].
}
destruct ll as [| l1]. {
  cbn.
  specialize (Hll _ (or_introl eq_refl)).
  subst n.
  rewrite Nat.pow_1_r in Hi.
  clear Hnz.
  revert i Hi.
  induction l as [| a]; intros; [ easy | cbn ].
  destruct i; [ easy | ].
  cbn in Hi; apply Nat.succ_lt_mono in Hi.
  now apply IHl.
}
remember (l1 :: ll) as ll'; cbn; subst ll'.
rewrite flat_map_concat_map.
apply nth_concat_same_length with (m := n ^ length (l1 :: ll)). {
  intros ll1 Hll1.
  apply in_map_iff in Hll1.
  destruct Hll1 as (a & Hll1 & Ha).
  subst ll1.
  rewrite map_length.
  rewrite list_prodn_length; [ | easy ].
  apply rngl_product_same_length.
  intros l2 Hl2.
  now apply Hll; right.
} {
  intros ll1 Hll1 l2 Hl2.
  apply in_map_iff in Hll1.
  destruct Hll1 as (a & Hll1 & Ha).
  subst ll1.
  apply in_map_iff in Hl2.
  destruct Hl2 as (l3 & Hl3 & Hl2).
  subst l2; cbn; f_equal.
  now apply in_list_prodn_length in Hl2.
} {
  rewrite map_length.
  rewrite Hll; [ | now left ].
  now rewrite <- Nat.pow_succ_r'.
}
Qed.

Theorem nth_all_comb_length : ∀ n i,
  i < n ^ n
  → length (nth i (all_comb n) []) = n.
Proof.
intros * Hi.
unfold all_comb.
rewrite nth_list_prodn_same_length with (n := n). {
  apply repeat_length.
} {
  intros l Hl.
  apply repeat_spec in Hl; subst l.
  apply seq_length.
} {
  now rewrite repeat_length.
}
Qed.

Theorem all_comb_elem_ub : ∀ i j n,
  nth i (nth j (all_comb n) []) 0 ≤ n.
Proof.
intros.
unfold all_comb.
remember (list_prodn (repeat (seq 1 n) n)) as ll eqn:Hll.
destruct (lt_dec j (length ll)) as [Hjll| Hjll]. 2: {
  apply Nat.nlt_ge in Hjll.
  rewrite (nth_overflow ll); [ | easy ].
  now rewrite List_nth_nil.
}
assert (H1 : nth j ll [] ∈ ll) by now apply nth_In.
rewrite Hll in H1.
apply in_list_prodn_repeat_iff in H1.
rewrite <- Hll in H1.
destruct H1 as [(H1, H2)| H1]. {
  rewrite H1, H2.
  now rewrite List_nth_nil.
}
destruct H1 as (Hnz & Hn & Hln).
specialize (Hln (nth i (nth j ll []) 0)).
destruct (lt_dec i n) as [Hin| Hin]. 2: {
  apply Nat.nlt_ge in Hin.
  rewrite nth_overflow; [ easy | ].
  now rewrite Hn.
}
assert (H : nth i (nth j ll []) 0 ∈ nth j ll []). {
  apply nth_In.
  now rewrite Hn.
}
now specialize (Hln H).
Qed.

Theorem all_comb_elem_lb : ∀ i j n,
  i < n
  → j < n ^ n
  → 1 ≤ nth i (nth j (all_comb n) []) 0.
Proof.
intros * Hin Hjn.
unfold all_comb.
remember (list_prodn (repeat (seq 1 n) n)) as ll eqn:Hll.
assert (Hj : nth j ll [] ∈ ll). {
  apply nth_In.
  rewrite Hll.
  rewrite list_prodn_length; [ | now destruct n ].
  rewrite rngl_product_same_length with (n := n). 2: {
    intros l Hl.
    apply repeat_spec in Hl; subst l.
    apply seq_length.
  }
  now rewrite repeat_length.
}
rewrite Hll in Hj.
apply in_list_prodn_repeat_iff in Hj.
rewrite <- Hll in Hj.
destruct Hj as [(H1, H2)| Hj]; [ now subst n | ].
destruct Hj as (H1 & H2 & H3).
apply H3.
apply nth_In.
now rewrite H2.
Qed.

Theorem nat_summation_list_all_same : ∀ A (l : list A) a,
  ∑ (_ ∈ l), a = a * length l.
Proof.
intros.
induction l as [| b]; [ easy | ].
rewrite rngl_summation_list_cons.
cbn - [ rngl_add rngl_zero ].
rewrite IHl.
now rewrite Nat.mul_succ_r, Nat.add_comm.
Qed.

Theorem nat_product_list_all_same : ∀ A (l : list A) a,
  ∏ (_ ∈ l), a = a ^ length l.
Proof.
intros.
induction l as [| b]; [ easy | ].
rewrite rngl_product_list_cons.
cbn - [ rngl_mul rngl_one ].
now rewrite IHl.
Qed.

Theorem nth_0_list_prodn_repeat : ∀ m n,
  n ≤ m
  → nth 0 (list_prodn (repeat (seq 1 m) n)) [] = repeat 1 n.
Proof.
intros * Hnm.
revert m Hnm.
induction n; intros; [ easy | ].
cbn - [ seq ].
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hnm.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn - [ seq ].
  clear Hnm.
  induction m; [ easy | ].
  rewrite seq_S.
  cbn - [ seq ].
  rewrite flat_map_app.
  rewrite app_nth1; [ easy | ].
  rewrite List_flat_map_length.
  cbn - [ rngl_zero rngl_add seq ].
  rewrite nat_summation_list_all_same, seq_length.
  now cbn.
}
rewrite seq_S at 1.
rewrite flat_map_app; cbn - [ seq ].
rewrite app_nth1. 2: {
  rewrite List_flat_map_length.
  erewrite rngl_summation_list_eq_compat. 2: {
    intros i Hi.
    rewrite map_length.
    rewrite list_prodn_length; [ | now destruct n ].
    erewrite rngl_product_list_eq_compat. 2: {
      intros l Hl.
      apply repeat_spec in Hl.
      rewrite Hl at 1.
      rewrite seq_length.
      easy.
    }
    cbn - [ rngl_one rngl_mul seq ].
    rewrite nat_product_list_all_same.
    now rewrite repeat_length.
  }
  cbn - [ rngl_zero rngl_add ].
  rewrite nat_summation_list_all_same.
  rewrite seq_length.
  apply Nat.neq_0_lt_0.
  apply Nat.neq_mul_0.
  split; [ | flia Hnm Hnz ].
  now apply Nat.pow_nonzero.
}
destruct m; [ flia Hnm Hnz | ].
rewrite flat_map_concat_map.
assert (Hzl : 0 < length (list_prodn (repeat (seq 1 (S (S m))) n))). {
  rewrite list_prodn_length; [ | now destruct n ].
  erewrite rngl_product_list_eq_compat. 2: {
    intros l Hl.
    apply repeat_spec in Hl.
    rewrite Hl at 1.
    rewrite seq_length.
    easy.
  }
  cbn - [ rngl_one rngl_mul seq ].
  rewrite nat_product_list_all_same.
  cbn - [ Nat.pow ].
  rewrite repeat_length.
  apply Nat.neq_0_lt_0.
  now apply Nat.pow_nonzero.
}
remember (seq 1 (S (S m))) as s; cbn; subst s.
rewrite app_nth1; [ | now rewrite map_length ].
rewrite (List_map_nth' []); [ | easy ].
f_equal.
apply IHn; flia Hnm.
Qed.

Fixpoint nth_concat A i (ll : list (list A)) d :=
  match ll with
  | [] => d
  | l :: ll' =>
      if lt_dec i (length l) then nth i l d
      else nth_concat (i - length l) ll' d
  end.

Theorem nth_concat_fun : ∀ A i ll (d : A),
  nth i (concat ll) d = nth_concat i ll d.
Proof.
intros.
revert i.
induction ll as [| l]; intros; cbn. {
  now rewrite Tauto_match_nat_same.
}
destruct (lt_dec i (length l)) as [Hil| Hil]. {
  now rewrite app_nth1.
}
apply Nat.nlt_ge in Hil.
rewrite app_nth2; [ | easy ].
apply IHll.
Qed.

Theorem concat_app_nth1 : ∀ A i lla llb (d : A),
  i < ∑ (l ∈ lla), length l
  → nth_concat i (lla ++ llb) d = nth_concat i lla d.
Proof.
intros * Hil.
revert i llb Hil.
induction lla as [| la]; intros; cbn. {
  now rewrite rngl_summation_list_empty in Hil.
}
destruct (lt_dec i (length la)) as [Hila| Hila]; [ easy | ].
apply Nat.nlt_ge in Hila.
apply IHlla.
rewrite rngl_summation_list_cons in Hil.
cbn in Hil |-*.
flia Hil Hila.
Qed.

Theorem det_isort_rows_with_dup : in_charac_0_field →
  ∀ A kl,
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_nrows A)
  → no_dup Nat.eqb kl = false
  → det (mat_select_rows kl A) =
      (ε kl * det (mat_select_rows (isort Nat.leb kl) A))%F.
Proof.
intros Hif * Hcm Hac Hkl Hadk.
apply (no_dup_false_iff Nat.eqb_eq) in Hadk.
destruct Hadk as (l1 & l2 & l3 & a & Ha).
rewrite ε_when_dup; [ | now destruct Hif | now destruct Hif | ]. 2: {
  intros H.
  rewrite Ha in H.
  apply NoDup_remove_2 in H.
  apply H; clear H.
  apply in_or_app; right.
  now apply in_or_app; right; left.
}
rewrite rngl_mul_0_l; [ | now destruct Hif; left ].
set (p1 := S (length l1)).
set (q1 := S (length (l1 ++ a :: l2))).
apply (determinant_same_rows Hif) with (p := p1) (q := q1); cycle 1. {
  unfold p1, q1.
  rewrite app_length; cbn; flia.
} {
  rewrite Ha.
  unfold p1.
  split; [ flia | ].
  rewrite mat_select_rows_nrows.
  rewrite app_length; cbn; flia.
} {
  rewrite Ha.
  unfold q1.
  split; [ flia | ].
  rewrite mat_select_rows_nrows.
  rewrite app_length; cbn.
  rewrite app_length; cbn.
  rewrite app_length; cbn; flia.
} {
  intros i Hi.
  unfold p1, q1.
  unfold mat_el; cbn.
  f_equal.
  rewrite (List_map_nth' 0). 2: {
    rewrite Ha.
    rewrite app_length; cbn; flia.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite Ha.
    rewrite app_length; cbn.
    rewrite app_length; cbn.
    rewrite app_length; cbn; flia.
  }
  apply map_ext_in.
  intros j Hj.
  do 2 rewrite Nat.sub_0_r.
  rewrite Ha.
  rewrite app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag; cbn.
  rewrite app_nth2; [ | rewrite app_length; flia ].
  rewrite app_length, Nat.add_comm, Nat.add_sub; cbn.
  rewrite app_nth2; [ | now unfold ge ].
  now rewrite Nat.sub_diag.
}
now apply mat_select_rows_is_square.
Qed.

Theorem det_isort_rows_no_dup : in_charac_0_field →
  ∀ A kl,
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_nrows A)
  → no_dup Nat.eqb kl = true
  → det (mat_select_rows kl A) =
      (ε kl * det (mat_select_rows (isort Nat.leb kl) A))%F.
Proof.
intros Hif * Hcm Hac Hkl Hadk.
destruct (Nat.eq_dec (length kl) 0) as [Hkz| Hkz]. {
  apply length_zero_iff_nil in Hkz; subst kl.
  cbn; rewrite ε_nil; symmetry.
  apply rngl_mul_1_l.
}
rewrite det_is_det''; try now destruct Hif. 2: {
  now apply mat_select_rows_is_square.
}
rewrite det_is_det''; try now destruct Hif. 2: {
  apply mat_select_rows_is_square; [ easy | | ]. {
    now rewrite isort_length.
  } {
    intros k Hk.
    apply Hkl.
    now apply in_isort in Hk.
  }
}
unfold det''.
do 2 rewrite mat_select_rows_nrows.
rewrite isort_length.
rewrite rngl_mul_summation_list_distr_l; [ | now destruct Hif; left ].
symmetry; erewrite rngl_summation_list_eq_compat. 2: {
  intros jl Hjl.
  now rewrite rngl_mul_assoc.
}
symmetry.
remember (length kl) as n eqn:Hn.
assert (Heql : equality (list_eqv Nat.eqb)). {
  intros la lb.
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
}
set (g1 := λ l, l ° collapse kl).
set (h1 := λ l, l ° isort_rank Nat.leb kl).
assert (Hgh : ∀ l, l ∈ all_comb n → g1 (h1 l) = l). {
  intros l Hl.
  unfold g1, h1.
  rewrite <- (permut_comp_assoc n); cycle 1. {
    now rewrite isort_rank_length.
  } {
    rewrite Hn.
    apply collapse_length.
  } {
    apply collapse_permut_seq_with_len.
  }
  rewrite permut_comp_isort_rank_r; [ | apply isort_rank_permut_seq ].
  rewrite isort_rank_length, <- Hn.
  apply comp_1_r.
  apply in_all_comb_iff in Hl.
  now destruct Hl.
}
assert (Hhg : ∀ l, l ∈ all_comb n → h1 (g1 l) = l). {
  intros l Hl.
  unfold g1, h1.
  rewrite <- (permut_comp_assoc n); cycle 1. {
    now rewrite collapse_length.
  } {
    rewrite Hn.
    apply isort_rank_length.
  } {
    apply isort_rank_permut_seq.
  }
  unfold collapse.
  rewrite permut_comp_isort_rank_l; [ | apply isort_rank_permut_seq ].
  rewrite isort_rank_length, <- Hn.
  apply comp_1_r.
  apply in_all_comb_iff in Hl.
  now destruct Hl.
}
rewrite rngl_summation_list_change_var with (g := g1) (h := h1); [ | easy ].
rewrite (rngl_summation_list_permut (list_eqv Nat.eqb))
    with (lb := all_comb n); [ | easy | ]. {
  apply rngl_summation_list_eq_compat.
  intros la Hla.
  f_equal. {
    unfold g1.
    rewrite (sign_comp Hif). 2: {
      apply in_all_comb_iff in Hla.
      destruct Hla as [Hla| Hla]; [ easy | ].
      destruct Hla as (_ & Hnc & Hcn).
      rewrite Hnc, Hn.
      apply collapse_permut_seq_with_len.
    }
    rewrite rngl_mul_comm; [ | now destruct Hif ].
    f_equal.
    apply ε_collapse_ε.
    now apply (no_dup_NoDup Nat.eqb_eq).
  }
  set (g2 := λ i, S (nth (i - 1) (isort_rank Nat.leb kl) 0)).
  set (h2 := λ i, S (nth (i - 1) (collapse kl) 0)).
  assert (Hgh2 : ∀ i, 1 ≤ i ≤ n → g2 (h2 i) = i). {
    intros i Hi.
    unfold g2, h2.
    rewrite Nat_sub_succ_1.
    unfold collapse.
    rewrite permut_permut_isort; [ flia Hi | | ]. {
      apply isort_rank_permut_seq.
    }
    rewrite isort_rank_length, <- Hn; flia Hi.
  }
  assert (Hhg2 : ∀ i, 1 ≤ i ≤ n → h2 (g2 i) = i). {
    intros i Hi.
    unfold g2, h2.
    rewrite Nat_sub_succ_1.
    unfold collapse.
    rewrite permut_isort_permut; [ flia Hi | | ]. {
      apply isort_rank_permut_seq.
    }
    rewrite isort_rank_length, <- Hn; flia Hi.
  }
  rewrite rngl_product_change_var with (g := g2) (h := h2); [ | easy ].
  rewrite (rngl_product_list_permut _ Nat.eqb_eq)
      with (lb := seq 1 n); [ | now destruct Hif | ]. {
    rewrite rngl_product_seq_product; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    apply rngl_product_eq_compat.
    intros i Hi.
    unfold g1.
    unfold "°".
    unfold g2.
    rewrite Nat_sub_succ_1.
    rewrite (List_map_nth' 0). 2: {
      rewrite collapse_length.
      apply isort_rank_ub.
      now intros H; rewrite H in Hn.
    }
    unfold collapse.
    rewrite permut_isort_permut; cycle 1. {
      apply isort_rank_permut_seq.
    } {
      rewrite isort_rank_length, <- Hn.
      flia Hi.
    }
    rewrite <- comp_isort_rank_r.
    unfold "°".
    unfold mat_el.
    f_equal.
    rewrite Nat_sub_succ_1.
    cbn.
    rewrite (List_map_nth' 0). 2: {
      apply isort_rank_ub.
      now intros H; rewrite H in Hn.
    }
    rewrite (List_map_nth' 0). 2: {
      rewrite map_length, isort_rank_length, <- Hn.
      flia Hi.
    }
    rewrite (List_map_nth' 0). 2: {
      rewrite isort_rank_length, <- Hn.
      flia Hi.
    }
    easy.
  }
  rewrite Nat_sub_succ_1.
  apply (NoDup_permutation Nat.eqb_eq). {
    apply (NoDup_map_iff 0).
    intros i j Hi Hj Hij.
    rewrite seq_length in Hi, Hj.
    rewrite seq_nth in Hij; [ | easy ].
    rewrite seq_nth in Hij; [ | easy ].
    unfold h2 in Hij.
    apply Nat.succ_inj in Hij.
    do 2 rewrite Nat.add_comm, Nat.add_sub in Hij.
    apply isort_rank_inj in Hij; [ easy | | | ]. {
      apply isort_rank_permut_seq.
    } {
      now rewrite isort_rank_length, <- Hn.
    } {
      now rewrite isort_rank_length, <- Hn.
    }
  } {
    apply seq_NoDup.
  }
  intros i.
  split; intros Hi. {
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj); subst i.
    apply in_seq in Hj.
    apply in_seq.
    unfold h2.
    split; [ flia | cbn ].
    apply -> Nat.succ_lt_mono.
    rewrite Hn.
    rewrite <- (isort_rank_length Nat.leb).
    apply isort_rank_ub.
    intros H.
    apply eq_isort_rank_nil in H.
    now subst kl.
  } {
    apply in_seq in Hi.
    apply in_map_iff.
    exists (g2 i).
    split; [ apply Hhg2; flia Hi | ].
    apply in_seq.
    unfold g2.
    split; [ flia | cbn ].
    apply -> Nat.succ_lt_mono.
    rewrite Hn.
    apply isort_rank_ub.
    intros H.
    now subst kl.
  }
}
apply NoDup_permutation. {
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
} {
  apply (NoDup_map_iff []).
  rewrite all_comb_length; [ | easy ].
  intros i j Hi Hj Hij.
  unfold h1 in Hij.
  unfold "°" in Hij.
  specialize (ext_in_map Hij) as H1.
  assert
    (H : ∀ k, k < n →
     nth k (nth i (all_comb n) []) 0 = nth k (nth j (all_comb n) []) 0). {
    intros k Hk.
    apply H1.
    apply (permutation_in_iff Nat.eqb_eq) with (la := seq 0 n). 2: {
      now apply in_seq.
    }
    apply (permutation_sym Nat.eqb_eq).
    eapply (permutation_trans Nat.eqb_eq). {
      apply isort_rank_permut_seq.
    }
    rewrite isort_rank_length, <- Hn.
    apply (permutation_refl Nat.eqb_eq).
  }
  clear H1; rename H into H1.
  specialize (all_comb_inj Hkz Hi Hj) as H2.
  apply H2.
  remember (nth i (all_comb n) []) as la eqn:Hla.
  remember (nth j (all_comb n) []) as lb eqn:Hlb.
  move lb before la.
  apply List_eq_iff.
  split. {
    rewrite Hla, Hlb.
    rewrite nth_all_comb_length; [ | easy ].
    now rewrite nth_all_comb_length.
  }
  intros d k.
  destruct (lt_dec k n) as [Hkn| Hkn]. 2: {
    apply Nat.nlt_ge in Hkn.
    rewrite nth_overflow. 2: {
      rewrite Hla.
      now rewrite nth_all_comb_length.
    }
    rewrite nth_overflow. 2: {
      rewrite Hlb.
      now rewrite nth_all_comb_length.
    }
    easy.
  }
  rewrite nth_indep with (d' := 0). 2: {
    rewrite Hla.
    now rewrite nth_all_comb_length.
  }
  symmetry.
  rewrite nth_indep with (d' := 0). 2: {
    rewrite Hlb.
    now rewrite nth_all_comb_length.
  }
  symmetry.
  now apply H1.
} {
  apply NoDup_all_comb.
}
intros la.
split; intros Hla. {
  apply in_map_iff in Hla.
  destruct Hla as (lb & Hla & Hlb); subst la.
  apply in_all_comb_iff in Hlb.
  destruct Hlb as [Hlb| Hlb]; [ easy | ].
  destruct Hlb as (_ & Hlb & Hlbn).
  unfold h1, "°"; cbn.
  apply in_all_comb_iff; right.
  split; [ easy | ].
  rewrite map_length, isort_rank_length.
  split; [ easy | ].
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hi & Hj); subst i.
  apply Hlbn, nth_In.
  apply in_isort_rank in Hj.
  congruence.
} {
  apply in_all_comb_iff in Hla.
  destruct Hla as [Hla| Hla]; [ easy | ].
  destruct Hla as (_ & Hlan & Hla).
  apply in_map_iff.
  exists (g1 la).
  split. {
    now apply Hhg, in_all_comb_iff; right.
  }
  apply in_all_comb_iff; right.
  split; [ easy | ].
  split. {
    unfold g1.
    now rewrite comp_length, collapse_length.
  }
  intros i Hi.
  unfold g1, "°" in Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hi & Hj); subst i.
  apply Hla, nth_In.
  apply in_isort_rank in Hj.
  rewrite isort_rank_length in Hj.
  congruence.
}
Qed.

Theorem det_isort_rows : in_charac_0_field →
  ∀ A kl,
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_nrows A)
  → det (mat_select_rows kl A) =
      (ε kl * det (mat_select_rows (isort Nat.leb kl) A))%F.
Proof.
intros Hif * Hcm Hac Hkl.
remember (no_dup Nat.eqb kl) as adk eqn:Hadk; symmetry in Hadk.
destruct adk. {
  now apply det_isort_rows_no_dup.
} {
  now apply det_isort_rows_with_dup.
}
Qed.

Theorem permutation_filter_app_filter : ∀ A (eqb : A → _),
  equality eqb →
  ∀ f la, permutation eqb la (filter f la ++ filter (λ x, negb (f x)) la).
Proof.
intros * Heqb *.
induction la as [| a]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (bool_dec (f a)) as [Hfa| Hfa]. {
  rewrite Hfa; cbn.
  apply (permutation_skip Heqb), IHla.
} {
  rewrite Hfa; cbn.
  apply (permutation_cons_app Heqb), IHla.
}
Qed.

Theorem List_filter_map : ∀ A B (f : B → bool) (g : A → B) (l : list A),
  filter f (map g l) =
  map g (filter (λ a, f (g a)) l).
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (bool_dec (f( g a))) as [H1| H1]. {
  rewrite H1.
  cbn; f_equal.
  apply IHl.
} {
  rewrite H1.
  apply IHl.
}
Qed.

Theorem filter_negb_member_prodn_succ : ∀ m n,
 filter (λ x, negb (member Nat.eqb (S n) x))
   (list_prodn (repeat (seq 1 (S n)) m)) =
 list_prodn (repeat (seq 1 n) m).
Proof.
intros.
revert n.
induction m; intros; [ easy | ].
cbn - [ seq ].
rewrite flat_map_concat_map.
rewrite <- concat_filter_map.
rewrite flat_map_concat_map.
rewrite map_map.
do 2 rewrite <- App_list_concat_map.
symmetry.
erewrite iter_list_eq_compat. 2: {
  intros i Hi.
  rewrite <- IHm.
  easy.
}
cbn - [ seq ].
symmetry.
erewrite iter_list_eq_compat. 2: {
  intros i Hi.
  rewrite List_filter_map.
  easy.
}
cbn - [ member seq ].
rewrite seq_S at 1.
rewrite iter_list_app.
unfold iter_list at 1.
cbn - [ member seq ].
rewrite <- app_nil_r.
f_equal. 2: {
  erewrite filter_ext. 2: {
    intros la; cbn.
    now rewrite Nat.eqb_refl; cbn.
  }
  remember (list_prodn _) as l; clear.
  now induction l.
}
apply iter_list_eq_compat.
intros i Hi; apply in_seq in Hi.
f_equal.
apply filter_ext.
intros la.
f_equal.
cbn.
destruct i; [ easy | ].
rewrite if_bool_if_dec.
destruct (bool_dec (n =? i)) as [Hni| Hni]; [ | easy ].
apply Nat.eqb_eq in Hni; subst i.
cbn in Hi; flia Hi.
Qed.

Theorem permutation_prodn_succ_app_prodn_filter : ∀ m n,
  permutation (list_eqv Nat.eqb)
    (list_prodn (repeat (seq 1 (S n)) m))
    (list_prodn (repeat (seq 1 n) m) ++
     filter (member Nat.eqb (S n)) (list_prodn (repeat (seq 1 (S n)) m))).
Proof.
intros.
assert (Hel : equality (list_eqv Nat.eqb)). {
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
}
eapply (permutation_trans Hel). {
  apply permutation_filter_app_filter with (f := member Nat.eqb (S n)).
  easy.
}
eapply (permutation_trans Hel). {
  apply (permutation_app_comm Hel).
}
apply (permutation_app_tail Hel).
rewrite filter_negb_member_prodn_succ.
apply (permutation_refl Hel).
Qed.

(*
Theorem map_map_sub_sls1n : ∀ m n,
  map (map (sub (S n))) (sls1n n (S m)) =
    flat_map
      (λ a,
         filter (is_sorted Nat.ltb)
           (map (cons a) (list_prodn (repeat (seq 1 n) m)))) (seq 1 n).
Proof.
intros.
Print sls1n.
Print sub_lists_of_seq_1_n.
Fixpoint sls1n' (i n k : nat) {struct n} : list (list nat) :=
  match k with
  | 0 => [[]]
  | S k' =>
      match n with
      | 0 => []
      | S n' => map (λ l : list nat, i :: l) (sls1n' (S i) n' k') ++ sls1n' (S i) n' k
      end
  end.
Compute (
  let n := 5 in
  let k := 0 in
  (sls1n' 1 n k, sub_lists_of_seq_1_n n k)
).
...
(*
Compute (
  let n := 6 in
  let m := 2 in
  map (map (sub (S n))) (sls1n n (S m))
 =
  flat_map
    (λ x : nat,
       filter (is_sorted Nat.ltb)
         (map (cons x) (list_prodn (repeat (seq 1 n) m))))
    (seq 1 n)
).
*)
revert m.
induction n; intros; [ easy | ].
cbn - [ seq "-" ].
rewrite map_app.
rewrite map_map.
cbn - [ "-" ].
...
*)

Theorem List_filter_is_sorted_cons : ∀ i l,
  filter (λ la, is_sorted Nat.ltb (i :: la)) l =
  map (λ la, tl la) (filter (λ la, is_sorted Nat.ltb la) (map (cons i) l)).
Proof.
intros.
revert i.
induction l as [| la lla]; intros; [ easy | ].
cbn - [ is_sorted ].
do 2 rewrite if_bool_if_dec.
destruct (bool_dec (is_sorted Nat.ltb (i :: la))) as [H1| H1]. {
  cbn - [ is_sorted ].
  f_equal.
  apply IHlla.
}
apply IHlla.
Qed.

Theorem list_prodn_repeat_seq_succ_l : ∀ sta len n,
  list_prodn (repeat (seq (S sta) len) n) =
  filter (λ la, negb (member Nat.eqb sta la))
    (list_prodn (repeat (seq sta (S len)) n)).
Proof.
intros.
revert sta len.
induction n; intros; [ easy | ].
remember (seq sta (S len)) as s; cbn; subst s.
do 2 rewrite flat_map_concat_map.
rewrite <- concat_filter_map.
rewrite map_map.
rewrite IHn.
cbn.
replace
  (filter (λ la : list nat, negb (member Nat.eqb sta la))
    (map (cons sta) (list_prodn (repeat (sta :: seq (S sta) len) n))))
    with ([] : list (list nat)). 2: {
  symmetry.
  clear IHn.
  rewrite List_filter_map; cbn.
  rewrite Nat.eqb_refl; cbn.
  replace [] with (map (cons sta) []) by easy.
  f_equal.
  now apply List_filter_nil_iff.
}
cbn.
f_equal.
apply map_ext_in.
intros a Ha.
apply in_seq in Ha.
rewrite List_filter_map.
f_equal.
apply filter_ext_in.
intros la Hla.
f_equal; cbn.
rewrite if_bool_if_dec.
destruct (bool_dec (sta =? a)) as [Hsa| Hsa]; [ | easy ].
apply Nat.eqb_eq in Hsa; subst a; flia Ha.
Qed.

Fixpoint prodn_repeat_seq sta len n :=
  match n with
  | 0 => [[]]
  | S n' =>
      flat_map (λ i, map (cons i) (prodn_repeat_seq sta len n')) (seq sta len)
  end.

Definition all_comb' n := prodn_repeat_seq 1 n n.

Theorem list_prodn_prodn_repeat : ∀ sta len n,
  list_prodn (repeat (seq sta len) n) = prodn_repeat_seq sta len n.
Proof.
intros.
revert sta len.
induction n; intros; [ easy | now cbn; rewrite IHn ].
Qed.

Theorem all_comb_all_comb' : ∀ n, all_comb n = all_comb' n.
Proof.
intros.
apply list_prodn_prodn_repeat.
Qed.

(* equivalence classes *)

Fixpoint ecl {A} (eqv : A → _) it la :=
  match it with
  | 0 => []
  | S it' =>
      match la with
      | [] => []
      | a :: la' =>
          let (ec, rest) := partition (eqv a) la' in
          (a, ec) :: ecl eqv it' rest
      end
  end.

Definition equiv_classes {A} (eqv : A → _) l := ecl eqv (length l) l.

Theorem ecl_enough_iter : ∀ A (eqv : A → _) it1 it2 la,
  length la ≤ it1
  → length la ≤ it2
  → ecl eqv it1 la = ecl eqv it2 la.
Proof.
intros * Hit1 Hit2.
revert la it2 Hit1 Hit2.
induction it1; intros; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Hit1; subst la.
  now destruct it2.
}
destruct la as [| a]; [ now destruct it2 | ].
destruct it2; [ easy | ].
cbn in Hit1, Hit2 |-*.
apply Nat.succ_le_mono in Hit1, Hit2.
remember (partition (eqv a) la) as er eqn:Her; symmetry in Her.
destruct er as (r, ec); f_equal.
apply partition_length in Her.
apply IHit1; [ flia Hit1 Her | flia Hit2 Her ].
Qed.

Theorem ecl_are_permutation : ∀ A (eqb : A → _),
  equality eqb →
  ∀ eqv la len,
  length la ≤ len
  → permutation eqb la (flat_map (λ rc, fst rc :: snd rc) (ecl eqv len la)).
Proof.
intros * Heqb * Hlen.
revert la Hlen.
induction len; intros. {
  now apply Nat.le_0_r, length_zero_iff_nil in Hlen; subst la.
}
destruct la as [| a]; [ easy | cbn ].
cbn in Hlen; apply Nat.succ_le_mono in Hlen.
remember (partition (eqv a) la) as ec eqn:Hec; symmetry in Hec.
destruct ec as (ec, rest); cbn.
apply (permutation_skip Heqb).
specialize (permutation_partition Heqb _ _ Hec) as H1.
eapply (permutation_trans Heqb); [ apply H1 | ].
apply (permutation_app Heqb); [ apply (permutation_refl Heqb) | ].
apply IHlen.
apply (permutation_length Heqb) in H1.
rewrite app_length in H1.
rewrite H1 in Hlen.
etransitivity; [ | apply Hlen ].
rewrite Nat.add_comm.
apply Nat.le_add_r.
Qed.

Theorem equiv_classes_are_permutation : ∀ A (eqb eqv : A → _),
  equality eqb →
  ∀ la,
  permutation eqb la
    (flat_map (λ rc, fst rc :: snd rc) (equiv_classes eqv la)).
Proof.
intros * Heqb *.
now apply ecl_are_permutation.
Qed.

Theorem filter_eqb_nodup : ∀ A (eqb : A → _),
  equality eqb →
  ∀ a la,
  NoDup (a :: la)
  → filter (eqb a) la ∈ [[]; [a]].
Proof.
intros * Heqb * Hnd.
induction la as [| b]; [ now left | ].
assert (H : NoDup (a :: la)). {
  apply NoDup_cons_iff in Hnd.
  apply NoDup_cons_iff.
  destruct Hnd as (Hab, Hnd).
  apply not_in_cons in Hab.
  split; [ easy | ].
  now apply NoDup_cons_iff in Hnd.
}
specialize (IHla H); clear H; cbn.
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  apply Heqb in Hab; subst b.
  apply NoDup_cons_iff in Hnd.
  destruct Hnd as (H, _).
  now exfalso; apply H; left.
} {
  destruct IHla as [H1| H1]; [ now left | ].
  destruct H1 as [H1| H1]; [ now right; left | easy ].
}
Qed.

Theorem partition_eqb_nodup : ∀ A (eqb : A → _),
  equality eqb →
  ∀ a la lb lc,
  NoDup (a :: la)
  → partition (eqb a) la = (lb, lc)
  → lb ∈ [[]; [a]].
Proof.
intros * Heqb * Hnd Hp.
apply List_partition_filter_iff in Hp.
destruct Hp as (Hb, Hc).
subst lb; clear lc Hc.
now apply (filter_eqb_nodup Heqb).
Qed.

Theorem nodup_partition_eqb : ∀ A (eqb : A → _),
  equality eqb →
  ∀ a la,
  NoDup (a :: la)
  → partition (eqb a) la = ([], la).
Proof.
intros * Heqb * Hnd.
revert a Hnd.
induction la as [| b]; intros; [ easy | cbn ].
remember (partition (eqb a) la) as p eqn:Hp; symmetry in Hp.
destruct p as (lb, lc).
rewrite IHla in Hp. 2: {
  apply NoDup_cons_iff in Hnd.
  apply NoDup_cons_iff.
  destruct Hnd as (Hab & Hnd).
  split; [ now apply not_in_cons in Hab | ].
  now apply NoDup_cons_iff in Hnd.
}
injection Hp; clear Hp; intros; subst lb lc.
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ | easy ].
exfalso.
apply Heqb in Hab; subst b.
apply NoDup_cons_iff in Hnd.
destruct Hnd as (Hab, Hnd).
apply Hab; clear Hab.
now left.
Qed.

Theorem partition_rel : ∀ A B (rel : A → B → _) a la lb lc,
  partition (rel a) la = (lb, lc)
  → (∀ b, b ∈ lb → rel a b = true) ∧
    (∀ b, b ∈ lc → rel a b = false) ∧
    (∀ b, b ∈ la ↔ b ∈ lb ++ lc).
Proof.
intros * Hp.
revert a lb lc Hp.
induction la as [| c]; intros. {
  cbn in Hp.
  now injection Hp; clear Hp; intros; subst lb lc.
}
cbn in Hp.
remember (partition (rel a) la) as p eqn:Hp'; symmetry in Hp'.
destruct p as (ld, le).
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
apply IHla in Hp'.
destruct Hp' as (Had & Hae & Hade).
destruct ac. {
  injection Hp; clear Hp; intros; subst lb le.
  split. {
    intros b Hb.
    destruct Hb as [Hb| Hb]; [ now subst c | now apply Had ].
  }
  split. {
    intros b Hb.
    now apply Hae.
  }
  intros b.
  split; intros Hb. {
    destruct Hb as [Hb| Hb]; [ now subst c; cbn; left | ].
    now apply Hade in Hb; cbn; right.
  } {
    cbn in Hb.
    destruct Hb as [Hb| Hb]; [ now left | ].
    now apply Hade in Hb; right.
  }
}
injection Hp; clear Hp; intros; subst ld lc.
split; [ easy | ].
split. {
  intros b Hb.
  destruct Hb as [Hb| Hb]; [ now subst c | ].
  now apply Hae.
}
intros b.
split; intros Hb. {
  destruct Hb as [Hb| Hb]. {
    now subst c; apply in_or_app; right; left.
  }
  apply Hade in Hb.
  apply in_app_or in Hb; apply in_or_app.
  destruct Hb as [Hb| Hb]; [ now left | now right; right ].
} {
  apply in_app_or in Hb.
  destruct Hb as [Hb| Hb]. {
    assert (H : b ∈ la) by now apply Hade, in_or_app; left.
    now right.
  }
  destruct Hb as [Hb| Hb]; [ now left | ].
  assert (H : b ∈ la) by now apply Hade, in_or_app; right.
  now right.
}
Qed.

Theorem in_ecl : ∀ A (eqv : A → _) r ec it la,
  (r, ec) ∈ ecl eqv it la
  → r ∈ la ∧ (∀ a, a ∈ ec → eqv r a = true).
Proof.
intros * Hecl.
revert r la ec Hecl.
induction it; intros; [ easy | cbn in Hecl ].
destruct la as [| b]; [ easy | ].
remember (partition (eqv b) la) as p eqn:Hp; symmetry in Hp.
destruct p as (lb, lc).
destruct Hecl as [Hecl| Hecl]. {
  injection Hecl; clear Hecl; intros; subst b ec.
  split; [ now left | ].
  intros a Hla.
  apply partition_rel in Hp.
  destruct Hp as (Hbb, Hbc).
  now apply Hbb.
}
split; [ | apply (IHit _ _ _ Hecl) ].
apply partition_rel in Hp.
destruct Hp as (Hbt & Hbf & Heq).
right; apply Heq.
apply in_or_app; right.
now apply IHit with (ec := ec).
Qed.

Theorem in_ecl_eqb : ∀ A (eqv : A → _),
  equivalence eqv →
  ∀ r ec it la,
  (r, ec) ∈ ecl eqv it la
  → list_eqv eqv (r :: ec) (filter (eqv r) la) = true.
Proof.
intros * Heqv * Hecl.
revert r ec la Hecl.
induction it; intros; [ easy | ].
destruct la as [| a]; [ easy | cbn ].
cbn in Hecl.
remember (partition (eqv a) la) as p eqn:Hp; symmetry in Hp.
destruct p as (lb, lc).
destruct Hecl as [Hecl| Hecl]. {
  injection Hecl; clear Hecl; intros; subst r ec; cbn.
  rewrite (proj1 Heqv), (proj1 Heqv).
  apply List_partition_filter_iff in Hp.
  destruct Hp as (Hb, Hc).
  rewrite Hb.
  apply <- (list_eqv_eq eqv a).
  split; [ easy | ].
  intros i Hi.
  apply (proj1 Heqv).
}
remember (eqv r a) as ra eqn:Hra; symmetry in Hra.
destruct ra. {
  exfalso.
  apply partition_rel in Hp.
  destruct Hp as (H1 & H2 & H3).
  destruct Heqv as (Hrefl & Hsymm & Htran).
  apply Hsymm in Hra.
  rewrite H2 in Hra; [ easy | ].
  now apply in_ecl in Hecl.
}
remember (filter (eqv r) la) as ld eqn:Hld; symmetry in Hld.
destruct ld as [| d]. {
  exfalso.
  specialize (proj1 (List_filter_nil_iff _ _) Hld) as H3.
  apply IHit in Hecl.
  cbn in Hecl.
  remember (filter (eqv r) lc) as le eqn:Hle; symmetry in Hle.
  destruct le as [| e]; [ easy | ].
  specialize (proj1 (filter_In (eqv r) e lc)) as H4.
  rewrite Hle in H4.
  specialize (H4 (or_introl eq_refl)).
  destruct H4 as (H4, H5).
  rewrite H5 in Hecl.
  rewrite H3 in H5; [ easy | ].
  apply partition_rel in Hp.
  destruct Hp as (Hp1 & Hp2 & Hp3).
  apply Hp3.
  now apply in_or_app; right.
}
remember (eqv r d) as rd eqn:Hrd; symmetry in Hrd.
destruct rd. 2: {
  exfalso.
  specialize (filter_In (eqv r) d la) as H4.
  rewrite Hld in H4.
  specialize (proj1 H4 (or_introl eq_refl)) as H5.
  destruct H5; congruence.
}
assert (H : filter (eqv r) la = filter (eqv r) lc). {
  apply List_partition_filter_iff in Hp.
  destruct Hp as (Hp1, Hp2).
  rewrite <- Hp2.
  symmetry.
  rewrite List_filter_filter.
  erewrite filter_ext_in. 2: {
    intros c Hc.
    now rewrite Bool.andb_comm.
  }
  rewrite <- List_filter_filter.
  erewrite filter_ext_in. 2: {
    intros b Hb.
    replace (eqv a b) with false. 2: {
      symmetry.
      apply filter_In in Hb.
      destruct Hb as (Hb1, Hb2).
      apply Bool.not_true_iff_false in Hra.
      apply Bool.not_true_iff_false.
      intros H; apply Hra.
      destruct Heqv as (Hrefl & Hsymm & Htran).
      apply Hsymm in H.
      now apply Htran with (b := b).
    }
    now cbn.
  }
  remember (filter (eqv r) la) as l eqn:Hl.
  clear.
  induction l as [| a]; [ easy | cbn ].
  now f_equal.
}
rewrite H in Hld.
specialize (IHit _ _ _ Hecl) as H1.
cbn in H1.
rewrite Hld in H1.
now rewrite Hrd in H1.
Qed.

Theorem isort_insert_isort : ∀ A (rel : A → _),
  transitive rel →
  connected_relation rel →
  ∀ a la,
  isort_insert rel a (isort rel la) = isort rel (isort_insert rel a la).
Proof.
intros * Htran Hcon *.
revert a.
induction la as [| b]; intros; [ easy | cbn ].
rewrite IHla.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; cbn; [ now rewrite IHla | ].
do 2 rewrite <- IHla.
clear IHla.
remember (isort rel la) as lb eqn:Hlb; symmetry in Hlb.
clear Hlb.
revert a b la Hab.
induction lb as [| c]; intros; cbn. {
  rewrite Hab.
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba; [ easy | ].
  now rewrite (Hcon a b Hab).
}
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
destruct bc. {
  cbn; rewrite Hab.
  remember (rel a c) as ac eqn:Hac; symmetry in Hac.
  destruct ac; cbn; rewrite Hbc; [ | easy ].
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba; [ easy | ].
  now rewrite (Hcon a b Hab Hba).
}
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
destruct ac; cbn; rewrite Hac, Hbc. {
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba; [ | easy ].
  now rewrite (Htran b a c Hba Hac) in Hbc.
}
f_equal.
now apply IHlb.
Qed.

Theorem isort_app_distr_l : ∀ A (eqb rel : A → _),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ la lb,
  isort rel (la ++ lb) = isort rel (isort rel la ++ lb).
Proof.
intros * Heqb Hant Htra Htot *.
(*
Compute (
  let rel := λ a b, fst a <? fst b in
  let la := [(1, 2); (1, 3); (1, 4)] in
  let lb := [(2, 1); (7, 1); (1, 1); (5, 1); (1, 7)] in
  isort rel (la ++ lb) = isort rel (isort rel la ++ lb)).
  isort rel (la ++ lb) = isort rel (la ++ isort rel lb)).
...
*)
apply (isort_when_permuted Heqb); [ easy | easy | easy | ].
apply (permutation_app Heqb); [ | now apply permutation_refl ].
now apply permuted_isort.
Qed.

Theorem isort_app_distr_r : ∀ A (eqb rel : A → _),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ la lb,
  isort rel (la ++ lb) = isort rel (la ++ isort rel lb).
Proof.
intros * Heqb Hant Htra Htot *.
apply (isort_when_permuted Heqb); [ easy | easy | easy | ].
apply (permutation_app Heqb); [ now apply permutation_refl | ].
now apply permuted_isort.
Qed.

Theorem all_permut_length : ∀ A (la : list A),
  length (all_permut la) = (length la)!.
Proof.
intros.
unfold all_permut.
destruct la as [| a]; [ easy | ].
unfold canon_sym_gr_list_list.
now rewrite map_length, List_map_seq_length.
Qed.

(*
Fixpoint list_prodn_nodup A (eqb : A → _) ll :=
  match ll with
  | [] => [[]]
  | l :: ll' =>
      let ll'' := list_prodn_nodup eqb ll' in
      flat_map
        (λ a,
         map (cons a) (filter (λ l', negb (member eqb a l')) ll''))
        l
  end.

Theorem list_prodn_nodup_list_prodn_nodup : ∀ A (eqb : A → _) ll,
  list_prodn_nodup eqb ll = filter (no_dup eqb) (list_prodn ll).
Proof.
intros.
induction ll as [| la]; [ easy | cbn ].
symmetry; rewrite flat_map_concat_map.
rewrite <- concat_filter_map; symmetry.
rewrite flat_map_concat_map.
rewrite map_map.
rewrite IHll.
erewrite map_ext_in. 2: {
  intros a Ha.
  rewrite List_filter_filter.
  remember (λ lb, _) as x; subst x.
  easy.
}
symmetry.
erewrite map_ext_in. 2: {
  intros a Ha.
  rewrite List_filter_map.
  easy.
}
cbn.
f_equal.
apply map_ext_in.
intros a Ha.
f_equal.
apply filter_ext_in.
intros lb Hlb.
now destruct (member eqb a lb).
Qed.
*)

Theorem list_prodn_repeat_length : ∀ A (l : list A) n,
  length (list_prodn (repeat l n)) = length l ^ n.
Proof.
intros.
revert l.
induction n; intros; [ easy | cbn ].
destruct l as [| a]; [ easy | cbn ].
rewrite app_length, map_length.
rewrite IHn; cbn; f_equal.
rewrite List_flat_map_length.
remember (∑ (b ∈ l), _) as x; subst x.
erewrite rngl_summation_list_eq_compat. 2: {
  intros b Hb.
  rewrite map_length, IHn; cbn.
  easy.
}
cbn - [ rngl_add rngl_zero ].
rewrite nat_summation_list_all_same.
apply Nat.mul_comm.
Qed.

(* new experimental list_prodn, named list_prodn'
   because I am tired of that "flat_mat" that appears
   each time I use list_prodn *)
Definition pair_cons {A} (ala : A * _) := fst ala :: snd ala.

Definition list_prodn' A (ll : list (list A)) :=
  fold_right (λ la ll', map pair_cons (list_prod la ll')) [[]] ll.

Theorem list_prodn_list_prodn' : ∀ A (ll : list (list A)),
  list_prodn ll = list_prodn' ll.
Proof.
intros.
induction ll as [| la]; [ easy | cbn ].
rewrite IHll; clear IHll.
induction la as [| a]; [ easy | cbn ].
rewrite map_app, map_map.
now rewrite IHla.
Qed.

(*
Search list_prodn.
About NoDup_list_prodn_repeat.

Compute (list_prod [[1;2];[3;4;5]] [[6;7;8];[9;10]]).

Fixpoint list_prodn_loop A (lla llb : list (list A)) :=
  match lla with
  | [] => []
  | [la] => map (λ a,
...

Definition list_prodn'' A (ll : list (list A)) := list_prodn_loop [[]] ll.
...
  | la :: ll' => map pair_cons (list_prod la (list_prodn'' ll'))
  end.
...
*)

Theorem incl_incl_permutation : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb, NoDup la → NoDup lb → la ⊂ lb → lb ⊂ la → permutation eqb la lb.
Proof.
intros * Heqb * Hnda Hndb Hla Hlb.
revert lb Hndb Hla Hlb.
induction la as [| a]; intros. {
  destruct lb as [| b]; [ easy | exfalso ].
  now specialize (Hlb b (or_introl eq_refl)).
}
assert (H : NoDup la) by now apply NoDup_cons_iff in Hnda.
specialize (IHla H); clear H.
(**)
specialize (Hla _ (or_introl eq_refl)) as Ha.
apply in_split in Ha.
destruct Ha as (l1 & l2 & H); subst lb.
apply (permutation_cons_app Heqb).
apply IHla. {
  apply NoDup_app_iff in Hndb.
  apply NoDup_app_iff.
  split; [ easy | ].
  destruct Hndb as (_ & H1 & H2).
  apply NoDup_cons_iff in H1.
  split; [ easy | ].
  intros c Hc Hc2.
  now specialize (H2 _ Hc); apply H2; right.
} {
  intros c Hc.
  unfold incl in Hla.
  specialize (Hla _ (or_intror Hc)).
  apply in_app_or in Hla.
  apply in_or_app.
  destruct Hla as [Hla| Hla]; [ now left | ].
  destruct Hla as [Hla| Hla]; [ | now right ].
  subst c.
  now apply NoDup_cons_iff in Hnda.
} {
  intros c Hc.
  unfold incl in Hla, Hlb.
  specialize (Hlb c).
  assert (H : c ∈ l1 ++ a :: l2). {
    apply in_app_or in Hc.
    apply in_or_app.
    destruct Hc as [Hc| Hc]; [ now left | ].
    now right; right.
  }
  specialize (Hlb H); clear H.
  destruct Hlb as [Hca| Hca]; [ | easy ].
  subst c.
  apply NoDup_app_iff in Hndb.
  apply in_app_or in Hc.
  destruct Hndb as (H1 & H2 & H3).
  destruct Hc as [Hc| Hc]. {
    specialize (H3 _ Hc).
    now exfalso; apply H3; left.
  }
  now apply NoDup_cons_iff in H2.
}
Qed.

Theorem permutation_no_dup_prodn_repeat_flat_all_permut_sub_lists : ∀ n m,
  permutation (list_eqv eqb)
    (filter (no_dup Nat.eqb) (prodn_repeat_seq 1 n m))
    (flat_map all_permut (sub_lists_of_seq_1_n n m)).
Proof.
intros.
assert (Hel : equality (list_eqv eqb)). {
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
}
apply permut_if_isort with (rel := list_leb Nat.leb); [ easy | ].
specialize Nat_leb_trans as Htra.
rewrite isort_when_sorted. 2: {
  rewrite <- list_prodn_prodn_repeat.
  apply sorted_filter; [ now apply transitive_list_leb | ].
  apply sorted_list_ltb_leb_incl.
  apply list_prodn_repeat_seq_ltb_sorted.
}
symmetry.
unfold sub_lists_of_seq_1_n.
rewrite flat_map_concat_map.
rewrite <- list_prodn_prodn_repeat.
rewrite <- flat_map_concat_map.
set (la := flat_map all_permut (sls1n 1 n m)).
set (lb := filter (no_dup Nat.eqb) (list_prodn (repeat (seq 1 n) m))).
assert (Hab : la ⊂ lb). {
  subst la lb.
  intros la Hla.
  apply in_flat_map in Hla.
  destruct Hla as (lb & Hlb & Hla).
  apply in_sls1n_iff in Hlb.
  destruct Hlb as [Hlb| Hlb]. {
    destruct Hlb; subst m lb.
    destruct Hla as [Hla| ]; [ subst la | easy ].
    cbn; now left.
  }
  destruct Hlb as (Hsb & Hlb & Hb).
  apply filter_In.
  split. {
    apply in_list_prodn_repeat_iff.
    destruct m; [ left | right ]. {
      apply length_zero_iff_nil in Hlb; subst lb.
      now destruct Hla.
    }
    split; [ easy | ].
    apply in_all_permut_permutation in Hla.
    split. {
      apply (permutation_length Nat.eqb_eq) in Hla; congruence.
    }
    intros i Hi.
    specialize (permutation_in_iff Nat.eqb_eq Hla) as H1.
    apply H1 in Hi.
    specialize (Hb _ Hi) as H2.
    split; [ easy | now apply Nat.lt_succ_r ].
  }
  apply in_all_permut_permutation in Hla.
  apply (no_dup_NoDup Nat.eqb_eq).
  apply (sorted_NoDup Nat.ltb_irrefl Nat_ltb_trans) in Hsb.
  apply (permutation_sym Nat.eqb_eq) in Hla.
  now apply (permutation_NoDup Nat.eqb_eq) in Hla.
}
assert (Hba : lb ⊂ la). {
  subst la lb.
  intros la Hla.
  apply filter_In in Hla.
  destruct Hla as (Hla, Hnd).
  apply (no_dup_NoDup Nat.eqb_eq) in Hnd.
  apply in_flat_map.
  apply (in_list_prodn_iff 0) in Hla.
  rewrite repeat_length in Hla.
  destruct Hla as (Hm, Hla).
  rewrite Hm in Hla.
  assert (H : ∀ i, i < m → 1 ≤ nth i la 0 ≤ n). {
    intros i Hi.
    specialize (Hla _ Hi) as H1.
    rewrite List_nth_repeat in H1.
    destruct (lt_dec i m); [ | easy ].
    apply in_seq in H1.
    split; [ easy | now apply Nat.lt_succ_r ].
  }
  clear Hla; rename H into Hla.
  exists (isort Nat.leb la).
  split. 2: {
    apply permutation_in_all_permut.
    apply permuted_isort; unfold equality.
    apply Nat.eqb_eq.
  }
  apply in_sls1n_iff.
  rewrite isort_length.
  right.
  split. {
    apply NoDup_sorted_nat_leb_ltb. 2: {
      apply sorted_isort; apply Nat_leb_total_relation.
    }
    apply (permutation_NoDup Nat.eqb_eq) with (la := la); [ | easy ].
    apply permuted_isort.
    unfold equality.
    apply Nat.eqb_eq.
  }
  split; [ easy | ].
  intros j Hj.
  apply in_isort in Hj.
  apply (In_nth _ _ 0) in Hj.
  destruct Hj as (k & Hk & Hj).
  rewrite Hm in Hk.
  specialize (Hla k Hk) as H1.
  rewrite Hj in H1.
  split; [ easy | now apply Nat.lt_succ_r ].
}
rewrite <- isort_when_sorted with (rel := list_leb Nat.leb) (l := lb). 2: {
  unfold lb.
  apply sorted_filter; [ apply transitive_list_leb, Nat_leb_trans | ].
  apply sorted_list_ltb_leb_incl.
  apply list_prodn_repeat_seq_ltb_sorted.
}
apply (isort_when_permuted Hel). {
  apply antisymmetric_list_leb, Nat_leb_antisym.
} {
  apply transitive_list_leb, Nat_leb_trans.
} {
  apply total_relation_list_leb, Nat_leb_total_relation.
}
apply (incl_incl_permutation Hel); [ | | easy | easy ]. {
  unfold la.
  rewrite flat_map_concat_map.
  apply NoDup_concat_if. {
    intros lc Hlc.
    apply in_map_iff in Hlc.
    destruct Hlc as (ld & H & Hld); subst lc.
    apply NoDup_all_permut.
    apply in_sls1n_iff in Hld.
    destruct Hld as [Hld| Hld]. {
      destruct Hld; subst m ld; constructor.
    }
    destruct Hld as (Hs & Hdm & Hld).
    now apply (sorted_NoDup Nat.ltb_irrefl Nat_ltb_trans).
  }
  intros i j Hij lc Hlci Hlcj.
  apply Hij; clear Hij.
  destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
    subst m.
    rewrite sls1n_0_r in Hlci, Hlcj.
    cbn in Hlci, Hlcj.
    destruct i; [ | now rewrite Tauto_match_nat_same in Hlci ].
    destruct j; [ | now rewrite Tauto_match_nat_same in Hlcj ].
    easy.
  }
  destruct (lt_dec i (binomial n m)) as [Hinm| Hinm]. 2: {
    apply Nat.nlt_ge in Hinm.
    rewrite nth_overflow in Hlci; [ easy | ].
    now rewrite map_length, sls1n_length.
  }
  destruct (lt_dec j (binomial n m)) as [Hjnm| Hjnm]. 2: {
    apply Nat.nlt_ge in Hjnm.
    rewrite nth_overflow in Hlcj; [ easy | ].
    now rewrite map_length, sls1n_length.
  }
  rewrite (List_map_nth' []) in Hlci; [ | now rewrite sls1n_length ].
  rewrite (List_map_nth' []) in Hlcj; [ | now rewrite sls1n_length ].
  apply in_all_permut_permutation in Hlci.
  apply in_all_permut_permutation in Hlcj.
  apply (permutation_sym Nat.eqb_eq) in Hlci.
  eapply (permutation_trans Nat.eqb_eq) in Hlcj; [ | apply Hlci ].
  specialize sorted_sorted_permuted as H1.
  apply (H1 _ _ Nat.ltb) in Hlcj; cycle 1. {
    unfold equality; apply Nat.eqb_eq.
  } {
    apply Nat_ltb_antisym.
  } {
    apply Nat_ltb_trans.
  } {
    apply (sls1n_are_sorted 1 n m), nth_In.
    now rewrite sls1n_length.
  } {
    apply (sls1n_are_sorted 1 n m), nth_In.
    now rewrite sls1n_length.
  }
  now apply sls1n_inj in Hlcj.
} {
  unfold lb.
  apply NoDup_filter.
  apply NoDup_list_prodn_repeat.
}
Qed.

Theorem rngl_summation_list_prodn_repeat_filter_no_dup :
  rngl_has_opp = true →
  rngl_has_eqb = true →
  ∀ n m f,
  ∑ (kl ∈ prodn_repeat_seq 1 n m), ε kl * f kl =
  ∑ (kl ∈ filter (no_dup Nat.eqb) (prodn_repeat_seq 1 n m)), ε kl * f kl.
Proof.
intros Hopp Heqb *.
assert (Hel : equality (list_eqv eqb)). {
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
}
set (g := no_dup Nat.eqb).
erewrite (rngl_summation_list_permut _ Hel). 2: {
  assert (H : ∀ ll,
    permutation (list_eqv eqb) ll
      (filter g ll ++ filter (λ l, negb (g l)) ll)). {
    now apply permutation_filter_app_filter.
  }
  apply H.
}
rewrite rngl_summation_list_app.
rewrite rngl_add_comm.
rewrite all_0_rngl_summation_list_0. 2: {
  intros kl Hkl.
  apply filter_In in Hkl.
  destruct Hkl as (Hkl, Hsl).
  unfold g in Hsl.
  apply Bool.negb_true_iff in Hsl.
  rewrite ε_when_dup; [ | easy | easy | ]. 2: {
    intros H.
    apply (no_dup_NoDup Nat.eqb_eq) in H.
    congruence.
  }
  now apply rngl_mul_0_l; left.
}
subst g.
rewrite rngl_add_0_l.
easy.
Qed.

Theorem rngl_summation_list_prodn_sub_lists_all_permut :
  rngl_has_opp = true →
  rngl_has_eqb = true →
  ∀ n m f,
  ∑ (kl ∈ list_prodn (repeat (seq 1 n) m)), ε kl * f kl =
  ∑ (jl ∈ sub_lists_of_seq_1_n n m), ∑ (kl ∈ all_permut jl), ε kl * f kl.
Proof.
intros Hopp Heqb *.
rewrite list_prodn_prodn_repeat.
rewrite rngl_summation_summation_list_flat_map; cbn.
assert (Hel : equality (list_eqv eqb)). {
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
}
rewrite rngl_summation_list_prodn_repeat_filter_no_dup; [ | easy | easy ].
apply (rngl_summation_list_permut _ Hel).
apply permutation_no_dup_prodn_repeat_flat_all_permut_sub_lists.
Qed.

Theorem map_collapse_all_permut_seq : ∀ i la n m,
  la ∈ sub_lists_of_seq_1_n n m
  → map (λ lb, map (add i) (collapse lb)) (all_permut la) =
    all_permut (seq i (length la)).
Proof.
intros * Hla.
destruct la as [| a]; intros; [ easy | ].
cbn - [ all_permut seq ].
unfold all_permut.
rewrite <- cons_seq at 1.
rewrite seq_length.
rewrite map_map.
apply map_ext_in.
intros lb Hlb.
apply in_map_iff in Hlb.
destruct Hlb as (k & Hlb & Hk).
apply in_seq in Hk; destruct Hk as (_, Hk); rewrite Nat.add_0_l in Hk.
subst lb.
erewrite map_ext_in with (f := λ j, nth _ (seq _ _) _). 2: {
  intros j Hj.
  apply in_canon_sym_gr_list in Hj; [ | easy ].
  now rewrite seq_nth.
}
f_equal.
clear i.
erewrite map_ext_in. 2: {
  intros j Hj.
  rewrite nth_indep with (d' := 0). 2: {
    now apply in_canon_sym_gr_list in Hj.
  }
  easy.
}
remember (a :: la) as lb eqn:Hlb.
replace (S (length la)) with (length lb) in Hk |-* by now subst lb.
clear a la Hlb; rename lb into la.
rewrite fold_comp_list.
apply in_sls1n_iff in Hla.
destruct Hla as [Hla| Hla]; [ now destruct Hla; subst m la | ].
destruct Hla as (Hs & Hlam & Hla).
rewrite collapse_comp; cycle 1. {
  now apply (sorted_NoDup Nat.ltb_irrefl Nat_ltb_trans).
} {
  now apply canon_sym_gr_list_permut_seq.
} {
  symmetry; apply canon_sym_gr_list_length.
}
rewrite eq_sorted_collapse_seq; [ | now apply sorted_nat_ltb_leb_incl ].
apply comp_1_l.
intros i Hi.
now apply in_canon_sym_gr_list in Hi.
Qed.

Theorem isort_insert_lb_app : ∀ A (rel : A → _) a lsorted,
  lsorted = [] ∨ rel a (hd a lsorted) = true
  → isort_insert rel a lsorted = a :: lsorted.
Proof.
intros * Ha.
destruct Ha as [Ha| Ha]; [ now subst lsorted | ].
revert a Ha.
induction lsorted as [| b]; intros; [ easy | cbn ].
remember (rel a b) as ab eqn:Hab.
destruct ab; [ easy | ].
cbn in Ha.
now rewrite <- Hab in Ha.
Qed.

Theorem isort_insert_ub_app : ∀ A (rel : A → _) a lsorted,
  (∀ b, b ∈ lsorted → rel a b = false)
  → isort_insert rel a lsorted = lsorted ++ [a].
Proof.
intros * Ha.
revert a Ha.
induction lsorted as [| b]; intros; [ easy | cbn ].
remember (rel a b) as ab eqn:Hab.
destruct ab. 2: {
  f_equal.
  apply IHlsorted.
  intros c Hc.
  now apply Ha; right.
}
specialize (Ha _ (or_introl eq_refl)).
congruence.
Qed.

Theorem isort_rank_insert_lb_app : ∀ A B (rel : A → _) (f : B → _) ia lrank,
  lrank = [] ∨ rel (f ia) (f (hd ia lrank)) = true
  → isort_rank_insert rel f ia lrank = ia :: lrank.
Proof.
intros * Ha.
destruct Ha as [Ha| Ha]; [ now subst lrank | ].
induction lrank as [| ib]; [ easy | cbn ].
remember (rel (f ia) (f ib)) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ easy | ].
cbn in Ha; congruence.
Qed.

Theorem isort_rank_insert_ub_app : ∀ A B (rel : A → _) (f : B → _) ia lrank,
  (∀ ib, ib ∈ lrank → rel (f ia) (f ib) = false)
  → isort_rank_insert rel f ia lrank = lrank ++ [ia].
Proof.
intros * Ha.
induction lrank as [| ib]; [ easy | cbn ].
remember (rel (f ia) (f ib)) as ab eqn:Hab; symmetry in Hab.
destruct ab. 2: {
  f_equal.
  apply IHlrank.
  intros ic Hic.
  now apply Ha; right.
}
rewrite Ha in Hab; [ easy | now left ].
Qed.

(* to be completed
Theorem cauchy_binet_formula : in_charac_0_field →
  ∀ m n A B,
  is_correct_matrix A = true
  → is_correct_matrix B = true
  → mat_nrows A = m
  → mat_ncols A = n
  → mat_nrows B = n
  → mat_ncols B = m
  → det (A * B) =
     ∑ (jl ∈ sub_lists_of_seq_1_n n m),
     det (mat_select_cols jl A) * det (mat_select_rows jl B).
Proof.
intros Hif * Hca Hcb Har Hac Hbr Hbc.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  move Hmz at top; subst m.
  apply is_scm_mat_iff in Hcb.
  destruct Hcb as (Hcrb, Hclb).
  specialize (Hcrb Hbc) as H1.
  rewrite Hbr in H1.
  move H1 at top; subst n.
  destruct A as (lla).
  destruct B as (llb).
  cbn in Har, Hbr.
  apply length_zero_iff_nil in Har, Hbr.
  subst lla llb; cbn.
  rewrite rngl_summation_list_only_one; cbn.
  symmetry; apply rngl_mul_1_l.
}
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  apply is_scm_mat_iff in Hca.
  destruct Hca as (Hcra, Hcla).
  specialize (Hcra Hac) as H1.
  now rewrite Har in H1.
}
assert (Hab : is_square_matrix (A * B) = true). {
  apply is_scm_mat_iff.
  split. {
    rewrite mat_mul_ncols; [ | now rewrite Har ].
    now intros H; rewrite H in Hbc; symmetry in Hbc.
  } {
    intros l Hl.
    rewrite mat_mul_nrows, Har.
    apply In_nth with (d := []) in Hl.
    destruct Hl as (p & Hp & Hl).
    rewrite <- Hl; cbn.
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
      cbn in Hp.
      now rewrite List_map_seq_length in Hp.
    }
    now rewrite List_map_seq_length.
  }
}
rewrite det_is_det''; try now destruct Hif.
unfold det''.
rewrite mat_mul_nrows, Har.
unfold "*"%M at 1.
unfold mat_mul_el.
rewrite Har, Hac, Hbc.
cbn - [ det ].
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    specialize (fact_neq_0 m) as Hm.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
    rewrite seq_nth; [ | flia Hi ].
    rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
    assert (Him : l.(i) - 1 < m). {
      apply in_all_comb_iff in Hl.
      destruct Hl as [Hl| Hl]; [ easy | ].
      destruct Hl as (_ & Hlm & Hl).
      assert (H : l.(i) ∈ l). {
        apply nth_In.
        rewrite Hlm; flia Hi.
      }
      specialize (Hl _ H); clear H.
      flia Hl.
    }
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite Nat.add_comm, Nat.sub_add. 2: {
      apply in_all_comb_iff in Hl.
      destruct Hl as [Hl| Hl]; [ easy | ].
      destruct Hl as (_ & Hlm & Hl).
      assert (H : nth (i - 1) l 0 ∈ l). {
        apply nth_In.
        rewrite Hlm; flia Hi.
      }
      now specialize (Hl _ H); clear H.
    }
    easy.
  }
  easy.
}
cbn - [ det ].
remember (∑ (kl ∈ _), _) as x; subst x. (* renaming *)
(*
  ∑ (l ∈ all_comb m),
  ε l *
  ∏ (i = 1, m), (∑ (j = 1, n), mat_el A i j * mat_el B j kl.(i))
*)
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  rewrite rngl_product_summation_distr_prodn; [ | | easy ]. 2: {
    now destruct Hif; left.
  }
  erewrite rngl_summation_list_eq_compat. 2: {
    intros l1 Hl1.
    rewrite rngl_product_mul_distr; [ | now destruct Hif ].
    easy.
  }
  cbn.
  rewrite rngl_mul_summation_list_distr_l; [ | now destruct Hif; left ].
  easy.
}
cbn - [ det ].
rewrite rngl_summation_summation_list_swap.
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
  erewrite rngl_summation_list_eq_compat. 2: {
    intros l1 Hl1.
    rewrite rngl_mul_comm; [ | now destruct Hif ].
    rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
    rewrite <- rngl_mul_assoc.
    easy.
  }
  cbn.
  rewrite <- rngl_mul_summation_list_distr_l; [ | now destruct Hif; left ].
  remember (∑ (l ∈ _), _) as x eqn:Hx; subst x. (* renaming *)
  easy.
}
cbn - [ det ].
remember (∑ (kl ∈ _), _) as x; subst x. (* renaming *)
(*
  ∑ (kl ∈ list_prodn (repeat (seq 1 n) m)),
  ∏ (i = 1, m), mat_el A i kl.(i) *
  (∑ (l ∈ all_comb m), ε l * ∏ (i = 1, m), mat_el B kl.(i) l.(i)) =
*)
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  replace (∑ (i ∈ all_comb m), ε i * ∏ (j = _, _), _) with
    (det (mat_select_rows l B)). 2: {
    generalize Hl; intros H.
    apply in_list_prodn_repeat_iff in H.
    destruct H as [H| H]; [ easy | ].
    destruct H as (_ & Hlm & Hln).
    rewrite det_is_det''; try now destruct Hif. 2: {
      apply mat_select_rows_is_square; [ easy | congruence | ].
      rewrite Hbr.
      intros j Hj.
      now apply Hln.
    }
    unfold det''.
    rewrite mat_select_rows_nrows, Hlm.
    apply rngl_summation_list_eq_compat.
    intros l1 Hl1.
    f_equal.
    apply rngl_product_eq_compat.
    intros i Hi.
    unfold mat_select_rows, mat_el; cbn.
    rewrite (List_map_nth' 0); [ | rewrite Hlm; flia Hi ].
    assert (H1 : l1.(i) - 1 < m). {
      apply in_list_prodn_repeat_iff in Hl1.
      destruct Hl1 as [Hl1| Hl1]; [ easy | ].
      destruct Hl1 as (_ & Hl1m & Hl1).
      specialize (Hl1 (nth (i - 1) l1 0)).
      assert (H : nth (i - 1) l1 0 ∈ l1). {
        apply nth_In; rewrite Hl1m; flia Hi.
      }
      specialize (Hl1 H); clear H.
      flia Hl1.
    }
    rewrite (List_map_nth' 0); [ | now rewrite seq_length, Hbc ].
    rewrite seq_nth; [ | now rewrite Hbc ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
cbn - [ det ].
remember (∑ (kl ∈ _), _) as x; subst x. (* renaming *)
(*
  ∑ (kl ∈ list_prodn (repeat (seq 1 n) m)),
  ∏ (i = 1, m), mat_el A i kl.(i) * det (mat_select_rows kl B) =
*)
erewrite rngl_summation_list_eq_compat. 2: {
  intros la Hla.
  rewrite (det_isort_rows Hif _ _ Hcb); cycle 1. {
    apply in_list_prodn_length in Hla.
    rewrite repeat_length in Hla.
    congruence.
  } {
    intros k Hk.
    apply in_list_prodn_repeat_iff in Hla.
    destruct Hla as [| Hla]; [ easy | ].
    destruct Hla as (_ & Hlam & Hla).
    rewrite Hbr.
    now apply Hla.
  }
  rewrite rngl_mul_assoc.
  assert (H : rngl_is_comm = true) by now destruct Hif.
  rewrite (rngl_mul_comm H _ (ε la)); clear H.
  easy.
}
cbn - [ det ].
remember (∑ (kl ∈ _), _) as x; subst x. (* renaming *)
(*
  ∑ (kl ∈ list_prodn (repeat (seq 1 n) m)),
  ε kl * ∏ (i = 1, m), mat_el A i kl.(i) *
  det (mat_select_rows (isort Nat.leb kl) B) =
*)
erewrite rngl_summation_list_eq_compat. 2: {
  intros la Hla.
  now rewrite <- rngl_mul_assoc.
}
cbn - [ det ].
rewrite rngl_summation_list_prodn_sub_lists_all_permut; cycle 1. {
  now destruct Hif.
} {
  now destruct Hif.
}
apply rngl_summation_list_eq_compat.
intros jl Hjl.
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
  replace (isort Nat.leb kl) with jl. 2: {
    symmetry.
    apply in_all_permut_permutation in Hkl.
    rewrite (isort_when_permuted Nat.eqb_eq) with (lb := jl); cycle 1. {
      apply Nat_leb_antisym.
    } {
      apply Nat_leb_trans.
    } {
      apply Nat_leb_total_relation.
    } {
      easy.
    }
    apply isort_when_sorted.
    apply (sub_lists_of_seq_1_n_are_sorted n m) in Hjl; [ | easy ].
    now apply sorted_nat_ltb_leb_incl.
  }
  rewrite rngl_mul_assoc.
  easy.
}
cbn - [ det ].
rewrite <- rngl_mul_summation_list_distr_r; [ | now destruct Hif; left ].
f_equal; symmetry.
remember (∑ (kl ∈ _), _) as x; subst x.
rewrite det_is_det''; try now destruct Hif. 2: {
  generalize Hjl; intros H.
  apply in_sub_lists_of_seq_1_n_length in H.
  apply mat_select_cols_is_square; [ easy | congruence | ].
  rewrite Hac.
  intros j Hj.
  now apply sub_lists_of_seq_1_n_bounds with (a := j) in Hjl.
}
unfold det''.
rewrite mat_select_cols_nrows; [ | | congruence ]. 2: {
  now apply sub_lists_of_seq_1_n_are_correct in Hjl.
}
rewrite Har.
remember (∑ (kl ∈ _), _) as x; subst x.
unfold all_comb.
rewrite rngl_summation_list_prodn_sub_lists_all_permut; cycle 1. {
  now destruct Hif.
} {
  now destruct Hif.
}
remember (∑ (jl' ∈ _), _) as x; subst x.
unfold sub_lists_of_seq_1_n.
rewrite sls1n_diag.
rewrite rngl_summation_list_only_one.
(*
  ============================
  ∑ (kl ∈ all_permut (seq 1 m)), ε kl * ∏ (i = 1, m), mat_el (mat_select_cols jl A) i kl.(i) =
  ∑ (kl ∈ all_permut jl), ε kl * ∏ (i = 1, m), mat_el A i kl.(i)
*)
generalize Hjl; intros H.
apply in_sls1n_iff in H.
destruct H as [H| H]; [ easy | ].
destruct H as (Hsj & Hjm & Hjlb).
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
  apply in_all_permut_iff in Hkl.
  generalize Hkl; intros Hpk.
  apply (permut_if_isort _ Nat.eqb_eq) in Hpk.
  rewrite (@isort_when_sorted _ _ (seq 1 m)) in Hkl. 2: {
    apply sorted_nat_ltb_leb_incl.
    apply sorted_seq.
  }
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite mat_select_cols_el; cycle 1. {
      now rewrite Har.
    } {
      rewrite Hjm.
      assert (Hklen : length kl = m). {
        apply (f_equal length) in Hkl.
        now rewrite isort_length, seq_length in Hkl.
      }
      rewrite <- Hklen in Hpk.
      specialize (permutation_in_iff Nat.eqb_eq) as Hp.
      specialize (Hp _ _ Hpk).
      assert (H : kl.(i) ∈ kl). {
        apply nth_In; rewrite Hklen; flia Hi.
      }
      apply Hp in H.
      rewrite Hklen in H.
      apply in_seq in H.
      split; [ easy | flia H ].
    } {
      rewrite Hac.
      intros j Hj.
      specialize (Hjlb jl.(j)).
      assert (H : jl.(j) ∈ jl) by (apply nth_In; flia Hj).
      specialize (Hjlb H); clear H.
      flia Hjlb.
    }
    easy.
  }
  now cbn.
}
remember (∑ (kl ∈ _), _) as x; subst x.
symmetry.
set (g1 := λ l, jl ° collapse l).
set (h1 := λ l, map S (collapse l)).
rewrite rngl_summation_list_change_var with (g := g1) (h := h1). 2: {
  intros kl Hkl.
  unfold g1, h1.
  replace (collapse (map S (collapse kl))) with (collapse kl). 2: {
    symmetry.
    unfold collapse at 1 3; f_equal.
    specialize (isort_rank_map_add_compat 1 0) as H1.
    rewrite H1; cbn.
    rewrite map_id.
    unfold collapse.
    apply permut_isort_rank_involutive.
    apply isort_rank_permut_seq.
  }
  apply in_all_permut_permutation in Hkl.
  apply sorted_permuted_comp_collapse. 2: {
    now apply (permutation_sym Nat.eqb_eq).
  }
  now apply sorted_nat_ltb_leb_incl.
}
replace (map h1 (all_permut jl)) with (all_permut (seq 1 m)). 2: {
  symmetry.
  unfold h1.
  specialize (map_collapse_all_permut_seq 1 _ _ _ Hjl) as H1.
  replace (add 1) with S in H1 by easy.
  now rewrite Hjm in H1.
}
remember (∑ (kl ∈ _), _) as x; subst x.
apply rngl_summation_list_eq_compat.
intros kl Hkl.
f_equal. {
  unfold g1.
  assert (Hndj : NoDup jl). {
    apply sorted_NoDup in Hsj; [ easy | | ]. {
      unfold irreflexive; apply Nat.ltb_irrefl.
    } {
      apply Nat_ltb_trans.
    }
  }
  assert (Hkm : length kl = m). {
    apply in_all_permut_permutation in Hkl.
    apply (permutation_length Nat.eqb_eq) in Hkl.
    now rewrite seq_length in Hkl.
  }
  rewrite <- ε_collapse_ε. 2: {
    apply NoDup_comp_iff; [ | easy ].
    rewrite Hjm, <- Hkm.
    apply collapse_permut_seq_with_len.
  }
  rewrite collapse_comp; [ | easy | | ]; cycle 1. {
    apply isort_rank_permut_seq.
  } {
    rewrite collapse_length; congruence.
  }
  symmetry.
  rewrite <- ε_collapse_ε. 2: {
    apply in_all_permut_permutation in Hkl.
    apply (permutation_sym Nat.eqb_eq) in Hkl.
    apply (permutation_NoDup Nat.eqb_eq) in Hkl; [ easy | ].
    apply seq_NoDup.
  }
  symmetry.
  rewrite (sign_comp Hif). 2: {
    rewrite collapse_length, Hjm, <- Hkm.
    apply collapse_permut_seq_with_len.
  }
  replace (collapse jl) with (seq 0 (length jl)). 2: {
    symmetry.
    apply sorted_nat_ltb_leb_incl in Hsj.
    apply eq_sorted_isort_rank_seq in Hsj.
    unfold collapse; rewrite Hsj.
    rewrite Hjm.
    assert (H : sorted Nat.leb (seq 0 m)). {
      apply sorted_nat_ltb_leb_incl, sorted_seq.
    }
    specialize (eq_sorted_isort_rank_seq H) as H1; clear H.
    now rewrite seq_length in H1.
  }
  now rewrite ε_seq, rngl_mul_1_l.
}
unfold g1.
apply rngl_product_eq_compat.
intros i Hi.
f_equal.
remember (i - 1) as j.
remember (nth j kl 0 - 1) as k.
unfold comp_list.
assert (Hkm : length kl = m). {
  apply in_all_permut_permutation in Hkl.
  apply (permutation_length Nat.eqb_eq) in Hkl.
  now rewrite seq_length in Hkl.
}
rewrite (List_map_nth' 0). 2: {
  rewrite collapse_length, Hkm, Heqj.
  flia Hi.
}
f_equal.
subst k.
apply in_all_permut_permutation in Hkl.
Theorem permutation_seq_collapse : ∀ sta la,
  permutation Nat.eqb la (seq sta (length la))
  → collapse la = map (λ i, i - sta) la.
Proof.
intros * Hp.
remember (length la) as len eqn:Hlen; symmetry in Hlen.
revert sta la Hlen Hp.
induction len; intros. {
  now apply length_zero_iff_nil in Hlen; subst la.
}
apply (permutation_sym Nat.eqb_eq) in Hp.
rewrite seq_S in Hp.
eapply (permutation_trans Nat.eqb_eq) in Hp. 2: {
  apply (permutation_cons_append Nat.eqb_eq).
}
apply permutation_cons_l_iff in Hp.
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Haft).
apply Nat.eqb_eq in H; subst x.
subst la.
rewrite app_length in Hlen; cbn in Hlen.
rewrite Nat.add_succ_r in Hlen.
apply Nat.succ_inj in Hlen.
rewrite <- app_length in Hlen.
apply (permutation_sym Nat.eqb_eq) in Hp.
specialize (IHlen _ _ Hlen Hp) as H1.
rewrite map_app.
remember (sta + len) as n eqn:Hn; cbn.
replace (n - sta) with len by now rewrite Hn, Nat.add_comm, Nat.add_sub.
Theorem collapse_app_cons : ∀ la lb a,
  (∀ b, b ∈ la ++ lb → b < a)
  → collapse (la ++ a :: lb) =
     firstn (length la) (collapse (la ++ lb)) ++
     length (la ++ lb) :: skipn (length la) (collapse (la ++ lb)).
Proof.
intros * Hab.
(*
Compute (
let la := [13; 34; 15] in
let lb := [8; 5; 17; 40] in
let a := 41 in
    collapse (la ++ a :: lb) =
     firstn (length la) (collapse (la ++ lb)) ++
     length (la ++ lb) :: skipn (length la) (collapse (la ++ lb))
).
...
*)
revert a lb Hab.
induction la as [| b]; intros. {
  cbn - [ nth ]; cbn in Hab.
  rewrite isort_rank_insert_ub_app. 2: {
    intros ib Hb.
    rewrite List_nth_0_cons.
    apply Nat.leb_gt, Hab.
    apply in_map_iff in Hb.
    destruct Hb as (ic & H & Hc); subst ib; cbn.
    apply in_isort_rank in Hc.
    now apply nth_In.
  }
  induction lb as [| ib]; [ easy | ].
  cbn - [ nth ].
  remember (isort_rank_insert _ _ _ _) as la eqn:Hla.
  generalize Hla; intros Hlab.
  apply (f_equal length) in Hlab.
  rewrite isort_rank_insert_length in Hlab.
  rewrite map_length, isort_rank_length in Hlab.
  rewrite <- Hlab.
(*
  assert (Hs : sorted Nat.leb la). {
    rewrite Hla.
    apply sorted_isort_rank_insert. {
      apply Nat_leb_trans.
    } {
      apply Nat_leb_total_relation.
    } {
      intros ia ic Hia Hic.
      destruct Hia as [Hia| Hia]. {
        subst ia; rewrite List_nth_0_cons.
        destruct Hic as [Hic| Hic]. {
          subst ic; rewrite List_nth_0_cons.
          now do 2 rewrite Nat.leb_refl.
        }
        apply in_map_iff in Hic.
        destruct Hic as (id & H & Hid); subst ic.
        rewrite List_nth_succ_cons.
        cbn; apply Nat.leb_le.
        generalize Hid; intros Hidb.
        apply in_isort_rank in Hidb.
...
        apply in_isort_rank in Hid; cbn.
...
*)
Theorem isort_rank_app_map_S_zero : ∀ la,
  isort_rank Nat.leb (map S la ++ [0]) =
  length la :: isort_rank Nat.leb la.
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn - [ nth ].
rewrite IHla.
clear IHla.
cbn - [ nth ].
rewrite List_nth_0_cons.
rewrite List_nth_succ_cons.
rewrite app_nth2; [ | now rewrite map_length; unfold ge ].
rewrite map_length, Nat.sub_diag, List_nth_0_cons.
cbn - [ nth ].
f_equal.
rewrite isort_rank_insert_lb_app. 2: {
  rename a into ia.
  rewrite List_nth_0_cons.
  destruct la as [| ib]; [ now left | right ].
  rewrite List_hd_nth_0.
  rewrite (List_map_nth' 0); [ | now rewrite isort_rank_length; cbn ].
  rewrite List_nth_succ_cons.
  rewrite app_nth1. 2: {
    rewrite map_length; cbn - [ nth ].
    apply isort_rank_insert_ub; [ easy | ].
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & H & Hj); subst i.
    apply -> Nat.succ_lt_mono.
    now apply in_isort_rank in Hj.
  }
  cbn - [ nth "<=?" ].
  remember (isort_rank_insert Nat.leb (λ i : nat, nth i (ib :: la) ib) 0
    (map S (isort_rank Nat.leb la))) as lb eqn:Hlb.
  symmetry in Hlb.
  destruct lb as [| ic]. {
About neq_isort_insert_nil.
...
    apply neq_isort_rank_insert_nil in Hlb.
...
  cbn - [ nth ] in IHla.
...
Search (nth _ (isort_rank_insert _ _ _ _)).
...
  intros ib Hib.
  apply in_map_iff in Hib.
  destruct Hib as (ic & H & Hic); subst ib.
  generalize Hic; intros H.
  apply in_isort_rank in H.
  rewrite List_nth_succ_cons.
  apply Nat.leb_le; cbn.
  rewrite app_nth1; [ | now rewrite map_length ].
  rewrite (List_map_nth' 0); [ | easy ].
  apply -> Nat.succ_le_mono.
...
  }
  apply Nat.nle_gt in Ha.
    rewrite (List_map_nth' 0); [ | easy ].
  destruct (le_dec a (nth ic la 0)) as [Ha| Ha]. {
...
  rewrite (List_map_nth' []).
  cbn - [ map ].
...
Search isort_rank_insert.
...
apply isort_rank_insert_eq_compat.
intros ia ib Hia Hib.
destruct Hia as [Hia| Hia].
...
  rewrite eq_sorted_isort_rank_insert_seq. 2: {
    intros ic Hic.
    rewrite List_nth_0_cons.
    apply in_map_iff in Hic.
    destruct Hic as (id & H & Hid); subst ic.
    rewrite List_nth_succ_cons.
    apply in_isort_rank in Hid.
...
  rewrite isort_insert_ub_app. 2: {
    intros b Hb.
    rewrite List_nth_0_cons.
    apply Nat.leb_gt, Hab.
    rewrite app_nil_l.
    apply in_map_iff in Hb.
    destruct Hb as (c & H & Hc); subst b; cbn.
    apply in_isort_rank in Hc.
    now apply nth_In.
  }
Theorem isort_rank_app : ∀ la lb,
  (∀ a b, a ∈ la → b ∈ lb → b < a)
  → isort_rank Nat.leb (la ++ lb) =
    map (add (length la)) (isort_rank Nat.leb lb) ++ isort_rank Nat.leb la.
Proof.
intros * Hlab.
(**)
Compute (
let la := [13; 34; 15] in
let lb := [8; 5; 7; 9] in
  isort_rank Nat.leb (la ++ lb) =
    map (add (length la)) (isort_rank Nat.leb lb) ++ isort_rank Nat.leb la
).
...
(**)
revert lb Hlab.
induction la as [| a]; intros. {
  cbn; rewrite app_nil_r.
  now rewrite map_id.
}
cbn - [ nth ].
...
rewrite isort_insert_lb_app. 2: {
  rewrite List_nth_0_cons.
  remember (la ++ lb) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]; [ now left | right ].
  rewrite List_hd_nth_0.
  rewrite (List_map_nth' 0); [ | now rewrite isort_rank_length; cbn ].
  rewrite <- Hlc.
  apply Nat.leb_le.
  destruct lb as [| b]. {
    rewrite app_nil_r in Hlc |-*.
    rewrite List_nth_succ_cons.
    rewrite Hlc.
    cbn - [ nth ].
Search (nth _ (isort_insert _ _ _)).
...
    rewrite app_nth2; [ | now rewrite map_length; unfold ge ].
    rewrite Nat.sub_0_l, app_nil_r.
    cbn; rewrite app_nil_r in Hlc.
...
  rewrite IHla. 2: {
    intros b d Hb Hd.
    apply Hlab; [ now right | easy ].
  }
  destruct lb as [| b]. {
    rewrite app_nth2; [ | now rewrite map_length; unfold ge ].
    rewrite Nat.sub_0_l, app_nil_r.
    cbn; rewrite app_nil_r in Hlc.
...
  }
  rewrite (List_map_nth' 0).
...
  apply in_map_iff in Hb.
  destruct Hb as (c & H & Hc); subst b; cbn.
  apply in_isort_rank in Hc.
  apply Nat.leb_gt.
  rewrite app_length in Hc.
  destruct (lt_dec c (length la)) as [Hcla| Hcla]. {
    rewrite app_nth1; [ | easy ].
    apply Hlab; [ now left | ].
Check isort_insert_ub_app.
...
isort_insert_ub_app
     : ∀ (A : Type) (rel : A → A → bool) (a : A) (lsorted : list A),
         (∀ b : A, b ∈ lsorted → rel a b = false) → isort_insert rel a lsorted = lsorted ++ [a]
...
Print isort_insert.
...
... ...
rewrite isort_rank_app. 2: {
  intros b c Hb Hc.
  destruct Hc as [Hc| Hc]; [ subst c | easy ].
  apply in_map_iff in Hb.
  now destruct Hb as (d & H & Hd); subst b.
}
cbn.
rewrite map_length, isort_rank_length, Nat.add_0_r.
specialize (isort_rank_map_add_compat 1 0) as H1.
replace (add 1) with S in H1 by easy.
now rewrite H1, map_id.
... ...
rewrite collapse_app_cons. 2: {
  intros i Hi.
  apply (permutation_in_iff Nat.eqb_eq Hp i) in Hi.
  now apply in_seq in Hi; rewrite <- Hn in Hi.
}
rewrite Hlen, H1.
rewrite firstn_map, skipn_map.
rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r.
rewrite firstn_all.
rewrite skipn_app, Nat.sub_diag, skipn_O.
now rewrite skipn_all, app_nil_l.
...
Search (collapse (_ ++ _)).
Search (isort_rank _ (_ ++ _)).
...
cbn - [ seq ] in Haft.
replace (S (length la)) with (length bef + (S (length la) - length bef))
  in Haft. 2: {
  rewrite Nat.add_comm, Nat.sub_add; [ easy | ].
  apply (f_equal length) in Haft.
  rewrite app_length, seq_length in Haft.
  rewrite Haft.
  now apply Nat.le_add_r.
}
rewrite seq_app in Haft.
apply List_app_eq_app' in Haft; [ | now rewrite seq_length ].
destruct Haft as (Hbef1 & Haft).
rewrite <- Hbef1 in Hbef, Hp.
clear Hbef1.
...
intros * Hp.
revert sta Hp.
induction la as [| a]; intros; [ easy | ].
cbn - [ nth ].
apply permutation_cons_l_iff in Hp.
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Haft).
apply Nat.eqb_eq in H; subst x.
cbn - [ seq ] in Haft.
replace (S (length la)) with (length bef + (S (length la) - length bef))
  in Haft. 2: {
  rewrite Nat.add_comm, Nat.sub_add; [ easy | ].
  apply (f_equal length) in Haft.
  rewrite app_length, seq_length in Haft.
  rewrite Haft.
  now apply Nat.le_add_r.
}
rewrite seq_app in Haft.
apply List_app_eq_app' in Haft; [ | now rewrite seq_length ].
destruct Haft as (Hbef1 & Haft).
rewrite <- Hbef1 in Hbef, Hp.
clear Hbef1.
... ...
rewrite (permutation_seq_collapse 1); [ | now rewrite Hkm ].
apply (List_map_nth' 0).
subst j; rewrite Hkm; flia Hi.
...
subst j.
rewrite <- Hkm in Hi, Hkl.
clear - Hkl Hi.
revert i Hi.
induction kl as [| k]; intros. {
  now cbn; rewrite Tauto_match_nat_same.
}
...
Search (permutation _ _ (seq _ _)).
Search (nth _ (isort_rank _ _)).
Search (nth _ (collapse _)).
Search all_permut.
unfold collapse.
Search (nth _ (isort_rank _ _)).
...
apply in_all_permut_iff in Hkl.
rewrite Hkl.
in_all_permut_iff: ∀ la lb : list nat, la ∈ all_permut lb ↔ isort Nat.leb la = isort Nat.leb lb
...
unfold collapse.
Search (nth _ (collapse _)).
Search (nth _ (isort_rank _ _)).
...
rewrite sorted_permuted_comp_collapse.
...
  Hjl : jl ∈ sub_lists_of_seq_1_n n m
  Hsj : sorted Nat.ltb jl
  Hjm : length jl = m
  Hkl : kl ∈ all_permut (seq 1 m)
  Hi : 1 ≤ i ≤ m
  ============================
  (jl ° collapse kl).(i) = jl.(kl.(i))
...
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
  let A := mk_mat [[1;-2;3;7];[4;5;-6;-12];[8;-3;5;9]]%Z in
  let m := mat_nrows A in
  let n := mat_ncols A in
  let jl := [1; 3; 4] in
  let kl := [2; 1; 3] in
map (λ i,
 (jl ° collapse kl).(i) = jl.(kl.(i))) (seq 1 m)).
...
map (λ i,
mat_el A i (jl ° collapse kl).(i) = mat_el A i jl.(kl.(i))) (seq 1 m)).
...
  ∏ (i = 1, m), mat_el A i (jl ° collapse kl).(i) = ∏ (i = 1, m), mat_el A i jl.(kl.(i))
).
...
     = [3 = 4; 1 = 1; 4 = 7; 7 = 0]
apply rngl_product_list_eq_compat.
rewrite Nat_sub_succ_1.
intros i Hi.
unfold g1.
f_equal.
Compute (
  let jl := [1; 3; 4; 7] in
  let kl := [3; 1; 4; 7] in
  let m := length jl in
map (λ i,
  (jl ° collapse kl).(i) = jl.(kl.(i)))
(seq 1 m)
).
...
unfold sign_diff.
remember (nth j la 0 ?= nth i la 0) as jia eqn:Hjia; symmetry in Hjia.
remember (nth j lb 0 ?= nth i lb 0) as jib eqn:Hjib; symmetry in Hjib.
move jib before jia.
destruct jia, jib; try easy; exfalso. {
  apply Nat.compare_eq_iff in Hjia.
  apply Nat.compare_lt_iff in Hjib.
(**)
  rewrite Hlab in Hj.
  revert i j lb Hab Hi Hj Hij Hjia Hjib Hlab.
  induction la as [| a]; intros; rewrite <- Hlab in Hj; cbn in Hi, Hj. {
    now apply Nat.le_0_r in Hi, Hj; subst i j.
  }
  rewrite Nat.sub_0_r in Hi, Hj.
  destruct lb as [| b]. {
    now do 2 rewrite List_nth_nil in Hjib.
  }
  cbn in Hlab; apply Nat.succ_inj in Hlab.
  rewrite Hlab in Hj.
  cbn - [ nth ] in Hab.
  rewrite isort_insert_nth_indep with (d' := 0) in Hab; [ | now cbn | ]. 2: {
    intros k Hk.
    apply in_map_iff in Hk.
    destruct Hk as (u & H & Hk); subst k; cbn.
    apply -> Nat.succ_lt_mono.
    now apply in_isort_rank in Hk.
  }
  symmetry in Hab.
  rewrite isort_insert_nth_indep with (d' := 0) in Hab; [ | now cbn | ]. 2: {
    intros k Hk.
    apply in_map_iff in Hk.
    destruct Hk as (u & H & Hk); subst k; cbn.
    apply -> Nat.succ_lt_mono.
    now apply in_isort_rank in Hk.
  }
  symmetry in Hab.
  set (rela := λ ia ib, nth ia (a :: la) 0 <=? nth ib (a :: la) 0).
  set (relb := λ ia ib, nth ia (b :: lb) 0 <=? nth ib (b :: lb) 0).
  fold rela in Hab.
  fold relb in Hab.
(*
Compute (
let a := 14 in
let b := 3 in
let la := [17;2;7] in
let lb := [5;9;8] in
  let rela := λ ia ib, nth ia (a :: la) 0 <=? nth ib (a :: la) 0 in
  let relb := λ ia ib, nth ia (b :: lb) 0 <=? nth ib (b :: lb) 0 in
  isort_insert rela 0 (map S (isort_rank Nat.leb la)) =
  isort_insert relb 0 (map S (isort_rank Nat.leb lb))
).
(* trop compliqué *)
*)
Theorem glop :
  sorted rela la
  → sorted relb lb
  → isort_insert rela i la = isort_insert relb i lb
  →
...
  revert i j lb Hab Hi Hj Hij Hjia Hjib.
  induction la as [| a]; intros; cbn in Hi, Hj. {
    now apply Nat.le_0_r in Hi, Hj; subst i j.
  }
  rewrite Nat.sub_0_r in Hi, Hj.
  cbn - [ nth ] in Hab.
  set (rela := λ ia ib, nth ia (a :: la) a <=? nth ib (a :: la) a).
  fold rela in Hab.
  destruct lb as [| b]. {
    now do 2 rewrite List_nth_nil in Hjib.
  }
  cbn - [ nth ] in Hab.
  set (relb := λ ia ib, nth ia (b :: lb) b <=? nth ib (b :: lb) b).
  fold relb in Hab.
Theorem glop :
  isort_insert rela i la = isort_insert relb i lb
  →
...
apply collapse_ε.
Search (collapse (_ ° _)).
Compute (
  let jl := [1; 3; 4;7] in
let m := length jl in
map (λ kl,
   collapse (jl ° collapse kl) = collapse kl) (all_permut (seq 1 m))).
...
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
  let jl := [1; 3; 4;7] in
let m := length jl in
map (λ kl,
  ε (jl ° collapse kl) = ε kl) (all_permut (seq 1 m))).
...
Search (permutation _ _ (seq _ _)).
Print permutation_assoc.
Print permutation_assoc_loop.
Search permutation_assoc.
Theorem permutation_seq_shift : ∀ la sta len,
  permutation eqb la (seq sta len)
  → permutation eqb (map (λ i, i - sta) la) (seq 0 len).
Proof.
intros * Hp.
revert la sta Hp.
induction len; intros. {
  now apply permutation_nil_r in Hp; subst la.
}
rewrite seq_S in Hp |-*; cbn.
eapply (permutation_trans Nat.eqb_eq). 2: {
  apply (permutation_cons_append Nat.eqb_eq).
}
apply (permutation_sym Nat.eqb_eq).
apply permutation_cons_l_iff.
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl len) as H1.
  rewrite Nat.eqb_refl in H1.
  assert (H : len ∈ map (λ i, i - sta) la). {
    apply in_map_iff.
    exists (sta + len).
    split; [ now rewrite Nat.add_comm, Nat.add_sub | ].
    eapply (permutation_in_iff Nat.eqb_eq); [ apply Hp | ].
    now apply in_or_app; right; left.
  }
  now specialize (H1 H).
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Haft).
apply Nat.eqb_eq in H; subst x.
... ...
apply permutation_seq_shift in Hkl.
...
  replace (collapse kl) with (map pred kl). 2: {
    apply in_all_permut_permutation in Hkl.
    assert (H : equality eqb) by now unfold equality; apply Nat.eqb_eq.
    eapply permutation_map with (f := pred) in Hkl; [ | easy | easy ].
    replace (map pred (seq 1 m)) with (seq 0 m) in Hkl. 2: {
      clear; remember 0 as sta; clear Heqsta.
      revert sta.
      induction m; intros; [ easy | cbn ].
      f_equal; apply IHm.
    }
Search (collapse (map _ _)).
Fixpoint isort_rank_insert {A} (rel : A → A → bool) la d ia lrank :=
  match lrank with
  | [] => [ia]
  | ib :: l =>
      if rel (nth ia la d) (nth ib la d) then ia :: lrank
      else ib :: isort_rank_insert rel la d ia l
  end.

Fixpoint isort_rank' {A} (rel : A → A → bool) (l : list A) :=
  match l with
  | [] => []
  | d :: l' => isort_rank_insert rel l d 0 (map S (isort_rank' rel l'))
  end.

Theorem isort_insert_isort_rank_insert : ∀ A d (rel : A → _) la ia lrank,
  isort_insert (λ ia ib, rel (nth ia la d) (nth ib la d)) ia lrank =
  isort_rank_insert rel la d ia lrank.
Proof.
intros.
revert la ia.
induction lrank as [| ib]; intros; [ easy | cbn ].
remember (rel (nth ia la d) (nth ib la d)) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ easy | ].
f_equal.
apply IHlrank.
Qed.

Theorem isort_rank_isort_rank' : ∀ A (rel : A → _) la,
  isort_rank rel la = isort_rank' rel la.
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn - [ nth ].
rewrite <- IHla.
apply isort_insert_isort_rank_insert.
Qed.

Theorem collapse_map : ∀ f la,
  (∀ a b, a ∈ la → b ∈ la → (a <=? b) = (f a <=? f b))
  → collapse (map f la) = collapse la.
Proof.
intros * Hf.
unfold collapse.
do 2 rewrite isort_rank_isort_rank'.
destruct la as [| a]; [ easy | ].
cbn - [ nth ].
rewrite isort_insert_isort_rank_insert.
do 2 rewrite isort_rank_isort_rank'.
f_equal.
rewrite <- map_cons.
Print isort_rank_insert.
Print isort_insert.
Search (isort_insert _ _ (map _ _)).
Theorem isort_rank_insert_map : ∀ d la ia lrank f,
  (∀ ia ib d, ia < length la → ib < length la →
    (nth ia (map f la) d <=? nth ib (map f la) d) =
    (nth ia la d <=? nth ib la d))
  → isort_rank_insert Nat.leb (map f la) (f d) ia lrank =
    isort_rank_insert Nat.leb la (f d) ia lrank.
Proof.
intros * Hab.
revert la ia Hab.
induction lrank as [| ib]; intros; [ easy | cbn ].
rewrite IHlrank. 2: {
  intros ic id e.
  now apply Hab.
}
destruct (lt_dec ia (length la)) as [Hia| Hia]. 2: {
  apply Nat.nlt_ge in Hia.
  rewrite nth_overflow; [ | now rewrite map_length ].
  symmetry.
  rewrite nth_overflow; [ | easy ].
  symmetry.
  destruct (lt_dec ib (length la)) as [Hib| Hib]. 2: {
    apply Nat.nlt_ge in Hib.
    rewrite nth_overflow; [ | now rewrite map_length ].
    now rewrite nth_overflow.
  }
...
rewrite Hab, if_leb_le_dec; [ easy | | ].
Qed.
rewrite isort_rank_insert_map. 2: {
  intros ia ib d.
  destruct (lt_dec ia (S (length la))) as [Hial| Hial]. 2: {
    apply Nat.nlt_ge in Hial.
    rewrite nth_overflow; [ | now rewrite map_length ].
    destruct (lt_dec ib (S (length la))) as [Hibl| Hibl]. 2: {
      apply Nat.nlt_ge in Hibl.
      rewrite nth_overflow; [ | now rewrite map_length ].
      rewrite Nat.leb_refl; symmetry.
      rewrite nth_overflow; [ | easy ].
      rewrite nth_overflow; [ | easy ].
      apply Nat.leb_refl.
    }
    symmetry.
    rewrite nth_overflow; [ | easy ].
...
      rewrite Hf; cycle 1. {
        destruct ia; [ easy | cbn ].
        apply Nat.succ_le_mono in Hial.
        rewrite nth_overflow; [ | easy ].
...
      apply Nat.leb_le.


  rewrite (List_map_nth' d).

...
  rewrite <- Hf.
  rewrite Hf; cycle 1. {
...
    rewrite (List_map_nth' d).
...
  remember (_ <=? _) as x eqn:Hx; symmetry in Hx |-*.
  destruct x. {
    apply Nat.leb_le in Hx; apply Nat.leb_le.
...
  isort_rank_insert Nat.leb (map f (a :: la)) (f a) 0 (map S (isort_rank' Nat.leb (map f la))) =
  isort_rank_insert Nat.leb (a :: la) a 0 (map S (isort_rank' Nat.leb la))
...
intros * Hf.
unfold collapse.
induction la as [| a]; [ easy | ].
cbn - [ nth ].
Print isort_rank.
...
rewrite <- (collapse_map pred).
Search (permutation _ (seq _ _)).
Search (permutation _ _ (seq _ _)).
Search (collapse _ = _).
Search (map _ (seq _ _)).
Search (map pred).
About permutation_map.
Require Import Permutation.
Check Permutation_map.
Search (Permutation (map _ _)).
...
    apply in_all_permut_iff in Hkl.
Search (permutation _ _ (seq _ _)).
...
  unfold "°".
  rewrite map_map.
Search (ε (map _ _)).
...
  rewrite <- (@ε_collapse_ε _ _ kl).
Search (ε (_ ° _)).
  rewrite sorted_permuted_comp_collapse; [ | | ]. {
...
  replace (collapse kl) with (map pred kl).
...
  rewrite sorted_permuted_comp_collapse; [ | | ]. {
...
unfold "°".
rewrite map_map.
...
(*
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
  let jl := [1; 3; 4;7] in
let m := length jl in
map (λ kl,
  ε (jl ° collapse kl) = ε kl) (all_permut (seq 1 m))).
Compute (
  let jl := [1; 3; 4;7] in
let m := length jl in
map (λ kl,
  (jl ° collapse kl) = kl) (all_permut (seq 1 m))).
*)
Search (ε _ = ε _).
About sorted_permuted_comp_collapse.
...
  rewrite sorted_permuted_comp_collapse; [ | | ]. {
...
Theorem collapse_collapse_ε : ∀ i j la lb,
  collapse (map (add i) la) = collapse (map (add j) lb) → ε la = ε lb.
...
apply (collapse_collapse_ε 1 0).
replace (add 1) with S by easy.
rewrite map_id.
cbn.
rewrite collapse_comp.
  rewrite sorted_permuted_comp_collapse; [ | | ]. {
...
  rewrite sorted_permuted_comp_collapse; [ easy | | ]. {
    now apply sorted_nat_ltb_leb_incl.
  }
...
  apply in_all_permut_permutation in Hkl.
...
rewrite <- isort_comp_permut_r with (p := isort_rank Nat.leb la).
rewrite isort_isort_rank with (d := 0).
Search (nth _ (_ ° _)).
isort_comp_permut_r: ∀ l p : list nat, permut_seq_with_len (length l) p → isort Nat.leb (l ° p) = isort Nat.leb l
......
apply isort_comp_collapse.
Compute (
let la := [8;7;2;3] in
  isort Nat.leb la ° collapse la = la
).
...
rewrite isort_isort_rank with (d := 0).
unfold "°"; cbn.
unfold collapse.
erewrite map_ext_in. 2: {
  intros i Hi.
  generalize Hi; intros Hli.
  apply in_isort_rank in Hli.
  rewrite (List_map_nth' 0); [ | easy ].
  rewrite isort_rank_length in Hli.
  easy.
}
Search (nth (nth _ (isort_rank _ _) _)).
rewrite nth_nth_isort_rank; [ | easy ].
easy.
}
...
  rewrite permut_permut_isort; [ | | easy ]. 2: {
}
...
intros * Hs Hp.
unfold collapse.
revert lb Hp.
induction la as [| a]; intros; cbn. {
  now apply permutation_nil_l in Hp; subst lb.
}
apply permutation_cons_l_iff in Hp.
remember (extract (Nat.eqb a) lb) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Nat.eqb_eq in H; subst x lb.
replace (isort_rank Nat.leb (bef ++ a :: aft)) with (0 :: map S (isort_rank Nat.leb (bef ++ aft))). 2: {
  clear Hp.
  induction bef as [| b]. {
    cbn - [ nth ].
...
permut_isort_rank_involutive: ∀ la : list nat, permut_seq la → isort_rank Nat.leb (isort_rank Nat.leb la) = la
f (f (f l)) = f l
...
(*
Compute (
  let la := [2;3;7;8] in
map (λ lb, la ° collapse lb = lb) (all_permut la)).
*)
...
apply glop.
unfold collapse.
...
Fixpoint isort_rank_insert {A B} (rel : A → A → bool) (f : B → A) ia lrank :=
  match lrank with
  | [] => [ia]
  | ib :: l =>
      if rel (f ia) (f ib) then ia :: lrank
      else ib :: isort_rank_insert rel f ia l
  end.

Fixpoint isort_rank' {A} (rel : A → A → bool) (l : list A) :=
  match l with
  | [] => []
  | d :: l' =>
      isort_rank_insert rel (λ i, nth i l d) 0 (map S (isort_rank' rel l'))
  end.

Print isort_rank.

assert (H : jl ° isort_rank' Nat.leb (isort_rank' Nat.leb kl) = kl). {
destruct kl as [| k]; [ easy | ].
cbn - [ nth ].
(* ouais, bon, j'y crois pas beaucoup *)
...
  unfold comp_list.
  unfold collapse.
...
(*
Theorem isort_isort_rank_compat : ∀ A (rel : A → _) la lb,
  isort rel la = isort rel lb → isort_rank rel la = isort_rank rel lb.
Proof.
intros * Hab.
(* bin non, c'est faux, ça *)
Compute (
  let rel := Nat.ltb in
  let la := [3;5;4;8] in
  let lb := [5;3;4;8] in
  isort rel la = isort rel lb → isort_rank rel la = isort_rank rel lb
).
*)
...
erewrite isort_insert_rel_eq_compat. 2: {
  intros x y Hx Hy.
...
Search (isort_insert _ _ (map _ _)).
Search isort_insert.
...
Search (_ ° collapse _).
  unfold collapse.
Search (_ ° isort_rank _ _).
Check comp_isort_rank_r.
...
  rewrite isort_isort_rank with (d := 0) in Hkl.
  rewrite isort_isort_rank with (d := 0) in Hkl.
Search isort.
...
assert (∀ kl, kl ∈ all_permut jl → g1 (h1 kl) = kl). {
  intros kl Hkl.
  unfold g1, h1.
  replace (collapse kl) with (map pred kl). 2: {
    apply in_all_permut_permutation in Hkl.
...
    rewrite <- Hkl.
unfold h1.
    rewrite map_map.
    erewrite map_ext_in. 2: {
      intros a Ha.
      rewrite Nat.pred_succ.
      easy.
    }
    apply map_id.
  }
...
  apply in_map_iff in Hkl.
destruct Hkl as (la & Hkl & Hla).
apply in_all_permut_permutation in Hla.
rewrite <- Hkl at 1.
  replace (collapse la) with (map pred kl). 2: {
...
rewrite rngl_summation_list_change_var with (g := g1) (h := h1). 2: {
  intros kl Hkl.
...
apply in_map_iff in Hkl.
destruct Hkl as (la & Hkl & Hla).
apply in_all_permut_permutation in Hla.
rewrite <- Hkl at 1.
  replace (collapse la) with (map pred kl). 2: {
...
  unfold g1, h1.

  rewrite map_map.
  erewrite map_ext_in by now intros; rewrite Nat.pred_succ.
  rewrite map_id.
...
remember (∑ (kl ∈ _), _) as x; subst x.
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
  unfold g1.
apply in_map_iff in Hkl.
destruct Hkl as (la & Hkl & Hla).
apply in_all_permut_permutation in Hla.
rewrite <- Hkl at 1.
  replace (collapse la) with (map pred kl). 2: {
    rewrite <- Hkl.
unfold h1.
    rewrite map_map.
    erewrite map_ext_in. 2: {
      intros a Ha.
      rewrite Nat.pred_succ.
      easy.
    }
    apply map_id.
  }
  rewrite Hkl.
Compute (
let jl := [3;5;8] in
map (λ kl,
jl ° collapse kl = kl
) (all_permut jl)).
(* oui bon c'est bon, alors *)
...
  rewrite map_map.
  erewrite map_ext_in by now intros; rewrite Nat.pred_succ.

  rewrite map_id.
  unfold h1 in Hkl.
  replace (collapse la) with (map pred kl). 2: {
    rewrite <- Hkl.
    rewrite map_map.
    erewrite map_ext_in. 2: {
      intros a Ha.
      rewrite Nat.pred_succ.
      easy.
    }
    apply map_id.
  }
Compute (
let jl := [3;5;8] in
map (λ kl,
((jl ° map pred kl), kl)
) (all_permut jl)).
...
rewrite rngl_summation_list_change_var with (g := g1) (h := h1). 2: {
  unfold g1, h1.
  intros kl Hkl.
  rewrite map_map.
  erewrite map_ext_in by now intros; rewrite Nat.pred_succ.
  rewrite map_id.
...
set (g1 := λ l, isort_rank Nat.leb (map pred l)).
set (h1 := λ l, map S (collapse l)).
rewrite rngl_summation_list_change_var with (g := g1) (h := h1). 2: {
  intros kl Hkl.
  unfold g1, h1.
  rewrite map_map.
  erewrite map_ext_in by now intros; rewrite Nat.pred_succ.
  rewrite map_id.
  unfold collapse.
...
Compute (
  let kl := [3;7;5] in
  isort_rank Nat.leb (isort_rank Nat.leb (isort_rank Nat.leb kl)) = kl
).
...
Check permut_isort_rank_involutive.
rewrite permut_isort_rank_involutive with (la := kl).
apply in_all_permut_permutation in Hkl.
...
  rewrite permut_isort_rank_involutive.
  apply in_all_permut_permutation in Hkl.
Search (pred (S _)).
...
unfold h1.
specialize (map_collapse_all_permut_seq 1 _ _ _ Hjl) as H1.
replace (add 1) with S in H1 by easy.
rewrite H1, Hjm.
remember (∑ (kl ∈ _), _) as x; subst x.
...
(*
...
Search (isort_rank _ _ = _).
Theorem isort_rank_when_permut : ∀ la,
  permut_seq la
  → isort_rank Nat.leb la = la.
...
rewrite isort_rank_when_permut.
...
*)
rewrite permut_isort_rank_involutive. 2: {
  apply (map_nth_permut_seq (length la)). 2: {
    now apply canon_sym_gr_list_permut_seq_with_len.
  }
...
rewrite map_collapse_all_permut_seq.
...
Theorem isort_isort_rank_iff : ∀ A (eqb rel : A → _),
  equality eqb →
  ∀ la lb,
  isort rel la = isort rel lb ↔ isort_rank rel la = isort_rank rel lb.
Proof.
intros * Heqb *.
Compute (
  let rel := Nat.ltb in
  let la := [1;2;3] in
  let lb := [2;1;3] in
  isort rel la = isort rel lb ↔ isort_rank rel la = isort_rank rel lb).
...
split; intros Hab. {
  destruct la as [| d]. {
    symmetry in Hab; cbn in Hab.
    now apply eq_isort_nil in Hab; subst lb.
  }
  remember (d :: la) as l eqn:Hl.
  clear la Hl; rename l into la; move la after lb.
  apply (permut_if_isort _ Heqb) in Hab.
Check isort_when_permuted.
Search permutation.
About isort_when_permuted.
...
apply (isort_rank_when_permuted Heqb).
...
(*
...
intros.
split; intros Hab. {
  destruct la as [| d]. {
    symmetry in Hab; cbn in Hab.
    now apply eq_isort_nil in Hab; subst lb.
  }
  remember (d :: la) as l eqn:Hl.
  clear la Hl; rename l into la; move la after lb.
(**)
revert lb Hab.
induction la as [| a]; intros. {
  symmetry in Hab.
  now apply eq_isort_nil in Hab; subst lb.
}
cbn - [ nth ].
destruct lb as [| b]; [ now apply eq_isort_nil in Hab | ].
cbn in Hab; cbn - [ nth ].
...
destruct la as [| a']. {
  cbn in Hab.
  symmetry in Hab.
  destruct lb as [| b']. {
    cbn in Hab.
    now injection Hab; clear Hab; intros; subst b.
  }
  cbn in Hab.
  cbn - [ nth ].
...
*)
  do 2 rewrite isort_isort_rank with (d := d) in Hab.
  assert (Hlen : length la = length lb). {
    apply List_eq_iff in Hab.
    now do 2 rewrite map_length, isort_rank_length in Hab.
  }
(*
  apply List_eq_iff in Hab.
  do 2 rewrite map_length, isort_rank_length in Hab.
  destruct Hab as (Hlen, Hab).
*)
  apply List_eq_iff.
  do 2 rewrite isort_rank_length.
  split; [ easy | ].
  intros d' i.
  destruct (lt_dec i (length la)) as [Hil| Hil]. 2: {
    apply Nat.nlt_ge in Hil.
    rewrite nth_overflow with (n := i); [ | now rewrite isort_rank_length ].
    rewrite Hlen in Hil.
    rewrite nth_overflow with (n := i); [ | now rewrite isort_rank_length ].
    easy.
  }
  rewrite nth_indep with (d' := 0); [ | now rewrite isort_rank_length ].
  rewrite Hlen in Hil; symmetry.
  rewrite nth_indep with (d' := 0); [ | now rewrite isort_rank_length ].
  rewrite <- Hlen in Hil; symmetry.
  clear d'.
...
  specialize (Hab d i) as H1.
  rewrite (List_map_nth' 0) in H1; [ | now rewrite isort_rank_length ].
  rewrite Hlen in Hil.
  rewrite (List_map_nth' 0) in H1; [ | now rewrite isort_rank_length ].
  rewrite <- Hlen in Hil.
  remember (nth i (isort_rank rel la) 0) as u eqn:Hu.
  remember (nth i (isort_rank rel lb) 0) as v eqn:Hv.
  move v before u.
  assert (H : isort_rank rel la = isort_rank rel lb). {
    apply List_eq_iff.
    do 2 rewrite isort_rank_length.
    split; [ easy | ].
    intros d' j.
    apply List_eq_iff.
    apply List_eq_iff.
    do 2 rewrite isort_rank_length.
    split; [ easy | ].
    intros d'' k.
...
Search (∀ _, nth _ _ _ = nth _ _ _).
...
  assert (H : isort_rank rel la = isort_rank rel lb). {
    apply List_eq_iff.
    do 2 rewrite isort_rank_length.
    split; [ easy | ].
    intros d' j.
...
  ============================
  nth j (isort_rank rel la) d' = nth j (isort_rank rel lb) d'
...
  apply isort_rank_inj in Hab.
Search (nth _ (isort_rank _ _)).
...
  assert
    (H : ∀ i,
     nth (nth i (isort_rank rel la) 0) la d =
     nth (nth i (isort_rank rel lb) 0) lb d). {
    intros i.
    destruct (lt_dec i (length la)) as [Hil| Hil]. 2: {
      apply Nat.nlt_ge in Hil.
      rewrite nth_overflow with (n := i); [ | now rewrite isort_rank_length ].
      rewrite Hlen in Hil.
      rewrite nth_overflow with (n := i); [ | now rewrite isort_rank_length ].
      rewrite <- Hlen in Hil.
      specialize (Hab i).
      rewrite nth_overflow in Hab.
2: now rewrite map_length, isort_rank_length.

...
    specialize (Hab i).
    rewrite (List_map_nth' 0) in Hab; [ | rewrite isort_rank_length ].

...
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    replace (mat_el A i kl.(i)) with
      (mat_el (mat_select_cols jl A) i (S (collapse kl).(i))). 2: {
      unfold collapse.
...
cbn.
apply in_sls1n_iff in Hjl.
destruct Hjl as [Hjl| Hjl]; [ easy | ].
destruct Hjl as (Hs & H1 & Hjl).
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  rewrite mat_select_rows_ncols. 2: {
    destruct jl; [ now symmetry in H1 | easy ].
  }
  rewrite mat_transp_ncols.
  rewrite Hac, Har.
  apply Nat.eqb_neq in Hnz.
  rewrite Hnz; flia Hi.
}
rewrite map_length, Nat.sub_0_r.
rewrite mat_transp_ncols, Har, Hac.
apply Nat.eqb_neq in Hnz; rewrite Hnz.
rewrite H1.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  unfold collapse.
  specialize (isort_rank_ub) as H2.
  specialize (H2 _ Nat.leb (isort_rank Nat.leb kl)).
  specialize (H2 (i - 1)).
  rewrite isort_rank_length in H2.
_admit.
}
rewrite (List_map_nth' 0). 2: {
  _admit.
}
rewrite mat_select_rows_ncols.
rewrite mat_transp_ncols, Har, Hac.
rewrite Hnz.
rewrite seq_nth; [ | flia Hi ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length; flia Hi.
}
rewrite seq_nth; [ | flia Hi ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  _admit.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length; flia Hi.
}
rewrite seq_nth; [ | flia Hi ].
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
f_equal.
rewrite seq_nth.
rewrite seq_nth.
rewrite Nat.add_comm, Nat.sub_add.
Search (_ ∈ all_permut _).
...
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
  let A := mk_mat [[1;-2;3;7];[4;5;-6;-12];[8;-3;5;9]]%Z in
  let m := mat_nrows A in
  let n := mat_ncols A in
  let jl := [1; 3; 4] in
  let kl := [3; 1; 4] in
  map (λ i,
mat_el A i kl.(i) =
mat_el (mat_select_cols jl A) i (S (collapse kl).(i))
) (seq 1 m)).
...
set (g1 := isort_rank Nat.leb). (* à corriger *)
set (h1 := λ l, map S (collapse l)).
erewrite rngl_summation_list_change_var with (g := g1) (h := h1).
replace (map h1 (all_permut jl)) with (all_permut (seq 1 m)). 2: {
  unfold h1.
(*
Compute (
  let jl := [2;3;5] in
  let m := length jl in
  all_permut (seq 1 m) = map (map S) (map collapse (all_permut jl))
).
*)
  unfold sub_lists_of_seq_1_n in Hjl.
  apply in_sls1n_iff in Hjl.
  destruct Hjl as [Hjl| Hjl]; [ easy | ].
  destruct Hjl as (Hs & Hjlm & Hjl).
  rewrite <- Hjlm.
  clear Hjlm.
  induction jl as [| j]; [ easy | ].
  cbn - [ nth seq ].
  rewrite map_map.
  unfold canon_sym_gr_list_list.
  rewrite map_map.
  unfold all_permut.
  rewrite seq_length.
  rewrite <- cons_seq.
  unfold canon_sym_gr_list_list.
  rewrite map_map.
  apply map_ext_in.
  intros i Hi.
  apply in_seq in Hi.
  symmetry.
  remember (map S) as x.
  erewrite map_ext_in. 2: {
    intros k Hk.
    erewrite nth_indep with (d' := 0). 2: {
      now apply in_canon_sym_gr_list in Hk.
    }
    easy.
  }
  subst x.
  symmetry.
  erewrite map_ext_in. 2: {
    intros k Hk.
    apply in_canon_sym_gr_list in Hk; [ | easy ].
    rewrite cons_seq, seq_nth; [ | easy ].
    now rewrite Nat.add_1_l.
  }
  f_equal.
  symmetry.
Search collapse.
Search (map (λ _, nth _ _ _)).
...
  rewrite permut_collapse. 2: {
    apply (map_nth_permut_seq 42).
    erewrite
Search (permut_seq (map _ _)).
Search collapse.
  unfold collapse.
Search isort_rank.
Search (seq (S _)).
Search (_ ∈ sls1n _ _ _).
Search (_ ∈ sub_lists_of_seq_1_n _ _).
...
unfold mat_select_cols, mat_select_rows.
rewrite mat_transp_ncols, Hac, Har.
generalize Hnz; intros H.
apply Nat.eqb_neq in H; rewrite H; clear H.
...
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
...
    rewrite mat_transp_el; [ | | flia Hi | ]; cycle 1. {
      erewrite map_ext_in. 2: {
        intros j Hj.
        erewrite map_ext_in. 2: {
          intros k Hk.
          apply in_seq in Hk.
          rewrite mat_transp_el; [ | easy | | flia Hk ]. 2: {
            apply (sub_lists_of_seq_1_n_bounds n m) in Hj; [ | easy ].
            flia Hj.
          }
          easy.
        }
        easy.
      }
      unfold is_correct_matrix.
      unfold mat_ncols; cbn.
      rewrite map_length.
      apply Bool.andb_true_iff.
      rewrite List_hd_nth_0.
      rewrite (List_map_nth' 0). 2: {
        apply in_sub_lists_of_seq_1_n_length in Hjl.
        apply Nat.neq_0_lt_0.
        congruence.
      }
      rewrite List_map_seq_length.
      split. {
        apply Bool.orb_true_iff.
        left.
        apply Bool.negb_true_iff.
        now apply Nat.eqb_neq.
      } {
        apply all_true_and_list_true_iff.
        intros la Hla.
        apply in_map_iff in Hla.
        destruct Hla as (a & H & Hla); subst la.
        rewrite List_map_seq_length.
        apply Nat.eqb_refl.
      }
    } {
      unfold all_permut in Hkl.
      destruct m; [ easy | ].
      cbn - [ nth ] in Hkl.
      apply in_map_iff in Hkl.
      destruct Hkl as (la & H & Hla); subst kl.
      apply in_map_iff in Hla.
      destruct Hla as (a & H & Hla).
      rewrite (List_map_nth' 0). 2: {
        subst la; cbn.
        rewrite map_length, seq_length.
        rewrite canon_sym_gr_list_length.
        flia Hi.
      }
      replace (1 :: seq 2 m) with (seq 1 (S m)) by easy.
      rewrite seq_nth; cbn. 2: {
        subst la.
        rewrite seq_length.
        destruct i; [ flia Hi | ].
        cbn; rewrite Nat.sub_0_r.
        destruct i. {
          apply in_seq in Hla.
          rewrite seq_length in Hla.
...
        rewrite List_nth_succ_cons.
        rewrite Nat.sub_0_r.
        rewrite
      easy.
...
      apply in_all_permut_permutation in Hkl.
...
Search permutation.
      replace m with (length kl) in Hkl.
...
      apply permut_list_permutation_iff in Hkl.
      apply permutation_length in Hkl.
      apply all_permut_bounds in Hkl.
...
Search (map _ (seq _ _)).
fold_mat_transp:
  ∀ (T : Type) (ro : ring_like_op T) (M : matrix T),
    {|
      mat_list_list :=
        map (λ j : nat, map (λ i : nat, mat_el M i j) (seq 1 (mat_nrows M)))
          (seq 1 (mat_ncols M))
    |} = M⁺%M

      Search is_correct_matrix.
cbn.
...
symmetry.
erewrite rngl_summation_list_change_var.
...
(g i).(i0) = nth i jl 0
Compute (all_permut (seq 1 3)).
Compute (all_permut [1;3;4]).
Print all_permut.
destruct m; [ easy | ].
unfold all_permut at 1.
set (s := seq 1 (S m)) at 1.
cbn in s; subst s.
cbn - [ mat_el seq ].
rewrite seq_length.
unfold all_permut.
destruct n; [ easy | ].
cbn in Hjl.
apply in_app_or in Hjl.
destruct Hjl as [Hjl| Hjl]. {
  apply in_map_iff in Hjl.
  destruct Hjl as (la & Hla & Hjl); subst jl.
  rewrite List_cons_length.
  apply in_sls1n_iff in Hjl.
  destruct Hjl as [Hjl| Hjl]. {
    destruct Hjl; subst m la.
...
    cbn.
    rewrite rngl_summation_list_only_one.
    rewrite rngl_product_only_one.
    cbn.
    rewrite map_length, seq_length.
...
  generalize Hjl; intros H.
Search (_ ∈ sls1n _ _ _).
  apply sls1n_length in Hjl.

remember (seq 1 (S m)) as s eqn:Hs.

cbn - [ all_permut mat_el ].
unfold all_permut at 1.

Search (∑ (_ ∈ _), _ = ∑ (_ ∈ _), _).
erewrite rngl_summation_list_change_var.
...
map h (all_permut (seq 1 m)) = all_permut jl.
g i = nth i jl ...
...
(*
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (sub_lists_of_seq_1_n 3 2).
Compute (
  let A := mk_mat [[1;-2;3;7];[4;5;-6;-12];[8;-3;5;9]]%Z in
  let m := mat_nrows A in
  let n := mat_ncols A in
  let jl := nth 2 (sub_lists_of_seq_1_n n m) [] in
jl).
  ∑ (jl' ∈ sub_lists_of_seq_1_n m m),
  (∑ (kl ∈ all_permut jl'),
   ε kl * ∏ (i = 1, m), mat_el (mat_select_cols jl A) i kl.(i)) =
  ∑ (kl ∈ all_permut jl), ε kl * ∏ (i = 1, m), mat_el A i kl.(i)
).
...
*)
(*
  ============================
  ∑ (l ∈ list_prodn (repeat (seq 1 m) m)), ε l * ∏ (i = 1, m), mat_el (mat_select_cols jl A) i l.(i) =
  ∑ (kl ∈ all_permut jl), ε kl * ∏ (i = 1, m), mat_el A i kl.(i)
*)
remember (∑ (kl ∈ _), _) as x; subst x.
rewrite list_prodn_prodn_repeat.
rewrite rngl_summation_list_prodn_repeat_filter_no_dup; try now destruct Hif.
(*
  ============================
  ∑ (kl ∈ filter (no_dup Nat.eqb) (prodn_repeat_seq 1 m m)),
  ε kl * ∏ (i = 1, m), mat_el (mat_select_cols jl A) i kl.(i) =
  ∑ (kl ∈ all_permut jl), ε kl * ∏ (i = 1, m), mat_el A i kl.(i)
*)
assert (Hel : equality (list_eqv eqb)). {
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
}
erewrite rngl_summation_list_permut; [ | apply Hel | ]. 2: {
  apply permutation_no_dup_prodn_repeat_flat_all_permut_sub_lists.
}
(*
  ============================
  ∑ (i ∈ flat_map all_permut (sub_lists_of_seq_1_n m m)),
  ε i * ∏ (i0 = 1, m), mat_el (mat_select_cols jl A) i0 i.(i0) =
  ∑ (kl ∈ all_permut jl), ε kl * ∏ (i = 1, m), mat_el A i kl.(i)
*)
rewrite flat_map_concat_map.
rewrite rngl_summation_list_concat.
rewrite rngl_summation_list_map.
(*
  ============================
  ∑ (i ∈ sub_lists_of_seq_1_n m m),
  (∑ (a ∈ all_permut i), ε a * ∏ (i0 = 1, m), mat_el (mat_select_cols jl A) i0 a.(i0)) =
  ∑ (kl ∈ all_permut jl), ε kl * ∏ (i = 1, m), mat_el A i kl.(i)
*)
Search (∑ (_ ∈ sub_lists_of_seq_1_n _ _), _).
...
rngl_summation_list_prodn_sub_lists_all_permut:
...
unfold sub_lists_of_seq_1_n in Hjl |-*.
...
*)

(* other attempts to prove det(AB)=det(A)det(B) *)

(*
Theorem determinant_mul : ∀ A B, det (A * B) = (det A * det B)%F.
Proof.
intros.
(* essai avec les formes multilinéaires alternées...

trouvé sur le web
(https://les-mathematiques.net/vanilla/index.php?p=discussion/1339028#Comment_1339028)

 Il vaut mieux éviter à tout prix la formule explicite. On peut
 utiliser la méthode de Gauss, ou bien utiliser le fait que
 l'application B↦det(AB) est multilinéaire alternée, et donc est un
 multiple de B↦detB

 Il faut d'abord avoir établi que l'espace des formes multilinéaires
 alternées est de dimension 1 et que le déterminant est l'unique telle
 forme qui vaut 1 en l'identité. Une fois ceci acquis, on en déduit
 que det(AB)=αdetB où α est un scalaire qui ne dépend que de A. On le
 trouve en prenant B=I, ce qui donne detA=αdetI=α.
*)
Check determinant_multilinear.
Check determinant_alternating.
...

(* very interesting, too, contains several proofs of det(AB)=det(A)det(B)
https://proofwiki.org/wiki/Determinant_of_Matrix_Product
*)

(* stuff to play with "ring_simplify" below *)
Context {Hic : @rngl_is_comm T ro rp = true}.
Context {Hop : @rngl_has_opp T ro = true}.
Require Import Ring.
Add Ring rngl_ring : (@rngl_ring_theory T ro rp Hic Hop).
(* end stuff *)

Theorem determinant_mul : in_charac_0_field →
  ∀ A B,
  is_square_matrix A = true
  → is_square_matrix B = true
  → mat_nrows A = mat_nrows B
  → det (A * B) = (det A * det B)%F.
Proof.
intros Hif * Hasm Hbsm Hrab.
(* essai avec le déterminant défini par permutations *)
assert (Habsm : is_square_matrix (A * B) = true). {
  now apply squ_mat_mul_is_squ.
}
remember (mat_nrows A) as n eqn:Hra.
rename Hrab into Hrb.
symmetry in Hra, Hrb.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold det; cbn.
  move Hnz at top; subst n; cbn.
  rewrite Hra, Hrb; cbn.
  symmetry; apply rngl_mul_1_l.
}
...
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite mat_mul_nrows.
unfold det'.
rewrite Hra, Hrb.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite mat_el_mul; cycle 1. {
      rewrite mat_mul_nrows, Hra.
      flia Hj.
    } {
      rewrite mat_mul_ncols; [ | rewrite Hra; flia Hj ].
      rewrite square_matrix_ncols; [ | easy ].
      rewrite Hrb.
      apply canon_sym_gr_list_ub; [ | flia Hj ].
      specialize (fact_neq_0 n) as Hfnz.
      flia Hi Hfnz.
    }
    rewrite square_matrix_ncols; [ | easy ].
    rewrite Hra.
    easy.
  }
  cbn.
  easy.
}
cbn.
(*1*)
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j (_, Hj).
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j (_, Hj).
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
rewrite rngl_mul_comm; [ | now destruct Hif ].
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j (_, Hj).
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
rewrite rngl_mul_comm; [ | now destruct Hif ].
symmetry.
(*
Noting
   ε(i) = signature of the i-th permutation in the canonic symmetric group
   σ(i,j) = j-th element of the i-th permutation in the canonic sym gr
We have to prove that
  ∑ (i = 0, n!-1), ε(i) ∏ (j = 0, n-1), ∑ (k = 0, n-1), a(j,k) * b(k,σ(i,j)) =
  ∑ (i = 0, n! - 1), ε(i) ∏ (j = 0, n-1), a(j,σ(i,j)) *
  ∑ (i = 0, n! - 1), ε(i) ∏ (j = 0, n-1), b(j,σ(i,j))
The problem is that the lhs contains
  n!*n^n terms
But the rhs contains
  n!*n! terms
Some terms of the lhs must cancel each other. But which ones?
*)
destruct n; [ easy | ].
destruct n. {
  cbn - [ "/" nth ].
...
  unfold ε'.
  do 3 rewrite rngl_summation_only_one.
  do 7 rewrite rngl_product_only_one.
  rewrite rngl_summation_only_one; cbn.
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  now do 3 rewrite rngl_mul_1_l.
}
destruct n. {
  unfold iter_seq, iter_list; cbn.
  do 7 rewrite rngl_add_0_l.
  do 6 rewrite rngl_mul_1_l.
  unfold ε', iter_seq, iter_list; cbn.
  do 8 rewrite rngl_mul_1_l.
  rewrite rngl_add_0_r.
  rewrite rngl_sub_0_r; [ | now destruct Hif; left ].
  rewrite rngl_add_sub; [ | now destruct Hif; left ].
  rewrite rngl_mul_1_l.
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  remember (mat_el A) as a eqn:Ha.
  remember (mat_el B) as b eqn:Hb.
  move b before a.
(**)
  ring_simplify.
(*
  rewrite rngl_mul_1_l.
  do 2 rewrite rngl_mul_1_l.
  unfold rngl_sub.
  replace rngl_has_opp with true by now destruct Hif.
  rewrite rngl_mul_1_r.
  rewrite rngl_add_0_l.
  rewrite rngl_mul_opp_l; [ | now destruct Hif ].
  rewrite rngl_mul_opp_l; [ | now destruct Hif ].
  rewrite rngl_mul_opp_l; [ | now destruct Hif ].
  do 3 rewrite rngl_mul_1_l.
  rewrite fold_rngl_sub; [ | now destruct Hif ].
  rewrite fold_rngl_sub; [ | now destruct Hif ].
  rewrite fold_rngl_sub; [ | now destruct Hif ].
*)
...
(*
  (a 0 0 * b 0 0 + a 0 1 * b 1 0) * (a 1 0 * b 0 1 + a 1 1 * b 1 1) -
  (a 0 0 * b 0 1 + a 0 1 * b 1 1) * (a 1 0 * b 0 0 + a 1 1 * b 1 0) =

  (a 0 0 * a 1 1 - a 0 1 * a 1 0) * (b 0 0 * b 1 1 - b 0 1 * b 1 0)
*)
...1
rewrite rngl_summation_mul_summation; [ | now destruct Hif; left ].
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite <- rngl_mul_summation_distr_l; [ | now destruct Hif; left ].
  easy.
}
symmetry.
apply rngl_summation_eq_compat.
intros i (_, Hi).
rewrite <- rngl_mul_assoc.
f_equal.
symmetry.
rewrite rngl_mul_summation_distr_l; [ | now destruct Hif; left ].
symmetry.
rewrite rngl_product_shift; [ | flia Hnz ].
rewrite rngl_product_summation_distr; [ | destruct Hif; now left ].
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  erewrite rngl_product_eq_compat. 2: {
    intros k Hk.
    now rewrite (Nat.add_comm 1 k), Nat.add_sub.
  }
  easy.
}
cbn.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite rngl_mul_assoc.
  rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
  rewrite <- rngl_product_mul_distr; [ | now destruct Hif ].
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros k Hk.
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  easy.
}
symmetry.
(* bizarre: n^n termes vs n! termes *)
destruct (Nat.eq_dec n 2) as [Hn2| Hn2]. {
  move Hn2 at top; subst n.
  cbn - [ "/" "mod" Nat.pow "-" canon_sym_gr_list ].
  replace (2 - 1) with 1 by easy.
  replace (2 ^ 2 - 1) with 3 by easy.
  cbn in Hi.
  cbn - [ "/" "mod" ].
  unfold iter_seq, iter_list.
  cbn - [ "/" "mod" ].
  do 2 rewrite rngl_add_0_l.
  do 6 rewrite rngl_mul_1_l.
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.mod_0_l; [ | easy ].
  rewrite Nat.mod_0_l; [ | easy ].
  do 4 rewrite Nat.div_1_r.
  rewrite Nat.div_same; [ | easy ].
  rewrite Nat.mod_same; [ | easy ].
  rewrite Nat.mod_small; [ | flia ].
  cbn.
  unfold ε'; cbn.
  unfold iter_seq, iter_list; cbn.
  do 8 rewrite rngl_mul_1_l.
  repeat rewrite rngl_add_0_r.
  rewrite rngl_sub_0_r; [ | now destruct Hif; left ].
  rewrite rngl_mul_1_l.
  rewrite rngl_mul_1_r.
  rewrite rngl_add_sub; [ | now destruct Hif; left ].
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  rewrite rngl_mul_1_l.
  rewrite rngl_mul_1_r.
  destruct (Nat.eq_dec i 1) as [Hi1| Hi1]. {
    subst i.
    cbn.
...
intros.
(* essai avec le déterminant défini par récurrence *)
cbn.
rewrite List_map_seq_length.
unfold det.
remember (mat_nrows A) as n eqn:Hra.
symmetry in Hra.
enough (Hrb : mat_nrows B = n).
...
intros.
rewrite laplace_formula_on_rows with (i := 0).
rewrite laplace_formula_on_rows with (i := 0).
rewrite laplace_formula_on_rows with (i := 0).
rewrite mat_mul_ncols.
(* déjà, ce serait pas mal si on  prouvait que com(A*B)=com(A)*com(B) *)
(* mais je viens de laisser tomber cette idée parce que, de toutes façons,
   la définition de com fait déjà intervenir det : ça boucle ! *)
...
Check comatrix_mul.
...
intros.
Check @laplace_formula_on_rows.
(* https://www.youtube.com/watch?v=-CySi7uauCg *)
...
rewrite det_is_det_by_canon_permut.
rewrite det_is_det_by_canon_permut.
rewrite det_is_det_by_canon_permut.
cbn; rewrite List_map_seq_length.
unfold determinant'.
...
Check laplace_formula_on_rows.
Check laplace_formula_on_cols.
Search comatrix.
...
Require Import IterMul.
Search determinant.
...
intros.
unfold determinant; cbn.
rewrite List_map_seq_length.
Print determinant_loop.
...
*)

End a.
