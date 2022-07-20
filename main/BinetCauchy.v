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

Require Import Misc PermutationFun SortingFun RingLike.
Require Import IterAdd IterMul IterAnd Pigeonhole.
Require Import Matrix PermutSeq Signature.
Require Import Determinant.
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
unfold sign_diff, ff_app.
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

Theorem app_seq_swap_is_permut_list : ∀ i j l,
  is_permut_list (seq 0 i ++ j :: l)
  → i < j
  → is_permut_list (seq 0 i ++ list_swap_elem 0 (j :: l) 0 (j - i)).
Proof.
intros * Hp Hilj.
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
  unfold ff_app in Huv.
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
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        easy.
      } {
        rewrite (@Nat_succ_sub_succ_r v i) in Huv; [ | flia Hviz ].
        rewrite List_nth_succ_cons in Huv.
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
  is_permut_list (seq 0 i ++ l)
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
    unfold ff_app in H2.
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
  assert (Hpa : is_permut_list (seq 0 i ++ la)). {
    rewrite Hla.
    now apply app_seq_swap_is_permut_list.
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
  unfold ff_app.
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
  is_permut_list l
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
  is_permut_list l
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
assert (H : is_permut (S n) l) by easy.
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
  is_permut_list (seq 0 i ++ p)
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
  unfold ff_app in H2.
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
now apply app_seq_swap_is_permut_list.
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
  → (∀ k, k < i → ff_app la k = k) ∧ nth i la 0 = j.
Proof.
intros * Hla.
unfold ff_app.
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

Theorem in_list_prodn_length : ∀ A (ll : list (list A)) l,
  (∀ l, l ∈ ll → l ≠ [])
  → l ∈ list_prodn ll
  → length l = length ll.
Proof.
intros * Hlz Hl.
revert l Hl.
induction ll as [| l1]; intros. {
  cbn in Hl.
  destruct Hl as [Hl| Hl]; [ now subst l | easy ].
}
cbn in Hl.
apply in_flat_map in Hl.
destruct Hl as (a & Hl1 & Ha).
apply in_map_iff in Ha.
destruct Ha as (l3 & Hl & Hl3).
subst l; cbn; f_equal.
apply IHll; [ | easy ].
intros l4 Hl4.
now apply Hlz; right.
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
  apply in_list_prodn_length in Hl2; [ easy | ].
  intros l4 Hl4.
  specialize (Hll _ (or_intror Hl4)).
  destruct l4; [ | easy ].
  now symmetry in Hll.
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

Theorem nth_in_list_prodn : ∀ A (d : A) ll l i,
  i < length ll
  → l ∈ list_prodn ll
  → nth i l d ∈ nth i ll [].
Proof.
intros * Hi Hll.
revert l i Hi Hll.
induction ll as [| l1]; intros; [ easy | ].
cbn in Hll |-*.
destruct i. {
  destruct ll as [| l2]. {
    apply in_flat_map in Hll.
    destruct Hll as (a & Ha & Hla).
    apply in_map_iff in Hla.
    now destruct Hla as (l2 & H & Hl2); subst l.
  }
  apply in_flat_map in Hll.
  destruct Hll as (a & Hl1 & Hl).
  apply in_map_iff in Hl.
  now destruct Hl as (l3 & H & Hl3); subst l.
}
cbn in Hi; apply Nat.succ_lt_mono in Hi.
destruct ll as [| l2]; [ easy | ].
apply in_flat_map in Hll.
destruct Hll as (a & Ha & Hl).
apply in_map_iff in Hl.
destruct Hl as (l3 & H & Hl3); subst l.
rewrite List_nth_succ_cons.
now apply IHll.
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
rewrite det_is_det'; try now destruct Hif. 2: {
  now apply mat_select_rows_is_square.
}
rewrite det'_is_det''; try now destruct Hif. 2: {
  now rewrite mat_select_rows_nrows.
}
rewrite det_is_det'; try now destruct Hif. 2: {
  apply mat_select_rows_is_square; [ easy | | ]. {
    now rewrite isort_length.
  } {
    intros k Hk.
    apply Hkl.
    now apply in_isort in Hk.
  }
}
rewrite det'_is_det''; try now destruct Hif. 2: {
  rewrite mat_select_rows_nrows.
  now rewrite isort_length.
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
assert (Heql : equality (list_eqb Nat.eqb)). {
  intros la lb.
  apply -> equality_list_eqb.
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
    apply collapse_is_permut.
  }
  rewrite permut_comp_isort_rank_r; [ | apply isort_rank_is_permut_list ].
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
    now apply isort_rank_is_permut.
  }
  unfold collapse.
  rewrite permut_comp_isort_rank_l; [ | apply isort_rank_is_permut_list ].
  rewrite isort_rank_length, <- Hn.
  apply comp_1_r.
  apply in_all_comb_iff in Hl.
  now destruct Hl.
}
rewrite rngl_summation_list_change_var with (g := g1) (h := h1); [ | easy ].
rewrite (rngl_summation_list_permut (list_eqb Nat.eqb))
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
      apply collapse_is_permut.
    }
    rewrite rngl_mul_comm; [ | now destruct Hif ].
    f_equal.
    apply ε_collapse_ε.
    now apply (no_dup_NoDup Nat.eqb_eq).
  }
  set (g2 := λ i, S (ff_app (isort_rank Nat.leb kl) (i - 1))).
  set (h2 := λ i, S (ff_app (collapse kl) (i - 1))).
  assert (Hgh2 : ∀ i, 1 ≤ i ≤ n → g2 (h2 i) = i). {
    intros i Hi.
    unfold g2, h2.
    rewrite Nat_sub_succ_1.
    rewrite permut_permut_isort; [ flia Hi | | ]. {
      apply isort_rank_is_permut_list.
    }
    rewrite isort_rank_length, <- Hn; flia Hi.
  }
  assert (Hhg2 : ∀ i, 1 ≤ i ≤ n → h2 (g2 i) = i). {
    intros i Hi.
    unfold g2, h2.
    rewrite Nat_sub_succ_1.
    unfold collapse.
    rewrite permut_isort_permut; [ flia Hi | | ]. {
      apply isort_rank_is_permut_list.
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
    unfold ff_app.
    unfold g2.
    rewrite Nat_sub_succ_1.
    rewrite (List_map_nth' 0). 2: {
      rewrite collapse_length.
      apply isort_rank_ub.
      now intros H; rewrite H in Hn.
    }
    do 3 rewrite fold_ff_app.
    unfold collapse.
    rewrite permut_isort_permut; cycle 1. {
      apply isort_rank_is_permut_list.
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
      apply isort_rank_is_permut_list.
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
  apply -> equality_list_eqb.
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
     ff_app (nth i (all_comb n) []) k = ff_app (nth j (all_comb n) []) k). {
    intros k Hk.
    apply H1.
    apply (permutation_in_iff Nat.eqb_eq) with (la := seq 0 n). 2: {
      now apply in_seq.
    }
    apply (permutation_sym Nat.eqb_eq).
    eapply (permutation_trans Nat.eqb_eq). {
      apply permut_list_permutation_iff.
      apply isort_rank_is_permut_list.
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
  apply in_isort_rank_lt in Hj.
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
  apply in_isort_rank_lt in Hj.
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
  permutation (list_eqb Nat.eqb)
    (list_prodn (repeat (seq 1 (S n)) m))
    (list_prodn (repeat (seq 1 n) m) ++
     filter (member Nat.eqb (S n)) (list_prodn (repeat (seq 1 (S n)) m))).
Proof.
intros.
assert (Hel : equality (list_eqb Nat.eqb)). {
  apply -> equality_list_eqb.
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

(*
Theorem map_map_map_sub_succ : ∀ m n p,
  n ≤ S p
  → map (map (λ i, i + n - p)) (map (map_sub_succ p) (sls1n n (S m))) =
    flat_map
      (λ a,
         filter (is_sorted Nat.ltb)
           (map (cons a) (list_prodn (repeat (seq 1 n) m))))
      (seq 1 n).
Proof.
intros * Hnp.
(*
Compute (
  let n := 6 in
  let m := 2 in
  let p := 5 in
  map (map (λ i, i + n - p))
  (map (map_sub_succ p) (sls1n n (S m)))
 =
  flat_map
    (λ x : nat,
       filter (is_sorted Nat.ltb)
         (map (cons x) (list_prodn (repeat (seq 1 n) m))))
    (seq 1 n)
).
...
*)
rewrite map_map.
unfold map_sub_succ.
erewrite map_ext_in. 2: {
  intros t Ht.
  rewrite map_map.
  erewrite map_ext_in. 2: {
    intros a Ha.
    rewrite <- Nat.add_sub_swap. 2: {
      apply in_sls1n_iff in Ht.
      destruct Ht as [| (Hs & Htm & Ht)]; [ easy | ].
      specialize (Ht _ Ha).
      flia Hnp Ht.
    }
    rewrite Nat_sub_sub_swap, Nat.add_comm.
    rewrite <- Nat.add_sub_assoc; [ | apply Nat.le_succ_diag_r ].
    rewrite Nat.sub_succ_l; [ | easy ].
    now rewrite Nat.sub_diag, Nat.add_1_r.
  }
  easy.
}
...
rewrite map_map.
revert m p Hnp.
induction n; intros; [ easy | ].
cbn - [ seq ].
apply Nat.succ_le_mono in Hnp.
...
destruct p. {
  apply Nat.le_0_r in Hnp; subst n.
...
  unfold map_sub_succ.
...
destruct p; [ easy | ].
cbn - [ seq ].
rewrite map_app.
rewrite map_map.
Theorem glop : ∀ n la,
  (∀ a, a ∈ la → a ≤ S n)
  → map_sub_succ (S n) la = map S (map_sub_succ n la).
Proof.
intros * Hla.
induction la as [| a]; [ easy | ].
cbn - [ "-" ].
f_equal. {
  specialize (Hla _ (or_introl eq_refl)).
  flia Hla.
}
apply IHla.
intros i Hi.
now apply Hla; right.
Qed.
remember (map _ _) as x.
erewrite map_ext_in. 2: {
  intros t Ht.
  rewrite glop. 2: {
    intros a Ha.
    apply in_sls1n_iff in Ht.
    destruct Ht as [| Ht]; [ easy | ].
    destruct Ht as (Hs & Htm & Ht).
    specialize (Ht a Ha).
    flia Ht Hnp.
  }
  rewrite map_map.
  easy.
}
subst x.
erewrite map_ext_in. 2: {
  intros t Ht.
  rewrite glop. 2: {
    intros a Ha.
    apply in_sls1n_iff in Ht.
    destruct Ha as [Ha| Ha]. {
      subst a.
      now apply -> Nat.succ_le_mono.
    }
    destruct Ht as [(H1, H2)| Ht]; [ now subst t | ].
    destruct Ht as (Hs & Htm & Ht).
    specialize (Ht a Ha).
    flia Ht Hnp.
  }
  rewrite map_map.
  easy.
}
...
rewrite IHn.
...
Theorem sub_lists_of_seq_1_n_succ_r : ∀ m n,
  sub_lists_of_seq_1_n n (S m) =
  concat
    (map (filter (is_sorted Nat.ltb))
       (map (λ a : nat, map (cons a) (list_prodn (repeat (seq 1 n) m)))
          (seq 1 n))).
Proof.
intros.
rewrite map_map.
rewrite <- flat_map_concat_map.
unfold sub_lists_of_seq_1_n.
...
rewrite <- map_map_map_sub_succ with (p := n); [ | easy ].
symmetry.
erewrite map_ext_in. 2: {
  intros t Ht.
  erewrite map_ext_in. 2: {
    intros i Hi.
    now rewrite Nat.sub_diag, Nat.sub_0_r.
  }
  now rewrite map_id.
}
now rewrite map_id.
...
Compute (
  let n := 5 in
  let m := 2 in
  let p := 7 in
  map (map (λ i, i - (p - n)))
  (map (map_sub_succ p) (sls1n n (S m)))
 =
  flat_map
    (λ x : nat,
       filter (is_sorted Nat.ltb)
         (map (cons x) (list_prodn (repeat (seq 1 n) m))))
    (seq 1 n)
).
...
revert m.
induction n; intros; [ easy | ].
cbn - [ seq ].
rewrite map_app.
cbn - [ seq ].
Compute (
  let n := 5 in
  let m := 2 in
  sub_lists_of_seq_1_n n (S m) =
  flat_map
    (λ x : nat,
       filter (is_sorted Nat.ltb)
         (map (cons x) (list_prodn (repeat (seq 1 n) m))))
    (seq 1 n)
).
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
(*
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
  let m := 2 in
  let n := 3 in
  let A := mk_mat [[1;2;3];[4;5;6]]%Z in
  let B := mk_mat [[7;8];[9;-10];[11;12]]%Z in
     det (A * B) =
     ∑ (jl ∈ sub_lists_of_seq_1_n n m),
     det (mat_select_cols jl A) * det (mat_select_rows jl B)
).
...
*)
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
(**)
rewrite det_is_det'; try now destruct Hif.
rewrite det'_is_det''; try now destruct Hif. 2: {
  now rewrite mat_mul_nrows, Har.
}
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
      unfold ff_app.
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
    rewrite det_is_det'; try now destruct Hif. 2: {
      apply mat_select_rows_is_square; [ easy | congruence | ].
      rewrite Hbr.
      intros j Hj.
      now apply Hln.
    }
    rewrite det'_is_det''; try now destruct Hif. 2: {
      rewrite mat_select_rows_nrows; congruence.
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
    apply in_list_prodn_length in Hla. 2: {
      intros lb Hlb.
      apply repeat_spec in Hlb; subst lb.
      now destruct n.
    }
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
(*
symmetry.
unfold sub_lists_of_seq_1_n.
rewrite rngl_summation_list_map.
*)
assert (Hel : equality (list_eqb Nat.eqb)). {
  intros la lb.
  apply -> equality_list_eqb.
  unfold equality.
  apply Nat.eqb_eq.
}
(*
set (revn := λ l : list nat, rev l).
erewrite (rngl_summation_list_permut (list_eqb Nat.eqb))
  with (lb := rev (sls1n n m)); [ | easy | now apply permutation_rev_r ].
erewrite rngl_summation_list_change_var with (g := revn) (h := revn). 2: {
  unfold rev; intros; apply rev_involutive.
}
remember (∑ (jl ∈ _), _) as x; subst x. (* renaming *)
Compute (
let n := 4 in
let k := 3 in
(map revn (rev (sls1n n k)),
 filter (is_sorted Nat.ltb) (list_prodn (repeat (seq 1 n) k)))
).
symmetry.
*)
(**)
set (f := no_dup Nat.eqb).
erewrite (rngl_summation_list_permut _ Hel). 2: {
  assert (H : ∀ ll,
    permutation (list_eqb Nat.eqb) ll
      (filter f ll ++ filter (λ l, negb (f l)) ll)). {
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
  unfold f in Hsl.
  apply Bool.negb_true_iff in Hsl.
  rewrite ε_when_dup; [ | now destruct Hif | now destruct Hif | ]. 2: {
    intros H.
    apply (no_dup_NoDup Nat.eqb_eq) in H.
    congruence.
  }
  rewrite <- rngl_mul_assoc.
  now apply rngl_mul_0_l; destruct Hif; left.
}
rewrite rngl_add_0_l.
remember (∑ (kl ∈ _), _) as x; subst x. (* renaming *)
subst f.
(*
  ∑ (kl ∈ filter (no_dup Nat.eqb) (list_prodn (repeat (seq 1 n) m))),
  ε kl * ∏ (i = 1, m), mat_el A i kl.(i) *
  det (mat_select_rows (isort Nat.leb kl) B)
*)
(* possible first step to do, for this left handed side *)
(*
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
  ∑ (kl ∈ filter (no_dup Nat.eqb) (list_prodn (repeat (seq 1 n) m))),
  if list_eqb Nat.eqb (isort Nat.leb kl) jl then
    ε kl * ∏ (i = 1, m), mat_el A i kl.(i) *
    det (mat_select_rows jl B)
  else 0
*)
Theorem rngl_summation_filter_no_dup_list_prodn : ∀ n m f,
  ∑ (kl ∈ list_prodn (repeat (seq 1 n) m)), ε kl * f kl =
  ∑ (jl ∈ sub_lists_of_seq_1_n n m), ∑ (kl ∈ all_permut 0 jl), ε kl * f kl.
Proof.
intros.
revert n.
induction m; intros; cbn. {
  rewrite sub_lists_of_seq_1_n_0_r.
  do 2 rewrite rngl_summation_list_only_one; cbn.
  now rewrite rngl_summation_list_only_one.
}
rewrite App_list_concat_map.
(*
rewrite rngl_summation_list_concat.
Compute (
  let n := 4 in
  let m := 2 in
  map (λ a : nat, map (cons a) (list_prodn (repeat (seq 1 n) m))) (seq 1 n)
).
Compute (
  let n := 4 in
  let m := 2 in
(
concat (
map (filter (is_sorted Nat.ltb))
(
  map (λ a : nat, map (cons a) (list_prodn (repeat (seq 1 n) m))) (seq 1 n)
)
),
sub_lists_of_seq_1_n n (S m)
)
).
*)
unfold sub_lists_of_seq_1_n.
Theorem sls1n_succ_r : ∀ i m n,
  sls1n i n (S m) =
  concat
    (map (filter (is_sorted Nat.ltb))
       (map (λ a : nat, map (cons a) (list_prodn (repeat (seq i n) m)))
          (seq i n))).
Proof.
intros.
rewrite map_map.
rewrite <- flat_map_concat_map.
(*
  ============================
  sls1n i n (S m) =
  flat_map (λ x : nat, filter (is_sorted Nat.ltb) (map (cons x) (list_prodn (repeat (seq i n) m)))) (seq i n)
*)
revert i m.
induction n; intros; [ easy | ].
cbn.
rewrite IHn.
f_equal. 2: {
  apply List_flat_map_ext_in.
  intros j Hj.
  do 2 rewrite List_filter_map.
  f_equal.
  clear IHn.
  remember (λ la, _) as x; subst x.
  apply in_seq in Hj.
  do 2 rewrite List_filter_is_sorted_cons.
  f_equal.
  rewrite list_prodn_repeat_seq_succ_l.
  rewrite List_filter_map.
  rewrite List_filter_filter.
  replace (i :: seq (S i) n) with (seq i (S n)) by easy.
  remember (list_prodn (repeat (seq i (S n)) m)) as lla eqn:Hlla.
  rewrite List_filter_map.
  f_equal.
  remember (λ la, _) as x; subst x; symmetry.
  remember (λ la, _) as x; subst x; symmetry.
  apply filter_ext_in.
  intros la Hla.
  remember (is_sorted Nat.ltb (j :: la)) as s eqn:Hs; symmetry in Hs.
  destruct s; [ cbn | easy ].
  apply Bool.negb_true_iff.
  apply (member_false_iff Nat.eqb_eq).
  intros a Ha H; subst a.
  apply (sorted_cons_iff Nat_ltb_trans) in Hs.
  destruct Hs as (Hs & Hjlt).
  specialize (Hjlt _ Ha).
  apply Nat.ltb_lt in Hjlt.
  flia Hj Hjlt.
}
clear IHn.
replace (i :: seq (S i) n) with (seq i (S n)) by easy.
replace (map (λ l, i :: l)) with (map (cons i)) by easy.
(*
  ============================
  map (cons i) (sls1n (S i) n m) =
  filter (is_sorted Nat.ltb) (map (cons i) (list_prodn (repeat (seq i (S n)) m)))
*)
...
Theorem glop : ∀ i m n,
  sls1n (S i) n m =
  filter (λ la, (is_sorted Nat.ltb la && (hd (S i) la ≠? i))%bool)
    (list_prodn (repeat (seq i (S n)) m)).
Proof.
intros.
destruct m. {
  destruct i; [ now destruct n | ].
  remember (S i) as x; cbn; subst x.
  rewrite Bool.if_negb.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S i) i) as [H| H]; [ flia H | clear H ].
  now destruct n.
}
Theorem glop : ∀ i m n,
  list_prodn (repeat (seq i n) (S m)) =
  concat (map (λ j, map (cons j) (list_prodn (repeat (seq i n) m))) (seq i n)).
Proof.
intros; cbn.
now rewrite App_list_concat_map.
Qed.
rewrite glop.
rewrite <- concat_filter_map.
rewrite map_map.
erewrite map_ext_in. 2: {
  intros j Hj.
  rewrite List_filter_map.
  cbn - [ is_sorted seq ].
  easy.
}
...
revert i m.
induction n; intros. {
  cbn; symmetry.
  rewrite App_list_concat_map.
  rewrite <- flat_map_concat_map.
  cbn - [ is_sorted ].
  rewrite app_nil_r.
  rewrite List_filter_map.
  rewrite (proj2 (List_filter_nil_iff _ _)); [ easy | ].
  intros la Hla; cbn.
  now rewrite Nat.eqb_refl, Bool.andb_false_r.
}
cbn - [ seq ].
rewrite App_list_concat_map.
rewrite <- flat_map_concat_map.
Compute (
  let i := 42 in
  let n := 3 in
  let m := 2 in
list_prodn (repeat (seq i n) (S m)) =
concat (map (λ j, map (cons j) (list_prodn (repeat (seq i n) m))) (seq i n))
).
Print list_prodn.
...
Compute (
  let i := 0(*42*) in
  let n := 4 in
  let m := 0(*3*) in
  sls1n (S i) n m =
  filter (λ la, (is_sorted Nat.ltb la && (hd 0 la ≠? i))%bool)
    (list_prodn (repeat (seq i (S n)) m))
).
Print sls1n.
...
  (sls1n (S i) n m) =
  filter (is_sorted Nat.ltb) (filter (λ la, negb (member Nat.eqb i la)) (list_prodn (repeat (seq i (S n)) m)))
).
  map (cons i) (sls1n (S i) n m) =
  filter (is_sorted Nat.ltb) (map (cons i) (list_prodn (repeat (seq i (S n)) m)))
).
...
seq (S i) n).
sls1n (S i) n m).
...
map (cons i) (sls1n (S i) n m)
=
filter (is_sorted Nat.ltb)
  (map (cons i) (list_prodn (repeat (seq i (S n)) m)))
).
...
rewrite List_filter_map.
f_equal.
Print list_prodn.
(**)
...
revert n i.
induction m; intros; [ now destruct n | ].
cbn - [ is_sorted ].
rewrite App_list_concat_map.
rewrite <- flat_map_concat_map.
cbn - [ is_sorted ].
...
... previous proof attempt
destruct m; [ now destruct n | ].
(*0*)
destruct n. {
  cbn - [ is_sorted ].
  symmetry.
  rewrite App_list_concat_map.
  rewrite <- flat_map_concat_map.
  cbn - [ is_sorted ].
  rewrite app_nil_r.
  rewrite List_filter_map.
  rewrite (proj2 (List_filter_nil_iff _ _)); [ easy | ].
  intros la Hla; cbn.
  destruct i; [ easy | ].
  replace (S i <=? i) with false; [ easy | ].
  now symmetry; apply Nat.leb_gt.
}
(*1*)
destruct n. {
  cbn - [ is_sorted ].
  destruct m. {
    cbn - [ is_sorted ].
    rewrite App_list_concat_map; cbn.
    rewrite Nat.leb_refl; cbn.
    destruct i; [ easy | ].
    replace (S i <=? i) with false; [ easy | ].
    now symmetry; apply Nat.leb_gt.
  }
  rewrite app_nil_r.
  symmetry.
  rewrite App_list_concat_map.
  rewrite <- flat_map_concat_map.
  cbn - [ is_sorted ].
  rewrite app_nil_r.
  rewrite filter_app.
  rewrite List_filter_map.
  rewrite (proj2 (List_filter_nil_iff _ _)). {
    rewrite app_nil_l.
    rewrite App_list_concat_map.
    rewrite List_filter_map.
    apply List_map_eq_nil_iff.
    apply List_filter_nil_iff.
    intros la Hla; cbn.
    rewrite Nat.leb_refl.
    rewrite Bool.andb_true_l.
    apply in_concat in Hla.
    destruct Hla as (lla & Ha & Hla).
    apply in_map_iff in Ha.
    destruct Ha as (a & H & Ha); subst lla.
    apply in_map_iff in Hla.
    destruct Hla as (lb & H & Hlb); subst la.
    destruct Ha as [Ha| Ha]. {
      subst a.
      destruct i; [ easy | ].
      destruct i; [ easy | ].
      replace (_ <=? _) with false; [ easy | ].
      symmetry; apply Nat.leb_gt; flia.
    }
    destruct Ha as [Ha| Ha]; [ subst a | easy ].
    destruct i; [ easy | ].
    replace (_ <=? _) with false; [ easy | ].
    now symmetry; apply Nat.leb_gt.
  }
  intros la Hla; cbn.
  destruct i; [ easy | ].
  replace (S i <=? i) with false; [ easy | ].
  now symmetry; apply Nat.leb_gt.
}
(*2*)
Theorem glop : ∀ m n k i,
  sls1n (S i) (k + n) (S m) =
  filter (λ a : list nat, is_sorted Nat.ltb (i :: a))
    (list_prodn (repeat (seq i (k + S n)) (S m))).
Proof.
intros.
cbn - [ is_sorted ].
rewrite App_list_concat_map.
rewrite <- flat_map_concat_map.
remember (list_prodn (repeat (seq i (k + S n)) m)) as lla eqn:Hlla.
...
apply (glop m n 2 i).
...
  ============================
  sls1n (S i) n (S m) =
  filter (λ a : list nat, is_sorted Nat.ltb (i :: a))
    (list_prodn (repeat (seq i (S n)) (S m)))
  ============================
  sls1n (S i) (S n) (S m) =
  filter (λ a : list nat, is_sorted Nat.ltb (i :: a))
    (list_prodn (repeat (seq i (S (S n))) (S m)))
============================
  sls1n (S i) (S (S n)) (S m) =
  filter (λ a : list nat, is_sorted Nat.ltb (i :: a))
    (list_prodn (repeat (seq i (S (S (S n)))) (S m)))
...
  induction m; intros. {
    cbn.
    rewrite Bool.andb_true_r.
    destruct i; [ easy | ].
    rewrite if_leb_le_dec.
    destruct (le_dec (S i) i) as [H| H]; [ flia H | easy ].
  }
  cbn - [ is_sorted ].
  rewrite App_list_concat_map.
  rewrite concat_map.
  rewrite map_map.
  rewrite <- concat_filter_map.
  rewrite map_map.
  apply concat_nil_Forall, Forall_forall.
  intros lla Hlla.
  apply in_map_iff in Hlla.
  destruct Hlla as (a & Ha & Hai).
  destruct Hai; [ subst a | easy ].
  remember (λ la, _) as x; subst x.
  rewrite map_map in Ha.
...
Compute (
  let n := 4 in
  let m := 2 in
  let i := 2 in
  let j := 3 in
    (map
       (λ x : nat,
          filter (λ a : list nat, is_sorted Nat.ltb (i :: a))
            (map (cons i) (map (cons x) (list_prodn (repeat [i] m))))) [i])
).
...
Theorem list_prodn_repeat_cons : ∀ A (a : A) la n,
  list_prodn (repeat (a :: la) (S n)) =
  map (cons a) (list_prodn (repeat (a :: la) n)) ++
  flat_map (λ b : A, map (cons b) (list_prodn (repeat (a :: la) n))) la.
Proof.
intros.
cbn.
rewrite App_list_concat_map.
now rewrite <- flat_map_concat_map.
Qed.
destruct m; [ easy | ].
cbn - [ is_sorted seq ].
rewrite App_list_concat_map.
rewrite <- flat_map_concat_map.
rewrite App_list_concat_map.
rewrite <- flat_map_concat_map.
(* ouais, ça marche pas, mon truc *)
...
... return
rewrite list_prodn_repeat_cons.
rewrite filter_app.
Compute (
  let n := 4 in
  let m := 2 in
  let i := 2 in
  let j := 3 in
(*
  (list_prodn (repeat (seq (S i) n) m)) =
  (list_prodn (repeat (i :: seq (S i) n) m))
).
...
*)
...
rewrite seq_S.
cbn - [ seq ].
rewrite flat_map_app.
cbn - [ seq ].
rewrite app_nil_r.
rewrite IHn.
...
Compute (
  let n := 5 in
  let m := 3 in
  let i := 3 in
  sls1n i n (S m) =
  concat
    (map (filter (is_sorted Nat.ltb))
       (map (λ a : nat, map (cons a) (list_prodn (repeat (seq i n) m)))
          (seq i n)))
).
...
Theorem sub_lists_of_seq_1_n_succ_r : ∀ m n,
  sub_lists_of_seq_1_n n (S m) =
  concat
    (map (filter (is_sorted Nat.ltb))
       (map (λ a : nat, map (cons a) (list_prodn (repeat (seq 1 n) m)))
          (seq 1 n))).
Proof.
intros.
unfold sub_lists_of_seq_1_n.
apply sls1n_succ_r.
...
Compute (
  let n := 5 in
  let m := 3 in
  let i := 3 in
  sls1n i n (S m) =
  concat
    (map (filter (is_sorted Nat.ltb))
       (map (λ a : nat, map (cons a) (list_prodn (repeat (seq i n) m)))
          (seq i n)))
).
... return.
rewrite sub_lists_of_seq_1_n_succ_r.
rewrite rngl_summation_list_concat.
rewrite rngl_summation_list_concat.
Search (∑ (_ ∈ map _ _), _).
rewrite map_map.
rewrite rngl_summation_list_map.
rewrite rngl_summation_list_map.
apply rngl_summation_list_eq_compat.
intros i Hi.
rewrite rngl_summation_list_map.
remember (∑ (kl ∈ _), _) as x; subst x.
...
Theorem rngl_summation_filter_no_dup_list_prodn : ∀ n m f,
  ∑ (kl ∈ filter (no_dup Nat.eqb) (list_prodn (repeat (seq 1 n) m))), f kl =
  ∑ (jl ∈ sub_lists_of_seq_1_n n m), ∑ (kl ∈ all_permut 0 jl), f kl.
Proof.
intros.
destruct m; intros; cbn. {
  rewrite sub_lists_of_seq_1_n_0_r.
  do 2 rewrite rngl_summation_list_only_one; cbn.
  now rewrite rngl_summation_list_only_one.
}
rewrite App_list_concat_map.
...
rewrite <- concat_filter_map.
rewrite rngl_summation_list_concat.
rewrite map_map.
remember (∑ (kl ∈ _), _) as x; subst x.
rewrite rngl_summation_list_map.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  rewrite rngl_summation_list_empty; [ | easy ].
  now rewrite rngl_summation_list_empty.
}
rewrite rngl_summation_seq_summation; [ | easy ].
rewrite Nat.add_comm, Nat.add_sub.
(* tout ça, c'était juste pour m'amuser, paskeu ça fait pas tellement
   avancer le schmilblick *)
Search (∑ (_ ∈ _), ∑ (_ ∈ _), _).
Check rngl_summation_list_concat.
(* peut-on exprimer "list_prodn" avec un "concat" ?
   si oui, alors on pourrait appliquer rngl_summation_list_concat *)
(* chais pas si ça aiderait, mais bon *)
(* du coup, faudrait prendre tout list_prodn et donc remettre un ε
   pour annuler les listes où il y a des duplications *)
Compute (
  let n := 5 in
  let m := 2 in
  list_prodn (repeat (seq 1 n) m)
).
Search list_prodn.
Print list_prodn.
Search (App (_ ∈ _), _).
...
(*
Compute (
  let n := 5 in
  let m := 2 in
  let f := λ l, length l + hd 3 l in
  ∑ (kl ∈ filter (no_dup Nat.eqb) (list_prodn (repeat (seq 1 n) m))), f kl =
  ∑ (jl ∈ sub_lists_of_seq_1_n n m), ∑ (kl ∈ all_permut 0 jl), f kl
).
...
*)
Theorem rngl_summation_list_by_subsets :
  ∀ A (eqb : A → _),
  ∀ B (la : list A) (lb : list B) lla f g g_1,
  (∀ b, b ∈ lb → g_1 (g b) = b)
  → (∀ la', la' ∈ lla → g (g_1 la') = la')
  → permutation eqb la (concat lla)
  → ∑ (a ∈ la), f a = ∑ (b ∈ lb), ∑ (a ∈ g b), f a.
Proof.
intros.
...
eapply rngl_summation_list_by_subsets with (eqb := list_eqb Nat.eqb)
  (g_1 := hd []).
(* hmmm... c'est compliqué... *)
(* compliqué de définir ?lla *)
...
Theorem rngl_summation_list_by_subsets :
  ∀ A B (la : list A) (lb : list B) llb f g f_1,
  (∀ a, a ∈ la → f_1 (f a) = a)
  → (∀ lb', lb' ∈ llb → f (f_1 lb') = lb')
  → ∑ (b ∈ lb), g b = ∑ (a ∈ la), ∑ (b ∈ f a), g b.
Proof.
... return
apply rngl_summation_list_by_subsets.
...
Theorem rngl_summation_list_all_permut : ∀ A (eqb : A → _),
  equality eqb →
  ∀ (d : A) lla llb f,
  (∀ la, la ∈ lla → ∃ lb, lb ∈ llb ∧ la ∈ all_permut d lb)
  → (∀ lb, lb ∈ llb → ∀ la, la ∈ all_permut d lb → la ∈ lla)
  → ∑ (la ∈ lla), f la = ∑ (lb ∈ llb), ∑ (la ∈ all_permut d lb), f la.
Proof.
intros * Heqb * Ha Hb.
...  bon, c'est pas clair...
revert lla Ha Hb.
induction llb as [| lb]; intros. {
  symmetry; rewrite rngl_summation_list_empty; [ symmetry | easy ].
  destruct lla as [| la]; [ now apply rngl_summation_list_empty | ].
  specialize (Ha _ (or_introl eq_refl)).
  now destruct Ha as (lb & Ha & _).
}
rewrite rngl_summation_list_cons.
assert (Hel : equality (list_eqb eqb)). {
  clear - Heqb; intros la lb.
  now apply -> equality_list_eqb.
}
set (g := λ la, member (list_eqb eqb) la (all_permut d lb)).
erewrite (rngl_summation_list_permut _ Hel). 2: {
  assert (H : ∀ ll,
    permutation (list_eqb eqb) ll
      (filter g ll ++ filter (λ l, negb (g l)) ll)). {
    now apply permutation_filter_app_filter.
  }
  apply H.
}
rewrite rngl_summation_list_app.
f_equal. {
  unfold g.
  remember (∑ (la ∈ _), _) as x in |-*; subst x.
  specialize (Hb _ (or_introl eq_refl)).
  apply (rngl_summation_list_permut _ Hel).
  clear - Hel Ha Hb.
Compute (
  let d := 0 in
  let eqb := Nat.eqb in
  let lb := [1;2;3] in
  let lla := [[1;2;3]] in
  permutation (list_eqb eqb)
    (filter (λ la, member (list_eqb eqb) la (all_permut d lb)) lla)
    (all_permut d lb)
).
(* ouais, c'est compliqué à tester *)
...
apply (NoDup_permutation Hel).
Check NoDup_permutation_bis.
...
  revert lb Ha Hb.
  induction lla as [| la]; intros. {
    cbn.
    specialize (Hb lb).
    assert (H : lb ∈ all_permut d lb). {
      unfold all_permut.
      apply in_map_iff.
      exists (seq 0 (length lb)).
      split; [ symmetry; apply List_map_nth_seq | ].
      unfold canon_sym_gr_list_list.
      apply in_map_iff.
      exists 0.
      split; [ apply canon_sym_gr_list_0_r | ].
      apply in_seq.
      split; [ easy | ].
      apply Nat.neq_0_lt_0, fact_neq_0.
    }
    now specialize (Hb H).
  }
  cbn.
  rewrite if_bool_if_dec.
  destruct (bool_dec (member _ _ _)) as [H1| H1]. 2: {
    specialize (proj1 (member_false_iff Hel _ _) H1) as H2.
    apply IHlla. {
      intros lc Hlc.
      specialize (Ha _ (or_intror Hlc)).
      destruct Ha as (ld & Hld & Hld').
      destruct Hld as [Hld| Hld]. {
        subst ld.
        exists lb.
        split; [ now left | easy ].
      } {
        exists ld.
        split; [ now right | easy ].
      }
    } {
      intros lc Hlc.
      specialize (H2 _ Hlc).
      specialize (Hb lc Hlc).
      now destruct Hb.
    }
  }
  apply (member_true_iff Hel) in H1.
  destruct H1 as (l1 & l2 & H1).
  rewrite H1.
  apply (permutation_cons_app Hel).
  rewrite <- H1.
(**)
  eapply (permutation_trans Hel); [ apply IHlla | ]. 3: {
    rewrite H1.
    (* bin non, ça marche pas *)
...
  eapply (permutation_trans Hel). {
    apply IHlla. {
      intros lc Hlc.
      specialize (Ha _ (or_intror Hlc)).
      destruct Ha as (ld & Hld & Hld').
      destruct Hld as [Hld| Hld]. {
        subst ld.
        exists lb.
        split; [ now left | easy ].
      } {
        exists ld.
        split; [ now right | easy ].
      }
    } {
      intros lc Hlc.
      specialize (Hb lc Hlc) as H2.
      destruct H2 as [H2| H2]; [ subst lc | easy ].
...
      subst lc.
      specialize (Ha la (or_introl eq_refl)).
      specialize (H2 _ Hlc).
      now destruct Hb.
    }
...
    } {
      intros lc Hlc.
      specialize (Hb _ Hlc).
      destruct Hb as [Hb| Hb]; [ | easy ].
      subst lc.
...
intros * Heqb * Ha Hb.
revert llb Ha Hb.
induction lla as [| la]; intros. {
  rewrite rngl_summation_list_empty; [ | easy ].
  destruct llb as [| lb]; [ now rewrite rngl_summation_list_empty | ].
  specialize (Hb _ (or_introl eq_refl) lb).
  assert (H : lb ∈ all_permut d lb). {
    unfold all_permut.
    apply in_map_iff.
    exists (seq 0 (length lb)).
    split; [ symmetry; apply List_map_nth_seq | ].
    unfold canon_sym_gr_list_list.
    apply in_map_iff.
    exists 0.
    split; [ apply canon_sym_gr_list_0_r | ].
    apply in_seq.
    split; [ easy | ].
    apply Nat.neq_0_lt_0, fact_neq_0.
  }
  now specialize (Hb H).
}
rewrite rngl_summation_list_cons.
destruct llb as [| lb]. {
  specialize (Ha _ (or_introl eq_refl)).
  now destruct Ha as (lb & Ha & _).
}
rewrite rngl_summation_list_cons.
assert (Hel : equality (list_eqb eqb)). {
  clear - Heqb; intros la lb.
  now apply -> equality_list_eqb.
}
set (g := λ la, member (list_eqb eqb) la (all_permut d lb)).
erewrite (rngl_summation_list_permut _ Hel). 2: {
  assert (H : ∀ ll,
    permutation (list_eqb eqb) ll
      (filter g ll ++ filter (λ l, negb (g l)) ll)). {
    now apply permutation_filter_app_filter.
  }
  apply H.
}
rewrite rngl_summation_list_app.
(* peut-être bon ; là, je vais essayer une induction sur llb, plutôt ; si elle
   marche pas, je peux retourner ici *)
...
rewrite (IHlla llb).
f_equal.
(* ouais, bin non, mais c'est normal : j'ai consommé un seul dans lla et
   un dans llb, mais llb est censé être associé à plusieurs dans lla *)
...
... return
apply (rngl_summation_list_all_permut 0).
...
... return
rewrite rngl_summation_filter_no_dup_list_prodn.
...
(* to see, to do afterwards... *)
(*
  ∀ f,
  ∑ (kl ∈ list_prodn (repeat (seq 1 n) m)), f kl =
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
    ∑ (kl ∈ list_prodn (repeat (seq 1 n) m)),
     if list_eqb Nat.eqb (isort Nat.leb kl) jl then f kl else 0
*)
(*
Compute (
  let n := 3 in
  let m := 2 in
(
 list_prodn (repeat (seq 1 n) m),
 sub_lists_of_seq_1_n n m
)
).
*)
...
(*
Locate "⊂".
Print incl.
sub_lists_of_seq_1_n n m ⊂ list_prodn (repeat (seq 1 n) m
*)
(* yet more generally *)
(*
  ∀ f lla llb,
  llb ⊂ lla
  → ∑ (kl ∈ lla), f kl =
    ∑ (jl ∈ llb),
      ∑ (kl ∈ lla),
       if list_eqb Nat.eqb (isort Nat.leb kl) jl then f kl else 0

-----> ah oui mais non. Faut réfléchir...
*)
...
(*
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
  ∑ (kl ∈ filter (no_dup Nat.eqb) (list_prodn (repeat (seq 1 n) m))),
  (if list_eqb Nat.eqb (isort Nat.leb kl) jl then
     ε kl * ∏ (i = 1, m), mat_el A i kl.(i)
   else 0) *
   det (mat_select_rows jl B)
*)
(*
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
  (∑ (kl ∈ filter (no_dup Nat.eqb) (list_prodn (repeat (seq 1 n) m))),
    if list_eqb Nat.eqb (isort Nat.leb kl) jl then
      ε kl * ∏ (i = 1, m), mat_el A i kl.(i)
    else 0) *
   det (mat_select_rows jl B)
) as x eqn:Hx.
*)
(* at end, must prove that
  (∑ (kl ∈ filter (no_dup Nat.eqb) (list_prodn (repeat (seq 1 n) m))),
    if list_eqb Nat.eqb (isort Nat.leb kl) jl then
      ε kl * ∏ (i = 1, m), mat_el A i kl.(i)
    else 0)
  is equal to det (mat_select_cols jl A
*)
...
 2: {
  intros kl Hkl.
  unfold g1, h1.
  unfold collapse.
...
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite <- mat_transp_el; [ | easy | | flia Hi ]. 2: {
      unfold ff_app.
      apply in_list_prodn_repeat_iff in Hkl.
      destruct Hkl as [Hkl| Hkl]; [ easy | ].
      destruct Hkl as (_ & Hklm & Hkl).
      specialize (Hkl (nth (i - 1) kl 0)).
      assert (H : nth (i - 1) kl 0 ∈ kl). {
        apply nth_In; rewrite Hklm; flia Hi.
      }
      specialize (Hkl H); clear H.
      flia Hkl.
    }
    easy.
  }
  cbn - [ det mat_el ].
  remember (∏ (j = _, _), _) as x; subst x. (* renaming *)
  easy.
}
cbn - [ det mat_el ].
remember (∑ (kl ∈ _), _) as x; subst x. (* renaming *)
...
Print mat_select_rows.
Check det_isort_rows.
Print det''.
...
mat_el A (ff_app kl i) j = mat_el (mat_select_rows kl A) i j.
...
set (f := is_sorted Nat.leb).
erewrite (rngl_summation_list_permut _ Hel). 2: {
  assert (H : ∀ ll,
    permutation (list_eqb Nat.eqb) ll
      (filter f ll ++ filter (λ l, negb (f l)) ll)). {
    now apply permutation_filter_app_filter.
  }
  apply H.
}
rewrite rngl_summation_list_app.
remember (∑ (jl ∈ _), _) as x; subst x. (* renaming *)
erewrite rngl_summation_list_eq_compat. 2: {
  intros jl Hjl.
  replace (isort Nat.leb jl) with jl. 2: {
    apply filter_In in Hjl.
    destruct Hjl as (Hjk, Hsl).
    unfold f in Hsl.
    symmetry.
    apply isort_when_sorted; [ | | easy ]. {
      apply Nat_leb_antisym.
    } {
      apply Nat_leb_trans.
    }
  }
  easy.
}
remember (∑ (jl ∈ _), _) as x; subst x. (* renaming *)
Compute (
  let n := 5 in
  let m := 3 in
filter f (list_prodn (repeat (seq 1 n) m))
).
erewrite rngl_summation_list_eq_compat. 2: {
  intros jl Hjl.
...
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite <- mat_transp_el; [ | easy | | flia Hi ]. 2: {
      unfold ff_app.
      apply filter_In in Hjl.
      destruct Hjl as (Hjk, Hsl).
      apply in_list_prodn_repeat_iff in Hjk.
      destruct Hjk as [Hjk| Hjk]; [ easy | ].
      destruct Hjk as (_ & Hjlm & Hjl).
      specialize (Hjl (nth (i - 1) jl 0)).
      assert (H : nth (i - 1) jl 0 ∈ jl). {
        apply nth_In; rewrite Hjlm; flia Hi.
      }
      specialize (Hjl H); clear H.
      flia Hjl.
    }
Search mat_select_rows.
Print mat_select_rows.
replace (mat_el A⁺ (ff_app jl (i - 1)) i) with
  (mat_el (mat_select_rows jl A⁺) i i). 2: {
  (* bizarre ce "i i" *)
  unfold mat_select_rows.
...
  (* et puis là, c'est la merde *)
  cbn - [ map ].
  rewrite fold_ff_app.
...
    easy.
  }
  cbn - [ det mat_el ].
Search mat_select_rows.
Print mat_select_cols.
Print mat_select_rows.
...
Check det_isort_rows.
Search (_ ⁺)%M.
mat_transp_el:
  ∀ (T : Type) (ro : ring_like_op T) (M : matrix T) (i j : nat),
    is_correct_matrix M = true → i ≠ 0 → j ≠ 0 → mat_el M⁺ i j = mat_el M j i
...
rewrite rngl_add_comm.
rewrite all_0_rngl_summation_list_0. 2: {
  intros kl Hkl.
  apply filter_In in Hkl.
  destruct Hkl as (Hkl, Hsl).
  unfold f in Hsl.
  apply Bool.negb_true_iff in Hsl.
...
  rewrite ε_when_dup; [ | now destruct Hif | now destruct Hif | ]. 2: {
    intros H.
    apply (no_dup_NoDup Nat.eqb_eq) in H.
    congruence.
  }
  rewrite <- rngl_mul_assoc.
  now apply rngl_mul_0_l; destruct Hif; left.
}
rewrite rngl_add_0_l.
remember (∑ (kl ∈ _), _) as x; subst x. (* renaming *)
(**)
Compute (
let n := 4 in
let m := 3 in
(
  filter f (list_prodn (repeat (seq 1 n) m)),
  map revn (rev (sls1n n m)))
).
(* ça pourrait être sympa d'ajouter le filtre "is_sorted Nat.ltb" car,
   dans ce cas, il y aurait les mêmes listes parcourues par le ∑ sauf
   que... ça ne marche pas : la liste restante (not (is_sorted Nat.ltb))
   ne vaut pas 0 *)
...
set (g := is_sorted Nat.ltb).
erewrite (rngl_summation_list_permut _ Heql). 2: {
  assert (H : ∀ ll,
    permutation (list_eqb Nat.eqb) ll
      (filter g ll ++ filter (λ l, negb (g l)) ll)). {
    now apply permutation_filter_app_filter.
  }
  apply H.
}
rewrite rngl_summation_list_app.
rewrite List_filter_filter.
rewrite List_filter_filter.
erewrite filter_ext. 2: {
  intros t.
  replace (g t && f t)%bool with (g t). 2: {
    remember (g t) as gt eqn:Hgt; symmetry in Hgt.
    destruct gt; [ cbn; symmetry | easy ].
    unfold g in Hgt; unfold f.
    assert (H : sorted Nat.ltb t) by easy.
    clear Hgt; rename H into Hgt.
    apply (no_dup_NoDup Nat.eqb_eq).
    apply sorted_lt_NoDup in Hgt; [ easy | | apply Nat_ltb_trans ].
    unfold irreflexive.
    apply Nat.ltb_irrefl.
  }
  easy.
}
erewrite rngl_summation_list_eq_compat. 2: {
  intros t Ht.
  rewrite isort_when_sorted; cycle 1. {
    apply Nat_leb_antisym.
  } {
    apply Nat_leb_trans.
  } {
    apply filter_In in Ht.
    now apply sorted_ltb_leb_incl.
  }
  easy.
}
remember (∑ (jl ∈ _), _) as x; subst x. (* renaming *)
(*
Compute (
let n := 4 in
let m := 3 in
(
  filter g (list_prodn (repeat (seq 1 n) m)),
  map revn (rev (sls1n n m)))
).
*)
rewrite rngl_add_comm.
remember (∑ (kl ∈ _), _) as x eqn:Hx.
assert (H : x = 0%F). {
  subst x.
  (* kl not sorted and no dup *)
(**)
Compute (
let n := 4 in
let m := 3 in
 filter (λ x : list nat, (negb (g x) && f x)%bool)
      (list_prodn (repeat (seq 1 n) m))
).
(**)
(* pas clair que ça vaille 0, ça *)
...
Compute (
let n := 4 in
let k := 3 in
let g1 := λ l : list nat, rev l in
(map g1 (rev (sls1n n k)),
 filter (is_sorted Nat.ltb) (list_prodn (repeat (seq 1 n) k)))
).
...
(*
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
let n := 4 in
let k := 3 in
  let A := mk_mat [[-1;2;-3;4];[4;5;-6;7];[-2;-6;-7;8]]%Z in
let f := λ l, ∏ (j = 1, k), mat_el A j (ff_app l (j - 1)) in
   ∑ (jl ∈ sub_lists_of_seq_1_n n k), f jl =
   ∑ (kl ∈ list_prodn (repeat (seq 1 n) k)),
   if is_sorted Nat.ltb kl then f kl else 0%F
).
*)
...
revert f k.
induction n; intros. {
  cbn.
  destruct k; cbn. {
    rewrite rngl_summation_list_only_one.
    now rewrite rngl_summation_list_only_one.
  }
  rewrite rngl_summation_list_empty; [ | easy ].
  rewrite iter_list_empty; [ easy | ].
  now rewrite iter_list_empty.
}
cbn - [ seq ].
destruct k. {
  cbn.
  rewrite rngl_summation_list_only_one.
  now rewrite rngl_summation_list_only_one.
}
rewrite rev_app_distr.
rewrite map_app.
rewrite rngl_summation_list_app.
remember (∑ (jl ∈ _), _) as x; subst x. (* renaming *)
remember (∑ (jl ∈ map revn (rev (map _ _))), _) as x; subst x. (* renaming *)
...
rewrite rngl_summation_list_map.
erewrite rngl_summation_list_eq_compat. 2: {
  intros jl Hjl.
  cbn - [ "-" ].
  rewrite Nat.sub_succ_l; [ | easy ].
  rewrite Nat.sub_diag.
  easy.
}
cbn - [ list_prodn repeat seq ].
...
erewrite map_ext_in. 2: {
  intros t Ht.
  unfold map_sub_succ.
  cbn - [ "-" ].
  rewrite Nat.sub_succ_l; [ | easy ].
  now rewrite Nat.sub_diag.
}
...
rewrite IHn.
rewrite map_map.
cbn - [ list_prodn repeat seq ].
symmetry.
assert (Hel : equality (list_eqb Nat.eqb)). {
  apply -> equality_list_eqb.
  unfold equality.
  apply Nat.eqb_eq.
}
erewrite (rngl_summation_list_permut _ _ Hel). 2: {
  apply permutation_prodn_succ_app_prodn_filter.
}
rewrite rngl_summation_list_app.
f_equal.
erewrite (rngl_summation_list_permut _ _ Hel). 2: {
  assert (H : ∀ ll,
    permutation (list_eqb Nat.eqb) ll
      (filter (is_sorted Nat.ltb) ll ++
       filter (λ l, negb (is_sorted Nat.ltb l)) ll)). {
    now apply permutation_filter_app_filter.
  }
  apply H.
}
rewrite rngl_summation_list_app.
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  apply filter_In in Hl.
  destruct Hl as (Hl, Hsl).
  now rewrite Hsl.
}
remember (∑ (jl ∈ _), _) as x.
rewrite all_0_rngl_summation_list_0. 2: {
  intros l Hl.
  apply filter_In in Hl.
  destruct Hl as (Hl, Hsl).
  apply Bool.negb_true_iff in Hsl.
  now rewrite Hsl.
}
rewrite rngl_add_0_r.
subst x.
remember (∑ (jl ∈ map (λ l, _) _), _) as x; subst x. (* renaming *)
rewrite List_filter_filter.
remember (filter (λ l, _) _) as x; subst x. (* renaming *)
Compute (
let n := 4 in
let m := 2 in
  filter (λ l : list nat, (is_sorted Nat.ltb l && member Nat.eqb (S n) l)%bool)
      (list_prodn (repeat (seq 1 (S n)) (S m))) =
  map (λ l : list nat, map S (l ++ [n])) (sub_lists_of_seq_1_n n m)
).
...
erewrite (rngl_summation_list_permut _ (list_eqb Nat.eqb_eq)).
Search permutation.
rewrite rngl_summation_list_change_var.

replace (list_prodn (repeat (seq 1 (S n)) (S m))) with
  (list_prodn (repeat (seq 1 n) (S m)) ++
...
remember (list_prodn (repeat (seq 1 (S n)) (S m))) as ll eqn:Hll.
Check List_rank.
remember
  (partition
     (λ l,
      match List_rank (Nat.eqb (S n)) l with
      | Some i => i <? m
      | None => false
      end) ll) as x eqn:Hx.
Compute (
let m := 2 in
let n := 3 in
   partition (member Nat.eqb (S n))
     (list_prodn (repeat (seq 1 (S n)) (S m)))
).
Theorem glop : ∀ m n p1 p2,
  partition (member Nat.eqb (S n))
    (list_prodn (repeat (seq 1 (S n)) m)) = (p1, p2)
  → p2 = list_prodn (repeat (seq 1 n) m).
...
(*
Theorem partition_permutation : ∀ A (eqb : A → _) p p1 p2 f,
  partition f p = (p1, p2)
  → permutation eqb p (p1 ++ p2).
*)
...
   partition
      match List_rank (Nat.eqb (S n)) l with
      | Some i => i <? m
      | None => false
      end) (list_prodn (repeat (seq 1 (S n)) (S m)))
).
(* mouais, bon, c'est pas vraiment ça ;
   mais l'idée, c'est de séparer les listes qui n'ont pas de S n, ou qui
   ont un S n à la fin : ce sont les seules qui ont une chance d'être
   triées et donc de ne pas renvoyer 0 *)
...
Compute (
let m := 2 in
let n := 3 in
list_prodn (repeat (seq 1 n) (S m))).
...
tous ceux qui contiennent des S n, on les filtre
de [1; 1; 1] à [3; 3; 3]
de [1; 1; 1] à [4; 4; 4]
...
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
let m := 3 in
let n := 4 in
  let A := mk_mat [[-1;2;-3;4];[4;5;-6;7];[-2;-6;-7;-8]]%Z in
let f := λ l, ∏ (j = 1, m), mat_el A j (ff_app l (j - 1)) in
  ∑ (jl ∈ map (map S) (sub_lists_of_seq_1_n n m)), f jl =
  ∑ (kl ∈ list_prodn (repeat (seq 1 n) m)),
  (if is_sorted Nat.ltb kl then f kl else 0)
).
...
symmetry.
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
  replace (ε kl * f kl)%F with
      (if no_dup Nat.eqb kl then ε kl * f kl else 0)%F. 2: {
    rewrite if_bool_if_dec.
    destruct (bool_dec (no_dup Nat.eqb kl)) as [Hdkl| Hdkl]; [ easy | ].
    rewrite ε_when_dup; [ | now destruct Hif | now destruct Hif | ]. 2: {
      intros H.
      apply (no_dup_NoDup Nat.eqb_eq) in H.
      congruence.
    }
    now symmetry; apply rngl_mul_0_l; destruct Hif; left.
  }
  easy.
}
cbn.
Search (∑ (_ ∈ _), _ = ∑ (_ ∈ _), _).
rewrite rngl_summation_list_map.
Print sub_lists_of_seq_1_n.
...
... retour au théorème cauchy_binet_formula
rewrite (rngl_summation_sub_lists_prodn Hif).
...
(*
Compute (
let m := 3 in
let n := 4 in
sub_lists_of_seq_1_n n m
).
Compute (
let m := 3 in
let n := 4 in
list_prodn (repeat (seq 1 n) m)
).
*)
(* I must prove that
     det (mat_select_rows kl B) = ε(kl) det (mat_select_rows jl B)
   where jl is ordered kl
*)
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
  let m := 2 in
  let n := 3 in
  let A := mk_mat [[-1;2;-3];[4;5;-6]]%Z in
  let B := mk_mat [[7;8];[9;10];[11;12]]%Z in
  ∑ (i ∈ list_prodn (repeat (seq 1 n) m)),
(*
  ∏ (i0 = 1, m), mat_el A i0 (ff_app i (i0 - 1)) *
  ε i * det (mat_select_rows (isort Nat.leb i) B) =
*)
(*
  (if is_sorted Nat.leb i then
  det (mat_select_cols i A) else 0%Z) *
  det (mat_select_rows i B) =
*)
(*
  det (mat_select_cols i A) *
  (if is_sorted Nat.leb i then
   det (mat_select_rows i B) else 0%Z) =
*)
(*
  (if is_sorted Nat.leb i then
  det (mat_select_cols i A) else 0%Z) *
  (if is_sorted Nat.leb i then
   det (mat_select_rows i B) else 0%Z) =
*)
(*
  (if is_sorted Nat.leb i then
     det (mat_select_cols i A) * det (mat_select_rows i B)
   else 0) =
*)
(* non
  det (mat_select_cols (isort Nat.leb i) A) *
   det (mat_select_rows (isort Nat.leb i) B) =
*)
  ∑ (jl ∈ map (map S) (sub_lists_of_seq_1_n n m)),
  det (mat_select_cols jl A) * det (mat_select_rows jl B)
).
(*
 map (map S) (sub_lists_of_seq_1_n n m)).
list_prodn (repeat (seq 1 n) m)).
let i := [3;3] in
 det (mat_select_rows i B)).
  ∑ (i ∈ list_prodn (repeat (seq 1 n) m)),
  ∏ (i0 = 1, m), mat_el A i0 (ff_app i (i0 - 1)) * det (mat_select_rows i B) =
  ∑ (jl ∈ map (map S) (sub_lists_of_seq_1_n n m)),
  det (mat_select_cols jl A) * det (mat_select_rows jl B)
).
*)
...
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
(**)
  replace (det (mat_select_rows kl B)) with
    (ε kl * det (mat_select_rows (isort Nat.leb kl) B))%F. 2: {
...
    symmetry; apply det_isort_rows.
...
  }
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
  replace (ε kl * ∏ (i = 1, m), mat_el A i (ff_app kl (i - 1)))%F with
    (det (mat_select_cols (isort Nat.eqb kl) A)). 2: {
...
  }
  easy.
}
cbn - [ det ].
...
  replace (∏ (i = 1, m), mat_el A i (ff_app k (i - 1))) with
    (det (mat_select_cols k A)). 2: {
    rewrite det_is_det'; try now destruct Hif. 2: {
      apply in_list_prodn_repeat_iff in Hk.
      destruct Hk as (_ & Hkm & Hk).
      apply mat_select_cols_is_square; [ easy | congruence | ].
      now rewrite Hac.
    }
    rewrite det'_is_det''; try now destruct Hif. 2: {
      unfold mat_select_cols.
      rewrite mat_transp_nrows.
      rewrite mat_select_rows_ncols. 2: {
        apply in_list_prodn_repeat_iff in Hk.
        destruct Hk as (_ & Hkm & Hk).
        now intros H; subst k; symmetry in Hkm.
      }
      rewrite mat_transp_ncols.
      rewrite Hac, Har.
      now apply Nat.eqb_neq in Hnz; rewrite Hnz.
    }
    unfold det''.
    rewrite mat_select_cols_nrows; [ | | now rewrite Hac ]. 2: {
      apply in_list_prodn_repeat_iff in Hk.
      destruct Hk as (_ & Hkm & Hk).
      now intros H; subst k; symmetry in Hkm.
    }
    rewrite Har.
...
*)

(*
End a.
Require Import RnglAlg.Zrl.
Require Import ZArith.
Open Scope Z_scope.
Arguments mat_select_cols {T}%type {ro} jl%list.
Compute (let A := mk_mat [[3;4;1];[0;6;7];[1;3;1]] in let jl := [0;2]%nat in mat_select_rows jl A).
Compute (let A := mk_mat [[3;4;1];[0;6;7];[1;3;1]] in let B := mk_mat [[0;6;7];[1;3;1];[3;2;1]] in let m := mat_nrows A in let n := mat_ncols A in (det (A * B), ∑ (jl ∈ sub_lists_of_seq_1_n n m), det (mat_select_cols jl A) * det (mat_select_rows jl B), det A * det B)).
Compute (let B := mk_mat [[3;4];[2;6];[1;3]] in let A := mk_mat [[1;6;7];[1;3;1]] in let m := mat_nrows A in let n := mat_ncols A in (det (A * B), ∑ (jl ∈ sub_lists_of_seq_1_n n m), det (mat_select_cols jl A) * det (mat_select_rows jl B), det A * det B, m, n, sub_lists_of_seq_1_n n m)).
Compute (sub_lists_of_seq_1_n 3 3).
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
  cbn - [ "/" ff_app ].
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
