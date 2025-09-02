(* signatures *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith Init.Nat.
Import List.ListNotations.

Require Import RingLike.Core.
Require Import RingLike.PermutationFun.
Require Import RingLike.IterMul.

Require Import Misc.
Require Import SortingFun SortRank.
Require Import PermutSeq.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hon : rngl_has_1 T = true).

(* version of signature (parity) of a list of nat *)

Fixpoint ε_aux i l :=
  match l with
  | [] => 1%L
  | j :: l' =>
      match i ?= j with
      | Lt => ε_aux i l'
      | Eq => 0%L
      | Gt => (- ε_aux i l')%L
      end
  end.

Fixpoint ε (l : list nat) :=
  match l with
  | [] => 1%L
  | i :: q => (ε_aux i q * ε q)%L
  end.

(* for testing with a elementary ring-like *)

Inductive test_rl := Minus_one | Zero | One.

Definition test_ring_like_op :=
  let test_opp a :=
    match a with
    | Minus_one => One
    | Zero => Zero
    | One => Minus_one
    end
  in
  {| rngl_zero := Zero;
     rngl_add _ _ := Zero;
     rngl_mul a b :=
       match a with
       | Zero => Zero
       | Minus_one => test_opp b
       | One => b
       end;
     rngl_opt_one := Some One;
     rngl_opt_opp_or_psub := Some (inl test_opp);
     rngl_opt_inv_or_pdiv := None;
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := None;
     rngl_opt_leb := None |}.

(* *)

Theorem minus_one_pow_mul_comm :
  rngl_has_opp T = true →
  ∀ i x, (minus_one_pow i * x = x * minus_one_pow i)%L.
Proof.
intros Hop *.
unfold minus_one_pow.
remember (i mod 2) as k eqn:Hk; symmetry in Hk.
destruct k. {
  now rewrite (rngl_mul_1_r Hon), (rngl_mul_1_l Hon).
}
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_opp_r Hop).
now rewrite rngl_mul_1_l, rngl_mul_1_r.
Qed.

Theorem ε_app_cons :
  rngl_has_opp T = true →
  ∀ {n} la lb,
  (∀ a, a ∈ la ++ lb → a < n)
  → ε (la ++ n :: lb) = (minus_one_pow (length lb) * ε (la ++ lb))%L.
Proof.
intros Hop * Hab.
revert n lb Hab.
induction la as [| a]; intros; cbn. {
  f_equal; cbn in Hab.
  induction lb as [| b]; [ easy | cbn ].
  specialize (Hab b (or_introl eq_refl)) as H1.
  remember (n ?= b) as c eqn:Hc; symmetry in Hc.
  destruct c. {
    now apply Nat.compare_eq_iff in Hc; subst b; apply Nat.lt_irrefl in H1.
  } {
    apply Nat.compare_lt_iff in Hc; flia H1 Hc.
  }
  rewrite (minus_one_pow_succ Hop).
  f_equal.
  apply IHlb.
  intros a Ha.
  now apply Hab; right.
}
rewrite IHla. 2: {
  intros b Hb.
  now apply Hab; right.
}
do 2 rewrite rngl_mul_assoc.
f_equal.
rewrite (minus_one_pow_mul_comm Hop); f_equal.
clear IHla.
revert a lb Hab.
induction la as [| a']; intros; cbn. {
  specialize (Hab a (or_introl eq_refl)).
  apply Nat.compare_lt_iff in Hab.
  now rewrite Hab.
}
remember (a ?= a') as c eqn:Hc; symmetry in Hc.
destruct c; [ easy | | ]. {
  apply IHla.
  intros b Hb.
  apply Hab.
  cbn in Hb |-*.
  destruct Hb; [ now left | now right; right ].
} {
  f_equal.
  apply IHla.
  intros b Hb.
  apply Hab.
  cbn in Hb |-*.
  destruct Hb; [ now left | now right; right ].
}
Qed.

Theorem ε_aux_dup :
  rngl_has_opp T = true →
  ∀ i l1 l2, ε_aux i (l1 ++ i :: l2) = 0%L.
Proof.
intros Hop *.
revert i l2.
induction l1 as [| j]; intros; cbn; [ now rewrite Nat.compare_refl | ].
destruct (i ?= j); [ easy | apply IHl1 | ].
rewrite IHl1.
apply (rngl_opp_0 Hop).
Qed.

Theorem minus_one_pow_mul_same :
  rngl_has_opp T = true →
  ∀ i, (minus_one_pow i * minus_one_pow i = 1)%L.
Proof.
intros Hop *.
unfold minus_one_pow.
destruct (i mod 2); [ apply (rngl_mul_1_l Hon) | ].
now apply rngl_squ_opp_1.
Qed.

(* ε (σ₁ ° σ₂) = ε σ₁ * ε σ₂ *)

Theorem butn_permut_seq_with_len : ∀ n i l,
  permut_seq_with_len (S n) l
  → n = List.nth i l 0
  → i < length l
  → permut_seq_with_len n (List_butn i l).
Proof.
intros * Hp Hni Hil.
split. {
  apply permut_seq_iff.
  split. {
    intros j Hj.
    rewrite List_length_butn.
    destruct Hp as (Hp, Hl).
    apply Nat.ltb_lt in Hil; rewrite Hil.
    apply Nat.ltb_lt in Hil.
    rewrite Hl, Nat_sub_succ_1.
    apply permut_seq_iff in Hp.
    destruct Hp as (Hpl, Hpi).
    specialize (Hpl j) as Hjl.
    assert (H : j ∈ l) by now apply List_in_butn in Hj.
    specialize (Hjl H); clear H.
    rewrite Hl in Hjl.
    destruct (Nat.eq_dec j n) as [H| H]; [ | flia H Hjl ].
    subst j; clear Hjl; exfalso.
    assert (Hnni : n ≠ i). {
      intros H; move H at top; subst i.
      apply (List.In_nth _ _ 0) in Hj.
      rewrite List_length_butn, Hl in Hj.
      replace (n <? S n) with true in Hj by now symmetry; apply Nat.ltb_lt.
      rewrite Nat_sub_succ_1 in Hj.
      destruct Hj as (j & Hjn & Hnj); symmetry in Hnj.
      rewrite List_nth_butn in Hnj.
      apply Nat.leb_gt in Hjn.
      rewrite Hjn, Nat.add_0_r in Hnj.
      apply Nat.leb_gt in Hjn.
      specialize (NoDup_nat _ Hpi j n) as H2.
      assert (H : j < length l) by now rewrite Hl; flia Hjn.
      specialize (H2 H Hil); clear H.
      assert (H : List.nth j l 0 = List.nth n l 0) by now rewrite <- Hni.
      specialize (H2 H).
      now rewrite H2 in Hjn; apply Nat.lt_irrefl in Hjn.
    }
    unfold List_butn in Hj.
    apply List.in_app_or in Hj.
    destruct Hj as [Hini| Hini]. {
      apply (List.In_nth _ _ 0) in Hini.
      destruct Hini as (j & Hjl & Hjn).
      rewrite List.length_firstn, min_l in Hjl; [ | flia Hil ].
      specialize (NoDup_nat _ Hpi i j Hil) as H2.
      assert (H : j < List.length l) by flia Hjl Hil.
      specialize (H2 H); clear H.
      rewrite <- Hni in H2.
      rewrite List_nth_firstn in Hjn; [ | easy ].
      symmetry in Hjn.
      specialize (H2 Hjn).
      rewrite <- H2 in Hjl.
      now apply Nat.lt_irrefl in Hjl.
    } {
      apply (List.In_nth _ _ 0) in Hini.
      destruct Hini as (j & Hjl & Hjn).
      rewrite List.length_skipn in Hjl.
      rewrite List_nth_skipn in Hjn.
      specialize (NoDup_nat _ Hpi i (j + S i) Hil) as H2.
      assert (H : j + S i < List.length l) by flia Hjl.
      specialize (H2 H); clear H.
      rewrite <- Hni in H2.
      rewrite Hjn in H2.
      specialize (H2 eq_refl).
      flia H2.
    }
  } {
    apply nat_NoDup.
    rewrite List_length_butn.
    apply Nat.ltb_lt in Hil; rewrite Hil.
    apply Nat.ltb_lt in Hil.
    destruct Hp as (Hpp, Hpl).
    rewrite Hpl, Nat_sub_succ_1.
    intros j k Hj Hk Hjk.
    apply permut_seq_iff in Hpp.
    destruct Hpp as (Hp, Hpi).
    do 2 rewrite List_nth_butn in Hjk.
    apply (NoDup_nat _ Hpi) in Hjk; cycle 1. {
      rewrite Hpl, <- Nat.add_1_r.
      apply Nat.add_lt_le_mono; [ easy | ].
      apply Nat_b2n_upper_bound.
    } {
      rewrite Hpl, <- Nat.add_1_r.
      apply Nat.add_lt_le_mono; [ easy | ].
      apply Nat_b2n_upper_bound.
    }
    unfold Nat.b2n in Hjk.
    do 2 rewrite if_leb_le_dec in Hjk.
    destruct (le_dec i j) as [Hij| Hij].  {
      destruct (le_dec i k) as [Hik| Hik]; [ flia Hjk | ].
      exfalso; flia Hik Hij Hjk.
    } {
      destruct (le_dec i k) as [Hik| Hik]; [ | flia Hjk ].
      exfalso; flia Hik Hij Hjk.
    }
  }
} {
  rewrite List_length_butn.
  apply Nat.ltb_lt in Hil.
  destruct Hp as (Hpp, Hpl).
  now rewrite Hil, Hpl, Nat_sub_succ_1.
}
Qed.

Theorem permut_without_highest : ∀ {n l},
  permut_seq_with_len (S n) l
  → ∃ i,
    i < List.length l ∧ List.nth i l 0 = n ∧
    permut_seq_with_len n (List_butn i l).
Proof.
intros * Hl.
exists (List.nth n (isort_rank Nat.leb l) 0).
split. {
  rewrite <- (isort_rank_length Nat.leb).
  destruct Hl as (Hp, Hl).
  specialize (isort_rank_permut_seq_with_len Nat.leb _ Hl) as Hil.
  destruct Hil as (Hil, Hil').
  apply permut_seq_iff in Hil.
  apply Hil, List.nth_In.
  rewrite isort_rank_length.
  now rewrite Hl.
}
split. {
  destruct Hl as (Hp, Hl).
  apply permut_permut_isort; [ easy | now rewrite Hl ].
}
apply butn_permut_seq_with_len; [ easy | | ]. {
  destruct Hl as (Hp, Hl).
  rewrite permut_permut_isort; [ easy | easy | now rewrite Hl ].
} {
  specialize (isort_rank_permut_seq Nat.leb l) as H1.
  destruct Hl as (H2, H3).
  apply permut_seq_iff in H1.
  destruct H1 as (H4, H5).
  rewrite isort_rank_length in H4.
  apply H4, List.nth_In.
  now rewrite isort_rank_length, H3.
}
Qed.

Theorem fold_comp_list :
   ∀ la lb, List.map (λ i, List.nth i la 0) lb = la ° lb.
Proof. easy. Qed.

Theorem fold_ε_cons : ∀ i q, (ε_aux i q * ε q)%L = ε (i :: q).
Proof. easy. Qed.

Theorem ε_aux_in :
  rngl_has_opp T = true →
  ∀ i la, ε_aux i la ∈ [-1; 0; 1]%L.
Proof.
intros Hop *.
induction la as [| a]; cbn; [ now right; right; left | ].
destruct (i ?= a); [ now right; left | | ]. {
  destruct IHla as [Ha| Ha]; [ now left | ].
  destruct Ha as [Ha| Ha]; [ now right; left | ].
  destruct Ha as [Ha| Ha]; [ now right; right; left | easy ].
} {
  destruct IHla as [Ha| Ha]. {
    now right; right; left; rewrite <- Ha, (rngl_opp_involutive Hop).
  }
  destruct Ha as [Ha| Ha]. {
    now right; left; rewrite <- Ha, (rngl_opp_0 Hop).
  }
  destruct Ha as [Ha| Ha]; [ now left; rewrite <- Ha | easy ].
}
Qed.

Theorem ε_in :
  rngl_has_opp T = true →
  ∀ la, ε la ∈ [-1; 0; 1]%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_psub_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
induction la as [| a]; cbn; [ now right; right; left | ].
specialize (ε_aux_in Hop a la) as H1.
destruct IHla as [H2| [H2| [H2| ]]]; [ | | | easy ]; rewrite <- H2. {
  destruct H1 as [H1| [H1| [H1| ]]]; [ | | | easy ]; rewrite <- H1. {
    right; right; left.
    symmetry; apply (rngl_squ_opp_1 Hon Hop).
  } {
    right; left.
    symmetry; apply (rngl_mul_0_l Hos).
  } {
    left.
    symmetry; apply (rngl_mul_1_l Hon).
  }
} {
  right; left.
  symmetry; apply (rngl_mul_0_r Hos).
} {
  now rewrite rngl_mul_1_r.
}
Qed.

Theorem ε_aux_mul_comm :
  rngl_has_opp T = true →
  ∀ i la a, (ε_aux i la * a = a * ε_aux i la)%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_psub_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
specialize (ε_aux_in Hop i la) as H1.
destruct H1 as [H1| H1]. {
  rewrite <- H1.
  rewrite (rngl_mul_opp_l Hop), (rngl_mul_1_l Hon).
  rewrite (rngl_mul_opp_r Hop), (rngl_mul_1_r Hon).
  easy.
}
destruct H1 as [H1| H1]. {
  rewrite <- H1.
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  easy.
}
destruct H1 as [H1| H1]; [ | easy ].
rewrite <- H1.
now rewrite rngl_mul_1_l, rngl_mul_1_r.
Qed.

Theorem ε_mul_comm :
  rngl_has_opp T = true →
  ∀ la a, (ε la * a = a * ε la)%L.
Proof.
intros Hop *.
induction la as [| b]. {
  now cbn; rewrite rngl_mul_1_l, rngl_mul_1_r.
}
cbn.
rewrite <- rngl_mul_assoc.
do 2 rewrite (ε_aux_mul_comm Hop).
rewrite IHla.
symmetry; apply rngl_mul_assoc.
Qed.

Theorem ε_aux_app_lt_lt :
  ∀ a b c la,
  a < c
  → b < c
  → ε_aux c (la ++ [b]) = ε_aux c (la ++ [a]).
Proof.
intros * Hab Hbb.
induction la as [| b'']; cbn. {
  remember (c ?= b) as bb2 eqn:Hbb2; symmetry in Hbb2.
  destruct bb2. {
    apply Nat.compare_eq_iff in Hbb2; subst c.
    now apply Nat.lt_irrefl in Hbb.
  } {
    apply Nat.compare_lt_iff in Hbb2; flia Hbb Hbb2.
  }
  remember (c ?= a) as ba eqn:Hba; symmetry in Hba.
  destruct ba; [ | | easy ]. {
    apply Nat.compare_eq_iff in Hba; subst c.
    now apply Nat.lt_irrefl in Hab.
  } {
    apply Nat.compare_lt_iff in Hba; flia Hab Hba.
  }
}
now rewrite IHla.
Qed.

Theorem ε_aux_app_lt_gt :
  rngl_has_opp T = true →
  ∀ a b c la,
  a < c
  → c < b
  → ε_aux c (la ++ [b]) = (- ε_aux c (la ++ [a]))%L.
Proof.
intros Hop * Hac Hcb.
induction la as [| d]; cbn. {
  remember (c ?= b) as cb2 eqn:Hcb2; symmetry in Hcb2.
  destruct cb2. {
    apply Nat.compare_eq_iff in Hcb2; subst c.
    now apply Nat.lt_irrefl in Hcb.
  } {
    remember (c ?= a) as ca eqn:Hca; symmetry in Hca.
    destruct ca; [ | | now rewrite (rngl_opp_involutive Hop) ]. {
      apply Nat.compare_eq_iff in Hca; subst c.
      now apply Nat.lt_irrefl in Hac.
    } {
      apply Nat.compare_lt_iff in Hca; flia Hac Hca.
    }
  }
  apply Nat.compare_gt_iff in Hcb2; flia Hcb Hcb2.
}
remember (c ?= d) as cd eqn:Hcd; symmetry in Hcd.
destruct cd; [ | easy | now rewrite IHla ].
symmetry; apply (rngl_opp_0 Hop).
Qed.

Theorem ε_aux_app_gt_gt :
  ∀ a b c la,
  a < b
  → a < c
  → ε_aux a (la ++ [b]) = ε_aux a (la ++ [c]).
Proof.
intros * Hab2 Hbb.
symmetry.
induction la as [| b'']; cbn. {
  remember (a ?= c) as bb2 eqn:Hbb2; symmetry in Hbb2.
  destruct bb2. {
    apply Nat.compare_eq_iff in Hbb2; subst a.
    now apply Nat.lt_irrefl in Hbb.
  } {
    remember (a ?= b) as ba eqn:Hba; symmetry in Hba.
    destruct ba; [ | easy | ]. {
      apply Nat.compare_eq_iff in Hba; subst a.
      now apply Nat.lt_irrefl in Hab2.
    } {
      apply Nat.compare_gt_iff in Hba; flia Hab2 Hba.
    }
  } {
    apply Nat.compare_gt_iff in Hbb2; flia Hbb Hbb2.
  }
}
now rewrite IHla.
Qed.

Theorem ε_aux_mul_ε_app_from_ε_cons_app_lt :
  rngl_has_opp T = true →
  ∀ a b la,
  a < b
  → (ε_aux a la * ε (la ++ [b]))%L = (- ε (b :: la ++ [a]))%L.
Proof.
intros Hop * Hab.
specialize (proj2 rngl_has_opp_or_psub_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
revert a b Hab.
induction la as [| b']; intros; cbn. {
  remember (b ?= a) as d eqn:Hd; symmetry in Hd.
  destruct d. {
    apply Nat.compare_eq_iff in Hd; subst b.
    now apply Nat.lt_irrefl in Hab.
  } {
    apply Nat.compare_lt_iff in Hd; flia Hab Hd.
  }
  clear Hd.
  rewrite <- (rngl_mul_opp_l Hop).
  now rewrite (rngl_opp_involutive Hop).
}
remember (a ?= b') as ab2 eqn:Hab2; symmetry in Hab2.
remember (b ?= b') as bb eqn:Hbb; symmetry in Hbb.
destruct ab2. {
  apply Nat.compare_eq_iff in Hab2; subst b'.
  rewrite (rngl_mul_0_l Hos).
  destruct bb. {
    rewrite (rngl_mul_0_l Hos).
    symmetry; apply (rngl_opp_0 Hop).
  } {
    apply Nat.compare_lt_iff in Hbb; flia Hab Hbb.
  }
  rewrite (ε_aux_dup Hop a la []).
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  symmetry; apply (rngl_opp_0 Hop).
} {
  apply Nat.compare_lt_iff in Hab2.
  destruct bb. {
    apply Nat.compare_eq_iff in Hbb; subst b'.
    rewrite (ε_aux_dup Hop b la []).
    do 2 rewrite (rngl_mul_0_l Hos).
    rewrite (rngl_mul_0_r Hos).
    symmetry; apply (rngl_opp_0 Hop).
  } {
    apply Nat.compare_lt_iff in Hbb.
    rewrite (ε_aux_mul_comm Hop b').
    rewrite rngl_mul_assoc.
    rewrite (IHla _ _ Hab); cbn.
    rewrite (rngl_mul_opp_l Hop).
    rewrite -> rngl_mul_assoc.
    f_equal.
    do 2 rewrite <- rngl_mul_assoc.
    f_equal.
    rewrite (ε_aux_mul_comm Hop).
    f_equal.
    now apply ε_aux_app_lt_lt.
  } {
    apply Nat.compare_gt_iff in Hbb.
    rewrite (ε_aux_mul_comm Hop b').
    rewrite rngl_mul_assoc.
    rewrite (IHla _ _ Hab); cbn.
    rewrite (rngl_mul_opp_l Hop).
    rewrite -> rngl_mul_assoc.
    f_equal.
    do 2 rewrite <- rngl_mul_assoc.
    rewrite (rngl_mul_opp_l Hop).
    rewrite <- (rngl_mul_opp_r Hop).
    f_equal.
    rewrite <- (rngl_mul_opp_l Hop).
    rewrite <- (ε_aux_mul_comm Hop).
    f_equal.
    now apply (ε_aux_app_lt_gt Hop).
  }
}
apply Nat.compare_gt_iff in Hab2.
destruct bb. {
  apply Nat.compare_eq_iff in Hbb; subst b'.
  rewrite (ε_aux_dup Hop b la []).
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_0_r Hos).
  symmetry; apply (rngl_opp_0 Hop).
} {
  apply Nat.compare_lt_iff in Hbb.
  flia Hab Hab2 Hbb.
}
apply Nat.compare_gt_iff in Hbb.
rewrite (rngl_mul_opp_l Hop).
f_equal.
rewrite (ε_aux_mul_comm Hop b').
rewrite rngl_mul_assoc.
rewrite (IHla _ _ Hab).
do 2 rewrite (rngl_mul_opp_l Hop).
cbn.
rewrite <- rngl_mul_assoc.
f_equal; f_equal.
rewrite <- (ε_aux_mul_comm Hop).
f_equal.
now apply ε_aux_app_gt_gt.
Qed.

Theorem ε_aux_mul_ε_app_from_ε_cons_app_gt :
  rngl_has_opp T = true
  → ∀ a b la,
  b < a
  → (ε_aux a la * ε (la ++ [b]))%L = ε (b :: la ++ [a]).
Proof.
intros Hop * Hc.
specialize (proj2 rngl_has_opp_or_psub_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
revert a b Hc.
induction la as [| b']; intros; cbn. {
  remember (b ?= a) as d eqn:Hd; symmetry in Hd.
  destruct d; [ | easy | ]. {
    apply Nat.compare_eq_iff in Hd; subst b.
    now apply Nat.lt_irrefl in Hc.
  }
  apply Nat.compare_gt_iff in Hd; flia Hc Hd.
}
remember (a ?= b') as ab eqn:Hab; symmetry in Hab.
remember (b ?= b') as bb eqn:Hbb; symmetry in Hbb.
destruct ab. {
  apply Nat.compare_eq_iff in Hab; subst b'.
  rewrite (rngl_mul_0_l Hos).
  destruct bb. {
    now rewrite (rngl_mul_0_l Hos).
  } {
    rewrite (ε_aux_dup Hop a la []).
    rewrite (rngl_mul_0_l Hos).
    now rewrite (rngl_mul_0_r Hos).
  } {
    apply Nat.compare_gt_iff in Hbb; flia Hc Hbb.
  }
} {
  apply Nat.compare_lt_iff in Hab.
  destruct bb. {
    apply Nat.compare_eq_iff in Hbb; subst b'; flia Hc Hab.
  } {
    apply Nat.compare_lt_iff in Hbb.
    rewrite (ε_aux_mul_comm Hop b').
    rewrite rngl_mul_assoc.
    rewrite (IHla _ _ Hc); cbn.
    rewrite <- rngl_mul_assoc.
    f_equal.
    rewrite <- (ε_aux_mul_comm Hop).
    f_equal.
    clear IHla Hc.
    induction la as [| b'']; cbn. {
      remember (b' ?= b) as bb2 eqn:Hbb2; symmetry in Hbb2.
      destruct bb2. {
        apply Nat.compare_eq_iff in Hbb2; subst b'.
        now apply Nat.lt_irrefl in Hbb.
      } {
        apply Nat.compare_lt_iff in Hbb2; flia Hbb Hbb2.
      }
      remember (b' ?= a) as ba eqn:Hba; symmetry in Hba.
      destruct ba; [ | | easy ]. {
        apply Nat.compare_eq_iff in Hba; subst b'.
        now apply Nat.lt_irrefl in Hab.
      } {
        apply Nat.compare_lt_iff in Hba; flia Hab Hba.
      }
    }
    now rewrite IHla.
  } {
    apply Nat.compare_gt_iff in Hbb.
    flia Hc Hab Hbb.
  }
}
apply Nat.compare_gt_iff in Hab.
destruct bb. {
  apply Nat.compare_eq_iff in Hbb; subst b'.
  rewrite (ε_aux_dup Hop b la []).
  do 2 rewrite (rngl_mul_0_l Hos).
  now rewrite (rngl_mul_0_r Hos).
} {
  apply Nat.compare_lt_iff in Hbb.
  rewrite (rngl_mul_opp_l Hop).
  rewrite (ε_aux_mul_comm Hop b').
  rewrite rngl_mul_assoc.
  rewrite (IHla _ _ Hc); cbn.
  rewrite <- (rngl_mul_opp_r Hop).
  rewrite <- rngl_mul_assoc.
  f_equal.
  rewrite (ε_aux_mul_comm Hop).
  f_equal.
  symmetry.
  now apply ε_aux_app_lt_gt.
}
apply Nat.compare_gt_iff in Hbb.
do 2 rewrite (rngl_mul_opp_l Hop).
f_equal.
rewrite (ε_aux_mul_comm Hop b').
rewrite rngl_mul_assoc.
rewrite (IHla _ _ Hc).
cbn.
rewrite <- rngl_mul_assoc.
f_equal.
rewrite <- (ε_aux_mul_comm Hop); cbn.
f_equal.
now apply ε_aux_app_gt_gt.
Qed.

Theorem ε_cons_from_ε_app :
  rngl_has_opp T = true →
  ∀ a la, ε (a :: la) = (minus_one_pow (List.length la) * ε (la ++ [a]))%L.
Proof.
intros Hop *; cbn.
specialize (proj2 rngl_has_opp_or_psub_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
revert a.
induction la as [| b]; intros; [ symmetry; apply (rngl_mul_1_l Hon) | cbn ].
remember (a ?= b) as c eqn:Hc; symmetry in Hc.
destruct c. {
  apply Nat.compare_eq_iff in Hc; subst b.
  rewrite (rngl_mul_0_l Hos).
  rewrite (ε_aux_dup Hop a la []).
  rewrite (rngl_mul_0_l Hos).
  now rewrite (rngl_mul_0_r Hos).
} {
  apply Nat.compare_lt_iff in Hc.
  rewrite IHla.
  rewrite rngl_mul_assoc.
  rewrite <- (minus_one_pow_mul_comm Hop).
  rewrite (minus_one_pow_succ Hop).
  rewrite (rngl_mul_opp_l Hop).
  rewrite <- (rngl_mul_opp_r Hop).
  rewrite <- rngl_mul_assoc; f_equal.
  rewrite fold_ε_cons.
  now apply (ε_aux_mul_ε_app_from_ε_cons_app_lt Hop).
} {
  apply Nat.compare_gt_iff in Hc.
  rewrite IHla.
  rewrite rngl_mul_assoc.
  rewrite <- (minus_one_pow_mul_comm Hop).
  rewrite (minus_one_pow_succ Hop).
  rewrite (rngl_mul_opp_l Hop).
  rewrite <- (rngl_mul_opp_r Hop).
  rewrite <- rngl_mul_assoc; f_equal.
  rewrite fold_ε_cons.
  clear IHla.
  rewrite (rngl_mul_opp_l Hop).
  f_equal.
  now apply (ε_aux_mul_ε_app_from_ε_cons_app_gt Hop).
}
Qed.

Theorem ε_aux_app_cons_ε_aux_app_app :
  rngl_has_opp T = true →
  ∀ a b la lb,
  ε_aux a (la ++ b :: lb) = ε_aux a (la ++ lb ++ [b]).
Proof.
intros Hop *.
induction la as [| a']; cbn; [ | now rewrite IHla ].
remember (a ?= b) as aa eqn:Haa; symmetry in Haa.
destruct aa. {
  apply Nat.compare_eq_iff in Haa; subst a.
  now rewrite (ε_aux_dup Hop).
} {
  induction lb as [| b']; cbn; [ now rewrite Haa | ].
  now rewrite IHlb.
} {
  induction lb as [| b']; cbn; [ now rewrite Haa | ].
  rewrite IHlb.
  remember (a ?= b') as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy | easy ].
  apply (rngl_opp_0 Hop).
}
Qed.

Theorem ε_app_cons2 :
  rngl_has_opp T = true →
  ∀ la lb a,
  ε (la ++ a :: lb) =
    (minus_one_pow (List.length lb) * ε (la ++ lb ++ [a]))%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_psub_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
revert a lb.
induction la as [| a']; intros; cbn. {
  rewrite fold_ε_cons.
  apply (ε_cons_from_ε_app Hop).
}
rewrite IHla.
rewrite rngl_mul_assoc.
rewrite <- (minus_one_pow_mul_comm Hop).
rewrite <- rngl_mul_assoc.
f_equal; f_equal.
clear IHla.
apply (ε_aux_app_cons_ε_aux_app_app Hop).
Qed.

Theorem ε_aux_app_cons_lt :
  ∀ {i j} la lb,
  i < j
  → ε_aux i (la ++ j :: lb) = ε_aux i (la ++ lb).
Proof.
intros * Hij.
revert i j lb Hij.
induction la as [| a]; intros; cbn; [ | now rewrite IHla ].
now apply Nat.compare_lt_iff in Hij; rewrite Hij.
Qed.

Theorem ε_aux_app_cons_gt :
  rngl_has_opp T = true →
  ∀ {i j} la lb,
  j < i
  → ε_aux i (la ++ j :: lb) = (- ε_aux i (la ++ lb))%L.
Proof.
intros Hop * Hij.
revert i j lb Hij.
induction la as [| a]; intros; cbn. {
  now apply Nat.compare_gt_iff in Hij; rewrite Hij.
}
rewrite (IHla _ _ _ Hij).
destruct (i ?= a); [ | easy | easy ].
symmetry; apply (rngl_opp_0 Hop).
Qed.

Theorem ε_aux_permut :
  rngl_has_opp T = true →
  ∀ i la lb,
  permutation Nat.eqb la lb
  → ε_aux i la = ε_aux i lb.
Proof.
intros Hop * Hp.
revert lb Hp.
induction la as [| a]; intros; cbn. {
  now apply permutation_nil_l in Hp; subst lb.
}
apply permutation_cons_l_iff in Hp.
remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Haft).
apply Nat.eqb_eq in Hx; subst x.
remember (i ?= a) as ia eqn:Hia; symmetry in Hia.
subst lb.
destruct ia. {
  apply Nat.compare_eq_iff in Hia; subst a.
  symmetry; apply (ε_aux_dup Hop).
} {
  apply Nat.compare_lt_iff in Hia.
  rewrite (ε_aux_app_cons_lt _ _ Hia).
  now apply IHla.
} {
  apply Nat.compare_gt_iff in Hia.
  rewrite (ε_aux_app_cons_gt Hop _ _ Hia).
  f_equal.
  now apply IHla.
}
Qed.

Theorem sign_comp :
  rngl_has_opp T = true →
  ∀ la lb,
  permut_seq_with_len (List.length la) lb
  → ε (la ° lb) = (ε la * ε lb)%L.
Proof.
intros Hop * Hbp.
remember (List.length la) as n eqn:Hla; symmetry in Hla.
revert lb Hbp la Hla.
induction n; intros; cbn. {
  destruct Hbp as (Hb, Hbl).
  apply List.length_zero_iff_nil in Hla, Hbl; subst la lb.
  symmetry; apply (rngl_mul_1_l Hon).
}
(* removing the highest value, "n" in "lb", permutation of {0..n} *)
specialize (permut_without_highest Hbp) as H1.
destruct H1 as (i & Hi & Hin & H1).
(* taking lb1 and lb2 such that lb=lb1++n::lb2 *)
specialize List.nth_split as H2.
specialize (H2 _ i lb 0 Hi).
destruct H2 as (lb1 & lb2 & Hlb & Hjl1).
rewrite Hin in Hlb.
(* proving that "lb1++lb2" is a permuation of {0..n-1} *)
rewrite Hlb in H1.
rewrite List_butn_app_cons in H1; [ | easy ].
(* replacing lb with lb1++n::lb2 in the goal... *)
rewrite Hlb.
rewrite comp_list_app_distr_l; cbn.
rewrite fold_comp_list.
(* ... we can make "(-1)^len(lb2)" appear in both sides of the equality *)
(* first, in the lhs *)
rewrite (ε_app_cons2 Hop).
rewrite comp_length.
(* second, in the rhs *)
rewrite (ε_app_cons Hop lb1). 2: {
  intros j Hj.
  destruct H1 as (H11, H12).
  generalize H11; intros H13.
  apply permut_seq_NoDup in H13.
  apply (List.In_nth _ _ 0) in Hj.
  destruct Hj as (k & Hnk & Hk).
  subst j.
  apply permut_seq_ub in H11.
  specialize (H11 (List.nth k (lb1 ++ lb2) 0)).
  rewrite H12 in H11.
  apply H11.
  now apply List.nth_In.
}
do 2 rewrite (minus_one_pow_mul_comm Hop).
rewrite rngl_mul_assoc.
(* so, this "(-1)^len(lb2)" can disappear *)
f_equal.
(* this operation makes the last (n-th) element of "la" appear appended
   to "la°(lb1++lb2)" *)
rewrite List.app_assoc.
rewrite <- comp_list_app_distr_l.
specialize (@List.app_removelast_last _ la 0) as H4.
assert (H : la ≠ []) by now intros H; rewrite H in Hla.
specialize (H4 H); clear H.
replace n with (List.length la - 1) by flia Hla.
rewrite <- List_last_nth.
(* we know that "la" without its last element (its n-th element) has
   List.length "n"... *)
assert (Hra : List.length (List.removelast la) = n). {
  apply (f_equal (λ l, List.length l)) in H4.
  rewrite List.length_app, Nat.add_1_r in H4.
  rewrite Hla in H4.
  now apply Nat.succ_inj in H4.
}
(* and that "lb1++lb2" also has List.length "n" *)
assert (Hbbl : List.length (lb1 ++ lb2) = n). {
  apply (f_equal (λ l, List.length l)) in Hlb.
  rewrite List.length_app in Hlb; cbn in Hlb.
  rewrite Nat.add_succ_r, <- List.length_app in Hlb.
  destruct Hbp as (Hbp1, Hbp2).
  rewrite Hbp2 in Hlb.
  now apply Nat.succ_inj in Hlb.
}
(* since "lb1++lb2" does not contain "n", the expression "la°(lb1++lb2)"
   can be replaced by "(la without its last)°(lb1++lb2)" *)
replace (la ° (lb1 ++ lb2)) with (List.removelast la ° (lb1 ++ lb2)). 2: {
  rewrite H4 at 2.
  unfold "°".
  apply List.map_ext_in.
  intros j Hj.
  rewrite List.app_nth1; [ easy | ].
  rewrite Hra.
  destruct H1 as (H11, H12).
  apply permut_seq_iff in H11.
  destruct H11 as (H111, H112).
  unfold AllLt in H111.
  rewrite H12 in H111.
  now apply H111.
}
(* we can make "(-1)^n" appear in the lhs... *)
specialize (ε_app_cons2 Hop) as H5.
specialize (H5 [] (List.removelast la ° (lb1 ++ lb2)) (List.last la 0)).
do 2 rewrite List.app_nil_l in H5.
rewrite comp_length in H5.
rewrite Hbbl in H5.
apply (f_equal (rngl_mul (minus_one_pow n))) in H5.
rewrite rngl_mul_assoc in H5.
rewrite (minus_one_pow_mul_same Hop) in H5.
rewrite (rngl_mul_1_l Hon) in H5.
rewrite <- H5; cbn; clear H5.
(* ... and the right factor of the lhs, being
   "ε((la without List.last)°(lb1++lb2)", can be replaced using
   the induction hypothesis *)
rewrite (IHn (lb1 ++ lb2) H1 _ Hra).
do 2 rewrite rngl_mul_assoc.
(* these operation make "ε(lb1++lb2)" appear as factors in both sides
   of the goal, we can remove them *)
f_equal.
(* the lhs, "ε(la)", is "(-1)^n" times
   "ε(List.last la++all but List.last la)" *)
symmetry.
specialize (ε_app_cons2 Hop [] (List.removelast la) (List.last la 0)) as H5.
cbn - [ ε ] in H5.
rewrite Hra in H5.
rewrite <- List.app_removelast_last in H5; [ | now intros H; subst la ].
apply (f_equal (rngl_mul (minus_one_pow n))) in H5.
rewrite rngl_mul_assoc in H5.
rewrite (minus_one_pow_mul_same Hop) in H5.
rewrite (rngl_mul_1_l Hon) in H5.
rewrite <- H5; cbn.
(* both sides now contain "(-1)^" and "ε(la without List.last)" that we can
   eliminate *)
rewrite <- rngl_mul_assoc; f_equal; cbn; f_equal.
(* the goal now contain equality between two "ε_aux (List.last la)" which
   can be proven saying when their second arguments are permutations
   the one to the other *)
apply (ε_aux_permut Hop).
unfold "°".
rewrite (List_map_nth_seq 0 (List.removelast la)) at 1.
rewrite Hra.
apply permutation_map with (eqba := Nat.eqb). {
  unfold equality; apply Nat.eqb_eq.
} {
  unfold equality; apply Nat.eqb_eq.
}
apply (@permut_seq_permutation n); [ | apply H1 ].
apply seq_permut_seq_with_len.
Qed.

(* *)

Theorem ε_nil : ε [] = 1%L.
Proof. easy. Qed.

Theorem ε_aux_map_S : ∀ i l,  ε_aux (S i) (List.map S l) = ε_aux i l.
Proof.
intros.
revert i.
induction l as [| j]; intros; [ easy | cbn ].
now rewrite IHl.
Qed.

Theorem ε_map_S : ∀ l, ε (List.map S l) = ε l.
Proof.
intros.
induction l as [| i]; [ easy | cbn ].
rewrite IHl.
f_equal.
apply ε_aux_map_S.
Qed.

Theorem transposition_permut_seq_with_len : ∀ p q n,
  p < n
  → q < n
  → permut_seq_with_len n (List.map (transposition p q) (List.seq 0 n)).
Proof.
intros * Hp Hq.
split. {
  apply permut_seq_iff.
  split. {
    intros i Hi.
    unfold transposition.
    rewrite List.length_map, List.length_seq.
    apply List.in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply List.in_seq in Hj.
    rewrite <- Hji.
    now apply transposition_lt.
  } {
    apply nat_NoDup.
    rewrite List_length_map_seq.
    intros i j Hi Hj Hs.
    unfold transposition in Hs.
    rewrite (List_map_nth' 0) in Hs; [ | now rewrite List.length_seq ].
    rewrite (List_map_nth' 0) in Hs; [ | now rewrite List.length_seq ].
    rewrite List.seq_nth in Hs; [ | easy ].
    rewrite List.seq_nth in Hs; [ | easy ].
    do 4 rewrite if_eqb_eq_dec in Hs.
    do 2 rewrite Nat.add_0_l in Hs.
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
}
now rewrite List.length_map, List.length_seq.
Qed.

Theorem ε_aux_app : ∀ i p q,
  (∀ j k, j ∈ i :: p → k ∈ q → j < k)
  → ε_aux i (p ++ q) = ε_aux i p.
Proof.
intros * Hpq.
revert i q Hpq.
induction p as [| j]; intros; cbn. {
  assert (H : ∀ k, k ∈ q → i < k). {
    intros.
    apply Hpq; [ now left | easy ].
  }
  clear Hpq; rename H into Hq.
  induction q as [| k]; [ easy | cbn ].
  specialize (Hq k (or_introl eq_refl)) as H.
  apply Nat.compare_lt_iff in H; rewrite H.
  apply IHq.
  intros j Hj.
  now apply Hq; right.
}
destruct (i ?= j); [ easy | | ]. {
  apply IHp.
  intros k l Hk Hl.
  apply Hpq; [ | easy ].
  destruct Hk; [ now left | now right; right ].
} {
  f_equal.
  apply IHp.
  intros k l Hk Hl.
  apply Hpq; [ | easy ].
  destruct Hk; [ now left | now right; right ].
}
Qed.

Theorem ε_app : ∀ p q,
  (∀ i j, i ∈ p → j ∈ q → i < j)
  → ε (p ++ q) = (ε p * ε q)%L.
Proof.
intros * Hpq.
revert q Hpq.
induction p as [| i]; intros. {
  cbn; symmetry; f_equal.
  apply (rngl_mul_1_l Hon).
}
cbn.
rewrite IHp. 2: {
  intros j k Hj Hk.
  apply Hpq; [ now right | easy ].
}
rewrite <- rngl_mul_assoc; f_equal.
now apply ε_aux_app.
Qed.

Theorem ε_aux_app2 :
  rngl_has_opp T = true →
  ∀ i p q,
  (∀ j k, j ∈ i :: p → k ∈ q → k < j)
  → ε_aux i (p ++ q) = (minus_one_pow (List.length q) * ε_aux i p)%L.
Proof.
intros Hop * Hpq.
revert i q Hpq.
induction p as [| j]; intros; cbn. {
  rewrite (rngl_mul_1_r Hon).
  assert (H : ∀ k, k ∈ q → k < i). {
    intros.
    apply Hpq; [ now left | easy ].
  }
  clear Hpq; rename H into Hq.
  induction q as [| k]; [ easy | cbn ].
  specialize (Hq k (or_introl eq_refl)) as H.
  apply Nat.compare_lt_iff in H.
  apply (f_equal CompOpp) in H; cbn in H.
  rewrite <- Nat.compare_antisym in H; rewrite H.
  rewrite (minus_one_pow_succ Hop); f_equal.
  apply IHq.
  intros j Hj.
  now apply Hq; right.
}
destruct (i ?= j). {
  symmetry; apply rngl_mul_0_r.
  now apply rngl_has_opp_or_psub_iff; left.
} {
  apply IHp.
  intros k l Hk Hl.
  apply Hpq; [ | easy ].
  destruct Hk; [ now left | now right; right ].
} {
  rewrite (rngl_mul_opp_r Hop).
  f_equal.
  apply IHp.
  intros k l Hk Hl.
  apply Hpq; [ | easy ].
  destruct Hk; [ now left | now right; right ].
}
Qed.

Theorem ε_app2 :
  rngl_has_opp T = true →
  ∀ p q,
  (∀ i j, i ∈ p → j ∈ q → j < i)
  → ε (p ++ q) =
    (minus_one_pow (List.length p * List.length q) * ε p * ε q)%L.
Proof.
intros Hop * Hpq.
revert q Hpq.
induction p as [| i]; intros. {
  cbn; symmetry; f_equal.
  now do 2 rewrite (rngl_mul_1_l Hon).
}
cbn.
rewrite IHp. 2: {
  intros j k Hj Hk.
  apply Hpq; [ now right | easy ].
}
do 3 rewrite rngl_mul_assoc.
f_equal; f_equal.
rewrite (minus_one_pow_add Hon Hop).
do 2 rewrite <- (minus_one_pow_mul_comm Hop).
rewrite <- rngl_mul_assoc; f_equal.
now apply ε_aux_app2.
Qed.

Theorem ε_seq : ∀ sta len, ε (List.seq sta len) = 1%L.
Proof.
intros.
revert sta.
induction len; intros; [ easy | ].
rewrite List.seq_S.
rewrite ε_app. 2: {
  intros * Hi Hj.
  apply List.in_seq in Hi.
  destruct Hj as [Hj| ]; [ now subst j | easy ].
}
cbn.
do 2 rewrite (rngl_mul_1_r Hon).
apply IHlen.
Qed.

Theorem transposition_signature_lt :
  rngl_has_opp T = true →
  ∀ {n p q},
  p < q
  → q < n
  → ε (List.map (transposition p q) (List.seq 0 n)) = (-1)%L.
Proof.
intros Hop * Hpq Hq.
unfold transposition.
rewrite (List_seq_cut3 p). 2: {
  apply List.in_seq.
  split; [ easy | cbn ].
  now transitivity q.
}
rewrite (List_seq_cut3 q (S p)). 2: {
  apply List.in_seq; cbn.
  split; [ easy | flia Hq ].
}
rewrite Nat.sub_0_r, Nat.add_0_l.
replace (S p + (n - S p) - S q) with (n - S q) by flia Hpq.
do 4 rewrite List.map_app.
cbn.
do 2 rewrite Nat.eqb_refl.
replace (q =? p) with false. 2: {
  symmetry; apply Nat.eqb_neq.
  intros H; subst q.
  now apply Nat.lt_irrefl in Hpq.
}
erewrite List.map_ext_in. 2: {
  intros i Hi.
  apply List.in_seq in Hi; cbn in Hi.
  destruct Hi as (_, Hi).
  replace (i =? q) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hpq Hi.
  }
  apply Nat.lt_neq in Hi.
  apply Nat.eqb_neq in Hi; rewrite Hi.
  easy.
}
rewrite List.map_id.
erewrite List.map_ext_in. 2: {
  intros i Hi.
  apply List.in_seq in Hi; cbn in Hi.
  replace (S (p + (q - S p))) with q in Hi by flia Hpq.
  replace (i =? p) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hi.
  }
  replace (i =? q) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hi.
  }
  easy.
}
rewrite List.map_id.
erewrite List.map_ext_in. 2: {
  intros i Hi.
  apply List.in_seq in Hi; cbn in Hi.
  replace (S (q + _)) with n in Hi by flia Hpq Hq.
  replace (i =? p) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hpq Hi.
  }
  replace (i =? q) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hi.
  }
  easy.
}
rewrite List.map_id.
rewrite ε_app. 2: {
  intros * Hi Hj.
  apply List.in_seq in Hi; cbn in Hi; destruct Hi as (_, Hi).
  destruct Hj as [Hj| Hj]; [ now subst j; transitivity p | ].
  apply List.in_app_iff in Hj.
  destruct Hj as [Hj| Hj]; [ apply List.in_seq in Hj; flia Hi Hj | ].
  destruct Hj as [Hj| Hj]; [ now subst j | ].
  apply List.in_seq in Hj; flia Hi Hpq Hj.
}
rewrite ε_seq, (rngl_mul_1_l Hon).
rewrite List_cons_is_app.
rewrite (List_cons_is_app p).
do 2 rewrite List.app_assoc.
rewrite ε_app. 2: {
  intros i j Hi Hj.
  apply List.in_seq in Hj.
  rewrite Nat.add_comm, Nat.sub_add in Hj; [ | easy ].
  apply List.in_app_iff in Hi.
  destruct Hi as [Hi| Hi]. {
    apply List.in_app_iff in Hi.
    destruct Hi as [Hi| Hi]. {
      destruct Hi; [ now subst i | easy ].
    }
    apply List.in_seq in Hi.
    rewrite Nat.add_comm, Nat.sub_add in Hi; [ | easy ].
    now transitivity q.
  }
  destruct Hi; [ subst i | easy ].
  now transitivity q.
}
rewrite ε_seq, (rngl_mul_1_r Hon).
clear n Hq.
rewrite (ε_app2 Hop). 2: {
  intros i j Hi Hj.
  destruct Hj; [ subst j | easy ].
  apply List.in_app_iff in Hi.
  destruct Hi as [Hi| Hi]. {
    destruct Hi; [ now subst i | easy ].
  }
  now apply List.in_seq in Hi.
}
rewrite List.length_app, List.length_seq.
cbn - [ ε ].
rewrite Nat.mul_1_r.
replace (ε [p]) with 1%L by now cbn; rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (minus_one_pow_succ Hop).
rewrite (rngl_mul_opp_l Hop); f_equal.
rewrite List_cons_is_app.
rewrite (ε_app2 Hop). 2: {
  intros i j Hi Hj.
  destruct Hi; [ subst i | easy ].
  apply List.in_seq in Hj.
  now rewrite Nat.add_comm, Nat.sub_add in Hj.
}
rewrite ε_seq, (rngl_mul_1_r Hon).
rewrite List.length_seq; cbn.
rewrite Nat.add_0_r.
do 2 rewrite (rngl_mul_1_r Hon).
now apply minus_one_pow_mul_same.
Qed.

Theorem transposition_signature :
  rngl_has_opp T = true →
  ∀ n p q,
  p ≠ q
  → p < n
  → q < n
  → ε (List.map (transposition p q) (List.seq 0 n)) = (-1)%L.
Proof.
intros Hop * Hpq Hp Hq.
destruct (lt_dec p q) as [Hpq'| Hpq']. {
  now apply transposition_signature_lt.
}
apply Nat.nlt_ge in Hpq'.
assert (H : q < p) by flia Hpq Hpq'.
rewrite <- (transposition_signature_lt Hop H Hp).
f_equal.
apply List.map_ext_in.
intros i Hi.
apply transposition_comm.
Qed.

Theorem comp_permut_seq : ∀ n σ₁ σ₂,
  permut_seq_with_len n σ₁
  → permut_seq_with_len n σ₂
  → permut_seq (σ₁ ° σ₂).
Proof.
intros * (Hp11, Hp12) (Hp21, Hp22).
apply permut_seq_iff.
split. {
  intros i Hi.
  unfold comp_list in Hi |-*.
  rewrite List.length_map.
  apply List.in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  subst i.
  rewrite Hp22, <- Hp12.
  apply permut_seq_ub; [ easy | ].
  apply List.nth_In.
  apply permut_seq_iff in Hp21.
  apply Hp21 in Hj.
  congruence.
} {
  unfold comp_list.
  apply nat_NoDup.
  rewrite List.length_map.
  intros i j Hi Hj.
  rewrite (List_map_nth' 0); [ | easy ].
  rewrite (List_map_nth' 0); [ | easy ].
  intros Hij.
  apply permut_seq_iff in Hp11.
  apply permut_seq_iff in Hp21.
  destruct Hp11 as (_, Hp11).
  apply (NoDup_nat _ Hp11) in Hij; cycle 1. {
    rewrite Hp12, <- Hp22.
    now apply Hp21, List.nth_In.
  } {
    rewrite Hp12, <- Hp22.
    now apply Hp21, List.nth_In.
  }
  destruct Hp21 as (_, Hp21).
  now apply (NoDup_nat _ Hp21) in Hij.
}
Qed.

Theorem comp_permut_seq_with_len : ∀ n σ₁ σ₂,
  permut_seq_with_len n σ₁
  → permut_seq_with_len n σ₂
  → permut_seq_with_len n (σ₁ ° σ₂).
Proof.
intros * Hp1 Hp2.
split; [ now apply (comp_permut_seq n) | ].
unfold "°".
rewrite List.length_map.
now destruct Hp2.
Qed.

Theorem permut_comp_cancel_l : ∀ n la lb lc,
  List.NoDup la
  → List.length la = n
  → permut_seq_with_len n lb
  → permut_seq_with_len n lc
  → la ° lb = la ° lc ↔ lb = lc.
Proof.
intros * Ha Hal Hb Hc.
split; [ | now intros; subst lc ].
intros Hbc.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  destruct Hb as (_, Hb).
  destruct Hc as (_, Hc).
  apply List.length_zero_iff_nil in Hb, Hc.
  congruence.
}
apply List_eq_iff in Hbc.
destruct Hbc as (_, Hbc).
apply List_eq_iff.
split; [ destruct Hb, Hc; congruence | ].
intros d i.
unfold "°" in Hbc.
assert
    (H :
       ∀ i,
       List.nth (List.nth i lb 0) la 0 = List.nth (List.nth i lc 0) la 0). {
  intros j.
  destruct (lt_dec j n) as [Hjn| Hjn]. 2: {
    apply Nat.nlt_ge in Hjn.
    rewrite (List.nth_overflow lb); [ | destruct Hb; congruence ].
    rewrite (List.nth_overflow lc); [ | destruct Hc; congruence ].
    easy.
  }
  specialize (Hbc 0 j).
  rewrite (List_map_nth' 0) in Hbc; [ | destruct Hb; congruence ].
  rewrite (List_map_nth' 0) in Hbc; [ | destruct Hc; congruence ].
  easy.
}
clear Hbc; rename H into Hbc.
destruct (lt_dec i n) as [Hin| Hin]. 2: {
  apply Nat.nlt_ge in Hin.
  rewrite List.nth_overflow; [ | destruct Hb; congruence ].
  rewrite List.nth_overflow; [ | destruct Hc; congruence ].
  easy.
}
specialize (Hbc i).
apply (NoDup_nat _ Ha) in Hbc; cycle 1. {
  destruct Hb as (Hbp, Hbl).
  rewrite Hal, <- Hbl.
  apply permut_seq_iff in Hbp.
  apply Hbp, List.nth_In.
  congruence.
} {
  destruct Hc as (Hcp, Hcl).
  rewrite Hal, <- Hcl.
  apply permut_seq_iff in Hcp.
  apply Hcp, List.nth_In.
  congruence.
}
rewrite List.nth_indep with (d' := 0); [ | destruct Hb; congruence ].
symmetry.
rewrite List.nth_indep with (d' := 0); [ | destruct Hc; congruence ].
now symmetry.
Qed.

Theorem permut_comp_cancel_r : ∀ n la lb lc,
  List.length la = n
  → List.length lb = n
  → permut_seq_with_len n lc
  → la ° lc = lb ° lc ↔ la = lb.
Proof.
intros * Hal Hbl Hc.
split; [ | now intros; subst la ].
intros Hab.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  apply List.length_zero_iff_nil in Hal, Hbl.
  congruence.
}
apply List_eq_iff in Hab.
destruct Hab as (_, Hab).
apply List_eq_iff.
split; [ congruence | ].
intros d i.
specialize (Hab d (List.nth i (isort_rank Nat.leb lc) 0)).
unfold "°" in Hab.
rewrite (List_map_nth' 0) in Hab. 2: {
  apply isort_rank_ub.
  intros H; subst lc.
  destruct Hc as (Hcp, Hcl).
  now symmetry in Hcl.
}
rewrite (List_map_nth' 0) in Hab. 2: {
  apply isort_rank_ub.
  intros H; subst lc.
  destruct Hc as (Hcp, Hcl).
  now symmetry in Hcl.
}
destruct Hc as (Hcp, Hcl).
destruct (lt_dec i n) as [Hin| Hin]. 2: {
  apply Nat.nlt_ge in Hin.
  rewrite List.nth_overflow; [ | now rewrite Hal ].
  rewrite List.nth_overflow; [ | now rewrite Hbl ].
  easy.
}
rewrite <- Hcl in Hin.
rewrite permut_permut_isort in Hab; [ | easy | easy ].
rewrite Hcl, <- Hal in Hin.
rewrite List.nth_indep with (d' := 0); [ symmetry | easy ].
rewrite Hal, <- Hbl in Hin.
rewrite List.nth_indep with (d' := 0); [ symmetry | easy ].
easy.
Qed.

Theorem comp_1_l : ∀ n l, AllLt l n → List.seq 0 n ° l = l.
Proof.
intros * Hp.
unfold "°".
erewrite List.map_ext_in. 2: {
  intros i Hi.
  rewrite List.seq_nth; [ | now apply Hp ].
  now apply Nat.add_0_l.
}
apply List.map_id.
Qed.

Theorem comp_1_r : ∀ n {la},
  List.length la = n
  → la ° List.seq 0 n = la.
Proof.
intros * Hl.
subst n.
unfold "°"; cbn.
symmetry.
apply List_map_nth_seq.
Qed.

Theorem collapse_permut_seq_with_len :
  ∀ l, permut_seq_with_len (List.length l) (collapse l).
Proof.
intros.
apply isort_rank_permut_seq_with_len.
apply isort_rank_length.
Qed.

Theorem permut_isort_rank_involutive : ∀ {la},
  permut_seq la
  → isort_rank Nat.leb (isort_rank Nat.leb la) = la.
Proof.
intros * Hp.
remember (isort_rank Nat.leb la) as lb eqn:Hlb.
apply (@permut_comp_cancel_r (List.length lb)) with (lc := lb). {
  now apply isort_rank_permut_seq_with_len.
} {
  now rewrite Hlb, isort_rank_length.
} {
  rewrite Hlb, isort_rank_length.
  now apply isort_rank_permut_seq_with_len.
}
subst lb.
rewrite comp_isort_rank_r.
rewrite permut_comp_isort_rank_l; [ | apply isort_rank_permut_seq ].
rewrite isort_rank_length; symmetry.
now apply permut_isort_leb.
Qed.

Theorem collapse_lt_compat : ∀ l i j,
  i < List.length l
  → j < List.length l
  → List.nth i l 0 < List.nth j l 0
  → List.nth i (collapse l) 0 < List.nth j (collapse l) 0.
Proof.
intros l j i Hj Hi Hc2.
specialize (collapse_permut_seq_with_len l) as Hc.
specialize (isort_rank_permut_seq_with_len Nat.leb (List.length l)) as Hr.
specialize (Hr _ eq_refl).
apply Nat.nle_gt; intros Hc1.
destruct (Nat.eq_dec (List.nth i (collapse l) 0) (List.nth j (collapse l) 0))
  as [H| H]. {
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  apply (NoDup_nat _ Hcn) in H; cycle 1. {
    now rewrite collapse_length.
  } {
    now rewrite collapse_length.
  }
  now subst j; apply Nat.lt_irrefl in Hc2.
}
assert (H' : List.nth i (collapse l) 0 < List.nth j (collapse l) 0)
  by flia Hc1 H.
clear Hc1 H; rename H' into Hc1.
unfold collapse in Hc1.
remember (isort_rank Nat.leb l) as lrank eqn:Hlr.
remember (List.nth i (collapse l) 0) as i' eqn:Hi'.
assert (Hii' : i = List.nth i' lrank 0). {
  subst i'; unfold collapse.
  rewrite <- Hlr; symmetry.
  destruct Hr as (Hrp, Hrl).
  apply permut_permut_isort; [ easy | now rewrite Hrl ].
}
rewrite Hii' in Hc1.
rewrite permut_isort_permut in Hc1; [ | now destruct Hr | ]. 2: {
  rewrite Hi'.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  rewrite Hcl in Hca.
  rewrite Hlr, isort_rank_length.
  apply Hca, List.nth_In.
  now rewrite Hcl.
}
remember (List.nth j (collapse l) 0) as j' eqn:Hj'.
assert (Hjj' : j = List.nth j' lrank 0). {
  subst j'; unfold collapse.
  rewrite <- Hlr; symmetry.
  destruct Hr as (Hrp, Hrl).
  apply permut_permut_isort; [ easy | now rewrite Hrl ].
}
rewrite Hjj' in Hc1.
rewrite permut_isort_permut in Hc1; [ | now destruct Hr | ]. 2: {
  rewrite Hj'.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  rewrite Hcl in Hca.
  rewrite Hlr, isort_rank_length.
  apply Hca, List.nth_In.
  now rewrite Hcl.
}
rewrite Hii', Hjj' in Hc2.
rewrite Hlr in Hc2.
assert (Hi'l : i' < List.length l). {
  rewrite Hi'.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  rewrite Hcl in Hca.
  apply Hca, List.nth_In.
  now rewrite collapse_length.
}
assert (Hj'l : j' < List.length l). {
  rewrite Hj'.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  rewrite Hcl in Hca.
  apply Hca, List.nth_In.
  now rewrite collapse_length.
}
rewrite nth_nth_isort_rank in Hc2; [ | easy ].
rewrite nth_nth_isort_rank in Hc2; [ | easy ].
specialize (sorted_isort Nat_leb_total_relation l) as Hsl.
rewrite (isort_isort_rank _ 0) in Hsl.
rewrite <- Hlr in Hsl.
specialize sorted_strongly_sorted as H1.
specialize (H1 _ _ Nat_leb_trans _ Hsl).
specialize strongly_sorted_if as H2.
specialize (H2 _ _ Nat_leb_trans _ H1 0).
rewrite List.length_map, Hlr, isort_rank_length in H2.
specialize (H2 i' j' Hi'l Hj'l Hc1).
apply Nat.leb_le in H2.
rewrite <- Hlr in H2.
rewrite (isort_isort_rank _ 0) in Hc2.
rewrite <- Hlr in Hc2.
now apply Nat.nle_gt in Hc2.
Qed.

Theorem collapse_keeps_order : ∀ {l},
  List.NoDup l
  → ∀ i j,  i < List.length l → j < List.length l
  → (List.nth i (collapse l) 0 ?= List.nth j (collapse l) 0) =
    (List.nth i l 0 ?= List.nth j l 0).
Proof.
intros * Hnd * Hi Hj.
remember (List.nth i (collapse l) 0 ?= List.nth j (collapse l) 0)
  as c1 eqn:Hc1.
remember (List.nth i l 0 ?= List.nth j l 0) as c2 eqn:Hc2.
specialize (collapse_permut_seq_with_len l) as Hc.
specialize (isort_rank_permut_seq_with_len Nat.leb (List.length l)) as Hr.
specialize (Hr _ eq_refl).
move c2 before c1.
symmetry in Hc1, Hc2.
destruct c1. {
  apply Nat.compare_eq_iff in Hc1.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  specialize (NoDup_nat _ Hcn i j) as H1.
  rewrite Hcl in H1.
  specialize (H1 Hi Hj Hc1).
  subst j.
  now rewrite Nat.compare_refl in Hc2.
} {
  apply Nat.compare_lt_iff in Hc1.
  destruct c2; [ | easy | ]; exfalso. {
    apply Nat.compare_eq_iff in Hc2.
    specialize (NoDup_nat _ Hnd i j Hi Hj Hc2) as H1.
    rewrite H1 in Hc1.
    now apply Nat.lt_irrefl in Hc1.
  } {
    apply Nat.compare_gt_iff in Hc2.
    apply Nat.nle_gt in Hc1; apply Hc1.
    now apply Nat.lt_le_incl, collapse_lt_compat.
  }
} {
  apply Nat.compare_gt_iff in Hc1.
  destruct c2; [ | | easy ]; exfalso. {
    apply Nat.compare_eq_iff in Hc2.
    specialize (NoDup_nat _ Hnd i j Hi Hj Hc2) as H1.
    rewrite H1 in Hc1.
    now apply Nat.lt_irrefl in Hc1.
  } {
    apply Nat.compare_lt_iff in Hc2.
    apply Nat.nle_gt in Hc1; apply Hc1.
    now apply Nat.lt_le_incl, collapse_lt_compat.
  }
}
Qed.

Definition keep_order la lb :=
  ∀ i j,  i < List.length la → j < List.length la →
  (List.nth i la 0 ?= List.nth j la 0) = (List.nth i lb 0 ?= List.nth j lb 0).

Theorem ε_keep_order :
  ∀ la lb, keep_order la lb → List.length la = List.length lb → ε la = ε lb.
Proof.
intros * Hko Hab.
revert lb Hko Hab.
induction la as [| a]; intros. {
  symmetry in Hab.
  now apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | ].
cbn in Hab; apply Nat.succ_inj in Hab.
cbn; rewrite IHla with (lb := lb); [ | | easy ]. 2: {
  intros i j Hi Hj.
  apply (Hko (S i) (S j)); now cbn; apply -> Nat.succ_lt_mono.
}
f_equal.
clear IHla.
move b before a.
revert a b lb Hko Hab.
induction la as [| a']; intros. {
  symmetry in Hab.
  now apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b']; [ easy | ].
cbn in Hab; apply Nat.succ_inj in Hab.
cbn.
specialize (Hko 0 1) as H1; cbn in H1.
rewrite <- H1; [ | easy | now apply -> Nat.succ_lt_mono ].
remember (a ?= a') as c eqn:Hc; symmetry in Hc.
assert (H : ε_aux a la = ε_aux b lb). {
  apply IHla; [ | easy ].
  intros i j Hi Hj.
  destruct i. {
    destruct j; [ now do 2 rewrite Nat.compare_refl | ].
    apply (Hko 0 (S (S j))); [ now cbn | ].
    now cbn; apply -> Nat.succ_lt_mono.
  }
  destruct j. {
    apply (Hko (S (S i)) 0); [ | now cbn ].
    now cbn; apply -> Nat.succ_lt_mono.
  }
  apply (Hko (S (S i)) (S (S j))); now cbn; apply -> Nat.succ_lt_mono.
}
destruct c; [ easy | easy | now f_equal ].
Qed.

Theorem ε_collapse_ε : ∀ l, List.NoDup l → ε (collapse l) = ε l.
Proof.
intros * Hnd.
apply ε_keep_order; [ | apply collapse_length ].
intros i j Hi Hj.
rewrite collapse_length in Hi, Hj.
now apply (collapse_keeps_order Hnd).
Qed.

Theorem permut_isort : ∀ {ord},
  antisymmetric ord
  → transitive ord
  → total_relation ord
  → ∀ n l p q,
  permut_seq_with_len n p
  → permut_seq_with_len n q
  → isort ord (l ° p) = isort ord (l ° q).
Proof.
intros * Hant Htr Htot * Hp Hq.
apply (isort_when_permuted Nat.eqb_eq); [ easy | easy | easy | ].
unfold "°".
apply (permutation_map Nat.eqb_eq Nat.eqb_eq).
apply (permutation_trans Nat.eqb_eq) with (lb := List.seq 0 n). {
  now destruct Hp as (Hp1, Hp2); rewrite <- Hp2.
} {
  destruct Hq as (Hq1, Hq2); rewrite <- Hq2.
  now apply (permutation_sym Nat.eqb_eq).
}
Qed.

Theorem isort_comp_permut_r : ∀ l p,
  permut_seq_with_len (List.length l) p
  → isort Nat.leb (l ° p) = isort Nat.leb l.
Proof.
intros * Hp.
symmetry.
rewrite <- (comp_1_r (List.length l) eq_refl) at 1.
specialize (permut_isort Nat_leb_antisym Nat_leb_trans) as H1.
specialize (H1 Nat_leb_total_relation).
apply (H1 (List.length l)); [ | easy ].
apply seq_permut_seq_with_len.
Qed.

Theorem permut_isort_rank_comp : ∀ n la lb,
  List.NoDup la
  → List.length la = n
  → permut_seq_with_len n lb
  → isort_rank Nat.leb (la ° lb) =
    isort_rank Nat.leb lb ° isort_rank Nat.leb la.
Proof.
intros * Ha Hal Hb.
apply permut_comp_cancel_l with (n := n) (la := la ° lb). {
  destruct Hb as (Hba, Hbl).
  apply permut_seq_iff in Hba.
  destruct Hba as (Hba, Hbn).
  unfold "°".
  apply (NoDup_map_iff 0).
  intros i j Hi Hj Hij.
  apply (NoDup_nat _ Ha) in Hij; cycle 1. {
    rewrite Hal, <- Hbl.
    now apply Hba, List.nth_In.
  } {
    rewrite Hal, <- Hbl.
    now apply Hba, List.nth_In.
  }
  now apply (NoDup_nat _ Hbn) in Hij.
} {
  now rewrite comp_length; destruct Hb.
} {
  apply isort_rank_permut_seq_with_len.
  now rewrite comp_length; destruct Hb.
} {
  destruct Hb.
  now apply comp_permut_seq_with_len; apply isort_rank_permut_seq_with_len.
}
rewrite comp_isort_rank_r.
rewrite <- (permut_comp_assoc n); cycle 1. {
  now destruct Hb.
} {
  destruct Hb as (Hba, Hbl).
  apply permut_seq_iff in Hba.
  destruct Hba as (Hba, Hbn).
  now apply comp_permut_seq_with_len; apply isort_rank_permut_seq_with_len.
} {
  apply (comp_permut_seq n). {
    apply isort_rank_permut_seq_with_len.
    now destruct Hb.
  } {
    now apply isort_rank_permut_seq_with_len.
  }
}
rewrite (permut_comp_assoc n) with (f := lb); cycle 1. {
  destruct Hb as (Hba, Hbl).
  apply permut_seq_iff in Hba.
  destruct Hba as (Hba, Hbn).
  now rewrite isort_rank_length.
} {
  now apply isort_rank_permut_seq_with_len.
} {
  apply isort_rank_permut_seq.
}
rewrite comp_isort_rank_r.
destruct Hb as (Hbp, Hbl).
rewrite (permut_isort_leb Hbp).
rewrite comp_1_l. 2: {
  intros i Hi.
  rewrite Hbl, <- Hal.
  now apply in_isort_rank in Hi.
}
rewrite comp_isort_rank_r.
apply isort_comp_permut_r.
now rewrite Hal, <- Hbl.
Qed.

Theorem permut_collapse : ∀ la,
  permut_seq la
  → collapse la = la.
Proof.
intros * Ha.
unfold collapse.
now apply permut_isort_rank_involutive.
Qed.

Theorem collapse_comp : ∀ la lb,
  List.NoDup la
  → permut_seq lb
  → List.length la = List.length lb
  → collapse (la ° lb) = collapse la ° lb.
Proof.
intros * Ha Hb Hab.
unfold collapse.
symmetry.
rewrite <- (permut_isort_rank_involutive Hb) at 1.
rewrite (permut_isort_rank_comp (List.length lb)); [ | easy | easy | easy ].
rewrite (permut_isort_rank_comp (List.length lb)); [ easy | | | ]. {
  apply NoDup_isort_rank.
} {
  apply isort_rank_length.
} {
  now apply isort_rank_permut_seq_with_len.
}
Qed.

Theorem isort_comp_collapse : ∀ la,
  isort Nat.leb la ° collapse la = la.
Proof.
intros.
apply List_eq_iff.
rewrite comp_length, collapse_length.
split; [ easy | ].
intros d i.
unfold comp_list.
destruct (lt_dec i (List.length la)) as [Hila| Hila]. 2: {
  apply Nat.nlt_ge in Hila.
  rewrite List.nth_overflow. 2: {
    now rewrite List.length_map, collapse_length.
  }
  now rewrite List.nth_overflow.
}
rewrite List.nth_indep with (d' := 0). 2: {
  now rewrite List.length_map, collapse_length.
}
symmetry.
rewrite List.nth_indep with (d' := 0); [ | easy ].
symmetry.
clear d.
rewrite (isort_isort_rank _ 0).
rewrite (List_map_nth' 0); [ | now rewrite collapse_length ].
rewrite (List_map_nth' 0). 2: {
  unfold collapse.
  apply isort_rank_ub.
  now intros H; apply eq_isort_rank_nil in H; subst la.
}
unfold collapse.
rewrite permut_permut_isort with (i := i); [ easy | | ]. 2: {
  now rewrite isort_rank_length.
}
apply isort_rank_permut_seq.
Qed.

Theorem sorted_permuted_comp_collapse : ∀ la lb,
  sorted Nat.leb la
  → permutation Nat.eqb la lb
  → la ° collapse lb = lb.
Proof.
intros * Hs Hp.
assert (Hba : isort Nat.leb lb = la). {
  rewrite isort_when_permuted with (eqb := Nat.eqb) (lb := la). {
    now apply isort_when_sorted.
  } {
    unfold equality; apply Nat.eqb_eq.
  } {
    apply Nat_leb_antisym.
  } {
    apply Nat_leb_trans.
  } {
    apply Nat_leb_total_relation.
  } {
    apply permutation_sym; [ | easy ].
    unfold equality; apply Nat.eqb_eq.
  }
}
rewrite <- Hba.
clear la Hs Hp Hba.
rename lb into la.
apply isort_comp_collapse.
Qed.

Theorem NoDup_comp_iff : ∀ la lb,
  permut_seq_with_len (List.length la) lb
  → List.NoDup la
  ↔ List.NoDup (la ° lb).
Proof.
intros * Hbp.
split. {
  intros Haa.
  unfold "°".
  apply (NoDup_map_iff 0).
  intros i j Hi Hj Hij.
  destruct Hbp as (Hbp, Hbl).
  apply (NoDup_nat _ Haa) in Hij; cycle 1. {
    rewrite <- Hbl.
    apply permut_seq_iff in Hbp.
    now apply Hbp, List.nth_In.
  } {
    rewrite <- Hbl.
    apply permut_seq_iff in Hbp.
    now apply Hbp, List.nth_In.
  }
  apply permut_seq_iff in Hbp.
  destruct Hbp as (Hba, Hbn).
  now apply (NoDup_nat _ Hbn) in Hij.
} {
  intros Haa.
  apply nat_NoDup.
  specialize (NoDup_nat _ Haa) as H1.
  intros i j Hi Hj Hij.
  rewrite comp_length in H1.
  destruct Hbp as (Hbp, Hbl).
  rewrite <- Hbl in Hi, Hj.
  remember (List.nth i (isort_rank Nat.leb lb) 0) as i' eqn:Hi'.
  remember (List.nth j (isort_rank Nat.leb lb) 0) as j' eqn:Hj'.
  specialize (H1 i' j').
  assert (H : i' < List.length lb). {
    rewrite Hi'.
    apply isort_rank_ub.
    now intros H; rewrite H in Hi.
  }
  specialize (H1 H); clear H.
  assert (H : j' < List.length lb). {
    rewrite Hj'.
    apply isort_rank_ub.
    now intros H; rewrite H in Hi.
  }
  specialize (H1 H); clear H.
  assert (H : List.nth i' (la ° lb) 0 = List.nth j' (la ° lb) 0). {
    rewrite Hi', Hj'.
    unfold "°".
    rewrite (List_map_nth' 0). 2: {
      apply isort_rank_ub.
      now intros H; subst lb.
    }
    rewrite (List_map_nth' 0). 2: {
      apply isort_rank_ub.
      now intros H; subst lb.
    }
    rewrite permut_permut_isort; [ | easy | easy ].
    rewrite permut_permut_isort; [ | easy | easy ].
    easy.
  }
  specialize (H1 H); clear H.
  rewrite Hi', Hj' in H1.
  assert (H : permut_seq (isort_rank Nat.leb lb)). {
    now apply isort_rank_permut_seq.
  }
  apply permut_seq_iff in H.
  destruct H as (Hra, Hrn).
  apply (NoDup_nat _ Hrn) in H1; [ easy | | ]. {
    now rewrite isort_rank_length.
  } {
    now rewrite isort_rank_length.
  }
}
Qed.

Theorem ε_dup :
  rngl_has_opp T = true →
  ∀ i l1 l2 l3, ε (l1 ++ i :: l2 ++ i :: l3) = 0%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_psub_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos after Hop.
revert i l2 l3.
induction l1 as [| j]; intros. {
  rewrite List.app_nil_l; cbn.
  rewrite (ε_aux_dup Hop).
  apply (rngl_mul_0_l Hos).
}
cbn.
rewrite IHl1.
apply (rngl_mul_0_r Hos).
Qed.

Theorem ε_when_dup :
  rngl_has_opp T = true →
  ∀ la,
  ¬ List.NoDup la
  → ε la = 0%L.
Proof.
intros Hop * Haa.
assert (H : no_dup Nat.eqb la = false). {
  apply Bool.negb_true_iff.
  apply Bool.eq_true_not_negb.
  intros H; apply Haa.
  now apply (no_dup_NoDup Nat.eqb_eq).
}
clear Haa; rename H into Haa.
apply (no_dup_false_iff Nat.eqb_eq) in Haa.
destruct Haa as (l1 & l2 & l3 & i & Haa).
subst la.
apply (ε_dup Hop).
Qed.

(* *)

Theorem ε_aux_ext_in :
  rngl_has_opp T = true →
  ∀ i f la lb,
  permutation Nat.eqb la lb
  → ε_aux i (List.map f la) = ε_aux i (List.map f lb).
Proof.
intros Hop * Hpab.
revert lb Hpab.
induction la as [| a]; intros; cbn. {
  now apply permutation_nil_l in Hpab; subst lb.
}
apply permutation_cons_l_iff in Hpab.
remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Haft).
apply Nat.eqb_eq in Hx; subst x.
specialize (IHla (bef ++ aft) Hpab) as H1.
rewrite H1, Haft.
remember (i ?= f a) as ifa eqn:Hifa; symmetry in Hifa.
do 2 rewrite List.map_app; cbn; symmetry.
destruct ifa. {
  apply Nat.compare_eq_iff in Hifa; subst i.
  apply (ε_aux_dup Hop).
} {
  apply Nat.compare_lt_iff in Hifa.
  now apply ε_aux_app_cons_lt.
} {
  apply Nat.compare_gt_iff in Hifa.
  now apply (ε_aux_app_cons_gt Hop).
}
Qed.

Theorem ε_aux_seq_out :
  rngl_has_opp T = true →
  ∀ sta len i,
  sta + len ≤ i
  → ε_aux i (List.seq sta len) = minus_one_pow len.
Proof.
intros Hop * Hi.
revert i sta Hi.
induction len; intros; [ easy | cbn ].
remember (i ?= sta) as is eqn:His; symmetry in His.
destruct is. {
  apply Nat.compare_eq_iff in His.
  flia Hi His.
} {
  apply Nat.compare_lt_iff in His.
  flia Hi His.
}
rewrite (minus_one_pow_succ Hop); f_equal.
rewrite <- Nat.add_succ_comm in Hi.
now apply IHlen.
Qed.

Theorem ε_aux_app_all_gt_l :
  rngl_has_opp T = true →
  ∀ i la lb,
  (∀ j, j ∈ la → j < i)
  → ε_aux i (la ++ lb) = (minus_one_pow (List.length la) * ε_aux i lb)%L.
Proof.
intros Hop * Hla.
revert lb.
induction la as [| a]; intros; cbn; [ symmetry; apply (rngl_mul_1_l Hon) | ].
specialize (Hla a (or_introl eq_refl)) as H1.
apply Nat.compare_gt_iff in H1.
rewrite H1.
rewrite (minus_one_pow_succ Hop).
rewrite (rngl_mul_opp_l Hop); f_equal.
apply IHla.
intros j Hj.
now apply Hla; right.
Qed.

Theorem ε_aux_app_comm :
  rngl_has_opp T = true →
  ∀ i la lb,
  ε_aux i (la ++ lb) = ε_aux i (lb ++ la).
Proof.
intros Hop *.
apply (ε_aux_permut Hop).
apply permutation_app_comm.
unfold equality; apply Nat.eqb_eq.
Qed.

Theorem ε_aux_all_gt :
  ∀ i la,
  (∀ j, j ∈ la → i < j)
  → ε_aux i la = 1%L.
Proof.
intros * Hi.
revert i Hi.
induction la as [| a]; intros; [ easy | cbn ].
remember (i ?= a) as ia eqn:Hia; symmetry in Hia.
destruct ia. {
  apply Nat.compare_eq_iff in Hia; subst a.
  specialize (Hi i (or_introl eq_refl)).
  now apply Nat.lt_irrefl in Hi.
} {
  apply IHla.
  intros j Hj.
  now apply Hi; right.
} {
  apply Nat.compare_gt_iff in Hia.
  specialize (Hi a (or_introl eq_refl)).
  flia Hi Hia.
}
Qed.

Theorem succ_when_ge_id : ∀ k, succ_when_ge k k = k + 1.
Proof.
intros.
unfold succ_when_ge.
now rewrite Nat.leb_refl.
Qed.

Theorem ε_aux_map_succ_when_ge_canon_sym_gr_list :
  rngl_has_opp T = true →
  ∀ n i j,
  i ≤ n
  → j < n!
  → ε_aux i (List.map (succ_when_ge i) (canon_sym_gr_list n j)) =
    minus_one_pow i.
Proof.
intros Hop * Hin Hjn.
rewrite (ε_aux_permut Hop _ _ (List.map (succ_when_ge i) (List.seq 0 n))).
2: {
  apply (permutation_map Nat.eqb_eq Nat.eqb_eq).
  apply permut_seq_permutation with (n := n). {
    now apply canon_sym_gr_list_permut_seq_with_len.
  } {
    apply seq_permut_seq_with_len.
  }
}
clear j Hjn.
destruct (Nat.eq_dec i n) as [Hien| Hien]. {
  subst i; clear Hin.
  erewrite List.map_ext_in. 2: {
    intros j Hj.
    apply List.in_seq in Hj; destruct Hj as (_, Hj); cbn in Hj.
    unfold succ_when_ge.
    now apply Nat.leb_gt in Hj; rewrite Hj, Nat.add_0_r.
  }
  rewrite List.map_id.
  now apply (ε_aux_seq_out Hop).
}
assert (H : i < n) by flia Hin Hien.
clear Hin Hien; rename H into Hin.
rewrite (List_seq_cut i); [ | now apply List.in_seq ].
rewrite Nat.sub_0_r, Nat.add_0_l.
rewrite List.map_app.
erewrite List.map_ext_in. 2: {
  intros j Hj.
  apply List.in_seq in Hj; destruct Hj as (_, Hj); cbn in Hj.
  unfold succ_when_ge, Nat.b2n.
  now apply Nat.leb_gt in Hj; rewrite Hj, Nat.add_0_r.
}
rewrite List.map_id.
rewrite (ε_aux_app_all_gt_l Hop). 2: {
  intros j Hj.
  now apply List.in_seq in Hj.
}
rewrite List.length_seq, <- (rngl_mul_1_r Hon); f_equal.
erewrite List.map_ext_in. 2: {
  intros j Hj.
  apply List.in_seq in Hj; destruct Hj as (Hij, Hjn).
  rewrite Nat.add_comm, Nat.sub_add in Hjn; [ | now apply Nat.lt_le_incl ].
  unfold succ_when_ge.
  now apply Nat.leb_le in Hij; rewrite Hij, Nat.add_1_r; cbn.
}
rewrite List.seq_shift.
apply ε_aux_all_gt.
intros j Hj.
apply List.in_seq in Hj.
flia Hj.
Qed.

Theorem ε_map_succ_when_ge :
   ∀ i la,
  List.NoDup la
  → ε (List.map (succ_when_ge i) la) = ε la.
Proof.
intros * Ha.
induction la as [| a]; [ easy | cbn ].
apply List.NoDup_cons_iff in Ha.
destruct Ha as (Ha, Hla).
specialize (IHla Hla).
rewrite IHla; f_equal.
clear Ha IHla.
induction la as [| b]; [ easy | cbn ].
apply List.NoDup_cons_iff in Hla.
destruct Hla as (Hb, Hla).
specialize (IHla Hla).
rewrite IHla.
unfold succ_when_ge, Nat.b2n.
do 2 rewrite if_leb_le_dec.
destruct (le_dec i a) as [Hia| Hia]. {
  destruct (le_dec i b) as [Hib| Hib]. {
    now do 2 rewrite Nat.add_1_r.
  }
  assert (H : b < a) by flia Hia Hib.
  apply Nat.compare_gt_iff in H; rewrite H; clear H.
  rewrite Nat.add_0_r.
  apply Nat.nle_gt in Hib.
  assert (H : b < a + 1) by flia Hia Hib.
  now apply Nat.compare_gt_iff in H; rewrite H.
}
apply Nat.nle_gt in Hia.
destruct (le_dec i b) as [Hib| Hib]. {
  assert (H : a < b) by flia Hia Hib.
  apply Nat.compare_lt_iff in H; rewrite H; clear H.
  rewrite Nat.add_0_r.
  assert (H : a < b + 1) by flia Hia Hib.
  now apply Nat.compare_lt_iff in H; rewrite H.
}
now do 2 rewrite Nat.add_0_r.
Qed.

(* equality of ε of sym_gr elem and ε_permut *)

Theorem ε_of_sym_gr_permut_succ :
  rngl_has_opp T = true →
  ∀ n k,
  k < (S n)!
  → ε (canon_sym_gr_list (S n) k) =
    (minus_one_pow (k / n!) * ε (canon_sym_gr_list n (k mod n!)))%L.
Proof.
intros Hop * Hkn; cbn.
f_equal. {
  apply (ε_aux_map_succ_when_ge_canon_sym_gr_list Hop). {
    apply Nat.lt_succ_r.
    apply Nat.Div0.div_lt_upper_bound.
    now rewrite Nat.mul_comm, <- Nat_fact_succ.
  } {
    apply Nat.mod_upper_bound, fact_neq_0.
  }
} {
  apply ε_map_succ_when_ge.
  apply permut_seq_NoDup.
  apply canon_sym_gr_list_permut_seq.
  apply Nat.mod_upper_bound, fact_neq_0.
}
Qed.

Theorem canon_sym_gr_surjective : ∀ {n k j},
  k < fact n
  → j < n
  → ∃ i : nat, i < n ∧ List.nth i (canon_sym_gr_list n k) 0 = j.
Proof.
intros * Hkn Hjn.
exists (List.nth j (canon_sym_gr_inv_list n k) 0).
split; [ now apply canon_sym_gr_inv_list_ub | ].
now apply canon_sym_gr_sym_gr_inv.
Qed.

Theorem NoDup_ε_1_opp_1 :
  rngl_has_opp T = true →
  ∀ σ, List.NoDup σ → ε σ = 1%L ∨ ε σ = (-1)%L.
Proof.
intros Hop * Hσ.
induction σ as [| a la]; [ now left | cbn ].
apply List.NoDup_cons_iff in Hσ.
destruct Hσ as (Ha, Hnd).
specialize (IHla Hnd).
destruct IHla as [Hla| Hla]; rewrite Hla. {
  rewrite (rngl_mul_1_r Hon).
  clear Hla.
  induction la as [| b]; intros; [ now left | cbn ].
  apply List.not_in_cons in Ha.
  destruct Ha as (Hab, Ha).
  apply List.NoDup_cons_iff in Hnd.
  destruct Hnd as (Hb, Hnd).
  specialize (IHla Ha Hnd).
  remember (a ?= b) as ab eqn:Hc; symmetry in Hc.
  destruct ab; [ now apply Nat.compare_eq_iff in Hc | easy | ].
  destruct IHla as [Haa| Haa]; rewrite Haa; [ now right | ].
  left; apply (rngl_opp_involutive Hop).
} {
  clear Hla.
  rewrite (rngl_mul_opp_r Hop), (rngl_mul_1_r Hon).
  induction la as [| b]; intros; [ now right | cbn ].
  apply List.not_in_cons in Ha.
  destruct Ha as (Hab, Ha).
  apply List.NoDup_cons_iff in Hnd.
  destruct Hnd as (Hb, Hnd).
  specialize (IHla Ha Hnd).
  remember (a ?= b) as ab eqn:Hc; symmetry in Hc.
  destruct ab; [ now apply Nat.compare_eq_iff in Hc | easy | ].
  destruct IHla as [Haa| Haa]; rewrite Haa; [ now right | ].
  left; apply (rngl_opp_involutive Hop).
}
Qed.

Theorem ε_1_opp_1_NoDup :
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  ∀ σ, ε σ = 1%L ∨ ε σ = (-1)%L → List.NoDup σ.
Proof.
intros Hop H10 * Hσ.
destruct (ListDec.NoDup_dec Nat.eq_dec σ) as [H1| H1]; [ easy | ].
exfalso.
apply (ε_when_dup Hop) in H1.
rewrite H1 in Hσ.
destruct Hσ as [Hσ| Hσ]; symmetry in Hσ. {
  revert Hσ; apply (rngl_1_neq_0_iff Hon), H10.
} {
  rewrite <- (rngl_opp_0 Hop) in Hσ.
  apply (rngl_opp_inj Hop) in Hσ.
  revert Hσ; apply (rngl_1_neq_0_iff Hon), H10.
}
Qed.

Theorem NoDup_ε_square :
  rngl_has_opp T = true →
  ∀ σ, List.NoDup σ → (ε σ * ε σ = 1)%L.
Proof.
intros Hop * Hσ.
specialize (NoDup_ε_1_opp_1) as H1.
specialize (H1 Hop σ Hσ).
destruct H1 as [H1| H1]; rewrite H1. {
  apply (rngl_mul_1_l Hon).
} {
  rewrite rngl_mul_opp_opp; [ | easy ].
  apply (rngl_mul_1_l Hon).
}
Qed.

End a.
