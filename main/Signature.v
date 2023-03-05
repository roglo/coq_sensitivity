(* signatures *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Init.Nat.
Import List List.ListNotations.

Require Import Misc RingLike.
Require Import SortingFun SortRank PermutationFun.
Require Import IterMul PermutSeq.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

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

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%L
  | _ => (- 1%L)%L
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
     rngl_one := One;
     rngl_add _ _ := Zero;
     rngl_mul a b :=
       match a with
       | Zero => Zero
       | Minus_one => test_opp b
       | One => b
       end;
   rngl_opt_opp_or_subt := Some (inl test_opp);
   rngl_opt_inv_or_quot := None;
   rngl_opt_eqb := None;
   rngl_opt_le := None |}.

(* *)

Theorem minus_one_pow_mul_comm :
  rngl_has_opp = true →
  ∀ i x, (minus_one_pow i * x = x * minus_one_pow i)%L.
Proof.
intros Hop *.
unfold minus_one_pow.
remember (i mod 2) as k eqn:Hk; symmetry in Hk.
destruct k; [ now rewrite rngl_mul_1_r, rngl_mul_1_l | ].
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_opp_r Hop).
now rewrite rngl_mul_1_l, rngl_mul_1_r.
Qed.

Theorem minus_one_pow_succ :
  rngl_has_opp = true →
  ∀ i, minus_one_pow (S i) = (- minus_one_pow i)%L.
Proof.
intros Hop *.
unfold minus_one_pow.
remember (i mod 2) as k eqn:Hk; symmetry in Hk.
destruct k. {
  apply Nat.mod_divides in Hk; [ | easy ].
  destruct Hk as (k, Hk); subst i.
  rewrite <- Nat.add_1_l, Nat.mul_comm.
  now rewrite Nat.mod_add.
}
destruct k. {
  rewrite <- Nat.add_1_l.
  rewrite <- Nat.add_mod_idemp_r; [ | easy ].
  rewrite Hk; cbn.
  symmetry.
  now apply rngl_opp_involutive.
}
specialize (Nat.mod_upper_bound i 2) as H1.
assert (H : 2 ≠ 0) by easy.
specialize (H1 H); clear H.
rewrite Hk in H1.
flia H1.
Qed.

Theorem ε_app_cons :
  rngl_has_opp = true →
  ∀ n la lb,
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
  rngl_has_opp = true →
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
  rngl_has_opp = true →
  ∀ i, (minus_one_pow i * minus_one_pow i = 1)%L.
Proof.
intros Hop *.
unfold minus_one_pow.
destruct (i mod 2); [ apply rngl_mul_1_l | ].
now apply rngl_squ_opp_1.
Qed.

(* ε (σ₁ ° σ₂) = ε σ₁ * ε σ₂ *)

Theorem butn_permut_seq_with_len : ∀ n i l,
  permut_seq_with_len (S n) l
  → n = nth i l 0
  → i < length l
  → permut_seq_with_len n (butn i l).
Proof.
intros * Hp Hni Hil.
split. {
  apply permut_seq_iff.
  split. {
    intros j Hj.
    rewrite butn_length.
    destruct Hp as (Hp, Hl).
    apply Nat.ltb_lt in Hil; rewrite Hil.
    apply Nat.ltb_lt in Hil.
    rewrite Hl, Nat_sub_succ_1.
    apply permut_seq_iff in Hp.
    destruct Hp as (Hpl, Hpi).
    specialize (Hpl j) as Hjl.
    assert (H : j ∈ l) by now apply in_butn in Hj.
    specialize (Hjl H); clear H.
    rewrite Hl in Hjl.
    destruct (Nat.eq_dec j n) as [H| H]; [ | flia H Hjl ].
    subst j; clear Hjl; exfalso.
    assert (Hnni : n ≠ i). {
      intros H; move H at top; subst i.
      apply (In_nth _ _ 0) in Hj.
      rewrite butn_length, Hl in Hj.
      replace (n <? S n) with true in Hj by now symmetry; apply Nat.ltb_lt.
      rewrite Nat_sub_succ_1 in Hj.
      destruct Hj as (j & Hjn & Hnj); symmetry in Hnj.
      rewrite nth_butn in Hnj.
      apply Nat.leb_gt in Hjn.
      rewrite Hjn, Nat.add_0_r in Hnj.
      apply Nat.leb_gt in Hjn.
      specialize (NoDup_nat _ Hpi j n) as H2.
      assert (H : j < length l) by now rewrite Hl; flia Hjn.
      specialize (H2 H Hil); clear H.
      assert (H : nth j l 0 = nth n l 0) by now rewrite <- Hni.
      specialize (H2 H).
      now rewrite H2 in Hjn; apply Nat.lt_irrefl in Hjn.
    }
    unfold butn in Hj.
    apply in_app_or in Hj.
    destruct Hj as [Hini| Hini]. {
      apply (In_nth _ _ 0) in Hini.
      destruct Hini as (j & Hjl & Hjn).
      rewrite firstn_length, min_l in Hjl; [ | flia Hil ].
      specialize (NoDup_nat _ Hpi i j Hil) as H2.
      assert (H : j < length l) by flia Hjl Hil.
      specialize (H2 H); clear H.
      rewrite <- Hni in H2.
      rewrite List_nth_firstn in Hjn; [ | easy ].
      symmetry in Hjn.
      specialize (H2 Hjn).
      rewrite <- H2 in Hjl.
      now apply Nat.lt_irrefl in Hjl.
    } {
      apply (In_nth _ _ 0) in Hini.
      destruct Hini as (j & Hjl & Hjn).
      rewrite skipn_length in Hjl.
      rewrite List_nth_skipn in Hjn.
      specialize (NoDup_nat _ Hpi i (j + S i) Hil) as H2.
      assert (H : j + S i < length l) by flia Hjl.
      specialize (H2 H); clear H.
      rewrite <- Hni in H2.
      rewrite Hjn in H2.
      specialize (H2 eq_refl).
      flia H2.
    }
  } {
    apply nat_NoDup.
    rewrite butn_length.
    apply Nat.ltb_lt in Hil; rewrite Hil.
    apply Nat.ltb_lt in Hil.
    destruct Hp as (Hpp, Hpl).
    rewrite Hpl, Nat_sub_succ_1.
    intros j k Hj Hk Hjk.
    apply permut_seq_iff in Hpp.
    destruct Hpp as (Hp, Hpi).
    do 2 rewrite nth_butn in Hjk.
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
  rewrite butn_length.
  apply Nat.ltb_lt in Hil.
  destruct Hp as (Hpp, Hpl).
  now rewrite Hil, Hpl, Nat_sub_succ_1.
}
Qed.

Theorem permut_without_highest : ∀ n l,
  permut_seq_with_len (S n) l
  → ∃ i, i < length l ∧ nth i l 0 = n ∧ permut_seq_with_len n (butn i l).
Proof.
intros * Hl.
exists (nth n (isort_rank Nat.leb l) 0).
split. {
  rewrite <- (isort_rank_length Nat.leb).
  destruct Hl as (Hp, Hl).
  specialize (isort_rank_permut_seq_with_len Nat.leb _ Hl) as Hil.
  destruct Hil as (Hil, Hil').
  apply permut_seq_iff in Hil.
  apply Hil, nth_In.
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
  apply H4, nth_In.
  now rewrite isort_rank_length, H3.
}
Qed.

Theorem fold_comp_list : ∀ la lb, map (λ i, nth i la 0) lb = la ° lb.
Proof. easy. Qed.

Theorem fold_ε_cons : ∀ i q, (ε_aux i q * ε q)%L = ε (i :: q).
Proof. easy. Qed.

Theorem ε_aux_in :
  rngl_has_opp = true →
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

Theorem ε_aux_mul_comm :
  rngl_has_opp = true →
  ∀ i la a, (ε_aux i la * a = a * ε_aux i la)%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
specialize (ε_aux_in Hop i la) as H1.
destruct H1 as [H1| H1]. {
  rewrite <- H1.
  rewrite (rngl_mul_opp_l Hop), rngl_mul_1_l.
  rewrite (rngl_mul_opp_r Hop), rngl_mul_1_r.
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
  rngl_has_opp = true →
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
  rngl_has_opp = true →
  ∀ a b la,
  a < b
  → (ε_aux a la * ε (la ++ [b]))%L = (- ε (b :: la ++ [a]))%L.
Proof.
intros Hop * Hab.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
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
  rngl_has_opp = true
  → ∀ a b la,
  b < a
  → (ε_aux a la * ε (la ++ [b]))%L = ε (b :: la ++ [a]).
Proof.
intros Hop * Hc.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
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
  rngl_has_opp = true →
  ∀ a la, ε (a :: la) = (minus_one_pow (length la) * ε (la ++ [a]))%L.
Proof.
intros Hop *; cbn.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
revert a.
induction la as [| b]; intros; [ symmetry; apply rngl_mul_1_l | cbn ].
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
  rngl_has_opp = true →
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
  rngl_has_opp = true →
  ∀ la lb a,
  ε (la ++ a :: lb) = (minus_one_pow (length lb) * ε (la ++ lb ++ [a]))%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
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
  ∀ i j la lb,
  i < j
  → ε_aux i (la ++ j :: lb) = ε_aux i (la ++ lb).
Proof.
intros * Hij.
revert i j lb Hij.
induction la as [| a]; intros; cbn; [ | now rewrite IHla ].
now apply Nat.compare_lt_iff in Hij; rewrite Hij.
Qed.

Theorem ε_aux_app_cons_gt :
  rngl_has_opp = true →
  ∀ i j la lb,
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
  rngl_has_opp = true →
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
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
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
  rngl_has_opp = true →
  ∀ la lb,
  permut_seq_with_len (length la) lb
  → ε (la ° lb) = (ε la * ε lb)%L.
Proof.
intros Hop * Hbp.
remember (length la) as n eqn:Hla; symmetry in Hla.
revert lb Hbp la Hla.
induction n; intros; cbn. {
  destruct Hbp as (Hb, Hbl).
  apply length_zero_iff_nil in Hla, Hbl; subst la lb.
  symmetry; apply rngl_mul_1_l.
}
(* removing the highest value, "n" in "lb", permutation of {0..n} *)
specialize (permut_without_highest Hbp) as H1.
destruct H1 as (i & Hi & Hin & H1).
(* taking lb1 and lb2 such that lb=lb1++n::lb2 *)
specialize nth_split as H2.
specialize (H2 _ i lb 0 Hi).
destruct H2 as (lb1 & lb2 & Hlb & Hjl1).
rewrite Hin in Hlb.
(* proving that "lb1++lb2" is a permuation of {0..n-1} *)
rewrite Hlb in H1.
rewrite butn_app_cons in H1; [ | easy ].
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
  apply (In_nth _ _ 0) in Hj.
  destruct Hj as (k & Hnk & Hk).
  subst j.
  apply permut_seq_ub in H11.
  specialize (H11 (nth k (lb1 ++ lb2) 0)).
  rewrite H12 in H11.
  apply H11.
  now apply nth_In.
}
do 2 rewrite (minus_one_pow_mul_comm Hop).
rewrite rngl_mul_assoc.
(* so, this "(-1)^len(lb2)" can disappear *)
f_equal.
(* this operation makes the last (n-th) element of "la" appear appended
   to "la°(lb1++lb2)" *)
rewrite app_assoc.
rewrite <- comp_list_app_distr_l.
specialize (@app_removelast_last _ la 0) as H4.
assert (H : la ≠ []) by now intros H; rewrite H in Hla.
specialize (H4 H); clear H.
replace n with (length la - 1) by flia Hla.
rewrite <- List_last_nth.
(* we know that "la" without its last element (its n-th element) has
   length "n"... *)
assert (Hra : length (removelast la) = n). {
  apply (f_equal length) in H4.
  rewrite app_length, Nat.add_1_r in H4.
  rewrite Hla in H4.
  now apply Nat.succ_inj in H4.
}
(* and that "lb1++lb2" also has length "n" *)
assert (Hbbl : length (lb1 ++ lb2) = n). {
  apply (f_equal length) in Hlb.
  rewrite app_length in Hlb; cbn in Hlb.
  rewrite Nat.add_succ_r, <- app_length in Hlb.
  destruct Hbp as (Hbp1, Hbp2).
  rewrite Hbp2 in Hlb.
  now apply Nat.succ_inj in Hlb.
}
(* since "lb1++lb2" does not contain "n", the expression "la°(lb1++lb2)"
   can be replaced by "(la without its last)°(lb1++lb2)" *)
replace (la ° (lb1 ++ lb2)) with (removelast la ° (lb1 ++ lb2)). 2: {
  rewrite H4 at 2.
  unfold "°".
  apply map_ext_in.
  intros j Hj.
  rewrite app_nth1; [ easy | ].
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
specialize (H5 [] (removelast la ° (lb1 ++ lb2)) (last la 0)).
do 2 rewrite app_nil_l in H5.
rewrite comp_length in H5.
rewrite Hbbl in H5.
apply (f_equal (rngl_mul (minus_one_pow n))) in H5.
rewrite rngl_mul_assoc in H5.
rewrite (minus_one_pow_mul_same Hop) in H5.
rewrite rngl_mul_1_l in H5.
rewrite <- H5; cbn; clear H5.
(* ... and the right factor of the lhs, being
   "ε((la without last)°(lb1++lb2)", can be replaced using
   the induction hypothesis *)
rewrite (IHn (lb1 ++ lb2) H1 _ Hra).
do 2 rewrite rngl_mul_assoc.
(* these operation make "ε(lb1++lb2)" appear as factors in both sides
   of the goal, we can remove them *)
f_equal.
(* the lhs, "ε(la)", is "(-1)^n" times "ε(last la++all but last la)" *)
symmetry.
specialize (ε_app_cons2 Hop [] (removelast la) (last la 0)) as H5.
cbn - [ ε ] in H5.
rewrite Hra in H5.
rewrite <- app_removelast_last in H5; [ | now intros H; subst la ].
apply (f_equal (rngl_mul (minus_one_pow n))) in H5.
rewrite rngl_mul_assoc in H5.
rewrite (minus_one_pow_mul_same Hop) in H5.
rewrite rngl_mul_1_l in H5.
rewrite <- H5; cbn.
(* both sides now contain "(-1)^" and "ε(la without last)" that we can
   eliminate *)
rewrite <- rngl_mul_assoc; f_equal; cbn; f_equal.
(* the goal now contain equality between two "ε_aux (last la)" which
   can be proven saying when their second arguments are permutations
   the one to the other *)
apply (ε_aux_permut Hop).
unfold "°".
rewrite (List_map_nth_seq (removelast la) 0) at 1.
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

(*
Theorem ε_nil : ε [] = 1%L.
Proof. easy. Qed.

Theorem ε_aux_map_S : ∀ i l,  ε_aux (S i) (map S l) = ε_aux i l.
Proof.
intros.
revert i.
induction l as [| j]; intros; [ easy | cbn ].
rewrite IHl.
now destruct (i ?= j).
Qed.

Theorem ε_map_S : ∀ l, ε (map S l) = ε l.
Proof.
intros.
induction l as [| i]; [ easy | cbn ].
rewrite IHl.
f_equal.
apply ε_aux_map_S.
Qed.
*)

(*
Theorem minus_one_pow_succ_succ :
  rngl_has_opp = true →
  ∀ i, minus_one_pow (S (S i)) = minus_one_pow i.
Proof.
intros Hop *.
rewrite minus_one_pow_succ; [ | easy ].
rewrite minus_one_pow_succ; [ | easy ].
now apply rngl_opp_involutive.
Qed.

Theorem minus_one_pow_add :
  rngl_has_opp = true →
  ∀ i j, minus_one_pow (i + j) = (minus_one_pow i * minus_one_pow j)%L.
Proof.
intros Hop *.
revert j.
induction i; intros; [ now cbn; rewrite rngl_mul_1_l | ].
rewrite Nat.add_succ_comm.
rewrite IHi.
rewrite minus_one_pow_succ; [ | easy ].
rewrite minus_one_pow_succ; [ | easy ].
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
easy.
Qed.

(* signature of the k-th permutation of the symmetric group *)

Fixpoint ε_permut n k :=
  match n with
  | 0 => 1%L
  | S n' => (minus_one_pow (k / fact n') * ε_permut n' (k mod fact n'))%L
  end.

Theorem rngl_product_product_if : ∀ b e f,
  (∏ (i = b, e), ∏ (j = b, e), if i <? j then f i j else 1)%L =
  (∏ (i = b, e), ∏ (j = i + 1, e), f i j)%L.
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
  rngl_has_opp = true →
  ∀ i j,
  (rngl_of_nat j - rngl_of_nat i)%L =
     if i <? j then rngl_of_nat (j - i)
     else (- rngl_of_nat (i - j))%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hop'.
specialize (Hop' (or_introl Hop)).
move Hop' before Hop.
rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]. {
  revert j Hij.
  induction i; intros; cbn. {
    rewrite rngl_sub_0_r; f_equal; [ | easy ].
    now destruct j.
  }
  destruct j; [ easy | cbn ].
  rewrite rngl_add_sub_simpl_l; [ | easy ].
  apply IHi.
  now apply Nat.succ_lt_mono in Hij.
} {
  apply Nat.nlt_ge in Hij.
  revert j Hij.
  induction i; intros; cbn. {
    rewrite rngl_sub_0_r; f_equal; [ | easy ].
    rewrite rngl_opp_0; [ | easy ].
    now apply Nat.le_0_r in Hij; subst j.
  }
  destruct j. {
    unfold rngl_sub; rewrite Hop; cbn.
    now rewrite rngl_add_0_l.
  }
  cbn.
  rewrite rngl_add_sub_simpl_l; [ | easy ].
  apply IHi.
  now apply Nat.succ_le_mono in Hij.
}
Qed.

Theorem rngl_of_nat_add : ∀ a b,
  (rngl_of_nat a + rngl_of_nat b)%L = rngl_of_nat (a + b).
Proof.
intros.
induction a; [ apply rngl_add_0_l | ].
now cbn; rewrite <- rngl_add_assoc; f_equal.
Qed.

Theorem rngl_of_nat_mul :
  rngl_has_opp_or_subt = true →
  ∀ a b, (rngl_of_nat a * rngl_of_nat b)%L = rngl_of_nat (a * b).
Proof.
intros Hom *.
induction a; [ now apply rngl_mul_0_l | cbn ].
rewrite rngl_mul_add_distr_r.
rewrite rngl_mul_1_l.
rewrite IHa.
apply rngl_of_nat_add.
Qed.

Theorem rngl_product_rngl_of_nat :
  rngl_has_opp_or_subt = true →
  ∀ n, (∏ (i = 1, n), rngl_of_nat i)%L = rngl_of_nat (fact n).
Proof.
intros Hom *.
induction n. {
  rewrite rngl_product_empty; [ | easy ].
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

Theorem rngl_product_product_div_eq_1 :
  rngl_has_opp_or_subt = true →
  rngl_mul_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_characteristic ≠ 1 →
  rngl_has_eqb = true →
  ∀ n f g,
  (∀ i j, i < n → j < n → g i j ≠ 0%L)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), (f i j / g i j)))%L = 1%L
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), f i j))%L =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), g i j))%L.
Proof.
intros Hom Hic Hiv Hin H10 Heq * Hg Hs.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hiv)).
move Hiq before Hiv.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
remember (∏ (i ∈ _), _)%L as a eqn:Ha in |-*.
remember (∏ (i ∈ _), _)%L as b eqn:Hb in |-*.
remember (rngl_eqb b 0%L) as bz eqn:Hbz; symmetry in Hbz.
destruct bz. {
  apply (rngl_eqb_eq Heq) in Hbz.
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
apply (rngl_eqb_neq Heq) in Hbz.
apply rngl_mul_cancel_r with (c := (b⁻¹)%L); [ easy | | ]. {
  intros Hbiz.
  apply (f_equal (rngl_mul b)) in Hbiz.
  rewrite fold_rngl_div in Hbiz; [ | easy ].
  rewrite rngl_div_diag in Hbiz; [ | easy | easy ].
  rewrite rngl_mul_0_r in Hbiz; [ | easy ].
  now apply rngl_1_neq_0_iff in Hbiz.
}
remember (_ * _)%L as c.
rewrite fold_rngl_div; [ | easy ].
rewrite rngl_div_diag; [ | easy | easy ].
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
erewrite (rngl_product_list_permut _ Nat.eqb_eq) with
    (la := rev _); [ | easy | ]. 2: {
  apply (permutation_rev_l Nat.eqb_eq).
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
  erewrite (rngl_product_list_permut _ Nat.eqb_eq) with
      (la := rev _); [ | easy | ]. 2: {
    apply (permutation_rev_l Nat.eqb_eq).
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
  rngl_mul_is_comm = true →
  ∀ n f,
  (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n), f i j)%L =
  ((∏ (i ∈ seq 0 n), f i i) *
   (∏ (i ∈ seq 0 (n - 1)), ∏ (j = i + 1, n - 1), (f i j * f j i)))%L.
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
rewrite (rngl_product_shift 1); [ | flia Hnz Hn1 ].
rewrite Nat.sub_diag.
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
  rewrite Nat_succ_sub_succ_r by flia Hnz Hn1 Hi.
  rewrite seq_S.
  rewrite Nat.add_comm, Nat.sub_add; [ | flia Hnz Hn1 Hi ].
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
  rewrite <- Nat_succ_sub_succ_r; [ | flia Hnz ].
  now rewrite Nat.sub_0_r, Nat.add_1_r.
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
rewrite (rngl_product_shift 1); [ | flia Hnz Hn1 ].
rewrite Nat.sub_diag.
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
rewrite (rngl_product_shift 1); [ | flia Hnz Hn1 ].
rewrite Nat.sub_diag.
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
  rngl_mul_is_comm = true →
  rngl_has_inv = true →
  rngl_characteristic ≠ 1 →
  permut_seq_with_len n σ
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%L)
  → ∀ i j, i < n → j < n →
    ((if nth i σ O <? nth j σ O then f i j else 1) /
      (if i <? j then f i j else 1) *
     ((if nth j σ O <? nth i σ O then f j i else 1) /
      (if j <? i then f j i else 1)))%L = 1%L.
Proof.
intros * Hic Hin H10 (Hp, Hn) Hfij Hfijnz * Hlin Hljn.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hin)).
move Hiq before Hin.
do 4 rewrite if_ltb_lt_dec.
destruct (lt_dec (nth i σ 0) (nth j σ 0)) as [H1| H1]. {
  destruct (lt_dec (nth j σ 0) (nth i σ 0)) as [H| H]; [ flia H1 H | ].
  clear H.
  destruct (lt_dec i j) as [H3| H3]. {
    destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
    rewrite Hfij.
    rewrite rngl_div_diag; [ | easy | ]. 2: {
      apply Hfijnz; [ easy | easy | flia H3 ].
    }
    rewrite rngl_mul_1_l.
    apply rngl_div_diag; [ easy | ].
    now apply rngl_1_neq_0_iff.
  }
  destruct (lt_dec j i) as [H4| H4]. {
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | easy | easy ].
    rewrite rngl_div_1_l; [ | easy ].
    rewrite fold_rngl_div; [ | easy ].
    apply rngl_div_diag; [ easy | ].
    apply Hfijnz; [ easy | easy | flia H4 ].
  }
  exfalso.
  apply Nat.nlt_ge in H3.
  apply Nat.nlt_ge in H4.
  apply Nat.le_antisymm in H3; [ | easy ].
  subst j; flia H1.
}
destruct (lt_dec (nth j σ 0) (nth i σ 0)) as [H2| H2]. {
  destruct (lt_dec i j) as [H3| H3]. {
    destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | easy | easy ].
    rewrite rngl_div_1_l; [ | easy ].
    rewrite rngl_mul_comm; [ | easy ].
    rewrite fold_rngl_div; [ | easy ].
    apply rngl_div_diag; [ easy | ].
    apply Hfijnz; [ easy | easy | flia H3 ].
  }
  destruct (lt_dec j i) as [H4| H4]. {
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | easy | easy ].
    rewrite rngl_mul_1_l.
    apply rngl_div_diag; [ easy | ].
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
  apply permut_seq_iff in Hp.
  destruct Hp as (_, Hp).
  apply (NoDup_nat _ Hp) in H1; [ | now rewrite Hn | now rewrite Hn ].
  flia H1 H3.
}
destruct (lt_dec j i) as [H4| H4]. {
  apply permut_seq_iff in Hp.
  destruct Hp as (_, Hp).
  apply (NoDup_nat _ Hp) in H1; [ | now rewrite Hn | now rewrite Hn ].
  flia H1 H4.
}
rewrite rngl_div_1_r; [ | easy | easy ].
apply rngl_mul_1_l.
Qed.

Theorem product_product_if_permut_div :
  rngl_mul_is_comm = true →
  rngl_characteristic ≠ 1 →
  rngl_has_inv = true →
  ∀ n σ f,
  permut_seq_with_len n σ
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%L)
  → (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n),
      ((if nth i σ O <? nth j σ O then f i j else 1) /
       (if i <? j then f i j else 1)))%L =
     1%L.
Proof.
intros Hic H10 Hin * (Hp, Hn) Hfij Hfijnz.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hin)).
move Hiq before Hin.
rewrite rngl_product_product_by_swap; [ | easy ].
rewrite all_1_rngl_product_list_1; [ | easy | ]. 2: {
  intros i Hi.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec _ _) as [H| H]; [ flia H | clear H ].
  destruct (lt_dec _ _) as [H| H]; [ flia H | clear H ].
  now apply rngl_div_1_r.
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
  rngl_has_opp_or_subt = true →
  rngl_mul_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_characteristic ≠ 1 →
  rngl_has_eqb = true →
  ∀ n σ f,
  permut_seq_with_len n σ
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%L)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n),
        if nth i σ O <? nth j σ O then f i j else 1))%L =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n),
        if i <? j then f i j else 1))%L.
Proof.
intros Hom Hic Hid Hin H10 Heq * (Hp, Hn) Hfij Hfijnz.
apply rngl_product_product_div_eq_1; try easy. {
  intros i j Hi Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | now apply rngl_1_neq_0_iff ].
  apply Hfijnz; [ easy | easy | flia Hij ].
}
now apply product_product_if_permut_div.
Qed.

Theorem rngl_product_product_abs_diff_div_diff : in_charac_0_field →
  ∀ p,
  permut_seq p
  → ∏ (i = 0, length p - 1),
    (∏ (j = 0, length p - 1),
     (if i <? j then
        rngl_of_nat (abs_diff (nth j p O) (nth i p O)) /
        rngl_of_nat (j - i)
      else 1)) = 1%L.
Proof.
intros Hif * Hp.
destruct Hif as (Hic, Hop, Hin, Hit, Hde, Hch).
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hin)).
move Hiq before Hin.
destruct (le_dec (length p) 1) as [Hn1| Hn1]. {
  replace (length p - 1) with 0 by flia Hn1.
  now do 2 rewrite rngl_product_only_one.
}
assert (H10 : rngl_characteristic ≠ 1) by now rewrite Hch.
rewrite rngl_product_product_if.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_div_distr; try easy.
  intros j Hj.
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
cbn.
rewrite rngl_product_div_distr; try easy. 2: {
  intros i Hi H.
  apply (rngl_product_integral Hos Hit H10) in H.
  destruct H as (j & Hj & Hji).
  apply eq_rngl_of_nat_0 in Hji; [ | easy ].
  flia Hj Hji.
}
apply eq_rngl_div_1; [ easy | | ]. {
  intros H.
  apply (rngl_product_integral Hos Hit H10) in H.
  destruct H as (i & Hi & H).
  apply (rngl_product_integral Hos Hit H10) in H.
  destruct H as (j & Hj & H).
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
rewrite <- rngl_product_product_if; symmetry.
rewrite <- rngl_product_product_if; symmetry.
apply Nat.nle_gt in Hn1.
(* changt of var *)
rewrite rngl_product_change_var with
  (g := λ i, nth i (isort_rank Nat.leb p) 0) (h := λ i, nth i p 0). 2: {
  intros i Hi.
  apply permut_isort_permut; [ easy | flia Hi Hn1 ].
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hn1 ].
rewrite Nat_sub_succ_1.
rewrite <- List_map_nth_seq.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_var with
    (g := λ i, nth i (isort_rank Nat.leb p) 0) (h := λ i, nth i p 0). 2: {
    intros j Hj.
    apply permut_isort_permut; [ easy | flia Hj Hn1 ].
  }
  rewrite <- Nat.sub_succ_l; [ | flia Hn1 ].
  rewrite Nat_sub_succ_1, Nat.sub_0_r.
  rewrite <- List_map_nth_seq.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (u & Hu & Hui).
  replace (nth (nth i _ 0) _ 0) with i. 2: {
    symmetry.
    apply permut_permut_isort; [ easy | ].
    rewrite <- Hui.
    apply permut_seq_ub; [ easy | now apply nth_In ].
  }
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    apply (In_nth _ _ 0) in Hj.
    destruct Hj as (v & Hv & Hvj).
    replace (nth (nth j _ 0) _ 0) with j. 2: {
      symmetry.
      apply permut_permut_isort; [ easy | ].
      rewrite <- Hvj.
      apply permut_seq_ub; [ easy | now apply nth_In ].
    }
    easy.
  }
  cbn - [ "<?" ].
  easy.
}
cbn - [ "<?" ].
rewrite (rngl_product_list_permut _ Nat.eqb_eq) with
    (lb := seq 0 (length p)); [ | easy | easy ].
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  now rewrite (rngl_product_list_permut _ Nat.eqb_eq) with
    (lb := seq 0 (length p)).
}
cbn - [ "<?" ].
rewrite product_product_if_permut; try easy; cycle 1. {
  now apply (isort_rank_permut_seq_with_len _ (length p)).
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
rewrite rngl_product_seq_product; [ | flia Hn1 ].
rewrite Nat.add_0_l.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_seq_product; [ | flia Hn1 ].
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

Theorem transposition_permut_seq_with_len : ∀ p q n,
  p < n → q < n → permut_seq_with_len n (map (transposition p q) (seq 0 n)).
Proof.
intros * Hp Hq.
split. {
  apply permut_seq_iff.
  split. {
    intros i Hi.
    unfold transposition.
    rewrite map_length, seq_length.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite <- Hji.
    now apply transposition_lt.
  } {
    apply nat_NoDup.
    rewrite List_map_seq_length.
    intros i j Hi Hj Hs.
    unfold transposition in Hs.
    rewrite (List_map_nth' 0) in Hs; [ | now rewrite seq_length ].
    rewrite (List_map_nth' 0) in Hs; [ | now rewrite seq_length ].
    rewrite seq_nth in Hs; [ | easy ].
    rewrite seq_nth in Hs; [ | easy ].
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
now rewrite map_length, seq_length.
Qed.
*)

(*
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
  apply rngl_mul_1_l.
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
  rngl_has_opp = true →
  ∀ i p q,
  (∀ j k, j ∈ i :: p → k ∈ q → k < j)
  → ε_aux i (p ++ q) = (minus_one_pow (length q) * ε_aux i p)%L.
Proof.
intros Hop * Hpq.
revert i q Hpq.
induction p as [| j]; intros; cbn. {
  rewrite rngl_mul_1_r.
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
  now apply rngl_has_opp_or_subt_iff; left.
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
*)

(*
Theorem ε_app2 :
  rngl_has_opp = true →
  ∀ p q,
  (∀ i j, i ∈ p → j ∈ q → j < i)
  → ε (p ++ q) = (minus_one_pow (length p * length q) * ε p * ε q)%L.
Proof.
intros Hop * Hpq.
revert q Hpq.
induction p as [| i]; intros. {
  cbn; symmetry; f_equal.
  now do 2 rewrite rngl_mul_1_l.
}
cbn.
rewrite IHp. 2: {
  intros j k Hj Hk.
  apply Hpq; [ now right | easy ].
}
do 3 rewrite rngl_mul_assoc.
f_equal; f_equal.
rewrite (minus_one_pow_add Hop).
do 2 rewrite <- (minus_one_pow_mul_comm Hop).
rewrite <- rngl_mul_assoc; f_equal.
now apply ε_aux_app2.
Qed.

Theorem ε_seq : ∀ sta len, ε (seq sta len) = 1%L.
Proof.
intros.
revert sta.
induction len; intros; [ easy | ].
rewrite seq_S.
rewrite ε_app. 2: {
  intros * Hi Hj.
  apply in_seq in Hi.
  destruct Hj as [Hj| ]; [ now subst j | easy ].
}
cbn.
do 2 rewrite rngl_mul_1_r.
apply IHlen.
Qed.
*)

(*
Theorem transposition_signature_lt :
  rngl_has_opp = true →
  ∀ n p q,
  p < q
  → q < n
  → ε (map (transposition p q) (seq 0 n)) = (-1)%L.
Proof.
intros Hop * Hpq Hq.
unfold transposition.
rewrite (List_seq_cut p). 2: {
  apply in_seq.
  split; [ easy | cbn ].
  now transitivity q.
}
rewrite (List_seq_cut q (S p)). 2: {
  apply in_seq; cbn.
  split; [ easy | flia Hq ].
}
rewrite Nat.sub_0_r, Nat.add_0_l.
replace (S p + (n - S p) - S q) with (n - S q) by flia Hpq.
do 4 rewrite map_app.
cbn.
do 2 rewrite Nat.eqb_refl.
replace (q =? p) with false. 2: {
  symmetry; apply Nat.eqb_neq.
  intros H; subst q.
  now apply Nat.lt_irrefl in Hpq.
}
erewrite map_ext_in. 2: {
  intros i Hi.
  apply in_seq in Hi; cbn in Hi.
  destruct Hi as (_, Hi).
  replace (i =? q) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hpq Hi.
  }
  apply Nat.lt_neq in Hi.
  apply Nat.eqb_neq in Hi; rewrite Hi.
  easy.
}
rewrite map_id.
erewrite map_ext_in. 2: {
  intros i Hi.
  apply in_seq in Hi; cbn in Hi.
  replace (S (p + (q - S p))) with q in Hi by flia Hpq.
  replace (i =? p) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hi.
  }
  replace (i =? q) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hi.
  }
  easy.
}
rewrite map_id.
erewrite map_ext_in. 2: {
  intros i Hi.
  apply in_seq in Hi; cbn in Hi.
  replace (S (q + _)) with n in Hi by flia Hpq Hq.
  replace (i =? p) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hpq Hi.
  }
  replace (i =? q) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hi.
  }
  easy.
}
rewrite map_id.
rewrite ε_app. 2: {
  intros * Hi Hj.
  apply in_seq in Hi; cbn in Hi; destruct Hi as (_, Hi).
  destruct Hj as [Hj| Hj]; [ now subst j; transitivity p | ].
  apply in_app_iff in Hj.
  destruct Hj as [Hj| Hj]; [ apply in_seq in Hj; flia Hi Hj | ].
  destruct Hj as [Hj| Hj]; [ now subst j | ].
  apply in_seq in Hj; flia Hi Hpq Hj.
}
rewrite ε_seq, rngl_mul_1_l.
rewrite List_cons_is_app.
rewrite (List_cons_is_app p).
do 2 rewrite app_assoc.
rewrite ε_app. 2: {
  intros i j Hi Hj.
  apply in_seq in Hj.
  rewrite Nat.add_comm, Nat.sub_add in Hj; [ | easy ].
  apply in_app_iff in Hi.
  destruct Hi as [Hi| Hi]. {
    apply in_app_iff in Hi.
    destruct Hi as [Hi| Hi]. {
      destruct Hi; [ now subst i | easy ].
    }
    apply in_seq in Hi.
    rewrite Nat.add_comm, Nat.sub_add in Hi; [ | easy ].
    now transitivity q.
  }
  destruct Hi; [ subst i | easy ].
  now transitivity q.
}
rewrite ε_seq, rngl_mul_1_r.
clear n Hq.
rewrite (ε_app2 Hop). 2: {
  intros i j Hi Hj.
  destruct Hj; [ subst j | easy ].
  apply in_app_iff in Hi.
  destruct Hi as [Hi| Hi]. {
    destruct Hi; [ now subst i | easy ].
  }
  now apply in_seq in Hi.
}
rewrite app_length, seq_length.
cbn - [ ε ].
rewrite Nat.mul_1_r.
replace (ε [p]) with 1%L by now cbn; rewrite rngl_mul_1_l.
rewrite rngl_mul_1_r.
rewrite (minus_one_pow_succ Hop).
rewrite (rngl_mul_opp_l Hop); f_equal.
rewrite List_cons_is_app.
rewrite (ε_app2 Hop). 2: {
  intros i j Hi Hj.
  destruct Hi; [ subst i | easy ].
  apply in_seq in Hj.
  now rewrite Nat.add_comm, Nat.sub_add in Hj.
}
rewrite ε_seq, rngl_mul_1_r.
rewrite seq_length; cbn.
rewrite Nat.add_0_r.
do 2 rewrite rngl_mul_1_r.
now apply minus_one_pow_mul_same.
Qed.

Theorem transposition_signature :
  rngl_has_opp = true →
  ∀ n p q,
  p ≠ q
  → p < n
  → q < n
  → ε (map (transposition p q) (seq 0 n)) = (-1)%L.
Proof.
intros Hop * Hpq Hp Hq.
destruct (lt_dec p q) as [Hpq'| Hpq']. {
  now apply transposition_signature_lt.
}
apply Nat.nlt_ge in Hpq'.
assert (H : q < p) by flia Hpq Hpq'.
rewrite <- (transposition_signature_lt Hop H Hp).
f_equal.
apply map_ext_in.
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
  rewrite map_length.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  subst i.
  rewrite Hp22, <- Hp12.
  apply permut_seq_ub; [ easy | ].
  apply nth_In.
  apply permut_seq_iff in Hp21.
  apply Hp21 in Hj.
  congruence.
} {
  unfold comp_list.
  apply nat_NoDup.
  rewrite map_length.
  intros i j Hi Hj.
  rewrite (List_map_nth' 0); [ | easy ].
  rewrite (List_map_nth' 0); [ | easy ].
  intros Hij.
  apply permut_seq_iff in Hp11.
  apply permut_seq_iff in Hp21.
  destruct Hp11 as (_, Hp11).
  apply (NoDup_nat _ Hp11) in Hij; cycle 1. {
    rewrite Hp12, <- Hp22.
    now apply Hp21, nth_In.
  } {
    rewrite Hp12, <- Hp22.
    now apply Hp21, nth_In.
  }
  destruct Hp21 as (_, Hp21).
  now apply (NoDup_nat _ Hp21) in Hij.
}
Qed.

Arguments comp_permut_seq n%nat [σ₁ σ₂]%list_scope.

Theorem comp_permut_seq_with_len : ∀ n σ₁ σ₂,
  permut_seq_with_len n σ₁
  → permut_seq_with_len n σ₂
  → permut_seq_with_len n (σ₁ ° σ₂).
Proof.
intros * Hp1 Hp2.
split; [ now apply (comp_permut_seq n) | ].
unfold "°".
rewrite map_length.
now destruct Hp2.
Qed.
*)

(*
Theorem map_nth_permut_seq : ∀ n la lb,
  permut_seq_with_len n la
  → permut_seq_with_len n lb
  → permut_seq (map (λ i, nth i la 0) lb).
Proof.
intros * (Hap, Hal) (Hbp, Hbl).
apply permut_seq_iff.
split. {
  intros j Hj.
  apply in_map_iff in Hj.
  destruct Hj as (k & Hkj & Hk).
  rewrite <- Hkj.
  rewrite map_length, Hbl, <- Hal.
  apply permut_seq_iff in Hap.
  apply Hap, nth_In.
  rewrite Hal, <- Hbl.
  apply permut_seq_iff in Hbp.
  now apply Hbp.
} {
  apply nat_NoDup.
  rewrite map_length.
  intros j k Hj Hk Hjk.
  assert (Hab : permut_seq_with_len n (la ° lb)) by now apply comp_permut_seq_with_len.
  destruct Hab as (Hab, _).
  apply permut_seq_iff in Hab.
  destruct Hab as (_, Hab).
  apply (NoDup_nat _ Hab) in Hjk; [ easy | | ]; now rewrite comp_length.
}
Qed.
*)

(*
Theorem permut_comp_cancel_l : ∀ n la lb lc,
  NoDup la
  → length la = n
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
  apply length_zero_iff_nil in Hb, Hc.
  congruence.
}
apply List_eq_iff in Hbc.
destruct Hbc as (_, Hbc).
apply List_eq_iff.
split; [ destruct Hb, Hc; congruence | ].
intros d i.
unfold "°" in Hbc.
assert (H : ∀ i, nth (nth i lb 0) la 0 = nth (nth i lc 0) la 0). {
  intros j.
  destruct (lt_dec j n) as [Hjn| Hjn]. 2: {
    apply Nat.nlt_ge in Hjn.
    rewrite (nth_overflow lb); [ | destruct Hb; congruence ].
    rewrite (nth_overflow lc); [ | destruct Hc; congruence ].
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
  rewrite nth_overflow; [ | destruct Hb; congruence ].
  rewrite nth_overflow; [ | destruct Hc; congruence ].
  easy.
}
specialize (Hbc i).
apply (NoDup_nat _ Ha) in Hbc; cycle 1. {
  destruct Hb as (Hbp, Hbl).
  rewrite Hal, <- Hbl.
  apply permut_seq_iff in Hbp.
  apply Hbp, nth_In.
  congruence.
} {
  destruct Hc as (Hcp, Hcl).
  rewrite Hal, <- Hcl.
  apply permut_seq_iff in Hcp.
  apply Hcp, nth_In.
  congruence.
}
rewrite nth_indep with (d' := 0); [ | destruct Hb; congruence ].
symmetry.
rewrite nth_indep with (d' := 0); [ | destruct Hc; congruence ].
now symmetry.
Qed.

Theorem permut_comp_cancel_r : ∀ n la lb lc,
  length la = n
  → length lb = n
  → permut_seq_with_len n lc
  → la ° lc = lb ° lc ↔ la = lb.
Proof.
intros * Hal Hbl Hc.
split; [ | now intros; subst la ].
intros Hab.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  apply length_zero_iff_nil in Hal, Hbl.
  congruence.
}
apply List_eq_iff in Hab.
destruct Hab as (_, Hab).
apply List_eq_iff.
split; [ congruence | ].
intros d i.
specialize (Hab d (nth i (isort_rank Nat.leb lc) 0)).
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
  rewrite nth_overflow; [ | now rewrite Hal ].
  rewrite nth_overflow; [ | now rewrite Hbl ].
  easy.
}
rewrite <- Hcl in Hin.
rewrite permut_permut_isort in Hab; [ | easy | easy ].
rewrite Hcl, <- Hal in Hin.
rewrite nth_indep with (d' := 0); [ symmetry | easy ].
rewrite Hal, <- Hbl in Hin.
rewrite nth_indep with (d' := 0); [ symmetry | easy ].
easy.
Qed.

Theorem comp_1_l : ∀ n l, AllLt l n → seq 0 n ° l = l.
Proof.
intros * Hp.
unfold "°".
erewrite map_ext_in. 2: {
  intros i Hi.
  rewrite seq_nth; [ | now apply Hp ].
  now apply Nat.add_0_l.
}
apply map_id.
Qed.

Theorem comp_1_r : ∀ n la,
  length la = n
  → la ° seq 0 n = la.
Proof.
intros * Hl.
subst n.
unfold "°"; cbn.
symmetry.
apply List_map_nth_seq.
Qed.

Arguments comp_1_r n%nat [la]%list.

Theorem collapse_permut_seq_with_len : ∀ l, permut_seq_with_len (length l) (collapse l).
Proof.
intros.
apply isort_rank_permut_seq_with_len.
apply isort_rank_length.
Qed.

Theorem permut_isort_rank_involutive : ∀ la,
  permut_seq la
  → isort_rank Nat.leb (isort_rank Nat.leb la) = la.
Proof.
intros * Hp.
remember (isort_rank Nat.leb la) as lb eqn:Hlb.
apply (@permut_comp_cancel_r (length lb)) with (lc := lb). {
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
  i < length l
  → j < length l
  → nth i l 0 < nth j l 0
  → nth i (collapse l) 0 < nth j (collapse l) 0.
Proof.
intros l j i Hj Hi Hc2.
specialize (collapse_permut_seq_with_len l) as Hc.
specialize (isort_rank_permut_seq_with_len Nat.leb (length l) eq_refl) as Hr.
apply Nat.nle_gt; intros Hc1.
destruct (Nat.eq_dec (nth i (collapse l) 0) (nth j (collapse l) 0))
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
assert (H' : nth i (collapse l) 0 < nth j (collapse l) 0) by flia Hc1 H.
clear Hc1 H; rename H' into Hc1.
unfold collapse in Hc1.
remember (isort_rank Nat.leb l) as lrank eqn:Hlr.
remember (nth i (collapse l) 0) as i' eqn:Hi'.
assert (Hii' : i = nth i' lrank 0). {
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
  apply Hca, nth_In.
  now rewrite Hcl.
}
remember (nth j (collapse l) 0) as j' eqn:Hj'.
assert (Hjj' : j = nth j' lrank 0). {
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
  apply Hca, nth_In.
  now rewrite Hcl.
}
rewrite Hii', Hjj' in Hc2.
rewrite Hlr in Hc2.
assert (Hi'l : i' < length l). {
  rewrite Hi'.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  rewrite Hcl in Hca.
  apply Hca, nth_In.
  now rewrite collapse_length.
}
assert (Hj'l : j' < length l). {
  rewrite Hj'.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  rewrite Hcl in Hca.
  apply Hca, nth_In.
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
rewrite map_length, Hlr, isort_rank_length in H2.
specialize (H2 i' j' Hi'l Hj'l Hc1).
apply Nat.leb_le in H2.
rewrite <- Hlr in H2.
rewrite (isort_isort_rank _ 0) in Hc2.
rewrite <- Hlr in Hc2.
now apply Nat.nle_gt in Hc2.
Qed.

Theorem collapse_keeps_order : ∀ l,
  NoDup l
  → ∀ i j,  i < length l → j < length l
  → (nth i (collapse l) 0 ?= nth j (collapse l) 0) =
    (nth i l 0 ?= nth j l 0).
Proof.
intros * Hnd * Hi Hj.
remember (nth i (collapse l) 0 ?= nth j (collapse l) 0) as c1 eqn:Hc1.
remember (nth i l 0 ?= nth j l 0) as c2 eqn:Hc2.
specialize (collapse_permut_seq_with_len l) as Hc.
specialize (isort_rank_permut_seq_with_len Nat.leb (length l) eq_refl) as Hr.
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
  ∀ i j,  i < length la → j < length la →
  (nth i la 0 ?= nth j la 0) = (nth i lb 0 ?= nth j lb 0).

Theorem ε_keep_order :
  ∀ la lb, keep_order la lb → length la = length lb → ε la = ε lb.
Proof.
intros * Hko Hab.
revert lb Hko Hab.
induction la as [| a]; intros. {
  symmetry in Hab.
  now apply length_zero_iff_nil in Hab; subst lb.
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
  now apply length_zero_iff_nil in Hab; subst lb.
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

Theorem ε_collapse_ε :
  rngl_has_opp_or_subt = true →
  ∀ l, NoDup l → ε (collapse l) = ε l.
Proof.
intros Hos * Hnd.
apply ε_keep_order; [ | apply collapse_length ].
intros i j Hi Hj.
rewrite collapse_length in Hi, Hj.
now apply (collapse_keeps_order Hnd).
Qed.

Theorem permut_isort : ∀ ord,
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
apply (permutation_trans Nat.eqb_eq) with (lb := seq 0 n). {
  now destruct Hp as (Hp1, Hp2); rewrite <- Hp2.
} {
  destruct Hq as (Hq1, Hq2); rewrite <- Hq2.
  now apply (permutation_sym Nat.eqb_eq).
}
Qed.

Theorem isort_comp_permut_r : ∀ l p,
  permut_seq_with_len (length l) p
  → isort Nat.leb (l ° p) = isort Nat.leb l.
Proof.
intros * Hp.
symmetry.
rewrite <- (comp_1_r (length l) eq_refl) at 1.
specialize (permut_isort Nat_leb_antisym Nat_leb_trans) as H1.
specialize (H1 Nat_leb_total_relation).
apply (H1 (length l)); [ | easy ].
apply seq_permut_seq_with_len.
Qed.

Theorem permut_isort_rank_comp : ∀ n la lb,
  NoDup la
  → length la = n
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
    now apply Hba, nth_In.
  } {
    rewrite Hal, <- Hbl.
    now apply Hba, nth_In.
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

Arguments permut_isort_rank_comp n%nat [la lb]%list.

Theorem permut_collapse : ∀ la,
  permut_seq la
  → collapse la = la.
Proof.
intros * Ha.
unfold collapse.
now apply permut_isort_rank_involutive.
Qed.

Theorem collapse_comp : ∀ la lb,
  NoDup la
  → permut_seq lb
  → length la = length lb
  → collapse (la ° lb) = collapse la ° lb.
Proof.
intros * Ha Hb Hab.
unfold collapse.
symmetry.
rewrite <- (permut_isort_rank_involutive Hb) at 1.
rewrite (permut_isort_rank_comp (length lb)); [ | easy | easy | easy ].
rewrite (permut_isort_rank_comp (length lb)); [ easy | | | ]. {
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
destruct (lt_dec i (length la)) as [Hila| Hila]. 2: {
  apply Nat.nlt_ge in Hila.
  rewrite nth_overflow; [ | now rewrite map_length, collapse_length ].
  now rewrite nth_overflow.
}
rewrite nth_indep with (d' := 0). 2: {
  now rewrite map_length, collapse_length.
}
symmetry.
rewrite nth_indep with (d' := 0); [ | easy ].
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
  permut_seq_with_len (length la) lb
  → NoDup la
  ↔ NoDup (la ° lb).
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
    now apply Hbp, nth_In.
  } {
    rewrite <- Hbl.
    apply permut_seq_iff in Hbp.
    now apply Hbp, nth_In.
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
  remember (nth i (isort_rank Nat.leb lb) 0) as i' eqn:Hi'.
  remember (nth j (isort_rank Nat.leb lb) 0) as j' eqn:Hj'.
  specialize (H1 i' j').
  assert (H : i' < length lb). {
    rewrite Hi'.
    apply isort_rank_ub.
    now intros H; rewrite H in Hi.
  }
  specialize (H1 H); clear H.
  assert (H : j' < length lb). {
    rewrite Hj'.
    apply isort_rank_ub.
    now intros H; rewrite H in Hi.
  }
  specialize (H1 H); clear H.
  assert (H : nth i' (la ° lb) 0 = nth j' (la ° lb) 0). {
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
  rngl_has_opp = true →
  ∀ i l1 l2 l3, ε (l1 ++ i :: l2 ++ i :: l3) = 0%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos after Hop.
revert i l2 l3.
induction l1 as [| j]; intros. {
  rewrite app_nil_l; cbn.
  rewrite (ε_aux_dup Hop).
  apply (rngl_mul_0_l Hos).
}
cbn.
rewrite IHl1.
apply (rngl_mul_0_r Hos).
Qed.

Theorem ε_when_dup :
  rngl_has_opp = true →
  ∀ la,
  ¬ NoDup la
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

Theorem comp_map : ∀ la lb,
  la ° lb = map (λ i, nth (nth i lb 0) la 0) (seq 0 (length lb)).
Proof.
intros.
unfold "°".
now rewrite (List_map_map_seq _ 0).
Qed.
*)

(* *)

Theorem canon_sym_gr_succ_values : ∀ n k σ σ',
  σ = canon_sym_gr_list (S n) k
  → σ' = canon_sym_gr_list n (k mod n!)
  → ∀ i,
    nth i σ 0 =
    match i with
    | 0 => k / n!
    | S i' =>
        if ((k <? n!) && (n <=? i'))%bool then 0
        else succ_when_ge (k / n!) (nth i' σ' 0)
    end.
Proof.
intros * Hσ Hσ' i.
destruct i; [ now subst σ | ].
subst σ; cbn - [ "<=?" ].
remember ((k <? n!) && (n <=? i))%bool as b eqn:Hb.
symmetry in Hb.
destruct b. {
  apply Bool.andb_true_iff in Hb.
  destruct Hb as (Hkn, Hni).
  apply Nat.ltb_lt in Hkn.
  apply Nat.leb_le in Hni.
  rewrite nth_overflow; [ easy | ].
  rewrite map_length.
  now rewrite canon_sym_gr_list_length.
}
apply Bool.andb_false_iff in Hb.
destruct Hb as [Hb| Hb]. {
  apply Nat.ltb_ge in Hb.
  destruct (lt_dec i n) as [Hin| Hin]. {
    rewrite (List_map_nth' 0); [ | now rewrite canon_sym_gr_list_length ].
    now rewrite Hσ'.
  } {
    apply Nat.nlt_ge in Hin.
    rewrite nth_overflow. 2: {
      now rewrite map_length, canon_sym_gr_list_length.
    }
    unfold succ_when_ge.
    rewrite Hσ'.
    rewrite nth_overflow; [ | now rewrite canon_sym_gr_list_length ].
    unfold Nat.b2n; rewrite if_leb_le_dec.
    destruct (le_dec (k / n!) 0) as [H1| H1]; [ | easy ].
    apply Nat.le_0_r in H1.
    apply Nat.div_small_iff in H1; [ | apply fact_neq_0 ].
    now apply Nat.nle_gt in H1.
  }
} {
  apply Nat.leb_gt in Hb.
  rewrite (List_map_nth' 0); [ | now rewrite canon_sym_gr_list_length ].
  now rewrite Hσ'.
}
Qed.

(* equality of ε of sym_gr elem and ε_permut *)

Theorem ε_of_sym_gr_permut_succ :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  ∀ n k,
  k < (S n)!
  → ε (canon_sym_gr_list (S n) k) =
    (minus_one_pow (k / n!) * ε (canon_sym_gr_list n (k mod n!)))%L.
Proof.
intros Hic Hop * Hkn.
cbn.
f_equal. {
  remember (k / n!) as i eqn:Hi.
  remember (k mod n!) as j eqn:Hj.
  assert (Hin : i ≤ n). {
    rewrite Hi.
    apply Nat.lt_succ_r.
    apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
    now rewrite Nat.mul_comm, <- Nat_fact_succ.
  }
  assert (Hjn : j < n!). {
    rewrite Hj.
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  clear k Hkn Hi Hj.
...
(*
  Hin : i ≤ n
  Hjn : j < n!
  ============================
  ε_aux i (map (succ_when_ge i) (canon_sym_gr_list n j)) = minus_one_pow i
*)
End a.

Compute (
  let ro := test_ring_like_op in
  let n := 5 in
map (λ i,
  map (λ j,
    (ε_aux ro i (map (succ_when_ge i) (canon_sym_gr_list n j)) = minus_one_pow ro i)
  ) (seq 0 n!)
) (seq 0 (S n))
).
...
  revert i j Hin Hjn.
  induction n; intros; [ now apply Nat.le_0_r in Hin; subst i | cbn ].
  remember (i ?= succ_when_ge i (j / n!)) as is eqn:His; symmetry in His.
  destruct is. {
    apply Nat.compare_eq_iff in His.
    exfalso.
    unfold succ_when_ge in His.
    unfold Nat.b2n in His.
    rewrite if_leb_le_dec in His.
    destruct (le_dec i (j / n!)) as [Hij| Hij]. {
      rewrite His, Nat.add_1_r in Hij.
      now apply Nat.nlt_ge in Hij; apply Hij.
    }
    rewrite His, Nat.add_0_r in Hij.
    apply Nat.nle_gt in Hij.
    now apply Nat.lt_irrefl in Hij.
  } {
    apply Nat.compare_lt_iff in His.
    unfold succ_when_ge, Nat.b2n in His.
    rewrite if_leb_le_dec in His.
    destruct (le_dec i (j / n!)) as [Hijn| Hijn]. 2: {
      apply Nat.nle_gt in Hijn.
      rewrite Nat.add_0_r in His.
      flia Hijn His.
    }
    clear His.
    rewrite map_map.
    remember (λ k, _) as f; subst f.
(*
    unfold succ_when_ge, Nat.b2n.
*)
    erewrite map_ext_in. 2: {
      intros k Hk.
      apply in_canon_sym_gr_list in Hk. 2: {
        apply Nat.mod_upper_bound, fact_neq_0.
      }
...
      do 2 rewrite if_leb_le_dec.
...
      destruct (le_dec (j / n!) k) as [Hjnk| Hjnk]. {
        destruct (le_dec i (k + 1)) as [Hik| Hik]. 2: {
          exfalso.
          flia Hijn Hjnk Hik.
        }
        easy.
      }
      cbn.
      rewrite Nat.add_0_r.
      apply Nat.nle_gt in Hjnk.
      destruct (le_dec i k) as [Hik| Hik].
...
Abort. (*
...
  Hin : i ≤ S n
  Hjn : j < (S n)!
  Hijn : i ≤ j / n!
  ============================
  ε_aux i (map (λ x : nat, succ_when_ge i (succ_when_ge (j / n!) x)) (canon_sym_gr_list n (j mod n!))) =
  minus_one_pow i
*)
End a.

(*
Require Import RnglAlg.Zrl ZArith.
*)

Compute (
(*
  let ro := RnglAlg.Zrl.Z_ring_like_op in
*)
  let ro := test_ring_like_op in
(**)
  let n := 4 in
let i := 1 in
let j := 24 in
(i ≤ S n, j < (S n)!, i ≤ j / n!,
  ε_aux ro i (map (λ x : nat, succ_when_ge i (succ_when_ge (j / n!) x)) (canon_sym_gr_list n (j mod n!))) =
  minus_one_pow ro i)
).
...

Compute (
(*
  let ro := RnglAlg.Zrl.Z_ring_like_op in
*)
  let ro := test_ring_like_op in
(**)
  let n := 4 in
map (λ i,
  map (λ j,
(i ≤ n, j < n!,
    ε_aux ro i (map (succ_when_ge i) (canon_sym_gr_list n j)) =
    minus_one_pow ro i))
    (seq 0 n!))
  (seq 0 (S n))
).
...
Compute (
  let ro := test_ring_like_op in
  let n := 3 in
  let i := 3 in
  let j := 6 in
    ε_aux ro i (map (succ_when_ge i) (canon_sym_gr_list n j)) =
    minus_one_pow ro i
).
...
Compute (
  let ro := test_ring_like_op in
  let n := 3 in
map (λ i,
  map (λ j,
    ε_aux ro i (map (succ_when_ge i) (canon_sym_gr_list n j)) =
    minus_one_pow ro i)
    (seq 0 15))
  (seq 0 (S n))
).
...
...
intros Hic Hop * Hkn.
cbn.
f_equal. {
destruct n; [ now apply Nat.lt_1_r in Hkn; subst k | ].
destruct n. {
  cbn in Hkn.
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  flia Hkn.
}
destruct n. {
  cbn in Hkn.
  do 4 (destruct k; [ easy | ]).
  do 2 (destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ]).
  flia Hkn.
}
destruct n. {
  cbn in Hkn.
  do 12 (destruct k; [ easy | ]).
  do 12 apply Nat.succ_lt_mono in Hkn.
  do 12 (destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ]).
  flia Hkn.
}
destruct n. {
  cbn in Hkn.
  do 48 (destruct k; [ easy | ]).
  do 72 apply Nat.succ_lt_mono in Hkn.
  do 48 rewrite <- Nat.add_1_r.
  do 47 rewrite <- Nat.add_assoc.
  cbn - [ canon_sym_gr_list fact ].
...
  do 48 (destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ]).
  flia Hkn.
}
...
Compute (
  let ro := test_ring_like_op in
  let n := 5 in
(*
map (λ k,
  (ε ro (map (succ_when_ge (k / n!)) (canon_sym_gr_list n (k mod n!))) =
   ε ro (canon_sym_gr_list n (k mod n!)))) (seq 0 15)
*)
map (λ k,
  ε_aux ro (k / n!)%nat (map (succ_when_ge (k / n!)) (canon_sym_gr_list n (k mod n!))) =
  minus_one_pow ro (k / n!)) (seq 0 10)
(**)
).
...
Compute (
  let ro := test_ring_like_op in
  let n := 3 in
map (λ j,
  map (λ i,
    ε_aux ro i (map (succ_when_ge i) (canon_sym_gr_list n j)) =
      minus_one_pow ro i) (seq 0 n)) (seq 0 n)
).
...
  revert k Hkn.
  induction n; intros; [ now apply Nat.lt_1_r in Hkn; subst k | ].
  specialize (IHn (k / S n)) as H1.
  assert (H : k / S n < (S n)!). {
    apply Nat.div_lt_upper_bound; [ easy | ].
...
  }
  specialize (H1 H); clear H.
  assert (H : k / S n / n! = k / (S n)!). {
    rewrite Nat.div_div; [ | easy | apply fact_neq_0 ].
    now rewrite <- Nat_fact_succ.
  }
  rewrite H in H1.
  rewrite <- H1.
(* euh... non *)
...
Compute (
  let n := 3 in
  map (λ k, map (succ_when_ge (k / n!)) (canon_sym_gr_list n (k mod n!)))
   (seq 0 50)
).
...

(*
End a.

Compute (
  let ro := test_ring_like_op in
  let n := 5 in
  let k := 390 in
(**)
map (λ k,
  (ε ro (map (succ_when_ge (k / n!)) (canon_sym_gr_list n (k mod n!))) =
   ε ro (canon_sym_gr_list n (k mod n!)))) (seq 110 50)
(*
map (λ k,
  ε_aux ro (k / n!)%nat (map (succ_when_ge (k / n!)) (canon_sym_gr_list n (k mod n!))) =
  minus_one_pow ro (k / n!)) (seq 600 50)
*)
).
*)
...
intros Hic Hop * Hkn.
cbn - [ ε ].
destruct n; [ now apply Nat.lt_1_r in Hkn; subst k | ].
destruct n. {
  cbn in Hkn.
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  flia Hkn.
}
destruct n. {
  cbn in Hkn.
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  do 4 apply Nat.succ_lt_mono in Hkn.
  cbn - [ div "mod" ].
  do 2 rewrite Nat.div_1_r.
  rewrite Nat.mod_1_r.
  do 4 rewrite rngl_mul_assoc.
  f_equal; f_equal.
  do 4 rewrite <- Nat.add_1_r.
  do 3 rewrite <- Nat.add_assoc.
  cbn - [ div "mod" ].
  replace 4 with (2 * 2) by easy.
  rewrite Nat.div_add; [ | easy ].
  rewrite Nat.mod_add; [ | easy ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  flia Hkn.
}
destruct n. {
  cbn in Hkn.
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  destruct k; [ easy | ].
  do 12 apply Nat.succ_lt_mono in Hkn.
  cbn - [ div "mod" ].
  do 2 rewrite Nat.div_1_r.
  rewrite Nat.mod_1_r.
  do 6 rewrite rngl_mul_assoc.
  f_equal; f_equal.
  do 12 rewrite <- Nat.add_1_r.
  do 11 rewrite <- Nat.add_assoc.
  cbn - [ div "mod" ].
  replace 12 with (2 * 6) by easy.
  rewrite Nat.div_add; [ | easy ].
  rewrite Nat.mod_add; [ | easy ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  destruct k; [ now cbn; rewrite (rngl_opp_involutive Hop) | ].
  flia Hkn.
}
...
remember (canon_sym_gr_list n (k mod n!)) as σ' eqn:Hσ'.
Compute (
  let n := 5 in
  let k := 388 in
  (canon_sym_gr_list (S n) k, k / n!, canon_sym_gr_list n (k mod n!))).
...
Compute (
  let n := 5 in
  let k := 388 in
  let σ' := canon_sym_gr_list n (k mod n!) in
  (k < (S n)!, k / n!, map (succ_when_ge (k / n!)) σ', σ')).
Print canon_sym_gr_list.
...
(*
remember (canon_sym_gr_list (S n) k) as σ eqn:Hσ.
remember (canon_sym_gr_list n (k mod n!)) as σ' eqn:Hσ'.
specialize (canon_sym_gr_succ_values Hσ Hσ') as H1.
move σ' before σ.
...
*)
rewrite (ε_cons_from_ε_app Hop).
rewrite map_length.
rewrite canon_sym_gr_list_length.
...
revert k Hkn.
induction n; intros; [ now apply Nat.lt_1_r in Hkn; subst k | ].
specialize (IHn (k / S (S n))) as H1.
...
intros Hic Hop * Hkn.
cbn - [ ε ].
remember (canon_sym_gr_list n (k mod n!)) as la eqn:Hla.
Search (ε (_ :: _)).
rewrite (ε_cons_from_ε_app Hop).
rewrite map_length.
rewrite Hla at 1.
rewrite canon_sym_gr_list_length.
Search (ε (_ ++ _)).
Compute (
  let n := 5 in
  let k := 388 in
  let x := canon_sym_gr_list n (k mod n!) in
  (k < (S n)!, map (succ_when_ge (k / n!)) x, k / n!)).
Check canon_sym_gr_succ_values.
revert k la Hkn Hla.
induction n; intros; cbn - [ div fact ]. {
  apply Nat.lt_1_r in Hkn; subst k.
  cbn in Hla; subst la.
  now cbn; rewrite rngl_mul_1_l.
}
...
intros Hic Hop * Hkn.
unfold ε at 1.
rewrite canon_sym_gr_list_length.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold ε.
  subst n; cbn.
  apply Nat.lt_1_r in Hkn; subst k; cbn.
  do 4 rewrite rngl_product_only_one; cbn.
  symmetry; apply rngl_mul_1_l.
}
rewrite Nat_sub_succ_1.
rewrite rngl_product_split_first; [ | easy ].
f_equal. {
  rewrite rngl_product_split_first; [ | easy ].
  replace (0 <? 0) with false by easy.
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec 0 i) as [H| H]; [ clear H | flia Hi H ].
    easy.
  }
  cbn - [ "<?" canon_sym_gr_list ].
  remember (canon_sym_gr_list (S n) k) as σ eqn:Hσ.
  remember (canon_sym_gr_list n (k mod n!)) as σ' eqn:Hσ'.
  specialize (canon_sym_gr_succ_values Hσ Hσ') as H1.
  unfold sign_diff at 1.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite H1.
    replace i with (S (i - 1)) at 1 by flia Hi.
    easy.
  }
  cbn - [ "<?" ].
  rewrite (rngl_product_shift 1); [ | flia Hnz ].
  rewrite Nat.sub_diag.
  remember (k / fact n) as x eqn:Hx.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    rewrite Nat.add_comm, Nat.add_sub.
    replace (match _ with Eq => _ | Lt => _ | Gt => _ end) with
      (if x <? nth i σ' 0 + 1 then 1%L else (-1)%L). 2: {
      rewrite H1.
      unfold succ_when_ge, Nat.b2n.
      rewrite if_ltb_lt_dec.
      rewrite if_leb_le_dec.
      remember ((k <? n!) && (n <=? i))%bool as b eqn:Hb.
      symmetry in Hb.
      destruct b. {
        apply Bool.andb_true_iff in Hb.
        destruct Hb as (_, Hb).
        apply Nat.leb_le in Hb.
        flia Hi Hb Hnz.
      }
      destruct (le_dec x (nth i σ' 0)) as [H2| H2]. {
        destruct (lt_dec x (nth i σ' 0 + 1)) as [H3| H3]; [ | flia H2 H3 ].
        apply Nat.compare_gt_iff in H3.
        now rewrite H3.
      }
      rewrite Nat.add_0_r.
      apply Nat.nle_gt in H2.
      apply Nat.compare_lt_iff in H2.
      rewrite H2.
      apply Nat.compare_lt_iff in H2.
      destruct (lt_dec x (nth i σ' 0)) as [H| H]; [ flia H H2 | clear H ].
      destruct (lt_dec x (nth i σ' 0 + 1)) as [H3| H3]; [ | easy ].
      flia H2 H3.
    }
    easy.
  }
  cbn - [ "<?" ].
  assert (Hp' : permut_seq_with_len n σ'). {
    rewrite Hσ'.
    now apply canon_sym_gr_list_permut_seq_with_len.
  }
  assert (Hp : permut_seq_with_len (S n) σ). {
    rewrite Hσ.
    now apply canon_sym_gr_list_permut_seq_with_len.
  }
  rewrite rngl_product_change_var with
    (g := λ i, nth i (isort_rank Nat.leb σ') 0) (h := λ i, nth i σ' 0). 2: {
    intros i (_, Hi).
    destruct Hp' as (Hp'p, Hp'l).
    apply permut_isort_permut; [ easy | rewrite Hp'l; flia Hnz Hi ].
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  destruct Hp' as (Hp'p, Hp'l).
  erewrite rngl_product_list_eq_compat. 2: {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite permut_permut_isort; [ | easy | ]. 2: {
      rewrite <- Hji.
      apply permut_seq_iff in Hp'p.
      destruct Hp'p as (Hp'a, Hp'n).
      apply Hp'a, nth_In.
      now rewrite Hp'l.
    }
    easy.
  }
  cbn - [ "<?" seq ].
  rewrite (rngl_product_list_permut _ Nat.eqb_eq) with
      (lb := seq 0 n); [ | easy | ]. 2: {
    apply permut_seq_iff in Hp'p.
    destruct Hp'p as (Hp'a, Hp'n).
    rewrite <- Hp'l at 1.
    rewrite <- List_map_nth_seq, <- Hp'l.
    now apply permut_seq_iff.
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
    split; [ easy | ].
    apply -> Nat.succ_le_mono.
    enough (H : x < S n) by flia H Hnz.
    replace x with (nth 0 σ 0) by now rewrite H1.
    destruct Hp as (Hp, Hp3).
    apply permut_seq_iff in Hp.
    destruct Hp as (Hp1, Hp2).
    rewrite <- Hp3.
    apply Hp1, nth_In.
    rewrite Hp3; flia.
  }
  remember (∏ (i = _, _), _)%L as y eqn:Hy.
  rewrite all_1_rngl_product_1. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec x (i + 1)) as [H2| H2]; [ easy | ].
    flia Hi H2.
  }
  subst y; rewrite rngl_mul_1_r.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? i + 1 then 1%L else _) with (-1)%L. 2: {
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
  rewrite rngl_product_split_last; [ | easy ].
  rewrite (rngl_product_shift 1); [ | flia ].
  rewrite Nat.sub_diag.
  rewrite Nat_sub_succ_1.
  rewrite IHx.
  symmetry.
  rewrite minus_one_pow_succ; [ | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
}
unfold ε.
rewrite canon_sym_gr_list_length.
rewrite (rngl_product_shift 1). 2: {
  split; [ easy | flia Hnz ].
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_split_first; [ | easy ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (1 + i) 0) as [H| H]; [ flia H | clear H ].
  rewrite rngl_mul_1_l.
  easy.
}
cbn - [ canon_sym_gr_list "<?" ].
apply rngl_product_eq_compat.
intros i Hi.
rewrite (rngl_product_shift 1). 2: {
  split; [ easy | flia Hnz ].
}
apply rngl_product_eq_compat.
intros j Hj.
cbn - [ "<?" canon_sym_gr_list ].
replace (S i <? S j) with (i <? j) by easy.
move j before i.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
remember (canon_sym_gr_list (S n) k) as σ eqn:Hσ.
remember (canon_sym_gr_list  n (k mod n!)) as σ' eqn:Hσ'.
specialize (canon_sym_gr_succ_values Hσ Hσ') as H1.
do 2 rewrite H1.
unfold succ_when_ge, Nat.b2n.
do 2 rewrite if_leb_le_dec.
remember ((k <? n!) && (n <=? i))%bool as bi eqn:Hbi.
remember ((k <? n!) && (n <=? j))%bool as bj eqn:Hbj.
symmetry in Hbi, Hbj.
move σ' before σ; move bj before bi.
destruct bi. {
  apply Bool.andb_true_iff in Hbi.
  destruct Hbi as (Hkni, Hni).
  apply Nat.leb_le in Hni.
  flia Hi Hni Hnz.
}
destruct bj. {
  apply Bool.andb_true_iff in Hbj.
  destruct Hbj as (Hknj, Hnj).
  apply Nat.leb_le in Hnj.
  flia Hj Hnj Hnz.
}
apply Bool.andb_false_iff in Hbi, Hbj.
unfold sign_diff.
destruct (le_dec (k / n!) (nth j σ' 0)) as [Hsfj| Hsfj]. {
  destruct (le_dec (k / n!) (nth i σ' 0)) as [Hsfi| Hsfi]. {
    now do 2 rewrite Nat.add_1_r.
  }
  rewrite Nat.add_0_r.
  replace (nth j σ' 0 + 1 ?= nth i σ' 0) with Gt. 2: {
    symmetry; apply Nat.compare_gt_iff.
    flia Hsfi Hsfj.
  }
  replace (nth j σ' 0 ?= nth i σ' 0) with Gt. 2: {
    symmetry; apply Nat.compare_gt_iff.
    flia Hsfi Hsfj.
  }
  easy.
}
destruct (le_dec (k / n!) (nth i σ' 0)) as [Hsfi| Hsfi]. {
  rewrite Nat.add_0_r.
  replace (nth j σ' 0 ?= nth i σ' 0 + 1) with Lt. 2: {
    symmetry; apply Nat.compare_lt_iff.
    flia Hsfi Hsfj.
  }
  replace (nth j σ' 0 ?= nth i σ' 0) with Lt. 2: {
    symmetry; apply Nat.compare_lt_iff.
    flia Hsfi Hsfj.
  }
  easy.
}
now do 2 rewrite Nat.add_0_r.
Qed.

Theorem canon_sym_gr_surjective : ∀ n k j,
  k < fact n
  → j < n
  → ∃ i : nat, i < n ∧ nth i (canon_sym_gr_list n k) 0 = j.
Proof.
intros * Hkn Hjn.
exists (nth j (canon_sym_gr_inv_list n k) 0).
split; [ now apply canon_sym_gr_inv_list_ub | ].
now apply canon_sym_gr_sym_gr_inv.
Qed.

Theorem NoDup_ε_1_opp_1 :
  rngl_has_opp = true →
  ∀ σ, NoDup σ → ε σ = 1%L ∨ ε σ = (-1)%L.
Proof.
intros Hop * Hσ.
unfold ε.
destruct (le_dec (length σ) 1) as [Hn1| Hn1]. {
  replace (length σ - 1) with 0 by flia Hn1.
  now do 2 rewrite rngl_product_only_one; cbn; left.
}
apply rngl_product_1_opp_1; [ easy | ].
intros i Hi.
apply rngl_product_1_opp_1; [ easy | ].
intros j Hj.
unfold sign_diff.
rewrite if_ltb_lt_dec.
remember (nth j σ 0 ?= nth i σ 0) as b eqn:Hb.
symmetry in Hb.
destruct (lt_dec i j) as [Hij| Hij]; [ | now left ].
destruct b; [ | now right | now left ].
apply Nat.compare_eq_iff in Hb.
apply (NoDup_nat _ Hσ) in Hb; [ | flia Hj Hn1 | flia Hi Hn1 ].
flia Hi Hj Hb Hij.
Qed.

Theorem ε_1_opp_1_NoDup :
  rngl_has_opp = true →
  rngl_characteristic ≠ 1 →
  rngl_has_eqb = true →
  ∀ σ, ε σ = 1%L ∨ ε σ = (-1)%L → NoDup σ.
Proof.
intros Hop H10 Heq * Hσ.
destruct (ListDec.NoDup_dec Nat.eq_dec σ) as [H1| H1]; [ easy | ].
exfalso.
apply ε_when_dup in H1; [ | easy | easy ].
rewrite H1 in Hσ.
destruct Hσ as [Hσ| Hσ]; symmetry in Hσ. {
  now apply rngl_1_neq_0_iff in Hσ.
} {
  rewrite <- rngl_opp_0 in Hσ; [ | easy ].
  apply rngl_opp_inj in Hσ; [ | easy ].
  now apply rngl_1_neq_0_iff in Hσ.
}
Qed.

Theorem NoDup_ε_square :
  rngl_has_opp = true →
  ∀ σ, NoDup σ → (ε σ * ε σ = 1)%L.
Proof.
intros Hop * Hσ.
specialize (NoDup_ε_1_opp_1) as H1.
specialize (H1 Hop σ Hσ).
destruct H1 as [H1| H1]; rewrite H1. {
  apply rngl_mul_1_l.
} {
  rewrite rngl_mul_opp_opp; [ | easy ].
  apply rngl_mul_1_l.
}
Qed.

(*
Theorem ε_seq : ∀ sta len, ε (seq sta len) = 1%L.
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
    replace (if _ <? _ then _ else _) with 1%L. 2: {
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
*)

End a.

Arguments ε {T}%type {ro}.
Arguments sign_diff {T}%type {ro} (u v)%nat.

Arguments ε_nil {T ro rp}.
Arguments ε_permut {T}%type {ro} (n k)%nat.
Arguments ε_of_sym_gr_permut_succ {T}%type {ro rp} Hic Hop (n k)%nat.
Arguments comp_permut_seq n%nat [σ₁ σ₂]%list.
Arguments map_nth_permut_seq n%nat [la lb]%list.
Arguments permut_isort_rank_comp n%nat [la lb]%list.
Arguments sign_comp {T}%type {ro rp} _ [la lb]%list.
Arguments transposition_signature {T}%type {ro rp} _ _ (n p q)%nat.
Arguments NoDup_ε_1_opp_1 {T}%type {ro rp} _  [σ].
Arguments NoDup_ε_square {T}%type {ro rp} _ [σ].
Arguments ε_when_dup {T ro rp} Hop Hde [la]%list.

Arguments minus_one_pow {T}%type {ro} n%nat.
Arguments minus_one_pow_add_r {T}%type {ro rp} Hop (i j)%nat.
Arguments minus_one_pow_mul_comm {T ro rp} Hop i%nat x%L.
Arguments minus_one_pow_succ {T}%type {ro rp} _ i%nat.
Arguments minus_one_pow_succ_succ {T}%type {ro rp} _ i%nat.
