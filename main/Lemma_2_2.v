(* Lemma 2.2 of the proof of the sensitivity conjecture *)

(* Lemma 2.2. We define a sequence of symmetric square matrices
   iteratively as follows

     A1 = [ 0 1 ]
          [ 1 0 ],
     An = [ A_{n-1} I        ]
          [ I       -A_{n-1} ]

   Then An is a 2^n x 2^n matrix whose eigenvalues are √n of multiplitiy
   2^{n-1} and -√n of multiplicity 2^{n-1}.
 *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc RingLike MyVector Matrix.
Require Import IterAdd.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hon : rngl_has_1 T = true).

Fixpoint map3 {A} f (la lb : list A) : list A :=
  match la with
  | [] => lb
  | a :: la' =>
      match lb with
      | [] => la
      | b :: lb' => f a b :: map3 f la' lb'
      end
  end.

Theorem map3_nil_r : ∀ A f (la : list A), map3 f la [] = la.
Proof.
intros.
now induction la.
Qed.

(* *)

Definition fold_app_in_list (lll : list (list (list T))) :=
  iter_list lll (map3 (app (A:=T))) [].

Definition flatten_list_list llll := flat_map fold_app_in_list llll.

Definition mat_of_mat_list_list (mll : list (list (matrix T))) : matrix T :=
  mk_mat (flatten_list_list (map (map (@mat_list_list T)) mll)).

(* sequence "An" *)

Fixpoint mA (n : nat) : matrix T :=
  match n with
  | 0 => mZ 1 1
  | S n' =>
      mat_of_mat_list_list
        [[mA n'; mI (2 ^ n')];
         [mI (2 ^ n'); (- mA n')%M]]
  end.

Theorem length_app_in_list : ∀ la lb,
  length (map3 (app (A := T)) la lb) = max (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem length_hd_app_in_list : ∀ la lb : list (list T),
  length (hd [] (map3 (app (A := T)) la lb)) =
  length (hd [] la) + length (hd [] lb).
Proof.
intros.
destruct la as [| a]; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
apply app_length.
Qed.

Theorem mA_nrows : ∀ n, mat_nrows (mA n) = 2 ^ n.
Proof.
intros.
induction n; [ easy | ].
cbn - [ "^" ].
rewrite app_nil_r.
rewrite app_length.
unfold fold_app_in_list, iter_list; cbn.
do 2 rewrite length_app_in_list.
do 2 rewrite map_length.
rewrite seq_length.
do 2 rewrite Nat.max_comm.
rewrite fold_mat_nrows, IHn.
rewrite Nat.max_id; cbn.
now rewrite Nat.add_0_r.
Qed.

Theorem mA_ncols : ∀ n, mat_ncols (mA n) = 2 ^ n.
Proof.
intros.
induction n; [ easy | ].
cbn - [ "^" ].
unfold mat_ncols; cbn - [ "^" ].
rewrite List_app_hd1. 2: {
  unfold fold_app_in_list, iter_list; cbn.
  rewrite length_app_in_list.
  rewrite List_map_seq_length.
  rewrite fold_mat_nrows.
  rewrite mA_nrows, Nat.max_id.
  apply Nat.neq_0_lt_0.
  now apply Nat.pow_nonzero.
}
unfold mat_ncols in IHn.
unfold fold_app_in_list, iter_list; cbn.
rewrite length_hd_app_in_list, IHn.
rewrite (List_map_hd 0). 2: {
  rewrite seq_length.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite List_map_seq_length; cbn.
now rewrite Nat.add_0_r.
Qed.

Theorem nth_map3_app : ∀ i lla llb d,
  i < length lla
  → i < length llb
  → nth i (map3 (app (A:=T)) lla llb) d = nth i lla d ++ nth i llb d.
Proof.
intros * Ha Hb.
revert i llb Ha Hb.
induction lla as [| la]; intros; [ easy | cbn ].
destruct llb as [| lb]; [ easy | cbn ].
destruct i; [ easy | ].
cbn in Ha, Hb.
apply Nat.succ_lt_mono in Ha.
apply Nat.succ_lt_mono in Hb.
now apply IHlla.
Qed.

Theorem in_map3_app : ∀ la lla llb,
  la ∈ map3 (app (A:=T)) lla llb
  → ∃ i,
    i < max (length lla) (length llb) ∧ la = nth i lla [] ++ nth i llb [].
Proof.
intros * Hla.
rename la into lc.
revert llb Hla.
induction lla as [| la]; intros; cbn. {
  cbn in Hla.
  induction llb as [| lb]; [ easy | ].
  destruct Hla as [Hla| Hla]. {
    subst lc.
    exists 0.
    split; [ | easy ].
    cbn; flia.
  } {
    specialize (IHllb Hla).
    destruct IHllb as (i & Hil & Hc).
    exists (S i).
    subst lc; cbn.
    split; [ now apply -> Nat.succ_lt_mono | ].
    now destruct i.
  }
}
destruct llb as [| lb]. {
  cbn in Hla |-*.
  destruct Hla as [Hla| Hla]. {
    subst lc; cbn.
    exists 0.
    split; [ easy | ].
    symmetry; apply app_nil_r.
  } {
    cbn.
    apply In_nth with (d := []) in Hla.
    destruct Hla as (n & Hnl & Hn).
    subst lc.
    exists (S n).
    split; [ now apply -> Nat.succ_lt_mono | ].
    symmetry; apply app_nil_r.
  }
}
cbn in Hla.
destruct Hla as [Hla| Hla]. {
  exists 0.
  subst lc; cbn.
  split; [ easy | easy ].
}
specialize (IHlla _ Hla).
destruct IHlla as (n & Hn & Hc).
exists (S n); cbn.
split; [ now apply -> Nat.succ_lt_mono | easy ].
Qed.

Theorem mA_is_correct : ∀ n, is_correct_matrix (mA n) = true.
Proof.
intros.
induction n. {
  now apply mZ_is_correct_matrix.
}
apply is_scm_mat_iff.
split; [ now rewrite mA_nrows, mA_ncols | ].
intros la Hla.
rewrite mA_ncols.
cbn in Hla.
rewrite app_nil_r in Hla.
apply in_app_or in Hla.
destruct Hla as [Hla| Hla]. {
  apply in_map3_app in Hla.
  destruct Hla as (i & Him & Hla).
  unfold map3 in Him.
  rewrite fold_mat_nrows, mA_nrows in Him.
  rewrite List_map_seq_length in Him.
  rewrite Nat.max_id in Him.
  subst la.
  rewrite app_length.
  unfold map3.
  rewrite fold_corr_mat_ncols; [ | easy | now rewrite mA_nrows ].
  rewrite mA_ncols.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite List_map_seq_length.
  now cbn; rewrite Nat.add_0_r.
} {
  apply in_map3_app in Hla.
  destruct Hla as (i & Him & Hla).
  unfold map3 in Him.
  rewrite List_map_seq_length in Him.
  rewrite map_length in Him.
  rewrite fold_mat_nrows, mA_nrows, Nat.max_id in Him.
  subst la; cbn.
  rewrite app_length.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite List_map_seq_length.
  f_equal; rewrite Nat.add_0_r.
  rewrite (List_map_nth' []). 2: {
    now rewrite fold_mat_nrows, mA_nrows.
  }
  rewrite map_length.
  rewrite fold_corr_mat_ncols; cycle 2. {
    now rewrite mA_nrows.
  } {
    apply mA_ncols.
  }
  easy.
}
Qed.

Theorem mA_is_square_matrix : ∀ n, is_square_matrix (mA n) = true.
Proof.
intros.
apply is_scm_mat_iff.
rewrite mA_nrows, mA_ncols.
split; [ easy | ].
intros la Hla.
revert la Hla.
induction n; intros. {
  cbn in Hla |-*.
  destruct Hla as [H| H]; [ now subst la | easy ].
}
cbn in Hla.
rewrite app_nil_r in Hla.
apply in_app_iff in Hla.
destruct Hla as [Hla| Hla]. {
  apply in_map3_app in Hla.
  destruct Hla as (i & Him & Hla); subst la.
  unfold map3 in Him.
  rewrite fold_mat_nrows, mA_nrows in Him.
  rewrite List_map_seq_length, Nat.max_id in Him.
  rewrite app_length; cbn.
  rewrite fold_corr_mat_ncols; cycle 1. {
    apply mA_is_correct.
  } {
    now rewrite mA_nrows.
  }
  rewrite mA_ncols.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite List_map_seq_length; cbn.
  now rewrite Nat.add_0_r.
} {
  apply in_map3_app in Hla.
  destruct Hla as (i & Him & Hla); subst la.
  unfold map3 in Him.
  rewrite List_map_seq_length in Him.
  rewrite map_length in Him.
  rewrite fold_mat_nrows, mA_nrows, Nat.max_id in Him.
  rewrite app_length; cbn.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' []); [ | now rewrite fold_mat_nrows, mA_nrows ].
  do 2 rewrite map_length.
  rewrite seq_length.
  rewrite fold_corr_mat_ncols; cycle 1. {
    apply mA_is_correct.
  } {
    now rewrite mA_nrows.
  }
  rewrite mA_ncols; cbn.
  now rewrite Nat.add_0_r.
}
Qed.

Theorem le_pow_succ_sub_1_lt : ∀ n j, j ≤ 2 ^ S n - 1 → j - 2 ^ n < 2 ^ n.
Proof.
intros * Hj.
apply (Nat.add_lt_mono_r _ _ (2 ^ n)).
destruct (le_dec (2 ^ n) j) as [H1| H1]. {
  rewrite Nat.sub_add; [ | easy ].
  cbn in Hj; rewrite Nat.add_0_r in Hj.
  apply (le_lt_trans _ (2 ^ n + 2 ^ n - 1)); [ easy | ].
  apply Nat.sub_lt; [ | easy ].
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.eq_add_0 in H.
  destruct H as (H, _); revert H.
  now apply Nat.pow_nonzero.
} {
  apply Nat.nle_gt in H1.
  rewrite (proj2 (Nat.sub_0_le j (2 ^ n))); [ | flia H1 ].
  apply Nat.lt_add_pos_r.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
Qed.

Theorem le_pow_sub_1_lt : ∀ n j, j ≤ 2 ^ n - 1 → j < 2 ^ n.
Proof.
intros n j Hj.
apply (le_lt_trans _ (2 ^ n - 1)); [ easy | ].
apply Nat.sub_lt; [ | easy ].
apply Nat.neq_0_lt_0.
now apply Nat.pow_nonzero.
Qed.

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I :
  rngl_has_opp = true →
  ∀ n, (mA n * mA n)%M = (rngl_mul_nat 1 n × mI (2 ^ n))%M.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
unfold "*"%M, "×"%M.
cbn; f_equal.
rewrite mA_nrows.
rewrite map_map.
rewrite <- seq_shift with (len := 2 ^ n), map_map.
apply map_ext_in.
intros i Hi.
rewrite mA_ncols.
rewrite map_map.
rewrite <- seq_shift, map_map.
apply map_ext_in.
intros k Hk.
move k before i.
unfold mat_mul_el.
rewrite mA_ncols.
apply in_seq in Hi, Hk.
destruct Hi as (_, Hi).
destruct Hk as (_, Hk).
rewrite Nat.add_0_l in Hi, Hk.
revert i k Hi Hk.
induction n; intros. {
  apply Nat.lt_1_r in Hi, Hk; subst i k; cbn.
  rewrite rngl_summation_only_one.
  rewrite Nat.sub_diag.
  rewrite rngl_mul_0_l; [ | easy ].
  now rewrite rngl_mul_0_l.
}
rewrite (rngl_summation_split (2 ^ n)). 2: {
  split; [ flia | ].
  apply -> Nat.succ_le_mono.
  apply Nat.pow_le_mono_r; [ easy | flia ].
}
cbn - [ Nat.pow ].
rewrite rngl_add_comm.
rewrite app_nil_r.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  assert (Hj' : 2 ^ n ≤ j - 1 ≤ 2 ^ S n - 1) by flia Hj.
  do 2 rewrite Nat.sub_0_r.
  unfold fold_app_in_list, iter_list; cbn.
  rewrite app_nth2 with (n := j - 1). 2: {
    rewrite length_app_in_list.
    rewrite List_map_seq_length.
    now rewrite fold_mat_nrows, mA_nrows, Nat.max_id.
  }
  rewrite length_app_in_list.
  rewrite fold_mat_nrows, mA_nrows.
  rewrite List_map_seq_length, Nat.max_id.
  rewrite nth_map3_app; cycle 1. {
    now rewrite List_map_seq_length; apply le_pow_succ_sub_1_lt.
  } {
    rewrite map_length, fold_mat_nrows, mA_nrows.
    now apply le_pow_succ_sub_1_lt.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply le_pow_succ_sub_1_lt.
  }
  rewrite (List_map_nth' []). 2: {
    rewrite fold_mat_nrows, mA_nrows.
    now apply le_pow_succ_sub_1_lt.
  }
  rewrite seq_nth; [ cbn | now apply le_pow_succ_sub_1_lt ].
  easy.
}
cbn - [ "^" ].
destruct (lt_dec i (2 ^ n)) as [Hin| Hin]. {
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    assert (Hj' : 2 ^ n ≤ j - 1 ≤ 2 ^ S n - 1) by flia Hj.
    rewrite app_nth1. 2: {
      rewrite length_app_in_list.
      rewrite List_map_seq_length.
      now rewrite fold_mat_nrows, mA_nrows, Nat.max_id.
    }
    rewrite nth_map3_app; cycle 1. {
      now rewrite fold_mat_nrows, mA_nrows.
    } {
      now rewrite List_map_seq_length.
    }
    rewrite app_nth2. 2: {
      rewrite fold_corr_mat_ncols; cycle 2. {
        now rewrite mA_nrows.
      } {
        now rewrite mA_ncols.
      }
      apply mA_is_correct.
    }
    rewrite fold_corr_mat_ncols; cycle 1. {
      apply mA_is_correct.
    } {
      now rewrite mA_nrows.
    }
    rewrite mA_ncols.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ cbn | easy ].
    rewrite (List_map_nth' 0). 2: {
      now rewrite seq_length; apply le_pow_succ_sub_1_lt.
    }
    rewrite seq_nth; [ cbn | now apply le_pow_succ_sub_1_lt ].
    easy.
  }
  cbn - [ "^" ].
  rewrite rngl_add_comm.
  do 2 rewrite Nat.sub_0_r.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    assert (Hj' : j - 1 ≤ 2 ^ n - 1) by flia Hj.
    unfold fold_app_in_list, iter_list; cbn.
    rewrite app_nth1 with (n := j - 1). 2: {
      rewrite length_app_in_list.
      rewrite List_map_seq_length.
      rewrite fold_mat_nrows, mA_nrows, Nat.max_id.
      now apply le_pow_sub_1_lt.
    }
    rewrite app_nth1. 2: {
      rewrite length_app_in_list.
      rewrite List_map_seq_length.
      now rewrite fold_mat_nrows, mA_nrows, Nat.max_id.
    }
    rewrite nth_map3_app; cycle 1. {
      now rewrite fold_mat_nrows, mA_nrows.
    } {
      now rewrite List_map_seq_length.
    }
    rewrite nth_map3_app; cycle 1. {
      rewrite fold_mat_nrows, mA_nrows.
      now apply le_pow_sub_1_lt.
    } {
      rewrite List_map_seq_length.
      now apply le_pow_sub_1_lt.
    }
    rewrite app_nth1. 2: {
      rewrite fold_corr_mat_ncols; cycle 2. {
        now rewrite mA_nrows.
      } {
        rewrite mA_ncols.
        now apply le_pow_sub_1_lt.
      }
      apply mA_is_correct.
    }
    rewrite fold_mat_el.
    easy.
  }
  rewrite rngl_add_comm.
  destruct (lt_dec k (2 ^ n)) as [Hkn| Hkn]. {
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite app_nth1. 2: {
        now rewrite List_map_seq_length.
      }
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ cbn | easy ].
      easy.
    }
    rewrite rngl_add_comm.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      assert (Hj' : j - 1 ≤ 2 ^ n - 1) by flia Hj.
      rewrite <- Nat.sub_succ_l; [ | easy ].
      rewrite Nat_sub_succ_1.
      rewrite app_nth1. 2: {
        rewrite fold_corr_mat_ncols; cycle 2. {
          rewrite mA_nrows.
          now apply le_pow_sub_1_lt.
        } {
          now rewrite mA_ncols.
        }
        apply mA_is_correct.
      }
      rewrite fold_mat_el.
      rewrite <- Nat.sub_succ_l; [ | easy ].
      rewrite Nat_sub_succ_1.
      easy.
    }
    rewrite rngl_add_comm.
    rewrite IHn; [ | easy | easy ].
    rewrite rngl_mul_add_distr_r, (rngl_mul_1_l Hon).
    f_equal.
    rewrite (rngl_summation_shift (2 ^ n)). 2: {
      split; [ flia | ].
      cbn; rewrite Nat.add_0_r.
      apply Nat.add_le_mono_l.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite Nat.add_comm, Nat.add_sub.
    cbn; rewrite Nat.add_0_r.
    rewrite Nat.add_sub.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite Nat_sub_sub_swap.
      now rewrite Nat.add_comm, Nat.add_sub.
    }
    cbn.
    destruct (lt_eq_lt_dec i k) as [[Hik| Hik]| Hik]. {
      rewrite δ_ndiag; [ | flia Hik ].
      apply all_0_rngl_summation_0.
      intros j Hj.
      unfold δ.
      do 2 rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec i (j - 1)) as [Hij| Hij]. {
        destruct (Nat.eq_dec (j - 1) k) as [Hjk| Hjk]. {
          rewrite Hij, Hjk in Hik; flia Hik.
        }
        now apply rngl_mul_0_r.
      } {
        now apply rngl_mul_0_l.
      }
    } {
      subst k.
      rewrite δ_diag.
      rewrite (rngl_summation_split3 (S i)); [ | split; flia Hin ].
      rewrite all_0_rngl_summation_0. 2: {
        intros j Hj.
        rewrite δ_ndiag; [ | flia Hj ].
        now apply rngl_mul_0_l.
      }
      rewrite rngl_add_0_l.
      rewrite Nat_sub_succ_1.
      rewrite δ_diag, (rngl_mul_1_l Hon).
      rewrite all_0_rngl_summation_0. 2: {
        intros j Hj.
        rewrite δ_ndiag; [ | flia Hj ].
        now apply rngl_mul_0_l.
      }
      apply rngl_add_0_r.
    } {
      rewrite δ_ndiag; [ | flia Hik ].
      apply all_0_rngl_summation_0.
      intros j Hj.
      unfold δ.
      do 2 rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec i (j - 1)) as [Hij| Hij]. {
        destruct (Nat.eq_dec (j - 1) k) as [Hjk| Hjk]. {
          rewrite Hij, Hjk in Hik; flia Hik.
        }
        now apply rngl_mul_0_r.
      } {
        now apply rngl_mul_0_l.
      }
    }
  } {
    apply Nat.nlt_ge in Hkn.
    rewrite δ_ndiag; [ | flia Hin Hkn ].
    rewrite rngl_mul_0_r; [ | easy ].
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      assert (Hj' : j - 1 ≤ 2 ^ S n - 1) by flia Hj.
      rewrite app_nth2. 2: {
        now rewrite List_map_seq_length.
      }
      rewrite List_map_seq_length.
      rewrite (List_map_nth' 0%L). 2: {
        rewrite fold_corr_mat_ncols; cycle 1. {
          apply mA_is_correct.
        } {
          rewrite mA_nrows.
          now apply le_pow_succ_sub_1_lt.
        }
        rewrite mA_ncols.
        apply Nat.add_lt_mono_r with (p := 2 ^ n).
        rewrite Nat.sub_add; [ | easy ].
        now cbn in Hk; rewrite Nat.add_0_r in Hk.
      }
      rewrite fold_mat_el.
      now rewrite rngl_mul_opp_r.
    }
    rewrite (rngl_summation_shift (2 ^ n + 1)). 2: {
      split; [ easy | ].
      cbn; rewrite Nat.add_0_r.
      apply Nat.add_le_mono_l.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite Nat.sub_diag.
    rewrite <- rngl_opp_summation; [ | easy ].
    cbn; rewrite Nat.add_0_r.
    rewrite Nat.sub_add_distr, Nat.add_sub.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite (Nat.add_comm _ j), Nat.add_assoc.
      now do 2 rewrite Nat.add_sub.
    }
    rewrite rngl_add_comm.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      assert (Hj' : j - 1 < 2 ^ n) by flia Hj.
      rewrite <- Nat.sub_succ_l; [ | easy ].
      rewrite Nat_sub_succ_1.
      rewrite app_nth2. 2: {
        rewrite fold_corr_mat_ncols; cycle 2. {
          now rewrite mA_nrows.
        } {
          now rewrite mA_ncols.
        }
        apply mA_is_correct.
      }
      rewrite fold_corr_mat_ncols; cycle 1. {
        apply mA_is_correct.
      } {
        now rewrite mA_nrows.
      }
      rewrite mA_ncols.
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length.
        apply le_pow_succ_sub_1_lt; flia Hk.
      }
      rewrite seq_nth; [ | easy ].
      rewrite seq_nth; [ | apply le_pow_succ_sub_1_lt; flia Hk ].
      now cbn.
    }
    cbn.
    rewrite fold_rngl_sub; [ | easy ].
    rewrite (rngl_summation_split3 (k - 2 ^ n + 1)). 2: {
      split; [ flia Hk | ].
      apply (Nat.add_le_mono_r _ _ (2 ^ n)).
      rewrite <- Nat.add_assoc.
      rewrite (Nat.add_comm _ (2 ^ n)).
      rewrite Nat.add_assoc.
      rewrite Nat.sub_add; [ | easy ].
      cbn in Hk; rewrite Nat.add_0_r in Hk.
      flia Hk.
    }
    rewrite Nat.add_sub.
    rewrite δ_diag, (rngl_mul_1_r Hon).
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_r.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_r.
    }
    rewrite rngl_add_0_r.
    rewrite (rngl_summation_split3 i). 2: {
      split; [ easy | flia Hin ].
    }
    rewrite δ_diag, (rngl_mul_1_l Hon).
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_l.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_l.
    }
    rewrite rngl_add_0_r.
    rewrite Nat.add_1_r.
    now apply rngl_sub_diag.
  }
} {
  apply Nat.nlt_ge in Hin.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    assert (Hj' : 2 ^ n ≤ j - 1) by flia Hj.
    rewrite app_nth2. 2: {
      rewrite length_app_in_list.
      rewrite List_map_seq_length.
      now rewrite fold_mat_nrows, mA_nrows, Nat.max_id.
    }
    rewrite length_app_in_list.
    rewrite List_map_seq_length.
    rewrite fold_mat_nrows, mA_nrows.
    rewrite Nat.max_id.
    rewrite nth_map3_app; cycle 1. {
      rewrite List_map_seq_length.
      apply le_pow_succ_sub_1_lt; flia Hi.
    } {
      rewrite map_length, fold_mat_nrows, mA_nrows.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite app_nth2. 2: {
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length.
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      now rewrite List_map_seq_length.
    }
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite List_map_seq_length.
    rewrite (List_map_nth' []). 2: {
      rewrite fold_mat_nrows, mA_nrows.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite (List_map_nth' 0%L). 2: {
      rewrite fold_corr_mat_ncols; cycle 1. {
        apply mA_is_correct.
      } {
        rewrite mA_nrows.
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      rewrite mA_ncols; apply le_pow_succ_sub_1_lt.
      flia Hj.
    }
    now rewrite fold_mat_el.
  }
  cbn - [ "^" ].
  destruct (lt_dec k (2 ^ n)) as [Hkn| Hkn]. {
    rewrite δ_ndiag; [ | flia Hin Hkn ].
    rewrite rngl_mul_0_r; [ | easy ].
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite app_nth1. 2: {
        now rewrite List_map_seq_length.
      }
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ cbn | easy ].
      rewrite rngl_mul_opp_l; [ | easy ].
      easy.
    }
    cbn - [ "^" ].
    rewrite <- rngl_opp_summation; [ | easy ].
    rewrite (rngl_summation_split3 (k + 2 ^ n + 1)). 2: {
      split; [ flia | cbn; flia Hkn ].
    }
    do 2 rewrite Nat.add_sub.
    rewrite δ_diag, (rngl_mul_1_r Hon).
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj Hkn ].
      now apply rngl_mul_0_r.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj Hkn ].
      now apply rngl_mul_0_r.
    }
    rewrite rngl_add_0_r.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      unfold fold_app_in_list, iter_list; cbn.
      do 2 rewrite Nat.sub_0_r.
      rewrite app_nth2. 2: {
        rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
        now rewrite List_map_seq_length, Nat.max_id.
      }
      rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
      rewrite List_map_seq_length, Nat.max_id.
      rewrite nth_map3_app; cycle 1. {
        rewrite List_map_seq_length.
        apply le_pow_succ_sub_1_lt; flia Hi.
      } {
        rewrite map_length, fold_mat_nrows, mA_nrows.
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length.
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      rewrite (List_map_nth' []). 2: {
        rewrite fold_mat_nrows, mA_nrows.
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      rewrite seq_nth; [ | apply le_pow_succ_sub_1_lt; flia Hi ].
      now cbn.
    }
    cbn.
    rewrite (rngl_summation_split3 (i - 2 ^ n + 1)). 2: {
      split; [ flia | ].
      cbn in Hi; flia Hi.
    }
    rewrite Nat.add_sub.
    rewrite app_nth1. 2: {
      rewrite List_map_seq_length.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite seq_nth. 2: {
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite δ_diag, (rngl_mul_1_l Hon).
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite app_nth1. 2: {
        rewrite List_map_seq_length.
        cbn in Hi; flia Hj Hi.
      }
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length.
        cbn in Hi; flia Hj Hi.
      }
      rewrite seq_nth; [ | cbn in Hi; flia Hj Hi ].
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_l.
    }
    rewrite rngl_add_0_l.
    rewrite app_nth1. 2: {
      rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
      rewrite List_map_seq_length, Nat.max_id.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite nth_map3_app; cycle 1. {
      rewrite fold_mat_nrows, mA_nrows.
      apply le_pow_succ_sub_1_lt; flia Hi.
    } {
      rewrite List_map_seq_length.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite app_nth1. 2: {
      rewrite fold_corr_mat_ncols; cycle 1. {
        apply mA_is_correct.
      } {
        rewrite mA_nrows.
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      now rewrite mA_ncols.
    }
    rewrite fold_mat_el.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite app_nth1. 2: {
        rewrite List_map_seq_length; flia Hj.
      }
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length; flia Hj.
      }
      rewrite seq_nth; [ | flia Hj ].
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_l.
    }
    rewrite rngl_add_0_r.
    now apply rngl_add_opp_l.
  } {
    apply Nat.nlt_ge in Hkn.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite app_nth2. 2: {
        now rewrite List_map_seq_length.
      }
      rewrite List_map_seq_length.
      rewrite (List_map_nth' 0%L). 2: {
        rewrite fold_corr_mat_ncols; cycle 1. {
          apply mA_is_correct.
        } {
          rewrite mA_nrows; apply le_pow_succ_sub_1_lt; flia Hj.
        }
        rewrite mA_ncols.
        apply le_pow_succ_sub_1_lt; flia Hk.
      }
      rewrite rngl_mul_opp_l; [ | easy ].
      rewrite rngl_mul_opp_r; [ | easy ].
      rewrite rngl_opp_involutive; [ | easy ].
      now rewrite fold_mat_el.
    }
    cbn - [ "^" ].
    rewrite (rngl_summation_shift (2 ^ n + 1)). 2: {
      split; [ easy | flia Hi Hin ].
    }
    rewrite Nat.sub_diag; cbn.
    rewrite Nat.add_0_r.
    rewrite Nat.sub_add_distr.
    rewrite Nat.add_sub.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite (Nat.add_comm _ j).
      now rewrite Nat.add_assoc, Nat.add_sub.
    }
    cbn - [ "^" ].
    rewrite rngl_summation_rshift.
    rewrite <- Nat.sub_succ_l. 2: {
      apply Nat.neq_0_lt_0.
      now apply Nat.pow_nonzero.
    }
    rewrite Nat_sub_succ_1.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite Nat.add_sub.
      rewrite <- (Nat.sub_succ_l 1); [ | easy ].
      rewrite Nat_sub_succ_1.
      easy.
    }
    cbn.
    rewrite IHn; cycle 1. {
      apply le_pow_succ_sub_1_lt; flia Hi.
    } {
      apply le_pow_succ_sub_1_lt; flia Hk.
    }
    rewrite rngl_mul_add_distr_r, (rngl_mul_1_l Hon), rngl_add_comm.
    f_equal. 2: {
      f_equal; unfold δ; symmetry.
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec i k) as [Hik| Hik]. {
        now subst k; rewrite Nat.eqb_refl.
      }
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec _ _) as [H| H]; [ | easy ].
      flia Hik H Hin Hkn.
    }
    do 2 rewrite Nat.sub_0_r.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      unfold fold_app_in_list, iter_list; cbn.
      rewrite app_nth2. 2: {
        rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
        now rewrite List_map_seq_length, Nat.max_id.
      }
      rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
      rewrite List_map_seq_length, Nat.max_id.
      rewrite nth_map3_app; cycle 1. {
        rewrite List_map_seq_length.
        apply le_pow_succ_sub_1_lt; flia Hi.
      } {
        rewrite map_length, fold_mat_nrows, mA_nrows.
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length.
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      rewrite seq_nth. 2: {
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      cbn.
      rewrite (List_map_nth' []). 2: {
        rewrite fold_mat_nrows, mA_nrows.
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      assert (Hj' : j - 1 < 2 ^ n) by flia Hj.
      rewrite app_nth1. 2: {
        now rewrite List_map_seq_length.
      }
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ cbn | easy ].
      rewrite app_nth1. 2: {
        rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
        now rewrite List_map_seq_length, Nat.max_id.
      }
      assert (Hj'' : j - 1 ≤ 2 ^ n - 1) by flia Hj.
      rewrite nth_map3_app; cycle 1. {
        now rewrite fold_mat_nrows, mA_nrows; apply le_pow_sub_1_lt.
      } {
        now rewrite List_map_seq_length; apply le_pow_sub_1_lt.
      }
      rewrite app_nth2. 2: {
        rewrite fold_corr_mat_ncols; cycle 1. {
          apply mA_is_correct.
        } {
          now rewrite mA_nrows; apply le_pow_sub_1_lt.
        }
        now rewrite mA_ncols.
      }
      rewrite fold_corr_mat_ncols; cycle 1. {
        apply mA_is_correct.
      } {
        now rewrite mA_nrows; apply le_pow_sub_1_lt.
      }
      rewrite mA_ncols.
      rewrite (List_map_nth' 0). 2: {
        now rewrite seq_length; apply le_pow_sub_1_lt.
      }
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length; apply le_pow_succ_sub_1_lt; flia Hk.
      }
      rewrite seq_nth; [ cbn | now apply le_pow_sub_1_lt ].
      rewrite seq_nth; [ | apply le_pow_succ_sub_1_lt; flia Hk ].
      now cbn.
    }
    cbn.
    rewrite (rngl_summation_split3 (k - 2 ^ n + 1)). 2: {
      split; [ flia | cbn in Hk; flia Hk ].
    }
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite (@δ_ndiag _ _ (j - 1 - 1)); [ | flia Hj ].
      now apply rngl_mul_0_r.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite (@δ_ndiag _ _ (j - 1)); [ | flia Hj ].
      now apply rngl_mul_0_r.
    }
    rewrite rngl_add_0_r.
    rewrite Nat.add_sub, δ_diag, (rngl_mul_1_r Hon).
    unfold δ; symmetry.
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec i k) as [Hik| Hik]. {
      now subst k; rewrite Nat.eqb_refl.
    }
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec _ _) as [H| H]; [ | easy ].
    flia Hik H Hin Hkn.
  }
}
Qed.

(* seems, on paper, that √(n+1) is an eignenvalue for A_{n+1}
   and a corresponding eigenvector is
      ( A_n + √(n+1) I )
      (                ) * V
      (       I        )
   for any vector V of dimension 2^(n+1).
     There is going to be a special case for n = 0.
   This way, we have to prove that this pair eigen(value,vector)
   works *)

Theorem m_o_mll_2x2_2x1 : ∀ n (M1 M2 M3 M4 M5 M6 : matrix T),
  is_square_matrix M1 = true
  → is_square_matrix M3 = true
  → is_square_matrix M5 = true
  → mat_nrows M1 = n
  → mat_nrows M2 = n
  → mat_nrows M3 = n
  → mat_nrows M4 = n
  → mat_nrows M5 = n
  → mat_ncols M2 = n
  → mat_ncols M4 = n
  → mat_ncols M6 = n
  → (mat_of_mat_list_list [[M1; M2]; [M3; M4]] *
     mat_of_mat_list_list [[M5]; [M6]])%M =
     mat_of_mat_list_list [[M1 * M5 + M2 * M6]; [M3 * M5 + M4 * M6]]%M.
Proof.
intros * Hs1 Hs3 Hs5 Hr1 Hr2 Hr3 Hr4 Hr5 Hc2 Hc4 Hc6.
specialize (squ_mat_ncols _ Hs1) as Hc1.
apply is_scm_mat_iff in Hs1.
destruct Hs1 as (_ & Hc1').
rewrite Hr1 in Hc1, Hc1'.
specialize (squ_mat_ncols _ Hs3) as Hc3.
apply is_scm_mat_iff in Hs3.
destruct Hs3 as (_ & Hc3').
rewrite Hr3 in Hc3, Hc3'.
specialize (squ_mat_ncols _ Hs5) as Hc5.
apply is_scm_mat_iff in Hs5.
destruct Hs5 as (Hcr5 & Hc5').
rewrite Hr5 in Hc5, Hc5'.
unfold mat_mul, mat_add; cbn.
unfold mat_of_mat_list_list; cbn.
f_equal.
do 3 rewrite app_nil_r.
rewrite app_length.
unfold fold_app_in_list, iter_list; cbn.
do 2 rewrite length_app_in_list.
do 4 rewrite fold_mat_nrows.
rewrite Hr1, Hr2, Hr3, Hr4, Nat.max_id.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  now move Hnz at top; subst n.
}
do 2 rewrite map2_map_l, map2_map_r.
do 2 rewrite map2_diag.
apply Nat.neq_0_lt_0 in Hnz.
erewrite map_ext_in. 2: {
  intros i Hi.
  erewrite map_ext_in. 2: {
    intros j Hj.
    unfold mat_ncols in Hj; cbn in Hj.
    rewrite List_app_hd1 in Hj; [ | now rewrite fold_mat_nrows, Hr5 ].
    rewrite fold_mat_ncols, Hc5 in Hj.
    unfold mat_mul_el; cbn.
    unfold mat_ncols; cbn.
    rewrite List_app_hd1. 2: {
      rewrite length_app_in_list.
      do 2 rewrite fold_mat_nrows.
      now rewrite Hr1, Hr2, Nat.max_id.
    }
    rewrite List_hd_nth_0.
    rewrite nth_map3_app; cycle 1. {
      now rewrite fold_mat_nrows, Hr1.
    } {
      now rewrite fold_mat_nrows, Hr2.
    }
    easy.
  }
  easy.
}
rewrite seq_app; cbn.
rewrite map_app.
erewrite map_ext_in. 2: {
  intros i Hi.
  apply in_seq in Hi.
  unfold mat_ncols; cbn.
  rewrite app_nth1. 2: {
    rewrite length_app_in_list.
    do 2 rewrite fold_mat_nrows.
    rewrite Hr1, Hr2, Nat.max_id; flia Hi.
  }
  rewrite List_app_hd1; [ | now rewrite fold_mat_nrows, Hr5 ].
  rewrite List_hd_nth_0.
  rewrite fold_corr_mat_ncols; cycle 1. {
    apply is_scm_mat_iff.
    split; [ easy | now rewrite Hc5 ].
  } {
    now rewrite Hr5.
  }
  rewrite Hc5.
  eapply map_ext_in.
  intros k Hk.
  rewrite app_length.
  do 2 rewrite <- List_hd_nth_0, fold_mat_ncols.
  rewrite Hc1, Hc2.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    rewrite nth_map3_app; cycle 1. {
      rewrite fold_mat_nrows, Hr1; flia Hi.
    } {
      rewrite fold_mat_nrows, Hr2; flia Hi.
    }
    easy.
  }
  now cbn.
}
cbn.
rewrite Hc5, Hc6.
f_equal. {
  apply map_ext_in.
  intros i Hi.
  rewrite map2_map_l, map2_map_r, map2_diag.
  apply map_ext_in.
  intros k Hk; move k before i.
  unfold mat_mul_el.
  rewrite Hc1, Hc2.
  rewrite (rngl_summation_split n); [ | flia ].
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    rewrite app_nth1. 2: {
      rewrite fold_corr_mat_ncols; cycle 1. {
        apply is_scm_mat_iff.
        split; [ now rewrite Hr1, Hc1 | now rewrite Hc1 ].
      } {
        apply in_seq in Hi; rewrite Hr1; flia Hi.
      }
      rewrite Hc1; flia Hnz Hj.
    }
    rewrite app_nth1. 2: {
      rewrite fold_mat_nrows, Hr5.
      flia Hj Hnz.
    }
    do 2 rewrite fold_mat_el.
    apply in_seq in Hi, Hk.
    rewrite <- Nat.sub_succ_l; [ | flia Hi ].
    rewrite <- Nat.sub_succ_l; [ | flia Hj ].
    rewrite <- Nat.sub_succ_l; [ | flia Hk ].
    do 3 rewrite Nat_sub_succ_1.
    easy.
  }
  f_equal.
  apply in_seq in Hi.
  rewrite (rngl_summation_shift n); [ | flia Hnz ].
  rewrite Nat.add_comm, Nat.add_sub, Nat.add_sub.
  apply rngl_summation_eq_compat.
  intros j Hj.
  rewrite app_nth2. 2: {
    rewrite fold_corr_mat_ncols; cycle 1. {
      apply is_scm_mat_iff.
      split; [ now rewrite Hr1, Hc1 | now rewrite Hc1 ].
    } {
      rewrite Hr1; flia Hi.
    }
    rewrite Hc1; flia Hj.
  }
  rewrite fold_corr_mat_ncols; cycle 1. {
    apply is_scm_mat_iff.
    split; [ now rewrite Hr1, Hc1 | now rewrite Hc1 ].
  } {
    rewrite Hr1; flia Hi.
  }
  rewrite Hc1, fold_mat_el.
  rewrite Nat.add_comm, Nat_sub_sub_swap, Nat.add_sub.
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite <- Nat.sub_succ_l; [ | easy ].
  do 2 rewrite Nat_sub_succ_1.
  f_equal.
  rewrite app_nth2. 2: {
    rewrite fold_mat_nrows, Hr5; flia Hj.
  }
  rewrite fold_mat_nrows, Hr5.
  rewrite Nat_sub_sub_swap, Nat.add_sub.
  rewrite fold_mat_el.
  apply in_seq in Hk.
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite <- Nat.sub_succ_l; [ | easy ].
  now do 2 rewrite Nat_sub_succ_1.
} {
  erewrite List_map_fun with (l' := seq 1 n) (d := 0); [ easy | | ]. {
    now do 2 rewrite seq_length.
  }
  cbn.
  intros i Hi.
  rewrite seq_length in Hi.
  rewrite map2_map_l, map2_map_r.
  unfold mat_ncols; cbn.
  rewrite app_nth2. 2: {
    rewrite seq_nth; [ | easy ].
    rewrite length_app_in_list.
    do 2 rewrite fold_mat_nrows.
    rewrite Hr1, Hr2, Nat.max_id; flia.
  }
  rewrite List_app_hd1; [ | now rewrite fold_mat_nrows, Hr5 ].
  do 2 rewrite <- List_hd_nth_0.
  rewrite fold_mat_ncols, Hc5.
  rewrite map2_diag.
  apply map_ext_in.
  intros k Hk; move k before i.
  rewrite app_length.
  do 2 rewrite fold_mat_ncols.
  rewrite Hc1, Hc2.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    rewrite seq_nth; [ | easy ].
    rewrite length_app_in_list.
    do 2 rewrite fold_mat_nrows.
    rewrite Hr1, Hr2, Nat.max_id.
    rewrite Nat.add_comm.
    rewrite <- Nat.sub_add_distr, Nat.add_sub.
    rewrite nth_map3_app; cycle 1. {
      now rewrite fold_mat_nrows, Hr3.
    } {
      now rewrite fold_mat_nrows, Hr4.
    }
    easy.
  }
  cbn.
  rewrite (rngl_summation_split n); [ | flia ].
  f_equal. {
    unfold mat_mul_el.
    rewrite Hc3.
    apply rngl_summation_eq_compat.
    intros j Hj.
    rewrite seq_nth; [ | easy ].
    rewrite app_nth1. 2: {
      rewrite fold_corr_mat_ncols; cycle 1. {
        apply is_scm_mat_iff.
        split; [ now rewrite Hr3, Hc3 | now rewrite Hc3 ].
      } {
        now rewrite Hr3.
      }
      rewrite Hc3; flia Hj Hnz.
    }
    rewrite fold_mat_el.
    rewrite <- Nat.sub_succ_l; [ | easy ].
    rewrite Nat_sub_succ_1.
    f_equal.
    rewrite app_nth1. 2: {
      rewrite fold_mat_nrows, Hr5.
      flia Hj Hnz.
    }
    rewrite fold_mat_el.
    apply in_seq in Hk.
    rewrite <- Nat.sub_succ_l; [ | easy ].
    rewrite <- Nat.sub_succ_l; [ | easy ].
    now do 2 rewrite Nat_sub_succ_1.
  } {
    rewrite (rngl_summation_shift n); [ | flia Hnz ].
    rewrite Nat.add_comm, Nat.add_sub, Nat.add_sub.
    unfold mat_mul_el; rewrite Hc4.
    apply rngl_summation_eq_compat.
    intros j Hj.
    rewrite app_nth2. 2: {
      rewrite fold_corr_mat_ncols; cycle 1. {
        apply is_scm_mat_iff.
        split; [ now rewrite Hr3, Hc3 | now rewrite Hc3 ].
      } {
        now rewrite Hr3.
      }
      rewrite Hc3; flia Hj.
    }
    rewrite fold_corr_mat_ncols; cycle 1. {
      apply is_scm_mat_iff.
      split; [ now rewrite Hr3, Hc3 | now rewrite Hc3 ].
    } {
      now rewrite Hr3.
    }
    rewrite Hc3, Nat_sub_sub_swap.
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite fold_mat_el.
    rewrite <- Nat.sub_succ_l; [ | easy ].
    rewrite Nat_sub_succ_1.
    rewrite app_nth2. 2: {
      rewrite fold_mat_nrows, Hr5; flia Hj.
    }
    rewrite fold_mat_nrows, Hr5, Nat_sub_sub_swap.
    now rewrite Nat.add_sub, seq_nth.
  }
}
Qed.

Definition base_vector_1 dim :=
  mk_vect (1%L :: repeat 0%L (dim - 1)).

Definition A_Sn_eigenvector_of_sqrt_Sn n μ (V : vector T) : vector T :=
  (mat_of_mat_list_list [[(mA n + μ × mI (2 ^ n))]; [mI (2 ^ n)]] • V)%M.

Theorem rngl_mul_eq_if : ∀ a b c d, a = c → b = d → (a * b = c * d)%L.
Proof.
intros * Hac Hbd.
now subst a b.
Qed.

Theorem mat_of_mat_list_list_mul_scal_l : ∀ μ mll,
  (μ × mat_of_mat_list_list mll =
   mat_of_mat_list_list (map (map (mat_mul_scal_l μ)) mll))%M.
Proof.
intros.
unfold mat_of_mat_list_list, "×"%M; cbn.
f_equal.
rewrite map_map.
unfold flatten_list_list.
do 2 rewrite flat_map_concat_map.
rewrite concat_map.
do 3 rewrite map_map.
unfold fold_app_in_list, iter_list; cbn.
f_equal.
apply map_ext_in.
intros la Hla.
symmetry.
rewrite List_fold_left_map.
rewrite List_fold_left_map.
symmetry.
cbn.
clear Hla.
assert (H : ∀ lb,
  map (map (rngl_mul μ))
    (fold_left (map3 (app (A:=T))) (map (mat_list_list (T:=T)) la) lb) =
  fold_left
    (λ (c : list (list T)) (b : matrix T),
       map3 (app (A:=T)) c (map (map (rngl_mul μ)) (mat_list_list b))) la
         (map (map (rngl_mul μ)) lb)). {
  induction la as [| a]; intros; [ easy | cbn ].
  rewrite IHla.
  f_equal.
  remember (mat_list_list a) as ll.
  clear Heqll.
  revert lb.
  induction ll as [| lc]; intros. {
    now do 2 rewrite map3_nil_r.
  }
  cbn.
  destruct lb as [| b]; [ easy | cbn ].
  rewrite IHll; f_equal.
  apply map_app.
}
apply H.
Qed.

Theorem is_corr_mat_of_list_list_squ_1_2 : ∀ MA MB,
  mat_nrows MA = mat_nrows MB
  → is_square_matrix MA = true
  → is_square_matrix MB = true
  → is_correct_matrix (mat_of_mat_list_list [[MA]; [MB]]) = true.
Proof.
intros * Hab Ha Hb.
specialize (squ_mat_ncols MA Ha) as Hcan.
specialize (squ_mat_ncols MB Hb) as Hcbn.
remember (mat_nrows MA) as n eqn:Hn.
rename Hn into Hra; rename Hab into Hrb.
symmetry in Hra, Hrb.
rewrite Hrb in Hcbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  apply is_scm_mat_iff in Ha, Hb.
  destruct Ha as (_ & Hca).
  destruct Hb as (_ & Hcb).
  rewrite Hra in Hca; rewrite Hrb in Hcb.
  apply is_scm_mat_iff.
  split. {
    cbn; intros Hc.
    unfold mat_of_mat_list_list; cbn.
    rewrite app_nil_r.
    unfold fold_app_in_list, iter_list; cbn.
    unfold mat_ncols; cbn.
    rewrite app_length.
    do 2 rewrite fold_mat_nrows.
    now rewrite Hra, Hrb.
  } {
    unfold mat_ncols; cbn.
    rewrite app_nil_r.
    unfold fold_app_in_list, iter_list; cbn.
    rewrite List_app_hd2. 2: {
      now rewrite fold_mat_nrows, Hra; unfold "≥".
    }
    cbn.
    rewrite fold_mat_ncols, Hcbn.
    intros l Hl.
    apply in_app_or in Hl.
    destruct Hl as [Hl| Hl]; [ now apply Hca | now apply Hcb ].
  }
}
apply Nat.neq_0_lt_0 in Hnz.
apply is_scm_mat_iff.
split. {
  cbn; intros Hc.
  unfold mat_ncols in Hc.
  unfold mat_of_mat_list_list in Hc; cbn in Hc.
  rewrite List_app_hd1 in Hc. 2: {
    unfold fold_app_in_list, iter_list; cbn.
    rewrite fold_mat_nrows.
    congruence.
  }
  unfold fold_app_in_list, iter_list in Hc; cbn in Hc.
  rewrite fold_mat_ncols in Hc.
  now rewrite <- Hcan, Hc in Hnz.
} {
  intros la Hla.
  unfold mat_ncols; cbn.
  rewrite app_nil_r.
  rewrite List_app_hd1. 2: {
    unfold fold_app_in_list, iter_list; cbn.
    rewrite fold_mat_nrows.
    congruence.
  }
  unfold fold_app_in_list, iter_list; cbn.
  rewrite fold_mat_ncols.
  cbn in Hla.
  unfold fold_app_in_list, iter_list in Hla; cbn in Hla.
  rewrite app_nil_r in Hla.
  apply in_app_or in Hla.
  rewrite Hcan.
  destruct Hla as [Hla| Hla]. {
    apply is_scm_mat_iff in Ha.
    destruct Ha as (_ & Hca).
    rewrite Hra in Hca.
    now apply Hca.
  } {
    apply is_scm_mat_iff in Hb.
    destruct Hb as (_ & Hcb).
    rewrite Hrb in Hcb.
    now apply Hcb.
  }
}
Qed.

Theorem is_corr_mat_of_list_list_1 : ∀ n μ,
  is_correct_matrix
    (mat_of_mat_list_list [[(mA n + μ × mI (2 ^ n))%M]; [mI (2 ^ n)]]) = true.
Proof.
intros.
apply is_corr_mat_of_list_list_squ_1_2. {
  rewrite mat_add_nrows, mA_nrows.
  rewrite mat_mul_scal_l_nrows, mI_nrows.
  apply Nat.min_id.
} {
  apply is_scm_mat_iff; cbn.
  unfold mat_ncols; cbn.
  rewrite map2_length, fold_mat_nrows, mA_nrows.
  do 2 rewrite map_length.
  rewrite seq_length, Nat.min_id.
  rewrite List_hd_nth_0.
  rewrite map2_nth with (a := []) (b := []); cycle 1. {
    rewrite fold_mat_nrows, mA_nrows.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  } {
    do 2 rewrite map_length.
    rewrite seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map2_length.
  rewrite <- List_hd_nth_0, fold_mat_ncols, mA_ncols.
  rewrite (List_map_nth' []). 2: {
    rewrite List_map_seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map_length.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite List_map_seq_length, Nat.min_id.
  split; [ easy | ].
  intros la Hla.
  apply in_map2_iff in Hla.
  destruct Hla as (i & Hi & lb & lc & Hla).
  rewrite fold_mat_nrows, mA_nrows in Hi.
  do 2 rewrite map_length in Hi.
  rewrite seq_length, Nat.min_id in Hi.
  subst la.
  rewrite map2_length.
  rewrite fold_corr_mat_ncols; cycle 1. {
    apply mA_is_correct.
  } {
    now rewrite mA_nrows.
  }
  rewrite mA_ncols.
  rewrite (List_map_nth' []); [ | now rewrite List_map_seq_length ].
  rewrite map_length.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  now rewrite List_map_seq_length, Nat.min_id.
} {
  apply mI_is_square_matrix.
}
Qed.

Theorem mat_ncols_mat_list_list_1_2 : ∀ n μ,
  mat_ncols
    (mat_of_mat_list_list [[(mA n + μ × mI (2 ^ n))%M]; [mI (2 ^ n)]]) =
  2 ^ n.
Proof.
intros.
unfold mat_ncols; cbn.
rewrite app_nil_r.
unfold fold_app_in_list, iter_list; cbn.
rewrite List_app_hd1. 2: {
  rewrite map2_length, fold_mat_nrows, mA_nrows.
  do 2 rewrite map_length.
  rewrite seq_length, Nat.min_id.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite List_hd_nth_0.
rewrite map2_nth with (a := []) (b := []); cycle 1. {
  rewrite fold_mat_nrows, mA_nrows.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
} {
  do 2 rewrite map_length.
  rewrite seq_length.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite map2_length.
rewrite <- List_hd_nth_0.
rewrite fold_mat_ncols, mA_ncols.
rewrite (List_map_nth' []). 2: {
  rewrite List_map_seq_length.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite map_length.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
now rewrite List_map_seq_length, Nat.min_id.
Qed.

Theorem An_eigen_equation_for_sqrt_n :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_eqb = true →
  ∀ n μ, (μ * μ)%L = rngl_mul_nat 1 n →
  match n with
  | 0 => ∀ V, vect_size V = 1 → (mA 0 • V = μ × V)%V
  | S n' =>
      ∀ U V,
      vect_size U = 2 ^ n'
      → V = A_Sn_eigenvector_of_sqrt_Sn n' μ U
      → (mA (S n') • V = μ × V)%V
  end.
Proof.
intros Hic Hop Hin Heq * Hμ.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
destruct n. {
  intros V Hv.
  cbn in Hμ, V |-*.
  assert (H : μ = 0%L). {
    remember (rngl_eqb μ 0%L) as μz eqn:Hμz; symmetry in Hμz.
    destruct μz; [ now apply rngl_eqb_eq | ].
    apply rngl_eqb_neq in Hμz; [ | easy ].
    apply (f_equal (rngl_mul (μ⁻¹)%L)) in Hμ.
    rewrite rngl_mul_0_r in Hμ; [ | easy ].
    rewrite rngl_mul_assoc in Hμ.
    rewrite (rngl_mul_inv_l Hon) in Hμ; [ | easy | easy ].
    now rewrite (rngl_mul_1_l Hon) in Hμ.
  }
  subst μ.
  apply vector_eq; [ | cbn; rewrite map_length; easy ].
  intros i Hi.
  cbn in Hi.
  replace i with 1 by flia Hi.
  unfold vect_dot_mul; cbn.
  destruct V as (la); cbn.
  destruct la as [| a]; [ easy | ].
  destruct la; [ cbn | easy ].
  unfold vect_dot_mul; cbn.
  unfold iter_list; cbn.
  now rewrite rngl_add_0_l, rngl_mul_0_l.
}
intros * HU HV.
subst V.
unfold A_Sn_eigenvector_of_sqrt_Sn.
rewrite mat_vect_mul_assoc; cycle 1. {
  easy.
} {
  apply mA_is_correct.
} {
  apply is_corr_mat_of_list_list_1.
} {
  rewrite mA_ncols.
  cbn - [ "^" ].
  rewrite app_nil_r.
  rewrite app_length.
  unfold fold_app_in_list, iter_list.
  cbn - [ "^" ].
  rewrite map2_length, fold_mat_nrows, mA_nrows.
  do 2 rewrite map_length.
  rewrite seq_length, Nat.min_id.
  now cbn; rewrite Nat.add_0_r.
} {
  rewrite HU.
  apply mat_ncols_mat_list_list_1_2.
}
rewrite mat_mul_scal_vect_assoc; cycle 1. {
  easy.
} {
  apply is_corr_mat_of_list_list_1.
} {
  rewrite HU.
  apply mat_ncols_mat_list_list_1_2.
}
f_equal; cbn.
rewrite m_o_mll_2x2_2x1 with (n := 2 ^ n); cycle 1. {
  apply mA_is_square_matrix.
} {
  apply mI_is_square_matrix.
} {
  apply squ_mat_add_is_squ. {
    apply mA_is_square_matrix.
  } {
    apply squ_mat_mul_scal_l_is_squ.
    apply mI_is_square_matrix.
  }
} {
  apply mA_nrows.
} {
  apply mI_nrows.
} {
  apply mI_nrows.
} {
  cbn; rewrite map_length.
  apply mA_nrows.
} {
  rewrite mat_add_nrows, mA_nrows.
  rewrite mat_mul_scal_l_nrows, mI_nrows.
  apply Nat.min_id.
} {
  apply mI_ncols.
} {
  unfold mat_ncols; cbn.
  rewrite (List_map_hd []). 2: {
    rewrite fold_mat_nrows, mA_nrows.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map_length, fold_mat_ncols.
  apply mA_ncols.
} {
  apply mI_ncols.
}
rewrite mat_of_mat_list_list_mul_scal_l; cbn.
assert (Hcma : is_correct_matrix (mA n) = true) by apply mA_is_correct.
assert (Hcmμi : is_correct_matrix (μ × mI (2 ^ n)) = true). {
  apply is_correct_matrix_mul_scal_l.
  apply mI_is_correct_matrix.
}
assert (Hμir : mat_nrows (μ × mI (2 ^ n)) = 2 ^ n). {
  rewrite mat_mul_scal_l_nrows.
  apply mI_nrows.
}
assert (Hμic : mat_ncols (μ × mI (2 ^ n)) = 2 ^ n). {
  rewrite mat_mul_scal_l_ncols.
  apply mI_ncols.
}
rewrite mat_mul_add_distr_l; [ | easy | easy | | | | ]; cycle 1. {
  rewrite mA_nrows.
  now apply Nat.pow_nonzero.
} {
  now rewrite mA_nrows, mA_ncols.
} {
  now rewrite mA_nrows.
} {
  rewrite mA_ncols.
  rewrite mat_mul_scal_l_ncols.
  symmetry; apply mI_ncols.
}
rewrite lemma_2_A_n_2_eq_n_I; [ | easy ].
rewrite mat_mul_mul_scal_l; [ | easy | easy | | | ]; cycle 1. {
  apply mI_is_correct_matrix.
} {
  rewrite mA_ncols.
  now apply Nat.pow_nonzero.
} {
  now rewrite mA_ncols, mI_nrows.
}
rewrite (mat_mul_1_r Hon); [ | easy | easy | symmetry; apply mA_ncols ].
rewrite (mat_mul_1_r Hon); [ | easy | | ]; cycle 1. {
  apply mI_is_correct_matrix.
} {
  symmetry; apply mI_ncols.
}
rewrite mat_mul_add_distr_l; [ | easy | easy | | | | ]; cycle 1. {
  rewrite mA_nrows.
  now apply Nat.pow_nonzero.
} {
  now rewrite mI_ncols, mA_nrows.
} {
  now rewrite mA_nrows.
} {
  rewrite mA_ncols.
  now rewrite mat_mul_scal_l_ncols, mI_ncols.
}
rewrite (mat_mul_1_l Hon); [ | easy | easy | symmetry; apply mA_nrows ].
rewrite (mat_mul_1_l Hon); [ | easy | easy | easy ].
rewrite (mat_mul_1_r Hon); [ | easy | | ]; cycle 1. {
  now apply mat_opp_is_correct.
} {
  unfold mat_ncols; cbn.
  rewrite (List_map_hd []). 2: {
    rewrite fold_mat_nrows, mA_nrows.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map_length; cbn.
  rewrite fold_mat_ncols.
  symmetry; apply mA_ncols.
}
rewrite fold_mat_sub.
rewrite (mat_add_comm (mA n)).
rewrite mat_add_sub; [ | easy | easy | easy | | ]; cycle 1. {
  now rewrite mA_nrows.
} {
  now rewrite mA_ncols.
}
rewrite mat_add_add_swap.
rewrite mat_mul_scal_l_add_distr_l.
f_equal; f_equal; f_equal; f_equal.
rewrite mat_mul_scal_l_mul_assoc.
rewrite Hμ; cbn.
rewrite mat_add_comm, mat_mul_scal_l_add_distr_r.
now rewrite mat_mul_scal_1_l.
Qed.

Theorem A_n_eigenvalue_squared_is_n :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_eqb = true →
  rngl_has_inv = true →
  ∀ n μ (V : vector T),
  vect_size V = 2 ^ n
  → V ≠ vect_zero (2 ^ n)
  → (mA n • V = μ × V)%V
  → (μ * μ)%L = rngl_mul_nat 1 n.
Proof.
intros Hic Hop Heq Hin * Hvs Hvr Hav.
assert (Hi1 : rngl_has_inv_and_1_or_quot = true). {
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hin)).
move Hiq before Hin.
specialize (lemma_2_A_n_2_eq_n_I Hop n) as Ha.
specialize (mA_is_correct n) as Hac.
specialize (mI_is_correct_matrix (2 ^ n)) as Hicm.
assert (Hcs : mat_ncols (mA n) = vect_size V) by now rewrite mA_ncols.
(* μ * μ = rngl_mul_nat 1 n *)
apply vect_mul_scal_reg_r with (V := V); [ easy | easy | congruence | ].
(* (μ * μ) × V = rngl_mul_nat 1 n × V *)
rewrite <- vect_mul_scal_l_assoc.
(* μ × (μ × V) = rngl_mul_nat 1 n × V *)
rewrite <- Hav.
(* μ × (mA n . V) = rngl_mul_nat 1 n × V *)
rewrite mat_mul_scal_vect_comm; [ | easy | easy | easy | easy ].
(* mA n . (μ × V) = rngl_mul_nat 1 n × V *)
rewrite <- Hav.
(* mA n . (mA n . V) = rngl_mul_nat 1 n × V *)
rewrite mat_vect_mul_assoc; [ | easy | easy | easy | | easy ]. 2: {
  now rewrite mA_nrows, mA_ncols.
}
(* (mA n * mA n) . V = rngl_mul_nat 1 n × V *)
rewrite Ha.
(* (rngl_mul_nat 1 n × mI (2 ^ n)) . V = rngl_mul_nat 1 n × V *)
rewrite <- mat_mul_scal_vect_assoc; [ | easy | easy | ]. 2: {
  now rewrite mI_ncols.
}
(* rngl_mul_nat 1 n × (mI (2 ^ n) . V) = rngl_mul_nat 1 n × V *)
rewrite mat_vect_mul_1_l; easy.
Qed.

Definition is_eigenvector_of_An n μ (V : vector T) :=
  vect_size V = 2 ^ n ∧ V ≠ vect_zero (2 ^ n) ∧ (mA n • V = μ × V)%V.

Theorem μ_is_ev_of_An_iff_μ2_eq_n :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_eqb = true →
  rngl_has_inv = true →
  rngl_characteristic ≠ 1 →
  ∀ n μ,
  (∃ V, is_eigenvector_of_An n μ V) ↔ (μ * μ = rngl_mul_nat 1 n)%L.
Proof.
intros Hic Hop Heq Hin H10 *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before H10.
split. {
  intros HV.
  destruct HV as (V & Hvz & Hv).
  now apply A_n_eigenvalue_squared_is_n with (V := V).
} {
  intros Hμ.
  destruct n. {
    cbn in Hμ |-*.
    unfold is_eigenvector_of_An; cbn.
    exists (base_vector_1 1).
    split; [ easy | ].
    split. {
      intros H.
      injection H; clear H; intros H.
      now apply rngl_1_neq_0_iff in H.
    }
    specialize An_eigen_equation_for_sqrt_n as H1.
    specialize (H1 Hic Hop Hin Heq).
    now apply (H1 0).
  }
  remember (A_Sn_eigenvector_of_sqrt_Sn n μ (base_vector_1 (2 ^ n))) as V
    eqn:Hv.
  exists V.
  split. {
    subst V.
    cbn - [ "^" ].
    rewrite app_nil_r.
    rewrite map_length, app_length.
    unfold fold_app_in_list, iter_list.
    cbn - [ "^" ].
    rewrite map2_length, fold_mat_nrows, mA_nrows.
    do 2 rewrite map_length.
    rewrite seq_length, Nat.min_id.
    now cbn; rewrite Nat.add_0_r.
  }
  split. 2: {
    specialize An_eigen_equation_for_sqrt_n as H1.
    specialize (H1 Hic Hop Hin Heq).
    specialize (H1 (S n) μ Hμ).
    cbn - [ mA ] in H1.
    specialize (H1 (base_vector_1 (2 ^ n)) V).
    cbn in H1.
    rewrite repeat_length in H1.
    rewrite <- Nat.sub_succ_l in H1. 2: {
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    cbn in H1; rewrite Nat.sub_0_r in H1.
    now specialize (H1 eq_refl Hv).
  }
  (* V ≠ vect_zero (2 ^ n) *)
  subst V.
  unfold A_Sn_eigenvector_of_sqrt_Sn.
  unfold mat_of_mat_list_list.
  cbn; rewrite Nat.add_0_r.
  rewrite app_nil_r.
  unfold fold_app_in_list, iter_list.
  cbn.
  intros H.
  injection H; clear H; intros H1.
  rewrite map_app in H1.
  rewrite repeat_app in H1.
  do 2 rewrite map_map in H1.
  apply List_app_eq_app' in H1. 2: {
    rewrite map_length, map2_length, repeat_length.
    rewrite fold_mat_nrows, mA_nrows.
    now rewrite List_map_seq_length, Nat.min_id.
  }
  destruct H1 as (H1, H2).
  rewrite List_repeat_as_map in H2.
  apply ext_in_map with (a := 0) in H2. 2: {
    apply in_seq.
    split; [ easy | ].
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  unfold vect_dot_mul in H2.
  cbn in H2.
  replace (2 ^ n) with (1 + (2 ^ n - 1)) in H2 at 1. 2: {
    rewrite Nat.add_comm.
    apply Nat.sub_add.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite seq_app in H2.
  cbn in H2.
  rewrite (rngl_mul_1_l Hon) in H2.
  rewrite rngl_summation_list_cons in H2.
  rewrite all_0_rngl_summation_list_0 in H2. 2: {
    intros i Hi.
    rewrite <- seq_shift in Hi.
    rewrite map_map in Hi.
    rewrite map2_map_l in Hi.
    rewrite List_repeat_as_map in Hi.
    rewrite map2_map_r in Hi.
    rewrite map2_diag in Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hi & Hj); subst i.
    now apply rngl_mul_0_r.
  }
  rewrite rngl_add_0_r in H2.
  now apply rngl_1_neq_0_iff in H2.
}
Qed.

End a.
