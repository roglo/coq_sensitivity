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
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc RingLike MyVector Matrix.
Require Import RLsummation.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

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

(*
End a.
Check @mA.
Require Import ZArith Zrl.
Open Scope Z_scope.
Compute list_list_of_mat (@mA Z Z_ring_like_op 2).
Compute list_list_of_mat (@mA Z Z_ring_like_op 3).
...
*)

(*
Theorem flatten_list_list_length : ∀ A f (llll : list (list (list (list A)))),
  length (flatten_list_list f llll) =
  length llll * length (hd [] llll) * length (hd [] (hd [] llll)).
Proof.
intros.
unfold flatten_list_list.
rewrite List_flat_map_length.
rewrite map_map.
induction llll as [| lll]; [ easy | cbn ].
rewrite IHllll.
(* pas sûr qu'il soit bon, ce lemme *)

Check flatten_list_list (@app nat) [[[[1;2];[3;4];[5;6]];[[7;8;9;10]]]].
Compute length (flatten_list_list (@app nat) [[[[1;2];[3;4];[5;6]];[[7;8;9;10]]];[[[11;12]]]]).
Compute length [[[[1;2];[3;4];[5;6]];[[7;8;9;10]]];[[[11;12]]]].
...
*)

Theorem length_app_in_list : ∀ la lb,
  length (map3 (app (A := T)) la lb) = max (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem length_hd_app_in_list: ∀ la lb : list (list T),
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
rewrite List_hd_nth_0.
rewrite app_nth1. 2: {
  unfold fold_app_in_list, iter_list; cbn.
  rewrite length_app_in_list.
  rewrite map_length, seq_length.
  rewrite fold_mat_nrows.
  rewrite mA_nrows, Nat.max_id.
  apply Nat.neq_0_lt_0.
  now apply Nat.pow_nonzero.
}
unfold mat_ncols in IHn.
rewrite <- List_hd_nth_0.
unfold fold_app_in_list, iter_list; cbn.
rewrite length_hd_app_in_list, IHn.
rewrite List_map_hd with (a := 0). 2: {
  intros H.
  apply List_seq_eq_nil in H.
  revert H.
  now apply Nat.pow_nonzero.
}
rewrite map_length, seq_length; cbn.
now rewrite Nat.add_0_r.
Qed.

Theorem nth_app_in_list : ∀ i lla llb d,
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

Theorem in_app_in_list : ∀ la lla llb,
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
    split; [ flia | ].
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
  split; [ flia | easy ].
}
specialize (IHlla _ Hla).
destruct IHlla as (n & Hn & Hc).
exists (S n); cbn.
split; [ now apply -> Nat.succ_lt_mono | easy ].
Qed.

Theorem mA_is_correct : ∀ n, is_correct_matrix (mA n).
Proof.
intros.
induction n. {
  cbn.
  now apply mZ_is_correct_matrix.
}
split; [ now rewrite mA_nrows, mA_ncols | ].
intros la Hla.
rewrite mA_ncols.
cbn in Hla.
rewrite app_nil_r in Hla.
apply in_app_or in Hla.
destruct Hla as [Hla| Hla]. {
  apply in_app_in_list in Hla.
  destruct Hla as (i & Him & Hla).
  unfold map3 in Him.
  rewrite fold_mat_nrows, mA_nrows in Him.
  rewrite map_length, seq_length in Him.
  rewrite Nat.max_id in Him.
  subst la.
  rewrite app_length.
  unfold map3.
  rewrite fold_corr_mat_ncols; [ | easy | now rewrite mA_nrows ].
  rewrite mA_ncols.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite map_length, seq_length.
  now cbn; rewrite Nat.add_0_r.
} {
  apply in_app_in_list in Hla.
  destruct Hla as (i & Him & Hla).
  unfold map3 in Him.
  rewrite map_length, seq_length in Him.
  rewrite map_length in Him.
  rewrite fold_mat_nrows, mA_nrows, Nat.max_id in Him.
  subst la; cbn.
  rewrite app_length.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite map_length, seq_length.
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

Theorem mA_is_square_matrix : ∀ n, is_square_matrix (2 ^ n) (mA n) = true.
Proof.
intros.
apply is_sm_mat_iff.
rewrite mA_nrows, mA_ncols.
split; [ easy | ].
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
  apply in_app_in_list in Hla.
  destruct Hla as (i & Him & Hla); subst la.
  unfold map3 in Him.
  rewrite fold_mat_nrows, mA_nrows in Him.
  rewrite map_length, seq_length, Nat.max_id in Him.
  rewrite app_length; cbn.
  rewrite fold_corr_mat_ncols; cycle 1. {
    apply mA_is_correct.
  } {
    now rewrite mA_nrows.
  }
  rewrite mA_ncols.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite map_length, seq_length; cbn.
  now rewrite Nat.add_0_r.
} {
  apply in_app_in_list in Hla.
  destruct Hla as (i & Him & Hla); subst la.
  unfold map3 in Him.
  rewrite map_length, seq_length in Him.
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
  apply Nat.sub_lt; [ | flia ].
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
apply Nat.sub_lt; [ | flia ].
apply Nat.neq_0_lt_0.
now apply Nat.pow_nonzero.
Qed.

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I :
  rngl_has_opp = true →
  ∀ n, (mA n * mA n)%M = (rngl_of_nat n × mI (2 ^ n))%M.
Proof.
intros Hro *.
unfold "*"%M, "×"%M.
cbn; f_equal.
rewrite mA_nrows.
rewrite map_map.
apply map_ext_in.
intros i Hi.
rewrite mA_ncols.
rewrite map_map.
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
  rewrite rngl_mul_0_l; [ | now left ].
  rewrite rngl_mul_0_l; [ easy | now left ].
}
rewrite (rngl_summation_split (2 ^ n - 1)). 2: {
  split; [ flia | ].
  apply -> Nat.succ_le_mono.
  apply Nat.sub_le_mono_r.
  apply Nat.pow_le_mono_r; [ easy | flia ].
}
rewrite Nat.sub_add. 2: {
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
cbn - [ Nat.pow ].
rewrite rngl_add_comm.
rewrite app_nil_r.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  unfold fold_app_in_list, iter_list; cbn.
  rewrite app_nth2 with (n := j). 2: {
    rewrite length_app_in_list.
    rewrite map_length, seq_length.
    now rewrite fold_mat_nrows, mA_nrows, Nat.max_id.
  }
  rewrite length_app_in_list.
  rewrite fold_mat_nrows, mA_nrows.
  rewrite map_length, seq_length, Nat.max_id.
  rewrite nth_app_in_list; cycle 1. {
    now rewrite map_length, seq_length; apply le_pow_succ_sub_1_lt.
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
    rewrite app_nth1. 2: {
      rewrite length_app_in_list.
      rewrite map_length, seq_length.
      now rewrite fold_mat_nrows, mA_nrows, Nat.max_id.
    }
    rewrite nth_app_in_list; cycle 1. {
      now rewrite fold_mat_nrows, mA_nrows.
    } {
      now rewrite map_length, seq_length.
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
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    unfold fold_app_in_list, iter_list; cbn.
    rewrite app_nth1 with (n := j). 2: {
      rewrite length_app_in_list.
      rewrite map_length, seq_length.
      rewrite fold_mat_nrows, mA_nrows, Nat.max_id.
      now apply le_pow_sub_1_lt.
    }
    rewrite app_nth1. 2: {
      rewrite length_app_in_list.
      rewrite map_length, seq_length.
      now rewrite fold_mat_nrows, mA_nrows, Nat.max_id.
    }
    rewrite nth_app_in_list; cycle 1. {
      now rewrite fold_mat_nrows, mA_nrows.
    } {
      now rewrite map_length, seq_length.
    }
    rewrite nth_app_in_list; cycle 1. {
      rewrite fold_mat_nrows, mA_nrows.
      now apply le_pow_sub_1_lt.
    } {
      rewrite map_length, seq_length.
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
        now rewrite map_length, seq_length.
      }
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ cbn | easy ].
      easy.
    }
    rewrite rngl_add_comm.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
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
      easy.
    }
    rewrite rngl_add_comm.
    rewrite IHn; [ | easy | easy ].
    rewrite rngl_mul_add_distr_r, rngl_mul_1_l.
    f_equal.
    rewrite rngl_summation_shift. 2: {
      cbn; rewrite Nat.add_0_r.
      rewrite <- Nat.add_sub_assoc; [ flia | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    cbn; rewrite Nat.add_0_r.
    rewrite Nat_sub_sub_swap.
    rewrite Nat.add_sub.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      now rewrite Nat.add_comm, Nat.add_sub.
    }
    cbn.
    destruct (lt_eq_lt_dec i k) as [[Hik| Hik]| Hik]. {
      rewrite δ_ndiag; [ | flia Hik ].
      apply all_0_rngl_summation_0.
      intros j Hj.
      unfold δ.
      do 2 rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec i j) as [Hij| Hij]. {
        destruct (Nat.eq_dec j k) as [Hjk| Hjk]. {
          rewrite Hij, Hjk in Hik; flia Hik.
        }
        now apply rngl_mul_0_r; left.
      } {
        destruct (Nat.eq_dec j k) as [Hjk| Hjk]. {
          now apply rngl_mul_0_l; left.
        }
        now apply rngl_mul_0_l; left.
      }
    } {
      subst k.
      rewrite δ_diag.
      rewrite (rngl_summation_split3 i); [ | split; flia Hin ].
      rewrite all_0_rngl_summation_0. 2: {
        intros j Hj.
        rewrite δ_ndiag; [ | flia Hj ].
        now apply rngl_mul_0_l; left.
      }
      rewrite rngl_add_0_l.
      rewrite δ_diag, rngl_mul_1_l.
      rewrite all_0_rngl_summation_0. 2: {
        intros j Hj.
        rewrite δ_ndiag; [ | flia Hj ].
        now apply rngl_mul_0_l; left.
      }
      apply rngl_add_0_r.
    } {
      rewrite δ_ndiag; [ | flia Hik ].
      apply all_0_rngl_summation_0.
      intros j Hj.
      unfold δ.
      do 2 rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec i j) as [Hij| Hij]. {
        destruct (Nat.eq_dec j k) as [Hjk| Hjk]. {
          rewrite Hij, Hjk in Hik; flia Hik.
        }
        now apply rngl_mul_0_r; left.
      } {
        destruct (Nat.eq_dec j k) as [Hjk| Hjk]. {
          now apply rngl_mul_0_l; left.
        }
        now apply rngl_mul_0_l; left.
      }
    }
  } {
    apply Nat.nlt_ge in Hkn.
    rewrite δ_ndiag; [ | flia Hin Hkn ].
    rewrite rngl_mul_0_r; [ | now left ].
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite app_nth2. 2: {
        now rewrite map_length, seq_length.
      }
      rewrite map_length, seq_length.
      rewrite (List_map_nth' 0%F). 2: {
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
    rewrite rngl_summation_shift. 2: {
      cbn; rewrite Nat.add_0_r.
      rewrite <- Nat.add_sub_assoc; [ flia | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite <- rngl_opp_summation; [ | easy ].
    cbn; rewrite Nat.add_0_r.
    rewrite Nat_sub_sub_swap, Nat.add_sub.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      now rewrite Nat.add_comm, Nat.add_sub.
    }
    rewrite rngl_add_comm.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite app_nth2. 2: {
        rewrite fold_corr_mat_ncols; cycle 2. {
          rewrite mA_nrows.
          now apply le_pow_sub_1_lt.
        } {
          now rewrite mA_ncols.
        }
        apply mA_is_correct.
      }
      rewrite fold_corr_mat_ncols; cycle 1. {
        apply mA_is_correct.
      } {
        rewrite mA_nrows.
        now apply le_pow_sub_1_lt.
      }
      rewrite mA_ncols.
      rewrite (List_map_nth' 0). 2: {
        now rewrite seq_length; apply le_pow_sub_1_lt.
      }
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length.
        apply le_pow_succ_sub_1_lt; flia Hk.
      }
      rewrite seq_nth; [ | now apply le_pow_sub_1_lt ].
      rewrite seq_nth; [ | apply le_pow_succ_sub_1_lt; flia Hk ].
      now cbn.
    }
    cbn.
    rewrite fold_rngl_sub; [ | easy ].
    rewrite (rngl_summation_split3 (k - 2 ^ n)). 2: {
      split; [ flia | ].
      apply (Nat.add_le_mono_r _ _ (2 ^ n)).
      rewrite Nat.sub_add; [ | easy ].
      cbn in Hk; rewrite Nat.add_0_r in Hk.
      flia Hk.
    }
    rewrite δ_diag, rngl_mul_1_r.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_r; left.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_r; left.
    }
    rewrite rngl_add_0_r.
    rewrite (rngl_summation_split3 i). 2: {
      split; [ flia | flia Hin ].
    }
    rewrite δ_diag, rngl_mul_1_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_l; left.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_l; left.
    }
    rewrite rngl_add_0_r.
    now apply rngl_sub_diag; left.
  }
} {
  apply Nat.nlt_ge in Hin.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    rewrite app_nth2. 2: {
      rewrite length_app_in_list.
      rewrite map_length, seq_length.
      now rewrite fold_mat_nrows, mA_nrows, Nat.max_id.
    }
    rewrite length_app_in_list.
    rewrite map_length, seq_length.
    rewrite fold_mat_nrows, mA_nrows.
    rewrite Nat.max_id.
    rewrite nth_app_in_list; cycle 1. {
      rewrite map_length, seq_length.
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
      now rewrite map_length, seq_length.
    }
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite map_length, seq_length.
    rewrite (List_map_nth' []). 2: {
      rewrite fold_mat_nrows, mA_nrows.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite (List_map_nth' 0%F). 2: {
      rewrite fold_corr_mat_ncols; cycle 1. {
        apply mA_is_correct.
      } {
        rewrite mA_nrows.
        apply le_pow_succ_sub_1_lt; flia Hi.
      }
      now rewrite mA_ncols; apply le_pow_succ_sub_1_lt.
    }
    now rewrite fold_mat_el.
  }
  cbn - [ "^" ].
  destruct (lt_dec k (2 ^ n)) as [Hkn| Hkn]. {
    rewrite δ_ndiag; [ | flia Hin Hkn ].
    rewrite rngl_mul_0_r; [ | now left ].
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite app_nth1. 2: {
        now rewrite map_length, seq_length.
      }
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ cbn | easy ].
      rewrite rngl_mul_opp_l; [ | easy ].
      easy.
    }
    cbn - [ "^" ].
    rewrite <- rngl_opp_summation; [ | easy ].
    rewrite (rngl_summation_split3 (k + 2 ^ n)). 2: {
      split; [ flia | cbn; flia Hkn ].
    }
    rewrite Nat.add_sub, δ_diag, rngl_mul_1_r.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj Hkn ].
      now apply rngl_mul_0_r; left.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite δ_ndiag; [ | flia Hj Hkn ].
      now apply rngl_mul_0_r; left.
    }
    rewrite rngl_add_0_r.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      unfold fold_app_in_list, iter_list; cbn.
      rewrite app_nth2. 2: {
        rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
        now rewrite map_length, seq_length, Nat.max_id.
      }
      rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
      rewrite map_length, seq_length, Nat.max_id.
      rewrite nth_app_in_list; cycle 1. {
        rewrite map_length, seq_length.
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
    rewrite (rngl_summation_split3 (i - 2 ^ n)). 2: {
      split; [ flia | ].
      cbn in Hi; flia Hi.
    }
    rewrite app_nth1. 2: {
      rewrite map_length, seq_length.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite seq_nth. 2: {
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite δ_diag, rngl_mul_1_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite app_nth1. 2: {
        rewrite map_length, seq_length.
        cbn in Hi; flia Hj Hi.
      }
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length.
        cbn in Hi; flia Hj Hi.
      }
      rewrite seq_nth; [ | cbn in Hi; flia Hj Hi ].
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_l; left.
    }
    rewrite rngl_add_0_l.
    rewrite app_nth1. 2: {
      rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
      rewrite map_length, seq_length, Nat.max_id.
      apply le_pow_succ_sub_1_lt; flia Hi.
    }
    rewrite nth_app_in_list; cycle 1. {
      rewrite fold_mat_nrows, mA_nrows.
      apply le_pow_succ_sub_1_lt; flia Hi.
    } {
      rewrite map_length, seq_length.
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
        rewrite map_length, seq_length.
        now apply le_pow_sub_1_lt.
      }
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length.
        now apply le_pow_sub_1_lt.
      }
      rewrite seq_nth; [ | now apply le_pow_sub_1_lt ].
      rewrite δ_ndiag; [ | flia Hj ].
      now apply rngl_mul_0_l; left.
    }
    rewrite rngl_add_0_r.
    now apply rngl_add_opp_l.
  } {
    apply Nat.nlt_ge in Hkn.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite app_nth2. 2: {
        now rewrite map_length, seq_length.
      }
      rewrite map_length, seq_length.
      rewrite (List_map_nth' 0%F). 2: {
        rewrite fold_corr_mat_ncols; cycle 1. {
          apply mA_is_correct.
        } {
          now rewrite mA_nrows; apply le_pow_succ_sub_1_lt.
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
    rewrite rngl_summation_shift; [ | cbn; flia ].
    rewrite Nat_sub_sub_swap.
    cbn; rewrite Nat.add_0_r, Nat.add_sub.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      now rewrite Nat.add_comm, Nat.add_sub.
    }
    cbn - [ "^" ].
    rewrite IHn; cycle 1. {
      apply le_pow_succ_sub_1_lt; flia Hi.
    } {
      apply le_pow_succ_sub_1_lt; flia Hk.
    }
    rewrite rngl_mul_add_distr_r, rngl_mul_1_l, rngl_add_comm.
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
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      unfold fold_app_in_list, iter_list; cbn.
      rewrite app_nth2. 2: {
        rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
        now rewrite map_length, seq_length, Nat.max_id.
      }
      rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
      rewrite map_length, seq_length, Nat.max_id.
      rewrite nth_app_in_list; cycle 1. {
        rewrite map_length, seq_length.
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
      rewrite app_nth1. 2: {
        rewrite map_length, seq_length.
        now apply le_pow_sub_1_lt.
      }
      rewrite (List_map_nth' 0); [ | now rewrite seq_length; apply le_pow_sub_1_lt ].
      rewrite seq_nth; [ cbn | now apply le_pow_sub_1_lt ].
      rewrite app_nth1. 2: {
        rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
        rewrite map_length, seq_length, Nat.max_id.
        now apply le_pow_sub_1_lt.
      }
      rewrite nth_app_in_list; cycle 1. {
        now rewrite fold_mat_nrows, mA_nrows; apply le_pow_sub_1_lt.
      } {
        now rewrite map_length, seq_length; apply le_pow_sub_1_lt.
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
    rewrite (rngl_summation_split3 (k - 2 ^ n)). 2: {
      split; [ flia | cbn in Hk; flia Hk ].
    }
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite (@δ_ndiag _ _ (j - 1)); [ | flia Hj ].
      now apply rngl_mul_0_r; left.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite (@δ_ndiag _ _ j); [ | flia Hj ].
      now apply rngl_mul_0_r; left.
    }
    rewrite rngl_add_0_r.
    rewrite δ_diag, rngl_mul_1_r.
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
  is_square_matrix n M1 = true
  → is_square_matrix n M3 = true
  → is_square_matrix n M5 = true
  → mat_nrows M2 = n
  → mat_nrows M4 = n
  → mat_ncols M2 = n
  → mat_ncols M4 = n
  → mat_ncols M6 = n
  → (mat_of_mat_list_list [[M1; M2]; [M3; M4]] *
     mat_of_mat_list_list [[M5]; [M6]])%M =
     mat_of_mat_list_list [[M1 * M5 + M2 * M6]; [M3 * M5 + M4 * M6]]%M.
Proof.
intros * Hs1 Hs3 Hs5 Hr2 Hr4 Hc2 Hc4 Hc6.
specialize (square_matrix_ncols _ Hs1) as Hc1.
apply is_sm_mat_iff in Hs1.
destruct Hs1 as (Hr1 & Hcr1 & Hc1').
move Hr1 before Hc1.
specialize (square_matrix_ncols _ Hs3) as Hc3.
apply is_sm_mat_iff in Hs3.
destruct Hs3 as (Hr3 & Hcr3 & Hc3').
move Hr3 before Hc3.
specialize (square_matrix_ncols _ Hs5) as Hc5.
apply is_sm_mat_iff in Hs5.
destruct Hs5 as (Hr5 & Hcr5 & Hc5').
move Hr5 before Hc5.
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
    rewrite List_hd_nth_0 in Hj.
    rewrite app_nth1 in Hj; [ | now rewrite fold_mat_nrows, Hr5 ].
    rewrite <- List_hd_nth_0 in Hj.
    rewrite fold_mat_ncols, Hc5 in Hj.
    unfold mat_mul_el; cbn.
    unfold mat_ncols; cbn.
    rewrite List_hd_nth_0.
    rewrite app_nth1. 2: {
      rewrite length_app_in_list.
      do 2 rewrite fold_mat_nrows.
      now rewrite Hr1, Hr2, Nat.max_id.
    }
    rewrite nth_app_in_list; cycle 1. {
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
    now rewrite Hr1, Hr2, Nat.max_id.
  }
  rewrite List_hd_nth_0.
  rewrite app_nth1; [ | now rewrite fold_mat_nrows, Hr5 ].
  rewrite fold_corr_mat_ncols; cycle 1. {
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
    rewrite nth_app_in_list; cycle 1. {
      now rewrite fold_mat_nrows, Hr1.
    } {
      now rewrite fold_mat_nrows, Hr2.
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
  rewrite (rngl_summation_split (n - 1)); [ | flia ].
  rewrite Nat.sub_add; [ | flia Hnz ].
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    rewrite app_nth1. 2: {
      rewrite fold_corr_mat_ncols; cycle 1. {
        split; [ easy | now rewrite Hc1 ].
      } {
        now apply in_seq in Hi; rewrite Hr1.
      }
      rewrite Hc1; flia Hnz Hj.
    }
    rewrite app_nth1. 2: {
      rewrite fold_mat_nrows, Hr5.
      flia Hj Hnz.
    }
    now do 2 rewrite fold_mat_el.
  }
  f_equal.
  apply in_seq in Hi.
  rewrite rngl_summation_shift; [ | flia ].
  rewrite Nat_sub_sub_swap, Nat.add_sub.
  apply rngl_summation_eq_compat.
  intros j Hj.
  rewrite app_nth2. 2: {
    rewrite fold_corr_mat_ncols; cycle 1. {
      split; [ easy | now rewrite Hc1 ].
    } {
      now rewrite Hr1.
    }
    rewrite Hc1; flia.
  }
  rewrite fold_corr_mat_ncols; cycle 1. {
    split; [ easy | now rewrite Hc1 ].
  } {
    now rewrite Hr1.
  }
  rewrite Hc1, fold_mat_el.
  rewrite Nat.add_comm, Nat.add_sub.
  f_equal.
  rewrite app_nth2. 2: {
    rewrite fold_mat_nrows, Hr5; flia.
  }
  rewrite fold_mat_nrows, Hr5, Nat.add_sub.
  apply fold_mat_el.
} {
  erewrite List_map_fun with (l' := seq 0 n) (d := 0); [ easy | | ]. {
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
  rewrite List_hd_nth_0.
  rewrite app_nth1; [ | now rewrite fold_mat_nrows, Hr5 ].
  do 3 rewrite <- List_hd_nth_0.
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
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite nth_app_in_list; cycle 1. {
      now rewrite fold_mat_nrows, Hr3.
    } {
      now rewrite fold_mat_nrows, Hr4.
    }
    easy.
  }
  cbn.
  rewrite (rngl_summation_split (n - 1)); [ | flia ].
  f_equal. {
    unfold mat_mul_el.
    rewrite Hc3.
    apply rngl_summation_eq_compat.
    intros j Hj.
    rewrite seq_nth; [ | easy ].
    rewrite app_nth1. 2: {
      rewrite fold_corr_mat_ncols; cycle 1. {
        split; [ easy | now rewrite Hc3 ].
      } {
        now rewrite Hr3.
      }
      rewrite Hc3; flia Hj Hnz.
    }
    rewrite fold_mat_el.
    f_equal.
    rewrite app_nth1. 2: {
      rewrite fold_mat_nrows, Hr5.
      flia Hj Hnz.
    }
    apply fold_mat_el.
  } {
    rewrite Nat.sub_add; [ | easy ].
    rewrite rngl_summation_shift; [ | flia ].
    rewrite Nat_sub_sub_swap, Nat.add_sub.
    unfold mat_mul_el; rewrite Hc4.
    apply rngl_summation_eq_compat.
    intros j Hj.
    rewrite app_nth2. 2: {
      rewrite fold_corr_mat_ncols; cycle 1. {
        split; [ easy | now rewrite Hc3 ].
      } {
        now rewrite Hr3.
      }
      rewrite Hc3; flia.
    }
    rewrite fold_corr_mat_ncols; cycle 1. {
      split; [ easy | now rewrite Hc3 ].
    } {
      now rewrite Hr3.
    }
    rewrite Hc3, Nat.add_comm, Nat.add_sub.
    rewrite fold_mat_el.
    rewrite app_nth2. 2: {
      rewrite fold_mat_nrows, Hr5; flia.
    }
    rewrite fold_mat_nrows, Hr5.
    now rewrite Nat.add_sub, fold_mat_el, seq_nth.
  }
}
Qed.

Definition base_vector_1 dim :=
  mk_vect (1%F :: repeat 0%F (dim - 1)).

Definition A_Sn_eigenvector_of_sqrt_Sn n μ (V : vector T) : vector T :=
  (mat_of_mat_list_list [[(mA n + μ × mI (2 ^ n))]; [mI (2 ^ n)]] • V)%M.

Theorem mA_diag_zero :
  rngl_has_opp = true →
  ∀ n i, i < 2 ^ n → mat_el (mA n) i i = 0%F.
Proof.
intros Hop * Hi2n.
revert i Hi2n.
induction n; intros. {
  destruct i; [ easy | now destruct i ].
}
unfold mat_el.
destruct (lt_dec i (2 ^ n)) as [Hin| Hin]. {
  cbn.
  unfold fold_app_in_list, iter_list; cbn.
  rewrite app_nth1. 2: {
    rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
    now rewrite map_length, seq_length, Nat.max_id.
  }
  rewrite nth_app_in_list; cycle 1. {
    now rewrite fold_mat_nrows, mA_nrows.
  } {
    now rewrite map_length, seq_length.
  }
  rewrite app_nth1. 2: {
    rewrite fold_corr_mat_ncols; cycle 1. {
      apply mA_is_correct.
    } {
      now rewrite mA_nrows.
    }
    now rewrite mA_ncols.
  }
  now apply IHn.
} {
  apply Nat.nlt_ge in Hin.
  cbn; rewrite app_nil_r.
  unfold fold_app_in_list, iter_list; cbn.
  rewrite app_nth2. 2: {
    rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
    now rewrite map_length, seq_length, Nat.max_id.
  }
  rewrite length_app_in_list, fold_mat_nrows, mA_nrows.
  rewrite map_length, seq_length, Nat.max_id.
  rewrite nth_app_in_list; cycle 1. {
    rewrite map_length, seq_length.
    apply le_pow_succ_sub_1_lt; flia Hi2n.
  } {
    rewrite map_length, fold_mat_nrows, mA_nrows.
    apply le_pow_succ_sub_1_lt; flia Hi2n.
  }
  rewrite app_nth2. 2: {
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
      apply le_pow_succ_sub_1_lt; flia Hi2n.
    }
    now rewrite map_length, seq_length.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    apply le_pow_succ_sub_1_lt; flia Hi2n.
  }
  rewrite map_length, seq_length.
  rewrite (List_map_nth' []). 2: {
    rewrite fold_mat_nrows, mA_nrows.
    apply le_pow_succ_sub_1_lt; flia Hi2n.
  }
  rewrite (List_map_nth' 0%F). 2: {
    rewrite fold_corr_mat_ncols; cycle 1. {
      apply mA_is_correct.
    } {
      rewrite mA_nrows.
      apply le_pow_succ_sub_1_lt; flia Hi2n.
    }
    rewrite mA_ncols.
    apply le_pow_succ_sub_1_lt; flia Hi2n.
  }
  rewrite fold_mat_el.
  rewrite IHn; [ | apply le_pow_succ_sub_1_lt; flia Hi2n ].
  now apply rngl_opp_0.
}
Qed.

Theorem rngl_mul_eq_if : ∀ a b c d, a = c → b = d → (a * b = c * d)%F.
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

Theorem An_eigen_equation_for_sqrt_n :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_dec_eq = true →
  ∀ n μ, (μ * μ)%F = rngl_of_nat n →
  match n with
  | 0 => ∀ V, vect_size V = 1 → (mA 0 • V = μ × V)%V
  | S n' =>
      ∀ U V,
      vect_size U = 2 ^ n'
      → V = A_Sn_eigenvector_of_sqrt_Sn n' μ U
      → (mA (S n') • V = μ × V)%V
  end.
Proof.
intros Hic Hro Hin Hde * Hμ.
destruct n. {
  intros V Hv.
  cbn in Hμ, V |-*.
  assert (H : μ = 0%F). {
    destruct (rngl_eq_dec Hde μ 0%F) as [Hμz| Hμz]; [ easy | ].
    apply (f_equal (rngl_mul (μ⁻¹)%F)) in Hμ.
    rewrite rngl_mul_0_r in Hμ; [ | now left ].
    rewrite rngl_mul_assoc in Hμ.
    rewrite rngl_mul_inv_l in Hμ; [ | easy | easy ].
    now rewrite rngl_mul_1_l in Hμ.
  }
  subst μ.
  apply vector_eq.
  intros i; cbn.
  rewrite nth_error_map.
  unfold option_map.
  unfold vect_dot_mul; cbn.
  destruct V as (la); cbn.
  destruct la as [| a]; [ easy | ].
  destruct la; [ | easy ].
  unfold iter_list; cbn.
  rewrite rngl_add_0_l, rngl_mul_0_l; [ | now left ].
  destruct i; cbn. {
    rewrite rngl_mul_0_l; [ easy | now left ].
  }
  now destruct i.
}
intros * HU HV.
subst V.
unfold A_Sn_eigenvector_of_sqrt_Sn.
rewrite mat_vect_mul_assoc; cycle 1. {
  easy.
} {
  apply mA_is_correct.
} {
  split. {
    cbn; intros Hc.
    unfold mat_ncols in Hc.
    unfold mat_of_mat_list_list in Hc; cbn in Hc.
    rewrite List_hd_nth_0 in Hc.
    rewrite app_nth1 in Hc. 2: {
      rewrite map2_map_r.
      unfold fold_app_in_list, iter_list; cbn.
      rewrite map2_length, fold_mat_nrows, mA_nrows.
      rewrite map_length, seq_length, Nat.min_id.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    unfold fold_app_in_list, iter_list in Hc; cbn in Hc.
    rewrite map2_nth with (a := []) (b := []) in Hc; cycle 1. {
      rewrite fold_mat_nrows, mA_nrows.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    } {
      do 2 rewrite map_length.
      rewrite seq_length.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite map2_length in Hc.
    rewrite <- List_hd_nth_0 in Hc.
    rewrite fold_mat_ncols, mA_ncols in Hc.
    rewrite (List_map_nth' []) in Hc. 2: {
      rewrite map_length, seq_length.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite map_length in Hc.
    rewrite (List_map_nth' 0) in Hc. 2: {
      rewrite seq_length.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite map_length, seq_length, Nat.min_id in Hc.
    now apply Nat.pow_nonzero in Hc.
  } {
    intros la Hla.
    unfold mat_ncols; cbn.
    rewrite List_hd_nth_0.
    rewrite app_nth1. 2: {
      rewrite map2_map_r.
      unfold fold_app_in_list, iter_list; cbn.
      rewrite map2_length, fold_mat_nrows, mA_nrows.
      rewrite map_length, seq_length, Nat.min_id.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    unfold fold_app_in_list, iter_list; cbn.
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
      rewrite map_length, seq_length.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite map_length.
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite map_length, seq_length, Nat.min_id.
    cbn in Hla.
    unfold fold_app_in_list, iter_list in Hla; cbn in Hla.
    rewrite app_nil_r in Hla.
    apply in_app_or in Hla.
    destruct Hla as [Hla| Hla]. {
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
      rewrite (List_map_nth' []); [ | now rewrite map_length, seq_length ].
      rewrite map_length.
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      now rewrite map_length, seq_length, Nat.min_id.
    } {
      apply in_map_iff in Hla.
      destruct Hla as (i & Hla & Hi); subst la.
      now rewrite map_length, seq_length.
    }
  }
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
  unfold mat_ncols; cbn.
  rewrite app_nil_r.
  rewrite List_hd_nth_0.
  unfold fold_app_in_list, iter_list; cbn.
  rewrite app_nth1. 2: {
    rewrite map2_length, fold_mat_nrows, mA_nrows.
    do 2 rewrite map_length.
    rewrite seq_length, Nat.min_id.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
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
    rewrite map_length, seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map_length.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  now rewrite map_length, seq_length, Nat.min_id.
}
...
    rewrite map2_length, fold_mat_nrows, mA_nrows.
      rewrite map_length, seq_length, Nat.min_id.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
...
Search (_ ∈ mat_list_list _).
Search (mat_list_list (mat_of_mat_list_list _)).
...
    rewrite <- List_hd_nth_0 in Hc.
    rewrite fold_mat_ncols, mA_ncols in Hc.
...
      rewrite map2_length, fold_mat_nrows, mA_nrows.
      rewrite map_length, seq_length, Nat.min_id.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite map2_map_r in Hc.
    rewrite map2_map_r in Hc.
    rewrite map2_nth with(a := []) (b := 0) in Hc; cycle 1. {
      rewrite fold_mat_nrows, mA_nrows.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    } {
      rewrite seq_length.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite map2_map_r in Hc.
    rewrite map2_map_r in Hc.
    rewrite map2_length, seq_length in Hc.
    rewrite <- List_hd_nth_0 in Hc.
    rewrite fold_mat_ncols, mA_ncols, Nat.min_id in Hc.
    now apply Nat.pow_nonzero in Hc.
  } {
    intros l Hl.
    unfold mat_of_list_list in Hl; cbn in Hl.
    rewrite app_nil_r in Hl.
    rewrite map2_map_r in Hl.
    rewrite map2_map_r in Hl.
    apply in_app_or in Hl.
    destruct Hl as [Hl| Hl]. {
      apply in_map2_iff in Hl.
      rewrite fold_mat_nrows, mA_nrows in Hl.
      rewrite seq_length, Nat.min_id in Hl.
      destruct Hl as (i & Hi & la & j & Hl); subst l.
      rewrite map2_length.
      rewrite map_length, map_length, seq_length.
      unfold mat_of_mat_list_list, mat_ncols; cbn.
      rewrite List_hd_nth_0.
      rewrite app_nth1. 2: {
        rewrite map2_map_r, map2_map_r.
        rewrite map2_length, seq_length.
        rewrite fold_mat_nrows, mA_nrows, Nat.min_id.
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
      }
      rewrite map2_map_r, map2_map_r.
      rewrite map2_nth with (a := []) (b := 0); cycle 1. {
        rewrite fold_mat_nrows, mA_nrows.
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
      } {
        rewrite seq_length.
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
      }
      rewrite map2_map_r.
      rewrite map2_map_r.
      rewrite map2_length, seq_length.
      rewrite <- List_hd_nth_0.
      rewrite fold_mat_ncols, mA_ncols, Nat.min_id.
      specialize (mA_is_correct n) as H1.
      destruct H1 as (Hcr & Hc).
      rewrite Hc. 2: {
        apply nth_In.
        now rewrite fold_mat_nrows, mA_nrows.
      }
      rewrite mA_ncols.
      apply Nat.min_id.
    } {
      apply in_map_iff in Hl.
      destruct Hl as (i & Hl & Hi); subst l.
      rewrite map_length, seq_length.
      unfold mat_of_mat_list_list, mat_ncols; cbn.
      rewrite List_hd_nth_0.
      rewrite app_nth1. 2: {
        rewrite map2_map_r, map2_map_r.
        rewrite map2_length, seq_length.
        rewrite fold_mat_nrows, mA_nrows, Nat.min_id.
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
      }
      rewrite map2_map_r, map2_map_r.
      rewrite map2_nth with (a := []) (b := 0); cycle 1. {
        rewrite fold_mat_nrows, mA_nrows.
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
      } {
        rewrite seq_length.
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
      }
      rewrite map2_map_r.
      rewrite map2_map_r.
      rewrite map2_length, seq_length.
      rewrite <- List_hd_nth_0.
      now rewrite fold_mat_ncols, mA_ncols, Nat.min_id.
    }
  }
} {
  rewrite mA_ncols.
  cbn - [ "^" ].
  rewrite app_nil_r, app_length.
  rewrite map2_length.
  rewrite fold_mat_nrows, mA_nrows.
  rewrite map_length, map_length, seq_length, Nat.min_id.
  now cbn; rewrite Nat.add_0_r.
} {
  unfold mat_ncols; cbn.
  rewrite app_nil_r.
  rewrite List_hd_nth_0.
  rewrite app_nth1. 2: {
    rewrite map2_length.
    rewrite fold_mat_nrows, mA_nrows.
    rewrite map_length, map_length, seq_length, Nat.min_id.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map2_nth with (a := []) (b := []); cycle 1. {
    rewrite fold_mat_nrows, mA_nrows.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  } {
    rewrite map_length, map_length, seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map2_length.
  rewrite <- List_hd_nth_0.
  rewrite fold_mat_ncols, mA_ncols.
  rewrite (List_map_nth' []). 2: {
    rewrite map_length, seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map_length.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  now rewrite map_length, seq_length, Nat.min_id.
}
rewrite mat_mul_scal_vect_assoc; cycle 1. {
  easy.
} {
  unfold is_correct_matrix.
  unfold mat_ncols, mat_of_mat_list_list; cbn.
  rewrite List_hd_nth_0.
  rewrite app_nth1. 2: {
    rewrite map2_length, fold_mat_nrows, mA_nrows.
    rewrite map_length, map_length, seq_length, Nat.min_id.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map2_nth with (a := []) (b := []); cycle 1. {
    rewrite fold_mat_nrows, mA_nrows.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  } {
    rewrite map_length, map_length, seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map2_length.
  rewrite <- List_hd_nth_0.
  rewrite fold_mat_ncols, mA_ncols.
  rewrite (List_map_nth' []). 2: {
    rewrite map_length, seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map_length.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map_length, seq_length, Nat.min_id.
  split; [ now intros Hc; apply Nat.pow_nonzero in Hc | ].
  intros l Hl.
  apply in_app_or in Hl.
  destruct Hl as [Hl| Hl]. {
    apply in_map2_iff in Hl.
    destruct Hl as (i & Hi & la & lb & Hl).
    rewrite fold_mat_nrows, mA_nrows in Hi.
    rewrite map_length, map_length, seq_length, Nat.min_id in Hi.
    subst l.
    rewrite map2_length.
    rewrite fold_corr_mat_ncols; cycle 1. {
      apply mA_is_correct.
    } {
      now rewrite mA_nrows.
    }
    rewrite mA_ncols.
    rewrite (List_map_nth' []); [ | now rewrite map_length, seq_length ].
    rewrite map_length.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    now rewrite map_length, seq_length, Nat.min_id.
  } {
    rewrite app_nil_r in Hl.
    apply in_map_iff in Hl.
    destruct Hl as (i & Hl & Hi); subst l.
    now rewrite map_length, seq_length.
  }
} {
  unfold mat_ncols; cbn.
  rewrite app_nil_r, List_hd_nth_0.
  rewrite app_nth1. 2: {
    rewrite map2_length, fold_mat_nrows, mA_nrows.
    rewrite map_length, map_length, seq_length, Nat.min_id.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map2_nth with (a := []) (b := []); cycle 1. {
    rewrite fold_mat_nrows, mA_nrows.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  } {
    rewrite map_length, map_length, seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map2_length, fold_corr_mat_ncols; cycle 1. {
    apply mA_is_correct.
  } {
    rewrite mA_nrows.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite mA_ncols.
  rewrite (List_map_nth' []). 2: {
    rewrite map_length, seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map_length.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  now rewrite map_length, seq_length, Nat.min_id.
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
  apply mI_nrows.
} {
  cbn; rewrite map_length.
  apply mA_nrows.
} {
  apply mI_ncols.
} {
  unfold mat_ncols; cbn.
  rewrite List_hd_nth_0.
  rewrite (List_map_nth' []). 2: {
    rewrite fold_mat_nrows, mA_nrows.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite map_length.
  rewrite <- List_hd_nth_0, fold_mat_ncols.
  apply mA_ncols.
} {
  apply mI_ncols.
}
...
rewrite mat_of_mat_list_list_mul_scal_l.
...
unfold "×"%M.
Search "×"%M.
unfold
unfold mat_of_mat_list_list.
cbn.
unfold
Search (_ × mk_mat _)%M.
Search (_ × mat_of_mat_list_list _)%M.
...
unfold "×"%M.
unfold mat_of_mat_list_list.
cbn; f_equal.
do 2 rewrite app_nil_r.
do 2 rewrite map_length.
rewrite seq_length.
rewrite map_app.
Inspect 8.
...
f_equal. {
  rewrite map2_map_l, map2_map_r.
  rewrite mA_nrows.
  rewrite map2_diag.
  rewrite map2_map_r.
  rewrite map2_map_r.
  rewrite map_map2.
  rewrite map_map.
  rewrite mat_add_ncols.
  rewrite mA_ncols.
  unfold mat_ncols; cbn.
  rewrite <- map_map2.
...
rewrite mat_vect_mul_assoc; [ | easy ].
rewrite mat_mul_scal_vect_assoc; [ | easy ].
cbn - [ Nat.pow ].
remember (mA n) as M1 eqn:HM1.
remember (mI (2 ^ n)) as M2 eqn:HM2.
remember (M1 + μ × M2)%M as M5 eqn:HM5.
move M2 before M1; move M5 before M2.
f_equal.
apply matrix_eq.
intros * Hi Hj.
cbn - [ Nat.pow ].
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  apply rngl_mul_eq_if; [ | reflexivity ].
  now rewrite mat_el_eq_rect.
}
cbn - [ Nat.pow mat_of_mat_list_list ].
remember (mat_of_mat_list_list [[M1; M2]; [M2; (- M1)%M]]) as MA eqn:HMA.
remember (mat_of_list_list_1_row_2_col _ _) as MB eqn:HMB.
move MB before MA.
cbn - [ Nat.pow ] in MA.
assert
  (H1 : ∀ i j,
   mat_el
     (mat_of_mat_list_list [[M1; M2]; [M2; - M1]] *
      mat_of_mat_list_list [[M5]; [M2]])%M i j =
   mat_el
     (mat_of_mat_list_list
        [[(M1 * M5 + M2 * M2)%M]; [(M2 * M5 + - M1 * M2)%M]]) i j). {
  now rewrite (m_o_mll_2x2_2x1 M1 M2 M2 (- M1)%M M5 M2).
}
rewrite <- HMA in H1.
cbn - [ Nat.pow ] in H1.
replace (2 ^ n * 2) with (2 ^ S n) in H1 by now rewrite Nat.mul_comm.
specialize (H1 i j).
rewrite HMB.
unfold mat_of_list_list_1_row_2_col.
destruct (Nat.mul_1_r (2 ^ n)).
destruct (two_pow_n_mul_two n).
cbn - [ Nat.pow ].
rewrite H1; clear H1.
unfold mat_list_list_el.
rewrite (Nat.div_small j); [ | easy ].
rewrite (Nat.mod_small j); [ | easy ].
destruct (lt_dec i (2 ^ n)) as [Hi2n| Hi2n]. {
  rewrite (Nat.div_small i); [ | easy ].
  rewrite (Nat.mod_small i); [ | easy ].
  cbn - [ Nat.pow ].
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite HM5 at 1; cbn.
    rewrite rngl_mul_add_distr_l.
    now rewrite HM1 at 1 2 3.
  }
  cbn - [ Nat.pow ].
  rewrite rngl_summation_add_distr; [ | easy ].
  assert
    (H1 : ∀ i j,
     mat_el (mA n * mA n) i j = mat_el (rngl_of_nat n × mI (2 ^ n)) i j). {
    intros i' j'.
    now rewrite lemma_2_A_n_2_eq_n_I.
  }
  specialize (H1 i j).
  cbn in H1.
  rewrite H1; clear H1.
...
  rewrite (rngl_summation_split _ j); [ | flia Hj ].
  rewrite rngl_summation_split_last; [ | flia ].
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec (k - 1) j) as [Hkj| Hkj]; [ flia Hkj Hk | ].
    rewrite rngl_mul_assoc, rngl_mul_0_r; [ easy | now left ].
  }
  rewrite rngl_add_0_l.
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ flia Hkj Hk | ].
    rewrite rngl_mul_assoc, rngl_mul_0_r; [ easy | now left ].
  }
  rewrite rngl_add_0_r.
  rewrite HM2 at 1; cbn.
  destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
  rewrite rngl_mul_1_r.
  destruct (Nat.eq_dec i j) as [Hij| Hij]. {
    rewrite rngl_mul_1_r; subst j.
    rewrite mA_diag_zero; [ | easy | easy ].
    rewrite rngl_mul_0_l, rngl_add_0_r; [ | now left ].
...
    rewrite (rngl_summation_split _ i); [ | flia Hi2n ].
    rewrite rngl_summation_split_last; [ | flia ].
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros k Hk.
      rewrite HM2; cbn.
      destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia H Hk | ].
      now apply rngl_mul_0_l; left.
    }
    rewrite rngl_add_0_l.
    rewrite HM2 at 1 2; cbn.
    destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
    rewrite rngl_mul_1_l.
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros k Hk.
      rewrite HM2; cbn.
      destruct (Nat.eq_dec i k) as [H| H]; [ flia H Hk | ].
      now apply rngl_mul_0_l; left.
    }
    rewrite rngl_add_0_r.
    rewrite HM5; cbn.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
    rewrite rngl_mul_1_r.
    rewrite HM1.
    rewrite mA_diag_zero; [ | easy | easy ].
    rewrite rngl_add_0_l.
    now rewrite rngl_add_comm.
  } {
    rewrite rngl_mul_0_r, rngl_add_0_l; [ | now left ].
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros k Hk.
      rewrite HM2; cbn.
      destruct (Nat.eq_dec i k) as [H| H]. 2: {
        rewrite rngl_mul_0_l; [ easy | now left ].
      }
      subst k.
      destruct (Nat.eq_dec i j) as [H| H]; [ easy | ].
      now apply rngl_mul_0_r; left.
    }
    rewrite rngl_add_0_r.
    rewrite HM5; cbn.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec i j) as [H| H]; [ easy | ].
    rewrite rngl_mul_0_r, rngl_add_0_r; [ | now left ].
    now rewrite HM1, rngl_mul_comm.
  }
} {
  apply Nat.nlt_ge in Hi2n.
  rewrite (Nat_div_less_small 1). 2: {
    now rewrite Nat.mul_1_l, Nat.mul_comm.
  }
  rewrite (Nat_mod_less_small 1). 2: {
    now rewrite Nat.mul_1_l, Nat.mul_comm.
  }
  cbn.
  rewrite Nat.add_0_r.
  remember (i - 2 ^ n) as k eqn:Hk.
  assert (H : k < 2 ^ n) by flia Hi2n Hk Hi.
  clear i Hi Hi2n Hk.
  rename k into i.
  rename H into Hi.
  move i after j.
  move Hi after Hj.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite HM5 at 1; cbn.
    rewrite rngl_mul_add_distr_l.
    now rewrite HM1 at 1 2 3.
  }
  cbn - [ Nat.pow ].
  rewrite rngl_summation_add_distr; [ | easy ].
...
  rewrite (rngl_summation_split _ i); [ | flia Hi ].
  rewrite rngl_summation_split_last; [ | flia ].
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia H Hk | ].
    now apply rngl_mul_0_l; left.
  }
  rewrite rngl_add_0_l.
  rewrite HM2 at 1; cbn.
  destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
  rewrite rngl_mul_1_l.
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec i k) as [H| H]; [ flia H Hk | ].
    now apply rngl_mul_0_l; left.
  }
  rewrite rngl_add_0_r.
...
  rewrite (rngl_summation_split _ i); [ | flia Hi ].
  rewrite rngl_summation_split_last; [ | flia ].
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia H Hk | ].
    now apply rngl_mul_0_l; left.
  }
  rewrite rngl_add_0_l.
  rewrite HM2 at 1; cbn.
  destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
  rewrite rngl_mul_1_l.
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec i k) as [H| H]; [ flia H Hk | ].
    now apply rngl_mul_0_l; left.
  }
  rewrite rngl_add_0_r.
...
  rewrite (rngl_summation_split _ j); [ | flia Hj ].
  rewrite rngl_summation_split_last; [ | flia ].
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec (k - 1) j) as [H| H]; [ flia Hk H | ].
    rewrite rngl_mul_0_r; [ easy | now left ].
  }
  rewrite rngl_add_0_l.
  rewrite HM2 at 2; cbn.
  destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
  rewrite rngl_mul_1_r.
  rewrite rngl_add_assoc.
  rewrite (rngl_add_add_swap (mat_el (mA n) i j)).
  rewrite HM1 at 1.
  rewrite fold_rngl_sub; [ | easy ].
  rewrite rngl_sub_diag, rngl_add_0_l; [ | now left ].
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec k j) as [H| H]; [ flia H Hk | ].
    now apply rngl_mul_0_r; left.
  }
  now rewrite rngl_add_0_r.
}
Qed.

...

Theorem A_n_eigenvalue_squared_is_n :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_dec_eq = true →
  rngl_has_inv = true →
  ∀ n μ (V : vector (2 ^ n) T),
  V ≠ vect_zero (2 ^ n)
  → (mA n • V = μ × V)%V
  → (μ * μ)%F = rngl_of_nat n.
Proof.
intros Hic Hro Hed Hin * Hvr Hav.
specialize (lemma_2_A_n_2_eq_n_I Hro n) as Ha.
(* μ * μ = rngl_of_nat n *)
apply vect_mul_scal_reg_r with (V0 := V); [ now left | easy | easy | ].
(* (μ * μ) × V = rngl_of_nat n × V *)
rewrite <- vect_mul_scal_l_mul_assoc; [ | easy ].
(* μ × (μ × V) = rngl_of_nat n × V *)
rewrite <- Hav.
(* μ × (mA n . V) = rngl_of_nat n × V *)
rewrite mat_mul_scal_vect_comm; [ | easy | easy ].
(* mA n . (μ × V) = rngl_of_nat n × V *)
rewrite <- Hav.
(* mA n . (mA n . V) = rngl_of_nat n × V *)
rewrite mat_vect_mul_assoc; [ | easy ].
(* (mA n * mA n) . V = rngl_of_nat n × V *)
rewrite Ha.
(* (rngl_of_nat n × mI (2 ^ n)) . V = rngl_of_nat n × V *)
rewrite <- mat_mul_scal_vect_assoc; [ | easy ].
(* rngl_of_nat n × (mI (2 ^ n) . V) = rngl_of_nat n × V *)
rewrite mat_vect_mul_1_l; easy.
Qed.

Definition is_eigenvector_of_An n μ (V : vector (2 ^ n) T) :=
  V ≠ vect_zero (2 ^ n) ∧ (mA n • V = μ × V)%V.

Theorem μ_is_ev_of_An_iff_μ2_eq_n :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_dec_eq = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_characteristic = 0 →
  ∀ n μ,
  (∃ V, is_eigenvector_of_An n μ V) ↔ (μ * μ = rngl_of_nat n)%F.
Proof.
intros Hic Hro Heq Hin H10 Hch *.
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
    split. {
      intros H.
      injection H; clear H; intros H.
      set (f := λ i, match i with 0 => 1%F | S _ => 0%F end) in H.
      set (g := λ _, 0%F) in H.
      assert (H1 : ∀ i, f i = g i) by now rewrite H.
      specialize (H1 0).
      unfold f, g in H1; cbn in H1.
      now apply rngl_1_neq_0 in H1.
    }
    specialize An_eigen_equation_for_sqrt_n as H1.
    specialize (H1 Hic Hro Hin Heq).
    now apply (H1 0).
  }
  remember (A_Sn_eigenvector_of_sqrt_Sn n μ (base_vector_1 (2 ^ n))) as V
    eqn:Hv.
  exists V.
  split. 2: {
    specialize An_eigen_equation_for_sqrt_n as H1.
    specialize (H1 Hic Hro Hin Heq).
    specialize (H1 (S n) μ Hμ).
    cbn - [ mA ] in H1.
    specialize (H1 (base_vector_1 (2 ^ n))).
    now specialize (H1 V Hv).
  }
  (* V ≠ vect_zero (2 ^ n) *)
  subst V.
  unfold A_Sn_eigenvector_of_sqrt_Sn.
  unfold mat_of_list_list_1_row_2_col.
  cbn - [ Nat.pow ].
  destruct (two_pow_n_mul_two n).
  destruct (Nat.mul_1_r (2 ^ n)).
  cbn - [ Nat.pow ].
  intros H.
  remember base_vector_1 as ffff.
  injection H; clear H; intros H1.
  subst ffff.
  rewrite Nat.mul_1_r in H1.
  set
    (f :=
       λ i,
       (Σ (j = 0, 2 ^ n - 1),
        mat_list_list_el [[(mA n + μ × mI (2 ^ n))%M]; [mI (2 ^ n)]] i j *
        vect_el (base_vector_1 (2 ^ n)) j)%F) in H1.
  set (g := λ _, 0%F) in H1.
  assert (H3 : ∀ i, f i = g i) by now rewrite H1.
  specialize (H3 0) as H4.
  unfold f, g in H4.
  rewrite rngl_summation_split_first in H4; [ | easy | flia ].
  unfold base_vector_1 in H4 at 1.
  cbn - [ base_vector_1 ] in H4.
  rewrite rngl_mul_1_r in H4.
  unfold mat_list_list_el in H4 at 1.
  cbn - [ base_vector_1 ] in H4.
  rewrite Nat.div_small in H4; [ | now apply Nat.neq_0_lt_0, Nat.pow_nonzero ].
  rewrite Nat.mod_small in H4; [ | now apply Nat.neq_0_lt_0, Nat.pow_nonzero ].
  cbn - [ base_vector_1 ] in H4.
  rewrite rngl_mul_1_r in H4.
  rewrite mA_diag_zero in H4; [ | easy | ]. 2: {
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite rngl_add_0_l in H4.
  rewrite all_0_rngl_summation_0 in H4; [ | easy | ]. 2: {
    intros i Hi; cbn.
    destruct i; [ easy | ].
    unfold mat_list_list_el; cbn.
    now apply rngl_mul_0_r; left.
  }
  rewrite rngl_add_0_r in H4.
  rewrite H4 in Hμ.
  rewrite rngl_mul_0_l in Hμ; [ | now left ].
  symmetry in Hμ.
  move Hμ at bottom.
  specialize rngl_characteristic_prop as H.
  rewrite Hch in H.
  now apply H in Hμ.
}
Qed.

End a.
