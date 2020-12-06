(* Lemma 2.2 of the proof of the sensitivity conjecture *)
(* sequence A_n of matrices and the proof their square is "n * I_n" *)
(* new version using a new version of block matrices with one only
   level: block matrices just being matrices of matrices, not matrices
   of block matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc Matrix.
Require Import Semiring Field2.
Require Import SRsummation SRproduct SRpolynomial.
Require Import CharacPolyn.
Import matrix_Notations.

Section in_ring.

Context {T : Type}.
Context (so : semiring_op T).
Context {ro : ring_op T}.
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.
Context {scp : sring_comm_prop T}.
Context {sdp : sring_dec_prop T}.
Context {fo : field_op T}.

(* *)

Definition mat_of_scalar (c : T) := mk_mat (λ i j, c) 1 1.

(* conversion matrix of matrices (actually list of list of matrices)
   into simple matrix *)

Definition upper_left_mat_in_list_list d mll :=
  hd (mat_of_scalar d) (hd [] mll).

Definition mat_list_list_el d mll i j :=
  let M := upper_left_mat_in_list_list d mll in
  let r := mat_nrows M in
  let c := mat_ncols M in
  mat_el (nth (j / c) (nth (i / r) mll []) (mat_of_scalar d))
    (i mod r) (j mod c).

Definition mat_of_mat_list_list d (mll : list (list (matrix T))) : matrix T :=
  let M := upper_left_mat_in_list_list d mll in
  let r := mat_nrows M in
  let c := mat_ncols M in
  mk_mat (mat_list_list_el d mll)
    (r * length mll)
    (c * length (hd [] mll)).

(* sequence "An" *)

Fixpoint mA n : matrix T :=
  match n with
  | 0 => mat_of_scalar 0%Rng
  | S n' =>
      mat_of_mat_list_list 0%Rng
        [[mA n'; squ_mat_one (2 ^ n')];
         [squ_mat_one (2 ^ n'); (- mA n')%M]]
  end.

Definition rng_mul_nat_l n v :=
  match n with
  | 0 => 0%Srng
  | S n' => (Σ (_ = 0, n'), v)%Srng
  end.

Definition mat_nat_mul_l n M :=
  mk_mat (λ i j, rng_mul_nat_l n (mat_el M i j)) (mat_nrows M) (mat_ncols M).

(* *)

Theorem mA_nrows : ∀ n, mat_nrows (mA n) = 2 ^ n.
Proof.
intros.
induction n; [ easy | cbn ].
now rewrite IHn, Nat.mul_comm; cbn.
Qed.

Theorem mA_ncols : ∀ n, mat_ncols (mA n) = 2 ^ n.
Proof.
intros.
induction n; [ easy | cbn ].
now rewrite IHn, Nat.mul_comm; cbn.
Qed.

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I : ∀ n,
  (mA n * mA n = mat_nat_mul_l n (squ_mat_one (2 ^ n)))%M.
Proof.
intros.
apply matrix_eq; [ apply mA_nrows | apply mA_ncols | ].
cbn - [ iter_seq ].
rewrite mA_nrows, mA_ncols.
intros i k Hi Hk.
revert i k Hi Hk.
induction n; intros. {
  now cbn; rewrite srng_mul_0_l, srng_add_0_l.
}
rewrite (srng_summation_split _ (2 ^ n - 1)). 2: {
  split; [ flia | ].
  apply -> Nat.succ_le_mono.
  apply Nat.sub_le_mono_r.
  apply Nat.pow_le_mono_r; [ easy | flia ].
}
rewrite Nat.sub_add. 2: {
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
cbn - [ iter_seq Nat.pow ].
unfold mat_list_list_el.
unfold upper_left_mat_in_list_list.
cbn - [ iter_seq Nat.pow ].
rewrite mA_nrows, mA_ncols.
erewrite srng_summation_eq_compat. 2: {
  intros j Hj.
  rewrite (Nat.div_small j); [ | cbn in Hi; flia Hj Hi ].
  rewrite (Nat.mod_small j); [ | cbn in Hi; flia Hj Hi ].
  easy.
}
cbn - [ iter_seq Nat.pow ].
rewrite srng_add_comm.
erewrite srng_summation_eq_compat. 2: {
  intros j Hj.
  assert (H : 1 * 2 ^ n ≤ j < (1 + 1) * 2 ^ n). {
    rewrite Nat.mul_1_l.
    split; [ easy | ].
    change (j < 2 ^ S n).
    enough (H : 0 < 2 ^ S n) by flia H Hj.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite (Nat_div_less_small 1); [ | easy ].
  rewrite (@Nat_mod_less_small 1 j); [ clear H | easy ].
  now rewrite Nat.mul_1_l.
}
rewrite srng_add_comm.
destruct (lt_dec i (2 ^ n)) as [Hi2n| Hi2n]. {
  rewrite (Nat.div_small i); [ | easy ].
  rewrite (Nat.mod_small i); [ | easy ].
  cbn - [ iter_seq Nat.pow ].
  destruct (lt_dec k (2 ^ n)) as [Hk2n| Hk2n]. {
    rewrite (Nat.div_small k); [ | easy ].
    rewrite (Nat.mod_small k); [ | easy ].
    cbn - [ iter_seq Nat.pow ].
    rewrite IHn; [ | easy | easy ].
    rewrite (srng_summation_split _ (i + 2 ^ n)); [ | cbn; flia Hi Hi2n ].
    rewrite srng_summation_split_last; [ | flia ].
    rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i (j - 1 - 2 ^ n)) as [Hij| Hij]. {
        flia Hj Hij.
      }
      apply srng_mul_0_l.
    }
    rewrite srng_add_0_l.
    rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i (j - 2 ^ n)) as [Hij| Hij]; [ flia Hj Hij | ].
      apply srng_mul_0_l.
    }
    rewrite srng_add_0_r.
    rewrite Nat.add_sub.
    destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
    rewrite srng_mul_1_l.
    symmetry.
    destruct (Nat.eq_dec i k) as [Hik| Hik]. {
      subst k.
      destruct n; [ easy | ].
      cbn - [ iter_seq ].
      rewrite srng_summation_split_last; [ | flia ].
      now rewrite srng_summation_succ_succ.
    } {
      rewrite srng_add_0_r.
      destruct n; [ apply srng_add_0_l | ].
      rewrite srng_summation_split_last; [ | flia ].
      now rewrite srng_summation_succ_succ, srng_add_0_r.
    }
  } {
    apply Nat.nlt_ge in Hk2n.
    assert (H : 1 * 2 ^ n ≤ k < (1 + 1) * 2 ^ n). {
      rewrite Nat.mul_1_l.
      split; [ easy | ].
      change (k < 2 ^ S n).
      enough (H : 0 < 2 ^ S n) by flia H Hk.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite (Nat_div_less_small 1); [ | easy ].
    rewrite (Nat_mod_less_small 1); [ clear H | easy ].
    rewrite Nat.mul_1_l.
    cbn - [ iter_seq Nat.pow ].
    rewrite (srng_summation_split _ (k - 2 ^ n)). 2: {
      split; [ flia | ].
      apply -> Nat.succ_le_mono.
      cbn in Hk; flia Hk.
    }
    rewrite srng_summation_split_last; [ | flia ].
    rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec (j - 1) (k - 2 ^ n)) as [Hjk| Hjk]. {
        flia Hj Hjk.
      }
      apply srng_mul_0_r.
    }
    rewrite srng_add_0_l.
    rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec j (k - 2 ^ n)) as [Hjk| Hjk]; [ flia Hj Hjk | ].
      apply srng_mul_0_r.
    }
    rewrite srng_add_0_r.
    remember (k - 2 ^ n) as j eqn:Hj.
    destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
    subst j; rewrite srng_mul_1_r.
    erewrite srng_summation_eq_compat. 2: {
      intros j Hj.
      now rewrite rng_mul_opp_opp.
    }
    cbn - [ iter_seq Nat.pow ].
    rewrite srng_summation_shift; [ | cbn; flia Hi ].
    rewrite Nat_sub_sub_swap.
    replace (2 ^ S n - 2 ^ n) with (2 ^ n). 2: {
      cbn; rewrite Nat.add_0_r; symmetry.
      apply Nat.add_sub.
    }
    erewrite srng_summation_eq_compat. 2: {
      intros j Hj.
      rewrite Nat.add_comm, Nat.add_sub.
      rewrite rng_mul_opp_opp.
      now rewrite rng_mul_opp_r.
    }
    cbn - [ iter_seq Nat.pow ].
    rewrite (srng_summation_split _ i); [ | flia Hi Hi2n ].
    rewrite srng_summation_split_last; [ | flia ].
    destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
    rewrite srng_mul_1_l.
    rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i (j - 1)) as [Hij| Hij]; [ flia Hij Hj | ].
      rewrite srng_mul_0_l.
      apply rng_opp_0.
    }
    rewrite srng_add_0_l.
    rewrite srng_add_assoc.
    rewrite fold_rng_sub.
    rewrite rng_add_opp_r, srng_add_0_l.
    destruct (Nat.eq_dec i k) as [Hik| Hik]; [ flia Hi2n Hk2n Hik | ].
    rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i j) as [Hij| Hij]; [ flia Hj Hij | ].
      rewrite srng_mul_0_l.
      apply rng_opp_0.
    }
    symmetry.
    now apply all_0_srng_summation_0.
  }
} {
  apply Nat.nlt_ge in Hi2n.
  assert (H : 1 * 2 ^ n ≤ i < (1 + 1) * 2 ^ n). {
    rewrite Nat.mul_1_l.
    split; [ easy | ].
    change (i < 2 ^ S n).
    enough (H : 0 < 2 ^ S n) by flia H Hi.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite (Nat_div_less_small 1); [ | easy ].
  rewrite (Nat_mod_less_small 1); [ clear H | easy ].
  rewrite Nat.mul_1_l.
  cbn - [ iter_seq Nat.pow ].
  rewrite (srng_summation_split _ (i - 2 ^ n)). 2: {
    split; [ flia | ].
    apply -> Nat.succ_le_mono.
    cbn in Hi; flia Hi.
  }
  rewrite srng_summation_split_last; [ | flia ].
  rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
    intros j Hj.
    destruct (Nat.eq_dec (i - 2 ^ n) (j - 1)) as [Hij| Hij]. {
      flia Hj Hij.
    }
    apply srng_mul_0_l.
  }
  rewrite srng_add_0_l.
  rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
    intros j Hj.
    destruct (Nat.eq_dec (i - 2 ^ n) j) as [Hij| Hij]; [ flia Hj Hij | ].
    apply srng_mul_0_l.
  }
  rewrite srng_add_0_r.
  remember (i - 2 ^ n) as j eqn:Hj.
  destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
  subst j; rewrite srng_mul_1_l.
  rewrite srng_summation_shift; [ | cbn; flia Hi ].
  rewrite Nat_sub_sub_swap.
  replace (2 ^ S n - 2 ^ n) with (2 ^ n). 2: {
    cbn; rewrite Nat.add_0_r; symmetry.
    apply Nat.add_sub.
  }
  erewrite srng_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  cbn - [ iter_seq Nat.pow ].
  destruct (lt_dec k (2 ^ n)) as [Hk2n| Hk2n]. {
    rewrite (Nat.div_small k); [ | easy ].
    rewrite (Nat.mod_small k); [ | easy ].
    cbn - [ iter_seq Nat.pow ].
    rewrite (srng_summation_split _ k). 2: {
      cbn in Hk; flia Hk Hk2n.
    }
    rewrite srng_summation_split_last; [ | flia ].
    destruct (Nat.eq_dec i k) as [Hik| Hik]; [ flia Hik Hi2n Hk2n | ].
    rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec (j - 1) k) as [Hjk| Hjk]; [ flia Hj Hjk | ].
      apply srng_mul_0_r.
    }
    rewrite srng_add_0_l.
    destruct (Nat.eq_dec k k) as [H| H]; [ clear H | easy ].
    rewrite srng_mul_1_r.
    rewrite srng_add_assoc.
    rewrite fold_rng_sub.
    rewrite rng_add_opp_r, srng_add_0_l.
    rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec j k) as [Hjk| Hjk]; [ flia Hj Hjk | ].
      apply srng_mul_0_r.
    }
    symmetry.
    destruct n; [ apply srng_add_0_l | ].
    now apply all_0_srng_summation_0.
  } {
    apply Nat.nlt_ge in Hk2n.
    assert (H : 1 * 2 ^ n ≤ k < (1 + 1) * 2 ^ n). {
      rewrite Nat.mul_1_l.
      split; [ easy | ].
      change (k < 2 ^ S n).
      enough (H : 0 < 2 ^ S n) by flia H Hk.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite (Nat_div_less_small 1); [ | easy ].
    rewrite (Nat_mod_less_small 1); [ clear H | easy ].
    rewrite Nat.mul_1_l.
    cbn - [ iter_seq Nat.pow ].
    erewrite srng_summation_eq_compat. 2: {
      intros l Hl.
      now rewrite rng_mul_opp_opp.
    }
    cbn - [ iter_seq Nat.pow ].
    rewrite IHn; [ | cbn in Hi; flia Hi | cbn in Hk; flia Hk ].
    destruct (Nat.eq_dec i k) as [Hik| Hik]. {
      subst k.
      remember (i - 2 ^ n) as j eqn:Hj.
      destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
      subst j.
      rewrite srng_add_comm.
      rewrite srng_summation_split_last; [ | flia ].
      f_equal.
      symmetry.
      destruct n; [ easy | ].
      cbn - [ iter_seq ].
      apply srng_summation_succ_succ.
    } {
      destruct (Nat.eq_dec (i - 2 ^ n) (k - 2 ^ n)) as [Hi2k| Hi2k]. {
        flia Hik Hi2k Hi2n Hk2n.
      }
      rewrite srng_add_0_l.
      symmetry.
      destruct n; [ apply srng_add_0_l | ].
      rewrite srng_summation_split_last; [ | flia ].
      now rewrite srng_summation_succ_succ, srng_add_0_r.
    }
  }
}
Qed.

Check mA.
Inspect 1.

Fixpoint srng_of_nat n :=
  match n with
  | 0 => 0%Srng
  | S n' => (1 + srng_of_nat n')%Srng
  end.

(* seems, on paper, that √(n+1) is an eignenvalue for A_{n+1}
   and a corresponding eigenvector is
      ( A_n + √(n+1) I )
      (                ) * V
      (       I        )
   for any vector V of dimension 2^(n+1).
     There is going to be a special case for n = 0.
     We can take V, for example, as (1, 0, 0, 0....0), etc.
   This way, we have to prove that this pair eigen(value,vector)
   works *)

Definition base_vector_1 dim :=
  mk_vect (λ i, match i with 0 => 1%Srng | _ => 0%Srng end) dim.

Definition A_n_eigenvector_of_sqrt_n n μ V :=
  match n with
  | 0 => base_vector_1 0
  | S n' =>
      (mat_of_mat_list_list 0%F
         [[(mA n' + μ × squ_mat_one (2 ^ n))%M]; [squ_mat_one (2 ^ n)]]
       · V)%V
  end.

Theorem m_o_mll_2x2_2x1 : ∀ d M1 M2 M3 M4 M5 M6,
   is_square_mat M1
   → mat_ncols M1 = mat_ncols M2
   → mat_ncols M1 = mat_nrows M5
   → (mat_of_mat_list_list d [[M1; M2]; [M3; M4]] *
      mat_of_mat_list_list d [[M5]; [M6]])%M =
     mat_of_mat_list_list d [[M1 * M5 + M2 * M6]; [M3 * M5 + M4 * M6]]%M.
Proof.
intros * Hsm1 Hc1c2 Hc1r5.
unfold is_square_mat in Hsm1.
apply matrix_eq; [ easy | easy | ].
cbn - [ iter_seq ].
intros * Hi Hj.
rewrite Nat.mul_1_r in Hj.
unfold mat_mul, mat_add.
cbn - [ iter_seq ].
unfold mat_list_list_el.
cbn - [ iter_seq ].
rewrite (Nat.div_small j); [ | flia Hj ].
rewrite (Nat.mod_small j); [ | flia Hj ].
rewrite <- Hc1r5.
rewrite <- Hc1c2.
rewrite (srng_summation_split _ (mat_ncols M1)); [ | flia Hi ].
rewrite srng_summation_split_last; [ | flia ].
assert (H : mat_ncols M1 ≠ 0). {
  intros H; rewrite H in Hsm1.
  now rewrite Hsm1 in Hi; cbn in Hi.
}
rewrite Nat.div_same; [ | easy ].
rewrite Nat.mod_same; [ clear H | easy ].
erewrite srng_summation_eq_compat. 2: {
  intros k Hk.
  rewrite (Nat.div_small (k - 1)); [ | flia Hk ].
  rewrite (Nat.mod_small (k - 1)); [ | flia Hk ].
  cbn - [ iter_seq ].
  easy.
}
cbn - [ iter_seq ].
erewrite (srng_summation_eq_compat _ _ _ (mat_ncols M1 + 1)). 2: {
  intros k Hk.
  rewrite (Nat_div_less_small 1); [ | flia Hk ].
  rewrite (@Nat_mod_less_small 1 k); [ | flia Hk ].
  rewrite Nat.mul_1_l.
  easy.
}
cbn - [ iter_seq ].
destruct (lt_dec i (mat_nrows M1)) as [Hir1| Hir1]. {
  rewrite Nat.div_small; [ | easy ].
  rewrite Nat.mod_small; [ | easy ].
  cbn - [ iter_seq ].
  rewrite <- srng_add_assoc.
  f_equal. {
    rewrite srng_summation_shift; [ | flia Hsm1 Hir1 ].
    apply srng_summation_eq_compat.
    intros k Hk.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  destruct (Nat.eq_dec (mat_ncols M1) 1) as [Hc11| Hc11]. {
    rewrite Hc11; cbn.
    now rewrite srng_add_0_r, srng_add_0_l.
  }
  rewrite srng_summation_shift; [ | flia Hsm1 Hir1 Hc11 ].
  remember (mat_ncols M1) as c.
  replace (c * 2 - 1 - (c + 1)) with (c - 2) by flia.
...

Theorem A_n_eigen_formula : ∀ n μ V,
  (μ * μ)%Rng = srng_of_nat n
  → V = A_n_eigenvector_of_sqrt_n n μ (base_vector_1 (2 ^ n))
  → (mA n · V = μ × V)%V.
Proof.
intros * Hμ HV.
destruct n. {
  cbn in Hμ, HV |-*.
  (* we need to add that the ring is integral *)
  admit.
}
cbn - [ Nat.pow ] in Hμ, HV.
rewrite HV.
rewrite mat_vect_mul_assoc; [ | easy | easy ].
cbn - [ iter_seq Nat.pow ].
...
rewrite m_o_mll_2x2_2x1.
...
(*
remember [mA n; squ_mat_one (2 ^ n)] as M1 eqn:HM1.
remember [squ_mat_one (2 ^ n); (- mA n)%M] as M2 eqn:HM2.
remember [(mA n + μ × squ_mat_one (2 ^ S n))%M] as M3 eqn:HM3.
move M1 after M3.
move M2 before M1.
remember [squ_mat_one (2 ^ S n)] as M4 eqn:HM4.
move M4 before M3.
unfold mat_of_mat_list_list.
cbn - [ iter_seq Nat.pow ].
unfold mat_list_list_el.
cbn - [ iter_seq Nat.pow ].
remember (upper_left_mat_in_list_list 0%F [M1; M2]) as M5 eqn:HM5.
rewrite HM1, HM2 in HM5; cbn in HM5; subst M5.
remember (upper_left_mat_in_list_list 0%F [M3; M4]) as M5 eqn:HM5.
rewrite HM3, HM4 in HM5; cbn in HM5; subst M5.
rewrite mA_nrows, mA_ncols.
remember (length M1) as len eqn:Hlen.
rewrite HM1 in Hlen; cbn in Hlen; subst len.
remember (length M3) as len eqn:Hlen.
rewrite HM3 in Hlen; cbn in Hlen; subst len.
cbn - [ iter_seq Nat.pow ].
rewrite mA_nrows, mA_ncols.
apply vector_eq; [ easy | ].
cbn - [ iter_seq Nat.pow ].
intros k Hk.
...
*)
unfold mat_of_mat_list_list.
cbn - [ iter_seq Nat.pow ].
rewrite mA_nrows, mA_ncols, Nat.mul_1_r.
unfold mat_mul.
cbn - [ iter_seq Nat.pow ].
unfold mat_list_list_el.
cbn - [ iter_seq Nat.pow ].
rewrite mA_nrows, mA_ncols.
apply vector_eq; [ easy | ].
cbn - [ iter_seq Nat.pow ].
intros i Hi.
rewrite srng_summation_split_first; [ | easy | flia ].
rewrite Nat.div_0_l; [ | now apply Nat.pow_nonzero ].
rewrite srng_mul_1_r.
rewrite (all_0_srng_summation_0 _ 1). 2: {
  intros k Hk.
  destruct k; [ easy | ].
  apply srng_mul_0_r.
}
rewrite srng_add_0_r.
rewrite Nat.mod_0_l; [ | now apply Nat.pow_nonzero ].
rewrite (srng_summation_split _ (2 ^ n - 1)); [ | flia ].
rewrite Nat.sub_add; [ | now apply Nat.neq_0_lt_0, Nat.pow_nonzero ].
erewrite srng_summation_eq_compat. 2: {
  intros k Hk.
  rewrite (Nat.div_small k); [ | flia Hi Hk ].
  rewrite (Nat.mod_small k); [ | flia Hi Hk ].
  easy.
}
cbn - [ iter_seq Nat.pow ].
rewrite srng_summation_split_first; [ | easy | flia ].
cbn - [ iter_seq Nat.pow ].
rewrite srng_mul_1_r.
erewrite srng_summation_eq_compat. 2: {
  intros k Hk.
  destruct (Nat.eq_dec k 0) as [Hkz| Hkz]; [ flia Hk Hkz | ].
  rewrite srng_mul_0_r, srng_add_0_r.
  easy.
}
cbn - [ iter_seq Nat.pow ].
destruct (lt_dec i (2 ^ n)) as [Hi2n| Hi2n]. {
  rewrite Nat.div_small; [ | easy ].
  rewrite Nat.mod_small; [ | easy ].
  cbn - [ iter_seq Nat.pow ].
...
rewrite (all_0_srng_summation_0 _ 1). 2: {
  intros k Hk.
  destruct k; [ easy | ].
  cbn.
  rewrite srng_mul_0_r.
}

rewrite (all_0_srng_summation_0 _ 1). 2: {
  intros k Hk.
  destruct k; [ easy | ].
  cbn.
  rewrite srng_mul_0_r.
}
...

Fixpoint first_non_zero_in_col (M : matrix T) it i j :=
  match it with
  | 0 => None
  | S it' =>
      if srng_eq_dec (mat_el M i j) 0 then
        first_non_zero_in_col M it' (i + 1) j
      else Some i
  end.

Theorem first_non_zero_Some : ∀ M it i j k,
  first_non_zero_in_col M it i j = Some k
  → k < i + it ∧
    (∀ h, i ≤ h < k → mat_el M h j = 0%Srng) ∧
    mat_el M k j ≠ 0%Srng.
Proof.
intros * Hk.
revert i j k Hk.
induction it; intros; [ easy | cbn ].
cbn in Hk.
destruct (srng_eq_dec (mat_el M i j) 0) as [Hmz| Hmz]. {
  specialize (IHit _ _ _ Hk) as H1.
  destruct H1 as (H1 & H2 & H3).
  rewrite <- Nat.add_assoc in H1.
  split; [ easy | ].
  split; [ | easy ].
  intros h Hh.
  destruct (Nat.eq_dec i h) as [Hih| Hih]; [ now subst h | ].
  apply H2; flia Hh Hih.
}
injection Hk; intros; subst k.
split; [ flia | ].
split; [ flia | easy ].
Qed.

Theorem first_non_zero_None : ∀ M it i j,
  mat_nrows M ≤ i + it
  → first_non_zero_in_col M it i j = None
  → ∀ h, i ≤ h < mat_nrows M → mat_el M h j = 0%Srng.
Proof.
intros * Hm Hz h Hh.
revert i j h Hz Hh Hm.
induction it; intros; [ flia Hh Hm | ].
cbn in Hz.
destruct (srng_eq_dec (mat_el M i j) 0) as [Hmz| Hmz]; [ | easy ].
destruct (Nat.eq_dec i h) as [Hih| Hih]; [ now subst h | ].
apply (IHit (i + 1)); [ easy | flia Hh Hih | flia Hm ].
Qed.

(* Matrix operator, swapping the rows i1 and i2 of a matrix.

   When multiplying this matrix with another matrix, it returns that
   other matrix where the rows i1 and i2 are swapped
     It is the identity matrix where the 1s at (i1,i1) and (i2,i2)
   are replaced by 0s, and the 0s at (i1,i2) and (i2,i1) are replaced
   by 1s.
     Example swapping rows 1 and 2 (indices start at 0) of a 5×5
   matrix
     1 0 0 0 0
     0 0 1 0 0
     0 1 0 0 0
     0 0 0 1 0
     0 0 0 0 1

   Works even if i1=i2; in that case it is the identity matrix *)

(* perhaps should be defined with "mat_swap_rows" of Matrix.v *)
Definition mat_id_swap_rows sz i1 i2 :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i i1 then if Nat.eq_dec j i2 then 1%Srng else 0%Srng
     else if Nat.eq_dec i i2 then if Nat.eq_dec j i1 then 1%Srng else 0%Srng
     else if Nat.eq_dec i j then 1%Srng else 0%Srng)
    sz sz.

(* Matrix operator, multiplying row k of a matrix by a scalar s

   When multiplying this matrix with another matrix, it returns that
   other matrix where all coefficients in row k are multiplied by s.
     It is the identity matrix where the 1 at (k,k) is replaced by s.
     Example for row 3 (staring at 0) of a 5x5 matrix
       1 0 0 0 0
       0 1 0 0 0
       0 0 1 0 0
       0 0 0 s 0
       0 0 0 0 1
*)

(* perhaps redundant; see Matrix.v *)
Definition mat_id_mul_row_by_scal sz k s :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i j then if Nat.eq_dec i k then s else 1%Srng
     else 0%Srng)
    sz sz.

Arguments mat_id_mul_row_by_scal sz k s%F.

(* Matrix operator, subtracting, to all rows k but row i, the row i multiplied
   by the coefficient in (k,j).

     When multiplying this matrix with another matrix, it returns that
   other matrix where all rows k (but row i) are replaced by themselves
   minus the value in row k of the same column times the value in (k,j).

     Example for row 2 column 4 where "*" contains the opposite of
   the value in the other matrix at its column 4
     1 0 * 0 0
     0 1 * 0 0
     0 0 1 0 0
     0 0 * 1 0
     0 0 * 0 1
*)

(* perhaps redundant; see Matrix.v *)
Definition mat_id_add_rows_mul_scal_row M i j :=
  mk_mat
    (λ i' j',
     if Nat.eq_dec i' j' then 1%Srng
     else if Nat.eq_dec j' i then (- mat_el M i' j)%Rng
     else 0%Srng)
   (mat_nrows M) (mat_nrows M).

(* Gauss-Jordan elimination *)

Definition gauss_jordan_step_op M i j k :=
  (mat_id_swap_rows (mat_nrows M) i k *
   mat_id_add_rows_mul_scal_row M k j *
   mat_id_mul_row_by_scal (mat_nrows M) k (/ mat_el M k j))%M.

Fixpoint gauss_jordan_loop (M : matrix T) i j it :=
  match it with
  | 0 => M
  | S it' =>
      match first_non_zero_in_col M (mat_nrows M - i) i j with
      | Some k =>
          let M' := (gauss_jordan_step_op M i j k * M)%M in
          gauss_jordan_loop M' (i + 1) (j + 1) it'
      | None =>
          gauss_jordan_loop M i (j + 1) it'
      end
  end.

Definition gauss_jordan (M : matrix T) :=
  gauss_jordan_loop (M : matrix T) 0 0 (mat_ncols M).

(* version returning the list of matrices whose product is the
   gauss-jordan elimination of the initial matrix *)

Definition gauss_jordan_step_list M i j k :=
  [mat_id_swap_rows (mat_nrows M) i k;
   mat_id_add_rows_mul_scal_row M k j;
   mat_id_mul_row_by_scal (mat_nrows M) k (/ mat_el M k j)%F].

Fixpoint gauss_jordan_list_loop (M : matrix T) i j it :=
  match it with
  | 0 => []
  | S it' =>
      match first_non_zero_in_col M (mat_nrows M - i) i j with
      | Some k =>
          let ml := gauss_jordan_step_list M i j k in
          let M' := fold_right mat_mul M ml in
          (i, j, k) :: gauss_jordan_list_loop M' (i + 1) (j + 1) it'
      | None =>
          gauss_jordan_list_loop M i (j + 1) it'
      end
  end.

Definition gauss_jordan_list (M : matrix T) :=
  gauss_jordan_list_loop M 0 0 (mat_ncols M).

Definition gauss_jordan' (M : matrix T) :=
  fold_left
    (λ A '(i, j, k),
     let ml := gauss_jordan_step_list A i j k in
     fold_right mat_mul A ml)
    (gauss_jordan_list M) M.

Theorem gauss_jordan_list_loop_gauss_jordan_loop : ∀ M i j it,
  fold_left
    (λ (A : matrix T) '(i, j, k),
       fold_right mat_mul A (gauss_jordan_step_list A i j k))
    (gauss_jordan_list_loop M i j it) M =
  gauss_jordan_loop M i j it.
Proof.
intros.
revert M i j.
induction it; intros; [ easy | ].
cbn - [ gauss_jordan_step_list ].
remember (first_non_zero_in_col M (mat_nrows M - i) i j) as k eqn:Hk.
symmetry in Hk.
destruct k as [k| ]; [ | apply IHit ].
cbn - [ gauss_jordan_step_list ].
rewrite IHit.
unfold gauss_jordan_step_op.
f_equal; cbn.
rewrite mat_mul_assoc; [ | easy | easy ].
now apply mat_mul_assoc.
Qed.

Theorem gauss_jordan_list_gauss_jordan : ∀ (M : matrix T),
  gauss_jordan' M = gauss_jordan M.
Proof.
intros.
unfold gauss_jordan', gauss_jordan.
unfold gauss_jordan_list.
apply gauss_jordan_list_loop_gauss_jordan_loop.
Qed.

(* resolve a system of n equations with n variables whose determinant
   is not zero; Cramer's method *)

Definition resolve_system (M : matrix T) (V : vector T) :=
  map (λ j, (determinant (mat_repl_vect j M V) / determinant M)%F)
    (seq 0 (mat_ncols M)).

(* closing the section and re-open it in order to generalize 'resolve_system'
   to any field T *)

End in_ring.

Arguments mat_id_swap_rows {T so}.
Arguments first_non_zero_in_col {T so sdp} M%M.
Arguments gauss_jordan_step_list {T so ro fo}.
Arguments gauss_jordan_step_op {T so ro fo}.
Arguments resolve_system {T so ro fo}.

Section in_field.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.
Context {scp : sring_comm_prop T}.
Context {sdp : sring_dec_prop T}.
Context {fo : field_op T}.
Context {fp : field_prop T}.

(* resolving a system of n equations with n variables even
   in the case when the determinant is 0 *)
(* returns one only solution (if any); to return the set of solutions,
   we must build a field holding constants a, b, c, etc.; polynomials
   could help but we need polynomials with several variables *)

Fixpoint resolve_loop n (M : matrix T) (V : vector T) :=
  match n with
  | 0 => []
  | S n' =>
      if srng_eq_dec (determinant M) 0%Srng then
        let MV := mat_vect_concat M V in
        let A := gauss_jordan MV in
        (* deletion last row which, normally, contains only zeros
           and the last variable is given the value 1 *)
        let B := mk_mat (mat_el A) (mat_nrows M - 1) (mat_ncols M - 1) in
        let U :=
          let rhs :=
            mk_vect (vect_el (vect_of_mat_col A (mat_ncols M)))
              (mat_nrows M - 1)
          in
          let last_col :=
            mk_vect (vect_el (vect_of_mat_col A (mat_ncols M - 1)))
              (mat_nrows M - 1)
          in
          vect_sub rhs last_col
        in
        resolve_loop n' B U ++ [1%Srng]
      else
        (* resolve for example by Cramer the system of equations Mx=V *)
        resolve_system M V
  end.

Definition resolve (M : matrix T) V :=
  vect_of_list 0%Srng (resolve_loop (mat_nrows M) M V).

(* pivot *)

Fixpoint pivot_index_loop (M : matrix T) i j it :=
  match it with
  | 0 => j
  | S it' =>
      if srng_eq_dec (mat_el M i j) 0 then pivot_index_loop M i (j + 1) it'
      else j
  end.

Definition pivot_index (M : matrix T) i :=
  pivot_index_loop M i 0 (mat_ncols M).

Definition pivot (M : matrix T) i :=
  mat_el M i (pivot_index M i).

Theorem fold_pivot : ∀ M i,
  mat_el M i (pivot_index M i) = pivot M i.
Proof. easy. Qed.

(* row echelon form *)
(* a matrix is in row echelon form if the pivot shifts at each row *)

Definition in_row_echelon_form (M : matrix T) :=
  ∀ i, i < mat_nrows M - 1 → pivot_index M (i + 1) < mat_ncols M →
  pivot_index M i < pivot_index M (i + 1).

(* reduced row echelon form *)
(* a matrix is in reduced row echelon form if
   1/ it is in row echelon form
   2/ the column of pivots hold 1 at pivot and 0 everywhere else
*)

Definition in_reduced_row_echelon_form (M : matrix T) :=
  in_row_echelon_form M ∧
  (∀ i, i < mat_nrows M → ∀ k, k < mat_nrows M →
   pivot_index M i < mat_ncols M
   → mat_el M k (pivot_index M i) = if Nat.eq_dec k i then 1%Srng else 0%Srng).

(* proof that Gauss-Jordan algorithm returns a matrix in row
   echelon form *)

Theorem gauss_jordan_step_op_nrows : ∀ M i j k,
  mat_nrows (gauss_jordan_step_op M i j k) = mat_nrows M.
Proof. easy. Qed.

Theorem gauss_jordan_step_op_ncols : ∀ M i j k,
  mat_ncols (gauss_jordan_step_op M i j k) = mat_nrows M.
Proof. easy. Qed.

Theorem gauss_jordan_loop_nrows : ∀ M i j it,
  mat_nrows (gauss_jordan_loop M i j it) = mat_nrows M.
Proof.
intros.
revert M i j.
induction it; intros; [ easy | ].
cbn - [ gauss_jordan_step_op ].
remember (first_non_zero_in_col _ _ _ _) as k eqn:Hk.
symmetry in Hk.
destruct k as [k| ]. {
  rewrite IHit.
  rewrite mat_mul_nrows.
  apply gauss_jordan_step_op_nrows.
}
apply IHit.
Qed.

Theorem gauss_jordan_loop_ncols : ∀ M i j it,
  mat_ncols (gauss_jordan_loop M i j it) = mat_ncols M.
Proof.
intros.
revert M i j.
induction it; intros; [ easy | ].
cbn - [ gauss_jordan_step_op ].
remember (first_non_zero_in_col _ _ _ _) as k eqn:Hk.
symmetry in Hk.
destruct k as [k| ]. {
  rewrite IHit.
  apply mat_mul_ncols.
}
apply IHit.
Qed.

Theorem gauss_jordan_nrows : ∀ M,
  mat_nrows (gauss_jordan M) = mat_nrows M.
Proof.
intros.
apply gauss_jordan_loop_nrows.
Qed.

Theorem gauss_jordan_ncols : ∀ M,
  mat_ncols (gauss_jordan M) = mat_ncols M.
Proof.
intros.
apply gauss_jordan_loop_ncols.
Qed.

Theorem mat_swap_row_mul_l_lemma : ∀ M i j sz,
  i < sz
  → (Σ (k = 0, sz - 1), (if Nat.eq_dec k i then 1 else 0) * mat_el M k j)%Rng
    = mat_el M i j.
Proof.
intros * His.
rewrite (srng_summation_split _ i); [ | flia His ].
rewrite srng_summation_split_last; [ | flia His ].
rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec (k - 1) i) as [H| H]; [ flia Hk H | clear H ].
  apply srng_mul_0_l.
}
rewrite srng_add_0_l.
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
rewrite srng_mul_1_l.
rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec k i) as [H| H]; [ flia Hk H | clear H ].
  apply srng_mul_0_l.
}
apply srng_add_0_r.
Qed.

Theorem mat_id_swap_rows_mul_l : ∀ M sz i1 i2,
  sz = mat_nrows M
  → i1 < sz
  → i2 < sz
  → (mat_id_swap_rows sz i1 i2 * M)%M = mat_swap_rows M i1 i2.
Proof.
intros * Hsz Hi1s Hi2s.
apply matrix_eq; [ easy | easy | ].
cbn - [ Nat.eq_dec iter_seq ].
intros i j Hi Hj.
destruct (Nat.eq_dec i i1) as [Hii1| Hii1]. {
  now apply mat_swap_row_mul_l_lemma.
}
destruct (Nat.eq_dec i i2) as [Hii2| Hii2]. {
  now apply mat_swap_row_mul_l_lemma.
}
rewrite (srng_summation_split _ i); [ | flia Hi ].
rewrite srng_summation_split_last; [ | flia ].
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | flia H ].
rewrite srng_mul_1_l.
rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia Hk H | clear H ].
  apply srng_mul_0_l.
}
rewrite srng_add_0_l.
rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i k) as [H| H]; [ flia Hk H | clear H ].
  apply srng_mul_0_l.
}
apply srng_add_0_r.
Qed.

(* Multiplicative factor for computing determinant from gauss-jordan form.
   We have
      det (M) = this_mult_fact * det (gauss_jordan M)
   We know that the determinant of a gauss_jordan form is 1 or 0.
 *)

Fixpoint det_mult_fact_from_gjl_loop (M : matrix T) i j it :=
  match it with
  | 0 => 1%Srng
  | S it' =>
      match first_non_zero_in_col M (mat_nrows M - i) i j with
      | Some k =>
          let ml := gauss_jordan_step_list M i j k in
          let M' := fold_right mat_mul M ml in
          let v :=
            ((if Nat.eq_dec i k then 1 else (- (1))) * mat_el M k j)%Rng
          in
          (v * det_mult_fact_from_gjl_loop M' (S i) (S j) it')%Srng
      | None =>
          det_mult_fact_from_gjl_loop M i (S j) it'
      end
  end.

Definition det_mult_fact_from_gjl M :=
  det_mult_fact_from_gjl_loop M 0 0 (mat_ncols M).

(* *)

Theorem resolved_with_nz_det : ∀ M V R,
  is_square_mat M
  → mat_nrows M = vect_nrows R
  → determinant M ≠ 0%F
  → V = vect_of_list 0%F (resolve_system M R)
  → (M · V)%V = R.
Proof.
intros * Hsm Hmr Hdz Hv.
unfold is_square_mat in Hsm.
unfold resolve_system in Hv.
unfold mat_mul_vect_r.
apply vector_eq; [ easy | ].
cbn - [ iter_seq ].
intros i Hi.
subst V.
cbn - [ iter_seq ].
erewrite srng_summation_eq_compat. 2: {
  intros j Hj.
  rewrite (List_map_nth_in _ 0); [ | rewrite seq_length; flia Hsm Hi Hj ].
  rewrite seq_nth; [ | flia Hsm Hi Hj ].
  rewrite Nat.add_0_l.
  easy.
}
cbn - [ iter_seq ].
(* should try to replace both determinants by a version going through
   column i0 instead of row 0: this way the sub-determinants are the
   same. *)
(* but in that case, I need that a determinant going through any row
   or any column is equal to the determinant I defined (going through
   the first row; I started that in Matrix.v, but I am blocked *)
(* well, I don't really need this theorem since my problem is about
   matrices the discriminants of which are equal to zero *)
(* but I wanted to prove it anyway, for the sport; I thought it was
   easy but it is not *)
...

Theorem resolved_with_zero_det : ∀ M V R,
  is_square_mat M
  → mat_nrows M = vect_nrows R
  → determinant M = 0%Rng
  → V = resolve M R
  → (M · V)%V = R.
Proof.
intros * Hsm Hrr Hdet Hv.
unfold is_square_mat in Hsm.
unfold resolve in Hv.
remember (mat_nrows M) as r eqn:Hmr; symmetry in Hmr.
rename Hsm into Hmc.
symmetry in Hmc, Hrr.
revert M V R Hmr Hmc Hrr Hdet Hv.
induction r; intros. {
  cbn in Hv.
  subst V.
  unfold mat_mul_vect_r.
  destruct R as (fr, rr).
  cbn in Hrr; subst rr; rewrite Hmr.
  now apply vector_eq.
}
cbn in Hv.
destruct (srng_eq_dec (determinant M) 0) as [Hdz| Hdz]; [ | easy ].
clear Hdz.
remember (gauss_jordan_loop (mat_vect_concat M R) 0 0 (mat_ncols M + 1))
  as MGJ eqn:Hmgj.
rewrite Hmr, Nat.sub_succ, Nat.sub_0_r in Hv.
rewrite Hmc, Nat.sub_succ, Nat.sub_0_r in Hv.
remember {| mat_el := mat_el MGJ; mat_nrows := r; mat_ncols := r |} as M'
  eqn:HM'.
remember
  ({| vect_el := λ i, mat_el MGJ i (S r); vect_nrows := r |} -
   {| vect_el := λ i, mat_el MGJ i r; vect_nrows := r |})%V as V' eqn:HV'.
unfold vect_sub in HV'.
unfold vect_opp in HV'; cbn in HV'.
unfold vect_add in HV'; cbn in HV'.
remember (mk_vect (vect_el R) r) as R' eqn:HR'.
destruct (srng_eq_dec (determinant M') 0) as [Hdz| Hdz]. {
  specialize (IHr M' V' R') as H1.
  assert (H : mat_nrows M' = r) by now subst M'.
  specialize (H1 H); clear H.
  assert (H : mat_ncols M' = r) by now subst M'.
  specialize (H1 H); clear H.
  assert (H : vect_nrows R' = r) by now subst R'.
  specialize (H1 H Hdz); clear H.
...

Theorem resolved : ∀ M V R,
  is_square_mat M
  → mat_nrows M = vect_nrows R
  → V = resolve M R
  → (M · V)%V = R.
Proof.
intros * Hsm Hrr Hv.
unfold is_square_mat in Hsm.
unfold resolve in Hv.
remember (mat_nrows M) as r eqn:Hr; symmetry in Hr.
destruct r. {
  cbn in Hv.
  subst V.
  unfold mat_mul_vect_r.
  destruct R as (fr, rr).
  cbn in Hrr; subst rr; rewrite Hr.
  now apply vector_eq.
}
rename Hr into Hmr.
symmetry in Hsm, Hrr.
cbn in Hv.
destruct (srng_eq_dec (determinant M) 0) as [Hdz| Hdz]. 2: {
...
Abort. (* for the moment...
  apply resolved_with_nz_det.
...
remember (gauss_jordan_loop (mat_vect_concat M R) 0 0 (mat_ncols M + 1))
  as MGJ eqn:Hmgj.
remember
  {| mat_el :=
       mat_el (gauss_jordan_loop (mat_vect_concat M R) 0 0 (mat_ncols M + 1));
     mat_nrows := mat_nrows M - 1;
     mat_ncols := mat_ncols M - 1 |}
  as A eqn:Ha.
remember {|
             vect_el := λ i : nat,
                          mat_el
                            (gauss_jordan_loop (mat_vect_concat M R) 0 0
                               (mat_ncols M + 1)) i 
                            (mat_ncols M);
             vect_nrows := mat_nrows M - 1 |} as Vrhs eqn:Hvrhs.
remember {|
             vect_el := λ i : nat,
                          mat_el
                            (gauss_jordan_loop (mat_vect_concat M R) 0 0
                               (mat_ncols M + 1)) i 
                            (mat_ncols M - 1);
             vect_nrows := mat_nrows M - 1 |} as Vlast eqn:Hvlast.
Print resolve_loop.
...
*)

(* Eigenvector property: the fact that V is such that MV=λV *)

Definition eval_mat_polyn M x :=
  mk_mat (λ i j, eval_polyn (mat_el M i j) x) (mat_nrows M) (mat_ncols M).

Theorem eigenvector_prop : ∀ M μ V S,
  eval_polyn (charac_polyn M) μ = 0%Srng
  → S = eval_mat_polyn (xI_sub_M M) μ
  → V = resolve S (vect_zero (mat_ncols M))
  → (M · V = μ × V)%V ∧ V ≠ vect_zero (vect_nrows V).
Proof.
intros * Hμ Hs Hv.
unfold charac_polyn in Hμ.
Abort. (* for the moment...
...
specialize (resolved Hv) as H1.
...
*)

Theorem gauss_jordan_in_reduced_row_echelon_form : ∀ (M : matrix T),
  mat_ncols M ≠ 0
  → in_reduced_row_echelon_form (gauss_jordan M).
Proof.
intros * Hcz.
(*
split. {
  unfold in_row_echelon_form.
  intros i Hi Hp.
...
  Hcz : mat_ncols M ≠ 0
  Hi : i < mat_nrows (gauss_jordan M) - 1
  Hp : pivot_index (gauss_jordan M) (i + 1) < mat_ncols (gauss_jordan M)
  ============================
  pivot_index (gauss_jordan M) i < pivot_index (gauss_jordan M) (i + 1)
*)
split. 2: {
  intros i Hi k Hk Hp.
  move k before i.
  rewrite gauss_jordan_nrows in Hi, Hk.
  rewrite gauss_jordan_ncols in Hp.
  destruct (Nat.eq_dec k i) as [Hki| Hki]. {
    subst i; clear Hi.
    rewrite <- gauss_jordan_list_gauss_jordan in Hp |-*; cycle 1. {
      easy.
    } {
      easy.
    } {
      easy.
Abort. (* for the moment...
...
(*trying to prove it just for the upper left number of the matrix*)
destruct k. {
  unfold gauss_jordan in Hp |-*.
  unfold pivot_index in Hp |-*.
  rewrite gauss_jordan_loop_ncols in Hp |-*.
  remember (mat_ncols M) as it eqn:Hit; symmetry in Hit.
  destruct it; [ easy | clear Hcz ].
  cbn - [ gauss_jordan_step_op ] in Hp |-*.
  rewrite Nat.sub_0_r in Hp |-*.
  remember (first_non_zero_in_col _ _ _ _) as k1 eqn:Hk1.
  symmetry in Hk1.
  destruct k1 as [k1| ]. {
    remember (gauss_jordan_loop _ _ _ _) as A eqn:Ha.
    destruct (srng_eq_dec (mat_el A 0 0) 0) as [Hmz| Hmz]. {
      unfold gauss_jordan_step_op in Ha.
      specialize (first_non_zero_prop _ _ _ _ Hk1) as (H1 & H2 & H3).
      cbn in H1.
...
      remember (multiply_row_by_scalar _ _ _ _) as A' eqn:Ha'.
      remember (swap_rows M 0 k1) as A'' eqn:Ha''.
      assert (H4 : mat_el A'' 0 0 ≠ 0%Srng). {
        rewrite Ha''.
        cbn - [ iter_seq Nat.eq_dec ].
        rewrite srng_summation_split_first; [ | easy | flia H1 ].
        destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
        destruct (Nat.eq_dec 0 k1) as [Hk1z| Hk1z]. {
          subst k1; rewrite srng_mul_1_l.
          rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
            intros i Hi.
            destruct (Nat.eq_dec i 0) as [Hiz| Hiz]; [ flia Hi Hiz | ].
            apply srng_mul_0_l.
          }
          now rewrite srng_add_0_r.
        }
        rewrite srng_mul_0_l, srng_add_0_l.
        rewrite (srng_summation_split _ k1); [ | flia H1 ].
        rewrite srng_summation_split_last; [ | flia Hk1z ].
        destruct (Nat.eq_dec k1 k1) as [H| H]; [ clear H | easy ].
        rewrite srng_mul_1_l.
        rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
          intros i Hi.
          destruct (Nat.eq_dec (i - 1) k1) as [H| H]; [ flia H Hi | ].
          apply srng_mul_0_l.
        }
        rewrite srng_add_0_l.
        rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
          intros i Hi.
          destruct (Nat.eq_dec i k1) as [H| H]; [ flia H Hi | ].
          apply srng_mul_0_l.
        }
        now rewrite srng_add_0_r.
      }
      assert (H5 : mat_el A' 0 0 = 1%Srng). {
        rewrite Ha', Ha''.
        cbn - [ iter_seq Nat.eq_dec ].
...
        apply fld_mul_inv_l.
        rewrite srng_summation_split_first; [ | easy | flia H1 ].
        destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
...
        rewrite srng_mul_0_l, srng_add_0_l.
        erewrite srng_summation_eq_compat; [ | easy | ]. 2: {
          intros i Hi.
          destruct (Nat.eq_dec 0 i) as [H| H]; [ flia Hi H | clear H ].
          easy.
        }
        cbn - [ iter_seq Nat.eq_dec ].
        rewrite (srng_summation_split _ k1); [ | flia H1 ].
        destruct (Nat.eq_dec k1 0) as [Hk1z| Hk1z]. {
          exfalso; subst k1.
          (* mmm... pas si simple *)
...
        apply (first_non_zero_prop _ _ _ _ Hk1).
      }
      move Hmz at bottom.
      (* normalement, contradiction entre H4 et Hmz
         parce que gauss_jordan_loop ne modifie pas
         mat_el A' 0 0 *)
      rewrite Ha in Hmz.
      specialize (List_app_fold_left) as H5.
      specialize (H5 nat (matrix T) T A').
      specialize (H5 (seq 0 (mat_nrows M))).
      remember (λ (B : matrix T) (i' : nat),
               if Nat.eq_dec i' 0
               then B
               else
                add_one_row_scalar_multiple_another so B i'
                  (- mat_el B i' 0)%F 0) as f eqn:Hf.
      specialize (H5 f).
      specialize (H5 (λ A', mat_el (gauss_jordan_loop A' 1 1 it) 0 0)).
      cbn in H5.
      rewrite H5 in Hmz; [ clear H5 | ]. 2: {
        intros A''' i Hi.
        rewrite Hf.
        destruct (Nat.eq_dec i 0) as [Hiz| Hiz]; [ easy | ].
        destruct i; [ easy | clear Hiz ].
Theorem glop : ∀ A i j it,
  mat_el (gauss_jordan_loop A (S i) (S j) it) 0 0 = mat_el A 0 0.
Proof.
intros.
revert i j A.
induction it; intros; [ easy | ].
cbn - [ gauss_jordan_step ].
remember (first_non_zero_in_col A (mat_nrows A - S i) (S i) (S j)) as k eqn:Hk.
symmetry in Hk.
destruct k as [k| ]; [ | apply IHit ].
rewrite IHit.
unfold gauss_jordan_step.
rewrite multiply_row_by_scalar_nrows.
rewrite swap_rows_nrows.
remember (swap_rows _ _ _) as A' eqn:Ha'.
remember (multiply_row_by_scalar _ _ _ _) as A'' eqn:Ha''.
move A'' before A'.
remember (mat_nrows A) as r eqn:Hr; symmetry in Hr.
destruct r; [ easy | ].
rewrite <- (Nat.add_1_l r).
rewrite seq_app.
rewrite fold_left_app; cbn.
remember (add_one_row_scalar_multiple_another _ _ _ _ _) as A''' eqn:Ha'''.
move A''' before A''.
...
rewrite List_app_fold_left with
  (g := (λ f b c a, f a b c) (mat_el (T := T)) 0 0). 2: {
  intros A'''' i' Hi'.
  destruct (Nat.eq_dec i' (S i)) as [Hii| Hii]; [ easy | ].
  destruct i'. {
    cbn.
    rewrite <- srng_add_0_r.
    f_equal.
...
(*end trying to prove it for the upper left number of the matrix*)
...
    unfold gauss_jordan in Hp |-*.
    unfold pivot_index in Hp |-*.
    rewrite gauss_jordan_loop_ncols in Hp |-*.
    remember (mat_ncols M) as it eqn:Hit; symmetry in Hit.
    destruct it; [ easy | clear Hcz ].
    cbn - [ gauss_jordan_step ] in Hp |-*.
    rewrite Nat.sub_0_r in Hp |-*.
    remember (first_non_zero_in_col _ _ _ _) as k1 eqn:Hk1.
    symmetry in Hk1.
    destruct k1 as [k1| ]. {
      remember (gauss_jordan_loop _ _ _ _) as A eqn:Ha.
      destruct (srng_eq_dec (mat_el A k 0) 0) as [Hmz| Hmz]. {
        destruct it; [ cbn in Hp; flia Hp | ].
        cbn in Hp |-*.
        destruct (srng_eq_dec (mat_el A k 1) 0) as [Hm1z| Hm1z]. {
          destruct it; [ cbn in Hp; flia Hp | ].
          cbn in Hp |-*.
          destruct (srng_eq_dec (mat_el A k 2) 0) as [Hm2z| Hm2z]. {
            destruct it; [ cbn in Hp; flia Hp | ].
            cbn in Hp |-*.
            destruct (srng_eq_dec (mat_el A k 3) 0) as [Hm3z| Hm3z]. {
...
            }
            rewrite Ha.
            remember (S (S it)) as sit eqn:Hsit.
            cbn - [ gauss_jordan_step ].
            rewrite gauss_jordan_step_nrows.
            remember (gauss_jordan_step so M 0 0 k1) as A' eqn:Ha'.
            remember (first_non_zero_in_col A' _ 1 1) as k2 eqn:Hk2.
            symmetry in Hk2.
            move k2 before k1.
            move Hk2 before Hk1.
            move A before M; move A' before A.
            destruct k2 as [k2| ]. {
              remember (gauss_jordan_step so A' _ _ _) as A2 eqn:Ha2.
              remember (gauss_jordan_loop A2 _ _ _) as A'2 eqn:Ha'2.
              move A2 before A'; move A'2 before A2.
              move Ha2 before Ha; move Ha'2 before Ha2.
clear Hp.
rewrite Hsit in Ha'2.
(*
...
  Ha'2 : A'2 = gauss_jordan_loop A2 2 2 (S (S it))
  ============================
  mat_el A'2 k 3 = 1%F
...
*)
Theorem glop : ∀ A A' k j it i,
   A = gauss_jordan_loop A' i i (it + j)
  → pivot_index_loop A k (S j) it < it + S j
  → mat_el A k (pivot_index_loop A k (S j) it) = 1%Srng.
Proof.
intros A * Ha Hp.
revert A A' k j i Ha Hp.
induction it; intros A A' k j i Ha Hp; [ cbn in Hp; flia Hp | ].
cbn in Hp |-*.
destruct (srng_eq_dec (mat_el A k (S j)) 0) as [Hmjz| Hmjz]. {
  apply IHit with (A' := A') (i := i); [ | flia Hp ].
  now replace (it + (j + 1)) with (S it + j) by flia.
}
clear Hp.
cbn - [ gauss_jordan_step ] in Ha.
rewrite Ha.
remember (first_non_zero_in_col A' (mat_nrows A' - i) i i) as k1 eqn:Hk1.
symmetry in Hk1.
destruct k1 as [k1| ]. {
  remember (gauss_jordan_step so A' i i k1) as A'' eqn:Ha''.
  specialize (IHit A A'' 42 j (i + 1) Ha) as H1.
(* ouais, c'pas clair... *)
...
  Hmjz : mat_el A k (S j) ≠ 0%F
  ============================
  mat_el A k (S j) = 1%F
...
    subst k; clear Hk.
    unfold gauss_jordan.
    remember (mat_ncols M) as c eqn:Hc; symmetry in Hc.
    destruct c; [ easy | clear Hcz ].
    cbn - [ gauss_jordan_step ].
    rewrite Nat.sub_0_r.
    remember (mat_nrows M) as r eqn:Hr; symmetry in Hr.
    move Hr after Hc.
    destruct r; [ easy | ].
    cbn - [ gauss_jordan_step ].
    destruct (srng_eq_dec (mat_el M 0 0) 0) as [Hmz| Hmz]. {
      remember (first_non_zero_in_col _ _ _ _) as k eqn:Hk.
      symmetry in Hk.
      destruct k as [k| ]. {
        remember (gauss_jordan_loop _ _ _ _) as A eqn:HA.
        revert M A c i k Hi Hr Hc Hmz Hk HA.
        induction r; intros; [ easy | ].
        rename A0 into A.
        cbn in Hk.
        destruct (srng_eq_dec (mat_el M 1 0) 0) as [Hm1z| Hm1z]. {
          destruct i. {
            clear IHr Hi.
...
*)

About mA.
Arguments mA {T so ro}.
About mA.

(*
End in_field.
Require Import ZArith Zring.
Open Scope Z.
Existing Instance Z_semiring_op.
Existing Instance Z_ring_op.
Definition glop n := list_list_of_mat (mA Z_semiring_op n).
Definition glip n := list_list_of_mat (squ_mat_one (Nat.pow 2 (n - 1))).
Compute glip 3.
Compute glop 3.
Check mk_vect.
Definition mB n i := mk_vect (λ j, if Nat.eq_dec i j then 1 else 0) n.
Search vector.
Definition pouet n i := list_of_vect (mat_mul_vect_r (mA _ n) (mB n i)).
Compute pouet 4 6.
Require Import Rational Qfield2.
Import Q.Notations.
Open Scope Q_scope.
Existing Instance Q_semiring_op.
Existing Instance Q_ring_op.
Existing Instance Q_sring_dec_prop.
Existing Instance Q_field_op.
Existing Instance Q_semiring_prop.
Existing Instance Q_ring_prop.

Compute determinant (mA Q_semiring_op 4).
Compute list_list_of_mat (gauss_jordan' (mA Q_semiring_op 2)).
*)

...

(* here, I would like to prove that, knowing that An^2 = nI, the
   eigenvalues of An are √n and -√n, as the Lemma 2.2. claims *)

Theorem A_eigenvalue : ∀ n μ,
  (μ * μ = srng_of_nat n)%Rng
  → ∃ V,
      V ≠ vect_zero (vect_nrows V) ∧
      (mat_of_squ_bmat (mA n) · V = μ × V)%V.
Proof.
intros * Hμ2n.
specialize (lemma_2_A_n_2_eq_n_I' n) as H1.
...

End in_field.
