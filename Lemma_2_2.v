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

Require Import Misc Matrix.
Require Import RingLike.
Require Import RLsummation.
Import matrix_Notations.

Section in_ring_like.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {Hro : rngl_has_opp = true}.
Context {Hin : rngl_has_inv = true}.
Context {Hic : rngl_is_comm = true}.
Context {Hde : rngl_has_dec_eq = true}.
Context
  {Hii :
     (rngl_is_integral_not_provable ||
      rngl_has_inv && rngl_has_dec_eq)%bool = true}.

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
  | 0 => mat_of_scalar 0%F
  | S n' =>
      mat_of_mat_list_list 0%F
        [[mA n'; mI (2 ^ n')];
         [mI (2 ^ n'); (- mA n')%M]]
  end.

Definition rngl_of_nat n := (Σ (i = 1, n), 1)%F.

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

Theorem mA_is_square : ∀ n, is_square_mat (mA n).
Proof.
intros.
unfold is_square_mat.
now rewrite mA_nrows, mA_ncols.
Qed.

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I : ∀ n,
  (mA n * mA n)%M = (rngl_of_nat n × mI (2 ^ n))%M.
Proof.
intros.
apply matrix_eq; [ apply mA_nrows | apply mA_ncols | ].
cbn - [ iter_seq ].
rewrite mA_nrows, mA_ncols.
intros i k Hi Hk.
revert i k Hi Hk.
induction n; intros. {
  cbn.
  rewrite rngl_mul_0_l; [ | easy ].
  rewrite rngl_mul_0_l; [ | easy ].
  apply rngl_add_0_l.
}
rewrite (rngl_summation_split _ (2 ^ n - 1)). 2: {
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
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite (Nat.div_small j); [ | cbn in Hi; flia Hj Hi ].
  rewrite (Nat.mod_small j); [ | cbn in Hi; flia Hj Hi ].
  easy.
}
cbn - [ iter_seq Nat.pow ].
rewrite rngl_add_comm.
erewrite rngl_summation_eq_compat. 2: {
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
rewrite rngl_add_comm.
destruct (lt_dec i (2 ^ n)) as [Hi2n| Hi2n]. {
  rewrite (Nat.div_small i); [ | easy ].
  rewrite (Nat.mod_small i); [ | easy ].
  cbn - [ iter_seq Nat.pow ].
  destruct (lt_dec k (2 ^ n)) as [Hk2n| Hk2n]. {
    rewrite (Nat.div_small k); [ | easy ].
    rewrite (Nat.mod_small k); [ | easy ].
    cbn - [ iter_seq Nat.pow ].
    rewrite IHn; [ | easy | easy ].
    rewrite (rngl_summation_split _ (i + 2 ^ n)); [ | cbn; flia Hi Hi2n ].
    rewrite rngl_summation_split_last; [ | flia ].
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i (j - 1 - 2 ^ n)) as [Hij| Hij]. {
        flia Hj Hij.
      }
      now apply rngl_mul_0_l.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i (j - 2 ^ n)) as [Hij| Hij]; [ flia Hj Hij | ].
      now apply rngl_mul_0_l.
    }
    rewrite rngl_add_0_r.
    rewrite Nat.add_sub.
    destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
    rewrite rngl_mul_1_l.
    symmetry.
    destruct (Nat.eq_dec i k) as [Hik| Hik]. {
      subst k.
      do 2 rewrite rngl_mul_1_r.
      destruct n; [ easy | ].
      cbn - [ iter_seq ].
      unfold rngl_of_nat.
      rewrite rngl_summation_split_last; [ | flia ].
      now rewrite rngl_summation_succ_succ.
    } {
      rewrite rngl_mul_0_r; [ | easy ].
      rewrite rngl_mul_0_r; [ | easy ].
      symmetry; apply rngl_add_0_r.
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
    rewrite (rngl_summation_split _ (k - 2 ^ n)). 2: {
      split; [ flia | ].
      apply -> Nat.succ_le_mono.
      cbn in Hk; flia Hk.
    }
    rewrite rngl_summation_split_last; [ | flia ].
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec (j - 1) (k - 2 ^ n)) as [Hjk| Hjk]. {
        flia Hj Hjk.
      }
      now apply rngl_mul_0_r.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec j (k - 2 ^ n)) as [Hjk| Hjk]; [ flia Hj Hjk | ].
      now apply rngl_mul_0_r.
    }
    rewrite rngl_add_0_r.
    remember (k - 2 ^ n) as j eqn:Hj.
    destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
    subst j; rewrite rngl_mul_1_r.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      now rewrite rngl_mul_opp_opp.
    }
    cbn - [ iter_seq Nat.pow ].
    rewrite rngl_summation_shift; [ | cbn; flia Hi ].
    rewrite Nat_sub_sub_swap.
    replace (2 ^ S n - 2 ^ n) with (2 ^ n). 2: {
      cbn; rewrite Nat.add_0_r; symmetry.
      apply Nat.add_sub.
    }
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite Nat.add_comm, Nat.add_sub.
      rewrite rngl_mul_opp_opp; [ | easy ].
      now rewrite rngl_mul_opp_r.
    }
    cbn - [ iter_seq Nat.pow ].
    rewrite (rngl_summation_split _ i); [ | flia Hi Hi2n ].
    rewrite rngl_summation_split_last; [ | flia ].
    destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
    rewrite rngl_mul_1_l.
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i (j - 1)) as [Hij| Hij]; [ flia Hij Hj | ].
      rewrite rngl_mul_0_l; [ | easy ].
      now apply rngl_opp_0.
    }
    rewrite rngl_add_0_l.
    rewrite rngl_add_assoc.
    rewrite fold_rngl_sub.
    rewrite rngl_add_opp_r; [ | easy ].
    rewrite rngl_add_0_l.
    destruct (Nat.eq_dec i k) as [Hik| Hik]; [ flia Hi2n Hk2n Hik | ].
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i j) as [Hij| Hij]; [ flia Hj Hij | ].
      rewrite rngl_mul_0_l; [ | easy ].
      now apply rngl_opp_0.
    }
    symmetry.
    now apply rngl_mul_0_r.
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
  rewrite (rngl_summation_split _ (i - 2 ^ n)). 2: {
    split; [ flia | ].
    apply -> Nat.succ_le_mono.
    cbn in Hi; flia Hi.
  }
  rewrite rngl_summation_split_last; [ | flia ].
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros j Hj.
    destruct (Nat.eq_dec (i - 2 ^ n) (j - 1)) as [Hij| Hij]. {
      flia Hj Hij.
    }
    now apply rngl_mul_0_l.
  }
  rewrite rngl_add_0_l.
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros j Hj.
    destruct (Nat.eq_dec (i - 2 ^ n) j) as [Hij| Hij]; [ flia Hj Hij | ].
    now apply rngl_mul_0_l.
  }
  rewrite rngl_add_0_r.
  remember (i - 2 ^ n) as j eqn:Hj.
  destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
  subst j; rewrite rngl_mul_1_l.
  rewrite rngl_summation_shift; [ | cbn; flia Hi ].
  rewrite Nat_sub_sub_swap.
  replace (2 ^ S n - 2 ^ n) with (2 ^ n). 2: {
    cbn; rewrite Nat.add_0_r; symmetry.
    apply Nat.add_sub.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  cbn - [ iter_seq Nat.pow ].
  destruct (lt_dec k (2 ^ n)) as [Hk2n| Hk2n]. {
    rewrite (Nat.div_small k); [ | easy ].
    rewrite (Nat.mod_small k); [ | easy ].
    cbn - [ iter_seq Nat.pow ].
    rewrite (rngl_summation_split _ k). 2: {
      cbn in Hk; flia Hk Hk2n.
    }
    rewrite rngl_summation_split_last; [ | flia ].
    destruct (Nat.eq_dec i k) as [Hik| Hik]; [ flia Hik Hi2n Hk2n | ].
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec (j - 1) k) as [Hjk| Hjk]; [ flia Hj Hjk | ].
      now apply rngl_mul_0_r.
    }
    rewrite rngl_add_0_l.
    destruct (Nat.eq_dec k k) as [H| H]; [ clear H | easy ].
    rewrite rngl_mul_1_r.
    rewrite rngl_add_assoc.
    rewrite fold_rngl_sub.
    rewrite rngl_add_opp_r; [ | easy ].
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec j k) as [Hjk| Hjk]; [ flia Hj Hjk | ].
      now apply rngl_mul_0_r.
    }
    symmetry.
    now apply rngl_mul_0_r.
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
    erewrite rngl_summation_eq_compat. 2: {
      intros l Hl.
      now rewrite rngl_mul_opp_opp.
    }
    cbn - [ iter_seq Nat.pow ].
    rewrite IHn; [ | cbn in Hi; flia Hi | cbn in Hk; flia Hk ].
    destruct (Nat.eq_dec i k) as [Hik| Hik]. {
      subst k.
      remember (i - 2 ^ n) as j eqn:Hj.
      destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
      subst j.
      do 2 rewrite rngl_mul_1_r.
      rewrite rngl_add_comm.
      unfold rngl_of_nat; symmetry.
      rewrite rngl_summation_split_last; [ | flia ].
      now rewrite rngl_summation_succ_succ.
    } {
      destruct (Nat.eq_dec (i - 2 ^ n) (k - 2 ^ n)) as [Hi2k| Hi2k]. {
        flia Hik Hi2k Hi2n Hk2n.
      }
      rewrite rngl_add_0_l.
      rewrite rngl_mul_0_r; [ | easy ].
      now rewrite rngl_mul_0_r.
    }
  }
}
Qed.

(*
Print mat_nat_mul_l.
Print rngl_mul_nat_l.
*)

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

Theorem m_o_mll_2x2_2x1 : ∀ d M1 M2 M3 M4 M5 M6,
   is_square_mat M1
   → mat_ncols M1 = mat_ncols M2
   → mat_ncols M1 = mat_ncols M3
   → mat_ncols M1 = mat_ncols M4
   → mat_ncols M1 = mat_nrows M5
   → (mat_of_mat_list_list d [[M1; M2]; [M3; M4]] *
      mat_of_mat_list_list d [[M5]; [M6]])%M =
     mat_of_mat_list_list d [[M1 * M5 + M2 * M6]; [M3 * M5 + M4 * M6]]%M.
Proof.
intros * Hsm1 Hc1c2 Hc1c3 Hc1c4 Hc1r5.
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
rewrite <- Hc1c2, <- Hc1c3, <- Hc1c4, <- Hc1r5.
rewrite (rngl_summation_split _ (mat_ncols M1)); [ | flia Hi ].
rewrite rngl_summation_split_last; [ | flia ].
assert (H : mat_ncols M1 ≠ 0). {
  intros H; rewrite H in Hsm1.
  now rewrite Hsm1 in Hi; cbn in Hi.
}
rewrite Nat.div_same; [ | easy ].
rewrite Nat.mod_same; [ clear H | easy ].
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite (Nat.div_small (k - 1)); [ | flia Hk ].
  rewrite (Nat.mod_small (k - 1)); [ | flia Hk ].
  cbn - [ iter_seq ].
  easy.
}
cbn - [ iter_seq ].
erewrite (rngl_summation_eq_compat _ _ _ (mat_ncols M1 + 1)). 2: {
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
  rewrite <- rngl_add_assoc.
  f_equal. {
    rewrite rngl_summation_shift; [ | flia Hsm1 Hir1 ].
    apply rngl_summation_eq_compat.
    intros k Hk.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  destruct (Nat.eq_dec (mat_ncols M1) 1) as [Hc11| Hc11]. {
    rewrite Hc11; cbn.
    now rewrite rngl_add_0_r, rngl_add_0_l.
  }
  rewrite rngl_summation_shift; [ | flia Hsm1 Hir1 Hc11 ].
  remember (mat_ncols M1) as c.
  replace (c * 2 - 1 - (c + 1)) with (c - 2) by flia.
  rewrite (rngl_summation_split_first _ _ (c - 1)); [ | flia Hc11 ].
  rewrite (rngl_summation_shift _ 1); [ | flia Hc11 Hsm1 Hir1 ].
  f_equal.
  replace (c - 1 - 1) with (c - 2) by flia.
  apply rngl_summation_eq_compat.
  intros k Hk.
  now rewrite <- Nat.add_assoc, Nat.add_comm, Nat.add_sub.
} {
  apply Nat.nlt_ge in Hir1.
  rewrite (Nat_div_less_small 1); [ | flia Hir1 Hi ].
  rewrite (Nat_mod_less_small 1); [ | flia Hir1 Hi ].
  cbn - [ iter_seq ].
  rewrite Nat.add_0_r, <- rngl_add_assoc.
  f_equal. {
    rewrite rngl_summation_shift; [ | flia Hsm1 Hi ].
    apply rngl_summation_eq_compat.
    intros k Hk.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  destruct (Nat.eq_dec (mat_ncols M1) 1) as [Hc11| Hc11]. {
    rewrite Hsm1, Hc11; cbn.
    now rewrite rngl_add_0_r, rngl_add_0_l.
  }
  rewrite rngl_summation_shift; [ | flia Hsm1 Hi Hc11 ].
  remember (mat_ncols M1) as c.
  replace (c * 2 - 1 - (c + 1)) with (c - 2) by flia.
  rewrite (rngl_summation_split_first _ _ (c - 1)); [ | flia Hc11 ].
  rewrite (rngl_summation_shift _ 1); [ | flia Hsm1 Hi Hc11 ].
  f_equal.
  replace (c - 1 - 1) with (c - 2) by flia.
  apply rngl_summation_eq_compat.
  intros k Hk.
  now rewrite <- Nat.add_assoc, Nat.add_comm, Nat.add_sub.
}
Qed.

Theorem m_o_mll_2x1_mul_scal_l : ∀ d a MA MB,
 (mat_of_mat_list_list d [[a × MA]%M; [a × MB]%M] =
  a × mat_of_mat_list_list d [[MA]; [MB]])%M.
Proof.
intros.
apply matrix_eq; [ easy | easy | ].
cbn; rewrite Nat.mul_1_r.
intros * Hi Hj.
unfold mat_list_list_el; cbn.
rewrite Nat.div_small; [ | easy ].
rewrite (Nat.mod_small j); [ | easy ].
destruct (lt_dec i (mat_nrows MA)) as [Hia| Hia]. {
  now rewrite Nat.div_small.
} {
  apply Nat.nlt_ge in Hia.
  rewrite (Nat_div_less_small 1); [ easy | flia Hi Hia ].
}
Qed.

Definition base_vector_1 dim :=
  mk_vect (λ i, match i with 0 => 1%F | _ => 0%F end) dim.

Definition A_n_eigenvector_of_sqrt_n n μ V :=
  match n with
  | 0 => base_vector_1 1
  | S n' =>
      (mat_of_mat_list_list 0%F
         [[(mA n' + μ × mI (2 ^ n'))%M]; [mI (2 ^ n')]]
       · V)%V
  end.

Theorem A_n_eigen_formula_for_sqrt_n : ∀ n μ U V,
  V = A_n_eigenvector_of_sqrt_n n μ U
  → (μ * μ)%F = rngl_of_nat n
  → (mA n · V = μ × V)%V.
Proof.
intros * HV Hμ.
destruct n. {
  cbn in Hμ, HV |-*.
  apply vector_eq; [ now subst V | ].
  intros i Hi; cbn in Hi |-*.
  subst V; cbn.
  rewrite rngl_mul_0_l, rngl_add_0_l; [ | easy ].
  destruct i; [ | flia Hi ].
  rewrite rngl_mul_1_r; symmetry; clear Hi.
  specialize (rngl_integral Hro Hin) as H.
  rewrite Hii in H.
  apply H in Hμ.
  now destruct Hμ.
}
cbn - [ Nat.pow ] in HV.
rewrite HV.
rewrite mat_vect_mul_assoc; [ | easy ].
cbn - [ iter_seq Nat.pow ].
specialize (mA_is_square n) as Hasm.
rewrite m_o_mll_2x2_2x1; [ | easy | | | easy | easy ]; cycle 1. {
  apply mA_ncols.
} {
  apply mA_ncols.
}
rewrite mat_mul_add_distr_l; [ | easy ].
rewrite lemma_2_A_n_2_eq_n_I.
rewrite mat_mul_add_distr_l; [ | easy ].
rewrite mat_mul_1_l; [ | easy | easy | easy ].
rewrite mat_mul_1_l; [ | easy | easy | now rewrite mA_ncols ].
rewrite mat_mul_1_l; [ | easy | easy | easy ].
rewrite mat_mul_1_r; [ | easy | easy | now cbn; rewrite mA_nrows ].
rewrite (mat_add_add_swap (mA n)).
rewrite mat_fold_sub.
rewrite mat_add_opp_r with (n0 := 2 ^ n); [ | easy | easy | ]. 2: {
  symmetry; apply mA_nrows.
}
rewrite mA_nrows.
rewrite mat_add_0_l; [ | easy | | easy ]. 2: {
  now apply mat_mul_scal_l_is_square.
}
rewrite mat_add_add_swap; [ | easy ].
remember (mI (2 ^ n)) as x eqn:Hx in |-*.
remember (rngl_of_nat n × x + x)%M as y eqn:Hy.
rewrite Hx in Hy at 1.
replace x with (1%F × x)%M in Hy. 2: {
  apply matrix_eq; [ easy | easy | ].
  intros * Hi Hj.
  apply rngl_mul_1_l.
}
subst x.
rewrite <- mat_mul_scal_l_add_distr_r in Hy; [ | easy ].
replace (rngl_of_nat n + 1)%F with (rngl_of_nat (S n)) in Hy. 2: {
  unfold rngl_of_nat.
  rewrite rngl_summation_split_last; [ | flia ].
  now rewrite rngl_summation_succ_succ.
}
subst y.
rewrite <- Hμ.
rewrite <- mat_mul_scal_l_mul_assoc; [ | easy ].
rewrite mat_mul_mul_scal_l; [ | easy | easy ].
rewrite <- mat_mul_scal_add_distr_l; [ | easy ].
rewrite m_o_mll_2x1_mul_scal_l.
rewrite mat_mul_scal_vect_assoc; [ | easy ].
rewrite mat_mul_1_r; [ | easy | easy | now rewrite mA_nrows ].
rewrite mat_add_comm; [ easy | easy | easy | easy | cbn ].
now rewrite mA_ncols.
Qed.

Theorem A_n_eigenvalue_squared_is_n : ∀ n μ V,
  vect_nrows V = 2 ^ n
  → V ≠ vect_zero (2 ^ n)
  → (mA n · V = μ × V)%V
  → (μ * μ)%F = rngl_of_nat n.
Proof.
intros * Hvr Hvz Hav.
specialize (lemma_2_A_n_2_eq_n_I n) as Ha.
(* μ * μ = rngl_of_nat n *)
apply vect_mul_scal_reg_r with (V0 := V); [ easy | easy | congruence | ].
(* (μ * μ) × V = rngl_of_nat n × V *)
rewrite <- vect_mul_scal_l_mul_assoc; [ | easy ].
(* μ × (μ × V) = rngl_of_nat n × V *)
rewrite <- Hav.
(* μ × (mA n . V) = rngl_of_nat n × V *)
rewrite mat_mul_scal_vect_assoc'; [ | easy | easy ].
(* mA n . (μ × V) = rngl_of_nat n × V *)
rewrite <- Hav.
(* mA n . (mA n . V) = rngl_of_nat n × V *)
rewrite mat_vect_mul_assoc; [ | easy ].
(* (mA n * mA n) . V = rngl_of_nat n × V *)
rewrite Ha.
(* (rngl_of_nat n × mI (2 ^ n)) . V = rngl_of_nat n × V *)
rewrite <- mat_mul_scal_vect_assoc; [ | easy ].
(* rngl_of_nat n × (mI (2 ^ n) . V) = rngl_of_nat n × V *)
rewrite vect_mul_1_l; easy.
Qed.

Theorem μ_is_ev_of_An_iff_μ2_eq_n : ∀ n μ,
  (∃ V, vect_nrows V = 2 ^ n ∧ V ≠ vect_zero (2 ^ n) ∧
   mA n · V = μ × V)%V ↔
  (μ * μ = rngl_of_nat n)%F.
Proof.
intros.
split. {
  intros HV.
  destruct HV as (V & Hvr & Hvz & Hv).
  now apply (@A_n_eigenvalue_squared_is_n _ _ V).
} {
  intros Hμ.
  remember (A_n_eigenvector_of_sqrt_n n μ (base_vector_1 42)) as V eqn:Hv.
  exists V.
  split. {
    rewrite Hv; cbn.
    unfold A_n_eigenvector_of_sqrt_n; cbn.
    destruct n; [ easy | cbn ].
    rewrite mA_nrows.
    now rewrite Nat.mul_comm.
  }
  split. {
    rewrite Hv; cbn.
    unfold A_n_eigenvector_of_sqrt_n; cbn.
    destruct n. {
      intros H.
      injection H; clear H; intros H.
      set (f := λ i, match i with 0 => 1%F | S _ => 0%F end) in H.
      set (g := λ _, 0%F) in H.
      assert (H1 : ∀ i, f i = g i) by now rewrite H.
      specialize (H1 0).
      unfold f, g in H1; cbn in H1.
      now apply rngl_1_neq_0 in H1.
    }
    intros H.
    injection H; clear H; intros H1 H2.
    set
      (f :=
       λ i,
       (Σ (j = 0, mat_ncols (mA n) * 1 - 1),
        mat_list_list_el 0 [[(mA n + μ × mI (2 ^ n))%M]; [mI (2 ^ n)]] i j *
        match j with 0 => 1 | S _ => 0 end)%F) in H2.
    set (g := λ _, 0%F) in H2.
    assert (H3 : ∀ i, f i = g i) by now rewrite H2.
    specialize (H3 0).
    unfold f, g in H3.
    cbn - [ iter_seq ] in H3.
    rewrite Nat.mul_1_r in H3.
    rewrite rngl_summation_split_first in H3; [ | easy | flia ].
    rewrite rngl_mul_1_r in H3.
    unfold mat_list_list_el in H3 at 1.
    cbn - [ iter_seq ] in H3.
    rewrite Nat.div_0_l in H3. 2: {
      now rewrite mA_ncols; apply Nat.pow_nonzero.
    }
    rewrite Nat.div_0_l in H3. 2: {
      now rewrite mA_nrows; apply Nat.pow_nonzero.
    }
    rewrite Nat.mod_0_l in H3. 2: {
      now rewrite mA_nrows; apply Nat.pow_nonzero.
    }
    rewrite Nat.mod_0_l in H3. 2: {
      now rewrite mA_ncols; apply Nat.pow_nonzero.
    }
    cbn - [ iter_seq ] in H3.
    rewrite rngl_mul_1_r in H3.
    replace (mat_el (mA n) 0 0) with 0%F in H3. 2: {
      clear.
      induction n; [ easy | cbn ].
      unfold mat_list_list_el; cbn.
      rewrite Nat.div_0_l. 2: {
        now rewrite mA_ncols; apply Nat.pow_nonzero.
      }
      rewrite Nat.div_0_l. 2: {
        now rewrite mA_nrows; apply Nat.pow_nonzero.
      }
      rewrite Nat.mod_0_l. 2: {
        now rewrite mA_nrows; apply Nat.pow_nonzero.
      }
      rewrite Nat.mod_0_l. 2: {
        now rewrite mA_ncols; apply Nat.pow_nonzero.
      }
      apply IHn.
    }
    rewrite rngl_add_0_l in H3.
    rewrite all_0_rngl_summation_0 in H3; [ | easy | ]. 2: {
      intros i Hi.
      unfold mat_list_list_el; cbn.
      assert (Hica : i < mat_ncols (mA n)) by flia Hi.
      assert (Hzra : 0 < mat_nrows (mA n)). {
        rewrite mA_nrows.
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
      }
      rewrite Nat.div_small; [ | easy ].
      rewrite Nat.div_small; [ | easy ].
      rewrite Nat.mod_small; [ | easy ].
      rewrite Nat.mod_small; [ | easy ].
      destruct i; [ easy | ].
      now apply rngl_mul_0_r.
    }
    rewrite rngl_add_0_r in H3.
    rewrite H3 in Hμ.
    rewrite rngl_mul_0_l in Hμ.
    unfold rngl_of_nat in Hμ.
...
  }
  now specialize (A_n_eigen_formula_for_sqrt_n _ _ _ Hv Hμ) as H1.
...

End in_ring_like.

Inspect 2.
