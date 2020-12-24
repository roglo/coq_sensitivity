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
Import EqNotations.

Require Import Misc RingLike Matrix.
Require Import RLsummation.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* *)

Definition mat_of_scalar (c : T) := mk_mat 1 1 (λ i j, c).

(* conversion matrix of matrices (actually list of list of matrices)
   into simple matrix *)

(*
Definition upper_left_mat_in_list_list {m n} mll : matrix m n T :=
  hd (mZ m n) (hd [] mll).
*)

Definition mat_list_list_el {m n} mll i j :=
  mat_el (nth (j / n) (nth (i / m) mll []) (mZ m n)) (i mod m) (j mod n).

Definition mat_of_mat_list_list {m n} (mll : list (list (matrix m n T))) :
    matrix _ _ T :=
  mk_mat (m * length mll) (n * length (hd [] mll)) (mat_list_list_el mll).

(* sequence "An" *)

Theorem two_pow_n_mul_two : ∀ n, 2 ^ n * 2 = 2 ^ S n.
Proof.
intros.
now rewrite Nat.mul_comm.
Qed.

(* the magic incancation
     rew [λ m, matrix m m T] two_pow_n_mul_two n' in
   in mA definition below, transforms the type of the expression
     mat_of_mat_list_list
       [[mA n'; mI (2 ^ n')];
        [mI (2 ^ n'); (- mA n')%M]]
   following it, from
     matrix (2 ^ n' * 2) (2 ^ n' * 2) T
   into the equivalent
     matrix (2 ^ S n') (2 ^ S n') T
 *)

Fixpoint mA (n : nat) : matrix (2 ^ n) (2 ^ n) T :=
  match n with
  | 0 => mZ 1 1
  | S n' =>
      rew [λ m, matrix m m T] two_pow_n_mul_two n' in
      mat_of_mat_list_list
        [[mA n'; mI (2 ^ n')];
         [mI (2 ^ n'); (- mA n')%M]]
  end.

(* *)

(*
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
*)

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I :
  rngl_has_opp = true →
  ∀ n, (mA n * mA n)%M = (rngl_of_nat n × mI (2 ^ n))%M.
Proof.
intros Hro *.
apply matrix_eq.
cbn - [ iter_seq ].
intros i k Hi Hk.
revert i k Hi Hk.
induction n; intros. {
  cbn.
  do 2 rewrite rngl_mul_0_l.
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
rewrite rngl_add_comm.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  destruct (two_pow_n_mul_two n); cbn.
  rewrite two_pow_n_mul_two in Hj.
  assert (H : 1 * 2 ^ n ≤ j < (1 + 1) * 2 ^ n). {
    rewrite Nat.mul_1_l.
    split; [ easy | ].
    change (j < 2 ^ S n).
    enough (H : 0 < 2 ^ S n) by flia H Hj.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  unfold mat_list_list_el.
  rewrite (Nat_div_less_small 1); [ | easy ].
  rewrite (@Nat_mod_less_small 1 j); [ clear H | easy ].
  now rewrite Nat.mul_1_l.
}
rewrite rngl_add_comm.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  now destruct (two_pow_n_mul_two n); cbn.
}
unfold mat_list_list_el.
cbn - [ iter_seq Nat.pow ].
destruct (lt_dec i (2 ^ n)) as [Hi2n| Hi2n]. {
  rewrite (Nat.div_small i); [ | easy ].
  rewrite (Nat.mod_small i); [ | easy ].
  cbn - [ iter_seq Nat.pow ].
  destruct (lt_dec k (2 ^ n)) as [Hk2n| Hk2n]. {
    rewrite (Nat.div_small k); [ | easy ].
    rewrite (Nat.mod_small k); [ | easy ].
    cbn - [ iter_seq Nat.pow ].
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite Nat.div_small; [ | flia Hi2n Hj ].
      now rewrite Nat.mod_small; [ | flia Hi2n Hj ].
    }
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
      clear Hi Hk Hi2n Hk2n IHn.
      induction n; cbn. {
        now rewrite rngl_add_0_l, rngl_add_0_r.
      }
      rewrite IHn, rngl_add_assoc; f_equal.
      apply IHn.
    } {
      do 2 rewrite rngl_mul_0_r.
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
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite Nat.div_small; [ | flia Hi2n Hj ].
      rewrite Nat.mod_small; [ | flia Hi2n Hj ].
      now cbn.
    }
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
      rewrite rngl_mul_0_l.
      now apply rngl_opp_0.
    }
    rewrite rngl_add_0_l.
    rewrite rngl_add_assoc.
    rewrite (@fold_rngl_sub _ _ Hro).
    rewrite rngl_add_opp_r.
    rewrite rngl_add_0_l.
    destruct (Nat.eq_dec i k) as [Hik| Hik]; [ flia Hi2n Hk2n Hik | ].
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i j) as [Hij| Hij]; [ flia Hj Hij | ].
      rewrite rngl_mul_0_l.
      now apply rngl_opp_0.
    }
    symmetry.
    apply rngl_mul_0_r.
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
(**)
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    assert (H : 0 < 2 ^ n). {
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite Nat.div_small; [ | flia Hj H ].
    rewrite Nat.mod_small; [ | flia Hj H ].
    easy.
  }
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
    rewrite (@fold_rngl_sub _ _ Hro).
    rewrite rngl_add_opp_r.
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
      now do 2 rewrite rngl_mul_1_r.
    } {
      destruct (Nat.eq_dec (i - 2 ^ n) (k - 2 ^ n)) as [Hi2k| Hi2k]. {
        flia Hik Hi2k Hi2n Hk2n.
      }
      rewrite rngl_add_0_l.
      rewrite rngl_mul_0_r.
      now rewrite rngl_mul_0_r.
    }
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
     We can take V, for example, as (1, 0, 0, 0....0), etc.
   This way, we have to prove that this pair eigen(value,vector)
   works *)

(* perhaps unnecessary theorem... *)
Theorem m_o_mll_2x2_2x1 : ∀ n (M1 M2 M3 M4 M5 M6 : matrix n n T),
  (mat_of_mat_list_list [[M1; M2]; [M3; M4]] *
   mat_of_mat_list_list [[M5]; [M6]])%M =
   mat_of_mat_list_list [[M1 * M5 + M2 * M6]; [M3 * M5 + M4 * M6]]%M.
Proof.
intros.
apply matrix_eq.
cbn - [ iter_seq ].
intros * Hi Hj.
rewrite Nat.mul_1_r in Hj.
unfold mat_mul, mat_add.
cbn - [ iter_seq ].
unfold mat_list_list_el.
cbn - [ iter_seq ].
rewrite (Nat.div_small j); [ | flia Hj ].
rewrite (Nat.mod_small j); [ | flia Hj ].
rewrite (rngl_summation_split _ n); [ | flia Hi ].
rewrite rngl_summation_split_last; [ | flia ].
assert (H : n ≠ 0) by flia Hj.
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
erewrite (rngl_summation_eq_compat _ _ _ (n + 1)). 2: {
  intros k Hk.
  rewrite (Nat_div_less_small 1); [ | flia Hk ].
  rewrite (@Nat_mod_less_small 1 k); [ | flia Hk ].
  rewrite Nat.mul_1_l.
  easy.
}
cbn - [ iter_seq ].
destruct (lt_dec i n) as [Hir1| Hir1]. {
  rewrite Nat.div_small; [ | easy ].
  rewrite Nat.mod_small; [ | easy ].
  cbn - [ iter_seq ].
  rewrite <- rngl_add_assoc.
  f_equal. {
    rewrite rngl_summation_shift; [ | flia Hj ].
    apply rngl_summation_eq_compat.
    intros k Hk.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  destruct (Nat.eq_dec n 1) as [Hc11| Hc11]. {
    subst n; cbn.
    now rewrite rngl_add_0_r, rngl_add_0_l.
  }
  rewrite rngl_summation_shift; [ | flia Hc11 Hj ].
  replace (n * 2 - 1 - (n + 1)) with (n - 2) by flia.
  rewrite (rngl_summation_split_first _ _ (n - 1)); [ | flia Hc11 ].
  rewrite (rngl_summation_shift _ 1); [ | flia Hc11 Hir1 ].
  f_equal.
  replace (n - 1 - 1) with (n - 2) by flia.
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
    rewrite rngl_summation_shift; [ | flia Hi ].
    apply rngl_summation_eq_compat.
    intros k Hk.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  destruct (Nat.eq_dec n 1) as [Hc11| Hc11]. {
    subst n; cbn.
    now rewrite rngl_add_0_r, rngl_add_0_l.
  }
  rewrite rngl_summation_shift; [ | flia Hi Hc11 ].
  replace (n * 2 - 1 - (n + 1)) with (n - 2) by flia.
  rewrite (rngl_summation_split_first _ _ (n - 1)); [ | flia Hc11 ].
  rewrite (rngl_summation_shift _ 1); [ | flia Hi Hc11 ].
  f_equal.
  replace (n - 1 - 1) with (n - 2) by flia.
  apply rngl_summation_eq_compat.
  intros k Hk.
  now rewrite <- Nat.add_assoc, Nat.add_comm, Nat.add_sub.
}
Qed.

(*
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
*)

Definition mat_of_list_list_1_row_2_col {n} (A B : matrix (2 ^ n) (2 ^ n) T) :
    matrix (2 ^ S n) (2 ^ n) T :=
  rew [λ m, matrix (2 ^ S n) m T] Nat.mul_1_r (2 ^ n) in
  rew [λ m, matrix m (2 ^ n * 1) T] two_pow_n_mul_two n in
  mat_of_mat_list_list [[A]; [B]].

Definition A_Sn_eigenvector_of_sqrt_Sn n μ (V : vector (2 ^ n) T) :
    vector (2 ^ S n) T :=
  (mat_of_list_list_1_row_2_col (mA n + μ × mI (2 ^ n))%M (mI (2 ^ n)) • V)%V.

(*
Definition pre_matrix_of_A_Sn_eigenvector_of_sqr_Sn n μ :
    matrix (2 ^ S n) (2 ^ n) T :=
  rew [λ m, matrix (2 ^ S n) m T] Nat.mul_1_r (2 ^ n) in
  rew [λ m, matrix m (2 ^ n * 1) T] two_pow_n_mul_two n in
  mat_of_mat_list_list [[(mA n + μ × mI (2 ^ n))%M]; [mI (2 ^ n)]].

Definition A_Sn_eigenvector_of_sqrt_Sn n μ (V : vector (2 ^ n) T) :
    vector (2 ^ S n) T :=
  (pre_matrix_of_A_Sn_eigenvector_of_sqr_Sn n μ • V)%V.
*)

(*
Definition base_vector_1 dim :=
  mk_vect dim (λ i, match i with 0 => 1%F | _ => 0%F end).

Definition A_n_eigenvector_of_sqrt_n n μ V :=
  match n with
  | 0 => base_vector_1 1
  | S n' =>
       mat_of_mat_list_list
         [[(mA n' + μ × mI (2 ^ n'))%M]; [mI (2 ^ n')]]
       • V)%V
  end.
*)

Theorem mA_diag_zero :
  rngl_has_opp = true →
  ∀ n i, i < 2 ^ n → mat_el (mA n) i i = 0%F.
Proof.
intros Hop * Hi2n.
revert i Hi2n.
induction n; intros; [ easy | cbn ].
(* destructions does not work this way (typing error):
destruct (two_pow_n_mul_two n).
*)
(* but works that way: *)
refine
  (rew dependent
     [fun _ Q => mat_el (rew [λ m : nat, matrix m m T] Q in _) i i = 0%F]
     (two_pow_n_mul_two n)
   in _).
cbn.
unfold mat_list_list_el.
destruct (lt_dec i (2 ^ n)) as [Hin| Hin]. {
  rewrite (Nat.div_small i); [ | easy ].
  rewrite (Nat.mod_small i); [ | easy ].
  now apply IHn.
} {
  apply Nat.nlt_ge in Hin.
  rewrite (Nat_div_less_small 1); [ | now rewrite Nat.mul_1_l ].
  rewrite (Nat_mod_less_small 1); [ | now rewrite Nat.mul_1_l ].
  cbn; rewrite Nat.add_0_r.
  rewrite <- rngl_opp_involutive; [ | easy ].
  rewrite rngl_opp_0; [ f_equal | easy ].
  apply IHn.
  cbn in Hi2n.
  flia Hi2n Hin.
}
Qed.

Theorem An_eigen_equation_for_sqrt_n :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_dec_eq = true →
  ∀ n μ, (μ * μ)%F = rngl_of_nat n →
  match n with
  | 0 => ∀ V, (mA 0 • V = μ × V)%V
  | S n' =>
      ∀ U V,
      V = A_Sn_eigenvector_of_sqrt_Sn n' μ U
      → (mA (S n') • V = μ × V)%V
  end.
Proof.
(* restart from "master" version" *)
...
intros Hic Hro Hin Hde * Hμ.
destruct n. {
  intros V.
  cbn in Hμ, V |-*.
  apply vector_eq.
  intros i Hi; cbn.
  apply Nat.lt_1_r in Hi; subst i; cbn.
  rewrite rngl_mul_0_l, rngl_add_0_l.
  specialize rngl_integral as H.
  rewrite Hin in H; cbn in H.
  rewrite Hde in H.
  rewrite Bool.orb_true_r in H.
  apply (H eq_refl) in Hμ.
  symmetry.
  destruct Hμ; subst μ; apply rngl_mul_0_l.
}
intros U V HV.
(**)
unfold A_Sn_eigenvector_of_sqrt_Sn in HV.
unfold mat_of_list_list_1_row_2_col in HV.
subst V.
rewrite mat_vect_mul_assoc.
cbn - [ iter_seq Nat.pow ].
destruct (two_pow_n_mul_two n).
cbn - [ iter_seq Nat.pow ].
remember (mA n) as M1 eqn:HM1.
remember (mI (2 ^ n)) as M2 eqn:HM2.
remember (M1 + μ × M2)%M as M5 eqn:HM5.
move M2 before M1; move M5 before M2.
apply vector_eq.
intros i Hi.
cbn - [ iter_seq Nat.pow ].
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros j Hj.
move j before i.
destruct (Nat.mul_1_r (2 ^ n)).
cbn - [ iter_seq Nat.pow ].
rewrite Nat.mul_1_r at 1.
unfold mat_list_list_el.
assert (Hz : 0 < 2 ^ n). {
  apply Nat.neq_0_lt_0.
  now apply Nat.pow_nonzero.
}
rewrite (Nat.div_small j); [ | flia Hj Hz ].
rewrite (Nat.mod_small j); [ | flia Hj Hz ].
destruct (lt_dec i (2 ^ n)) as [Hi2n| Hi2n]. {
  rewrite (Nat.div_small i); [ | flia Hi2n ].
  rewrite (Nat.mod_small i); [ | flia Hi2n ].
  remember (nth 0 _ _) as x; cbn in Heqx; subst x.
  remember (nth 0 _ _) as x; cbn in Heqx; subst x.
  rewrite (rngl_summation_split _ (2 ^ n)); [ | flia ].
  rewrite rngl_summation_split_last; [ | flia ].
  rewrite rngl_summation_shift; [ | flia Hz ].
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite (Nat.div_small k); [ | flia Hk Hz ].
    rewrite (Nat.mod_small k); [ | flia Hk Hz ].
    cbn - [ Nat.pow ].
    rewrite HM5 at 1.
    cbn - [ Nat.pow ].
    rewrite rngl_mul_add_distr_l.
    easy.
  }
  cbn - [ iter_seq Nat.pow nth ].
  rewrite rngl_summation_add_distr; [ | easy ].
  specialize (lemma_2_A_n_2_eq_n_I Hro n) as H1.
  rewrite <- HM1 in H1.
  assert
    (H2 : ∀ i j,
     mat_el (M1 * M1) i j = mat_el (rngl_of_nat n × mI (2 ^ n))%M i j). {
    intros.
    now rewrite H1.
  }
  specialize (H2 i j).
  cbn - [ iter_seq Nat.pow rngl_of_nat ] in H2.
  rewrite H2; clear H1 H2.
  rewrite Nat.div_same; [ | now apply Nat.pow_nonzero ].
  rewrite Nat.mod_same; [ | now apply Nat.pow_nonzero ].
  remember (nth 1 _ _) as x eqn:Hx.
  cbn in Hx; subst x.
  remember (nth 0 _ _) as x eqn:Hx.
  cbn in Hx; subst x.
  rewrite (rngl_summation_split _ j); [ | flia Hj ].
  rewrite rngl_summation_split_last; [ | easy ].
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    subst M2; cbn.
    destruct (Nat.eq_dec (k - 1) j) as [H| H]; [ flia Hk H | ].
    now do 2 rewrite rngl_mul_0_r.
  }
  rewrite rngl_add_0_l.
  replace (mat_el M2 j j) with 1%F. 2: {
    subst M2; cbn.
    now destruct (Nat.eq_dec j j).
  }
  rewrite rngl_mul_1_r.
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    subst M2; cbn.
    destruct (Nat.eq_dec k j) as [H| H]; [ flia Hk H | ].
    now do 2 rewrite rngl_mul_0_r.
  }
  rewrite rngl_add_0_r.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite (Nat_div_less_small 1); [ | flia Hk ].
    rewrite (Nat_mod_less_small 1); [ | flia Hk ].
    cbn - [ Nat.pow ].
    now rewrite Nat.add_0_r.
  }
  cbn - [ iter_seq Nat.pow rngl_of_nat ].
  destruct (Nat.eq_dec i j) as [Hij| Hij]. {
    subst j.
    rewrite rngl_mul_1_r.
    rewrite HM1 at 1.
    rewrite mA_diag_zero; [ | easy | easy ].
    rewrite rngl_mul_0_l, rngl_add_0_r.
    rewrite HM5.
    cbn - [ iter_seq Nat.pow rngl_of_nat ].
    replace (mat_el M2 i i) with 1%F. 2: {
      rewrite HM2; cbn.
      now destruct (Nat.eq_dec i i).
    }
    rewrite rngl_mul_1_r.
    replace (mat_el M1 i i) with 0%F. 2: {
      rewrite HM1; symmetry.
      now apply mA_diag_zero.
    }
    rewrite rngl_add_0_l.
    rewrite rngl_mul_assoc.
    rewrite Hμ.
    destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
      subst i.
      rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
        intros k Hk.
        rewrite HM2; cbn - [ Nat.pow Nat.eq_dec ].
        destruct (Nat.eq_dec 0 (k - 2 ^ n)) as [H| H]; [ flia H Hk | ].
        apply rngl_mul_0_l.
      }
      rewrite rngl_add_0_r.
...
  ============================
  ((rngl_of_nat (S n) + mat_el M2 0 0 * mat_el M2 0 0) * vect_el U 0)%F =
  (rngl_of_nat (S (S n)) * vect_el U 0)%F
...
    rewrite (rngl_summation_split _ (i + 2 ^ S n)); [ | flia Hi2n ].
    destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
      subst i.
...
    rewrite rngl_summation_split_last; [ | flia Hi2n Hiz ].
...
    replace (mat_el M1 i i) with 0%F. 2: {
      subst M1; symmetry.
rewrite mA_diag_0.
      destruct (two_pow_n_mul_two n).
...
  rewrite rngl_summation_shift. 2: {
    apply Nat.le_add_le_sub_r.
    rewrite Nat.mul_comm.
    clear.
    remember (2 ^ S n) as x; cbn; subst x.
    rewrite <- Nat.add_assoc.
    apply Nat.add_le_mono_l.
    rewrite Nat.add_0_r.
    remember (1 + 1) as x; cbn; subst x.
    rewrite Nat.add_0_r.
    now apply Nat.add_le_mono; apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite Nat.sub_add_distr.
  rewrite (Nat_sub_sub_swap _ 1).
  replace (2 ^ S n * 2 - 2 ^ S n) with (2 ^ S n).
...
  unfold mat_mul in H1.
...
unfold mat_of_mat_list_list.
unfold mat_list_list_el.
destruct (Nat.mul_1_r (2 ^ S n)).
Check (mat_of_mat_list_list [[M5]; [M2]]).
Check
  (rew [λ m : nat, matrix (2 ^ S n * 2) m T] Nat.mul_1_r (2 ^ S n) in
   mat_of_mat_list_list [[M5]; [M2]]).
destruct (Nat.mul_1_r (2 ^ S n)).
...
specialize m_o_mll_2x2_2x1.
...
destruct (Nat.mul_1_r (2 ^ sn)).
cbn - [ iter_seq Nat.pow ].
...
rewrite HV.
rewrite mat_vect_mul_assoc.
cbn - [ iter_seq Nat.pow ].
...
remember (S n) as sn; cbn - [ Nat.pow ]; subst sn.
rewrite HV.
unfold A_Sn_eigenvector_of_sqrt_Sn.
rewrite mat_vect_mul_assoc.
rewrite mat_mul_scal_vect_assoc.
unfold mat_of_list_list_1_row_2_col.
destruct (two_pow_n_mul_two (S n)).
remember (S n) as sn; cbn - [ mat_of_list_list Nat.pow ] in HV |-*; subst sn.
...
unfold A_Sn_eigenvector_of_sqrt_Sn in HV.
unfold mat_of_list_list_1_row_2_col in HV.
destruct (two_pow_n_mul_two (S n)).
...
(**)
apply vector_eq.
intros i Hi.
cbn - [ mat_of_mat_list_list Nat.pow iter_seq ].
apply rngl_summation_eq_compat.
intros j Hj.
f_equal.
...
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.

  rewrite rngl_mul_assoc.

rewrite <- rngl_mul_summation_distr_r.
...
(*
destruct (vect_opt_eq_dec Hde _ U (vect_zero _)) as [Huz| Huz]. {
  rewrite Huz.
  rewrite mat_vect_mul_0_r; [ | easy ].
  now rewrite mat_vect_mul_0_r.
}
*)
Theorem vect_move_0_r :
  ∀ n (VA VB : vector n T), (VA - VB = vect_zero _)%V → VA = VB.
...
apply vect_move_0_r.
unfold vect_sub.
Search (- (_ • _))%V.
Theorem mat_vect_mul_opp_l : ∀ m n (M : matrix m n T) V, (- M • V = - (M • V))%V.
...
rewrite <- mat_vect_mul_opp_l.
Search (_ • _ + _ • _)%V.
Theorem mat_vect_mul_distr_r : ∀ m n (MA MB : matrix m n T) V, ((MA + MB) • V = MA • V + MB • V)%V.
...
rewrite <- mat_vect_mul_distr_r.
remember (mA (S n)) as M1 eqn:HM1.
remember (mI (2 ^ S n)) as M2 eqn:HM2.
remember (M1 + μ × M2)%M as M5 eqn:HM5.
move M2 before M1; move M5 before M2.
remember
             (@eq_rect nat (Init.Nat.mul (Nat.pow (S (S O)) (S n)) (S O))
                (fun m : nat => matrix (Init.Nat.mul (Nat.pow (S (S O)) (S n)) (S (S O))) m T)
                (@mat_of_mat_list_list (Nat.pow (S (S O)) (S n)) (Nat.pow (S (S O)) (S n))
                   (@cons (list (matrix (Nat.pow (S (S O)) (S n)) (Nat.pow (S (S O)) (S n)) T))
                      (@cons (matrix (Nat.pow (S (S O)) (S n)) (Nat.pow (S (S O)) (S n)) T) M5
                         (@nil (matrix (Nat.pow (S (S O)) (S n)) (Nat.pow (S (S O)) (S n)) T)))
                      (@cons (list (matrix (Nat.pow (S (S O)) (S n)) (Nat.pow (S (S O)) (S n)) T))
                         (@cons (matrix (Nat.pow (S (S O)) (S n)) (Nat.pow (S (S O)) (S n)) T) M2
                            (@nil (matrix (Nat.pow (S (S O)) (S n)) (Nat.pow (S (S O)) (S n)) T)))
                         (@nil (list (matrix (Nat.pow (S (S O)) (S n)) (Nat.pow (S (S O)) (S n)) T))))))
                (Nat.pow (S (S O)) (S n)) (Nat.mul_1_r (Nat.pow (S (S O)) (S n)))) as x eqn:Hx.
remember (S n) as sn.
cbn in x; subst sn.
Search (mat_of_mat_list_list).
...
rewrite m_o_mll_2x2_2x1.
destruct (Nat.mul_1_r (2 ^ S n)).

remember (rew [λ m : nat, matrix (2 ^ S n * 2) m T] Nat.mul_1_r (2 ^ S n) in mat_of_mat_list_list [[M5]; [M2]])%M as x eqn:Hx.
cbn in x.
...
unfold mat_of_list_list_1_row_2_col.
destruct (two_pow_n_mul_two (S n)).
...
remember (mA (S n)) as M1 eqn:HM1.
remember (mI (2 ^ S n)) as M2 eqn:HM2.
remember (M1 + μ × M2)%M as M5 eqn:HM5.
move M2 before M1; move M5 before M2.

...
Search (_ • (_ • _))%V.

rewrite <- mat_vect_mul_distr_r.
rewrite mat_
...
destruct (two_pow_n_mul_two (S n)).
...
(*
f_equal.
*)
unfold mat_of_list_list_1_row_2_col.
destruct (two_pow_n_mul_two (S n)).
(**)
remember (S n) as sn; cbn - [ mat_of_list_list Nat.pow ]; subst sn.
(*
destruct (Nat.mul_1_r (2 ^ S n)).
*)
remember (mA (S n)) as M1 eqn:HM1.
remember (mI (2 ^ S n)) as M2 eqn:HM2.
remember (M1 + μ × M2)%M as M5 eqn:HM5.
move M2 before M1; move M5 before M2.
(*
clear U V Huz HV.
*)
specialize (m_o_mll_2x2_2x1 M1 M2 M2 (- M1)%M M5 M2) as H1.
...
destruct (Nat.mul_1_r (2 ^ S n)).
...
cbn in H1 |-*; rewrite H1; clear H1.
rewrite HM2.
do 2 rewrite mat_mul_1_r.
rewrite mat_mul_1_l.
rewrite <- HM2.
rewrite HM5.
rewrite (mat_add_comm M1).
rewrite <- mat_add_assoc; [ | easy ].
rewrite fold_mat_sub.
rewrite mat_add_opp_r; [ | easy ].
rewrite (mat_add_comm (μ × M2)%M (mZ _ _)).
rewrite mat_add_0_l; [ | easy ].
rewrite mat_mul_add_distr_l; [ | easy ].
rewrite HM1.
specialize (lemma_2_A_n_2_eq_n_I Hro (S n)) as H1.
remember (mI (2 ^ S n)) as x.
cbn - [ mat_mul mA rngl_of_nat ] in H1 |-*.
rewrite H1; clear H1; subst x.
rewrite <- HM1.
rewrite mat_mul_mul_scal_l; [ | easy ].
rewrite HM2.
rewrite mat_mul_1_r.
rewrite <- HM2.
apply matrix_eq.
intros * Hi Hj.
rewrite Nat.mul_1_r in Hj.
cbn - [ rngl_of_nat ].
unfold mat_list_list_el.
set (tsn := 2 ^ n + (2 ^ n + 0)) in Hi, Hj |-*.
rewrite (Nat.div_small j); [ | easy ].
rewrite (Nat.mod_small j); [ | easy ].
cbn - [ rngl_of_nat ].
destruct (lt_dec i tsn) as [Hit| Hit]. {
  rewrite (Nat.div_small i); [ | easy ].
  rewrite (Nat.mod_small i); [ | easy ].
  cbn - [ rngl_of_nat ].
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_assoc.
  rewrite Hμ.
  rewrite rngl_add_comm.
  rewrite rngl_add_assoc.
  rewrite rngl_add_comm.
  f_equal.
(* ok if i≠j, but not ok for i=j *)
...
destruct (two_pow_n_mul_two n).
cbn - [ mat_of_mat_list_list Nat.pow ].
remember (mat_of_mat_list_list [[mA n; mI (2 ^ n)]; [mI (2 ^ n); (- mA n)%M]]) as M1 eqn:HM1.
remember (mI (2 ^ n * 2)) as M2 eqn:HM2.
move M2 before M1.
cbn in M1.
remember (M1 + μ × M2)%M as M5 eqn:HM5.
move M5 before M2.
specialize (m_o_mll_2x2_2x1 M1 M2 M2 (- M1)%M M5 M2) as H1.
cbn in H1; rewrite H1; clear H1.
(*
remember (mat_of_mat_list_list [[M5]; [M2]]) as M52 eqn:HM52.
cbn in M52.
..
Theorem glop : ∀ MA MB,
  mat_of_mat_list_list [[MA]; [MB]] = (MA * MB)%M.
...
*)
apply matrix_eq; cbn.
rewrite Nat.mul_1_r.
intros * Hi Hj.
unfold mat_list_list_el.
rewrite (Nat.div_small j); [ | easy ].
rewrite (Nat.mod_small j); [ | easy ].
cbn.
destruct (lt_dec i (2 ^ n * 2)) as [Hi2n| Hi2n]. {
  rewrite Nat.div_small; [ | easy ].
  rewrite Nat.mod_small; [ | easy ].
  cbn - [ iter_seq ].
  rewrite rngl_add_comm.
  rewrite (rngl_summation_split _ j); [ | flia Hj ].
  rewrite rngl_summation_split_last; [ | flia ].
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec (k - 1) j) as [H| H]; [ flia Hk H | ].
    apply rngl_mul_0_r.
  }
  rewrite rngl_add_0_l.
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros k Hk.
    rewrite HM2; cbn.
    destruct (Nat.eq_dec k j) as [H| H]; [ flia Hk H | ].
    apply rngl_mul_0_r.
  }
  rewrite rngl_add_0_r.
  rewrite HM2.
  cbn - [ iter_seq ].
  destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
  rewrite rngl_mul_1_r.
  rewrite HM5 at 1.
  cbn - [ iter_seq ].
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_assoc.
  rewrite Hμ.
  rewrite HM5.
  remember (S n) as sn; cbn - [ iter_seq ]; subst sn.
Check lemma_2_A_n_2_eq_n_I.
...

unfold mat_of_mat_list_list; cbn.
unfold mat_list_list_el.
cbn.
...
subst M1 M2 M5.
rewrite mat_mul_add_distr_l; [ | easy ].
Check lemma_2_A_n_2_eq_n_I.
...
apply matrix_eq; cbn.
rewrite Nat.mul_1_r.
intros * Hi Hj.
unfold mat_list_list_el.
unfold mat_of_mat_list_list.
cbn.
rewrite lemma_2_A_n_2_eq_n_I; [ | easy ].
...
rewrite m_o_mll_2x2_2x1.
rewrite m_o_mll_2x2_2x1; [ | easy | | | easy | easy ]; cycle 1. {
...
destruct (two_pow_n_mul_two n).
destruct (Nat.mul_1_r (2 ^ S n)).
...
specialize (mA_is_square n) as Hasm.
rewrite m_o_mll_2x2_2x1; [ | easy | | | easy | easy ]; cycle 1. {
  apply mA_ncols.
} {
  apply mA_ncols.
}
rewrite mat_mul_add_distr_l; [ | easy ].
rewrite lemma_2_A_n_2_eq_n_I; [ | easy ].
rewrite mat_mul_add_distr_l; [ | easy ].
rewrite mat_mul_1_l; [ | easy | easy ].
rewrite mat_mul_1_l; [ | easy | now rewrite mA_ncols ].
rewrite mat_mul_1_l; [ | easy | easy ].
rewrite mat_mul_1_r; [ | easy | now cbn; rewrite mA_nrows ].
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
  clear HV Hμ Hasm Hy; cbn.
  induction n; cbn. {
    now rewrite rngl_add_0_l, rngl_add_0_r.
  }
  rewrite IHn, rngl_add_assoc; f_equal.
  apply IHn.
}
subst y.
rewrite <- Hμ.
rewrite <- mat_mul_scal_l_mul_assoc; [ | easy ].
rewrite mat_mul_mul_scal_l; [ | easy ].
rewrite <- mat_mul_scal_add_distr_l; [ | easy ].
rewrite m_o_mll_2x1_mul_scal_l.
rewrite mat_mul_scal_vect_assoc.
rewrite mat_mul_1_r; [ | easy | now rewrite mA_nrows ].
rewrite mat_add_comm; [ easy | easy | easy | easy | cbn ].
now rewrite mA_ncols.
Qed.

Theorem A_n_eigenvalue_squared_is_n :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_dec_eq = true →
  rngl_has_inv = true →
  ∀ n μ V,
  vect_nrows V = 2 ^ n
  → V ≠ vect_zero (2 ^ n)
  → (mA n • V = μ × V)%V
  → (μ * μ)%F = rngl_of_nat n.
Proof.
intros Hic Hro Hed Hin * Hvr Hvz Hav.
specialize (lemma_2_A_n_2_eq_n_I Hro n) as Ha.
(* μ * μ = rngl_of_nat n *)
apply vect_mul_scal_reg_r with (V0 := V); [ easy | now left | congruence | ].
(* (μ * μ) × V = rngl_of_nat n × V *)
rewrite <- vect_mul_scal_l_mul_assoc; [ | easy ].
(* μ × (μ × V) = rngl_of_nat n × V *)
rewrite <- Hav.
(* μ × (mA n . V) = rngl_of_nat n × V *)
rewrite mat_mul_scal_vect_comm; [ | easy ].
(* mA n . (μ × V) = rngl_of_nat n × V *)
rewrite <- Hav.
(* mA n . (mA n . V) = rngl_of_nat n × V *)
rewrite mat_vect_mul_assoc.
(* (mA n * mA n) . V = rngl_of_nat n × V *)
rewrite Ha.
(* (rngl_of_nat n × mI (2 ^ n)) . V = rngl_of_nat n × V *)
rewrite <- mat_mul_scal_vect_assoc.
(* rngl_of_nat n × (mI (2 ^ n) . V) = rngl_of_nat n × V *)
rewrite vect_mul_1_l; easy.
Qed.

Definition is_eigenvector_of_An n μ (V : vector T) :=
  vect_nrows V = 2 ^ n ∧
  V ≠ vect_zero (2 ^ n) ∧
  (mA n • V = μ × V)%V.

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
  destruct HV as (V & Hvr & Hvz & Hv).
  now apply A_n_eigenvalue_squared_is_n with (V := V).
} {
  intros Hμ.
  remember (A_n_eigenvector_of_sqrt_n n μ (base_vector_1 42)) as V eqn:Hv.
  assert (Hvn : vect_nrows V = 2 ^ n). {
    rewrite Hv; cbn.
    unfold A_n_eigenvector_of_sqrt_n; cbn.
    destruct n; [ easy | cbn ].
    rewrite mA_nrows.
    now rewrite Nat.mul_comm.
  }
  exists V.
  split; [ easy | ].
  split. 2: {
    now apply An_eigen_equation_for_sqrt_n with (U := base_vector_1 42).
  }
  (* V ≠ vect_zero (2 ^ n) *)
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
    specialize rngl_opt_1_neq_0 as rngl_1_neq_0.
    rewrite H10 in rngl_1_neq_0.
    now apply rngl_1_neq_0 in H1.
  }
  intros H.
  remember base_vector_1 as ffff.
  injection H; clear H; intros H1 H2.
  subst ffff.
  set
    (f :=
       λ i,
       (Σ (j = 0, mat_ncols (mA n) * 1 - 1),
        mat_list_list_el 0 [[(mA n + μ × mI (2 ^ n))%M]; [mI (2 ^ n)]] i j *
        vect_el (base_vector_1 42) j)%F) in H2.
  set (g := λ _, 0%F) in H2.
  assert (H3 : ∀ i, f i = g i) by now rewrite H2.
  specialize (H3 0) as H4.
  unfold f, g in H4.
  rewrite Nat.mul_1_r in H4.
  rewrite rngl_summation_split_first in H4; [ | easy | flia ].
  unfold base_vector_1 in H4 at 1.
  cbn - [ iter_seq base_vector_1 ] in H4.
  rewrite rngl_mul_1_r in H4.
  unfold mat_list_list_el in H4 at 1.
  cbn - [ iter_seq base_vector_1 ] in H4.
  assert (Hzca : 0 < mat_ncols (mA n)). {
    rewrite mA_ncols.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  assert (Hzra : 0 < mat_nrows (mA n)). {
    rewrite mA_nrows.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  rewrite Nat.div_small in H4; [ | easy ].
  rewrite (Nat.mod_small 0) in H4; [ | easy ].
  rewrite Nat.div_small in H4; [ | easy ].
  rewrite (Nat.mod_small 0) in H4; [ | easy ].
  cbn - [ iter_seq base_vector_1 ] in H4.
  rewrite rngl_mul_1_r in H4.
  replace (mat_el (mA n) 0 0) with 0%F in H4. 2: {
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
  rewrite rngl_add_0_l in H4.
  rewrite all_0_rngl_summation_0 in H4; [ | easy | ]. 2: {
    intros i Hi; cbn.
    destruct i; [ easy | ].
    unfold mat_list_list_el; cbn.
    now apply rngl_mul_0_r.
  }
  rewrite rngl_add_0_r in H4.
  rewrite H4 in Hμ.
  rewrite rngl_mul_0_l in Hμ.
  symmetry in Hμ.
  move Hμ at bottom.
  specialize rngl_characteristic_prop as H.
  rewrite Hch in H.
  now apply H in Hμ.
}
Qed.

End a.

Inspect 1.
