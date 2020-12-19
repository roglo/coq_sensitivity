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

Definition upper_left_mat_in_list_list {m n} mll : matrix m n T :=
  hd (mZ m n) (hd [] mll).

Definition mat_list_list_el {m n} mll i j :=
  let M : matrix m n T := upper_left_mat_in_list_list mll in
  mat_el (nth (j / n) (nth (i / m) mll []) (mZ m n))
    (i mod m) (j mod n).

Definition mat_of_mat_list_list {m n} (mll : list (list (matrix m n T))) :
    matrix _ _ T :=
  let M := upper_left_mat_in_list_list mll in
  mk_mat (m * length mll) (n * length (hd [] mll))
    (mat_list_list_el mll).

(* sequence "An" *)

Theorem mA_transp_prop : ∀ n len,
  2 = len
  → matrix (2 ^ n * len) (2 ^ n * len) T =
     matrix (2 ^ S n) (2 ^ S n) T.
Proof.
intros * Hlen; cbn.
destruct Hlen.
now rewrite Nat.mul_comm.
Qed.

(*
Definition mA_transp_prop' n len (Hlen : 2 = len) :=
  match Hlen with
  | eq_refl =>
      match
        match Nat.mul_comm (2 ^ n) 2 in (_ = sn) return (sn = 2 ^ n * 2) with
        | eq_refl => eq_refl
        end in (_ = m) return matrix m m T = matrix (2 ^ S n) (2 ^ S n) T
      with
      | eq_refl => eq_refl
      end
  end.
*)

Fixpoint mA (n : nat) : matrix (2 ^ n) (2 ^ n) T :=
  match n with
  | 0 => mZ 1 1
  | S n' =>
      let ll :=
        [[mA n'; mI (2 ^ n')];
         [mI (2 ^ n'); (- mA n')%M]]
      in
      transport (mat_of_mat_list_list ll) (mA_transp_prop n' eq_refl)
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
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  unfold transport.
enough (rngl_has_dec_eq = true).
specialize rngl_opt_eq_dec as rngl_eq_dec.
rewrite H in rngl_eq_dec.
Check (mA_transp_prop n eq_refl).
Check (Eqdep_dec.UIP_dec rngl_eq_dec).
...
rewrite (Eqdep_dec.UIP_dec rngl_eq_dec) with (x := matrix (2 ^ n * 2) (2 ^ n * 2) T).
...
Theorem glop : ∀ m n p q (A : matrix m n T) P i j,
  mat_el (transport A P : matrix p q T) i j = mat_el A i j.
Proof.
intros.
unfold transport.
...
do 2 rewrite glop.
cbn.
...
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
       • V)%V
  end.

Theorem A_n_eigen_formula_for_sqrt_n :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_dec_eq = true →
  ∀ n μ U V,
  V = A_n_eigenvector_of_sqrt_n n μ U
  → (μ * μ)%F = rngl_of_nat n
  → (mA n • V = μ × V)%V.
Proof.
intros Hic Hro Hin Hde * HV Hμ.
destruct n. {
  cbn in Hμ, HV |-*.
  apply vector_eq; [ now subst V | ].
  intros i Hi; cbn in Hi |-*.
  subst V; cbn.
  rewrite rngl_mul_0_l, rngl_add_0_l.
  destruct i; [ | flia Hi ].
  rewrite rngl_mul_1_r; symmetry; clear Hi.
  specialize rngl_integral as H.
  rewrite Hin in H; cbn in H.
  rewrite Hde in H.
  rewrite Bool.orb_true_r in H.
  apply (H eq_refl) in Hμ.
  now destruct Hμ.
}
cbn - [ Nat.pow ] in HV.
rewrite HV.
rewrite mat_vect_mul_assoc.
cbn - [ iter_seq Nat.pow ].
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
  rngl_characteristic = 0 →
  ∀ n μ,
  (∃ V, is_eigenvector_of_An n μ V) ↔ (μ * μ = rngl_of_nat n)%F.
Proof.
intros Hic Hro Heq Hin Hch *.
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
    now apply A_n_eigen_formula_for_sqrt_n with (U := base_vector_1 42).
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
