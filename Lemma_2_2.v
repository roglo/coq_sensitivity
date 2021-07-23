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
(*
Import EqNotations.
*)

Require Import Misc RingLike MyVector Matrix.
Require Import RLsummation.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* *)

Print map2.
Fixpoint map2' A (f : A → A → A) (la lb : list A) :=
  match la with
  | [] => lb
  | a :: la' =>
      match lb with
      | [] => a :: la'
      | b :: lb' => f a b :: map2' f la' lb'
      end
  end.

(* conversion list of list of matrices into simple matrix *)

Definition mat_of_mat_list_list (mll : list (list (matrix T))) : matrix T :=
  mk_mat
    (flat_map
       (λ row,
        iter_list (map (@mat_list_list T) row) (map2' (@app T)) []) mll).

Notation "'MAP' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, map2' g c i) [])
  (at level 45, i at level 0, l at level 60).

Print mat_of_mat_list_list.
Print flat_map.

...

(*
Definition mat_of_mat_list_list (mll : list (list (matrix T))) : matrix T :=
  mk_mat
    (flat_map (λ row, iter_list row (map2' (@app T)) [])
       (map (λ row : list (matrix T), map (@mat_list_list T) row) mll)).

Definition old_mat_of_mat_list_list (mll : list (list (matrix T))) : matrix T :=
  mk_mat
    (flat_map (λ row, iter_list (tl row) (map2 (@app T)) (hd [] row))
       (map (λ row : list (matrix T), map (@mat_list_list T) row) mll)).
*)

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
*)

Theorem mA_nrows : ∀ n, mat_nrows (mA n) = 2 ^ n.
Proof.
intros.
induction n; [ easy | ].
cbn - [ "^" ].
rewrite app_nil_r, app_length.
unfold mat_nrows in IHn.
Search (length (iter_list _ _ _)).
Search (iter_list (map _ _)).
...

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I :
  rngl_has_opp = true →
  ∀ n, (mA n * mA n)%M = (rngl_of_nat n × mI (2 ^ n))%M.
Proof.
intros Hro *.
unfold "*"%M, "×"%M.
cbn; f_equal.
...
rewrite mA_nrows.
...
intros Hro *.
apply matrix_eq; cbn.
intros i k Hi Hk.
revert i k Hi Hk.
induction n; intros. {
  cbn.
  rewrite rngl_mul_0_l; [ | now left ].
  rewrite rngl_mul_0_l; [ | now left ].
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
cbn - [ Nat.pow ].
rewrite rngl_add_comm.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite mat_el_eq_rect; cbn.
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
  now rewrite mat_el_eq_rect; cbn.
}
unfold mat_list_list_el.
cbn - [ Nat.pow ].
destruct (lt_dec i (2 ^ n)) as [Hi2n| Hi2n]. {
  rewrite (Nat.div_small i); [ | easy ].
  rewrite (Nat.mod_small i); [ | easy ].
  cbn - [ Nat.pow ].
  destruct (lt_dec k (2 ^ n)) as [Hk2n| Hk2n]. {
    rewrite (Nat.div_small k); [ | easy ].
    rewrite (Nat.mod_small k); [ | easy ].
    cbn - [ Nat.pow ].
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite Nat.div_small; [ | flia Hi2n Hj ].
      now rewrite Nat.mod_small; [ | flia Hi2n Hj ].
    }
    cbn - [ Nat.pow ].
    rewrite IHn; [ | easy | easy ].
    rewrite (rngl_summation_split _ (i + 2 ^ n)); [ | cbn; flia Hi Hi2n ].
    rewrite rngl_summation_split_last; [ | flia ].
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i (j - 1 - 2 ^ n)) as [Hij| Hij]. {
        flia Hj Hij.
      }
      now apply rngl_mul_0_l; left.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i (j - 2 ^ n)) as [Hij| Hij]; [ flia Hj Hij | ].
      now apply rngl_mul_0_l; left.
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
      rewrite rngl_mul_0_r; [ | now left ].
      rewrite rngl_mul_0_r; [ | now left ].
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
    cbn - [ Nat.pow ].
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite Nat.div_small; [ | flia Hi2n Hj ].
      rewrite Nat.mod_small; [ | flia Hi2n Hj ].
      now cbn.
    }
    cbn - [ Nat.pow ].
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
      now apply rngl_mul_0_r; left.
    }
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec j (k - 2 ^ n)) as [Hjk| Hjk]; [ flia Hj Hjk | ].
      now apply rngl_mul_0_r; left.
    }
    rewrite rngl_add_0_r.
    remember (k - 2 ^ n) as j eqn:Hj.
    destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
    subst j; rewrite rngl_mul_1_r.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      now rewrite rngl_mul_opp_opp.
    }
    cbn - [ Nat.pow ].
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
    cbn - [ Nat.pow ].
    rewrite (rngl_summation_split _ i); [ | flia Hi Hi2n ].
    rewrite rngl_summation_split_last; [ | flia ].
    destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
    rewrite rngl_mul_1_l.
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i (j - 1)) as [Hij| Hij]; [ flia Hij Hj | ].
      rewrite rngl_mul_0_l; [ | now left ].
      now apply rngl_opp_0.
    }
    rewrite rngl_add_0_l.
    rewrite rngl_add_assoc.
    rewrite (@fold_rngl_sub _ _ Hro).
    rewrite rngl_sub_diag; [ | now left ].
    rewrite rngl_add_0_l.
    destruct (Nat.eq_dec i k) as [Hik| Hik]; [ flia Hi2n Hk2n Hik | ].
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec i j) as [Hij| Hij]; [ flia Hj Hij | ].
      rewrite rngl_mul_0_l; [ | now left ].
      now apply rngl_opp_0.
    }
    symmetry.
    now apply rngl_mul_0_r; left.
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
  cbn - [ Nat.pow ].
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    assert (H : 0 < 2 ^ n). {
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite Nat.div_small; [ | flia Hj H ].
    rewrite Nat.mod_small; [ | flia Hj H ].
    easy.
  }
  cbn - [ Nat.pow ].
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
    now apply rngl_mul_0_l; left.
  }
  rewrite rngl_add_0_l.
  rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
    intros j Hj.
    destruct (Nat.eq_dec (i - 2 ^ n) j) as [Hij| Hij]; [ flia Hj Hij | ].
    now apply rngl_mul_0_l; left.
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
  cbn - [ Nat.pow ].
  destruct (lt_dec k (2 ^ n)) as [Hk2n| Hk2n]. {
    rewrite (Nat.div_small k); [ | easy ].
    rewrite (Nat.mod_small k); [ | easy ].
    cbn - [ Nat.pow ].
    rewrite (rngl_summation_split _ k). 2: {
      cbn in Hk; flia Hk Hk2n.
    }
    rewrite rngl_summation_split_last; [ | flia ].
    destruct (Nat.eq_dec i k) as [Hik| Hik]; [ flia Hik Hi2n Hk2n | ].
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec (j - 1) k) as [Hjk| Hjk]; [ flia Hj Hjk | ].
      now apply rngl_mul_0_r; left.
    }
    rewrite rngl_add_0_l.
    destruct (Nat.eq_dec k k) as [H| H]; [ clear H | easy ].
    rewrite rngl_mul_1_r.
    rewrite rngl_add_assoc.
    rewrite (@fold_rngl_sub _ _ Hro).
    rewrite rngl_sub_diag; [ | now left ].
    rewrite rngl_add_0_l.
    rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
      intros j Hj.
      destruct (Nat.eq_dec j k) as [Hjk| Hjk]; [ flia Hj Hjk | ].
      now apply rngl_mul_0_r; left.
    }
    symmetry.
    now apply rngl_mul_0_r; left.
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
    cbn - [ Nat.pow ].
    erewrite rngl_summation_eq_compat. 2: {
      intros l Hl.
      now rewrite rngl_mul_opp_opp.
    }
    cbn - [ Nat.pow ].
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
      rewrite rngl_mul_0_r; [ | now left ].
      rewrite rngl_mul_0_r; [ easy | now left ].
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
   This way, we have to prove that this pair eigen(value,vector)
   works *)

Theorem m_o_mll_2x2_2x1 : ∀ n (M1 M2 M3 M4 M5 M6 : matrix n n T),
  (mat_of_mat_list_list [[M1; M2]; [M3; M4]] *
   mat_of_mat_list_list [[M5]; [M6]])%M =
   mat_of_mat_list_list [[M1 * M5 + M2 * M6]; [M3 * M5 + M4 * M6]]%M.
Proof.
intros.
apply matrix_eq; cbn.
intros * Hi Hj.
rewrite Nat.mul_1_r in Hj.
unfold mat_mul, mat_add; cbn.
unfold mat_list_list_el; cbn.
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
  easy.
}
cbn.
erewrite (rngl_summation_eq_compat _ _ _ (n + 1)). 2: {
  intros k Hk.
  rewrite (Nat_div_less_small 1); [ | flia Hk ].
  rewrite (@Nat_mod_less_small 1 k); [ | flia Hk ].
  rewrite Nat.mul_1_l.
  easy.
}
cbn.
destruct (lt_dec i n) as [Hir1| Hir1]. {
  rewrite Nat.div_small; [ | easy ].
  rewrite Nat.mod_small; [ | easy ].
  cbn.
  rewrite <- rngl_add_assoc.
  f_equal. {
    rewrite rngl_summation_shift; [ | flia Hj ].
    apply rngl_summation_eq_compat.
    intros k Hk.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  destruct (Nat.eq_dec n 1) as [Hc11| Hc11]. {
    subst n; cbn.
    unfold iter_seq, iter_list; cbn.
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
  cbn.
  rewrite Nat.add_0_r, <- rngl_add_assoc.
  f_equal. {
    rewrite rngl_summation_shift; [ | flia Hi ].
    apply rngl_summation_eq_compat.
    intros k Hk.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  destruct (Nat.eq_dec n 1) as [Hc11| Hc11]. {
    subst n; cbn.
    unfold iter_seq, iter_list; cbn.
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

Definition mat_of_list_list_1_row_2_col {n} (A B : matrix (2 ^ n) (2 ^ n) T) :
    matrix (2 ^ S n) (2 ^ n) T :=
  eq_rect _ (λ m, matrix (2 ^ S n) m T)
    (eq_rect _ (λ m, matrix m (2 ^ n * 1) T)
       (mat_of_mat_list_list [[A]; [B]]) _
       (two_pow_n_mul_two n)) _
    (Nat.mul_1_r (2 ^ n)).

Definition base_vector_1 dim :=
  mk_vect dim (λ i, match i with 0 => 1%F | _ => 0%F end).

Definition A_Sn_eigenvector_of_sqrt_Sn n μ (V : vector (2 ^ n) T) :
    vector (2 ^ S n) T :=
  (mat_of_list_list_1_row_2_col (mA n + μ × mI (2 ^ n))%M (mI (2 ^ n)) • V)%M.

(*
...
*)

Theorem mA_diag_zero :
  rngl_has_opp = true →
  ∀ n i, i < 2 ^ n → mat_el (mA n) i i = 0%F.
Proof.
intros Hop * Hi2n.
revert i Hi2n.
induction n; intros; [ easy | cbn ].
etransitivity; [ now rewrite mat_el_eq_rect | cbn ].
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

Theorem rngl_mul_eq_if : ∀ a b c d, a = c → b = d → (a * b = c * d)%F.
Proof.
intros * Hac Hbd.
now subst a b.
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
intros Hic Hro Hin Hde * Hμ.
destruct n. {
  intros V.
  cbn in Hμ, V |-*.
  apply vector_eq.
  intros i Hi; cbn in Hi |-*.
  apply Nat.lt_1_r in Hi; subst i.
  unfold iter_seq, iter_list; cbn.
  rewrite rngl_mul_0_l, rngl_add_0_l; [ | now left ].
  specialize rngl_integral as H.
  rewrite Hro, Hin, Hde in H; cbn in H.
  rewrite Bool.orb_true_r in H.
  apply (H (or_introl eq_refl) eq_refl) in Hμ.
  symmetry.
  now destruct Hμ; subst μ; apply rngl_mul_0_l; left.
}
intros * HV.
subst V.
unfold A_Sn_eigenvector_of_sqrt_Sn.
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
