(* characteristic polynomial = det(xI-M) *)

Set Typeclasses Depth 100.
Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Init.Nat.

Require Import Misc Semiring SRsummation SRproduct.
Require Import SRpolynomial Matrix.
Import polynomial_Notations.
Import matrix_Notations.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.
Context {sdp : sring_dec_prop T}.
Context {acp : algeb_closed_prop}.
Existing Instance polyn_semiring_op.
Existing Instance polyn_ring_op.
Existing Instance polyn_semiring_prop.
Existing Instance polyn_ring_prop.

(* convertion matrix → matrix with monomials *)

Definition m2mm M : matrix (polynomial T) :=
  mk_mat (λ i j, polyn_of_const (mat_el M i j))
    (mat_nrows M) (mat_ncols M).

Definition xI_sub_M M := (_x × m2mm (mI (mat_nrows M)) - m2mm M)%M.
Definition charac_polyn (M : matrix T) := determinant (xI_sub_M M).

Theorem fold_xI_sub_M : ∀ M,
  (_x × m2mm (mI (mat_nrows M)) - m2mm M)%M = xI_sub_M M.
Proof. easy. Qed.

Theorem xI_sub_M_nrows : ∀ M,
  mat_nrows (xI_sub_M M) = mat_nrows M.
Proof. easy. Qed.

Theorem submatrix_m2mm : ∀ (M : matrix T) i j,
  subm (m2mm M) i j = m2mm (subm M i j).
Proof.
intros.
apply matrix_eq; cbn; [ easy | easy | ].
intros k l Hk Hl.
now destruct (lt_dec k i), (lt_dec l j).
Qed.

Theorem submatrix_xI_sub_M : ∀ M i,
  subm (xI_sub_M M) i i = xI_sub_M (subm M i i).
Proof.
intros.
unfold xI_sub_M; cbn.
rewrite submatrix_sub, <- submatrix_m2mm; f_equal.
rewrite submatrix_mul_scal_l.
rewrite submatrix_m2mm.
destruct (mat_nrows M) as [| r]. {
  now cbn; apply matrix_eq.
}
rewrite submatrix_mI.
now rewrite Nat.sub_succ, Nat.sub_0_r.
Qed.

Theorem mat_el_xI_sub_M : ∀ i j M,
  mat_el (xI_sub_M M) i j =
    if Nat.eq_dec i j then (_x - polyn_of_const (mat_el M i i))%P
    else (- polyn_of_const (mat_el M i j))%P.
Proof.
intros; cbn.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  now rewrite Hij, polyn_mul_1_r.
}
unfold polyn_of_const.
now rewrite polyn_of_list_0, polyn_mul_0_r, polyn_add_0_l.
Qed.

Theorem polyn_degree_mat_el_xI_sub_M_0_0 : ∀ M,
  polyn_degree (mat_el (xI_sub_M M) 0 0) = 1.
Proof.
intros.
rewrite mat_el_xI_sub_M.
apply polyn_degree_1; [ easy | ].
rewrite polyn_degree_opp.
apply polyn_degree_of_const.
Qed.

Theorem polyn_coeff_mat_el_xI_sub_M_0_0 : ∀ M,
  polyn_coeff (mat_el (xI_sub_M M) 0 0) 1 = 1%Srng.
Proof.
intros.
cbn; rewrite if_1_eq_0; cbn.
cbn; rewrite if_1_eq_0; cbn.
rewrite srng_add_0_l, srng_mul_0_l, srng_mul_1_l.
rewrite srng_add_0_l, srng_mul_0_l.
rewrite if_1_eq_0; cbn.
destruct (srng_eq_dec (mat_el M 0 0)) as [Hmz| Hmz]. {
  now cbn; rewrite if_1_eq_0.
}
now cbn; rewrite if_1_eq_0.
Qed.

Theorem mat_el_xI_sub_M_0_succ : ∀ M i,
  mat_el (xI_sub_M M) 0 (S i) = (- polyn_of_list [mat_el M 0 (S i)])%P.
Proof.
intros.
apply mat_el_xI_sub_M.
Qed.

Theorem polyn_degree_mat_el_xI_sub_M_0_succ : ∀ M i,
  polyn_degree (mat_el (xI_sub_M M) 0 (S i)) = 0.
Proof.
intros.
rewrite mat_el_xI_sub_M_0_succ.
rewrite polyn_degree_opp.
apply polyn_degree_of_const.
Qed.

Theorem polyn_coeff_mat_el_xI_sub_M_0_succ : ∀ i M,
  polyn_coeff (mat_el (xI_sub_M M) 0 (S i)) 0 = (- mat_el M 0 (S i))%Rng.
Proof.
intros.
rewrite mat_el_xI_sub_M_0_succ.
rewrite polyn_coeff_opp.
f_equal.
apply polyn_coeff_of_const.
Qed.

Theorem polyn_degree_mat_el_subm_xI_sub_M_0_succ_0_0 : ∀ M i,
  polyn_degree (mat_el (subm (xI_sub_M M) 0 (S i)) 0 0) = 0.
Proof.
intros; cbn.
rewrite if_1_eq_0; cbn.
rewrite if_0_eq_0; cbn.
rewrite srng_add_0_l, srng_mul_0_l.
rewrite if_0_eq_0; cbn.
destruct (srng_eq_dec (mat_el M 1 0) 0) as [Hmz| Hmz]; [ easy | cbn ].
now destruct (srng_eq_dec (- mat_el M 1 0)%Rng 0).
Qed.

Theorem polyn_degree_mat_el_subm_subm_xI_sub_M_0_succ_0_0 : ∀ M i,
  polyn_degree (mat_el (subm (subm (xI_sub_M M) 0 (S i)) 0 0) 0 0) ≤ 1.
Proof.
intros; cbn.
unfold polyn_of_const.
rewrite srng_mul_1_r.
specialize (polyn_of_list_repeat_0s 1) as H.
cbn in H; rewrite H; clear H.
rewrite srng_mul_0_r, srng_add_0_l.
destruct (lt_dec 1 (S i)) as [H1i| H1i]. {
  rewrite polyn_degree_opp.
  rewrite fold_polyn_of_const.
  rewrite polyn_degree_of_const.
  apply Nat.le_0_l.
}
rewrite polyn_degree_1; [ easy | easy | ].
rewrite polyn_degree_opp.
rewrite fold_polyn_of_const.
now rewrite polyn_degree_of_const.
Qed.

Theorem polyn_coeff_mat_el_subm_xI_sub_M_succ_0_0_0 : ∀ M i,
  polyn_coeff (mat_el (subm (xI_sub_M M) 0 (S i)) 0 0) 0 =
    (- mat_el M 1 0)%Rng.
Proof.
intros; cbn.
rewrite if_1_eq_0; cbn.
rewrite if_0_eq_0; cbn.
rewrite srng_add_0_l, srng_mul_0_l.
rewrite if_0_eq_0; cbn.
destruct (srng_eq_dec (mat_el M 1 0) 0) as [Hmz| Hmz]. {
  cbn; symmetry.
  rewrite Hmz.
  apply rng_opp_0.
}
cbn.
now destruct (srng_eq_dec (- mat_el M 1 0)%Rng 0).
Qed.

Fixpoint repeat_subm T (M : matrix T) l :=
  match l with
  | [] => M
  | i :: l' => subm (repeat_subm M l') 0 i
  end.

Theorem subm_repeat_subm : ∀ T (M : matrix T) l i,
  subm (repeat_subm M l) 0 i = repeat_subm M (i :: l).
Proof. easy. Qed.

Theorem polyn_degree_mat_el_repeat_subm_le_1 : ∀ M i j k l,
  polyn_degree (mat_el (repeat_subm (subm (xI_sub_M M) 0 i) l) k j) ≤ 1.
Proof.
intros.
revert j k.
induction l as [| m]; intros. {
  cbn.
  destruct (lt_dec j i) as [Hji| Hji]. {
    destruct (Nat.eq_dec (k + 1) j) as [Hkj| Hkj]. {
      rewrite polyn_mul_1_r; [ | easy ].
      rewrite polyn_degree_1; [ easy | easy | ].
      rewrite polyn_degree_opp.
      now rewrite polyn_degree_of_const.
    }
    unfold polyn_of_const.
    rewrite polyn_of_list_0.
    rewrite polyn_mul_0_r; [ | easy ].
    rewrite polyn_add_0_l.
    rewrite polyn_degree_opp.
    rewrite fold_polyn_of_const.
    rewrite polyn_degree_of_const.
    apply Nat.le_0_l.
  }
  destruct (Nat.eq_dec (k + 1) (j + 1)) as [Hkj| Hkj]. {
    rewrite polyn_mul_1_r; [ | easy ].
    rewrite polyn_degree_1; [ easy | easy | ].
    rewrite polyn_degree_opp.
    now rewrite polyn_degree_of_const.
  }
  unfold polyn_of_const.
  rewrite polyn_of_list_0.
  rewrite polyn_mul_0_r; [ | easy ].
  rewrite polyn_add_0_l.
  rewrite polyn_degree_opp.
  rewrite fold_polyn_of_const.
  rewrite polyn_degree_of_const.
  apply Nat.le_0_l.
}
cbn.
destruct (lt_dec j m) as [Hjm| Hjm]; [ apply IHl | ].
apply IHl.
Qed.

Theorem polyn_degree_minus_one_pow : ∀ i,
  polyn_degree (minus_one_pow i) = 0.
Proof.
intros.
unfold polyn_degree.
unfold polyn_degree_plus_1.
unfold minus_one_pow.
now destruct (i mod 2); cbn; rewrite if_1_eq_0.
Qed.

Theorem polyn_coeff_minus_one_pow : ∀ i,
  polyn_coeff (minus_one_pow i) 0 = minus_one_pow i.
Proof.
intros.
unfold minus_one_pow.
now destruct (i mod 2); cbn; rewrite if_1_eq_0.
Qed.

Theorem polyn_degree_det_loop_repeat_subm_le : ∀ l M i n,
  polyn_degree (det_loop (repeat_subm (subm (xI_sub_M M) 0 i) l) n) ≤ n.
Proof.
intros.
revert l.
induction n; intros; [ now cbn; rewrite if_1_eq_0 | ].
cbn - [ iter_seq repeat_subm ].
etransitivity; [ now apply polyn_degree_summation_ub | ].
cbn - [ iter_seq polyn_degree xI_sub_M ].
apply Max_lub_le.
intros j (_, Hj).
move j before i.
rewrite <- polyn_mul_assoc; [ | easy | easy ].
etransitivity; [ now apply polyn_degree_mul_le | ].
rewrite polyn_degree_minus_one_pow, Nat.add_0_l.
etransitivity; [ now apply polyn_degree_mul_le | ].
etransitivity. {
  apply (Nat.add_le_mono_r _ 1).
  apply polyn_degree_mat_el_repeat_subm_le_1.
}
apply -> Nat.succ_le_mono.
rewrite subm_repeat_subm.
apply IHn.
Qed.

Theorem polyn_degree_det_loop_subm_xI_sub_M_le : ∀ i n M,
  polyn_degree (det_loop (subm (xI_sub_M M) 0 i) n) ≤ n.
Proof.
intros.
revert i M.
destruct n; intros; [ now cbn; rewrite if_1_eq_0; cbn | ].
cbn - [ iter_seq xI_sub_M ].
etransitivity; [ now apply polyn_degree_summation_ub | ].
cbn - [ iter_seq polyn_degree xI_sub_M ].
apply Max_lub_le.
intros j (_, Hj).
move j before i.
rewrite <- polyn_mul_assoc; [ | easy | easy ].
etransitivity; [ now apply polyn_degree_mul_le | ].
rewrite polyn_degree_minus_one_pow, Nat.add_0_l.
etransitivity; [ now apply polyn_degree_mul_le | ].
etransitivity. {
  apply (Nat.add_le_mono_r _ 1).
  destruct (lt_dec j i) as [Hji| Hji]. {
    rewrite mat_el_xI_sub_M.
    destruct (Nat.eq_dec 1 j) as [H1j| H1j]. {
      unfold polyn_sub.
      rewrite polyn_degree_1; [ easy | easy | ].
      rewrite polyn_degree_opp.
      apply polyn_degree_of_const.
    }
    rewrite polyn_degree_opp.
    rewrite polyn_degree_of_const.
    apply Nat.le_0_l.
  }
  apply Nat.nlt_ge in Hji.
  rewrite mat_el_xI_sub_M.
  destruct (Nat.eq_dec 1 (j + 1)) as [H1j| H1j]. {
    unfold polyn_sub.
    rewrite polyn_degree_1; [ easy | easy | ].
    rewrite polyn_degree_opp.
    apply polyn_degree_of_const.
  }
  rewrite polyn_degree_opp.
  rewrite polyn_degree_of_const.
  apply Nat.le_0_l.
}
apply -> Nat.succ_le_mono.
revert i j M Hj.
induction n; intros; [ now cbn; rewrite if_1_eq_0 | ].
cbn - [ iter_seq xI_sub_M ].
etransitivity; [ now apply polyn_degree_summation_ub | ].
cbn - [ iter_seq polyn_degree xI_sub_M ].
apply Max_lub_le.
intros k (_, Hk).
move k before j.
rewrite <- polyn_mul_assoc; [ | easy | easy ].
etransitivity; [ now apply polyn_degree_mul_le | ].
rewrite polyn_degree_minus_one_pow, Nat.add_0_l.
etransitivity; [ now apply polyn_degree_mul_le | ].
etransitivity. {
  apply (Nat.add_le_mono_r _ 1).
  destruct (lt_dec k j) as [Hkj| Hkj]. {
    destruct (lt_dec k i) as [Hki| Hki]. {
      rewrite mat_el_xI_sub_M.
      destruct (Nat.eq_dec 2 k) as [H2k| H2k]. {
        unfold polyn_sub.
        rewrite polyn_degree_1; [ easy | easy | ].
        rewrite polyn_degree_opp.
        apply polyn_degree_of_const.
      }
      rewrite polyn_degree_opp.
      rewrite polyn_degree_of_const.
      apply Nat.le_0_l.
    }
    apply Nat.nlt_ge in Hki.
    rewrite mat_el_xI_sub_M.
    destruct (Nat.eq_dec 2 (k + 1)) as [H2k| H2k]. {
      unfold polyn_sub.
      rewrite polyn_degree_1; [ easy | easy | ].
      rewrite polyn_degree_opp.
      apply polyn_degree_of_const.
    }
    rewrite polyn_degree_opp.
    rewrite polyn_degree_of_const.
    apply Nat.le_0_l.
  }
  apply Nat.nlt_ge in Hkj.
  destruct (lt_dec (k + 1) i) as [Hki| Hki]. {
    rewrite mat_el_xI_sub_M.
    destruct (Nat.eq_dec 2 (k + 1)) as [H2k| H2k]. {
      unfold polyn_sub.
      rewrite polyn_degree_1; [ easy | easy | ].
      rewrite polyn_degree_opp.
      apply polyn_degree_of_const.
    }
    rewrite polyn_degree_opp.
    rewrite polyn_degree_of_const.
    apply Nat.le_0_l.
  }
  apply Nat.nlt_ge in Hki.
  rewrite mat_el_xI_sub_M.
  destruct (Nat.eq_dec 2 (k + 1 + 1)) as [H2k| H2k]. {
    unfold polyn_sub.
    rewrite polyn_degree_1; [ easy | easy | ].
    rewrite polyn_degree_opp.
    apply polyn_degree_of_const.
  }
  rewrite polyn_degree_opp.
  rewrite polyn_degree_of_const.
  apply Nat.le_0_l.
}
apply -> Nat.succ_le_mono.
apply (polyn_degree_det_loop_repeat_subm_le [k; j]).
Qed.

Theorem polyn_degree_det_loop_xI_sub_M : ∀ n M,
  mat_nrows M = n
  → polyn_degree (det_loop (xI_sub_M M) n) = n.
Proof.
intros * Hr.
revert M Hr.
induction n; intros; [ now cbn; rewrite if_1_eq_0 | ].
cbn - [ iter_seq xI_sub_M ].
specialize (IHn (subm M 0 0)) as Hpd.
rewrite submatrix_nrows, Hr, Nat.sub_succ, Nat.sub_0_r in Hpd.
specialize (Hpd eq_refl).
rewrite <- submatrix_xI_sub_M in Hpd.
rewrite srng_summation_split_first; [ | | apply Nat.le_0_l ]. 2: {
  now apply polyn_semiring_prop.
}
remember (det_loop (subm (xI_sub_M M) 0 0) n) as P eqn:HP.
cbn - [ polyn_degree xI_sub_M iter_seq ].
rewrite srng_mul_1_l.
rewrite polyn_degree_lt_add; [ | easy | ]. 2: {
  eapply le_lt_trans; [ now apply polyn_degree_summation_ub | ].
  cbn - [ iter_seq polyn_degree mat_el ].
  apply le_lt_trans with
    (m := Max (i = 1, n), polyn_degree (det_loop (subm (xI_sub_M M) 0 i) n)).
  {
    apply Max_le_compat.
    intros i Hi.
    rewrite <- polyn_mul_assoc; [ | easy | easy ].
    etransitivity; [ now apply polyn_degree_mul_le | ].
    rewrite polyn_degree_minus_one_pow, Nat.add_0_l.
    etransitivity; [ now apply polyn_degree_mul_le | ].
    destruct i; [ flia Hi | ].
    rewrite polyn_degree_mat_el_xI_sub_M_0_succ, Nat.add_0_l.
    easy.
  }
  apply Max_lub_lt. {
    destruct n. {
      cbn in HP; rewrite HP.
      rewrite fold_polyn_of_const.
      rewrite polyn_mul_1_r; [ | easy ].
      rewrite polyn_degree_mat_el_xI_sub_M_0_0.
      apply Nat.lt_0_1.
    }
    rewrite polyn_degree_mul; [ | easy | ]. 2: {
      rewrite polyn_degree_mat_el_xI_sub_M_0_0.
      rewrite polyn_coeff_mat_el_xI_sub_M_0_0, srng_mul_1_l.
      apply polyn_highest_coeff_neq_0.
      now rewrite Hpd.
    }
    rewrite polyn_degree_mat_el_xI_sub_M_0_0.
    flia.
  }
  intros i Hi.
  rewrite polyn_degree_mul; [ | easy | ]. 2: {
    rewrite polyn_degree_mat_el_xI_sub_M_0_0.
    rewrite polyn_coeff_mat_el_xI_sub_M_0_0, srng_mul_1_l.
    apply polyn_highest_coeff_neq_0.
    rewrite Hpd; flia Hi.
  }
  rewrite Hpd.
  rewrite polyn_degree_mat_el_xI_sub_M_0_0, Nat.add_1_l.
  apply Nat.lt_succ_r.
  apply polyn_degree_det_loop_subm_xI_sub_M_le.
}
rewrite polyn_degree_mul; [ | easy | ]. 2: {
  rewrite polyn_degree_mat_el_xI_sub_M_0_0.
  rewrite polyn_coeff_mat_el_xI_sub_M_0_0.
  rewrite srng_mul_1_l.
  destruct n. {
    cbn in HP; subst P; cbn.
    rewrite if_1_eq_0; cbn.
    apply srng_1_neq_0.
  }
  apply polyn_highest_coeff_neq_0.
  now rewrite Hpd.
}
rewrite polyn_degree_mat_el_xI_sub_M_0_0.
destruct n. {
  subst P; cbn.
  now rewrite if_1_eq_0.
}
now rewrite Hpd.
Qed.

Theorem polyn_coeff_det_loop_xI_sub_M : ∀ n M,
  mat_nrows M = n
  → polyn_coeff (det_loop (xI_sub_M M) n) n = 1%Srng.
Proof.
intros * Hr.
revert M Hr.
induction n; intros; [ now cbn; rewrite if_1_eq_0 | ].
cbn - [ iter_seq xI_sub_M ].
specialize (IHn (subm M 0 0)) as Hpc.
rewrite submatrix_nrows, Hr, Nat.sub_succ, Nat.sub_0_r in Hpc.
specialize (Hpc eq_refl).
rewrite <- submatrix_xI_sub_M in Hpc.
rewrite srng_summation_split_first; [ | | apply Nat.le_0_l ]. 2: {
  now apply polyn_semiring_prop.
}
remember (det_loop (subm (xI_sub_M M) 0 0) n) as P eqn:HP.
cbn - [ polyn_coeff xI_sub_M iter_seq ].
rewrite srng_mul_1_l.
rewrite polyn_coeff_add; [ | easy ].
rewrite srng_add_comm.
rewrite polyn_coeff_overflow. 2: {
  eapply le_lt_trans; [ now apply polyn_degree_summation_ub | ].
  cbn - [ iter_seq polyn_degree xI_sub_M ].
  apply Max_lub_lt; [ apply Nat.lt_0_succ | ].
  intros i Hi.
  eapply le_lt_trans; [ now apply polyn_degree_mul_le | ].
  rewrite <- Nat.add_1_l.
  apply Nat.add_lt_le_mono. {
    eapply le_lt_trans; [ now apply polyn_degree_mul_le |].
    rewrite polyn_degree_minus_one_pow.
    destruct i; [ easy | ].
    rewrite polyn_degree_mat_el_xI_sub_M_0_succ.
    apply Nat.lt_0_succ.
  }
  destruct i; [ easy | ].
  apply polyn_degree_det_loop_subm_xI_sub_M_le.
}
rewrite srng_add_0_l.
rewrite polyn_coeff_mul; [ | easy ].
rewrite srng_summation_split_first; [ | easy | apply Nat.le_0_l ].
rewrite Nat.sub_0_r.
rewrite srng_summation_split_first; [ | easy | flia ].
rewrite Nat.sub_succ, Nat.sub_0_r, Hpc, srng_mul_1_r.
rewrite polyn_coeff_mat_el_xI_sub_M_0_0.
rewrite (polyn_coeff_overflow P). 2: {
  rewrite HP.
  apply Nat.lt_succ_r.
  apply polyn_degree_det_loop_subm_xI_sub_M_le.
}
rewrite srng_mul_0_r, srng_add_0_l.
rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
  intros i Hi.
  rewrite mat_el_xI_sub_M.
  destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
  rewrite polyn_coeff_overflow. 2: {
    unfold polyn_sub.
    rewrite polyn_degree_1; [ easy | easy | ].
    rewrite polyn_degree_opp.
    apply polyn_degree_of_const.
  }
  apply srng_mul_0_l.
}
apply srng_add_0_r.
Qed.

(* the degree of the caracteristic polynomial is the size of the matrix *)

Theorem charac_polyn_degree : ∀ M,
  polyn_degree (charac_polyn M) = mat_nrows M.
Proof.
intros.
unfold charac_polyn.
unfold determinant; cbn.
now apply polyn_degree_det_loop_xI_sub_M.
Qed.

(* the caracteristic polynomial of a matrix is monic, i.e. its
   leading coefficient is 1 *)

Theorem charac_polyn_is_monic : ∀ M,
  is_monic_polyn (charac_polyn M).
Proof.
intros.
unfold is_monic_polyn.
rewrite charac_polyn_degree.
unfold charac_polyn.
unfold determinant; cbn.
now apply polyn_coeff_det_loop_xI_sub_M.
Qed.

(* the list of coefficients of the characteristic polynomial of a matrix M
   has length "nrows(M) + 1"
   e.g. matrix
        (a b)
        (c d)
   characteristic polynomial = determinant of
        (x-a -b )
        (-c  x-d)
   which is
        (x-a)(x-d)-cb = x²-(a+d)x+(ad-bc)
   list of its coefficients
        [ad-bc; -(a+d); 1]
   whose length is 3 = nrows(M)+1
 *)

Theorem charac_polyn_list_length : ∀ M,
  length (polyn_list (charac_polyn M)) = mat_nrows M + 1.
Proof.
intros.
remember (mat_nrows M) as n eqn:Hn; symmetry in Hn.
destruct n. {
  cbn; rewrite Hn; cbn.
  now rewrite if_1_eq_0.
}
specialize (charac_polyn_degree M) as Hcp.
cbn in Hcp |-*.
unfold polyn_degree, polyn_degree_plus_1 in Hcp.
flia Hn Hcp.
Qed.

(* roots of characteristic polynomial supposed to be eigenvalues *)

(*
Theorem exists_root_of_charac_polyn : ∀  (M : matrix T),
  mat_nrows M ≠ 0
  → is_square_mat M
  → ∃ μ, eval_polyn (charac_polyn M) μ = 0%Srng.
Proof.
intros M Hrz HM.
destruct acp as (Hroots).
specialize (Hroots (charac_polyn M)) as H1.
assert (H2 : polyn_coeff (charac_polyn M) (mat_nrows M) = 1%Srng). {
  specialize (charac_polyn_is_monic M) as H2.
  unfold is_monic_polyn in H2.
  now rewrite charac_polyn_degree in H2.
}
assert (H3 : polyn_degree (charac_polyn M) = mat_nrows M). {
  apply charac_polyn_degree.
}
unfold so in H1.
rewrite H3 in H1.
assert (H : mat_nrows M > 0) by flia Hrz.
specialize (H1 H); clear H.
destruct H1 as (μ, Hμ).
now exists μ.
Qed.
*)

Theorem exists_charac_polyn_roots : ∀ (M : matrix T),
  is_square_mat M
  → ∃ roots,
     charac_polyn M =
       (Π (i = 1, mat_nrows M),
          (_x - polyn_of_const (nth (i - 1) roots 0%Srng))%P)%Srng.
Proof.
intros M HM.
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  exists [].
  now cbn; rewrite Hrz; cbn.
}
specialize (alcl_roots (charac_polyn M)) as H1.
assert (H2 : polyn_coeff (charac_polyn M) (mat_nrows M) = 1%Srng). {
  specialize (charac_polyn_is_monic M) as H2.
  unfold is_monic_polyn in H2.
  now rewrite charac_polyn_degree in H2.
}
assert (H3 : polyn_degree (charac_polyn M) = mat_nrows M). {
  apply charac_polyn_degree.
}
rewrite H3 in H1.
assert (H : mat_nrows M > 0) by flia Hrz.
specialize (H1 H); clear H.
destruct H1 as (x, Hx).
specialize (polyn_in_algeb_closed (charac_polyn M)) as H1.
destruct H1 as (RL, Hrl); exists RL.
unfold polyn_highest_coeff in Hrl.
rewrite H3, H2 in Hrl.
unfold polyn_of_const in Hrl at 1.
now rewrite srng_mul_1_l in Hrl.
Qed.

End in_ring.
