(* Lemma 2.1 of the proof of the sensitivity conjecture *)

(* Given a n×n matrix A, a principal submatrix of A is obtained by
   deleting the same set of rows and columns from A. *)

(* Lemma 2.1. (Cauchy’s Interlace Theorem) Let A be a symmetric n×n
   matrix, and B be a m×m principal submatrix of A, for some m < n.
   If the eigenvalues of A are λ1 ≥ λ2 ≥ ... ≥ λn, and the eigenvalues
   of B are μ1 ≥ μ2 ≥ ... ≥ μm, then for all 1 ≤ i ≤ m,
     λi ≥ μi ≥ λ_{i-n+m}
 *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import Init.Nat List List.ListNotations.
Require Import Permutation Sorted.

Require Import Misc MyVector Matrix Determinant Comatrix.
Require Import RingLike.
Require Import IterAdd.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

Definition is_symm_mat (A : matrix T) :=
  is_square_matrix A = true ∧
  ∀ i j, i < mat_nrows A → j < mat_nrows A → mat_el A i j = mat_el A j i.

Definition princ_subm_1 (A : matrix T) k := subm A k k.

Fixpoint mat_princ_subm (A : matrix T) l : matrix T :=
  match l with
  | [] => A
  | i :: l' => mat_princ_subm (subm A i i) l'
  end.

Theorem subm_z : ∀ i j, subm (mk_mat []) i j = mZ 0 0.
Proof.
intros.
unfold subm, mZ; cbn.
now rewrite butn_nil.
Qed.

Definition eigenvalues n M ev :=
  ∀ μ, μ ∈ ev → ∃ V, V ≠ vect_zero n ∧ (M • V = μ × V)%V.

Definition eigenvalues_and_norm_vectors n M ev eV :=
  (∀ V, V ∈ eV → vect_size V = n) ∧
  (∀ i j, i < n → j < n → i ≠ j → nth i ev 0%F ≠ nth j ev 0%F) ∧
  (∀ i, i < n → vect_squ_norm (nth i eV (vect_zero n)) = 1%F) ∧
  ∀ i μ V, i < n →
  μ = nth i ev 0%F
  → V = nth i eV (vect_zero n)
  → (M • V = μ × V)%V.

(* Rayleigh quotient *)

Definition Rayleigh_quotient (M : matrix T) (x : vector T) :=
  (≺ x, M • x ≻ / ≺ x, x ≻)%F.

Arguments Rayleigh_quotient M%M x%V.

Theorem rngl_0_le_squ :
  rngl_has_dec_le = true →
  rngl_has_opp = true →
  rngl_is_ordered = true →
  ∀ n, (0 ≤ n * n)%F.
Proof.
intros Hld Hop Hor *.
rewrite <- (rngl_mul_0_r (or_introl Hop) 0).
destruct (rngl_le_dec Hld 0%F n) as [Hnz| Hnz]. {
  apply rngl_mul_le_compat_nonneg; [ easy | easy | | ]. {
    split; [ now apply rngl_le_refl | easy ].
  } {
    split; [ now apply rngl_le_refl | easy ].
  }
} {
  apply rngl_mul_le_compat_nonpos; [ easy | easy | | ]. {
    split; [ | now apply rngl_le_refl ].
    apply rngl_not_le in Hnz; [ | easy ].
    destruct Hnz as [Hnz| Hnz]; [ | easy ].
    now rewrite <- Hnz; apply rngl_le_refl.
  } {
    split; [ | now apply rngl_le_refl ].
    apply rngl_not_le in Hnz; [ | easy ].
    destruct Hnz as [Hnz| Hnz]; [ | easy ].
    now rewrite <- Hnz; apply rngl_le_refl.
  }
}
Qed.

Definition in_ordered_field :=
  rngl_is_comm = true ∧
  rngl_has_opp = true ∧
  rngl_has_dec_eq = true ∧
  rngl_has_dec_le = true ∧
  rngl_is_integral = true ∧
  rngl_has_inv = true ∧
  rngl_is_ordered = true.

Theorem eq_vect_squ_0 :
  rngl_has_opp = true →
  rngl_has_dec_le = true →
  rngl_is_integral = true →
  rngl_is_ordered = true →
  ∀ v, ≺ v, v ≻ = 0%F → v = vect_zero (vect_size v).
Proof.
(**)
intros Hop Hed Hdo Hor * Hvvz.
unfold vect_dot_mul in Hvvz.
apply vector_eq; [ | now cbn; rewrite repeat_length ].
intros i Hi.
destruct v as (la).
cbn in Hvvz, Hi |-*.
rewrite nth_repeat.
revert i Hi.
induction la as [| a]; intros; [ easy | ].
cbn in Hvvz, Hi.
rewrite rngl_summation_list_cons in Hvvz.
apply rngl_eq_add_0 in Hvvz; [ | easy | | ]; cycle 1. {
  now apply rngl_0_le_squ.
} {
  clear a Hvvz Hi IHla.
  induction la as [| a]. {
    unfold iter_list; cbn.
    now apply rngl_le_refl.
  }
  cbn.
  rewrite rngl_summation_list_cons.
  apply (rngl_le_trans Hor _ (a * a)). {
    now apply rngl_0_le_squ.
  }
  rewrite <- rngl_add_0_r at 1.
  apply rngl_add_le_compat; [ easy | now apply rngl_le_refl | easy ].
}
destruct Hvvz as (Haz, Hvvz).
specialize (IHla Hvvz).
destruct i. {
  apply rngl_integral in Haz; [ | now left | ]. 2: {
    now apply Bool.orb_true_iff; left.
  }
  now destruct Haz.
}
cbn.
apply Nat.succ_lt_mono in Hi.
now apply IHla.
Qed.

Theorem Rayleigh_quotient_mul_scal_l_zero :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ c M,
  Rayleigh_quotient M (c × vect_zero (mat_nrows M)) =
  Rayleigh_quotient M (vect_zero (mat_nrows M)).
Proof.
intros Hop *.
unfold Rayleigh_quotient.
unfold vect_dot_mul; cbn.
unfold vect_dot_mul; cbn.
do 3 rewrite map2_map_r.
do 2 rewrite map2_map_l.
f_equal. {
  rewrite map2_ext_in with (g := λ _ _, 0%F). 2: {
    intros i j Hi Hj.
    apply repeat_spec in Hi; subst i.
    rewrite rngl_mul_0_r; [ | easy ].
    now apply rngl_mul_0_l.
  }
  symmetry.
  rewrite map2_ext_in with (g := λ _ _, 0%F). 2: {
    intros i j Hi Hj.
    apply repeat_spec in Hi; subst i.
    now apply rngl_mul_0_l.
  }
  easy.
} {
  rewrite map2_ext_in with (g := λ _ _, 0%F). 2: {
    intros i j Hi Hj.
    apply repeat_spec in Hi; subst i.
    rewrite rngl_mul_0_r; [ | easy ].
    now apply rngl_mul_0_l.
  }
  symmetry.
  rewrite map2_ext_in with (g := λ _ _, 0%F). 2: {
    intros i j Hi Hj.
    apply repeat_spec in Hi; subst i.
    now apply rngl_mul_0_l.
  }
  easy.
}
Qed.

Theorem RQ_mul_scal_prop :
  in_ordered_field →
  ∀ (M : matrix T) V c,
  is_square_matrix M = true
  → vect_size V = mat_nrows M
  → c ≠ 0%F
  → Rayleigh_quotient M (c × V) = Rayleigh_quotient M V.
Proof.
intros Hof * Hsm Hsr Hcz.
destruct Hof as (Hic & Hop & Hed & Hld & Hdo & Hin & Hor).
destruct (vect_eq_dec Hed V (vect_zero (mat_nrows M))) as [Hvz| Hvz]. {
  subst V; cbn.
  now apply Rayleigh_quotient_mul_scal_l_zero; left.
}
unfold Rayleigh_quotient.
rewrite <- mat_mul_scal_vect_comm; [ | easy | easy | | ]; cycle 1. {
  now apply squ_mat_is_corr.
} {
  now rewrite square_matrix_ncols.
}
rewrite vect_dot_mul_scal_mul_comm; [ | now left | easy ].
rewrite vect_dot_mul_scal_mul_comm; [ | now left | easy ].
rewrite vect_scal_mul_dot_mul_comm; [ | now left ].
rewrite vect_scal_mul_dot_mul_comm; [ | now left ].
do 2 rewrite rngl_mul_assoc.
unfold rngl_div.
rewrite Hin.
rewrite rngl_inv_mul_distr; [ | now left | easy | easy | | ]; cycle 1. {
  intros H.
  apply rngl_integral in H; [ now destruct H | now left | ].
  now apply Bool.orb_true_iff; left.
} {
  intros H.
  apply eq_vect_squ_0 in H; [ | easy | easy | easy | easy ].
  now rewrite Hsr in H.
}
rewrite rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
do 2 rewrite rngl_mul_assoc.
rewrite rngl_mul_inv_l; [ now rewrite rngl_mul_1_l | easy | ].
intros H; apply Hcz.
apply rngl_integral in H; [ now destruct H| now left | ].
now apply Bool.orb_true_iff; left.
Qed.

Theorem Rayleigh_quotient_of_eigenvector :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_dec_le = true →
  rngl_is_integral = true →
  rngl_has_inv = true →
  rngl_is_ordered = true →
  ∀ (M : matrix T) V μ,
  V ≠ vect_zero (vect_size V)
  → (M • V = μ × V)%V
  → Rayleigh_quotient M V = μ.
Proof.
intros Hic Hop Hii Hdo Hor Hdl * Hvz Hmv.
unfold Rayleigh_quotient.
rewrite Hmv.
rewrite vect_dot_mul_scal_mul_comm; [ | now left | easy ].
apply rngl_mul_div_l; [ now left | ].
intros H.
now apply eq_vect_squ_0 in H.
Qed.

Definition is_orthogonal_matrix (M : matrix T) :=
  (mat_transp M * M)%M = mI (mat_nrows M).

(* diagonal matrix with diagonal d being given *)

Definition mat_with_diag n d :=
  mk_mat
    (map (λ i, map (λ j, if i =? j then nth i d 0%F else 0%F) (seq 0 n))
       (seq 0 n)).

(* matrix with columns given as list of vectors *)

Definition mat_with_vect n Vl :=
  mk_mat
    (map (λ i, map (λ j, vect_el (nth j Vl (vect_zero n)) i) (seq 0 n))
       (seq 0 n)).

(* In the real case, the symmetric matrix M is diagonalisable in the
   sense that there exists an orthogonal matrix U (the columns of which
   are eigenvectors) and a diagonal matrix D the coefficients of which
   are eigenvalues μ_i such that
      M = U . D . U^t *)

Theorem diagonalized_matrix_prop_1 :
  rngl_is_comm = true →
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ n (M : matrix T) ev eV D U,
  is_symm_mat M
  → mat_nrows M = n
  → eigenvalues_and_norm_vectors n M ev eV
  → length eV = n
  → (∀ V, V ∈ eV → vect_size V = n)
  → D = mat_with_diag n ev
  → U = mat_with_vect n eV
  → (M * U = U * D)%M.
Proof.
intros Hic Hos * Hsy Hrn Hvv Hlev Hevn Hd Ho.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  unfold mat_with_vect in Ho; cbn in Ho.
  unfold mat_with_diag in Hd; cbn in Hd.
  rewrite Ho, Hd.
  destruct M as (ll); cbn.
  cbn in Hrn.
  now apply length_zero_iff_nil in Hrn; cbn in Hrn; subst ll.
}
apply Nat.neq_0_lt_0 in Hnz.
subst U D; cbn.
remember (mat_with_vect n eV) as U eqn:Hmo.
remember (mat_with_diag n ev) as D eqn:Hmd.
move D before U.
destruct Hvv as (HeV & Hall_diff & Hall_norm_1 & Hvv).
unfold is_symm_mat in Hsy.
assert (Hus : is_square_matrix U = true). {
  rewrite Hmo; cbn.
  unfold mat_with_vect; cbn.
  apply is_scm_mat_iff; cbn.
  unfold mat_ncols; cbn.
  rewrite List_map_seq_length.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  rewrite List_map_seq_length.
  split; [ easy | ].
  intros l Hl.
  apply in_map_iff in Hl.
  destruct Hl as (x & Hl & Hx).
  now rewrite <- Hl, List_map_seq_length.
}
assert (Hdc : is_correct_matrix D = true). {
  rewrite Hmd; cbn.
  unfold mat_with_diag; cbn.
  apply is_scm_mat_iff; cbn.
  unfold mat_ncols; cbn.
  rewrite List_map_seq_length.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  rewrite List_map_seq_length.
  split; [ easy | ].
  intros l Hl.
  apply in_map_iff in Hl.
  destruct Hl as (x & Hl & Hx).
  now rewrite <- Hl, List_map_seq_length.
}
apply matrix_eq; cycle 1. {
  apply mat_mul_is_corr. {
    now apply squ_mat_is_corr.
  } {
    now apply squ_mat_is_corr.
  }
  rewrite Hmo; cbn.
  rewrite List_map_seq_length.
  now apply Nat.neq_0_lt_0.
} {
  apply mat_mul_is_corr; [ now apply squ_mat_is_corr | easy | ].
  rewrite Hmd; cbn.
  rewrite List_map_seq_length.
  now apply Nat.neq_0_lt_0.
} {
  rewrite Hmo; cbn.
  now do 3 rewrite List_map_seq_length.
} {
  unfold mat_ncols; cbn.
  rewrite (List_map_hd 0); [ | now rewrite seq_length, Hrn ].
  rewrite (List_map_hd 0). 2: {
    rewrite seq_length, Hmo; cbn.
    now rewrite List_map_seq_length.
  }
  do 2 rewrite List_map_seq_length.
  rewrite Hmo, Hmd; unfold mat_ncols; cbn.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  now do 2 rewrite List_map_seq_length.
}
unfold mat_ncols; cbn.
rewrite List_map_seq_length, Hrn, Hmd.
rewrite (List_map_hd 0). 2: {
  rewrite seq_length.
  rewrite Hmo; cbn.
  now rewrite List_map_seq_length.
}
rewrite List_map_seq_length.
intros i j Hi Hj.
unfold mat_ncols, mat_with_diag in Hj; cbn in Hj.
rewrite (List_map_hd 0) in Hj; [ | now rewrite seq_length ].
rewrite List_map_seq_length in Hj.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  rewrite Hmo; unfold mat_ncols; cbn.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  now rewrite List_map_seq_length.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  rewrite Hmo; cbn.
  now rewrite List_map_seq_length.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  unfold mat_ncols; cbn.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  now rewrite List_map_seq_length.
}
rewrite seq_nth; [ | easy ].
rewrite seq_nth. 2: {
  rewrite Hmo; unfold mat_ncols; cbn.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  now rewrite List_map_seq_length.
}
rewrite seq_nth. 2: {
  rewrite Hmo; cbn.
  now rewrite List_map_seq_length.
}
rewrite seq_nth. 2: {
  unfold mat_ncols, mat_with_diag; cbn.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  now rewrite List_map_seq_length.
}
cbn.
rewrite <- Hmd.
unfold mat_mul_el.
symmetry.
rewrite (rngl_summation_split j). 2: {
  split; [ easy | ].
  rewrite square_matrix_ncols; [ | easy ].
  rewrite Hmo; cbn.
  rewrite List_map_seq_length.
  apply -> Nat.succ_le_mono; flia Hj.
}
rewrite rngl_summation_split_last; [ | easy ].
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite Hmo; cbn.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hk Hj ].
  rewrite seq_nth; [ | flia Hk Hj ].
  rewrite seq_nth; [ | easy ].
  cbn.
  rewrite Hmd; cbn.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hk Hj ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | flia Hk Hj ].
  rewrite seq_nth; [ | easy ].
  cbn; rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (k - 1) j) as [Hkj| Hkj]; [ flia Hk Hkj | ].
  now apply rngl_mul_0_r.
}
rewrite rngl_add_0_l.
replace (mat_ncols U) with (mat_ncols M). 2: {
  rewrite square_matrix_ncols; [ | easy ].
  rewrite Hrn.
  rewrite Hmo; unfold mat_ncols; cbn.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  now rewrite List_map_seq_length.
}
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite square_matrix_ncols in Hk; [ | easy ].
  rewrite Hrn in Hk.
  rewrite Hmd; cbn.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hk Hj ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | flia Hk Hj ].
  rewrite seq_nth; [ | easy ].
  cbn; rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ flia Hk Hkj | ].
  now apply rngl_mul_0_r.
}
rewrite rngl_add_0_r.
rewrite Hmd; cbn - [ iter_seq ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ cbn | easy ].
rewrite Nat.eqb_refl.
rewrite Hmo.
cbn - [ iter_seq ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite seq_nth; [ | easy ].
cbn - [ iter_seq ].
erewrite rngl_summation_eq_compat. 2: {
  intros u (_, Hu).
  rewrite square_matrix_ncols in Hu; [ | easy ].
  rewrite Hrn in Hu.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hu Hnz ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | flia Hu Hnz ].
  now cbn.
}
cbn.
specialize (Hvv j (nth j ev 0%F) (nth j eV (vect_zero n))) as H1.
specialize (H1 Hj eq_refl eq_refl).
remember (nth j ev 0%F) as μ eqn:Hμ.
remember (nth j eV (vect_zero n)) as V eqn:Hv.
symmetry.
apply (f_equal (λ x, vect_el x i)) in H1.
cbn - [ iter_seq ] in H1.
rewrite (List_map_nth' []) in H1; [ | now rewrite fold_mat_nrows, Hrn ].
rewrite (List_map_nth' 0%F) in H1. 2: {
  rewrite fold_vect_size.
  rewrite Hevn; [ easy | ].
  rewrite Hv.
  apply nth_In.
  now rewrite Hlev.
}
rewrite fold_vect_el in H1.
rewrite rngl_mul_comm in H1; [ | easy ].
cbn in H1.
rewrite <- H1.
unfold mat_el.
remember (nth i (mat_list_list M) []) as l eqn:Hl.
erewrite rngl_summation_eq_compat. 2: {
  intros u Hu.
  replace (nth u l 0%F) with (vect_el (mk_vect l) u) by easy.
  easy.
}
remember (mk_vect l) as W eqn:HW.
subst l.
rewrite vect_dot_mul_dot_mul'; [ | easy ].
unfold vect_dot_mul'.
rewrite (Hevn V). 2: {
  rewrite Hv; cbn.
  apply nth_In.
  now rewrite Hlev.
}
replace (vect_size W) with n. 2: {
  rewrite HW; cbn; symmetry.
  destruct Hsy as (Hsm, Hsy).
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr, Hcl).
  rewrite Hcl; [ easy | ].
  apply nth_In.
  now rewrite fold_mat_nrows, Hrn.
}
rewrite Nat.min_id.
rewrite square_matrix_ncols; [ | easy ].
now rewrite Hrn.
Qed.

Theorem mat_mul_vect_dot_vect :
  rngl_is_comm = true →
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ (M : matrix T) U V,
  is_square_matrix M = true
  → vect_size U = mat_nrows M
  → vect_size V = mat_nrows M
  → ≺ M • U, V ≻ = ≺ U, M⁺ • V ≻.
Proof.
intros Hic Hos * Hsm Hur Hvr.
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  rewrite Hrz in Hur, Hvr.
  destruct M as (ll).
  destruct U as (lu).
  destruct V as (lv); cbn.
  cbn in Hur, Hvr, Hrz.
  apply length_zero_iff_nil in Hur, Hvr, Hrz.
  now subst lu lv ll.
}
rewrite vect_dot_mul_dot_mul'; [ | easy ].
rewrite vect_dot_mul_dot_mul'; [ | easy ].
unfold vect_dot_mul'.
rewrite Hur, Hvr.
cbn.
do 3 rewrite map_length.
rewrite seq_length.
rewrite fold_mat_nrows.
rewrite square_matrix_ncols; [ | easy ].
rewrite Nat.min_id.
destruct M as (ll).
destruct U as (lu).
destruct V as (lv); cbn.
cbn in Hur, Hvr, Hrz.
rewrite map_map.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite (List_map_nth' []). 2: {
   apply Nat.min_glb_lt_iff with (m := length lv).
   rewrite Hvr, Nat.min_id.
   flia Hi Hrz.
  }
  rewrite vect_dot_mul_dot_mul'; [ | easy ].
  unfold vect_dot_mul'; cbn.
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr, Hcl).
  rewrite (Hcl (nth i ll [])). 2: {
    cbn; apply nth_In; flia Hi Hrz.
  }
  cbn; rewrite Hur, Nat.min_id.
  rewrite rngl_mul_summation_distr_r; [ | easy ].
  easy.
}
cbn.
rewrite rngl_summation_summation_exch'.
apply rngl_summation_eq_compat.
intros i (_, Hi).
erewrite rngl_summation_eq_compat. 2: {
  intros j (_, Hj).
  rewrite rngl_mul_mul_swap; [ | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  easy.
}
cbn.
rewrite <- rngl_mul_summation_distr_l; [ | easy ].
f_equal.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi Hrz ].
rewrite vect_dot_mul_dot_mul'; [ | easy ].
unfold vect_dot_mul'; cbn.
rewrite List_map_seq_length.
rewrite Hvr, Nat.min_id.
eapply rngl_summation_eq_compat.
intros j (_, Hj).
f_equal.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj Hrz ].
rewrite seq_nth; [ | flia Hi Hrz ].
rewrite seq_nth; [ | flia Hj Hrz ].
easy.
Qed.

Theorem mat_with_vect_is_square : ∀ n vl,
  is_square_matrix (mat_with_vect n vl) = true.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply Nat.neq_0_lt_0 in Hnz.
apply is_scm_mat_iff.
split. {
  unfold mat_ncols; cbn.
  rewrite List_map_seq_length.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  now rewrite List_map_seq_length.
} {
  unfold mat_ncols; cbn.
  rewrite List_map_seq_length.
  intros l Hl.
  apply in_map_iff in Hl.
  destruct Hl as (x & Hxl & Hx).
  apply in_seq in Hx.
  rewrite <- Hxl.
  now rewrite List_map_seq_length.
}
Qed.

Theorem mat_with_vect_is_corr : ∀ n vl,
  is_correct_matrix (mat_with_vect n vl) = true.
Proof.
intros.
apply squ_mat_is_corr, mat_with_vect_is_square.
Qed.

Theorem mat_with_vect_nrows : ∀ n vl, mat_nrows (mat_with_vect n vl) = n.
Proof.
intros.
now cbn; rewrite List_map_seq_length.
Qed.

Theorem mat_with_vect_ncols : ∀ n vl, mat_ncols (mat_with_vect n vl) = n.
Proof.
intros.
unfold mat_ncols; cbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply Nat.neq_0_lt_0 in Hnz.
rewrite (List_map_hd 0); [ | now rewrite seq_length ].
now rewrite List_map_seq_length.
Qed.

Theorem mat_with_vect_el : ∀ n lv i j,
  i < n
  → j < n
  → mat_el (mat_with_vect n lv) i j = vect_el (nth j lv (vect_zero n)) i.
Proof.
intros * Hin Hjn; cbn.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite seq_nth; [ | easy ].
easy.
Qed.

Theorem fold_vect_dot_mul' : ∀ U V,
  ∑ (i = 0, min (vect_size U) (vect_size V) - 1), vect_el U i * vect_el V i =
  vect_dot_mul' U V.
Proof. easy. Qed.

(* trying to prove that det(AB)=det(A)det(B) *)
(* there are several proofs of that, none of them being simple *)
(* here, trying to prove it by the Cauchy-Binet Formula *)
(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)

(* det(AB)= ∑ 1≤j1<j2<⋯<jm≤n det(Aj1j2…jm)det(Bj1j2…jm)
   where A is a m×n matrix, B a n×m matrix
   Aj1j2…jm denotes the m×m matrix consisting of columns j1,j2,…,jm of A.
   Bj1j2…jm denotes the m×m matrix consisting of rows j1,j2,…,jm of B. *)

(* all lists [j1;j2;...jm] such that 0≤j1<j2<...<jm<n *)
Fixpoint ordered_tuples (m n : nat) : list (list nat) :=
  match m with
  | 0 => [[]]
  | S m' =>
      let ot := ordered_tuples m' n in
      List.concat
        (map
           (λ i,
            map (λ l, i :: map (Nat.add (S i)) l)
              (filter (forallb (λ j, Nat.ltb (S (i + j)) n)) ot))
           (seq 0 n))
  end.

Compute (let n := 5 in map (λ i, let l := ordered_tuples i n in length l) (seq 0 (n + 3))).
Compute (let n := 5 in map (λ i, let l := ordered_tuples i n in (length l, l)) (seq 0 (n + 3))).

...

(* submatrix of A with list cols jl *)
(* phony definition for the moment... *)
Definition mat_with_cols (jl : list nat) (A : matrix T) := A.

(* submatrix of B with list rows jl *)
(* phony definition for the moment... *)
Definition mat_with_rows (jl : list nat) (B : matrix T) := B.

Theorem cauchy_binet_formula : ∀ m n A B,
  is_correct_matrix A = true
  → is_correct_matrix B = true
  → mat_nrows A = m
  → mat_ncols A = n
  → mat_nrows B = n
  → mat_ncols B = m
  → det (A * B) =
     ∑ (jl ∈ ordered_tuples m n),
     det (mat_with_cols jl A) * det (mat_with_rows jl B).

...

(* other attempts to prove det(AB)=det(A)det(B) *)

(*
Theorem determinant_mul : ∀ A B, det (A * B) = (det A * det B)%F.
Proof.
intros.
(* essai avec les formes multilinéaires alternées...

trouvé sur le web
(https://les-mathematiques.net/vanilla/index.php?p=discussion/1339028#Comment_1339028)

 Il vaut mieux éviter à tout prix la formule explicite. On peut
 utiliser la méthode de Gauss, ou bien utiliser le fait que
 l'application B↦det(AB) est multilinéaire alternée, et donc est un
 multiple de B↦detB

 Il faut d'abord avoir établi que l'espace des formes multilinéaires
 alternées est de dimension 1 et que le déterminant est l'unique telle
 forme qui vaut 1 en l'identité. Une fois ceci acquis, on en déduit
 que det(AB)=αdetB où α est un scalaire qui ne dépend que de A. On le
 trouve en prenant B=I, ce qui donne detA=αdetI=α.
*)
Check determinant_multilinear.
Check determinant_alternating.
...
*)

(* very interesting, too, contains several proofs of det(AB)=det(A)det(B)
https://proofwiki.org/wiki/Determinant_of_Matrix_Product
*)

(* stuff to play with "ring_simplify" below *)
Context {Hic : @rngl_is_comm T ro rp = true}.
Context {Hop : @rngl_has_opp T ro = true}.
Require Import Ring.
Add Ring rngl_ring : (@rngl_ring_theory T ro rp Hic Hop).
(* end stuff *)

Theorem determinant_mul : in_charac_0_field →
  ∀ A B,
  is_square_matrix A = true
  → is_square_matrix B = true
  → mat_nrows A = mat_nrows B
  → det (A * B) = (det A * det B)%F.
Proof.
intros Hif * Hasm Hbsm Hrab.
(* essai avec le déterminant défini par permutations *)
assert (Habsm : is_square_matrix (A * B) = true). {
  now apply squ_mat_mul_is_squ.
}
remember (mat_nrows A) as n eqn:Hra.
rename Hrab into Hrb.
symmetry in Hra, Hrb.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold det; cbn.
  move Hnz at top; subst n; cbn.
  rewrite Hra, Hrb; cbn.
  symmetry; apply rngl_mul_1_l.
}
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite mat_mul_nrows.
unfold det'.
Require Import IterMul Signature PermutSeq.
rewrite Hra, Hrb.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite mat_el_mul; cycle 1. {
      rewrite mat_mul_nrows, Hra.
      flia Hj.
    } {
      rewrite mat_mul_ncols; [ | rewrite Hra; flia Hj ].
      rewrite square_matrix_ncols; [ | easy ].
      rewrite Hrb.
      apply canon_sym_gr_list_ub; [ | flia Hj ].
      specialize (fact_neq_0 n) as Hfnz.
      flia Hi Hfnz.
    }
    rewrite square_matrix_ncols; [ | easy ].
    rewrite Hra.
    easy.
  }
  cbn.
  easy.
}
cbn.
(*1*)
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j (_, Hj).
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j (_, Hj).
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
rewrite rngl_mul_comm; [ | now destruct Hif ].
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j (_, Hj).
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
rewrite rngl_mul_comm; [ | now destruct Hif ].
symmetry.
(*
Noting
   ε(i) = signature of the i-th permutation in the canonic symmetric group
   σ(i,j) = j-th element of the i-th permutation in the canonic sym gr
We have to prove that
  ∑ (i = 0, n!-1), ε(i) ∏ (j = 0, n-1), ∑ (k = 0, n-1), a(j,k) * b(k,σ(i,j)) =
  ∑ (i = 0, n! - 1), ε(i) ∏ (j = 0, n-1), a(j,σ(i,j)) *
  ∑ (i = 0, n! - 1), ε(i) ∏ (j = 0, n-1), b(j,σ(i,j))
The problem is that the lhs contains
  n!*n^n terms
But the rhs contains
  n!*n! terms
Some terms of the lhs must cancel each other. But which ones?
*)
destruct n; [ easy | ].
destruct n. {
  cbn - [ "/" ff_app ].
  unfold ε.
  do 3 rewrite rngl_summation_only_one.
  do 7 rewrite rngl_product_only_one.
  rewrite rngl_summation_only_one; cbn.
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  now do 3 rewrite rngl_mul_1_l.
}
destruct n. {
  unfold iter_seq, iter_list; cbn.
  do 7 rewrite rngl_add_0_l.
  do 6 rewrite rngl_mul_1_l.
  unfold ε, iter_seq, iter_list; cbn.
  do 8 rewrite rngl_mul_1_l.
  rewrite rngl_add_0_r.
  rewrite rngl_sub_0_r; [ | now destruct Hif; left ].
  rewrite rngl_add_sub; [ | now destruct Hif; left ].
  rewrite rngl_mul_1_l.
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  remember (mat_el A) as a eqn:Ha.
  remember (mat_el B) as b eqn:Hb.
  move b before a.
(**)
  ring_simplify.
(*
  rewrite rngl_mul_1_l.
  do 2 rewrite rngl_mul_1_l.
  unfold rngl_sub.
  replace rngl_has_opp with true by now destruct Hif.
  rewrite rngl_mul_1_r.
  rewrite rngl_add_0_l.
  rewrite rngl_mul_opp_l; [ | now destruct Hif ].
  rewrite rngl_mul_opp_l; [ | now destruct Hif ].
  rewrite rngl_mul_opp_l; [ | now destruct Hif ].
  do 3 rewrite rngl_mul_1_l.
  rewrite fold_rngl_sub; [ | now destruct Hif ].
  rewrite fold_rngl_sub; [ | now destruct Hif ].
  rewrite fold_rngl_sub; [ | now destruct Hif ].
*)
...
(*
  (a 0 0 * b 0 0 + a 0 1 * b 1 0) * (a 1 0 * b 0 1 + a 1 1 * b 1 1) -
  (a 0 0 * b 0 1 + a 0 1 * b 1 1) * (a 1 0 * b 0 0 + a 1 1 * b 1 0) =

  (a 0 0 * a 1 1 - a 0 1 * a 1 0) * (b 0 0 * b 1 1 - b 0 1 * b 1 0)
*)
...1
rewrite rngl_summation_mul_summation; [ | now destruct Hif; left ].
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite <- rngl_mul_summation_distr_l; [ | now destruct Hif; left ].
  easy.
}
symmetry.
apply rngl_summation_eq_compat.
intros i (_, Hi).
rewrite <- rngl_mul_assoc.
f_equal.
symmetry.
rewrite rngl_mul_summation_distr_l; [ | now destruct Hif; left ].
symmetry.
rewrite rngl_product_shift; [ | flia Hnz ].
rewrite rngl_product_summation_distr; [ | destruct Hif; now left ].
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  erewrite rngl_product_eq_compat. 2: {
    intros k Hk.
    now rewrite (Nat.add_comm 1 k), Nat.add_sub.
  }
  easy.
}
cbn.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite rngl_mul_assoc.
  rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
  rewrite <- rngl_product_mul_distr; [ | now destruct Hif ].
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros k Hk.
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  easy.
}
symmetry.
(* bizarre: n^n termes vs n! termes *)
destruct (Nat.eq_dec n 2) as [Hn2| Hn2]. {
  move Hn2 at top; subst n.
  cbn - [ "/" "mod" Nat.pow "-" canon_sym_gr_list ].
  replace (2 - 1) with 1 by easy.
  replace (2 ^ 2 - 1) with 3 by easy.
  cbn in Hi.
  cbn - [ "/" "mod" ].
  unfold iter_seq, iter_list.
  cbn - [ "/" "mod" ].
  do 2 rewrite rngl_add_0_l.
  do 6 rewrite rngl_mul_1_l.
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.mod_0_l; [ | easy ].
  rewrite Nat.mod_0_l; [ | easy ].
  do 4 rewrite Nat.div_1_r.
  rewrite Nat.div_same; [ | easy ].
  rewrite Nat.mod_same; [ | easy ].
  rewrite Nat.mod_small; [ | flia ].
  cbn.
  unfold ε; cbn.
  unfold iter_seq, iter_list; cbn.
  do 8 rewrite rngl_mul_1_l.
  repeat rewrite rngl_add_0_r.
  rewrite rngl_sub_0_r; [ | now destruct Hif; left ].
  rewrite rngl_mul_1_l.
  rewrite rngl_mul_1_r.
  rewrite rngl_add_sub; [ | now destruct Hif; left ].
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  rewrite rngl_mul_1_l.
  rewrite rngl_mul_1_r.
  destruct (Nat.eq_dec i 1) as [Hi1| Hi1]. {
    subst i.
    cbn.
...
intros.
(* essai avec le déterminant défini par récurrence *)
cbn.
rewrite List_map_seq_length.
unfold det.
remember (mat_nrows A) as n eqn:Hra.
symmetry in Hra.
enough (Hrb : mat_nrows B = n).
...
intros.
rewrite laplace_formula_on_rows with (i := 0).
rewrite laplace_formula_on_rows with (i := 0).
rewrite laplace_formula_on_rows with (i := 0).
rewrite mat_mul_ncols.
(* déjà, ce serait pas mal si on  prouvait que com(A*B)=com(A)*com(B) *)
(* mais je viens de laisser tomber cette idée parce que, de toutes façons,
   la définition de com fait déjà intervenir det : ça boucle ! *)
...
Check comatrix_mul.
...
intros.
Check @laplace_formula_on_rows.
(* https://www.youtube.com/watch?v=-CySi7uauCg *)
...
rewrite det_is_det_by_canon_permut.
rewrite det_is_det_by_canon_permut.
rewrite det_is_det_by_canon_permut.
cbn; rewrite List_map_seq_length.
unfold determinant'.
...
Check laplace_formula_on_rows.
Check laplace_formula_on_cols.
Search comatrix.
...
Require Import IterMul.
Search determinant.
...
intros.
unfold determinant; cbn.
rewrite List_map_seq_length.
Print determinant_loop.
...
*)

(* https://math.stackexchange.com/questions/82467/eigenvectors-of-real-symmetric-matrices-are-orthogonal *)

Theorem for_symm_squ_mat_eigen_vect_mat_is_ortho :
  rngl_is_comm = true →
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_has_dec_eq = true →
  rngl_has_inv = true →
  ∀ n (M : matrix T) ev eV A,
  is_symm_mat M
  → mat_nrows M = n
  → eigenvalues_and_norm_vectors n M ev eV
  → A = mat_with_vect n eV
  → (A⁺ * A = mI n)%M.
Proof.
intros Hic Hos Heq Hii * Hsy Hr Hvv Hm.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now move Hnz at top; subst n A | ].
rewrite Hm.
apply matrix_eq; cycle 1. {
  apply mat_mul_is_corr. {
    apply mat_transp_is_corr.
    apply mat_with_vect_is_corr.
  } {
    apply mat_with_vect_is_corr.
  }
  now cbn; rewrite List_map_seq_length.
} {
  apply mI_is_correct_matrix.
} {
  cbn; do 3 rewrite List_map_seq_length.
  apply mat_with_vect_ncols.
} {
  rewrite mI_ncols.
  rewrite mat_mul_ncols. 2: {
    now rewrite mat_transp_nrows, mat_with_vect_ncols.
  }
  apply mat_with_vect_ncols.
}
rewrite mat_mul_nrows.
rewrite mat_transp_nrows.
rewrite mat_with_vect_ncols.
rewrite mI_ncols.
intros * Hi Hj.
rewrite mat_el_mul; cycle 1. {
  now rewrite mat_mul_nrows, mat_transp_nrows, mat_with_vect_ncols.
} {
  rewrite mat_mul_ncols. 2: {
    now rewrite mat_transp_nrows, mat_with_vect_ncols.
  }
  now rewrite mat_with_vect_ncols.
}
rewrite mat_transp_ncols.
rewrite mat_with_vect_ncols.
apply Nat.eqb_neq in Hnz; rewrite Hnz.
rewrite mat_with_vect_nrows.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite mat_transp_el; [ | apply mat_with_vect_is_corr ].
  rewrite mat_with_vect_el; [ | flia Hk Hi | easy ].
  rewrite mat_with_vect_el; [ | flia Hk Hi | easy ].
  easy.
}
cbn.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite seq_nth; [ | easy ].
cbn.
remember (nth i eV (vect_zero n)) as vi eqn:Hvi.
remember (nth j eV (vect_zero n)) as vj eqn:Hvj.
move vj before vi.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j; clear Hj.
  rewrite δ_diag.
  destruct Hvv as (Hev & Hall_diff & Hall_norm_1 & Hvv).
  specialize (Hall_norm_1 i Hi) as H1.
  unfold vect_squ_norm in H1.
  rewrite <- Hvi in H1.
  rewrite vect_dot_mul_dot_mul' in H1; [ | easy ].
  unfold vect_dot_mul' in H1.
  rewrite Nat.min_id in H1.
  destruct (lt_dec i (length eV)) as [Hie| Hie]. 2: {
    apply Nat.nlt_ge in Hie.
    rewrite <- H1.
    rewrite nth_overflow in Hvi; [ subst vi | easy ].
    unfold vect_zero; cbn.
    rewrite repeat_length.
    apply rngl_summation_eq_compat.
    intros j Hj.
    f_equal.
    rewrite Hvj; cbn.
    unfold vect_el; cbn.
    rewrite List_nth_repeat.
    rewrite <- if_ltb_lt_dec.
    rewrite Tauto.if_same.
    rewrite nth_overflow with (n := i); [ | easy ].
    now cbn; rewrite nth_repeat.
  }
  rewrite Hev in H1. 2: {
    rewrite Hvi.
    now apply nth_In.
  }
  now rewrite Hvj, <- Hvi.
} {
  rewrite δ_ndiag; [ | easy ].
  destruct Hvv as (Hev & Hall_diff & Hall_norm_1 & Hvv).
  destruct (lt_dec i (length eV)) as [Hie| Hie]. 2: {
    apply Nat.nlt_ge in Hie.
    apply all_0_rngl_summation_0.
    intros k Hk.
    rewrite Hvi.
    rewrite nth_overflow; [ cbn | easy ].
    rewrite nth_repeat.
    now apply rngl_mul_0_l.
  }
  destruct (lt_dec j (length eV)) as [Hje| Hje]. 2: {
    apply Nat.nlt_ge in Hje.
    apply all_0_rngl_summation_0.
    intros k Hk.
    rewrite Hvj.
    rewrite nth_overflow; [ cbn | easy ].
    rewrite nth_repeat.
    now apply rngl_mul_0_r.
  }
  replace n with (min (vect_size vi) (vect_size vj)). 2: {
    rewrite Hev; [ | now rewrite Hvi; apply nth_In ].
    rewrite Hev; [ | now rewrite Hvj; apply nth_In ].
    apply Nat.min_id.
  }
  rewrite fold_vect_dot_mul'.
  rewrite <- vect_dot_mul_dot_mul'; [ | easy ].
  specialize (mat_mul_vect_dot_vect Hic Hos M vi vj) as H1.
  destruct Hsy as (Hsm, Hsy).
  specialize (H1 Hsm).
  rewrite Hr in H1.
  assert (H : vect_size vi = n). {
    rewrite Hvi, Hev; [ easy | ].
    now apply nth_In.
  }
  specialize (H1 H); clear H.
  assert (H : vect_size vj = n). {
    rewrite Hvj, Hev; [ easy | ].
    now apply nth_In.
  }
  specialize (H1 H); clear H.
  (* H1 : ≺ M • vi, vj ≻ = ≺ vi, M⁺ • vj ≻ *)
  specialize (Hvv i (nth i ev 0%F) vi Hi eq_refl Hvi) as H2.
  rewrite H2 in H1.
  clear H2.
  replace (M⁺)%M with M in H1. 2: {
    unfold mat_transp; cbn.
    rewrite square_matrix_ncols; [ rewrite Hr | easy ].
    destruct M as (ll); cbn in Hr, Hsy |-*; f_equal.
    rewrite (List_map_nth_seq ll []) at 1.
    rewrite Hr.
    apply map_ext_in.
    intros i' Hi'; apply in_seq in Hi'.
    rewrite (List_map_nth_seq (nth i' ll []) 0%F) at 1.
    apply is_scm_mat_iff in Hsm; cbn in Hsm.
    destruct Hsm as (Hcr, Hcl).
    rewrite Hcl; [ rewrite Hr | now apply nth_In; rewrite Hr ].
    apply map_ext_in.
    intros j' Hj'; apply in_seq in Hj'.
    now apply Hsy; rewrite Hr.
  }
  specialize (Hvv j (nth j ev 0%F) vj Hj eq_refl Hvj) as H2.
  rewrite H2 in H1.
  clear H2.
  rewrite vect_scal_mul_dot_mul_comm in H1; [ | easy ].
  rewrite vect_dot_mul_scal_mul_comm in H1; [ | easy | easy ].
  destruct (rngl_eq_dec Heq (≺ vi, vj ≻) 0%F) as [Hvvij| Hvvij]; [ easy | ].
  exfalso.
  apply rngl_mul_cancel_r in H1; [ | now left | easy ].
  revert H1.
  now apply Hall_diff.
}
Qed.

Inspect 1.

(* can I prove, with that, that A⁻¹ = A⁺ ? *)

...

Theorem diagonalized_matrix_prop : in_charac_0_field →
  ∀ n (M : matrix T) ev eV D U,
  is_symm_mat M
  → mat_nrows M = n
  → eigenvalues_and_norm_vectors n M ev eV
  → length eV = n
  → (∀ V, V ∈ eV → vect_size V = n)
  → D = mat_with_diag n ev
  → U = mat_with_vect n eV
  → (M = U * D * U⁻¹)%M.
Proof.
intros Hif * Hsy Hrn Hvv Hlev Hevn Hd Ho.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  unfold mat_with_vect in Ho; cbn in Ho.
  unfold mat_with_diag in Hd; cbn in Hd.
  rewrite Ho, Hd.
  destruct M as (ll); cbn.
  cbn in Hrn.
  now apply length_zero_iff_nil in Hrn; cbn in Hrn; subst ll.
}
specialize diagonalized_matrix_prop_1 as H1.
assert (H : rngl_is_comm = true) by now destruct Hif.
specialize (H1 H); clear H.
assert (H : rngl_has_opp = true) by now destruct Hif.
specialize (H1 (or_introl H)); clear H.
specialize (H1 n M ev eV D U Hsy Hrn Hvv Hlev Hevn Hd Ho).
generalize H1; intros H1v.
apply (f_equal (λ A, (A * U⁻¹)%M)) in H1.
rewrite <- mat_mul_assoc in H1; [ | now destruct Hif | | | ]; cycle 1. {
  now rewrite Ho, mat_with_vect_nrows.
} {
  now rewrite Ho, mat_with_vect_ncols.
} {
  rewrite Ho, mat_with_vect_nrows.
  rewrite square_matrix_ncols; [ easy | now destruct Hsy ].
}
rewrite mat_mul_inv_r in H1; [ | easy | | ]; cycle 1. {
  rewrite Ho.
  apply mat_with_vect_is_square.
} {
  rewrite Ho.
(* tout un programme ! *)
Search mat_with_vect.
(* for_symm_squ_mat_eigen_vect_mat_is_ortho seems to say that U⁻¹=U⁺ and,
   therefore their determinants are equal, therefore equal to det(U) *)
(* or I can also "f_equal (λ A, (A * U⁺)%M)" instead of U⁻¹ and use
   for_symm_squ_mat_eigen_vect_mat_is_ortho with version "U * U⁺ = I" *)
(* I don't know *)
...
  rewrite det_is_det_by_canon_permut; [ | easy | ]. 2: {
    apply mat_with_vect_is_square.
  }
Require Import IterMul.
Require Import PermutSeq Signature.
unfold determinant'.
rewrite mat_with_vect_nrows.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite mat_with_vect_el; [ | flia Hj | ]. 2: {
      apply canon_sym_gr_list_ub; [ | flia Hj ].
      specialize (fact_neq_0 n) as H2.
      flia Hi H2.
    }
    easy.
  }
  easy.
}
cbn.
Print determinant'.
...
unfold eigenvalues_and_norm_vectors in Hvv.
...
  unfold mat_with_vect; cbn.
  rewrite List_map_seq_length.
  cb
...

Theorem mat_mul_vect_size : ∀ M V, vect_size (M • V) = mat_nrows M.
Proof.
intros; cbn.
now rewrite map_length.
Qed.

(* https://people.orie.cornell.edu/dpw/orie6334/Fall2016/lecture4.pdf *)
(* https://en.wikipedia.org/wiki/Min-max_theorem#Cauchy_interlacing_theorem *)

(* changing variable x as y = O⁺.x, the Rayleigh quotient R(M,x)
   is equal to
      Σ (i = 1, n), μ_i * y_i ^ 2 / Σ (i = 1, n), y_i ^ 2 *)

(* https://en.wikipedia.org/wiki/Rayleigh_quotient#Bounds_for_Hermitian_M *)
(* https://en.wikipedia.org/wiki/Normal_matrix *)
(* https://en.wikipedia.org/wiki/Min-max_theorem#Min-max_theorem *)

Theorem Rayleigh_quotient_from_ortho : in_ordered_field →
  rngl_has_1_neq_0 = true →
  ∀ n (M : matrix T) D U eV x y ev,
  n ≠ 0
  → is_symm_mat M
  → is_square_matrix U = true
  → is_square_matrix D = true
  → mat_nrows M = n
  → vect_size x = n
  → ≺ x, x ≻ = 1%F
  → eigenvalues_and_norm_vectors n M ev eV
  → U = mat_with_vect n eV
  → M = (U⁺ * D * U)%M
  → y = (U⁺ • x)%M
  → y ≠ vect_zero n
  → Rayleigh_quotient M x =
      ((∑ (i = 1, n), nth (i - 1) ev 0%F * rngl_squ (vect_el y (i - 1))) /
       (∑ (i = 1, n), rngl_squ (vect_el y (i - 1))))%F.
Proof.
intros Hof H10 * Hnz Hsym Hsmu Hsmd Hr Hsx Hx1 HeV HU Hmin Hmax Hyz.
(*1*)
assert (HUU : (U⁺ * U)%M = mI n). {
  specialize for_symm_squ_mat_eigen_vect_mat_is_ortho as HUU.
  destruct Hof as (Hic & Hop & Hde & _ & _ & Hiv & _).
  specialize (HUU Hic (or_introl Hop)).
  specialize (HUU Hde Hiv n M ev).
  specialize (HUU eV U Hsym Hr HeV).
  now specialize (HUU HU).
}
(*
...
M y = U⁺ D U U⁺ x = U⁺ D x (ou presque, puisque j'ai U⁺U=I et non pas UU⁺=I)
U y = U U⁺ x = x (pareil)
...
*)
move HUU at bottom.
assert (Hsy : vect_size y = n). {
  apply (f_equal vect_size) in Hmax.
  rewrite mat_mul_vect_size in Hmax.
  rewrite mat_transp_nrows in Hmax.
  generalize Hmin; intros H.
  apply (f_equal mat_nrows) in Hmin.
  apply (f_equal mat_ncols) in H.
  do 2 rewrite mat_mul_nrows in Hmin.
  rewrite mat_transp_nrows in Hmin.
  rewrite mat_mul_ncols in H. 2: {
    rewrite mat_mul_nrows.
    rewrite mat_transp_nrows.
    congruence.
  }
  congruence.
}
move Hsy before Hsx.
assert (Hcu : mat_ncols U = n). {
  apply (f_equal mat_nrows) in Hmin.
  do 2 rewrite mat_mul_nrows in Hmin.
  rewrite mat_transp_nrows in Hmin.
  congruence.
}
assert (Hru : mat_nrows U = n). {
  now rewrite square_matrix_ncols in Hcu.
}
move Hru after Hcu.
unfold Rayleigh_quotient.
destruct Hof as (Hic & Hop & Hde & Hdl & Hit & Hiv & Hor).
rewrite Hx1.
rewrite vect_dot_mul_dot_mul'; [ | now left ].
unfold vect_dot_mul'.
cbn - [ vect_el ].
rewrite map_length, fold_mat_nrows, Hr, Hsx.
rewrite Nat.min_id.
(*
...
, rngl_div_1_r; [ | now left | easy ].
Search (_ = _ * _ ↔ _ / _ = _)%F.
Search (_ = _ * _ ↔ _ = _ / _)%F.
Search (_ * _ = _ ↔ _ / _ = _)%F.
Search (_ * _ = _ ↔ _ = _ / _)%F.
Search (_ = _ / _)%F.
...
*)
apply rngl_div_div_mul_mul; [ easy | easy | | | ]. {
  now apply rngl_1_neq_0.
(*
  enough (H : ≺ x, x ≻ ≠ 0%F). {
    rewrite vect_dot_mul_dot_mul' in H; [ | now left ].
    unfold vect_dot_mul' in H.
    now rewrite Nat.min_id, Hsx in H.
  }
  intros H.
  apply eq_vect_squ_0 in H; [ | easy | easy | easy | easy ].
  rewrite Hsx in H.
  rewrite Hmax, H in Hyz.
  apply Hyz.
  apply mat_vect_mul_0_r; [ easy | | ]. {
    now rewrite mat_transp_nrows.
  } {
    rewrite mat_transp_ncols, Hcu, Hru.
    now destruct n.
  }
*)
} {
  enough (H : ≺ y, y ≻ ≠ 0%F). {
    rewrite vect_dot_mul_dot_mul' in H; [ | now left ].
    unfold vect_dot_mul' in H.
    rewrite Nat.min_id, Hsy in H.
    rewrite rngl_summation_shift; [ | now apply Nat.neq_0_lt_0 ].
    erewrite rngl_summation_eq_compat. 2: {
      intros i Hi.
      rewrite Nat.add_comm, Nat.add_sub.
      unfold rngl_squ.
      easy.
    }
    easy.
  }
  intros H.
  apply eq_vect_squ_0 in H; [ | easy | easy | easy | easy ].
  now rewrite Hsy in H.
}
rewrite rngl_mul_1_l.
Check diagonalized_matrix_prop_1.
...
(* faudrait que j'essaie avec des exemples *)
(* mais, bon, c'est compliqué... *)
...
Mx = (a₁₁ x₁ + a₁₂ x₂  ; a₂₁ x₁ + a₂₂ x₂)
...
(x₁ * (a₁₁ x₁ + a₁₂ x₂) + x₂ (a₂₁ x₁ + a₂₂ x₂)) *
((u₁₁ x₁ + u₂₁ x₂) * (u₁₁ x₁ + u₂₁ x₂) + (u₁₂ x₁ + u₂₂ x₂) (u₁₂ x₁ + u₂₂ x₂))
...
f_equal. 2: {
  replace x with (U • y)%M; cbn.
  erewrite rngl_summation_eq_compat. 2: {
    intros i (_, Hi).
    rewrite (List_map_nth' []). 2: {
      rewrite fold_mat_nrows, Hru.
      flia Hi Hnz.
    }
    rewrite vect_dot_mul_dot_mul'; [ | easy ].
    unfold vect_dot_mul'; cbn.
    rewrite Hsy.
    apply is_scm_mat_iff in Hsmu.
    destruct Hsmu as (Hcru, Hclu).
    rewrite Hclu; [ | apply nth_In; rewrite fold_mat_nrows, Hru; flia Hi Hnz ].
    rewrite Hru, Nat.min_id.
    erewrite rngl_summation_eq_compat. 2: {
      intros j (_, Hj).
      rewrite fold_mat_el.
      easy.
    }
    cbn.
    easy.
  }
  cbn.
  unfold rngl_squ.
(* bof, non, ça le fait pas *)
...1
assert (Hsy : vect_size y = n). {
  apply (f_equal vect_size) in Hmax.
  rewrite mat_mul_vect_size in Hmax.
  rewrite mat_transp_nrows in Hmax.
  generalize Hmin; intros H.
  apply (f_equal mat_nrows) in Hmin.
  apply (f_equal mat_ncols) in H.
  do 2 rewrite mat_mul_nrows in Hmin.
  rewrite mat_transp_nrows in Hmin.
  rewrite mat_mul_ncols in H. 2: {
    rewrite mat_mul_nrows.
    rewrite mat_transp_nrows.
    congruence.
  }
  congruence.
}
move Hsy before Hsx.
assert (Hcu : mat_ncols U = n). {
  apply (f_equal mat_nrows) in Hmin.
  do 2 rewrite mat_mul_nrows in Hmin.
  rewrite mat_transp_nrows in Hmin.
  congruence.
}
assert (Hru : mat_nrows U = n). {
  now rewrite square_matrix_ncols in Hcu.
}
move Hru after Hcu.
unfold Rayleigh_quotient.
rewrite vect_dot_mul_dot_mul'; [ | easy ].
rewrite vect_dot_mul_dot_mul'; [ | easy ].
unfold vect_dot_mul'.
rewrite Nat.min_id.
cbn - [ vect_el ].
rewrite map_length, fold_mat_nrows, Hr, Hsx.
rewrite Nat.min_id.
(**)
f_equal.
Search (_⁺ * _)%M.
...
unfold rngl_squ.
symmetry.
rewrite rngl_summation_shift; [ | now apply Nat.neq_0_lt_0 ].
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite rngl_summation_shift; [ | now apply Nat.neq_0_lt_0 ].
  erewrite rngl_summation_eq_compat. 2: {
    intros j (_, Hj).
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  easy.
}
cbn - [ vect_el ].
unfold "/"%F.
rewrite Hiv.
rewrite <- rngl_mul_summation_distr_r; [ | easy ].
f_equal. {
  apply rngl_summation_eq_compat.
  intros i (_, Hi).
  unfold eigenvalues in Hev.
Print Rayleigh_quotient.
...
f_equal. 2: {
  f_equal.
  rewrite Hmax.
  erewrite rngl_summation_eq_compat. 2: {
    intros i (_, Hi); cbn.
    rewrite (List_map_nth' []). 2: {
      rewrite List_map_seq_length.
      apply (f_equal mat_ncols) in Hmin.
(*
      rewrite <- mat_mul_assoc in Hmin.
*)
      rewrite Hcu; flia Hi Hnz.
    }
    rewrite (List_map_nth' 0); [ | rewrite seq_length, Hcu; flia Hi Hnz ].
    erewrite map_ext_in. 2: {
      intros j Hj; apply in_seq in Hj.
      rewrite Hru in Hj.
      rewrite seq_nth; [ cbn | rewrite Hcu; flia Hi Hnz ].
      easy.
    }
    easy.
  }
  cbn.
...
  rewrite fold_mat_transp.
Check List_map_nth_seq.
Print mat_transp.
Check fold_mat_transp.
...
  rewrite vect_dot_mul_dot_mul'; [ | easy ].
  cbn.
...
Theorem Rayleigh_quotient_from_ortho : ∀ n (M : matrix n n T) D U x y ev,
  is_symm_mat M
  → eigenvalues M ev
  → M = (mat_transp U * D * U)%M
  → y = (mat_transp U • x)%M
  → Rayleigh_quotient M x =
      (Σ (i = 1, n), nth i ev 0%F * rngl_squ (vect_el y i) /
       Σ (i = 1, n), rngl_squ (vect_el y i))%F.
Proof.
intros * Hsy Hev Hmin Hmax.
...

(* The Rayleigh quotient reaches its minimum value μ_min (the smallest
   eigenvalue of M) when x is v_min (the corresponding eigenvector).
   Similarly, R (M,x) ≤ μ_max and R (M,v_max) = μ_max *)

Theorem glop : ∀ n (M : matrix n n T) x sev μ_min μ_max,
  eigenvalues M sev
  → Sorted rngl_le sev
  → μ_min = hd 0%F sev
  → μ_max = last sev 0%F
  → (μ_min ≤ Rayleigh_quotient M x ≤ μ_max)%F.
Proof.
intros * Hev Hsev Hmin Hmax.
...

(* min-max theorem, or variational theorem, or Courant–Fischer–Weyl min-max principle *)

(* Lemma 2.1 *)

Theorem lemma_2_1 :
  ∀ n m l (A : matrix n n T) (B : matrix (n - length l) (n - length l) T)
    seva sevb,
  m = n - length l
  → m < n
  → is_symm_mat A
  → B = mat_princ_subm A l
  → eigenvalues A seva
  → eigenvalues B sevb
  → Sorted rngl_le seva
  → Sorted rngl_le sevb
  → ∀ i, 1 ≤ i ≤ m →
    (nth (i-n+m) seva 0%F ≤ nth i sevb 0%F ≤ nth i seva 0%F)%F.
Proof.
intros * Hm Hmn Hisa Hb Heva Hevb Hsa Hsb * Him.
...

End a.
