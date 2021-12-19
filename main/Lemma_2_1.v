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

Definition is_ordered_field :=
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
  is_ordered_field →
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

Theorem mat_mul_is_corr : ∀ A B,
  is_correct_matrix A = true
  → is_correct_matrix B = true
  → mat_nrows B ≠ 0
  → is_correct_matrix (A * B) = true.
Proof.
intros * Ha Hb Hbz.
destruct (Nat.eq_dec (mat_nrows A) 0) as [Haz| Haz]. {
  unfold mat_nrows in Haz.
  apply length_zero_iff_nil in Haz.
  now destruct A as (lla); cbn in Haz; subst lla.
}
apply Nat.neq_0_lt_0 in Haz, Hbz.
apply is_scm_mat_iff in Ha.
apply is_scm_mat_iff in Hb.
apply is_scm_mat_iff.
destruct Ha as (Hacr & Hac).
destruct Hb as (Hbcr & Hbc).
split. {
  intros Hab.
  unfold mat_ncols in Hab.
  cbn in Hab |-*.
  rewrite List_map_seq_length.
  rewrite (List_map_hd 0) in Hab; [ | now rewrite seq_length ].
  rewrite List_map_seq_length in Hab.
  now rewrite Hbcr in Hbz.
} {
  intros lab Hlab.
  unfold mat_ncols; cbn.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  rewrite List_map_seq_length.
  cbn in Hlab.
  apply in_map_iff in Hlab.
  destruct Hlab as (x & Hlab & Hx).
  now rewrite <- Hlab, List_map_seq_length.
}
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
  mat_nrows M = n
  → length eV = n
  → (∀ V, V ∈ eV → vect_size V = n)
  → is_square_matrix M = true
  → is_symm_mat M
  → eigenvalues_and_norm_vectors n M ev eV
  → D = mat_with_diag n ev
  → U = mat_with_vect n eV
   → (M * U = U * D)%M.
Proof.
intros Hic Hos * Hrn Hlev Hevn Hsm Hsy Hvv Hd Ho.
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
(**)
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

Theorem mat_mul_nrows : ∀ MA MB, mat_nrows (MA * MB) = mat_nrows MA.
Proof.
intros; cbn.
now rewrite List_map_seq_length.
Qed.

Theorem mat_mul_ncols : ∀ MA MB,
  mat_nrows MA ≠ 0
  → mat_ncols (MA * MB) = mat_ncols MB.
Proof.
intros * Hraz; unfold mat_ncols; cbn.
rewrite (List_map_hd 0). 2: {
  rewrite seq_length.
  now apply Nat.neq_0_lt_0.
}
now rewrite map_length, seq_length.
Qed.

Theorem mat_el_mul : ∀ MA MB i j,
  i < mat_nrows (MA * MB)
  → j < mat_ncols (MA * MB)
  → mat_el (MA * MB) i j =
    ∑ (k = 0, mat_ncols MA - 1), mat_el MA i k * mat_el MB k j.
Proof.
intros * Hir Hjc; cbn.
rewrite mat_mul_nrows in Hir.
rewrite mat_mul_ncols in Hjc; [ | flia Hir ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite seq_nth; [ | easy ].
easy.
Qed.

Theorem mat_transp_mul :
  rngl_is_comm = true →
  ∀ (MA : matrix T) (MB : matrix T),
  is_correct_matrix MA = true
  → is_correct_matrix MB = true
  → mat_nrows MA ≠ 0
  → mat_nrows MB ≠ 0
  → mat_ncols MA = mat_nrows MB
  → ((MA * MB)⁺ = MB⁺ * MA⁺)%M.
Proof.
intros Hic * Ha Hb Haz Hbz Hcarb.
apply matrix_eq; cycle 1. {
  apply mat_transp_is_corr.
  now apply mat_mul_is_corr.
} {
  apply mat_mul_is_corr. {
    now apply mat_transp_is_corr.
  } {
    now apply mat_transp_is_corr.
  }
  rewrite mat_transp_nrows.
  intros H.
  apply is_scm_mat_iff in Ha.
  destruct Ha as (Hcra, Hcla).
  now apply Hcra in H.
} {
  cbn.
  unfold mat_ncols; cbn.
  do 3 rewrite List_map_seq_length.
  rewrite (List_map_hd 0); [ | now rewrite seq_length; apply Nat.neq_0_lt_0 ].
  now rewrite List_map_seq_length.
} {
  unfold mat_ncols; cbn.
  do 2 rewrite List_map_seq_length.
  rewrite (List_map_hd 0). 2: {
    rewrite seq_length.
    unfold mat_ncols; cbn.
    rewrite (List_map_hd 0). 2: {
      rewrite seq_length.
      now apply Nat.neq_0_lt_0.
    }
    rewrite List_map_seq_length.
    apply Nat.neq_0_lt_0.
    intros H.
    apply is_scm_mat_iff in Hb.
    now apply Hb in H.
  }
  rewrite List_map_seq_length.
  rewrite (List_map_hd 0). 2: {
    rewrite seq_length.
    apply Nat.neq_0_lt_0.
    intros H.
    apply is_scm_mat_iff in Hb.
    now apply Hb in H.
  }
  rewrite List_map_seq_length.
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ _) as [Hacz| Hacz]; [ | easy ].
  apply is_scm_mat_iff in Ha.
  now apply Ha.
}
intros i j Hi Hj.
rewrite mat_transp_nrows in Hi.
rewrite mat_transp_el; [ | now apply mat_mul_is_corr ].
rewrite mat_mul_ncols in Hi; [ | easy ].
rewrite mat_mul_ncols in Hj; [ | rewrite mat_transp_nrows; flia Hi ].
rewrite mat_transp_ncols in Hj.
rewrite if_eqb_eq_dec in Hj.
destruct (Nat.eq_dec (mat_ncols MA) 0) as [H1| H1]; [ easy | ].
rewrite mat_el_mul; cycle 1. {
  now rewrite mat_mul_nrows.
} {
  now rewrite mat_mul_ncols.
}
rewrite mat_el_mul; cycle 1. {
  now rewrite mat_mul_nrows, mat_transp_nrows.
} {
  rewrite mat_mul_ncols, mat_transp_ncols. 2: {
    rewrite mat_transp_nrows; flia Hi.
  }
  now apply Nat.eqb_neq in H1; rewrite H1.
}
rewrite mat_transp_ncols.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (mat_ncols MB) 0) as [H2| H2]; [ flia Hi H2 | ].
rewrite <- Hcarb; symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros k (_, Hk).
  rewrite rngl_mul_comm; [ | easy ].
  rewrite mat_transp_el; [ | easy ].
  rewrite mat_transp_el; [ | easy ].
  easy.
}
easy.
Qed.

Theorem mI_transp_idemp : ∀ n, ((mI n)⁺)%M = mI n.
Proof.
intros.
apply matrix_eq; cycle 1. {
  apply mat_transp_is_corr.
  apply mI_is_correct_matrix.
} {
  apply mI_is_correct_matrix.
} {
  rewrite mat_transp_nrows.
  now rewrite mI_nrows, mI_ncols.
} {
  rewrite mat_transp_ncols.
  rewrite mI_nrows, mI_ncols.
  now destruct n.
}
rewrite mat_transp_nrows, mI_ncols.
intros * Hi Hj.
rewrite mat_transp_el; [ | apply mI_is_correct_matrix ].
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  now subst i; destruct (Nat.eq_dec j j).
} {
  rewrite mat_el_mI_ndiag; [ | now apply Nat.neq_sym ].
  rewrite mat_el_mI_ndiag; [ | easy ].
  easy.
}
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
(*
intros Hic *.
unfold vect_dot_mul.
destruct M as (ll).
destruct U as (lu).
destruct V as (lv); cbn.
rewrite map_map.
unfold vect_dot_mul; cbn.
rewrite map2_map_l.
rewrite map2_map_r.
unfold mat_ncols; cbn.
symmetry.
erewrite map2_ext_in. 2: {
  intros a  i Ha Hi.
  rewrite rngl_mul_summation_list_distr_l.
  rewrite map2_map_l.
  easy.
admit.
}
symmetry.
...
*)
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

Theorem mat_with_vect_is_corr : ∀ n vl,
  is_correct_matrix (mat_with_vect n vl) = true.
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
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  rewrite List_map_seq_length.
  intros l Hl.
  apply in_map_iff in Hl.
  destruct Hl as (x & Hxl & Hx).
  apply in_seq in Hx.
  rewrite <- Hxl.
  now rewrite List_map_seq_length.
}
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

(* https://math.stackexchange.com/questions/82467/eigenvectors-of-real-symmetric-matrices-are-orthogonal *)

Theorem for_symm_squ_mat_eigen_vect_mat_is_ortho :
  rngl_is_comm = true →
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_has_dec_eq = true →
  rngl_has_inv = true →
  ∀ n (M : matrix T) ev eV A,
  is_symm_mat M
  → eigenvalues_and_norm_vectors n M ev eV
  → A = mat_with_vect n eV
  → (A⁺ * A = mI n)%M.
Proof.
intros Hic Hos Heq Hii * Hsy Hvv Hm.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n A | ].
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
...
  (* H1 : ((M • vi) · vj)%V = (vi · (M⁺ • vj))%V *)
  specialize (Hvv i (nth i ev 0%F) vi) as H2.
  assert (H : 0 ≤ i < n) by flia Hi.
  specialize (H2 H eq_refl Hvi); clear H.
  rewrite H2 in H1.
  clear H2.
  replace (M⁺)%M with M in H1. 2: {
    unfold mat_transp; cbn.
    apply matrix_eq; cbn.
    intros i' j' Hi' Hj'.
    now rewrite Hsy.
  }
  specialize (Hvv j (nth j ev 0%F) vj) as H2.
  assert (H : 0 ≤ j < n) by flia Hj.
  specialize (H2 H eq_refl Hvj); clear H.
  rewrite H2 in H1.
  clear H2.
  rewrite vect_scal_mul_dot_mul_comm in H1.
  rewrite vect_dot_mul_scal_mul_comm in H1; [ | easy ].
  destruct (rngl_eq_dec Heq (≺ vi, vj ≻) 0%F) as [Hvvij| Hvvij]; [ easy | ].
  exfalso.
  apply rngl_mul_cancel_r in H1; [ | easy | easy ].
  revert H1.
  apply Hall_diff; [ | | easy ]. {
    split; [ flia | easy ].
  } {
    split; [ flia | easy ].
  }
}...
Theorem for_symm_squ_mat_eigen_vect_mat_is_ortho :
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_inv = true ∨ rngl_has_eucl_div = true →
  ∀ n (M : matrix n n T) ev eV U,
  is_symm_mat M
  → eigenvalues_and_norm_vectors M ev eV
  → U = mat_with_vect eV
  → (U⁺ * U = mI n)%M.
Proof.
intros Hic Heq Hii * Hsy Hvv Hm.
rewrite Hm; cbn.
apply matrix_eq.
cbn - [ iter_seq ].
intros * Hi Hj.
remember (nth i eV (vect_zero n)) as vi eqn:Hvi.
remember (nth j eV (vect_zero n)) as vj eqn:Hvj.
move vj before vi.
destruct (Nat.eq_dec i j) as [Hij| Hij]. 2: {
  destruct Hvv as (Hall_diff & Hall_norm_1 & Hvv).
  enough (Hvvz : ≺ vi, vj ≻ = 0%F) by easy.
  specialize (mat_mul_vect_dot_vect Hic M vi vj) as H1.
  (* H1 : ((M • vi) · vj)%V = (vi · (M⁺ • vj))%V *)
  specialize (Hvv i (nth i ev 0%F) vi) as H2.
  assert (H : 0 ≤ i < n) by flia Hi.
  specialize (H2 H eq_refl Hvi); clear H.
  rewrite H2 in H1.
  clear H2.
  replace (M⁺)%M with M in H1. 2: {
    unfold mat_transp; cbn.
    apply matrix_eq; cbn.
    intros i' j' Hi' Hj'.
    now rewrite Hsy.
  }
  specialize (Hvv j (nth j ev 0%F) vj) as H2.
  assert (H : 0 ≤ j < n) by flia Hj.
  specialize (H2 H eq_refl Hvj); clear H.
  rewrite H2 in H1.
  clear H2.
  rewrite vect_scal_mul_dot_mul_comm in H1.
  rewrite vect_dot_mul_scal_mul_comm in H1; [ | easy ].
  destruct (rngl_eq_dec Heq (≺ vi, vj ≻) 0%F) as [Hvvij| Hvvij]; [ easy | ].
  exfalso.
  apply rngl_mul_cancel_r in H1; [ | easy | easy ].
  revert H1.
  apply Hall_diff; [ | | easy ]. {
    split; [ flia | easy ].
  } {
    split; [ flia | easy ].
  }
}
subst j.
rewrite Hvj, <- Hvi.
destruct Hvv as (Hall_diff & Hall_norm_1 & Hvv).
specialize (Hall_norm_1 i) as H1.
rewrite <- Hvi in H1.
apply H1; flia Hi.
Qed.

(* changing variable x as y = O^T . x, the Rayleigh quotient R (M, x)
   is equal to
      Σ (i = 1, n), μ_i * y_i ^ 2 / Σ (i = 1, n), y_i ^ 2 *)

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
Abort. (*
...
*)

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
Abort. (*
...
*)

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
Abort. (*
...
*)

End a.
