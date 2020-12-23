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
Import List List.ListNotations.
Require Import Permutation Sorted.

Require Import Misc Matrix.
Require Import RingLike.
Require Import RLsummation.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

Definition is_symm_mat (A : matrix T) :=
  ∀ i j, i < mat_nrows A → j < mat_nrows A →
  mat_el A i j = mat_el A j i.

Definition is_symm_squ_mat n (A : square_matrix n) :=
  is_symm_mat (mat_of_squ_mat A).

Definition princ_subm_1 (A : matrix T) n := subm A n n.

Theorem princ_subm_1_preserves_symm : ∀ (A : matrix T) n,
  is_symm_mat A
  → is_symm_mat (princ_subm_1 A n).
Proof.
intros * Ha.
unfold is_symm_mat in Ha |-*; cbn.
intros i j Hi Hj.
destruct (lt_dec i n) as [Hin| Hin]. {
  destruct (lt_dec j n) as [Hjn| Hjn]. {
    apply Ha; [ flia Hi | flia Hj ].
  } {
    apply Ha; [ flia Hi | flia Hj ].
  }
} {
  destruct (lt_dec j n) as [Hjn| Hjn]. {
    apply Ha; [ flia Hi | flia Hj ].
  } {
    apply Ha; [ flia Hi | flia Hj ].
  }
}
Qed.

Definition mat_princ_subm (A : matrix T) l :=
  fold_left (λ a i, subm a i i) l A.

Theorem subm_z : ∀ f i j, subm (mk_mat f 0 0) i j = mZ 0.
Proof. now intros; apply matrix_eq. Qed.

Theorem princ_subm_prop : ∀ n (A : square_matrix n) l,
  ((mat_nrows (mat_princ_subm (mat_of_squ_mat A) l) =? n - length l) &&
   (mat_ncols (mat_princ_subm (mat_of_squ_mat A) l) =? n - length l))%bool = true.
Proof.
intros.
apply Bool.andb_true_iff.
revert n A.
induction l as [| i]; intros. {
  cbn; rewrite Nat.sub_0_r.
  destruct A as (A, Ha); cbn in Ha |-*.
  apply Bool.andb_true_iff in Ha.
  destruct Ha as (Hra, Hca).
  apply Nat.eqb_eq in Hra.
  apply Nat.eqb_eq in Hca.
  now split; apply Nat.eqb_eq.
}
cbn.
unfold mat_princ_subm in IHl.
destruct n. {
  destruct A as (A, Ha); cbn in Ha |-*.
  apply Bool.andb_true_iff in Ha.
  destruct Ha as (Hra, Hca).
  apply Nat.eqb_eq in Hra.
  apply Nat.eqb_eq in Hca.
  destruct A as (fa, ra, ca).
  cbn in Hra, Hca.
  subst ra ca.
  rewrite subm_z.
  clear.
  replace (fold_left _ l (mZ 0)) with (mZ 0); [ easy | ].
  symmetry.
  induction l as [| i]; [ easy | cbn ].
  replace (subm (mZ 0) i i) with (mZ 0); [ easy | ].
  now apply matrix_eq.
}
rewrite Nat.sub_succ.
specialize (IHl _ (squ_mat_subm A i i)) as (H1, H2).
cbn in H1; rewrite Nat.sub_0_r in H1; rewrite H1.
cbn in H2; rewrite Nat.sub_0_r in H2; rewrite H2.
easy.
Qed.

Definition princ_subm n (A : square_matrix n) (l : list nat) :
   square_matrix (n - length l) :=
 exist _ (mat_princ_subm (mat_of_squ_mat A) l) (princ_subm_prop A l).

Definition eigenvalues M ev :=
  ∀ μ, μ ∈ ev → ∃ V, V ≠ vect_zero (mat_nrows M) ∧ (M • V = μ × V)%V.

Definition eigenvalues_and_vectors M ev eV :=
  ∀ i μ V, 0 ≤ i < mat_nrows M →
  μ = nth i ev 0%F
  → V = nth i eV (vect_zero (mat_nrows M))
  → vect_nrows V = mat_nrows M ∧
    V ≠ vect_zero (vect_nrows V) ∧
    (M • V = μ × V)%V.

(* Rayleigh quotient *)

Definition Rayleigh_quotient n (M : square_matrix n) (x : vector T) :=
  ((x · (M • x)%SM)%V / (x · x)%V)%F.

Arguments Rayleigh_quotient [n]%nat_scope M%SM x%V.

Theorem rngl_0_le_squ :
  rngl_has_dec_le = true →
  rngl_has_opp = true →
  rngl_is_ordered = true →
  ∀ n, (0 ≤ n * n)%F.
Proof.
intros Hld Hop Hor *.
specialize rngl_opt_le_dec as rngl_le_dec.
specialize rngl_opt_le_refl as rngl_le_refl.
specialize rngl_opt_mul_le_compat_nonneg as rngl_mul_le_compat_nonneg.
specialize rngl_opt_mul_le_compat_nonpos as rngl_mul_le_compat_nonpos.
specialize rngl_opt_not_le as rngl_not_le.
rewrite Hld in rngl_le_dec.
rewrite Hor in rngl_le_refl.
rewrite Hor, Hop in rngl_mul_le_compat_nonneg.
rewrite Hor, Hop in rngl_mul_le_compat_nonpos.
rewrite <- (rngl_mul_0_r 0).
rewrite Hor in rngl_not_le.
destruct (rngl_le_dec 0%F n) as [Hnz| Hnz]. {
  apply rngl_mul_le_compat_nonneg. {
    split; [ now apply rngl_le_refl | easy ].
  } {
    split; [ now apply rngl_le_refl | easy ].
  }
} {
  apply rngl_mul_le_compat_nonpos. {
    split; [ | now apply rngl_le_refl ].
    apply rngl_not_le in Hnz.
    destruct Hnz as [Hnz| Hnz]; [ | easy ].
    rewrite <- Hnz; apply rngl_le_refl.
  } {
    split; [ | now apply rngl_le_refl ].
    apply rngl_not_le in Hnz.
    destruct Hnz as [Hnz| Hnz]; [ | easy ].
    rewrite <- Hnz; apply rngl_le_refl.
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
  ∀ x, (x · x)%V = 0%F → x = vect_zero (vect_nrows x).
Proof.
intros Hop Hed Hdo Hor * H.
remember (vect_nrows x) as r eqn:Hr.
specialize rngl_opt_integral as rngl_integral.
specialize rngl_opt_add_le_compat as rngl_add_le_compat.
rewrite Hdo in rngl_integral.
rewrite Hor in rngl_add_le_compat.
unfold vect_dot_product in H.
apply vector_eq; [ easy | cbn ].
intros i Hi.
rewrite <- Hr in H, Hi.
remember (vect_el x) as f.
revert i Hi.
clear Hr.
induction r; intros; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r in H.
rewrite rngl_summation_split_last in H; [ | flia ].
destruct r. {
  cbn in H.
  rewrite rngl_add_0_l in H.
  specialize (rngl_integral _ _ H) as H1.
  apply Nat.lt_1_r in Hi; subst i.
  now destruct H1.
}
rewrite rngl_summation_shift in H; [ | flia ].
rewrite Nat.sub_succ, Nat.sub_0_r in H.
erewrite rngl_summation_eq_compat in H. 2: {
  intros j Hj.
  now rewrite Nat.add_comm, Nat.add_sub.
}
cbn - [ iter_seq ] in H.
apply rngl_eq_add_0 in H; [ | easy | | ]; cycle 1. {
  clear H IHr Hi.
  induction r. {
    cbn; rewrite rngl_add_0_l.
    now apply rngl_0_le_squ.
  }
  rewrite rngl_summation_split_last; [ | flia ].
  rewrite rngl_summation_shift; [ | flia ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  cbn - [ iter_seq ].
  rewrite <- (rngl_add_0_r 0%F) at 1.
  apply rngl_add_le_compat; [ easy | ].
  now apply rngl_0_le_squ.
} {
  now apply rngl_0_le_squ.
}
destruct H as (H1, H2).
specialize (rngl_integral _ _ H2) as H3.
destruct (Nat.eq_dec i (S r)) as [Hisr| Hisr]; [ now subst i; destruct H3 | ].
apply IHr; [ | flia Hi Hisr ].
now rewrite Nat.sub_succ, Nat.sub_0_r.
Qed.

Theorem RQ_mul_scal_prop :
  is_ordered_field →
  ∀ n (M : square_matrix n) x c,
  c ≠ 0%F
  → Rayleigh_quotient M (c × x) = Rayleigh_quotient M x.
Proof.
intros (Hic & Hop & Hed & Hld & Hdo & Hin & Hor) * Hcz.
unfold Rayleigh_quotient.
remember (vect_nrows x) as r eqn:Hr.
destruct (vect_eq_dec Hed r x (vect_zero r)) as [Hxz| Hxz]. {
  easy.
} {
  easy.
} {
  subst x; cbn.
  do 2 rewrite rngl_mul_0_l.
  do 3 rewrite rngl_mul_0_r.
  now rewrite rngl_mul_0_l.
}
rewrite <- squ_mat_mul_scal_vect_comm; [ | easy ].
rewrite vect_dot_mul_scal_mul_comm; [ | easy ].
rewrite vect_dot_mul_scal_mul_comm; [ | easy ].
do 2 rewrite vect_scal_mul_dot_mul_comm.
do 2 rewrite rngl_mul_assoc.
unfold rngl_div.
specialize (rngl_inv_mul Hdo Hin) as H1.
specialize rngl_opt_mul_comm as rngl_mul_comm.
specialize rngl_opt_mul_inv_l as rngl_mul_inv_l.
specialize rngl_opt_integral as rngl_integral.
specialize rngl_opt_add_le_compat as rngl_add_le_compat.
specialize rngl_opt_mul_le_compat_nonneg as rngl_mul_le_compat_nonneg.
specialize rngl_opt_mul_le_compat_nonpos as rngl_mul_le_compat_nonpos.
specialize rngl_opt_not_le as rngl_not_le.
specialize rngl_opt_le_refl as rngl_le_refl.
specialize rngl_opt_le_dec as rngl_le_dec.
rewrite Hic in rngl_mul_comm.
rewrite Hin in rngl_mul_inv_l |-*.
rewrite Hdo in rngl_integral.
rewrite Hor in rngl_le_refl.
rewrite Hor in rngl_add_le_compat.
rewrite Hor, Hop in rngl_mul_le_compat_nonneg.
rewrite Hor, Hop in rngl_mul_le_compat_nonpos.
rewrite Hor in rngl_not_le.
rewrite Hld in rngl_le_dec.
cbn in rngl_mul_le_compat_nonneg, rngl_mul_le_compat_nonpos.
rewrite H1; cycle 1. {
  intros H; apply Hcz.
  apply rngl_integral in H.
  now destruct H.
} {
  subst r.
  intros H; apply Hxz.
  now apply eq_vect_squ_0.
}
rewrite rngl_mul_assoc.
rewrite rngl_mul_comm.
do 2 rewrite rngl_mul_assoc.
rewrite rngl_mul_inv_l; [ now rewrite rngl_mul_1_l | ].
intros H; apply Hcz.
apply rngl_integral in H.
now destruct H.
Qed.

Theorem Rayleigh_quotient_of_eigenvector :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_dec_le = true →
  rngl_is_integral = true →
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  rngl_is_ordered = true →
  ∀ n (M : square_matrix n) V μ,
  V ≠ vect_zero (vect_nrows V)
  → (M • V)%SM = (μ × V)%V
  → Rayleigh_quotient M V = μ.
Proof.
intros Hic Hop Hii Hdo Hor Hdl * Hvz Hmv.
unfold Rayleigh_quotient.
rewrite Hmv.
rewrite vect_dot_mul_scal_mul_comm; [ | easy ].
apply rngl_mul_div_l; [ easy | ].
intros H.
now apply eq_vect_squ_0 in H.
Qed.

Definition is_orthogonal_matrix (M : matrix T) :=
  (mat_transp M * M)%M = mI (mat_nrows M).

Definition is_orthogonal_square_matrix n (M : square_matrix n) :=
  is_orthogonal_matrix (mat_of_squ_mat M).

(* diagonal matrix with diagonal d being given *)

Definition mat_with_diag n d :=
  mk_mat (λ i j, if Nat.eq_dec i j then nth i d 0%F else 0%F) n n.

Theorem mat_with_diag_prop : ∀ n d,
  ((mat_nrows (mat_with_diag n d) =? n) &&
   (mat_ncols (mat_with_diag n d) =? n))%bool = true.
Proof.
intros; cbn.
apply Bool.andb_true_iff.
now split; apply Nat.eqb_eq.
Qed.

(* diagonal square matrix with diagonal d being given *)

Definition squ_mat_with_diag n d : square_matrix n :=
 exist _ (mat_with_diag n d) (mat_with_diag_prop n d).

(* matrix with columns given as list of vectors *)

Definition mat_with_vect n Vl :=
  mk_mat (λ i j, vect_el (nth j Vl (vect_zero n)) i) n n.

(* square matrix with columns given as list of vectors *)

Theorem mat_with_vect_prop : ∀ n Vl,
  ((mat_nrows (mat_with_vect n Vl) =? n) &&
   (mat_ncols (mat_with_vect n Vl) =? n))%bool = true.
Proof.
intros; cbn.
apply Bool.andb_true_iff.
now split; apply Nat.eqb_eq.
Qed.

Definition squ_mat_with_vect n (Vl : list (vector T)) :
   square_matrix n :=
 exist _ (mat_with_vect n Vl) (mat_with_vect_prop n Vl).

(* In the real case, the symmetric matrix M is diagonalisable in the
   sense that there exists an orthogonal matrix U (the columns of which
   are eigenvectors) and a diagonal matrix D the coefficients of which
   are eigenvalues μ_i such that
      M = U . D . U^t *)

Theorem diagonalized_matrix_prop_1 :
  rngl_is_comm = true →
  ∀ n (M : @square_matrix T n) ev eV D U,
  is_symm_squ_mat M
  → eigenvalues_and_vectors (mat_of_squ_mat M) ev eV
  → D = squ_mat_with_diag n ev
  → U = squ_mat_with_vect n eV
   → (M * U = U * D)%SM.
Proof.
intros Hic * Hsy Hvv Hd Ho.
apply square_matrix_eq; cbn.
subst U D; cbn.
remember (mat_with_vect n eV) as U eqn:Hmo.
remember (mat_with_diag n ev) as D eqn:Hmd.
move D before U.
unfold eigenvalues_and_vectors in Hvv.
unfold is_symm_squ_mat in Hsy.
destruct M as (M, Hm).
cbn in Hsy, Hvv |-*.
apply Bool.andb_true_iff in Hm.
destruct Hm as (Hr, Hc).
apply Nat.eqb_eq in Hr.
apply Nat.eqb_eq in Hc.
rewrite Hr in Hvv.
apply matrix_eq; [ now rewrite Hmo; cbn | | ]. {
  now rewrite Hmo, Hmd; cbn.
}
cbn - [ iter_seq ].
rewrite Hr, Hc.
intros * Hi Hj.
rewrite Hmd in Hj; cbn in Hj.
remember (mat_ncols U) as x eqn:Hx.
rewrite Hmo in Hx; cbn in Hx; subst x.
symmetry.
rewrite (rngl_summation_split _ j); [ | flia Hj ].
rewrite rngl_summation_split_last; [ | flia ].
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  rewrite Hmd; cbn.
  destruct (Nat.eq_dec (k - 1) j) as [Hkj| Hkj]; [ flia Hk Hkj | ].
  apply rngl_mul_0_r.
}
rewrite rngl_add_0_l.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  rewrite Hmd; cbn.
  destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ flia Hk Hkj | ].
  apply rngl_mul_0_r.
}
rewrite rngl_add_0_r.
rewrite Hmd; cbn - [ iter_seq ].
destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
rewrite Hmo.
cbn - [ iter_seq ].
specialize (Hvv j (nth j ev 0%F) (nth j eV (vect_zero n))) as H1.
assert (H : 0 ≤ j < n) by flia Hj.
specialize (H1 H eq_refl eq_refl); clear H.
destruct H1 as (Hvjz & Hvj & H1).
remember (nth j ev 0%F) as μ eqn:Hμ.
remember (nth j eV (vect_zero n)) as V eqn:Hv.
symmetry.
assert (H : vect_el (M • V) i = vect_el (μ × V) i) by now rewrite H1.
cbn - [ iter_seq ] in H.
rewrite Hc in H.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
now rewrite rngl_mul_comm in H.
Qed.

Theorem mat_transp_invol : ∀ M : matrix T, (M⁺)⁺%M = M.
Proof.
intros.
now apply matrix_eq.
Qed.

Theorem mat_transp_mul :
  rngl_is_comm = true →
  ∀ MA MB : matrix T,
  mat_ncols MA = mat_nrows MB
  → ((MA * MB)⁺ = MB⁺ * MA⁺)%M.
Proof.
intros Hic * Hab.
apply matrix_eq; [ easy | easy | ].
cbn - [ iter_seq ].
intros * Hi Hj.
rewrite <- Hab.
apply rngl_summation_eq_compat.
intros k Hk.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
apply rngl_mul_comm.
Qed.

Theorem mI_transp_idemp : ∀ n, ((mI n)⁺)%M = mI n.
Proof.
intros.
apply matrix_eq; [ easy | easy | cbn ].
intros * Hi Hj.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  now subst i; destruct (Nat.eq_dec j j).
} {
  destruct (Nat.eq_dec j i); [ now subst j | easy ].
}
Qed.

Theorem squ_mat_mul_vect_dot_vect :
  rngl_is_comm = true →
  ∀ n (M : square_matrix n) U V,
  vect_nrows U = n
  → ((M • U)%SM · V = U · (M⁺ • V)%SM)%V.
Proof.
intros Hic * Hun.
unfold vect_dot_product.
unfold squ_mat_mul_vect_r, squ_mat_transp.
cbn - [ iter_seq ].
rewrite mat_nrows_of_squ_mat.
rewrite mat_ncols_of_squ_mat.
rewrite Hun.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite rngl_mul_summation_distr_r.
}
cbn - [ iter_seq ].
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite rngl_mul_summation_distr_l.
}
cbn - [ iter_seq ].
symmetry.
rewrite rngl_summation_summation_exch'; [ | easy ].
apply rngl_summation_eq_compat.
intros i Hi.
apply rngl_summation_eq_compat.
intros j Hj.
rewrite rngl_mul_assoc; f_equal.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
apply rngl_mul_comm.
Qed.

Theorem for_symm_squ_mat_eigen_vect_mat_is_ortho :
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  ∀ n (M : square_matrix n) ev eV U,
  is_symm_squ_mat M
  → eigenvalues_and_vectors (mat_of_squ_mat M) ev eV
  → U = squ_mat_with_vect n eV
  → (U * U⁺ = squ_mat_one n)%SM.
Proof.
intros Hic Heq Hii * Hsy Hvv Hm.
apply square_matrix_eq; cbn.
rewrite Hm; cbn.
apply matrix_eq; [ easy | easy | ].
cbn - [ iter_seq ].
intros * Hi Hj.
remember (mk_vect (λ j, vect_el (nth j eV (vect_zero n)) i) n) as vi eqn:Hvi.
remember (mk_vect (λ i, vect_el (nth i eV (vect_zero n)) j) n) as vj eqn:Hvj.
move vj before vi.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  replace (vect_el (nth k eV (vect_zero n)) i) with (vect_el vi k). 2: {
    now rewrite Hvi.
  }
  replace (vect_el (nth k eV (vect_zero n)) j) with (vect_el vj k). 2: {
    now rewrite Hvj.
  }
  easy.
}
cbn - [ iter_seq ].
(* problem: if vi=vj but i≠j (same eigenvalues), this does not work *)
destruct (Nat.eq_dec i j) as [Hij| Hij]. 2: {
  unfold eigenvalues_and_vectors in Hvv.
  enough (Hvvz : (vi · vj)%V = 0%F). {
    unfold vect_dot_product in Hvvz.
    specialize (Hvv i (nth i ev 0%F)) as H1.
    rewrite mat_nrows_of_squ_mat in H1.
...
    assert (H : 0 ≤ i < n) by (split; [ flia | easy ]).
    specialize (H1 H eq_refl); clear H.
    specialize (H1 H eq_refl Hvi); clear H.
    destruct H1 as (H1 & H2 & H3).
    now rewrite H1 in Hvvz.
  }
  specialize (squ_mat_mul_vect_dot_vect Hic M vi vj) as H1.
  (* ((M • vi)%SM · vj)%V = (vi · (M⁺ • vj)%SM)%V *)
  assert (H : vect_nrows vi = n). {
    specialize (Hvv i (nth i ev 0%F) vi) as H2.
    rewrite mat_nrows_of_squ_mat in H2.
    assert (H : 0 ≤ i < n) by flia Hi.
    now specialize (H2 H eq_refl Hvi); clear H.
  }
  specialize (H1 H); clear H.
  (* H1 : ((M • vi)%SM · vj)%V = (vi · (M⁺ • vj)%SM)%V *)
  specialize (Hvv i (nth i ev 0%F) vi) as H2.
  rewrite mat_nrows_of_squ_mat in H2.
  assert (H : 0 ≤ i < n) by flia Hi.
  specialize (H2 H eq_refl Hvi); clear H.
  destruct H2 as (_ & _& H2).
  assert (H : (M • vi)%SM = (mat_of_squ_mat M • vi)%V). {
    apply vector_eq; [ easy | ].
    cbn - [ iter_seq ].
    now rewrite mat_nrows_of_squ_mat.
  }
  rewrite H, H2 in H1.
  clear H2 H.
  replace (M⁺)%SM with M in H1. 2: {
    apply square_matrix_eq; cbn.
    unfold mat_transp; cbn.
    rewrite mat_nrows_of_squ_mat.
    rewrite mat_ncols_of_squ_mat.
    apply matrix_eq; cbn. {
      now rewrite mat_nrows_of_squ_mat.
    } {
      now rewrite mat_ncols_of_squ_mat.
    }
    intros i' j' Hi' Hj'.
    rewrite Hsy; [ easy | easy | ].
    now rewrite mat_nrows_of_squ_mat.
  }
  specialize (Hvv j (nth j ev 0%F) vj) as H2.
  rewrite mat_nrows_of_squ_mat in H2.
  assert (H : 0 ≤ j < n) by flia Hj.
  specialize (H2 H eq_refl Hvj); clear H.
  destruct H2 as (_ & _& H2).
  assert (H : (M • vj)%SM = (mat_of_squ_mat M • vj)%V). {
    apply vector_eq; [ easy | ].
    cbn - [ iter_seq ].
    now rewrite mat_nrows_of_squ_mat.
  }
  rewrite H, H2 in H1.
  clear H2 H.
  rewrite vect_scal_mul_dot_mul_comm in H1.
  rewrite vect_dot_mul_scal_mul_comm in H1; [ | easy ].
  specialize rngl_opt_eq_dec as rngl_eq_dec.
  rewrite Heq in rngl_eq_dec.
  destruct (rngl_eq_dec (vi · vj)%V 0%F) as [Hvvij| Hvvij]; [ easy | ].
  exfalso.
  apply rngl_mul_reg_r in H1; [ | easy | easy ].
  (* all eigenvalues are supposed to be different? *)
  (* https://math.stackexchange.com/questions/82467/eigenvectors-of-real-symmetric-matrices-are-orthogonal *)
  Print eigenvalues_and_vectors.
  (* my definition of eigenvalues_and_vectors is not good because it does not
   imply that the eigenvalues are different and even the egenvectors are
   different; it could be just one eigenvalue and its eigenvector repeated;
   I could specify that all eigenvalues are different but, doing so, it is
   not enough general, because an eigenvalue can have a multiplicity *)
...
*)

Theorem for_symm_squ_mat_eigen_vect_mat_is_ortho :
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  ∀ n (M : square_matrix n) ev eV U,
  is_symm_squ_mat M
  → eigenvalues_and_vectors (mat_of_squ_mat M) ev eV
  → U = squ_mat_with_vect n eV
  → (U⁺ * U = squ_mat_one n)%SM.
Proof.
intros Hic Heq Hii * Hsy Hvv Hm.
apply square_matrix_eq; cbn.
rewrite Hm; cbn.
apply matrix_eq; [ easy | easy | ].
cbn - [ iter_seq ].
intros * Hi Hj.
remember (nth i eV (vect_zero n)) as vi eqn:Hvi.
remember (nth j eV (vect_zero n)) as vj eqn:Hvj.
move vj before vi.
(* problem: if vi=vj but i≠j (same eigenvalues), this does not work *)
destruct (Nat.eq_dec i j) as [Hij| Hij]. 2: {
  unfold eigenvalues_and_vectors in Hvv.
  enough (Hvvz : (vi · vj)%V = 0%F). {
    unfold vect_dot_product in Hvvz.
    specialize (Hvv i (nth i ev 0%F) vi) as H1.
    rewrite mat_nrows_of_squ_mat in H1.
    assert (H : 0 ≤ i < n) by (split; [ flia | easy ]).
    specialize (H1 H eq_refl Hvi); clear H.
    destruct H1 as (H1 & H2 & H3).
    now rewrite H1 in Hvvz.
  }
  specialize (squ_mat_mul_vect_dot_vect Hic M vi vj) as H1.
  (* ((M • vi)%SM · vj)%V = (vi · (M⁺ • vj)%SM)%V *)
  assert (H : vect_nrows vi = n). {
    specialize (Hvv i (nth i ev 0%F) vi) as H2.
    rewrite mat_nrows_of_squ_mat in H2.
    assert (H : 0 ≤ i < n) by flia Hi.
    now specialize (H2 H eq_refl Hvi); clear H.
  }
  specialize (H1 H); clear H.
  (* H1 : ((M • vi)%SM · vj)%V = (vi · (M⁺ • vj)%SM)%V *)
  specialize (Hvv i (nth i ev 0%F) vi) as H2.
  rewrite mat_nrows_of_squ_mat in H2.
  assert (H : 0 ≤ i < n) by flia Hi.
  specialize (H2 H eq_refl Hvi); clear H.
  destruct H2 as (_ & _& H2).
  assert (H : (M • vi)%SM = (mat_of_squ_mat M • vi)%V). {
    apply vector_eq; [ easy | ].
    cbn - [ iter_seq ].
    now rewrite mat_nrows_of_squ_mat.
  }
  rewrite H, H2 in H1.
  clear H2 H.
  replace (M⁺)%SM with M in H1. 2: {
    apply square_matrix_eq; cbn.
    unfold mat_transp; cbn.
    rewrite mat_nrows_of_squ_mat.
    rewrite mat_ncols_of_squ_mat.
    apply matrix_eq; cbn. {
      now rewrite mat_nrows_of_squ_mat.
    } {
      now rewrite mat_ncols_of_squ_mat.
    }
    intros i' j' Hi' Hj'.
    rewrite Hsy; [ easy | easy | ].
    now rewrite mat_nrows_of_squ_mat.
  }
  specialize (Hvv j (nth j ev 0%F) vj) as H2.
  rewrite mat_nrows_of_squ_mat in H2.
  assert (H : 0 ≤ j < n) by flia Hj.
  specialize (H2 H eq_refl Hvj); clear H.
  destruct H2 as (_ & _& H2).
  assert (H : (M • vj)%SM = (mat_of_squ_mat M • vj)%V). {
    apply vector_eq; [ easy | ].
    cbn - [ iter_seq ].
    now rewrite mat_nrows_of_squ_mat.
  }
  rewrite H, H2 in H1.
  clear H2 H.
  rewrite vect_scal_mul_dot_mul_comm in H1.
  rewrite vect_dot_mul_scal_mul_comm in H1; [ | easy ].
  specialize rngl_opt_eq_dec as rngl_eq_dec.
  rewrite Heq in rngl_eq_dec.
  destruct (rngl_eq_dec (vi · vj)%V 0%F) as [Hvvij| Hvvij]; [ easy | ].
  exfalso.
  apply rngl_mul_reg_r in H1; [ | easy | easy ].
  (* all eigenvalues are supposed to be different? *)
  (* https://math.stackexchange.com/questions/82467/eigenvectors-of-real-symmetric-matrices-are-orthogonal *)
  Print eigenvalues_and_vectors.
  (* my definition of eigenvalues_and_vectors is not good because it does not
   imply that the eigenvalues are different and even the egenvectors are
   different; it could be just one eigenvalue and its eigenvector repeated;
   I could specify that all eigenvalues are different but, doing so, it is
   not enough general, because an eigenvalue can have a multiplicity *)
...

Theorem diagonalized_matrix_prop :
  rngl_is_comm = true →
  ∀ n (M : square_matrix n) ev eV D U,
  is_symm_squ_mat M
  → eigenvalues_and_vectors (mat_of_squ_mat M) ev eV
  → D = squ_mat_with_diag n ev
  → U = squ_mat_with_vect n eV
   → M = (U * D * U⁺)%SM.
Proof.
intros Hic * Hsy Hvv Hd Ho.
specialize (diagonalized_matrix_prop_1 Hic) as H.
specialize (H n M ev eV D U Hsy Hvv Hd Ho).
rewrite <- H.
rewrite <- squ_mat_mul_assoc; [ | easy ].
...

(* changing variable x as y = O^T . x, the Rayleigh quotient R (M, x)
   is equal to
      Σ (i = 1, n), μ_i * y_i ^ 2 / Σ (i = 1, n), y_i ^ 2 *)

Theorem Rayleigh_quotient_from_ortho : ∀ n (M : square_matrix n) D U x y ev,
  is_symm_squ_mat M
  → eigenvalues (mat_of_squ_mat M) ev
  → M = (squ_mat_transp U * D * U)%SM
  → y = (squ_mat_transp U • x)%SM
  → Rayleigh_quotient M x =
      (Σ (i = 1, n), nth i ev 0%F * rngl_squ (vect_el y i) /
       Σ (i = 1, n), rngl_squ (vect_el y i))%F.
Proof.
intros * Hsy Hev Hmin Hmax.
Abort.

(* The Rayleigh quotient reaches its minimum value μ_min (the smallest
   eigenvalue of M) when x is v_min (the corresponding eigenvector).
   Similarly, R (M,x) ≤ μ_max and R (M,v_max) = μ_max *)

Theorem glop : ∀ n (M : square_matrix n) x sev μ_min μ_max,
  eigenvalues (mat_of_squ_mat M) sev
  → Sorted rngl_le sev
  → μ_min = hd 0%F sev
  → μ_max = last sev 0%F
  → (μ_min ≤ Rayleigh_quotient M x ≤ μ_max)%F.
Proof.
intros * Hev Hsev Hmin Hmax.
...

(* min-max theorem, or variational theorem, or Courant–Fischer–Weyl min-max principle *)

...

(* Lemma 2.1 *)

Theorem lemma_2_1 :
  ∀ n m l (A : square_matrix n) (B : square_matrix (n - length l)) seva sevb,
  m = n - length l
  → m < n
  → is_symm_squ_mat A
  → B = princ_subm A l
  → eigenvalues (mat_of_squ_mat A) seva
  → eigenvalues (mat_of_squ_mat B) sevb
  → Sorted rngl_le seva
  → Sorted rngl_le sevb
  → ∀ i, 1 ≤ i ≤ m →
    (nth (i-n+m) seva 0%F ≤ nth i sevb 0%F ≤ nth i seva 0%F)%F.
Proof.
intros * Hm Hmn Hisa Hb Heva Hevb Hsa Hsb * Him.
...

End in_ring_like.
