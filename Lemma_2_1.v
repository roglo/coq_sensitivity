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

Require Import Misc MyVector Matrix Determinant.
Require Import RingLike.
Require Import RLsummation.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

Definition is_symm_mat n (A : matrix n n T) :=
  ∀ i j, i < n → j < n → mat_el A i j = mat_el A j i.

Definition princ_subm_1 m n (A : matrix m n T) k := subm A k k.

Theorem Nat_sub_length_nil_r : ∀ n, n = n - @length nat [].
Proof.
intros.
now rewrite Nat.sub_0_r.
Qed.

Theorem Nat_sub_1_sub_length : ∀ n l,
  n - 1 - length l = n - S (@length nat l).
Proof.
intros.
now rewrite <- Nat.sub_add_distr.
Qed.

Fixpoint mat_princ_subm n (A : matrix n n T) l :
    matrix (n - length l) (n - length l) T :=
  match l with
  | [] =>
      eq_rect _ (λ m, matrix m m T) A _ (Nat_sub_length_nil_r n)
  | i :: l' =>
      eq_rect _ (λ m, matrix m m T) (mat_princ_subm (subm A i i) l') _
        (Nat_sub_1_sub_length n l')
  end.

Theorem subm_z : ∀ f i j, subm (mk_mat 0 0 f) i j = mZ 0 0.
Proof. now intros; apply matrix_eq. Qed.

Definition eigenvalues n M ev :=
  ∀ μ, μ ∈ ev → ∃ V, V ≠ vect_zero n ∧ (M • V = μ × V)%V.

Definition eigenvalues_and_norm_vectors n M ev eV :=
  (∀ i j, 0 ≤ i < n → 0 ≤ j < n → i ≠ j → nth i ev 0%F ≠ nth j ev 0%F) ∧
  (∀ i, 0 ≤ i < n → vect_squ_norm (nth i eV (vect_zero n)) = 1%F) ∧
  ∀ i μ V, 0 ≤ i < n →
  μ = nth i ev 0%F
  → V = nth i eV (vect_zero n)
  → (M • V = μ × V)%V.

(* Rayleigh quotient *)

Definition Rayleigh_quotient n (M : matrix n n T) (x : vector n T) :=
  (≺ x, M • x ≻ / ≺ x, x ≻)%F.

Arguments Rayleigh_quotient [n]%nat_scope M%M x%V.

Theorem rngl_0_le_squ :
  rngl_has_dec_le = true →
  rngl_has_opp = true →
  rngl_is_ordered = true →
  ∀ n, (0 ≤ n * n)%F.
Proof.
intros Hld Hop Hor *.
rewrite <- (rngl_mul_0_r 0).
destruct (rngl_le_dec Hld 0%F n) as [Hnz| Hnz]. {
  apply rngl_mul_le_compat_nonneg. {
    now rewrite Hor, Hop.
  } {
    split; [ now apply rngl_le_refl | easy ].
  } {
    split; [ now apply rngl_le_refl | easy ].
  }
} {
  apply rngl_mul_le_compat_nonpos. {
    now rewrite Hor, Hop.
  } {
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
  ∀ n v, ≺ v, v ≻ = 0%F → v = vect_zero n.
Proof.
intros Hop Hed Hdo Hor * H.
unfold vect_dot_product in H.
apply vector_eq.
intros i Hi.
cbn.
revert v i Hi H.
induction n; intros; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r in H.
rewrite rngl_summation_split_last in H; [ | flia ].
destruct n. {
  unfold iter_seq, iter_list in H.
  cbn in H.
  rewrite rngl_add_0_l in H.
  apply Nat.lt_1_r in Hi; subst i.
  apply rngl_integral in H; [ | now rewrite Hdo ].
  now destruct H.
}
rewrite rngl_summation_shift in H; [ | flia ].
rewrite Nat.sub_succ, Nat.sub_0_r in H.
erewrite rngl_summation_eq_compat in H. 2: {
  intros j Hj.
  now rewrite Nat.add_comm, Nat.add_sub.
}
cbn - [ iter_seq ] in H.
apply rngl_eq_add_0 in H; [ | easy | | ]; cycle 1. {
  clear H Hi IHn.
  induction n. {
    unfold iter_seq, iter_list.
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
  apply rngl_add_le_compat; [ easy | | now apply rngl_0_le_squ ].
  remember (mk_vect (S (S n)) (λ i, vect_el v i)) as u eqn:Hu.
  specialize (IHn u) as H1.
  now subst u.
} {
  now apply rngl_0_le_squ.
}
destruct H as (H1, H2).
apply rngl_integral in H2; [ | now rewrite Hdo ].
destruct (Nat.eq_dec i (S n)) as [Hisn| Hisn]; [ now subst i; destruct H2 | ].
remember (mk_vect (S n) (λ i, vect_el v i)) as u eqn:Hu.
specialize (IHn u) as H4.
subst u.
cbn - [ iter_seq ] in H4.
apply H4; [ flia Hi Hisn | ].
now rewrite Nat.sub_0_r.
Qed.

Theorem RQ_mul_scal_prop :
  is_ordered_field →
  ∀ n (M : matrix n n T) x c,
  c ≠ 0%F
  → Rayleigh_quotient M (c × x) = Rayleigh_quotient M x.
Proof.
intros (Hic & Hop & Hed & Hld & Hdo & Hin & Hor) * Hcz.
unfold Rayleigh_quotient.
destruct (vect_opt_eq_dec Hed n x (vect_zero n)) as [Hxz| Hxz]. {
  subst x; cbn.
  unfold vect_dot_product, iter_seq, iter_list; cbn.
  unfold iter_seq, iter_list; cbn.
  do 2 rewrite rngl_mul_0_l.
  do 3 rewrite rngl_mul_0_r.
  now rewrite rngl_mul_0_l.
}
rewrite <- mat_mul_scal_vect_comm; [ | easy ].
rewrite vect_dot_mul_scal_mul_comm; [ | easy ].
rewrite vect_dot_mul_scal_mul_comm; [ | easy ].
do 2 rewrite vect_scal_mul_dot_mul_comm.
do 2 rewrite rngl_mul_assoc.
unfold rngl_div.
specialize (rngl_inv_mul_distr Hdo Hin) as H1.
specialize rngl_opt_mul_inv_l as rngl_mul_inv_l.
rewrite Hin in rngl_mul_inv_l |-*.
rewrite H1; cycle 1. {
  intros H; apply Hcz.
  apply rngl_integral in H; [ | now rewrite Hdo ].
  now destruct H.
} {
  intros H; apply Hxz.
  now apply eq_vect_squ_0.
}
rewrite rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
do 2 rewrite rngl_mul_assoc.
rewrite rngl_mul_inv_l; [ now rewrite rngl_mul_1_l | ].
intros H; apply Hcz.
apply rngl_integral in H; [ | now rewrite Hdo ].
now destruct H.
Qed.

Theorem Rayleigh_quotient_of_eigenvector :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_dec_le = true →
  rngl_is_integral = true →
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  rngl_is_ordered = true →
  ∀ n (M : matrix n n T) V μ,
  V ≠ vect_zero n
  → (M • V = μ × V)%V
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

Definition is_orthogonal_matrix n (M : matrix n n T) :=
  (mat_transp M * M)%M = mI n.

(* diagonal matrix with diagonal d being given *)

Definition mat_with_diag n d :=
  mk_mat n n (λ i j, if Nat.eq_dec i j then nth i d 0%F else 0%F).

(* matrix with columns given as list of vectors *)

Definition mat_with_vect n Vl :=
  mk_mat n n (λ i j, vect_el (nth j Vl (vect_zero n)) i).

(* In the real case, the symmetric matrix M is diagonalisable in the
   sense that there exists an orthogonal matrix U (the columns of which
   are eigenvectors) and a diagonal matrix D the coefficients of which
   are eigenvalues μ_i such that
      M = U . D . U^t *)

Theorem diagonalized_matrix_prop_1 :
  rngl_is_comm = true →
  ∀ n (M : matrix n n T) ev eV D U,
  is_symm_mat M
  → eigenvalues_and_norm_vectors M ev eV
  → D = mat_with_diag n ev
  → U = mat_with_vect eV
   → (M * U = U * D)%M.
Proof.
intros Hic * Hsy Hvv Hd Ho.
subst U D; cbn.
remember (mat_with_vect eV) as U eqn:Hmo.
remember (mat_with_diag n ev) as D eqn:Hmd.
move D before U.
destruct Hvv as (Hall_diff & Hall_norm_1 & Hvv).
unfold is_symm_mat in Hsy.
apply matrix_eq.
cbn - [ iter_seq ].
intros * Hi Hj.
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
remember (nth j ev 0%F) as μ eqn:Hμ.
remember (nth j eV (vect_zero n)) as V eqn:Hv.
symmetry.
assert (H : vect_el (M • V) i = vect_el (μ × V) i) by now rewrite H1.
cbn - [ iter_seq ] in H.
now rewrite rngl_mul_comm in H.
Qed.

Theorem mat_transp_invol : ∀ m n (M : matrix m n T), (M⁺)⁺%M = M.
Proof.
intros.
now apply matrix_eq.
Qed.

Theorem mat_transp_mul :
  rngl_is_comm = true →
  ∀ m n p (MA : matrix m n T) (MB : matrix n p T),
  ((MA * MB)⁺ = MB⁺ * MA⁺)%M.
Proof.
intros Hic *.
apply matrix_eq.
cbn - [ iter_seq ].
intros * Hi Hj.
apply rngl_summation_eq_compat.
intros k Hk.
now apply rngl_mul_comm.
Qed.

Theorem mI_transp_idemp : ∀ n, ((mI n)⁺)%M = mI n.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj.
cbn.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  now subst i; destruct (Nat.eq_dec j j).
} {
  destruct (Nat.eq_dec j i); [ now subst j | easy ].
}
Qed.

Theorem mat_mul_vect_dot_vect :
  rngl_is_comm = true →
  ∀ n (M : matrix n n T) U V,
  ≺ M • U, V ≻ = ≺ U, M⁺ • V ≻.
Proof.
intros Hic *.
unfold vect_dot_product.
unfold mat_mul_vect_r, mat_transp.
cbn - [ iter_seq ].
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
now apply rngl_mul_comm.
Qed.

(* https://math.stackexchange.com/questions/82467/eigenvectors-of-real-symmetric-matrices-are-orthogonal *)

Theorem for_symm_squ_mat_eigen_vect_mat_is_ortho :
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
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
  apply rngl_mul_reg_r in H1; [ | easy | easy ].
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

Theorem mat_inv :
  rngl_is_comm = true →
  rngl_has_opp = true →
  ∀ n (M : matrix n n T), (M * (comatrix M)⁺)%M = (determinant M × mI n)%M.
Proof.
intros Hic Hop *.
apply matrix_eq.
intros * Hi Hj.
cbn - [ iter_seq ].
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j; clear Hj.
  rewrite rngl_mul_1_r.
  enough (H : det_from_row M i = determinant M). {
    rewrite <- H.
    unfold det_from_row.
    rewrite rngl_mul_summation_distr_l.
    apply rngl_summation_eq_compat.
    intros j Hj.
    do 3 rewrite rngl_mul_assoc.
    f_equal.
    rewrite rngl_mul_comm; [ | easy ].
    f_equal.
    now apply minus_one_pow_add_r.
  }
Abort. (*
...
(*
  unfold determinant.
  induction n; [ easy | ].
  rewrite Nat.sub_succ, Nat.sub_0_r at 1.
  cbn - [ iter_seq ].
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    specialize rngl_opt_mul_comm as rngl_mul_comm.
    rewrite Hic in rngl_mul_comm.
    rewrite rngl_mul_assoc, (rngl_mul_comm (mat_el M i j)).
    easy.
  }
  cbn - [ iter_seq ].
...
*)

Theorem det_nz_inv_comm : ∀ n (MA MB : matrix n n T),
  determinant MA ≠ 0%F
  → (MA * MB = mI n)%M
  → (MB * MA = mI n)%M.
Proof.
intros * Hdet Hab.
Print comatrix.
...

(* how to prove that one? *)
Theorem mat_with_eigen_vect_mul_transp_r :
  ∀ n (M : matrix n n T) ev eV U,
  is_symm_mat M
  → eigenvalues_and_norm_vectors M ev eV
  → U = mat_with_vect eV
  → (U * U⁺)%M = mI n.
Proof.
intros * Hsy Hvv Hu.
...

Theorem diagonalized_matrix_prop :
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  ∀ n (M : matrix n n T) ev eV D U,
  is_symm_mat M
  → eigenvalues_and_norm_vectors M ev eV
  → D = mat_with_diag n ev
  → U = mat_with_vect eV
   → M = (U * D * U⁺)%M.
Proof.
intros Hic Hed Hiv * Hsy Hvv Hd Hu.
specialize (diagonalized_matrix_prop_1 Hic) as H1.
specialize (H1 n M ev eV D U Hsy Hvv Hd Hu).
rewrite <- H1.
rewrite <- mat_mul_assoc; [ | easy ].
...
rewrite (mat_with_eigen_vect_mul_transpr Hsy Hvv Hu).
...
(*
rewrite (@det_nz_inv_comm _ _ U). 3: {
  specialize for_symm_squ_mat_eigen_vect_mat_is_ortho as H2.
  specialize (H2 Hic Hed Hiv n M ev eV).
  now apply H2.
} 2: {
...
*)
*)

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
