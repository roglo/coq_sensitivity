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

Require Import Utf8 Arith.
Import Init.Nat List List.ListNotations.
Require Import Sorted.

Require Import Misc RingLike IterAdd IterMul MyVector.
Require Import Matrix Signature Determinant Comatrix.
Require Import CauchyBinet.
Import matrix_Notations.

Notation "l .( i )" := (nth (i - 1) l 0%L)
  (at level 1, format "l .( i )") : ring_like_scope.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

(*
Definition is_symm_mat (A : matrix T) :=
  is_square_matrix A = true ∧
  ∀ i j, 1 ≤ i ≤ mat_nrows A → 1 ≤ j ≤ mat_nrows A →
  mat_el A i j = mat_el A j i.
*)
Definition is_symm_mat (A : matrix T) :=
  is_square_matrix A = true ∧ A = (A⁺)%M.

Definition princ_subm_1 (A : matrix T) k := subm (S k) (S k) A.

Fixpoint mat_princ_subm (A : matrix T) l : matrix T :=
  match l with
  | [] => A
  | i :: l' => mat_princ_subm (subm (S i) (S i) A) l'
  end.

Theorem subm_z : ∀ i j, subm i j (mk_mat []) = mZ 0 0.
Proof.
intros.
unfold subm, mZ; cbn.
now rewrite butn_nil.
Qed.

(* to be completed
Theorem exist_eigenvalues :
  rngl_is_alg_closed = true →
  ∀ n (M : matrix T),
  is_square_matrix M = true
  → mat_nrows M = n
  → ∃ ev, ev = 0.
Proof.
intros Hac * Hsm Hr.
specialize rngl_opt_alg_closed as H1.
rewrite Hac in H1.
...
*)

Definition eigenvalues n M ev :=
  ∀ μ, μ ∈ ev → ∃ V, V ≠ vect_zero n ∧ (M • V = μ × V)%V.

Definition eigenvalues_and_norm_vectors n M ev eV :=
  (∀ V : vector T, V ∈ eV → vect_size V = n) ∧
  (∀ i j, 1 ≤ i ≤ n → 1 ≤ j ≤ n → i ≠ j → ev.(i)%L ≠ ev.(j)%L) ∧
  (∀ i, 1 ≤ i ≤ n → vect_squ_norm (nth (i - 1) eV (vect_zero n)) = 1%L) ∧
  (∀ i (μ : T) (V : vector T),
   1 ≤ i ≤ n
   → μ = ev.(i)%L
   → V = nth (i - 1) eV (vect_zero n)
   → (M • V)%V = (μ × V)%V).

(* Rayleigh quotient *)

Definition Rayleigh_quotient (M : matrix T) (v : vector T) :=
  (≺ v, M • v ≻ / ≺ v, v ≻)%L.

Theorem rngl_0_le_squ :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ n, (0 ≤ n * n)%L.
Proof.
intros Hop Hor *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
rewrite <- (rngl_mul_0_r Hos 0).
destruct (rngl_le_dec Hor 0%L n) as [Hnz| Hnz]. {
  apply rngl_mul_le_compat_nonneg; [ easy | easy | | ]. {
    split; [ now apply rngl_le_refl | easy ].
  } {
    split; [ now apply rngl_le_refl | easy ].
  }
} {
  apply rngl_mul_le_compat_nonpos; [ easy | easy | | ]. {
    split; [ | now apply rngl_le_refl ].
    now apply rngl_not_le in Hnz.
  } {
    split; [ | now apply rngl_le_refl ].
    now apply rngl_not_le in Hnz.
  }
}
Qed.

Definition in_ordered_field :=
  rngl_has_1 T = true ∧
  rngl_mul_is_comm T = true ∧
  rngl_has_opp T = true ∧
  rngl_has_eq_dec T = true ∧
  rngl_has_inv T = true ∧
  rngl_characteristic T = 0 ∧
  rngl_is_ordered T = true.

Theorem eq_vect_squ_0 :
  rngl_has_opp T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  rngl_is_ordered T = true →
  ∀ v, ≺ v, v ≻ = 0%L → v = vect_zero (vect_size v).
Proof.
intros Hop Hdo Hor * Hvvz.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
unfold vect_dot_mul in Hvvz.
apply vector_eq; [ | now cbn; rewrite repeat_length ].
intros i Hi.
destruct v as (la).
cbn in Hvvz, Hi |-*.
rewrite nth_repeat.
revert i Hi.
induction la as [| a]; intros; [ cbn in Hi; flia Hi | ].
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
  apply rngl_integral in Haz; [ | easy | ]. 2: {
    now apply Bool.orb_true_iff; left.
  }
  now destruct Haz.
}
rewrite Nat_sub_succ_1.
destruct i. {
  apply rngl_integral in Haz; [ | easy | easy ].
  now destruct Haz.
}
cbn.
replace i with (S i - 1) by flia Hi.
apply IHla.
flia Hi.
Qed.

Theorem Rayleigh_quotient_mul_scal_l_zero :
  rngl_has_opp_or_subt T = true →
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
  rewrite map2_ext_in with (g := λ _ _, 0%L). 2: {
    intros (i, j) Hi; cbn.
    apply in_combine_l in Hi.
    apply repeat_spec in Hi; subst i.
    rewrite rngl_mul_0_r; [ | easy ].
    now apply rngl_mul_0_l.
  }
  symmetry.
  rewrite map2_ext_in with (g := λ _ _, 0%L). 2: {
    intros (i, j) Hi.
    apply in_combine_l in Hi.
    apply repeat_spec in Hi; subst i.
    now apply rngl_mul_0_l.
  }
  easy.
} {
  rewrite map2_ext_in with (g := λ _ _, 0%L). 2: {
    intros (i, j) Hi; cbn.
    apply in_combine_l in Hi.
    apply repeat_spec in Hi; subst i.
    rewrite rngl_mul_0_r; [ | easy ].
    now apply rngl_mul_0_l.
  }
  symmetry.
  rewrite map2_ext_in with (g := λ _ _, 0%L). 2: {
    intros (i, j) Hi; cbn.
    apply in_combine_l in Hi.
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
  → c ≠ 0%L
  → Rayleigh_quotient M (c × V) = Rayleigh_quotient M V.
Proof.
intros Hof * Hsm Hsr Hcz.
destruct Hof as (Hon & Hic & Hop & Heq & Hin & Hch & Hor).
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
destruct (vect_eq_dec Heq V (vect_zero (mat_nrows M))) as [Hvz| Hvz]. {
  subst V; cbn.
  now apply Rayleigh_quotient_mul_scal_l_zero.
}
unfold Rayleigh_quotient.
rewrite <- mat_mul_scal_vect_comm; [ | easy | easy | | ]; cycle 1. {
  now apply squ_mat_is_corr.
} {
  now rewrite squ_mat_ncols.
}
rewrite vect_dot_mul_scal_mul_comm; [ | easy | easy ].
rewrite vect_dot_mul_scal_mul_comm; [ | easy | easy ].
rewrite vect_scal_mul_dot_mul_comm; [ | easy ].
rewrite vect_scal_mul_dot_mul_comm; [ | easy ].
do 2 rewrite rngl_mul_assoc.
unfold rngl_div.
rewrite Hin.
rewrite (rngl_inv_mul_distr Hon Hos Hin); cycle 1. {
  intros H.
  apply (rngl_eq_mul_0_l Hos) in H; [ easy | | easy ].
  apply Bool.orb_true_iff; right.
  apply rngl_has_inv_and_1_or_quot_iff; left.
  easy.
} {
  intros H.
  apply eq_vect_squ_0 in H; [ | easy | | easy ]. 2: {
    apply Bool.orb_true_iff; right.
    rewrite Heq, Bool.andb_true_iff; split; [ | easy ].
    now apply rngl_has_inv_and_1_or_quot_iff; left.
  }
  now rewrite Hsr in H.
}
rewrite rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
do 2 rewrite rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hon Hin); [ now rewrite rngl_mul_1_l | ].
intros H; apply Hcz.
apply (rngl_eq_mul_0_l Hos) in H; [ easy | | easy ].
apply Bool.orb_true_iff; right.
apply rngl_has_inv_and_1_or_quot_iff; left.
easy.
Qed.

Theorem Rayleigh_quotient_of_eigenvector :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  (rngl_is_integral_domain T || rngl_has_eq_dec T)%bool = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ (M : matrix T) V μ,
  V ≠ vect_zero (vect_size V)
  → (M • V = μ × V)%V
  → Rayleigh_quotient M V = μ.
Proof.
intros Hon Hic Hop Hii Hin Hdo * Hvz Hmv.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
specialize (proj2 rngl_has_inv_and_1_or_quot_iff) as Hi1.
specialize (Hi1 (or_introl (conj Hin Hon))).
unfold Rayleigh_quotient.
rewrite Hmv.
rewrite vect_dot_mul_scal_mul_comm; [ | easy | easy ].
apply (rngl_mul_div Hi1).
intros H.
apply eq_vect_squ_0 in H; [ easy | easy | | easy ].
apply Bool.orb_true_iff in Hii.
apply Bool.orb_true_iff.
destruct Hii as [Hii| Hii]; [ now left | right ].
rewrite Hii, Bool.andb_true_r.
now apply rngl_has_inv_and_1_or_quot_iff; left.
Qed.

Definition is_orthogonal_matrix (M : matrix T) :=
  (mat_transp M * M)%M = mI (mat_nrows M).

(* diagonal matrix with diagonal d being given *)

Definition mat_with_diag n d :=
  mk_mat
    (map (λ i, map (λ j, if i =? j then nth i d 0%L else 0%L) (seq 0 n))
       (seq 0 n)).

(* matrix with columns given as list of vectors *)

Definition mat_with_vect n Vl :=
  mk_mat
    (map (λ i, map (λ j, vect_el (nth j Vl (vect_zero n)) i) (seq 0 n))
       (seq 1 n)).

(*
End a.
Arguments mat_with_diag {T ro} n%nat d%list.
Arguments mat_with_vect {T ro} n%nat Vl%list.
Require Import RnglAlg.Nrl.
Compute (mat_with_diag 3 [7;1;2]).
Compute (
let Vl := [mk_vect [1;2;3]; mk_vect [4;5;6]; mk_vect [7;8;9]] in
mat_with_vect 3 Vl
).
*)

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

Theorem mat_with_vect_el : ∀ n lv i j,
  1 ≤ i ≤ n
  → 1 ≤ j ≤ n
  → mat_el (mat_with_vect n lv) i j = vect_el (nth (j - 1) lv (vect_zero n)) i.
Proof.
intros * Hin Hjn; cbn.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hin ].
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hjn ].
rewrite seq_nth; [ | flia Hjn ].
rewrite seq_nth; [ | flia Hin ].
rewrite Nat.add_0_l, Nat.add_comm, Nat.sub_add; [ | easy ].
easy.
Qed.

Theorem fold_vect_dot_mul' : ∀ U V,
  ∑ (i = 1, min (vect_size U) (vect_size V)), vect_el U i * vect_el V i =
  vect_dot_mul' U V.
Proof. easy. Qed.

Theorem mat_mul_vect_size : ∀ M V, vect_size (M • V) = mat_nrows M.
Proof.
intros; cbn.
now rewrite map_length.
Qed.

Theorem mat_mul_vect_dot_vect :
  rngl_mul_is_comm T = true →
  rngl_has_opp_or_subt T = true →
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
rewrite squ_mat_ncols; [ | easy ].
rewrite Nat.min_id.
destruct M as (ll).
destruct U as (lu).
destruct V as (lv); cbn.
cbn in Hur, Hvr, Hrz.
rewrite map_map.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite (List_map_nth' []). 2: {
   apply Nat.min_glb_lt_iff with (m := length lv).
   rewrite Hvr, Nat.min_id.
   flia Hi Hrz.
  }
  rewrite vect_dot_mul_dot_mul'; [ | easy ].
  unfold vect_dot_mul'; cbn.
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr, Hcl).
  rewrite (Hcl (nth (i - 1) ll [])). 2: {
    cbn; apply nth_In; flia Hi Hrz.
  }
  cbn; rewrite Hur, Nat.min_id.
  rewrite rngl_mul_summation_distr_r; [ | easy ].
  easy.
}
cbn.
unfold iter_seq at 1 2.
rewrite rngl_summation_summation_list_swap.
rewrite fold_iter_seq.
apply rngl_summation_eq_compat.
intros i Hi.
rewrite fold_iter_seq.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
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
intros j Hj.
f_equal.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj Hrz ].
rewrite seq_nth; [ | flia Hi Hrz ].
rewrite seq_nth; [ | flia Hj Hrz ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.add_sub.
easy.
Qed.

(* https://math.stackexchange.com/questions/82467/eigenvectors-of-real-symmetric-matrices-are-orthogonal *)

Theorem for_symm_squ_mat_eigen_vect_mat_is_ortho :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_eq_dec T = true →
  rngl_has_inv T = true →
  ∀ n (M : matrix T) ev eV A,
  is_symm_mat M
  → mat_nrows M = n
  → eigenvalues_and_norm_vectors n M ev eV
  → A = mat_with_vect n eV
  → (A⁺ * A = mI n)%M.
Proof.
intros Hon Hic Hos Heq Hin * Hsy Hr Hvv Hm.
specialize (proj2 rngl_has_inv_and_1_or_quot_iff) as Hi1.
specialize (Hi1 (or_introl (conj Hin Hon))).
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
  rewrite mat_transp_el; [ | | flia Hi | flia Hk ]. 2: {
    apply mat_with_vect_is_corr.
  }
  rewrite mat_with_vect_el; [ | easy | easy ].
  rewrite mat_with_vect_el; [ | easy | easy ].
  easy.
}
cbn.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj ].
rewrite seq_nth; [ | flia Hi ].
rewrite seq_nth; [ | flia Hj ].
cbn.
remember (nth (i - 1) eV (vect_zero n)) as vi eqn:Hvi.
remember (nth (j - 1) eV (vect_zero n)) as vj eqn:Hvj.
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
  destruct (le_dec i (length eV)) as [Hie| Hie]. 2: {
    apply Nat.nle_gt in Hie.
    rewrite <- H1.
    rewrite nth_overflow in Hvi; [ subst vi | flia Hie ].
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
    rewrite nth_overflow with (n := i - 1); [ | flia Hie ].
    now cbn; rewrite nth_repeat.
  }
  rewrite Hev in H1. 2: {
    rewrite Hvi.
    apply nth_In; flia Hi Hie.
  }
  now rewrite Hvj, <- Hvi.
} {
  rewrite δ_ndiag; [ | flia Hij Hi Hj ].
  destruct Hvv as (Hev & Hall_diff & Hall_norm_1 & Hvv).
  destruct (le_dec i (length eV)) as [Hie| Hie]. 2: {
    apply Nat.nle_gt in Hie.
    apply all_0_rngl_summation_0.
    intros k Hk.
    rewrite Hvi.
    rewrite nth_overflow; [ cbn | flia Hie ].
    rewrite nth_repeat.
    now apply rngl_mul_0_l.
  }
  destruct (le_dec j (length eV)) as [Hje| Hje]. 2: {
    apply Nat.nle_gt in Hje.
    apply all_0_rngl_summation_0.
    intros k Hk.
    rewrite Hvj.
    rewrite nth_overflow; [ cbn | flia Hje ].
    rewrite nth_repeat.
    now apply rngl_mul_0_r.
  }
  replace n with (min (vect_size vi) (vect_size vj)). 2: {
    rewrite Hev; [ | rewrite Hvi; apply nth_In; flia Hie Hi ].
    rewrite Hev; [ | rewrite Hvj; apply nth_In; flia Hje Hj ].
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
    apply nth_In; flia Hie Hi.
  }
  specialize (H1 H); clear H.
  assert (H : vect_size vj = n). {
    rewrite Hvj, Hev; [ easy | ].
    apply nth_In; flia Hje Hj.
  }
  specialize (H1 H); clear H.
  (* H1 : ≺ M • vi, vj ≻ = ≺ vi, M⁺ • vj ≻ *)
  specialize (Hvv i _ vi Hi eq_refl Hvi) as H2.
  rewrite H2 in H1.
  clear H2.
  replace (M⁺)%M with M in H1 by easy.
  specialize (Hvv j _ vj Hj eq_refl Hvj) as H2.
  rewrite H2 in H1.
  clear H2.
  rewrite vect_scal_mul_dot_mul_comm in H1; [ | easy ].
  rewrite vect_dot_mul_scal_mul_comm in H1; [ | easy | easy ].
  remember (rngl_eqb (≺ vi, vj ≻) 0%L) as vvij eqn:Hvvij.
  symmetry in Hvvij.
  destruct vvij; [ now apply rngl_eqb_eq | ].
  apply rngl_eqb_neq in Hvvij; [ | easy ].
  exfalso.
  apply (rngl_mul_cancel_r Hi1) in H1; [ | easy ].
  revert H1.
  apply Hall_diff; [ easy | easy | flia Hij Hi Hj ].
}
Qed.

(* A lemma to prove the theorem M = U . D . U^t
   see the comment for the theorem below *)
Lemma diagonalized_matrix_prop_1 :
  rngl_mul_is_comm T = true →
  rngl_has_opp_or_subt T = true →
  ∀ n (M : matrix T) ev eV D U,
  mat_nrows M = n
  → length eV = n
  → is_symm_mat M
  → eigenvalues_and_norm_vectors n M ev eV
  → (∀ V, V ∈ eV → vect_size V = n)
  → D = mat_with_diag n ev
  → U = mat_with_vect n eV
  → (M * U = U * D)%M.
Proof.
intros Hic Hos * Hrn Hlev Hsy Hvv Hevn Hd Ho.
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
assert (Hi' : i - 1 < n) by now apply Nat_1_le_sub_lt.
assert (Hj' : j - 1 < n) by now apply Nat_1_le_sub_lt.
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
rewrite squ_mat_ncols; [ | easy ].
rewrite squ_mat_ncols; [ | easy ].
rewrite Hrn.
replace (mat_nrows U) with n. 2: {
  rewrite Hmo; cbn.
  now rewrite List_map_seq_length.
}
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite <- Nat.sub_succ_l; [ | easy ].
  do 2 rewrite Nat_sub_succ_1.
  easy.
}
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite <- Nat.sub_succ_l; [ | easy ].
  do 2 rewrite Nat_sub_succ_1.
  easy.
}
cbn.
rewrite (rngl_summation_split j). 2: {
  split; [ flia | ].
  now apply -> Nat.succ_le_mono.
}
rewrite rngl_summation_split_last; [ | easy ].
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  assert (Hk' : k - 1 - 1 < n) by flia Hk Hj.
  rewrite Hmo; cbn.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | easy ].
  cbn.
  rewrite Hmd; cbn.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | easy ].
  cbn; rewrite if_eqb_eq_dec.
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite Nat_sub_succ_1.
  destruct (Nat.eq_dec (k - 1 - 1) (j - 1)) as [Hkj| Hkj]; [ flia Hk Hkj | ].
  now apply rngl_mul_0_r.
}
rewrite rngl_add_0_l.
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  assert (Hk' : k - 1 < n) by flia Hk.
  rewrite Hmd; cbn.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | easy ].
  cbn; rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (k - 1) (j - 1)) as [Hkj| Hkj]; [ flia Hk Hj Hkj | ].
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
  intros u Hu.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hu Hnz ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | flia Hu Hnz ].
  now cbn.
}
cbn.
specialize (Hvv j (ev.(j))%L) as H1.
specialize (H1 (nth (j - 1) eV (vect_zero n))).
specialize (H1 Hj eq_refl eq_refl).
remember (nth (j - 1) ev 0%L) as μ eqn:Hμ.
remember (nth (j - 1) eV (vect_zero n)) as V eqn:Hv.
symmetry.
apply (f_equal (λ x, vect_el x i)) in H1.
cbn - [ iter_seq ] in H1.
rewrite (List_map_nth' []) in H1; [ | now rewrite fold_mat_nrows, Hrn ].
rewrite (List_map_nth' 0%L) in H1. 2: {
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
remember (nth (i - 1) (mat_list_list M) []) as l eqn:Hl.
erewrite rngl_summation_eq_compat. 2: {
  intros u Hu.
  replace (nth (u - 1) l 0%L) with (vect_el (mk_vect l) u) by easy.
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite Nat_sub_succ_1.
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
now rewrite Nat.min_id.
Qed.

(* In the real case, the symmetric matrix M is diagonalisable in the
   sense that there exists an orthogonal matrix U (the columns of which
   are eigenvectors) and a diagonal matrix D the coefficients of which
   are eigenvalues μ_i such that
      M = U . D . U^t *)

Theorem diagonalized_matrix_prop : in_charac_0_field →
  ∀ n (M : matrix T) ev eV,
  mat_nrows M = n
  → length eV = n
  → (∀ V, V ∈ eV → vect_size V = n)
  → is_symm_mat M
  → eigenvalues_and_norm_vectors n M ev eV
  → ∀ D U,
  D = mat_with_diag n ev
  → U = mat_with_vect n eV
  → (M = U * D * U⁻¹)%M.
Proof.
intros Hif * Hrn Hlev Hevn Hsy Hvv * Hd Ho.
assert (H10 : rngl_characteristic T ≠ 1). {
  now rewrite (cf_characteristic Hif).
}
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
assert (H : rngl_has_opp T = true) by now destruct Hif.
specialize (Hos (or_introl H)); clear H.
move Hos before Hif.
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
assert (H : rngl_mul_is_comm T = true) by now destruct Hif.
specialize (H1 H Hos); clear H.
specialize (H1 n M ev eV D U Hrn Hlev Hsy Hvv Hevn Hd Ho).
generalize H1; intros H1v.
apply (f_equal (λ A, (A * U⁻¹)%M)) in H1.
rewrite <- mat_mul_assoc in H1; [ | now destruct Hif | | | ]; cycle 1. {
  now rewrite Ho, mat_with_vect_nrows.
} {
  now rewrite Ho, mat_with_vect_ncols.
} {
  rewrite Ho, mat_with_vect_nrows.
  rewrite squ_mat_ncols; [ easy | now destruct Hsy ].
}
assert (Hsu : is_square_matrix U = true). {
  rewrite Ho; apply mat_with_vect_is_square.
}
assert (Hdu : det U ≠ 0%L). {
  generalize Hvv; intros H.
  apply for_symm_squ_mat_eigen_vect_mat_is_ortho with (A := U) in H;
    try (now destruct Hif).
  rename H into Huu.
  apply (f_equal det) in Huu.
  rewrite (determinant_mul Hif) in Huu; [ | | easy | ]; cycle 1. {
    now apply mat_transp_is_square.
  } {
    rewrite mat_transp_nrows.
    now apply squ_mat_ncols.
  }
  generalize Hif; intros H.
  destruct H as (Hon, Hic, Hop, Hin, Hde, Hch).
  rewrite (determinant_transpose Hon Hic Hop) in Huu; [ | | easy ]. 2: {
    now rewrite Hch.
  }
  rewrite (det_mI Hon) in Huu; [ | easy ].
  intros H; rewrite H in Huu.
  rewrite rngl_mul_0_r in Huu; [ | easy ].
  symmetry in Huu; revert Huu.
  now apply rngl_1_neq_0_iff.
}
rewrite mat_mul_inv_diag_r in H1; [ | easy | | apply Hdu ]. {
  rewrite <- H1v.
  rewrite <- mat_mul_assoc; [ | now destruct Hif | | | ]; cycle 1. {
    now rewrite Ho, mat_with_vect_nrows.
  } {
    now rewrite Ho, mat_with_vect_ncols.
  } {
    rewrite Ho, mat_with_vect_nrows, squ_mat_ncols; [ easy | ].
    now unfold is_symm_mat in Hsy.
  }
  rewrite mat_mul_inv_diag_r; [ | easy | | apply Hdu ]. 2: {
    rewrite Ho.
    apply mat_with_vect_is_square.
  }
  symmetry.
  apply mat_mul_1_r; [ now destruct Hif | now destruct Hif | | ]. {
    unfold is_symm_mat in Hsy.
    now apply squ_mat_is_corr.
  }
  rewrite Ho, mat_with_vect_nrows; symmetry.
  rewrite <- Hrn.
  apply squ_mat_ncols.
  now destruct Hsy.
} {
  rewrite Ho.
  apply mat_with_vect_is_square.
}
Qed.

(* https://people.orie.cornell.edu/dpw/orie6334/Fall2016/lecture4.pdf *)
(* https://en.wikipedia.org/wiki/Min-max_theorem#Cauchy_interlacing_theorem *)

(* changing variable x as y = O⁺.x, the Rayleigh quotient R(M,x)
   is equal to
      Σ (i = 1, n), μ_i * y_i ^ 2 / Σ (i = 1, n), y_i ^ 2 *)

(* https://en.wikipedia.org/wiki/Rayleigh_quotient#Bounds_for_Hermitian_M *)
(* https://en.wikipedia.org/wiki/Normal_matrix *)
(* https://en.wikipedia.org/wiki/Min-max_theorem#Min-max_theorem *)
(* https://ecroot.math.gatech.edu/notes_linear.pdf *)

(* to be completed
Theorem Rayleigh_quotient_from_dot_mul : in_ordered_field →
  ∀ n (M : matrix T) D U v,
  vect_size v = n
  → Rayleigh_quotient M v = (≺ U • v, D • (U • v) ≻ / ≺ U • v, U • v ≻)%L.
Proof.
intros Hof * Hsv.
assert (Hcf : in_charac_0_field) by now destruct Hof.
unfold Rayleigh_quotient.
assert (Hdm : D = (U * M * U⁺)%M). {
  assert (M = (U⁺ * D * U)%M). {
    specialize (diagonalized_matrix_prop Hcf) as H1.
    specialize (H1 n M).
Print eigenvalues_and_norm_vectors.
...
  rewrite mat_mul_assoc; [ | easy | | | ]; try congruence.
    rewrite mat_mul_assoc; [ | easy | | | ]; try congruence.
    rewrite Huu1.
    rewrite mat_mul_1_l; [ | easy | | ]. 2: {
...

Theorem Rayleigh_quotient_from_ortho :
  ∀ n (M : matrix T) eigen_val eigen_vect U x y,
  U = mat_with_vect n eigen_vect
  → y = (U⁺ • x)%M
  → Rayleigh_quotient M x =
      ((∑ (i = 1, n), eigen_val.(i) * (vect_el y i) ^ 2) /
       (∑ (i = 1, n), vect_el y i ^ 2))%L.
Proof.
intros * HU Hy.
...

Theorem Rayleigh_quotient_from_ortho : in_ordered_field →
  rngl_characteristic ≠ 1 →
  ∀ n (M : matrix T) D U eV x y ev,
  mat_nrows M = n
  → vect_size x = n
  → n ≠ 0
  → is_symm_mat M
  → is_square_matrix U = true
  → is_square_matrix D = true
  → ≺ x, x ≻ = 1%L
  → eigenvalues_and_norm_vectors n M ev eV
  → U = mat_with_vect n eV
  → M = (U⁺ * D * U)%M
  → y = (U⁺ • x)%M
  → y ≠ vect_zero n
  → Rayleigh_quotient M x =
      ((∑ (i = 1, n), ev.(i) * (vect_el y i) ^ 2) /
       (∑ (i = 1, n), vect_el y i ^ 2))%L.
Proof.
intros Hof H10 * Hr Hsx Hnz Hsym Hsmu Hsmd Hx1 HeV HU Hmin Hmax Hyz.
(**)
Print Rayleigh_quotient.
assert
  (Hrqd :
     ∀ v,
       vect_size v = n
       → Rayleigh_quotient M v =
           (≺ U • v, D • (U • v) ≻ / ≺ U • v, U • v ≻)%L). {
  intros v Hsv.
  destruct Hof as (Hic & Hop & Heq & Hde & Hit & Hiv & Hor).
  assert (Hos : rngl_has_opp_or_subt T = true). {
    now apply rngl_has_opp_or_subt_iff; left.
  }
  unfold eigenvalues_and_norm_vectors in HeV.
  destruct HeV as (Hvs & Hvd & Hvn & Hmv).
  unfold Rayleigh_quotient.
  destruct Hsym as (Hsmm, Htm).
  assert (Hur : mat_nrows U = n). {
    apply (f_equal mat_nrows) in Hmin.
    rewrite mat_mul_nrows in Hmin.
    rewrite mat_mul_nrows in Hmin.
    rewrite mat_transp_nrows in Hmin.
    rewrite squ_mat_ncols in Hmin; [ | easy ].
    congruence.
  }
  assert (Huc : mat_ncols U = n). {
    now rewrite squ_mat_ncols.
  }
  assert (Hu'r : mat_nrows U⁺ = n). {
    now rewrite mat_transp_nrows.
  }
  assert (Hu'c : mat_ncols U⁺ = n). {
    rewrite mat_transp_ncols.
    rewrite Huc.
    now apply Nat.eqb_neq in Hnz; rewrite Hnz.
  }
(* here I am waiting for me to have implemented:
   - polynomials → ok
   - characteristic polynomials
   - proof that all polynomials of degree n have n roots
   - building eigenvalues and eigenvectors
   - diagonalization
   - and then U and D are the result of this diagonalization
*)
...
  assert (Hdc : mat_ncols D = n) by _admit.
  assert (H1 : mat_nrows (U⁺ * D) = n). {
    rewrite mat_mul_nrows, mat_transp_nrows.
    congruence.
  }
  assert (H2 : mat_ncols (U⁺ * D) = n). {
    rewrite mat_mul_ncols; [ congruence | ].
    rewrite mat_transp_nrows.
    rewrite squ_mat_ncols; [ | easy ].
    congruence.
  }
  assert (Huu1 : (U * U⁺ = mI n)%M) by _admit.
  assert (Huu2 : (U⁺ * U = mI n)%M) by _admit.
  assert (Hdm : D = (U * M * U⁺)%M). {
    rewrite Hmin.
    rewrite mat_mul_assoc; [ | easy | | | ]; try congruence.
    rewrite mat_mul_assoc; [ | easy | | | ]; try congruence.
    rewrite Huu1.
    rewrite mat_mul_1_l; [ | easy | | ]. 2: {
...
    rewrite mat_mul_1_l; [ | easy | _admit | _admit ].
    rewrite <- mat_mul_assoc; [ | easy | _admit | _admit | _admit ].
    rewrite Huu1.
    symmetry; apply mat_mul_1_r; [ easy | _admit | _admit ].
  }
  assert (Hdd : D⁺%M = D). {
    rewrite Hdm.
    rewrite mat_transp_mul; [ | easy | _admit | _admit | _admit | _admit | _admit ].
    rewrite mat_transp_involutive; [ | _admit ].
    rewrite mat_transp_mul; [ | easy | _admit | _admit | _admit | _admit | _admit ].
    rewrite <- Htm.
    rewrite mat_mul_assoc; [ | easy | _admit | _admit | _admit ].
    easy.
  }
  f_equal. 2: {
    rewrite mat_mul_vect_dot_vect; [ | easy | easy | easy | _admit | _admit ].
    rewrite mat_vect_mul_assoc; [ | easy | _admit | _admit | _admit | _admit ].
    rewrite Huu2.
    now rewrite mat_vect_mul_1_l.
  }
  rewrite Htm.
  rewrite <- mat_mul_vect_dot_vect; try easy; try congruence.
  rewrite Hmin.
  rewrite <- mat_vect_mul_assoc; [ | easy | _admit | _admit | _admit | _admit ].
  rewrite mat_mul_vect_dot_vect; [ | easy | _admit | _admit | _admit | _admit ].
  rewrite mat_transp_mul; [ | easy | _admit | _admit | _admit | _admit | _admit ].
  rewrite mat_transp_involutive; [ | _admit ].
  rewrite <- mat_vect_mul_assoc; [ | easy | _admit | _admit | _admit | _admit ].
  now rewrite Hdd.
}
(* bon, il faut que je prouve que, si M est symétrique, alors
   M est diagonalisable avec M = U⁺ D U, avec
   - U est orthogonale, c'est-à-dire U U⁺ = 1
   - D est diagonale
   - la diagonale de D contient les valeurs propres de M
*)
...
assert (mat_is_ortho U = true). {
...
}
assert (mat_is_diag_and_hold_eigenv M). {
...
}
...
assert (Huc : mat_ncols U = n). {
  apply (f_equal mat_nrows) in Hmin.
  do 2 rewrite mat_mul_nrows in Hmin.
  rewrite mat_transp_nrows in Hmin.
  congruence.
}
assert (Hur : mat_nrows U = n). {
  now rewrite squ_mat_ncols in Huc.
}
assert (HneV : n ≤ length eV). {
  unfold eigenvalues_and_norm_vectors in HeV.
  destruct HeV as (Hvs & Hvd & Hvn & Hmv).
  apply Nat.nlt_ge; intros HeVl.
  specialize (Hvn n) as H1.
  assert (H : 1 ≤ n ≤ n) by now split; [ flia Hnz | ].
  specialize (H1 H); clear H.
  rewrite nth_overflow in H1; [ | flia HeVl ].
  unfold vect_squ_norm in H1.
  unfold vect_dot_mul in H1.
  rewrite all_0_rngl_summation_list_0 in H1. 2: {
    intros a Ha; cbn in Ha.
    apply in_map2_iff in Ha.
    rewrite repeat_length in Ha.
    rewrite Nat.min_id in Ha.
    destruct Ha as (i & Hi & b & c & Hbc).
    rewrite List_nth_repeat in Hbc.
    destruct (lt_dec i n) as [H| H]; [ clear H | flia Hi H ].
    rewrite rngl_mul_0_l in Hbc; [ easy | now destruct Hof; left ].
  }
  symmetry in H1.
  apply rngl_1_neq_0 in H1; [ easy | now destruct Hof ].
}
set (nth_eV := λ i, nth (i - 1) eV (vect_zero n)).
assert (Hyi : ∀ i, 1 ≤ i ≤ n → vect_el y i = ≺ nth_eV i, x ≻). {
  intros i Hi.
  unfold nth_eV.
  rewrite Hmax; cbn.
  rewrite map_map, Hur, Huc.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
  rewrite HU; cbn.
  f_equal.
  rewrite seq_nth; [ | flia Hi ].
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite <- seq_shift.
  rewrite map_map.
  erewrite map_ext_in. 2: {
    intros j Hj.
    rewrite Nat_sub_succ_1.
    apply in_seq in Hj.
    rewrite (List_map_nth' 0); [ | now rewrite List_map_seq_length ].
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
    rewrite seq_nth; [ | flia Hi ].
    rewrite Nat.add_0_l.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite Nat.add_0_l.
    unfold vect_el.
    now rewrite Nat_sub_succ_1.
  }
  destruct (lt_dec (i - 1) (length eV)) as [HieV| HieV]. 2: {
    apply Nat.nlt_ge in HieV.
    rewrite nth_overflow; [ cbn | easy ].
    erewrite map_ext_in. 2: {
      intros j Hj.
      now rewrite nth_repeat.
    }
    now rewrite <- List_repeat_as_map.
  }
  remember (nth (i - 1) eV (vect_zero n)) as v eqn:Hv.
  replace n with (length (vect_list v)). 2: {
    rewrite Hv; cbn.
    rewrite fold_vect_size.
    unfold eigenvalues_and_norm_vectors in HeV.
    destruct HeV as (H1, HeV).
    now apply H1, nth_In.
  }
  rewrite <- List_map_nth_seq.
  now destruct v.
}
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite Hyi; [ | easy ].
  easy.
}
cbn - [ rngl_power ].
erewrite rngl_summation_eq_compat with (g := λ _, (_ ^ _)%L). 2: {
  now intros; cbn; rewrite rngl_mul_1_r, Hyi.
}
cbn - [ "^"%L ].
unfold Rayleigh_quotient.
rewrite Hx1.
rewrite rngl_div_1_r; [ | now destruct Hof; left | now destruct Hof ].
(**)
unfold eigenvalues_and_norm_vectors in HeV.
destruct HeV as (Hvs & Hvd & Hvn & Hmv).
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi; cbn.
  rewrite rngl_mul_1_r, rngl_mul_assoc.
  rewrite <- vect_scal_mul_dot_mul_comm with (a := (ev.(i))%L). 2: {
    now destruct Hof; left.
  }
  rewrite <- (Hmv i); [ | easy | easy | easy ].
  rewrite mat_mul_vect_dot_vect; [ | | | | | congruence ]; cycle 1. {
    now destruct Hof.
  } {
    now destruct Hof; left.
  } {
    now destruct Hsym.
  } {
    rewrite Hr; apply Hvs.
    apply nth_In; flia HneV Hi.
  }
  unfold is_symm_mat in Hsym.
  replace (M⁺)%M with M by easy.
  easy.
}
cbn.
Search vect_dot_mul.
...
(*
  ============================
  ≺ x, M • x ≻ =
  ((∑ (i = 1, n), ≺ nth_eV i, M • x ≻ * ≺ nth_eV i, x ≻) /
   (∑ (i = 1, n), ≺ nth_eV i, x ≻ * ≺ nth_eV i, x ≻))%L
*)
unfold is_symm_mat in Hsym.
destruct Hsym as (Hsmm, Htm).
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite <- (mat_transp_involutive _ M) at 1. 2: {
    now apply squ_mat_is_corr.
  }
  rewrite <- mat_mul_vect_dot_vect; cycle 1. {
    now destruct Hof.
  } {
    now destruct Hof; left.
  } {
    now rewrite <- Htm.
  } {
    rewrite mat_transp_nrows.
    rewrite Hvs; [ | apply nth_In; flia Hi HneV ].
    now rewrite squ_mat_ncols, Hr.
  } {
    rewrite mat_transp_nrows, Hsx.
    now rewrite squ_mat_ncols, Hr.
  }
  rewrite <- Htm.
  erewrite (Hmv i _ _ Hi eq_refl); [ | easy ].
  rewrite vect_scal_mul_dot_mul_comm; [ | now destruct Hof; left ].
  easy.
}
cbn; symmetry.
...
  ============================
  (≺ x, M • x ≻ / ≺ x, x ≻)%L =
  ((∑ (i = 1, n), ev.(i) * ≺ nth_eV i, x ≻ * ≺ nth_eV i, x ≻) /
   (∑ (i = 1, n), ≺ nth_eV i, x ≻ * ≺ nth_eV i, x ≻))%L
...
Search (≺ _, _ • _ ≻).
mat_mul_vect_dot_vect:
...
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  specialize (Hvn i Hi) as H1.
  unfold vect_squ_norm in H1.
  fold (nth_eV i) in H1.
  rewrite <- vect_scal_mul_dot_mul_comm; [ | now destruct Hof; left ].
  easy.
}
cbn.
...
Search (≺ _ • _, _ ≻).
Search (≺ _ , _ ≻ * _)%L.
...
assert (∑ (i = 1, n), rngl_squ (vect_el y i) = ≺ y, y ≻). {
  rewrite vect_dot_mul_dot_mul'; [ | now destruct Hof; left ].
  unfold vect_dot_mul'.
  rewrite Nat.min_id.
  replace (vect_size y) with n; [ easy | ].
  rewrite Hmax, mat_mul_vect_size, mat_transp_nrows.
  now rewrite HU, mat_with_vect_ncols.
}
rewrite H.
...
Search vect_dot_mul.
Search (matrix _ → vector _ → _).
Search (vector _ → matrix _ → _).
Print vect_dot_mul.
...
Print vect_dot_mul'.
(*
  R(M,x) = (x*Mx) / (x*x)
  eigenpair (λ_i, v_i)
  y_i = v_i* x
*)
...
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
  now rewrite squ_mat_ncols in Hcu.
}
move Hru before Hsy; move Hcu before Hru.
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
Search (_ = _ * _ ↔ _ / _ = _)%L.
Search (_ = _ * _ ↔ _ = _ / _)%L.
Search (_ * _ = _ ↔ _ / _ = _)%L.
Search (_ * _ = _ ↔ _ = _ / _)%L.
Search (_ = _ / _)%L.
...
*)
apply rngl_div_div_mul_mul; [ easy | easy | | | ]. {
  now apply rngl_1_neq_0.
(*
  enough (H : ≺ x, x ≻ ≠ 0%L). {
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
  enough (H : ≺ y, y ≻ ≠ 0%L). {
    rewrite vect_dot_mul_dot_mul' in H; [ | now left ].
    unfold vect_dot_mul' in H.
    now rewrite Nat.min_id, Hsy in H.
  }
  intros H.
  apply eq_vect_squ_0 in H; [ | easy | easy | easy | easy ].
  now rewrite Hsy in H.
}
rewrite rngl_mul_1_l.
...
rewrite Hmax.
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
  now rewrite squ_mat_ncols in Hcu.
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
unfold "/"%L.
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
      (Σ (i = 1, n), nth i ev 0%L * rngl_squ (vect_el y i) /
       Σ (i = 1, n), rngl_squ (vect_el y i))%L.
Proof.
intros * Hsy Hev Hmin Hmax.
...
*)

(* The Rayleigh quotient reaches its minimum value μ_min (the smallest
   eigenvalue of M) when x is v_min (the corresponding eigenvector).
   Similarly, R (M,x) ≤ μ_max and R (M,v_max) = μ_max *)

(* to be completed
Theorem glop : ∀ n (M : matrix T) x sev μ_min μ_max,
  eigenvalues M sev
  → Sorted rngl_le sev
  → μ_min = hd 0%L sev
  → μ_max = last sev 0%L
  → (μ_min ≤ Rayleigh_quotient M x ≤ μ_max)%L.
Proof.
intros * Hev Hsev Hmin Hmax.
...
*)

(* min-max theorem, or variational theorem, or Courant–Fischer–Weyl min-max principle *)

(* Lemma 2.1 *)

(* to be completed
Theorem lemma_2_1 :
  ∀ n m l (A : matrix T) (B : matrix (n - length l) (n - length l) T)
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
    (nth (i-n+m) seva 0%L ≤ nth i sevb 0%L ≤ nth i seva 0%L)%L.
Proof.
intros * Hm Hmn Hisa Hb Heva Hevb Hsa Hsb * Him.
...
*)

End a.
