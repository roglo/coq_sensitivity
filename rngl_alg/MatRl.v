(* square matrix ring like algebra *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.
(*
Require Import Init.Nat.
*)

Require Import Main.Misc.
Require Import Main.RingLike Main.IterAdd (*IterMul IterAnd*).
(*
Require Import MyVector Signature.
*)
Require Import Main.Matrix.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.
Context {Hro : @rngl_has_opp T ro = true}.

Theorem mZ_is_square_matrix : ∀ n,
  (mat_nrows (mZ n n) =? n) && is_square_matrix (mZ n n) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split. {
  cbn; rewrite repeat_length.
  apply Nat.eqb_refl.
}
apply is_scm_mat_iff.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n; cbn | ].
split; [ now rewrite mZ_nrows, mZ_ncols | ].
intros la Hla.
cbn in Hla.
apply repeat_spec in Hla; subst la.
now cbn; do 2 rewrite repeat_length.
Qed.

Theorem mI_square_matrix_prop : ∀ n,
  (mat_nrows (mI n) =? n) && is_square_matrix (mI n) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply mI_is_square_matrix ].
cbn; rewrite List_map_seq_length.
apply Nat.eqb_refl.
Qed.

Theorem square_matrix_add_prop : ∀ n (MA MB : square_matrix n T),
  (mat_nrows (sm_mat MA + sm_mat MB) =? n) &&
  is_square_matrix (sm_mat MA + sm_mat MB) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply square_matrix_add_is_square ].
apply Nat.eqb_eq; cbn.
rewrite map2_length.
do 2 rewrite fold_mat_nrows.
do 2 rewrite squ_mat_nrows.
apply Nat.min_id.
Qed.

Theorem square_matrix_mul_prop : ∀ n (MA MB : square_matrix n T),
  (mat_nrows (sm_mat MA * sm_mat MB) =? n) &&
  is_square_matrix (sm_mat MA * sm_mat MB) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply square_matrix_mul_is_square ].
apply Nat.eqb_eq; cbn.
rewrite List_map_seq_length.
apply squ_mat_nrows.
Qed.

Theorem square_matrix_opp_prop : ∀ n (M : square_matrix n T),
  (mat_nrows (- sm_mat M) =? n) && is_square_matrix (- sm_mat M) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply square_matrix_opp_is_square ].
apply Nat.eqb_eq; cbn.
rewrite map_length.
apply squ_mat_nrows.
Qed.

Definition smZ n : square_matrix n T :=
  {| sm_mat := mZ n n;
     sm_prop := mZ_is_square_matrix n |}.

Definition smI n : square_matrix n T :=
  {| sm_mat := mI n;
     sm_prop := mI_square_matrix_prop n |}.

Definition square_matrix_add {n} (MA MB : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := (sm_mat MA + sm_mat MB);
     sm_prop := square_matrix_add_prop MA MB |}.

Definition square_matrix_mul {n} (MA MB : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := sm_mat MA * sm_mat MB;
     sm_prop := square_matrix_mul_prop MA MB |}.

Definition square_matrix_opp {n} (M : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := - sm_mat M;
     sm_prop := square_matrix_opp_prop M |}.

Canonical Structure mat_ring_like_op n : ring_like_op (square_matrix n T) :=
  {| rngl_zero := smZ n;
     rngl_one := smI n;
     rngl_add := square_matrix_add;
     rngl_mul := square_matrix_mul;
     rngl_opt_opp := Some square_matrix_opp;
     rngl_opt_inv := None;
     rngl_opt_sous := None;
     rngl_opt_quot := None;
     rngl_le := phony_mat_le |}.

Existing Instance mat_ring_like_op.

Theorem mat_ncols_of_nat {n} : ∀ i,
  mat_ncols (@sm_mat n T (rngl_of_nat i)) = n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n; destruct i | ].
induction i; [ now apply mZ_ncols | cbn ].
rewrite mat_add_ncols.
rewrite mI_ncols, IHi.
apply Nat.min_id.
Qed.

Theorem sm_mat_of_nat :
  @rngl_has_opp T ro = true ∨ @rngl_has_sous T ro = true
  → ∀ n m,
     sm_mat (rngl_of_nat m : square_matrix n T) = (rngl_of_nat m × mI n)%M.
(*
  rngl_has_opp = true ∨ rngl_has_sous = true
  → ∀ n m : nat, sm_mat (rngl_of_nat m) = (rngl_of_nat m × mI n)%M
*)
Proof.
cbn.
intros Hop; cbn.
induction m; cbn. {
  unfold "×"%M, mZ, mI.
  f_equal; cbn.
  rewrite map_map.
  rewrite List_repeat_as_map.
  apply map_ext_in.
  intros i Hi.
  rewrite List_repeat_as_map.
  rewrite map_map.
  apply map_ext_in.
  intros j Hj.
  now symmetry; apply rngl_mul_0_l.
}
rewrite mat_mul_scal_l_add_distr_r.
now rewrite mat_mul_scal_1_l, IHm.
Qed.

Theorem mat_el_of_nat_diag {n} : ∀ m i,
  i < n
  → mat_el
      (sm_mat
         (@rngl_of_nat (square_matrix n T) (mat_ring_like_op n) m)) i i =
    rngl_of_nat m.
(*
  ∀ m i : nat, i < n → mat_el (sm_mat (rngl_of_nat m)) i i = rngl_of_nat m
*)
Proof.
intros * Hin.
rewrite sm_mat_of_nat; [ | now left ].
cbn.
rewrite map_map.
rewrite List_map_nth' with (a := 0); [ | now rewrite seq_length ].
rewrite List_map_nth' with (a := 0%F). 2: {
  now rewrite List_map_seq_length.
}
rewrite List_map_nth' with (a := 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ cbn | easy ].
unfold δ.
now rewrite Nat.eqb_refl, rngl_mul_1_r.
Qed.

Theorem rngl_of_nat_is_correct_matrix {n} :
  rngl_characteristic = 0
  → ∀ i, is_correct_matrix (@sm_mat n T (rngl_of_nat i)) = true.
Proof.
intros Hch *.
apply is_scm_mat_iff.
split. {
  intros Hc.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    now subst n; destruct i.
  }
  destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
    subst i; cbn in Hc |-*.
    now rewrite mZ_ncols in Hc.
  }
  unfold mat_ncols in Hc.
  unfold mat_nrows.
  apply length_zero_iff_nil in Hc.
  apply length_zero_iff_nil.
  remember (mat_list_list _) as lla eqn:Hlla.
  symmetry in Hlla.
  apply (f_equal (λ ll, nth 0 (nth 0 ll []) 0%F)) in Hlla.
  rewrite fold_mat_el in Hlla.
  rewrite List_hd_nth_0 in Hc.
  rewrite Hc in Hlla; cbn in Hlla.
  exfalso; clear lla Hc.
  destruct i; [ easy | clear Hiz ].
  cbn - [ mat_el ] in Hlla.
  apply Nat.neq_0_lt_0 in Hnz.
  rewrite mat_el_add in Hlla; cycle 1. {
    apply mI_is_correct_matrix.
  } {
    apply square_matrix_is_correct.
  } {
    now rewrite mI_nrows.
  } {
    now rewrite squ_mat_nrows.
  } {
    now rewrite mI_ncols.
  } {
    now rewrite squ_mat_ncols.
  }
  rewrite mat_el_mI_diag in Hlla; [ | easy ].
  rewrite mat_el_of_nat_diag in Hlla; [ | easy ].
  specialize rngl_characteristic_prop as H1.
  rewrite Hch in H1; cbn in H1.
  now apply (H1 i).
} {
  intros l Hl.
  rewrite mat_ncols_of_nat.
  remember (rngl_of_nat i) as M eqn:HM.
  destruct M as (M, Hm); cbn in Hl.
  clear HM.
  apply Bool.andb_true_iff in Hm.
  destruct Hm as (Hr, Hm).
  apply Nat.eqb_eq in Hr.
  apply is_scm_mat_iff in Hm.
  destruct Hm as (Hcr & Hc).
  rewrite Hr in Hc.
  now apply Hc.
}
Qed.

Theorem squ_mat_add_comm {n} : ∀ (MA MB : square_matrix n T),
  (MA + MB)%F = (MB + MA)%F.
Proof.
intros.
apply square_matrix_eq.
apply mat_add_comm.
Qed.

Theorem squ_mat_add_assoc {n} : ∀ (MA MB MC : square_matrix n T),
  (MA + (MB + MC) = (MA + MB) + MC)%F.
Proof.
intros.
apply square_matrix_eq.
apply mat_add_assoc.
Qed.

Theorem squ_mat_add_0_l {n} : ∀ M : square_matrix n T, (0 + M)%F = M.
Proof.
intros.
apply square_matrix_eq.
cbn.
apply mat_add_0_l; cycle 1. {
  symmetry; apply squ_mat_nrows.
} {
  symmetry; apply squ_mat_ncols.
}
apply square_matrix_is_correct.
Qed.

Theorem squ_mat_mul_assoc {n} : ∀ (MA MB MC : square_matrix n T),
  (MA * (MB * MC) = (MA * MB) * MC)%F.
Proof.
intros.
apply square_matrix_eq.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb).
destruct MC as (MC & Hc); cbn.
apply Bool.andb_true_iff in Ha, Hb, Hc.
destruct Ha as (Hra, Ha).
destruct Hb as (Hrb, Hb).
destruct Hc as (Hrc, Hc).
apply Nat.eqb_eq in Hra, Hrb, Hrc.
move MB before MA; move MC before MB.
move Hrb before Hra; move Hrc before Hrb.
apply is_scm_mat_iff in Ha.
apply is_scm_mat_iff in Hb.
apply is_scm_mat_iff in Hc.
destruct Ha as (Hcra & Hca).
destruct Hb as (Hcrb & Hcb).
destruct Hc as (Hcrc & Hcc).
move Hrb before Hra; move Hrc before Hrb.
move Hcrb before Hcra; move Hcrc before Hcrb.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n; cbn.
  unfold "*"%M; cbn.
  now rewrite Hra, Hrb.
}
apply mat_mul_assoc; [ easy | | | ]. {
  now rewrite Hrb.
} {
  intros H; apply Hnz.
  apply Hcrb in H.
  rewrite <- Hrb; apply H.
} {
  rewrite Hrb.
  unfold mat_ncols.
  rewrite Hra in Hca.
  apply Hca.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hra.
}
Qed.

Theorem squ_mat_mul_1_l {n} : ∀ M : square_matrix n T, (1 * M)%F = M.
Proof.
intros.
apply square_matrix_eq; cbn.
apply mat_mul_1_l; [ easy | | symmetry; apply squ_mat_nrows ].
apply square_matrix_is_correct.
Qed.

Theorem squ_mat_mul_add_distr_l {n} : ∀ (MA MB MC : square_matrix n T),
  (MA * (MB + MC) = MA * MB + MA * MC)%F.
Proof.
intros.
apply square_matrix_eq.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb).
destruct MC as (MC & Hc); cbn.
move MB before MA; move MC before MB.
apply Bool.andb_true_iff in Ha, Hb, Hc.
destruct Ha as (Hra, Ha).
destruct Hb as (Hrb, Hb).
destruct Hc as (Hrc, Hc).
apply Nat.eqb_eq in Hra, Hrb, Hrc.
move MB before MA; move MC before MB.
move Hrb before Hra; move Hrc before Hrb.
apply is_scm_mat_iff in Ha.
apply is_scm_mat_iff in Hb.
apply is_scm_mat_iff in Hc.
destruct Ha as (Hcra & Hca).
destruct Hb as (Hcrb & Hcb).
destruct Hc as (Hcrc & Hcc).
move Hrb before Hra; move Hrc before Hrb.
move Hcrb before Hcra; move Hcrc before Hcrb.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n; cbn.
  unfold "*"%M, "+"%M; cbn.
  now rewrite Hra.
}
apply mat_mul_add_distr_l. {
  apply is_scm_mat_iff.
  split; [ easy | ].
  intros l Hl.
  rewrite Hcb; [ | easy ].
  symmetry; apply Hcb.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hrb.
} {
  apply is_scm_mat_iff.
  split; [ easy | ].
  intros l Hl.
  rewrite Hcc; [ | easy ].
  symmetry; apply Hcc.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hrc.
} {
  now rewrite Hrb.
} {
  rewrite Hrb; unfold mat_ncols.
  rewrite Hra in Hca.
  apply Hca.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hra.
} {
  congruence.
} {
  unfold mat_ncols.
  rewrite Hcb. 2: {
    apply List_hd_in, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hrb.
  }
  rewrite Hcc. 2: {
    apply List_hd_in, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hrc.
  }
  congruence.
}
Qed.

Theorem squ_mat_opt_1_neq_0 {n} :
  if rngl_has_1_neq_0 && (n ≠? 0) then
    @rngl_one _ (mat_ring_like_op n) ≠
    @rngl_zero _ (mat_ring_like_op n)
  else not_applicable.
(*
  if rngl_has_1_neq_0 && negb (n =? 0) then 1%F ≠ 0%F else not_applicable.
*)
Proof.
remember (rngl_has_1_neq_0 && (n ≠? 0)) as b eqn:Hb.
symmetry in Hb.
destruct b; [ | easy ].
apply Bool.andb_true_iff in Hb.
destruct Hb as (H10, Hb).
apply Bool.negb_true_iff in Hb.
apply Nat.eqb_neq in Hb.
intros H; cbn in H.
unfold smI, smZ in H.
injection H; clear H; intros H.
destruct n; [ easy | ].
cbn in H.
injection H; intros H1 H2.
now apply rngl_1_neq_0.
Qed.

Theorem squ_mat_mul_1_r {n} : ∀ M : square_matrix n T, (M * 1)%F = M.
Proof.
intros.
apply square_matrix_eq; cbn.
apply mat_mul_1_r; [ easy | | symmetry; apply squ_mat_ncols ].
apply square_matrix_is_correct.
Qed.

Theorem squ_mat_mul_add_distr_r {n} : ∀ (MA MB MC : square_matrix n T),
  ((MA + MB) * MC = MA * MC + MB * MC)%F.
Proof.
intros.
apply square_matrix_eq.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb).
destruct MC as (MC & Hc); cbn.
move MB before MA; move MC before MB.
apply Bool.andb_true_iff in Ha, Hb, Hc.
destruct Ha as (Hra, Ha).
destruct Hb as (Hrb, Hb).
destruct Hc as (Hrc, Hc).
apply Nat.eqb_eq in Hra, Hrb, Hrc.
move MB before MA; move MC before MB.
move Hrb before Hra; move Hrc before Hrb.
apply is_scm_mat_iff in Ha.
apply is_scm_mat_iff in Hb.
apply is_scm_mat_iff in Hc.
destruct Ha as (Hcra & Hca).
destruct Hb as (Hcrb & Hcb).
destruct Hc as (Hcrc & Hcc).
move Hrb before Hra; move Hrc before Hrb.
move Hcrb before Hcra; move Hcrc before Hcrb.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n; cbn.
  unfold "*"%M, "+"%M; cbn.
  rewrite map2_length; cbn.
  do 2 rewrite fold_mat_nrows.
  now rewrite Hra.
}
apply mat_mul_add_distr_r; [ easy | | | | | ]. {
  apply is_scm_mat_iff.
  split; [ easy | ].
  intros l Hl.
  rewrite Hca; [ | easy ].
  symmetry; apply Hca.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hra.
} {
  apply is_scm_mat_iff.
  split; [ easy | ].
  intros l Hl.
  rewrite Hcb; [ | easy ].
  symmetry; apply Hcb.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hrb.
} {
  now rewrite Hra.
} {
  congruence.
} {
  unfold mat_ncols.
  rewrite Hca. 2: {
    apply List_hd_in, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hra.
  }
  rewrite Hcb. 2: {
    apply List_hd_in, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hrb.
  }
  congruence.
}
Qed.

Theorem squ_mat_opt_add_opp_l {n} :
  if @rngl_has_opp (square_matrix n T) (mat_ring_like_op n) then
    ∀ M : square_matrix n T, (- M + M)%F = 0%F
  else not_applicable.
(*
  if rngl_has_opp then ∀ M : square_matrix n T, (- M + M)%F = 0%F
  else not_applicable.
*)
Proof.
remember (@rngl_has_opp (square_matrix n T) (mat_ring_like_op n)) as b
  eqn:Hb.
symmetry in Hb.
destruct b; [ | easy ].
intros M; cbn.
apply square_matrix_eq; cbn.
destruct M as (M & Hs); cbn.
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hr, Hs).
apply Nat.eqb_eq in Hr.
apply is_scm_mat_iff in Hs.
destruct Hs as (Hcr & Hc).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n; cbn.
  unfold mat_opp, "+"%M, mZ; cbn.
  apply length_zero_iff_nil in Hr.
  now rewrite Hr.
}
apply mat_add_opp_l; [ easy | easy | | easy | ]. 2: {
  unfold mat_ncols.
  rewrite Hr in Hc.
  symmetry; apply Hc.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hr.
}
apply is_scm_mat_iff.
split; [ easy | ].
intros l Hl.
unfold mat_ncols.
rewrite Hc; [ | easy ].
symmetry; apply Hc.
apply List_hd_in, Nat.neq_0_lt_0.
now rewrite fold_mat_nrows, Hr.
Qed.

Theorem squ_mat_opt_eq_dec {n} :
  if rngl_has_dec_eq then ∀ MA MB : square_matrix n T, {MA = MB} + {MA ≠ MB}
  else not_applicable.
Proof.
remember rngl_has_dec_eq as b eqn:Hed; symmetry in Hed.
destruct b; [ | easy ].
intros.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb).
move MB before MA.
destruct (mat_eq_dec Hed MA MB) as [Hab| Hab]. {
  left; subst MB.
  now apply square_matrix_eq.
} {
  right; intros H; apply Hab; clear Hab.
  now injection H.
}
Qed.

Theorem squ_mat_characteristic_prop {n} :
  if (if n =? 0 then 1 else rngl_characteristic) =? 0
  then
    ∀ i, @rngl_of_nat (square_matrix n T) (mat_ring_like_op n) (S i) ≠ 0%F
  else
    @rngl_of_nat (square_matrix n T) (mat_ring_like_op n)
      (if n =? 0 then 1 else rngl_characteristic) = 0%F.
Proof.
rewrite (if_eqb_eq_dec n).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  now apply square_matrix_eq.
}
apply Nat.neq_0_lt_0 in Hnz.
specialize @rngl_characteristic_prop as H1.
specialize (H1 T ro rp).
rewrite if_eqb_eq_dec in H1 |-*.
destruct (Nat.eq_dec rngl_characteristic 0) as [Hch| Hcn]. {
  intros i Hi.
  apply (f_equal (λ M, mat_el (sm_mat M) 0 0)) in Hi.
  cbn in Hi.
  rewrite List_nth_repeat in Hi.
  destruct (lt_dec 0 n) as [H| H]; [ clear H | flia Hnz H ].
  rewrite List_nth_repeat in Hi.
  destruct (lt_dec 0 n) as [H| H]; [ clear H | flia Hnz H ].
  rewrite map2_map_l in Hi.
  rewrite map2_nth with (a := 0) (b := []) in Hi; cycle 1. {
    now rewrite seq_length.
  } {
    rewrite fold_mat_nrows.
    clear Hi.
    induction i; cbn; [ now rewrite repeat_length | ].
    rewrite map2_length, List_map_seq_length.
    rewrite fold_mat_nrows.
    flia Hnz IHi.
  }
  rewrite map2_nth with (a := 0%F) (b := 0%F) in Hi; cycle 1. {
    now rewrite List_map_seq_length.
  } {
    rewrite <- List_hd_nth_0, fold_mat_ncols.
    now rewrite mat_ncols_of_nat.
  }
  rewrite List_map_nth' with (a := 0) in Hi; [ | now rewrite seq_length ].
  rewrite seq_nth in Hi; [ cbn in Hi | easy ].
  rewrite fold_mat_el in Hi.
  replace (mat_el (sm_mat (rngl_of_nat i)) 0 0) with
    (@rngl_of_nat T ro i) in Hi. 2: {
    symmetry.
    clear Hi.
    induction i. {
      cbn.
      rewrite List_nth_repeat.
      destruct (lt_dec 0 n) as [H| H]; [ clear H | flia Hnz H ].
      rewrite List_nth_repeat.
      now destruct (lt_dec 0 n).
    }
    cbn - [ mat_el ].
    rewrite mat_el_add; cycle 1. {
      apply mI_is_correct_matrix.
    } {
      now apply rngl_of_nat_is_correct_matrix.
    } {
      now rewrite mI_nrows.
    } {
      now rewrite squ_mat_nrows.
    } {
      now rewrite mI_ncols.
    } {
      now rewrite squ_mat_ncols.
    }
    rewrite mat_el_mI_diag; [ | easy ].
    now rewrite IHi.
  }
  now specialize (H1 i); cbn in H1.
}
cbn.
apply square_matrix_eq; cbn.
rewrite sm_mat_of_nat; [ | now left ].
unfold "×"%M, mZ.
f_equal; rewrite H1.
destruct n; [ flia Hnz | clear Hnz ].
cbn.
f_equal. {
  f_equal; [ now apply rngl_mul_0_l; left | ].
  rewrite <- seq_shift.
  rewrite map_map, map_map.
  rewrite List_repeat_as_map.
  apply map_ext_in.
  intros i Hi.
  now apply rngl_mul_0_l; left.
}
rewrite <- seq_shift.
rewrite map_map, map_map.
rewrite List_repeat_as_map.
apply map_ext_in.
intros i Hi.
rewrite map_map; cbn.
rewrite rngl_mul_0_l; [ | now left ].
f_equal.
rewrite List_repeat_as_map.
rewrite map_map.
apply map_ext_in.
intros j Hj.
now apply rngl_mul_0_l; left.
Qed.

Theorem squ_mat_consistent {n} :
  (@rngl_has_opp (square_matrix n T) (mat_ring_like_op n) = false
   ∨ @rngl_has_sous (square_matrix n T) (mat_ring_like_op n) = false)
  ∧ (@rngl_has_inv (square_matrix n T) (mat_ring_like_op n) = false
     ∨ @rngl_has_quot (square_matrix n T) (mat_ring_like_op n) = false).
(*
  (rngl_has_opp = false ∨ rngl_has_sous = false) ∧
  (rngl_has_inv = false ∨ rngl_has_quot = false)
*)
Proof.
now split; right.
Qed.

Definition mat_ring_like_prop (n : nat) :
  ring_like_prop (square_matrix n T) :=
  {| rngl_is_comm := false;
     rngl_has_dec_eq := @rngl_has_dec_eq T ro rp;
     rngl_has_dec_le := false;
     rngl_has_1_neq_0 := rngl_has_1_neq_0 && (n ≠? 0);
     rngl_is_ordered := false;
     rngl_is_integral := false;
     rngl_characteristic := if n =? 0 then 1 else rngl_characteristic;
     rngl_add_comm := squ_mat_add_comm;
     rngl_add_assoc := squ_mat_add_assoc;
     rngl_add_0_l := squ_mat_add_0_l;
     rngl_mul_assoc := squ_mat_mul_assoc;
     rngl_mul_1_l := squ_mat_mul_1_l;
     rngl_mul_add_distr_l := squ_mat_mul_add_distr_l;
     rngl_opt_1_neq_0 := squ_mat_opt_1_neq_0;
     rngl_opt_mul_comm := NA;
     rngl_opt_mul_1_r := squ_mat_mul_1_r;
     rngl_opt_mul_add_distr_r := squ_mat_mul_add_distr_r;
     rngl_opt_add_opp_l := squ_mat_opt_add_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_sub_sub_add := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_quot_l := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eq_dec := squ_mat_opt_eq_dec;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := NA;
     rngl_characteristic_prop := squ_mat_characteristic_prop;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA;
     rngl_consistent := squ_mat_consistent |}.

End a.
