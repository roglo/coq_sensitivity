(* square matrix ring like algebra *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith (*Bool*).
Import List (* List.ListNotations *).
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

(* associativity of multiplication *)

Theorem mat_mul_assoc :
  ∀ (MA : matrix T) (MB : matrix T) (MC : matrix T),
  mat_nrows MB ≠ 0
  → mat_ncols MB ≠ 0
  → mat_ncols MA = mat_nrows MB
  → (MA * (MB * MC))%M = ((MA * MB) * MC)%M.
Proof.
intros * Hrbz Hcbz Hcarb.
unfold "*"%M.
f_equal.
unfold mat_nrows at 5; cbn.
rewrite List_map_seq_length.
apply map_ext_in.
intros i Hi.
unfold mat_ncols at 2; cbn.
rewrite (List_map_hd 0). 2: {
  now rewrite seq_length; apply Nat.neq_0_lt_0.
}
rewrite List_map_seq_length.
apply map_ext_in.
intros j Hj.
move j before i.
unfold mat_mul_el.
unfold mat_ncols at 4.
cbn.
rewrite (List_map_hd 0). 2: {
  rewrite seq_length; apply Nat.neq_0_lt_0.
  now intros H; rewrite H in Hi.
}
rewrite List_map_seq_length.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite List_map_nth' with (a := 0). 2: {
    rewrite seq_length.
    rewrite Hcarb in Hk.
    flia Hrbz Hk.
  }
  rewrite List_map_nth' with (a := 0). 2: {
    rewrite seq_length.
    now apply in_seq in Hj.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros m Hm.
    rewrite seq_nth; [ | rewrite Hcarb in Hk; flia Hrbz Hk ].
    rewrite seq_nth; [ | now apply in_seq in Hj ].
    easy.
  }
  rewrite rngl_mul_summation_distr_l; [ | now left ].
  erewrite rngl_summation_eq_compat. 2: {
    intros m Hm.
    now rewrite rngl_mul_assoc.
  }
  easy.
}
cbn.
erewrite rngl_summation_eq_compat with (k := mat_ncols MB - 1). 2: {
  intros k Hk.
  rewrite List_map_nth' with (a := 0). 2: {
    rewrite seq_length.
    now apply in_seq in Hi.
  }
  rewrite List_map_nth' with (a := 0). 2: {
    rewrite seq_length.
    flia Hcbz Hk.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros m Hm.
    rewrite seq_nth; [ | now apply in_seq in Hi ].
    rewrite seq_nth; [ | flia Hcbz Hk ].
    easy.
  }
  rewrite rngl_mul_summation_distr_r; [ | now left ].
  easy.
}
cbn.
apply rngl_summation_summation_exch'.
Qed.

Existing Instance mat_ring_like_op.

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
apply mat_mul_assoc. {
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
