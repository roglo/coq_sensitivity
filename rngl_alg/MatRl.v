(* square matrix ring like algebra *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith Bool.
Import List.ListNotations.

Require Import Main.Misc.
Require Import Main.RingLike Main.IterAdd.
Require Import Main.Matrix.
Require Import Main.Determinant.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hon : @rngl_has_1 T ro = true).
Context (Hop : @rngl_has_opp T ro = true).

Theorem mZ_is_square_matrix : ∀ n,
  (mat_nrows (mZ n n) =? n) && is_square_matrix (mZ n n) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split. {
  cbn; rewrite List.repeat_length.
  apply Nat.eqb_refl.
}
apply is_scm_mat_iff.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n; cbn | ].
split; [ now rewrite mZ_nrows, mZ_ncols | ].
intros la Hla.
cbn in Hla.
apply List.repeat_spec in Hla; subst la.
now cbn; do 2 rewrite List.repeat_length.
Qed.

Theorem mI_square_matrix_prop : ∀ n,
  (mat_nrows (mI n) =? n) && is_square_matrix (mI n) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply mI_is_square_matrix ].
cbn; rewrite List_length_map_seq.
apply Nat.eqb_refl.
Qed.

Theorem square_matrix_add_prop : ∀ {n} (MA MB : square_matrix n T),
  (mat_nrows (sm_mat MA + sm_mat MB) =? n) &&
  is_square_matrix (sm_mat MA + sm_mat MB) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply square_matrix_add_is_square ].
apply Nat.eqb_eq; cbn.
rewrite List_length_map2.
do 2 rewrite fold_mat_nrows.
do 2 rewrite smat_nrows.
apply Nat.min_id.
Qed.

Theorem square_matrix_mul_prop : ∀ {n} (MA MB : square_matrix n T),
  (mat_nrows (sm_mat MA * sm_mat MB) =? n) &&
  is_square_matrix (sm_mat MA * sm_mat MB) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply square_matrix_mul_is_square ].
apply Nat.eqb_eq; cbn.
progress unfold mat_list_list_mul.
rewrite List_length_map_seq.
apply smat_nrows.
Qed.

Theorem square_matrix_opp_prop : ∀ {n} (M : square_matrix n T),
  (mat_nrows (- sm_mat M) =? n) && is_square_matrix (- sm_mat M) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply square_matrix_opp_is_square ].
apply Nat.eqb_eq; cbn.
rewrite List.length_map.
apply smat_nrows.
Qed.

Definition smZ n : square_matrix n T :=
  {| sm_mat := mZ n n;
     sm_prop := mZ_is_square_matrix n |}.

Definition smI n : square_matrix n T :=
  {| sm_mat := mI n;
     sm_prop := mI_square_matrix_prop n |}.

Definition square_matrix_add {n} (MA MB : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := sm_mat MA + sm_mat MB;
     sm_prop := square_matrix_add_prop MA MB |}.

Definition square_matrix_mul {n} (MA MB : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := sm_mat MA * sm_mat MB;
     sm_prop := square_matrix_mul_prop MA MB |}.

Definition square_matrix_opp {n} (M : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := - sm_mat M;
     sm_prop := square_matrix_opp_prop M |}.

Definition square_matrix_eqb eqb {n} (A B : square_matrix n T) :=
  mat_eqb eqb (sm_mat A) (sm_mat B).

Theorem square_matrix_eq_dec (eq_dec : ∀ x y : T, {x = y} + {x ≠ y}) {n} :
  ∀ A B : square_matrix n T, {A = B} + {A ≠ B}.
Proof.
intros.
specialize (mat_eq_dec eq_dec (sm_mat A) (sm_mat B)) as H1.
destruct H1 as [H1| H1]; [ left | right ]. {
  now apply square_matrix_eq.
} {
  now intros H; subst B.
}
Qed.

Instance mat_ring_like_op (eq_dec : ∀ x y : T, {x = y} + {x ≠ y}) {n} :
    ring_like_op (square_matrix n T) :=
  {| rngl_zero := smZ n;
     rngl_add := square_matrix_add;
     rngl_mul := square_matrix_mul;
     rngl_opt_one := Some (smI n);
     rngl_opt_opp_or_subt := Some (inl square_matrix_opp);
     rngl_opt_inv_or_quot := None;
(*
     rngl_opt_zero_divisors := Some (λ M, det (sm_mat M) = 0%L);
*)
     rngl_opt_zero_divisors := Some (λ _, True);
(**)
     rngl_opt_eq_dec := Some (square_matrix_eq_dec eq_dec);
     rngl_opt_leb := None |}.

(*
Canonical Structure mat_ring_like_op.
says:
Warning: Projection value has no head constant:
match rngl_opt_eqb with
| Some eqb => Some (square_matrix_eqb eqb)
| None => None
end in canonical instance mat_ring_like_op of rngl_opt_eqb, ignoring it.
 [projection-no-head-constant,typechecker]
*)

(*
Existing Instance mat_ring_like_op.
*)

Theorem mat_ncols_of_nat eq_dec {n} : ∀ i,
  let rom := mat_ring_like_op eq_dec in
  mat_ncols (@sm_mat n T (rngl_of_nat i)) = n.
Proof.
intros; cbn.
progress unfold rngl_of_nat.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n; destruct i | ].
induction i; [ now apply mZ_ncols | cbn ].
rewrite mat_add_ncols.
rewrite mI_ncols, IHi.
apply Nat.min_id.
Qed.

Theorem sm_mat_of_nat :
  ∀ eq_dec n,
  let rom := mat_ring_like_op eq_dec in
  ∀ m,
  sm_mat (rngl_of_nat m : square_matrix n T) = (rngl_of_nat m × mI n)%M.
(*
  ∀ n m : nat, sm_mat (rngl_of_nat m) = (rngl_of_nat m × mI n)%M
*)
Proof.
intros; cbn.
progress unfold rngl_of_nat.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn.
specialize (proj2 rngl_has_opp_or_subt_iff (or_introl Hop)) as Hos.
induction m; cbn. {
  unfold "×"%M, mZ, mI.
  f_equal; cbn.
  rewrite List.map_map.
  rewrite List_repeat_as_map.
  apply List.map_ext_in.
  intros i Hi.
  rewrite List_repeat_as_map.
  rewrite List.map_map.
  apply List.map_ext_in.
  intros j Hj.
  now symmetry; apply rngl_mul_0_l.
}
rewrite mat_mul_scal_l_add_distr_r.
now rewrite mat_mul_scal_1_l, IHm.
Qed.

Theorem mat_el_of_nat_diag {n} : ∀ eq_dec m i,
  1 ≤ i ≤ n
  → mat_el
      (sm_mat
         (@rngl_mul_nat (square_matrix n T) (mat_ring_like_op eq_dec)
            (smI _) m)) i i =
    rngl_of_nat m.
(*
  ∀ m i : nat, 1 ≤ i ≤ n →
  mat_el (sm_mat (rngl_of_nat m)) i i = rngl_of_nat m
*)
Proof.
intros * Hin.
assert (Hi' : i - 1 < n) by flia Hin.
specialize sm_mat_of_nat as H1.
progress unfold rngl_of_nat in H1; cbn in H1.
rewrite H1; clear H1; cbn.
rewrite List.map_map.
rewrite List_map_nth' with (a := 0); [ | now rewrite List.length_seq ].
rewrite List_map_nth' with (a := 0%L). 2: {
  now rewrite List_length_map_seq.
}
rewrite List_map_nth' with (a := 0); [ | now rewrite List.length_seq ].
rewrite List.seq_nth; [ cbn | easy ].
unfold δ.
now rewrite Nat.eqb_refl, rngl_mul_1_r.
Qed.

Theorem rngl_of_nat_is_correct_matrix :
  ∀ eq_dec n,
  let rom := mat_ring_like_op eq_dec in
  rngl_characteristic T = 0
  → ∀ i, is_correct_matrix (@sm_mat n T (rngl_of_nat i)) = true.
Proof.
intros eq_dec n rom Hch *.
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
  apply List.length_zero_iff_nil in Hc.
  apply List.length_zero_iff_nil.
  remember (mat_list_list _) as lla eqn:Hlla.
  symmetry in Hlla.
  apply (f_equal (λ ll, List.nth 0 (List.nth 0 ll []) 0%L)) in Hlla.
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
    now rewrite smat_nrows.
  } {
    now rewrite mI_ncols.
  } {
    now rewrite smat_ncols.
  }
  rewrite mat_el_mI_diag in Hlla; [ | easy ].
  subst rom.
  specialize (@mat_el_of_nat_diag n eq_dec) as H1.
  progress unfold rngl_mul_nat in H1.
  progress unfold mul_nat in H1; cbn in H1.
  rewrite H1 in Hlla; [ clear H1 | easy ].
  now apply (rngl_characteristic_0 Hon Hch i).
} {
  intros l Hl.
  subst rom.
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

Theorem squ_mat_add_comm :
  ∀ {n} eq_dec,
  let rom := mat_ring_like_op eq_dec in
  ∀ (MA MB : square_matrix n T), (MA + MB)%L = (MB + MA)%L.
Proof.
intros.
apply square_matrix_eq.
apply mat_add_comm.
Qed.

Theorem squ_mat_add_assoc :
  ∀ {n} eq_dec,
  let rom := mat_ring_like_op eq_dec in
  ∀ (MA MB MC : square_matrix n T), (MA + (MB + MC) = (MA + MB) + MC)%L.
Proof.
intros.
apply square_matrix_eq.
apply mat_add_assoc.
Qed.

Theorem squ_mat_add_0_l :
  ∀ {n} eq_dec,
  let rom := mat_ring_like_op eq_dec in
  ∀ (M : square_matrix n T), (0 + M)%L = M.
Proof.
intros.
apply square_matrix_eq.
cbn.
apply mat_add_0_l; cycle 1. {
  symmetry; apply smat_nrows.
} {
  symmetry; apply smat_ncols.
}
apply square_matrix_is_correct.
Qed.

Theorem squ_mat_mul_assoc :
  ∀ {n} eq_dec,
  let rom := mat_ring_like_op eq_dec in
  ∀ (MA MB MC : square_matrix n T), (MA * (MB * MC) = (MA * MB) * MC)%L.
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
  progress unfold mat_list_list_mul.
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

Theorem squ_mat_mul_1_l :
  ∀ {n} eq_dec,
  let rom := mat_ring_like_op eq_dec in
  ∀ (M : square_matrix n T), (1 * M)%L = M.
Proof.
intros.
apply square_matrix_eq; cbn.
apply (mat_mul_1_l Hon); [ easy | | symmetry; apply smat_nrows ].
apply square_matrix_is_correct.
Qed.

Theorem squ_mat_mul_add_distr_l :
  ∀ {n} eq_dec,
  let rom := mat_ring_like_op eq_dec in
  ∀ (MA MB MC : square_matrix n T), (MA * (MB + MC) = MA * MB + MA * MC)%L.
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
  progress unfold mat_list_list_mul.
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

Theorem squ_mat_mul_1_r :
  ∀ {n} eq_dec,
  let rom := mat_ring_like_op eq_dec in
  ∀ (M : square_matrix n T), (M * 1)%L = M.
Proof.
intros.
apply square_matrix_eq; cbn.
apply (mat_mul_1_r Hon); [ easy | | symmetry; apply smat_ncols ].
apply square_matrix_is_correct.
Qed.

Theorem squ_mat_mul_add_distr_r :
  ∀ {n} eq_dec,
  let rom := mat_ring_like_op eq_dec in
  ∀ (MA MB MC : square_matrix n T),
  ((MA + MB) * MC = MA * MC + MB * MC)%L.
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
  rewrite List_length_map2; cbn.
  do 2 rewrite fold_mat_nrows.
  progress unfold mat_list_list_mul.
  now rewrite Hra.
}
apply mat_mul_add_distr_r. {
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

Theorem squ_mat_opt_add_opp_diag_l :
  ∀ {n} eq_dec,
  let rom := mat_ring_like_op eq_dec in
  if @rngl_has_opp (square_matrix n T) (mat_ring_like_op eq_dec) then
    ∀ M : square_matrix n T, (- M + M)%L = 0%L
  else not_applicable.
(*
  if rngl_has_opp then ∀ M : square_matrix n T, (- M + M)%L = 0%L
  else not_applicable.
*)
Proof.
intros.
remember (@rngl_has_opp (square_matrix n T) (mat_ring_like_op eq_dec)) as b
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
  apply List.length_zero_iff_nil in Hr.
  now rewrite Hr.
}
apply mat_add_opp_diag_l; [ easy | | easy | ]. 2: {
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

(*
Theorem mat_opt_eqb_eq : ∀ eq_dec n,
  match
    @rngl_has_eq_dec (square_matrix n T) (@mat_ring_like_op eq_dec n)
    return Prop
  with
  | true =>
      forall a b : square_matrix n T,
      iff
        (@eq bool
           (@rngl_eqb (square_matrix n T) (@mat_ring_like_op eq_dec n) a b)
              true)
           (@eq (square_matrix n T) a b)
  | false => not_applicable
  end.
(*
  (if square_matrix_eq_dec eq_dec a b then true else false) = true ↔ a = b
*)
Proof.
cbn.
cbn; intros.
split; intros Hab. {
  destruct (square_matrix_eq_dec eq_dec a b) as [H1| H1]; [ | easy ].
...
cbn; intros.
split; intros Hab. {
  apply mat_eqb_eq in Hab; [ | easy ].
  now apply square_matrix_eq.
} {
  subst b; cbn.
  unfold square_matrix_eqb.
  now apply mat_eqb_eq.
}
Qed.
*)

Theorem squ_mat_integral eq_dec n :
  let rom := @mat_ring_like_op eq_dec n in
  ∀ A B : square_matrix n T,
  (A * B)%L = 0%L
  → A = 0%L ∨ B = 0%L ∨ rngl_zero_divisor A ∨ rngl_zero_divisor B.
Proof.
intros * Hab.
(*
cbn.
cbn in Hab.
injection Hab; clear Hab; intros H1.
...
Print mat_mul.
About mat_mul.
...
*)
now right; right; left.
Qed.

Theorem squ_mat_characteristic_prop :
  ∀ eq_dec n,
  let rom := @mat_ring_like_op eq_dec n in
  let ch := if n =? 0 then 1 else rngl_characteristic T in
  if ch =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
  else
   (∀ i : nat, 0 < i < ch → rngl_of_nat i ≠ 0%L)
   ∧ rngl_of_nat ch = 0%L.
Proof.
intros eq_dec n rom *.
specialize (proj2 rngl_has_opp_or_subt_iff (or_introl Hop)) as Hos.
move Hos before Hop.
subst ch.
rewrite (if_eqb_eq_dec n).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  split; [ | now apply square_matrix_eq ].
  intros i Hi; flia Hi.
}
apply Nat.neq_0_lt_0 in Hnz.
specialize @rngl_opt_characteristic_prop as H1.
specialize (H1 T ro rp).
rewrite Hon in H1.
rewrite if_eqb_eq_dec in H1 |-*.
destruct (Nat.eq_dec (rngl_characteristic T) 0) as [Hch| Hcn]. {
  intros i Hi.
  apply (f_equal (λ M, mat_el (sm_mat M) 1 1)) in Hi.
  cbn in Hi.
  rewrite List_nth_repeat in Hi.
  destruct (lt_dec 0 n) as [H| H]; [ clear H | flia Hnz H ].
  rewrite List_nth_repeat in Hi.
  destruct (lt_dec 0 n) as [H| H]; [ clear H | flia Hnz H ].
  rewrite List_map2_map_l in Hi.
  rewrite List_map2_nth with (a := 0) (b := []) in Hi; cycle 1. {
    now rewrite List.length_seq.
  } {
    rewrite fold_mat_nrows.
    clear Hi.
    induction i; cbn; [ now rewrite List.repeat_length | ].
    rewrite List_length_map2, List_length_map_seq.
    rewrite fold_mat_nrows.
    flia Hnz IHi.
  }
  rewrite List_map2_nth with (a := 0%L) (b := 0%L) in Hi; cycle 1. {
    now rewrite List_length_map_seq.
  } {
    rewrite <- List_hd_nth_0, fold_mat_ncols.
    subst rom.
    specialize (@mat_ncols_of_nat eq_dec) as H2.
    progress unfold rngl_of_nat in H2.
    progress unfold rngl_mul_nat in H2.
    progress unfold mul_nat in H2; cbn in H2.
    now rewrite H2.
  }
  rewrite (List_map_nth' 0) in Hi; [ | now rewrite List.length_seq ].
  rewrite List.seq_nth in Hi; [ cbn in Hi | easy ].
  rewrite fold_mat_el in Hi.
  replace (mat_el (sm_mat (List.fold_right _ _ _)) 1 1) with
    (@rngl_mul_nat T ro 1 i) in Hi. 2: {
    symmetry.
    clear Hi.
    progress unfold rngl_mul_nat.
    progress unfold mul_nat; cbn.
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
      specialize (rngl_of_nat_is_correct_matrix eq_dec) as H2.
      progress unfold rngl_of_nat in H2.
      progress unfold rngl_mul_nat in H2.
      progress unfold mul_nat in H2; cbn in H2.
      now apply H2.
    } {
      now rewrite mI_nrows.
    } {
      now rewrite smat_nrows.
    } {
      now rewrite mI_ncols.
    } {
      now rewrite smat_ncols.
    }
    rewrite mat_el_mI_diag; [ | easy ].
    now rewrite IHi.
  }
  now specialize (H1 i); cbn in H1.
}
cbn.
destruct H1 as (Hbef, H1).
split. {
  intros * Hi.
  specialize (Hbef _ Hi) as H.
  intros H2; apply H; clear H.
  destruct n; [ easy | ].
  apply (f_equal (λ M, mat_el (sm_mat M) 1 1)) in H2.
  cbn in H2.
  subst rom.
  progress unfold rngl_of_nat in H2.
  progress unfold rngl_of_nat.
  cbn in H2 |-*.
  now rewrite mat_el_of_nat_diag in H2; [ | flia ].
}
apply square_matrix_eq; cbn.
subst rom.
rewrite sm_mat_of_nat.
unfold "×"%M, mZ.
f_equal; rewrite H1.
destruct n; [ flia Hnz | clear Hnz ].
cbn.
f_equal. {
  f_equal; [ now apply rngl_mul_0_l | ].
  rewrite <- List.seq_shift.
  rewrite List.map_map, List.map_map.
  rewrite List_repeat_as_map.
  apply List.map_ext_in.
  intros i Hi.
  now apply rngl_mul_0_l.
}
rewrite <- List.seq_shift.
rewrite List.map_map, List.map_map.
rewrite List_repeat_as_map.
apply List.map_ext_in.
intros i Hi.
rewrite List.map_map; cbn.
rewrite rngl_mul_0_l; [ | easy ].
f_equal.
rewrite List_repeat_as_map.
rewrite List.map_map.
apply List.map_ext_in.
intros j Hj.
now apply rngl_mul_0_l.
Qed.

Instance mat_ring_like_prop (eq_dec : ∀ x y : T, {x = y} + {x ≠ y})
    (n : nat) :
  let rom := mat_ring_like_op eq_dec in
  ring_like_prop (square_matrix n T) :=
  {| rngl_mul_is_comm := false;
     rngl_is_archimedean := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := if n =? 0 then 1 else rngl_characteristic T;
     rngl_add_comm := squ_mat_add_comm eq_dec;
     rngl_add_assoc := squ_mat_add_assoc eq_dec;
     rngl_add_0_l := squ_mat_add_0_l eq_dec;
     rngl_mul_assoc := squ_mat_mul_assoc eq_dec;
     rngl_opt_mul_1_l := squ_mat_mul_1_l eq_dec;
     rngl_mul_add_distr_l := squ_mat_mul_add_distr_l eq_dec;
     rngl_opt_mul_comm := NA;
     rngl_opt_mul_1_r := squ_mat_mul_1_r eq_dec;
     rngl_opt_mul_add_distr_r := squ_mat_mul_add_distr_r eq_dec;
     rngl_opt_add_opp_diag_l := squ_mat_opt_add_opp_diag_l eq_dec;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_integral := squ_mat_integral eq_dec n;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := squ_mat_characteristic_prop eq_dec n;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.

End a.
