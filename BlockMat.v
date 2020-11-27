(* block matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Init.Nat.
Require Import Relations.

Require Import Misc.
Require Import Matrix.
Require Import Semiring SRsummation SRproduct.
Import matrix_Notations.

Existing Instance nat_semiring_op.
Existing Instance nat_semiring_prop.

(* block matrices *)

Inductive bmatrix T :=
  | BM_1 : T → bmatrix T
  | BM_M : matrix (bmatrix T) → bmatrix T.

Theorem bmatrix_ind2 : ∀ T (P : bmatrix T → Prop),
  (∀ t, P (BM_1 t))
  → (∀ M, (∀ i j, i < mat_nrows M → j < mat_ncols M → P (mat_el M i j))
      → P (BM_M M))
  → ∀ BM, P BM.
Proof.
fix IHB 5.
intros * H1 HM *.
destruct BM as [x| M]; [ apply H1 | ].
apply HM.
intros.
destruct M as (f, r, c); cbn.
remember (f i j) as BM eqn:HBM.
symmetry in HBM.
destruct BM as [x| M]; [ apply H1 | ].
apply HM.
intros k l Hk Hl.
now apply IHB.
Qed.

Fixpoint list_list_of_bmat T (MM : bmatrix T) : list (list T) :=
  match MM with
  | BM_1 x => [[x]]
  | BM_M MMM =>
      let ll :=
        map
          (λ i,
             concat_list_list_list
               (map (λ j, list_list_of_bmat (mat_el MMM i j))
                  (seq 0 (mat_ncols MMM))))
          (seq 0 (mat_nrows MMM))
      in
      List.concat ll
  end.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.

(* addition of block matrices *)

Fixpoint bmat_add {so : semiring_op T} (MM1 MM2 : bmatrix T) :=
  match MM1 with
  | BM_1 xa =>
      match MM2 with
      | BM_1 xb => BM_1 (xa + xb)%Srng
      | BM_M MMB => BM_1 0%Srng
      end
  | BM_M MMA =>
      match MM2 with
      | BM_1 xb => BM_1 0%Srng
      | BM_M MMB =>
          let r :=
            {| mat_el i j := bmat_add (mat_el MMA i j) (mat_el MMB i j);
               mat_nrows := mat_nrows MMA;
               mat_ncols := mat_ncols MMA |}
          in
          BM_M r
      end
  end.

(* a null or identity block matrix having the same structure as a given
    block matrix; see usage below for null and identity *)

Fixpoint bmat_IZ_like (u : T) {so : semiring_op T} (BM : bmatrix T) :=
  match BM with
  | BM_1 _ => BM_1 u
  | BM_M M =>
      let M' :=
        mk_mat
          (λ i j,
           bmat_IZ_like (if eqb i j then u else 0%Srng) (mat_el M i j))
          (mat_nrows M) (mat_ncols M)
      in
      BM_M M'
  end.

Arguments bmat_IZ_like u%Rng {so}.

(* a null block matrix having the same structure as a given block matrix *)

Definition bmat_zero_like := bmat_IZ_like 0.

Theorem fold_bmat_zero_like : bmat_IZ_like 0 = bmat_zero_like.
Proof. easy. Qed.

(* an identity block matrix having the same structure as a given block
    matrix *)

Definition bmat_one_like := bmat_IZ_like 1.

(* multiplication of block matrices *)

Fixpoint bmat_mul (MM1 MM2 : bmatrix T) :=
  match MM1 with
  | BM_1 xa =>
      match MM2 with
      | BM_1 xb => BM_1 (xa * xb)%Srng
      | BM_M _ => BM_1 0%Srng
      end
  | BM_M MMA =>
      match MM2 with
      | BM_1 _ => BM_1 0%Srng
      | BM_M MMB =>
          let mat_el_mul i k :=
            iter_seq 0 (mat_ncols MMA - 1)
              (λ acc j,
                 bmat_add acc (bmat_mul (mat_el MMA i j) (mat_el MMB j k)))
              (bmat_zero_like (mat_el MMA 0 0))
          in
          let r :=
            {| mat_el i k := mat_el_mul i k;
               mat_nrows := mat_nrows MMA;
               mat_ncols := mat_ncols MMB |}
          in
          BM_M r
      end
  end.

Definition bmat_semiring_op {M} : semiring_op (bmatrix T) :=
  {| srng_zero := bmat_zero_like M;
     srng_one := bmat_one_like M;
     srng_add := bmat_add;
     srng_mul := bmat_mul |}.

Canonical Structure bmat_semiring_op.

Fixpoint bmat_opp BM : bmatrix T :=
  match BM with
  | BM_1 x => BM_1 (- x)%Rng
  | BM_M MMM =>
      let M :=
         {| mat_el i j := bmat_opp (mat_el MMM i j);
            mat_nrows := mat_nrows MMM;
            mat_ncols := mat_ncols MMM |}
      in
      BM_M M
  end.

Theorem bmat_opp_involutive : ∀ BM,
  bmat_opp (bmat_opp BM) = BM.
Proof.
intros.
induction BM as [x| M IHBM] using bmatrix_ind2. {
  now cbn; rewrite rng_opp_involutive.
} {
  destruct M as (f, r, c).
  cbn in IHBM |-*.
  f_equal.
  apply matrix_eq; cbn; [ easy | easy | ].
  intros * Hi Hj.
  now apply IHBM.
}
Qed.


Definition bmat_sub BMA BMB :=
  bmat_add BMA (bmat_opp BMB).

End in_ring.

(* notations *)

Module bmatrix_Notations.

Declare Scope BM_scope.
Delimit Scope BM_scope with BM.

Notation "a + b" := (bmat_add a b) : BM_scope.
Notation "a - b" := (bmat_sub _ a b) : BM_scope.
Notation "a * b" := (bmat_mul _ a b) : BM_scope.
Notation "- a" := (bmat_opp a) : BM_scope.

Arguments bmat_add {T so} _%BM _%BM.
Arguments bmat_sub {T ro so} _%BM _%BM.
Arguments bmat_mul {T so} _%BM _%BM.
Arguments bmat_opp_involutive {T ro so sp rp} _%BM.
Arguments bmat_zero_like {T so} BM%BM.
Arguments bmat_one_like {T so} BM%BM.

End bmatrix_Notations.

Import bmatrix_Notations.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {scp : sring_comm_prop T}.
Context {rp : ring_prop T}.

(* zero and one block matrices *)
(* this is, I guess, an old version that should be removed one day;
   now I use bmat_IZ_like *)

Fixpoint IZ_2_pow (u : T) n :=
  match n with
  | 0 => BM_1 u
  | S n' =>
      BM_M
        (mat_of_list_list (BM_1 u)
           [[IZ_2_pow u n'; IZ_2_pow 0%Srng n'];
            [IZ_2_pow 0%Srng n'; IZ_2_pow u n']])
  end.

Definition I_2_pow := IZ_2_pow 1%Srng.
Definition Z_2_pow := IZ_2_pow 0%Srng.

Theorem fold_Z_2_pow : ∀ n,
  IZ_2_pow 0%Srng n = Z_2_pow n.
Proof. easy. Qed.

Theorem fold_I_2_pow : ∀ n,
  IZ_2_pow 1%Srng n = I_2_pow n.
Proof. easy. Qed.

(*
Require Import ZArith.

About Z_ring_op.
Compute (let n := 2%nat in let _ := Z_ring_op in let _ := rng_semiring in A n).

Compute (let n := 3%nat in let _ := Z_ring_op in let _ := rng_semiring in list_list_of_bmat (I_2_pow n)).
Compute (let n := 3%nat in let _ := Z_ring_op in let _ := rng_semiring in list_list_of_bmat (A n)).
Compute (let n := 3%nat in let _ := Z_ring_op in let _ := rng_semiring in list_list_of_bmat (bmat_mul (A n) (A n))).
*)

Definition rng_mul_nat_l n v :=
  match n with
  | 0 => 0%Srng
  | S n' => (Σ (_ = 0, n'), v)%Srng
  end.

Fixpoint bmat_nat_mul_l n BM :=
  match BM with
  | BM_1 x => BM_1 (rng_mul_nat_l n x)
  | BM_M M =>
      BM_M
        {| mat_el i j := bmat_nat_mul_l n (mat_el M i j);
           mat_nrows := mat_nrows M;
           mat_ncols := mat_ncols M |}
  end.

Fixpoint bmat_fit_for_add (MA MB : bmatrix T) :=
  match MA with
  | BM_1 xa =>
      match MB with
      | BM_1 xb => True
      | BM_M MMB => False
      end
  | BM_M MMA =>
      match MB with
      | BM_1 xb => False
      | BM_M MMB =>
          mat_nrows MMA = mat_nrows MMB ∧
          mat_ncols MMA = mat_ncols MMB ∧
          ∀ i j, i < mat_nrows MMA → j < mat_ncols MMA →
          bmat_fit_for_add (mat_el MMA i j) (mat_el MMB i j)
      end
  end.

Theorem bmat_fit_for_add_refl : reflexive _ bmat_fit_for_add.
Proof.
intros * M.
induction M as [x| M IHM] using bmatrix_ind2; [ easy | cbn ].
destruct M as (ll, r, c); cbn in IHM |-*.
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
now apply IHM.
Qed.

Theorem bmat_fit_for_add_symm : symmetric _ bmat_fit_for_add.
Proof.
intros * MA MB HMM.
revert MB HMM.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  now destruct MB.
}
destruct MB as [xb| mb]; [ easy | ].
cbn in HMM |-*.
destruct ma as (lla, ra, ca); destruct mb as (llb, rb, cb).
cbn in IHMA, HMM |-*.
destruct HMM as (Hrr & Hcc & Hss).
subst rb cb.
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
now apply IHMA, Hss.
Qed.

Theorem bmat_fit_for_add_trans : transitive _ bmat_fit_for_add.
Proof.
intros * MA MB MC HAB HBC.
revert MB MC HAB HBC.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  now destruct MB.
}
destruct MB as [xb| mb]; [ easy | ].
destruct MC as [xc| mc]; [ easy | ].
cbn in HAB, HBC |-*.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
destruct mc as (fc, rc, cc).
cbn in IHMA, HAB, HBC |-*.
destruct HAB as (Hrr & Hcc & Hab); subst rb cb.
destruct HBC as (Hrr & Hcc & Hbc); subst rc cc.
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
now apply IHMA with (MB := fb i j); [ | | apply Hab | apply Hbc ].
Qed.

Add Parametric Relation : _ bmat_fit_for_add
 reflexivity proved by bmat_fit_for_add_refl
 symmetry proved by bmat_fit_for_add_symm
 transitivity proved by bmat_fit_for_add_trans
 as bmat_fit_for_add_equivalence.

Theorem bmat_add_comm : ∀ MA MB,
  bmat_fit_for_add MA MB
  → bmat_add MA MB = bmat_add MB MA.
Proof.
intros * Hss.
revert MB Hss.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  destruct MB as [xb| mb]; [ | easy ].
  now cbn; rewrite srng_add_comm.
}
destruct MB as [xb| mb]; [ easy | ].
cbn in Hss.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in IHMA, Hss |-*.
destruct Hss as (Hrr & Hcc & Hss); subst rb cb.
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
apply IHMA; [ easy | easy | ].
now apply Hss.
Qed.

Theorem old_bmat_add_0_l : ∀ n M,
  bmat_fit_for_add (Z_2_pow n) M
  → bmat_add (Z_2_pow n) M = M.
Proof.
intros * Hss.
revert M Hss.
induction n; intros. {
  cbn.
  destruct M as [x| M]; [ now rewrite srng_add_0_l | easy ].
}
cbn in Hss |-*.
destruct M as [x| M]; [ easy | f_equal ].
destruct Hss as (Hr & Hc & Hss).
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
rewrite <- Hc in Hj.
specialize (Hss _ _ Hi Hj) as H1.
destruct i. {
  destruct j; [ now apply IHn | cbn ].
  destruct j; [ now apply IHn | flia Hj ].
}
destruct i; [ cbn | flia Hi ].
destruct j; [ now apply IHn | cbn ].
destruct j; [ now apply IHn | flia Hj ].
Qed.

Theorem old_bmat_add_0_r : ∀ n M,
  bmat_fit_for_add (Z_2_pow n) M
  → bmat_add M (Z_2_pow n) = M.
Proof.
intros * Hss.
rewrite bmat_add_comm; [ | easy ].
now apply old_bmat_add_0_l.
Qed.

Theorem bmat_fit_for_add_IZ_IZ : ∀ u v n,
  bmat_fit_for_add (IZ_2_pow u n) (IZ_2_pow v n).
Proof.
intros.
revert u v.
induction n; intros; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
destruct i. {
  destruct j; [ apply IHn | ].
  destruct j; [ apply IHn | flia Hj ].
}
destruct i; [ | flia Hi ].
destruct j; [ apply IHn | ].
destruct j; [ apply IHn | flia Hj ].
Qed.

Theorem bmat_fit_for_add_opp_r : ∀ M,
  bmat_fit_for_add M (bmat_opp M).
Proof.
intros.
induction M as [| M IHM] using bmatrix_ind2; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros * Hi Hj.
now apply IHM.
Qed.

(* square bmatrices *)
(* being a square bmatrix is a proposition *)

Fixpoint is_square_bmat_loop sizes (M : bmatrix T) {struct sizes} :=
  match M with
  | BM_1 _ => sizes = []
  | BM_M MM =>
      match sizes with
      | size :: sizes' =>
          mat_nrows MM = size ∧
          mat_ncols MM = size ∧
          (∀ i j, i < size → j < size →
           is_square_bmat_loop sizes' (mat_el MM i j))
      | [] => False
      end
  end.

Fixpoint is_square_bmat_bool_loop sizes (M : bmatrix T) {struct sizes} :=
  match M with
  | BM_1 _ => match sizes with [] => true | _ => false end
  | BM_M MM =>
      match sizes with
      | size :: sizes' =>
          ((mat_nrows MM =? size) &&
           (mat_ncols MM =? size) &&
           forallb
             (λ '(i, j), is_square_bmat_bool_loop sizes' (mat_el MM i j))
             (list_prod (seq 0 size) (seq 0 size)))%bool
      | [] => false
      end
  end.

(* Some kinds of square bmatrices are manipulated to make operations
   (addition, multiplication, ...) possible: the ones which have the
   same size (= number of rows = number of columns) at each level;
   this is computed by "sizes_of_bmatrix" which returns a list of
   naturals, the first one for the size of all submatrices at level
   1, the second one for the size of all submatrices at level 2, and
   so on. This is taken from the first matrix (upper left one) at
   each level. If the other matrices don't have the same size, they
   are going to be truncated or extended with 0s if necessary. *)

Fixpoint sizes_of_bmatrix (BM : bmatrix T) :=
  match BM with
  | BM_1 _ => []
  | BM_M M =>
      if zerop (mat_nrows M) ∨∨ zerop (mat_ncols M) then []
      else mat_nrows M :: sizes_of_bmatrix (mat_el M 0 0)
  end.

Definition is_square_bmat (BM : bmatrix T) :=
  is_square_bmat_loop (sizes_of_bmatrix BM) BM.

Definition is_square_bmat_bool (BM : bmatrix T) :=
  is_square_bmat_bool_loop (sizes_of_bmatrix BM) BM.

Arguments is_square_bmat BM%BM.

Theorem sizes_of_bmat_zero_like : ∀ (BM : bmatrix T),
  sizes_of_bmatrix (bmat_zero_like BM) = sizes_of_bmatrix BM.
Proof.
intros.
induction BM as [x| M IHBM] using bmatrix_ind2; [ easy | cbn ].
destruct (zerop (mat_nrows M)) as [Hr| Hr]; [ easy | ].
destruct (zerop (mat_ncols M)) as [Hc| Hc]; [ easy | ].
cbn; f_equal.
now apply IHBM.
Qed.

Theorem sizes_of_bmat_one_like : ∀ (BM : bmatrix T),
  sizes_of_bmatrix (bmat_one_like BM) = sizes_of_bmatrix BM.
Proof.
intros.
induction BM as [x| M IHBM] using bmatrix_ind2; [ easy | cbn ].
destruct (zerop (mat_nrows M)) as [Hr| Hr]; [ easy | ].
destruct (zerop (mat_ncols M)) as [Hc| Hc]; [ easy | ].
cbn; f_equal.
now apply IHBM.
Qed.

Theorem is_square_bmat_loop_IZ_like : ∀ u BM sizes,
  is_square_bmat_loop sizes BM
  → is_square_bmat_loop sizes (bmat_IZ_like u BM).
Proof.
intros * HBM.
revert u BM HBM.
induction sizes as [| size]; intros; [ now destruct BM | ].
cbn in HBM |-*.
destruct BM as [x| M]; [ easy | cbn ].
destruct HBM as (Hr & Hc & HBM).
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
now destruct (Nat.eq_dec i j); apply IHsizes, HBM.
Qed.

Theorem is_square_bmat_loop_zero_like : ∀ BM sizes,
  is_square_bmat_loop sizes BM
  → is_square_bmat_loop sizes (bmat_zero_like BM).
Proof.
intros * HBM.
now apply is_square_bmat_loop_IZ_like.
Qed.

Theorem is_square_bmat_zero_like : ∀ (BM : bmatrix T),
  is_square_bmat BM
  → is_square_bmat (bmat_zero_like BM).
Proof.
intros * HBM.
unfold is_square_bmat in HBM |-*.
rewrite sizes_of_bmat_zero_like.
now apply is_square_bmat_loop_zero_like.
Qed.

Theorem is_square_bmat_loop_one_like : ∀ BM sizes,
  is_square_bmat_loop sizes BM
  → is_square_bmat_loop sizes (bmat_one_like BM).
Proof.
intros * HBM.
now apply is_square_bmat_loop_IZ_like.
Qed.

Theorem is_square_bmat_one_like : ∀ (BM : bmatrix T),
  is_square_bmat BM
  → is_square_bmat (bmat_one_like BM).
Proof.
intros * HBM.
unfold is_square_bmat in HBM |-*.
rewrite sizes_of_bmat_one_like.
now apply is_square_bmat_loop_one_like.
Qed.

Theorem no_zero_bmat_size : ∀ (BM : bmatrix T), 0 ∉ sizes_of_bmatrix BM.
Proof.
intros * Hs.
induction BM as [x| M IHBM] using bmatrix_ind2; [ easy | ].
cbn in Hs.
destruct (zerop (mat_nrows M)) as [Hrz| Hrz]; [ easy | ].
destruct (zerop (mat_ncols M)) as [Hcz| Hcz]; [ easy | ].
cbn - [ In ] in Hs.
destruct Hs as [Hs| Hs]; [ now rewrite Hs in Hrz | ].
now apply (IHBM 0 0).
Qed.

Theorem sizes_of_bmatrix_mat_el :
  ∀ (M : matrix (bmatrix T)),
  is_square_bmat (BM_M M)
  → ∀ i j,
     i < mat_nrows M → j < mat_ncols M →
     sizes_of_bmatrix (mat_el M i j) = sizes_of_bmatrix (mat_el M 0 0).
Proof.
intros * Ha * Hi Hj.
cbn in Ha.
destruct (zerop (mat_nrows M)) as [Hrz| Hrz]; [ easy | ].
destruct (zerop (mat_ncols M)) as [Hcz| Hcz]; [ easy | cbn in Ha ].
destruct Ha as (_ & Hcr & Ha).
destruct M as (fa, ra, ca); cbn in *.
subst ca; clear Hrz Hcz.
remember (sizes_of_bmatrix (fa 0 0)) as sizes eqn:Hsizes.
specialize (Ha _ _ Hi Hj) as H1.
destruct sizes as [| size]; [ now destruct (fa i j) | cbn in H1 ].
remember (fa i j) as M eqn:Hm; symmetry in Hm.
destruct M as [x| M]; [ easy | ].
destruct H1 as (Hr & Hc & H1); cbn.
rewrite Hr, Hc.
destruct (zerop size) as [Hzs| Hzs]. {
  move Hzs at top; subst size; exfalso.
  specialize (no_zero_bmat_size (fa 0 0)) as H2.
  rewrite <- Hsizes in H2.
  now apply H2; left.
}
cbn; f_equal.
specialize (H1 0 0 Hzs Hzs) as H2.
specialize (no_zero_bmat_size (fa 0 0)) as H3.
rewrite <- Hsizes in H3.
clear Hsizes Hm Ha Hzs Hr Hc.
clear i j Hi Hj fa ra.
revert M size H1 H2 H3.
induction sizes as [| size1]; intros; [ now destruct (mat_el M 0 0) | ].
cbn in H2.
remember (mat_el M 0 0) as BM eqn:HBM; symmetry in HBM.
destruct BM as [x| M']; [ easy | ].
destruct H2 as (Hr' & Hc' & Hss); cbn.
rewrite Hr', Hc'.
destruct (zerop size1) as [Hs1| Hs1]. {
  exfalso.
  now apply H3; rewrite Hs1; right; left.
}
cbn; f_equal.
apply (IHsizes _ size1); [ easy | now apply Hss | ]. {
  intros H; apply H3.
  destruct H as [H| H]; [ now right; left | now right; right ].
}
Qed.

Theorem sizes_of_bmatrix_at_0_0 :
  ∀ (f : _ → _ → bmatrix T) r,
  (∀ i j, i < r → j < r →
      is_square_bmat_loop (sizes_of_bmatrix (f 0 0)) (f i j))
  → ∀ i j, i < r → j < r →
  sizes_of_bmatrix (f i j) = sizes_of_bmatrix (f 0 0).
Proof.
intros * Hf * Hi Hj.
apply (sizes_of_bmatrix_mat_el (mk_mat f r r)); cbn; [ | easy | easy ].
destruct (zerop r) as [Hrz| Hrz]; [ flia Hi Hrz | easy ].
Qed.

Theorem bmat_zero_like_add_distr : ∀ BMA BMB,
  bmat_zero_like (BMA + BMB)%BM =
  (bmat_zero_like BMA + bmat_zero_like BMB)%BM.
Proof.
intros.
revert BMB.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros; cbn. {
  destruct BMB as [xb| mb]; [ cbn | easy ].
  now rewrite srng_add_0_l.
}
destruct BMB as [xb| mb]; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
rewrite Tauto.if_same.
now apply IHBMA.
Qed.

Theorem bmat_zero_like_idemp :
  ∀ BM, bmat_zero_like (bmat_zero_like BM) = bmat_zero_like BM.
Proof.
intros.
induction BM as [x| M IHBM] using bmatrix_ind2; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
destruct M as (f, r, c); cbn in *.
rewrite Tauto.if_same.
now apply IHBM.
Qed.

Definition compatible_square_bmatrices (BML : list (bmatrix T)) :=
  ∃ sizes,
  ∀ BM, BM ∈ BML → is_square_bmat BM ∧ sizes_of_bmatrix BM = sizes.

Definition list_eqb T eqb d (l1 l2 : list T) :=
  (Nat.eqb (length l1) (length l2) &&
   forallb (λ i, eqb (nth i l1 d) (nth i l2 d)) (seq 0 (length l1)))%bool.

Definition compatible_square_bmatrices_bool (BML : list (bmatrix T)) :=
  (forallb is_square_bmat_bool BML &&
   forallb
     (λ BM,
        let sz1 := sizes_of_bmatrix BM in
        let sz2 := sizes_of_bmatrix (hd (BM_1 0%Srng) BML) in
        list_eqb Nat.eqb 0 sz1 sz2)
     BML)%bool.

Theorem is_square_bmat_bool_iff : ∀ BM,
  is_square_bmat BM ↔ is_square_bmat_bool BM = true.
Proof.
intros.
unfold is_square_bmat, is_square_bmat_bool.
remember (sizes_of_bmatrix BM) as sizes eqn:H; clear H.
split; intros Hbm. {
  revert sizes Hbm.
  induction BM as [x| m IHBM] using bmatrix_ind2; intros; cbn. {
    now destruct sizes.
  }
  destruct sizes as [| size]; [ easy | ].
  cbn in Hbm |-*.
  destruct Hbm as (Hr & Hc & Hbm).
  apply Bool.andb_true_iff.
  split; [ apply Bool.andb_true_iff; split | ]. {
    now apply Nat.eqb_eq.
  } {
    now apply Nat.eqb_eq.
  }
  apply forallb_forall.
  intros (i, j) Hij.
  apply in_prod_iff in Hij.
  destruct Hij as (Hi, Hj).
  apply in_seq in Hi.
  apply in_seq in Hj.
  apply IHBM; [ | | now apply Hbm ]. {
    now rewrite <- Hr in Hi.
  } {
    now rewrite <- Hc in Hj.
  }
} {
  revert sizes Hbm.
  induction BM as [x| m IHBM] using bmatrix_ind2; intros; cbn. {
    now destruct sizes.
  }
  destruct sizes as [| size]; [ easy | ].
  cbn in Hbm |-*.
  apply Bool.andb_true_iff in Hbm.
  destruct Hbm as (Hrc, Hbm).
  apply Bool.andb_true_iff in Hrc.
  destruct Hrc as (Hr, Hc).
  apply Nat.eqb_eq in Hr.
  apply Nat.eqb_eq in Hc.
  split; [ easy | ].
  split; [ easy | ].
  intros * Hi Hj.
  apply IHBM; [ now rewrite Hr | now rewrite Hc | ].
  specialize forallb_forall as H1.
  specialize (H1 (nat * nat)%type).
  specialize (H1 (λ '(i, j), is_square_bmat_bool_loop sizes (mat_el m i j))).
  specialize (H1 (list_prod (seq 0 size) (seq 0 size))).
  specialize (proj1 H1 Hbm (i, j)) as H2; clear H1.
  cbn in H2.
  apply H2.
  apply in_prod_iff.
  split. {
    apply in_seq; split; [ flia | easy ].
  } {
    apply in_seq; split; [ flia | easy ].
  }
}
Qed.

Theorem compatible_square_bmatrices_bool_iff : ∀ BML,
  compatible_square_bmatrices BML ↔
  compatible_square_bmatrices_bool BML = true.
Proof.
intros.
unfold compatible_square_bmatrices, compatible_square_bmatrices_bool.
split; intros Hbml. {
  destruct Hbml as (sizes, Hbml).
  apply Bool.andb_true_iff.
  split. {
    apply forallb_forall.
    intros BM Hbm.
    specialize (Hbml _ Hbm) as H1.
    specialize (Hbml (hd (BM_1 0%Rng) BML)) as H2.
    assert (H : hd (BM_1 0%Rng) BML ∈ BML). {
      destruct BML as [| BM0]; [ easy | cbn ].
      now left.
    }
    specialize (H2 H); clear H.
    now apply is_square_bmat_bool_iff.
  } {
    apply forallb_forall.
    intros BM Hbm.
    specialize (Hbml _ Hbm) as H1.
    specialize (Hbml (hd (BM_1 0%Rng) BML)) as H2.
    assert (H : hd (BM_1 0%Rng) BML ∈ BML). {
      destruct BML as [| BM0]; [ easy | cbn ].
      now left.
    }
    specialize (H2 H); clear H.
    destruct H1 as (_, H1).
    destruct H2 as (_, H2).
    rewrite H1, H2.
    unfold list_eqb.
    apply Bool.andb_true_iff.
    split; [ apply Nat.eqb_refl | ].
    apply forallb_forall.
    intros i Hi.
    apply Nat.eqb_refl.
  }
} {
  exists (sizes_of_bmatrix (hd (BM_1 0%Rng) BML)).
  intros BM Hbm.
  apply Bool.andb_true_iff in Hbml.
  destruct Hbml as (Hsq, Hsz).
  specialize (proj1 (forallb_forall _ _) Hsq _ Hbm) as H1.
  specialize (proj1 (forallb_forall _ _) Hsz _ Hbm) as H2.
  cbn in H2.
  apply is_square_bmat_bool_iff in H1.
  split; [ easy | ].
  unfold list_eqb in H2.
  apply Bool.andb_true_iff in H2.
  destruct H2 as (H2, H3).
  apply Nat.eqb_eq in H2.
  specialize (proj1 (forallb_forall _ _) H3) as H4.
  cbn in H4; clear H3.
  remember (sizes_of_bmatrix BM) as sizes eqn:Hsizes.
  apply List_eq_iff.
  split; [ easy | ].
  apply List_eq_iff.
  apply (nth_ext _ _ 0 0); [ easy | ].
  intros i d.
  assert (H : i ∈ seq 0 (length sizes)). {
    apply in_seq.
    split; [ flia | easy ].
  }
  specialize (H4 _ H); clear H.
  now apply Nat.eqb_eq in H4.
}
Qed.

Theorem bmat_zero_like_mul_distr_l : ∀ BMA BMB,
  is_square_bmat BMA
  → bmat_zero_like (BMA * BMB) = (bmat_zero_like BMA * BMB)%BM.
Proof.
intros * Ha.
revert BMB.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros. {
  destruct BMB as [xb| mb]; [ cbn | easy ].
  now rewrite srng_mul_0_l.
}
cbn - [ iter_seq ].
destruct BMB as [xb| mb]; [ easy | ].
cbn - [ iter_seq ]; f_equal.
apply matrix_eq; [ easy | easy | ].
cbn - [ iter_seq ].
intros * Hi Hj.
rewrite Tauto.if_same.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn - [ iter_seq ] in *.
destruct (zerop ra) as [H| H]; [ easy | cbn in Ha; clear H ].
destruct (zerop ca) as [H| H]; [ easy | cbn in Ha; clear H ].
destruct Ha as (_ & H & Ha); subst ca.
rewrite fold_bmat_zero_like.
replace
  (bmat_zero_like (iter_seq 0 (ra - 1) (λ a k, (a + fa i k * fb k j)%BM)
     (bmat_zero_like (fa 0 0))))
with
  (iter_seq 0 (ra - 1) (λ a k, (a + bmat_zero_like (fa i k * fb k j))%BM)
     (bmat_zero_like (fa 0 0))). 2: {
  clear IHBMA Ha Hi.
  induction ra. {
    cbn.
    rewrite bmat_zero_like_add_distr.
    now rewrite bmat_zero_like_idemp.
  }
  unfold iter_seq.
  rewrite Nat.sub_succ.
  do 2 rewrite Nat.sub_0_r.
  rewrite List_seq_succ_r.
  rewrite fold_left_app; cbn.
  rewrite fold_left_app; cbn.
  rewrite bmat_zero_like_add_distr.
  f_equal.
  destruct ra. {
    cbn; symmetry.
    apply bmat_zero_like_idemp.
  }
  rewrite Nat.sub_succ, Nat.sub_0_r in IHra.
  apply IHra.
}
rewrite bmat_zero_like_idemp.
apply List_fold_left_ext_in.
intros k BM Hk; f_equal.
rewrite Tauto.if_same.
rewrite fold_bmat_zero_like.
apply in_seq in Hk.
assert (Hk' : k < ra) by flia Hk Hi.
apply IHBMA; [ easy | easy | ].
rewrite sizes_of_bmatrix_at_0_0 with (r := ra); [ | easy | easy | easy ].
now apply Ha.
Qed.

Theorem bmat_zero_like_mul_distr_r : ∀ BMA BMB,
  is_square_bmat BMA
  → bmat_zero_like (BMA * BMB)%BM = (BMA * bmat_zero_like BMB)%BM.
Proof.
intros * Ha.
revert BMB.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros. {
  destruct BMB as [xb| mb]; [ cbn | easy ].
  now rewrite srng_mul_0_r.
}
destruct BMB as [xb| mb]; [ easy | ].
cbn - [ iter_seq ].
f_equal.
apply matrix_eq; [ easy | easy | ].
cbn - [ iter_seq ].
intros * Hi Hj.
rewrite Tauto.if_same.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn - [ iter_seq ] in *.
destruct (zerop ra) as [H| H]; [ easy | cbn in Ha; clear H ].
destruct (zerop ca) as [H| H]; [ easy | cbn in Ha; clear H ].
destruct Ha as (_ & H & Ha); subst ca.
rewrite fold_bmat_zero_like.
replace
  (bmat_zero_like (iter_seq 0 (ra - 1) (λ a k, (a + fa i k * fb k j)%BM)
     (bmat_zero_like (fa 0 0))))
with
  (iter_seq 0 (ra - 1) (λ a k, (a + bmat_zero_like (fa i k * fb k j))%BM)
     (bmat_zero_like (fa 0 0))). 2: {
  clear IHBMA Ha Hi Hj.
  induction ra. {
    cbn.
    rewrite bmat_zero_like_add_distr.
    now rewrite bmat_zero_like_idemp.
  }
  unfold iter_seq.
  rewrite Nat.sub_succ.
  do 2 rewrite Nat.sub_0_r.
  rewrite List_seq_succ_r.
  rewrite fold_left_app; cbn.
  rewrite fold_left_app; cbn.
  rewrite bmat_zero_like_add_distr.
  f_equal.
  destruct ra. {
    cbn; symmetry.
    apply bmat_zero_like_idemp.
  }
  rewrite Nat.sub_succ, Nat.sub_0_r in IHra.
  apply IHra.
}
apply List_fold_left_ext_in.
intros k BM Hk; f_equal.
rewrite Tauto.if_same.
rewrite fold_bmat_zero_like.
apply in_seq in Hk.
assert (Hk' : k < ra) by flia Hk Hi.
apply IHBMA; [ easy | easy | ].
rewrite sizes_of_bmatrix_at_0_0 with (r := ra); [ | easy | easy | easy ].
now apply Ha.
Qed.

Theorem bmat_zero_like_eq_compat : ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → bmat_zero_like BMA = bmat_zero_like BMB.
Proof.
intros * Ha Hb Hab.
unfold is_square_bmat in Ha, Hb.
rewrite <- Hab in Hb.
remember (sizes_of_bmatrix BMA) as sizes; clear Heqsizes Hab.
revert BMA BMB Ha Hb.
induction sizes as [| size]; intros; [ now destruct BMA, BMB | ].
cbn in Ha, Hb.
destruct BMA as [xa| ma]; [ easy | ].
destruct BMB as [xb| mb]; [ easy | ].
destruct Ha as (Hra & Hca & Ha).
destruct Hb as (Hrb & Hcb & Hb).
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *; subst ra ca rb cb.
f_equal.
apply matrix_eq; [ easy | easy | cbn ].
intros * Hi Hj.
rewrite Tauto.if_same.
apply IHsizes; [ now apply Ha | now apply Hb ].
Qed.

Theorem sizes_of_bmatrix_add : ∀ BMA BMB,
  sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → sizes_of_bmatrix (BMA + BMB)%BM = sizes_of_bmatrix BMA.
Proof.
intros * Hab.
revert BMB Hab.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros. {
  now destruct BMB.
}
destruct BMB as [xb| mb]; [ easy | cbn ].
move mb before ma.
cbn in Hab.
destruct (zerop (mat_nrows ma)) as [Hrza| Hrza]; [ easy | ].
destruct (zerop (mat_ncols ma)) as [Hcza| Hcza]; [ easy | ].
destruct (zerop (mat_nrows mb)) as [Hrzb| Hrzb]; [ easy | ].
destruct (zerop (mat_ncols mb)) as [Hczb| Hczb]; [ easy | ].
cbn in Hab |-*.
f_equal.
injection Hab; clear Hab; intros Hss H2.
now apply IHBMA.
Qed.

Theorem is_square_bmat_loop_add : ∀ BMA BMB sizes,
  is_square_bmat_loop sizes BMA
  → is_square_bmat_loop sizes BMB
  → is_square_bmat_loop sizes (BMA + BMB)%BM.
Proof.
intros * Ha Hb.
revert BMA BMB Ha Hb.
induction sizes as [| size]; intros; cbn; [ now destruct BMA, BMB | ].
cbn in Ha, Hb.
destruct BMA as [xa| ma]; [ easy | ].
destruct BMB as [xb| mb]; [ easy | ].
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb); cbn in *.
destruct Ha as (Hra & Hca & Ha).
destruct Hb as (Hrb & Hcb & Hb).
subst ra ca rb cb.
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
apply IHsizes; [ now apply Ha | now apply Hb ].
Qed.

Theorem is_square_bmat_fit_for_add : ∀ sizes (MA MB : bmatrix T),
  is_square_bmat_loop sizes MA
  → is_square_bmat_loop sizes MB
  ↔ bmat_fit_for_add MA MB.
Proof.
intros * Ha.
split; intros Hb. {
  revert MA MB Ha Hb.
  induction sizes as [| size]; intros; [ now destruct MA, MB | ].
  cbn in Ha, Hb.
  destruct MA as [xa| ma]; [ easy | ].
  destruct MB as [xb| mb]; [ easy | cbn ].
  destruct Ha as (Hra & Hca & Ha).
  destruct Hb as (Hrb & Hcb & Hb).
  split; [ congruence | ].
  split; [ congruence | ].
  intros * Hi Hj.
  apply IHsizes; [ apply Ha; congruence | apply Hb; congruence ].
} {
  revert MA MB Ha Hb.
  induction sizes as [| size]; intros; [ now destruct MA, MB | ].
  destruct MA as [xa| ma]; [ easy | ].
  destruct MB as [xb| mb]; [ easy | cbn ].
  cbn in Ha, Hb |-*.
  destruct Ha as (Hra & Hca & Ha).
  destruct Hb as (Hrb & Hcb & Hb).
  split; [ congruence | ].
  split; [ congruence | ].
  intros * Hi Hj.
  apply (IHsizes (mat_el ma i j)); [ now apply Ha | ].
  apply Hb; congruence.
}
Qed.

Theorem bmat_add_0_l : ∀ BM,
  (bmat_zero_like BM + BM)%BM = BM.
Proof.
intros.
induction BM as [x| M IHBM] using bmatrix_ind2. {
  now cbn; rewrite srng_add_0_l.
}
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
rewrite Tauto.if_same.
now apply IHBM.
Qed.

Theorem bmat_add_0_r : ∀ BM,
  (BM + bmat_zero_like BM)%BM = BM.
Proof.
intros.
induction BM as [x| M IHBM] using bmatrix_ind2. {
  now cbn; rewrite srng_add_0_r.
}
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
rewrite Tauto.if_same.
now apply IHBM.
Qed.

Theorem is_square_bmat_loop_mul : ∀ BMA BMB sizes,
  is_square_bmat_loop sizes BMA
  → is_square_bmat_loop sizes BMB
  → is_square_bmat_loop sizes (BMA * BMB)%BM.
Proof.
intros * Ha Hb.
revert BMA BMB Ha Hb.
induction sizes as [| size]; intros; [ now destruct BMA, BMB | ].
cbn in Ha, Hb |-*.
destruct BMA as [xa| ma]; [ easy | ].
destruct BMB as [xb| mb]; [ easy | ].
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb); cbn - [ iter_seq ] in *.
destruct Ha as (Hra & Hca & Ha).
destruct Hb as (Hrb & Hcb & Hb).
subst ra ca rb cb.
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
assert (H : 0 < size) by flia Hi.
specialize (Ha 0 0 H H) as Ha00.
clear H.
assert (H : ∀ j, j < size → is_square_bmat_loop sizes (fa i j)). {
  intros k Hk.
  now apply Ha.
}
move H before Ha; clear Ha; rename H into Ha.
assert (H : ∀ i, i < size → is_square_bmat_loop sizes (fb i j)). {
  intros k Hk.
  now apply Hb.
}
move H before Hb; clear Hb; rename H into Hb.
destruct size; [ easy | ].
cbn - [ iter_seq ].
clear Hi Hj.
move j before i.
rewrite Nat.sub_0_r.
induction size. {
  cbn.
  apply is_square_bmat_loop_add. {
    now apply is_square_bmat_loop_zero_like.
  }
  apply IHsizes; [ apply Ha; flia | apply Hb; flia ].
}
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
apply is_square_bmat_loop_add. 2: {
  apply IHsizes; [ apply Ha; flia | apply Hb; flia ].
}
apply IHsize. {
  intros k Hk.
  apply Ha; flia Hk.
} {
  intros k Hk.
  apply Hb; flia Hk.
}
Qed.

Theorem sizes_of_bmatrix_fold_left : ∀ BM sta len f,
  (∀ n, sta ≤ n < sta + len → sizes_of_bmatrix BM = sizes_of_bmatrix (f n))
  → sizes_of_bmatrix (fold_left (λ acc j, (acc + f j)%BM) (seq sta len) BM) =
    sizes_of_bmatrix BM.
Proof.
intros * Hfb.
revert sta BM Hfb.
induction len; intros; [ easy | cbn ].
rewrite IHlen. 2: {
  intros * Hn.
  rewrite sizes_of_bmatrix_add. {
    apply Hfb; flia Hn.
  } {
    apply Hfb; flia.
  }
}
apply sizes_of_bmatrix_add.
apply Hfb; flia.
Qed.

Theorem sizes_of_bmatrix_mul_a : ∀ fa fb ra,
  (∀ i j,
   i < S (S ra)
   → j < S (S ra)
   → is_square_bmat_loop (sizes_of_bmatrix (fa i j)) (fa i j)
   → ∀ BMB,
      is_square_bmat BMB
      → sizes_of_bmatrix (fa i j) = sizes_of_bmatrix BMB
      → sizes_of_bmatrix (fa i j * BMB)%BM = sizes_of_bmatrix (fa i j))
  → (∀ i j, i < S (S ra) → j < S (S ra) →
      is_square_bmat_loop (sizes_of_bmatrix (fa 0 0)) (fa i j))
  → (∀ i j, i < S (S ra) → j < S (S ra) →
      is_square_bmat_loop (sizes_of_bmatrix (fb 0 0)) (fb i j))
  → sizes_of_bmatrix (fa 0 0) = sizes_of_bmatrix (fb 0 0)
  → is_square_bmat_loop (sizes_of_bmatrix (fa 0 ra * fb ra 0)%BM) (fa 0 ra).
Proof.
intros * IHBMA Ha Hb Hab.
assert (Hzr : 0 < S (S ra)) by flia.
assert (H5 : ra < S (S ra)) by flia.
assert
  (H6' : sizes_of_bmatrix (fa 0 ra) = sizes_of_bmatrix (fa 0 0)). {
  apply sizes_of_bmatrix_at_0_0 with (r := S ra). {
    intros i j Hi Hj.
    apply Ha; [ flia Hi | flia Hj ].
  } {
    flia.
  } {
    flia.
  }
}
assert
  (H7' : sizes_of_bmatrix (fb ra 0) = sizes_of_bmatrix (fb 0 0)). {
  apply sizes_of_bmatrix_at_0_0 with (r := S ra). {
    intros i j Hi Hj.
    apply Hb; [ flia Hi | flia Hj ].
  } {
    flia.
  } {
    flia.
  }
}
rewrite IHBMA; [ | easy | easy | | | congruence ]. {
  now rewrite H6'; apply Ha.
} {
  now rewrite H6'; apply Ha.
} {
  unfold is_square_bmat.
  now rewrite H7'; apply Hb.
}
Qed.

Arguments sizes_of_bmatrix BM%BM.

Theorem is_square_bmat_add : ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → is_square_bmat (BMA + BMB)%BM.
Proof.
intros * Ha Hb Hab.
unfold is_square_bmat.
rewrite sizes_of_bmatrix_add; [ | easy ].
apply is_square_bmat_loop_add; [ apply Ha | ].
rewrite Hab.
apply Hb.
Qed.

Theorem sizes_of_bmatrix_mul : ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → sizes_of_bmatrix (BMA * BMB) = sizes_of_bmatrix BMA.
Proof.
intros * Ha Hb Hab.
revert BMB Hb Hab.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros. {
  now destruct BMB.
}
destruct BMB as [xb| mb]; [ easy | ].
cbn - [ iter_seq ].
move mb before ma.
cbn in Ha, Hb, Hab.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn - [ iter_seq ] in *.
destruct (zerop ra) as [Hraz| Hraz]; [ easy | ].
destruct (zerop ca) as [Hcaz| Hcaz]; [ easy | ].
destruct (zerop rb) as [Hrbz| Hrbz]; [ easy | ].
destruct (zerop cb) as [Hcbz| Hcbz]; [ easy | ].
cbn - [ iter_seq ] in Ha, Hb, Hab |-*.
f_equal.
destruct Ha as (_ & H & Ha); subst ca.
destruct Hb as (_ & H & Hb); subst cb.
injection Hab; clear Hab; intros Hab H; subst rb.
clear Hcaz Hcbz Hrbz.
revert Hraz.
induction ra; intros; [ easy | clear Hraz ].
assert
  (H : ∀ i j,
   i < ra → j < ra
   → is_square_bmat_loop (sizes_of_bmatrix (fa i j)) (fa i j)
   → ∀ BMB : bmatrix T,
       is_square_bmat BMB
       → sizes_of_bmatrix (fa i j) = sizes_of_bmatrix BMB
       → sizes_of_bmatrix (fa i j * BMB)%BM = sizes_of_bmatrix (fa i j)). {
  intros i j Hi Hj Hsa * HBMB Hss.
  apply IHBMA; [ flia Hi | flia Hj | easy | easy | easy ].
}
specialize (IHra H); clear H.
assert
  (H : ∀ i j,
   i < ra → j < ra
   → is_square_bmat_loop (sizes_of_bmatrix (fa 0 0)) (fa i j)). {
  intros * Hi Hj.
  apply Ha; [ flia Hi | flia Hj ].
}
specialize (IHra H); clear H.
assert
  (H : ∀ i j,
   i < ra → j < ra
   → is_square_bmat_loop (sizes_of_bmatrix (fb 0 0)) (fb i j)). {
  intros * Hi Hj.
  apply Hb; [ flia Hi | flia Hj ].
}
specialize (IHra H); clear H.
assert (Hsa : is_square_bmat (fa 0 0)) by (apply Ha; flia).
assert (Hsb : is_square_bmat (fb 0 0)) by (apply Hb; flia).
assert
  (Hssm :
   sizes_of_bmatrix (fa 0 0 * fb 0 0)%BM = sizes_of_bmatrix (fa 0 0)). {
  apply IHBMA; [ flia | flia | apply Ha; flia |  apply Hb; flia| easy ].
}
assert
  (Hsaba :
     is_square_bmat_loop (sizes_of_bmatrix (fa 0 0 * fb 0 0)%BM) (fa 0 0)). {
  assert (Hzr : 0 < S ra) by flia.
  rewrite IHBMA; [ | flia | flia | | | easy ]. {
    now apply Ha.
  } {
    now apply Ha.
  } {
    now apply Hb.
  }
}
assert
  (Hsabb :
     is_square_bmat_loop (sizes_of_bmatrix (fa 0 0 * fb 0 0)%BM) (fb 0 0)). {
  assert (Hzr : 0 < S ra) by flia.
  rewrite IHBMA; [ | flia | flia | | | easy ]. {
    now rewrite Hab; apply Hb.
  } {
    now apply Ha.
  } {
    now apply Hb.
  }
}
assert
  (Haj :
   ∀ j, j < S ra → sizes_of_bmatrix (fa 0 j) = sizes_of_bmatrix (fa 0 0)). {
  intros j Hj.
  apply (@sizes_of_bmatrix_at_0_0 _ (S ra)); [ | flia Hj | easy ].
  intros i k Hi Hk.
  apply Ha; [ flia Hi | flia Hk ].
}
assert
  (Hbj : ∀ j, j < S ra →
   sizes_of_bmatrix (fb j 0) = sizes_of_bmatrix (fb 0 0)). {
  intros j Hj.
  apply (@sizes_of_bmatrix_at_0_0 _ (S ra)); [ | easy | flia Hj ].
  intros i k Hi Hk.
  apply Hb; [ flia Hi | flia Hk ].
}
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite sizes_of_bmatrix_add. {
  destruct ra; [ apply sizes_of_bmat_zero_like | ].
  rewrite Nat.sub_succ, Nat.sub_0_r in IHra.
  unfold iter_seq in IHra.
  apply IHra; flia.
} {
  destruct ra; [ now cbn; rewrite sizes_of_bmat_zero_like | ].
  unfold iter_seq in IHra.
  rewrite Nat.sub_succ, (Nat.sub_0_r ra) in IHra.
  rewrite IHra; [ | flia ].
  symmetry.
  assert (H0ss : 0 < S (S ra)) by flia.
  assert (Hssr : S ra < S (S ra)) by flia.
  rewrite IHBMA; [ now apply Haj | easy | easy | | | ]. {
    rewrite Haj; [ now apply Ha | easy ].
  } {
    unfold is_square_bmat.
    rewrite Hbj; [ now apply Hb | easy ].
  } {
    rewrite Haj; [ now rewrite Hbj | easy ].
  }
}
Qed.

Theorem is_square_bmat_mul : ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → is_square_bmat (BMA * BMB)%BM.
Proof.
intros * Ha Hb Hab.
unfold is_square_bmat.
rewrite sizes_of_bmatrix_mul; [ | easy | easy | easy ].
apply is_square_bmat_loop_mul; [ apply Ha | ].
rewrite Hab.
apply Hb.
Qed.

Theorem bmat_zero_like_mul : ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → bmat_zero_like (BMA * BMB)%BM = bmat_zero_like BMA.
Proof.
intros * Ha Hb Hab.
apply bmat_zero_like_eq_compat; [ | easy | ]. {
  now apply is_square_bmat_mul.
}
now apply sizes_of_bmatrix_mul.
Qed.

Theorem bmat_zero_like_sqr : ∀ BM,
  is_square_bmat BM
  → bmat_zero_like (BM * BM)%BM = bmat_zero_like BM.
Proof.
intros * Hss.
now apply bmat_zero_like_mul.
Qed.

Theorem bmat_mul_0_l : ∀ BM,
  is_square_bmat BM
  → (bmat_zero_like BM * BM)%BM = bmat_zero_like BM.
Proof.
intros * Hss.
rewrite <- bmat_zero_like_mul_distr_l; [ | easy ].
now apply bmat_zero_like_sqr.
Qed.

Theorem bmat_mul_0_r : ∀ BM,
  is_square_bmat BM
  → (BM * bmat_zero_like BM)%BM = bmat_zero_like BM.
Proof.
intros * Hss.
rewrite <- bmat_zero_like_mul_distr_r; [ | easy ].
now apply bmat_zero_like_sqr.
Qed.

Theorem sizes_of_bmatrix_IZ : ∀ n u,
  sizes_of_bmatrix (IZ_2_pow u n) = repeat 2 n.
Proof.
intros.
induction n; [ easy | now cbn; f_equal ].
Qed.

Theorem IZ_is_square_bmat : ∀ n u,
  is_square_bmat (IZ_2_pow u n).
Proof.
intros.
revert u.
induction n; intros; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
destruct i; cbn. {
  destruct j; [ apply IHn | cbn ].
  destruct j; [ | flia Hj ].
  rewrite sizes_of_bmatrix_IZ.
  rewrite <- (sizes_of_bmatrix_IZ n 0%Srng).
  apply IHn.
}
destruct i; [ | flia Hi ].
destruct j; cbn. {
  rewrite sizes_of_bmatrix_IZ.
  rewrite <- (sizes_of_bmatrix_IZ n 0%Srng).
  apply IHn.
}
destruct j; [ | flia Hj ].
apply IHn.
Qed.

Theorem bmat_mul_Z_2_pow_l : ∀ n M,
  bmat_fit_for_add (I_2_pow n) M
  → bmat_mul (Z_2_pow n) M = Z_2_pow n.
Proof.
intros * Hss.
revert M Hss.
induction n; intros. {
  cbn.
  destruct M as [xm| mm]; [ now cbn; rewrite srng_mul_0_l | easy ].
}
destruct M as [xm| mm]; [ easy | ].
cbn in Hss.
destruct Hss as (Hr & Hc & Hss).
cbn; f_equal.
rewrite <- Hc.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
specialize (Hss 0 0 Nat.lt_0_2 Nat.lt_0_2) as Hij00; cbn in Hij00.
specialize (Hss 0 1 Nat.lt_0_2 Nat.lt_1_2) as Hij01; cbn in Hij01.
specialize (Hss 1 0 Nat.lt_1_2 Nat.lt_0_2) as Hij10; cbn in Hij10.
specialize (Hss 1 1 Nat.lt_1_2 Nat.lt_1_2) as Hij11; cbn in Hij11.
destruct i. {
  destruct j. {
    rewrite IHn; [ cbn | easy ].
    rewrite IHn. 2: {
      transitivity (Z_2_pow n); [ | easy ].
      apply bmat_fit_for_add_IZ_IZ.
    }
    rewrite bmat_add_0_l.
    now apply old_bmat_add_0_l.
  }
  destruct j; [ cbn | flia Hj ].
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite IHn; [ | easy ].
  rewrite bmat_add_0_l.
  now apply old_bmat_add_0_l.
}
destruct i; [ cbn | flia Hi ].
destruct j. {
  rewrite IHn; [ | easy ].
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite bmat_add_0_l.
  now apply old_bmat_add_0_l.
}
destruct j; [ | flia Hj ].
rewrite IHn. 2: {
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite IHn; [ | easy ].
rewrite bmat_add_0_l.
now apply old_bmat_add_0_l.
Qed.

Theorem bmat_fit_for_add_sizes : ∀ BMA BMB,
  bmat_fit_for_add BMA BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB.
Proof.
intros * Hab.
revert BMB Hab.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros. {
  now destruct BMB.
}
destruct BMB as [xb| mb]; [ easy | ].
cbn in Hab |-*.
destruct Hab as (Hr & Hc & Hab).
rewrite <- Hr, <- Hc.
destruct (zerop (mat_nrows ma)) as [Hzr| Hzr]; [ easy | ].
destruct (zerop (mat_ncols ma)) as [Hzc| Hzc]; [ easy | cbn ].
f_equal.
apply IHBMA; [ easy | easy | ].
now apply Hab.
Qed.

Theorem bmat_mul_Z_2_pow_r : ∀ n u M,
  bmat_fit_for_add (IZ_2_pow u n) M
  → bmat_mul M (Z_2_pow n) = Z_2_pow n.
Proof.
intros * Hss.
revert M Hss.
revert u.
induction n; intros. {
  cbn.
  destruct M as [xm| mm]; [ now cbn; rewrite srng_mul_0_r | easy ].
}
destruct M as [xm| mm]; [ easy | ].
cbn in Hss.
destruct Hss as (Hr & Hc & Hss).
cbn; f_equal.
rewrite <- Hr, <- Hc.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
specialize (Hss 0 0 Nat.lt_0_2 Nat.lt_0_2) as Hij00; cbn in Hij00.
specialize (Hss 0 1 Nat.lt_0_2 Nat.lt_1_2) as Hij01; cbn in Hij01.
specialize (Hss 1 0 Nat.lt_1_2 Nat.lt_0_2) as Hij10; cbn in Hij10.
specialize (Hss 1 1 Nat.lt_1_2 Nat.lt_1_2) as Hij11; cbn in Hij11.
assert
  (H1 :
     (bmat_zero_like (mat_el mm 0 0) + Z_2_pow n + Z_2_pow n)%BM =
     Z_2_pow n). {
  rewrite (bmat_zero_like_eq_compat _ (Z_2_pow n)); cycle 1. {
    specialize (Hss 0 0 Nat.lt_0_2 Nat.lt_0_2).
    cbn in Hss.
    unfold is_square_bmat.
    remember (sizes_of_bmatrix (mat_el mm 0 0)) as sizes eqn:Hsizes.
    apply (is_square_bmat_fit_for_add sizes (IZ_2_pow u n)); [ | easy ].
    rewrite Hsizes.
    rewrite (bmat_fit_for_add_sizes _ (IZ_2_pow u n)); [ | easy ].
    apply IZ_is_square_bmat.
  } {
    apply IZ_is_square_bmat.
  } {
    apply bmat_fit_for_add_sizes.
    transitivity (IZ_2_pow u n); [ easy | ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite bmat_add_0_l.
  now apply old_bmat_add_0_l.
}
destruct i. {
  destruct j. {
    rewrite (IHn u); [ cbn | easy ].
    rewrite (IHn u); [ easy | ].
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  } {
    destruct j; [ cbn | flia Hj ].
    rewrite (IHn u); [ cbn | easy ].
    rewrite (IHn u); [ easy | ].
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
} {
  destruct i; [ | flia Hi ].
  destruct j. {
    rewrite (IHn u); [ now rewrite (IHn u) | ].
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  } {
    destruct j; [ cbn | flia Hj ].
    rewrite (IHn u); [ now rewrite (IHn u) | ].
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
}
Qed.

Theorem bmat_fit_for_add_add_l : ∀ MA MB MC,
  bmat_fit_for_add MA MC
  → bmat_fit_for_add MB MC
  → bmat_fit_for_add (MA + MB)%BM MC.
Proof.
intros * Hssac Hssbc.
revert MA MB Hssac Hssbc.
induction MC as [xc| mc IHMC] using bmatrix_ind2; intros. {
  destruct MA; [ now destruct MB | easy ].
}
destruct MA as [xa| ma]; [ easy | ].
destruct MB as [xb| mb]; [ easy | ].
cbn in Hssac, Hssbc |-*.
destruct Hssac as (Hrac & Hcac & Hssac).
destruct Hssbc as (Hrbc & Hcbc & Hssbc).
split; [ easy | ].
split; [ easy | ].
intros * Hi Hj.
apply IHMC; [ | | now apply Hssac | ]. {
  now rewrite Hrac in Hi.
} {
  now rewrite Hcac in Hj.
} {
  apply Hssbc. {
    now rewrite Hrac, <- Hrbc in Hi.
  } {
    now rewrite Hcac, <- Hcbc in Hj.
  }
}
Qed.

Theorem bmat_fit_for_add_add_r : ∀ MA MB MC,
  bmat_fit_for_add MA MB
  → bmat_fit_for_add MA MC
  → bmat_fit_for_add MA (MB + MC)%BM.
Proof.
intros * Hssab Hsscc.
symmetry.
now apply bmat_fit_for_add_add_l.
Qed.

Theorem old_bmat_mul_1_l : ∀ n M,
  bmat_fit_for_add (I_2_pow n) M
  → bmat_mul (I_2_pow n) M = M.
Proof.
intros * Hss.
revert M Hss.
induction n; intros. {
  cbn.
  destruct M as [x| M]; [ now rewrite srng_mul_1_l | easy ].
}
cbn.
destruct M as [x| M]; [ easy | f_equal ].
cbn in Hss.
destruct Hss as (Hr & Hc & Hss).
rewrite <- Hc.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
rewrite <- Hc in Hj.
specialize (Hss 0 0 Nat.lt_0_2 Nat.lt_0_2) as Hij00; cbn in Hij00.
specialize (Hss 0 1 Nat.lt_0_2 Nat.lt_1_2) as Hij01; cbn in Hij01.
specialize (Hss 1 0 Nat.lt_1_2 Nat.lt_0_2) as Hij10; cbn in Hij10.
specialize (Hss 1 1 Nat.lt_1_2 Nat.lt_1_2) as Hij11; cbn in Hij11.
destruct i. {
  cbn.
  rewrite IHn. 2: {
    destruct j; [ easy | ].
    destruct j; [ | flia Hj ].
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite fold_Z_2_pow.
  rewrite bmat_mul_Z_2_pow_l. 2: {
    destruct j. {
      transitivity (Z_2_pow n); [ | easy ].
      apply bmat_fit_for_add_IZ_IZ.
    }
    destruct j; [ easy | flia Hj ].
  }
  destruct j. {
    rewrite old_bmat_add_0_r. 2: {
      apply -> is_square_bmat_fit_for_add. 2: {
        apply IZ_is_square_bmat.
      }
      apply is_square_bmat_loop_add. 2: {
        apply <- is_square_bmat_fit_for_add in Hij00; [ apply Hij00 | ].
        rewrite sizes_of_bmatrix_IZ.
        rewrite <- (sizes_of_bmatrix_IZ n 1%Srng).
        apply IZ_is_square_bmat.
      }
      apply is_square_bmat_loop_zero_like.
      rewrite sizes_of_bmatrix_IZ.
      rewrite <- (sizes_of_bmatrix_IZ n 1%Srng).
      apply IZ_is_square_bmat.
    }
    rewrite (bmat_zero_like_eq_compat _ (mat_el M 0 0)); cycle 1. {
      apply IZ_is_square_bmat.
    } {
      apply <- is_square_bmat_fit_for_add; [ apply Hij00 | ].
      apply bmat_fit_for_add_sizes in Hij00.
      rewrite <- Hij00.
      apply IZ_is_square_bmat.
    } {
      now apply bmat_fit_for_add_sizes in Hij00.
    }
    apply bmat_add_0_l.
  } {
    destruct j; [ | flia Hj ].
    rewrite old_bmat_add_0_r. 2: {
      apply -> is_square_bmat_fit_for_add. 2: {
        apply IZ_is_square_bmat.
      }
      apply is_square_bmat_loop_add. 2: {
        apply <- is_square_bmat_fit_for_add in Hij01; [ apply Hij01 | ].
        apply IZ_is_square_bmat.
      }
      apply is_square_bmat_loop_zero_like.
      rewrite sizes_of_bmatrix_IZ.
      rewrite <- (sizes_of_bmatrix_IZ n 1%Srng).
      apply IZ_is_square_bmat.
    }
    rewrite (bmat_zero_like_eq_compat _ (mat_el M 0 1)); cycle 1. {
      apply IZ_is_square_bmat.
    } {
      apply <- is_square_bmat_fit_for_add; [ apply Hij01 | ].
      apply bmat_fit_for_add_sizes in Hij01.
      rewrite <- Hij01.
      apply IZ_is_square_bmat.
    } {
      apply bmat_fit_for_add_sizes in Hij01.
      unfold I_2_pow.
      rewrite sizes_of_bmatrix_IZ.
      now rewrite <- (sizes_of_bmatrix_IZ n 0%Srng).
    }
    apply bmat_add_0_l.
  }
}
destruct i; [ cbn | flia Hi ].
rewrite fold_Z_2_pow.
rewrite bmat_mul_Z_2_pow_l. 2: {
  destruct j; [ easy | ].
  destruct j; [ | flia Hj ].
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite IHn. 2: {
  destruct j. {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  destruct j; [ easy | flia Hj ].
}
rewrite old_bmat_add_0_r. 2: {
  apply -> is_square_bmat_fit_for_add; [ | apply IZ_is_square_bmat ].
  apply is_square_bmat_loop_zero_like.
  rewrite sizes_of_bmatrix_IZ.
  rewrite <- (sizes_of_bmatrix_IZ n 1%Srng).
  apply IZ_is_square_bmat.
}
rewrite (bmat_zero_like_eq_compat _ (mat_el M 1 j)); cycle 1. {
  apply IZ_is_square_bmat.
} {
  destruct j. {
    apply <- is_square_bmat_fit_for_add; [ apply Hij10 | ].
    apply bmat_fit_for_add_sizes in Hij10.
    rewrite <- Hij10.
    apply IZ_is_square_bmat.
  } {
    destruct j; [ | flia Hj ].
    apply <- is_square_bmat_fit_for_add; [ apply Hij11 | ].
    apply bmat_fit_for_add_sizes in Hij11.
    rewrite <- Hij11.
    apply IZ_is_square_bmat.
  }
} {
  destruct j. {
    apply bmat_fit_for_add_sizes in Hij10.
    rewrite <- Hij10.
    unfold I_2_pow.
    now do 2 rewrite sizes_of_bmatrix_IZ.
  } {
    destruct j; [ | flia Hj ].
    now apply bmat_fit_for_add_sizes in Hij11.
  }
}
apply bmat_add_0_l.
Qed.

Theorem old_bmat_mul_1_r : ∀ n M,
  bmat_fit_for_add (I_2_pow n) M
  → bmat_mul M (I_2_pow n) = M.
Proof.
intros * Hss.
revert M Hss.
induction n; intros. {
  cbn.
  destruct M as [x| M]; [ now cbn; rewrite srng_mul_1_r | easy ].
}
destruct M as [x| M]; [ easy | cbn; f_equal ].
cbn in Hss.
destruct Hss as (Hr & Hc & Hss).
rewrite <- Hc; cbn.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
rewrite <- Hr in Hi.
rewrite <- Hc in Hj.
specialize (Hss 0 0 Nat.lt_0_2 Nat.lt_0_2) as Hij00; cbn in Hij00.
specialize (Hss 0 1 Nat.lt_0_2 Nat.lt_1_2) as Hij01; cbn in Hij01.
specialize (Hss 1 0 Nat.lt_1_2 Nat.lt_0_2) as Hij10; cbn in Hij10.
specialize (Hss 1 1 Nat.lt_1_2 Nat.lt_1_2) as Hij11; cbn in Hij11.
destruct i. {
  destruct j. {
    rewrite IHn; [ | easy ].
    rewrite fold_Z_2_pow.
    rewrite bmat_add_0_l.
    rewrite (bmat_mul_Z_2_pow_r _ 0%Srng); [ | easy ].
    apply old_bmat_add_0_r.
    transitivity (I_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  } {
    destruct j; [ | flia Hj ].
    rewrite (bmat_mul_Z_2_pow_r _ 1%Srng); [ | easy ].
    rewrite IHn. 2: {
      transitivity (Z_2_pow n); [ | easy ].
      apply bmat_fit_for_add_IZ_IZ.
    }
    rewrite old_bmat_add_0_r. 2: {
      apply -> is_square_bmat_fit_for_add; [ | apply IZ_is_square_bmat ].
      apply is_square_bmat_loop_zero_like.
      apply <- is_square_bmat_fit_for_add; [ apply Hij00 | ].
      rewrite sizes_of_bmatrix_IZ.
      rewrite <- (sizes_of_bmatrix_IZ _ 1%Srng).
      apply IZ_is_square_bmat.
    }
    rewrite (bmat_zero_like_eq_compat _ (mat_el M 0 1)); cycle 1. {
      apply <- is_square_bmat_fit_for_add; [ apply Hij00 | ].
      apply bmat_fit_for_add_sizes in Hij00.
      rewrite <- Hij00.
      apply IZ_is_square_bmat.
    } {
      apply <- is_square_bmat_fit_for_add; [ apply Hij01 | ].
      apply bmat_fit_for_add_sizes in Hij01.
      rewrite <- Hij01.
      apply IZ_is_square_bmat.
    } {
      apply bmat_fit_for_add_sizes in Hij00.
      apply bmat_fit_for_add_sizes in Hij01.
      unfold I_2_pow in Hij00.
      rewrite sizes_of_bmatrix_IZ in Hij00, Hij01.
      congruence.
    }
    apply bmat_add_0_l.
  }
}
destruct i; [ cbn | flia Hi ].
destruct j. {
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite fold_Z_2_pow.
  rewrite (bmat_mul_Z_2_pow_r _ 1%Srng); [ | easy ].
  rewrite old_bmat_add_0_r. 2: {
    apply bmat_fit_for_add_add_r; [ | easy ].
    apply -> is_square_bmat_fit_for_add. {
      apply is_square_bmat_loop_zero_like.
      apply <- is_square_bmat_fit_for_add in Hij00.
      apply Hij00.
      apply IZ_is_square_bmat.
    }
    rewrite sizes_of_bmatrix_IZ.
    rewrite <- (sizes_of_bmatrix_IZ _ 0%Srng).
    apply IZ_is_square_bmat.
  }
  rewrite (bmat_zero_like_eq_compat _ (mat_el M 1 0)); cycle 1. {
    apply <- is_square_bmat_fit_for_add; [ apply Hij00 | ].
    apply bmat_fit_for_add_sizes in Hij00.
    rewrite <- Hij00.
    apply IZ_is_square_bmat.
  } {
    apply <- is_square_bmat_fit_for_add; [ apply Hij10 | ].
    apply bmat_fit_for_add_sizes in Hij10.
    rewrite <- Hij10.
    apply IZ_is_square_bmat.
  } {
    apply bmat_fit_for_add_sizes in Hij00.
    apply bmat_fit_for_add_sizes in Hij10.
    unfold I_2_pow in Hij00.
    rewrite sizes_of_bmatrix_IZ in Hij00, Hij10.
    congruence.
  }
  apply bmat_add_0_l.
}
destruct j; [ | flia Hj ].
rewrite fold_Z_2_pow.
rewrite (bmat_mul_Z_2_pow_r _ 0%Srng). 2: {
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite IHn; [ | easy ].
rewrite old_bmat_add_0_r. 2: {
  apply -> is_square_bmat_fit_for_add; [ | apply IZ_is_square_bmat ].
  apply is_square_bmat_loop_zero_like.
  apply <- is_square_bmat_fit_for_add; [ | apply IZ_is_square_bmat ].
  transitivity (I_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite (bmat_zero_like_eq_compat _ (mat_el M 1 1)); cycle 1. {
  apply <- is_square_bmat_fit_for_add; [ apply Hij00 | ].
  apply bmat_fit_for_add_sizes in Hij00.
  rewrite <- Hij00.
  apply IZ_is_square_bmat.
} {
  apply <- is_square_bmat_fit_for_add; [ apply Hij11 | ].
  apply bmat_fit_for_add_sizes in Hij11.
  rewrite <- Hij11.
  apply IZ_is_square_bmat.
} {
  apply bmat_fit_for_add_sizes in Hij00.
  apply bmat_fit_for_add_sizes in Hij11.
  unfold I_2_pow in Hij00, Hij11.
  rewrite sizes_of_bmatrix_IZ in Hij00, Hij11.
  congruence.
}
apply bmat_add_0_l.
Qed.

Theorem bmat_nat_mul_l_succ : ∀ n M,
  bmat_nat_mul_l (S n) M = bmat_add (bmat_nat_mul_l n M) M.
Proof.
intros.
induction M as [x| M IHM] using bmatrix_ind2. {
  remember (S n) as sn; cbn; subst sn.
  f_equal.
  revert x.
  induction n; intros; [ easy | ].
  remember (S n) as sn; cbn; subst sn.
  rewrite <- (Nat.add_1_r n) at 1.
  rewrite seq_app; cbn.
  rewrite srng_add_0_l.
  apply fold_left_app.
}
cbn.
f_equal.
now apply matrix_eq.
Qed.

Theorem bmat_add_opp_r : ∀ M,
  bmat_add M (bmat_opp M) = bmat_zero_like M.
Proof.
intros.
induction M as [x| M IHM] using bmatrix_ind2; intros. {
  cbn.
  rewrite fold_rng_sub.
  now rewrite rng_add_opp_r.
}
cbn; f_equal.
apply matrix_eq; [ easy | easy | cbn ].
intros * Hi Hj.
rewrite Tauto.if_same.
now apply IHM.
Qed.

Theorem bmat_nat_mul_0_r : ∀ k n,
  bmat_nat_mul_l k (Z_2_pow n) = Z_2_pow n.
Proof.
intros.
revert k.
induction n; intros. {
  cbn; f_equal.
  unfold rng_mul_nat_l.
  destruct k; [ easy | ].
  now apply all_0_srng_summation_0.
}
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
destruct i. {
  destruct j; [ easy | cbn ].
  destruct j; [ easy | flia Hj ].
}
destruct i; [ | flia Hi ].
destruct j; [ easy | cbn ].
destruct j; [ easy | flia Hj ].
Qed.

Theorem bmat_add_add_swap : ∀ MA MB MC,
  bmat_fit_for_add MA MB
  → bmat_fit_for_add MA MC
  → (MA + MB + MC = MA + MC + MB)%BM.
Proof.
intros * Hssab Hssac.
revert MB MC Hssab Hssac.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  destruct MB as [xb| mb]; [ cbn | easy ].
  destruct MC as [xc| mc]; [ cbn | easy ].
  now rewrite srng_add_add_swap.
}
destruct MB as [xb| mb]; [ easy | ].
destruct MC as [xc| mc]; [ easy | cbn ].
f_equal.
apply matrix_eq; [ easy | easy | cbn ].
intros i j Hi Hj.
apply IHMA; [ easy | easy | now apply Hssab | now apply Hssac ].
Qed.

Theorem bmat_add_assoc : ∀ MA MB MC,
  bmat_fit_for_add MA MB
  → bmat_fit_for_add MB MC
  → (MA + (MB + MC) = (MA + MB) + MC)%BM.
Proof.
intros * Hssab Hssbc.
rewrite bmat_add_comm. 2: {
  symmetry.
  apply bmat_fit_for_add_add_l; symmetry; [ easy | ].
  now transitivity MB.
}
rewrite (bmat_add_comm MA MB); [ | easy ].
apply bmat_add_add_swap; [ easy | now symmetry ].
Qed.

Theorem bmat_zero_like_add_diag : ∀ BM,
  bmat_zero_like (BM + BM)%BM = bmat_zero_like BM.
Proof.
intros.
induction BM as [x| m IHBM] using bmatrix_ind2; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
rewrite Tauto.if_same.
now apply IHBM.
Qed.

(**)

Theorem bmat_mul_add_distr_r :
  ∀ (MA MB MC : bmatrix T),
  compatible_square_bmatrices [MA; MB; MC]
  → ((MA + MB) * MC = MA * MC + MB * MC)%BM.
Proof.
intros * Hcsb.
destruct Hcsb as (sizes & Hcsb).
revert MA MB sizes Hcsb.
induction MC as [xc| mc IHMC] using bmatrix_ind2; intros. {
  unfold is_square_bmat in Hcsb.
  destruct sizes as [| size]. 2: {
    specialize (Hcsb _ (or_intror (or_intror (or_introl eq_refl)))).
    destruct Hcsb as (Hsq, Hsz).
    now rewrite Hsz in Hsq.
  }
  destruct MA as [xa| ma]. 2: {
    specialize (Hcsb _ (or_introl eq_refl)).
    destruct Hcsb as (Hsq, Hsz).
    now rewrite Hsz in Hsq.
  }
  destruct MB as [xb| mb]. 2: {
    specialize (Hcsb _ (or_intror (or_introl eq_refl))).
    destruct Hcsb as (Hsq, Hsz).
    now rewrite Hsz in Hsq.
  }
  now cbn; rewrite srng_mul_add_distr_r.
}
destruct sizes as [| size]. {
  specialize (Hcsb _ (or_intror (or_intror (or_introl eq_refl)))).
  destruct Hcsb as (Hsq, Hsz).
  unfold is_square_bmat in Hsq.
  now rewrite Hsz in Hsq.
}
destruct MA as [xa| ma]. {
  now specialize (Hcsb _ (or_introl eq_refl)).
}
destruct MB as [xb| mb]; [ easy | ].
specialize (Hcsb _ (or_introl eq_refl)) as Ha.
specialize (Hcsb _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hcsb _ (or_intror (or_intror (or_introl eq_refl)))) as Hc.
destruct Ha as (Ha, Has).
destruct Hb as (Hb, Hbs).
destruct Hc as (Hc, Hcs).
unfold is_square_bmat in Ha, Hb, Hc.
rewrite Has in Ha; rewrite Hbs in Hb; rewrite Hcs in Hc.
(**)
cbn - [ seq ]; f_equal.
apply matrix_eq; [ easy | easy | ].
cbn - [ seq ].
unfold iter_seq.
intros i j Hi Hj.
replace (S (mat_ncols ma - 1)) with (mat_ncols ma). 2: {
  rewrite <- Nat.sub_succ_l; [ flia | ].
  destruct Ha as (H1 & H2 & _).
  rewrite H2, <- H1; flia Hi.
}
replace (S (mat_ncols mb - 1)) with (mat_ncols mb). 2: {
  rewrite <- Nat.sub_succ_l; [ flia | ].
  cbn in Ha, Hb.
  destruct Ha as (H1 & H2 & _).
  destruct Hb as (H3 & H4 & _).
  rewrite H4, <- H1; flia Hi.
}
do 2 rewrite Nat.sub_0_r.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
destruct mc as (fc, rc, cc).
cbn - [ In ] in *.
cbn in Ha, Hb, Hc.
destruct Ha as (H1 & H2 & Ha); subst ra ca.
destruct Hb as (H1 & H2 & Hb); subst rb cb.
destruct Hc as (H1 & H2 & Hc); subst rc cc.
destruct (zerop size) as [H| H]; [ easy | ].
cbn in Has, Hbs, Hcs; clear H.
injection Has; clear Has; intros Has.
injection Hbs; clear Hbs; intros Hbs.
injection Hcs; clear Hcs; intros Hcs.
replace
  (fold_left
    (λ (acc : bmatrix T) (j0 : nat), (acc + (fa i j0 + fb i j0) * fc j0 j)%BM)
    (seq 0 size) (bmat_zero_like (fa 0 0 + fb 0 0)%BM))
with
  (fold_left
    (λ (acc : bmatrix T) (j0 : nat),
       (acc + (fa i j0 * fc j0 j + fb i j0 * fc j0 j))%BM)
    (seq 0 size) (bmat_zero_like (fa 0 0 + fb 0 0)%BM)). 2: {
  apply List_fold_left_ext_in.
  intros k M Hk.
  f_equal.
  apply in_seq in Hk.
  symmetry.
  apply IHMC with (sizes := sizes); [ flia Hk | easy | ].
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  intros BM HBM.
  unfold is_square_bmat.
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia Hk ].
    split; [ | easy ].
    apply Ha; [ easy | flia Hk ].
  }
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | flia Hk ].
    split; [ | easy ].
    apply Hb; [ easy | flia Hk ].
  }
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hk | easy ].
    split; [ | easy ].
    apply Hc; [ flia Hk | easy ].
  }
  easy.
}
assert (Hfa00 : is_square_bmat_loop sizes (fa 0 0)). {
  apply Ha; flia Hi.
}
assert (Hfb00 : is_square_bmat_loop sizes (fb 0 0)). {
  apply Hb; flia Hi.
}
assert (H : ∀ j, j < size → is_square_bmat_loop sizes (fa i j)). {
  now intros; apply Ha.
}
move H before Ha; clear Ha; rename H into Ha.
assert (H : ∀ j, j < size → is_square_bmat_loop sizes (fb i j)). {
  now intros; apply Hb.
}
move H before Hb; clear Hb; rename H into Hb.
assert (H : ∀ i, i < size → is_square_bmat_loop sizes (fc i j)). {
  now intros; apply Hc.
}
move H before Hc; clear Hc; rename H into Hc.
clear Hi Hj IHMC Hcsb.
induction size; [ apply bmat_zero_like_add_distr | ].
rewrite List_seq_succ_r; cbn.
do 3 rewrite fold_left_app; cbn.
rewrite IHsize; cycle 1. {
  intros k Hk; apply Ha; flia Hk.
} {
  intros k Hk; apply Hb; flia Hk.
} {
  intros k Hk; apply Hc; flia Hk.
}
clear IHsize.
remember
  (fold_left (λ acc j0, acc + fa i j0 * fc j0 j) (seq 0 size)
     (bmat_zero_like (fa 0 0)))%BM as x.
remember
  (fold_left (λ acc j0, acc + fb i j0 * fc j0 j) (seq 0 size)
     (bmat_zero_like (fb 0 0)))%BM as y.
remember (fa i size) as u.
remember (fb i size) as v.
remember (fc size j) as w.
move y before x; move u before y.
move v before u; move w before v.
assert (Hx : is_square_bmat_loop sizes x). {
  subst x.
  clear Heqy Hequ Heqv Heqw.
  induction size. {
    now apply is_square_bmat_loop_zero_like.
  }
  rewrite List_seq_succ_r; cbn.
  rewrite fold_left_app; cbn.
  apply is_square_bmat_loop_add. 2: {
    apply is_square_bmat_loop_mul; [ apply Ha; flia | apply Hc; flia ].
  }
  apply IHsize. {
    intros k Hk; apply Ha; flia Hk.
  } {
    intros k Hk; apply Hb; flia Hk.
  } {
    intros k Hk; apply Hc; flia Hk.
  }
}
assert (Hy : is_square_bmat_loop sizes y). {
  subst y.
  clear Heqx Hequ Heqv Heqw.
  induction size. {
    now apply is_square_bmat_loop_zero_like.
  }
  rewrite List_seq_succ_r; cbn.
  rewrite fold_left_app; cbn.
  apply is_square_bmat_loop_add. 2: {
    apply is_square_bmat_loop_mul; [ apply Hb; flia | apply Hc; flia ].
  }
  apply IHsize. {
    intros k Hk; apply Ha; flia Hk.
  } {
    intros k Hk; apply Hb; flia Hk.
  } {
    intros k Hk; apply Hc; flia Hk.
  }
}
assert (Su : is_square_bmat_loop sizes u) by (subst u; apply Ha; flia).
assert (Sv : is_square_bmat_loop sizes v) by (subst v; apply Hb; flia).
assert (Sw : is_square_bmat_loop sizes w) by (subst w; apply Hc; flia).
assert (Sxy : is_square_bmat_loop sizes (x + y)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Suw : is_square_bmat_loop sizes (u * w)%BM). {
  now apply is_square_bmat_loop_mul.
}
assert (Svw : is_square_bmat_loop sizes (v * w)%BM). {
  now apply is_square_bmat_loop_mul.
}
assert (Syvw : is_square_bmat_loop sizes (y + v * w)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Hxy : bmat_fit_for_add x y). {
  now apply (is_square_bmat_fit_for_add sizes).
}
assert (Hx_yvw : bmat_fit_for_add x (y + v * w)%BM). {
  now apply (is_square_bmat_fit_for_add sizes).
}
assert (Hx_uw : bmat_fit_for_add x (u * w)%BM). {
  now apply (is_square_bmat_fit_for_add sizes).
}
assert (Hxy_vw : bmat_fit_for_add (x + y)%BM (v * w)%BM). {
  now apply (is_square_bmat_fit_for_add sizes).
}
assert (Hy_vw : bmat_fit_for_add y (v * w)%BM). {
  now apply (is_square_bmat_fit_for_add sizes).
}
assert (Huw_vw : bmat_fit_for_add (u * w)%BM (v * w)%BM). {
  now apply (is_square_bmat_fit_for_add sizes).
}
rewrite <- (bmat_add_add_swap _ _ (u * w)%BM); [ | easy | easy ].
rewrite (bmat_add_assoc x); [ | easy | easy ].
rewrite <- (bmat_add_assoc (x + y)%BM); [ | easy | now symmetry ].
f_equal.
now apply bmat_add_comm.
Qed.

Theorem bmat_mul_add_distr_l :
  ∀ (MA MB MC : bmatrix T),
  compatible_square_bmatrices [MA; MB; MC]
  → (MA * (MB + MC) = MA * MB + MA * MC)%BM.
Proof.
intros * Hcsb.
destruct Hcsb as (sizes & Hcsb).
revert MA MB sizes Hcsb.
induction MC as [xc| mc IHMC] using bmatrix_ind2; intros. {
  unfold is_square_bmat in Hcsb.
  destruct sizes as [| size]. 2: {
    specialize (Hcsb _ (or_intror (or_intror (or_introl eq_refl)))).
    destruct Hcsb as (Hsq, Hsz).
    now rewrite Hsz in Hsq.
  }
  destruct MA as [xa| ma]. 2: {
    specialize (Hcsb _ (or_introl eq_refl)).
    destruct Hcsb as (Hsq, Hsz).
    now rewrite Hsz in Hsq.
  }
  destruct MB as [xb| mb]. 2: {
    specialize (Hcsb _ (or_intror (or_introl eq_refl))).
    destruct Hcsb as (Hsq, Hsz).
    now rewrite Hsz in Hsq.
  }
  now cbn; rewrite srng_mul_add_distr_l.
}
destruct sizes as [| size]. {
  specialize (Hcsb _ (or_intror (or_intror (or_introl eq_refl)))).
  destruct Hcsb as (Hsq, Hsz).
  unfold is_square_bmat in Hsq.
  now rewrite Hsz in Hsq.
}
destruct MA as [xa| ma]. {
  now specialize (Hcsb _ (or_introl eq_refl)).
}
destruct MB as [xb| mb]; [ easy | ].
specialize (Hcsb _ (or_introl eq_refl)) as Ha.
specialize (Hcsb _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hcsb _ (or_intror (or_intror (or_introl eq_refl)))) as Hc.
destruct Ha as (Ha, Has).
destruct Hb as (Hb, Hbs).
destruct Hc as (Hc, Hcs).
unfold is_square_bmat in Ha, Hb, Hc.
rewrite Has in Ha; rewrite Hbs in Hb; rewrite Hcs in Hc.
cbn - [ seq ]; f_equal.
apply matrix_eq; [ easy | easy | ].
cbn - [ seq ].
unfold iter_seq.
intros i j Hi Hj.
replace (S (mat_ncols ma - 1)) with (mat_ncols ma). 2: {
  rewrite <- Nat.sub_succ_l; [ flia | ].
  destruct Ha as (H1 & H2 & _).
  rewrite H2, <- H1; flia Hi.
}
rewrite Nat.sub_0_r.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
destruct mc as (fc, rc, cc).
cbn - [ In ] in *.
cbn in Ha, Hb, Hc.
destruct Ha as (H1 & H2 & Ha); subst ra ca.
destruct Hb as (H1 & H2 & Hb); subst rb cb.
destruct Hc as (H1 & H2 & Hc); subst rc cc.
destruct (zerop size) as [H| H]; [ easy | ].
cbn in Has, Hbs, Hcs; clear H.
injection Has; clear Has; intros Has.
injection Hbs; clear Hbs; intros Hbs.
injection Hcs; clear Hcs; intros Hcs.
replace
  (fold_left
    (λ (acc : bmatrix T) (k : nat),
       (acc + fa i k * (fb k j + fc k j))%BM)
    (seq 0 size) (bmat_zero_like (fa 0 0)%BM))
with
  (fold_left
    (λ (acc : bmatrix T) (k : nat),
       (acc + (fa i k * fb k j + fa i k * fc k j))%BM)
    (seq 0 size) (bmat_zero_like (fa 0 0)%BM)). 2: {
  apply List_fold_left_ext_in.
  intros k M Hk.
  f_equal.
  apply in_seq in Hk.
  symmetry.
  apply IHMC with (sizes := sizes); [ flia Hk | easy | ].
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  intros BM HBM.
  unfold is_square_bmat.
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia Hk ].
    split; [ | easy ].
    apply Ha; [ easy | flia Hk ].
  }
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | easy ].
    split; [ | easy ].
    now apply Hb.
  }
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hk | easy ].
    split; [ | easy ].
    apply Hc; [ flia Hk | easy ].
  }
  easy.
}
assert (Hfa00 : is_square_bmat_loop sizes (fa 0 0)). {
  apply Ha; flia Hi.
}
assert (Hfb00 : is_square_bmat_loop sizes (fb 0 0)). {
  apply Hb; flia Hi.
}
assert (H : ∀ j, j < size → is_square_bmat_loop sizes (fa i j)). {
  now intros; apply Ha.
}
move H before Ha; clear Ha; rename H into Ha.
assert (H : ∀ i, i < size → is_square_bmat_loop sizes (fb i j)). {
  now intros; apply Hb.
}
move H before Hb; clear Hb; rename H into Hb.
assert (H : ∀ i, i < size → is_square_bmat_loop sizes (fc i j)). {
  now intros; apply Hc.
}
move H before Hc; clear Hc; rename H into Hc.
clear Hi Hj IHMC Hcsb.
induction size. {
  cbn; symmetry.
  rewrite <- bmat_zero_like_add_distr.
  apply bmat_zero_like_add_diag.
}
rewrite List_seq_succ_r; cbn.
do 3 rewrite fold_left_app; cbn.
rewrite IHsize; cycle 1. {
  intros k Hk; apply Ha; flia Hk.
} {
  intros k Hk; apply Hb; flia Hk.
} {
  intros k Hk; apply Hc; flia Hk.
}
clear IHsize.
remember
  (fold_left (λ acc j0, acc + fa i j0 * fb j0 j) (seq 0 size)
     (bmat_zero_like (fa 0 0)))%BM as x.
remember
  (fold_left (λ acc j0, acc + fa i j0 * fc j0 j) (seq 0 size)
     (bmat_zero_like (fa 0 0)))%BM as y.
remember (fa i size) as u.
remember (fb size j) as v.
remember (fc size j) as w.
move y before x; move u before y.
move v before u; move w before v.
assert (Hx : is_square_bmat_loop sizes x). {
  subst x.
  clear Heqy Hequ Heqv Heqw.
  induction size. {
    now apply is_square_bmat_loop_zero_like.
  }
  rewrite List_seq_succ_r; cbn.
  rewrite fold_left_app; cbn.
  apply is_square_bmat_loop_add. 2: {
    apply is_square_bmat_loop_mul; [ apply Ha; flia | apply Hb; flia ].
  }
  apply IHsize. {
    intros k Hk; apply Ha; flia Hk.
  } {
    intros k Hk; apply Hb; flia Hk.
  } {
    intros k Hk; apply Hc; flia Hk.
  }
}
assert (Hy : is_square_bmat_loop sizes y). {
  subst y.
  clear Heqx Hequ Heqv Heqw.
  induction size. {
    now apply is_square_bmat_loop_zero_like.
  }
  rewrite List_seq_succ_r; cbn.
  rewrite fold_left_app; cbn.
  apply is_square_bmat_loop_add. 2: {
    apply is_square_bmat_loop_mul; [ apply Ha; flia | apply Hc; flia ].
  }
  apply IHsize; intros k Hk. {
    apply Ha; flia Hk.
  } {
    apply Hb; flia Hk.
  } {
    apply Hc; flia Hk.
  }
}
assert (Su : is_square_bmat_loop sizes u) by (subst u; apply Ha; flia).
assert (Sv : is_square_bmat_loop sizes v) by (subst v; apply Hb; flia).
assert (Sw : is_square_bmat_loop sizes w) by (subst w; apply Hc; flia).
assert (Sxy : is_square_bmat_loop sizes (x + y)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Suv : is_square_bmat_loop sizes (u * v)%BM). {
  now apply is_square_bmat_loop_mul.
}
assert (Suw : is_square_bmat_loop sizes (u * w)%BM). {
  now apply is_square_bmat_loop_mul.
}
assert (Sy_uw : is_square_bmat_loop sizes (y + u * w)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Hxy : bmat_fit_for_add x y). {
  now apply (is_square_bmat_fit_for_add sizes).
}
assert (Hx_yuw : bmat_fit_for_add x (y + u * w)%BM). {
  now apply (is_square_bmat_fit_for_add sizes).
}
assert (Hx_uv : bmat_fit_for_add x (u * v)%BM). {
  now apply (is_square_bmat_fit_for_add sizes).
}
assert (Hxy_uw : bmat_fit_for_add (x + y)%BM (u * w)%BM). {
  now apply (is_square_bmat_fit_for_add sizes).
}
assert (Hy_uw : bmat_fit_for_add y (u * w)%BM). {
  now apply (is_square_bmat_fit_for_add sizes).
}
assert (Huw_uv : bmat_fit_for_add (u * w)%BM (u * v)%BM). {
  now apply (is_square_bmat_fit_for_add sizes).
}
rewrite <- (bmat_add_add_swap _ _ (u * v)%BM); [ | easy | easy ].
rewrite (bmat_add_assoc x); [ | easy | easy ].
rewrite <- (bmat_add_assoc (x + y)%BM); [ | easy | easy ].
f_equal.
now apply bmat_add_comm.
Qed.

Theorem bmat_mul_assoc :
  ∀ (MA MB MC : bmatrix T),
  compatible_square_bmatrices [MA; MB; MC]
  → (MA * (MB * MC) = (MA * MB) * MC)%BM.
Proof.
intros * Hcsb.
destruct Hcsb as (sizes & Hcsb).
revert MB MC sizes Hcsb.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  unfold is_square_bmat in Hcsb.
  destruct sizes as [| size]. 2: {
    specialize (Hcsb _ (or_introl eq_refl)).
    destruct Hcsb as (Hsq, Hsz).
    now rewrite Hsz in Hsq.
  }
  destruct MB as [xb| mb]. 2: {
    specialize (Hcsb _ (or_intror (or_introl eq_refl))).
    destruct Hcsb as (Hsq, Hsz).
    now rewrite Hsz in Hsq.
  }
  destruct MC as [xc| mc]. 2: {
    specialize (Hcsb _ (or_intror (or_intror (or_introl eq_refl)))).
    destruct Hcsb as (Hsq, Hsz).
    now rewrite Hsz in Hsq.
  }
  now cbn; rewrite srng_mul_assoc.
}
destruct sizes as [| size]. {
  specialize (Hcsb _ (or_introl eq_refl)).
  destruct Hcsb as (Hsq, Hsz).
  unfold is_square_bmat in Hsq.
  now rewrite Hsz in Hsq.
}
destruct MB as [xb| mb]. {
  now specialize (Hcsb _ (or_intror (or_introl eq_refl))).
}
destruct MC as [xc| mc]; [ easy | ].
specialize (Hcsb _ (or_introl eq_refl)) as Ha.
specialize (Hcsb _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hcsb _ (or_intror (or_intror (or_introl eq_refl)))) as Hc.
destruct Ha as (Ha, Has).
destruct Hb as (Hb, Hbs).
destruct Hc as (Hc, Hcs).
unfold is_square_bmat in Ha, Hb, Hc.
rewrite Has in Ha; rewrite Hbs in Hb; rewrite Hcs in Hc.
cbn - [ seq ]; f_equal.
apply matrix_eq; [ easy | easy | ].
cbn - [ seq ].
unfold iter_seq.
intros i j Hi Hj.
replace (S (mat_ncols ma - 1)) with (mat_ncols ma). 2: {
  rewrite <- Nat.sub_succ_l; [ flia | ].
  destruct Ha as (H1 & H2 & _).
  rewrite H2, <- H1; flia Hi.
}
replace (S (mat_ncols mb - 1)) with (mat_ncols mb). 2: {
  rewrite <- Nat.sub_succ_l; [ flia | ].
  cbn in Ha, Hb.
  destruct Ha as (H1 & H2 & _).
  destruct Hb as (H3 & H4 & _).
  rewrite H4, <- H1; flia Hi.
}
do 2 rewrite Nat.sub_0_r.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
destruct mc as (fc, rc, cc).
cbn - [ In ] in *.
cbn in Ha, Hb, Hc.
destruct Ha as (H1 & H2 & Ha); subst ra ca.
destruct Hb as (H1 & H2 & Hb); subst rb cb.
destruct Hc as (H1 & H2 & Hc); subst rc cc.
destruct (zerop size) as [H| H]; [ easy | ].
cbn in Has, Hbs, Hcs; clear H.
injection Has; clear Has; intros Has.
injection Hbs; clear Hbs; intros Hbs.
injection Hcs; clear Hcs; intros Hcs.
(**)
replace size with (S (size - 1) - 0).
erewrite List_fold_left_ext_in. 2: {
  intros k M Hk.
  rewrite fold_iter_seq.
  easy.
}
rewrite fold_iter_seq.
symmetry.
erewrite List_fold_left_ext_in. 2: {
  intros k M Hk.
  rewrite fold_iter_seq.
  easy.
}
do 2 rewrite fold_iter_seq.
symmetry.
(**)
erewrite iter_seq_eq_compat. 2: {
  intros k Hk.
...
  rewrite mul_iter_seq_distr_l; [ easy | ].
  intros y z.
  apply bmat_mul_add_distr_l.
...
replace
  (fold_left
     (λ (acc : bmatrix T) (j0 : nat),
        (acc +
         fa i j0 *
         fold_left (λ acc0 j1, acc0 + fb j0 j1 * fc j1 j)
           (seq 0 size) (bmat_zero_like (fb 0 0)))%BM) 
     (seq 0 size) (bmat_zero_like (fa 0 0)))
with
  (fold_left
     (λ (acc : bmatrix T) (j0 : nat),
        (acc +
         fold_left
           (λ acc0 j1, acc0 + fa i j0 * (fb j0 j1 * fc j1 j))
           (seq 0 size) (bmat_zero_like (fb 0 0)))%BM) 
     (seq 0 size) (bmat_zero_like (fa 0 0))). 2: {
  apply List_fold_left_ext_in.
  intros k M Hk.
  f_equal.
  apply in_seq in Hk.
  cbn in Hk; destruct Hk as (_, Hk).
  specialize (Ha i k Hi Hk) as Haik.
  assert (Hbz : is_square_bmat_loop sizes (fb 0 0)). {
    intros; apply Hb; flia Hk.
  }
  assert (Hbk : ∀ j, j < size → is_square_bmat_loop sizes (fb k j)). {
    now intros; apply Hb.
  }
  assert (Hcj : ∀ i, i < size → is_square_bmat_loop sizes (fc i j)). {
    now intros; apply Hc.
  }
  assert (Haiks : sizes_of_bmatrix (fa i k) = sizes). {
    rewrite (@sizes_of_bmatrix_at_0_0 _ size); [ easy | | easy | easy ].
    now rewrite <- Has in Ha.
  }
  assert (Hbks : ∀ j, j < size → sizes_of_bmatrix (fb k j) = sizes). {
    intros l Hl.
    rewrite (@sizes_of_bmatrix_at_0_0 _ size); [ easy | | easy | easy ].
    now rewrite <- Hbs in Hb.
  }
  assert (Hcjs : ∀ i, i < size → sizes_of_bmatrix (fc i j) = sizes). {
    intros l Hl.
    rewrite (@sizes_of_bmatrix_at_0_0 _ size); [ easy | | easy | easy ].
    now rewrite <- Hcs in Hc.
  }
  specialize (IHMA i k Hi Hk) as IHMAik.
  remember (fa i k) as faik; clear Heqfaik.
  destruct size; [ easy | ].
  clear - sp scp IHMAik Haik Hbk Hcj Haiks Hbks Hcjs Hbz Hbs.
  revert j k Hbk Hcj Hbks Hcjs.
  induction size; intros. {
    cbn.
    rewrite bmat_mul_add_distr_l. 2: {
      exists sizes.
      intros BM HBM.
      unfold is_square_bmat.
      destruct HBM as [H| HBM]; [ subst BM | ]. {
        now rewrite <- Haiks in Haik.
      }
      destruct HBM as [H| HBM]; [ subst BM | ]. {
        rewrite sizes_of_bmat_zero_like.
        split; [ | easy ].
        rewrite Hbs.
        now apply is_square_bmat_loop_zero_like.
      }
      destruct HBM as [H| ]; [ | easy ].
      subst BM.
      rewrite sizes_of_bmatrix_mul; cycle 1. {
        unfold is_square_bmat.
        rewrite Hbks; [ | flia ].
        apply Hbk; flia.
      } {
        unfold is_square_bmat.
        rewrite Hcjs; [ | flia ].
        apply Hcj; flia.
      } {
        rewrite Hbks; [ | flia ].
        rewrite Hcjs; [ easy | flia ].
      }
      rewrite Hbks; [ | flia ].
      split; [ | easy ].
      apply is_square_bmat_loop_mul; [ apply Hbk; flia | ].
      apply Hcj; flia.
    }
    rewrite IHMAik with (sizes := sizes). 2: {
      intros BM HBM.
      destruct HBM as [H| HBM]. {
        subst BM.
        unfold is_square_bmat.
        now rewrite Haiks.
      }
      destruct HBM as [H| HBM]. {
        subst BM.
        unfold is_square_bmat.
        rewrite Hbks; [ | flia ].
        split; [ | easy ].
        apply Hbk; flia.
      } {
        destruct HBM as [H| ]; [ | easy ].
        subst BM.
        unfold is_square_bmat.
        rewrite Hcjs; [ | flia ].
        split; [ | easy ].
        apply Hcj; flia.
      }
    }
    f_equal.
    rewrite <- bmat_zero_like_mul_distr_r. 2: {
      unfold is_square_bmat.
      now rewrite Haiks.
    }
    rewrite bmat_zero_like_mul; cycle 1. {
      unfold is_square_bmat.
      now rewrite Haiks.
    } {
      unfold is_square_bmat.
      now rewrite Hbs.
    } {
      congruence.
    }
    apply bmat_zero_like_eq_compat. {
      unfold is_square_bmat.
      now rewrite Hbs.
    } {
      unfold is_square_bmat.
      now rewrite Haiks.
    } {
      congruence.
    }
  }
  rewrite List_seq_succ_r.
  remember (S size) as ss; cbn; subst ss.
  do 2 rewrite fold_left_app.
  remember (S size) as ss; cbn; subst ss.
  rewrite IHsize; cycle 1. {
    intros l Hl; apply Hbk; flia Hl.
  } {
    intros l Hl; apply Hcj; flia Hl.
  } {
    intros l Hl; apply Hbks; flia Hl.
  } {
    intros l Hl; apply Hcjs; flia Hl.
  }
  symmetry.
  apply bmat_mul_add_distr_l.
  exists sizes.
  intros BM HBM.
  unfold is_square_bmat.
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    now rewrite <- Haiks in Haik.
  }
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    rewrite sizes_of_bmatrix_fold_left. 2: {
      intros l Hl.
      rewrite sizes_of_bmat_zero_like.
      rewrite sizes_of_bmatrix_mul; cycle 1. {
        unfold is_square_bmat.
        rewrite Hbks; [ | flia Hl ].
        apply Hbk; flia Hl.
      } {
        unfold is_square_bmat.
        rewrite Hcjs; [ | flia Hl ].
        apply Hcj; flia Hl.
      } {
        rewrite Hbks; [ | flia Hl ].
        rewrite Hcjs; [ easy | flia Hl ].
      }
      rewrite Hbks; [ easy | flia Hl ].
    }
    rewrite sizes_of_bmat_zero_like.
    split; [ | easy ].
    rewrite Hbs.
    clear IHsize.
    induction size. {
      cbn.
...
    split; [ | easy ].
    rewrite Hbs.
    now apply is_square_bmat_loop_zero_like.
  }
      destruct HBM as [H| ]; [ | easy ].
      subst BM.
      rewrite sizes_of_bmatrix_mul; cycle 1. {
        unfold is_square_bmat.
        rewrite Hbks; [ | flia ].
        apply Hbk; flia.
      } {
        unfold is_square_bmat.
        rewrite Hcjs; [ | flia ].
        apply Hcj; flia.
      } {
        rewrite Hbks; [ | flia ].
        rewrite Hcjs; [ easy | flia ].
      }
      rewrite Hbks; [ | flia ].
      split; [ | easy ].
      apply is_square_bmat_loop_mul; [ apply Hbk; flia | ].
      apply Hcj; flia.
    }
    rewrite IHMAik with (sizes := sizes). 2: {
      intros BM HBM.
      destruct HBM as [H| HBM]. {
        subst BM.
  intros
...
  rewrite IHsize.
...
        rewrite Hbks.
        rewrite sizes_of_bmat_zero_like.
        rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia Hk ].
        split; [ | easy ].
        apply Ha; [ easy | flia Hk ].
      }
      rewrite <- Has in Ha.
    rewrite <- Hbs in Hb.
    rewrite <- Hcs in Hc.
...
    rewrite (bmat_zero_like_eq_compat _ faik); cycle 1. {
      unfold is_square_bmat.
      rewrite H
...
  symmetry.
  clear Hcsb.
  destruct size; [ easy | ].
  rewrite List_seq_succ_r.
  do 2 rewrite fold_left_app; cbn.
  set (MB' := (fold_left (λ (acc0 : bmatrix T) (j1 : nat), acc0 + fb k j1 * fc j1 j) (seq 0 size) (bmat_zero_like (fb 0 0)))%BM).
  set (MC' := (fb k size * fc size j)%BM).
  rewrite bmat_mul_add_distr_l. 2: {
    exists sizes.
    rewrite <- Has in Ha.
    rewrite <- Hbs in Hb.
    rewrite <- Hcs in Hc.
    intros BM HBM.
    unfold is_square_bmat.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia Hk ].
      split; [ | easy ].
      apply Ha; [ easy | flia Hk ].
    }
    destruct HBM as [H| HBM]. {
      subst BM.
      unfold MB'.
      rewrite sizes_of_bmatrix_fold_left. 2: {
        intros l Hl.
        rewrite sizes_of_bmat_zero_like.
        rewrite sizes_of_bmatrix_mul; cycle 1. {
          unfold is_square_bmat.
          rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | flia Hl ].
          apply Hb; [ easy | flia Hl ].
        } {
          unfold is_square_bmat.
          rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hl | easy ].
          apply Hc; [ flia Hl | easy ].
        } {
          rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | flia Hl ].
          rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hl | easy ].
          congruence.
        }
        symmetry.
        apply (sizes_of_bmatrix_at_0_0 fb Hb); [ easy | flia Hl ].
      }
      rewrite sizes_of_bmat_zero_like.
      rewrite Hbs.
      split; [ | easy ].
      rewrite Has in Ha.
      rewrite Hbs in Hb.
      rewrite Hcs in Hc.
...
      assert (H : ∀ j, j < size → is_square_bmat_loop sizes (fa i j)). {
        intros l Hl.
        apply Ha; [ easy | flia Hl ].
      }
      move H before Ha; clear Ha; rename H into Ha.
      assert (H : ∀ i, i < size → is_square_bmat_loop sizes (fb i j)). {
        intros l Hl.
        apply Hb; [ flia Hl | easy ].
      }
      move H before Hb; clear Hb; rename H into Hb.
      clear IHMA (*Ha Hc Hi Hj Hk*).
      clear MB' MC'.
      revert i j Ha Hb Hi Hj.
      induction size; intros. {
        cbn.
        apply is_square_bmat_loop_zero_like.
        apply Hb.
        apply Hb; flia.
      }
      rewrite List_seq_succ_r.
      rewrite fold_left_app; cbn.
      set (MD := (fold_left (λ (acc0 : bmatrix T) (j1 : nat), acc0 + fb k j1 * fc j1 j) (seq 0 size) (bmat_zero_like (fb 0 0)))%BM) in IHsize |-*.
      apply is_square_bmat_loop_add. 2: {
        apply is_square_bmat_loop_mul. {
          apply Hb; [ easy | flia ].
        }
        apply Hc; [ flia | easy ].
      } {
        apply IHsize.
(* crotte *)
...
  apply IHMA with (sizes := sizes); [ flia Hk | easy | ].
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  intros BM HBM.
  unfold is_square_bmat.
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia Hk ].
    split; [ | easy ].
    apply Ha; [ easy | flia Hk ].
  }
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | easy ].
    split; [ | easy ].
    now apply Hb.
  }
  destruct HBM as [H| HBM]; [ subst BM | ]. {
    rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hk | easy ].
    split; [ | easy ].
    apply Hc; [ flia Hk | easy ].
  }
  easy.
}
assert (Hfa00 : is_square_bmat_loop sizes (fa 0 0)). {
...
  apply in_seq in Hk.
  symmetry.
  clear Hcsb.
  destruct size; [ easy | ].
  rewrite List_seq_succ_r.
  do 2 rewrite fold_left_app; cbn.
  rewrite bmat_mul_add_distr_l. 2: {
    exists sizes.
    rewrite <- Has in Ha.
    rewrite <- Hbs in Hb.
    rewrite <- Hcs in Hc.
    intros BM HBM.
    unfold is_square_bmat.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia Hk ].
      split; [ | easy ].
      apply Ha; [ easy | flia Hk ].
    }
    destruct HBM as [H| HBM]. {
      subst BM.
      rewrite sizes_of_bmatrix_fold_left. 2: {
        intros l Hl.
        rewrite sizes_of_bmat_zero_like.
        rewrite sizes_of_bmatrix_mul; cycle 1. {
          unfold is_square_bmat.
          rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | flia Hl ].
          apply Hb; [ easy | flia Hl ].
        } {
          unfold is_square_bmat.
          rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hl | easy ].
          apply Hc; [ flia Hl | easy ].
        } {
          rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | flia Hl ].
          rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hl | easy ].
          congruence.
        }
        symmetry.
        apply (sizes_of_bmatrix_at_0_0 fb Hb); [ easy | flia Hl ].
      }
      rewrite sizes_of_bmat_zero_like.
      rewrite Hbs.
      split; [ | easy ].
...
      rewrite Hbs in Hb.
      clear IHMC Ha Hc Hi Hj Hk.
      induction size. {
        cbn.
        apply is_square_bmat_loop_zero_like.
        apply Hb; flia.
      }
      rewrite List_seq_succ_r.
      rewrite fold_left_app; cbn.
Search (is_square_bmat_loop _ (_ + _)).
...
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | flia Hk ].
      split; [ | easy ].
      apply Hb; [ easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hk | easy ].
      split; [ | easy ].
      apply Hc; [ flia Hk | easy ].
    }
    easy.
  }
...
assert (Hfa00 : is_square_bmat_loop sizes (fa 0 0)). {
...

Theorem is_square_bmat_loop_opp : ∀ (M : bmatrix T) sizes,
  is_square_bmat_loop sizes M → is_square_bmat_loop sizes (- M)%BM.
Proof.
intros * HM.
revert M HM.
induction sizes as [| size]; intros; [ now destruct M | ].
cbn in HM |-*.
destruct M as [x| M]; [ easy | cbn ].
destruct HM as (Hr & Hc & HM).
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
now apply IHsizes, HM.
Qed.

Theorem sizes_of_bmatrix_opp : ∀ (M : bmatrix T),
  sizes_of_bmatrix (- M)%BM = sizes_of_bmatrix M.
Proof.
intros *.
induction M as [x| M IHBM] using bmatrix_ind2; [ easy | cbn ].
destruct (zerop (mat_nrows M)) as [Hrz| Hrz]; [ easy | cbn ].
destruct (zerop (mat_ncols M)) as [Hcz| Hcz]; [ easy | cbn ].
f_equal.
now apply IHBM.
Qed.

Theorem is_square_bmat_opp : ∀ (M : bmatrix T),
  is_square_bmat M → is_square_bmat (- M)%BM.
Proof.
intros * HM.
apply is_square_bmat_loop_opp.
unfold is_square_bmat in HM.
now rewrite sizes_of_bmatrix_opp.
Qed.

Theorem bmat_add_move_l : ∀ MA MB MC,
  compatible_square_bmatrices [MA; MB; MC]
  → (MA + MB)%BM = MC
  → MB = (MC - MA)%BM.
Proof.
intros * Hcsb Hab.
rewrite <- Hab.
unfold bmat_sub.
destruct Hcsb as (sizes & Hcsb).
unfold is_square_bmat in Hcsb.
rewrite bmat_add_add_swap; cycle 1. {
  apply (is_square_bmat_fit_for_add (sizes_of_bmatrix MA)). {
    now apply Hcsb; left.
  } {
    rewrite (proj2 (Hcsb _ (or_introl eq_refl))).
    rewrite <- (proj2 (Hcsb _ (or_intror (or_introl eq_refl)))).
    now apply Hcsb; right; left.
  }
} {
  apply (is_square_bmat_fit_for_add (sizes_of_bmatrix MA)). {
    now apply Hcsb; left.
  } {
    apply is_square_bmat_loop_opp.
    now apply Hcsb; left.
  }
}
rewrite bmat_add_opp_r.
symmetry.
rewrite (bmat_zero_like_eq_compat _ MB); cycle 1. {
  now apply Hcsb; left.
} {
  now apply Hcsb; right; left.
} {
  rewrite (proj2 (Hcsb _ (or_introl eq_refl))).
  rewrite (proj2 (Hcsb _ (or_intror (or_introl eq_refl)))).
  easy.
}
apply bmat_add_0_l.
Qed.

Theorem bmat_zero_like_opp : ∀ MA,
  is_square_bmat MA
  → bmat_zero_like (- MA)%BM = bmat_zero_like MA.
Proof.
intros * Ha.
induction MA as [xa| ma IHMA] using bmatrix_ind2; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
rewrite Tauto.if_same.
apply IHMA; [ easy | easy | ].
cbn in Ha.
destruct (zerop (mat_nrows ma)) as [Hrz| Hrz]; [ flia Hrz Hi | ].
destruct (zerop (mat_ncols ma)) as [Hcz| Hcz]; [ flia Hcz Hj | ].
cbn in Ha.
destruct Ha as (_ & Hrc & Ha).
unfold is_square_bmat.
rewrite Hrc in Hj.
rewrite sizes_of_bmatrix_at_0_0 with (r := mat_nrows ma); try easy.
now apply Ha.
Qed.

Theorem bmat_add_move_0_l : ∀ MA MB,
  compatible_square_bmatrices [MA; MB]
  → (MA + MB)%BM = bmat_zero_like MA
  → MB = (- MA)%BM.
Proof.
intros * Hcsb Hab.
apply bmat_add_move_l in Hab. 2: {
  destruct Hcsb as (sizes & Hcsb).
  exists sizes.
  intros * HBM.
  destruct HBM as [HBM| HBM]; [ now subst BM; apply Hcsb; left | ].
  destruct HBM as [HBM| HBM]; [ now subst BM; apply Hcsb; right; left | ].
  destruct HBM as [HBM| HBM]; [ subst BM | easy ].
  split. {
    now apply is_square_bmat_zero_like, Hcsb; left.
  } {
    rewrite sizes_of_bmat_zero_like.
    now apply Hcsb; left.
  }
}
unfold bmat_sub in Hab.
rewrite <- bmat_zero_like_opp in Hab. 2: {
  destruct Hcsb as (size & Hcsb).
  now apply Hcsb; left.
}
now rewrite bmat_add_0_l in Hab.
Qed.

Theorem bmat_mul_opp_l : ∀ MA MB,
  compatible_square_bmatrices [MA; MB]
  → ((- MA) * MB = - (MA * MB))%BM.
Proof.
intros * Hcsb.
specialize (@bmat_mul_add_distr_r MA (bmat_opp MA) MB) as H1.
destruct Hcsb as (sizes & Hcsb).
specialize (Hcsb _ (or_introl eq_refl)) as Ha.
specialize (Hcsb _ (or_intror (or_introl eq_refl))) as Hb.
destruct Ha as (Ha, Has).
destruct Hb as (Hb, Hbs).
generalize Ha; intros Hao.
apply is_square_bmat_opp in Hao.
generalize Has; intros Haso.
rewrite <- sizes_of_bmatrix_opp in Haso.
assert (H : compatible_square_bmatrices [MA; (- MA)%BM; MB]). {
  exists sizes.
  intros BM HBM.
  destruct HBM as [HBM| HBM]; [ now subst BM | ].
  destruct HBM as [HBM| HBM]; [ now subst BM | ].
  destruct HBM as [HBM| HBM]; [ now subst BM | easy ].
}
specialize (H1 H); clear H.
rewrite bmat_add_opp_r in H1.
assert (Hss : sizes_of_bmatrix MA = sizes_of_bmatrix MB). {
  now rewrite Has, Hbs.
}
assert (Hab : bmat_zero_like MA = bmat_zero_like MB). {
  now rewrite (bmat_zero_like_eq_compat _ MB).
}
rewrite Hab in H1.
rewrite bmat_mul_0_l in H1; [ | easy ].
symmetry in H1.
rewrite <- Hab in H1.
rewrite (bmat_zero_like_eq_compat _ MB) in H1; [ | easy | easy | easy ].
rewrite <- Hab in H1.
rewrite <- (bmat_zero_like_mul _ MB) in H1; [ | easy | easy | easy ].
apply bmat_add_move_0_l in H1; [ easy | ].
exists sizes.
intros BM HBM.
destruct HBM as [HBM| HBM]; [ subst BM | ]. {
  split. {
    now apply is_square_bmat_mul.
  } {
    now rewrite sizes_of_bmatrix_mul.
  }
}
destruct HBM as [HBM| HBM]; [ subst BM | easy ].
split. {
  apply is_square_bmat_mul; [ easy | easy | ].
  now rewrite Haso, Hbs.
} {
  rewrite sizes_of_bmatrix_mul; [ easy | easy | easy | ].
  now rewrite sizes_of_bmatrix_opp.
}
Qed.

Theorem bmat_mul_opp_r : ∀ MA MB,
  compatible_square_bmatrices [MA; MB]
  → (MA * (- MB) = - (MA * MB))%BM.
Proof.
intros * Hcsb.
specialize (@bmat_mul_add_distr_l MA MB (bmat_opp MB)) as H1.
destruct Hcsb as (sizes & Hcsb).
specialize (Hcsb _ (or_introl eq_refl)) as Ha.
specialize (Hcsb _ (or_intror (or_introl eq_refl))) as Hb.
destruct Ha as (Ha, Has).
destruct Hb as (Hb, Hbs).
generalize Hb; intros Hbo.
apply is_square_bmat_opp in Hbo.
generalize Hbs; intros Hbso.
rewrite <- sizes_of_bmatrix_opp in Hbso.
assert (H : compatible_square_bmatrices [MA; MB; (- MB)%BM]). {
  exists sizes.
  intros BM HBM.
  destruct HBM as [HBM| HBM]; [ now subst BM | ].
  destruct HBM as [HBM| HBM]; [ now subst BM | ].
  destruct HBM as [HBM| HBM]; [ now subst BM | easy ].
}
specialize (H1 H); clear H.
rewrite bmat_add_opp_r in H1.
assert (Hss : sizes_of_bmatrix MA = sizes_of_bmatrix MB). {
  now rewrite Has, Hbs.
}
assert (Hab : bmat_zero_like MA = bmat_zero_like MB). {
  now rewrite (bmat_zero_like_eq_compat _ MB).
}
rewrite <- Hab in H1.
rewrite bmat_mul_0_r in H1; [ | easy ].
symmetry in H1.
rewrite (bmat_zero_like_eq_compat _ MB) in H1; [ | easy | easy | easy ].
rewrite <- Hab in H1.
rewrite <- (bmat_zero_like_mul _ MB) in H1; [ | easy | easy | easy ].
apply bmat_add_move_0_l in H1; [ easy | ].
exists sizes.
intros BM HBM.
destruct HBM as [HBM| HBM]; [ subst BM | ]. {
  split. {
    now apply is_square_bmat_mul.
  } {
    now rewrite sizes_of_bmatrix_mul.
  }
}
destruct HBM as [HBM| HBM]; [ subst BM | easy ].
split. {
  apply is_square_bmat_mul; [ easy | easy | ].
  congruence.
} {
  rewrite sizes_of_bmatrix_mul; [ easy | easy | easy | ].
  now rewrite sizes_of_bmatrix_opp.
}
Qed.

Theorem bmat_mul_opp_opp : ∀ MA MB,
  compatible_square_bmatrices [MA; MB]
  → (- MA * - MB = MA * MB)%BM.
Proof.
intros * Hab.
rewrite bmat_mul_opp_l. 2: {
  destruct Hab as (sizes & Hab).
  exists sizes.
  intros BM HBM.
  destruct HBM as [HBM| HBM]; [ now subst BM; apply Hab; left | ].
  destruct HBM as [HBM| HBM]; [ subst BM | easy ].
  split. {
    now apply is_square_bmat_opp, Hab; right; left.
  } {
    now rewrite sizes_of_bmatrix_opp; apply Hab; right; left.
  }
}
rewrite bmat_mul_opp_r; [ | easy ].
now rewrite bmat_opp_involutive.
Qed.

Theorem bmat_mul_sqr_opp : ∀ M,
  is_square_bmat M
  → (- M * - M = M * M)%BM.
Proof.
intros * HM.
apply bmat_mul_opp_opp.
exists (sizes_of_bmatrix M).
intros BM HBM.
replace BM with M; [ easy | ].
destruct HBM as [| HBM]; [ easy | now destruct HBM ].
Qed.

Theorem bmat_fit_for_add_Z_2_pow_bmat_nat_mul_l :
  ∀ n,
  bmat_fit_for_add (Z_2_pow n) (bmat_nat_mul_l n (Z_2_pow n)).
Proof.
intros.
induction n; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
rewrite bmat_nat_mul_l_succ.
destruct i; cbn. {
  destruct j; cbn. {
    symmetry.
    now apply bmat_fit_for_add_add_l; symmetry.
  }
  destruct j; [ | flia Hj ].
  symmetry.
  now apply bmat_fit_for_add_add_l; symmetry.
}
destruct i; [ | flia Hi ].
destruct j; cbn. {
  symmetry.
  now apply bmat_fit_for_add_add_l; symmetry.
}
destruct j; [ | flia Hj ]. {
  symmetry.
  now apply bmat_fit_for_add_add_l; symmetry.
}
Qed.

Theorem bmat_zero_like_IZ_eq_Z :
  ∀ u n, bmat_zero_like (IZ_2_pow u n) = Z_2_pow n.
Proof.
intros.
revert u.
induction n; intros; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
rewrite Tauto.if_same.
rewrite fold_bmat_zero_like.
destruct i; cbn. {
  destruct j; cbn; [ easy | ].
  destruct j; cbn; [ easy | flia Hj ].
}
destruct i; [ cbn | flia Hi ].
destruct j; cbn; [ easy | ].
destruct j; [ easy | flia Hj ].
Qed.

(* block matrix trace *)

Fixpoint Tr (BM : bmatrix T) :=
  match BM with
  | BM_1 x => x
  | BM_M M => (Σ (i = 0, mat_nrows M - 1), Tr (mat_el M i i))%Srng
  end.

(*
End in_ring.
Require Import ZArith.
Compute (let ro := Z_ring_op in Tr (I_2_pow 3)).
Compute (let ro := Z_ring_op in Tr (I_2_pow 3)).
Compute (let ro := Z_ring_op in Tr (I_2_pow 4)).
Compute (let ro := Z_ring_op in Tr (A 3)).
*)

Theorem Tr_opp : ∀ BM,
  is_square_bmat BM
  → Tr (- BM)%BM = (- Tr BM)%Rng.
Proof.
intros * HBM.
induction BM as [x| M IHBM] using bmatrix_ind2; [ easy | ].
cbn - [ seq sub ].
cbn in HBM.
destruct (zerop (mat_nrows M)) as [Hrz| Hrz]; [ easy | ].
destruct (zerop (mat_ncols M)) as [Hcz| Hcz]; [ easy | ].
cbn in HBM.
rewrite rng_opp_summation; [ cbn | easy | easy ].
rewrite IHBM; [ | easy | easy | now apply HBM ].
rewrite srng_add_0_l.
apply List_fold_left_ext_in.
intros i x Hi.
apply in_seq in Hi.
f_equal.
destruct HBM as (_ & Hcr & HBM).
apply IHBM; [ flia Hi | flia Hi Hcr | ].
unfold is_square_bmat.
rewrite sizes_of_bmatrix_at_0_0 with (r := mat_nrows M);
  [ | easy | flia Hi | flia Hi ].
apply HBM; flia Hi.
Qed.

Fixpoint bmat_el (BM : bmatrix T) i j :=
  match BM with
  | BM_1 x => x
  | BM_M MBM =>
      match sizes_of_bmatrix BM with
      | s :: sl =>
          let n := (Π (k = 1, length sl), nth (k - 1) sl 0)%Srng in
          bmat_el (mat_el MBM (i / n) (j / n)) (i mod n) (j mod n)
      | [] => 0%Srng
      end
  end.

Arguments bmat_el BM%BM (i j)%nat.

Definition sqr_bmat_size (BM : bmatrix T) :=
  let sl := sizes_of_bmatrix BM in
  (Π (i = 1, length sl), nth (i - 1) sl 0)%Srng.

Arguments sqr_bmat_size BM%BM.

Theorem product_bmatrix_sizes_ne_0 : ∀ sizes A,
  sizes = sizes_of_bmatrix A
  → (Π (k = 1, length sizes), nth (k - 1) sizes 0%Rng)%Srng ≠ 0.
Proof.
intros * Hsizes Hlen.
revert A Hsizes.
induction sizes as [| size]; intros; [ easy | ].
cbn - [ iter_seq srng_mul srng_one nth ] in Hlen.
rewrite iter_succ_succ in Hlen.
rewrite srng_product_split_first in Hlen; [ | | | flia ]; cycle 1. {
  apply nat_semiring_prop.
} {
  apply nat_sring_comm_prop.
}
apply Nat.eq_mul_0 in Hlen.
destruct Hlen as [Hlen| Hlen]. {
  specialize (no_zero_bmat_size A) as H1.
  now apply H1; rewrite <- Hsizes; left.
}
destruct A as [xa| MA]; [ easy | ].
apply IHsizes with (A := mat_el MA 0 0). 2: {
  cbn in Hsizes.
  destruct (zerop (mat_nrows MA)) as [H| Hrz]; [ easy | ].
  destruct (zerop (mat_ncols MA)) as [H| Hcz]; [ easy | ].
  cbn in Hsizes.
  now injection Hsizes.
}
rewrite <- Hlen at 2.
apply srng_product_eq_compat. {
  apply nat_semiring_prop.
} {
  apply nat_sring_comm_prop.
}
intros i Hi.
destruct i; [ flia Hi | ].
now do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
Qed.

Theorem bmat_el_add : ∀ A B,
  compatible_square_bmatrices [A; B]
  → ∀ i j, i < sqr_bmat_size A → j < sqr_bmat_size A
  → bmat_el (A + B) i j = (bmat_el A i j + bmat_el B i j)%Srng.
Proof.
intros * Hab * Hi Hj.
destruct Hab as (sz & Hab).
specialize (Hab A (or_introl eq_refl)) as Hsqa.
specialize (Hab B (or_intror (or_introl eq_refl))) as Hsqb.
destruct Hsqa as (Hsqa, Hsma).
destruct Hsqb as (Hsqb, Hsmb).
clear Hab.
revert sz B Hsqb Hsma Hsmb i j Hi Hj.
induction A as [xa| MA IHA] using bmatrix_ind2; intros. {
  cbn in Hsma; subst sz.
  destruct B as [xb| MB]; [ easy | ].
  cbn in Hsqb, Hsmb.
  destruct (zerop (mat_nrows MB)) as [Hrbz| Hrbz]; [ easy | ].
  now destruct (zerop (mat_ncols MB)).
}
generalize Hsqa; intros Hsqa'.
generalize Hsqb; intros Hsqb'.
cbn in Hsma, Hsqa.
destruct B as [xb| MB]. {
  cbn in Hsqa, Hsmb.
  move Hsmb after Hsma; subst sz.
  destruct (zerop (mat_nrows MA)) as [Hraz| Hraz]; [ easy | ].
  now destruct (zerop (mat_ncols MA)).
}
cbn in Hsqb, Hsmb.
unfold sqr_bmat_size in Hi, Hj.
cbn - [ iter_seq srng_mul srng_one ] in Hi, Hj |-*.
destruct (zerop (mat_nrows MA)) as [Hraz| Hraz]; [ easy | ].
destruct (zerop (mat_ncols MA)) as [Hcaz| Hcaz]; [ easy | ].
destruct (zerop (mat_nrows MB)) as [Hrbz| Hrbz]; [ easy | ].
destruct (zerop (mat_ncols MB)) as [Hcbz| Hcbz]; [ easy | ].
cbn in Hsqa, Hsqb, Hsma, Hsmb.
cbn - [ iter_seq srng_mul srng_one nth ] in Hi, Hj |-*.
rewrite <- Hsma in Hsmb.
injection Hsmb; clear Hsmb; intros Hsab Hrab.
remember (mat_nrows MA) as n eqn:Hran; symmetry in Hran.
destruct Hsqa as (_ & Hcan & Hqsa).
move Hcan before Hran.
rename Hrab into Hrbn.
move Hrbn before Hcan; move MB before MA.
destruct Hsqb as (_ & Hcbn & Hqsb).
rewrite Hrbn in Hcbn.
move Hcbn before Hrbn.
clear Hcaz Hrbz Hcbz.
rewrite sizes_of_bmatrix_add; [ | easy ].
rewrite Hsab.
remember (sizes_of_bmatrix (mat_el MA 0 0)) as sizes eqn:Hsizes.
remember (Π (k = 1, length sizes), nth (k - 1) sizes 0)%Srng as len eqn:Hlen.
assert (Hilen : i / len < n). {
  apply Nat.div_lt_upper_bound. {
    rewrite Hlen.
    now apply (product_bmatrix_sizes_ne_0 (mat_el MA 0 0)).
  } {
    rewrite iter_succ_succ in Hi.
    rewrite srng_product_split_first in Hi; [ | | | flia ]; cycle 1. {
      apply nat_semiring_prop.
    } {
      apply nat_sring_comm_prop.
    }
    remember (nth (_ - _) _ _) as x in Hi; cbn in Heqx; subst x.
    rewrite Nat.mul_comm in Hi.
    erewrite srng_product_eq_compat in Hi; cycle 1. {
      apply nat_semiring_prop.
    } {
      apply nat_sring_comm_prop.
    } {
      intros k Hk.
      rewrite Nat.sub_succ_l; [ | easy ].
      now cbn.
    }
    cbn - [ iter_seq srng_mul srng_one ] in Hi, Hlen.
    now rewrite <- Hlen in Hi.
  }
}
assert (Hjlen : j / len < n). {
  apply Nat.div_lt_upper_bound. {
    rewrite Hlen.
    now apply (product_bmatrix_sizes_ne_0 (mat_el MA 0 0)).
  } {
    rewrite iter_succ_succ in Hj.
    rewrite srng_product_split_first in Hj; [ | | | flia ]; cycle 1. {
      apply nat_semiring_prop.
    } {
      apply nat_sring_comm_prop.
    }
    remember (nth (_ - _) _ _) as x in Hj; cbn in Heqx; subst x.
    rewrite Nat.mul_comm in Hj.
    erewrite srng_product_eq_compat in Hj; cycle 1. {
      apply nat_semiring_prop.
    } {
      apply nat_sring_comm_prop.
    } {
      intros k Hk.
      rewrite Nat.sub_succ_l; [ | easy ].
      now cbn.
    }
    cbn - [ iter_seq srng_mul srng_one ] in Hj, Hlen.
    now rewrite <- Hlen in Hj.
  }
}
assert (Hsa : sizes_of_bmatrix (mat_el MA (i / len) (j / len)) = sizes). {
  rewrite sizes_of_bmatrix_mat_el; [ | easy | | ]; cycle 1. {
    now rewrite Hran.
  } {
    now rewrite Hcan.
  }
  now rewrite <- Hsizes.
}
assert (Hsb : sizes_of_bmatrix (mat_el MB (i / len) (j / len)) = sizes). {
  rewrite sizes_of_bmatrix_mat_el; [ easy | easy | | ]. {
    now rewrite Hrbn.
  } {
    now rewrite Hcbn.
  }
}
apply IHA with (sz := sizes); [ easy | | | | easy | easy | | ]. {
  now rewrite Hcan.
} {
  unfold is_square_bmat.
  rewrite Hsa.
  now apply Hqsa.
} {
  unfold is_square_bmat.
  rewrite Hsb.
  rewrite Hsab in Hqsb.
  now apply Hqsb; rewrite Hrbn.
} {
  unfold sqr_bmat_size.
  rewrite Hsa, <- Hlen.
  apply Nat.mod_upper_bound.
  rewrite Hlen.
  now apply (product_bmatrix_sizes_ne_0 (mat_el MA 0 0)).
} {
  unfold sqr_bmat_size.
  rewrite Hsa, <- Hlen.
  apply Nat.mod_upper_bound.
  rewrite Hlen.
  now apply (product_bmatrix_sizes_ne_0 (mat_el MA 0 0)).
}
Qed.

(*
End in_ring.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.

Arguments bmat_el {T so} BM%BM (i j)%nat.
*)

Definition square_bmatrix M (HM : is_square_bmat M) :=
  {A : bmatrix T | compatible_square_bmatrices_bool [M; A] = true}.

Theorem square_bmatrix_eq M (HM : is_square_bmat M) :
  ∀ (A B : square_bmatrix M HM),
  proj1_sig A = proj1_sig B → A = B.
Proof.
intros * Hab.
destruct A as (A, Ha).
destruct B as (B, Hb).
cbn in Hab.
subst A.
apply eq_exist_uncurried.
exists eq_refl.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem comp_squ_bmat_with_zero_like : ∀ M (HM : is_square_bmat M),
  compatible_square_bmatrices [M; bmat_zero_like M].
Proof.
intros.
exists (sizes_of_bmatrix M).
intros * HBM.
destruct HBM as [HBM| HBM]; [ now subst BM | ].
destruct HBM as [HBM| HBM]; [ | easy ].
subst BM.
split. {
  now apply is_square_bmat_zero_like.
} {
  apply sizes_of_bmat_zero_like.
}
Qed.

Theorem comp_squ_bmat_with_one_like : ∀ M (HM : is_square_bmat M),
  compatible_square_bmatrices [M; bmat_one_like M].
Proof.
intros.
exists (sizes_of_bmatrix M).
intros * HBM.
destruct HBM as [HBM| HBM]; [ now subst BM | ].
destruct HBM as [HBM| HBM]; [ | easy ].
subst BM.
split. {
  now apply is_square_bmat_one_like.
} {
  apply sizes_of_bmat_one_like.
}
Qed.

Theorem comp_squ_bmat_with_add : ∀ M (HM : is_square_bmat M) MA MB,
  compatible_square_bmatrices [M; MA]
  → compatible_square_bmatrices [M; MB]
  → compatible_square_bmatrices [M; (MA + MB)%BM].
Proof.
intros * HM * Hma Hmb.
destruct Hma as (sza & Hma).
destruct Hmb as (szb & Hmb).
exists (sizes_of_bmatrix M).
intros M' Hbm.
destruct Hbm as [Hbm| Hbm]; [ now subst M' | ].
destruct Hbm as [Hbm| Hbm]; [ | easy ].
subst M'.
split. {
  apply is_square_bmat_add. {
    now apply Hma; right; left.
  } {
    now apply Hmb; right; left.
  }
  transitivity (sizes_of_bmatrix M). {
    rewrite (proj2 (Hma _ (or_intror (or_introl eq_refl)))).
    now symmetry; apply Hma; left.
  } {
    rewrite (proj2 (Hmb _ (or_intror (or_introl eq_refl)))).
    now apply Hmb; left.
  }
} {
  rewrite sizes_of_bmatrix_add. {
    rewrite (proj2 (Hma _ (or_intror (or_introl eq_refl)))).
    now symmetry; apply Hma; left.
  } {
    transitivity (sizes_of_bmatrix M). {
      rewrite (proj2 (Hma _ (or_intror (or_introl eq_refl)))).
      now symmetry; apply Hma; left.
    } {
      rewrite (proj2 (Hmb _ (or_intror (or_introl eq_refl)))).
      now apply Hmb; left.
    }
  }
}
Qed.

Theorem comp_squ_bmat_with_mul : ∀ M (HM : is_square_bmat M) MA MB,
  compatible_square_bmatrices [M; MA]
  → compatible_square_bmatrices [M; MB]
  → compatible_square_bmatrices [M; (MA * MB)%BM].
Proof.
intros * HM * Hma Hmb.
destruct Hma as (sza & Hma).
destruct Hmb as (szb & Hmb).
exists (sizes_of_bmatrix M).
intros M' Hbm.
destruct Hbm as [Hbm| Hbm]; [ now subst M' | ].
destruct Hbm as [Hbm| Hbm]; [ | easy ].
subst M'.
split. {
(**)
  apply is_square_bmat_mul. {
    now apply Hma; right; left.
  } {
    now apply Hmb; right; left.
  }
  transitivity (sizes_of_bmatrix M). {
    rewrite (proj2 (Hma _ (or_intror (or_introl eq_refl)))).
    now symmetry; apply Hma; left.
  } {
    rewrite (proj2 (Hmb _ (or_intror (or_introl eq_refl)))).
    now apply Hmb; left.
  }
} {
  rewrite sizes_of_bmatrix_mul. {
    rewrite (proj2 (Hma _ (or_intror (or_introl eq_refl)))).
    now symmetry; apply Hma; left.
  } {
    now apply Hma; right; left.
  } {
    now apply Hmb; right; left.
  } {
    transitivity (sizes_of_bmatrix M). {
      rewrite (proj2 (Hma _ (or_intror (or_introl eq_refl)))).
      now symmetry; apply Hma; left.
    } {
      rewrite (proj2 (Hmb _ (or_intror (or_introl eq_refl)))).
      now apply Hmb; left.
    }
  }
}
Qed.

Definition squ_bmat_zero M HM : square_bmatrix M HM.
Proof.
exists (bmat_zero_like M).
apply compatible_square_bmatrices_bool_iff.
now apply comp_squ_bmat_with_zero_like.
Defined.

Definition squ_bmat_one M HM : square_bmatrix M HM.
Proof.
exists (bmat_one_like M).
apply compatible_square_bmatrices_bool_iff.
now apply comp_squ_bmat_with_one_like.
Defined.

Definition squ_bmat_add M HM (MA MB : square_bmatrix M HM) :
  square_bmatrix M HM.
Proof.
destruct MA as (MA & Hma).
destruct MB as (MB & Hmb).
exists (MA + MB)%BM.
apply compatible_square_bmatrices_bool_iff in Hma.
apply compatible_square_bmatrices_bool_iff in Hmb.
apply compatible_square_bmatrices_bool_iff.
now apply comp_squ_bmat_with_add.
Defined.

Definition squ_bmat_mul M HM (MA MB : square_bmatrix M HM) :
  square_bmatrix M HM.
Proof.
destruct MA as (MA & Hma).
destruct MB as (MB & Hmb).
exists (MA * MB)%BM.
apply compatible_square_bmatrices_bool_iff in Hma.
apply compatible_square_bmatrices_bool_iff in Hmb.
apply compatible_square_bmatrices_bool_iff.
now apply comp_squ_bmat_with_mul.
Defined.

End in_ring.

Module square_bmatrix_Notations.

Declare Scope SBM_scope.
Delimit Scope SBM_scope with SBM.

Arguments square_bmatrix {T so} M%BM HM.
Arguments squ_bmat_zero {T so M%BM HM}.
Arguments squ_bmat_one {T so M%M HM}.
Arguments squ_bmat_add {T so M%M HM} MA%SBM MB%SBM.
Arguments squ_bmat_mul {T so M%M HM} MA%SBM MB%SBM.
Arguments compatible_square_bmatrices_bool {T so} BML%SBM.

Notation "0" := (squ_bmat_zero) : SBM_scope.
Notation "1" := (squ_bmat_one) : SBM_scope.
Notation "A + B" := (squ_bmat_add A B) : SBM_scope.
Notation "A * B" := (squ_bmat_mul A B) : SBM_scope.

End square_bmatrix_Notations.

Import square_bmatrix_Notations.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.

Definition squ_bmat_semiring_op_for M HM : semiring_op (square_bmatrix M HM) :=
  {| srng_zero := 0%SBM;
     srng_one := 1%SBM;
     srng_add := squ_bmat_add;
     srng_mul := squ_bmat_mul |}.

Canonical Structure squ_bmat_semiring_op_for.

Theorem comp_squ_bmat_fit_for_add : ∀ M A B,
  compatible_square_bmatrices_bool [M; A] = true
  → compatible_square_bmatrices_bool [M; B] = true
  → bmat_fit_for_add A B.
Proof.
intros * HA HB.
apply compatible_square_bmatrices_bool_iff in HA.
apply compatible_square_bmatrices_bool_iff in HB.
destruct HA as (sza, Ha).
destruct HB as (szb, Hb).
assert (H : szb = sza). {
  specialize (Ha _ (or_introl eq_refl)).
  specialize (Hb _ (or_introl eq_refl)).
  now rewrite <- (proj2 Ha), (proj2 Hb).
}
subst szb.
unfold is_square_bmat in Ha, Hb.
apply (is_square_bmat_fit_for_add sza). {
  specialize (Ha _ (or_intror (or_introl eq_refl))) as H1.
  now rewrite (proj2 H1) in H1.
} {
  specialize (Hb _ (or_intror (or_introl eq_refl))) as H1.
  now rewrite (proj2 H1) in H1.
}
Qed.

Theorem squ_bmat_add_comm : ∀ M HM (a b : square_bmatrix M HM),
  (a + b)%SBM = (b + a)%SBM.
Proof.
intros.
destruct a as (A, HA).
destruct b as (B, HB).
apply square_bmatrix_eq; cbn.
apply bmat_add_comm; [ easy | ].
now apply (comp_squ_bmat_fit_for_add M).
Qed.

Theorem squ_bmat_add_assoc : ∀ M HM (a b c : square_bmatrix M HM),
  (a + (b + c))%SBM = ((a + b) + c)%SBM.
Proof.
intros M HM (A, Ha) (B, Hb) (C, Hc).
apply square_bmatrix_eq; cbn.
now apply bmat_add_assoc; [ easy | | ]; apply (comp_squ_bmat_fit_for_add M).
Qed.

Theorem bmat_zero_like_squ_bmat : ∀ M HM (A : square_bmatrix M HM),
  bmat_zero_like M = bmat_zero_like (proj1_sig A).
Proof.
intros.
destruct A as (A, Ha); cbn.
apply compatible_square_bmatrices_bool_iff in Ha.
destruct Ha as (sz, Ha).
specialize (Ha _ (or_introl eq_refl)) as H1.
specialize (Ha _ (or_intror (or_introl eq_refl))) as H2.
apply bmat_zero_like_eq_compat; [ easy | easy | ].
destruct H1, H2; congruence.
Qed.

Theorem squ_bmat_add_0_l : ∀ M HM (A : square_bmatrix M HM),
  (0 + A = A)%SBM.
Proof.
intros M HM A.
specialize (bmat_zero_like_squ_bmat A) as H1.
destruct A as (A, Ha); cbn in H1.
apply square_bmatrix_eq; cbn.
rewrite H1.
now apply bmat_add_0_l.
Qed.

Theorem squ_bmat_mul_assoc : ∀ M HM (A B C : square_bmatrix M HM),
  (A * (B * C))%SBM = ((A * B) * C)%SBM.
Proof.
intros M HM (A, Ha) (B, Hb) (C, Hc).
apply square_bmatrix_eq; cbn.
Search (_ * (_ * _))%BM.
Abort. (* à faire quand bmat_mul_assoc sera fait *)

(*
Definition squ_bmat_semiring_prop_for M HM :
  semiring_prop (square_bmatrix M HM) :=
  {| srng_add_comm := @squ_bmat_add_comm M HM;
     srng_add_assoc := @squ_bmat_add_assoc M HM;
     srng_add_0_l := @squ_bmat_add_0_l M HM;
     srng_mul_assoc := @squ_bmat_mul_assoc M HM |}.
... à compléter quand il y aura bien tous les théorèmes
*)

...

Theorem bmat_el_summation : ∀ b e i j f
  (bso := squ_bmat_semiring_op_for (f b)),
  b ≤ e
  → is_square_bmat (f b)
  → bmat_el (Σ (k = b, e), f k)%Srng i j =
      (Σ (k = b, e), bmat_el (f k) i j)%Srng.
Proof.
intros * Hbe Hsf.
unfold iter_seq.
remember (S e - b) as len eqn:Hlen.
assert (H : 0 < len) by flia Hbe Hlen.
clear e Hbe Hlen; rename H into Hlen.
revert b i j bso Hsf.
induction len; intros; [ easy | clear Hlen ].
destruct (Nat.eq_dec len 0) as [Hlz| Hlz]. {
  subst len; cbn.
  rewrite srng_add_0_l.
  now rewrite bmat_add_0_l.
}
rewrite List_seq_succ_r.
do 2 rewrite fold_left_app.
cbn; rewrite bmat_el_add. 2: {
  unfold compatible_square_bmatrices.
  split. {
    intros BM HBM.
    destruct HBM as [HBM| HBM]. {
      subst BM.
      clear IHlen.
      replace (@bmat_add T so) with (@srng_add _ bso) by easy.
Check @fold_left_add_fun_from_0.
Check @fold_left_srng_add_fun_from_0.
      rewrite fold_left_srng_add_fun_from_0.
...
Set Printing All.
(*
      replace len with (S (b + len - 1) - b) by flia Hlz.
      rewrite fold_iter_seq.
      replace (@bmat_add T so) with (@srng_add _ bso) by easy.
      replace (@bmat_zero_like T so (f b)) with (@srng_zero _ bso) by easy.
*)
      clear IHlen.
      induction len; intros. {
        cbn - [ is_square_bmat ].
        destruct b. {
          cbn.
        admit.
      }
...
      induction len; [ easy | clear Hlz ].
      destruct len. {
        cbn - [ is_square_bmat ].
        apply is_square_bmat_add; [ | easy | ]. {
          now apply is_square_bmat_zero_like.
        }
        apply sizes_of_bmat_zero_like.
      }
      rewrite List_seq_succ_r.
      rewrite fold_left_app.
      cbn - [ is_square_bmat ].
      apply is_square_bmat_add; cycle 1. {
        admit.
      } {
...
        rewrite fold_left_srng_add_fun_from_0.
        rewrite List_fold_left_f
        rewrite sizes_of_bmatrix_add.
...
      rewrite <- seq_shift.
Search (fold_left _ _ 0%Srng).
rewrite fold_left_srng_add_fun_from_0.
      rewrite List_fold_left_f
..
  exists (sizes_of_bmatrix

cbn.


remember (fold_left (λ c k, c + f k) (seq b len) (bmat_zero_like (f b)))%Rng as A.
remember (f (b + len)) as B eqn:HB.
About bmat_el_add.
specialize (bmat_el_add A B) as H1.
cbn in H1.
clear - H1.
Set Printing All.
...
rewrite H1.
...
*)

Definition mat_of_sqr_bmat (BM : bmatrix T) : matrix T :=
  mk_mat (bmat_el BM) (sqr_bmat_size BM) (sqr_bmat_size BM).

Arguments mat_of_sqr_bmat BM%BM.

Theorem sqr_bmat_size_mul : ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → sqr_bmat_size (BMA * BMB) = sqr_bmat_size BMA.
Proof.
intros * Ha Hb Hab.
unfold sqr_bmat_size.
now rewrite sizes_of_bmatrix_mul.
Qed.

Theorem mat_of_sqr_bmat_mul : ∀ A B,
  is_square_bmat A
  → is_square_bmat B
  → sizes_of_bmatrix A = sizes_of_bmatrix B
  → mat_of_sqr_bmat (A * B) = (mat_of_sqr_bmat A * mat_of_sqr_bmat B)%M.
Proof.
intros * Ha Hb Hab.
apply matrix_eq. {
  cbn - [ iter_seq ].
  unfold sqr_bmat_size.
  now rewrite sizes_of_bmatrix_mul.
} {
  cbn - [ iter_seq ].
  unfold sqr_bmat_size.
  rewrite sizes_of_bmatrix_mul; [ | easy | easy | easy ].
  now rewrite Hab.
}
cbn - [ iter_seq ].
intros i j Hi Hj.
rewrite sqr_bmat_size_mul in Hi; [ | easy | easy | easy ].
unfold sqr_bmat_size.
remember (sizes_of_bmatrix A) as sz eqn:Has.
rename Hab into Hbs.
(**)
symmetry in Has, Hbs.
revert i j A B Ha Hb Has Hbs Hi Hj.
induction sz as [| size]; intros. {
  destruct A as [xa| MA]. {
    clear Ha Has.
    destruct B as [xb| MB]. {
      cbn; symmetry.
      apply srng_add_0_l.
    }
    cbn in Hb, Hbs.
    destruct (zerop (mat_nrows MB)) as [Hbrz| Hbrz]; [ easy | ].
    now destruct (zerop (mat_ncols MB)).
  }
  cbn in Ha, Has.
  destruct (zerop (mat_nrows MA)) as [Harz| Harz]; [ easy | ].
  now destruct (zerop (mat_ncols MA)).
}
remember (Π (i0 = 1, length (size :: sz)), nth (i0 - 1) (size :: sz) 0)%Srng
  as len eqn:Hlen.
rewrite srng_product_split_first in Hlen; cycle 1. {
  apply nat_semiring_prop.
} {
  cbn; flia.
}
rewrite Nat.sub_diag in Hlen.
unfold nth in Hlen at 1.
erewrite srng_product_eq_compat in Hlen; [ | apply nat_semiring_prop | ]. 2: {
  intros k Hk.
  replace (k - 1) with (S (k - 2)) by flia Hk.
  cbn; easy.
}
rewrite List_length_cons in Hlen.
rewrite iter_succ_succ in Hlen.
erewrite srng_product_eq_compat in Hlen; [ | apply nat_semiring_prop | ]. 2: {
  intros k Hk.
  now rewrite Nat.sub_succ.
}
cbn - [ iter_seq nth srng_mul srng_one ] in Hlen.
destruct size. {
  specialize (no_zero_bmat_size A) as H1.
  rewrite Has in H1.
  now exfalso; apply H1; left.
}
destruct A as [xa| MA]; [ easy | ].
destruct B as [xb| MB]; [ easy | ].
cbn - [ iter_seq srng_mul srng_one ].
cbn - [ iter_seq ] in Ha, Hb, Has, Hbs.
unfold sqr_bmat_size in Hi, Hj.
cbn - [ iter_seq srng_mul srng_one ] in Hi, Hj.
destruct (zerop (mat_nrows MA)) as [Hraz| Hraz]; [ easy | ].
destruct (zerop (mat_ncols MA)) as [Hcaz| Hcaz]; [ easy | ].
destruct (zerop (mat_nrows MB)) as [Hrbz| Hrbz]; [ easy | ].
destruct (zerop (mat_ncols MB)) as [Hcbz| Hcbz]; [ easy | ].
cbn in Ha, Hb, Has, Hbs.
cbn - [ iter_seq srng_mul srng_one ] in Hi, Hj.
destruct Ha as (_ & Hcra & Ha).
destruct Hb as (_ & Hcrb & Hb).
move Hrbz before Hraz; move Hcbz before Hcaz.
move Hcrb before Hcra; move Hb before Ha.
injection Has; clear Has; intros Has Hra.
injection Hbs; clear Hbs; intros Hbs Hrb.
move Hbs before Has.
cbn - [ iter_seq srng_mul srng_one ].
rewrite Has, Hbs.
(**)
rewrite Has in Ha, Hi.
rewrite Hbs in Hb, Hj.
assert
  (Hsza : ∀ i j, i < mat_nrows MA → j < mat_ncols MA →
   sizes_of_bmatrix (mat_el MA i j) = sizes_of_bmatrix (mat_el MA 0 0)). {
  intros i' j' Hi' Hj'.
  apply sizes_of_bmatrix_mat_el; [ | easy | easy ].
  cbn.
  destruct (zerop (mat_nrows MA)) as [H| H]; [ flia H Hraz | ].
  cbn; clear H.
  destruct (zerop (mat_ncols MA)) as [H| H]; [ flia H Hcaz | ].
  cbn; clear H.
  split; [ easy | ].
  split; [ easy | ].
  intros i'' j'' Hi'' Hj''.
  rewrite Has.
  now apply Ha.
}
assert
  (Hszb : ∀ i j, i < mat_nrows MB → j < mat_ncols MB →
   sizes_of_bmatrix (mat_el MB i j) = sizes_of_bmatrix (mat_el MB 0 0)). {
  intros i' j' Hi' Hj'.
  apply sizes_of_bmatrix_mat_el; [ | easy | easy ].
  cbn.
  destruct (zerop (mat_nrows MB)) as [H| H]; [ flia H Hrbz | ].
  cbn; clear H.
  destruct (zerop (mat_ncols MB)) as [H| H]; [ flia H Hcbz | ].
  cbn; clear H.
  split; [ easy | ].
  split; [ easy | ].
  intros i'' j'' Hi'' Hj''.
  rewrite Hbs.
  now apply Hb.
}
rewrite sizes_of_bmatrix_fold_left. 2: {
  intros k Hk.
  rewrite sizes_of_bmat_zero_like.
  symmetry.
  rewrite sizes_of_bmatrix_mul; cycle 1. {
    unfold is_square_bmat.
    rewrite Hsza; [ | easy | easy ].
    rewrite Has.
    apply Ha; [ easy | ].
    now rewrite <- Hcra.
  } {
    unfold is_square_bmat.
    rewrite Hszb; [ | now rewrite Hrb, <- Hra, <- Hcra | easy ].
    rewrite Hbs.
    apply Hb; [ now rewrite Hrb, <- Hra, <- Hcra | easy ].
  } {
    rewrite Hsza; [ | easy | easy ].
    rewrite Hszb; [ | now rewrite Hrb, <- Hra, <- Hcra | easy ].
    now rewrite Hbs.
  } {
    now apply Hsza.
  }
}
rewrite sizes_of_bmat_zero_like.
rewrite Has.
remember (Π (k = 1, length sz), nth (k - 1) sz 0)%Srng as len1 eqn:Hlen1.
move Hlen after Hlen1.
move Hra after Hraz; move Hrb before Hra.
rewrite Hra in Hcra.
rewrite Hrb in Hcrb.
clear Hraz Hrbz Hcaz Hcbz.
(* make lhs printed with notation 'Σ' *)
rewrite Hcra, <- (Nat.sub_0_r (S size)).
rewrite fold_iter_seq.
set (bso := bmat_semiring_op_for (mat_el MA 0 0)).
replace (@bmat_add T so) with (@srng_add _ bso) by easy.
replace (@bmat_zero_like T so (@mat_el (bmatrix T) MA O O))
  with (@srng_zero _ bso) by easy.
move IHsz at bottom.
set (i1 := i / len1).
set (j1 := j / len1).
set (i2 := i mod len1).
set (j2 := j mod len1).
rewrite Hlen.
...
rewrite (bmat_el_summation (mat_el MA 0 0)).
...
revert i j sz B Hb Hi Hj Has Hbs.
induction A as [xa| MA IHMA] using bmatrix_ind2; intros. {
  cbn; rewrite Hbs.
  destruct B as [xb| MB]. {
    symmetry.
    apply srng_add_0_l.
  }
  cbn in Hbs.
  unfold is_square_bmat in Hb; cbn in Hb.
  destruct (zerop (mat_nrows MB)) as [Hbrz| Hbrz]. {
    cbn; rewrite Hbrz; cbn.
    rewrite srng_mul_0_r; symmetry.
    apply srng_add_0_l.
  }
  destruct (zerop (mat_ncols MB)); [ easy | ].
  now subst sz.
}
destruct B as [xb| MB]. {
  cbn in Hbs; rewrite Hbs.
  cbn in Has.
  unfold is_square_bmat in Ha; cbn in Ha.
  destruct (zerop (mat_nrows MA)) as [Harz| Harz]. {
    cbn; rewrite Harz; cbn.
    rewrite srng_mul_0_l; symmetry.
    apply srng_add_0_l.
  }
  destruct (zerop (mat_ncols MA)); [ easy | ].
  now subst sz.
}
remember 1 as one.
cbn - [ iter_seq ].
cbn - [ iter_seq ] in Ha, Hb, Has, Hbs, Hi, Hj.
cbn in Hi, Hj; subst one.
destruct (zerop (mat_nrows MA)) as [Hraz| Hraz]; [ easy | ].
destruct (zerop (mat_ncols MA)) as [Hcaz| Hcaz]; [ easy | ].
destruct (zerop (mat_nrows MB)) as [Hrbz| Hrbz]; [ easy | ].
destruct (zerop (mat_ncols MB)) as [Hcbz| Hcbz]; [ easy | ].
cbn in Ha, Hb, Hi, Hj, Has, Hbs.
destruct Ha as (_ & Hcra & Ha).
destruct Hb as (_ & Hcrb & Hb).
move Hrbz before Hraz; move Hcbz before Hcaz.
move Hcrb before Hcra; move Hb before Ha.
rewrite Has in Hbs.
injection Hbs; clear Hbs; intros Hsb Hrr.
move Hrr after Hcra; move MB after Hraz.
cbn - [ iter_seq ].
rewrite <- Hsb.
remember (sizes_of_bmatrix (mat_el MA 0 0)) as sz1 eqn:Hsz1.
remember
  (sizes_of_bmatrix
     (fold_left (λ acc k, (acc + mat_el MA 0 k * mat_el MB k 0)%BM)
        (seq 0 (mat_ncols MA)) (bmat_zero_like (mat_el MA 0 0))))
  as sz2 eqn:Hsz2.
remember (Π (k = 1, length sz1), nth (k - 1) sz1 0) as s1 eqn:Hs1.
remember (Π (k = 1, length sz2), nth (k - 1) sz2 0) as s2 eqn:Hs2.
rename Hsz1 into Hsa.
move sz2 before sz1; move Hsb before Hsa.
move sz after sz1; move Has after Hsa.
move Hsz2 before Hsb.
move s2 before s1.
specialize (IHMA (i / s1)) as H1.
replace (mat_ncols MA) with (S (mat_ncols MA - 1) - 0) by flia Hcaz.
rewrite fold_iter_seq.
...

(*
End in_ring.
Require Import ZArith.
Open Scope Z_scope.
Existing Instance Z_ring_op.
(*
Compute (let n := 3%nat in list_list_of_bmat (A n)).
Compute (let n := 4%nat in mat_of_bmat (A n)%BM).
Compute (let n := 4%nat in list_list_of_mat (mat_of_bmat (A n))).
Compute (let n := 4%nat in map (λ i, map (λ j, bmat_el (A n) i j) (seq 0 (Nat.pow 2 n))) (seq 0 (Nat.pow 2 n))).
*)
Compute (list_list_of_bmat
     (BM_M (mat_of_list_list (BM_1 0) (map(map (@BM_1 _))
         [[1;2;3;4;5]; [6;7;8;9;10]; [11;12;13;14;15]])))).
Definition ex :=
 BM_M (mat_of_list_list (BM_1 0)
   [[BM_M (mat_of_list_list (BM_1 0) (map(map (@BM_1 _))
      [[1;2;3;4;5]; [6;7;8;9;10]; [11;12;13;14;15];
         [16;17;18;19;20]; [21;22;23;24;25]]));
     BM_M (mat_of_list_list (BM_1 0) (map(map (@BM_1 _))
        [[31;32;33;34;35]; [36;37;38;39;40]; [41;42;43;44;45];
           [46;47;48;49;50]; [51;52;53;54;55]]));
     BM_M (mat_of_list_list (BM_1 0) (map(map (@BM_1 _))
       [[61;62;63;64;65]; [66;67;68;69;60]; [71;72;73;74;75];
          [76;77;78;79;70]; [81;82;83;84;85]]))];
    [BM_M (mat_of_list_list (BM_1 0) (map(map (@BM_1 _))
      [[101;2;3;4;5]; [6;7;8;9;10]; [11;12;13;14;15];
         [16;17;18;19;20]; [21;22;23;24;25]]));
     BM_M (mat_of_list_list (BM_1 0) (map(map (@BM_1 _))
        [[31;32;33;34;35]; [36;37;38;39;40]; [41;42;43;44;45];
           [46;47;48;49;50]; [51;52;53;54;55]]));
     BM_M (mat_of_list_list (BM_1 0) (map(map (@BM_1 _))
       [[31;32;33;34;35]; [36;37;38;39;40]; [41;42;43;44;45];
          [46;47;48;49;50]; [51;52;53;54;55]]))];
    [BM_M (mat_of_list_list (BM_1 0) (map(map (@BM_1 _))
      [[201;2;3;4;5]; [6;7;8;9;10]; [11;12;13;14;15];
         [16;17;18;19;20]; [21;22;23;24;25]]));
     BM_M (mat_of_list_list (BM_1 0) (map(map (@BM_1 _))
        [[31;32;33;34;35]; [36;37;38;39;40]; [41;42;43;44;45];
           [46;47;48;49;50]; [51;52;53;54;55]]));
     BM_M (mat_of_list_list (BM_1 0) (map(map (@BM_1 _))
       [[31;32;33;34;35]; [36;37;38;39;40]; [41;42;43;44;45];
          [46;47;48;49;50]; [51;52;53;54;55]]))]]).
Compute (sizes_of_bmatrix ex).
Compute (list_list_of_bmat ex).
Compute (let n := sqr_bmat_size ex in map (λ i, map (λ j, bmat_el ex i j) (seq 0 n)) (seq 0 n)).
Compute (list_list_of_mat (mat_of_sqr_bmat ex)).
Compute (sqr_bmat_size ex).
*)

End in_ring.

Module bmatrix_Notations.

Declare Scope BM_scope.
Delimit Scope BM_scope with BM.

Notation "A + B" := (bmat_add A B) : BM_scope.
Notation "A - B" := (bmat_sub A B) : BM_scope.
Notation "A * B" := (bmat_mul A B) : BM_scope.
Notation "- A" := (bmat_opp A) : BM_scope.

Arguments bmat_el {T so} BM%BM i%nat j%nat.
Arguments bmat_nat_mul_l {T so}.
Arguments mat_of_sqr_bmat {T so} BM%BM.
Arguments I_2_pow {T so}.
Arguments Z_2_pow {T so}.
Arguments IZ_2_pow {T so}.
Arguments sizes_of_bmatrix_IZ {T so}.
Arguments sqr_bmat_size {T} BM%BM.
Arguments Tr {T so}.

End bmatrix_Notations.
