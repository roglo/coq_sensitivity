(* matrices and block matrices *)
(* sequence A_n of matrices defined in sensitivity conjecture
   and the proof their square is "n * I_n" *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Init.Nat.
Require Import Misc.

(* "Given a n×n matrix A, a principal submatrix of A is obtained by deleting
    the same set of rows and columns from A.

   Theorem 2.1. (Cauchy’s Interlace Theorem) Let A be a symmetric n×n matrix,
      and B be a m×m principal submatrix of A, for some m < n. If the
      eigenvalues of A are λ₁ ≥ λ₂ ≥ … ≥ λ_n, and the eigenvalues of B
      are µ₁ ≥ µ₂ ≥ … ≥ µ_m, then for all 1 ≤ i ≤ m,
              λ_i ≥ µ_i ≥ λ_{i+n-m}."
*)

Require Import Semiring SRsummation.
Require Import Relations.

(* matrices *)

Record matrix T := mk_mat
  { mat_el : nat → nat → T;
    mat_nrows : nat;
    mat_ncols : nat }.

(* function extensionality required for matrices *)
Axiom matrix_eq : ∀ T (MA MB : matrix T),
  mat_nrows MA = mat_nrows MB
  → mat_ncols MA = mat_ncols MB
  → (∀ i j, i < mat_nrows MA → j < mat_ncols MB →
      mat_el MA i j = mat_el MB i j)
  → MA = MB.

Definition list_list_nrows T (ll : list (list T)) :=
  length ll.

Definition list_list_ncols T (ll : list (list T)) :=
  length (hd [] ll).

Definition list_list_of_mat T (M : matrix T) : list (list T) :=
  map (λ i, map (mat_el M i) (seq 0 (mat_ncols M))) (seq 0 (mat_nrows M)).

Definition list_list_el T d (ll : list (list T)) i j : T :=
  nth j (nth i ll []) d.

Definition mat_of_list_list T d (ll : list (list T)) :=
  mk_mat (list_list_el d ll) (list_list_nrows ll) (list_list_ncols ll).

(*
Compute (let (i, j) := (2, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (let (i, j) := (7, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (let (i, j) := (1, 3) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (list_list_of_mat (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]])).
*)

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

Fixpoint concat_list_in_list {T} (ll1 ll2 : list (list T)) :=
  match ll1 with
  | [] => ll2
  | l1 :: ll1' =>
       match ll2 with
       | [] => ll1
       | l2 :: ll2' => app l1 l2 :: concat_list_in_list ll1' ll2'
       end
  end.

Definition concat_list_list_list {T} (lll : list (list (list T))) :=
  fold_left concat_list_in_list lll [].

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
Context (so := rng_semiring).
Context {sp : @semiring_prop T (@rng_semiring T ro)}.
Context {rp : @ring_prop T ro}.
Existing Instance so.

(* addition *)

Definition mat_add {so : semiring_op T} (MA MB : matrix T) :=
  {| mat_el i j := (mat_el MA i j + mat_el MB i j)%Srng;
     mat_nrows := mat_nrows MA;
     mat_ncols := mat_ncols MA |}.

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

Definition nat_semiring_op : semiring_op nat :=
  {| srng_zero := 0;
     srng_one := 1;
     srng_add := Nat.add;
     srng_mul := Nat.mul |}.

(*
End in_ring.
Compute (list_list_of_mat (mat_add add (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
Compute (list_list_of_mat (mat_add add (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
*)

(* multiplication *)

Definition mat_mul {so : semiring_op T} (MA MB : matrix T) :=
  {| mat_el i k :=
       (Σ (j = 0, mat_ncols MA - 1), mat_el MA i j * mat_el MB j k)%Srng;
     mat_nrows := mat_nrows MA;
     mat_ncols := mat_ncols MB |}.

(*
End in_ring.
Compute (let _ := nat_semiring_op in list_list_of_mat (mat_mul (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
*)

(* a null block matrix having the same structure as a given block matrix *)

Fixpoint bmat_zero_like {so : semiring_op T} (BM : bmatrix T) :=
  match BM with
  | BM_1 _ => BM_1 0%Srng
  | BM_M M =>
      let M' :=
        mk_mat (λ i j, bmat_zero_like (mat_el M i j))
          (mat_nrows M) (mat_ncols M)
      in
      BM_M M'
  end.

(* multiplication of block matrices *)

Fixpoint bmat_mul {so : semiring_op T} (MM1 MM2 : bmatrix T) :=
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
            fold_left
              (λ acc j,
                 bmat_add acc (bmat_mul (mat_el MMA i j) (mat_el MMB j k)))
              (seq 0 (mat_ncols MMA))
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

(* opposite *)

Definition mat_opp M : matrix T :=
  {| mat_el i j := (- mat_el M i j)%Rng;
     mat_nrows := mat_nrows M;
     mat_ncols := mat_ncols M |}.

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

(* subtraction *)

Definition mat_sub MA MB :=
  mat_add MA (mat_opp MB).

Definition bmat_sub BMA BMB :=
  bmat_add BMA (bmat_opp BMB).

(* notations *)

Declare Scope BM_scope.
Delimit Scope BM_scope with BM.

Notation "a + b" := (bmat_add a b) : BM_scope.
Notation "a - b" := (bmat_sub a b) : BM_scope.
Notation "a * b" := (bmat_mul a b) : BM_scope.
Notation "- a" := (bmat_opp a) : BM_scope.

(* sequence "An" *)

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

Fixpoint A n : bmatrix T :=
  match n with
  | 0 => BM_1 0%Srng
  | S n' =>
       BM_M
         (mat_of_list_list (BM_1 0%Srng)
            [[A n'; I_2_pow n'];
             [I_2_pow n'; bmat_opp (A n')]])
  end.

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

Theorem bmat_fit_for_add_IZ_A : ∀ u n,
  bmat_fit_for_add (IZ_2_pow u n) (A n).
Proof.
intros.
revert u.
induction n; intros; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros * Hi Hj.
destruct i. {
  destruct j; [ apply IHn | ].
  destruct j; [ cbn | flia Hj ].
  apply bmat_fit_for_add_IZ_IZ.
}
destruct i; [ | flia Hi ].
destruct j; [ apply bmat_fit_for_add_IZ_IZ | ].
destruct j; [ cbn | flia Hj ].
transitivity (A n); [ easy | ].
apply bmat_fit_for_add_opp_r.
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

Fixpoint sizes_of_bmatrix (BM : bmatrix T) :=
  match BM with
  | BM_1 _ => []
  | BM_M M =>
      if zerop (mat_nrows M) ∨∨ zerop (mat_ncols M) then []
      else mat_nrows M :: sizes_of_bmatrix (mat_el M 0 0)
  end.

Definition is_square_bmat (BM : bmatrix T) :=
  is_square_bmat_loop (sizes_of_bmatrix BM) BM.

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

Theorem is_square_bmat_loop_zero_like : ∀ BM sizes,
  is_square_bmat_loop sizes BM
  → is_square_bmat_loop sizes (bmat_zero_like BM).
Proof.
intros * HBM.
revert BM HBM.
induction sizes as [| size]; intros; [ now destruct BM | ].
cbn in HBM |-*.
destruct BM as [x| M]; [ easy | cbn ].
destruct HBM as (Hr & Hc & HBM).
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
apply IHsizes.
now apply HBM.
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
now apply IHBM.
Qed.

Definition compatible_square_bmatrices (BML : list (bmatrix T)) :=
  ∃ sizes,
   (∀ BM, BM ∈ BML → is_square_bmat BM) ∧
   (∀ BM, BM ∈ BML → sizes_of_bmatrix BM = sizes).

Theorem bmat_zero_like_mul_distr_l : ∀ BMA BMB,
  is_square_bmat BMA
  → bmat_zero_like (BMA * BMB)%BM = (bmat_zero_like BMA * BMB)%BM.
Proof.
intros * Ha.
revert BMB.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros; cbn. {
  destruct BMB as [xb| mb]; [ | easy ].
  now rewrite srng_mul_0_l.
}
destruct BMB as [xb| mb]; [ easy | ].
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
rewrite bmat_zero_like_idemp.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *.
destruct (zerop ra) as [H| H]; [ easy | cbn in Ha; clear H ].
destruct (zerop ca) as [H| H]; [ easy | cbn in Ha; clear H ].
destruct Ha as (_ & H & Ha); subst ca.
replace
  (fold_left (λ a k, a + bmat_zero_like (fa i k) * fb k j)
    (seq 0 ra) (bmat_zero_like (fa 0 0)))%BM
with
  (fold_left (λ a k, a + bmat_zero_like (fa i k * fb k j))
    (seq 0 ra) (bmat_zero_like (fa 0 0)))%BM. 2: {
  apply List_fold_left_ext_in.
  intros k BM Hk; f_equal.
  apply in_seq in Hk.
  clear BM.
  apply IHBMA; [ easy | flia Hk | ].
  rewrite sizes_of_bmatrix_at_0_0 with (r := ra); [ | easy | easy | easy ].
  now apply Ha.
}
clear Hi IHBMA.
induction ra. {
  cbn; apply bmat_zero_like_idemp.
}
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite fold_left_app; cbn.
rewrite bmat_zero_like_add_distr.
f_equal.
apply IHra.
intros i1 j1 Hi1 Hj1.
apply Ha; [ flia Hi1 | flia Hj1 ].
Qed.

Theorem bmat_zero_like_mul_distr_r : ∀ BMA BMB,
  is_square_bmat BMA
  → bmat_zero_like (BMA * BMB)%BM = (BMA * bmat_zero_like BMB)%BM.
Proof.
intros * Ha.
revert BMB.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros; cbn. {
  destruct BMB as [xb| mb]; [ cbn | easy ].
  now rewrite srng_mul_0_r.
}
destruct BMB as [xb| mb]; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *.
destruct (zerop ra) as [H| H]; [ easy | cbn in Ha; clear H ].
destruct (zerop ca) as [H| H]; [ easy | cbn in Ha; clear H ].
destruct Ha as (_ & H & Ha); subst ca.
replace
  (fold_left (λ a k, a + fa i k * bmat_zero_like (fb k j))
    (seq 0 ra) (bmat_zero_like (fa 0 0)))%BM
with
  (fold_left (λ a k, a + bmat_zero_like (fa i k * fb k j))
    (seq 0 ra) (bmat_zero_like (fa 0 0)))%BM. 2: {
  apply List_fold_left_ext_in.
  intros k BM Hk; f_equal.
  apply in_seq in Hk.
  clear BM.
  apply IHBMA; [ easy | flia Hk | ].
  rewrite sizes_of_bmatrix_at_0_0 with (r := ra); [ | easy | easy | easy ].
  now apply Ha.
}
clear Hi IHBMA.
induction ra. {
  cbn; apply bmat_zero_like_idemp.
}
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite fold_left_app; cbn.
rewrite bmat_zero_like_add_distr.
f_equal.
apply IHra.
intros i1 j1 Hi1 Hj1.
apply Ha; [ flia Hi1 | flia Hj1 ].
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
apply IHsizes; [ now apply Ha | now apply Hb ].
Qed.

Theorem sizes_of_bmatrix_add : ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → sizes_of_bmatrix (BMA + BMB)%BM = sizes_of_bmatrix BMA.
Proof.
intros * Ha Hb Hab.
revert BMB Hb Hab.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros. {
  now destruct BMB.
}
destruct BMB as [xb| mb]; [ easy | cbn ].
move mb before ma.
cbn in Ha, Hb, Hab.
destruct (zerop (mat_nrows ma)) as [Hrza| Hrza]; [ easy | ].
destruct (zerop (mat_ncols ma)) as [Hcza| Hcza]; [ easy | ].
destruct (zerop (mat_nrows mb)) as [Hrzb| Hrzb]; [ easy | ].
destruct (zerop (mat_ncols mb)) as [Hczb| Hczb]; [ easy | ].
cbn in Ha, Hb, Hab |-*.
f_equal.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *.
destruct Ha as (_ & Hrca & Ha).
destruct Hb as (_ & Hrcb & Hb).
subst ca cb.
injection Hab; clear Hab; intros Hss H2; subst rb.
apply IHBMA; [ easy | easy | | | easy ]. {
  now apply Ha.
} {
  now apply Hb.
}
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
now apply IHBM.
Qed.

Theorem is_square_bmat_loop_mul : ∀ BMA BMB sizes,
  is_square_bmat_loop sizes BMA
  → is_square_bmat_loop sizes BMB
  → is_square_bmat_loop sizes (BMA * BMB)%BM.
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
destruct size; [ easy | cbn ].
clear Hi Hj.
move j before i.
induction size. {
  cbn.
  apply is_square_bmat_loop_add. {
    now apply is_square_bmat_loop_zero_like.
  }
  apply IHsizes; [ apply Ha; flia | apply Hb; flia ].
}
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
  is_square_bmat BM
  → (∀ n, sta ≤ n < sta + len → is_square_bmat (f n))
  → (∀ n, sta ≤ n < sta + len → sizes_of_bmatrix BM = sizes_of_bmatrix (f n))
  → sizes_of_bmatrix (fold_left (λ acc j, (acc + f j)%BM) (seq sta len) BM) =
    sizes_of_bmatrix BM.
Proof.
intros * Hb Hf Hfb.
revert sta BM Hf Hb Hfb.
induction len; intros; [ easy | cbn ].
rewrite IHlen; cycle 1. {
  intros n Hn.
  apply Hf; flia Hn.
} {
  apply is_square_bmat_loop_add. {
    rewrite sizes_of_bmatrix_add; [ easy | easy | | ]. {
      apply Hf; flia.
    } {
      apply Hfb; flia.
    }
  } {
    rewrite sizes_of_bmatrix_add; [ | easy | | ]. {
      rewrite (Hfb sta); [ | flia ].
      apply Hf; flia.
    } {
      apply Hf; flia.
    } {
      apply Hfb; flia.
    }
  }
} {
  intros * Hn.
  rewrite sizes_of_bmatrix_add; [ | easy | | ]. {
    apply Hfb; flia Hn.
  } {
    apply Hf; flia.
  } {
    apply Hfb; flia.
  }
}
apply sizes_of_bmatrix_add; [ easy | apply Hf; flia | apply Hfb; flia ].
Qed.

Lemma sizes_of_bmatrix_mul_a : ∀ fa fb ra,
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

Theorem sizes_of_bmatrix_mul : ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → sizes_of_bmatrix (BMA * BMB)%BM = sizes_of_bmatrix BMA.
Proof.
intros * Ha Hb Hab.
revert BMB Hb Hab.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros. {
  now destruct BMB.
}
destruct BMB as [xb| mb]; [ easy | cbn ].
move mb before ma.
cbn in Ha, Hb, Hab.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *.
destruct (zerop ra) as [Hraz| Hraz]; [ easy | ].
destruct (zerop ca) as [Hcaz| Hcaz]; [ easy | ].
destruct (zerop rb) as [Hrbz| Hrbz]; [ easy | ].
destruct (zerop cb) as [Hcbz| Hcbz]; [ easy | ].
cbn in Ha, Hb, Hab |-*.
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
  (Hssm : sizes_of_bmatrix (fa 0 0 * fb 0 0)%BM = sizes_of_bmatrix (fa 0 0)). {
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
  (Haj : ∀ j, j < S ra → sizes_of_bmatrix (fa 0 j) = sizes_of_bmatrix (fa 0 0)). {
  intros j Hj.
  apply (@sizes_of_bmatrix_at_0_0 _ (S ra)); [ | flia Hj | easy ].
  intros i k Hi Hk.
  apply Ha; [ flia Hi | flia Hk ].
}
assert
  (Hbj : ∀ j, j < S ra → sizes_of_bmatrix (fb j 0) = sizes_of_bmatrix (fb 0 0)). {
  intros j Hj.
  apply (@sizes_of_bmatrix_at_0_0 _ (S ra)); [ | easy | flia Hj ].
  intros i k Hi Hk.
  apply Hb; [ flia Hi | flia Hk ].
}
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite sizes_of_bmatrix_add. {
  destruct ra; [ apply sizes_of_bmat_zero_like | ].
  apply IHra; flia.
} {
  clear IHra.
  induction ra. {
    apply is_square_bmat_zero_like.
    apply Ha; flia.
  }
  assert
    (H : ∀ i j,
     i < S ra → j < S ra
     → is_square_bmat_loop (sizes_of_bmatrix (fa i j)) (fa i j)
     → ∀ BMB : bmatrix T,
         is_square_bmat BMB
         → sizes_of_bmatrix (fa i j) = sizes_of_bmatrix BMB
         → sizes_of_bmatrix (fa i j * BMB)%BM = sizes_of_bmatrix (fa i j)). {
    intros i j Hi Hj Hsa' * HBMB Hss.
    apply IHBMA; [ flia Hi | flia Hj | easy | easy | easy ].
  }
  specialize (IHra H); clear H.
  assert
    (H : ∀ i j,
     i < S ra → j < S ra
     → is_square_bmat_loop (sizes_of_bmatrix (fa 0 0)) (fa i j)). {
    intros * Hi Hj.
    apply Ha; [ flia Hi | flia Hj ].
  }
  specialize (IHra H); clear H.
  assert
    (H : ∀ i j,
     i < S ra → j < S ra
     → is_square_bmat_loop (sizes_of_bmatrix (fb 0 0)) (fb i j)). {
    intros * Hi Hj.
    apply Hb; [ flia Hi | flia Hj ].
  }
  specialize (IHra H); clear H.
  assert
    (H : ∀ j, j < S ra
     → sizes_of_bmatrix (fa 0 j) = sizes_of_bmatrix (fa 0 0)). {
    intros * Hj.
    apply Haj; flia Hj.
  }
  specialize (IHra H); clear H.
  assert
    (H : ∀ j, j < S ra
     → sizes_of_bmatrix (fb j 0) = sizes_of_bmatrix (fb 0 0)). {
    intros * Hj.
    apply Hbj; flia Hj.
  }
  specialize (IHra H); clear H.
  assert (Hzsr : 0 < S ra) by flia.
  assert (Hzssr : 0 < S (S ra)) by flia.
  assert (Hrsr : ra < S ra) by flia.
  assert (Hrssr : ra < S (S ra)) by flia.
  assert (Hsab : ∀ j, j < S ra → is_square_bmat (fa 0 j * fb j 0)%BM). {
    intros j Hj.
    assert (H9 : j < S (S ra)) by flia Hj.
    apply is_square_bmat_loop_mul. {
      apply sizes_of_bmatrix_mul_a; [ | | | easy ]. {
        intros i k Hi Hk H6 * H7 H11.
        apply IHBMA; [ flia Hi Hj | flia Hk Hj | easy | easy | easy ].
      } {
        intros i k Hi Hk.
        apply Ha; [ flia Hi Hj | flia Hk Hj ].
      } {
        intros i k Hi Hk.
        apply Hb; [ flia Hi Hj | flia Hk Hj ].
      }
    } {
      rewrite IHBMA; [ | easy | easy | | | ]. {
        rewrite Haj; [ | easy ].
        now rewrite Hab; apply Hb.
      } {
        rewrite Haj; [ now apply Ha | easy ].
      } {
        unfold is_square_bmat.
        rewrite Hbj; [ now apply Hb | easy ].
      } {
        rewrite Haj; [ now rewrite Hbj | easy ].
      }
    }
  }
  rewrite List_seq_succ_r; cbn.
  rewrite fold_left_app; cbn.
  apply is_square_bmat_loop_add. {
    rewrite sizes_of_bmatrix_add; [ easy | easy | now apply Hsab | ].
    rewrite sizes_of_bmatrix_fold_left. {
      rewrite sizes_of_bmat_zero_like.
      symmetry.
      rewrite IHBMA; [ now apply Haj | easy | easy | | | ]. {
        rewrite Haj; [ now apply Ha | easy ].
      } {
        unfold is_square_bmat.
        rewrite Hbj; [ now apply Hb | easy ].
      } {
        rewrite Haj; [ now rewrite Hbj | easy ].
      }
    } {
      apply is_square_bmat_zero_like.
      now apply Ha.
    } {
      intros j Hj.
      apply Hsab; flia Hj.
    } {
      intros j Hj.
      assert (H9 : j < S (S ra)) by flia Hj.
      rewrite sizes_of_bmat_zero_like.
      symmetry.
      rewrite IHBMA; [ now apply Haj | easy | easy | | | ]. {
        rewrite Haj; [ now apply Ha | easy ].
      } {
        unfold is_square_bmat.
        rewrite Hbj; [ now apply Hb | easy ].
      } {
        rewrite Haj; [ now rewrite Hbj | easy ].
      }
    }
  } {
    rewrite sizes_of_bmatrix_add; [ | easy | now apply Hsab | ]. {
      rewrite sizes_of_bmatrix_fold_left. {
        rewrite sizes_of_bmat_zero_like.
        apply is_square_bmat_loop_mul; [ now apply Ha | ].
        now rewrite Hab; apply Hb.
      } {
        apply is_square_bmat_zero_like.
        now apply Ha.
      } {
        intros j Hj.
        apply Hsab; flia Hj.
      } {
        intros j Hj.
        assert (H9 : j < S (S ra)) by flia Hj.
        rewrite sizes_of_bmat_zero_like.
        rewrite IHBMA; [ | easy | easy | | | ]. {
          now symmetry; apply Haj.
        } {
          rewrite Haj; [ | easy ].
          apply Ha; [ easy | flia Hj ].
        } {
          unfold is_square_bmat.
          rewrite Hbj; [ | easy ].
          apply Hb; [ flia Hj | easy ].
        } {
          rewrite Haj; [ now rewrite Hbj | easy ].
        }
      }
    } {
      rewrite sizes_of_bmatrix_fold_left. {
        rewrite sizes_of_bmat_zero_like.
        symmetry.
        rewrite IHBMA; [ now apply Haj | easy | easy | | | ]. {
          rewrite Haj; [ now apply Ha | easy ].
        } {
          unfold is_square_bmat.
          rewrite Hbj; [ now apply Hb | easy ].
        } {
          rewrite Haj; [ now rewrite Hbj | easy ].
        }
      } {
        now apply is_square_bmat_zero_like, Ha.
      } {
        intros j Hj.
        apply Hsab; flia Hj.
      } {
        intros j Hj.
        assert (H9 : j < S ra) by flia Hj.
        assert (Hjssr : j < S (S ra)) by flia Hj.
        rewrite sizes_of_bmat_zero_like.
        symmetry.
        rewrite IHBMA; [ | easy | easy | | | ]. {
          apply (@sizes_of_bmatrix_at_0_0 _ (S ra)); [ | easy | easy ].
          intros i k Hi Hk.
          apply Ha; [ flia Hi | flia Hk ].
        } {
          rewrite Haj; [ now apply Ha | easy ].
        } {
          unfold is_square_bmat.
          rewrite Hbj; [ now apply Hb | easy ].
        } {
          rewrite Haj; [ now rewrite Hbj | easy ].
        }
      }
    }
  }
} {
  assert (H3 : 0 < S ra) by flia.
  assert (H4 : ra < S ra) by flia.
  apply is_square_bmat_loop_mul. {
    rewrite IHBMA; [ | easy | easy | | | ]. {
      rewrite Haj; [ now apply Ha | easy ].
    } {
      rewrite Haj; [ now apply Ha | easy ].
    } {
      unfold is_square_bmat.
      rewrite Hbj; [ now apply Hb | easy ].
    } {
      rewrite Haj; [ now rewrite Hbj | easy ].
    }
  } {
    rewrite IHBMA; [ | easy | easy | | | ]. {
      rewrite Haj; [ | easy ].
      now rewrite Hab; apply Hb.
    } {
      rewrite Haj; [ now apply Ha | easy ].
    } {
      unfold is_square_bmat.
      rewrite Hbj; [ now apply Hb | easy ].
    } {
      rewrite Haj; [ now rewrite Hbj | easy ].
    }
  }
} {
  destruct ra; [ now cbn; rewrite sizes_of_bmat_zero_like | ].
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
  unfold so.
  rewrite sizes_of_bmatrix_IZ.
  rewrite <- (sizes_of_bmatrix_IZ n 0%Srng).
  apply IHn.
}
destruct i; [ | flia Hi ].
destruct j; cbn. {
  unfold so.
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

Theorem bmat_mul_1_l : ∀ n M,
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

Theorem bmat_mul_1_r : ∀ n M,
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
  unfold so.
  rewrite fold_rng_sub.
  now rewrite rng_add_opp_r.
}
cbn; f_equal.
now apply matrix_eq.
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
now apply IHBM.
Qed.

Theorem bmat_mul_add_distr_r :
  ∀ (MA MB MC : bmatrix T),
  compatible_square_bmatrices [MA; MB; MC]
  → ((MA + MB) * MC = MA * MC + MB * MC)%BM.
Proof.
intros * Hcsb.
revert MA MB Hcsb.
induction MC as [xc| mc IHMC] using bmatrix_ind2; intros. {
  destruct Hcsb as (sizes & Hsq & Hsz).
  unfold is_square_bmat in Hsq.
  destruct sizes as [| size]. 2: {
    specialize (Hsq _ (or_intror (or_intror (or_introl eq_refl)))).
    rewrite Hsz in Hsq; [ easy | now right; right; left ].
  }
  destruct MA as [xa| ma]. 2: {
    specialize (Hsq _ (or_introl eq_refl)).
    rewrite Hsz in Hsq; [ easy | now left ].
  }
  destruct MB as [xb| mb]. 2: {
    specialize (Hsq _ (or_intror (or_introl eq_refl))).
    rewrite Hsz in Hsq; [ easy | now right; left ].
  }
  now cbn; rewrite srng_mul_add_distr_r.
}
destruct Hcsb as (sizes & Hsq & Hsz).
destruct sizes as [| size]. {
  specialize (Hsq _ (or_intror (or_intror (or_introl eq_refl)))).
  unfold is_square_bmat in Hsq.
  rewrite Hsz in Hsq; [ easy | now right; right; left ].
}
destruct MA as [xa| ma]. {
  now specialize (Hsz _ (or_introl eq_refl)).
}
destruct MB as [xb| mb]; [ easy | ].
specialize (Hsq _ (or_introl eq_refl)) as Ha.
specialize (Hsq _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hsq _ (or_intror (or_intror (or_introl eq_refl)))) as Hc.
unfold is_square_bmat in Ha, Hb, Hc.
specialize (Hsz _ (or_introl eq_refl)) as Has.
specialize (Hsz _ (or_intror (or_introl eq_refl))) as Hbs.
specialize (Hsz _ (or_intror (or_intror (or_introl eq_refl)))) as Hcs.
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
destruct mc as (fc, rc, cc).
cbn - [ In ] in *.
rewrite Has in Ha; rewrite Hbs in Hb; rewrite Hcs in Hc.
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
    (λ (acc : bmatrix T) (j0 : nat),
       (acc + (fa i j0 + fb i j0) * fc j0 j)%BM)
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
  apply IHMC; [ flia Hk | easy | ].
  exists sizes.
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  split. {
    intros BM HBM.
    unfold is_square_bmat.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia Hk ].
      apply Ha; [ easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | flia Hk ].
      apply Hb; [ easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hk | easy ].
      apply Hc; [ flia Hk | easy ].
    }
    easy.
  } {
    intros BM HBM.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ easy | easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ easy | easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ easy | flia Hk | easy ].
    }
    easy.
  }
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
clear Hi Hj IHMC Hsq Hsz.
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
revert MB MC Hcsb.
induction MA as [xa| ma IHMA] using bmatrix_ind2; intros. {
  destruct Hcsb as (sizes & Hsq & Hsz).
  unfold is_square_bmat in Hsq.
  destruct sizes as [| size]. 2: {
    specialize (Hsq _ (or_introl eq_refl)).
    rewrite Hsz in Hsq; [ easy | now left ].
  }
  destruct MB as [xb| mb]. 2: {
    specialize (Hsq _ (or_intror (or_introl eq_refl))).
    rewrite Hsz in Hsq; [ easy | now right; left ].
  }
  destruct MC as [xc| mc]. 2: {
    specialize (Hsq _ (or_intror (or_intror (or_introl eq_refl)))).
    rewrite Hsz in Hsq; [ easy | now right; right; left ].
  }
  now cbn; rewrite srng_mul_add_distr_l.
}
destruct Hcsb as (sizes & Hsq & Hsz).
destruct sizes as [| size]. {
  specialize (Hsq _ (or_introl eq_refl)).
  unfold is_square_bmat in Hsq.
  rewrite Hsz in Hsq; [ easy | now left ].
}
destruct MB as [xb| mb]. {
  now specialize (Hsz _ (or_intror (or_introl eq_refl))).
}
destruct MC as [xc| mc]; [ easy | ].
specialize (Hsq _ (or_introl eq_refl)) as Ha.
specialize (Hsq _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hsq _ (or_intror (or_intror (or_introl eq_refl)))) as Hc.
unfold is_square_bmat in Ha, Hb, Hc.
specialize (Hsz _ (or_introl eq_refl)) as Has.
specialize (Hsz _ (or_intror (or_introl eq_refl))) as Hbs.
specialize (Hsz _ (or_intror (or_intror (or_introl eq_refl)))) as Hcs.
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
destruct mc as (fc, rc, cc).
cbn - [ In ] in *.
rewrite Has in Ha; rewrite Hbs in Hb; rewrite Hcs in Hc.
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
  apply IHMA; [ easy | flia Hk | ].
  exists sizes.
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  split. {
    intros BM HBM.
    unfold is_square_bmat.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia Hk ].
      apply Ha; [ easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | flia Hk | easy ].
      apply Hb; [ flia Hk | easy ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia Hk | easy ].
      apply Hc; [ flia Hk | easy ].
    }
    easy.
  } {
    intros BM HBM.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ easy | easy | flia Hk ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ easy | flia Hk | easy ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ easy | flia Hk | easy ].
    }
    easy.
  }
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
clear Hi Hj IHMA Hsq Hsz.
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
destruct Hcsb as (sizes & Hsq & Hsz).
rewrite bmat_add_add_swap; cycle 1. {
  apply (is_square_bmat_fit_for_add (sizes_of_bmatrix MA)). {
    now apply Hsq; left.
  } {
    specialize (Hsq _ (or_intror (or_introl eq_refl))) as H.
    rewrite Hsz; [ | now left ].
    rewrite <- (Hsz MB); [ | now right; left ].
    now apply Hsq; right; left.
  }
} {
  apply (is_square_bmat_fit_for_add (sizes_of_bmatrix MA)). {
    now apply Hsq; left.
  } {
    specialize (Hsq _ (or_introl eq_refl)) as H.
    apply is_square_bmat_loop_opp.
    now apply Hsq; left.
  }
}
unfold so.
rewrite bmat_add_opp_r.
symmetry.
rewrite (bmat_zero_like_eq_compat _ MB); cycle 1. {
  now apply Hsq; left.
} {
  now apply Hsq; right; left.
} {
  rewrite Hsz; [ | now left ].
  rewrite Hsz; [ | now right; left ].
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
  destruct Hcsb as (sizes & Hsq & Hsz).
  exists sizes.
  split. {
    intros * HBM.
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsq; left | ].
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsq; right; left | ].
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    now apply is_square_bmat_zero_like, Hsq; left.
  } {
    intros * HBM.
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsz; left | ].
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsz; right; left | ].
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    rewrite sizes_of_bmat_zero_like.
    now apply Hsz; left.
  }
}
unfold bmat_sub in Hab.
unfold so in Hab.
rewrite <- bmat_zero_like_opp in Hab. 2: {
  destruct Hcsb as (size & Hsq & Hsz).
  now apply Hsq; left.
}
now rewrite bmat_add_0_l in Hab.
Qed.

Theorem bmat_mul_opp_l : ∀ MA MB,
  compatible_square_bmatrices [MA; MB]
  → ((- MA) * MB = - (MA * MB))%BM.
Proof.
intros * Hcsb.
specialize (@bmat_mul_add_distr_r MA (bmat_opp MA) MB) as H1.
destruct Hcsb as (sizes & Hsq & Hsz).
specialize (Hsq _ (or_introl eq_refl)) as Ha.
specialize (Hsq _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hsz _ (or_introl eq_refl)) as Has.
specialize (Hsz _ (or_intror (or_introl eq_refl))) as Hbs.
generalize Ha; intros Hao.
apply is_square_bmat_opp in Hao.
generalize Has; intros Haso.
rewrite <- sizes_of_bmatrix_opp in Haso.
assert (H : compatible_square_bmatrices [MA; (- MA)%BM; MB]). {
  exists sizes.
  split; intros BM HBM. {
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | easy ].
  } {
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | easy ].
  }
}
specialize (H1 H); clear H.
unfold so in H1.
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
split; intros BM HBM. {
  destruct HBM as [HBM| HBM]; [ subst BM | ]. {
    now apply is_square_bmat_mul.
  }
  destruct HBM as [HBM| HBM]; [ subst BM | easy ].
  apply is_square_bmat_mul; [ easy | easy | ].
  now rewrite Haso, Hbs.
} {
  destruct HBM as [HBM| HBM]; [ subst BM | ]. {
    now rewrite sizes_of_bmatrix_mul.
  } {
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    rewrite sizes_of_bmatrix_mul; [ easy | easy | easy | ].
    now rewrite sizes_of_bmatrix_opp.
  }
}
Qed.

Theorem bmat_mul_opp_r : ∀ MA MB,
  compatible_square_bmatrices [MA; MB]
  → (MA * (- MB) = - (MA * MB))%BM.
Proof.
intros * Hcsb.
specialize (@bmat_mul_add_distr_l MA MB (bmat_opp MB)) as H1.
destruct Hcsb as (sizes & Hsq & Hsz).
specialize (Hsq _ (or_introl eq_refl)) as Ha.
specialize (Hsq _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hsz _ (or_introl eq_refl)) as Has.
specialize (Hsz _ (or_intror (or_introl eq_refl))) as Hbs.
generalize Hb; intros Hbo.
apply is_square_bmat_opp in Hbo.
generalize Hbs; intros Hbso.
rewrite <- sizes_of_bmatrix_opp in Hbso.
assert (H : compatible_square_bmatrices [MA; MB; (- MB)%BM]). {
  exists sizes.
  split; intros BM HBM. {
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | easy ].
  } {
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | ].
    destruct HBM as [HBM| HBM]; [ now subst BM | easy ].
  }
}
specialize (H1 H); clear H.
unfold so in H1.
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
split; intros BM HBM. {
  destruct HBM as [HBM| HBM]; [ subst BM | ]. {
    now apply is_square_bmat_mul.
  }
  destruct HBM as [HBM| HBM]; [ subst BM | easy ].
  apply is_square_bmat_mul; [ easy | easy | ].
  congruence.
} {
  destruct HBM as [HBM| HBM]; [ subst BM | ]. {
    now rewrite sizes_of_bmatrix_mul.
  } {
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    rewrite sizes_of_bmatrix_mul; [ easy | easy | easy | ].
    now rewrite sizes_of_bmatrix_opp.
  }
}
Qed.

Theorem bmat_mul_opp_opp : ∀ MA MB,
  compatible_square_bmatrices [MA; MB]
  → (- MA * - MB = MA * MB)%BM.
Proof.
intros * Hab.
rewrite bmat_mul_opp_l. 2: {
  destruct Hab as (sizes & Hsq & Hsz).
  exists sizes.
  split; intros BM HBM. {
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsq; left | ].
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    now apply is_square_bmat_opp, Hsq; right; left.
  } {
    destruct HBM as [HBM| HBM]; [ now subst BM; apply Hsz; left | ].
    destruct HBM as [HBM| HBM]; [ subst BM | easy ].
    now rewrite sizes_of_bmatrix_opp; apply Hsz; right; left.
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
split; intros BM HBM. {
  replace BM with M; [ easy | ].
  destruct HBM as [| HBM]; [ easy | now destruct HBM ].
} {
  replace BM with M; [ easy | ].
  destruct HBM as [| HBM]; [ easy | now destruct HBM ].
}
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
destruct i; cbn. {
  destruct j; cbn; [ easy | ].
  destruct j; [ easy | flia Hj ].
}
destruct i; [ cbn | flia Hi ].
destruct j; cbn; [ easy | ].
destruct j; [ easy | flia Hj ].
Qed.

Theorem sizes_of_bmatrix_A : ∀ n,
  sizes_of_bmatrix (A n) = repeat 2 n.
Proof.
intros.
induction n; [ easy | now cbn; f_equal ].
Qed.

Theorem A_is_square_bmat : ∀ n,
  is_square_bmat (A n).
Proof.
intros.
induction n; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
destruct i; cbn. {
  destruct j; [ easy | cbn ].
  destruct j; [ | flia Hj ].
  rewrite sizes_of_bmatrix_A.
  rewrite <- (sizes_of_bmatrix_IZ n 1%Srng).
  apply IZ_is_square_bmat.
}
destruct i; [ cbn | flia Hi ].
destruct j; cbn. {
  rewrite sizes_of_bmatrix_A.
  rewrite <- (sizes_of_bmatrix_IZ n 1%Srng).
  apply IZ_is_square_bmat.
}
destruct j; [ | flia Hj ].
apply is_square_bmat_loop_opp.
apply IHn.
Qed.

Theorem bmat_zero_like_A_eq_Z :
  ∀ n, bmat_zero_like (A n) = Z_2_pow n.
Proof.
intros.
induction n; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
destruct i; cbn. {
  destruct j; cbn; [ easy | ].
  destruct j; [ cbn | flia Hj ].
  apply bmat_zero_like_IZ_eq_Z.
}
destruct i; [ cbn | flia Hi ].
destruct j; cbn. {
  apply bmat_zero_like_IZ_eq_Z.
}
destruct j; [ | flia Hj ].
unfold so.
rewrite bmat_zero_like_opp; [ easy | ].
apply A_is_square_bmat.
Qed.

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I : ∀ n,
  (A n * A n = bmat_nat_mul_l n (I_2_pow n))%BM.
Proof.
intros.
induction n; intros; [ now cbn; rewrite srng_mul_0_l | ].
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
destruct i. {
  destruct j. {
    cbn.
    rewrite bmat_nat_mul_l_succ.
    rewrite <- IHn.
    rewrite bmat_mul_1_r; [ | easy ].
    f_equal.
    rewrite <- bmat_zero_like_sqr; [ | apply A_is_square_bmat ].
    apply bmat_add_0_l.
  }
  destruct j; [ cbn | flia Hj ].
  rewrite bmat_nat_mul_l_succ.
  rewrite bmat_mul_1_r. 2: {
    unfold I_2_pow.
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_mul_1_l. 2: {
    unfold I_2_pow.
    transitivity (A n); [ apply bmat_fit_for_add_IZ_A | ].
    apply bmat_fit_for_add_opp_r.
  }
  rewrite bmat_add_0_l.
  rewrite bmat_add_opp_r.
  rewrite fold_Z_2_pow.
  rewrite old_bmat_add_0_r. 2: {
    now apply bmat_fit_for_add_Z_2_pow_bmat_nat_mul_l.
  }
  rewrite bmat_nat_mul_0_r.
  now apply bmat_zero_like_A_eq_Z.
}
destruct i; [ | flia Hi ].
destruct j; cbn. {
  rewrite bmat_mul_1_l. 2: {
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_mul_1_r. 2: {
    transitivity (A n); [ | apply bmat_fit_for_add_opp_r ].
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_add_0_l.
  rewrite bmat_add_opp_r.
  rewrite bmat_nat_mul_l_succ.
  rewrite fold_Z_2_pow.
  rewrite bmat_nat_mul_0_r.
  rewrite old_bmat_add_0_r; [ | easy ].
  now apply bmat_zero_like_A_eq_Z.
}
destruct j; [ cbn | flia Hj ].
rewrite bmat_mul_1_l; [ | easy ].
rewrite bmat_mul_sqr_opp; [ | apply A_is_square_bmat ].
rewrite bmat_nat_mul_l_succ.
rewrite <- IHn.
rewrite bmat_zero_like_A_eq_Z.
rewrite old_bmat_add_0_l; [ | apply bmat_fit_for_add_IZ_IZ ].
apply bmat_add_comm.
transitivity (A n). 2: {
  apply (is_square_bmat_fit_for_add (sizes_of_bmatrix (A n))). {
    apply A_is_square_bmat.
  }
  apply is_square_bmat_loop_mul; apply A_is_square_bmat.
}
apply bmat_fit_for_add_IZ_A.
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
unfold so.
rewrite rng_opp_summation; cbn.
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

Theorem Tr_A : ∀ n, Tr (A n) = 0%Srng.
Proof.
intros.
(*
revert n.
apply nat_ind; [ | intros n IHn ]; [ easy | ].
*)
induction n; [ easy | cbn ].
rewrite IHn.
do 2 rewrite srng_add_0_l.
unfold so.
rewrite Tr_opp; [ | apply A_is_square_bmat ].
rewrite IHn.
apply rng_opp_0.
Qed.

(* *)

Definition is_square_mat (M : matrix T) := mat_nrows M = mat_ncols M.

(* vector *)

Record vector T := mk_vect
  { vect_el : nat → T;
    vect_nrows : nat }.

(* multiplication of a matrix by a vector *)

Definition mat_mul_vect_r M V :=
  mk_vect (λ i, (Σ (j = 0, mat_ncols M - 1), mat_el M i j * vect_el V j)%Srng)
    (mat_nrows M).

(* multiplication of a vector by a scalar *)

Definition vect_mul_scal_l μ V :=
  mk_vect (λ i, μ * vect_el V i)%Srng (vect_nrows V).

(* multiplication of a matrix by a scalar *)

Definition mat_mul_scal_l μ M :=
  mk_mat (λ i j, μ * mat_el M i j)%Srng (mat_nrows M) (mat_ncols M).

(* matrix without row i and column j *)

Definition submatrix (M : matrix T) i j :=
  mk_mat
    (λ k l,
       if lt_dec k i then
         if lt_dec l j then mat_el M k l
         else mat_el M k (l + 1)
       else
         if lt_dec l j then mat_el M (k + 1) l
         else mat_el M (k + 1) (l + 1))
    (mat_nrows M - 1)
    (mat_ncols M - 1).

(* (-1) ^ n *)

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%Rng
  | _ => (- 1%Srng)%Rng
  end.

(* determinant *)

Fixpoint det_loop M n :=
  match n with
  | 0 => 0%Rng
  | 1 => mat_el M 0 0
  | S n' =>
      (Σ (j = 0, n'),
       minus_one_pow j * mat_el M 0 j * det_loop (submatrix M 0 j) n')%Rng
  end.

Definition determinant M := det_loop M (mat_nrows M).

(*
End in_ring.

Require Import ZArith.
Open Scope Z_scope.

Compute let ro := Z_ring_op in determinant (mat_of_list_list 0 [[1; 2]; [3; 4]]).
Compute let ro := Z_ring_op in determinant (mat_of_list_list 0 [[-2; 2; -3]; [-1; 1; 3]; [2; 0; -1]]). (* 18: seems good *)
*)

End in_ring.

Module matrix_Notations.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Notation "a + b" := (mat_add a b) : M_scope.
Notation "a - b" := (mat_sub a b) : M_scope.
Notation "a * b" := (mat_mul a b) : M_scope.
Notation "- a" := (mat_opp a) : M_scope.

End matrix_Notations.

Module bmatrix_Notations.

Declare Scope BM_scope.
Delimit Scope BM_scope with BM.

Notation "a + b" := (bmat_add a b) : BM_scope.
Notation "a - b" := (bmat_sub a b) : BM_scope.
Notation "a * b" := (bmat_mul a b) : BM_scope.
Notation "- a" := (bmat_opp a) : BM_scope.

End bmatrix_Notations.

Import matrix_Notations.
Import bmatrix_Notations.

(* decidability of equality in semirings
   and the fact that 1 ≠ 0 *)

Class sring_dec_prop T {so : semiring_op T} :=
  { srng_eq_dec : ∀ a b : T, {a = b} + {a ≠ b};
    srng_1_neq_0 : (1 ≠ 0)%Srng }.

Arguments srng_eq_dec {T}%type {so sring_dec_prop} _%Srng _%Srng.

(* property of a polynomial: its coefficient of higher degree is not 0 *)
(* returns a boolean to allow proof of equality to be unique *)

Definition polyn_prop_test T {so : semiring_op T} {fdp : sring_dec_prop} f n :=
  match n with
  | 0 => true
  | S n => if srng_eq_dec (f n) 0%Srng then false else true
  end.

(* polynomial *)

Record polynomial T (so : semiring_op T) (sdp : sring_dec_prop) := mk_polyn
  { polyn_list : list T;
    polyn_prop :
      polyn_prop_test (λ i, nth i polyn_list 0%Srng) (length polyn_list) =
      true }.

Arguments polynomial T%type_scope {so sdp}.
Arguments mk_polyn {T so sdp}.

Definition polyn_coeff T {so : semiring_op T} {sdp : sring_dec_prop} P i :=
  nth i (polyn_list P) 0%Srng.

(* degree of a polynomial *)

Definition polyn_degree_plus_1 T {so : semiring_op T} {sdp : sring_dec_prop}
     P :=
  length (polyn_list P).

Definition polyn_degree T {so : semiring_op T} {sdp : sring_dec_prop} P :=
  polyn_degree_plus_1 P - 1.

(* evaluation of a polynomial *)

Definition eval_polyn T {so : semiring_op T} {sdp : sring_dec_prop}
    (P : polynomial T) x :=
  match polyn_degree_plus_1 P with
  | 0 => 0%Srng
  | S n => (Σ (i = 0, n), polyn_coeff P i * x ^ i)%Srng
  end.

(* algebraically closed set *)

Class algeb_closed_prop T {so : semiring_op T} {sdp : sring_dec_prop} :=
  { alcl_roots :
      ∀ P : polynomial T, polyn_degree P > 0 → ∃ x, eval_polyn P x = 0%Srng }.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so := rng_semiring).
Context {sp : @semiring_prop T (@rng_semiring T ro)}.
Context {rp : @ring_prop T ro}.
Context {sdp : @sring_dec_prop T so}.
Existing Instance so.

(* normalize a list, i.e. remove all trailing 0s *)

Fixpoint strip_0s l :=
  match l with
  | [] => []
  | a :: l' => if srng_eq_dec a 0%Srng then strip_0s l' else l
  end.

Definition norm_list_as_polyn l := rev (strip_0s (rev l)).

(* polynomial from and to a list *)

Theorem polyn_of_list_prop : ∀ l,
  polyn_prop_test (λ i, nth i (norm_list_as_polyn l) 0%Srng)
    (length (norm_list_as_polyn l)) = true.
Proof.
intros.
unfold norm_list_as_polyn.
remember (rev l) as l' eqn:Hl.
clear l Hl.
rename l' into l.
rewrite rev_length.
induction l as [| a]; [ easy | cbn ].
destruct (srng_eq_dec a 0%Srng) as [Haz| Haz]; [ apply IHl | cbn ].
rewrite app_nth2; rewrite rev_length; [ | now unfold ge ].
rewrite Nat.sub_diag; cbn.
now destruct (srng_eq_dec a 0%Srng).
Qed.

Definition polyn_of_list l :=
  mk_polyn (norm_list_as_polyn l) (polyn_of_list_prop l).

Definition list_of_polyn (P : polynomial T) :=
  polyn_list P.

(*
End in_ring.

Require Import ZArith.
Open Scope Z_scope.

Theorem Z_neq_1_0 : 1%Z ≠ 0%Z. Proof. easy. Qed.

Definition Z_sring_dec_prop :=
  {| srng_eq_dec := Z.eq_dec;
     srng_1_neq_0 := Z_neq_1_0 |}.

Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in polyn_of_list [3; 4; 7; 0].
Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in list_of_polyn (polyn_of_list [3; 4; 7; 0]).
Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in list_of_polyn (polyn_of_list [0]).
*)

(* monomial *)

Definition monom_x := polyn_of_list [0; 1]%Srng.

(* convertion matrix → matrix with monomials *)

Definition monom_mat_of_mat M : matrix (polynomial T) :=
  mk_mat (λ i j, polyn_of_list [mat_el M i j])
    (mat_nrows M) (mat_ncols M).

(* addition of polynomials *)

Fixpoint polyn_list_add la lb :=
  match la with
  | [] => lb
  | a :: la' =>
      match lb with
      | [] => la
      | b :: lb' => (a + b)%Srng :: polyn_list_add la' lb'
      end
  end.

Definition polyn_add P Q :=
  polyn_of_list (polyn_list_add (polyn_list P) (polyn_list Q)).

(*
End in_ring.

Require Import ZArith.
Open Scope Z_scope.

Theorem Z_neq_1_0 : 1%Z ≠ 0%Z. Proof. easy. Qed.

Definition Z_sring_dec_prop :=
  {| srng_eq_dec := Z.eq_dec;
     srng_1_neq_0 := Z_neq_1_0 |}.

Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in list_of_polyn (polyn_add (polyn_of_list [3; 4; 7; 0])
(polyn_of_list [7; 0; 0; 22; -4])).
Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in list_of_polyn (polyn_add (polyn_of_list [3; 4; 7; 0])
(polyn_of_list [7; 2; -7])).
*)

(* opposite of a polynomial *)

Theorem polyn_opp_prop_test : ∀ P,
  polyn_prop_test (λ i, nth i (map rng_opp (polyn_list P)) 0%Srng)
    (length (map rng_opp (polyn_list P))) = true.
Proof.
intros.
rewrite map_length.
destruct P as (l, p).
unfold polyn_prop_test in p |-*; cbn.
remember (length l) as len eqn:Hlen.
symmetry in Hlen.
destruct len; [ easy | ].
rewrite (List_map_nth_in _ 0%Srng); [ | flia Hlen ].
destruct (srng_eq_dec (nth len l 0%Srng) 0%Srng) as [H| Hz]; [ easy | ].
clear p.
destruct (srng_eq_dec (- nth len l 0%Srng)%Rng 0%Srng) as [H| H]; [ | easy ].
rewrite <- rng_opp_involutive in H.
apply rng_opp_inj in H.
unfold so in H.
now rewrite rng_opp_0 in H.
Qed.

Definition polyn_opp P :=
  mk_polyn (map rng_opp (polyn_list P)) (polyn_opp_prop_test P).

(* subtraction of polynomials *)

Definition polyn_sub P Q :=
  polyn_add P (polyn_opp Q).

(* multiplication of polynomials *)

Definition polyn_list_convol_mul la lb i :=
  (Σ (j = 0, i), nth j la 0 * nth (i - j) lb 0)%Srng.

Definition polyn_list_mul la lb :=
  map (polyn_list_convol_mul la lb) (seq 0 (length la + length lb - 1)).

Definition polyn_mul P Q :=
  polyn_of_list (polyn_list_mul (polyn_list P) (polyn_list Q)).

(*
End in_ring.

Require Import ZArith.
Open Scope Z_scope.

Theorem Z_neq_1_0 : 1%Z ≠ 0%Z. Proof. easy. Qed.

Definition Z_sring_dec_prop :=
  {| srng_eq_dec := Z.eq_dec;
     srng_1_neq_0 := Z_neq_1_0 |}.

Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in polyn_list_mul [1] [3; 4].
Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in polyn_list_mul [1; 1; 0] [-1; 1; 0].
Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in list_of_polyn (polyn_mul (polyn_of_list [1; 1]) (polyn_of_list [-1; 1])).
*)

(* polynomial syntax *)

Declare Scope polynomial_scope.
Delimit Scope polynomial_scope with P.

Notation "0" := (polyn_of_list []) : polynomial_scope.
Notation "1" := (polyn_of_list [1%Srng]) : polynomial_scope.
Notation "P + Q" := (polyn_add P Q) : polynomial_scope.
Notation "P - Q" := (polyn_sub P Q) : polynomial_scope.
Notation "P * Q" := (polyn_mul P Q) : polynomial_scope.
Notation "- P" := (polyn_opp P) : polynomial_scope.

(* identity matrix of size n *)

Definition mat_id n :=
  mk_mat (λ i j, if Nat.eq_dec i j then 1%Srng else 0%Srng) n n.

(* semiring and ring of polynomials *)

Definition polyn_semiring_op : semiring_op (polynomial T) :=
  {| srng_zero := polyn_of_list [];
     srng_one := polyn_of_list [1%Srng];
     srng_add := polyn_add;
     srng_mul := polyn_mul |}.

Definition polyn_ring_op : ring_op (polynomial T) :=
  {| rng_semiring := polyn_semiring_op;
     rng_opp := polyn_opp |}.

Existing Instance polyn_semiring_op.
Existing Instance polyn_ring_op.

(* equality of polynomials ↔ equality of their lists *)

Theorem polyn_eq : ∀ P Q,
  polyn_list P = polyn_list Q
  → P = Q.
Proof.
intros (PL, PP) (QL, QP) HPQ.
cbn in HPQ |-*.
subst QL.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

(* polynomials semiring properties *)

Theorem polyn_list_add_comm : ∀ la lb,
  polyn_list_add la lb = polyn_list_add lb la.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | cbn ].
f_equal; [ | apply IHla ].
apply srng_add_comm.
Qed.

Theorem polyn_add_comm : ∀ P Q : polynomial T, (P + Q)%P = (Q + P)%P.
Proof.
intros (PL, PP) (QL, QP); cbn.
apply polyn_eq; cbn.
f_equal; f_equal; f_equal.
clear PP QP.
apply polyn_list_add_comm.
Qed.

Theorem polyn_list_add_0_l : ∀ la, polyn_list_add [] la = la.
Proof. easy. Qed.

Theorem polyn_list_add_0_r : ∀ la, polyn_list_add la [] = la.
Proof.
intros; rewrite polyn_list_add_comm; apply polyn_list_add_0_l.
Qed.

Theorem polyn_add_0_l : ∀ P, (0 + P)%P = P.
Proof.
intros (la, Pa); cbn.
apply polyn_eq.
cbn - [ polyn_list_add ].
rewrite polyn_list_add_0_l.
unfold norm_list_as_polyn.
rewrite <- rev_involutive; f_equal.
rewrite <- (rev_involutive la) in Pa.
rewrite rev_length in Pa.
remember (rev la) as l; clear la Heql.
rename l into la.
unfold polyn_prop_test in Pa.
destruct la as [| a]; [ easy | ].
cbn - [ nth ] in Pa |-*.
destruct (srng_eq_dec a 0%Srng) as [Haz| Haz]; [ | easy ].
subst a; exfalso.
rewrite app_nth2 in Pa; [ | now unfold ge; rewrite rev_length ].
rewrite rev_length, Nat.sub_diag in Pa; cbn in Pa.
now destruct (srng_eq_dec 0%Srng 0%Srng).
Qed.

Theorem strip_0s_idemp : ∀ la,
  strip_0s (strip_0s la) =
  strip_0s la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
destruct (srng_eq_dec a 0%Srng) as [Haz| Haz]; [ easy | cbn ].
now destruct (srng_eq_dec a 0%Srng).
Qed.

Theorem strip_0s_app : ∀ la lb,
  strip_0s (la ++ lb) =
    match strip_0s la with
    | [] => strip_0s lb
    | a :: la' => a :: la' ++ lb
    end.
Proof.
intros.
remember (strip_0s la) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  induction la as [| a]; [ easy | ].
  cbn in Hlc |-*.
  destruct (srng_eq_dec a 0%Srng) as [Haz| Haz]; [ now apply IHla | easy ].
}
revert lb c lc Hlc.
induction la as [| a]; intros; [ easy | cbn ].
destruct (srng_eq_dec a 0%Srng) as [Haz| Haz]. {
  subst a; cbn in Hlc.
  destruct (srng_eq_dec 0%Srng 0%Srng) as [H| H]; [ clear H | easy ].
  apply IHla, Hlc.
}
cbn in Hlc.
destruct (srng_eq_dec a 0%Srng) as [H| H]; [ easy | clear H ].
now injection Hlc; clear Hlc; intros; subst c lc.
Qed.

Theorem eq_strip_0s_nil : ∀ la,
  strip_0s la = [] ↔ ∃ n, la = repeat 0%Srng n.
Proof.
intros.
split. {
  intros Hla.
  induction la as [| a]; [ now exists 0 | ].
  cbn in Hla.
  destruct (srng_eq_dec a 0%Srng) as [Haz| Haz]; [ | easy ].
  subst a.
  specialize (IHla Hla) as (n, Hn).
  now exists (S n); cbn; subst la.
} {
  intros (n, Hn).
  subst la.
  induction n; cbn; [ easy | ].
  now destruct (srng_eq_dec 0 0).
}
Qed.

Theorem strip_0s_repeat_0s : ∀ n,
  strip_0s (repeat 0%Srng n) = [].
Proof.
intros.
induction n; [ easy | cbn ].
now destruct (srng_eq_dec 0%Srng 0%Srng).
Qed.

Theorem norm_list_as_polyn_app : ∀ la lb,
  norm_list_as_polyn (la ++ lb) =
  match norm_list_as_polyn lb with
  | [] => norm_list_as_polyn la
  | lc => la ++ lc
  end.
Proof.
intros.
unfold norm_list_as_polyn.
rewrite rev_app_distr.
rewrite strip_0s_app.
remember (strip_0s (rev lb)) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]; [ easy | ].
rewrite app_comm_cons.
rewrite rev_app_distr.
rewrite rev_involutive.
remember (rev (c :: lc)) as ld eqn:Hld.
symmetry in Hld.
destruct ld as [| d]; [ | easy ].
now apply List_eq_rev_nil in Hld.
Qed.

Theorem polyn_list_add_repeat_0s_l : ∀ n la,
  polyn_list_add (repeat 0%Srng n) la = la ++ repeat 0%Srng (n - length la).
Proof.
intros.
revert la.
induction n; intros; [ now rewrite app_nil_r | ].
destruct la as [| a]; [ easy | cbn ].
rewrite srng_add_0_l; f_equal.
apply IHn.
Qed.

Theorem neq_strip_0s_cons_0 : ∀ la lb,
  strip_0s la ≠ 0%Srng :: lb.
Proof.
intros * Hll.
revert lb Hll.
induction la as [| a]; intros; [ easy | cbn ].
cbn in Hll.
destruct (srng_eq_dec a 0%Srng) as [Haz| Haz]. {
  now apply IHla in Hll.
}
now injection Hll; intros.
Qed.

Theorem polyn_list_add_app_l : ∀ la lb lc,
  polyn_list_add (la ++ lb) lc =
  polyn_list_add la (firstn (length la) lc) ++
  polyn_list_add lb (skipn (length la) lc).
Proof.
intros.
revert la lb.
induction lc as [| c]; intros; cbn. {
  rewrite firstn_nil, skipn_nil.
  now do 3 rewrite polyn_list_add_0_r.
}
destruct la as [| a]; [ easy | cbn ].
f_equal; apply IHlc.
Qed.

Theorem polyn_list_add_app_r : ∀ la lb lc,
  polyn_list_add la (lb ++ lc) =
  polyn_list_add (firstn (length lb) la) lb ++
  polyn_list_add (skipn (length lb) la) lc.
Proof.
intros.
do 3 rewrite polyn_list_add_comm.
rewrite polyn_list_add_app_l.
rewrite (polyn_list_add_comm lb).
rewrite (polyn_list_add_comm lc).
easy.
Qed.

Theorem List_eq_app_repeat : ∀ A la lb n (c : A),
  la ++ lb = repeat c n
  → la = repeat c (length la) ∧ lb = repeat c (length lb) ∧
     length la + length lb = n.
Proof.
intros A * Hll.
revert n Hll.
induction la as [| a]; intros; cbn. {
  cbn in Hll; subst lb; cbn.
  now rewrite repeat_length.
}
destruct n; [ easy | ].
cbn in Hll.
injection Hll; clear Hll; intros Hll H; subst c.
specialize (IHla n Hll).
destruct IHla as (H1 & H2 & H3).
now rewrite <- H1, <- H2, H3.
Qed.

Theorem polyn_list_add_length : ∀ la lb,
  length (polyn_list_add la lb) = max (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal; apply IHla.
Qed.

Theorem norm_list_as_polyn_involutive : ∀ la,
  norm_list_as_polyn (norm_list_as_polyn la) = norm_list_as_polyn la.
Proof.
intros.
induction la as [| a] using rev_ind; [ easy | ].
rewrite norm_list_as_polyn_app.
remember (norm_list_as_polyn [a]) as x eqn:Hx.
cbn in Hx; subst x.
destruct (srng_eq_dec a 0) as [Haz| Haz]; [ easy | ].
cbn - [ norm_list_as_polyn ].
rewrite norm_list_as_polyn_app; cbn.
now destruct (srng_eq_dec a 0).
Qed.

Theorem norm_list_as_polyn_add_idemp_l : ∀ la lb,
  norm_list_as_polyn (polyn_list_add (norm_list_as_polyn la) lb) =
  norm_list_as_polyn (polyn_list_add la lb).
Proof.
intros.
unfold norm_list_as_polyn; f_equal.
revert la.
induction lb as [| b]; intros. {
  do 2 rewrite polyn_list_add_0_r.
  now rewrite rev_involutive, strip_0s_idemp.
}
cbn.
destruct la as [| a]; [ easy | cbn ].
do 2 rewrite strip_0s_app; cbn.
rewrite <- IHlb.
remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  destruct (srng_eq_dec a 0) as [Haz| Haz]. {
    subst a; rewrite srng_add_0_l; cbn.
    now rewrite strip_0s_app.
  }
  cbn.
  now rewrite strip_0s_app.
}
cbn.
rewrite rev_app_distr; cbn.
now rewrite strip_0s_app.
Qed.

Theorem norm_list_as_polyn_add_idemp_r : ∀ la lb,
  norm_list_as_polyn (polyn_list_add la (norm_list_as_polyn lb)) =
  norm_list_as_polyn (polyn_list_add la lb).
Proof.
intros.
rewrite polyn_list_add_comm.
rewrite norm_list_as_polyn_add_idemp_l.
now rewrite polyn_list_add_comm.
Qed.

Theorem polyn_list_add_assoc : ∀ la lb lc,
  polyn_list_add la (polyn_list_add lb lc) =
  polyn_list_add (polyn_list_add la lb) lc.
Proof.
intros.
revert lb lc.
induction la; intros; [ easy | ].
destruct lb; [ easy | cbn ].
destruct lc; [ easy | cbn ].
rewrite srng_add_assoc.
f_equal.
apply IHla.
Qed.

Theorem polyn_add_assoc : ∀ P Q R, (P + (Q + R) = (P + Q) + R)%P.
Proof.
intros (la, Pa) (lb, Pb) (lc, Pc).
apply polyn_eq.
cbn - [ polyn_list_add ].
rewrite norm_list_as_polyn_add_idemp_l.
rewrite norm_list_as_polyn_add_idemp_r.
f_equal.
apply polyn_list_add_assoc.
Qed.

Theorem polyn_add_add_swap : ∀ P Q R, (P + Q + R = P + R + Q)%P.
Proof.
intros.
do 2 rewrite <- polyn_add_assoc.
now rewrite (polyn_add_comm R).
Qed.

(*
Theorem find_polyn_deg_eq_compat : ∀ f g n,
  (∀ i, i < n → f i = g i)
  → find_polyn_deg f n = find_polyn_deg g n.
Proof.
intros * Hfg.
induction n; [ easy | cbn ].
rewrite <- Hfg; [ | now apply Nat.lt_succ_r ].
destruct (srng_eq_dec (f n) 0%Srng) as [Hfz| Hfz]; [ | easy ].
apply IHn; intros i Hi.
now apply Hfg, Nat.lt_lt_succ_r.
Qed.
*)

Theorem polyn_list_convol_mul_comm : ∀ la lb i,
  polyn_list_convol_mul la lb i = polyn_list_convol_mul lb la i.
Proof.
intros.
unfold polyn_list_convol_mul, so.
rewrite srng_summation_rtl.
apply srng_summation_eq_compat.
intros j Hj.
rewrite srng_mul_comm.
rewrite Nat.add_0_r.
now replace (i - (i - j)) with j by flia Hj.
Qed.

Theorem polyn_list_mul_comm : ∀ la lb,
  polyn_list_mul la lb = polyn_list_mul lb la.
Proof.
intros la lb.
unfold polyn_list_mul.
rewrite (Nat.add_comm (length lb)).
apply map_ext.
apply polyn_list_convol_mul_comm.
Qed.

Theorem polyn_mul_comm : ∀ P Q, (P * Q = Q * P)%P.
Proof.
intros.
unfold polyn_mul.
apply polyn_eq.
f_equal; f_equal.
apply polyn_list_mul_comm.
Qed.

Theorem strip_0s_map_0 : ∀ A (la lb : list A),
  strip_0s (map (λ _, 0%Srng) la) = strip_0s (map (λ _, 0%Srng) lb).
Proof.
intros A *.
revert lb.
induction la as [| a]; intros; cbn. {
  induction lb as [| b]; [ easy | cbn ].
  now destruct (srng_eq_dec 0 0).
}
now destruct (srng_eq_dec 0 0).
Qed.

Theorem polyn_list_convol_mul_0_l : ∀ n la i,
  polyn_list_convol_mul (repeat 0%Srng n) la i = 0%Srng.
Proof.
intros.
unfold polyn_list_convol_mul.
apply all_0_srng_summation_0.
intros j ahj.
remember (@srng_zero T so) as z.
replace (nth j (repeat z n) z) with z; subst z. 2: {
  symmetry; clear.
  revert j.
  induction n; intros; cbn; [ now destruct j | ].
  destruct j; [ easy | ].
  apply IHn.
}
apply srng_mul_0_l.
Qed.

Theorem map_polyn_list_convol_mul_0_l : ∀ n la li,
  map (polyn_list_convol_mul (repeat 0%Srng n) la) li =
  repeat 0%Srng (length li).
Proof.
intros.
induction li as [| i]; [ easy | ].
cbn - [ polyn_list_convol_mul ].
rewrite IHli; f_equal.
apply polyn_list_convol_mul_0_l.
Qed.

Theorem norm_list_as_polyn_repeat_0 : ∀ n,
  norm_list_as_polyn (repeat 0%Srng n) = [].
Proof.
intros.
induction n; [ easy | ].
rewrite List_repeat_succ_app.
rewrite norm_list_as_polyn_app; cbn.
now destruct (srng_eq_dec 0 0).
Qed.

Theorem map_polyn_list_convol_mul_cons_l : ∀ a la lb ln,
  map (polyn_list_convol_mul (a :: la) lb) ln =
  polyn_list_add
    (map (λ n, a * nth n lb 0) ln)%Srng
    (map (λ n, (Σ (j = 1, n), nth (j - 1) la 0 * nth (n - j) lb 0)%Srng) ln).
Proof.
intros.
unfold polyn_list_convol_mul.
induction ln as [| n]; [ easy | ].
cbn - [ nth seq sub ].
f_equal; [ | apply IHln ].
unfold so.
rewrite srng_summation_split_first; [ | apply Nat.le_0_l ].
f_equal; [ now cbn; rewrite Nat.sub_0_r | ].
apply srng_summation_eq_compat.
intros i Hi; f_equal.
destruct i; [ easy | ].
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem map_polyn_list_convol_mul_cons_r : ∀ b la lb ln,
  map (polyn_list_convol_mul la (b :: lb)) ln =
  polyn_list_add
    (map (λ n, nth n la 0 * b) ln)%Srng
    (map (λ n, (Σ (j = 1, n), nth (j - 1) la 0 * nth (n - j) lb 0)%Srng) ln).
Proof.
intros.
unfold polyn_list_convol_mul.
induction ln as [| n]; [ easy | ].
cbn - [ nth seq sub ].
f_equal; [ | apply IHln ].
unfold so.
rewrite srng_summation_split_last; [ | apply Nat.le_0_l ].
rewrite Nat.sub_diag.
rewrite srng_add_comm; f_equal.
apply srng_summation_eq_compat.
intros i Hi; f_equal.
now replace (n - (i - 1)) with (S (n - i)) by flia Hi.
Qed.

Theorem map_polyn_list_convol_mul_const_l : ∀ n a ln lb,
  map (λ i, polyn_list_convol_mul (a :: repeat 0%Srng n) lb i) ln =
  map (λ i, a * nth i lb 0)%Srng ln.
Proof.
intros.
unfold polyn_list_convol_mul.
apply map_ext_in.
intros i Hi.
destruct i; [ cbn; apply srng_add_0_l | ].
unfold so.
rewrite srng_summation_split_first; [ | apply Nat.le_0_l ].
rewrite all_0_srng_summation_0. 2: {
  intros j Hj.
  destruct j; [ easy | cbn ].
  rewrite List_nth_repeat.
  destruct (lt_dec j n); apply srng_mul_0_l.
}
now rewrite Nat.sub_0_r, srng_add_0_r.
Qed.

Theorem all_0_norm_list_as_polyn_map_0 : ∀ A (ln : list A) f,
  (∀ n, n ∈ ln → f n = 0%Srng)
  → norm_list_as_polyn (map f ln) = [].
Proof.
intros A * Hf.
unfold norm_list_as_polyn.
apply List_eq_rev_nil.
rewrite rev_involutive.
induction ln as [| n]; [ easy | cbn ].
rewrite strip_0s_app.
rewrite IHln. 2: {
  intros i Hi.
  now apply Hf; right.
}
cbn.
destruct (srng_eq_dec (f n) 0) as [H| H]; [ easy | ].
exfalso; apply H.
now apply Hf; left.
Qed.

Theorem length_strip_0s_le : ∀ la, length (strip_0s la) ≤ length la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
destruct (srng_eq_dec a 0) as [Haz| Haz]; [ | easy ].
transitivity (length la); [ easy | ].
apply Nat.le_succ_diag_r.
Qed.

Theorem norm_list_as_polyn_map_seq_ext : ∀ sta len dlen f,
  (∀ i, sta + len ≤ i < sta + len + dlen → f i = 0%Srng)
  → norm_list_as_polyn (map f (seq sta (len + dlen))) =
    norm_list_as_polyn (map f (seq sta len)).
Proof.
intros * Hi.
Admitted. (*
unfold norm_list_as_polyn; f_equal.
revert sta dlen Hi.
induction len; intros. {
  cbn.
  apply eq_strip_0s_nil.
...
induction len; intros; [ now rewrite Nat.add_0_r | ].
rewrite <- Nat.add_succ_comm.
rewrite IHdlen. 2: {
  intros j Hj.

  rewrite <- Nat.add_succ_comm.
  rewrite Nat.add_assoc.
  apply Hi; flia Hj.
}
rewrite List_seq_succ_r.
rewrite map_app.
rewrite rev_app_distr; cbn.
destruct (srng_eq_dec (f (sta + len)) 0) as [Hz| Hz]; [ easy | ].
symmetry.
...
exfalso; apply Hz.
apply Hi; flia.
Qed.
*)

Theorem norm_list_as_polyn_mul_idemp_l : ∀ la lb,
  norm_list_as_polyn (polyn_list_mul (norm_list_as_polyn la) lb) =
  norm_list_as_polyn (polyn_list_mul la lb).
Proof.
intros.
unfold polyn_list_mul.
destruct la as [| a]; [ easy | ].
cbn - [ nth seq sub ].
rewrite strip_0s_app.
rewrite rev_length.
remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  apply eq_strip_0s_nil in Hlc.
  destruct Hlc as (n, Hn).
  apply List_eq_rev_l in Hn.
  rewrite List_rev_repeat in Hn.
  subst la.
  cbn - [ nth seq sub ].
  destruct (srng_eq_dec a 0) as [Haz| Haz]. {
    subst a.
    cbn - [ nth seq sub ].
    rewrite (map_polyn_list_convol_mul_0_l 0).
    rewrite seq_length.
    rewrite norm_list_as_polyn_repeat_0; cbn.
    symmetry.
    apply List_eq_rev_nil.
    rewrite rev_involutive.
    apply eq_strip_0s_nil.
    rewrite repeat_length.
    rewrite Nat.sub_0_r.
    exists (n + length lb).
    symmetry.
    apply List_eq_rev_l.
    rewrite List_rev_repeat; symmetry.
    rewrite (map_polyn_list_convol_mul_0_l (S n)).
    now rewrite seq_length.
  }
  rewrite Nat.sub_succ, Nat.sub_0_r.
  rewrite Nat.sub_succ, Nat.sub_0_r.
  rewrite repeat_length; cbn.
  rewrite (map_polyn_list_convol_mul_const_l 0).
  rewrite (map_polyn_list_convol_mul_const_l n).
  rewrite Nat.add_comm.
  rewrite seq_app, map_app.
  rewrite norm_list_as_polyn_app; cbn.
  remember (norm_list_as_polyn (map _ (seq _ n))) as la eqn:Hla.
  symmetry in Hla.
  destruct la as [| a1]; [ easy | exfalso ].
  rewrite map_ext_in with (g := λ i, 0%Srng) in Hla. 2: {
    intros j Hj.
    apply in_seq in Hj.
    rewrite nth_overflow; [ | easy ].
    apply srng_mul_0_r.
  }
  now rewrite all_0_norm_list_as_polyn_map_0 in Hla.
}
rewrite map_ext_in with
  (g := polyn_list_convol_mul lb (rev (c :: lc ++ [a]))). 2: {
  intros i Hi.
  apply polyn_list_convol_mul_comm.
}
symmetry.
rewrite map_ext_in with (g :=polyn_list_convol_mul lb (a :: la)). 2: {
  intros i Hi.
  apply polyn_list_convol_mul_comm.
}
symmetry.
rewrite Nat.sub_succ, Nat.sub_0_r.
rewrite app_comm_cons, app_length.
cbn - [ norm_list_as_polyn ].
rewrite Nat.sub_0_r.
rewrite rev_app_distr; cbn.
do 2 rewrite (Nat.add_comm _ (length lb)).
rewrite map_polyn_list_convol_mul_cons_r.
rewrite map_polyn_list_convol_mul_cons_r.
rewrite <- norm_list_as_polyn_add_idemp_l.
rewrite <- norm_list_as_polyn_add_idemp_r; symmetry.
rewrite <- norm_list_as_polyn_add_idemp_l.
rewrite <- norm_list_as_polyn_add_idemp_r; symmetry.
f_equal; f_equal. {
  do 2 (rewrite seq_app; symmetry).
  do 2 rewrite map_app.
  do 2 rewrite norm_list_as_polyn_app.
  rewrite Nat.add_0_l.
  rewrite all_0_norm_list_as_polyn_map_0. 2: {
    intros n Hn.
    apply in_seq in Hn.
    rewrite nth_overflow; [ | easy ].
    apply srng_mul_0_l.
  }
  symmetry.
  rewrite all_0_norm_list_as_polyn_map_0. 2: {
    intros n Hn.
    apply in_seq in Hn.
    rewrite nth_overflow; [ | easy ].
    apply srng_mul_0_l.
  }
  easy.
}
do 2 (rewrite seq_app; symmetry).
do 2 rewrite map_app.
do 2 rewrite norm_list_as_polyn_app.
cbn - [ nth seq sub ].
...
Check norm_list_as_polyn_map_seq_ext.
...
rewrite norm_list_as_polyn_map_seq_ext. 2: {
  intros i Hi.
  rewrite Nat.add_0_l.
  replace i with (length lb + (i - length lb)) by flia Hi.
Search (Σ (_ = _, _ + _), _).
...
  apply all_0_srng_summation_0.
  intros j Hj.
  rewrite nth_overflow.

rewrite norm_list_as_polyn_map_seq_ext.
...
do 2 rewrite (seq_app (length lb)).
do 2 rewrite map_app.
cbn - [ nth seq sub ].
do 2 rewrite norm_list_as_polyn_app.
...
rewrite all_0_norm_list_as_polyn_map_0. 2: {
  intros n Hn.
  apply in_seq in Hn.
  apply all_0_srng_summation_0.
  intros i Hi.
  rewrite nth_overflow.
(* euh... non... *)
...
do 2 rewrite (Nat.add_comm (length lb)).
replace (rev lc ++ [c]) with (rev (c :: lc)) by easy.
rewrite <- Hlc.
assert (Hca : length lc < length la). {
  apply Nat.succ_lt_mono.
  replace (S (length lc)) with (length (c :: lc)) by easy.
  rewrite <- Hlc.
  rewrite <- (rev_length la).
  apply Nat.lt_succ_r.
  apply length_strip_0s_le.
}
rewrite Nat.add_1_r.
remember (length la - S (length lc)) as lac eqn:Hlac.
replace (length la) with (S (length lc) + lac) by flia Hca Hlac.
replace (S (length lc)) with (length (strip_0s (rev la))) by now rewrite Hlc.
rewrite <- Nat.add_assoc.
do 2 rewrite seq_app.
rewrite Nat.add_0_l.
...
  ============================
  norm_list_as_polyn
    (map
       (λ n : nat,
          (Σ (j = 1, n),
           nth (j - 1) (rev (strip_0s (rev la))) 0 * nth (n - j) lb 0)%Srng)
       (seq 0 (length (strip_0s (rev la))) ++
        seq (length (strip_0s (rev la))) (length lb))) =
  norm_list_as_polyn
    (map (λ n : nat, (Σ (j = 1, n), nth (j - 1) la 0 * nth (n - j) lb 0)%Srng)
       (seq 0 (length (strip_0s (rev la))) ++
        seq (length (strip_0s (rev la))) (lac + length lb)))
,,,
do 2 rewrite map_app.
do 2 rewrite norm_list_as_polyn_app.
...
  destruct lb as [| b]; [ easy | ].
  remember (b :: lb) as ld eqn:Hld; symmetry in Hld.
  do 2 rewrite Nat.sub_0_r.
  rewrite fold_lap_norm.
  rewrite (lap_convol_mul_cons_with_0_l _ la). 2: {
    intros i.
    specialize (proj1 (eq_strip_0s_nil _) Hlc) as H1.
    destruct (lt_dec i (length la)) as [Hil| Hil]. {
      specialize (H1 (length la - S i)).
      rewrite <- rev_length in H1.
      rewrite <- rev_nth in H1. {
        now rewrite rev_involutive in H1.
      }
      now rewrite rev_length.
    }
    apply Nat.nlt_ge in Hil.
    now rewrite nth_overflow.
  }
  rewrite Nat.add_comm.
  apply lap_convol_mul_more; cbn.
  now rewrite Nat.sub_0_r.
}
rewrite rev_app_distr; cbn.
rewrite fold_lap_norm.
destruct lb as [| b]; [ easy | ].
remember (b :: lb) as d eqn:Hd.
replace (rev lc ++ [c]) with (rev (c :: lc)) by easy.
rewrite <- Hlc.
rewrite fold_lap_norm.
do 2 rewrite Nat.sub_0_r.
clear c lc b lb Hlc Hd.
rename d into lb.
rewrite (lap_convol_mul_more (length la - length (lap_norm la))). 2: {
  now cbn; rewrite Nat.sub_0_r.
}
rewrite (Nat.add_comm _ (length lb)).
rewrite <- Nat.add_assoc.
rewrite Nat.add_sub_assoc; [ | apply lap_norm_length_le ].
rewrite (Nat.add_comm _ (length la)).
rewrite Nat.add_sub.
rewrite Nat.add_comm.
apply lap_norm_cons_norm.
now cbn; rewrite Nat.sub_0_r.
...
intros.
unfold norm_list_as_polyn; f_equal.
revert la.
induction lb as [| b]; intros. {
  do 2 rewrite polyn_list_add_0_r.
  now rewrite rev_involutive, strip_0s_idemp.
}
cbn.
destruct la as [| a]; [ easy | cbn ].
do 2 rewrite strip_0s_app; cbn.
rewrite <- IHlb.
remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  destruct (srng_eq_dec a 0) as [Haz| Haz]. {
    subst a; rewrite srng_add_0_l; cbn.
    now rewrite strip_0s_app.
  }
  cbn.
  now rewrite strip_0s_app.
}
cbn.
rewrite rev_app_distr; cbn.
now rewrite strip_0s_app.
Qed.
...

Theorem norm_list_as_polyn_mul_idemp_r : ∀ la lb,
  norm_list_as_polyn (polyn_list_mul la (norm_list_as_polyn lb)) =
  norm_list_as_polyn (polyn_list_mul la lb).
Proof.
intros.
rewrite polyn_list_mul_comm.
rewrite norm_list_as_polyn_mul_idemp_l.
now rewrite polyn_list_mul_comm.
Qed.

Theorem polyn_of_list_mul_1_l : ∀ la,
  polyn_list_mul (polyn_list 1%P) la = la.
Proof.
intros.
cbn - [ seq ].
destruct (srng_eq_dec 1 0) as [H| H]; [ now apply srng_1_neq_0 in H | ].
cbn - [ seq ]; clear H.
unfold polyn_list_mul.
unfold length at 1.
rewrite (Nat.add_comm 1), Nat.add_sub.
replace (map _ _) with (map (λ i, nth i la 0%Srng) (seq 0 (length la))). 2: {
  apply map_ext_in.
  intros j Hj.
  apply in_seq in Hj.
  unfold so.
  rewrite srng_summation_split_first; [ | easy ].
  unfold nth at 2.
  rewrite srng_mul_1_l, Nat.sub_0_r.
  rewrite all_0_srng_summation_0; [ now rewrite srng_add_0_r | ].
  intros i Hi.
  destruct i; [ flia Hi | ].
  now destruct i; cbn; rewrite srng_mul_0_l.
}
induction la as [| a]; [ easy | ].
cbn - [ nth seq ].
rewrite <- Nat.add_1_l.
rewrite seq_app.
rewrite map_app.
rewrite Nat.add_0_l.
remember (map _ (seq 0 1)) as x; cbn in Heqx; subst x.
rewrite <- List_cons_app; f_equal.
rewrite <- seq_shift.
now rewrite map_map.
Qed.

Theorem polyn_mul_1_l : ∀ P, (1 * P)%P = P.
Proof.
intros.
unfold polyn_mul.
rewrite polyn_of_list_mul_1_l.
apply polyn_eq; cbn.
unfold norm_list_as_polyn.
destruct P as (la, Hla); cbn.
unfold polyn_prop_test in Hla.
destruct la as [| a]; [ easy | ].
cbn - [ nth ] in Hla.
destruct (srng_eq_dec (nth (length la) (a :: la) 0%Srng) 0)
  as [Hz| Hz]; [ easy | ].
symmetry; apply List_eq_rev_l; symmetry.
clear Hla.
remember (rev (a :: la)) as lb eqn:Hlb.
symmetry in Hlb.
apply List_eq_rev_l in Hlb.
rewrite Hlb in Hz.
Search (nth _ (rev _)).
apply (f_equal length) in Hlb.
cbn in Hlb; rewrite rev_length in Hlb.
rewrite rev_nth in Hz; [ | flia Hlb ].
rewrite <- Hlb, Nat.sub_diag in Hz.
clear Hlb.
induction lb as [| b]; [ easy | ].
cbn in Hz |-*.
now destruct (srng_eq_dec b 0).
Qed.

Theorem polyn_mul_add_distr_l : ∀ P Q R, (P * (Q + R) = P * Q + P * R)%P.
Proof.
intros.
unfold polyn_mul.
apply polyn_eq.
cbn - [ polyn_list_add ].
rewrite norm_list_as_polyn_mul_idemp_r.
rewrite norm_list_as_polyn_add_idemp_l.
rewrite norm_list_as_polyn_add_idemp_r.
f_equal.
...
rewrite fold_lap_norm.
rewrite lap_mul_norm_idemp_r.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_norm_idemp_r.
now rewrite lap_mul_add_distr_l.
...
apply polyn_eq; cbn. {
  remember (polyn_deg_ub P) as pd eqn:Hpd.
  remember (polyn_deg_ub Q) as qd eqn:Hqd.
  remember (polyn_deg_ub R) as rd eqn:Hrd.
  move qd before pd; move rd before qd.
  rewrite <- Nat.add_max_distr_l.
  now rewrite Nat.sub_max_distr_r.
} {
  unfold polyn_coeff.
  unfold polyn_add, polyn_mul.
  unfold polyn_coeff.
  remember (polyn_deg_ub P) as pd eqn:Hpd.
  remember (polyn_deg_ub Q) as qd eqn:Hqd.
  remember (polyn_deg_ub R) as rd eqn:Hrd.
  move qd before pd; move rd before qd.
  intros i Hi; cbn.
  do 3 rewrite srng_add_0_l.
  rewrite Nat.sub_0_r; cbn.
  destruct (lt_dec i (pd + qd - 1)) as [Hipq| Hipq]. {
    unfold so.
    rewrite fold_left_srng_add_fun_from_0; symmetry.
    rewrite fold_left_srng_add_fun_from_0.
    rewrite srng_add_add_swap.
    rewrite fold_left_srng_add_fun_from_0.
    destruct (lt_dec i (pd + rd - 1)) as [Hipr| Hipr]. {
      rewrite srng_add_assoc.
      rewrite <- srng_add_assoc.
      f_equal. {
        rewrite <- srng_mul_add_distr_l.
        f_equal.
        destruct (lt_dec i (max qd rd)) as [Hiqr| Hiqr]; [ easy | ].
        destruct (lt_dec i qd) as [Hiq| Hiq]. {
          exfalso; apply Hiqr.
          now apply Nat.max_lt_iff; left.
        }
        destruct (lt_dec i rd) as [Hir| Hir]. {
          exfalso; apply Hiqr.
          now apply Nat.max_lt_iff; right.
        }
        apply srng_add_0_l.
      }
      destruct (zerop i) as [Hzi| Hzi]. {
        subst i; cbn.
        apply srng_add_0_l.
      }
      remember (seq 1 i) as s eqn:Hs.
      replace i with (S i - 1) in Hs by flia Hzi; subst s.
      rewrite <- srng_summation_add_distr.
      apply srng_summation_eq_compat.
      intros j Hj.
      rewrite <- srng_mul_add_distr_l.
      f_equal.
      rewrite srng_add_comm.
      destruct (lt_dec (i - j) (max qd rd)) as [Hijqr| Hijqr]; [ easy | ].
      destruct (lt_dec (i - j) qd) as [Hijq| Hijq]. {
        exfalso; apply Hijqr.
        now apply Nat.max_lt_iff; left.
      }
      destruct (lt_dec (i - j) rd) as [Hijr| Hijr]. {
        exfalso; apply Hijqr.
        now apply Nat.max_lt_iff; right.
      }
      apply srng_add_0_l.
    }
    f_equal. {
      rewrite srng_add_0_r.
      destruct (lt_dec 0 pd) as [Hzp| Hzp]. 2: {
        now do 2 rewrite srng_mul_0_l.
      }
      f_equal.
      destruct (lt_dec i (max qd rd)) as [Hiqr| Hiqr]. {
        destruct (lt_dec i qd) as [Hiq| Hiq]. 2: {
          destruct (lt_dec i rd) as [Hir| Hir]. 2: {
            symmetry; apply srng_add_0_l.
          }
          flia Hipq Hipr Hiqr Hiq.
        } {
          destruct (lt_dec i rd) as [Hir| Hir]. 2: {
            symmetry; apply srng_add_0_r.
          }
          clear Hiqr.
          flia Hi Hipq Hipr Hiq Hir Hzp.
        }
      } {
        destruct (lt_dec i qd) as [Hiq| Hiq]; [ | easy ].
        flia Hi Hipq Hipr Hzp Hiqr Hiq.
      }
    } {
      apply List_fold_left_ext_in.
      intros j c Hj.
      apply in_seq in Hj.
      f_equal.
      destruct (lt_dec j pd) as [Hjp| Hjp]. 2: {
        now do 2 rewrite srng_mul_0_l.
      }
      f_equal.
      destruct (lt_dec (i - j) qd) as [Hijq| Hijq]. 2: {
        rewrite srng_add_0_l.
        destruct (lt_dec (i - j) (max qd rd)) as [Hijqr| Hijqr]; [ | easy ].
        destruct (lt_dec (i - j) rd) as [Hijr| Hijr]; [ | easy ].
        flia Hipr Hjp Hijr.
      }
      destruct (lt_dec (i - j) (max qd rd)) as [Hijqr| Hijqr]. 2: {
        flia Hijq Hijqr.
      }
      destruct (lt_dec (i - j) rd) as [Hijr| Hijr]. 2: {
        now rewrite srng_add_0_r.
      }
      flia Hipr Hjp Hijr.
    }
  } {
    rewrite srng_add_0_l.
    destruct (lt_dec i (pd + rd - 1)) as [Hipr| Hipr]. 2: {
      flia Hi Hipq Hipr.
    }
    destruct (lt_dec 0 pd) as [Hzp| Hzp]. 2: {
      do 2 rewrite srng_mul_0_l.
      apply Nat.nlt_ge in Hzp.
      apply Nat.le_0_r in Hzp.
      move Hzp at top; subst pd.
      apply List_fold_left_ext_in.
      intros j c Hj; f_equal.
      apply in_seq in Hj.
      destruct (lt_dec j 0) as [Hjz| Hjz]; [ easy | ].
      now do 2 rewrite srng_mul_0_l.
    }
    destruct (lt_dec i (max qd rd)) as [Hiqr| Hiqr]. {
      destruct (lt_dec i rd) as [Hir| Hir]; [ | flia Hi Hipq Hiqr Hir ].
      destruct (lt_dec i qd) as [Hiq| Hiq]; [ flia Hipq Hzp Hiq | ].
      rewrite srng_add_0_l.
      apply List_fold_left_ext_in.
      intros j c Hj; f_equal; clear c.
      apply in_seq in Hj.
      destruct (lt_dec j pd) as [Hjp| Hjp]. 2: {
        now do 2 rewrite srng_mul_0_l.
      }
      f_equal.
      destruct (lt_dec (i - j) rd) as [Hijr| Hijr]; [ | flia Hir Hijr ].
      destruct (lt_dec (i - j) qd) as [Hijq| Hijq]; [ flia Hipq Hjp Hijq | ].
      rewrite srng_add_0_l.
      destruct (lt_dec (i - j) (max qd rd)) as [Hijqr| Hijqr]; [ easy | ].
      flia Hijr Hijq Hijqr.
    } {
      destruct (lt_dec i rd) as [Hir| Hir]; [ flia Hiqr Hir | ].
      rewrite srng_mul_0_r.
      apply List_fold_left_ext_in.
      intros j c Hj; f_equal; clear c.
      apply in_seq in Hj.
      destruct (lt_dec j pd) as [Hjp| Hjp]. 2: {
        now do 2 rewrite srng_mul_0_l.
      }
      f_equal.
      destruct (lt_dec (i - j) rd) as [Hijr| Hijr]. 2: {
        destruct (lt_dec (i - j) (max qd rd)) as [Hijqr| Hijqr]; [ | easy ].
        rewrite srng_add_0_r.
        destruct (lt_dec (i - j) qd) as [Hijq| Hijq]; [ | easy ].
        flia Hipq Hjp Hijq.
      }
      destruct (lt_dec (i - j) qd) as [Hijq| Hijq]; [ flia Hipq Hjp Hijq | ].
      rewrite srng_add_0_l.
      destruct (lt_dec (i - j) (max qd rd)) as [Hijqr| Hijqr]; [ easy | ].
      flia Hijr Hijq Hijqr.
    }
  }
}
Qed.

Theorem polyn_mul_0_l : ∀ P, (0 * P = 0)%P.
Proof.
intros.
apply polyn_eq. {
  cbn.
Print polyn_mul.
...

Definition polyn_semiring_prop : semiring_prop (polynomial T) :=
  {| srng_add_comm := polyn_add_comm;
     srng_add_assoc := polyn_add_assoc;
     srng_add_0_l := polyn_add_0_l;
     srng_mul_comm := polyn_mul_comm;
     srng_mul_1_l := polyn_mul_1_l;
     srng_mul_add_distr_l := polyn_mul_add_distr_l;
     srng_mul_0_l := polyn_mul_0_l |}.

...

(* degree upper bound (polyn_deg_ub) of sum of polynomials *)

Theorem polyn_deg_ub_add : ∀ P Q,
  polyn_deg_ub (P + Q)%P = max (polyn_deg_ub P) (polyn_deg_ub Q).
Proof. easy. Qed.

Theorem summation_polyn_deg_ub : ∀ f b e,
   polyn_deg_ub (Σ (i = b, e), f i)%Rng =
   fold_left max (map polyn_deg_ub (map f (seq b (S e - b)))) 0.
Proof.
intros.
cbn - [ sub ].
remember (S e - b) as len; clear e Heqlen.
revert b.
induction len; intros; [ easy | ].
rewrite List_seq_succ_r; cbn.
do 2 rewrite map_app; cbn.
do 2 rewrite fold_left_app; cbn.
now f_equal.
Qed.

(* characteristic polynomial = det(xI-M) *)

Definition charac_polyn (M : matrix T) :=
  determinant
    (mat_mul_scal_l (monom_x) (monom_mat_of_mat (mat_id (mat_nrows M))) -
     monom_mat_of_mat M)%M.

(* the higher coefficient of a characateristic polynomial is 1 *)

Theorem charac_polyn_higher_coeff : ∀ M,
  mat_nrows M ≠ 0
  → polyn_el (charac_polyn M) (mat_nrows M) = 1%Srng.
Proof.
intros * Hrz.
unfold charac_polyn.
unfold determinant.
remember (mat_nrows (_ - _)%M) as x.
cbn in Heqx; subst x.
remember (mat_nrows M) as r eqn:Hr; clear Hr.
induction r; [ easy | clear Hrz ].
cbn - [ mat_id sub polyn_ring_op ].
unfold so.
destruct r. {
  cbn.
  rewrite srng_add_0_l.
  rewrite srng_add_0_r.
  rewrite srng_mul_0_l.
  rewrite srng_add_0_l.
  now rewrite srng_mul_1_l.
}
unfold so.
Search (Σ (_ = _, _), _)%Srng.
unfold so.
...
rewrite srng_summation_split_first.
Search (Σ (_ = _, _), _)%Rng.
...
intros * Hrz.
unfold charac_polyn.
unfold determinant.
remember (mat_nrows (_ - _)%M) as x.
cbn in Heqx; subst x.
remember (mat_nrows M) as r eqn:Hr. clear Hr.
destruct r; [ easy | clear Hrz ].
cbn - [ mat_id sub polyn_ring_op ].
destruct r. {
  cbn.
  rewrite srng_add_0_l.
  rewrite srng_add_0_r.
  rewrite srng_mul_0_l.
  rewrite srng_add_0_l.
  now rewrite srng_mul_1_l.
}
destruct r. {
  cbn.
  repeat rewrite srng_add_0_l.
  repeat rewrite srng_add_0_r.
  repeat rewrite srng_mul_0_l.
  repeat rewrite srng_mul_0_r.
  progress repeat rewrite srng_add_0_l.
  progress repeat rewrite srng_add_0_r.
  progress repeat rewrite srng_mul_0_r.
  progress repeat rewrite srng_add_0_r.
  now repeat rewrite srng_mul_1_l.
}
destruct r. {
  cbn.
  repeat rewrite srng_add_0_l.
  repeat rewrite srng_add_0_r.
  repeat rewrite srng_mul_0_l.
  repeat rewrite srng_mul_0_r.
  progress repeat rewrite srng_add_0_l.
  progress repeat rewrite srng_add_0_r.
  progress repeat rewrite srng_mul_0_r.
  progress repeat rewrite srng_mul_0_l.
  progress repeat rewrite srng_add_0_r.
  now repeat rewrite srng_mul_1_l.
}
...

(* eigenvalues and eigenvectors *)

Theorem exists_eigenvalues : ∀ (acp : algeb_closed_prop) (M : matrix T),
  mat_nrows M ≠ 0
  → is_square_mat M
  → ∃ EVL, length EVL = mat_nrows M ∧
     (∀ μ V, (μ, V) ∈ EVL ↔ mat_mul_vect_r M V = vect_mul_scal_l μ V).
Proof.
intros acp M Hrz HM.
destruct acp as (Hroots).
specialize (Hroots (charac_polyn M)) as H1.
...
assert (H2 : polyn_el (charac_polyn M) (mat_nrows M) = 1%Srng). {
  now apply charac_polyn_higher_coeff.
}
assert (H3 : polyn_degree (charac_polyn M) = mat_nrows M). {
...

End in_ring.

Module bmatrix_Notations.

Declare Scope BM_scope.
Delimit Scope BM_scope with BM.

Notation "a + b" := (bmat_add a b) : BM_scope.
Notation "a - b" := (bmat_sub a b) : BM_scope.
Notation "a * b" := (bmat_mul a b) : BM_scope.
Notation "- a" := (bmat_opp a) : BM_scope.

End bmatrix_Notations.

Import bmatrix_Notations.
