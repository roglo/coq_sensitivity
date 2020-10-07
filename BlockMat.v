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

Require Import SRpolynomial.
Import polynomial_Notations.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so := rng_semiring).
Context {sp : @semiring_prop T (@rng_semiring T ro)}.
Context {rp : @ring_prop T ro}.
Context {sdp : @sring_dec_prop T so}.
Existing Instance so.
Existing Instance polyn_semiring_op.
Existing Instance polyn_ring_op.
Existing Instance polyn_semiring_prop.
Existing Instance polyn_ring_prop.

(* convertion matrix → matrix with monomials *)

Definition monom_mat_of_mat M : matrix (polynomial T) :=
  mk_mat (λ i j, polyn_of_list [mat_el M i j])
    (mat_nrows M) (mat_ncols M).

(* identity matrix of size n *)

Definition mat_id n : matrix T :=
  mk_mat (λ i j, if Nat.eq_dec i j then 1%Srng else 0%Srng) n n.

(* characteristic polynomial = det(xI-M) *)

Definition charac_polyn (M : matrix T) :=
  determinant
    (mat_mul_scal_l (_x) (monom_mat_of_mat (mat_id (mat_nrows M))) -
     monom_mat_of_mat M)%M.

(* monic polynomial: polynomial whose leading coefficient is 1 *)
(* to be moved to SRpolynomial.v *)

Definition is_monic_polyn P := polyn_coeff P (polyn_degree P) = 1%Srng.
Arguments is_monic_polyn P%P.

Theorem polyn_x_minus_is_monic : ∀ a,
  polyn_degree a = 0
  → is_monic_polyn (_x - a).
Proof.
intros * Ha.
unfold polyn_degree in Ha; cbn in Ha.
unfold polyn_degree_plus_1 in Ha; cbn in Ha.
apply Nat.sub_0_le in Ha.
destruct a as (la, Hla).
cbn in Ha |-*.
destruct la as [| a]. {
  unfold is_monic_polyn; cbn.
  destruct (srng_eq_dec 1 0) as [H| H]; [ now apply srng_1_neq_0 in H | cbn ].
  clear H.
  destruct (srng_eq_dec 1 0) as [H| H]; [ now apply srng_1_neq_0 in H | cbn ].
  easy.
}
destruct la; [ | cbn in Ha; flia Ha ].
cbn in Hla.
unfold is_monic_polyn; cbn.
destruct (srng_eq_dec 1 0) as [H| H]; [ now apply srng_1_neq_0 in H | cbn ].
clear H.
destruct (srng_eq_dec 1 0) as [H| H]; [ now apply srng_1_neq_0 in H | ].
easy.
Qed.

Theorem norm_polyn_list_id : ∀ la,
  last la 0%Srng ≠ 0%Srng
  → norm_polyn_list la = la.
Proof.
intros * Hla.
unfold norm_polyn_list; f_equal.
apply List_eq_rev_r.
remember (rev la) as lb eqn:Hlb.
apply List_eq_rev_r in Hlb; subst la.
rename lb into la.
rewrite List_rev_last in Hla.
destruct la as [| a]; [ easy | ].
cbn in Hla |-*.
now destruct (srng_eq_dec a 0).
Qed.

Theorem norm_polyn_list_app_last_nz : ∀ la lb,
  last lb 0%Srng ≠ 0%Srng
  → norm_polyn_list (la ++ lb) = la ++ norm_polyn_list lb.
Proof.
intros * Hlb.
revert lb Hlb.
induction la as [| a]; intros; [ easy | ].
cbn - [ norm_polyn_list ].
rewrite List_cons_app.
rewrite norm_polyn_list_app.
rewrite IHla; [ | easy ].
destruct lb as [| b]; [ easy | ].
destruct la as [| a1]; [ | easy ].
cbn - [ norm_polyn_list ].
remember (norm_polyn_list (b :: lb)) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]; [ | easy ].
exfalso; apply Hlb; clear Hlb.
clear IHla.
revert b Hlc.
induction lb as [| b1]; intros. {
  cbn in Hlc.
  now destruct (srng_eq_dec b 0%Rng).
}
rewrite List_last_cons_cons.
apply IHlb.
cbn in Hlc |-*.
apply List_eq_rev_l in Hlc.
apply List_eq_rev_r.
rewrite strip_0s_app in Hlc.
remember (strip_0s (rev lb ++ [b1])) as ld eqn:Hld.
symmetry in Hld.
now destruct ld.
Qed.

Theorem norm_polyn_list_cons : ∀ a la,
  last la 0%Srng ≠ 0%Srng
  → norm_polyn_list (a :: la) = a :: norm_polyn_list la.
Proof.
intros * Hla.
now specialize (norm_polyn_list_app_last_nz [a] la Hla) as H.
Qed.

Theorem polyn_degree_sum : ∀ P Q,
  polyn_degree Q < polyn_degree P
  → polyn_degree (P + Q) = polyn_degree P.
Proof.
intros * Hdeg.
unfold polyn_degree in Hdeg |-*.
unfold polyn_degree_plus_1 in Hdeg |-*.
f_equal.
destruct P as (la, Hla).
destruct Q as (lb, Hlb).
move lb before la.
cbn - [ norm_polyn_list ] in Hdeg |-*.
unfold polyn_prop_test in Hla, Hlb.
destruct la as [| a]; [ easy | ].
cbn - [ nth ] in Hla.
destruct (srng_eq_dec (nth (length la) (a :: la) 0%Srng) 0) as [Haz| Haz]. {
  easy.
}
clear Hla.
destruct lb as [| b]. {
  rewrite polyn_list_add_0_r.
  rewrite norm_polyn_list_id; [ easy | ].
  now rewrite List_last_nth_cons.
}
cbn - [ nth ] in Hlb.
destruct (srng_eq_dec (nth (length lb) (b :: lb) 0%Srng) 0) as [Hbz| Hbz]. {
  easy.
}
clear Hlb.
cbn in Hdeg.
do 2 rewrite Nat.sub_0_r in Hdeg.
rewrite <- List_last_nth_cons in Haz.
rewrite <- List_last_nth_cons in Hbz.
cbn - [ norm_polyn_list ].
revert a b lb Haz Hbz Hdeg.
induction la as [| a1]; intros; [ easy | ].
destruct lb as [| b1]. {
  cbn - [ norm_polyn_list ].
  now rewrite norm_polyn_list_id.
}
cbn - [ norm_polyn_list ].
cbn in Hdeg.
apply Nat.succ_lt_mono in Hdeg.
rewrite List_last_cons_cons in Haz, Hbz.
specialize (IHla a1 b1 lb Haz Hbz Hdeg).
rewrite norm_polyn_list_cons. {
  cbn - [ norm_polyn_list ].
  now rewrite IHla.
}
clear - so Haz Hdeg.
revert lb a1 b1 Haz Hdeg.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
remember (a :: la) as x; cbn in Haz; subst x.
cbn in Hdeg.
apply Nat.succ_lt_mono in Hdeg.
now apply IHla.
Qed.

Theorem is_monic_polyn_sum : ∀ P Q,
  polyn_degree Q < polyn_degree P
  → is_monic_polyn P
  → is_monic_polyn (P + Q).
Proof.
intros * Hdeg HP.
unfold is_monic_polyn in HP |-*.
rewrite polyn_degree_sum; [ | easy ].
cbn in HP |-*.
destruct P as (la, Hla).
destruct Q as (lb, Hlb).
move lb before la.
cbn in Hla, Hlb, Hdeg, HP.
cbn - [ norm_polyn_list ].
destruct la as [| a]; [ easy | ].
cbn - [ nth ] in HP.
cbn - [ norm_polyn_list "+"%PL ].
rewrite Nat.sub_0_r in HP |-*.
destruct lb as [| b]. {
  rewrite polyn_list_add_0_r.
  rewrite norm_polyn_list_id; [ easy | ].
  rewrite List_last_nth_cons, HP.
  apply srng_1_neq_0.
}
cbn in Hdeg.
do 2 rewrite Nat.sub_0_r in Hdeg.
rewrite <- List_last_nth_cons in HP.
clear - Hdeg HP.
move b before a.
revert a b lb Hdeg HP.
induction la as [| a1]; intros; [ easy | ].
rewrite List_last_cons_cons in HP.
destruct lb as [| b1]. {
  cbn - [ norm_polyn_list ].
  rewrite norm_polyn_list_id. 2: {
    remember (a1 :: la) as l; cbn; subst l.
    rewrite HP.
    apply srng_1_neq_0.
  }
  remember (a1 :: la) as l; cbn; subst l.
  now rewrite List_last_nth_cons in HP.
}
cbn - [ norm_polyn_list ].
cbn in Hdeg.
apply Nat.succ_lt_mono in Hdeg.
specialize (IHla a1 b1 lb Hdeg HP).
rewrite norm_polyn_list_cons; [ easy | ].
clear - so sdp HP Hdeg.
revert lb a1 b1 HP Hdeg.
induction la as [| a]; intros; [ easy | cbn ].
rewrite List_last_cons_cons in HP.
destruct lb as [| b]. {
  rewrite HP.
  apply srng_1_neq_0.
}
cbn in Hdeg.
apply Nat.succ_lt_mono in Hdeg.
now apply IHla.
Qed.

Theorem polyn_list_add_map : ∀ A f g (l : list A),
  (map f l + map g l)%PL = (map (λ i, (f i + g i)%Rng) l).
Proof.
intros A *.
induction l as [| a la]; [ easy | ].
now cbn; rewrite IHla.
Qed.

Theorem polyn_list_add_repeat_0_r : ∀ la n,
  (la + repeat 0%Srng n)%PL = la ++ repeat 0%Srng (n - length la).
Proof.
intros.
revert n.
induction la as [| a]; intros. {
  now cbn; rewrite Nat.sub_0_r.
}
destruct n. {
  now cbn; rewrite app_nil_r.
}
cbn; rewrite srng_add_0_r; f_equal.
apply IHla.
Qed.

Theorem polyn_degree_prod : ∀ P Q,
  (polyn_coeff P (polyn_degree P) * polyn_coeff Q (polyn_degree Q) ≠ 0)%Srng
  → polyn_degree (P * Q) = polyn_degree P + polyn_degree Q.
Proof.
intros * HPQ.
unfold polyn_degree; cbn.
unfold polyn_degree_plus_1.
destruct P as (la, Hla).
destruct Q as (lb, Hlb).
move lb before la.
cbn - [ norm_polyn_list polyn_list_mul ].
cbn in HPQ.
do 2 rewrite <- List_last_nth in HPQ.
clear Hla Hlb.
destruct la as [| a]. {
  exfalso; apply HPQ; cbn.
  apply srng_mul_0_l.
}
destruct lb as [| b]. {
  exfalso; apply HPQ; cbn.
  apply srng_mul_0_r.
}
cbn - [ norm_polyn_list "*"%PL "+"%PL ].
do 2 rewrite Nat.sub_0_r.
destruct (srng_eq_dec (nth (length la) (a :: la) 0%Rng) 0) as [Haz| Haz]. {
  rewrite <- List_last_nth_cons in Haz.
  now rewrite Haz, srng_mul_0_l in HPQ.
}
destruct (srng_eq_dec (nth (length lb) (b :: lb) 0%Rng) 0) as [Hbz| Hbz]. {
  rewrite <- List_last_nth_cons in Hbz.
  now rewrite Hbz, srng_mul_0_r in HPQ.
}
move b before a.
rewrite <- List_last_nth_cons in Haz, Hbz.
(**)
rewrite norm_polyn_list_id. 2: {
  rewrite List_last_nth.
  cbn; rewrite map_length, seq_length, Nat.sub_0_r.
  rewrite Nat.add_succ_r, Nat.sub_succ, Nat.sub_0_r.
  rewrite (List_map_nth_in _ 0); [ | rewrite seq_length; flia ].
  rewrite seq_nth; [ | flia ].
  rewrite Nat.add_0_l.
  unfold polyn_list_convol_mul.
Print polyn_list_mul.
(* oups, mais en fait, c'est faux, ma définition de polyn_list_mul ! *)
...
revert a b lb HPQ Haz Hbz.
induction la as [| a1]; intros. {
  remember (b :: lb) as lc.
  cbn in HPQ, Haz.
  cbn - [ norm_polyn_list ].
  rewrite Nat.sub_0_r; subst lc.
  rewrite List_length_cons.
  rewrite map_polyn_list_convol_mul_cons_l.
  erewrite (map_ext_in (λ x, polyn_list_convol_mul _ _ _)). 2: {
    intros i Hi.
    apply in_seq in Hi.
    unfold polyn_list_convol_mul.
    rewrite srng_summation_split_first; [ | flia Hi ].
    rewrite Nat.sub_0_r.
    rewrite <- List_hd_nth_0; unfold hd.
    rewrite srng_mul_0_l, srng_add_0_l.
    rewrite all_0_srng_summation_0. 2: {
      intros j Hj.
      rewrite nth_overflow; [ | cbn; flia ].
      apply srng_mul_0_l.
    }
    easy.
  }
  replace (0%Rng :: _) with (repeat 0%Rng (S (length lb))). 2: {
    clear; cbn; f_equal.
    remember 1 as n eqn:Hn; clear Hn.
    revert n.
    induction lb as [| b]; intros; [ easy | ].
    cbn; f_equal.
    apply IHlb.
  }
  rewrite polyn_list_add_repeat_0_r.
  rewrite map_length, seq_length, Nat.sub_diag.
  rewrite app_nil_r.
  rewrite norm_polyn_list_id. 2: {
    rewrite List_last_nth.
    rewrite map_length, seq_length, Nat.sub_succ, Nat.sub_0_r.
    rewrite (List_map_nth_in _ 0); [ | rewrite seq_length; flia ].
    rewrite seq_nth; [ | flia ].
    rewrite Nat.add_0_l.
    now rewrite <- List_last_nth_cons.
  }
  rewrite map_length, seq_length.
  now cbn; rewrite Nat.sub_0_r.
}
rewrite List_last_cons_cons in HPQ, Haz.
specialize (IHla _ _ _ HPQ Haz Hbz).
rewrite norm_polyn_list_id.
...
(**)
rewrite map_polyn_list_convol_mul_cons_l.
rewrite <- seq_shift, map_map.
erewrite (map_ext_in (λ x, polyn_list_convol_mul _ _ _)). 2: {
  intros i Hi.
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
remember (map _ _) as lc eqn:Hlc in |-*.
remember (map (polyn_list_convol_mul _ _) _) as ld eqn:Hld.
move ld before lc; cbn.
cbn - [ nth ] in Hlc.
rewrite <- seq_shift, map_map in Hlc.
unfold nth in Hlc at 1.
subst lc.
remember (map _ _) as lc eqn:Hlc in |-*.
move lc after ld; move Hlc after Hld.
cbn - [ norm_polyn_list ].
rewrite srng_add_0_r.
erewrite map_ext_in in Hlc. 2: {
  intros i Hi.
  now cbn.
}
subst lc ld.
rewrite polyn_list_add_map.
rewrite norm_polyn_list_cons. 2: {
...
... 2
remember (seq 0 (S (length la + length lb))) as lc eqn:Hlc.
replace (map _ _) with ([a] * map (λ n, nth n (b :: lb) 0%Srng) lc)%PL. 2: {
  clear - sp.
  revert a b lb.
  induction lc as [| c]; intros; [ easy | ].
  cbn - [ "*"%PL nth ].
  cbn - [ nth ].
  unfold so.
  rewrite srng_add_0_l.
  f_equal.
  rewrite map_length.
... 1
revert a b lb Haz Hbz HPQ.
induction la as [| a1]; intros. {
  cbn - [ norm_polyn_list seq ].
  cbn in Haz.
  unfold last in HPQ at 1.
  unfold polyn_list_convol_mul.
  erewrite map_ext_in. 2: {
    intros i Hi.
    apply in_seq in Hi.
    rewrite srng_summation_split_first; [ | easy ].
    rewrite Nat.sub_0_r.
    rewrite <- List_hd_nth_0; unfold hd.
    rewrite all_0_srng_summation_0. 2: {
      intros j Hj.
      rewrite nth_overflow; [ | easy ].
      apply srng_mul_0_l.
    }
    now rewrite srng_add_0_r.
  }
  revert a b Haz Hbz HPQ.
  induction lb as [| b1]; intros. {
    now cbn; destruct (srng_eq_dec (a * b) 0).
  }
  rewrite List_last_cons_cons in Hbz, HPQ.
  specialize (IHlb a b1 Haz Hbz HPQ).
  cbn - [ norm_polyn_list polyn_list_convol_mul seq nth ].
  remember (S (length lb)) as n.
  cbn - [ norm_polyn_list nth ].
  subst n.
  rewrite <- List_hd_nth_0; unfold hd.
  rewrite <- seq_shift.
  rewrite map_map.
  erewrite map_ext_in. 2: {
    intros i Hi.
    now remember (b1 :: lb) as l; cbn; subst l.
  }
  destruct lb as [| b2]. {
    cbn in Hbz, HPQ |-*.
    now destruct (srng_eq_dec (a * b1) 0).
  }
  rewrite norm_polyn_list_cons. {
    rewrite List_length_cons.
    rewrite Nat.sub_succ, Nat.sub_0_r.
    rewrite <- IHlb at 2.
    rewrite <- Nat.sub_succ_l. {
      now rewrite Nat.sub_succ, Nat.sub_0_r.
    }
    rewrite List_seq_succ_r, Nat.add_0_l.
    rewrite map_app.
    cbn - [ norm_polyn_list nth seq ].
    rewrite norm_polyn_list_app.
    remember (b2 :: lb) as l.
    cbn; subst l.
    rewrite <- List_last_nth_cons.
    rewrite List_last_cons_cons in HPQ.
    destruct (srng_eq_dec (a * last (b2 :: lb) 0%Srng) 0) as [Habz| Habz]. {
      easy.
    }
    cbn; flia.
  }
  rewrite List_last_cons_cons in Hbz, HPQ.
  cbn - [ nth seq ].
  rewrite List_seq_succ_r.
  rewrite map_app.
  cbn - [ nth seq ].
  rewrite List_last_app.
  remember (b2 :: lb) as l; cbn; subst l.
  now rewrite <- List_last_nth_cons.
}
rewrite List_last_cons_cons in Haz, HPQ.
specialize (IHla _ _ _ Haz Hbz HPQ).
rewrite map_polyn_list_convol_mul_cons_l.
rewrite <- seq_shift, map_map.
erewrite (map_ext_in (λ x, polyn_list_convol_mul _ _ _)). 2: {
  intros i Hi.
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
remember (map _ _) as lc eqn:Hc in |-*.
move IHla at bottom.
remember (map (polyn_list_convol_mul _ _) _) as ld eqn:Hld.
move ld before lc; cbn.
Search (norm_polyn_list (_ + _)).
...
cbn - [ norm_polyn_list polyn_list_convol_mul seq ].
rewrite map_polyn_list_convol_mul_comm.
rewrite map_polyn_list_convol_mul_cons_r_gen.
...
cbn - [ nth ] in HP.
cbn - [ norm_polyn_list "+"%PL ].
rewrite Nat.sub_0_r in HP |-*.
destruct lb as [| b]. {
  rewrite polyn_list_add_0_r.
  rewrite norm_polyn_list_id; [ easy | ].
  rewrite List_last_nth.
  cbn - [ nth ].
  rewrite Nat.sub_0_r, HP.
  apply srng_1_neq_0.
}
cbn in Hdeg.
do 2 rewrite Nat.sub_0_r in Hdeg.
specialize (List_last_nth (a :: la) 0%Rng) as H.
cbn - [ last nth ] in H.
rewrite Nat.sub_0_r in H.
unfold so in HP.
rewrite <- H in HP; clear H.
clear - Hdeg HP.
move b before a.
revert a b lb Hdeg HP.
induction la as [| a1]; intros; [ easy | ].
remember (a1 :: la) as l; cbn in HP; subst l.
destruct lb as [| b1]. {
  cbn - [ norm_polyn_list ].
  rewrite norm_polyn_list_id. 2: {
    remember (a1 :: la) as l; cbn; subst l.
    unfold so; rewrite HP.
    apply srng_1_neq_0.
  }
  remember (a1 :: la) as l; cbn; subst l.
  rewrite List_last_nth in HP.
  cbn - [ nth ] in HP.
  now rewrite Nat.sub_0_r in HP.
}
cbn - [ norm_polyn_list ].
cbn in Hdeg.
apply Nat.succ_lt_mono in Hdeg.
specialize (IHla a1 b1 lb Hdeg HP).
rewrite norm_polyn_list_cons; [ easy | ].
clear - so sdp HP Hdeg.
revert lb a1 b1 HP Hdeg.
induction la as [| a]; intros; [ easy | cbn ].
remember (a :: la) as l; cbn in HP; subst l.
destruct lb as [| b]. {
  unfold so; rewrite HP.
  apply srng_1_neq_0.
}
cbn in Hdeg.
apply Nat.succ_lt_mono in Hdeg.
now apply IHla.
Qed.
...

(* the caracteristic polynomial of a matrix is monic, i.e. its
   leading coefficient is 1 *)

Theorem charac_polyn_is_monic : ∀ M,
  mat_nrows M ≠ 0
  → is_monic_polyn (charac_polyn M).
Proof.
intros * Hrz.
unfold charac_polyn.
unfold determinant; cbn.
remember (mat_nrows M) as r eqn:Hr; symmetry in Hr.
destruct r; [ easy | clear Hrz ].
remember
  (mat_mul_scal_l _x (monom_mat_of_mat (mat_id (S r))) - monom_mat_of_mat M)%M
  as PM eqn:HPM.
revert M PM Hr HPM.
induction r; intros. {
  subst PM; cbn; unfold so.
  rewrite polyn_mul_1_r.
  rewrite fold_polyn_sub.
  apply polyn_x_minus_is_monic.
  now cbn; destruct (srng_eq_dec (mat_el M 0 0) 0).
}
remember (S r) as sr.
cbn - [ "-" ]; subst sr.
rewrite srng_summation_split_first; [ | flia ].
cbn - [ sub det_loop ].
unfold minus_one_pow at 1.
cbn - [ sub det_loop ].
rewrite Nat.sub_diag, polyn_mul_1_l.
remember (mat_el PM 0 0) as x_a eqn:Hxa.
rewrite HPM in Hxa; cbn in Hxa.
unfold so in Hxa.
rewrite srng_mul_1_r in Hxa.
rewrite fold_polyn_sub in Hxa.
apply is_monic_polyn_sum. {
...
rewrite polyn_degree_prod.
...
intros * Hrz.
unfold charac_polyn.
unfold determinant; cbn.
remember (mat_nrows M) as r eqn:Hr; symmetry in Hr.
revert M Hr.
induction r; intros; [ easy | clear Hrz ].
cbn - [ summation mat_mul_scal_l ].
Print det_loop.
remember (mat_mul_scal_l _x (monom_mat_of_mat (mat_id (S r))) - monom_mat_of_mat M)%M as d eqn:Hd.
cbn - [ nth seq sub ].
...
rewrite fold_summation.
cbn - [ nth seq sub mat_mul_scal_l ].
...
destruct r. {
  unfold so.
  rewrite polyn_mul_1_r.
  rewrite fold_polyn_sub.
  apply polyn_x_minus_is_monic.
  now cbn; destruct (srng_eq_dec (mat_el M 0 0) 0).
}
destruct r. {
  cbn.
  rewrite polyn_add_0_l.
  rewrite polyn_mul_1_l.
  unfold so.
  rewrite polyn_mul_1_r.
  assert (H : polyn_of_list [0%Rng] = 0%P). {
    apply polyn_eq; cbn.
    now destruct (srng_eq_dec 0 0).
  }
  rewrite H.
  rewrite polyn_mul_0_r.
  do 2 rewrite polyn_add_0_l.
  rewrite rng_mul_opp_opp; cbn.
  rewrite srng_mul_1_l.
  rewrite rng_mul_opp_r; cbn.
  do 3 rewrite fold_polyn_sub; cbn.
(* ouais, ça marche, mais, bon *)
...
intros * Hrz.
specialize (polyn_prop (charac_polyn M)) as H1.
unfold polyn_prop_test in H1.
unfold charac_polyn in H1.
...
intros * Hrz.
unfold charac_polyn.
unfold determinant.
remember (mat_nrows (_ - _)%M) as x.
cbn in Heqx; subst x.
remember (mat_nrows M) as r eqn:Hr; symmetry in Hr.
revert M Hr.
induction r; intros; [ easy | clear Hrz ].
cbn - [ mat_id sub polyn_ring_op ].
rewrite fold_rng_sub.
destruct r. {
  cbn.
  do 2 rewrite rev_length.
  destruct (srng_eq_dec 1 0) as [H| H]; [ now apply srng_1_neq_0 in H | ].
  clear H; cbn.
  do 2 rewrite srng_add_0_l.
  do 2 rewrite srng_mul_0_l.
  rewrite srng_add_0_l.
  rewrite srng_mul_1_l.
  destruct (srng_eq_dec 1 0) as [H| H]; [ | clear H ]. {
    now apply srng_1_neq_0 in H.
  }
  destruct (srng_eq_dec (mat_el M 0 0)) as [Hmz| Hmz]. {
    cbn.
    destruct (srng_eq_dec 1 0) as [H| H]; [ | easy ].
    now apply srng_1_neq_0 in H.
  } {
    cbn.
    destruct (srng_eq_dec 1 0) as [H| H]; [ | easy ].
    now apply srng_1_neq_0 in H.
  }
}
specialize (IHr (Nat.neq_succ_0 _)).
destruct r. {
  cbn - [ norm_polyn_list ].
  rewrite map_length.
  cbn.
  destruct (srng_eq_dec 1 0) as [H| H]; [ now apply srng_1_neq_0 in H | ].
  clear H; cbn.
  repeat rewrite srng_add_0_l.
  repeat rewrite srng_add_0_r.
  repeat rewrite srng_mul_0_l.
  repeat rewrite srng_mul_0_r.
  repeat rewrite srng_mul_1_l.
  repeat rewrite srng_mul_1_r.
  repeat rewrite srng_add_0_l.
  repeat rewrite srng_add_0_r.
  repeat rewrite srng_mul_0_l.
  repeat rewrite srng_mul_0_r.
  repeat rewrite srng_mul_1_l.
  repeat rewrite srng_mul_1_r.
  destruct (srng_eq_dec 0 0) as [H| H]; [ clear H; cbn | easy ].
  destruct (srng_eq_dec 0 0) as [H| H]; [ clear H; cbn | easy ].
  destruct (srng_eq_dec 1 0) as [H| H]; [ now apply srng_1_neq_0 in H | ].
  clear H; cbn.
(* ouais, bon, c'est l'enfer *)
...
  polyn_coeff
    (Σ (j = 0, 1),
     minus_one_pow j * (_x * polyn_of_list [mat_el (mat_id 2) 0 j] + - polyn_of_list [mat_el M 0 j]) *
     det_loop (submatrix (mat_mul_scal_l _x (monom_mat_of_mat (mat_id 2)) - monom_mat_of_mat M)%M 0 j) 1)%Rng 2 =
  1%Srng
...
Print det_loop.
About _x.
Print mat_id.
Print submatrix.
remember (Σ (j = _, _), _)%Srng as x.
Print mat_mul_scal_l.
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

(* the list of coefficients of the characteristic polynomial of a matrix M
   has length "nrows(M) + 1"
   e.g. matrix
        (a b)
        (c d)
   characteristic polynomial = determinant of
        (x-a -b )
        (-c  x-d)
   which is
        (x-a)(x-d)-cb = x²-(a+d)x+(ad-bc)
   list of its coefficients
        [ad-bc; -(a+d); 1]
   whose length is 3 = nrows(M)+1
 *)

Theorem charac_polyn_list_length : ∀ M,
  length (polyn_list (charac_polyn M)) = mat_nrows M + 1.
Proof.
intros.
cbn.
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
