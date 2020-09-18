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

Fixpoint concat_list_in_list T (ll1 ll2 : list (list T)) :=
  match ll1 with
  | [] => ll2
  | l1 :: ll1' =>
       match ll2 with
       | [] => ll1
       | l2 :: ll2' => app l1 l2 :: concat_list_in_list ll1' ll2'
       end
  end.

Definition concat_list_list_list T (lll : list (list (list T))) :=
  fold_left (@concat_list_in_list T) lll [].

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

Definition mat_add (add : T → T → T) (M1 M2 : matrix T) : matrix T :=
  {| mat_el i j := add (mat_el M1 i j) (mat_el M2 i j);
     mat_nrows := mat_nrows M1;
     mat_ncols := mat_ncols M1 |}.

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
  {| mat_el i k := (Σ (j = 0, mat_ncols MA), mat_el MA i j * mat_el MB j k)%Srng;
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

Theorem square_bmat_loop_zero_like : ∀ BM sizes,
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
now apply square_bmat_loop_zero_like.
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

(*
Theorem bmat_zero_like_mul_distr_r :
  ∀ BMA BMB,
  compatible_square_bmatrices [BMA; BMB]
  → bmat_zero_like (BMA * BMB)%BM = (BMA * bmat_zero_like BMB)%BM.
Proof.
intros * Hcsb.
revert BMB Hcsb.
induction BMA as [xa| ma IHBMA] using bmatrix_ind2; intros; cbn. {
  destruct BMB as [xb| mb]; [ cbn | easy ].
  now rewrite srng_mul_0_r.
}
destruct BMB as [xb| mb]; [ easy | ].
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
destruct Hcsb as (sizes & Hsq & Hsz).
specialize (Hsq _ (or_introl eq_refl)) as Ha.
specialize (Hsq _ (or_intror (or_introl eq_refl))) as Hb.
specialize (Hsz _ (or_introl eq_refl)) as Has.
specialize (Hsz _ (or_intror (or_introl eq_refl))) as Hbs.
clear Hsq Hsz.
destruct ma as (fa, ra, ca).
destruct mb as (fb, rb, cb).
cbn in *.
destruct (zerop ra) as [Hraz| Hraz]; [ easy | ].
destruct (zerop ca) as [Hcaz| Hcaz]; [ easy | ].
destruct (zerop rb) as [Hrbz| Hrbz]; [ easy | ].
destruct (zerop cb) as [Hcbz| Hcbz]; [ easy | ].
cbn in Ha, Has, Hb, Hbs.
destruct Ha as (_ & H & Ha); subst ca.
destruct Hb as (_ & H & Hb); subst cb.
rewrite <- Has in Hbs.
injection Hbs; clear Hbs; intros Hab H; subst rb.
clear Hraz Hcaz Hcbz Hrbz.
destruct ra; [ easy | cbn ].
rewrite Nat.sub_0_r.
destruct sizes as [| size]; [ easy | ].
injection Has; clear Has; intros Has H.
clear size H.
replace
  (fold_left (λ a k, a + fa i (k + 1)%nat * bmat_zero_like (fb (k + 1)%nat j))
     (seq 0 ra) (fa i 0 * bmat_zero_like (fb 0 j)))%BM
with
  (fold_left (λ a k, a + bmat_zero_like (fa i (k + 1)%nat * fb (k + 1)%nat j))
     (seq 0 ra) (bmat_zero_like (fa i 0 * fb 0 j)))%BM. 2: {
  rewrite <- IHBMA; [ | easy | flia | ]. 2: {
    exists sizes.
    split; intros BM HBM. {
      destruct HBM as [HBM| HBM]; [ subst BM | ]. {
        unfold is_square_bmat.
        rewrite (@sizes_of_bmatrix_at_0_0 _ (S ra)); [ | easy | easy | flia ].
        apply Ha; [ easy | flia ].
      } {
        destruct HBM as [HBM| HBM]; [ subst BM | easy ].
        unfold is_square_bmat.
        rewrite (@sizes_of_bmatrix_at_0_0 _ (S ra)); [ | easy | flia | easy ].
        apply Hb; [ flia | easy ].
      }
    } {
      destruct HBM as [HBM| HBM]; [ subst BM | ]. {
        rewrite (@sizes_of_bmatrix_at_0_0 _ (S ra)); [ | | | flia ]; easy.
      } {
        destruct HBM as [HBM| HBM]; [ subst BM | easy ].
        rewrite (@sizes_of_bmatrix_at_0_0 _ (S ra));
          [ congruence | easy | flia | easy ].
      }
    }
  }
  apply List_fold_left_ext_in.
  intros k BM Hk; f_equal.
  apply in_seq in Hk.
  clear BM.
  apply IHBMA; [ easy | flia Hk | ].
  exists sizes.
  split; intros BM HBM. {
    destruct HBM as [HBM| HBM]; [ subst BM | ]. {
      unfold is_square_bmat.
      rewrite (@sizes_of_bmatrix_at_0_0 _ (S ra));
        [ | easy | easy | flia Hk ].
        apply Ha; [ easy | flia Hk ].
      } {
        destruct HBM as [HBM| HBM]; [ subst BM | easy ].
        unfold is_square_bmat.
        rewrite (@sizes_of_bmatrix_at_0_0 _ (S ra));
          [ | easy | flia Hk | easy ].
        apply Hb; [ flia Hk | easy ].
      }
    } {
      destruct HBM as [HBM| HBM]; [ subst BM | ]. {
        rewrite (@sizes_of_bmatrix_at_0_0 _ (S ra));
          [ easy | easy | easy | flia Hk ].
      } {
        destruct HBM as [HBM| HBM]; [ subst BM | easy ].
        rewrite (@sizes_of_bmatrix_at_0_0 _ (S ra));
          [ congruence | easy | flia Hk | easy ].
      }
  }
}
clear IHBMA.
clear Hi Hj.
induction ra; [ easy | ].
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite fold_left_app; cbn.
rewrite bmat_zero_like_add_distr.
f_equal.
apply IHra. {
  intros i1 j1 Hi1 Hj1.
  apply Ha; [ flia Hi1 | flia Hj1 ].
} {
  intros i1 j1 Hi1 Hj1.
  apply Hb; [ flia Hi1 | flia Hj1 ].
}
Qed.
*)

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

Theorem square_bmat_fit_for_add : ∀ sizes (MA MB : bmatrix T),
  is_square_bmat_loop sizes MA
  → is_square_bmat_loop sizes MB
  → bmat_fit_for_add MA MB.
Proof.
intros * Ha Hb.
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
Qed.

Theorem bmat_add_0_l : ∀ BM,
  is_square_bmat BM
  → (bmat_zero_like BM + BM)%BM = BM.
Proof.
intros * Hss.
induction BM as [x| M IHBM] using bmatrix_ind2. {
  now cbn; rewrite srng_add_0_l.
}
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
apply IHBM; [ easy | easy | ].
cbn in Hss.
unfold is_square_bmat.
destruct (zerop (mat_nrows M)) as [H| H]; [ flia Hi H | cbn in Hss; clear H ].
destruct (zerop (mat_ncols M)) as [H| H]; [ flia Hj H | cbn in Hss; clear H ].
destruct Hss as (_ & Hcr & Hss).
erewrite sizes_of_bmatrix_mat_el; [ | | easy | easy ]. {
  rewrite Hcr in Hj.
  now apply Hss.
} {
  cbn; rewrite Hcr.
  destruct (zerop (mat_nrows M)) as [H| H]; [ flia Hi H | cbn; clear H ].
  split; [ easy | ].
  split; [ easy | ].
  clear i j Hi Hj.
  intros i j Hi Hj.
  now apply Hss.
}
Qed.

Theorem bmat_add_0_r : ∀ BM,
  is_square_bmat BM
  → (BM + bmat_zero_like BM)%BM = BM.
Proof.
intros * Hss.
rewrite bmat_add_comm. 2: {
  apply square_bmat_fit_for_add with (sizes := sizes_of_bmatrix BM); [ easy | ].
  rewrite <- sizes_of_bmat_zero_like.
  now apply is_square_bmat_zero_like.
}
now apply bmat_add_0_l.
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
    now apply square_bmat_loop_zero_like.
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
specialize (sizes_of_bmatrix_mat_el ma Ha) as Has.
specialize (sizes_of_bmatrix_mat_el mb Hb) as Hbs.
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
induction ra; [ easy | clear Hraz ].
assert (Hsa : is_square_bmat (fa 0 0)) by (apply Ha; flia).
assert (Hsb : is_square_bmat (fb 0 0)) by (apply Hb; flia).
assert (Hssm :
  sizes_of_bmatrix (bmat_zero_like (fa 0 0)) =
  sizes_of_bmatrix (fa 0 0 * fb 0 0)%BM). {
  rewrite sizes_of_bmat_zero_like.
  symmetry.
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
assert (H6 : sizes_of_bmatrix (fa 0 ra) = sizes_of_bmatrix (fa 0 0)). {
  apply sizes_of_bmatrix_at_0_0 with (r := S ra). {
    intros i j Hi Hj.
    apply Ha; [ flia Hi | flia Hj ].
  } {
    apply Nat.lt_0_succ.
  } {
    apply Nat.lt_succ_diag_r.
  }
}
assert
  (H7 : sizes_of_bmatrix (fb ra 0) = sizes_of_bmatrix (fb 0 0)). {
  apply sizes_of_bmatrix_at_0_0 with (r := S ra). {
    intros i j Hi Hj.
    apply Hb; [ flia Hi | flia Hj ].
  } {
    apply Nat.lt_succ_diag_r.
  } {
    apply Nat.lt_0_succ.
  }
}
(*
...
destruct ra. {
  cbn.
  rewrite sizes_of_bmatrix_add. {
    apply sizes_of_bmat_zero_like.
  } {
    apply is_square_bmat_zero_like.
    apply Ha; flia.
  } {
    now apply is_square_bmat_loop_mul.
  } {
    rewrite sizes_of_bmat_zero_like.
    rewrite IHBMA; [ easy | flia | flia | easy | easy | easy ].
  }
}
*)
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite sizes_of_bmatrix_add. {
  destruct ra; [ apply sizes_of_bmat_zero_like | ].
  apply IHra; [ | flia | | | | ]. {
    intros * Hi Hj Hij * HBMB Hfb.
    apply IHBMA; [ flia Hi | flia Hj | easy | easy | easy ].
  } {
    intros * Hi Hj.
    apply Ha; [ flia Hi | flia Hj ].
  } {
    intros * Hi Hj.
    apply Hb; [ flia Hi | flia Hj ].
  } {
    intros * Hi Hj.
    apply Has; [ flia Hi | flia Hj ].
  } {
    intros * Hi Hj.
    apply Hbs; [ flia Hi | flia Hj ].
  }
} {
  clear IHra.
  clear - Ha Hb Hab IHBMA Hssm Hsaba Hsabb H6 H7.
  assert (Hzr : 0 < S (S ra)) by flia.
  assert (H2 : is_square_bmat (fa 0 0 * fb 0 0)%BM). {
    now apply is_square_bmat_loop_mul.
  }
  clear - H2 Ha Hb Hab IHBMA Hssm Hsaba Hsabb.
  induction ra. {
    apply is_square_bmat_zero_like.
    apply Ha; flia.
  }
(*
  induction ra. {
    cbn.
    assert (H1 : 0 < 2) by flia.
    rewrite sizes_of_bmatrix_add; [ | | easy | easy ]. {
      apply is_square_bmat_loop_add. {
        apply square_bmat_loop_zero_like.
        rewrite sizes_of_bmat_zero_like.
        now apply Ha.
      } {
        rewrite sizes_of_bmat_zero_like.
        apply is_square_bmat_loop_mul. {
          now apply Ha.
        } {
          now rewrite Hab; apply Hb.
        }
      }
    } {
      apply is_square_bmat_zero_like.
      now apply Ha.
    }
  }
*)
  assert (Hzsr : 0 < S ra) by flia.
  assert (Hzssr : 0 < S (S ra)) by flia.
  assert (Hrsr : ra < S ra) by flia.
  assert (Hrssr : ra < S (S ra)) by flia.
  rewrite List_seq_succ_r; cbn.
  rewrite fold_left_app; cbn.
  assert
    (H6' : sizes_of_bmatrix (fa 0 ra) = sizes_of_bmatrix (fa 0 0)). {
    apply sizes_of_bmatrix_at_0_0 with (r := S ra). {
      intros i j Hi Hj.
      apply Ha; [ flia Hi | flia Hj ].
    } {
      easy.
    } {
      easy.
    }
  }
  assert
  (H7' : sizes_of_bmatrix (fb ra 0) = sizes_of_bmatrix (fb 0 0)). {
    apply sizes_of_bmatrix_at_0_0 with (r := S ra). {
      intros i j Hi Hj.
      apply Hb; [ flia Hi | flia Hj ].
    } {
      easy.
    } {
      easy.
    }
  }
  apply is_square_bmat_loop_add. {
    rewrite sizes_of_bmatrix_add. {
      apply IHra. {
        intros * Hi Hj Hsq * HBMB Hss.
        apply IHBMA; [ flia Hi | flia Hj | easy | easy | easy ].
      } {
        intros * Hi Hj.
        apply Ha; [ flia Hi | flia Hj ].
      } {
        intros * Hi Hj.
        apply Hb; [ flia Hi | flia Hj ].
      }
    } {
      apply IHra. {
        intros * Hi Hj Hsq * HBMB Hss.
        apply IHBMA; [ flia Hi | flia Hj | easy | easy | easy ].
      } {
        intros * Hi Hj.
        apply Ha; [ flia Hi | flia Hj ].
      } {
        intros * Hi Hj.
        apply Hb; [ flia Hi | flia Hj ].
      }
    } {
      apply is_square_bmat_loop_mul. {
        now apply sizes_of_bmatrix_mul_a.
      } {
        rewrite IHBMA; [ | easy | easy | | | congruence ]. {
          now rewrite H6', Hab; apply Hb.
        } {
          now rewrite H6'; apply Ha.
        } {
          unfold is_square_bmat.
          now rewrite H7'; apply Hb.
        }
      }
    } {
      rewrite sizes_of_bmatrix_fold_left. {
        rewrite sizes_of_bmat_zero_like.
        symmetry.
        rewrite IHBMA; [ easy | easy | easy | | | congruence ]. {
          now rewrite H6'; apply Ha.
        } {
          unfold is_square_bmat.
          now rewrite H7'; apply Hb.
        }
      } {
        apply is_square_bmat_zero_like.
        now apply Ha.
      } {
        intros j Hj.
        assert (H9 : j < S (S ra)) by flia Hj.
        assert
          (H10 : sizes_of_bmatrix (fa 0 j) = sizes_of_bmatrix (fa 0 0)). {
          apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
            intros i k Hi Hk.
            apply Ha; [ flia Hi | flia Hk ].
          } {
            easy.
          } {
            easy.
          }
        }
        assert
          (H11 : sizes_of_bmatrix (fb j 0) = sizes_of_bmatrix (fb 0 0)). {
          apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
            intros i k Hi Hk.
            apply Hb; [ flia Hi | flia Hk ].
          } {
            easy.
          } {
            easy.
          }
        }
        apply is_square_bmat_loop_mul. {
          apply sizes_of_bmatrix_mul_a; [ | | | easy ]. {
            intros i k Hi Hk H6 * H7 H8.
            apply IHBMA; [ flia Hi Hj | flia Hk Hj | easy | easy | easy ].
          } {
            intros i k Hi Hk.
            apply Ha; [ flia Hi Hj | flia Hk Hj ].
          } {
            intros i k Hi Hk.
            apply Hb; [ flia Hi Hj | flia Hk Hj ].
          }
        } {
          rewrite IHBMA; [ | easy | easy | | | congruence ]. {
            now rewrite H10, Hab; apply Hb.
          } {
            now rewrite H10; apply Ha.
          } {
            unfold is_square_bmat.
            now rewrite H11; apply Hb.
          }
        }
      } {
        intros j Hj.
        assert (H9 : j < S (S ra)) by flia Hj.
        rewrite sizes_of_bmat_zero_like.
        symmetry.
        rewrite IHBMA; [ | easy | easy | | | ]. {
          apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
            intros i k Hi Hk.
            apply Ha; [ flia Hi | flia Hk ].
          } {
            easy.
          } {
            flia Hj.
          }
        } {
          rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
            now apply Ha.
          } {
            intros i k Hi Hk.
            apply Ha; [ flia Hi | flia Hk ].
          } {
            easy.
          } {
            flia Hj.
          }
        } {
          unfold is_square_bmat.
          rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
            now apply Hb.
          } {
            intros i k Hi Hk.
            apply Hb; [ flia Hi | flia Hk ].
          } {
            flia Hj.
          } {
            easy.
          }
        } {
          rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
            symmetry.
            rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
              easy.
            } {
              intros i k Hi Hk.
              apply Hb; [ flia Hi | flia Hk ].
            } {
              flia Hj.
            } {
              easy.
            }
          } {
            intros i k Hi Hk.
            apply Ha; [ flia Hi | flia Hk ].
          } {
            easy.
          } {
            flia Hj.
          }
        }
      }
    }
  } {
    rewrite sizes_of_bmatrix_add. {
      rewrite sizes_of_bmatrix_fold_left. {
        rewrite sizes_of_bmat_zero_like.
        apply is_square_bmat_loop_mul. {
          now apply Ha.
        } {
          now rewrite Hab; apply Hb.
        }
      } {
        apply is_square_bmat_zero_like.
        now apply Ha.
      } {
        intros j Hj.
        assert (H9 : j < S (S (S ra))) by flia Hj.
        assert
          (H10 : sizes_of_bmatrix (fa 0 j) = sizes_of_bmatrix (fa 0 0)). {
          apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
            intros i k Hi Hk.
            apply Ha; [ flia Hi | flia Hk ].
          } {
            easy.
          } {
            flia Hj.
          }
        }
        assert
          (H11 : sizes_of_bmatrix (fb j 0) = sizes_of_bmatrix (fb 0 0)). {
          apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
            intros i k Hi Hk.
            apply Hb; [ flia Hi | flia Hk ].
          } {
            flia Hj.
          } {
            easy.
          }
        }
        apply is_square_bmat_loop_mul. {
...
          rewrite IHBMA; [ | easy | easy | | | congruence ]. {
            now rewrite H10; apply Ha.
          } {
            now rewrite H10; apply Ha.
          } {
            unfold is_square_bmat.
            now rewrite H11; apply Hb.
          }
        } {
          rewrite IHBMA; [ | easy | easy | | | congruence ]. {
            now rewrite H10, Hab; apply Hb.
          } {
            now rewrite H10; apply Ha.
          } {
            unfold is_square_bmat.
            now rewrite H11; apply Hb.
          }
        }
      } {
        intros j Hj.
        assert
          (Haj : sizes_of_bmatrix (fa 0 j) = sizes_of_bmatrix (fa 0 0)). {
          apply sizes_of_bmatrix_at_0_0 with (r := S ra). {
            intros i k Hi Hk.
            apply Ha; [ flia Hi | flia Hk ].
          } {
            flia.
          } {
            easy.
          }
        }
        assert
          (Hbj : sizes_of_bmatrix (fb j 0) = sizes_of_bmatrix (fb 0 0)). {
          apply sizes_of_bmatrix_at_0_0 with (r := S ra). {
            intros i k Hi Hk.
            apply Hb; [ flia Hi | flia Hk ].
          } {
            easy.
          } {
            flia.
          }
        }
        assert
          (Habj :
             sizes_of_bmatrix (fa 0 j * fb j 0)%BM =
             sizes_of_bmatrix (fa 0 0)). {
          rewrite IHBMA; [ easy | easy | flia Hj | | | congruence ]. {
            rewrite Haj.
            apply Ha; [ easy | flia Hj ].
          } {
            unfold is_square_bmat.
            rewrite Hbj.
            apply Hb; [ flia Hj | easy ].
          }
        }
        assert
          (Hab0 :
             sizes_of_bmatrix (fa 0 0 * fb 0 0)%BM =
             sizes_of_bmatrix (fa 0 0)). {
            rewrite IHBMA; [ easy | easy | easy | | | easy ]. {
              now apply Ha.
            } {
              now apply Hb.
            }
        }
        rewrite sizes_of_bmatrix_add. {
          now rewrite sizes_of_bmat_zero_like.
        } {
          apply is_square_bmat_zero_like.
          now apply Ha.
        } {
          apply is_square_bmat_loop_mul. {
            rewrite Hab0.
            now apply Ha.
          } {
            rewrite Hab0, Hab.
            now apply Hb.
          }
        } {
          now rewrite sizes_of_bmat_zero_like.
        }
      }
    } {
      apply IHra. {
        intros * Hi Hj Hsq * HBMB Hss.
        apply IHBMA; [ flia Hi | flia Hj | easy | easy | easy ].
      } {
        intros * Hi Hj.
        apply Ha; [ flia Hi | flia Hj ].
      } {
        intros * Hi Hj.
        apply Hb; [ flia Hi | flia Hj ].
      }
    } {
      apply is_square_bmat_loop_mul. {
        rewrite IHBMA; [ | easy | easy | | | congruence ]. {
          now rewrite H6'; apply Ha.
        } {
          now rewrite H6'; apply Ha.
        } {
          unfold is_square_bmat.
          now rewrite H7'; apply Hb.
        }
      } {
        rewrite IHBMA; [ | easy | easy | | | congruence ]. {
          now rewrite H6', Hab; apply Hb.
        } {
          now rewrite H6'; apply Ha.
        } {
          unfold is_square_bmat.
          now rewrite H7'; apply Hb.
        }
      }
    } {
      rewrite sizes_of_bmatrix_fold_left. {
        rewrite sizes_of_bmatrix_add; [ | | easy | easy ]. {
          rewrite sizes_of_bmat_zero_like.
          symmetry.
          rewrite IHBMA; [ easy | easy | easy | | | congruence ]. {
            now rewrite H6'; apply Ha.
          } {
            unfold is_square_bmat.
            now rewrite H7'; apply Hb.
          }
        } {
          now apply is_square_bmat_zero_like, Ha.
        }
      } {
        apply is_square_bmat_loop_add. {
          rewrite sizes_of_bmatrix_add; [ | | easy | easy ]. {
            apply is_square_bmat_zero_like.
            now apply Ha.
          } {
            apply is_square_bmat_zero_like.
            now apply Ha.
          }
        } {
          rewrite sizes_of_bmatrix_add; [ | | easy | easy ]. {
            rewrite sizes_of_bmat_zero_like.
            apply is_square_bmat_loop_mul; [ now apply Ha | ].
            now rewrite Hab; apply Hb.
          } {
            apply is_square_bmat_zero_like.
            now apply Ha.
          }
        }
      } {
        intros j Hj.
        assert (H9 : j < S (S (S ra))) by flia Hj.
        assert
          (H10 : sizes_of_bmatrix (fa 0 j) = sizes_of_bmatrix (fa 0 0)). {
          apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
            intros i k Hi Hk.
            apply Ha; [ flia Hi | flia Hk ].
          } {
            easy.
          } {
            flia Hj.
          }
        }
        assert
          (H11 : sizes_of_bmatrix (fb j 0) = sizes_of_bmatrix (fb 0 0)). {
          apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
            intros i k Hi Hk.
            apply Hb; [ flia Hi | flia Hk ].
          } {
            flia Hj.
          } {
            easy.
          }
        }
        apply is_square_bmat_loop_mul. {
          rewrite IHBMA; [ | easy | easy | | | congruence ]. {
            now rewrite H10; apply Ha.
          } {
            now rewrite H10; apply Ha.
          } {
            unfold is_square_bmat.
            now rewrite H11; apply Hb.
          }
        } {
          rewrite IHBMA; [ | easy | easy | | | congruence ]. {
            now rewrite H10, Hab; apply Hb.
          } {
            now rewrite H10; apply Ha.
          } {
            unfold is_square_bmat.
            now rewrite H11; apply Hb.
          }
        }
      } {
        intros j Hj.
        assert (H9 : j < S (S (S ra))) by flia Hj.
        rewrite sizes_of_bmatrix_add; [ | | easy | easy ]. {
          clear - IHBMA Ha Hj Hb Hab.
          cbn in Hj.
          destruct Hj as (_ & Hj).
          assert (H3 : 0 < S (S ra)) by flia.
          assert (H9 : j < S (S (S ra))) by flia Hj.
          assert (Hsss : 0 < S (S (S ra))) by flia.
          rewrite sizes_of_bmat_zero_like.
          symmetry.
          rewrite IHBMA; [ | easy | easy | | | ]. {
            apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
              intros i k Hi Hk.
              apply Ha; [ flia Hi | flia Hk ].
            } {
              easy.
            } {
              flia Hj.
            }
          } {
            rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
              now apply Ha.
            } {
              intros i k Hi Hk.
              apply Ha; [ flia Hi | flia Hk ].
            } {
              easy.
            } {
              flia Hj.
            }
          } {
            unfold is_square_bmat.
            rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
              now apply Hb.
            } {
              intros i k Hi Hk.
              apply Hb; [ flia Hi | flia Hk ].
            } {
              flia Hj.
            } {
              easy.
            }
          } {
            rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
              symmetry.
              rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
                easy.
              } {
                intros i k Hi Hk.
                apply Hb; [ flia Hi | flia Hk ].
              } {
                flia Hj.
              } {
                easy.
              }
            } {
              intros i k Hi Hk.
              apply Ha; [ flia Hi | flia Hk ].
            } {
              easy.
            } {
              flia Hj.
            }
          }
        } {
          apply is_square_bmat_zero_like.
          now apply Ha.
        }
      }
    }
  }
} {
  assert (H3 : 0 < S (S ra)) by flia.
  assert (H4 : S ra < S (S ra)) by flia.
  apply is_square_bmat_loop_mul. {
    rewrite IHBMA; [ | easy | easy | | | congruence ]. {
      now rewrite H6; apply Ha.
    } {
      now rewrite H6; apply Ha.
    } {
      unfold is_square_bmat.
      now rewrite H7; apply Hb.
    }
  } {
    rewrite IHBMA; [ | easy | easy | | | congruence ]. {
      now rewrite H6, Hab; apply Hb.
    } {
      now rewrite H6; apply Ha.
    } {
      unfold is_square_bmat.
      now rewrite H7; apply Hb.
    }
  }
} {
  cbn in IHra.
  rewrite IHra. {
    symmetry.
    rewrite IHBMA; [ | flia | flia | | | ]. {
      apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
        intros i j Hi Hj.
        apply Ha; [ flia Hi | flia Hj ].
      } {
        flia.
      } {
        flia.
      }
    } {
      rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
        apply Ha; flia.
      } {
        intros i j Hi Hj.
        apply Ha; [ flia Hi | flia Hj ].
      } {
        flia.
      } {
        flia.
      }
    } {
      unfold is_square_bmat.
      rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
        apply Hb; flia.
      } {
        intros i j Hi Hj.
        apply Hb; [ flia Hi | flia Hj ].
      } {
        flia.
      } {
        flia.
      }
    } {
      rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
        symmetry.
        rewrite sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
          easy.
        } {
          apply Hb; flia.
        } {
          flia.
        } {
          flia.
        }
      } {
        intros i j Hi Hj.
        apply Ha; [ flia Hi | flia Hj ].
      } {
        flia.
      } {
        flia.
      }
    }
  } {
    intros * Hi Hj Hsq * HBMB Hss.
    apply IHBMA; [ flia Hi | flia Hj | easy | easy | easy ].
  } {
    flia.
  } {
    intros * Hi Hj.
    apply Ha; [ flia Hi | flia Hj ].
  } {
    intros * Hi Hj.
    apply Hb; [ flia Hi | flia Hj ].
  } {
    intros * Hi Hj.
    apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
      intros i1 j1 Hi1 Hj1.
      apply Ha; [ flia Hi1 | flia Hj1 ].
    } {
      flia Hi.
    } {
      flia Hj.
    }
  } {
    intros * Hi Hj.
    apply sizes_of_bmatrix_at_0_0 with (r := S (S ra)). {
      intros i1 j1 Hi1 Hj1.
      apply Hb; [ flia Hi1 | flia Hj1 ].
    } {
      flia Hi.
    } {
      flia Hj.
    }
  }
}
Qed.

(* pfiou... 900 lignes pour un théorème... *)
(* ça va pas, ça *)

Inspect 1.

...

Theorem is_square_bmat_mul : ∀ BMA BMB,
  is_square_bmat BMA
  → is_square_bmat BMB
  → sizes_of_bmatrix BMA = sizes_of_bmatrix BMB
  → is_square_bmat (BMA * BMB)%BM.
Proof.
intros * Ha Hb Hab.
unfold is_square_bmat.
...
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
...
  now apply is_square_bmat_mul.
}
now apply sizes_of_bmatrix_mul.
Qed.

Theorem bmat_zero_like_sqr : ∀ BM,
  is_square_bmat BM
  → bmat_zero_like (BM * BM)%BM = bmat_zero_like BM.
Proof.
intros * Hss.
...
now apply bmat_zero_like_mul.
Qed.

(* bon, je me suis faich... à prouver ça, mais il y a une autre
   preuve ci-dessous, invoquant des théorèmes que j'avais déjà
   faits.
Theorem bmat_mul_0_l' : ∀ BM,
  is_square_bmat BM
  → (bmat_zero_like BM * BM)%BM = bmat_zero_like BM.
Proof.
intros * Hss.
induction BM as [x| M IHBM] using bmatrix_ind2. {
  now cbn; rewrite srng_mul_0_l.
}
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
rewrite bmat_zero_like_idemp.
destruct M as (f, r, c); cbn in *.
destruct (zerop r) as [H| H]; [ easy | cbn in Hss; clear H ].
destruct (zerop c) as [H| H]; [ easy | cbn in Hss; clear H ].
destruct Hss as (_ & H & Hss); subst c.
rewrite bmat_zero_like_eq_compat with (BMB := f i j); cycle 1. {
  apply Hss; flia Hi.
} {
  unfold is_square_bmat.
  rewrite (sizes_of_bmatrix_at_0_0 f Hss Hi Hj).
  now apply Hss.
} {
  symmetry.
  apply (sizes_of_bmatrix_at_0_0 f Hss Hi Hj).
}
replace
  (fold_left
     (λ (acc : bmatrix T) (j0 : nat),
       (acc + bmat_zero_like (f i j0) * f j0 j)%BM)
     (seq 0 r) (bmat_zero_like (f i j)))
with
  (fold_left
     (λ (acc : bmatrix T) (j0 : nat),
       (acc + bmat_zero_like (f i j))%BM)
     (seq 0 r) (bmat_zero_like (f i j))). 2: {
  apply List_fold_left_ext_in.
  intros k M Hk.
  apply in_seq in Hk.
  f_equal.
  symmetry.
  rewrite bmat_zero_like_eq_compat with (BMB := f k j); cycle 1. {
    unfold is_square_bmat.
    rewrite (sizes_of_bmatrix_at_0_0 f Hss); [ | easy | easy ].
    now apply Hss.
  } {
    unfold is_square_bmat.
    rewrite (sizes_of_bmatrix_at_0_0 f Hss); [ | easy | easy ].
    now apply Hss.
  } {
    rewrite (sizes_of_bmatrix_at_0_0 f Hss); [ symmetry | easy | easy ].
    now rewrite (sizes_of_bmatrix_at_0_0 f Hss).
  }
  rewrite IHBM; [ | easy | easy | ]. 2: {
    rewrite (sizes_of_bmatrix_at_0_0 f Hss); [ | easy | easy ].
    now apply Hss.
  }
  apply bmat_zero_like_eq_compat. {
    unfold is_square_bmat.
    rewrite (sizes_of_bmatrix_at_0_0 f Hss); [ | easy | easy ].
    now apply Hss.
  } {
    unfold is_square_bmat.
    rewrite sizes_of_bmatrix_at_0_0 with (r := r); [ | easy | easy | easy ].
    now apply Hss.
  }
  rewrite (sizes_of_bmatrix_at_0_0 f Hss); [ symmetry | easy | easy ].
  now rewrite (sizes_of_bmatrix_at_0_0 f Hss).
}
rewrite bmat_zero_like_eq_compat with (BMB := f 0 0); cycle 1. {
  unfold is_square_bmat.
  rewrite (sizes_of_bmatrix_at_0_0 f Hss); [ | easy | easy ].
  now apply Hss.
} {
  apply Hss; flia Hi.
} {
  apply sizes_of_bmatrix_at_0_0 with (r := r); [ | easy | easy ].
  apply Hss.
}
clear - sp Hss.
induction r; [ easy | ].
rewrite List_seq_succ_r; cbn.
rewrite fold_left_app; cbn.
rewrite IHr. {
  rewrite <- bmat_zero_like_idemp at 2.
  apply bmat_add_0_r.
  apply is_square_bmat_zero_like.
  apply Hss; flia.
}
intros i j Hi Hj.
apply Hss; [ flia Hi | flia Hj ].
Qed.
*)

Theorem bmat_mul_0_l : ∀ BM,
  is_square_bmat BM
  → (bmat_zero_like BM * BM)%BM = bmat_zero_like BM.
Proof.
intros * Hss.
rewrite <- bmat_zero_like_mul_distr_l; [ | easy ].
...
now apply bmat_zero_like_sqr.
Qed.

...

Theorem bmat_mul_0_r : ∀ BM,
  is_square_bmat BM
  → (BM * bmat_zero_like BM)%BM = bmat_zero_like BM.
Proof.
intros * Hss.
rewrite <- bmat_zero_like_mul_distr_r. 2: {
  exists (sizes_of_bmatrix BM).
  split; intros BMA HBMA. {
    destruct HBMA as [| HBMA]; [ now subst BMA | ].
    destruct HBMA; [ now subst BMA | easy ].
  } {
    destruct HBMA as [| HBMA]; [ now subst BMA | ].
    destruct HBMA; [ now subst BMA | easy ].
  }
}
now apply bmat_zero_like_sqr.
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
    now apply old_bmat_add_0_l.
  }
  destruct j; [ cbn | flia Hj ].
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite IHn; [ | easy ].
  now apply old_bmat_add_0_l.
}
destruct i; [ cbn | flia Hi ].
destruct j. {
  rewrite IHn; [ | easy ].
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  now apply old_bmat_add_0_l.
}
destruct j; [ | flia Hj ].
rewrite IHn. 2: {
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite IHn; [ | easy ].
now apply old_bmat_add_0_l.
Qed.

Theorem bmat_mul_Z_2_pow_r : ∀ n M,
  bmat_fit_for_add (I_2_pow n) M
  → bmat_mul M (Z_2_pow n) = Z_2_pow n.
Proof.
intros * Hss.
revert M Hss.
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
destruct i. {
  destruct j. {
    rewrite IHn; [ cbn | easy ].
    rewrite IHn. 2: {
      transitivity (Z_2_pow n); [ | easy ].
      apply bmat_fit_for_add_IZ_IZ.
    }
    now apply old_bmat_add_0_l.
  }
  destruct j; [ cbn | flia Hj ].
  rewrite IHn; [ | easy ].
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  now apply old_bmat_add_0_l.
}
destruct i; [ cbn | flia Hi ].
destruct j. {
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite IHn; [ | easy ].
  now apply old_bmat_add_0_l.
}
destruct j; [ | flia Hj ].
rewrite IHn. 2: {
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite IHn; [ | easy ].
now apply old_bmat_add_0_l.
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
  apply old_bmat_add_0_r.
  destruct j. {
    transitivity (I_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  destruct j; [ | flia Hj ].
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
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
apply old_bmat_add_0_l.
destruct j; [ easy | ].
destruct j; [ | flia Hj ].
transitivity (I_2_pow n); [ | easy ].
apply bmat_fit_for_add_IZ_IZ.
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
    rewrite bmat_mul_Z_2_pow_r. 2: {
      transitivity (Z_2_pow n); [ | easy ].
      apply bmat_fit_for_add_IZ_IZ.
    }
    apply old_bmat_add_0_r.
    transitivity (I_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  destruct j; [ | flia Hj ].
  rewrite fold_Z_2_pow.
  rewrite bmat_mul_Z_2_pow_r; [ | easy ].
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  now apply old_bmat_add_0_l.
}
destruct i; [ cbn | flia Hi ].
destruct j. {
  rewrite IHn. 2: {
    transitivity (Z_2_pow n); [ | easy ].
    apply bmat_fit_for_add_IZ_IZ.
  }
  rewrite fold_Z_2_pow.
  rewrite bmat_mul_Z_2_pow_r; [ | easy ].
  now apply old_bmat_add_0_r.
}
destruct j; [ | flia Hj ].
rewrite fold_Z_2_pow.
rewrite bmat_mul_Z_2_pow_r. 2: {
  transitivity (Z_2_pow n); [ | easy ].
  apply bmat_fit_for_add_IZ_IZ.
}
rewrite IHn; [ | easy ].
apply old_bmat_add_0_l.
transitivity (I_2_pow n); [ | easy ].
apply bmat_fit_for_add_IZ_IZ.
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
  apply all_0_srng_summation_0; [ | easy ].
  apply sp.
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

Theorem square_bmat_add : ∀ MA MB sizes,
  is_square_bmat_loop sizes MA
  → is_square_bmat_loop sizes MB
  → is_square_bmat_loop sizes (MA + MB)%BM.
Proof.
intros * Ha Hb.
revert MA MB Ha Hb.
induction sizes as [| size]; intros; [ now destruct MA, MB | ].
cbn in Ha, Hb |-*.
destruct MA as [xa| ma]; [ easy | ].
destruct MB as [xb| mb]; [ easy | cbn ].
destruct Ha as (Hra & Hca & Ha).
destruct Hb as (Hrb & Hcb & Hb).
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
apply IHsizes; [ now apply Ha | now apply Hb ].
Qed.

Theorem square_bmat_fold_left :
  ∀ (fa fb : nat → nat → bmatrix T) size sizes i j,
  (∀ MA MB,
   is_square_bmat_loop sizes MA
   → is_square_bmat_loop sizes MB
   → is_square_bmat_loop sizes (MA * MB)%BM)
  → (∀ j, j < S size → is_square_bmat_loop sizes (fa i j))
  → (∀ i, i < S size → is_square_bmat_loop sizes (fb i j))
  → is_square_bmat_loop sizes
       (fold_left (λ a k, (a + fa i (k + 1)%nat * fb (k + 1)%nat j)%BM) 
       (seq 0 size) (fa i 0 * fb 0 j)%BM).
Proof.
intros * IHsizes Ha Hb.
induction size. {
  apply IHsizes; [ apply Ha; flia | apply Hb; flia ].
}
rewrite <- (Nat.add_1_r size).
rewrite seq_app.
rewrite fold_left_app.
rewrite Nat.add_0_l.
unfold seq at 1.
unfold fold_left at 1.
apply square_bmat_add. 2: {
  apply IHsizes; [ apply Ha; flia | apply Hb; flia ].
}
apply IHsize. {
  intros k Hk; apply Ha; flia Hk.
} {
  intros k Hk; apply Hb; flia Hk.
}
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
destruct size; [ easy | cbn in Has, Hbs, Hcs |-* ].
injection Has; clear Has; intros Has.
injection Hbs; clear Hbs; intros Hbs.
injection Hcs; clear Hcs; intros Hcs.
rewrite Nat.sub_0_r.
rewrite IHMC; [ | flia | easy | ]. 2: {
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  exists sizes.
  split. {
    intros BM HBM.
    unfold is_square_bmat.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia ].
      apply Ha; [ easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | easy | flia ].
      apply Hb; [ easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia | easy ].
      apply Hc; [ flia | easy ].
    }
    easy.
  } {
    intros BM HBM.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ easy | easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ easy | easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ easy | flia | easy ].
    }
    easy.
  }
}
replace
  (fold_left
    (λ (acc : bmatrix T) (j0 : nat),
       (acc + (fa i (j0 + 1)%nat + fb i (j0 + 1)%nat) * fc (j0 + 1)%nat j)%BM)
    (seq 0 size) (fa i 0 * fc 0 j + fb i 0 * fc 0 j)%BM)
with
  (fold_left
    (λ (acc : bmatrix T) (j0 : nat),
       (acc +
        (fa i (j0 + 1)%nat * fc (j0 + 1)%nat j +
         fb i (j0 + 1)%nat * fc (j0 + 1)%nat j))%BM)
    (seq 0 size) (fa i 0 * fc 0 j + fb i 0 * fc 0 j)%BM). 2: {
  apply List_fold_left_ext_in.
  intros k M Hk.
  f_equal.
  apply in_seq in Hk.
  symmetry.
  apply IHMC; [ flia Hk | easy | ].
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  exists sizes.
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
assert (H : ∀ j, j < S size → is_square_bmat_loop sizes (fa i j)). {
  now intros; apply Ha.
}
move H before Ha; clear Ha; rename H into Ha.
assert (H : ∀ j, j < S size → is_square_bmat_loop sizes (fb i j)). {
  now intros; apply Hb.
}
move H before Hb; clear Hb; rename H into Hb.
assert (H : ∀ i, i < S size → is_square_bmat_loop sizes (fc i j)). {
  now intros; apply Hc.
}
move H before Hc; clear Hc; rename H into Hc.
move j before i.
clear Hi Hj IHMC Hsq Hsz.
induction size; [ easy | ].
rewrite List_seq_succ_r; cbn.
do 3 rewrite fold_left_app; cbn.
rewrite IHsize; cycle 1. {
  intros k Hk; apply Ha; flia Hk.
} {
  intros k Hk; apply Hb; flia Hk.
} {
  intros k Hk; apply Hc; flia Hk.
}
remember
  (fold_left (λ acc j0, acc + fa i (j0 + 1)%nat * fc (j0 + 1)%nat j)
     (seq 0 size) (fa i 0 * fc 0 j))%BM as x.
remember
  (fold_left (λ acc j0, acc + fb i (j0 + 1)%nat * fc (j0 + 1)%nat j)
     (seq 0 size) (fb i 0 * fc 0 j))%BM as y.
remember (fa i (size + 1)%nat) as u.
remember (fb i (size + 1)%nat) as v.
remember (fc (size + 1)%nat j) as w.
assert (Hx : is_square_bmat_loop sizes x). {
  subst x.
  apply square_bmat_fold_left; cycle 1. {
    intros k Hk; apply Ha; flia Hk.
  } {
    intros k Hk; apply Hc; flia Hk.
  }
  intros * HA HB.
  now apply is_square_bmat_loop_mul.
}
assert (Hy : is_square_bmat_loop sizes y). {
  subst y.
  apply square_bmat_fold_left; cycle 1. {
    intros k Hk; apply Hb; flia Hk.
  } {
    intros k Hk; apply Hc; flia Hk.
  }
  intros * HA HB.
  now apply is_square_bmat_loop_mul.
}
assert (Sxy : is_square_bmat_loop sizes (x + y)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Su : is_square_bmat_loop sizes u) by (subst u; apply Ha; flia).
assert (Sv : is_square_bmat_loop sizes v) by (subst v; apply Hb; flia).
assert (Sw : is_square_bmat_loop sizes w) by (subst w; apply Hc; flia).
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
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hx_uw : bmat_fit_for_add x (u * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hx_yvw : bmat_fit_for_add x (y + v * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hy_vw : bmat_fit_for_add y (v * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hxy_vw : bmat_fit_for_add (x + y)%BM (v * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Huw_vw : bmat_fit_for_add (u * w)%BM (v * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
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
destruct size; [ easy | cbn in Has, Hbs, Hcs |-* ].
injection Has; clear Has; intros Has.
injection Hbs; clear Hbs; intros Hbs.
injection Hcs; clear Hcs; intros Hcs.
rewrite Nat.sub_0_r.
rewrite IHMA; [ | easy | flia | ]. 2: {
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  exists sizes.
  split. {
    intros BM HBM.
    unfold is_square_bmat.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ | easy | flia ].
      apply Ha; [ easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ | flia | easy ].
      apply Hb; [ flia | easy ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ | flia | easy ].
      apply Hc; [ flia | easy ].
    }
    easy.
  } {
    intros BM HBM.
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fa Ha); [ easy | easy | flia ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fb Hb); [ easy | flia | easy ].
    }
    destruct HBM as [H| HBM]; [ subst BM | ]. {
      rewrite (sizes_of_bmatrix_at_0_0 fc Hc); [ easy | flia | easy ].
    }
    easy.
  }
}
replace
  (fold_left
    (λ (acc : bmatrix T) (j0 : nat),
       (acc + fa i (j0 + 1)%nat * (fb (j0 + 1)%nat j + fc (j0 + 1)%nat j))%BM)
    (seq 0 size) (fa i 0 * fb 0 j + fa i 0 * fc 0 j)%BM)
with
  (fold_left
    (λ (acc : bmatrix T) (j0 : nat),
       (acc +
        (fa i (j0 + 1)%nat * fb (j0 + 1)%nat j +
         fa i (j0 + 1)%nat * fc (j0 + 1)%nat j))%BM)
    (seq 0 size) (fa i 0 * fb 0 j + fa i 0 * fc 0 j)%BM). 2: {
  apply List_fold_left_ext_in.
  intros k M Hk.
  f_equal.
  apply in_seq in Hk.
  symmetry.
  apply IHMA; [ easy | flia Hk | ].
  rewrite <- Has in Ha.
  rewrite <- Hbs in Hb.
  rewrite <- Hcs in Hc.
  exists sizes.
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
assert (H : ∀ j, j < S size → is_square_bmat_loop sizes (fa i j)). {
  now intros; apply Ha.
}
move H before Ha; clear Ha; rename H into Ha.
assert (H : ∀ i, i < S size → is_square_bmat_loop sizes (fb i j)). {
  now intros; apply Hb.
}
move H before Hb; clear Hb; rename H into Hb.
assert (H : ∀ i, i < S size → is_square_bmat_loop sizes (fc i j)). {
  now intros; apply Hc.
}
move H before Hc; clear Hc; rename H into Hc.
move j before i.
clear Hi Hj IHMA Hsq Hsz.
induction size; [ easy | ].
rewrite List_seq_succ_r; cbn.
do 3 rewrite fold_left_app; cbn.
rewrite IHsize; cycle 1. {
  intros k Hk; apply Ha; flia Hk.
} {
  intros k Hk; apply Hb; flia Hk.
} {
  intros k Hk; apply Hc; flia Hk.
}
remember
  (fold_left (λ acc j0, acc + fa i (j0 + 1)%nat * fb (j0 + 1)%nat j)
     (seq 0 size) (fa i 0 * fb 0 j))%BM as x.
remember
  (fold_left (λ acc j0, acc + fa i (j0 + 1)%nat * fc (j0 + 1)%nat j)
     (seq 0 size) (fa i 0 * fc 0 j))%BM as y.
remember (fa i (size + 1)%nat) as u.
remember (fb (size + 1)%nat j) as v.
remember (fc (size + 1)%nat j) as w.
assert (Hx : is_square_bmat_loop sizes x). {
  subst x.
  apply square_bmat_fold_left; cycle 1. {
    intros k Hk; apply Ha; flia Hk.
  } {
    intros k Hk; apply Hb; flia Hk.
  }
  intros * HA HB.
  now apply is_square_bmat_loop_mul.
}
assert (Hy : is_square_bmat_loop sizes y). {
  subst y.
  apply square_bmat_fold_left; cycle 1. {
    intros k Hk; apply Ha; flia Hk.
  } {
    intros k Hk; apply Hc; flia Hk.
  }
  intros * HA HB.
  now apply is_square_bmat_loop_mul.
}
assert (Sxy : is_square_bmat_loop sizes (x + y)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Su : is_square_bmat_loop sizes u) by (subst u; apply Ha; flia).
assert (Sv : is_square_bmat_loop sizes v) by (subst v; apply Hb; flia).
assert (Sw : is_square_bmat_loop sizes w) by (subst w; apply Hc; flia).
assert (Suv : is_square_bmat_loop sizes (u * v)%BM). {
  now apply is_square_bmat_loop_mul.
}
assert (Suw : is_square_bmat_loop sizes (u * w)%BM). {
  now apply is_square_bmat_loop_mul.
}
assert (Syuw : is_square_bmat_loop sizes (y + u * w)%BM). {
  now apply is_square_bmat_loop_add.
}
assert (Hxy : bmat_fit_for_add x y). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hx_uv : bmat_fit_for_add x (u * v)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hx_yuw : bmat_fit_for_add x (y + u * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hy_uw : bmat_fit_for_add y (u * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Hxy_uw : bmat_fit_for_add (x + y)%BM (u * w)%BM). {
  now apply (square_bmat_fit_for_add sizes).
}
assert (Huw_uv : bmat_fit_for_add (u * w)%BM (u * v)%BM). {
  now apply (square_bmat_fit_for_add sizes).
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
  apply (square_bmat_fit_for_add (sizes_of_bmatrix MA)). {
    now apply Hsq; left.
  } {
    specialize (Hsq _ (or_intror (or_introl eq_refl))) as H.
    rewrite Hsz; [ | now left ].
    rewrite <- (Hsz MB); [ | now right; left ].
    now apply Hsq; right; left.
  }
} {
  apply (square_bmat_fit_for_add (sizes_of_bmatrix MA)). {
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
now apply Hsq; right; left.
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
rewrite bmat_add_0_l in Hab; [ easy | ].
apply is_square_bmat_opp.
destruct Hcsb as (sizes & Hsq & Hsz).
now apply Hsq; left.
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
unfold so in Hab.
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
unfold so in Hab.
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
    cbn; rewrite IHn; symmetry.
    rewrite bmat_nat_mul_l_succ.
    now rewrite bmat_mul_1_r.
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
  unfold so.
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
  unfold so.
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
apply bmat_add_comm.
transitivity (A n). 2: {
  apply (square_bmat_fit_for_add (sizes_of_bmatrix (A n))). {
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
cbn - [ seq "-" ].
cbn in HBM.
destruct (zerop (mat_nrows M)) as [Hrz| Hrz]; [ easy | ].
destruct (zerop (mat_ncols M)) as [Hcz| Hcz]; [ easy | ].
cbn in HBM.
rewrite rng_opp_summation; [ | apply rp | apply sp ].
cbn.
rewrite IHBM; [ | easy | easy | now apply HBM ].
do 2 rewrite srng_add_0_l.
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
induction n; [ easy | cbn ].
rewrite IHn.
do 2 rewrite srng_add_0_l.
unfold so.
rewrite Tr_opp; [ | apply A_is_square_bmat ].
rewrite IHn.
apply rng_opp_0.
Qed.

End in_ring.

Module bmatrix_Notations.

Notation "a + b" := (bmat_add a b) : BM_scope.
Notation "a - b" := (bmat_sub a b) : BM_scope.
Notation "a * b" := (bmat_mul a b) : BM_scope.
Notation "- a" := (bmat_opp a) : BM_scope.

End bmatrix_Notations.

Import bmatrix_Notations.

(* eigenvalues and eigenvectors *)

...

Theorem exists_eigenvalues : ∀ (M : matrix T),
  is_square_mat M
  → ∃ EVL, length EVL = mat_nrows M ∧
     ∀ μ V, (μ, V) ∈ EVL → mat_mul_scal_l μ M = vect_mul_scal μ V.

...

Definition charac_polyn {A} {n : nat} (M : matrix A) := det (M - x * I).

...
