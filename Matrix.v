(* matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.
Require Import Init.Nat.

Require Import Misc.
Require Import RingLike RLsummation RLproduct.

(* matrices *)

Record matrix (m n : nat) T := mk_mat
  { mat_el : nat → nat → T }.

(* function extensionality required for matrices *)
Axiom matrix_eq : ∀ m n T (MA MB : matrix m n T),
  (∀ i j, i < m → j < n → mat_el MA i j = mat_el MB i j)
  → MA = MB.

Theorem matrix_neq : ∀ m n T (MA MB : matrix m n T),
  ¬ (∀ i j, i < m → j < n → mat_el MA i j = mat_el MB i j)
  → MA ≠ MB.
Proof.
intros * Hab.
intros H.
subst MB.
now apply Hab.
Qed.

Definition list_list_nrows T (ll : list (list T)) :=
  length ll.

Definition list_list_ncols T (ll : list (list T)) :=
  length (hd [] ll).

Definition list_list_of_mat m n T (M : matrix m n T) : list (list T) :=
  map (λ i, map (mat_el M i) (seq 0 m)) (seq 0 n).

Definition list_list_el T d (ll : list (list T)) i j : T :=
  nth j (nth i ll []) d.

Definition mat_of_list_list T d (ll : list (list T)) :
  matrix (list_list_nrows ll) (list_list_ncols ll) T :=
  mk_mat (list_list_nrows ll) (list_list_ncols ll) (list_list_el d ll).

(*
Compute (let (i, j) := (2, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (let (i, j) := (7, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (let (i, j) := (1, 3) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (list_list_of_mat (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]])).
*)

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

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

(* addition *)

Definition mat_add {ro : ring_like_op T} {m n} (MA MB : matrix m n T) :
  matrix m n T :=
  {| mat_el i j := (mat_el MA i j + mat_el MB i j)%F |}.

(* multiplication *)

Definition mat_mul {ro : ring_like_op T} {m n p}
    (MA : matrix m n T) (MB : matrix n p T) : matrix m p T :=
  {| mat_el i k := (Σ (j = 0, n - 1), mat_el MA i j * mat_el MB j k)%F |}.

(* opposite *)

Definition mat_opp {m n} (M : matrix m n T) : matrix m n T :=
  {| mat_el i j := (- mat_el M i j)%F |}.

(* subtraction *)

Definition mat_sub {m n} (MA MB : matrix m n T) :=
  mat_add MA (mat_opp MB).

(* vector *)

Record vector (n : nat) T := mk_vect
  { vect_el : nat → T }.

(* function extensionality required for vectors *)
Axiom vector_eq : ∀ n T (VA VB : vector n T),
  (∀ i, i < n → vect_el VA i = vect_el VB i)
  → VA = VB.

Definition vect_of_list {T} d (l : list T) :=
  mk_vect (length l) (λ i, nth i l d).
Definition list_of_vect {n T} (v : vector n T) :=
  map (vect_el v) (seq 0 n).

Definition vect_zero n := mk_vect n (λ _, 0%F).

(* addition, subtraction of vector *)

Definition vect_add {n} (U V : vector n T) :=
  mk_vect n (λ i, (vect_el U i + vect_el V i)%F).
Definition vect_opp {n} (V : vector n T) :=
  mk_vect n (λ i, (- vect_el V i)%F).

Definition vect_sub {n} (U V : vector n T) := vect_add U (vect_opp V).

(* vector from a matrix column *)

Definition vect_of_mat_col {m n} (M : matrix m n T) j :=
  mk_vect m (λ i, mat_el M i j).

(* concatenation of a matrix and a vector *)

Definition mat_vect_concat {m n} (M : matrix m n T) (V : vector m T) :
  matrix m (n + 1) T :=
  mk_mat m (n + 1)
    (λ i j, if Nat.eq_dec j n then vect_el V i else mat_el M i j).

(* multiplication of a matrix by a vector *)

Definition mat_mul_vect_r {m n} (M : matrix m n T) (V : vector n T) :=
  mk_vect m (λ i, (Σ (j = 0, n - 1), mat_el M i j * vect_el V j)%F).

(* multiplication of a vector by a scalar *)

Definition vect_mul_scal_l s {n} (V : vector n T) :=
  mk_vect n (λ i, s * vect_el V i)%F.

(* dot product *)

Definition vect_dot_product {n} (U V : vector n T) :=
  (Σ (i = 0, n - 1), vect_el U i * vect_el V i)%F.

Definition vect_squ_norm n (V : vector n T) := vect_dot_product V V.

(* multiplication of a matrix by a scalar *)

Definition mat_mul_scal_l {m n} s (M : matrix m n T) :=
  mk_mat m n (λ i j, s * mat_el M i j)%F.

(* matrix whose k-th column is replaced by a vector *)

Definition mat_repl_vect {m n} k (M : matrix m n T) (V : vector m T) :=
  mk_mat m n (λ i j, if Nat.eq_dec j k then vect_el V i else mat_el M i j).

(* (-1) ^ n *)

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%F
  | _ => (- 1%F)%F
  end.

Theorem minus_one_pow_succ :
  rngl_has_opp = true →
  ∀ i, minus_one_pow (S i) = (- minus_one_pow i)%F.
Proof.
intros Hop *.
unfold minus_one_pow.
remember (i mod 2) as k eqn:Hk; symmetry in Hk.
destruct k. {
  apply Nat.mod_divides in Hk; [ | easy ].
  destruct Hk as (k, Hk); subst i.
  rewrite <- Nat.add_1_l, Nat.mul_comm.
  now rewrite Nat.mod_add.
}
destruct k. {
  rewrite <- Nat.add_1_l.
  rewrite <- Nat.add_mod_idemp_r; [ | easy ].
  rewrite Hk; cbn.
  symmetry.
  now apply rngl_opp_involutive.
}
specialize (Nat.mod_upper_bound i 2) as H1.
assert (H : 2 ≠ 0) by easy.
specialize (H1 H); clear H.
rewrite Hk in H1.
flia H1.
Qed.

Theorem minus_one_pow_add_r :
  rngl_has_opp = true →
  ∀ i j, minus_one_pow (i + j) = (minus_one_pow i * minus_one_pow j)%F.
Proof.
intros Hop *.
revert j.
induction i; intros; [ now cbn; rewrite rngl_mul_1_l | ].
rewrite Nat.add_succ_comm.
rewrite IHi.
rewrite minus_one_pow_succ; [ | easy ].
rewrite minus_one_pow_succ; [ | easy ].
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
easy.
Qed.

(* *)

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments vect_el {n}%nat {T} v%V.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.

Definition permut_succ_vect_fun {n} (σ_n : nat → vector n nat) i j :=
  match j with
  | 0 => i / fact n
  | S j' =>
      vect_el (σ_n (i mod fact n)) j' +
      Nat.b2n (i / fact n <=? vect_el (σ_n (i mod fact n)) j')
  end.

Fixpoint permut n k : vector n nat :=
  match n with
  | 0 => mk_vect 0 (λ _, 0)
  | S n' => mk_vect (S n') (permut_succ_vect_fun (permut n') k)
  end.

(* other order of permutations where ranks p & q are swapped
   with the last two numbers, allowing consecutive permutations
   to have the p-th and the q-th numbers swapped; perhaps
   useful to prove aternativity, if I can do it.
   we have: permut_swap_last (n-2) (n-1) n k = permut n k *)

(*
Compute list_of_vect (permut 4 13).
     = [2; 0; 3; 1]
*)

(* i such that vect_el (permut n k) i = j *)

Fixpoint permut_inv n k (j : nat) :=
  match n with
  | 0 => 0
  | S n' =>
      if lt_dec j (k / fact n') then
        S (permut_inv n' (k mod fact n') j)
      else if lt_dec (k / fact n') j then
        S (permut_inv n' (k mod fact n') (j - 1))
      else 0
  end.

(*
Compute (map (λ i, list_of_vect (permut 3 i)) (seq 0 (fact 3))).
Compute list_of_vect (permut 3 4).
Compute permut_inv 3 4 0.
Compute permut_inv 3 4 1.
Compute permut_inv 3 4 2.
Compute list_of_vect (permut 4 12).
Compute permut_inv 4 12 0.
Compute permut_inv 4 12 1.
Compute permut_inv 4 12 2.
Compute permut_inv 4 12 3.

Compute vect_el (permut 3 4) (permut_inv 3 4 1).
Compute permut_inv 3 4 (vect_el (permut 3 4) 1).
*)

Theorem permut_inv_upper_bound : ∀ n k j,
  k < fact n
  → j < n
  → permut_inv n k j < n.
Proof.
intros * Hkn Hjn.
revert k j Hkn Hjn.
induction n; intros; [ easy | ].
cbn.
destruct (lt_dec j (k / fact n)) as [Hjkn| Hjkn]. {
  apply -> Nat.succ_lt_mono.
  destruct n. {
    cbn in Hkn.
    apply Nat.lt_1_r in Hkn; subst k.
    now cbn in Hjkn.
  }
  destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
    subst j.
    clear Hjn.
    exfalso; apply Nat.nle_gt in Hjkn; apply Hjkn; clear Hjkn.
    rewrite Nat_fact_succ in Hkn.
    rewrite Nat.mul_comm in Hkn.
    apply Nat.lt_succ_r.
    apply Nat.div_lt_upper_bound; [ | easy ].
    apply fact_neq_0.
  } {
    apply IHn; [ | flia Hjn Hjsn ].
    apply Nat.mod_upper_bound, fact_neq_0.
  }
} {
  apply Nat.nlt_ge in Hjkn.
  destruct (lt_dec (k / fact n) j) as [Hknj| Hknj]; [ | flia ].
  apply -> Nat.succ_lt_mono.
  destruct n. {
    now apply Nat.lt_1_r in Hjn; subst j.
  }
  apply IHn; [ | flia Hjn Hknj ].
  apply Nat.mod_upper_bound, fact_neq_0.
}
Qed.

Theorem permut_permut_inv : ∀ n k j,
  j < n
  → k < fact n
  → vect_el (permut n k) (permut_inv n k j) = j.
Proof.
intros * Hjn Hkn.
revert j k Hjn Hkn.
induction n; intros; [ easy | ].
cbn.
destruct (lt_dec j (k / fact n)) as [Hjkn| Hjkn]. {
  cbn.
  destruct n. {
    rewrite Nat.div_1_r in Hjkn; cbn in Hkn.
    flia Hkn Hjkn.
  }
  destruct (lt_dec k (fact (S n))) as [Hksn| Hksn]. {
    now rewrite Nat.div_small in Hjkn.
  }
  apply Nat.nlt_ge in Hksn.
  destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
    subst j.
    clear Hjn.
    exfalso; apply Nat.nle_gt in Hjkn; apply Hjkn; clear Hjkn.
    rewrite Nat_fact_succ in Hkn.
    rewrite Nat.mul_comm in Hkn.
    apply Nat.lt_succ_r.
    apply Nat.div_lt_upper_bound; [ | easy ].
    apply fact_neq_0.
  }
  rewrite IHn; [ | flia Hjn Hjsn | ]. 2: {
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  remember (k / fact (S n) <=? j) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ exfalso | apply Nat.add_0_r ].
  apply Nat.leb_le in Hb.
  flia Hjkn Hb.
} {
  apply Nat.nlt_ge in Hjkn.
  destruct (lt_dec (k / fact n) j) as [Hkj| Hkj]. 2: {
    apply Nat.nlt_ge in Hkj; cbn.
    now apply Nat.le_antisymm.
  }
  clear Hjkn.
  destruct j; [ easy | ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  cbn.
  destruct n; [ flia Hjn | ].
  apply Nat.succ_lt_mono in Hjn.
  rewrite IHn; [ | easy | ]. 2: {
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  remember (k / fact (S n) <=? j) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ apply Nat.add_1_r | exfalso ].
  apply Nat.leb_nle in Hb.
  now apply Nat.succ_le_mono in Hkj.
}
Qed.

Theorem permut_inv_permut : ∀ n k i,
  i < n
  → k < fact n
  → permut_inv n k (vect_el (permut n k) i) = i.
Proof.
intros * Hi Hkn.
revert k i Hi Hkn.
induction n; intros; [ flia Hi | ].
destruct i. {
  clear Hi; cbn.
  remember (k / fact n) as p eqn:Hp.
  destruct (lt_dec p p) as [H| H]; [ flia H | easy ].
}
apply Nat.succ_lt_mono in Hi.
cbn.
remember (k / fact n) as p eqn:Hp.
remember (vect_el (permut n (k mod fact n)) i) as q eqn:Hq.
move q before p.
remember (p <=? q) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply Nat.leb_le in Hb; cbn.
  destruct (lt_dec (q + 1) p) as [Hpq| Hqp]; [ flia Hb Hpq | ].
  apply Nat.nlt_ge in Hqp.
  destruct (lt_dec p (q + 1)) as [Hpq| Hpq]; [ | flia Hb Hpq ].
  clear Hpq Hqp.
  f_equal.
  rewrite Nat.add_sub.
  rewrite Hq.
  apply IHn; [ easy | ].
  apply Nat.mod_upper_bound, fact_neq_0.
} {
  apply Nat.leb_gt in Hb; cbn.
  rewrite Nat.add_0_r.
  destruct (lt_dec q p) as [H| H]; [ clear H | flia Hb H ].
  f_equal.
  rewrite Hq.
  apply IHn; [ easy | ].
  apply Nat.mod_upper_bound, fact_neq_0.
}
Qed.

Theorem permut_surjective : ∀ n k j,
  k < fact n
  → j < n
  → ∃ i : nat, i < n ∧ vect_el (permut n k) i = j.
Proof.
intros * Hkn Hjn.
exists (permut_inv n k j).
destruct n; [ easy | ].
split. {
  cbn.
  destruct (lt_dec j (k / fact n)) as [Hjk| Hjk]. {
    apply -> Nat.succ_lt_mono.
    destruct n. {
      now apply Nat.lt_1_r in Hkn; subst k.
    }
    destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
      subst j; clear Hjn.
      apply Nat.nle_gt in Hjk.
      exfalso; apply Hjk; clear Hjk.
      rewrite Nat_fact_succ in Hkn.
      rewrite Nat.mul_comm in Hkn.
      apply Nat.lt_succ_r.
      apply Nat.div_lt_upper_bound; [ | easy ].
      apply fact_neq_0.
    }
    apply permut_inv_upper_bound; [ | flia Hjn Hjsn ].
    apply Nat.mod_upper_bound, fact_neq_0.
  } {
    apply Nat.nlt_ge in Hjk.
    destruct (lt_dec (k / fact n) j) as [Hkj| Hkj]; [ | flia ].
    apply -> Nat.succ_lt_mono.
    destruct n. {
      apply Nat.lt_1_r in Hkn; subst k.
      flia Hjn Hkj.
    }
    apply permut_inv_upper_bound; [ | flia Hjn Hkj ].
    apply Nat.mod_upper_bound, fact_neq_0.
  }
}
now apply permut_permut_inv.
Qed.

Theorem permut_injective : ∀ n k i j,
  k < fact n
  → i < n
  → j < n
  → vect_el (permut n k) i = vect_el (permut n k) j
  → i = j.
Proof.
intros * Hk Hi Hj Hij.
assert (Hnz : n ≠ 0) by flia Hi.
rewrite <- permut_inv_permut with (n := n) (k := k); [ | easy | easy ].
symmetry.
rewrite <- permut_inv_permut with (n := n) (k := k); [ | easy | easy ].
now f_equal.
Qed.

(*
Compute (map (λ i, list_of_vect (permut 3 i)) (seq 0 (fact 3))).
*)

(* *)

(*
Compute  nat_of_permut (permut 3 0).
Compute  nat_of_permut (permut 3 1).
Compute  nat_of_permut (permut 3 2).
Compute  nat_of_permut (permut 3 3).
Compute  nat_of_permut (permut 3 4).
Compute  nat_of_permut (permut 3 5).
*)

(* *)

(*
Compute map (λ i, list_of_vect (permut 4 i)) (seq 0 (fact 4)).
*)

Definition swap_nat i j k :=
  if Nat.eq_dec k i then j
  else if Nat.eq_dec k j then i
  else k.

Definition vect_swap_elem n (v : vector n nat) i j :=
  mk_vect n (λ k, vect_el v (swap_nat i j k)).

Definition swap_in_permut n i j k := vect_swap_elem (permut n k) i j.

Definition permut_swap_last (p q : nat) n k :=
  vect_swap_elem (vect_swap_elem (permut n k) p (n - 2)) q (n - 1).

(*
Compute (map (λ i, list_of_vect (permut_swap_last 0 1 3 i)) (seq 0 (fact 3))).
Compute (map (λ i, list_of_vect (permut_swap_last 0 2 3 i)) (seq 0 (fact 3))).
Compute (map (λ i, list_of_vect (permut_swap_last 1 2 3 i)) (seq 0 (fact 3))).
Compute (map (λ i, list_of_vect (permut_swap_last 0 1 6 i)) (seq 0 (fact 6))).
*)

(*
Theorem pouet : ∀ n (M : matrix n n T) l r1 r2,
  n ≠ 0
  → l =
      map (λ k,
        (- signature n k *
         Π (i = 1, n),
         mat_el M (i - 1) (vect_el (swap_in_permut n r1 r2 k) (i - 1)%nat))%F)
        (seq 0 (fact n))
  → Permutation l (determinant'_list M).
Proof.
intros * Hnz Hl.
unfold determinant'_list; subst l.
destruct n; [ easy | clear Hnz ].
replace (fact (S n)) with (1 + (fact (S n) - 1)). 2: {
  rewrite Nat.add_comm, Nat.sub_add; [ easy | ].
  apply Nat.neq_0_lt_0, fact_neq_0.
}
rewrite seq_app.
cbn - [ iter_seq signature swap_in_permut permut fact ].
Print Permutation.
Search (Permutation (_ :: _)).
...
cbn - [ iter_seq signature swap_in_permut permut ].
rewrite seq_app.
do 2 rewrite map_app.
cbn - [ iter_seq signature swap_in_permut permut ].
...
Search (Permutation (_ ++ _)).
Print Permutation.
...

Compute let n := 4 in let '(i, j) := (0, 2) in nat_of_permut (swap_in_permut n i j (nat_of_permut (swap_in_permut n i j 13))).

Theorem pouet : ∀ n i j k,
  i < n
  → j < n
  → k < fact n
  → nat_of_permut
      (swap_in_permut n i j (nat_of_permut (swap_in_permut n i j k))) = k.
Proof.
intros * Hi Hj Hk.
revert i j k Hi Hj Hk.
induction n; intros; [ easy | ].
cbn - [ nat_of_permut_sub_vect ].
...

Compute list_of_vect (permut 2 1).
Compute list_of_vect (permut 2 2).
Compute list_of_vect (permut 2 3).
...

Theorem glop : ∀ b e f g,
  (∀ i, b ≤ i ≤ e → b ≤ g i ≤ e)
  → (∀ i, b ≤ i ≤ e → g i ≠ i)
  → (∀ i, b ≤ i ≤ e → g (g i) = i)
  → (Σ (i = b, e), f i =
     Σ (i = b, e), (if lt_dec i (g i) then f i else 0) +
     Σ (i = b, e), (if lt_dec i (g i) then f (g i) else 0))%F.
Proof.
intros * Hgbe Hgii Hggi.
destruct (le_dec b e) as [Hbe| Hbe]. 2: {
  apply Nat.nle_gt in Hbe.
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  symmetry; apply rngl_add_0_l.
}
remember (S e - b) as len eqn:Hlen.
replace e with (b + len - 1) in * by flia Hbe Hlen.
clear e.
destruct len. {
  destruct b; [ easy | cbn in Hbe; flia Hbe ].
}
rewrite <- Nat.add_sub_assoc; [ | flia ].
rewrite <- Nat.add_sub_assoc in Hgbe; [ | flia ].
rewrite <- Nat.add_sub_assoc in Hgii; [ | flia ].
rewrite <- Nat.add_sub_assoc in Hggi; [ | flia ].
rewrite Nat.sub_succ, Nat.sub_0_r in Hgbe, Hgii, Hggi |-*.
clear Hbe Hlen.
(**)
rewrite (rngl_summation_split_first _ b); [ | flia ].
rewrite (rngl_summation_split_first _ b); [ | flia ].
rewrite (rngl_summation_split_first _ b); [ | flia ].
destruct (lt_dec b (g b)) as [Hbgb| Hbgb]. {
  rewrite <- rngl_add_assoc; f_equal.
  rewrite (rngl_summation_split _ (g b)). 2: {
    split; [ flia Hbgb | ].
    apply -> Nat.succ_le_mono.
    apply Hgbe; flia.
  }
  rewrite (rngl_summation_split_last _ _ (g b)); [ | easy ].
  rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap; symmetry.
  rewrite rngl_add_add_swap; symmetry; f_equal.
  rewrite (rngl_summation_split _ (g b) _ (S b)). 2: {
    split; [ flia Hbgb | ].
    apply -> Nat.succ_le_mono.
    apply Hgbe; flia.
  }
  rewrite (rngl_summation_split_last _ (S b) (g b)); [ | easy ].
  rewrite (rngl_summation_split _ (g b) _ (S b)). 2: {
    split; [ flia Hbgb | ].
    apply -> Nat.succ_le_mono.
    apply Hgbe; flia.
  }
  rewrite (rngl_summation_split_last _ (S b) (g b)); [ | easy ].
  rewrite Hggi; [ | flia ].
  destruct (lt_dec (g b) b) as [H| H]; [ flia Hbgb H | clear H ].
  do 2 rewrite rngl_add_0_r.
...
revert f g b Hgbe Hgii Hggi.
induction len; intros. {
  rewrite Nat.add_0_r in Hgbe, Hgii.
  specialize (Hgbe b) as H1.
  specialize (Hgii b) as H2.
  assert (H : b ≤ b ≤ b) by easy.
  specialize (H1 H); specialize (H2 H); clear H.
  flia H1 H2.
}
rewrite (rngl_summation_split_first _ b); [ | flia ].
rewrite (rngl_summation_split_first _ b); [ | flia ].
rewrite (rngl_summation_split_first _ b); [ | flia ].
destruct (lt_dec b (g b)) as [Hbg| Hbg]. {
  rewrite <- rngl_add_assoc; f_equal.
  rewrite <- Nat.add_succ_comm in Hgbe |-*.
  rewrite (rngl_summation_split _ (g b)). 2: {
    specialize (Hgbe b) as H1.
    assert (b ≤ b ≤ S b + len) by flia.
    specialize (H1 H); clear H.
    flia H1.
  }
  rewrite rngl_summation_split_last; [ | easy ].
  rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap; symmetry.
  rewrite rngl_add_add_swap; symmetry.
  f_equal.
  symmetry.
  rewrite (rngl_summation_split _ (g b)). 2: {
    specialize (Hgbe b) as H1.
    assert (b ≤ b ≤ S b + len) by flia.
    specialize (H1 H); clear H.
    flia H1.
  }
  rewrite rngl_summation_split_last; [ | easy ].
  symmetry.
  rewrite Hggi; [ | flia ].
  destruct (lt_dec (g b) b) as [H| H]; [ flia Hbg H | clear H ].
  rewrite rngl_add_0_r.
...
  rewrite IHlen with (g := λ i, S (g i)); cycle 1. {
    intros i Hi.
    specialize (Hgbe i) as H1.
    assert (H : b ≤ S i ≤ S b + len).
    specialize (H1 H); clear H.
    split; [ | easy ].
...
  destruct (lt_dec b (g b)) as [Hbg| Hbg]; [ now rewrite rngl_add_0_r | ].
  apply Nat.nlt_ge in Hbg.
  rewrite rngl_add_0_l.
  specialize (Hgbe b).
  now replace (g b) with b by flia Hgbe.
}
rewrite (rngl_summation_split_first _ b); [ | flia ].
rewrite (rngl_summation_split_first _ b); [ | flia ].
rewrite (rngl_summation_split_first _ b); [ | flia ].
destruct (lt_dec b (g b)) as [Hbg| Hbg]. {
  rewrite rngl_add_0_l.
  rewrite <- rngl_add_assoc; f_equal.
  rewrite <- Nat.add_succ_comm in Hgbe, Hgii, Hggi |-*.
(*
  apply IHlen. {
    intros i Hi.
    specialize (Hgbe i) as H1.
    split; [ | flia Hi H1 ].
    assert (H : b ≤ i ≤ S b + len) by flia Hi.
    specialize (H1 H).
    clear H.
    specialize (Hgbe _ H1) as H2.
...
  rewrite Nat.add_succ_l.
  do 3 rewrite rngl_summation_succ_succ.
  rewrite IHlen with (g := λ i, g (S i)); cycle 1. {
    intros i Hi.
    specialize (Hgbe (S i)) as H1.
    assert (H : b ≤ S i ≤ S b + len) by flia Hi.
    specialize (H1 H).
    split; [ easy | ].
...
    specialize (Hgbe (S i)) as H1.
    assert (H : b ≤ S i ≤ S b + len) by flia Hi.
    specialize (H1 H).
    clear H.
    split; [ | flia H1 ].
...
*)
  destruct len. {
    rewrite Nat.add_0_r.
    rewrite rngl_summation_only_one; [ | easy ].
    rewrite rngl_summation_only_one; [ | easy ].
    rewrite rngl_summation_only_one; [ | easy ].
    destruct (lt_dec (S b) (g (S b))) as [Hsbg| Hsbg]. {
      symmetry; apply rngl_add_0_r.
    }
    symmetry; apply rngl_add_0_l.
  }
  rewrite Nat.add_succ_r.
  cbn - [ iter_seq ].
  do 3 rewrite rngl_summation_succ_succ.
  destruct len. {
    rewrite Nat.add_0_r.
    cbn.
    destruct b; cbn. {
      do 3 rewrite rngl_add_0_l.
      destruct (lt_dec 1 (g 1)) as [H1g1| H1g1]. {
        rewrite rngl_add_0_l.
        rewrite <- rngl_add_assoc; f_equal.
        destruct (lt_dec 2 (g 2)) as [H2g2| H2g2]. {
          now rewrite rngl_add_0_r.
        }
        now rewrite rngl_add_0_l.
      }
      rewrite rngl_add_0_l.
      destruct (lt_dec 2 (g 2)) as [H2g2| H2g2]. {
        now rewrite rngl_add_0_r, rngl_add_comm.
      }
      now rewrite rngl_add_0_l.
    }
    destruct b. {
      cbn.
      (* ouais, bon, fait chier *)
...
  rewrite IHlen with (g := g); cycle 1. {
    intros i Hi.
    specialize (Hgbe i) as H1.
    assert (H : b ≤ i ≤ S b + S len) by flia Hi.
    specialize (H1 H).
    split; [ | easy ].
...
  rewrite IHlen with (g := g); cycle 1. {
    intros i Hi.
    specialize (Hgbe i) as H1.
    assert (H : b ≤ i ≤ S b + len) by flia Hi.
    specialize (H1 H); clear H.
    split; [ | easy ].
...
  rewrite IHlen with (g := λ i, S (g i)); cycle 1. {
    intros i Hi.
    specialize (Hgbe i) as H1.
    assert (H : b ≤ i ≤ S b + len) by flia Hi.
    specialize (H1 H); clear H.
    split; [ flia H1 | ].
    cbn.
    apply -> Nat.succ_le_mono.
...
  apply IHlen. {
    intros i Hi.
...
rewrite IHlen; cycle 1. {
  intros i Hi.
  split; [ | apply Hgbe; flia Hi ].
...
rewrite rngl_add_0_l.
assert (H : ∀ i, i ≤ len → b ≤ g (b + i) ≤ b + len). {
  intros i Hi; apply Hgbe; flia Hi.
}
move H before Hgbe; clear Hgbe; rename H into Hgbe.
assert (H : ∀ i, i ≤ len → g (b + i) ≠ b + i). {
  intros i Hi; apply Hgii; flia Hi.
}
move H before Hgii; clear Hgii; rename H into Hgii.
assert (H : ∀ i, i ≤ len → g (g (b + i)) = b + i). {
  intros i Hi; apply Hggi; flia Hi.
}
move H before Hggi; clear Hggi; rename H into Hggi.
rewrite rngl_summation_shift; [ symmetry | flia ].
rewrite rngl_summation_shift; [ symmetry | flia ].
rewrite Nat.add_comm, Nat.add_sub.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_summation_shift; [ | flia ].
  now rewrite Nat.add_sub.
}
symmetry.
revert b g Hgbe Hgii Hggi.
induction len; intros. {
  rewrite rngl_summation_only_one; [ | easy ].
  rewrite rngl_summation_only_one; [ | easy ].
  rewrite rngl_summation_only_one; [ | easy ].
  rewrite Nat.add_0_r in Hgbe |-*.
  destruct (lt_dec b (g b)) as [Hbg| Hbg]; [ easy | ].
  apply Nat.nlt_ge in Hbg.
  specialize (Hgbe 0 (le_refl _)).
  rewrite Nat.add_0_r in Hgbe.
  now replace (g b) with b by flia Hgbe.
}
rewrite rngl_summation_split_first; [ symmetry | easy | flia ].
rewrite rngl_summation_split_first; [ symmetry | easy | flia ].
rewrite Nat.add_0_r.
destruct (lt_dec b (g b)) as [Hgb| Hgb]. {
  f_equal.
  do 2 rewrite rngl_summation_succ_succ.
  erewrite rngl_summation_eq_compat. 2: {
    intros * Hi.
    now rewrite <- Nat.add_succ_comm.
  }
  symmetry.
  erewrite rngl_summation_eq_compat. 2: {
    intros * Hi.
    now rewrite <- Nat.add_succ_comm.
  }
  symmetry.
...
  rewrite IHlen with (g := λ i, g (i - 1)); cycle 1. {
    intros i Hi.
    specialize (Hgbe i) as H1.
...
    assert (H : S i ≤ S len) by flia Hi.
    specialize (H1 H); clear H.
    do 2 rewrite Nat.add_succ_comm.
    split; [ | easy ].
...
  rewrite IHlen; cycle 1. {
    intros i Hi.
    specialize (Hgbe (S i)) as H1.
    assert (H : S i ≤ S len) by flia Hi.
    specialize (H1 H); clear H.
    do 2 rewrite Nat.add_succ_comm.
    split; [ | easy ].
    destruct (Nat.eq_dec (g (b + S i)) b) as [Hgbi| Hgbi]; [ | flia H1 Hgbi ].
...
  rewrite IHlen; cycle 1. {
    intros i Hi.
    specialize (Hgbe i) as H1.
    specialize (Hgii i) as H2.
    specialize (Hggi i) as H3.
    assert (H : b ≤ i ≤ S b + len) by flia Hi.
    specialize (H1 H).
    specialize (H2 H).
    specialize (H3 H); clear H.
    split; [ | easy ].
    destruct (Nat.eq_dec b (g i)) as [Hbg| Hbg]; [ | flia H1 Hbg ].
    subst b.
    specialize (Hgbe (g i)) as H4.
    specialize (Hgii (g i)) as H5.
    specialize (Hggi (g i)) as H6.
    rewrite H3 in H4, H5, H6.
    clear H1 H5 H6.
    rewrite H3 in Hgb.
...
*)

(*
Theorem summation_pair : ∀ b e f g,
  (∀ i, b ≤ i ≤ e → b ≤ g i ≤ e)
  → (∀ i, b ≤ i ≤ e → g i ≠ i)
  → (∀ i, b ≤ i ≤ e → g (g i) = i)
  → (Σ (i = b, e), f i =
     Σ (i = b, e), if lt_dec i (g i) then f i + f (g i) else 0)%F.
Proof.
intros * Hgbe Hgii Hggi.
destruct (le_dec b e) as [Hbe| Hbe]. 2: {
  apply Nat.nle_gt in Hbe.
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_empty; [ | easy ].
  easy.
}
...
(* experimentation by looking at the first item *)
rewrite rngl_summation_split_first; [ symmetry | easy | easy ].
rewrite rngl_summation_split_first; [ symmetry | easy | easy ].
destruct (lt_dec b (g b)) as [Hbg| Hbg]. 2: {
  apply Nat.nlt_ge in Hbg.
  specialize (Hgbe b) as H1.
  specialize (Hgii b) as H2.
  assert (H : b ≤ b ≤ e) by flia Hbe.
  specialize (H1 H); specialize (H2 H); clear H.
  flia Hbg H1 H2.
}
rewrite <- rngl_add_assoc; f_equal.
symmetry.
rewrite (rngl_summation_split _ (g b)). 2: {
  split; [ flia Hbg | ].
  apply -> Nat.succ_le_mono.
  apply Hgbe; flia Hbe.
}
rewrite rngl_summation_split_last; [ | easy ].
rewrite Hggi; [ | flia Hbe ].
destruct (lt_dec (g b) b) as [H| H]; [ flia Hbg H | clear H ].
rewrite rngl_add_0_r.
symmetry.
rewrite (rngl_summation_split _ (g b)). 2: {
  split; [ flia Hbg | ].
  apply -> Nat.succ_le_mono.
  apply Hgbe; flia Hbe.
}
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_add_comm, rngl_add_assoc, rngl_add_comm.
f_equal; rewrite rngl_add_comm.
...
unfold iter_seq.
remember (S e - b) as len eqn:Hlen.
replace e with (b + len - 1) in Hg by flia Hbe Hlen.
(*
assert (H : ∀ i, i < len → g (b + i) < b + len ∧ g (b + i) ≠ b + i). {
  intros i Hi.
  specialize (Hg (b + i)).
  assert (H : b ≤ b + i ≤ e). {
    split; [ flia | ].
    flia Hbe Hi Hlen.
  }
  specialize (Hg H); clear H.
  split; [ | easy ].
  flia Hg Hlen.
}
move H before Hg; clear Hg; rename H into Hg.
*)
clear e Hbe Hlen.
revert b Hg.
induction len; intros; [ easy | ].
cbn.
(*
destruct len. {
  cbn.
  specialize (Hg b).
  rewrite Nat.add_sub in Hg.
  assert (H : b ≤ b ≤ b) by flia.
  specialize (Hg H); clear H.
  flia Hg.
}
*)
do 2 rewrite rngl_add_0_l.
rewrite fold_left_rngl_add_fun_from_0; [ symmetry | easy ].
rewrite fold_left_rngl_add_fun_from_0; [ symmetry | easy ].
destruct (lt_dec b (g b)) as [Hgb| Hgb]. {
  rewrite <- rngl_add_assoc.
  f_equal.
...
  rewrite <- IHlen. 2: {
    intros i Hi.
    specialize (Hg i) as H1.
    assert (H : b ≤ i ≤ b + S len - 1) by flia Hi Hgb.
    specialize (H1 H); clear H.
    split; [ | easy ].
    split; [ | flia H1 ].
...
    do 2 rewrite Nat.add_succ_comm.
    apply Hg; flia Hi.
  }
...
             fold_left (λ (c : T) (i : nat), c + f i) (seq (S b) len) 0%F =
  (f (g b) + fold_left (λ (c : T) (i : nat), c + f i) (seq (S b) len) 0)%F

  (f b + fold_left (λ (c : T) (i : nat), c + f i) (seq (S b) len) 0)%F =
         fold_left (λ (c : T) (i : nat), c + f i) (seq (S b) len) 0%F
...
*)

(* null matrix of dimension m × n *)

Definition mZ m n : matrix m n T :=
  mk_mat m n (λ i j, 0%F).

(* identity square matrix of dimension n *)

Definition mI n : matrix n n T :=
  mk_mat n n (λ i j, if Nat.eq_dec i j then 1%F else 0%F).

End a.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Arguments mat_mul_scal_l {T ro m n} s%F M%M.
Arguments mat_opp {T}%type {ro} {m n}%nat.
Arguments mat_sub {T ro m n} MA%M MB%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments minus_one_pow {T ro}.
Arguments vect_zero {T ro} n%nat.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments mat_mul_vect_r {T ro m n} M%M V%V.
Arguments vect_mul_scal_l {T ro} s%F {n}%nat V%V.
Arguments vect_dot_product {T}%type {ro n} (U V)%V.
Arguments vect_el {n}%nat {T}%type v%V.

Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "U · V" := (vect_dot_product U V) (at level 40) : V_scope.

Theorem fold_mat_sub : ∀ m n (MA MB : matrix m n T), (MA + - MB = MA - MB)%M.
Proof. easy. Qed.

(* commutativity of addition *)

Theorem mat_add_comm : ∀ {m n} (MA MB : matrix m n T), (MA + MB = MB + MA)%M.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj.
apply rngl_add_comm.
Qed.

(* associativity of addition *)

Theorem mat_add_add_swap : ∀ {m n} (MA MB MC : matrix m n T),
  (MA + MB + MC = MA + MC + MB)%M.
Proof.
intros.
apply matrix_eq.
intros i j Hi Hj.
apply rngl_add_add_swap.
Qed.

Theorem mat_add_assoc : ∀ {m n} (MA MB MC : matrix m n T),
  (MA + (MB + MC) = (MA + MB) + MC)%M.
Proof.
intros.
apply matrix_eq.
intros i j Hi Hj.
apply rngl_add_assoc.
Qed.

(* addition to zero *)

Theorem mat_add_0_l : ∀ {m n} (M : matrix m n T), (mZ m n + M)%M = M.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj.
apply rngl_add_0_l.
Qed.

(* addition left and right with opposite *)

Theorem mat_add_opp_l {m n} :
  rngl_has_opp = true →
  ∀ (M : matrix m n T), (- M + M = mZ m n)%M.
Proof.
intros Hro *.
apply matrix_eq; cbn.
intros * Hi Hj.
now apply rngl_add_opp_l.
Qed.

Theorem mat_add_opp_r {m n} :
  rngl_has_opp = true →
  ∀ (M : matrix m n T), (M - M = mZ m n)%M.
Proof.
intros Hro *.
apply matrix_eq; cbn.
intros * Hi Hj.
specialize rngl_add_opp_r as H.
unfold rngl_sub in H.
rewrite Hro in H.
apply H.
Qed.

(* multiplication left and right with identity *)

Theorem mat_mul_1_l : ∀ {n} (M : matrix n n T), (mI n * M)%M = M.
Proof.
intros.
apply matrix_eq.
cbn - [ iter_seq ].
intros * Hi Hj.
rewrite (rngl_summation_split _ i); [ | flia Hi ].
rewrite rngl_summation_split_last; [ | flia ].
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
rewrite rngl_mul_1_l.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l.
}
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i k) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l.
}
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

Theorem mat_mul_1_r : ∀ {n} (M : matrix n n T), (M * mI n)%M = M.
Proof.
intros.
apply matrix_eq.
cbn - [ iter_seq ].
intros * Hi Hj.
rewrite (rngl_summation_split _ j); [ | flia Hj ].
rewrite rngl_summation_split_last; [ | flia ].
destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
rewrite rngl_mul_1_r.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec (k - 1) j) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_r.
}
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec k j) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_r.
}
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

Theorem vect_mul_1_l : ∀ {n} (V : vector n T), (mI n • V)%V = V.
Proof.
intros.
apply vector_eq.
cbn - [ iter_seq ].
intros * Hi.
rewrite (rngl_summation_split _ i); [ | flia Hi ].
rewrite rngl_summation_split_last; [ | flia ].
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
rewrite rngl_mul_1_l.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l.
}
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i k) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l.
}
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

(* associativity of multiplication *)

Theorem mat_mul_assoc {m n p q} :
  ∀ (MA : matrix m n T) (MB : matrix n p T) (MC : matrix p q T),
  (MA * (MB * MC))%M = ((MA * MB) * MC)%M.
Proof.
intros.
apply matrix_eq.
intros i j Hi Hj.
cbn - [ iter_seq ].
cbn in Hi, Hj.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  now apply rngl_mul_summation_distr_l.
}
cbn - [ iter_seq ].
rewrite rngl_summation_summation_exch'; [ | easy ].
apply rngl_summation_eq_compat.
intros k Hk.
erewrite rngl_summation_eq_compat. 2: {
  intros l Hl.
  now rewrite rngl_mul_assoc.
}
cbn - [ iter_seq ].
symmetry.
now apply rngl_mul_summation_distr_r.
Qed.

(* left distributivity of multiplication over addition *)

Theorem mat_mul_add_distr_l {m n p} :
  ∀ (MA : matrix m n T) (MB : matrix n p T) (MC : matrix n p T),
  (MA * (MB + MC) = MA * MB + MA * MC)%M.
Proof.
intros.
apply matrix_eq.
intros i j Hi Hj.
cbn - [ iter_seq ].
cbn in Hi, Hj.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  apply rngl_mul_add_distr_l.
}
cbn - [ iter_seq ].
now apply rngl_summation_add_distr.
Qed.

(* right distributivity of multiplication over addition *)

Theorem mat_mul_add_distr_r {m n p} :
  ∀ (MA : matrix m n T) (MB : matrix m n T) (MC : matrix n p T),
  ((MA + MB) * MC = MA * MC + MB * MC)%M.
Proof.
intros.
apply matrix_eq.
intros i j Hi Hj.
cbn - [ iter_seq ].
cbn in Hi, Hj.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  apply rngl_mul_add_distr_r.
}
cbn - [ iter_seq ].
now rewrite rngl_summation_add_distr.
Qed.

(* left distributivity of multiplication by scalar over addition *)

Theorem mat_mul_scal_l_add_distr_r {m n} : ∀ a b (M : matrix m n T),
  ((a + b)%F × M)%M = (a × M + b × M)%M.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj; cbn.
apply rngl_mul_add_distr_r.
Qed.

(* associativity of multiplication by scalar *)

Theorem mat_mul_scal_l_mul_assoc {m n} : ∀ a b (M : matrix m n T),
  (a × (b × M))%M = ((a * b)%F × M)%M.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj; cbn.
apply rngl_mul_assoc.
Qed.

Theorem vect_mul_scal_l_mul_assoc {n} : ∀ a b (V : vector n T),
  (a × (b × V))%V = ((a * b)%F × V)%V.
Proof.
intros.
apply vector_eq.
intros * Hi; cbn.
apply rngl_mul_assoc.
Qed.

Theorem vect_mul_scal_reg_r :
  rngl_has_dec_eq = true →
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  ∀ {n} (V : vector n T) a b,
  V ≠ vect_zero n
  → (a × V = b × V)%V
  → a = b.
Proof.
intros Hde Hii * Hvz Hab.
assert (Hiv : ∀ i, vect_el (a × V)%V i = vect_el (b × V)%V i). {
  intros i.
  now rewrite Hab.
}
unfold vect_mul_scal_l in Hiv.
cbn in Hiv.
assert (Hn : ¬ ∀ i, i < n → vect_el V i = 0%F). {
  intros H; apply Hvz.
  apply vector_eq.
  cbn; intros * Hi.
  now apply H.
}
assert (∃ i, vect_el V i ≠ 0%F). {
  specialize rngl_opt_eq_dec as rngl_eq_dec.
  rewrite Hde in rngl_eq_dec.
  apply (not_forall_in_interv_imp_exist (a:=0) (b:=n-1));
    cycle 1. {
    flia.
  } {
    intros Hnv.
    apply Hn.
    intros i Hi.
    specialize (Hnv i).
    assert (H : 0 ≤ i ≤ n - 1) by flia Hi.
    specialize (Hnv H).
    now destruct (rngl_eq_dec (vect_el V i) 0%F).
  }
  intros k.
  unfold Decidable.decidable.
  specialize (rngl_eq_dec (vect_el V k) 0%F) as [Hvnz| Hvnz]. {
    now right.
  } {
    now left.
  }
}
move Hiv at bottom.
destruct H as (i, Hi).
specialize (Hiv i).
now apply rngl_mul_reg_r in Hiv.
Qed.

Theorem mat_mul_mul_scal_l :
  rngl_is_comm = true →
  ∀ {m n p} a (MA : matrix m n T) (MB : matrix n p T),
  (MA * (a × MB) = a × (MA * MB))%M.
Proof.
intros Hic *.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
apply matrix_eq.
intros * Hi Hj.
cbn - [ iter_seq ].
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros k Hk.
rewrite rngl_mul_comm.
rewrite <- rngl_mul_assoc.
f_equal.
apply rngl_mul_comm.
Qed.

Theorem mat_mul_scal_add_distr_l : ∀ {m n} a (MA MB : matrix m n T),
  (a × (MA + MB) = (a × MA + a × MB))%M.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj.
apply rngl_mul_add_distr_l.
Qed.

(* associativity with multiplication with vector *)

Theorem mat_vect_mul_assoc_as_sums :
  ∀ {m n p} (A : matrix m n T) (B : matrix n p T) (V : vector p T) i,
  i < m
  → (Σ (j = 0, n - 1),
       mat_el A i j *
       (Σ (k = 0, p - 1), mat_el B j k * vect_el V k))%F =
    (Σ (j = 0, p - 1),
       (Σ (k = 0, n - 1), mat_el A i k * mat_el B k j) *
       vect_el V j)%F.
Proof.
intros * Hi.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  now rewrite rngl_mul_summation_distr_l.
}
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  now rewrite rngl_mul_summation_distr_r.
}
symmetry.
cbn - [ iter_seq ].
rewrite rngl_summation_summation_exch'; [ | easy ].
apply rngl_summation_eq_compat.
intros j Hj.
apply rngl_summation_eq_compat.
intros k Hk.
apply rngl_mul_assoc.
Qed.

Theorem mat_vect_mul_assoc {m n p} :
  ∀ (A : matrix m n T) (B : matrix n p T) (V : vector p T),
  (A • (B • V) = (A * B) • V)%V.
Proof.
intros.
apply vector_eq.
intros i Hi.
cbn in Hi.
unfold mat_mul_vect_r.
unfold mat_mul.
cbn - [ iter_seq ].
now apply mat_vect_mul_assoc_as_sums.
Qed.

Theorem mat_mul_scal_vect_assoc {m n} :
  ∀ a (MA : matrix m n T) (V : vector n T), (a × (MA • V) = (a × MA) • V)%V.
Proof.
intros.
apply vector_eq.
intros i Hi.
cbn in Hi.
cbn - [ iter_seq ].
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros j Hj.
apply rngl_mul_assoc.
Qed.

Theorem mat_mul_scal_vect_comm :
  rngl_is_comm = true →
  ∀ {m n} a (MA : matrix m n T) V, (a × (MA • V) = MA • (a × V))%V.
Proof.
intros Hic *.
apply vector_eq.
intros i Hi.
cbn in Hi.
cbn - [ iter_seq ].
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros j Hj.
do 2 rewrite rngl_mul_assoc.
f_equal.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
apply rngl_mul_comm.
Qed.

Theorem vect_dot_mul_scal_mul_comm :
  rngl_is_comm = true →
  ∀ {n} (a : T) (U V : vector n T),
  (U · (a × V) = (a * (U · V))%F)%V.
Proof.
intros Hic *.
unfold vect_dot_product.
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros j Hj; cbn.
do 2 rewrite rngl_mul_assoc.
f_equal.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
apply rngl_mul_comm.
Qed.

Theorem vect_scal_mul_dot_mul_comm : ∀ {n} (a : T) (U V : vector n T),
  ((a × U) · V = (a * (U · V))%F)%V.
Proof.
intros.
unfold vect_dot_product.
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros j Hj; cbn.
symmetry; apply rngl_mul_assoc.
Qed.

(* matrix transpose *)

Definition mat_transp {m n} (M : matrix m n T) : matrix n m T :=
  {| mat_el i j := mat_el M j i |}.

(* matrix without row i and column j *)

Definition subm {m n} (M : matrix m n T) i j :=
  mk_mat (m - 1) (n - 1)
    (λ k l, mat_el M (k + Nat.b2n (i <=? k)) (l + Nat.b2n (j <=? l))).

(* combinations of submatrix and other *)

Theorem submatrix_sub {m n} : ∀ (MA MB : matrix m n T) i j,
  subm (MA - MB)%M i j = (subm MA i j - subm MB i j)%M.
Proof.
intros.
apply matrix_eq.
intros k l Hk Hl; cbn.
now destruct (lt_dec k i), (lt_dec l j).
Qed.

Theorem submatrix_mul_scal_l {m n} : ∀ (μ : T) (M : matrix m n T) i j,
  subm (μ × M)%M i j = (μ × subm M i j)%M.
Proof.
intros.
apply matrix_eq.
intros k l Hk Hl; cbn.
now destruct (lt_dec k i), (lt_dec l j).
Qed.

Theorem submatrix_mI : ∀ i r, subm (mI r) i i = mI (r - 1).
Proof.
intros.
apply matrix_eq.
intros k l Hk Hl; cbn.
remember (i <=? k) as ki eqn:Hki; symmetry in Hki.
remember (i <=? l) as li eqn:Hli; symmetry in Hli.
destruct ki; cbn. {
  destruct li; cbn. {
    destruct (Nat.eq_dec (k + 1) (l + 1)) as [Hkl1| Hkl1]. {
      destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ easy | flia Hkl1 Hkl ].
    } {
      destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ flia Hkl1 Hkl | easy ].
    }
  } {
    rewrite Nat.add_0_r.
    apply Nat.leb_le in Hki; apply Nat.leb_nle in Hli.
    destruct (Nat.eq_dec (k + 1) l) as [Hkl1| Hkl1]; [ flia Hki Hli Hkl1 | ].
    destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ flia Hki Hli Hkl | easy ].
  }
} {
  rewrite Nat.add_0_r.
  destruct li; cbn. {
    apply Nat.leb_nle in Hki; apply Nat.leb_le in Hli.
    destruct (Nat.eq_dec k (l + 1)) as [Hkl1| Hkl1]; [ flia Hki Hli Hkl1 | ].
    destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ flia Hki Hli Hkl | easy ].
  } {
    now rewrite Nat.add_0_r.
  }
}
Qed.

Theorem mat_mul_scal_1_l {m n} : ∀ (M : matrix m n T), (1 × M = M)%M.
Proof.
intros.
apply matrix_eq; cbn.
intros * Hi Hj.
apply rngl_mul_1_l.
Qed.

Definition phony_mat_le n (MA MB : matrix n n T) := True.
Definition phony_mat_div n (MA MB : matrix n n T) := MA.
Definition phony_mat_inv n (M : matrix n n T) := M.

Definition at_least_1 n := S (n - 1).

Canonical Structure mat_ring_like_op n :
  ring_like_op (matrix n n T) :=
  {| rngl_has_opp := true;
     rngl_has_inv := false;
     rngl_has_no_inv_but_div := false;
     rngl_zero := mZ n n;
     rngl_one := mI n;
     rngl_add := @mat_add T _ n n;
     rngl_mul := @mat_mul T _ n n n;
     rngl_opp := @mat_opp T _ n n;
     rngl_inv := @phony_mat_inv n;
     rngl_le := @phony_mat_le n;
     rngl_opt_sub := @mat_sub T ro n n;
     rngl_opt_div := @phony_mat_div n |}.

(**)
Existing Instance mat_ring_like_op.
(**)

Context {Hro : @rngl_has_opp T ro = true}.

Theorem mat_opt_add_opp_l : ∀ n,
  if @rngl_has_opp (matrix n n T) _ then
    ∀ a : matrix n n T, (- a + a)%F = 0%F
  else True.
Proof.
intros.
remember rngl_has_opp as x eqn:Hx in |-*; symmetry in Hx.
destruct x; [ | easy ].
intros MA.
now apply mat_add_opp_l.
Qed.

Theorem mat_opt_add_sub : ∀ n,
  if @rngl_has_opp (matrix n n T) _ then not_applicable
  else ∀ a b : matrix n n T, (a + b - b)%F = a.
Proof.
intros.
specialize rngl_opt_add_sub as rngl_add_sub.
cbn in rngl_add_sub.
unfold mat_ring_like_op; cbn.
now destruct (@rngl_has_opp T ro).
Qed.

Theorem mat_characteristic_prop : ∀ n,
  match
    match Nat.eq_dec n O return nat with
    | left _ => S O
    | right x => rngl_characteristic
    end return Prop
  with
  | O =>
      forall i : nat,
      not
        (@eq (matrix n n T) (@rngl_of_nat (matrix n n T) (mat_ring_like_op n) (S i))
           (@rngl_zero (matrix n n T) (mat_ring_like_op n)))
  | S _ =>
      @eq (matrix n n T)
        (@rngl_of_nat (matrix n n T) (mat_ring_like_op n)
           match Nat.eq_dec n O return nat with
           | left _ => S O
           | right x => rngl_characteristic
           end) (@rngl_zero (matrix n n T) (mat_ring_like_op n))
  end.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  now apply matrix_eq.
}
remember rngl_characteristic as c eqn:Hc.
symmetry in Hc.
specialize (rngl_characteristic_prop) as Hcp.
rewrite Hc in Hcp.
destruct c. {
  intros.
  apply matrix_neq; cbn.
  intros H.
  destruct n; [ easy | ].
  specialize (H 0 0 (Nat.lt_0_succ _) (Nat.lt_0_succ _)).
  cbn in H.
  replace
    (@mat_el (S n) (S n) T
       (@rngl_of_nat (matrix (S n) (S n) T) (mat_ring_like_op (S n)) i)
       0 0)%F
  with (@rngl_of_nat T ro i) in H. 2: {
    clear H.
    induction i; [ easy | cbn ].
    now rewrite <- IHi.
  }
  now specialize (Hcp i).
}
cbn in Hcp |-*.
apply matrix_eq; cbn.
intros * Hi Hn.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  replace
    (@mat_el n n T (@rngl_of_nat (matrix n n T) (mat_ring_like_op n) c) i i)%F
  with (@rngl_of_nat T ro c). 2: {
    clear Hc.
    clear Hcp.
    induction c; [ easy | cbn ].
    destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
    now rewrite <- IHc.
  }
  easy.
}
rewrite rngl_add_0_l.
clear Hc Hcp.
induction c; [ easy | cbn ].
destruct (Nat.eq_dec i j) as [H| H]; [ easy | clear H ].
now rewrite rngl_add_0_l.
Qed.

Theorem mat_opt_eq_dec : ∀ n,
  if rngl_has_dec_eq then ∀ a b : matrix n n T, {a = b} + {a ≠ b}
  else not_applicable.
Proof.
intros.
specialize rngl_opt_eq_dec as rngl_eq_dec.
remember rngl_has_dec_eq as x eqn:Hde; symmetry in Hde.
destruct x; [ | easy ].
intros MA MB.
destruct MA as (fa).
destruct MB as (fb).
assert (∀ i j, {fa i j = fb i j} + {fa i j ≠ fb i j}). {
  intros.
  apply rngl_eq_dec.
}
induction n; intros; [ now left; apply matrix_eq | ].
destruct IHn as [IHn| IHn]. {
  injection IHn; clear IHn; intros IHn.
  now left; subst fb.
} {
  right.
  intros H1; apply IHn; clear IHn.
  injection H1; clear H1; intros H1.
  now subst fb.
}
Qed.

Theorem mat_1_neq_0 : ∀ n,
  if rngl_has_1_neq_0 && negb (n =? 0) then @mI T ro n ≠ mZ n n
  else not_applicable.
Proof.
intros.
specialize rngl_opt_1_neq_0 as rngl_1_neq_0.
remember (rngl_has_1_neq_0 && negb (n =? 0)) as b eqn:Hb.
symmetry in Hb.
destruct b; [ | easy ].
apply Bool.andb_true_iff in Hb.
destruct Hb as (H10, Hb).
apply Bool.negb_true_iff in Hb.
apply Nat.eqb_neq in Hb.
rewrite H10 in rngl_1_neq_0.
apply matrix_neq.
intros H; cbn in H.
destruct n; [ easy | ].
now specialize (H 0 0 (Nat.lt_0_succ _) (Nat.lt_0_succ _)).
Qed.

Theorem mat_consistent : ∀ n,
  let TM := matrix n n T in
  let rom := mat_ring_like_op n in
  (@rngl_has_inv TM rom = false ∨ @rngl_has_no_inv_but_div TM rom = false).
Proof. now intros; now right. Qed.

Definition mat_ring_like_prop (n : nat) :
  ring_like_prop (matrix n n T) :=
  {| rngl_is_comm := false;
     rngl_has_dec_eq := @rngl_has_dec_eq T ro rp;
     rngl_has_dec_le := false;
     rngl_has_1_neq_0 := (rngl_has_1_neq_0 && negb (Nat.eqb n 0))%bool;
     rngl_is_ordered := false;
     rngl_is_integral := false;
     rngl_characteristic := if Nat.eq_dec n 0 then 1 else rngl_characteristic;
     rngl_add_comm := mat_add_comm;
     rngl_add_assoc := mat_add_assoc;
     rngl_add_0_l := mat_add_0_l;
     rngl_mul_assoc := mat_mul_assoc;
     rngl_mul_1_l := mat_mul_1_l;
     rngl_mul_add_distr_l := mat_mul_add_distr_l;
     rngl_opt_1_neq_0 := @mat_1_neq_0 n;
     rngl_opt_mul_comm := NA;
     rngl_opt_mul_1_r := mat_mul_1_r;
     rngl_opt_mul_add_distr_r := mat_mul_add_distr_r;
     rngl_opt_add_opp_l := @mat_opt_add_opp_l n;
     rngl_opt_add_sub := mat_opt_add_sub n;
     rngl_opt_mul_0_l := NA;
     rngl_opt_mul_0_r := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div_l := NA;
     rngl_opt_mul_div_r := NA;
     rngl_opt_eq_dec := mat_opt_eq_dec n;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := NA;
     rngl_characteristic_prop := @mat_characteristic_prop n;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA;
     rngl_consistent := mat_consistent n |}.

Theorem vect_opt_eq_dec :
  rngl_has_dec_eq = true →
  ∀ n (U V : vector n T), {U = V} + {U ≠ V}.
Proof.
intros Hed *.
specialize rngl_opt_eq_dec as rngl_eq_dec.
rewrite Hed in rngl_eq_dec.
destruct U as (fu).
destruct V as (fv).
assert (H : ∀ i, {fu i = fv i} + {fu i ≠ fv i}). {
  intros.
  apply rngl_eq_dec.
}
induction n; intros; [ now left; apply vector_eq | ].
destruct IHn as [IHn| IHn]. {
  injection IHn; clear IHn; intros IHn.
  now left; subst fv.
} {
  right.
  intros H1; apply IHn; clear IHn.
  injection H1; clear H1; intros H1.
  now subst fv.
}
Qed.

Theorem mat_vect_mul_0_r : ∀ m n (M : matrix m n T),
  (M • vect_zero _ = vect_zero _)%V.
Proof.
intros.
apply vector_eq.
intros i Hi.
cbn - [ iter_seq ].
rewrite <- rngl_mul_summation_distr_r.
apply rngl_mul_0_r.
Qed.

(* *)

End a.

Module matrix_Notations.

Declare Scope M_scope.
Declare Scope V_scope.
Delimit Scope M_scope with M.
Delimit Scope V_scope with V.

Arguments mat_el [m n]%nat [T]%type M%M (i j)%nat : rename.
Arguments mat_add_opp_r {T}%type {ro rp} {m n}%nat Hro M%M.
Arguments mat_mul_mul_scal_l {T}%type {ro rp} Hic {m n p}%nat a%F MA%M.
Arguments mat_mul_scal_l {T ro} {m n}%nat s%F M%M.
Arguments mat_mul_vect_r {T ro} {m n}%nat M%M V%V.
Arguments mat_mul_scal_vect_comm {T}%type {ro rp} Hic {m n}%nat a%F MA%M V%V.
Arguments mat_mul_scal_vect_assoc {T}%type {ro rp} {m n}%nat a%F MA%M V%V.
Arguments mat_vect_mul_assoc {T}%type {ro rp} {m n p}%nat (A B)%M V%V.
Arguments mat_mul_1_l {T}%type {ro rp} {n}%nat M%M.
Arguments mat_mul_1_r {T}%type {ro rp} {n}%nat M%M.
Arguments mat_opp {T ro} {m n}%nat M%M.
Arguments mat_sub {T ro} {m n}%nat MA%M MB%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments minus_one_pow {T ro}.
Arguments subm {T} {m n}%nat M%M i%nat j%nat.
Arguments vect_add {T ro} {n}%nat U%V V%V.
Arguments vect_sub {T ro} {n}%nat U%V V%V.
Arguments vect_opp {T ro} {n}%nat V%V.
Arguments vect_mul_scal_l {T ro} s%F {n}%nat V%V.
Arguments vect_mul_scal_reg_r {T}%type {ro rp} Hde Hii {n}%nat V%V (a b)%F.
Arguments vect_mul_1_l {T}%type {ro rp} {n}%nat V%V.
Arguments vect_zero {T ro} n%nat.
Arguments vect_dot_product {T}%type {ro} {n}%nat (U V)%V.
Arguments vect_dot_mul_scal_mul_comm {T}%type {ro rp} Hic {n}%nat a%F (U V)%V.
Arguments vect_scal_mul_dot_mul_comm {T}%type {ro rp} {n}%nat a%F (U V)%V.
Arguments vect_opt_eq_dec {T}%type {ro rp} _ n%nat U%V V%V.
Arguments vect_el {n}%nat {T}%type v%V c%nat.
Arguments vect_squ_norm {T}%type {ro} {n}%nat V%V.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.
Notation "A ⁺" := (mat_transp A) (at level 1, format "A ⁺") : M_scope.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "U - V" := (vect_sub U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.
Notation "U · V" := (vect_dot_product U V) (at level 40) : V_scope.
Notation "- V" := (vect_opp V) : V_scope.

End matrix_Notations.
