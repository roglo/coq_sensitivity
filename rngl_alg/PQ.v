(* Implementation of positive (non zero) rationals using only nat *)

From Stdlib Require Import Utf8 Arith Morphisms.
Require Import RingLike.Misc Misc.

Set Nested Proofs Allowed.

Reserved Notation "a // b" (at level 32, format "a // b").

(* Non null natural
   Natural numbers excluding 0.
   Represented by a nat "n" meaning "n+1" *)

Record nnn := mknn { nn : nat }.

Declare Scope nnn_scope.
Delimit Scope nnn_scope with n.
Bind Scope nnn_scope with nnn.

(* A PQ number {PQnum1:=a; PQden1:=b} represents the rational (a+1)/(b+1) *)

Record PQ := PQmake { PQnum1 : nnn; PQden1 : nnn }.

Declare Scope PQ_scope.
Delimit Scope PQ_scope with PQ.
Bind Scope PQ_scope with PQ.

Definition PQ_of_pair n d := PQmake (mknn (n - 1)) (mknn (d - 1)).
Definition nd x y := (nn (PQnum1 x) + 1) * (nn (PQden1 y) + 1).
Definition PQeq x y := nd x y = nd y x.

Theorem PQeq_dec : ∀ x y : PQ, {PQeq x y} + {¬ PQeq x y}.
Proof. intros; apply Nat.eq_dec. Qed.

Definition if_PQeq {A} (P Q : A) x y := if PQeq_dec x y then P else Q.

Definition PQlt x y := nd x y < nd y x.
Definition PQle x y := nd x y ≤ nd y x.
Definition PQgt x y := PQlt y x.
Definition PQge x y := PQle y x.

(* addition, subtraction *)
(* no opp : there are no negative numbers of type PQ
   but like for nat, a subtraction can be defined *)

Definition PQadd_num1 x y := nd x y + nd y x - 1.
Definition PQsub_num1 x y := nd x y - nd y x - 1.
Definition PQadd_den1 x y := (nn (PQden1 x) + 1) * (nn (PQden1 y) + 1) - 1.

Definition PQadd x y :=
  PQmake (mknn (PQadd_num1 x y)) (mknn (PQadd_den1 x y)).
Definition PQsub x y :=
  PQmake (mknn (PQsub_num1 x y)) (mknn (PQadd_den1 x y)).

(* multiplication, inversion, division *)
(* unlike opp, inv exists in PQ *)

Definition PQinv x := PQmake (PQden1 x) (PQnum1 x).

Definition PQmul_num1 x y := (nn (PQnum1 x) + 1) * (nn (PQnum1 y) + 1) - 1.
Definition PQmul_den1 x y := (nn (PQden1 x) + 1) * (nn (PQden1 y) + 1) - 1.

Definition PQmul x y :=
  PQmake (mknn (PQmul_num1 x y)) (mknn (PQmul_den1 x y)).
Definition PQdiv x y :=
  PQmul x (PQinv y).

Module PQ_Notations.

Notation "a ╱ b" := (PQmake a b) (at level 1, format "a ╱ b") : PQ_scope.
Notation "x == y" := (PQeq x y) (at level 70) : PQ_scope.
Notation "x ≠≠ y" := (¬ PQeq x y) (at level 70) : PQ_scope.
Notation "'if_PQeq_dec' x y 'then' P 'else' Q" :=
  (if_PQeq P Q x y) (at level 200, x at level 9, y at level 9).
Notation "x < y" := (PQlt x y) : PQ_scope.
Notation "x ≤ y" := (PQle x y) : PQ_scope.
Notation "x > y" := (PQgt x y) : PQ_scope.
Notation "x ≥ y" := (PQge x y) : PQ_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%PQ (at level 70, y at next level) :
  PQ_scope.
Notation "x + y" := (PQadd x y) : PQ_scope.
Notation "x - y" := (PQsub x y) : PQ_scope.
Notation "x * y" := (PQmul x y) : PQ_scope.
Notation "x / y" := (PQdiv x y) : PQ_scope.
Notation "¹/ x" := (PQinv x) (at level 35, right associativity) : PQ_scope.

Definition PQ_of_decimal_uint (n : Decimal.uint) : option PQ :=
  let a := Nat.of_uint n in
  if Nat.eq_dec a 0 then None
  else Some (PQ_of_pair a 1).

Definition PQ_of_decimal_int (n : Decimal.int) : option PQ :=
  match n with
  | Decimal.Pos ui => PQ_of_decimal_uint ui
  | Decimal.Neg ui => None
  end.

Definition PQ_of_numeral_int (n : Number.int) : option PQ :=
  match n with
  | Number.IntDecimal n => PQ_of_decimal_int n
  | Number.IntHexadecimal _ => None
  end.

Definition PQ_to_numeral_uint (pq : PQ) : option Number.uint :=
  match nn (PQden1 pq) with
  | 0 => Some (Number.UIntDecimal (Nat.to_uint (nn (PQnum1 pq) + 1)))
  | _ => None
  end.

Number Notation PQ PQ_of_numeral_int PQ_to_numeral_uint : PQ_scope.

(* *)

Definition nnn_of_decimal_uint (n : Decimal.uint) : option nnn :=
  let a := Nat.of_uint n in
  if Nat.eq_dec a 0 then None
  else Some (mknn (a - 1)).

Definition nnn_of_decimal_int (n : Decimal.int) : option nnn :=
  match n with
  | Decimal.Pos ui => nnn_of_decimal_uint ui
  | Decimal.Neg ui => None
  end.

(* *)

Definition nnn_of_numeral_int (n : Number.int) : option nnn :=
  match n with
  | Number.IntDecimal n => nnn_of_decimal_int n
  | Number.IntHexadecimal _ => None
  end.

Definition nnn_to_numeral_uint (nn1 : nnn) : option Number.uint :=
  Some (Number.UIntDecimal (Nat.to_uint (nn nn1 + 1))).

Number Notation nnn nnn_of_numeral_int nnn_to_numeral_uint : nnn_scope.

(*
Check (12 - 7)%PQ.
Check 25%PQ.
Check (22 / 7)%PQ.
Print PQ.
Check (PQmake 22 7 / 7)%PQ.
Compute (22 / 7)%PQ.
Compute (22 / 1)%PQ.
Check (mknn 21).
Check 3%PQ.
Compute 3%PQ.
Check (3//2)%PQ.
Compute (3//2)%PQ.
(* *)
Print PQ.
Check (3/2)%PQ.
Compute (PQnum1 (3/2)).
Compute (PQden1 (3/2)).
Check (3/2)%PQ.
Check (PQinv (3//2)%PQ).
Compute (PQinv (3//2)%PQ).
Compute (2//3 / 4 // 15)%PQ.
Fail Check 0%PQ.
*)

End PQ_Notations.

Import PQ_Notations.

Definition PQone x := PQmake (PQden1 x) (PQden1 x).
Definition PQ_of_nat n := PQmake (mknn (n - 1)) 1.

(* equality *)

Theorem PQeq_refl : ∀ x : PQ, (x == x)%PQ.
Proof. easy. Qed.

Theorem PQeq_symm : ∀ x y : PQ, (x == y)%PQ → (y == x)%PQ.
Proof. easy. Qed.

Theorem PQeq_trans : ∀ x y z : PQ, (x == y)%PQ → (y == z)%PQ → (x == z)%PQ.
Proof.
progress unfold "==".
intros * Hxy Hyz.
progress unfold nd in *.
apply (Nat.mul_cancel_l _ _ (nn (PQnum1 y) + 1)); [ flia | ].
rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hyz.
rewrite Nat.mul_shuffle0, <- Nat.mul_assoc, Hxy.
rewrite Nat.mul_comm, Nat.mul_shuffle0.
symmetry; apply Nat.mul_assoc.
Qed.

Add Parametric Relation : _ PQeq
 reflexivity proved by PQeq_refl
 symmetry proved by PQeq_symm
 transitivity proved by PQeq_trans
 as PQeq_equiv_rel.

Theorem PQeq_if : ∀ A {P Q : A} x y,
  (if PQeq_dec x y then P else Q) = if_PQeq P Q x y.
Proof. easy. Qed.

(* allows to use rewrite inside a if_PQeq_dec ...
   through PQeq_if, e.g.
      H : (x = y)%PQ
      ====================
      ... if_PQeq_dec x z then P else Q ...
   > rewrite H.
      ====================
      ... if_PQeq_dec y z then P else Q ...
 *)
Global Instance PQif_PQeq_morph {P Q : Prop} :
  Proper (PQeq ==> PQeq ==> iff) (λ x y, if PQeq_dec x y then P else Q).
Proof.
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
destruct (PQeq_dec x1 y1) as [H1| H1]; rewrite Hx, Hy in H1. {
  now destruct (PQeq_dec x2 y2).
} {
  now destruct (PQeq_dec x2 y2).
}
Qed.

(* inequality *)

Definition PQcompare x y := Nat.compare (nd x y) (nd y x).

Theorem PQcompare_eq_iff : ∀ x y, PQcompare x y = Eq ↔ (x == y)%PQ.
Proof. intros; apply Nat.compare_eq_iff. Qed.

Theorem PQcompare_lt_iff : ∀ x y, PQcompare x y = Lt ↔ (x < y)%PQ.
Proof. intros; apply Nat.compare_lt_iff. Qed.

Theorem PQcompare_gt_iff : ∀ x y, PQcompare x y = Gt ↔ (x > y)%PQ.
Proof. intros; apply Nat.compare_gt_iff. Qed.

Theorem PQle_refl : ∀ x, (x ≤ x)%PQ.
Proof. now progress unfold "≤"%PQ. Qed.

Theorem PQnlt_ge : ∀ x y, ¬ (x < y)%PQ ↔ (y ≤ x)%PQ.
Proof.
intros.
split; intros H; [ now apply Nat.nlt_ge in H | ].
now apply Nat.nlt_ge.
Qed.

Theorem PQnle_gt : ∀ x y, ¬ (x ≤ y)%PQ ↔ (y < x)%PQ.
Proof.
intros.
split; intros H; [ now apply Nat.nle_gt in H | ].
now apply Nat.nle_gt.
Qed.

Theorem PQlt_le_dec : ∀ x y : PQ, {(x < y)%PQ} + {(y ≤ x)%PQ}.
Proof.
intros (xn, xd) (yn, yd).
progress unfold PQlt, PQle, nd; simpl.
destruct (lt_dec ((nn xn + 1) * (nn yd + 1)) ((nn yn + 1) * (nn xd + 1)))
  as [H1| H1]. {
  now left.
} {
  now right; apply Nat.nlt_ge.
}
Qed.

Theorem PQle_lt_dec : ∀ x y : PQ, {(x ≤ y)%PQ} + {(y < x)%PQ}.
Proof.
intros (xn, xd) (yn, yd).
progress unfold PQlt, PQle, nd; simpl.
destruct (le_dec ((nn xn + 1) * (nn yd + 1)) ((nn yn + 1) * (nn xd + 1)))
  as [H1| H1]. {
  now left.
} {
  now right; apply Nat.nle_gt.
}
Qed.

Theorem PQle_dec : ∀ x y : PQ, {(x ≤ y)%PQ} + {¬ (x ≤ y)%PQ}.
Proof.
intros (xn, xd) (yn, yd).
progress unfold PQlt, PQle, nd; simpl.
destruct (le_dec ((nn xn + 1) * (nn yd + 1)) ((nn yn + 1) * (nn xd + 1)))
  as [H1| H1]. {
  now left.
} {
  now right.
}
Qed.

Ltac split_var x :=
  let xn := fresh x in
  let xd := fresh x in
  let Hpn := fresh x in
  let Hpd := fresh x in
  remember (nn (PQnum1 x) + 1) as xn eqn:Hxn;
  remember (nn (PQden1 x) + 1) as xd eqn:Hxd;
  assert (Hpn : 0 < xn) by flia Hxn;
  assert (Hpd : 0 < xd) by flia Hxd;
  clear Hxn Hxd.

(* allows to use rewrite inside a less than
   e.g.
      H : x = y
      ====================
      (x < z)%PQ
   rewrite H.
 *)
Global Instance PQlt_morph : Proper (PQeq ==> PQeq ==> iff) PQlt.
Proof.
assert (H : ∀ x1 x2 y1 y2,
  (x1 == x2)%PQ → (y1 == y2)%PQ → (x1 < y1)%PQ → (x2 < y2)%PQ). {
  intros x1q x2q y1q y2q Hx Hy Hxy.
  progress unfold "<"%PQ, nd in Hxy |-*.
  progress unfold "=="%PQ, nd in Hx, Hy.
  split_var x1q; split_var x2q; split_var y1q; split_var y2q.
  move Hx before Hy.
  apply (Nat.mul_lt_mono_pos_l y1q0); [ easy | ].
  rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hy; clear Hy.
  remember (y2q0 * y1q1 * x2q0) as u; rewrite Nat.mul_comm; subst u.
  do 2 rewrite <- Nat.mul_assoc.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply (Nat.mul_lt_mono_pos_r x1q1); [ easy | ].
  rewrite <- Nat.mul_assoc, <- Hx; clear Hx.
  rewrite Nat.mul_assoc, Nat.mul_comm.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  now rewrite Nat.mul_comm.
}
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
split; intros Hxy.
-now apply (H x1 x2 y1 y2).
-symmetry in Hx, Hy.
 now apply (H x2 x1 y2 y1).
Qed.

Global Instance PQgt_morph : Proper (PQeq ==> PQeq ==> iff) PQgt.
Proof.
intros x1 x2 Hx y1 y2 Hy.
now apply PQlt_morph.
Qed.

(* allows to use rewrite inside a less equal
   e.g.
      H : x = y
      ====================
      (x ≤ z)%PQ
   rewrite H.
 *)
Global Instance PQle_morph : Proper (PQeq ==> PQeq ==> iff) PQle.
Proof.
assert (H : ∀ x1 x2 y1 y2,
  (x1 == x2)%PQ → (y1 == y2)%PQ → (x1 ≤ y1)%PQ → (x2 ≤ y2)%PQ). {
  intros x1q x2q y1q y2q Hx Hy Hxy.
  progress unfold "≤"%PQ, nd in Hxy |-*.
  progress unfold "=="%PQ, nd in Hx, Hy.
  split_var x1q; split_var x2q; split_var y1q; split_var y2q.
  move Hx before Hy.
  apply (Nat.mul_le_mono_pos_l _ _ y1q0); [ easy | ].
  rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hy; clear Hy.
  remember (y2q0 * y1q1 * x2q0) as u; rewrite Nat.mul_comm; subst u.
  do 2 rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_pos_l; [ easy | ].
  apply (Nat.mul_le_mono_pos_r _ _ x1q1); [ easy | ].
  rewrite <- Nat.mul_assoc, <- Hx; clear Hx.
  rewrite Nat.mul_assoc, Nat.mul_comm.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_pos_l; [ easy | ].
  now rewrite Nat.mul_comm.
}
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
split; intros Hxy. {
  now apply (H x1 x2 y1 y2).
} {
  symmetry in Hx, Hy.
  now apply (H x2 x1 y2 y1).
}
Qed.

Global Instance PQge_morph : Proper (PQeq ==> PQeq ==> iff) PQge.
Proof.
intros x1 x2 Hx y1 y2 Hy.
now apply PQle_morph.
Qed.

(* allows to use rewrite inside an addition
   e.g.
      H : x = y
      ====================
      ..... (x + z)%PQ ....
   rewrite H.
 *)
Global Instance PQadd_morph : Proper (PQeq ==> PQeq ==> PQeq) PQadd.
Proof.
intros x1q x2q Hx y1q y2q Hy.
move Hx before Hy.
progress unfold "+"%PQ.
progress unfold "==", nd in Hx, Hy |-*.
progress unfold PQadd_num1, PQadd_den1, nd; simpl.
rewrite Nat.sub_add; [ | do 4 rewrite Nat.add_1_r; simpl; flia ].
rewrite Nat.sub_add; [ | do 2 rewrite Nat.add_1_r; simpl; flia ].
rewrite Nat.sub_add; [ | do 2 rewrite Nat.add_1_r; simpl; flia ].
rewrite Nat.sub_add; [ | do 2 rewrite Nat.add_1_r; simpl; flia ].
split_var x1q; split_var x2q; split_var y1q; split_var y2q.
move Hx before Hy.
ring_simplify.
rewrite Nat.add_comm; f_equal. {
  replace (y1q0 * x1q1 * x2q1 * y2q1) with
    (y1q0 * y2q1 * x1q1 * x2q1) by flia.
  rewrite Hy; flia.
} {
  replace (x1q0 * y1q1 * x2q1) with (x1q0 * x2q1 * y1q1) by flia.
  rewrite Hx; flia.
}
Qed.

Theorem PQsub_morph : ∀ x1 x2 y1 y2,
  (x1 < y1)%PQ
  → (x1 == x2)%PQ
  → (y1 == y2)%PQ
  → (y1 - x1 == y2 - x2)%PQ.
Proof.
intros * H1 Hx Hy.
generalize H1; intros H2; move H2 before H1.
rewrite Hx, Hy in H2.
progress unfold "-"%PQ.
progress unfold "==", nd in Hx, Hy |-*.
progress unfold "<"%PQ, nd in H1, H2.
progress unfold PQsub_num1, PQadd_den1, nd; simpl.
do 4 rewrite Nat.add_1_r in H1, H2, Hx, Hy.
do 12 rewrite Nat.add_1_r.
do 2 (rewrite <- Nat.sub_succ_l; [ | flia H1 ]).
rewrite Nat_sub_sub_swap, Nat_sub_succ_1.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite Nat_sub_succ_1.
do 2 (rewrite <- Nat.sub_succ_l; [ | flia H2 ]).
rewrite Nat_sub_sub_swap, Nat_sub_succ_1.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite Nat_sub_succ_1.
do 2 rewrite Nat.mul_sub_distr_r.
remember (S (nn (PQnum1 x1))) as x1n eqn:Hx1n.
remember (S (nn (PQden1 x1))) as x1d eqn:Hx1d.
remember (S (nn (PQnum1 x2))) as x2n eqn:Hx2n.
remember (S (nn (PQden1 x2))) as x2d eqn:Hx2d.
remember (S (nn (PQnum1 y1))) as y1n eqn:Hy1n.
remember (S (nn (PQden1 y1))) as y1d eqn:Hy1d.
remember (S (nn (PQnum1 y2))) as y2n eqn:Hy2n.
remember (S (nn (PQden1 y2))) as y2d eqn:Hy2d.
move H1 before H2.
f_equal.
-replace (y1n * x1d * (y2d * x2d)) with (y1n * y2d * x1d * x2d) by flia.
 rewrite Hy; flia.
-replace (x1n * y1d * (y2d * x2d)) with (x1n * x2d * y1d * y2d) by flia.
 rewrite Hx; flia.
Qed.

(* allows to use rewrite inside a multiplication
   e.g.
      H : x = y
      ====================
      ..... (x * z)%PQ ....
   rewrite H.
 *)
Global Instance PQmul_morph : Proper (PQeq ==> PQeq ==> PQeq) PQmul.
Proof.
progress unfold "*"%PQ.
progress unfold "==", nd; simpl.
progress unfold PQmul_num1, PQmul_den1; simpl.
intros x1 x2 Hx y1 y2 Hy; simpl.
move Hx before Hy.
do 4 rewrite Nat.add_1_r in Hx, Hy.
do 12 rewrite Nat.add_1_r.
do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 4 rewrite Nat_sub_succ_1.
setoid_rewrite Nat.mul_shuffle0.
do 2 rewrite Nat.mul_assoc; rewrite Hx.
setoid_rewrite <- Nat.mul_assoc; f_equal.
rewrite Nat.mul_comm, Hy.
apply Nat.mul_comm.
Qed.

Ltac split_var2 x xn xd Hpn Hpd :=
  remember (S (PQnum1 x)) as xn eqn:Heqxn;
  remember (S (PQden1 x)) as xd eqn:Heqxd;
  move xn at top; move xd at top;
  assert (Hpn : 0 < xn) by flia Heqxn;
  assert (Hpd : 0 < xd) by flia Heqxd;
  clear Heqxn Heqxd.

Ltac PQtac1 :=
  unfold "+"%PQ, "-"%PQ, "<"%PQ, "=="%PQ, "≤"%PQ;
  unfold PQadd_num1, PQsub_num1, PQadd_den1, nd; simpl;
  repeat rewrite Nat.add_1_r.

Ltac PQtac2 :=
  rewrite <- Nat.sub_succ_l;
  try (rewrite Nat_sub_succ_1);
  match goal with
  | [ |- 1 ≤ S _ * _ ] => try (simpl; flia)
  | [ |- 1 ≤ S _ * _ * _ ] => try (simpl; flia)
  | _ => idtac
  end.

Ltac PQtac3 :=
  repeat rewrite Nat.mul_sub_distr_l;
  repeat rewrite Nat.mul_add_distr_l;
  repeat rewrite Nat.mul_sub_distr_r;
  repeat rewrite Nat.mul_add_distr_r;
  repeat rewrite Nat.mul_assoc.

Theorem PQmul_one_r : ∀ x y, (x * PQone y == x)%PQ.
Proof.
intros.
progress unfold "*"%PQ, "==", PQone, nd; simpl.
progress unfold PQmul_num1, PQmul_den1; simpl.
PQtac1; repeat PQtac2; PQtac3.
apply Nat.mul_shuffle0.
Qed.

Theorem PQadd_comm : ∀ x y, (x + y)%PQ = (y + x)%PQ.
Proof.
intros.
progress unfold "+"%PQ; f_equal.
-now progress unfold PQadd_num1, nd; rewrite Nat.add_comm.
-now progress unfold PQadd_den1, nd; rewrite Nat.mul_comm.
Qed.

Theorem PQadd_add_swap : ∀ x y z, (x + y + z)%PQ = (x + z + y)%PQ.
Proof.
intros; PQtac1.
repeat PQtac2; [ | simpl; flia | simpl; flia ].
PQtac3; f_equal; f_equal; [ | f_equal; apply Nat.mul_shuffle0 ].
f_equal.
rewrite Nat.add_shuffle0.
f_equal; f_equal.
apply Nat.mul_shuffle0.
Qed.

Theorem PQadd_assoc : ∀ x y z, (x + (y + z))%PQ = ((x + y) + z)%PQ.
Proof.
intros.
rewrite PQadd_comm.
remember (x + y)%PQ as t eqn:Ht.
rewrite PQadd_comm in Ht; subst t.
apply PQadd_add_swap.
Qed.

(* *)

Theorem PQlt_irrefl : ∀ x, (¬ x < x)%PQ.
Proof. intros x; apply Nat.lt_irrefl. Qed.

Theorem PQlt_le_incl : ∀ x y, (x < y)%PQ → (x ≤ y)%PQ.
Proof. intros * Hxy; now apply Nat.lt_le_incl. Qed.

Theorem PQle_trans : ∀ x y z, (x ≤ y)%PQ → (y ≤ z)%PQ → (x ≤ z)%PQ.
Proof.
intros * Hxy Hyz.
progress unfold "≤"%PQ, nd in Hxy, Hyz |-*.
apply (Nat.mul_le_mono_pos_r _ _ (nn (PQden1 y) + 1)); [ flia | ].
rewrite Nat.mul_shuffle0.
apply
  (Nat.le_trans _
    ((nn (PQnum1 y) + 1) * (nn (PQden1 x) + 1) * (nn (PQden1 z) + 1))).
-apply Nat.mul_le_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_le_mono_pos_r; [ flia | easy ].
Qed.

Theorem PQlt_trans : ∀ x y z, (x < y)%PQ → (y < z)%PQ → (x < z)%PQ.
Proof.
intros * Hxy Hyz.
progress unfold "<"%PQ, nd in Hxy, Hyz |-*.
apply (Nat.mul_lt_mono_pos_r (nn (PQden1 y) + 1)); [ flia | ].
rewrite Nat.mul_shuffle0.
apply
  (Nat.lt_trans _
     ((nn (PQnum1 y) + 1) * (nn (PQden1 x) + 1) * (nn (PQden1 z) + 1))).
-apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
Qed.

Theorem PQle_lt_trans : ∀ x y z, (x ≤ y)%PQ → (y < z)%PQ → (x < z)%PQ.
Proof.
intros * Hxy Hyz.
progress unfold "<"%PQ, nd in Hyz |-*.
progress unfold "≤"%PQ, nd in Hxy.
apply (Nat.mul_lt_mono_pos_r (nn (PQden1 y) + 1)); [ flia | ].
rewrite Nat.mul_shuffle0.
apply
  (Nat.le_lt_trans _
     ((nn (PQnum1 y) + 1) * (nn (PQden1 x) + 1) * (nn (PQden1 z) + 1))).
-apply Nat.mul_le_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
Qed.

Theorem PQlt_le_trans : ∀ x y z, (x < y)%PQ → (y ≤ z)%PQ → (x < z)%PQ.
Proof.
intros * Hxy Hyz.
progress unfold "<"%PQ, nd in Hxy |-*.
progress unfold "≤"%PQ, nd in Hyz.
apply (Nat.mul_lt_mono_pos_r (nn (PQden1 y) + 1)); [ flia | ].
rewrite Nat.mul_shuffle0.
apply
  (Nat.lt_le_trans _
     ((nn (PQnum1 y) + 1) * (nn (PQden1 x) + 1) * (nn (PQden1 z) + 1))).
-apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_le_mono_pos_r; [ flia | easy ].
Qed.

Global Instance PQcompare_morph : Proper (PQeq ==> PQeq ==> eq) PQcompare.
Proof.
intros x1 x2 Hx y1 y2 Hy.
move Hx before Hy.
remember (PQcompare x1 y1) as c1 eqn:Hc1; symmetry in Hc1.
remember (PQcompare x2 y2) as c2 eqn:Hc2; symmetry in Hc2.
move c2 before c1.
destruct c1.
-apply PQcompare_eq_iff in Hc1.
 destruct c2; [ easy | | ].
 +apply PQcompare_lt_iff in Hc2.
  rewrite <- Hy, <- Hc1, Hx in Hc2.
  now apply PQlt_irrefl in Hc2.
 +apply PQcompare_gt_iff in Hc2.
  rewrite <- Hy, <- Hc1, Hx in Hc2.
  now apply PQlt_irrefl in Hc2.
-apply PQcompare_lt_iff in Hc1.
 destruct c2; [ | easy | ].
 +apply PQcompare_eq_iff in Hc2.
  rewrite Hx, Hc2, Hy in Hc1.
  now apply PQlt_irrefl in Hc1.
 +apply PQcompare_gt_iff in Hc2.
  rewrite Hx, Hy in Hc1.
  apply PQnle_gt in Hc2.
  now exfalso; apply Hc2, PQlt_le_incl.
-apply PQcompare_gt_iff in Hc1.
 destruct c2; [ | | easy ].
 +apply PQcompare_eq_iff in Hc2.
  rewrite Hx, Hc2, <- Hy in Hc1.
  now apply PQlt_irrefl in Hc1.
 +apply PQcompare_lt_iff in Hc2.
  rewrite Hx, Hy in Hc1.
  apply PQnle_gt in Hc2.
  now exfalso; apply Hc2, PQlt_le_incl.
Qed.

Theorem PQadd_lt_mono_r : ∀ x y z, (x < y)%PQ ↔ (x + z < y + z)%PQ.
Proof.
progress unfold "<"%PQ, "+"%PQ, PQadd_num1, PQadd_den1, nd; simpl.
intros *.
do 10 rewrite Nat.add_1_r.
do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 4 rewrite Nat_sub_succ_1.
do 2 rewrite Nat.mul_add_distr_r.
remember (S (nn (PQnum1 x))) as xn eqn:Hxn.
remember (S (nn (PQden1 x))) as xd eqn:Hxd.
remember (S (nn (PQnum1 y))) as yn eqn:Hyn.
remember (S (nn (PQden1 y))) as yd eqn:Hyd.
remember (S (nn (PQnum1 z))) as zn eqn:Hzn.
remember (S (nn (PQden1 z))) as zd eqn:Hzd.
replace (zn * yd * (xd * zd)) with (zn * xd * (yd * zd)) by flia.
replace (xn * zd * (yd * zd)) with (xn * yd * (zd * zd)) by flia.
replace (yn * zd * (xd * zd)) with (yn * xd * (zd * zd)) by flia.
split; intros H.
-apply Nat.add_lt_mono_r.
 apply Nat.mul_lt_mono_pos_r; [ | easy ].
 subst zd; simpl; flia.
-apply Nat.add_lt_mono_r in H.
 apply Nat.mul_lt_mono_pos_r in H; [ easy | ].
 subst zd; simpl; flia.
Qed.

Theorem PQadd_lt_mono_l : ∀ x y z, (y < z)%PQ ↔ (x + y < x + z)%PQ.
Proof.
intros.
setoid_rewrite PQadd_comm.
apply PQadd_lt_mono_r.
Qed.

Theorem PQadd_le_mono_r : ∀ x y z, (x ≤ y ↔ x + z ≤ y + z)%PQ.
Proof.
progress unfold "≤"%PQ, "+"%PQ, PQadd_num1, PQadd_den1, nd; simpl.
intros *.
do 10 rewrite Nat.add_1_r.
do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 4 rewrite Nat_sub_succ_1.
do 2 rewrite Nat.mul_add_distr_r.
remember (S (nn (PQnum1 x))) as xn eqn:Hxn.
remember (S (nn (PQden1 x))) as xd eqn:Hxd.
remember (S (nn (PQnum1 y))) as yn eqn:Hyn.
remember (S (nn (PQden1 y))) as yd eqn:Hyd.
remember (S (nn (PQnum1 z))) as zn eqn:Hzn.
remember (S (nn (PQden1 z))) as zd eqn:Hzd.
replace (zn * yd * (xd * zd)) with (zn * xd * (yd * zd)) by flia.
replace (xn * zd * (yd * zd)) with (xn * yd * (zd * zd)) by flia.
replace (yn * zd * (xd * zd)) with (yn * xd * (zd * zd)) by flia.
split; intros H.
-apply Nat.add_le_mono_r.
 now apply Nat.mul_le_mono_r.
-apply Nat.add_le_mono_r in H.
 apply Nat.mul_le_mono_pos_r in H; [ easy | ].
 subst zd; simpl; flia.
Qed.

Theorem PQadd_le_mono_l : ∀ x y z, (x ≤ y ↔ z + x ≤ z + y)%PQ.
Proof.
setoid_rewrite PQadd_comm.
apply PQadd_le_mono_r.
Qed.

Theorem PQsub_add_eq : ∀ x y,
  (y < x)%PQ → (x - y + y = x * PQone y * PQone y)%PQ.
Proof.
intros x y Hxy.
progress unfold "<"%PQ, nd in Hxy.
progress unfold "+"%PQ, "-"%PQ, "==", nd; simpl.
progress unfold PQsub_num1, PQadd_num1, PQadd_den1, nd; simpl.
progress unfold "*"%PQ, PQone, PQmul_num1, PQmul_den1; simpl.
do 4 rewrite Nat.add_1_r in Hxy.
f_equal.
PQtac1; repeat PQtac2; [ | flia Hxy ].
PQtac3; rewrite Nat.sub_add; [ easy | ].
setoid_rewrite Nat.mul_shuffle0.
rewrite Nat.mul_shuffle0.
now apply Nat.mul_le_mono_r, Nat.lt_le_incl.
Qed.

Theorem PQsub_add : ∀ x y, (y < x)%PQ → (x - y + y == x)%PQ.
Proof.
intros x y Hxy.
rewrite PQsub_add_eq; [ | easy ].
now do 2 rewrite PQmul_one_r.
Qed.

Theorem PQsub_le_mono_l : ∀ x y z,
  (x < z)%PQ → (y < z)%PQ → (y ≤ x)%PQ ↔ (z - x ≤ z - y)%PQ.
Proof.
intros * Hzx Hzy.
split.
-intros Hxy.
 revert Hzx Hxy Hzy.
 progress unfold "≤"%PQ, "<"%PQ, "-"%PQ, PQsub_num1, PQadd_den1, nd; simpl.
 do 10 rewrite Nat.add_1_r.
 intros.
 rewrite <- Nat.sub_succ_l; [ | flia Hzx ].
 rewrite Nat_sub_succ_1.
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 rewrite Nat_sub_succ_1.
 rewrite <- Nat.sub_succ_l; [ | flia Hzy ].
 rewrite Nat_sub_succ_1.
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 rewrite Nat_sub_succ_1.
 remember (S (nn (PQnum1 x))) as xn eqn:Hxn.
 remember (S (nn (PQden1 x))) as xd eqn:Hxd.
 remember (S (nn (PQnum1 y))) as yn eqn:Hyn.
 remember (S (nn (PQden1 y))) as yd eqn:Hyd.
 remember (S (nn (PQnum1 z))) as zn eqn:Hzn.
 remember (S (nn (PQden1 z))) as zd eqn:Hzd.
 do 2 rewrite Nat.mul_sub_distr_r.
 replace (zn * yd * (zd * xd)) with (zn * xd * (zd * yd)) by flia.
 replace (xn * zd * (zd * yd)) with (xn * yd * (zd * zd)) by flia.
 replace (yn * zd * (zd * xd)) with (yn * xd * (zd * zd)) by flia.
 apply Nat.sub_le_mono_l.
 now apply Nat.mul_le_mono_r.
-intros Hxyz.
 apply (PQadd_le_mono_r _ _ (x + y)%PQ) in Hxyz.
 do 2 rewrite PQadd_assoc in Hxyz.
 rewrite PQsub_add in Hxyz; [ | easy ].
 rewrite PQadd_add_swap in Hxyz.
 rewrite PQsub_add in Hxyz; [ | easy ].
 now apply PQadd_le_mono_l in Hxyz.
Qed.

Theorem PQadd_no_neutral : ∀ x y, (y + x ≠≠ x)%PQ.
Proof.
intros x y Hxy.
progress unfold "+"%PQ, "=="%PQ, nd in Hxy; simpl in Hxy.
progress unfold PQadd_num1, PQadd_den1, nd in Hxy.
do 6 rewrite Nat.add_1_r in Hxy.
do 2 (rewrite <- Nat.sub_succ_l in Hxy; [ | simpl; flia ]).
do 2 rewrite Nat_sub_succ_1 in Hxy.
rewrite Nat.mul_add_distr_r in Hxy.
rewrite Nat.mul_assoc in Hxy.
apply Nat.add_sub_eq_r in Hxy.
now rewrite Nat.sub_diag in Hxy.
Qed.

Theorem PQsub_no_neutral : ∀ x y, (y < x)%PQ → (x - y ≠≠ x)%PQ.
Proof.
intros *; PQtac1; intros Hyz.
PQtac2; [ | flia Hyz ].
PQtac3.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite Nat_sub_succ_1, Nat.mul_assoc.
intros H.
apply Nat.add_sub_eq_nz in H; [ | simpl; flia ].
rewrite Nat.add_comm, Nat.mul_shuffle0 in H.
rewrite <- Nat.add_0_r in H.
now apply Nat.add_cancel_l in H.
Qed.

Theorem PQadd_sub_same_eq : ∀ px py pz,
  (py == pz)%PQ
  → (px + py - pz = px * PQone py * PQone pz)%PQ.
Proof.
intros * Hyz.
progress unfold "*"%PQ, PQmul_num1, PQmul_den1.
revert Hyz.
PQtac1; intros; PQtac2; [ | simpl; flia ].
PQtac3; do 2 PQtac2; PQtac3; f_equal.
remember (S (nn (PQnum1 px)) * S (nn (PQden1 py))) as t.
now rewrite Nat.mul_shuffle0, Hyz, Nat.mul_shuffle0, Nat.add_sub.
Qed.

Theorem PQadd_sub_eq : ∀ x y, (x + y - y = x * PQone y * PQone y)%PQ.
Proof. now intros; rewrite PQadd_sub_same_eq. Qed.

Theorem PQadd_sub : ∀ x y, (x + y - y == x)%PQ.
Proof.
intros x y.
rewrite PQadd_sub_eq.
now do 2 rewrite PQmul_one_r.
Qed.

Theorem PQlt_add_r : ∀ x y, (x < x + y)%PQ.
Proof.
intros.
progress unfold "<"%PQ, "+"%PQ; simpl.
progress unfold PQadd_num1, PQadd_den1, nd; simpl.
do 6 rewrite Nat.add_1_r.
do 2 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 2 (rewrite Nat_sub_succ_1).
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_assoc, Nat.mul_shuffle0.
rewrite <- Nat.add_0_r at 1.
apply Nat.add_le_lt_mono; [ easy | simpl; flia ].
Qed.

Theorem PQlt_add_l : ∀ x y, (x < y + x)%PQ.
Proof.
intros.
rewrite PQadd_comm.
apply PQlt_add_r.
Qed.

Theorem PQle_add_r : ∀ x y, (x ≤ x + y)%PQ.
Proof.
intros.
progress unfold "≤"%PQ, "+"%PQ; simpl.
progress unfold PQadd_num1, PQadd_den1, nd; simpl.
do 6 rewrite Nat.add_1_r.
do 2 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 2 (rewrite Nat_sub_succ_1).
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_assoc, Nat.mul_shuffle0.
rewrite <- Nat.add_0_r at 1.
apply Nat.add_le_mono; [ easy | simpl; flia ].
Qed.

Theorem PQle_add_l : ∀ x y, (x ≤ y + x)%PQ.
Proof.
intros.
rewrite PQadd_comm.
apply PQle_add_r.
Qed.

Theorem PQsub_lt : ∀ x y, (y < x)%PQ → (x - y < x)%PQ.
Proof.
intros * Hyx.
revert Hyx; PQtac1; intros.
repeat PQtac2.
-rewrite Nat.mul_assoc, Nat.mul_shuffle0.
 apply Nat.mul_lt_mono_pos_r; [ apply Nat.lt_0_succ | ].
 apply Nat.sub_lt; [ | simpl; apply Nat.lt_0_succ ].
 now apply Nat.lt_le_incl.
-flia Hyx.
Qed.

Theorem PQsub_add_distr : ∀ x y z,
  (y < x)%PQ → (x - (y + z))%PQ = (x - y - z)%PQ.
Proof.
intros * Hyx.
revert Hyx; PQtac1; intros.
repeat PQtac2; PQtac3; [ f_equal; f_equal; flia | flia Hyx | simpl; flia ].
Qed.

Theorem PQsub_sub_distr : ∀ x y z,
  (z < y)%PQ → (y - z < x)%PQ → (x - (y - z))%PQ = (x + z - y)%PQ.
Proof.
intros * Hzy Hyzx.
revert Hzy Hyzx; PQtac1; intros.
rewrite Nat_sub_sub_swap in Hyzx.
do 2 (rewrite <- Nat.sub_succ_l in Hyzx; [ | flia Hzy ]).
rewrite <- Nat.sub_succ_l in Hyzx; [ | simpl; flia ].
do 2 rewrite Nat_sub_succ_1 in Hyzx.
rewrite Nat.mul_sub_distr_r, Nat.mul_assoc in Hyzx.
repeat PQtac2; PQtac3; [ | simpl; flia | ].
-f_equal; [ f_equal | now rewrite Nat.mul_shuffle0 ].
 rewrite Nat_sub_sub_assoc.
 +f_equal; f_equal; [ | now rewrite Nat.mul_shuffle0 ].
  now f_equal; rewrite Nat.mul_shuffle0.
 +split; [ | flia Hyzx ].
  now apply Nat.mul_le_mono_r, Nat.lt_le_incl.
-flia Hzy.
Qed.

Theorem PQadd_sub_assoc : ∀ x y z,
  (z < y)%PQ → (x + (y - z))%PQ = (x + y - z)%PQ.
Proof.
intros * Hzy.
revert Hzy; PQtac1; intros.
repeat PQtac2; [ | simpl; flia | flia Hzy ].
PQtac3.
f_equal; f_equal.
rewrite Nat.add_sub_assoc.
-f_equal; f_equal; [ f_equal; apply Nat.mul_shuffle0 | ].
 apply Nat.mul_shuffle0.
-now apply Nat.mul_le_mono_r, Nat.lt_le_incl.
Qed.

Theorem PQadd_cancel_l_eq : ∀ x y z,
  (z + x == z + y)%PQ → (x * PQone y = y * PQone x)%PQ.
Proof.
intros * H.
revert H; PQtac1; intros.
do 4 (rewrite <- Nat.sub_succ_l in H; [ | simpl; flia ]).
do 4 rewrite Nat_sub_succ_1 in H.
setoid_rewrite Nat.mul_comm in H.
do 2 rewrite <- Nat.mul_assoc in H.
apply Nat.mul_cancel_l in H; [ | easy ].
setoid_rewrite Nat.mul_comm in H.
do 2 rewrite Nat.mul_add_distr_r in H.
rewrite Nat.mul_shuffle0 in H.
apply Nat.add_cancel_l in H.
setoid_rewrite Nat.mul_shuffle0 in H.
apply Nat.mul_cancel_r in H; [ | easy ].
progress unfold "*"%PQ, PQone, PQmul_num1, PQmul_den1; simpl.
PQtac1; rewrite H; f_equal.
now rewrite Nat.mul_comm.
Qed.

Theorem PQadd_cancel_l : ∀ x y z, (z + x == z + y)%PQ ↔ (x == y)%PQ.
Proof.
intros.
split; intros H; [ | now rewrite H ].
specialize (PQadd_cancel_l_eq _ _ _ H) as H1.
progress unfold "*"%PQ, PQone, PQmul_num1, PQmul_den1 in H1; simpl in H1.
injection H1; clear H1; intros H1 H2.
revert H2; PQtac1; intros.
simpl in H2; simpl; do 2 rewrite Nat.sub_0_r in H2.
now rewrite H2.
Qed.

Theorem PQmul_comm : ∀ x y, (x * y = y * x)%PQ.
Proof.
intros.
progress unfold "*"%PQ; f_equal.
-now progress unfold PQmul_num1; simpl; rewrite Nat.mul_comm.
-now progress unfold PQmul_den1; simpl; rewrite Nat.mul_comm.
Qed.

Theorem PQmul_1_l : ∀ a, (1 * a)%PQ = a.
Proof.
intros.
progress unfold "*"%PQ.
progress unfold PQmul_num1, PQmul_den1; simpl.
do 2 rewrite Nat.add_0_r, Nat.add_sub.
now destruct a, PQnum2, PQden2.
Qed.

Theorem PQmul_mul_swap : ∀ x y z, (x * y * z = x * z * y)%PQ.
intros.
progress unfold "*"%PQ; simpl.
progress unfold PQmul_num1, PQmul_den1; simpl; PQtac1; repeat PQtac2; f_equal.
-now rewrite Nat.mul_shuffle0.
-now rewrite Nat.mul_shuffle0.
Qed.

Theorem PQmul_le_mono : ∀ x y z t,
  (x ≤ y)%PQ → (z ≤ t)%PQ → (x * z ≤ y * t)%PQ.
Proof.
intros *.
progress unfold "≤"%PQ, nd; cbn.
progress unfold PQmul_num1, PQmul_den1.
do 12 rewrite Nat.add_1_r.
do 4 (rewrite <- Nat.sub_succ_l; [ | cbn; flia ]).
do 4 rewrite Nat_sub_succ_1.
intros Hxy Hzt.
setoid_rewrite Nat.mul_shuffle0.
do 2 rewrite Nat.mul_assoc.
setoid_rewrite <- Nat.mul_assoc.
apply Nat.mul_le_mono; [ easy | ].
now setoid_rewrite Nat.mul_comm.
Qed.

Theorem PQmul_le_mono_l : ∀ x y z, (x ≤ y ↔ z * x ≤ z * y)%PQ.
Proof.
intros *.
progress unfold "≤"%PQ, nd; simpl.
progress unfold PQmul_num1, PQmul_den1.
do 10 rewrite Nat.add_1_r.
do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 4 rewrite Nat_sub_succ_1.
do 2 rewrite Nat.mul_assoc.
setoid_rewrite Nat.mul_shuffle0.
split; intros Hxy.
-apply Nat.mul_le_mono_r.
 do 2 rewrite <- Nat.mul_assoc.
 now apply Nat.mul_le_mono_l.
-apply Nat.mul_le_mono_pos_r in Hxy; [ | flia ].
 do 2 rewrite <- Nat.mul_assoc in Hxy.
 apply Nat.mul_le_mono_pos_l in Hxy; [ | flia ].
 easy.
Qed.

Theorem PQmul_add_distr_l_eq : ∀ x y z,
  (x * (y + z) * PQone x = x * y + x * z)%PQ.
Proof.
intros.
progress unfold "==", "*"%PQ, "+"%PQ, nd; simpl.
progress unfold PQmul_num1, PQadd_den1, PQadd_num1, PQmul_den1, nd; simpl.
PQtac1; do 2 PQtac2; [ | simpl; flia ].
PQtac3; do 6 PQtac2.
PQtac3; f_equal; [ | now rewrite Nat.mul_shuffle0 ].
now f_equal; f_equal; f_equal; rewrite Nat.mul_shuffle0.
Qed.

Theorem PQmul_add_distr_l : ∀ x y z, (x * (y + z) == x * y + x * z)%PQ.
Proof. now intros; rewrite <- PQmul_add_distr_l_eq, PQmul_one_r. Qed.

Theorem PQmul_sub_distr_l_eq : ∀ x y z,
  (z < y → x * (y - z) * PQone x = x * y - x * z)%PQ.
Proof.
intros *.
progress unfold "==", "*"%PQ, "+"%PQ, "<"%PQ, nd; simpl.
progress unfold PQmul_num1, PQadd_den1, PQadd_num1, PQmul_den1, nd; simpl.
PQtac1; intros Hzy.
repeat PQtac2.
-repeat rewrite Nat.mul_assoc; f_equal.
 +f_equal; PQtac3; f_equal; f_equal; apply Nat.mul_shuffle0.
 +f_equal; f_equal; apply Nat.mul_shuffle0.
-flia Hzy.
-cbn.
 rewrite Nat.mul_sub_distr_l.
 rewrite Nat.mul_add_distr_l.
 rewrite Nat.mul_add_distr_l.
 flia Hzy.
-flia Hzy.
Qed.

Theorem PQmul_sub_distr_l : ∀ x y z,
  (z < y → x * (y - z) == x * y - x * z)%PQ.
Proof.
intros * Hzy.
rewrite <- PQmul_sub_distr_l_eq; [ | easy ].
now rewrite PQmul_one_r.
Qed.

Theorem PQmul_cancel_l_eq : ∀ x y z,
  (z * x == z * y)%PQ → (x * PQone y = y * PQone x)%PQ.
Proof.
intros * H.
revert H; progress unfold "*"%PQ, PQmul_num1, PQmul_den1.
destruct x as (xn, xd).
destruct y as (yn, yd).
destruct z as (zn, zd); simpl.
PQtac1; do 4 PQtac2.
intros.
do 2 rewrite <- Nat.mul_assoc in H.
apply Nat.mul_cancel_l in H; [ | easy ].
setoid_rewrite Nat.mul_comm in H.
do 2 rewrite <- Nat.mul_assoc in H.
apply Nat.mul_cancel_l in H; [ | easy ].
f_equal; rewrite Nat.mul_comm; [ now rewrite H, Nat.mul_comm | easy ].
Qed.

Theorem PQmul_cancel_l : ∀ x y z, (z * x == z * y ↔ x == y)%PQ.
Proof.
Proof.
intros.
split; intros H; [ | now rewrite H ].
specialize (PQmul_cancel_l_eq _ _ _ H) as H1.
progress unfold "*"%PQ, PQone, PQmul_num1, PQmul_den1 in H1; simpl in H1.
injection H1; clear H1; intros H1 H2.
revert H2; PQtac1; intros.
simpl in H2; simpl; do 2 rewrite Nat.sub_0_r in H2.
now rewrite H2.
Qed.

(* *)

Ltac PQcompare_iff :=
  match goal with
  | [ H : PQcompare _ _ = Eq |- _ ] => apply PQcompare_eq_iff in H
  | [ H : PQcompare _ _ = Lt |- _ ] => apply PQcompare_lt_iff in H
  | [ H : PQcompare _ _ = Gt |- _ ] => apply PQcompare_gt_iff in H
  end.

Theorem PQmul_lt_cancel_l : ∀ x y z, (x * y < x * z)%PQ ↔ (y < z)%PQ.
Proof.
intros.
progress unfold "<"%PQ, nd.
progress unfold "*"%PQ; simpl.
progress unfold PQmul_num1, PQmul_den1.
rewrite Nat.sub_add; [ | destruct (PQnum1 x); simpl; flia ].
rewrite Nat.sub_add; [ | destruct (PQden1 x); simpl; flia ].
rewrite Nat.sub_add; [ | destruct (PQnum1 x); simpl; flia ].
rewrite Nat.sub_add; [ | destruct (PQden1 x); simpl; flia ].
setoid_rewrite Nat.mul_shuffle1.
split; intros H.
-apply Nat.mul_lt_mono_pos_l in H; [ easy | ].
 do 2 rewrite Nat.add_1_r; simpl; apply Nat.lt_0_succ.
-apply Nat.mul_lt_mono_pos_l; [ | easy ].
 do 2 rewrite Nat.add_1_r; simpl; apply Nat.lt_0_succ.
Qed.

Theorem PQcompare_mul_cancel_l : ∀ x y z,
  PQcompare (x * y) (x * z) = PQcompare y z.
Proof.
intros.
remember (PQcompare (x * y) (x * z)) as b1 eqn:Hb1.
symmetry in Hb1; symmetry.
destruct b1; PQcompare_iff.
-apply PQcompare_eq_iff.
 now apply PQmul_cancel_l in Hb1.
-apply PQcompare_lt_iff.
 now apply PQmul_lt_cancel_l in Hb1.
-apply PQcompare_gt_iff.
 now apply PQmul_lt_cancel_l in Hb1.
Qed.

Require Import Nat_ggcd.

Definition PQred x :=
  let '(_, (aa, bb)) := ggcd (nn (PQnum1 x) + 1) (nn (PQden1 x) + 1) in
  PQmake (mknn (aa - 1)) (mknn (bb - 1)).

Global Instance PQred_morph : Proper (PQeq ==> PQeq) PQred.
Proof.
intros (xn, xd) (yn, yd) Hxy.
progress unfold "=="%PQ, nd in Hxy |-*; simpl in *.
progress unfold PQred; simpl.
remember (ggcd (nn xn + 1) (nn xd + 1)) as g1 eqn:Hg1; symmetry in Hg1.
remember (ggcd (nn yn + 1) (nn yd + 1)) as g2 eqn:Hg2; symmetry in Hg2.
move g2 before g1.
destruct g1 as (g1 & aa1 & bb1).
destruct g2 as (g2 & aa2 & bb2); simpl.
specialize (ggcd_correct_divisors (nn xn + 1) (nn xd + 1)) as H1.
rewrite Hg1 in H1; destruct H1 as (Hxn, Hxd).
specialize (ggcd_correct_divisors (nn yn + 1) (nn yd + 1)) as H1.
rewrite Hg2 in H1; destruct H1 as (Hyn, Hyd).
rewrite Nat.mul_comm, Nat.add_1_r in Hxn, Hxd, Hyn, Hyd.
rewrite Nat.sub_add; [ | destruct aa1; flia Hxn ].
rewrite Nat.sub_add; [ | destruct bb2; flia Hyd ].
rewrite Nat.sub_add; [ | destruct aa2; flia Hyn ].
rewrite Nat.sub_add; [ | destruct bb1; flia Hxd ].
rewrite Nat.mul_comm in Hxn, Hxd, Hyn, Hyd.
do 4 rewrite Nat.add_1_r in Hxy.
apply (Nat.mul_cancel_l _ _ g1); [ now destruct g1 | ].
rewrite Nat.mul_assoc, <- Hxn, Nat.mul_comm.
apply (Nat.mul_cancel_l _ _ g2); [ now destruct g2 | ].
rewrite Nat.mul_assoc, <- Hyd, Nat.mul_comm.
rewrite Hxy, Hyn, Hxd.
flia.
Qed.

Theorem PQred_add_mul_one_l :
  ∀ x y a, PQred (x + y) = PQred (PQmake a a * x + y).
Proof.
intros (xn, xd) (yn, yd) a.
progress unfold PQred; simpl.
progress unfold "*"%PQ, PQ_of_nat.
progress unfold PQmul_num1, PQmul_den1; simpl.
progress unfold PQadd_num1, PQadd_den1, nd; simpl.
PQtac1.
PQtac2; [ PQtac2 | simpl; flia ].
PQtac2; [ | simpl; flia ].
do 3 PQtac2.
replace (S (nn yn) * (S (nn a) * S (nn xd))) with
  (S (nn a) * (S (nn yn) * S (nn xd))) by flia.
rewrite <- Nat.mul_assoc, <- Nat.mul_add_distr_l.
rewrite <- Nat.mul_assoc.
rewrite ggcd_mul_mono_l; [ | easy ].
now destruct
  (ggcd (S (nn xn) * S (nn yd) + S (nn yn) * S (nn xd))
     (S (nn xd) * S (nn yd))).
Qed.

Theorem PQred_sub_mul_one_l : ∀ x y a,
  (y < x)%PQ -> PQred (x - y) = PQred (PQmake a a * x - y).
Proof.
intros (xn, xd) (yn, yd) a Hyx.
progress unfold PQred; simpl.
progress unfold "*"%PQ, PQ_of_nat.
progress unfold PQmul_num1, PQmul_den1; simpl.
progress unfold PQsub_num1, PQadd_den1, nd; simpl.
revert Hyx; PQtac1; intros.
PQtac2; [ PQtac2 | flia Hyx ].
PQtac2.
-do 3 PQtac2.
 replace (S (nn yn) * (S (nn a) * S (nn xd))) with
   (S (nn a) * (S (nn yn) * S (nn xd))) by flia.
 rewrite <- Nat.mul_assoc, <- Nat.mul_sub_distr_l.
 rewrite <- Nat.mul_assoc.
 rewrite ggcd_mul_mono_l; [ | easy ].
 now destruct
   (ggcd (S (nn xn) * S (nn yd) - S (nn yn) * S (nn xd))
      (S (nn xd) * S (nn yd))).
-do 2 PQtac2.
 replace (S (nn yn) * (S (nn a) * S (nn xd))) with
   (S (nn a) * (S (nn yn) * S (nn xd))) by flia.
 rewrite <- Nat.mul_assoc, <- Nat.mul_sub_distr_l.
 apply Nat.sub_gt in Hyx.
 remember (_ - _) as u.
 destruct u; [ easy | cbn; flia ].
Qed.

Theorem PQred_sub_mul_one_r : ∀ x y a,
  (y < x)%PQ -> PQred (x - y) = PQred (x - PQmake a a * y).
Proof.
intros (xn, xd) (yn, yd) a Hyx.
progress unfold PQred; simpl.
progress unfold "*"%PQ, PQ_of_nat.
progress unfold PQmul_num1, PQmul_den1; simpl.
progress unfold PQsub_num1, PQadd_den1, nd; simpl.
revert Hyx; PQtac1; intros.
PQtac2; [ PQtac2 | flia Hyx ].
destruct a as (a).
destruct xn as (xn).
destruct xd as (xd).
destruct yn as (yn).
destruct yd as (yd).
cbn - [ ggcd Nat.mul ].
PQtac2.
-do 3 PQtac2.
 replace (S xn * (S a * S yd)) with (S a * (S xn * S yd)) by flia.
 rewrite <- Nat.mul_assoc, <- Nat.mul_sub_distr_l.
 replace (S xd * (S a * S yd)) with (S a * (S xd * S yd)) by flia.
 rewrite ggcd_mul_mono_l; [ | easy ].
 now destruct (ggcd (S xn * S yd - S yn * S xd) (S xd * S yd)).
-do 2 PQtac2.
 replace (S xn * (S a * S yd)) with (S a * (S xn * S yd)) by flia.
 rewrite <- Nat.mul_assoc, <- Nat.mul_sub_distr_l.
 apply Nat.sub_gt in Hyx.
 remember (_ - _) as u.
 destruct u; [ easy | cbn; flia ].
Qed.

Theorem PQred_mul_mul_one_l :
  ∀ x y a, PQred (x * y) = PQred (PQmake a a * x * y).
Proof.
intros (xn, xd) (yn, yd) a.
progress unfold PQred; simpl.
progress unfold "*"%PQ, PQ_of_nat.
progress unfold PQmul_num1, PQmul_den1; simpl.
PQtac1.
do 6 PQtac2.
do 2 rewrite <- Nat.mul_assoc.
rewrite ggcd_mul_mono_l; [ | easy ].
now destruct (ggcd (S (nn xn) * S (nn yn)) (S (nn xd) * S (nn yd))).
Qed.

Theorem PQred_eq : ∀ x, (PQred x == x)%PQ.
Proof.
intros (xn, xd).
progress unfold PQred; simpl.
remember (ggcd (nn xn + 1) (nn xd + 1)) as g eqn:Hg; symmetry in Hg.
destruct g as (g, (aa, bb)).
progress unfold "=="%PQ, nd; simpl.
specialize (ggcd_correct_divisors (nn xn + 1) (nn xd + 1)) as H.
rewrite Hg in H.
destruct H as (Hxn, Hxd).
rewrite Nat.sub_add; cycle 1. {
  destruct aa; [ | flia ].
  now rewrite Nat.add_1_r, Nat.mul_0_r in Hxn.
}
rewrite Nat.sub_add; cycle 1. {
  destruct bb; [ | flia ].
  now rewrite Nat.add_1_r, Nat.mul_0_r in Hxd.
}
rewrite Hxn, Hxd.
now rewrite Nat.mul_comm, Nat.mul_shuffle0.
Qed.

Theorem PQred_lt_l : ∀ x y, (x < y)%PQ ↔ (PQred x < y)%PQ.
Proof. intros; now rewrite PQred_eq. Qed.

Theorem PQred_lt_r : ∀ x y, (x < y ↔ x < PQred y)%PQ.
Proof. intros; now rewrite PQred_eq. Qed.

Theorem PQred_lt : ∀ x y, (x < y)%PQ ↔ (PQred x < PQred y)%PQ.
Proof. intros; now do 2 rewrite PQred_eq. Qed.

Theorem PQred_le : ∀ x y, (x ≤ y)%PQ ↔ (PQred x ≤ PQred y)%PQ.
Proof. intros; now do 2 rewrite PQred_eq. Qed.

Theorem PQred_add_l : ∀ x y, PQred (x + y) = PQred (PQred x + y).
Proof.
intros.
remember (Nat.gcd (nn (PQnum1 x) + 1) (nn (PQden1 x) + 1)) as a eqn:Ha.
rewrite (PQred_add_mul_one_l (PQred x) y (mknn (a - 1))).
f_equal; f_equal.
destruct x as (xn, xd).
simpl in Ha.
progress unfold "*"%PQ; simpl.
progress unfold PQmul_num1, PQmul_den1; simpl.
progress unfold PQred; simpl.
specialize (ggcd_split (nn xn + 1) (nn xd + 1) a Ha) as H.
rewrite H; simpl.
destruct a.
-symmetry in Ha.
 apply Nat.gcd_eq_0_l in Ha; flia Ha.
-replace (S a - 1 + 1) with (S a) by flia.
 assert (H2 : (nn xn + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (@Nat_gcd_le_l (nn xn + 1) (nn xd +  1)) as H2.
   assert (H3 : nn xn + 1 ≠ 0) by flia.
   specialize (H2 H3).
   flia Ha H1 H2.
 }
 assert (H3 : (nn xd + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (@Nat_gcd_le_r (nn xn + 1) (nn xd +  1)) as H3.
   assert (H4 : nn xd + 1 ≠ 0) by flia.
   specialize (H3 H4).
   flia Ha H1 H3.
 }
 rewrite Nat.sub_add; [ | flia H2 ].
 rewrite Nat.sub_add; [ | flia H3 ].
 specialize (Nat.gcd_divide_l (nn xn + 1) (nn xd + 1)) as (c1, Hc1).
 rewrite <- Ha in Hc1; rewrite Hc1.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc1, Nat.add_sub.
 specialize (Nat.gcd_divide_r (nn xn + 1) (nn xd + 1)) as (c2, Hc2).
 rewrite <- Ha in Hc2; rewrite Hc2.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc2, Nat.add_sub.
 now destruct xn, xd.
Qed.

Theorem PQred_sub_l : ∀ x y, (y < x)%PQ → PQred (x - y) = PQred (PQred x - y).
Proof.
intros * Hyx.
remember (Nat.gcd (nn (PQnum1 x) + 1) (nn (PQden1 x) + 1)) as a eqn:Ha.
rewrite (PQred_sub_mul_one_l (PQred x) y (mknn (a - 1))); cycle 1. {
  now apply -> PQred_lt_r.
}
destruct x as (xn, xd).
simpl in Ha.
progress unfold "*"%PQ; simpl.
progress unfold PQmul_num1, PQmul_den1; simpl.
progress unfold PQred; simpl.
specialize (ggcd_split (nn xn + 1) (nn xd + 1) a Ha) as H.
rewrite H; simpl.
destruct a.
-symmetry in Ha.
 apply Nat.gcd_eq_0_l in Ha; flia Ha.
-replace (S a - 1 + 1) with (S a) by flia.
 assert (H2 : (nn xn + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (@Nat_gcd_le_l (nn xn + 1) (nn xd +  1)) as H2.
   assert (H3 : nn xn + 1 ≠ 0) by flia.
   specialize (H2 H3).
   flia Ha H1 H2.
 }
 assert (H3 : (nn xd + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (@Nat_gcd_le_r (nn xn + 1) (nn xd +  1)) as H3.
   assert (H4 : nn xd + 1 ≠ 0) by flia.
   specialize (H3 H4).
   flia Ha H1 H3.
 }
 rewrite Nat.sub_add; [ | flia H2 ].
 rewrite Nat.sub_add; [ | flia H3 ].
 specialize (Nat.gcd_divide_l (nn xn + 1) (nn xd + 1)) as (c1, Hc1).
 rewrite <- Ha in Hc1; rewrite Hc1.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc1, Nat.add_sub.
 specialize (Nat.gcd_divide_r (nn xn + 1) (nn xd + 1)) as (c2, Hc2).
 rewrite <- Ha in Hc2; rewrite Hc2.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc2, Nat.add_sub.
 easy.
Qed.

Theorem PQred_sub_r : ∀ x y, (y < x)%PQ → PQred (x - y) = PQred (x - PQred y).
Proof.
intros * Hyx.
remember (Nat.gcd (nn (PQnum1 y) + 1) (nn (PQden1 y) + 1)) as a eqn:Ha.
rewrite (PQred_sub_mul_one_r x (PQred y) (mknn (a - 1))); cycle 1. {
  now apply -> PQred_lt_l.
}
destruct y as (yn, yd).
simpl in Ha.
progress unfold "*"%PQ; simpl.
progress unfold PQmul_num1, PQmul_den1; simpl.
progress unfold PQred; simpl.
specialize (ggcd_split (nn yn + 1) (nn yd + 1) a Ha) as H.
rewrite H; simpl.
destruct a.
-symmetry in Ha.
 apply Nat.gcd_eq_0_l in Ha; flia Ha.
-replace (S a - 1 + 1) with (S a) by flia.
 assert (H2 : (nn yn + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (@Nat_gcd_le_l (nn yn + 1) (nn yd +  1)) as H2.
   assert (H3 : nn yn + 1 ≠ 0) by flia.
   specialize (H2 H3).
   flia Ha H1 H2.
 }
 assert (H3 : (nn yd + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (@Nat_gcd_le_r (nn yn + 1) (nn yd +  1)) as H3.
   assert (H4 : nn yd + 1 ≠ 0) by flia.
   specialize (H3 H4).
   flia Ha H1 H3.
 }
 rewrite Nat.sub_add; [ | flia H2 ].
 rewrite Nat.sub_add; [ | flia H3 ].
 specialize (Nat.gcd_divide_l (nn yn + 1) (nn yd + 1)) as (c1, Hc1).
 rewrite <- Ha in Hc1; rewrite Hc1.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc1, Nat.add_sub.
 specialize (Nat.gcd_divide_r (nn yn + 1) (nn yd + 1)) as (c2, Hc2).
 rewrite <- Ha in Hc2; rewrite Hc2.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc2, Nat.add_sub.
 easy.
Qed.

Theorem PQred_add : ∀ x y, PQred (x + y) = PQred (PQred x + PQred y).
Proof.
intros.
rewrite PQred_add_l, PQadd_comm.
rewrite PQred_add_l, PQadd_comm.
easy.
Qed.
(* merci Bérénice ! *)

Theorem PQred_sub : ∀ x y,
  (y < x)%PQ → PQred (x - y) = PQred (PQred x - PQred y).
Proof.
intros.
rewrite PQred_sub_l; [ | easy ].
rewrite PQred_sub_r; [ easy | ].
now apply -> PQred_lt_r.
Qed.

Theorem PQred_mul_l : ∀ x y, PQred (x * y) = PQred (PQred x * y).
Proof.
intros.
remember (Nat.gcd (nn (PQnum1 x) + 1) (nn (PQden1 x) + 1)) as a eqn:Ha.
rewrite (PQred_mul_mul_one_l (PQred x) y (mknn (a - 1))).
destruct x as ((xn), (xd)).
simpl in Ha.
progress unfold "*"%PQ; simpl.
progress unfold PQmul_num1, PQmul_den1; simpl.
progress unfold PQred; simpl.
specialize (ggcd_split (xn + 1) (xd + 1) a Ha) as H.
rewrite H; simpl.
destruct a.
-symmetry in Ha.
 apply Nat.gcd_eq_0_l in Ha; flia Ha.
-replace (S a - 1 + 1) with (S a) by flia.
 assert (H2 : 1 ≤ (xn + 1) / S a). {
   apply Nat.div_str_pos.
   split; [ apply Nat.lt_0_succ | ].
   rewrite Ha; apply Nat_gcd_le_l.
   now rewrite Nat.add_1_r.
 }
 assert (H3 : 1 ≤ (xd + 1) / S a). {
   apply Nat.div_str_pos.
   split; [ apply Nat.lt_0_succ | ].
   rewrite Ha; apply Nat_gcd_le_r.
   now rewrite Nat.add_1_r.
 }
 do 2 (rewrite Nat.sub_add; [ | do 2 rewrite Nat.add_1_r; simpl; flia ]).
 rewrite Nat.sub_add. 2: {
   do 4 rewrite Nat.add_1_r.
   cbn; remember (_ + _) as z in |-*; flia.
 }
 rewrite Nat.sub_add. 2: {
   do 2 rewrite Nat.add_1_r.
   cbn; remember (_ + _) as z in |-*; flia.
 }
 rewrite Nat.sub_add; [ | easy ].
 rewrite Nat.sub_add.
 +rewrite Nat.sub_add.
  *rewrite Nat.sub_add; [ | easy ].
   rewrite <- Nat.Lcm0.divide_div_mul_exact.
  --rewrite <- Nat.Lcm0.divide_div_mul_exact.
   ++replace (S a * (xn + 1)) with ((xn + 1) * S a) by apply Nat.mul_comm.
     replace (S a * (xd + 1)) with ((xd + 1) * S a) by apply Nat.mul_comm.
     rewrite Nat.div_mul; [ | easy ].
     now rewrite Nat.div_mul.
   ++rewrite Ha; apply Nat.gcd_divide_r.
  --rewrite Ha; apply Nat.gcd_divide_l.
  *rewrite Nat.sub_add; [ | easy ].
   rewrite <- Nat.Lcm0.divide_div_mul_exact.
  --rewrite Nat.mul_comm, Nat.div_mul; [ flia | easy ].
  --rewrite Ha; apply Nat.gcd_divide_r.
 +rewrite Nat.sub_add.
  *rewrite Nat.sub_add; [ | easy ].
   do 2 rewrite Nat.add_1_r.
   eapply Nat.le_trans; [ | now apply Nat.le_mul_r ].
   do 2 rewrite Nat.add_1_r in Ha.
   rewrite <- Nat.Lcm0.divide_div_mul_exact.
  --rewrite Nat.mul_comm, Nat.div_mul; [ flia | easy ].
  --rewrite Ha; apply Nat.gcd_divide_r.
  *rewrite Nat.sub_add; [ | easy ].
   rewrite <- Nat.Lcm0.divide_div_mul_exact.
  --rewrite Nat.mul_comm, Nat.div_mul; [ flia | easy ].
  --rewrite Ha; apply Nat.gcd_divide_r.
Qed.

Theorem PQred_mul_r : ∀ x y, PQred (x * y) = PQred (x * PQred y).
Proof.
intros.
setoid_rewrite PQmul_comm.
apply PQred_mul_l.
Qed.

Theorem PQred_mul : ∀ x y, PQred (x * y) = PQred (PQred x * PQred y).
Proof.
intros.
now rewrite PQred_mul_l, PQred_mul_r.
Qed.

Theorem PQred_gcd : ∀ x,
  Nat.gcd (nn (PQnum1 (PQred x)) + 1) (nn (PQden1 (PQred x)) + 1) = 1.
Proof.
intros.
progress unfold PQred.
remember (ggcd (nn (PQnum1 x) + 1) (nn (PQden1 x) + 1)) as g eqn:Hg1.
destruct g as (g1, (aa1, bb1)); simpl.
remember (Nat.gcd (nn (PQnum1 x) + 1) (nn (PQden1 x) + 1)) as g eqn:Hg.
specialize (ggcd_split _ _ _ Hg) as H.
rewrite <- Hg1 in H.
do 2 rewrite Nat.add_1_r in Hg1; symmetry in Hg1.
rewrite Nat.sub_add.
-rewrite Nat.sub_add.
 +injection H; clear H; intros; subst g1 aa1 bb1.
  apply ggcd_succ_l in Hg1.
  now apply Nat.gcd_div_gcd.
 +apply ggcd_succ_r in Hg1; flia Hg1.
-apply ggcd_succ_l in Hg1; flia Hg1.
Qed.

Theorem gcd_1_PQred : ∀ x,
  Nat.gcd (nn (PQnum1 x) + 1) (nn (PQden1 x) + 1) = 1
  → x = PQred x.
Proof.
intros x Hx.
destruct x as ((xn), (xd)).
rewrite <- ggcd_gcd in Hx.
progress unfold PQred.
remember ggcd as f; cbn in Hx; cbn; subst f.
remember (ggcd (xn + 1) (xd + 1)) as g eqn:Hg.
destruct g as (g, (aa, bb)); cbn in Hx; subst g.
specialize (ggcd_correct_divisors (xn + 1) (xd + 1)) as H.
rewrite <- Hg in H; do 2 rewrite Nat.mul_1_l in H.
destruct H as (Hxn, Hxd).
subst aa bb.
now do 2 rewrite Nat.add_sub.
Qed.

Theorem PQeq_red_l : ∀ x y,
  x = PQred x → (x == y)%PQ → ∃ a, y = (a ╱ a * x)%PQ.
Proof.
intros * Hx Hxy.
progress unfold "=="%PQ, nd in Hxy.
specialize (PQred_gcd x) as Hg.
rewrite <- Hx in Hg.
destruct x as ((xn), (xd)), y as ((yn), (yd)).
cbn in Hxy, Hg.
assert (Hd : Nat.divide (xn + 1) ((xd + 1) * (yn + 1))). {
  rewrite Nat.mul_comm, <- Hxy.
  exists (yd + 1).
  apply Nat.mul_comm.
}
specialize (Nat.gauss _ _ _ Hd Hg) as H1.
destruct H1 as (c, Hc).
exists (mknn (c - 1)).
progress unfold "*"%PQ; cbn.
rewrite Nat.sub_add; cycle 1. {
  destruct c; [ now rewrite Nat.add_1_r in Hc | flia ].
}
rewrite <- Hc.
rewrite Nat.add_sub; f_equal.
symmetry in Hxy.
rewrite Hc, Nat.mul_shuffle0, Nat.mul_comm in Hxy.
apply Nat.mul_cancel_l in Hxy; [ | flia ].
now rewrite Hxy, Nat.add_sub.
Qed.

Theorem PQeq_red : ∀ x y,
  x = PQred x → y = PQred y → (x == y)%PQ ↔ x = y.
Proof.
intros * Hx Hy.
split; [ | now intros; subst y ].
intros Hxy.
specialize (PQeq_red_l x y Hx Hxy) as H1.
symmetry in Hxy.
specialize (PQeq_red_l y x Hy Hxy) as H2.
destruct H1 as ((c), Hc).
destruct H2 as ((d), Hd).
move d before c.
destruct x as ((xn), (xd)), y as ((yn), (yd)).
progress unfold "*"%PQ in Hc, Hd.
cbn in Hc, Hd.
injection Hc; clear Hc; intros H1 H2.
injection Hd; clear Hd; intros H3 H4.
destruct d.
-cbn in H3, H4.
 rewrite Nat.add_0_r, Nat.add_sub in H3, H4.
 now subst xd xn.
-cbn in H3, H4.
 rewrite Nat.add_comm, Nat.add_assoc in H3, H4.
 rewrite Nat.add_sub in H3, H4.
 destruct c.
 +cbn in H1, H2.
  rewrite Nat.add_0_r, Nat.add_sub in H1, H2.
  now subst xd xn.
 +cbn in H1, H2.
  rewrite Nat.add_comm, Nat.add_assoc in H1, H2.
  rewrite Nat.add_sub in H1, H2.
  cbn in H1, H2, H3, H4.
  rewrite H1 in H3 at 1.
  assert (H : c * (xd + 1) + d * (yd + 1) = 0) by flia H3.
  apply Nat.eq_add_0 in H.
  destruct H as (H5, H6).
  apply Nat.eq_mul_0 in H5.
  apply Nat.eq_mul_0 in H6.
  destruct H5 as [H5| H5]; [ | flia H5].
  destruct H6 as [H6| H6]; [ | flia H6].
  subst c d.
  cbn in H3.
  flia H3.
Qed.

Theorem PQred_diag : ∀ x, PQred (x ╱ x) = 1%PQ.
Proof.
intros (x).
progress unfold PQred.
cbn - [ ggcd ].
rewrite ggcd_diag; [ easy | flia ].
Qed.

Theorem PQle_decidable : ∀ x y, Decidable.decidable (x ≤ y)%PQ.
Proof.
intros.
progress unfold Decidable.decidable.
apply Nat.le_decidable.
Qed.
