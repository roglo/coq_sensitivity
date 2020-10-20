(* polynomials in a semiring *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Init.Nat.
Require Import Misc.

Require Import Semiring SRsummation.

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

Definition norm_polyn_list l := rev (strip_0s (rev l)).

Theorem fold_norm_polyn_list : ∀ la,
  rev (strip_0s (rev la)) = norm_polyn_list la.
Proof. easy. Qed.

(* polynomial from and to a list *)

Theorem polyn_of_list_prop : ∀ l,
  polyn_prop_test (λ i, nth i (norm_polyn_list l) 0%Srng)
    (length (norm_polyn_list l)) = true.
Proof.
intros.
unfold norm_polyn_list.
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
  mk_polyn (norm_polyn_list l) (polyn_of_list_prop l).

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

Definition _x := polyn_of_list [0; 1]%Srng.

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

Theorem fold_polyn_sub : ∀ P Q, polyn_add P (polyn_opp Q) = polyn_sub P Q.
Proof. easy. Qed.

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

Declare Scope polyn_list_scope.
Delimit Scope polyn_list_scope with PL.

(*
Notation "0" := ([]) : polyn_list_scope.
*)
Notation "1" := ([1%Srng]) : polyn_list_scope.
Notation "la + lb" := (polyn_list_add la lb) : polyn_list_scope.
Notation "la * lb" := (polyn_list_mul la lb) : polyn_list_scope.

Arguments polyn_degree {T so sdp} P%P.

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

(* often encountered cases: "if 0=0" and if "1=0" *)

Theorem if_0_eq_0 : ∀ A (a b : A),
  (if srng_eq_dec 0 0 then a else b) = a.
intros.
now destruct (srng_eq_dec 0 0).
Qed.

Theorem if_1_eq_0 : ∀ A (a b : A),
  (if srng_eq_dec 1 0 then a else b) = b.
intros.
destruct (srng_eq_dec 1 0) as [H| H]; [ now apply srng_1_neq_0 in H | ].
easy.
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
unfold norm_polyn_list.
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
now rewrite if_0_eq_0 in Pa.
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
  rewrite if_0_eq_0 in Hlc.
  apply IHla, Hlc.
}
cbn in Hlc.
destruct (srng_eq_dec a 0%Srng) as [H| H]; [ easy | clear H ].
now injection Hlc; clear Hlc; intros; subst c lc.
Qed.

Theorem strip_0s_repeat_0s : ∀ n,
  strip_0s (repeat 0%Srng n) = [].
Proof.
intros.
induction n; [ easy | cbn ].
now rewrite if_0_eq_0.
Qed.

Theorem eq_strip_0s_nil : ∀ la,
  strip_0s la = [] ↔ la = repeat 0%Srng (length la).
Proof.
intros.
split. {
  intros Hla.
  induction la as [| a]; [ easy | ].
  cbn in Hla.
  destruct (srng_eq_dec a 0%Srng) as [Haz| Haz]; [ | easy ].
  subst a.
  specialize (IHla Hla).
  now cbn; f_equal.
} {
  intros H; rewrite H.
  apply strip_0s_repeat_0s.
}
Qed.

Theorem norm_polyn_list_app : ∀ la lb,
  norm_polyn_list (la ++ lb) =
  match norm_polyn_list lb with
  | [] => norm_polyn_list la
  | lc => la ++ lc
  end.
Proof.
intros.
unfold norm_polyn_list.
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

Theorem norm_polyn_list_involutive : ∀ la,
  norm_polyn_list (norm_polyn_list la) = norm_polyn_list la.
Proof.
intros.
induction la as [| a] using rev_ind; [ easy | ].
rewrite norm_polyn_list_app.
remember (norm_polyn_list [a]) as x eqn:Hx.
cbn in Hx; subst x.
destruct (srng_eq_dec a 0) as [Haz| Haz]; [ easy | ].
cbn - [ norm_polyn_list ].
rewrite norm_polyn_list_app; cbn.
now destruct (srng_eq_dec a 0).
Qed.

Theorem norm_polyn_list_add_idemp_l : ∀ la lb,
  norm_polyn_list (polyn_list_add (norm_polyn_list la) lb) =
  norm_polyn_list (polyn_list_add la lb).
Proof.
intros.
unfold norm_polyn_list; f_equal.
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

Theorem norm_polyn_list_add_idemp_r : ∀ la lb,
  norm_polyn_list (polyn_list_add la (norm_polyn_list lb)) =
  norm_polyn_list (polyn_list_add la lb).
Proof.
intros.
rewrite polyn_list_add_comm.
rewrite norm_polyn_list_add_idemp_l.
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
rewrite norm_polyn_list_add_idemp_l.
rewrite norm_polyn_list_add_idemp_r.
f_equal.
apply polyn_list_add_assoc.
Qed.

Theorem polyn_add_add_swap : ∀ P Q R, (P + Q + R = P + R + Q)%P.
Proof.
intros.
do 2 rewrite <- polyn_add_assoc.
now rewrite (polyn_add_comm R).
Qed.

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
  now rewrite if_0_eq_0.
}
now rewrite if_0_eq_0.
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

Theorem polyn_list_convol_mul_0_r : ∀ n la i,
  polyn_list_convol_mul la (repeat 0%Srng n) i = 0%Srng.
Proof.
intros.
rewrite polyn_list_convol_mul_comm.
apply polyn_list_convol_mul_0_l.
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

Theorem map_polyn_list_convol_mul_0_r : ∀ n la li,
  map (polyn_list_convol_mul la (repeat 0%Srng n)) li =
  repeat 0%Srng (length li).
Proof.
intros.
induction li as [| i]; [ easy | ].
cbn - [ polyn_list_convol_mul ].
rewrite IHli; f_equal.
apply polyn_list_convol_mul_0_r.
Qed.

Theorem norm_polyn_list_repeat_0 : ∀ n,
  norm_polyn_list (repeat 0%Srng n) = [].
Proof.
intros.
induction n; [ easy | ].
rewrite List_repeat_succ_app.
rewrite norm_polyn_list_app; cbn.
now rewrite if_0_eq_0.
Qed.

Theorem map_polyn_list_convol_mul_comm : ∀ la lb ln,
  map (polyn_list_convol_mul la lb) ln =
  map (polyn_list_convol_mul lb la) ln.
Proof.
intros.
unfold polyn_list_convol_mul.
apply map_ext_in.
intros i Hi.
unfold so.
rewrite srng_summation_rtl.
apply srng_summation_eq_compat.
intros j Hj.
rewrite Nat.add_0_r.
rewrite Nat_sub_sub_distr; [ | easy ].
rewrite Nat.sub_diag, Nat.add_0_l.
apply srng_mul_comm.
Qed.

Theorem map_polyn_list_convol_mul_cons_r_gen : ∀ b la lb sta len,
  map (polyn_list_convol_mul la (b :: lb)) (seq sta len) =
  polyn_list_add
    (map (λ n, nth n la 0 * b) (seq sta len))%Srng
    (map
       (λ n,
          if zerop n then 0%Srng
          else (Σ (j = 0, n - 1), nth j la 0 * nth (n - j - 1) lb 0)%Srng)
       (seq sta len)).
Proof.
intros.
unfold polyn_list_convol_mul.
revert sta.
induction len; intros; [ easy | ].
rewrite List_seq_succ_r.
rewrite map_app, IHlen.
do 2 rewrite map_app.
rewrite polyn_list_add_app_r, map_length.
rewrite firstn_app, map_length, Nat.sub_diag, firstn_O.
rewrite app_nil_r.
rewrite skipn_app, map_length, Nat.sub_diag, skipn_O.
rewrite polyn_list_add_app_l.
rewrite skipn_length.
do 2 rewrite List_firstn_map.
rewrite map_length.
do 2 rewrite List_skipn_map.
rewrite seq_length.
rewrite List_firstn_seq, Nat.min_id.
rewrite List_skipn_seq; [ | easy ].
rewrite Nat.sub_diag.
rewrite polyn_list_add_0_l.
remember (firstn 0 _) as x; cbn in Heqx; subst x.
remember (skipn 0 _) as x; cbn in Heqx; subst x.
remember (map _ []) as x; cbn in Heqx; subst x.
rewrite app_nil_l.
f_equal.
cbn - [ nth seq sub ].
f_equal.
destruct (Nat.eq_dec (sta + len) 0) as [Hz| Hz]. {
  rewrite Hz; cbn.
  apply srng_add_comm.
}
remember (sta + len) as n eqn:Hn.
destruct n; [ easy | ].
cbn - [ nth seq sub ].
rewrite srng_add_comm.
replace (S n - 1) with n by flia.
unfold so.
rewrite srng_summation_split_last; [ | apply Nat.le_0_l ].
rewrite Nat.sub_diag.
f_equal.
rewrite srng_summation_succ_succ.
apply srng_summation_eq_compat.
intros i Hi.
rewrite Nat.sub_succ, Nat.sub_0_r.
f_equal.
replace (S n - i) with (S (n - i)) by flia Hi.
now rewrite Nat.sub_succ, Nat.sub_0_r.
Qed.

Theorem map_polyn_list_convol_mul_cons_r : ∀ b la lb len,
  map (polyn_list_convol_mul la (b :: lb)) (seq 0 (S len)) =
  polyn_list_add (map (λ n, (nth n la 0 * b)%Srng) (seq 0 (S len)))
    (0%Srng :: map (λ n, polyn_list_convol_mul la lb (n - 1)) (seq 1 len)).
Proof.
intros.
rewrite map_polyn_list_convol_mul_cons_r_gen.
f_equal.
rewrite <- (Nat.add_1_l len).
rewrite seq_app.
cbn - [ nth seq sub ].
rewrite map_app.
replace (seq 0 1) with [0] by easy.
cbn - [ nth seq sub ].
f_equal.
apply map_ext_in.
intros i Hi.
apply in_seq in Hi.
destruct (zerop i) as [H| H]; [ flia Hi H | ].
apply srng_summation_eq_compat.
intros j Hj.
now rewrite Nat_sub_sub_swap.
Qed.

(* (a+xP)Q = aQ+x(PQ) *)
Theorem map_polyn_list_convol_mul_cons_l : ∀ a la lb len,
  map (polyn_list_convol_mul (a :: la) lb) (seq 0 (S len)) =
  polyn_list_add (map (λ n, (a * nth n lb 0)%Srng) (seq 0 (S len)))
    (0%Srng :: map (λ n, polyn_list_convol_mul la lb (n - 1)) (seq 1 len)).
Proof.
intros.
rewrite map_polyn_list_convol_mul_comm.
rewrite map_polyn_list_convol_mul_cons_r.
erewrite map_ext_in. 2: {
  intros i Hi.
  apply srng_mul_comm.
}
f_equal; f_equal.
erewrite map_ext_in. 2: {
  intros i Hi.
  apply polyn_list_convol_mul_comm.
}
easy.
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

Theorem all_0_norm_polyn_list_map_0 : ∀ A (ln : list A) f,
  (∀ n, n ∈ ln → f n = 0%Srng)
  ↔ norm_polyn_list (map f ln) = [].
Proof.
intros A *.
split; intros Hf. {
  unfold norm_polyn_list.
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
} {
  intros n Hn.
  unfold norm_polyn_list in Hf.
  apply List_eq_rev_nil in Hf.
  apply eq_strip_0s_nil in Hf.
  rewrite rev_length, map_length in Hf.
  apply List_eq_rev_l in Hf.
  apply (in_map f) in Hn.
  rewrite Hf in Hn.
  apply in_rev in Hn.
  now apply repeat_spec in Hn.
}
Qed.

Theorem length_strip_0s_le : ∀ la, length (strip_0s la) ≤ length la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
destruct (srng_eq_dec a 0) as [Haz| Haz]; [ | easy ].
transitivity (length la); [ easy | ].
apply Nat.le_succ_diag_r.
Qed.

Theorem norm_polyn_list_cons_0 : ∀ la lb,
  norm_polyn_list la = norm_polyn_list lb
  → norm_polyn_list (0%Srng :: la) =
     norm_polyn_list (0%Srng :: lb).
Proof.
intros * Hll.
unfold norm_polyn_list in Hll |-*.
f_equal.
apply List_rev_inj in Hll; cbn.
do 2 rewrite strip_0s_app.
now rewrite Hll.
Qed.

Theorem polyn_list_convol_mul_more : ∀ n la lb i len,
  length la + length lb - 1 ≤ i + len
  → norm_polyn_list (map (polyn_list_convol_mul la lb) (seq i len)) =
    norm_polyn_list (map (polyn_list_convol_mul la lb) (seq i (len + n))).
Proof.
intros.
induction n; [ now rewrite Nat.add_0_r | ].
rewrite Nat.add_succ_r.
rewrite List_seq_succ_r.
rewrite map_app.
rewrite norm_polyn_list_app.
rewrite <- IHn.
cbn - [ norm_polyn_list nth seq sub ].
unfold polyn_list_convol_mul at 2.
unfold so.
rewrite all_0_srng_summation_0; [ now cbn; rewrite if_0_eq_0 | ].
intros j (_, Hj).
destruct (le_dec (length la) j) as [H1| H1]. {
  rewrite nth_overflow; [ | easy ].
  apply srng_mul_0_l.
} {
  apply Nat.nle_gt in H1.
  destruct (le_dec (length lb) (i + (len + n) - j)) as [H2| H2]. {
    rewrite (nth_overflow lb); [ | easy ].
    apply srng_mul_0_r.
  }
  exfalso; apply H2; clear H2.
  flia H H1.
}
Qed.

Fixpoint map_seq A (f : nat → A) b len :=
  match len with
  | 0 => []
  | S len' => f b :: map_seq f (S b) len'
  end.

Theorem eq_map_seq : ∀ A (f : nat → A) b len,
  map f (seq b len) = map_seq f b len.
Proof.
intros A *.
revert b.
induction len; intros; [ easy | cbn ].
now rewrite IHlen.
Qed.

Theorem norm_polyn_list_app_repeat_0 : ∀ la,
  la =
    norm_polyn_list la ++
    repeat 0%Rng (length la - length (norm_polyn_list la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn.
rewrite rev_length.
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  destruct (srng_eq_dec a 0) as [Haz| Haz]. {
    cbn; subst a; f_equal.
    apply eq_strip_0s_nil in Hlb.
    apply List_eq_rev_l in Hlb.
    now rewrite rev_length, List_rev_repeat in Hlb.
  } {
    cbn; f_equal.
    rewrite Nat.sub_0_r.
    apply eq_strip_0s_nil in Hlb.
    apply List_eq_rev_l in Hlb.
    now rewrite rev_length, List_rev_repeat in Hlb.
  }
} {
  cbn.
  rewrite rev_app_distr; cbn; f_equal.
  replace (rev lb ++ [b]) with (rev (b :: lb)) by easy.
  rewrite <- Hlb.
  rewrite app_length; cbn.
  rewrite Nat.add_1_r.
  replace (S (length lb)) with (length (b :: lb)) by easy.
  rewrite <- Hlb.
  now rewrite <- (rev_length (strip_0s _)).
}
Qed.

Theorem polyn_list_convol_mul_app_rep_0_l : ∀ la lb i len n,
  norm_polyn_list
    (map (polyn_list_convol_mul (la ++ repeat 0%Srng n) lb) (seq i len)) =
  norm_polyn_list
    (map (polyn_list_convol_mul la lb) (seq i len)).
Proof.
intros.
revert la i len.
induction n; intros; [ now cbn; rewrite app_nil_r | cbn ].
remember (0%Srng) as z.
replace (z :: repeat z n) with ([z] ++ repeat z n) by easy.
subst z.
rewrite app_assoc.
rewrite IHn; clear n IHn.
revert la i.
induction len; intros; [ easy | ].
rewrite <- Nat.add_1_l.
rewrite seq_app.
do 2 rewrite map_app.
do 2 rewrite norm_polyn_list_app.
cbn - [ norm_polyn_list nth sub ].
rewrite IHlen.
assert
  (Hll :
     polyn_list_convol_mul la lb i =
     polyn_list_convol_mul (la ++ [0%Srng]) lb i). {
  unfold polyn_list_convol_mul.
  apply srng_summation_eq_compat.
  intros j Hj.
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. {
    now rewrite app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (nth_overflow la); [ | easy ].
  rewrite app_nth2; [ | easy ].
  destruct (Nat.eq_dec j (length la)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  symmetry.
  rewrite nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
}
now rewrite Hll.
Qed.

Theorem norm_polyn_list_cons_norm : ∀ a la lb i len,
  length (a :: la) + length lb - 1 ≤ i + len
  → norm_polyn_list
      (map (polyn_list_convol_mul (a :: norm_polyn_list la) lb) (seq i len)) =
    norm_polyn_list
      (map (polyn_list_convol_mul (a :: la) lb) (seq i len)).
Proof.
intros * Hlen.
rewrite (norm_polyn_list_app_repeat_0 la) at 2.
rewrite app_comm_cons.
now rewrite polyn_list_convol_mul_app_rep_0_l.
Qed.

Theorem norm_polyn_list_mul_idemp_l : ∀ la lb,
  norm_polyn_list (polyn_list_mul (norm_polyn_list la) lb) =
  norm_polyn_list (polyn_list_mul la lb).
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
  apply List_eq_rev_l in Hlc.
  rewrite List_rev_repeat, rev_length in Hlc.
  rewrite Hlc.
  cbn - [ nth seq sub ].
  destruct (srng_eq_dec a 0) as [Haz| Haz]. {
    subst a.
    cbn - [ nth seq sub ].
    rewrite (map_polyn_list_convol_mul_0_l 0).
    rewrite seq_length.
    rewrite norm_polyn_list_repeat_0; cbn.
    symmetry.
    apply List_eq_rev_nil.
    rewrite rev_involutive.
    apply eq_strip_0s_nil.
    rewrite repeat_length.
    rewrite Nat.sub_0_r.
    rewrite rev_length, map_length, seq_length.
    symmetry.
    apply List_eq_rev_l.
    rewrite List_rev_repeat; symmetry.
    rewrite (map_polyn_list_convol_mul_0_l (S (length la))).
    now rewrite seq_length.
  }
  rewrite Nat.sub_succ, Nat.sub_0_r.
  rewrite Nat.sub_succ, Nat.sub_0_r.
  rewrite repeat_length; cbn.
  rewrite (map_polyn_list_convol_mul_const_l 0).
  rewrite (map_polyn_list_convol_mul_const_l (length la)).
  rewrite Nat.add_comm.
  rewrite seq_app, map_app.
  rewrite norm_polyn_list_app; cbn.
  remember (norm_polyn_list (map _ (seq _ (length la)))) as ld eqn:Hld.
  symmetry in Hld.
  destruct ld as [| d]; [ easy | exfalso ].
  rewrite map_ext_in with (g := λ i, 0%Srng) in Hld. 2: {
    intros j Hj.
    apply in_seq in Hj.
    rewrite nth_overflow; [ | easy ].
    apply srng_mul_0_r.
  }
  now rewrite (proj1 (all_0_norm_polyn_list_map_0 _ _)) in Hld.
}
rewrite Nat.sub_succ, Nat.sub_0_r.
rewrite app_comm_cons, app_length.
cbn - [ norm_polyn_list ].
rewrite Nat.sub_0_r.
rewrite rev_app_distr; cbn.
do 2 rewrite (Nat.add_comm _ (length lb)).
rewrite
  (polyn_list_convol_mul_more
     (length la - length (norm_polyn_list la))). 2: {
  cbn; rewrite app_length, rev_length; cbn.
  rewrite Nat.sub_0_r.
  now rewrite Nat.add_comm.
}
remember (norm_polyn_list la) as x eqn:Hx.
unfold norm_polyn_list in Hx.
rewrite Hlc in Hx; subst x.
rewrite rev_length.
remember (length (c :: lc)) as x eqn:Hx.
cbn in Hx; subst x.
rewrite <- Nat.add_assoc.
rewrite Nat.add_sub_assoc. 2: {
  specialize (length_strip_0s_le (rev la)) as H.
  now rewrite Hlc, rev_length in H.
}
rewrite Nat.add_1_r, (Nat.add_comm _ (length la)).
rewrite Nat.add_sub.
unfold norm_polyn_list at 2.
replace (rev lc ++ [c]) with (rev (c :: lc)) by easy.
rewrite <- Hlc.
do 2 rewrite fold_norm_polyn_list.
apply norm_polyn_list_cons_norm.
cbn.
now rewrite Nat.sub_0_r, Nat.add_comm.
Qed.

Theorem norm_polyn_list_mul_idemp_r : ∀ la lb,
  norm_polyn_list (polyn_list_mul la (norm_polyn_list lb)) =
  norm_polyn_list (polyn_list_mul la lb).
Proof.
intros.
rewrite polyn_list_mul_comm.
rewrite norm_polyn_list_mul_idemp_l.
now rewrite polyn_list_mul_comm.
Qed.

Theorem polyn_of_list_mul_1_l : ∀ la,
  polyn_list_mul (polyn_list 1%P) la = la.
Proof.
intros.
cbn - [ seq ].
rewrite if_1_eq_0.
cbn - [ seq ].
unfold polyn_list_mul.
unfold length at 1.
rewrite (Nat.add_comm 1), Nat.add_sub.
replace (map _ _) with (map (λ i, nth i la 0%Srng) (seq 0 (length la))). 2: {
  apply map_ext_in.
  intros j Hj.
  apply in_seq in Hj.
  unfold polyn_list_convol_mul.
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
unfold norm_polyn_list.
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
apply (f_equal length) in Hlb.
cbn in Hlb; rewrite rev_length in Hlb.
rewrite rev_nth in Hz; [ | flia Hlb ].
rewrite <- Hlb, Nat.sub_diag in Hz.
clear Hlb.
induction lb as [| b]; [ easy | ].
cbn in Hz |-*.
now destruct (srng_eq_dec b 0).
Qed.

Theorem polyn_mul_1_r : ∀ P, (P * 1)%P = P.
Proof.
intros.
rewrite polyn_mul_comm.
apply polyn_mul_1_l.
Qed.

Theorem eq_norm_polyn_list_eq_length : ∀ la lb,
  norm_polyn_list la = norm_polyn_list lb
  → length la = length lb
  → la = lb.
Proof.
intros * Hll Hlen.
unfold norm_polyn_list in Hll.
apply (f_equal (@rev _)) in Hll.
do 2 rewrite rev_involutive in Hll.
setoid_rewrite <- rev_length in Hlen.
apply List_rev_inj.
remember (rev la) as l; clear la Heql; rename l into la.
remember (rev lb) as l; clear lb Heql; rename l into lb.
revert la Hll Hlen.
induction lb as [| b]; intros. {
  now apply length_zero_iff_nil in Hlen.
}
destruct la as [| a]; [ easy | ].
cbn in Hll, Hlen.
apply Nat.succ_inj in Hlen.
destruct (srng_eq_dec a 0) as [Haz| Haz]. {
  destruct (srng_eq_dec b 0) as [Hbz| Hbz]. {
    subst a b; f_equal.
    now apply IHlb.
  }
  exfalso; clear - Hbz Hll Hlen.
  assert (H : length la ≤ length lb) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction la as [| a]; [ easy | ].
  cbn in Hll.
  destruct (srng_eq_dec a 0) as [Haz| Haz]. {
    cbn in Hlen.
    apply IHla; [ easy | flia Hlen ].
  }
  rewrite Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
destruct (srng_eq_dec b 0) as [Hbz| Hbz]. {
  exfalso; clear b Hbz.
  clear - Haz Hll Hlen.
  assert (H : length lb ≤ length la) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction lb as [| b]; [ easy | ].
  cbn in Hll.
  destruct (srng_eq_dec b 0) as [Hbz| Hbz]. {
    cbn in Hlen.
    apply IHlb; [ easy | flia Hlen ].
  }
  rewrite <- Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
easy.
Qed.

Fixpoint polyn_list_convol_mul_add (la lb lc : list T) i len :=
  match len with
  | O => []
  | S len1 =>
      (Σ (j = 0, i),
       List.nth j la 0 *
       (List.nth (i - j) lb 0 + List.nth (i - j) lc 0))%Srng ::
       polyn_list_convol_mul_add la lb lc (S i) len1
  end.

Theorem list_polyn_nth_add : ∀ k la lb,
  (List.nth k (la + lb)%PL 0 =
   List.nth k la 0 + List.nth k lb 0)%Srng.
Proof.
intros k la lb.
revert la lb.
induction k; intros. {
 destruct la as [| a]; cbn; [ now rewrite srng_add_0_l | ].
 destruct lb as [| b]; cbn; [ now rewrite srng_add_0_r | easy ].
} {
 destruct la as [| a]; cbn; [ now rewrite srng_add_0_l | ].
 destruct lb as [| b]; cbn; [ now rewrite srng_add_0_r | easy ].
}
Qed.

Theorem map_polyn_list_convol_mul_add : ∀ la lb lc i len,
  map (polyn_list_convol_mul la (lb + lc)%PL) (seq i len) =
  polyn_list_convol_mul_add la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ easy | ].
rewrite <- Nat.add_1_l.
rewrite seq_app.
rewrite map_app.
rewrite IHlen.
rewrite (Nat.add_comm i).
cbn - [ nth ]; f_equal.
rewrite Nat.sub_0_r.
do 2 rewrite srng_add_0_l.
unfold so.
do 2 (rewrite fold_left_srng_add_fun_from_0; symmetry).
f_equal. {
  f_equal.
  apply list_polyn_nth_add.
}
replace i with (S i - 1) at 1 2 by flia.
apply srng_summation_eq_compat.
intros j Hj.
now rewrite list_polyn_nth_add.
Qed.

Theorem map_polyn_list_add_convol_mul : ∀ la lb lc i len,
  (map (polyn_list_convol_mul la lb) (seq i len) +
   map (polyn_list_convol_mul la lc) (seq i len))%PL =
  polyn_list_convol_mul_add la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ easy | ].
cbn - [ nth sub ].
rewrite IHlen; f_equal.
unfold polyn_list_convol_mul.
unfold so.
rewrite <- srng_summation_add_distr.
apply srng_summation_eq_compat; intros j (_, Hj).
now rewrite srng_mul_add_distr_l.
Qed.

Theorem norm_polyn_list_mul_add_distr_l : ∀ la lb lc,
  norm_polyn_list (la * (lb + lc))%PL =
  norm_polyn_list (la * lb + la * lc)%PL.
Proof.
intros la lb lc.
unfold polyn_list_mul.
remember (length la + length (lb + lc)%PL - 1) as labc.
remember (length la + length lb - 1) as lab.
remember (length la + length lc - 1) as lac.
rewrite Heqlabc.
remember (lb + lc)%PL as lbc.
symmetry in Heqlbc.
rewrite <- Heqlbc in Heqlabc |-*.
rewrite (polyn_list_convol_mul_more (lab + lac)); [ | subst; flia ].
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite <- norm_polyn_list_add_idemp_l.
rewrite (polyn_list_convol_mul_more (labc + lac)); [ | flia ].
rewrite <- Heqlab.
rewrite norm_polyn_list_add_idemp_l.
rewrite polyn_list_add_comm.
rewrite <- norm_polyn_list_add_idemp_l.
rewrite Heqlac.
rewrite (polyn_list_convol_mul_more (labc + lab)); [ | flia ].
rewrite norm_polyn_list_add_idemp_l.
rewrite <- Heqlac.
rewrite Nat.add_comm.
rewrite polyn_list_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite map_polyn_list_convol_mul_add.
now rewrite map_polyn_list_add_convol_mul.
Qed.

Theorem polyn_list_mul_add_distr_l : ∀ la lb lc,
  (la * (lb + lc))%PL = (la * lb + la * lc)%PL.
Proof.
intros.
apply eq_norm_polyn_list_eq_length. {
  apply norm_polyn_list_mul_add_distr_l.
}
unfold polyn_list_mul.
rewrite map_length, seq_length.
do 2 rewrite polyn_list_add_length.
do 2 rewrite map_length, seq_length.
rewrite <- Nat.add_max_distr_l.
now rewrite Nat.sub_max_distr_r.
Qed.

Theorem polyn_mul_add_distr_l : ∀ P Q R, (P * (Q + R) = P * Q + P * R)%P.
Proof.
intros.
unfold polyn_mul.
apply polyn_eq; cbn.
rewrite fold_norm_polyn_list.
rewrite norm_polyn_list_mul_idemp_r.
rewrite norm_polyn_list_add_idemp_l.
rewrite norm_polyn_list_add_idemp_r.
f_equal.
apply polyn_list_mul_add_distr_l.
Qed.

Theorem polyn_list_mul_0_l : ∀ la,
  norm_polyn_list ([] * la)%PL = [].
Proof.
intros.
apply List_eq_rev_r.
apply eq_strip_0s_nil; cbn.
rewrite rev_length, map_length.
rewrite seq_length.
apply List_eq_rev_r.
rewrite List_rev_repeat.
rewrite (map_polyn_list_convol_mul_0_l 0).
now rewrite seq_length.
Qed.

Theorem polyn_list_mul_0_r : ∀ la,
  norm_polyn_list (la * [])%PL = [].
Proof.
intros.
rewrite polyn_list_mul_comm.
apply polyn_list_mul_0_l.
Qed.

Theorem polyn_mul_0_l : ∀ P, (0 * P = 0)%P.
Proof.
intros.
apply polyn_eq.
apply polyn_list_mul_0_l.
Qed.

Theorem polyn_mul_0_r : ∀ P, (P * 0 = 0)%P.
Proof.
intros.
rewrite polyn_mul_comm.
apply polyn_mul_0_l.
Qed.

Theorem list_nth_polyn_list_eq : ∀ la lb,
  (∀ i, (List.nth i la 0 = List.nth i lb 0)%Rng)
  → norm_polyn_list la = norm_polyn_list lb.
Proof.
intros * Hi.
unfold norm_polyn_list; f_equal.
revert lb Hi.
induction la as [| a]; intros. {
  induction lb as [| b]; [ easy | ].
  specialize (Hi 0) as H; cbn in H.
  subst b; cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (rev lb)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]; [ now destruct (srng_eq_dec _ _) | ].
  assert (H : norm_polyn_list [] = norm_polyn_list lb). {
    unfold norm_polyn_list; cbn.
    cbn in IHlb.
    change (rev [] = rev (strip_0s (rev lb))).
    f_equal.
    rewrite Hlc.
    apply IHlb.
    intros i; cbn; rewrite match_id.
    now specialize (Hi (S i)); cbn in Hi.
  }
  cbn in H.
  unfold norm_polyn_list in H.
  rewrite Hlc in H.
  symmetry in H.
  now apply List_eq_rev_nil in H.
} {
  cbn.
  rewrite strip_0s_app.
  remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]. {
    assert (Hla : ∀ i, nth i la 0%Rng = 0%Rng). {
      intros i.
      clear - Hlc.
      revert i.
      induction la as [| a]; intros; [ now cbn; rewrite match_id | cbn ].
      destruct i. {
        cbn in Hlc.
        rewrite strip_0s_app in Hlc; cbn in Hlc.
        remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
        destruct lb as [| b]; [ now destruct (srng_eq_dec a 0) | easy ].
      }
      apply IHla.
      cbn in Hlc.
      rewrite strip_0s_app in Hlc; cbn in Hlc.
      remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
      destruct lb as [| b]; [ now destruct (srng_eq_dec a 0) | easy ].
    }
    cbn.
    destruct (srng_eq_dec a 0) as [Haz| Haz]. {
      assert (Hlb : ∀ i, nth i lb 0%Rng = 0%Rng). {
        intros.
        rewrite <- Hi; cbn.
        destruct i; [ easy | ].
        apply Hla.
      }
      clear - Hlb.
      induction lb as [| b]; [ easy | cbn ].
      specialize (Hlb 0) as H1; cbn in H1; subst b.
      rewrite strip_0s_app; cbn.
      rewrite <- IHlb; [ now rewrite if_0_eq_0 | ].
      intros i.
      now specialize (Hlb (S i)).
    }
    destruct lb as [| b]; [ now specialize (Hi 0); cbn in Hi | cbn ].
    rewrite strip_0s_app; cbn.
    remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
    destruct ld as [| d]. {
      destruct (srng_eq_dec b 0) as [Hbz| Hbz]. {
        subst b.
        now specialize (Hi 0).
      }
      f_equal.
      now specialize (Hi 0).
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, nth i la 0%Rng = nth i lb 0%Rng). {
      intros i.
      now specialize (Hi (S i)); cbn in Hi.
    }
    specialize (IHla H); clear H.
    now rewrite Hld in IHla.
  }
  destruct lb as [| b]. {
    specialize (IHla []).
    assert (H : ∀ i : nat, nth i la 0%Rng = nth i [] 0%Rng). {
      intros i; cbn; rewrite match_id.
      now specialize (Hi (S i)).
    }
    now specialize (IHla H).
  }
  cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
  destruct ld as [| d]. {
    destruct (srng_eq_dec b 0) as [Hbz| Hbz]. {
      subst b.
      specialize (IHla lb).
      assert (H : ∀ i : nat, nth i la 0%Rng = nth i lb 0%Rng). {
        intros i.
        now specialize (Hi (S i)); cbn in Hi.
      }
      specialize (IHla H); clear H.
      now rewrite Hld in IHla.
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, nth i la 0%Rng = nth i lb 0%Rng). {
      intros i.
      now specialize (Hi (S i)); cbn in Hi.
    }
    specialize (IHla H); clear H.
    now rewrite Hld in IHla.
  }
  specialize (Hi 0) as H1; cbn in H1; subst b.
  do 2 rewrite app_comm_cons; f_equal.
  rewrite <- Hld.
  apply IHla.
  now intros i; specialize (Hi (S i)).
}
Qed.

Theorem list_nth_polyn_list_convol_mul_aux : ∀ la lb n i len,
  List.length la + List.length lb - 1 = (i + len)%nat
  → (List.nth n (map (polyn_list_convol_mul la lb) (seq i len)) 0%Rng =
     Σ (j = 0, n + i),
     List.nth j la 0 * List.nth (n + i - j) lb 0)%Rng.
Proof.
intros la lb n i len Hlen.
revert la lb i n Hlen.
induction len; intros. {
  rewrite Nat.add_0_r in Hlen.
  rewrite all_0_srng_summation_0; [ now destruct n | ].
  intros j (_, Hj).
  destruct (le_dec (length la) j) as [H1| H1]. {
    rewrite nth_overflow; [ | easy ].
    now rewrite srng_mul_0_l.
  }
  destruct (le_dec (length lb) (n + i - j)) as [H2| H2]. {
   rewrite srng_mul_comm.
   rewrite nth_overflow; [ | easy ].
   now rewrite rng_mul_0_l.
  }
  exfalso; apply H2; clear Hj H2.
  apply Nat.nle_gt in H1; subst i.
  flia H1.
} {
  destruct n; [ easy | ].
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
  cbn - [ iterate sub ].
  rewrite IHlen; [ | easy ].
  now rewrite Nat.add_succ_r, <- Nat.add_succ_l.
}
Qed.

Theorem list_nth_polyn_list_convol_mul : ∀ la lb i len,
  len = length la + length lb - 1
  → (List.nth i (map (polyn_list_convol_mul la lb) (seq 0 len)) 0 =
     Σ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%Rng.
Proof.
intros la lb i len Hlen.
symmetry in Hlen.
rewrite list_nth_polyn_list_convol_mul_aux; [ | easy ].
now rewrite Nat.add_0_r.
Qed.

Theorem srng_summation_mul_polyn_list_nth_map_list_convol_mul : ∀ la lb lc k,
  (Σ (i = 0, k),
     List.nth i la 0 *
     List.nth (k - i)
       (map (polyn_list_convol_mul lb lc) (seq 0 (length lb + length lc - 1)))
       0 =
   Σ (i = 0, k),
     List.nth i la 0 *
     Σ (j = 0, k - i),
       List.nth j lb 0 * List.nth (k - i - j) lc 0)%Rng.
Proof.
intros la lb lc k.
apply srng_summation_eq_compat; intros i (_, Hi).
f_equal.
now rewrite list_nth_polyn_list_convol_mul.
Qed.

Theorem srng_summation_mul_polyn_list_nth_map_list_convol_mul_2 : ∀ la lb lc k,
   (Σ (i = 0, k),
      List.nth i lc 0 *
      List.nth (k - i)
        (map (polyn_list_convol_mul la lb)
           (seq 0 (length la + length lb - 1))) 0 =
    Σ (i = 0, k),
      List.nth (k - i) lc 0 *
      Σ (j = 0, i),
        List.nth j la 0 * List.nth (i - j) lb 0)%Rng.
Proof.
intros la lb lc k.
rewrite srng_summation_rtl.
apply srng_summation_eq_compat; intros i (_, Hi).
rewrite Nat.add_0_r.
f_equal.
rewrite Nat_sub_sub_distr; [ | easy ].
rewrite Nat.sub_diag.
now apply list_nth_polyn_list_convol_mul.
Qed.

Theorem srng_summation_aux_summation_aux_mul_swap : ∀ g1 (g2 : nat → T) g3 b1 b2 len,
  fold_left
    (λ c i, (c + fold_left (λ d j, d + g2 i * g3 i j) (seq b2 (g1 i)) 0)%Rng)
    (seq b1 len) 0%Rng =
  fold_left
    (λ c i, (c + g2 i * fold_left (λ d j, d + g3 i j) (seq b2 (g1 i)) 0)%Rng)
    (seq b1 len) 0%Rng.
Proof.
intros.
revert b1 b2.
induction len; intros; [ easy | ].
rewrite List_seq_succ_r.
do 2 rewrite fold_left_app.
rewrite IHlen.
rewrite fold_left_srng_add_fun_from_0; symmetry.
rewrite fold_left_srng_add_fun_from_0; symmetry.
apply srng_add_compat_l.
...
apply summation_aux_mul_swap.
Qed.

...

Theorem srng_summation_summation_mul_swap : ∀ g1 (g2 : nat → T) g3 k,
  (Σ (i = 0, k), (Σ (j = 0, g1 i), g2 i * g3 i j)
   = Σ (i = 0, k), g2 i * Σ (j = 0, g1 i), g3 i j)%Rng.
Proof.
intros.
apply srng_summation_aux_summation_aux_mul_swap.
Qed.

Theorem norm_polyn_list_mul_assoc : ∀ la lb lc,
  norm_polyn_list (la * (lb * lc))%PL =
  norm_polyn_list ((la * lb) * lc)%PL.
Proof.
intros la lb lc.
symmetry; rewrite polyn_list_mul_comm.
unfold polyn_list_mul.
do 2 rewrite map_length, seq_length.
destruct lc as [| c]. {
  destruct la as [| a]. {
    do 2 rewrite (map_polyn_list_convol_mul_0_l 0).
    now rewrite (Nat.add_comm (length []) (length lb)).
  }
  destruct lb as [| b]. {
    do 2 rewrite (map_polyn_list_convol_mul_0_l 0).
    rewrite (map_polyn_list_convol_mul_0_r 0).
    now do 2 rewrite norm_polyn_list_repeat_0.
  }
  cbn - [ norm_polyn_list ].
  rewrite (map_polyn_list_convol_mul_0_l 0).
  rewrite (map_polyn_list_convol_mul_0_r 0).
  rewrite map_polyn_list_convol_mul_0_r.
  now do 2 rewrite norm_polyn_list_repeat_0.
}
destruct la as [| a]. {
  do 2 rewrite (map_polyn_list_convol_mul_0_l 0).
  rewrite map_polyn_list_convol_mul_0_r.
  now do 2 rewrite norm_polyn_list_repeat_0.
}
destruct lb as [| b]. {
  rewrite (map_polyn_list_convol_mul_0_l 0).
  rewrite (map_polyn_list_convol_mul_0_r 0).
  rewrite map_polyn_list_convol_mul_0_r.
  rewrite map_polyn_list_convol_mul_0_r.
  now do 2 rewrite norm_polyn_list_repeat_0.
}
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
move lb' before la'; move lc' before lb'.
remember (length la' + length lb' + length lc' - 2) as len eqn:Hlen.
replace (length lc' + (length la' + length lb' - 1) - 1) with len. 2: {
  subst la' lb' lc'; cbn in Hlen |-*; flia Hlen.
}
replace (length la' + (length lb' + length lc' - 1) - 1) with len. 2: {
  subst la' lb' lc'; cbn in Hlen |-*; flia Hlen.
}
apply list_nth_polyn_list_eq; intros k.
remember
  (map (polyn_list_convol_mul la' lb') (seq 0 (length la' + length lb' - 1)))
  as ld eqn:Hld.
remember
  (map (polyn_list_convol_mul lb' lc') (seq 0 (length lb' + length lc' - 1)))
  as le eqn:Hle.
symmetry in Hld, Hle.
move le before ld.
destruct ld as [| d]. {
  apply map_eq_nil in Hld.
  apply List_seq_eq_nil in Hld.
  rewrite Hla', Hlb' in Hld; cbn in Hld.
  flia Hld.
}
destruct le as [| e]. {
  apply map_eq_nil in Hle.
  apply List_seq_eq_nil in Hle.
  rewrite Hlc', Hlb' in Hle; cbn in Hle.
  flia Hle.
}
destruct (lt_dec k len) as [Hklen| Hklen]. {
  rewrite (List_map_nth_in _ 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth_in _ 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  unfold polyn_list_convol_mul.
  rewrite <- Hld, <- Hle.
  rewrite srng_summation_mul_polyn_list_nth_map_list_convol_mul_2; symmetry.
  rewrite srng_summation_mul_polyn_list_nth_map_list_convol_mul; symmetry.
...
rewrite <- srng_summation_summation_mul_swap.
rewrite <- srng_summation_summation_mul_swap.
...
rewrite <- summation_summation_mul_swap.
rewrite <- summation_summation_mul_swap.
rewrite summation_summation_exch.
rewrite summation_summation_shift.
apply summation_compat; intros i Hi.
apply summation_compat; intros j Hj.
rewrite rng_mul_comm, rng_mul_assoc.
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.sub_add_distr.
reflexivity.
Qed.
...
intros la lb lc.
unfold polyn_list_mul.
do 2 rewrite map_length.
do 2 rewrite seq_length.
destruct (Nat.eq_dec (length lb) 0) as [Hbz| Hbz]. {
  rewrite Hbz; cbn; rewrite Nat.add_0_r.
  apply length_zero_iff_nil in Hbz; subst lb.
  rewrite (map_polyn_list_convol_mul_0_l 0).
  rewrite (map_polyn_list_convol_mul_0_r 0).
  do 2 rewrite seq_length.
  rewrite map_polyn_list_convol_mul_0_l.
  rewrite map_polyn_list_convol_mul_0_r.
  now do 2 rewrite norm_polyn_list_repeat_0.
}
remember (length la + length lb + length lc - 2) as len eqn:Hlen.
replace (length la + (length lb + length lc - 1) - 1) with len
  by flia Hlen Hbz.
replace (length la + length lb - 1 + length lc - 1) with len
  by flia Hlen Hbz.
clear Hlen.
revert la lb lc Hbz.
induction len; intros; [ easy | ].
cbn - [ norm_polyn_list polyn_list_convol_mul ].
Check polyn_list_convol_mul_more.
Search polyn_list_convol_mul.
...
Check norm_polyn_list_mul_idemp_l.
...
Print norm_polyn_list.
Search (norm_polyn_list (_ ++ _)).
Search (norm_polyn_list (_ :: _)).
cbn.
...
rewrite (polyn_list_convol_mul_more (lab + lbc)); [ | subst; flia ].
symmetry.
...
rewrite Heqlabc.
remember (lb + lc)%PL as lbc.
symmetry in Heqlbc.
rewrite <- Heqlbc in Heqlabc |-*.
rewrite (polyn_list_convol_mul_more (lab + lac)); [ | subst; flia ].
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite <- norm_polyn_list_add_idemp_l.
rewrite (polyn_list_convol_mul_more (labc + lac)); [ | flia ].
rewrite <- Heqlab.
rewrite norm_polyn_list_add_idemp_l.
rewrite polyn_list_add_comm.
rewrite <- norm_polyn_list_add_idemp_l.
rewrite Heqlac.
rewrite (polyn_list_convol_mul_more (labc + lab)); [ | flia ].
rewrite norm_polyn_list_add_idemp_l.
rewrite <- Heqlac.
rewrite Nat.add_comm.
rewrite polyn_list_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite map_polyn_list_convol_mul_add.
now rewrite map_polyn_list_add_convol_mul.
Qed.
*)

Theorem polyn_mul_assoc : ∀ P Q R, (P * (Q * R))%P = (P * Q * R)%P.
Proof.
intros (la, Pa) (lb, Pb) (lc, Pc).
apply polyn_eq.
cbn - [ polyn_list_mul ].
rewrite norm_polyn_list_mul_idemp_l.
rewrite norm_polyn_list_mul_idemp_r.
...
apply norm_polyn_list_mul_assoc.
Qed.

...

Definition polyn_semiring_prop : semiring_prop (polynomial T) :=
  {| srng_add_comm := polyn_add_comm;
     srng_add_assoc := polyn_add_assoc;
     srng_add_0_l := polyn_add_0_l;
     srng_mul_comm := polyn_mul_comm;
     srng_mul_assoc := polyn_mul_assoc;
     srng_mul_1_l := polyn_mul_1_l;
     srng_mul_add_distr_l := polyn_mul_add_distr_l;
     srng_mul_0_l := polyn_mul_0_l |}.

Theorem polyn_add_opp_l : ∀ P : polynomial T, (- P + P)%P = 0%P.
Proof.
intros.
apply polyn_eq; cbn.
destruct P as (la, Hla); cbn.
apply List_eq_rev_r; cbn.
apply eq_strip_0s_nil.
apply List_eq_rev_r; cbn.
rewrite List_rev_repeat.
rewrite rev_length.
clear Hla.
induction la as [| a]; [ easy | cbn ].
unfold so.
now rewrite rng_add_opp_l; f_equal.
Qed.

Theorem polyn_add_opp_r : ∀ P : polynomial T, (P - P)%P = 0%P.
Proof.
intros.
unfold polyn_sub.
rewrite polyn_add_comm.
apply polyn_add_opp_l.
Qed.

Definition polyn_ring_prop : ring_prop (polynomial T) :=
  {| rng_add_opp_l := polyn_add_opp_l |}.

Theorem polyn_eq_dec : ∀ P Q : polynomial T, {P = Q} + {P ≠ Q}.
Proof.
intros.
destruct P as (la, Hla).
destruct Q as (lb, Hlb).
enough (H : {la = lb} + {la ≠ lb}). {
  destruct H as [H| H]. {
    subst la; left.
    now apply polyn_eq; cbn.
  } {
    right.
    intros H'; apply H; clear H.
    now injection H'.
  }
}
clear Hla Hlb.
apply list_eq_dec, sdp.
Qed.

Theorem polyn_1_neq_0 : 1%P ≠ 0%P.
Proof.
unfold polyn_of_list; cbn.
intros H.
injection H; clear H; intros.
now rewrite if_1_eq_0 in H.
Qed.

Definition polyn_sring_dec_prop : @sring_dec_prop _ polyn_semiring_op :=
  {| srng_eq_dec := polyn_eq_dec;
     srng_1_neq_0 := polyn_1_neq_0 |}.

Canonical Structure polyn_semiring_op.
Canonical Structure polyn_ring_op.
Canonical Structure polyn_semiring_prop.
Canonical Structure polyn_ring_prop.
Canonical Structure polyn_sring_dec_prop.

End in_ring.

Module polynomial_Notations.

Declare Scope polynomial_scope.
Delimit Scope polynomial_scope with P.

Notation "0" := (polyn_of_list []) : polynomial_scope.
Notation "1" := (polyn_of_list [1%Srng]) : polynomial_scope.
Notation "P + Q" := (polyn_add P Q) : polynomial_scope.
Notation "P - Q" := (polyn_sub P Q) : polynomial_scope.
Notation "P * Q" := (polyn_mul P Q) : polynomial_scope.
Notation "- P" := (polyn_opp P) : polynomial_scope.

Declare Scope polyn_list_scope.
Delimit Scope polyn_list_scope with PL.

(*
Notation "0" := ([]) : polyn_list_scope.
*)
Notation "1" := ([1%Srng]) : polyn_list_scope.
Notation "la + lb" := (polyn_list_add la lb) : polyn_list_scope.
Notation "la * lb" := (polyn_list_mul la lb) : polyn_list_scope.

Notation "'Σ' ( i = b , e ) , g" :=
  (iterate b e (λ c i, (c + g)%P) 0%P)
  (at level 45, i at level 0, b at level 60, e at level 60) :
     polynomial_scope.

Arguments norm_polyn_list {T ro sdp} l%PL.
Arguments polyn_coeff {T so sdp} P%P i%nat.
Arguments polyn_degree {T so sdp} P%P.
Arguments polyn_list_convol_mul {T ro} la%PL lb%PL _%nat.
Arguments polyn_list {T so sdp} p%P.

End polynomial_Notations.
