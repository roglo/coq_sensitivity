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

(* could be a theorem, perhaps...
Definition eval_polyn T {so : semiring_op T} {sdp : sring_dec_prop}
    (P : polynomial T) x :=
  match polyn_degree_plus_1 P with
  | 0 => 0%Srng
  | S n => (Σ (i = 0, n), polyn_coeff P i * x ^ i)%Srng
  end.
*)

Definition eval_polyn_list T {so : semiring_op T} (la : list T) x :=
  fold_right (λ a acc, (acc * x + a)%Srng) 0%Srng la.

Definition eval_polyn T {so : semiring_op T} {sdp : sring_dec_prop}
    (P : polynomial T) :=
  eval_polyn_list (polyn_list P).

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

Theorem fold_eval_polyn_list : ∀ la (x : T),
  fold_right (λ a acc, (acc * x + a)%Srng) 0%Srng la = eval_polyn_list la x.
Proof. easy. Qed.

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

Notation "'Σ' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c + g)%P) 0%P)
  (at level 45, i at level 0, b at level 60, e at level 60) :
     polynomial_scope.

Notation "'Π' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c * g)%P) 1%P)
  (at level 45, i at level 0, b at level 60, e at level 60) :
     polynomial_scope.

Arguments norm_polyn_list l%PL.
Arguments polyn_coeff {T so sdp} P%P i%nat.
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
  length (la + lb)%PL = max (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal; apply IHla.
Qed.

Theorem polyn_list_mul_length : ∀ la lb,
  length (la * lb)%PL = length la + length lb - 1.
Proof.
intros.
unfold polyn_list_mul; cbn.
now rewrite map_length, seq_length.
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

Theorem polyn_mul_add_distr_r : ∀ P Q R, ((P + Q) * R = P * R + Q * R)%P.
Proof.
intros.
rewrite polyn_mul_comm.
rewrite polyn_mul_add_distr_l.
now do 2 rewrite (polyn_mul_comm R).
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
  cbn - [ iter_seq sub ].
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
cbn; do 2 rewrite srng_add_0_l.
destruct (zerop (b2 + g1 (b1 + len))) as [Hz| Hz]. {
  apply Nat.eq_add_0 in Hz.
  destruct Hz as (Hbz, Hgz).
  subst b2; rewrite Hgz.
  cbn; symmetry.
  apply srng_mul_0_r.
}
rewrite fold_iter_seq_2; [ | easy ].
rewrite fold_iter_seq_2; [ | easy ].
symmetry.
apply srng_mul_summation_distr_l.
Qed.

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
  rewrite <- srng_summation_summation_mul_swap.
  rewrite <- srng_summation_summation_mul_swap.
  rewrite srng_summation_summation_exch.
  rewrite srng_summation_summation_shift.
  apply srng_summation_eq_compat; intros i Hi.
  apply srng_summation_eq_compat; intros j Hj.
  rewrite srng_mul_comm, srng_mul_assoc.
  rewrite Nat.add_comm, Nat.add_sub.
  now rewrite Nat.add_comm, Nat.sub_add_distr.
}
apply Nat.nlt_ge in Hklen.
rewrite nth_overflow; [ | now rewrite map_length, seq_length ].
rewrite nth_overflow; [ | now rewrite map_length, seq_length ].
easy.
Qed.

Theorem polyn_mul_assoc : ∀ P Q R, (P * (Q * R))%P = (P * Q * R)%P.
Proof.
intros (la, Pa) (lb, Pb) (lc, Pc).
apply polyn_eq.
cbn - [ polyn_list_mul ].
rewrite norm_polyn_list_mul_idemp_l.
rewrite norm_polyn_list_mul_idemp_r.
apply norm_polyn_list_mul_assoc.
Qed.

Definition polyn_semiring_prop : semiring_prop (polynomial T) :=
  {| srng_add_comm := polyn_add_comm;
     srng_add_assoc := polyn_add_assoc;
     srng_add_0_l := polyn_add_0_l;
     srng_mul_comm := polyn_mul_comm;
     srng_mul_assoc := polyn_mul_assoc;
     srng_mul_1_l := polyn_mul_1_l;
     srng_mul_add_distr_l := polyn_mul_add_distr_l;
     srng_mul_0_l := polyn_mul_0_l |}.

Existing Instance polyn_semiring_prop.

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

Existing Instance polyn_ring_prop.

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

(* monic polynomial: polynomial whose leading coefficient is 1 *)

Definition is_monic_polyn (P : polynomial T) :=
  polyn_coeff P (polyn_degree P) = 1%Srng.

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
  rewrite if_1_eq_0; cbn.
  now rewrite if_1_eq_0.
}
destruct la; [ | cbn in Ha; flia Ha ].
cbn in Hla.
unfold is_monic_polyn; cbn.
rewrite if_1_eq_0; cbn.
now rewrite if_1_eq_0.
Qed.

(* *)

Theorem norm_polyn_list_app_last_nz : ∀ (la lb : list T),
  last (la ++ lb) 0%Srng ≠ 0%Srng
  → norm_polyn_list (la ++ lb) = la ++ norm_polyn_list lb.
Proof.
intros * Hlb.
revert lb Hlb.
induction la as [| a]; intros; [ easy | ].
cbn - [ norm_polyn_list ].
rewrite List_cons_app.
rewrite norm_polyn_list_app.
remember (la ++ lb) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]. cbn. {
  apply app_eq_nil in Hlc.
  destruct Hlc; subst la lb.
  cbn in Hlb |-*.
  now destruct (srng_eq_dec a 0).
}
rewrite <- Hlc.
rewrite IHla. 2: {
  cbn in Hlb.
  rewrite Hlc in Hlb.
  now rewrite <- Hlc in Hlb.
}
destruct lb as [| b]. {
  cbn in Hlb.
  rewrite Hlc in Hlb.
  rewrite app_nil_r in Hlc.
  now rewrite Hlc.
}
destruct la as [| a1]; [ | easy ].
cbn in Hlc.
cbn - [ norm_polyn_list ].
remember (norm_polyn_list (b :: lb)) as ld eqn:Hld.
symmetry in Hld.
destruct ld as [| d]; [ | easy ].
exfalso; apply Hlb; clear Hlb.
clear IHla Hlc.
revert b Hld.
induction lb as [| b1]; intros. {
  cbn in Hld.
  now destruct (srng_eq_dec b 0).
}
cbn - [ last ].
rewrite List_last_cons_cons.
apply IHlb.
cbn in Hld |-*.
apply List_eq_rev_l in Hld.
apply List_eq_rev_r.
rewrite strip_0s_app in Hld.
remember (strip_0s (rev lb ++ [b1])) as le eqn:Hle.
symmetry in Hle.
now destruct le.
Qed.

Theorem norm_polyn_list_id : ∀ (la : list T),
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

Theorem norm_polyn_list_cons : ∀ (a : T) la,
  last (a :: la) 0%Srng ≠ 0%Srng
  → norm_polyn_list (a :: la) = a :: norm_polyn_list la.
Proof.
intros * Hla.
now specialize (norm_polyn_list_app_last_nz [a] la Hla) as H.
Qed.

Theorem polyn_degree_lt_add : ∀ P Q,
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
rewrite List_last_cons_cons.
clear - so Haz Hdeg.
revert lb a1 b1 Haz Hdeg.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
remember (a :: la) as x; cbn in Haz; subst x.
cbn in Hdeg.
apply Nat.succ_lt_mono in Hdeg.
now apply IHla.
Qed.

(* normalized list is smaller than the list *)

Theorem norm_polyn_list_length_le : ∀ la,
  length (norm_polyn_list la) ≤ length la.
Proof.
intros.
induction la as [| a] using rev_ind; [ easy | ].
rewrite norm_polyn_list_app, app_length; cbn.
destruct (srng_eq_dec a 0%Srng) as [Hz| Hz]. {
  cbn; flia IHla.
}
cbn.
now rewrite app_length.
Qed.

(* degree of sum and summation upper bound *)

Theorem polyn_degree_add_ub : ∀ P Q,
  polyn_degree (P + Q) ≤ max (polyn_degree P) (polyn_degree Q).
Proof.
intros (la, Hla) (lb, Hlb).
move lb before la.
cbn - [ "+"%PL ].
rewrite Nat.sub_max_distr_r.
apply Nat.sub_le_mono_r.
destruct la as [| a]. {
  clear Hla.
  rewrite Nat.max_r; [ | cbn; flia ].
  rewrite polyn_list_add_0_l.
  destruct lb as [| b]; [ easy | ].
  cbn - [ nth ] in Hlb.
  destruct (srng_eq_dec (nth (length lb) (b :: lb) 0%Srng) 0)
    as [| H]; [ easy | clear Hlb ].
  rewrite <- List_last_nth_cons in H.
  rewrite norm_polyn_list_cons; [ cbn | easy ].
  apply -> Nat.succ_le_mono.
  apply norm_polyn_list_length_le.
}
cbn - [ nth ] in Hla.
destruct (srng_eq_dec (nth (length la) (a :: la) 0%Srng) 0)
  as [Haz| Haz]; [ easy | clear Hla ].
rewrite <- List_last_nth_cons in Haz.
destruct lb as [| b]. {
  cbn - [ norm_polyn_list ].
  clear Hlb.
  revert a Haz.
  induction la as [| a1]; intros. {
    cbn in Haz |-*.
    now destruct (srng_eq_dec a 0).
  }
  rewrite List_last_cons_cons in Haz.
  rewrite norm_polyn_list_cons; [ | easy ].
  remember (a1 :: la) as lc; cbn; subst lc.
  apply -> Nat.succ_le_mono.
  now apply IHla.
}
cbn - [ nth ] in Hlb.
destruct (srng_eq_dec (nth (length lb) (b :: lb) 0%Srng) 0)
  as [Hbz| Hbz]; [ easy | clear Hlb ].
rewrite <- List_last_nth_cons in Hbz.
move b before a.
revert a b lb Haz Hbz.
induction la as [| a1]; intros. {
  cbn in Haz.
  cbn - [ norm_polyn_list ].
  remember (a + b)%Srng as c; clear Heqc.
  revert b c Hbz.
  induction lb as [| b1]; intros. {
    cbn in Hbz |-*.
    destruct (srng_eq_dec c 0); cbn; flia.
  }
  rewrite norm_polyn_list_cons; [ | easy ].
  rewrite List_last_cons_cons in Hbz.
  remember (b1 :: lb) as lc; cbn; subst lc.
  apply -> Nat.succ_le_mono.
  now apply (IHlb b1).
}
rewrite List_last_cons_cons in Haz.
remember (a1 :: la) as lc.
cbn - [ norm_polyn_list ].
subst lc.
destruct lb as [| b1]. {
  rewrite polyn_list_add_0_r.
  cbn in Hbz.
  rewrite norm_polyn_list_cons; [ | easy ].
  cbn - [ norm_polyn_list ] in IHla |-*.
  apply -> Nat.succ_le_mono.
  clear IHla.
  revert a1 Haz.
  induction la as [| a2]; intros. {
    cbn.
    now destruct (srng_eq_dec a1 0).
  }
  rewrite List_last_cons_cons in Haz.
  rewrite norm_polyn_list_cons; [ | easy ].
  cbn - [ norm_polyn_list ].
  apply -> Nat.succ_le_mono.
  now apply IHla.
}
rewrite List_last_cons_cons in Hbz.
specialize (IHla _ _ _ Haz Hbz).
apply Nat.succ_le_mono in IHla.
etransitivity; [ | apply IHla ].
remember ((a1 :: la) + (b1 :: lb))%PL as lc eqn:Hlc.
remember (a + b)%Srng as c; clear a b Heqc.
clear.
revert c.
induction lc as [| c1] using rev_ind; intros. {
  cbn.
  now destruct (srng_eq_dec c 0); cbn; flia.
}
destruct (srng_eq_dec c1 0) as [Hz| Hz]. {
  subst c1.
  rewrite app_comm_cons.
  do 2 rewrite norm_polyn_list_app.
  cbn - [ norm_polyn_list ].
  unfold norm_polyn_list at 1 3.
  cbn - [ norm_polyn_list ].
  unfold so.
  rewrite if_0_eq_0.
  cbn - [ norm_polyn_list ].
  apply IHlc.
}
rewrite app_comm_cons.
do 2 rewrite norm_polyn_list_app.
cbn - [ norm_polyn_list ].
unfold norm_polyn_list at 1 3.
cbn - [ norm_polyn_list ].
unfold so.
now destruct (srng_eq_dec c1 0).
Qed.

(* highest coefficient *)

Definition polyn_highest_coeff P :=
  polyn_coeff P (polyn_degree P).

Theorem polyn_highest_coeff_neq_0 : ∀ (P : polynomial T),
  polyn_degree P ≠ 0
  → polyn_highest_coeff P ≠ 0%Srng.
Proof.
intros (la, Hla) Hd.
cbn in Hla, Hd |-*.
destruct la as [| a] using rev_ind; [ easy | clear IHla ].
rewrite <- List_last_nth, List_last_app.
rewrite app_length, Nat.add_comm in Hla.
cbn in Hla.
rewrite app_nth2 in Hla; [ | now unfold ge ].
rewrite Nat.sub_diag in Hla; cbn in Hla.
now destruct (srng_eq_dec a 0).
Qed.

Theorem polyn_degree_add_not_cancel : ∀ P Q,
  polyn_degree P = polyn_degree Q
  → (polyn_highest_coeff P + polyn_highest_coeff Q ≠ 0)%Srng
  → polyn_degree (P + Q) = polyn_degree P.
Proof.
intros (la, Hla) (lb, Hlb) HPQ HCPQ.
move lb before la.
cbn - [ norm_polyn_list ] in *.
destruct la as [| a] using rev_ind. {
  cbn in HPQ, HCPQ |-*.
  rewrite rev_length.
  destruct lb as [| b]; [ easy | cbn ].
  cbn in HPQ; rewrite Nat.sub_0_r in HPQ.
  symmetry in HPQ.
  apply length_zero_iff_nil in HPQ; subst lb.
  cbn in Hlb, HCPQ |-*.
  now destruct (srng_eq_dec b 0).
}
clear IHla.
rewrite app_length in Hla, HCPQ, HPQ.
rewrite Nat.add_1_r in Hla; cbn in Hla.
rewrite Nat.add_sub in HPQ, HCPQ.
rewrite app_nth2 in Hla; [ | now unfold ge ].
rewrite app_nth2 in HCPQ; [ | now unfold ge ].
rewrite Nat.sub_diag in Hla; cbn in Hla.
rewrite Nat.sub_diag in HCPQ; cbn in HCPQ.
destruct lb as [| b] using rev_ind. {
  apply length_zero_iff_nil in HPQ; subst la; cbn.
  now destruct (srng_eq_dec a 0).
}
clear IHlb.
move b before a.
rewrite app_length in Hlb, HCPQ, HPQ.
rewrite Nat.add_1_r in Hlb; cbn in Hlb.
rewrite Nat.add_sub in HPQ, HCPQ.
rewrite app_nth2 in Hlb; [ | now unfold ge ].
rewrite app_nth2 in HCPQ; [ | now unfold ge ].
rewrite Nat.sub_diag in Hlb; cbn in Hlb.
rewrite Nat.sub_diag in HCPQ; cbn in HCPQ.
rewrite app_length, Nat.add_sub.
rewrite polyn_list_add_app_l.
rewrite firstn_app, HPQ, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
rewrite skipn_app, skipn_all, app_nil_l, Nat.sub_diag, skipn_O; cbn.
rewrite norm_polyn_list_app; cbn.
destruct (srng_eq_dec (a + b) 0) as [H| H]; [ easy | clear H; cbn ].
rewrite app_length, Nat.add_sub.
rewrite polyn_list_add_length, max_r; [ easy | ].
now rewrite HPQ.
Qed.

Theorem polyn_degree_add_compat : ∀ Pa Pb Qa Qb,
  polyn_degree Pa = polyn_degree Pb
  → polyn_degree Qa = polyn_degree Qb
  → (polyn_highest_coeff Pa + polyn_highest_coeff Qa)%Srng ≠ 0%Srng
  → (polyn_highest_coeff Pb + polyn_highest_coeff Qb)%Srng ≠ 0%Srng
  → polyn_degree (Pa + Qa) = polyn_degree (Pb + Qb).
Proof.
intros * HP HQ Hha Hhb.
destruct (lt_dec (polyn_degree Pa) (polyn_degree Qa)) as [HPQ| HPQ]. {
  rewrite polyn_add_comm.
  rewrite polyn_degree_lt_add; [ | easy ].
  rewrite polyn_add_comm.
  rewrite polyn_degree_lt_add; [ easy | ].
  now rewrite <- HP, <- HQ.
}
apply Nat.nlt_ge in HPQ.
destruct (lt_dec (polyn_degree Qa) (polyn_degree Pa)) as [HQP| HQP]. {
  rewrite polyn_degree_lt_add; [ | easy ].
  rewrite polyn_degree_lt_add; [ easy | ].
  now rewrite <- HP, <- HQ.
}
apply Nat.nlt_ge in HQP.
apply Nat.le_antisymm in HPQ; [ clear HQP | easy ].
rewrite polyn_degree_add_not_cancel; [ | easy | easy ].
rewrite polyn_degree_add_not_cancel; [ | congruence | easy ].
congruence.
Qed.

Theorem polyn_degree_add_le_compat : ∀ P P' Q Q',
  polyn_degree P ≤ polyn_degree P'
  → polyn_degree Q ≤ polyn_degree Q'
  → (polyn_highest_coeff P' + polyn_highest_coeff Q')%Srng ≠ 0%Srng
  → polyn_degree (P + Q) ≤ polyn_degree (P' + Q').
Proof.
intros * HP HQ Hhb.
destruct (lt_dec (polyn_degree P) (polyn_degree Q)) as [HPQ| HPQ]. {
  rewrite polyn_add_comm.
  rewrite polyn_degree_lt_add; [ | easy ].
  rewrite polyn_add_comm.
  destruct (lt_dec (polyn_degree Q') (polyn_degree P')) as [HQP| HQP]. {
    rewrite polyn_add_comm, polyn_degree_lt_add; [ | easy ].
    etransitivity; [ apply HQ | ].
    now apply Nat.lt_le_incl.
  }
  apply Nat.nlt_ge in HQP.
  destruct (lt_dec (polyn_degree P') (polyn_degree Q')) as [H| H]. {
    now rewrite polyn_degree_lt_add.
  }
  apply Nat.nlt_ge in H.
  apply Nat.le_antisymm in HQP; [ clear H | easy ].
  rewrite polyn_degree_add_not_cancel; [ | easy | now rewrite srng_add_comm ].
  easy.
}
apply Nat.nlt_ge in HPQ.
destruct (lt_dec (polyn_degree Q) (polyn_degree P)) as [HQP| HQP]. {
  rewrite polyn_degree_lt_add; [ | easy ].
  rewrite polyn_add_comm.
  destruct (lt_dec (polyn_degree Q') (polyn_degree P')) as [HQP'| HQP']. {
    now rewrite polyn_add_comm, polyn_degree_lt_add.
  }
  apply Nat.nlt_ge in HQP'.
  destruct (lt_dec (polyn_degree P') (polyn_degree Q')) as [H| H]. {
    rewrite polyn_degree_lt_add; [ | easy ].
    etransitivity; [ apply HP | easy ].
  }
  apply Nat.nlt_ge in H.
  apply Nat.le_antisymm in HQP'; [ clear H | easy ].
  rewrite polyn_degree_add_not_cancel; [ | easy | now rewrite srng_add_comm ].
  congruence.
}
apply Nat.nlt_ge in HQP.
apply Nat.le_antisymm in HPQ; [ clear HQP | easy ].
etransitivity; [ apply polyn_degree_add_ub | ].
rewrite max_l; [ | now rewrite HPQ ].
destruct (lt_dec (polyn_degree Q') (polyn_degree P')) as [HQP'| HQP']. {
  now rewrite polyn_degree_lt_add.
}
apply Nat.nlt_ge in HQP'.
destruct (lt_dec (polyn_degree P') (polyn_degree Q')) as [H| H]. {
  rewrite polyn_add_comm, polyn_degree_lt_add; [ | easy ].
  etransitivity; [ apply HP | easy ].
}
apply Nat.nlt_ge in H.
apply Nat.le_antisymm in HQP'; [ clear H | easy ].
now rewrite polyn_degree_add_not_cancel.
Qed.

(* *)

Theorem nth_norm_polyn_list_map : ∀ i len f,
  (∀ i, len ≤ i → f i = 0%Srng)
  → nth i (norm_polyn_list (map f (seq 0 len))) 0%Srng = f i.
Proof.
intros * Hf.
revert i.
induction len; intros. {
  cbn; rewrite match_id; symmetry.
  apply Hf, Nat.le_0_l.
}
rewrite List_seq_succ_r.
rewrite map_app.
rewrite norm_polyn_list_app.
cbn - [ norm_polyn_list ].
unfold norm_polyn_list at 1.
cbn - [ norm_polyn_list ].
destruct (srng_eq_dec (f len) 0) as [Hfz| Hfz]. {
  cbn - [ norm_polyn_list ].
  apply IHlen.
  intros j Hj.
  destruct (Nat.eq_dec j len) as [Hjlen| Hjlen]. {
    now rewrite Hjlen.
  }
  apply Hf.
  flia Hj Hjlen.
}
cbn.
destruct (lt_dec i len) as [Hilen| Hilen]. {
  rewrite app_nth1; [ | now rewrite map_length, seq_length ].
  rewrite (List_map_nth_in _ 0); [ | now rewrite seq_length ].
  now rewrite seq_nth.
}
apply Nat.nlt_ge in Hilen.
rewrite app_nth2; [ | now rewrite map_length, seq_length ].
rewrite map_length, seq_length.
destruct (Nat.eq_dec i len) as [Hiel| Hiel]. {
  now rewrite Hiel, Nat.sub_diag.
}
rewrite nth_overflow; [ | cbn; flia Hilen Hiel ].
symmetry.
apply Hf.
flia Hilen Hiel.
Qed.

Theorem polyn_coeff_overflow : ∀ P n,
  polyn_degree P < n
  → polyn_coeff P n = 0%Srng.
Proof.
intros (la, Hla) n Hpn.
cbn in Hpn |-*.
rewrite nth_overflow; [ easy | flia Hpn ].
Qed.

(*
Theorem nth_polyn_list_mul : ∀ la lb i,
  nth i (la * lb)%PL 0%Srng = polyn_list_convol_mul la lb i.
Proof.
...
Theorem nth_polyn_list_mul : ∀ la lb i,
  nth i (la * lb)%PL 0%Srng = (Σ (j = 0, i), nth j la 0 * nth (i - j) lb 0)%Srng.
Proof.
intros.
Print polyn_list_convol_mul.
remember (length la + length lb - 1) as len eqn:Hlen.
destruct (lt_dec i len) as [Hilen| Hilen]. 2: {
  apply Nat.nlt_ge in Hilen.
  rewrite nth_overflow. 2: {
    unfold polyn_list_mul.
    now rewrite map_length, seq_length, <- Hlen.
  }
  symmetry.
  apply all_0_srng_summation_0.
  intros j Hj.
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. 2: {
    apply Nat.nlt_ge in Hjla.
    rewrite nth_overflow; [ | easy ].
    apply srng_mul_0_l.
  }
  destruct (lt_dec (i - j) (length lb)) as [Hjlb| Hjlb]. 2: {
    apply Nat.nlt_ge in Hjlb.
    rewrite (nth_overflow lb); [ | easy ].
    apply srng_mul_0_r.
  }
  flia Hlen Hilen Hj Hjla Hjlb.
}
unfold polyn_list_mul.
rewrite Hlen in Hilen.
rewrite (List_map_nth_in _ 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
now rewrite Nat.add_0_l.
Qed.
*)

Theorem polyn_coeff_mul : ∀ P Q i,
  polyn_coeff (P * Q)%P i =
    (Σ (j = 0, i), polyn_coeff P j * polyn_coeff Q (i - j))%Srng.
Proof.
(*
intros.
unfold polyn_coeff.
cbn - [ iter_seq norm_polyn_list ].
remember (polyn_list P) as la.
remember (polyn_list Q) as lb.
Search (polyn_list (polyn_of_list _)).
unfold polyn_of_list.
...
cbn - [ iter_seq polyn_list_mul ].
destruct P as (la, Hla).
destruct Q as (lb, Hlb).
cbn - [ iter_seq polyn_list_mul ].
...
*)
intros.
cbn - [ iter_seq ].
destruct P as (la, Hla).
destruct Q as (lb, Hlb).
cbn - [ iter_seq norm_polyn_list ].
unfold polyn_list_convol_mul.
remember (length la + length lb - 1) as len eqn:Hlen.
destruct (lt_dec i len) as [Hilen| Hilen]. 2: {
  apply Nat.nlt_ge in Hilen.
  rewrite nth_overflow. 2: {
    etransitivity; [ apply norm_polyn_list_length_le | ].
    now rewrite map_length, seq_length.
  }
  symmetry.
  apply all_0_srng_summation_0.
  intros j Hj.
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. 2: {
    apply Nat.nlt_ge in Hjla.
    rewrite nth_overflow; [ | easy ].
    apply srng_mul_0_l.
  }
  destruct (lt_dec (i - j) (length lb)) as [Hjlb| Hjlb]. 2: {
    apply Nat.nlt_ge in Hjlb.
    rewrite (nth_overflow lb); [ | easy ].
    apply srng_mul_0_r.
  }
  flia Hlen Hilen Hj Hjla Hjlb.
}
rewrite nth_norm_polyn_list_map; [ easy | ].
intros j Hj.
apply all_0_srng_summation_0.
intros k Hk.
destruct (lt_dec k (length la)) as [Hka| Hka]. 2: {
  apply Nat.nlt_ge in Hka.
  rewrite nth_overflow; [ | easy ].
  apply srng_mul_0_l.
}
destruct (lt_dec (j - k) (length lb)) as [Hjkb| Hjkb]. 2: {
  apply Nat.nlt_ge in Hjkb.
  rewrite (nth_overflow lb); [ | easy ].
  apply srng_mul_0_r.
}
flia Hlen Hj Hka Hjkb.
Qed.

(* degree of monomial "x" *)

Theorem polyn_degree_monom : polyn_degree _x = 1.
Proof.
now cbn; rewrite if_1_eq_0.
Qed.

Theorem polyn_degree_summation_ub : ∀ b e f,
  polyn_degree (Σ (i = b, e), f i) ≤ Max (i = b, e), polyn_degree (f i).
Proof.
intros.
unfold iter_seq.
remember (S e - b) as len eqn:Hlen.
clear e Hlen.
revert b.
induction len; intros; [ cbn; flia | ].
cbn; rewrite polyn_add_0_l.
rewrite fold_left_srng_add_fun_from_0.
rewrite fold_left_max_fun_from_0.
cbn - [ polyn_degree ].
rewrite polyn_add_comm.
etransitivity; [ apply polyn_degree_add_ub | ].
rewrite Nat.max_comm.
apply Nat.max_le_compat_l.
apply IHlen.
Qed.

Theorem polyn_coeff_opp : ∀ P i,
  polyn_coeff (- P) i = (- polyn_coeff P i)%Rng.
Proof.
intros (la, Hla) *; cbn.
unfold polyn_coeff.
destruct (lt_dec i (length la)) as [Hila| Hila]. {
  now rewrite (List_map_nth_in _ 0%Rng).
}
apply Nat.nlt_ge in Hila.
rewrite nth_overflow; [ | now rewrite map_length ].
rewrite nth_overflow; [ | easy ].
symmetry.
apply rng_opp_0.
Qed.

Theorem is_monic_polyn_add : ∀ (P Q : polynomial T),
  polyn_degree Q < polyn_degree P
  → is_monic_polyn P
  → is_monic_polyn (P + Q).
Proof.
intros * Hdeg HP.
unfold is_monic_polyn in HP |-*.
rewrite polyn_degree_lt_add; [ | easy ].
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
rewrite List_last_cons_cons.
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

Theorem polyn_degree_mul : ∀ (P Q : polynomial T),
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
rewrite norm_polyn_list_id. 2: {
  destruct la as [| a]. {
    exfalso; apply HPQ; cbn.
    apply srng_mul_0_l.
  }
  destruct lb as [| b]. {
    exfalso; apply HPQ; cbn.
    apply srng_mul_0_r.
  }
  rewrite List_last_nth.
  cbn; rewrite map_length, seq_length, Nat.sub_0_r.
  rewrite Nat.add_succ_r, Nat.sub_succ, Nat.sub_0_r.
  rewrite (List_map_nth_in _ 0); [ | rewrite seq_length; flia ].
  rewrite seq_nth; [ | flia ].
  rewrite Nat.add_0_l.
  unfold polyn_list_convol_mul.
  destruct (zerop (length la)) as [Hzla| Hzla]. {
    rewrite Hzla, Nat.add_0_l.
    apply length_zero_iff_nil in Hzla; subst la.
    unfold so.
    rewrite srng_summation_split_first; [ | flia ].
    rewrite Nat.sub_0_r, <- List_hd_nth_0; unfold hd.
    rewrite <- List_last_nth_cons.
    rewrite all_0_srng_summation_0. 2: {
      intros i Hi.
      rewrite nth_overflow; [ | easy ].
      apply srng_mul_0_l.
    }
    now rewrite srng_add_0_r.
  }
  unfold so.
  rewrite (srng_summation_split (length la - 1)); [ | flia ].
  rewrite all_0_srng_summation_0. 2: {
    intros i (_, Hi).
    rewrite (nth_overflow (b :: lb)); [ | cbn; flia Hi Hzla ].
    apply srng_mul_0_r.
  }
  rewrite srng_add_0_l.
  rewrite Nat.sub_add; [ | easy ].
  rewrite srng_summation_split_first; [ | flia ].
  rewrite Nat.add_comm, Nat.add_sub.
  do 2 rewrite <- List_last_nth_cons.
  rewrite all_0_srng_summation_0. 2: {
    intros i Hi.
    rewrite nth_overflow; [ | easy ].
    apply srng_mul_0_l.
  }
  now rewrite srng_add_0_r.
}
unfold "*"%PL.
rewrite map_length, seq_length.
destruct (zerop (length la)) as [Hzla| Hzla]. {
  exfalso; apply HPQ.
  apply length_zero_iff_nil in Hzla; subst la; cbn.
  apply srng_mul_0_l.
}
destruct (zerop (length lb)) as [Hzlb| Hzlb]. {
  exfalso; apply HPQ.
  apply length_zero_iff_nil in Hzlb; subst lb; cbn.
  apply srng_mul_0_r.
}
flia Hzla Hzlb.
Qed.

Theorem polyn_degree_mul_le : ∀ P Q,
  polyn_degree (P * Q) ≤ polyn_degree P + polyn_degree Q.
Proof.
intros.
destruct
  (srng_eq_dec
     (polyn_coeff P (polyn_degree P) * polyn_coeff Q (polyn_degree Q)) 0)
  as [Hzz| Hzz]. 2: {
  now rewrite polyn_degree_mul.
}
unfold polyn_degree; cbn.
unfold polyn_degree_plus_1.
destruct P as (la, Hla).
destruct Q as (lb, Hlb).
move lb before la.
cbn - [ norm_polyn_list polyn_list_mul ].
cbn in Hzz.
do 2 rewrite <- List_last_nth in Hzz.
unfold "*"%PL.
destruct la as [| a]. {
  clear Hla.
  unfold polyn_list_convol_mul.
  rewrite (proj1 (all_0_norm_polyn_list_map_0 _ _)); [ cbn; flia | ].
  intros i Hi; cbn in Hi.
  apply all_0_srng_summation_0.
  intros j Hj.
  destruct j; cbn; apply srng_mul_0_l.
}
cbn - [ nth ] in Hla.
rewrite <- List_last_nth_cons in Hla.
destruct (srng_eq_dec (last (a :: la) 0%Srng) 0) as [Haz| Haz]; [ easy | ].
clear Hla.
cbn - [ norm_polyn_list ].
do 2 rewrite Nat.sub_0_r.
destruct lb as [| b]. {
  clear Hlb.
  unfold polyn_list_convol_mul.
  rewrite (proj1 (all_0_norm_polyn_list_map_0 _ _)); [ cbn; flia | ].
  intros i Hi.
  apply all_0_srng_summation_0.
  intros j Hj.
  destruct (i - j); cbn; apply srng_mul_0_r.
}
cbn - [ nth ] in Hlb.
rewrite <- List_last_nth_cons in Hlb.
destruct (srng_eq_dec (last (b :: lb) 0%Srng) 0) as [Hbz| Hbz]; [ easy | ].
clear Hlb.
cbn - [ norm_polyn_list ].
rewrite Nat.sub_0_r.
rewrite Nat.add_succ_r.
cbn - [ norm_polyn_list ].
rewrite srng_add_0_l.
remember (_ :: _) as l in |-*.
destruct (srng_eq_dec (last l 0%Srng) 0) as [Hlab| Hlab]. 2: {
  subst l.
  rewrite norm_polyn_list_cons; [ | easy ].
  cbn; rewrite Nat.sub_0_r.
  remember (_ :: _) as l in Hlab.
  symmetry in Heql.
  destruct l as [| x]; [ easy | ].
  injection Heql; clear Heql; intros Hl Hab; subst x.
  rewrite Hl.
  destruct l as [| x]; [ cbn; flia | ].
  rewrite List_last_cons_cons in Hlab.
  rewrite norm_polyn_list_id; [ | easy ].
  rewrite <- Hl.
  now rewrite map_length, seq_length.
}
etransitivity; [ apply Nat.sub_le_mono_r, norm_polyn_list_length_le | ].
rewrite Heql; cbn.
rewrite map_length, seq_length.
now rewrite Nat.sub_0_r.
Qed.

Theorem polyn_coeff_mul_at_0 : ∀ P Q,
  polyn_coeff (P * Q) 0 = (polyn_coeff P 0 * polyn_coeff Q 0)%Srng.
Proof.
intros (la, Hla) (lb, Hlb).
move lb before la.
cbn - [ polyn_list_mul ].
destruct la as [| a]. {
  rewrite polyn_list_mul_0_l; cbn.
  symmetry.
  apply srng_mul_0_l.
}
cbn - [ nth ] in Hla.
rewrite <- List_last_nth_cons in Hla.
destruct (srng_eq_dec (last (a :: la) 0%Srng) 0) as [| Haz]; [ easy | ].
clear Hla.
cbn - [ norm_polyn_list polyn_list_mul ].
destruct lb as [| b]. {
  rewrite polyn_list_mul_0_r; cbn.
  symmetry.
  apply srng_mul_0_r.
}
cbn - [ nth ] in Hlb.
rewrite <- List_last_nth_cons in Hlb.
destruct (srng_eq_dec (last (b :: lb) 0%Srng) 0) as [| Hbz]; [ easy | ].
clear Hlb; cbn.
rewrite Nat.sub_0_r, Nat.add_succ_r; cbn.
rewrite srng_add_0_l.
rewrite strip_0s_app; cbn.
remember (strip_0s _) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]; [ now destruct (srng_eq_dec (a * b) 0) | ].
now cbn; rewrite rev_app_distr; cbn.
Qed.

Theorem polyn_of_list_0 : polyn_of_list [0%Rng] = 0%P.
Proof.
apply polyn_eq; cbn.
now destruct (srng_eq_dec 0 0).
Qed.

Theorem polyn_degree_1 : ∀ P,
  polyn_degree P = 0
  → polyn_degree (_x + P) = 1.
Proof.
intros (la, Hla) HP.
cbn - [ norm_polyn_list ] in HP |-*.
rewrite norm_polyn_list_add_idemp_l.
destruct la as [| a] using rev_ind; [ now cbn; rewrite if_1_eq_0 | ].
clear IHla.
destruct la as [| a1]. 2: {
  cbn in HP.
  rewrite app_length in HP; cbn in HP; flia HP.
}
clear HP; cbn.
now rewrite if_1_eq_0.
Qed.

Theorem polyn_degree_of_single : ∀ a, polyn_degree (polyn_of_list [a]) = 0.
Proof.
now intros; cbn; destruct (srng_eq_dec a 0).
Qed.

Theorem polyn_coeff_of_single : ∀ a, polyn_coeff (polyn_of_list [a]) 0 = a.
Proof.
now intros; cbn; destruct (srng_eq_dec a 0).
Qed.

Theorem polyn_of_list_repeat_0s : ∀ n,
  polyn_of_list (repeat 0%Rng n) = 0%P.
Proof.
intros.
apply polyn_eq; cbn.
induction n; [ easy | ].
rewrite List_repeat_succ_app.
rewrite norm_polyn_list_app; cbn.
now rewrite if_0_eq_0.
Qed.

Theorem polyn_coeff_add : ∀ P Q i,
  polyn_coeff (P + Q)%P i = (polyn_coeff P i + polyn_coeff Q i)%Srng.
Proof.
intros (la, Hla) (lb, Hlb) i.
move lb before la.
cbn - [ norm_polyn_list ].
unfold polyn_prop_test in Hla.
unfold polyn_prop_test in Hlb.
induction la as [| a] using rev_ind. {
  rewrite polyn_list_add_0_l.
  rewrite (nth_overflow []); [ | cbn; flia ].
  rewrite srng_add_0_l.
  revert i.
  induction lb as [| b] using rev_ind; intros; [ easy | ].
  rewrite app_length, Nat.add_comm in Hlb; cbn in Hlb.
  rewrite app_nth2 in Hlb; [ | now unfold ge ].
  rewrite Nat.sub_diag in Hlb; cbn in Hlb.
  rewrite norm_polyn_list_app; cbn.
  now destruct (srng_eq_dec b 0).
}
clear IHla.
rewrite app_length, Nat.add_comm in Hla; cbn in Hla.
rewrite app_nth2 in Hla; [ | now unfold ge ].
rewrite Nat.sub_diag in Hla; cbn in Hla.
destruct (srng_eq_dec a 0) as [Haz| Haz]; [ easy | clear Hla ].
induction lb as [| b] using rev_ind. {
  rewrite polyn_list_add_0_r.
  rewrite (nth_overflow []); [ | cbn; flia ].
  rewrite srng_add_0_r.
  rewrite norm_polyn_list_id; [ easy | now rewrite List_last_app ].
}
clear IHlb.
rewrite app_length, Nat.add_comm in Hlb; cbn in Hlb.
rewrite app_nth2 in Hlb; [ | now unfold ge ].
rewrite Nat.sub_diag in Hlb; cbn in Hlb.
destruct (srng_eq_dec b 0) as [Hbz| Hbz]; [ easy | clear Hlb ].
move b before a.
destruct (Nat.eq_dec (length la) (length lb)) as [Hlab| Hlab]. 2: {
  rewrite norm_polyn_list_id. 2: {
    destruct (lt_dec (length la) (length lb)) as [Hll| Hll]. {
      clear Hlab i.
      rewrite polyn_list_add_app_r.
      rewrite skipn_all2; [ | now rewrite app_length, Nat.add_1_r ].
      now rewrite List_last_app_not_nil_r.
    } {
      assert (H : length lb < length la) by flia Hlab Hll.
      clear Hlab Hll i.
      rewrite polyn_list_add_app_l.
      rewrite skipn_all2; [ | now rewrite app_length, Nat.add_1_r ].
      now rewrite List_last_app_not_nil_r.
    }
  }
  apply list_polyn_nth_add.
}
rewrite polyn_list_add_app_l.
rewrite firstn_app.
rewrite Hlab, firstn_all.
rewrite Nat.sub_diag, firstn_O.
rewrite app_nil_r.
rewrite skipn_app.
rewrite skipn_all, Nat.sub_diag, skipn_O.
rewrite app_nil_l; cbn.
rewrite norm_polyn_list_app; cbn.
destruct (srng_eq_dec (a + b) 0) as [Habz| Habz]. {
  cbn.
  destruct (lt_dec i (length la)) as [Hil| Hil]. {
    rewrite app_nth1; [ | easy ].
    rewrite app_nth1; [ | congruence ].
    clear a b Haz Hbz Habz.
    revert i lb Hlab Hil.
    induction la as [| a]; intros. {
      rewrite (nth_overflow []); [ | cbn; flia ].
      symmetry in Hlab.
      apply length_zero_iff_nil in Hlab; subst lb.
      now rewrite srng_add_0_l.
    }
    destruct lb as [| b]; [ easy | ].
    cbn in Hlab.
    apply Nat.succ_inj in Hlab.
    destruct i. {
      cbn.
      rewrite strip_0s_app.
      remember (strip_0s _) as lc eqn:Hlc.
      symmetry in Hlc.
      destruct lc as [| c]; [ now cbn; destruct (srng_eq_dec (a + b) 0) | ].
      now cbn; rewrite rev_app_distr.
    }
    cbn in Hil.
    apply Nat.succ_lt_mono in Hil.
    cbn - [ norm_polyn_list ].
    specialize (IHla _ _ Hlab Hil) as H1.
    unfold norm_polyn_list in H1 |-*; cbn.
    rewrite strip_0s_app.
    remember (strip_0s (rev (la + lb)%PL)) as lc eqn:Hlc.
    symmetry in Hlc.
    destruct lc as [| c]. {
      cbn in H1 |-*.
      destruct (srng_eq_dec (a + b) 0) as [Habz| Habz]; [ now destruct i | ].
      easy.
    }
    cbn in H1 |-*.
    now rewrite rev_app_distr.
  }
  apply Nat.nlt_ge in Hil.
  rewrite app_nth2; [ | easy ].
  rewrite app_nth2; [ | now rewrite <- Hlab ].
  destruct (Nat.eq_dec i (length la)) as [Hila| Hila]. {
    rewrite Hila, Hlab, Nat.sub_diag; cbn.
    rewrite Habz.
    apply nth_overflow.
    etransitivity; [ apply norm_polyn_list_length_le | ].
    rewrite polyn_list_add_length.
    rewrite max_r; [ easy | ].
    now rewrite Hlab.
  }
  rewrite (nth_overflow [a]); [ | cbn; flia Hil Hila ].
  rewrite (nth_overflow [b]); [ | cbn; flia Hil Hila Hlab ].
  rewrite srng_add_0_l.
  apply nth_overflow.
  etransitivity; [ apply norm_polyn_list_length_le | ].
  rewrite polyn_list_add_length.
  rewrite max_l; [ easy | ].
  now rewrite Hlab.
}
cbn.
destruct (lt_dec i (length la)) as [Hil| Hil]. {
  rewrite app_nth1. 2: {
    rewrite polyn_list_add_length.
    rewrite max_l; [ easy | ].
    now rewrite Hlab.
  }
  rewrite app_nth1; [ | easy ].
  rewrite app_nth1; [ | now rewrite <- Hlab ].
  apply list_polyn_nth_add.
}
destruct (lt_dec (length la) i) as [Hlai| Hlai]. {
  rewrite nth_overflow. 2: {
    rewrite app_length, Nat.add_1_r.
    rewrite polyn_list_add_length.
    rewrite max_l; [ easy | ].
    now rewrite Hlab.
  }
  rewrite nth_overflow. 2: {
    now rewrite app_length, Nat.add_1_r.
  }
  rewrite nth_overflow. 2: {
    now rewrite app_length, Nat.add_1_r, <- Hlab.
  }
  now rewrite srng_add_0_l.
}
apply Nat.nlt_ge in Hil.
apply Nat.nlt_ge in Hlai.
apply Nat.le_antisymm in Hil; [ | easy ].
rewrite Hil.
rewrite app_nth2. 2: {
  rewrite polyn_list_add_length.
  unfold ge.
  rewrite max_l; [ easy | now rewrite Hlab ].
}
rewrite polyn_list_add_length.
rewrite max_l; [ | now rewrite Hlab ].
rewrite app_nth2; [ | now unfold ge ].
rewrite app_nth2; [ | now unfold ge; rewrite Hlab ].
rewrite Hlab.
now rewrite Nat.sub_diag.
Qed.

(* sub-polynomial:
   polynomial skipping i coefficients:
     input: Σ (j = 0, n), a_j x^j
     output: Σ (j = i, n), a_j x^(j-i) *)

Theorem subp_polyn_prop : ∀ i P,
  polyn_prop_test (λ i0 : nat, nth i0 (skipn i (polyn_list P)) 0%Srng)
    (length (skipn i (polyn_list P))) = true.
Proof.
intros i (la, Hla); cbn.
revert i.
induction la as [| a]; intros; [ now rewrite skipn_nil | ].
cbn - [ nth ] in Hla.
rewrite <- List_last_nth_cons in Hla.
destruct (srng_eq_dec (last (a :: la) 0%Srng) 0) as [H| Haz]; [ easy | ].
clear Hla.
rewrite skipn_length.
cbn - [ sub ].
assert (H : polyn_prop_test (λ i : nat, nth i la 0%Srng) (length la) = true). {
  clear - Haz.
  revert a Haz.
  induction la as [| a1]; intros; [ easy | ].
  cbn - [ nth ].
  rewrite  <- List_last_nth_cons.
  rewrite List_last_cons_cons in Haz.
  now destruct (srng_eq_dec (last (a1 :: la) 0%Srng) 0).
}
specialize (IHla H); clear H.
destruct i. {
  rewrite Nat.sub_0_r.
  cbn - [ nth ].
  rewrite  <- List_last_nth_cons.
  now destruct (srng_eq_dec (last (a :: la) 0%Srng) 0).
}
rewrite Nat.sub_succ.
specialize (IHla i) as H1.
now rewrite skipn_length in H1.
Qed.

Theorem polyn_list_length : ∀ P,
  length (polyn_list P) = polyn_degree_plus_1 P.
Proof. easy. Qed.

Definition sub_polyn_list (la : list T) i := skipn i la.

Definition sub_polyn P i :=
  {| polyn_list := sub_polyn_list (polyn_list P) i;
     polyn_prop := subp_polyn_prop i P |}.

Theorem eval_polyn_list_cons : ∀ la (a x : T),
  eval_polyn_list (a :: la) x = (a + x * eval_polyn_list la x)%Srng.
Proof.
intros.
cbn; rewrite srng_add_comm; f_equal.
apply srng_mul_comm.
Qed.

Theorem last_polyn_list_add_length_lt : ∀ la lb d,
  length lb < length la
  → last (la + lb)%PL d = last la d.
Proof.
intros * Hll.
rewrite polyn_list_add_comm.
revert la Hll.
induction lb as [| b] using rev_ind; intros; [ easy | ].
destruct la as [| a] using rev_ind; [ now cbn in Hll | clear IHla ].
do 2 rewrite app_length, Nat.add_1_r in Hll.
apply Nat.succ_lt_mono in Hll.
rewrite List_last_app.
rewrite polyn_list_add_app_l.
rewrite firstn_app.
rewrite (proj2 (Nat.sub_0_le _ _)); [ | flia Hll ].
rewrite firstn_O, app_nil_r.
rewrite skipn_app.
rewrite (proj2 (Nat.sub_0_le _ _)); [ | flia Hll ].
rewrite skipn_O.
rewrite List_last_app_not_nil_r. 2: {
  now destruct (skipn (length lb) la).
}
cbn.
remember (skipn (length lb) la) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]. {
  exfalso.
  remember (length lb) as len.
  clear - Hll Hlc.
  revert la Hll Hlc.
  induction len; intros; cbn. {
    now cbn in Hlc; subst la.
  }
  destruct la as [| a]; [ easy | ].
  cbn in Hll, Hlc.
  apply Nat.succ_lt_mono in Hll.
  now apply (IHlen la).
}
cbn.
rewrite List_last_app.
remember (lc ++ [a]) as ld eqn:Hld.
symmetry in Hld.
destruct ld; [ | easy ].
now apply app_eq_nil in Hld.
Qed.

Theorem polyn_list_mul_last : ∀ la lb,
  last (la * lb)%PL 0%Srng = (last la 0 * last lb 0)%Srng.
Proof.
intros.
unfold polyn_list_mul.
remember (length la + length lb - 1) as len eqn:Hlen.
symmetry in Hlen.
revert la lb Hlen.
induction len; intros. {
  cbn.
  destruct la as [| a]; [ now cbn; rewrite srng_mul_0_l | ].
  cbn in Hlen; rewrite Nat.sub_0_r in Hlen.
  destruct la; [ | easy ].
  apply length_zero_iff_nil in Hlen; subst lb; cbn.
  symmetry; apply srng_mul_0_r.
}
(**)
rewrite List_seq_succ_r.
rewrite map_app.
cbn - [ last polyn_list_convol_mul ].
rewrite List_last_app.
unfold polyn_list_convol_mul.
do 2 rewrite List_last_nth.
destruct la as [| a]. {
  unfold so.
  rewrite all_0_srng_summation_0. 2: {
    intros i Hi.
    rewrite nth_overflow; [ | cbn; flia ].
    apply srng_mul_0_l.
  }
  cbn; symmetry.
  apply srng_mul_0_l.
}
destruct lb as [| b]. {
  unfold so.
  rewrite all_0_srng_summation_0. 2: {
    intros i Hi.
    rewrite (nth_overflow []); [ | cbn; flia ].
    apply srng_mul_0_r.
  }
  cbn; symmetry.
  apply srng_mul_0_r.
}
cbn in Hlen.
cbn - [ iter_seq nth ].
do 2 rewrite Nat.sub_0_r.
destruct la as [| a1]. {
  unfold so.
  cbn in Hlen.
  apply Nat.succ_inj in Hlen.
  rewrite srng_summation_split_first; [ | flia ].
  rewrite all_0_srng_summation_0. 2: {
    intros i Hi.
    destruct i; [ easy | ].
    rewrite nth_overflow; [ | cbn; flia ].
    apply srng_mul_0_l.
  }
  rewrite srng_add_0_r, Nat.sub_0_r.
  now rewrite Hlen.
}
rewrite <- List_last_nth_cons.
rewrite List_last_cons_cons.
rewrite List_last_nth_cons.
rewrite Nat.sub_0_r in Hlen; cbn in Hlen.
unfold so.
rewrite (srng_summation_split (S (length la))); [ | flia Hlen ].
rewrite (srng_summation_split (length la)); [ | flia Hlen ].
rewrite all_0_srng_summation_0. 2: {
  intros i Hi.
  rewrite (nth_overflow (b :: lb)); [ | cbn; flia Hlen Hi ].
  apply srng_mul_0_r.
}
rewrite srng_add_0_l.
rewrite Nat.add_1_r.
rewrite srng_summation_only_one.
rewrite all_0_srng_summation_0. 2: {
  intros i Hi.
  rewrite (nth_overflow (a :: a1 :: la)); [ | cbn; flia Hlen Hi ].
  apply srng_mul_0_l.
}
rewrite srng_add_0_r.
now replace (len - S (length la)) with (length lb) by flia Hlen.
Qed.

(* division of a polynomial P with (x - c) *)
(* P = (x-c).Q + R with
   Q = a_n.x^{n-1} +
       (a_n.c+a_{n-1}).x^{n-2} +
       ... +
       ((a_n.c+a_{n-1})c+...+a_1)x^0
   R = P(c) *)

Definition polyn_list_div_x_sub_const la c :=
  (map (λ i, eval_polyn_list (sub_polyn_list la i) c) (seq 1 (length la - 1)),
   eval_polyn_list la c).

Definition polyn_div_x_sub_const P c :=
  (polyn_of_list (fst (polyn_list_div_x_sub_const (polyn_list P) c)),
   snd (polyn_list_div_x_sub_const (polyn_list P) c)).

Theorem polyn_list_nth_quotient_with_x_sub_const : ∀ la lq r c,
  polyn_list_div_x_sub_const la c = (lq, r)
  → ∀ i, i < length la - 1
  → nth i lq 0%Srng = eval_polyn_list (sub_polyn_list la (i + 1)) c.
Proof.
intros * Hqr * Hi.
injection Hqr; clear Hqr; intros Hr Hq.
subst lq; cbn.
rewrite (List_map_nth_in _ 0); [ | now rewrite seq_length ].
rewrite Nat.add_comm.
now rewrite seq_nth.
Qed.

Theorem polyn_coeff_quotient_with_x_sub_const : ∀ P c Q r,
  polyn_div_x_sub_const P c = (Q, r)
  → ∀ i, i < polyn_degree P
  → polyn_coeff Q i = eval_polyn (sub_polyn P (i + 1)) c.
Proof.
intros * Hqr * Hi.
unfold polyn_div_x_sub_const in Hqr.
remember (polyn_list_div_x_sub_const _ _) as ll eqn:Hll.
symmetry in Hll.
destruct ll as (lq, rr).
injection Hqr; clear Hqr; intros Hr Hq; subst Q rr.
unfold eval_polyn, sub_polyn.
cbn - [ eval_polyn_list sub_polyn_list ].
unfold polyn_degree, polyn_degree_plus_1 in Hi.
remember (polyn_list P) as la.
clear P Heqla.
replace (nth i (norm_polyn_list lq) 0%Srng) with (nth i lq 0%Srng). 2: {
  injection Hll; clear Hll; intros; subst lq r.
  rewrite <- seq_shift, map_map.
  rewrite (List_map_nth_in _ 0); [ | rewrite seq_length; flia Hi ].
  rewrite seq_nth; [ | flia Hi ].
  rewrite Nat.add_0_l.
  symmetry.
  apply nth_norm_polyn_list_map.
  intros j Hj.
  unfold sub_polyn_list.
  rewrite skipn_all2; [ easy | flia Hj ].
}
apply polyn_list_nth_quotient_with_x_sub_const with (r := r); [ easy | ].
flia Hi.
Qed.

Theorem polyn_list_div_x_sub_const_length : ∀ la lq c r,
  last la 0%Srng ≠ 0%Srng
  → polyn_list_div_x_sub_const la c = (lq, r)
  → length la = length (norm_polyn_list ([(- c)%Rng; 1%Srng] * lq + [r])%PL).
Proof.
intros * Haz Hqr.
injection Hqr; clear Hqr; intros Hr Hq.
  remember (length la) as n eqn:Hn; symmetry in Hn.
  symmetry.
  destruct n. {
    now apply length_zero_iff_nil in Hn; subst la.
  }
  rewrite Nat.sub_succ, Nat.sub_0_r in Hq.
  destruct n. {
    cbn in Hq; subst lq.
    unfold so.
    destruct la as [| a]; [ easy | ].
    destruct la; [ | easy ].
    cbn in Haz, Hr.
    rewrite srng_mul_0_l, srng_add_0_l in Hr.
    subst a; cbn.
    rewrite srng_add_0_l, srng_mul_0_r, srng_add_0_l.
    now destruct (srng_eq_dec r 0).
  }
  rewrite norm_polyn_list_id. 2: {
    rewrite last_polyn_list_add_length_lt. 2: {
      cbn - [ polyn_list_mul ].
      destruct lq as [| q]; [ exfalso | cbn; flia ].
      now apply map_eq_nil in Hq.
    }
    rewrite polyn_list_mul_last.
    cbn; rewrite srng_mul_1_l.
    rewrite <- Hq.
    rewrite List_seq_succ_r.
    rewrite map_app.
    cbn - [ sub_polyn_list ].
    rewrite List_last_app.
    unfold sub_polyn_list.
    replace (S n) with (length la - 1) by flia Hn.
    rewrite List_skipn_last with (d := 0%Srng) by now destruct la.
    now cbn; rewrite srng_mul_0_l, srng_add_0_l.
  }
  rewrite polyn_list_add_length.
  rewrite polyn_list_mul_length; cbn.
  rewrite <- Hq.
  rewrite map_length, seq_length.
  rewrite max_l; [ easy | apply Nat.le_0_l ].
Qed.

Theorem polyn_list_div_x_sub_const_prop : ∀ la lq c r,
  last la 0%Srng ≠ 0%Srng
  → polyn_list_div_x_sub_const la c = (lq, r)
  → la = norm_polyn_list ([(- c)%Rng; 1%Srng] * lq + [r])%PL.
Proof.
intros * Haz Hqr.
apply (proj2 (List_eq_iff _ _)).
specialize (polyn_list_div_x_sub_const_length Haz Hqr) as Hll.
split; [ easy | ].
remember (norm_polyn_list _) as la' eqn:Hla'.
intros.
move d before r.
...
  revert la lq c r Hr Hn Hq.
  induction n; intros. {
    cbn.
    rewrite polyn_list_add_0_r, srng_add_0_l.
    apply length_zero_iff_nil in Hn; subst la; cbn in Hr, Hq.
    subst r lq; cbn.
    rewrite srng_mul_0_r, srng_add_0_l.
    now rewrite if_0_eq_0.
  }
  destruct la as [| a]; [ easy | ].
  cbn in Hn.
  apply Nat.succ_inj in Hn.
  rewrite eval_polyn_list_cons in Hr.
  remember (eval_polyn_list la c) as r' eqn:Hr'.
  symmetry in Hr'; subst r.
  cbn in Hq.
  rewrite <- seq_shift in Hq.
  rewrite map_map in Hq.
  erewrite map_ext_in in Hq. 2: {
    intros i Hi.
    cbn - [ eval_polyn_list ].
    replace (skipn i la) with (sub_polyn_list la i) by easy.
    easy.
  }
  remember (map (λ i, eval_polyn_list (sub_polyn_list la i) c) (seq 1 n))
    as lq' eqn:Hlq'.
  symmetry in Hlq'; subst lq.
  specialize (IHn la lq' c r' Hr' Hn Hlq') as H1.
  rewrite fold_eval_polyn_list.
...
}
split; [ easy | ].
...

Theorem polyn_div_x_sub_const_prop : ∀ P c Q r,
  polyn_div_x_sub_const P c = (Q, r)
  → P = ((_x - polyn_of_list [c]) * Q + polyn_of_list [r])%P.
Proof.
intros * Hqr.
apply polyn_eq.
cbn - [ norm_polyn_list polyn_list_mul ].
rewrite norm_polyn_list_add_idemp_l.
rewrite norm_polyn_list_add_idemp_l.
rewrite norm_polyn_list_add_idemp_r.
replace  ([0%Srng; 1%Srng] + map rng_opp (norm_polyn_list [c]))%PL
  with [(- c)%Rng; 1%Srng]. 2: {
  cbn.
  destruct (srng_eq_dec c 0) as [Hcz| Hcz]. {
    subst c; cbn.
    unfold so.
    now rewrite rng_opp_0.
  }
  cbn.
  now rewrite srng_add_0_l.
}
remember (norm_polyn_list [_; _]) as x eqn:Hx.
cbn in Hx.
rewrite if_1_eq_0 in Hx; cbn in Hx; subst x.
unfold polyn_div_x_sub_const in Hqr.
remember (polyn_list_div_x_sub_const _ _) as ll eqn:Hll.
symmetry in Hll.
destruct ll as (lq, rr).
injection Hqr; clear Hqr; intros Hr Hq; subst Q rr.
remember (polyn_list (polyn_of_list lq)) as x eqn:Hx.
cbn in Hx; subst x.
rewrite <- norm_polyn_list_add_idemp_l.
rewrite norm_polyn_list_mul_idemp_r.
rewrite norm_polyn_list_add_idemp_l.
...
now apply polyn_list_div_x_sub_const_prop.
...
destruct P as (la, Hla).
destruct Q as (lb, Hlb).
move lb before la.
move Hlb before Hla.
injection HQR; clear HQR; intros HR HQ.
cbn - [ norm_polyn_list ].
rewrite norm_polyn_list_add_idemp_l.
rewrite norm_polyn_list_add_idemp_l.
rewrite norm_polyn_list_add_idemp_r.
unfold eval_polyn, sub_polyn in H1.
cbn - [ eval_polyn_list sub_polyn_list ] in H1.
Search (polyn_list_convol_mul (norm_polyn_list _)).
...
rewrite norm_polyn_list_add.
...
nth_norm_polyn_list_map:
  ∀ (i len : nat) (f : nat → T),
    (∀ i0 : nat, len ≤ i0 → f i0 = 0%Srng)
    → nth i (norm_polyn_list (map f (seq 0 len))) 0%Srng = f i
...
intros * HQR.
injection HQR; clear HQR; intros HR HQ.
apply polyn_eq.
subst Q r.
remember (polyn_degree P) as n eqn:Hn.
symmetry in Hn.
revert c P Hn.
induction n; intros. {
  cbn; rewrite if_1_eq_0; cbn.
  destruct (srng_eq_dec c 0) as [Hcz| Hcz]. {
    cbn; rewrite if_1_eq_0; cbn.
    rewrite srng_add_0_l, srng_mul_0_l.
    subst c; cbn.
    destruct P as (la, Hla); cbn - [ eval_polyn_list ].
    destruct (srng_eq_dec (eval_polyn_list la 0%Srng) 0) as [Hpz| Hpz]. {
      cbn.
      rewrite rev_length.
...
      destruct P as (la, Hla); cbn in Hn |-*.
      destruct la as [| a]; [ easy | exfalso ].
      cbn in Hn.
      rewrite Nat.sub_0_r in Hn.
      apply length_zero_iff_nil in Hn; subst la.
      cbn in Hla, Hpz.
      rewrite srng_add_0_l, srng_mul_1_r in Hpz; subst a.
      now rewrite if_0_eq_0 in Hla.
    }
    destruct P as (la, Hla); cbn in Hn |-*.
    destruct la as [| a]; [ easy | ].
    cbn in Hn.
    rewrite Nat.sub_0_r in Hn.
    apply length_zero_iff_nil in Hn; subst la.
    cbn in Hla, Hpz |-*.
    rewrite srng_add_0_l, srng_mul_1_r in Hpz |-*.
    now destruct (srng_eq_dec a 0).
  }
...

intros * HQR.
injection HQR; clear HQR; intros HR HQ.
apply polyn_eq.
subst Q r.
unfold polyn_sub.
rewrite polyn_mul_add_distr_r.
rewrite rng_mul_opp_l.
rewrite fold_polyn_sub.
Search (polyn_of_list (map _ _)).
...
destruct P as (la, Hla).
cbn - [ norm_polyn_list ].
...
*)

(* in algebraically closed set, a polynomial P is the
   product of its highest coefficient and all (x-rn)
   where rn cover all roots of P *)

Theorem polyn_in_algeb_closed :
  ∀ (acp : algeb_closed_prop) (P : polynomial T),
  ∃ RL, P =
      (polyn_of_list [polyn_highest_coeff P] *
       Π (i = 1, polyn_degree P),
         (_x - polyn_of_list [nth (i - 1) RL 0%Srng]))%P.
Proof.
intros.
remember (polyn_degree P) as n eqn:Hn; symmetry in Hn.
revert P Hn.
induction n; intros. {
  exists [].
  unfold polyn_highest_coeff.
  unfold polyn_coeff.
  rewrite Hn; cbn.
  unfold so.
  rewrite polyn_mul_1_r.
  apply polyn_eq; cbn.
  unfold so; cbn; fold so.
  destruct (srng_eq_dec (nth 0 (polyn_list P) 0%Srng) 0) as [Hpz| Hpz]. {
    destruct P as (la, Hla).
    destruct la as [| a]; [ easy | exfalso ].
    cbn in Hn; rewrite Nat.sub_0_r in Hn.
    apply length_zero_iff_nil in Hn; subst la.
    cbn in Hla, Hpz.
    subst a.
    now rewrite if_0_eq_0 in Hla.
  }
  destruct P as (la, Hla).
  destruct la as [| a]; [ easy | cbn ].
  now destruct la.
}
destruct acp as (Hroots).
specialize (Hroots P) as H1.
rewrite Hn in H1.
specialize (H1 (Nat.lt_0_succ _)).
destruct H1 as (x, Hx).
remember (polyn_div_x_sub_const P x) as QR eqn:HQR.
symmetry in HQR.
destruct QR as (Q, R).
...
apply polyn_div_x_sub_const_prop in HQR.
...
specialize (IHn Q) as H1.
assert (H : polyn_degree Q = n). {
  destruct Q as (lb, Hlb); cbn.
  destruct lb as [| b]. {
    cbn in Hlb.
    unfold polyn_div_x_sub_const in HQR.
    rewrite Hn in HQR.
    rewrite Nat.sub_succ, Nat.sub_0_r in HQR.
    injection HQR; clear HQR; intros HR HQ.
    rewrite Hx in HR.
    specialize (proj2 (all_0_norm_polyn_list_map_0 _ _) HQ) as H2.
    cbn in H2.
    clear H1 Hlb R HR.
    specialize (H2 n) as H3.
    destruct n; [ easy | exfalso ].
    assert (H : S n ∈ seq 1 (S n)). {
      apply in_seq; flia.
    }
    specialize (H3 H); clear H.
    unfold eval_polyn in H3.
    unfold polyn_degree_plus_1 in H3.
    remember (length (polyn_list (sub_polyn P (S n)))) as len eqn:Hlen.
    symmetry in Hlen.
    destruct len. {
      destruct P as (la, Hla).
      cbn in Hlen, Hn.
      destruct la as [| a]; [ easy | ].
      cbn in Hn; rewrite Nat.sub_0_r in Hn.
      clear - Hn Hlen.
      revert n Hn Hlen.
      induction la as [| a]; intros; [ easy | ].
      destruct n; [ easy | cbn in Hn, Hlen ].
      apply Nat.succ_inj in Hn.
      now apply (IHla n).
    }
...
*)

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
  (iter_seq b e (λ c i, (c + g)%P) 0%P)
  (at level 45, i at level 0, b at level 60, e at level 60) :
     polynomial_scope.

Notation "'Π' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c * g)%P) 1%P)
  (at level 45, i at level 0, b at level 60, e at level 60) :
     polynomial_scope.

Arguments is_monic_polyn {T ro sdp} P%P.
Arguments norm_polyn_list {T ro sdp} l%PL.
Arguments polyn_coeff {T so sdp} P%P i%nat.
Arguments polyn_degree {T so sdp} P%P.
Arguments polyn_eq_dec {T ro sdp} P%P Q%P.
Arguments polyn_list_convol_mul {T ro} la%PL lb%PL _%nat.
Arguments polyn_list {T so sdp} p%P.

End polynomial_Notations.
