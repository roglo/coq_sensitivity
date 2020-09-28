(* SRpolynomial.v *)

(* polynomials on a semiring *)

Set Nested Proofs Allowed.
Set Implicit Arguments.
Require Import Utf8 Arith.
Import List ListNotations.

Require Import Misc Semiring SRsummation.

(* decidability of equality in semirings
   and the fact that 1 ≠ 0 *)

Class sring_dec_prop T {so : semiring_op T} :=
  { srng_eq_dec : ∀ a b : T, {a = b} + {a ≠ b};
    srng_1_neq_0 : (1 ≠ 0)%Srng }.

Arguments srng_eq_dec {T}%type {so sring_dec_prop} _%Srng _%Srng.

(* property of a polynomial: its coefficient of higher degree is not 0 *)
(* returns a boolean to allow proof of equality to be unique *)

Definition srng_eqb {T} {so : semiring_op T} {fdp : sring_dec_prop}
    (a b : T) :=
  if srng_eq_dec a b then true else false.

Record polynomial T {so : semiring_op T} {sdp : sring_dec_prop} := mk_polyn
  { polyn_list : list T;
    polyn_prop : srng_eqb (last polyn_list 1%Srng) 0%Srng = false }.

Arguments polynomial T%type_scope {so sdp}.
Arguments polyn_list {T so sdp}.
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

Theorem eq_polyn_prop : ∀ la,
  srng_eqb (last la 1%Rng) 0%Rng = false ↔ last la 1%Rng ≠ 0%Rng.
Proof.
intros.
unfold srng_eqb.
now destruct (srng_eq_dec (last la 1%Rng) 0%Rng).
Qed.

Theorem polyn_list_1_0_prop : srng_eqb (last [] 1%Rng) 0%Rng = false.
Proof.
cbn.
unfold srng_eqb.
destruct (srng_eq_dec 1%Rng 0%Rng); [ | easy ].
now apply srng_1_neq_0 in e.
Qed.

Definition polyn_zero :=
  mk_polyn [] polyn_list_1_0_prop.
Definition polyn_one :=
  mk_polyn [1%Rng] polyn_list_1_0_prop.

(* normalization *)

Fixpoint strip_0s la :=
  match la with
  | [] => []
  | a :: la' => if srng_eq_dec a 0%Rng then strip_0s la' else la
  end.

Lemma strip_0s_app : ∀ la lb,
  strip_0s (la ++ lb) =
  match strip_0s la with
  | [] => strip_0s lb
  | lc => lc ++ lb
  end.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct (srng_eq_dec a 0%Rng) as [Haz| Haz]; [ apply IHla | easy ].
Qed.

Definition polyn_list_norm la := rev (strip_0s (rev la)).

Theorem polyn_norm_prop : ∀ la, last (polyn_list_norm la) 1%Rng ≠ 0%Rng.
Proof.
intros.
unfold polyn_list_norm.
induction la as [| a]; [ apply srng_1_neq_0 | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; cbn. {
  destruct (srng_eq_dec a 0%Rng) as [Haz| Haz]; [ apply srng_1_neq_0 | easy ].
}
cbn in IHla.
rewrite List_last_app.
now rewrite List_last_app in IHla.
Qed.

Definition polyn_norm la :=
  mk_polyn (polyn_list_norm la) (proj2 (eq_polyn_prop _) (polyn_norm_prop la)).

(* polynomial from and to a list *)

Theorem polyn_of_list_prop : ∀ l,
  srng_eqb (last (polyn_list_norm l) 1%Srng) 0%Srng = false.
Proof.
intros.
unfold polyn_list_norm.
remember (rev l) as l' eqn:Hl.
clear l Hl.
rename l' into l.
(**)
induction l as [| a]. {
  destruct (srng_eq_dec 1 0) as [Haz| Haz]. {
    now apply srng_1_neq_0 in Haz.
  }
  cbn.
Search srng_eqb.
Check polyn_list_1_0_prop.
...
rewrite rev_length.
induction l as [| a]; [ easy | cbn ].
destruct (srng_eq_dec a 0%Srng) as [Haz| Haz]; [ apply IHl | cbn ].
rewrite app_nth2; rewrite rev_length; [ | now unfold ge ].
rewrite Nat.sub_diag; cbn.
now destruct (srng_eq_dec a 0%Srng).
Qed.
*)

Definition polyn_of_list l :=
  mk_polyn (polyn_list_norm l) (polyn_of_list_prop l).

Definition list_of_polyn (P : polynomial T) :=
  polyn_list P.

...

(**)
End in_ring.
Require Import ZArith.

Theorem Z_neq_1_0 : 1%Z ≠ 0%Z. Proof. easy. Qed.

Definition Z_sring_dec_prop :=
  {| srng_eq_dec := Z.eq_dec;
     srng_1_neq_0 := Z_neq_1_0 |}.

Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in polyn_of_list [3; 4; 7; 0].
Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in list_of_polyn (polyn_of_list [3; 4; 7; 0]).
Compute let ro := Z_ring_op in let sdp := Z_sring_dec_prop in list_of_polyn (polyn_of_list [0]).
(**)

...

(* addition *)

Fixpoint polyn_list_add {α} {ro : ring_op α} {sp : semiring_prop} al1 al2 :=
  match al1 with
  | [] => al2
  | a1 :: bl1 =>
      match al2 with
      | [] => al1
      | a2 :: bl2 => (a1 + a2)%Rng :: polyn_list_add bl1 bl2
      end
  end.

Definition polyn_list_opp {α} {ro : ring_op α} {sp : semiring_prop} la := List.map srng_opp la.
Definition polyn_list_sub {A} {so : semiring_op T} {sp : semiring_prop} la lb := polyn_list_add la (polyn_list_opp lb).

Definition polyn_add {A} {so : semiring_op T} {sp : semiring_prop} p1 p2 :=
  polyn_norm (polyn_list_add (polyn_list p1) (polyn_list p2)).

Definition polyn_opp {α} {ro : ring_op α} {sp : semiring_prop} pol :=
  polyn_norm (polyn_list_opp (polyn_list pol)).

Definition polyn_sub {α} {ro : ring_op α} {sp : semiring_prop} p1 p2 :=
  polyn_add p1 (polyn_opp p2).

(*
Compute (@polyn_add Z Z_ring (polyn_norm [3;4;5]%Z) (polyn_norm [2;3;-4;5]%Z)).
Compute (@polyn_add Z Z_ring (polyn_norm [3;4;5]%Z) (polyn_norm [2;3;-5]%Z)).
*)

(* multiplication *)

Fixpoint polyn_list_convol_mul {α} {ro : ring_op α} {sp : semiring_prop} al1 al2 i len :=
  match len with
  | O => []
  | S len1 =>
      (Σ (j = 0, i), List.nth j al1 0 * List.nth (i - j) al2 0)%Rng ::
      polyn_list_convol_mul al1 al2 (S i) len1
  end.

Definition polyn_list_mul {α} {ro : ring_op α} {sp : semiring_prop} la lb :=
  match la with
  | [] => []
  | _ =>
      match lb with
      | [] => []
      | _ => polyn_list_convol_mul la lb 0 (length la + length lb - 1)
      end
  end.

Definition polyn_mul {A} {so : semiring_op T} {sp : semiring_prop} p1 p2 :=
  polyn_norm (polyn_list_mul (polyn_list p1) (polyn_list p2)).

(*
Compute (@polyn_list_mul Z Z_ring [3;4;5]%Z [2;3;-4;5]%Z).
Compute (@polyn_mul Z Z_ring (polyn_norm [3;4;5]%Z) (polyn_norm [2;3;-4;5]%Z)).
*)

(* power *)

Fixpoint polyn_list_power {α} {ro : ring_op α} {sp : semiring_prop} la n :=
  match n with
  | O => [1%Rng]
  | S m => polyn_list_mul la (polyn_list_power la m)
  end.

Definition polyn_power {A} {so : semiring_op T} {sp : semiring_prop} pol n :=
  polyn_norm (polyn_list_power (polyn_list pol) n).

(*
Compute (@polyn_power Z Z_ring (polyn_norm [1; -1]%Z) 4).
*)

(* composition *)

Definition polyn_list_compose {α} {ro : ring_op α} {sp : semiring_prop} la lb :=
  List.fold_right (λ c accu, polyn_list_add (polyn_list_mul accu lb) [c]) [] la.

Definition polyn_list_compose2 {α} {ro : ring_op α} {sp : semiring_prop} la lb :=
  List.fold_right
    (λ i accu,
     polyn_list_add accu (polyn_list_mul [List.nth i la 0] (polyn_list_power lb i)))%Rng
    [] (List.seq 0 (length la)).

(* *)

Fixpoint list_pad {α} n (zero : α) rem :=
  match n with
  | O => rem
  | S n1 => zero :: list_pad n1 zero rem
  end.

Theorem xpow_norm {A} {so : semiring_op T} {sp : semiring_prop} : ∀ i,
  srng_eqb (last (repeat 0%Rng i ++ [1%Rng]) 1%Rng) 0%Rng = false.
Proof.
intros.
rewrite List_last_app.
unfold srng_eqb.
destruct (srng_eq_dec 1 0) as [H| H]; [ | easy ].
now apply srng_1_neq_0 in H.
Qed.

Definition xpow {α} {ro : ring_op α} {sp : semiring_prop} i :=
  mk_polyn (repeat 0%Rng i ++ [1%Rng]) (xpow_norm i).

Declare Scope polyn_list_scope.
Delimit Scope polyn_list_scope with polyn_list.
Notation "1" := [1%Rng] : polyn_list_scope.
Notation "- a" := (polyn_list_opp a) : polyn_list_scope.
Notation "a + b" := (polyn_list_add a b) : polyn_list_scope.
Notation "a - b" := (polyn_list_sub a b) : polyn_list_scope.
Notation "a * b" := (polyn_list_mul a b) : polyn_list_scope.
Notation "a ^ b" := (polyn_list_power a b) : polyn_list_scope.

Definition list_nth_def_0 {α} {ro : ring_op α} {sp : semiring_prop} n l := List.nth n l 0%Rng.

Declare Scope polyn_scope.
Delimit Scope polyn_scope with pol.
Notation "0" := polyn_zero : polyn_scope.
Notation "1" := polyn_one : polyn_scope.
Notation "- a" := (polyn_opp a) : polyn_scope.
Notation "a + b" := (polyn_add a b) : polyn_scope.
Notation "a - b" := (polyn_sub a b) : polyn_scope.
Notation "a * b" := (polyn_mul a b) : polyn_scope.
Notation "'ⓧ' ^ a" := (xpow a) (at level 30, format "'ⓧ' ^ a") : polyn_scope.
Notation "'ⓧ'" := (xpow 1) (at level 30, format "'ⓧ'") : polyn_scope.

(* *)

Theorem polyn_list_convol_mul_comm : ∀ α {ro : ring_op α} {sp : semiring_prop} l1 l2 i len,
  polyn_list_convol_mul l1 l2 i len = polyn_list_convol_mul l2 l1 i len.
Proof.
intros.
revert i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
rewrite summation_rtl.
apply summation_compat; intros j (_, Hj).
rewrite Nat.add_0_r.
rewrite srng_mul_comm.
apply srng_mul_compat; [ idtac | reflexivity ].
rewrite Nat_sub_sub_distr; [ idtac | easy ].
rewrite Nat.sub_diag, Nat.add_0_l; reflexivity.
Qed.

Theorem polyn_list_convol_mul_nil_l : ∀ α {ro : ring_op α} {sp : semiring_prop} l i len,
  polyn_list_norm (polyn_list_convol_mul [] l i len) = [].
Proof.
intros.
unfold polyn_list_norm.
revert i.
induction len; intros; [ reflexivity | ].
cbn - [ summation ].
rewrite all_0_summation_0. {
  rewrite strip_0s_app; cbn.
  specialize (IHlen (S i)).
  apply List_eq_rev_nil in IHlen.
  rewrite IHlen.
  now destruct (srng_eq_dec 0%Rng 0%Rng).
}
intros k (_, Hk).
now rewrite match_id, srng_mul_0_l.
Qed.

Theorem polyn_list_convol_mul_nil_r : ∀ α {ro : ring_op α} {sp : semiring_prop} l i len,
  polyn_list_norm (polyn_list_convol_mul l [] i len) = [].
Proof.
intros.
rewrite polyn_list_convol_mul_comm.
apply polyn_list_convol_mul_nil_l.
Qed.

Theorem list_nth_polyn_list_eq : ∀ α {ro : ring_op α} {sp : semiring_prop} la lb,
  (∀ i, (List.nth i la 0 = List.nth i lb 0)%Rng)
  → polyn_list_norm la = polyn_list_norm lb.
Proof.
intros * Hi.
unfold polyn_list_norm; f_equal.
revert lb Hi.
induction la as [| a]; intros. {
  induction lb as [| b]; [ reflexivity | ].
  specialize (Hi 0) as H; cbn in H.
  subst b; cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (rev lb)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]; [ now destruct (srng_eq_dec _ _) | ].
  assert (H : polyn_list_norm [] = polyn_list_norm lb). {
    unfold polyn_list_norm; cbn.
    cbn in IHlb.
    change (rev [] = rev (strip_0s (rev lb))).
    f_equal.
    rewrite Hlc.
    apply IHlb.
    intros i; cbn; rewrite match_id.
    now specialize (Hi (S i)); cbn in Hi.
  }
  cbn in H.
  unfold polyn_list_norm in H.
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
        destruct lb as [| b]; [ now destruct (srng_eq_dec a 0%Rng) | easy ].
      }
      apply IHla.
      cbn in Hlc.
      rewrite strip_0s_app in Hlc; cbn in Hlc.
      remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
      destruct lb as [| b]; [ now destruct (srng_eq_dec a 0%Rng) | easy ].
    }
    cbn.
    destruct (srng_eq_dec a 0%Rng) as [Haz| Haz]. {
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
      rewrite <- IHlb; [ now destruct (srng_eq_dec 0%Rng 0%Rng) | ].
      intros i.
      now specialize (Hlb (S i)).
    }
    destruct lb as [| b]; [ now specialize (Hi 0); cbn in Hi | cbn ].
    rewrite strip_0s_app; cbn.
    remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
    destruct ld as [| d]. {
      destruct (srng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
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
    destruct (srng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
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

Theorem fold_polyn_list_norm {A} {so : semiring_op T} {sp : semiring_prop} :
  ∀ la, rev (strip_0s (rev la)) = polyn_list_norm la.
Proof. easy. Qed.

Theorem polyn_list_add_0_l {α} {ro : ring_op α} {sp : semiring_prop} : ∀ la, polyn_list_add [] la = la.
Proof. easy. Qed.

Theorem polyn_list_add_0_r {α} {ro : ring_op α} {sp : semiring_prop} : ∀ la, polyn_list_add la [] = la.
Proof. intros; now destruct la. Qed.

Theorem polyn_add_0_l {α} {ro : ring_op α} {sp : semiring_prop} : ∀ p, (0 + p)%pol = p.
Proof.
intros (la, polyn_listr).
apply eq_polyn_eq; cbn.
apply eq_polyn_prop in polyn_listr.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
rewrite <- (rev_involutive (strip_0s _)).
rewrite IHla; cbn. {
  remember (rev la) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| b]. {
    apply List_eq_rev_nil in Hlb; subst la.
    now destruct (srng_eq_dec a 0).
  }
  cbn.
  rewrite rev_app_distr; cbn; f_equal.
  now rewrite <- rev_involutive, Hlb.
} {
  destruct la as [| a2]; [ | easy ].
  apply srng_1_neq_0.
}
Qed.

Theorem polyn_list_mul_0_l {α} {ro : ring_op α} {sp : semiring_prop} : ∀ la, polyn_list_norm (polyn_list_mul [] la) = [].
Proof. easy. Qed.

Theorem polyn_list_mul_0_r {α} {ro : ring_op α} {sp : semiring_prop} : ∀ la, polyn_list_norm (polyn_list_mul la []) = [].
Proof. now intros; destruct la. Qed.

Section polyn_list.

Context {α : Type}.
Context {ro : ring_op α} {sp : semiring_prop}.

Theorem strip_0s_idemp : ∀ la, strip_0s (strip_0s la) = strip_0s la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
destruct (srng_eq_dec a 0%Rng) as [Haz| Haz]; [ easy | cbn ].
now destruct (srng_eq_dec a 0%Rng).
Qed.

Theorem polyn_list_norm_idemp : ∀ la, polyn_list_norm (polyn_list_norm la) = polyn_list_norm la.
Proof.
intros.
unfold polyn_list_norm.
rewrite rev_involutive.
now rewrite strip_0s_idemp.
Qed.

Theorem eq_polyn_list_convol_mul_nil : ∀ la lb i len,
  polyn_list_convol_mul la lb i len = [] → len = 0.
Proof. now intros; induction len. Qed.

(* addition theorems *)

Theorem polyn_list_add_comm : ∀ al1 al2,
  polyn_list_add al1 al2 = polyn_list_add al2 al1.
Proof.
intros al1 al2.
revert al2.
induction al1; intros; [ now destruct al2 | ].
destruct al2; [ easy | cbn ].
now rewrite srng_add_comm, IHal1.
Qed.

Theorem polyn_add_comm : ∀ a b, (a + b)%pol = (b + a)%pol.
Proof.
intros.
unfold "+"%pol.
now rewrite polyn_list_add_comm.
Qed.

Theorem polyn_list_add_norm_idemp_l : ∀ la lb,
  polyn_list_norm (polyn_list_norm la + lb)%polyn_list = polyn_list_norm (la + lb)%polyn_list.
Proof.
intros.
unfold polyn_list_norm; f_equal.
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

Theorem polyn_list_add_norm_idemp_r : ∀ la lb,
  polyn_list_norm (la + polyn_list_norm lb)%polyn_list = polyn_list_norm (la + lb)%polyn_list.
Proof.
intros.
rewrite polyn_list_add_comm, polyn_list_add_norm_idemp_l.
now rewrite polyn_list_add_comm.
Qed.

Theorem polyn_list_add_assoc : ∀ al1 al2 al3,
  polyn_list_add al1 (polyn_list_add al2 al3) = polyn_list_add (polyn_list_add al1 al2) al3.
Proof.
intros al1 al2 al3.
revert al2 al3.
induction al1; intros; [ easy | ].
destruct al2; [ easy | cbn ].
destruct al3; [ easy | cbn ].
rewrite srng_add_assoc.
now rewrite IHal1.
Qed.

Theorem polyn_list_add_add_swap : ∀ la lb lc,
  polyn_list_add (polyn_list_add la lb) lc = polyn_list_add (polyn_list_add la lc) lb.
Proof.
intros la lb lc.
do 2 rewrite <- polyn_list_add_assoc.
now rewrite (polyn_list_add_comm lb).
Qed.

Theorem polyn_add_assoc : ∀ pa pb pc,
  (pa + (pb + pc) = (pa + pb) + pc)%pol.
Proof.
intros (la, polyn_listr) (lb, lbpr) (lc, lcpr).
apply eq_polyn_eq.
cbn - [ polyn_list_norm ].
rewrite polyn_list_add_norm_idemp_l.
rewrite polyn_list_add_norm_idemp_r.
now rewrite polyn_list_add_assoc.
Qed.

(* multiplication theorems *)

Theorem polyn_list_mul_comm : ∀ a b, polyn_list_mul a b = polyn_list_mul b a.
Proof.
intros la lb.
unfold polyn_list_mul.
destruct la as [| a]; [ now destruct lb | cbn ].
rewrite <- Nat.add_succ_comm; cbn.
rewrite (Nat.add_comm (length lb)).
now rewrite polyn_list_convol_mul_comm.
Qed.

Theorem polyn_mul_comm : ∀ pa pb, (pa * pb)%pol = (pb * pa)%pol.
Proof.
intros.
apply eq_polyn_eq; cbn.
now rewrite polyn_list_mul_comm.
Qed.

Theorem list_nth_polyn_list_convol_mul_aux : ∀ la lb n i len,
  List.length la + List.length lb - 1 = (i + len)%nat
  → (List.nth n (polyn_list_convol_mul la lb i len) 0%Rng =
     Σ (j = 0, n + i),
     List.nth j la 0 * List.nth (n + i - j) lb 0)%Rng.
Proof.
intros la lb n i len Hlen.
revert la lb i n Hlen.
induction len; intros.
 simpl.
 rewrite Nat.add_0_r in Hlen.
 rewrite all_0_summation_0; [ destruct n; reflexivity | idtac ].
 intros j (_, Hj).
 destruct (le_dec (length la) j) as [H1| H1].
  rewrite List.nth_overflow; [ idtac | assumption ].
  rewrite srng_mul_0_l; reflexivity.

  destruct (le_dec (length lb) (n + i - j)) as [H2| H2].
   rewrite srng_mul_comm.
   rewrite List.nth_overflow; [ idtac | assumption ].
   rewrite srng_mul_0_l; reflexivity.

   exfalso; apply H2; clear Hj H2.
   apply Nat.nle_gt in H1; subst i.
   flia H1.

 simpl.
 destruct n; [ reflexivity | idtac ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
 rewrite IHlen; [ idtac | assumption ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l; reflexivity.
Qed.

(* to be unified perhaps with list_nth_convol_mul below *)
Theorem list_nth_polyn_list_convol_mul : ∀ la lb i len,
  len = length la + length lb - 1
  → (List.nth i (polyn_list_convol_mul la lb 0 len) 0 =
     Σ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%Rng.
Proof.
intros la lb i len Hlen.
symmetry in Hlen.
rewrite list_nth_polyn_list_convol_mul_aux; [ idtac | assumption ].
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem summation_mul_list_nth_polyn_list_convol_mul : ∀ la lb lc k,
  (Σ (i = 0, k),
     List.nth i la 0 *
     List.nth (k - i)
       (polyn_list_convol_mul lb lc 0 (length lb + length lc - 1))
       0 =
   Σ (i = 0, k),
     List.nth i la 0 *
     Σ (j = 0, k - i),
       List.nth j lb 0 * List.nth (k - i - j) lc 0)%Rng.
Proof.
intros la lb lc k.
apply summation_compat; intros i (_, Hi).
f_equal.
rewrite list_nth_polyn_list_convol_mul; reflexivity.
Qed.

Theorem summation_mul_list_nth_polyn_list_convol_mul_2 : ∀ la lb lc k,
   (Σ (i = 0, k),
      List.nth i lc 0 *
      List.nth (k - i)
        (polyn_list_convol_mul la lb 0 (length la + length lb - 1))  0 =
    Σ (i = 0, k),
      List.nth (k - i) lc 0 *
      Σ (j = 0, i),
        List.nth j la 0 * List.nth (i - j) lb 0)%Rng.
Proof.
intros la lb lc k.
rewrite summation_rtl.
apply summation_compat; intros i (_, Hi).
rewrite Nat.add_0_r.
f_equal.
rewrite Nat_sub_sub_distr; [ idtac | easy ].
rewrite Nat.sub_diag.
apply list_nth_polyn_list_convol_mul; reflexivity.
Qed.

Lemma polyn_list_norm_mul_assoc : ∀ la lb lc,
  polyn_list_norm (la * (lb * lc))%polyn_list = polyn_list_norm (la * lb * lc)%polyn_list.
Proof.
intros la lb lc.
symmetry; rewrite polyn_list_mul_comm.
unfold polyn_list_mul.
destruct lc as [| c]. {
  destruct la as [| a]; [ easy | now destruct lb ].
}
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
apply list_nth_polyn_list_eq; intros k.
remember (polyn_list_convol_mul la' lb' 0 (length la' + length lb' - 1)) as ld
  eqn:Hld.
remember (polyn_list_convol_mul lb' lc' 0 (length lb' + length lc' - 1)) as le
  eqn:Hle.
symmetry in Hld, Hle.
destruct ld as [| d]. {
  destruct le as [| e]; [ easy | cbn ].
  rewrite match_id.
  move e before c.
  apply eq_polyn_list_convol_mul_nil in Hld.
  apply Nat.sub_0_le in Hld.
  remember (length la' + length lb') as len eqn:Hlen.
  symmetry in Hlen.
  destruct len. {
    apply Nat.eq_add_0 in Hlen.
    now subst la'.
  }
  destruct len; [ clear Hld | flia Hld ].
  apply Nat.eq_add_1 in Hlen.
  destruct Hlen as [Hlen| Hlen]; [ now rewrite Hlb' in Hlen | ].
  now rewrite Hla' in Hlen.
}
destruct le as [| e]. {
  cbn; rewrite match_id.
  move d before c.
  apply eq_polyn_list_convol_mul_nil in Hle.
  apply Nat.sub_0_le in Hle.
  remember (length lb' + length lc') as len eqn:Hlen.
  symmetry in Hlen.
  destruct len. {
    apply Nat.eq_add_0 in Hlen.
    now subst lb'.
  }
  destruct len; [ clear Hle | flia Hle ].
  apply Nat.eq_add_1 in Hlen.
  destruct Hlen as [Hlen| Hlen]; [ now rewrite Hlc' in Hlen | ].
  now rewrite Hlb' in Hlen.
}
rewrite list_nth_polyn_list_convol_mul; [ idtac | reflexivity ].
rewrite list_nth_polyn_list_convol_mul; [ idtac | reflexivity ].
rewrite <- Hld, <- Hle.
rewrite summation_mul_list_nth_polyn_list_convol_mul_2; symmetry.
rewrite summation_mul_list_nth_polyn_list_convol_mul; symmetry.
rewrite <- summation_summation_mul_swap.
rewrite <- summation_summation_mul_swap.
rewrite summation_summation_exch.
rewrite summation_summation_shift.
apply summation_compat; intros i Hi.
apply summation_compat; intros j Hj.
rewrite srng_mul_comm, srng_mul_assoc.
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.sub_add_distr.
reflexivity.
Qed.

Theorem eq_polyn_list_norm_eq_length : ∀ la lb,
  polyn_list_norm la = polyn_list_norm lb
  → length la = length lb
  → la = lb.
Proof.
intros * Hll Hlen.
unfold polyn_list_norm in Hll.
apply (f_equal (@rev α)) in Hll.
do 2 rewrite rev_involutive in Hll.
setoid_rewrite <- rev_length in Hlen.
enough (H : rev la = rev lb). {
  apply (f_equal (@rev α)) in H.
  now do 2 rewrite rev_involutive in H.
}
remember (rev la) as l; clear la Heql; rename l into la.
remember (rev lb) as l; clear lb Heql; rename l into lb.
revert la Hll Hlen.
induction lb as [| b]; intros. {
  now apply length_zero_iff_nil in Hlen.
}
destruct la as [| a]; [ easy | ].
cbn in Hll, Hlen.
apply Nat.succ_inj in Hlen.
destruct (srng_eq_dec a 0%Rng) as [Haz| Haz]. {
  destruct (srng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
    subst a b; f_equal.
    now apply IHlb.
  }
  exfalso; clear - Hbz Hll Hlen.
  assert (H : length la ≤ length lb) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction la as [| a]; [ easy | ].
  cbn in Hll.
  destruct (srng_eq_dec a 0%Rng) as [Haz| Haz]. {
    cbn in Hlen.
    clear a Haz.
    apply IHla; [ easy | flia Hlen ].
  }
  rewrite Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
destruct (srng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
  exfalso; clear b Hbz.
  clear - Haz Hll Hlen.
  assert (H : length lb ≤ length la) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction lb as [| b]; [ easy | ].
  cbn in Hll.
  destruct (srng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
    cbn in Hlen.
    clear b Hbz.
    apply IHlb; [ easy | flia Hlen ].
  }
  rewrite <- Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
easy.
Qed.

Theorem polyn_list_convol_mul_length : ∀ la lb i len,
  length (polyn_list_convol_mul la lb i len) = len.
Proof.
intros.
revert la lb i.
induction len; intros; [ easy | ].
cbn.
now rewrite IHlen.
Qed.

Theorem polyn_list_mul_assoc : ∀ la lb lc,
  (la * (lb * lc))%polyn_list = ((la * lb) * lc)%polyn_list.
Proof.
intros.
apply eq_polyn_list_norm_eq_length; [ apply polyn_list_norm_mul_assoc | ].
unfold "*"%polyn_list.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]. {
  now destruct (polyn_list_convol_mul _ _ _ _).
}
cbn.
do 4 (rewrite Nat.add_succ_r; cbn); f_equal.
do 2 rewrite srng_add_0_r.
do 4 rewrite polyn_list_convol_mul_length.
apply Nat.add_assoc.
Qed.

Theorem polyn_list_convol_mul_0_l : ∀ la lb i len,
  (∀ i, nth i la 0%Rng = 0%Rng)
  → polyn_list_norm (polyn_list_convol_mul la lb i len) = [].
Proof.
intros * Ha.
revert i.
induction len; intros; [ easy | ].
cbn - [ summation ].
rewrite strip_0s_app.
remember (strip_0s (rev _)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  rewrite all_0_summation_0. 2: {
    intros j Hj.
    now rewrite Ha, srng_mul_0_l.
  }
  cbn.
  now destruct (srng_eq_dec 0%Rng 0%Rng).
}
unfold polyn_list_norm in IHlen.
specialize (IHlen (S i)).
rewrite Hlc in IHlen.
now apply List_eq_rev_nil in IHlen.
Qed.

Theorem all_0_all_rev_0 : ∀ la,
  (∀ i, nth i la 0%Rng = 0%Rng)
  ↔ (∀ i, nth i (rev la) 0%Rng = 0%Rng).
Proof.
intros *.
split; intros H i. {
  destruct (lt_dec i (length la)) as [Hila| Hila]. {
    rewrite rev_nth; [ apply H | easy ].
  }
  apply nth_overflow; rewrite rev_length; flia Hila.
} {
  destruct (lt_dec i (length la)) as [Hila| Hila]. {
    rewrite <- (rev_involutive la).
    rewrite rev_nth; [ apply H | now rewrite rev_length ].
  }
  apply nth_overflow; flia Hila.
}
Qed.

Theorem eq_strip_0s_nil : ∀ la,
  strip_0s la = [] ↔ ∀ i, nth i la 0%Rng = 0%Rng.
Proof.
intros.
split. {
  intros Hla *.
  revert i.
  induction la as [| a]; intros; [ now destruct i | cbn ].
  cbn in Hla.
  destruct (srng_eq_dec a 0%Rng) as [Haz| Haz]; [ | easy ].
  destruct i; [ easy | ].
  now apply IHla.
} {
  intros Hla.
  induction la as [| a]; [ easy | cbn ].
  destruct (srng_eq_dec a 0%Rng) as [Haz| Haz]. {
    apply IHla.
    intros i.
    now specialize (Hla (S i)).
  }
  now specialize (Hla 0).
}
Qed.

Theorem eq_strip_0s_rev_nil : ∀ la,
  strip_0s (rev la) = [] ↔ ∀ i, nth i la 0%Rng = 0%Rng.
Proof.
intros.
split; intros Hla. {
  apply all_0_all_rev_0.
  now apply eq_strip_0s_nil.
} {
  apply eq_strip_0s_nil.
  apply all_0_all_rev_0.
  now rewrite rev_involutive.
}
Qed.

Lemma polyn_list_convol_mul_cons_with_0_l : ∀ a la lb i len,
  (∀ i, nth i la 0%Rng = 0%Rng)
  → polyn_list_convol_mul (a :: la) lb i len = polyn_list_convol_mul [a] lb i len.
Proof.
intros * Hla.
revert i.
induction len; intros; [ easy | ].
cbn - [ summation ].
f_equal; [ | apply IHlen ].
apply summation_compat.
intros j Hj.
destruct j; [ easy | ].
rewrite match_id.
now rewrite Hla.
Qed.

Theorem polyn_list_convol_mul_succ : ∀ la lb i len,
  polyn_list_convol_mul la lb i (S len) =
  polyn_list_convol_mul la lb i len ++
    [Σ (j = 0, i + len),
     List.nth j la 0 * List.nth (i + len - j) lb 0]%Rng.
Proof.
intros.
cbn - [ summation ].
revert i.
induction len; intros. {
  now rewrite Nat.add_0_r.
}
cbn - [ summation ].
f_equal.
specialize (IHlen (S i)).
cbn - [ summation ] in IHlen.
rewrite Nat.add_succ_r.
apply IHlen.
Qed.

Theorem polyn_list_norm_app_0_r : ∀ la lb,
  (∀ i, nth i lb 0%Rng = 0%Rng)
  → polyn_list_norm la = polyn_list_norm (la ++ lb).
Proof.
intros * Hlb.
unfold polyn_list_norm; f_equal.
induction la as [| a]. {
  cbn; symmetry.
  induction lb as [| b]; [ easy | cbn ].
  rewrite strip_0s_app.
  rewrite IHlb. 2: {
    intros i.
    now specialize (Hlb (S i)).
  }
  specialize (Hlb 0); cbn in Hlb; rewrite Hlb; cbn.
  now destruct (srng_eq_dec 0%Rng 0%Rng).
}
cbn.
do 2 rewrite strip_0s_app.
now rewrite IHla.
Qed.

Theorem polyn_list_convol_mul_more : ∀ n la lb i len,
  length la + length lb - 1 ≤ i + len
  → polyn_list_norm (polyn_list_convol_mul la lb i len) =
    polyn_list_norm (polyn_list_convol_mul la lb i (len + n)).
Proof.
intros.
induction n; [ rewrite Nat.add_0_r; reflexivity | idtac ].
rewrite Nat.add_succ_r.
rewrite polyn_list_convol_mul_succ.
rewrite IHn.
apply polyn_list_norm_app_0_r.
intros j.
rewrite all_0_summation_0. {
  destruct j; [ easy | now destruct j ].
}
clear j.
intros j (_, Hj).
apply srng_mul_eq_0.
destruct (le_dec (length la) j) as [H1| H1]. {
  now left; rewrite List.nth_overflow.
} {
  apply Nat.nle_gt in H1.
  destruct (le_dec (length lb) (i + (len + n) - j)) as [H2| H2]. {
    now right; rewrite nth_overflow.
  } {
    exfalso; apply H2; clear H2.
    flia H H1.
  }
}
Qed.

Theorem all_0_polyn_list_norm_nil : ∀ la,
  (∀ i, nth i la 0%Rng = 0%Rng)
  → polyn_list_norm la = [].
Proof.
intros * Hla.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  destruct (srng_eq_dec a 0%Rng) as [H1| H1]; [ easy | exfalso ].
  now specialize (Hla 0); cbn in Hla.
}
exfalso.
assert (H : strip_0s (rev la) = []). {
  clear - Hla.
  apply eq_strip_0s_nil.
  intros i.
  destruct (lt_dec i (length la)) as [Hila| Hila]. {
    rewrite rev_nth; [ | easy ].
    specialize (Hla (S (length la - S i))).
    now cbn in Hla.
  }
  apply Nat.nlt_ge in Hila.
  rewrite nth_overflow; [ easy | now rewrite rev_length ].
}
now rewrite Hlb in H.
Qed.

Theorem polyn_list_norm_repeat_0 : ∀ la,
  la = polyn_list_norm la ++ repeat 0%Rng (length la - length (polyn_list_norm la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  destruct (srng_eq_dec a 0%Rng) as [Haz| Haz]. {
    cbn; subst a; f_equal.
    assert (H : polyn_list_norm la = []). {
      apply all_0_polyn_list_norm_nil.
      intros i.
      specialize (proj1 (eq_strip_0s_nil _) Hlb) as H1.
      destruct (lt_dec i (length la)) as [Hila| Hila]. {
        replace la with (rev (rev la)) by apply rev_involutive.
        rewrite rev_nth; rewrite rev_length; [ | easy ].
        apply H1.
      }
      apply Nat.nlt_ge in Hila.
      now rewrite nth_overflow.
    }
    rewrite H in IHla; cbn in IHla.
    now rewrite Nat.sub_0_r in IHla.
  } {
    cbn; f_equal.
    assert (H : polyn_list_norm la = []). {
      apply all_0_polyn_list_norm_nil.
      intros i.
      specialize (proj1 (eq_strip_0s_nil _) Hlb) as H1.
      destruct (lt_dec i (length la)) as [Hila| Hila]. {
        replace la with (rev (rev la)) by apply rev_involutive.
        rewrite rev_nth; rewrite rev_length; [ | easy ].
        apply H1.
      }
      apply Nat.nlt_ge in Hila.
      now rewrite nth_overflow.
    }
    now rewrite H in IHla; cbn in IHla.
  }
} {
  cbn.
  rewrite rev_app_distr; cbn; f_equal.
  replace (rev lb ++ [b]) with (rev (b :: lb)) by easy.
  rewrite <- Hlb.
  now rewrite fold_polyn_list_norm.
}
Qed.

Theorem polyn_list_convol_mul_app_rep_0_l : ∀ la lb i len n,
  polyn_list_norm (polyn_list_convol_mul (la ++ repeat 0%Rng n) lb i len) =
  polyn_list_norm (polyn_list_convol_mul la lb i len).
Proof.
intros.
revert la i len.
induction n; intros. {
  now cbn; rewrite app_nil_r.
}
cbn.
replace (0%Rng :: repeat 0%Rng n) with ([0%Rng] ++ repeat 0%Rng n) by easy.
rewrite app_assoc.
rewrite IHn; clear n IHn.
revert la i.
induction len; intros; [ easy | ].
cbn - [ summation ].
do 2 rewrite strip_0s_app.
rewrite <- (rev_involutive (strip_0s _)).
rewrite fold_polyn_list_norm.
rewrite <- (rev_involutive (strip_0s (rev _))).
rewrite fold_polyn_list_norm.
rewrite IHlen.
remember (rev (polyn_list_norm _)) as lc eqn:Hlc; symmetry in Hlc.
f_equal.
destruct lc as [| c]. {
  apply List_eq_rev_nil in Hlc.
  f_equal; f_equal.
  apply summation_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. {
    now rewrite app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (nth_overflow la); [ | easy ].
  rewrite app_nth2; [ | easy ].
  destruct (Nat.eq_dec j (length la)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
} {
  f_equal; f_equal.
  apply summation_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. {
    now rewrite app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (nth_overflow la); [ | easy ].
  rewrite app_nth2; [ | easy ].
  destruct (Nat.eq_dec j (length la)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
}
Qed.

Theorem polyn_list_norm_cons_norm : ∀ a la lb i len,
  length (a :: la) + length lb - 1 ≤ i + len
  → polyn_list_norm (polyn_list_convol_mul (a :: polyn_list_norm la) lb i len) =
    polyn_list_norm (polyn_list_convol_mul (a :: la) lb i len).
Proof.
intros * Hlen.
rewrite (polyn_list_norm_repeat_0 la) at 2.
rewrite app_comm_cons.
now rewrite polyn_list_convol_mul_app_rep_0_l.
Qed.

Theorem polyn_list_norm_length_le : ∀ la, length (polyn_list_norm la) ≤ length la.
Proof.
intros.
rewrite (polyn_list_norm_repeat_0 la) at 2.
rewrite app_length; flia.
Qed.

Theorem nth_polyn_list_add : ∀ i la lb,
  nth i (la + lb)%polyn_list 0%Rng = (nth i la 0 + nth i lb 0)%Rng.
Proof.
intros.
revert i lb.
induction la as [| a]; intros; cbn. {
  now rewrite match_id, srng_add_0_l.
}
destruct lb as [| b]; cbn. {
  now rewrite match_id, srng_add_0_r.
}
destruct i; [ easy | ].
apply IHla.
Qed.

Theorem polyn_list_mul_norm_idemp_l : ∀ la lb,
  polyn_list_norm (polyn_list_norm la * lb)%polyn_list = polyn_list_norm (la * lb)%polyn_list.
Proof.
intros.
unfold "*"%polyn_list; cbn.
destruct la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  destruct (srng_eq_dec a 0%Rng) as [Haz| Haz]. {
    cbn.
    destruct lb as [| b]; [ easy | cbn ].
    rewrite polyn_list_convol_mul_0_l; [ easy | ].
    intros i; cbn.
    destruct i; [ easy | ].
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
  cbn.
  destruct lb as [| b]; [ easy | ].
  remember (b :: lb) as ld eqn:Hld; symmetry in Hld.
  do 2 rewrite Nat.sub_0_r.
  rewrite fold_polyn_list_norm.
  rewrite (polyn_list_convol_mul_cons_with_0_l _ la). 2: {
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
  apply polyn_list_convol_mul_more; cbn.
  now rewrite Nat.sub_0_r.
}
rewrite rev_app_distr; cbn.
rewrite fold_polyn_list_norm.
destruct lb as [| b]; [ easy | ].
remember (b :: lb) as d eqn:Hd.
replace (rev lc ++ [c]) with (rev (c :: lc)) by easy.
rewrite <- Hlc.
rewrite fold_polyn_list_norm.
do 2 rewrite Nat.sub_0_r.
clear c lc b lb Hlc Hd.
rename d into lb.
rewrite (polyn_list_convol_mul_more (length la - length (polyn_list_norm la))). 2: {
  now cbn; rewrite Nat.sub_0_r.
}
rewrite (Nat.add_comm _ (length lb)).
rewrite <- Nat.add_assoc.
rewrite Nat.add_sub_assoc; [ | apply polyn_list_norm_length_le ].
rewrite (Nat.add_comm _ (length la)).
rewrite Nat.add_sub.
rewrite Nat.add_comm.
apply polyn_list_norm_cons_norm.
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem polyn_list_mul_norm_idemp_r : ∀ la lb,
  polyn_list_norm (la * polyn_list_norm lb)%polyn_list = polyn_list_norm (la * lb)%polyn_list.
Proof.
intros.
setoid_rewrite polyn_list_mul_comm.
apply polyn_list_mul_norm_idemp_l.
Qed.

Theorem polyn_mul_assoc : ∀ p1 p2 p3,
  (p1 * (p2 * p3))%pol = ((p1 * p2) * p3) %pol.
Proof.
intros.
unfold "*"%pol.
remember (polyn_list p1) as la.
remember (polyn_list p2) as lb.
remember (polyn_list p3) as lc.
clear p1 Heqla.
clear p2 Heqlb.
clear p3 Heqlc.
unfold polyn_norm at 1 3.
apply eq_polyn_eq; cbn.
rewrite polyn_list_mul_norm_idemp_l.
rewrite polyn_list_mul_norm_idemp_r.
now rewrite polyn_list_mul_assoc.
Qed.

Theorem polyn_list_mul_mul_swap : ∀ la lb lc,
  polyn_list_mul (polyn_list_mul la lb) lc = polyn_list_mul (polyn_list_mul la lc) lb.
Proof.
intros la lb lc.
do 2 rewrite <- polyn_list_mul_assoc.
now rewrite (polyn_list_mul_comm lb).
Qed.

Fixpoint polyn_list_convol_mul_add al1 al2 al3 i len :=
  match len with
  | O => []
  | S len1 =>
      (Σ (j = 0, i),
       List.nth j al1 0 *
       (List.nth (i - j) al2 0 + List.nth (i - j) al3 0))%Rng ::
       polyn_list_convol_mul_add al1 al2 al3 (S i) len1
  end.

(* *)

Theorem list_nth_add : ∀ k la lb,
  (List.nth k (polyn_list_add la lb) 0 =
   List.nth k la 0 + List.nth k lb 0)%Rng.
Proof.
intros k la lb.
revert la lb.
induction k; intros.
 destruct la as [| a]; simpl; [ rewrite srng_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite srng_add_0_r; reflexivity | idtac ].
 reflexivity.

 destruct la as [| a]; simpl; [ rewrite srng_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite srng_add_0_r; reflexivity | idtac ].
 apply IHk.
Qed.

Theorem polyn_list_convol_mul_polyn_list_add : ∀ la lb lc i len,
  eq
    (polyn_list_convol_mul la (polyn_list_add lb lc) i len)
    (polyn_list_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
apply summation_compat; intros j (_, Hj).
f_equal.
rewrite list_nth_add; reflexivity.
Qed.

Theorem polyn_list_add_polyn_list_convol_mul : ∀ la lb lc i len,
  eq
     (polyn_list_add
        (polyn_list_convol_mul la lb i len)
        (polyn_list_convol_mul la lc i len))
     (polyn_list_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
rewrite <- summation_add_distr.
apply summation_compat; intros j (_, Hj).
rewrite srng_mul_add_distr_l; reflexivity.
Qed.

Lemma polyn_list_norm_mul_add_distr_l : ∀ la lb lc,
  polyn_list_norm (la * (lb + lc))%polyn_list = polyn_list_norm (la * lb + la * lc)%polyn_list.
Proof.
intros la lb lc.
unfold polyn_list_mul.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]; [ now cbn; rewrite polyn_list_add_0_r | ].
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
remember (length la' + length (polyn_list_add lb' lc') - 1) as labc.
remember (length la' + length lb' - 1) as lab.
remember (length la' + length lc' - 1) as lac.
rewrite Heqlabc.
remember (lb' + lc')%polyn_list as lbc.
symmetry in Heqlbc.
destruct lbc as [| bc]. {
  cbn.
  now subst lb' lc'.
}
rewrite <- Heqlbc in Heqlabc |-*.
rewrite polyn_list_convol_mul_more with (n := (lab + lac)%nat). 2: {
  subst; flia.
}
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite <- polyn_list_add_norm_idemp_l.
rewrite polyn_list_convol_mul_more with (n := (labc + lac)%nat); [ | flia ].
rewrite <- Heqlab.
rewrite polyn_list_add_norm_idemp_l.
rewrite polyn_list_add_comm.
rewrite <- polyn_list_add_norm_idemp_l.
rewrite Heqlac.
rewrite polyn_list_convol_mul_more with (n := (labc + lab)%nat); [ | flia ].
rewrite polyn_list_add_norm_idemp_l.
rewrite <- Heqlac.
rewrite Nat.add_comm.
rewrite polyn_list_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite polyn_list_convol_mul_polyn_list_add.
rewrite polyn_list_add_polyn_list_convol_mul.
reflexivity.
Qed.

Theorem polyn_list_add_length : ∀ la lb,
  length (la + lb)%polyn_list = max (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | ].
cbn.
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
Qed.

Lemma polyn_list_mul_add_distr_l : ∀ la lb lc,
  (la * (lb + lc))%polyn_list = (la * lb + la * lc)%polyn_list.
Proof.
intros la lb lc.
apply eq_polyn_list_norm_eq_length; [ apply polyn_list_norm_mul_add_distr_l | ].
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]. {
  now cbn; rewrite polyn_list_add_0_r.
}
cbn.
do 3 (rewrite Nat.add_succ_r; cbn); f_equal.
rewrite polyn_list_convol_mul_length.
do 2 rewrite polyn_list_add_length; cbn.
do 2 rewrite polyn_list_convol_mul_length.
now rewrite Nat.add_max_distr_l.
Qed.

Theorem polyn_mul_add_distr_l : ∀ pa pb pc,
  (pa * (pb + pc))%pol = (pa * pb + pa * pc)%pol.
Proof.
intros.
apply eq_polyn_eq; cbn.
rewrite fold_polyn_list_norm.
rewrite polyn_list_mul_norm_idemp_r.
rewrite polyn_list_add_norm_idemp_l.
rewrite polyn_list_add_norm_idemp_r.
now rewrite polyn_list_mul_add_distr_l.
Qed.

Lemma polyn_list_convol_mul_1_l : ∀ la i len,
  length la = i + len
  → polyn_list_convol_mul [1%Rng] la i len = skipn i la.
Proof.
intros * Hlen.
revert i Hlen.
induction len; intros. {
  rewrite Nat.add_0_r in Hlen; rewrite <- Hlen.
  symmetry; apply skipn_all.
}
cbn - [ summation nth ].
rewrite summation_split_first; [ | flia ].
rewrite all_0_summation_0. 2: {
  intros j Hj.
  destruct j; [ flia Hj | cbn ].
  now rewrite match_id, srng_mul_0_l.
}
rewrite Nat.sub_0_r, srng_add_0_r; cbn.
rewrite srng_mul_1_l.
rewrite IHlen; [ | flia Hlen ].
clear - Hlen.
revert i Hlen.
induction la as [ | a]; intros. {
  cbn in Hlen; flia Hlen.
}
cbn.
destruct i; [ easy | ].
rewrite IHla; [ easy | ].
cbn in Hlen; flia Hlen.
Qed.

Theorem polyn_list_mul_1_l : ∀ la, ([1%Rng] * la)%polyn_list = la.
Proof.
intros la.
unfold polyn_list_mul.
destruct la as [| a]; [ easy | cbn ].
rewrite srng_mul_1_l, srng_add_0_r; f_equal.
now rewrite polyn_list_convol_mul_1_l.
Qed.

Theorem polyn_list_mul_1_r : ∀ la, (la * [1%Rng])%polyn_list = la.
Proof.
intros la.
rewrite polyn_list_mul_comm.
apply polyn_list_mul_1_l.
Qed.

Theorem polyn_mul_1_l : ∀ p, (1 * p)%pol = p.
Proof.
intros (la, polyn_listr).
unfold "*"%pol.
rewrite polyn_list_mul_1_l; cbn.
apply eq_polyn_eq; cbn.
unfold srng_eqb in polyn_listr.
unfold polyn_list_norm.
destruct (srng_eq_dec (last la 1%Rng) 0) as [Hlaz| Hlaz]; [ easy | ].
clear polyn_listr.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  specialize (proj1 (eq_strip_0s_rev_nil _) Hlb) as H1.
  cbn; clear Hlb.
  destruct (srng_eq_dec a 0) as [Haz| Haz]. {
    exfalso; subst a.
    cbn in IHla.
    destruct la as [| a]; [ easy | ].
    remember (a :: la) as lb; cbn in Hlaz; subst lb.
    now specialize (IHla Hlaz).
  }
  cbn in IHla |-*.
  rewrite <- IHla; [ easy | ].
  cbn in Hlaz.
  destruct la as [| a2]; [ | easy ].
  intros; apply srng_1_neq_0.
}
cbn.
rewrite rev_app_distr; cbn; f_equal.
apply IHla.
cbn in Hlaz.
now destruct la.
Qed.

End polyn_list.

Lemma polyn_list_add_opp_l {α} {ro : ring_op α} {sp : semiring_prop} : ∀ la, polyn_list_norm (- la + la)%polyn_list = [].
Proof.
intros.
unfold polyn_list_norm.
apply List_eq_rev_nil.
rewrite rev_involutive.
induction la as [| a]; [ reflexivity | cbn ].
rewrite strip_0s_app.
remember (strip_0s _) as lb eqn:Hlb; symmetry in Hlb.
subst lb.
rewrite IHla; cbn.
rewrite srng_add_opp_l.
now destruct (srng_eq_dec 0 0).
Qed.

Theorem polyn_add_opp_l {α} {ro : ring_op α} {sp : semiring_prop} : ∀ p, (- p + p)%pol = 0%pol.
Proof.
intros p.
unfold "+"%pol; cbn.
apply eq_polyn_eq; cbn.
rewrite polyn_list_add_norm_idemp_l.
apply polyn_list_add_opp_l.
Qed.

Theorem polyn_add_opp_r {α} {ro : ring_op α} {sp : semiring_prop} : ∀ p, (p - p)%pol = 0%pol.
Proof.
intros p.
unfold polyn_sub.
rewrite polyn_add_comm.
apply polyn_add_opp_l.
Qed.

Theorem polyn_1_neq_0 {A} {so : semiring_op T} {sp : semiring_prop} : 1%pol ≠ 0%pol.
Proof. easy. Qed.

Fixpoint polyn_list_eqb {A} {so : semiring_op T} {sp : semiring_prop} la lb :=
  match la with
  | [] =>
      match lb with
      | [] => true
      | _ :: _ => false
      end
  | a :: la' =>
      match lb with
      | [] => false
      | b :: lb' => if srng_eq_dec a b then polyn_list_eqb la' lb' else false
      end
  end.

Theorem polyn_list_eqb_eq {A} {so : semiring_op T} {sp : semiring_prop} : ∀ la lb,
  polyn_list_eqb la lb = true ↔ la = lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | cbn ].
destruct (srng_eq_dec a b) as [Hab| Hab]. {
  subst b.
  split; intros Hll; [ now f_equal; apply IHla | ].
  injection Hll; clear Hll; intros; subst lb.
  now apply IHla.
} {
  split; intros Hll; [ easy | ].
  now injection Hll; intros.
}
Qed.

Theorem polyn_list_eqb_neq {A} {so : semiring_op T} {sp : semiring_prop} : ∀ la lb,
  polyn_list_eqb la lb = false ↔ la ≠ lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | cbn ].
destruct (srng_eq_dec a b) as [Hab| Hab]. {
  subst b.
  split; intros Hll. {
    intros H.
    injection H; clear H; intros; subst lb.
    now apply IHla in Hll.
  } {
    apply IHla.
    intros H; apply Hll.
    now subst lb.
  }
} {
  split; intros Hll; [ | easy ].
  intros H; apply Hab.
  now injection H; intros.
}
Qed.

Lemma polyn_list_eq_dec {A} {so : semiring_op T} {sp : semiring_prop} : ∀ la lb : list A,
  {la = lb} + {la ≠ lb}.
Proof.
intros.
remember (polyn_list_eqb la lb) as lab eqn:Hlab; symmetry in Hlab.
destruct lab. {
  now left; apply polyn_list_eqb_eq.
} {
  now right; apply polyn_list_eqb_neq.
}
Qed.

Theorem polyn_eq_dec {A} {so : semiring_op T} {sp : semiring_prop} : ∀ pa pb : poly _,
  {pa = pb} + {pa ≠ pb}.
Proof.
intros (la, polyn_listr) (lb, lbpr).
destruct (polyn_list_eq_dec la lb) as [Hll| Hll]. {
  left; subst lb.
  now apply eq_polyn_eq.
} {
  right; intros H; apply Hll.
  now injection H.
}
Qed.

Definition polynomial_ring_op {α} {ro : ring_op α} {sp : semiring_prop} :
  ring_op (poly α) :=
  {| srng_zero := polyn_zero;
     srng_one := polyn_one;
     srng_add := polyn_add;
     srng_mul := polyn_mul;
     srng_opp := polyn_opp |}.

Definition polynomial_ring_prop {α} {ro : ring_op α} {sp : semiring_prop} :=
  let _ := polynomial_ring_op in
  {| srng_1_neq_0 := polyn_1_neq_0;
     srng_eq_dec := polyn_eq_dec;
     srng_add_comm := polyn_add_comm;
     srng_add_assoc := polyn_add_assoc;
     srng_add_0_l := polyn_add_0_l;
     srng_add_opp_l := polyn_add_opp_l;
     srng_mul_comm := polyn_mul_comm;
     srng_mul_assoc := polyn_mul_assoc;
     srng_mul_1_l := polyn_mul_1_l;
     srng_mul_add_distr_l := polyn_mul_add_distr_l |}.

(* allows to use ring theorems on polynomials *)
Canonical Structure polynomial_ring_prop.

(* *)

Definition eval_polyn_list {α} {ro : ring_op α} {sp : semiring_prop} la x :=
  (List.fold_right (λ c accu, accu * x + c) 0 la)%Rng.

Definition eval_poly {α} {ro : ring_op α} {sp : semiring_prop} pol :=
  eval_polyn_list (polyn_list pol).
