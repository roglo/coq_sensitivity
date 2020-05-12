(* Fpolynomial.v *)

(* polynomials on a ring *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List ListNotations.

Require Import Misc Ring2 Rsummation.

(* definition of a polynomial *)

Definition rng_eqb {A} {rng : ring A} (a b : A) :=
  if rng_eq_dec a b then true else false.

(* (lap : list as polynomial) *)
Record poly A {rng : ring A} := mkpoly
  { lap : list A;
    lap_prop : rng_eqb (last lap 1%Rng) 0%Rng = false }.

Arguments lap {A} {rng}.

Theorem eq_poly_eq {A} {rng : ring A} : ∀ p1 p2, p1 = p2 ↔ lap p1 = lap p2.
Proof.
intros.
split; [ now intros; subst p1 | ].
intros Hll.
destruct p1 as (la, lapr).
destruct p2 as (lb, lbpr).
cbn in Hll; subst la; f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem eq_poly_prop {A} {rng : ring A} : ∀ la,
  rng_eqb (last la 1%Rng) 0%Rng = false ↔ last la 1%Rng ≠ 0%Rng.
Proof.
intros.
unfold rng_eqb.
now destruct (rng_eq_dec (last la 1%Rng) 0%Rng).
Qed.

Arguments mkpoly {_} {_}.

Theorem lap_1_0_prop {A} {rng : ring A} :
  rng_eqb (last [] 1%Rng) 0%Rng = false.
Proof.
cbn.
unfold rng_eqb.
destruct (rng_eq_dec 1%Rng 0%Rng); [ | easy ].
now apply rng_1_neq_0 in e.
Qed.

Definition poly_zero {α} {r : ring α} := mkpoly [] lap_1_0_prop.
Definition poly_one {α} {r : ring α} := mkpoly [1%Rng] lap_1_0_prop.

(* normalization *)

Fixpoint strip_0s {A} {rng : ring A} la :=
  match la with
  | [] => []
  | a :: la' => if rng_eq_dec a 0%Rng then strip_0s la' else la
  end.

Lemma strip_0s_app {A} {rng : ring A} : ∀ la lb,
  strip_0s (la ++ lb) =
  match strip_0s la with
  | [] => strip_0s lb
  | lc => lc ++ lb
  end.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]; [ apply IHla | easy ].
Qed.

Definition lap_norm {A} {rng : ring A} la := rev (strip_0s (rev la)).

Theorem poly_norm_prop {A} {rng : ring A} : ∀ la,
  last (lap_norm la) 1%Rng ≠ 0%Rng.
Proof.
intros.
unfold lap_norm.
induction la as [| a]; [ apply rng_1_neq_0 | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; cbn. {
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]; [ apply rng_1_neq_0 | easy ].
}
cbn in IHla.
rewrite List_last_app.
now rewrite List_last_app in IHla.
Qed.

Definition poly_norm {A} {rng : ring A} la :=
  mkpoly (lap_norm la) (proj2 (eq_poly_prop _) (poly_norm_prop la)).

(**)
Require Import ZArith.

Theorem Z_1_neq_0 : (1 ≠ 0)%Z.
Proof. easy. Qed.

Definition Z_ring : ring Z :=
  {| rng_zero := 0%Z;
     rng_one := 1%Z;
     rng_add := Z.add;
     rng_mul := Z.mul;
     rng_opp := Z.opp;
     rng_1_neq_0 := Z_1_neq_0;
     rng_eq_dec := Z.eq_dec;
     rng_add_comm := Z.add_comm;
     rng_add_assoc := Z.add_assoc;
     rng_add_0_l := Z.add_0_l;
     rng_add_opp_l := Z.add_opp_diag_l;
     rng_mul_comm := Z.mul_comm;
     rng_mul_assoc := Z.mul_assoc;
     rng_mul_1_l := Z.mul_1_l;
     rng_mul_add_distr_l := Z.mul_add_distr_l |}.

(* allows to use ring theorems on Z *)
Canonical Structure Z_ring.

(*
Compute (@lap_norm Z Z_ring [3; 4; 0; 5; 0; 0; 0]%Z).
*)
(**)

(* addition *)

Fixpoint lap_add {α} {r : ring α} al1 al2 :=
  match al1 with
  | [] => al2
  | a1 :: bl1 =>
      match al2 with
      | [] => al1
      | a2 :: bl2 => (a1 + a2)%Rng :: lap_add bl1 bl2
      end
  end.

Definition lap_opp {α} {r : ring α} la := List.map rng_opp la.
Definition lap_sub {A} {rng : ring A} la lb := lap_add la (lap_opp lb).

Definition poly_add {A} {rng : ring A} p1 p2 :=
  poly_norm (lap_add (lap p1) (lap p2)).

Definition poly_opp {α} {r : ring α} pol :=
  poly_norm (lap_opp (lap pol)).

Definition poly_sub {α} {r : ring α} p1 p2 :=
  poly_add p1 (poly_opp p2).

(*
Compute (@poly_add Z Z_ring (poly_norm [3;4;5]%Z) (poly_norm [2;3;-4;5]%Z)).
Compute (@poly_add Z Z_ring (poly_norm [3;4;5]%Z) (poly_norm [2;3;-5]%Z)).
*)

(* multiplication *)

Fixpoint lap_convol_mul {α} {r : ring α} al1 al2 i len :=
  match len with
  | O => []
  | S len1 =>
      (Σ (j = 0, i), List.nth j al1 0 * List.nth (i - j) al2 0)%Rng ::
      lap_convol_mul al1 al2 (S i) len1
  end.

Definition lap_mul {α} {R : ring α} la lb :=
  match la with
  | [] => []
  | _ =>
      match lb with
      | [] => []
      | _ => lap_convol_mul la lb 0 (length la + length lb - 1)
      end
  end.

Definition poly_mul {A} {rng : ring A} p1 p2 :=
  poly_norm (lap_mul (lap p1) (lap p2)).

(*
Compute (@lap_mul Z Z_ring [3;4;5]%Z [2;3;-4;5]%Z).
Compute (@poly_mul Z Z_ring (poly_norm [3;4;5]%Z) (poly_norm [2;3;-4;5]%Z)).
*)

(* power *)

Fixpoint lap_power {α} {r : ring α} la n :=
  match n with
  | O => [1%Rng]
  | S m => lap_mul la (lap_power la m)
  end.

Definition poly_power {A} {rng : ring A} pol n :=
  poly_norm (lap_power (lap pol) n).

(*
Compute (@poly_power Z Z_ring (poly_norm [1; -1]%Z) 4).
*)

(* composition *)

Definition lap_compose {α} {r : ring α} la lb :=
  List.fold_right (λ c accu, lap_add (lap_mul accu lb) [c]) [] la.

Definition lap_compose2 {α} {r : ring α} la lb :=
  List.fold_right
    (λ i accu,
     lap_add accu (lap_mul [List.nth i la 0] (lap_power lb i)))%Rng
    [] (List.seq 0 (length la)).

(* *)

Fixpoint list_pad {α} n (zero : α) rem :=
  match n with
  | O => rem
  | S n1 => zero :: list_pad n1 zero rem
  end.

Theorem xpow_norm {A} {rng : ring A} : ∀ i,
  rng_eqb (last (repeat 0%Rng i ++ [1%Rng]) 1%Rng) 0%Rng = false.
Proof.
intros.
rewrite List_last_app.
unfold rng_eqb.
destruct (rng_eq_dec 1 0) as [H| H]; [ | easy ].
now apply rng_1_neq_0 in H.
Qed.

Definition xpow {α} {r : ring α} i :=
  mkpoly (repeat 0%Rng i ++ [1%Rng]) (xpow_norm i).

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.
Notation "1" := [1%Rng] : lap_scope.
Notation "- a" := (lap_opp a) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
Notation "a ^ b" := (lap_power a b) : lap_scope.

Definition list_nth_def_0 {α} {R : ring α} n l := List.nth n l 0%Rng.

Declare Scope poly_scope.
Delimit Scope poly_scope with pol.
Notation "0" := poly_zero : poly_scope.
Notation "1" := poly_one : poly_scope.
Notation "- a" := (poly_opp a) : poly_scope.
Notation "a + b" := (poly_add a b) : poly_scope.
Notation "a - b" := (poly_sub a b) : poly_scope.
Notation "a * b" := (poly_mul a b) : poly_scope.
Notation "'ⓧ' ^ a" := (xpow a) (at level 30, format "'ⓧ' ^ a") : poly_scope.
Notation "'ⓧ'" := (xpow 1) (at level 30, format "'ⓧ'") : poly_scope.

(* *)

Theorem lap_convol_mul_comm : ∀ α (R : ring α) l1 l2 i len,
  lap_convol_mul l1 l2 i len = lap_convol_mul l2 l1 i len.
Proof.
intros α R l1 l2 i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
rewrite summation_rtl.
apply summation_compat; intros j (_, Hj).
rewrite Nat.add_0_r.
rewrite rng_mul_comm.
apply rng_mul_compat; [ idtac | reflexivity ].
rewrite Nat_sub_sub_distr; [ idtac | easy ].
rewrite Nat.sub_diag, Nat.add_0_l; reflexivity.
Qed.

Theorem lap_convol_mul_nil_l : ∀ α (R : ring α) l i len,
  lap_norm (lap_convol_mul [] l i len) = [].
Proof.
intros α R l i len.
unfold lap_norm.
revert i.
induction len; intros; [ reflexivity | ].
cbn - [ summation ].
rewrite all_0_summation_0. {
  rewrite strip_0s_app; cbn.
  specialize (IHlen (S i)).
  apply List_eq_rev_nil in IHlen.
  rewrite IHlen.
  now destruct (rng_eq_dec 0%Rng 0%Rng).
}
intros k (_, Hk).
now rewrite match_id, rng_mul_0_l.
Qed.

Theorem lap_convol_mul_nil_r : ∀ α (R : ring α) l i len,
  lap_norm (lap_convol_mul l [] i len) = [].
Proof.
intros α R l i len.
rewrite lap_convol_mul_comm.
apply lap_convol_mul_nil_l.
Qed.

Theorem list_nth_lap_eq : ∀ α (r : ring α) la lb,
  (∀ i, (List.nth i la 0 = List.nth i lb 0)%Rng)
  → lap_norm la = lap_norm lb.
Proof.
intros α r la lb Hi.
unfold lap_norm; f_equal.
revert lb Hi.
induction la as [| a]; intros. {
  induction lb as [| b]; [ reflexivity | ].
  specialize (Hi 0) as H; cbn in H.
  subst b; cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (rev lb)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]; [ now destruct (rng_eq_dec _ _) | ].
  assert (H : lap_norm [] = lap_norm lb). {
    unfold lap_norm; cbn.
    cbn in IHlb.
    change (rev [] = rev (strip_0s (rev lb))).
    f_equal.
    rewrite Hlc.
    apply IHlb.
    intros i; cbn; rewrite match_id.
    now specialize (Hi (S i)); cbn in Hi.
  }
  cbn in H.
  unfold lap_norm in H.
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
        destruct lb as [| b]; [ now destruct (rng_eq_dec a 0%Rng) | easy ].
      }
      apply IHla.
      cbn in Hlc.
      rewrite strip_0s_app in Hlc; cbn in Hlc.
      remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
      destruct lb as [| b]; [ now destruct (rng_eq_dec a 0%Rng) | easy ].
    }
    cbn.
    destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
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
      rewrite <- IHlb; [ now destruct (rng_eq_dec 0%Rng 0%Rng) | ].
      intros i.
      now specialize (Hlb (S i)).
    }
    destruct lb as [| b]; [ now specialize (Hi 0); cbn in Hi | cbn ].
    rewrite strip_0s_app; cbn.
    remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
    destruct ld as [| d]. {
      destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
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
    destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
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

Theorem fold_lap_norm {A} {rng : ring A} :
  ∀ la, rev (strip_0s (rev la)) = lap_norm la.
Proof. easy. Qed.

Theorem lap_add_0_l {α} {r : ring α} : ∀ la, lap_add [] la = la.
Proof. easy. Qed.

Theorem lap_add_0_r {α} {r : ring α} : ∀ la, lap_add la [] = la.
Proof. intros; now destruct la. Qed.

Theorem poly_add_0_l {α} {r : ring α} : ∀ p, (0 + p)%pol = p.
Proof.
intros (la, lapr).
apply eq_poly_eq; cbn.
apply eq_poly_prop in lapr.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
rewrite <- (rev_involutive (strip_0s _)).
rewrite IHla; cbn. {
  remember (rev la) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| b]. {
    apply List_eq_rev_nil in Hlb; subst la.
    now destruct (rng_eq_dec a 0).
  }
  cbn.
  rewrite rev_app_distr; cbn; f_equal.
  now rewrite <- rev_involutive, Hlb.
} {
  destruct la as [| a2]; [ | easy ].
  apply rng_1_neq_0.
}
Qed.

Theorem lap_mul_0_l {α} {r : ring α} : ∀ la, lap_norm (lap_mul [] la) = [].
Proof. easy. Qed.

Theorem lap_mul_0_r {α} {r : ring α} : ∀ la, lap_norm (lap_mul la []) = [].
Proof. now intros; destruct la. Qed.

Section lap.

Context {α : Type}.
Context {r : ring α}.

Theorem strip_0s_idemp : ∀ la, strip_0s (strip_0s la) = strip_0s la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]; [ easy | cbn ].
now destruct (rng_eq_dec a 0%Rng).
Qed.

Theorem lap_norm_idemp : ∀ la, lap_norm (lap_norm la) = lap_norm la.
Proof.
intros.
unfold lap_norm.
rewrite rev_involutive.
now rewrite strip_0s_idemp.
Qed.

Theorem eq_lap_convol_mul_nil : ∀ la lb i len,
  lap_convol_mul la lb i len = [] → len = 0.
Proof. now intros; induction len. Qed.

(* addition theorems *)

Theorem lap_add_comm : ∀ al1 al2,
  lap_add al1 al2 = lap_add al2 al1.
Proof.
intros al1 al2.
revert al2.
induction al1; intros; [ now destruct al2 | ].
destruct al2; [ easy | cbn ].
now rewrite rng_add_comm, IHal1.
Qed.

Theorem poly_add_comm : ∀ a b, (a + b)%pol = (b + a)%pol.
Proof.
intros.
unfold "+"%pol.
now rewrite lap_add_comm.
Qed.

Theorem lap_add_norm_idemp_l : ∀ la lb,
  lap_norm (lap_norm la + lb)%lap = lap_norm (la + lb)%lap.
Proof.
intros.
unfold lap_norm; f_equal.
revert la.
induction lb as [| b]; intros. {
  do 2 rewrite lap_add_0_r.
  now rewrite rev_involutive, strip_0s_idemp.
}
cbn.
destruct la as [| a]; [ easy | cbn ].
do 2 rewrite strip_0s_app; cbn.
rewrite <- IHlb.
remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  destruct (rng_eq_dec a 0) as [Haz| Haz]. {
    subst a; rewrite rng_add_0_l; cbn.
    now rewrite strip_0s_app.
  }
  cbn.
  now rewrite strip_0s_app.
}
cbn.
rewrite rev_app_distr; cbn.
now rewrite strip_0s_app.
Qed.

Theorem lap_add_norm_idemp_r : ∀ la lb,
  lap_norm (la + lap_norm lb)%lap = lap_norm (la + lb)%lap.
Proof.
intros.
rewrite lap_add_comm, lap_add_norm_idemp_l.
now rewrite lap_add_comm.
Qed.

Theorem lap_add_assoc : ∀ al1 al2 al3,
  lap_add al1 (lap_add al2 al3) = lap_add (lap_add al1 al2) al3.
Proof.
intros al1 al2 al3.
revert al2 al3.
induction al1; intros; [ easy | ].
destruct al2; [ easy | cbn ].
destruct al3; [ easy | cbn ].
rewrite rng_add_assoc.
now rewrite IHal1.
Qed.

Theorem lap_add_add_swap : ∀ la lb lc,
  lap_add (lap_add la lb) lc = lap_add (lap_add la lc) lb.
Proof.
intros la lb lc.
do 2 rewrite <- lap_add_assoc.
now rewrite (lap_add_comm lb).
Qed.

Theorem poly_add_assoc : ∀ pa pb pc,
  (pa + (pb + pc) = (pa + pb) + pc)%pol.
Proof.
intros (la, lapr) (lb, lbpr) (lc, lcpr).
apply eq_poly_eq.
cbn - [ lap_norm ].
rewrite lap_add_norm_idemp_l.
rewrite lap_add_norm_idemp_r.
now rewrite lap_add_assoc.
Qed.

(* multiplication theorems *)

Theorem lap_mul_comm : ∀ a b, lap_mul a b = lap_mul b a.
Proof.
intros la lb.
unfold lap_mul.
destruct la as [| a]; [ now destruct lb | cbn ].
rewrite <- Nat.add_succ_comm; cbn.
rewrite (Nat.add_comm (length lb)).
now rewrite lap_convol_mul_comm.
Qed.

Theorem poly_mul_comm : ∀ pa pb, (pa * pb)%pol = (pb * pa)%pol.
Proof.
intros.
apply eq_poly_eq; cbn.
now rewrite lap_mul_comm.
Qed.

Theorem list_nth_lap_convol_mul_aux : ∀ la lb n i len,
  List.length la + List.length lb - 1 = (i + len)%nat
  → (List.nth n (lap_convol_mul la lb i len) 0%Rng =
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
  rewrite rng_mul_0_l; reflexivity.

  destruct (le_dec (length lb) (n + i - j)) as [H2| H2].
   rewrite rng_mul_comm.
   rewrite List.nth_overflow; [ idtac | assumption ].
   rewrite rng_mul_0_l; reflexivity.

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
Theorem list_nth_lap_convol_mul : ∀ la lb i len,
  len = length la + length lb - 1
  → (List.nth i (lap_convol_mul la lb 0 len) 0 =
     Σ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%Rng.
Proof.
intros la lb i len Hlen.
symmetry in Hlen.
rewrite list_nth_lap_convol_mul_aux; [ idtac | assumption ].
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul : ∀ la lb lc k,
  (Σ (i = 0, k),
     List.nth i la 0 *
     List.nth (k - i)
       (lap_convol_mul lb lc 0 (length lb + length lc - 1))
       0 =
   Σ (i = 0, k),
     List.nth i la 0 *
     Σ (j = 0, k - i),
       List.nth j lb 0 * List.nth (k - i - j) lc 0)%Rng.
Proof.
intros la lb lc k.
apply summation_compat; intros i (_, Hi).
f_equal.
rewrite list_nth_lap_convol_mul; reflexivity.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul_2 : ∀ la lb lc k,
   (Σ (i = 0, k),
      List.nth i lc 0 *
      List.nth (k - i)
        (lap_convol_mul la lb 0 (length la + length lb - 1))  0 =
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
apply list_nth_lap_convol_mul; reflexivity.
Qed.

Lemma lap_norm_mul_assoc : ∀ la lb lc,
  lap_norm (la * (lb * lc))%lap = lap_norm (la * lb * lc)%lap.
Proof.
intros la lb lc.
symmetry; rewrite lap_mul_comm.
unfold lap_mul.
destruct lc as [| c]. {
  destruct la as [| a]; [ easy | now destruct lb ].
}
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
apply list_nth_lap_eq; intros k.
remember (lap_convol_mul la' lb' 0 (length la' + length lb' - 1)) as ld
  eqn:Hld.
remember (lap_convol_mul lb' lc' 0 (length lb' + length lc' - 1)) as le
  eqn:Hle.
symmetry in Hld, Hle.
destruct ld as [| d]. {
  destruct le as [| e]; [ easy | cbn ].
  rewrite match_id.
  move e before c.
  apply eq_lap_convol_mul_nil in Hld.
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
  apply eq_lap_convol_mul_nil in Hle.
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
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite <- Hld, <- Hle.
rewrite summation_mul_list_nth_lap_convol_mul_2; symmetry.
rewrite summation_mul_list_nth_lap_convol_mul; symmetry.
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

Theorem eq_lap_norm_eq_length : ∀ la lb,
  lap_norm la = lap_norm lb
  → length la = length lb
  → la = lb.
Proof.
intros * Hll Hlen.
unfold lap_norm in Hll.
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
destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
  destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
    subst a b; f_equal.
    now apply IHlb.
  }
  exfalso; clear - Hbz Hll Hlen.
  assert (H : length la ≤ length lb) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction la as [| a]; [ easy | ].
  cbn in Hll.
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
    cbn in Hlen.
    clear a Haz.
    apply IHla; [ easy | flia Hlen ].
  }
  rewrite Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
  exfalso; clear b Hbz.
  clear - Haz Hll Hlen.
  assert (H : length lb ≤ length la) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction lb as [| b]; [ easy | ].
  cbn in Hll.
  destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
    cbn in Hlen.
    clear b Hbz.
    apply IHlb; [ easy | flia Hlen ].
  }
  rewrite <- Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
easy.
Qed.

Theorem lap_convol_mul_length : ∀ la lb i len,
  length (lap_convol_mul la lb i len) = len.
Proof.
intros.
revert la lb i.
induction len; intros; [ easy | ].
cbn.
now rewrite IHlen.
Qed.

Theorem lap_mul_assoc : ∀ la lb lc,
  (la * (lb * lc))%lap = ((la * lb) * lc)%lap.
Proof.
intros.
apply eq_lap_norm_eq_length; [ apply lap_norm_mul_assoc | ].
unfold "*"%lap.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]. {
  now destruct (lap_convol_mul _ _ _ _).
}
cbn.
do 4 (rewrite Nat.add_succ_r; cbn); f_equal.
do 2 rewrite rng_add_0_r.
do 4 rewrite lap_convol_mul_length.
apply Nat.add_assoc.
Qed.

Theorem lap_convol_mul_0_l : ∀ la lb i len,
  (∀ i, nth i la 0%Rng = 0%Rng)
  → lap_norm (lap_convol_mul la lb i len) = [].
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
    now rewrite Ha, rng_mul_0_l.
  }
  cbn.
  now destruct (rng_eq_dec 0%Rng 0%Rng).
}
unfold lap_norm in IHlen.
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
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]; [ | easy ].
  destruct i; [ easy | ].
  now apply IHla.
} {
  intros Hla.
  induction la as [| a]; [ easy | cbn ].
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
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

Lemma lap_convol_mul_cons_with_0_l : ∀ a la lb i len,
  (∀ i, nth i la 0%Rng = 0%Rng)
  → lap_convol_mul (a :: la) lb i len = lap_convol_mul [a] lb i len.
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

Theorem lap_convol_mul_succ : ∀ la lb i len,
  lap_convol_mul la lb i (S len) =
  lap_convol_mul la lb i len ++
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

Theorem lap_norm_app_0_r : ∀ la lb,
  (∀ i, nth i lb 0%Rng = 0%Rng)
  → lap_norm la = lap_norm (la ++ lb).
Proof.
intros * Hlb.
unfold lap_norm; f_equal.
induction la as [| a]. {
  cbn; symmetry.
  induction lb as [| b]; [ easy | cbn ].
  rewrite strip_0s_app.
  rewrite IHlb. 2: {
    intros i.
    now specialize (Hlb (S i)).
  }
  specialize (Hlb 0); cbn in Hlb; rewrite Hlb; cbn.
  now destruct (rng_eq_dec 0%Rng 0%Rng).
}
cbn.
do 2 rewrite strip_0s_app.
now rewrite IHla.
Qed.

Theorem lap_convol_mul_more : ∀ n la lb i len,
  length la + length lb - 1 ≤ i + len
  → lap_norm (lap_convol_mul la lb i len) =
    lap_norm (lap_convol_mul la lb i (len + n)).
Proof.
intros.
induction n; [ rewrite Nat.add_0_r; reflexivity | idtac ].
rewrite Nat.add_succ_r.
rewrite lap_convol_mul_succ.
rewrite IHn.
apply lap_norm_app_0_r.
intros j.
rewrite all_0_summation_0. {
  destruct j; [ easy | now destruct j ].
}
clear j.
intros j (_, Hj).
apply rng_mul_eq_0.
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

Theorem all_0_lap_norm_nil : ∀ la,
  (∀ i, nth i la 0%Rng = 0%Rng)
  → lap_norm la = [].
Proof.
intros * Hla.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  destruct (rng_eq_dec a 0%Rng) as [H1| H1]; [ easy | exfalso ].
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

Theorem lap_norm_repeat_0 : ∀ la,
  la = lap_norm la ++ repeat 0%Rng (length la - length (lap_norm la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
    cbn; subst a; f_equal.
    assert (H : lap_norm la = []). {
      apply all_0_lap_norm_nil.
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
    assert (H : lap_norm la = []). {
      apply all_0_lap_norm_nil.
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
  now rewrite fold_lap_norm.
}
Qed.

Theorem lap_convol_mul_app_rep_0_l : ∀ la lb i len n,
  lap_norm (lap_convol_mul (la ++ repeat 0%Rng n) lb i len) =
  lap_norm (lap_convol_mul la lb i len).
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
rewrite fold_lap_norm.
rewrite <- (rev_involutive (strip_0s (rev _))).
rewrite fold_lap_norm.
rewrite IHlen.
remember (rev (lap_norm _)) as lc eqn:Hlc; symmetry in Hlc.
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

Theorem lap_norm_cons_norm : ∀ a la lb i len,
  length (a :: la) + length lb - 1 ≤ i + len
  → lap_norm (lap_convol_mul (a :: lap_norm la) lb i len) =
    lap_norm (lap_convol_mul (a :: la) lb i len).
Proof.
intros * Hlen.
rewrite (lap_norm_repeat_0 la) at 2.
rewrite app_comm_cons.
now rewrite lap_convol_mul_app_rep_0_l.
Qed.

Theorem lap_norm_length_le : ∀ la, length (lap_norm la) ≤ length la.
Proof.
intros.
rewrite (lap_norm_repeat_0 la) at 2.
rewrite app_length; flia.
Qed.

Theorem nth_lap_add : ∀ i la lb,
  nth i (la + lb)%lap 0%Rng = (nth i la 0 + nth i lb 0)%Rng.
Proof.
intros.
revert i lb.
induction la as [| a]; intros; cbn. {
  now rewrite match_id, rng_add_0_l.
}
destruct lb as [| b]; cbn. {
  now rewrite match_id, rng_add_0_r.
}
destruct i; [ easy | ].
apply IHla.
Qed.

Theorem lap_mul_norm_idemp_l : ∀ la lb,
  lap_norm (lap_norm la * lb)%lap = lap_norm (la * lb)%lap.
Proof.
intros.
unfold "*"%lap; cbn.
destruct la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
    cbn.
    destruct lb as [| b]; [ easy | cbn ].
    rewrite lap_convol_mul_0_l; [ easy | ].
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
Qed.

Theorem lap_mul_norm_idemp_r : ∀ la lb,
  lap_norm (la * lap_norm lb)%lap = lap_norm (la * lb)%lap.
Proof.
intros.
setoid_rewrite lap_mul_comm.
apply lap_mul_norm_idemp_l.
Qed.

Theorem poly_mul_assoc : ∀ p1 p2 p3,
  (p1 * (p2 * p3))%pol = ((p1 * p2) * p3) %pol.
Proof.
intros.
unfold "*"%pol.
remember (lap p1) as la.
remember (lap p2) as lb.
remember (lap p3) as lc.
clear p1 Heqla.
clear p2 Heqlb.
clear p3 Heqlc.
unfold poly_norm at 1 3.
apply eq_poly_eq; cbn.
rewrite lap_mul_norm_idemp_l.
rewrite lap_mul_norm_idemp_r.
now rewrite lap_mul_assoc.
Qed.

Theorem lap_mul_mul_swap : ∀ la lb lc,
  lap_mul (lap_mul la lb) lc = lap_mul (lap_mul la lc) lb.
Proof.
intros la lb lc.
do 2 rewrite <- lap_mul_assoc.
now rewrite (lap_mul_comm lb).
Qed.

Fixpoint lap_convol_mul_add al1 al2 al3 i len :=
  match len with
  | O => []
  | S len1 =>
      (Σ (j = 0, i),
       List.nth j al1 0 *
       (List.nth (i - j) al2 0 + List.nth (i - j) al3 0))%Rng ::
       lap_convol_mul_add al1 al2 al3 (S i) len1
  end.

(* *)

Theorem list_nth_add : ∀ k la lb,
  (List.nth k (lap_add la lb) 0 =
   List.nth k la 0 + List.nth k lb 0)%Rng.
Proof.
intros k la lb.
revert la lb.
induction k; intros.
 destruct la as [| a]; simpl; [ rewrite rng_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite rng_add_0_r; reflexivity | idtac ].
 reflexivity.

 destruct la as [| a]; simpl; [ rewrite rng_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite rng_add_0_r; reflexivity | idtac ].
 apply IHk.
Qed.

Theorem lap_convol_mul_lap_add : ∀ la lb lc i len,
  eq
    (lap_convol_mul la (lap_add lb lc) i len)
    (lap_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
apply summation_compat; intros j (_, Hj).
f_equal.
rewrite list_nth_add; reflexivity.
Qed.

Theorem lap_add_lap_convol_mul : ∀ la lb lc i len,
  eq
     (lap_add
        (lap_convol_mul la lb i len)
        (lap_convol_mul la lc i len))
     (lap_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
rewrite <- summation_add_distr.
apply summation_compat; intros j (_, Hj).
rewrite rng_mul_add_distr_l; reflexivity.
Qed.

Lemma lap_norm_mul_add_distr_l : ∀ la lb lc,
  lap_norm (la * (lb + lc))%lap = lap_norm (la * lb + la * lc)%lap.
Proof.
intros la lb lc.
unfold lap_mul.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]; [ now cbn; rewrite lap_add_0_r | ].
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
remember (length la' + length (lap_add lb' lc') - 1) as labc.
remember (length la' + length lb' - 1) as lab.
remember (length la' + length lc' - 1) as lac.
rewrite Heqlabc.
remember (lb' + lc')%lap as lbc.
symmetry in Heqlbc.
destruct lbc as [| bc]. {
  cbn.
  now subst lb' lc'.
}
rewrite <- Heqlbc in Heqlabc |-*.
rewrite lap_convol_mul_more with (n := (lab + lac)%nat). 2: {
  subst; flia.
}
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite <- lap_add_norm_idemp_l.
rewrite lap_convol_mul_more with (n := (labc + lac)%nat); [ | flia ].
rewrite <- Heqlab.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_comm.
rewrite <- lap_add_norm_idemp_l.
rewrite Heqlac.
rewrite lap_convol_mul_more with (n := (labc + lab)%nat); [ | flia ].
rewrite lap_add_norm_idemp_l.
rewrite <- Heqlac.
rewrite Nat.add_comm.
rewrite lap_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite lap_convol_mul_lap_add.
rewrite lap_add_lap_convol_mul.
reflexivity.
Qed.

Theorem lap_add_length : ∀ la lb,
  length (la + lb)%lap = max (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | ].
cbn.
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
Qed.

Lemma lap_mul_add_distr_l : ∀ la lb lc,
  (la * (lb + lc))%lap = (la * lb + la * lc)%lap.
Proof.
intros la lb lc.
apply eq_lap_norm_eq_length; [ apply lap_norm_mul_add_distr_l | ].
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]. {
  now cbn; rewrite lap_add_0_r.
}
cbn.
do 3 (rewrite Nat.add_succ_r; cbn); f_equal.
rewrite lap_convol_mul_length.
do 2 rewrite lap_add_length; cbn.
do 2 rewrite lap_convol_mul_length.
now rewrite Nat.add_max_distr_l.
Qed.

Theorem poly_mul_add_distr_l : ∀ pa pb pc,
  (pa * (pb + pc))%pol = (pa * pb + pa * pc)%pol.
Proof.
intros.
apply eq_poly_eq; cbn.
rewrite fold_lap_norm.
rewrite lap_mul_norm_idemp_r.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_norm_idemp_r.
now rewrite lap_mul_add_distr_l.
Qed.

Lemma lap_convol_mul_1_l : ∀ la i len,
  length la = i + len
  → lap_convol_mul [1%Rng] la i len = skipn i la.
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
  now rewrite match_id, rng_mul_0_l.
}
rewrite Nat.sub_0_r, rng_add_0_r; cbn.
rewrite rng_mul_1_l.
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

Theorem lap_mul_1_l : ∀ la, ([1%Rng] * la)%lap = la.
Proof.
intros la.
unfold lap_mul.
destruct la as [| a]; [ easy | cbn ].
rewrite rng_mul_1_l, rng_add_0_r; f_equal.
now rewrite lap_convol_mul_1_l.
Qed.

Theorem lap_mul_1_r : ∀ la, (la * [1%Rng])%lap = la.
Proof.
intros la.
rewrite lap_mul_comm.
apply lap_mul_1_l.
Qed.

Theorem poly_mul_1_l : ∀ p, (1 * p)%pol = p.
Proof.
intros (la, lapr).
unfold "*"%pol.
rewrite lap_mul_1_l; cbn.
apply eq_poly_eq; cbn.
unfold rng_eqb in lapr.
unfold lap_norm.
destruct (rng_eq_dec (last la 1%Rng) 0) as [Hlaz| Hlaz]; [ easy | ].
clear lapr.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  specialize (proj1 (eq_strip_0s_rev_nil _) Hlb) as H1.
  cbn; clear Hlb.
  destruct (rng_eq_dec a 0) as [Haz| Haz]. {
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
  intros; apply rng_1_neq_0.
}
cbn.
rewrite rev_app_distr; cbn; f_equal.
apply IHla.
cbn in Hlaz.
now destruct la.
Qed.

End lap.

Lemma lap_add_opp_l {α} {r : ring α} : ∀ la, lap_norm (- la + la)%lap = [].
Proof.
intros.
unfold lap_norm.
apply List_eq_rev_nil.
rewrite rev_involutive.
induction la as [| a]; [ reflexivity | cbn ].
rewrite strip_0s_app.
remember (strip_0s _) as lb eqn:Hlb; symmetry in Hlb.
subst lb.
rewrite IHla; cbn.
rewrite rng_add_opp_l.
now destruct (rng_eq_dec 0 0).
Qed.

Theorem poly_add_opp_l {α} {r : ring α} : ∀ p, (- p + p)%pol = 0%pol.
Proof.
intros p.
unfold "+"%pol; cbn.
apply eq_poly_eq; cbn.
rewrite lap_add_norm_idemp_l.
apply lap_add_opp_l.
Qed.

Theorem poly_add_opp_r {α} {r : ring α} : ∀ p, (p - p)%pol = 0%pol.
Proof.
intros p.
unfold poly_sub.
rewrite poly_add_comm.
apply poly_add_opp_l.
Qed.

Theorem poly_1_neq_0 {A} {rng : ring A} : 1%pol ≠ 0%pol.
Proof. easy. Qed.

Fixpoint lap_eqb {A} {rng : ring A} la lb :=
  match la with
  | [] =>
      match lb with
      | [] => true
      | _ :: _ => false
      end
  | a :: la' =>
      match lb with
      | [] => false
      | b :: lb' => if rng_eq_dec a b then lap_eqb la' lb' else false
      end
  end.

Theorem lap_eqb_eq {A} {rng : ring A} : ∀ la lb,
  lap_eqb la lb = true ↔ la = lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | cbn ].
destruct (rng_eq_dec a b) as [Hab| Hab]. {
  subst b.
  split; intros Hll; [ now f_equal; apply IHla | ].
  injection Hll; clear Hll; intros; subst lb.
  now apply IHla.
} {
  split; intros Hll; [ easy | ].
  now injection Hll; intros.
}
Qed.

Theorem lap_eqb_neq {A} {rng : ring A} : ∀ la lb,
  lap_eqb la lb = false ↔ la ≠ lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | cbn ].
destruct (rng_eq_dec a b) as [Hab| Hab]. {
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

Lemma lap_eq_dec {A} {rng : ring A} : ∀ la lb : list A,
  {la = lb} + {la ≠ lb}.
Proof.
intros.
remember (lap_eqb la lb) as lab eqn:Hlab; symmetry in Hlab.
destruct lab. {
  now left; apply lap_eqb_eq.
} {
  now right; apply lap_eqb_neq.
}
Qed.

Theorem poly_eq_dec {A} {rng : ring A} : ∀ pa pb : poly _,
  {pa = pb} + {pa ≠ pb}.
Proof.
intros (la, lapr) (lb, lbpr).
destruct (lap_eq_dec la lb) as [Hll| Hll]. {
  left; subst lb.
  now apply eq_poly_eq.
} {
  right; intros H; apply Hll.
  now injection H.
}
Qed.

Definition polynomial_ring {α} {r : ring α} : ring (poly α) :=
  {| rng_zero := poly_zero;
     rng_one := poly_one;
     rng_add := poly_add;
     rng_mul := poly_mul;
     rng_opp := poly_opp;
     rng_1_neq_0 := poly_1_neq_0;
     rng_eq_dec := poly_eq_dec;
     rng_add_comm := poly_add_comm;
     rng_add_assoc := poly_add_assoc;
     rng_add_0_l := poly_add_0_l;
     rng_add_opp_l := poly_add_opp_l;
     rng_mul_comm := poly_mul_comm;
     rng_mul_assoc := poly_mul_assoc;
     rng_mul_1_l := poly_mul_1_l;
     rng_mul_add_distr_l := poly_mul_add_distr_l |}.

(* allows to use ring theorems on polynomials *)
Canonical Structure polynomial_ring.

(* *)

Definition eval_lap {α} {R : ring α} la x :=
  (List.fold_right (λ c accu, accu * x + c) 0 la)%Rng.

Definition eval_poly {α} {R : ring α} pol :=
  eval_lap (lap pol).
