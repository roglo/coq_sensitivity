(* Polynomial.v *)

(* polynomials on a RingLike *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List ListNotations Init.Nat.

Require Import Misc RingLike IterAdd IterAnd.
Require Import PermutationFun SortingFun.

(* (lap : list as polynomial) *)
(* e.g. polynomial ax²+bx+c is implemented by the list [c;b;a] *)
(* TODO: use an intermediate type like this:
      Record polyn T := mk_polyn { lap : list T }.
   and another type for the condition that the last value in lap
   is not null.
*)
Definition is_empty_list {A} (la : list A) :=
  match la with [] => true | _ => false end.
Definition has_polyn_prop T {ro : ring_like_op T} (lap : list T) :=
  (is_empty_list lap || (last lap 0 ≠? 0)%F)%bool.

Record polyn T {ro : ring_like_op T} := mk_polyn
  { lap : list T;
    lap_prop : has_polyn_prop lap = true }.

Arguments polyn T {ro}.
Arguments mk_polyn {T ro} lap%list.
Arguments lap {T ro}.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
Context {Heb : rngl_has_eqb = true}.
Context (H10 : rngl_has_1_neq_0 = true).
Context {Hos : rngl_has_opp_or_sous = true}.

Definition lap_eqb (eqb : T → _) (P Q : list T) :=
  list_eqv eqb P Q.

Definition polyn_eqb (eqb : T → _) (P Q : polyn T) :=
  list_eqv eqb (lap P) (lap Q).

(* polyn_eq is equivalent to lap_eq *)

Theorem eq_polyn_eq : ∀ pa pb,
  lap pa = lap pb
  ↔ pa = pb.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct pa as (la, pa).
destruct pb as (lb, pb).
cbn in Hab.
subst lb.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

(* polyn_eqb is an equality *)

Theorem polyn_eqb_eq : ∀ (eqb : T → T → bool),
  equality eqb →
  ∀ (P Q : polyn T),
  polyn_eqb eqb P Q = true ↔ P = Q.
Proof.
intros * Heqb *.
split; intros Hpq. {
  unfold polyn_eqb in Hpq.
  apply list_eqb_eq in Hpq; [ | easy ].
  destruct P as (P, Pprop).
  destruct Q as (Q, Qprop).
  cbn in Hpq; cbn.
  destruct Hpq.
  f_equal.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
} {
  subst Q.
  now apply list_eqb_eq.
}
Qed.

Definition lap_one := [1%F].

Theorem polyn_one_prop : has_polyn_prop lap_one = true.
Proof.
unfold lap_one.
unfold has_polyn_prop; cbn.
apply (rngl_neqb_neq Heb).
now apply rngl_1_neq_0.
Qed.

Definition polyn_zero := mk_polyn [] eq_refl.
Definition polyn_one := mk_polyn lap_one polyn_one_prop.

(* normalization *)

Fixpoint strip_0s la :=
  match la with
  | [] => []
  | a :: la' => if (a =? 0)%F then strip_0s la' else la
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
destruct (a =? 0)%F; [ apply IHla | easy ].
Qed.

Theorem eq_strip_0s_nil : ∀ la,
  strip_0s la = [] ↔ ∀ i, nth i la 0%F = 0%F.
Proof.
intros.
split. {
  intros Hla *.
  revert i.
  induction la as [| a]; intros; [ now destruct i | cbn ].
  cbn in Hla.
  rewrite if_bool_if_dec in Hla.
  destruct (bool_dec _) as [Haz| Haz]; [ | easy ].
  apply (rngl_eqb_eq Heb) in Haz.
  destruct i; [ easy | ].
  now apply IHla.
} {
  intros Hla.
  induction la as [| a]; [ easy | cbn ].
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [Haz| Haz]. {
    apply IHla.
    intros i.
    now specialize (Hla (S i)).
  }
  apply (rngl_eqb_neq Heb) in Haz.
  now specialize (Hla 0).
}
Qed.

Theorem eq_strip_0s_cons : ∀ la lb b,
  strip_0s la = b :: lb → b ≠ 0%F.
Proof.
intros * Hab.
intros H; subst b.
induction la as [| a]; [ easy | cbn in Hab ].
rewrite if_bool_if_dec in Hab.
destruct (bool_dec _) as [Haz| Haz]; [ congruence | ].
injection Hab; clear Hab; intros Hab Ha; subst a.
now rewrite (rngl_eqb_refl Heb) in Haz.
Qed.

Definition lap_norm la := rev (strip_0s (rev la)).

Theorem polyn_norm_prop : ∀ la, has_polyn_prop (lap_norm la) = true.
Proof.
intros.
unfold has_polyn_prop, lap_norm.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; cbn. {
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [Haz| Haz]; [ easy | cbn ].
  now apply Bool.negb_true_iff.
}
cbn in IHla.
rewrite last_last in IHla.
apply Bool.orb_true_iff in IHla.
apply Bool.orb_true_iff; right.
rewrite last_last.
destruct IHla as [H1| H1]; [ | easy ].
apply eq_strip_0s_cons in Hlb.
now apply (rngl_neqb_neq Heb).
Qed.

Definition polyn_norm la :=
  mk_polyn (lap_norm la) (polyn_norm_prop la).

(* addition *)

Fixpoint lap_add la lb :=
  match la with
  | [] => lb
  | a1 :: bl1 =>
      match lb with
      | [] => la
      | a2 :: bl2 => (a1 + a2)%F :: lap_add bl1 bl2
      end
  end.

Definition lap_opp la := map rngl_opp la.
Definition lap_sub la lb := lap_add la (lap_opp lb).

Definition polyn_add p1 p2 := polyn_norm (lap_add (lap p1) (lap p2)).
Definition polyn_opp pol := polyn_norm (lap_opp (lap pol)).
Definition polyn_sub p1 p2 := polyn_add p1 (polyn_opp p2).

Theorem fold_lap_opp : ∀ la, map rngl_opp la = lap_opp la.
Proof. easy. Qed.

Theorem fold_lap_sub : ∀ la lb, lap_add la (lap_opp lb) = lap_sub la lb.
Proof. easy. Qed.

(* multiplication *)

Fixpoint lap_convol_mul al1 al2 i len :=
  match len with
  | O => []
  | S len1 =>
      (∑ (j = 0, i), List.nth j al1 0 * List.nth (i - j) al2 0)%F ::
      lap_convol_mul al1 al2 (S i) len1
  end.

Definition lap_mul la lb :=
  match la with
  | [] => []
  | _ =>
      match lb with
      | [] => []
      | _ => lap_convol_mul la lb 0 (length la + length lb - 1)
      end
  end.

Definition polyn_mul p1 p2 := polyn_norm (lap_mul (lap p1) (lap p2)).

(* power *)

Fixpoint lap_power la n :=
  match n with
  | O => [1%F]
  | S m => lap_mul la (lap_power la m)
  end.

(* euclidean division *)

Definition rlap_quot_rem_nb_iter (la lb : list T) :=
  S (length la).

Definition rlap_quot_rem_step (rla rlb : list T) :=
  match rlb with
  | [] => (None, []) (* division by zero *)
  | b :: rlb' =>
      match rla with
      | [] => (None, [])
      | a :: rla' =>
          if length rla' <? length rlb' then (None, rla)
          else
            let cq := (a / b)%F in
            let rlr := lap_sub rla' (map (λ cb, (cb * cq)%F) rlb') in
            (Some cq, rlr)
      end
  end.

Fixpoint rlap_quot_rem_loop it (rla rlb : list T) : list T * list T :=
  match it with
  | 0 => ([], [rngl_mul_nat_l 97 1]) (* algo err: not enough iterations *)
  | S it' =>
      let (q, rlr) := rlap_quot_rem_step rla rlb in
      match q with
      | Some cq =>
           let (rlq', rlr') := rlap_quot_rem_loop it' rlr rlb in
           (cq :: rlq', rlr')
      | None => ([], rlr)
      end
  end.

Definition rlap_quot_rem rla rlb :=
  rlap_quot_rem_loop (rlap_quot_rem_nb_iter rla rlb) rla rlb.

Definition lap_quot_rem la lb :=
  let (rlq, rlr) := rlap_quot_rem (rev la) (rev lb) in
  (rev rlq, rev (strip_0s rlr)).

Definition lap_quot la lb :=
  let (rlq, rlr) := rlap_quot_rem (rev la) (rev lb) in
  rev rlq.

Definition lap_rem la lb :=
  let (rlq, rlr) := rlap_quot_rem (rev la) (rev lb) in
  rev (strip_0s rlr).

(*
End a.
Arguments lap_add {T ro} (la lb)%list.
Arguments lap_sub {T ro} (la lb)%list.
Arguments lap_mul {T ro} (la lb)%list.
Arguments lap_quot_rem {T ro} (la lb)%list.
Arguments rlap_quot_rem {T ro} (rla rlb)%list.
Arguments rlap_quot_rem_step {T ro} (rla rlb)%list.
Arguments rlap_quot_rem_loop {T ro} it%nat (rla rlb)%list.
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.
Compute (rlap_quot_rem [1] [2]).
Compute (rlap_quot_rem [1;0;1;1;0] [1;0;1;0;0]).
Compute (rlap_quot_rem [1;1;1] [1;1;0]).
Compute (rlap_quot_rem [1;0;0;1] [1;1]).
Compute (rlap_quot_rem [1;1;0;1] [1;1]).
Compute (rlap_quot_rem_step [1;1;0;1] [1;1]).
Compute (rlap_quot_rem [0;0;1] [1;1]).
Compute (rlap_quot_rem_step [0;0;1] [1;1]).
Print rlap_quot_rem_loop.
Print rlap_quot_rem.
Compute (rlap_quot_rem [0;1;0;0;1] [1;1]).
Compute (
  let la := [0;1] in
  let lb := [1;0;0;1] in
  let (lq, lr) := lap_quot_rem la lb in
  (la = (lap_add (lap_mul lb lq) lr))).
Compute (
  let la := [1;0;0] in
  let lb := [1;0;0;1] in
  let (lq, lr) := lap_quot_rem la lb in
  (la = (lap_add (lap_mul lb lq) lr))).
Compute (rlap_quot_rem [1;0;0;1] [1;7]).
Compute (rlap_quot_rem [6;-2;9;-2;-2] [1;0;2]).
Compute (rlap_quot_rem [1;6;-1;-30] [1;5]).
Compute (rlap_quot_rem [1;3;-2;7;-12] [1;0;-1]).
Compute (rlap_quot_rem [1;0;1;-10] [1;-2]).
Compute (rlap_quot_rem [1;-1;-1;3;-2;0] [1;-1;1]).
Compute (rlap_quot_rem [1;1;1;1] [1;0;1]).
Compute (rlap_quot_rem [1;2;0;3] [1;-1;-1]).
Compute (rlap_quot_rem [1;2;0;3] [1;-1;-1]).
Compute (rlap_quot_rem [1;0;0;-1;0] [2;1]).
Compute (rlap_quot_rem [-3;0;1;0;-5;0;1] [3;1;1]).
Compute (rlap_quot_rem [-3;0;1;0;-5;0;1;0;0] [3;1;1;0]).
(* censé ci-dessous être (x3-2x+1, x-1) *)
Compute (rlap_quot_rem [1;-1;-1;3;-2;0] [1;-1;1]).
(**)
Compute (lap_quot_rem [-2;-2;9;-2;6] [2;0;1]).
Compute (lap_add (lap_mul [2;0;1] [-3;-2;6]) [4;2] = [-2;-2;9;-2;6]).
...
*)

Theorem lap_add_0_l : ∀ la, lap_add [] la = la.
Proof. easy. Qed.

Theorem lap_add_0_r : ∀ la, lap_add la [] = la.
Proof. intros; now destruct la. Qed.

Theorem lap_sub_0_r : ∀ la, lap_sub la [] = la.
Proof. intros; now destruct la. Qed.

Theorem lap_mul_0_l : ∀ la, lap_mul [] la = [].
Proof. easy. Qed.

Theorem lap_mul_0_r : ∀ la, lap_mul la [] = [].
Proof. now intros; destruct la. Qed.

Theorem strip_0s_length_le : ∀ l, length (strip_0s l) ≤ length l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
destruct (a =? 0)%F; cbn; [ | easy ].
flia IHl.
Qed.

Theorem lap_add_length : ∀ la lb,
  length (lap_add la lb) = max (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal; apply IHla.
Qed.

Theorem lap_opp_length : ∀ la, length (lap_opp la) = length la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
f_equal; apply IHla.
Qed.

Theorem lap_sub_length : ∀ la lb,
  length (lap_sub la lb) = max (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; cbn; [ now rewrite lap_opp_length | ].
destruct lb as [| b]; [ easy | cbn ].
f_equal; apply IHla.
Qed.

Theorem all_0_lap_norm_nil : ∀ la,
  (∀ i, nth i la 0%F = 0%F)
  ↔ lap_norm la = [].
Proof.
intros *.
split; intros Hla. {
  induction la as [| a]; [ easy | cbn ].
  rewrite strip_0s_app.
  remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| b]. {
    cbn.
    rewrite if_bool_if_dec.
    destruct (bool_dec _) as [H1| H1]; [ easy | exfalso ].
    apply (rngl_eqb_neq Heb) in H1.
    now specialize (Hla 0); cbn in Hla.
  }
  exfalso.
  assert (H : strip_0s (rev la) = []). {
    clear - rp Heb Hla.
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
} {
  intros i.
  destruct (lt_dec i (length la)) as [Hila| Hila]. 2: {
    apply Nat.nlt_ge in Hila.
    now apply nth_overflow.
  }
  unfold lap_norm in Hla.
  apply List_eq_rev_nil in Hla.
  apply eq_strip_0s_nil with (i := length la - S i) in Hla.
  rewrite rev_nth in Hla; [ | flia Hila ].
  rewrite <- Nat_succ_sub_succ_r in Hla; [ | easy ].
  rewrite Nat_sub_sub_distr in Hla; [ | flia Hila ].
  now rewrite Nat.add_comm, Nat.add_sub in Hla.
}
Qed.

Theorem fold_lap_norm : ∀ la, rev (strip_0s (rev la)) = lap_norm la.
Proof. easy. Qed.

Theorem lap_norm_app_repeat_0 : ∀ la,
  la = lap_norm la ++ repeat 0%F (length la - length (lap_norm la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [Haz| Haz]. {
    apply (rngl_eqb_eq Heb) in Haz.
    cbn; subst a; f_equal.
    assert (H : lap_norm la = []). {
      apply all_0_lap_norm_nil.
      intros i.
      specialize (proj1 (eq_strip_0s_nil _) Hlb) as H1.
      destruct (lt_dec i (length la)) as [Hila| Hila]. {
        rewrite <- (rev_involutive la).
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
        rewrite <- (rev_involutive la).
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

Theorem lap_norm_length_le : ∀ la, length (lap_norm la) ≤ length la.
Proof.
intros.
rewrite (lap_norm_app_repeat_0 la) at 2.
rewrite app_length; flia.
Qed.

Theorem lap_sub_repeat_0 : ∀ la,
  lap_sub la (repeat 0%F (length la)) = la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
rewrite fold_lap_opp, fold_lap_sub, IHla; f_equal.
remember rngl_has_opp as hop eqn:Hop; symmetry in Hop.
destruct hop. {
  now rewrite (rngl_opp_0 Hop), rngl_add_0_r.
}
unfold rngl_opp.
unfold rngl_has_opp in Hop.
remember rngl_opt_opp_or_sous as os eqn:Hoos; symmetry in Hoos.
destruct os as [os| ]. {
  destruct os as [os| os]; [ easy | apply rngl_add_0_r ].
}
apply rngl_add_0_r.
Qed.

Theorem lap_norm_add_length_le : ∀ la lb,
  length (lap_norm (lap_add la lb)) ≤ max (length la) (length lb).
Proof.
intros.
unfold lap_norm.
rewrite rev_length.
etransitivity; [ apply strip_0s_length_le | ].
rewrite rev_length.
now rewrite lap_add_length.
Qed.

Theorem lap_norm_sub_length_le : ∀ la lb,
  length (lap_norm (lap_sub la lb)) ≤ max (length la) (length lb).
Proof.
intros.
unfold lap_norm.
rewrite rev_length.
etransitivity; [ apply strip_0s_length_le | ].
rewrite rev_length.
now rewrite lap_sub_length.
Qed.

Theorem rlap_quot_rem_step_None : ∀ la lb lr,
  rlap_quot_rem_step la lb = (None, lr)
  → lb = [] ∧ lr = [] ∨ la = [] ∧ lr = [] ∨ length la < length lb ∧ lr = la.
Proof.
intros * Hrl.
destruct lb as [| b]. {
  injection Hrl; clear Hrl; intros; subst.
  now left.
}
destruct la as [| a]. {
  injection Hrl; clear Hrl; intros; subst.
  now right; left.
}
cbn in Hrl |-*; right; right.
rewrite if_ltb_lt_dec in Hrl.
destruct (lt_dec _ _) as [Hab| Hab]; [ | easy ].
injection Hrl; clear Hrl; intros; subst lr.
split; [ | easy ].
now apply Nat.succ_lt_mono in Hab.
Qed.

Theorem rlap_quot_rem_step_length_r_a : ∀ rla rlb rlr cq,
  rlap_quot_rem_step rla rlb = (Some cq, rlr)
  → S (length rlr) = length rla.
Proof.
intros * Hrab.
unfold rlap_quot_rem_step in Hrab.
destruct rlb as [| b]; [ easy | ].
destruct rla as [| a]; [ easy | ].
rewrite if_bool_if_dec in Hrab.
destruct (bool_dec _) as [Hab| Hab]; [ easy | ].
apply Nat.ltb_ge in Hab.
injection Hrab; clear Hrab; intros; subst cq rlr.
rewrite lap_sub_length, map_length.
now rewrite Nat.max_l.
Qed.

Theorem rlap_rem_loop_prop : ∀ it rla rlb rlq rlr,
  rlb ≠ []
  → rlap_quot_rem_loop it rla rlb = (rlq, rlr)
  → S (length rla) ≤ it
  → length rlr < length rlb.
Proof.
intros * Hbz Hqr Hit.
revert rla rlq rlr Hqr Hit.
induction it; intros; [ easy | ].
cbn in Hqr.
remember (rlap_quot_rem_step rla rlb) as qr eqn:Hqr'; symmetry in Hqr'.
destruct qr as (q, rlr').
destruct q as [cq| ]. 2: {
  injection Hqr; clear Hqr; intros; subst rlq rlr'.
  apply rlap_quot_rem_step_None in Hqr'.
  destruct Hqr' as [(H1, H2)| Hqr]; [ easy | ].
  destruct Hqr as [(H1, H2)| Hqr]. {
    subst rla rlr.
    destruct rlb; [ easy | ].
    cbn; easy.
  }
  now destruct Hqr as (H1, H2); subst rlr.
}
remember (rlap_quot_rem_loop it rlr' rlb) as qr eqn:Hqr''.
symmetry in Hqr''.
destruct qr as (rlq', rlr'').
injection Hqr; clear Hqr; intros; subst rlq rlr''.
apply IHit in Hqr''; [ easy | ].
apply rlap_quot_rem_step_length_r_a in Hqr'.
rewrite Hqr'.
now apply Nat.succ_le_mono in Hit.
Qed.

Theorem rlap_rem_prop : ∀ rla rlb rlq rlr,
  rlb ≠ []
  → rlap_quot_rem rla rlb = (rlq, rlr)
  → length rlr < length rlb.
Proof.
intros * Hbz Hqr.
unfold rlap_quot_rem in Hqr.
remember (rlap_quot_rem_nb_iter rla rlb) as it eqn:Hit.
unfold rlap_quot_rem_nb_iter in Hit.
assert (H : S (length rla) ≤ it) by flia Hit.
now apply rlap_rem_loop_prop in Hqr.
Qed.

Theorem lap_rem_length_lt :
  rngl_has_opp = true →
  rngl_mul_is_comm = true →
  ∀ la lb lq lr : list T,
  lb ≠ []
  → has_polyn_prop lb = true
  → lap_quot_rem la lb = (lq, lr)
  → length lr < length lb.
Proof.
intros Hop Hco * Hbz Hbn Hab.
unfold lap_quot_rem in Hab.
remember (rlap_quot_rem (rev la) (rev lb)) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (rlq, rlr).
injection Hab; clear Hab; intros; subst lq lr.
apply rlap_rem_prop in Hqr. 2: {
  now intros H; apply List_eq_rev_nil in H.
}
rewrite rev_length in Hqr |-*.
eapply le_lt_trans; [ | apply Hqr ].
apply strip_0s_length_le.
Qed.

Theorem rlap_quot_prop :
  rngl_has_inv = true →
  ∀ la lb lq lr,
  la = [] ∨ hd 0%F la ≠ 0%F
  → lb = [] ∨ hd 0%F lb ≠ 0%F
  → rlap_quot_rem la lb = (lq, lr)
  → lq = [] ∨ hd 0%F lq ≠ 0%F.
Proof.
intros Hiv * Ha Hb Hab.
unfold rlap_quot_rem in Hab.
remember (rlap_quot_rem_nb_iter _ _) as it eqn:Hit.
symmetry in Hit.
assert (H : rlap_quot_rem_nb_iter la lb ≤ it) by flia Hit.
move H before Hit; clear Hit; rename H into Hit.
destruct it; [ easy | ].
cbn in Hab.
remember (rlap_quot_rem_step la lb) as orlr eqn:Hor; symmetry in Hor.
destruct orlr as (o, rlr).
destruct o as [cq| ]. 2: {
  injection Hab; clear Hab; intros; subst lq lr.
  now left.
}
destruct lb as [| b]; [ easy | ].
destruct la as [| a]; [ easy | cbn ].
destruct Ha as [Ha| Ha]; [ easy | ].
destruct Hb as [Hb| Hb]; [ easy | ].
cbn in Ha, Hb, Hor.
rewrite if_ltb_lt_dec in Hor.
destruct (lt_dec _ _) as [Halb| Halb]; [ easy | ].
apply Nat.nlt_ge in Halb.
symmetry in Hor.
injection Hor; clear Hor; intros Hrlr Hcq.
rewrite <- Hcq in Hrlr.
remember (rlap_quot_rem_loop it rlr (b :: lb)) as rb eqn:Hrb.
symmetry in Hrb.
destruct rb as (lq', lr').
symmetry in Hab.
injection Hab; clear Hab; intros H1 Hlq; subst lr'.
rewrite Hlq; cbn.
rewrite Hcq.
unfold rngl_div.
rewrite Hiv.
right.
intros Hq.
apply rngl_integral in Hq; [ | easy | ]. 2: {
  apply Bool.orb_true_iff; right.
  rewrite Heb, Bool.andb_true_r.
  now apply rngl_has_inv_or_quot_iff; left.
}
destruct Hq as [Hq| Hq]; [ easy | ].
exfalso; revert Hq.
apply rngl_inv_neq_0; [ easy | easy | easy | easy ].
Qed.

Theorem lap_quot_is_norm :
  rngl_has_inv = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → has_polyn_prop (lap_quot la lb) = true.
Proof.
intros Hiv * Ha Hb.
unfold lap_quot.
remember (rlap_quot_rem (rev la) (rev lb)) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (rlq, rlr); cbn.
unfold has_polyn_prop.
apply Bool.orb_true_iff.
destruct rlq as [| q]; [ now left | right ].
cbn; rewrite last_last.
apply (rlap_quot_prop Hiv) in Hqr; cycle 1. {
  apply Bool.orb_true_iff in Ha.
  destruct Ha as [Ha| Ha]; [ now left; destruct la | right ].
  destruct la as [| a] using rev_ind. {
    cbn in Ha.
    now rewrite (rngl_eqb_refl Heb) in Ha.
  }
  rewrite last_last in Ha.
  rewrite rev_app_distr; cbn.
  now apply (rngl_neqb_neq Heb) in Ha.
} {
  unfold has_polyn_prop in Hb.
  apply Bool.orb_true_iff in Hb.
  destruct Hb as [Hb| Hb]; [ now left; destruct lb | right ].
  destruct lb as [| b] using rev_ind. {
    cbn in Hb.
    now rewrite (rngl_eqb_refl Heb) in Hb.
  }
  rewrite last_last in Hb.
  rewrite rev_app_distr; cbn.
  now apply (rngl_neqb_neq Heb) in Hb.
}
destruct Hqr as [Hqr| Hqr]; [ easy | ].
cbn in Hqr.
now apply (rngl_neqb_neq Heb).
Qed.

Theorem lap_rem_is_norm : ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → has_polyn_prop (lap_rem la lb) = true.
Proof.
intros * Ha Hb.
unfold lap_rem.
remember (rlap_quot_rem (rev la) (rev lb)) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (rlq, rlr); cbn.
unfold has_polyn_prop.
destruct rlr as [| r]; [ easy | ].
cbn; rewrite if_bool_if_dec.
apply Bool.orb_true_iff.
destruct (bool_dec _) as [Hrz| Hrz]. {
  rewrite List_last_rev.
  remember (strip_0s rlr) as rl eqn:Hrl;symmetry in Hrl.
  destruct rl as [| a]; [ now left | right; cbn ].
  apply eq_strip_0s_cons in Hrl.
  now apply (rngl_neqb_neq Heb).
}
right; cbn; rewrite last_last.
now rewrite Hrz.
Qed.

Definition polyn_quot (pa pb : polyn T) : polyn T :=
  match bool_dec rngl_has_inv with
  | left Hiv =>
      let lq := lap_quot (lap pa) (lap pb) in
      mk_polyn lq
        (lap_quot_is_norm Hiv (lap pa) (lap pb) (lap_prop pa) (lap_prop pb))
  | right _ =>
      polyn_zero
  end.

Definition polyn_rem (pa pb : polyn T) : polyn T :=
  let lq := lap_rem (lap pa) (lap pb) in
  mk_polyn lq
    (lap_rem_is_norm (lap pa) (lap pb) (lap_prop pa) (lap_prop pb)).

Definition polyn_quot_rem (pa pb : polyn T) : polyn T * polyn T :=
  (polyn_quot pa pb, polyn_rem pa pb).

(* polyn opposite or subtraction *)

Definition lap_opt_opp_or_sous :
  option ((list T → list T) + (list T → list T → list T)) :=
  match rngl_opt_opp_or_sous with
  | Some (inl _) => Some (inl lap_opp)
  | Some (inr _) => None
  | None => None
  end.

Definition polyn_opt_opp_or_sous :
  option ((polyn T → polyn T) + (polyn T → polyn T → polyn T)) :=
  match rngl_opt_opp_or_sous with
  | Some (inl _) => Some (inl polyn_opp)
  | Some (inr _) => None
  | None => None
  end.

(* polyn quotient *)

Definition lap_opt_inv_or_quot :
  option ((list T → list T) + (list T → list T → list T)) :=
  match bool_dec rngl_mul_is_comm with
  | left Hco =>
      match bool_dec rngl_has_opp with
      | left Hop =>
          match bool_dec rngl_has_inv with
         | left Hiv =>
             match rngl_opt_inv_or_quot with
             | Some _ => Some (inr lap_quot)
             | None => None
             end
          | right _ => None
          end
      | right _ => None
      end
  | right _ => None
  end.

Definition polyn_opt_inv_or_quot :
  option ((polyn T → polyn T) + (polyn T → polyn T → polyn T)) :=
  match bool_dec rngl_mul_is_comm with
  | left Hco =>
      match bool_dec rngl_has_opp with
      | left Hop =>
          match bool_dec rngl_has_inv with
         | left Hiv =>
             match rngl_opt_inv_or_quot with
             | Some _ => Some (inr polyn_quot)
             | None => None
             end
          | right _ => None
          end
      | right _ => None
      end
  | right _ => None
  end.

(* ring-like operators *)

Definition lap_ring_like_op : ring_like_op (list T) :=
  {| rngl_zero := [];
     rngl_one := lap_one;
     rngl_add := lap_add;
     rngl_mul := lap_mul;
     rngl_opt_opp_or_sous := lap_opt_opp_or_sous;
     rngl_opt_inv_or_quot := lap_opt_inv_or_quot;
     rngl_opt_eqb := Some (lap_eqb rngl_eqb);
     rngl_opt_le := None |}.

Definition polyn_ring_like_op : ring_like_op (polyn T) :=
  {| rngl_zero := polyn_zero;
     rngl_one := polyn_one;
     rngl_add := polyn_add;
     rngl_mul := polyn_mul;
     rngl_opt_opp_or_sous := polyn_opt_opp_or_sous;
     rngl_opt_inv_or_quot := polyn_opt_inv_or_quot;
     rngl_opt_eqb := Some (polyn_eqb rngl_eqb);
     rngl_opt_le := None |}.

(* allows to use ring-like theorems on polynomials *)
Canonical Structure polyn_ring_like_op.

(* to search for ring-like polynomials operators in the context *)
(*
Existing Instance polyn_ring_like_op.
*)
(* Another way is to add at the beginning of the theorem
  let _ := polyn_ring_like_op in
*)

Declare Scope polyn_scope.
Delimit Scope polyn_scope with pol.

Notation "0" := polyn_zero : polyn_scope.
Notation "1" := polyn_one : polyn_scope.
Notation "- a" := (polyn_opp a) : polyn_scope.
Notation "a + b" := (polyn_add a b) : polyn_scope.
Notation "a - b" := (polyn_sub a b) : polyn_scope.
Notation "a * b" := (polyn_mul a b) : polyn_scope.
Notation "a / b" := (polyn_quot a b) : polyn_scope.

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.

Arguments lap_add (la lb)%lap.
Arguments lap_mul (la lb)%lap.
Arguments lap_quot_rem (la lb)%lap.
Arguments lap_quot (la lb)%lap.
Arguments lap_rem (la lb)%lap.

(*
Notation "0" := [] : lap_scope.
*)
Notation "1" := lap_one : lap_scope.
Notation "- a" := (lap_opp a) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
Notation "a / b" := (lap_quot a b) : lap_scope.
Notation "a 'mod' b" := (lap_rem a b) : lap_scope.

Arguments lap {T ro} p%pol.
Arguments lap_norm la%lap.

(* commutativity of addition *)

Theorem lap_add_comm : ∀ al1 al2,
  lap_add al1 al2 = lap_add al2 al1.
Proof.
intros al1 al2.
revert al2.
induction al1; intros; [ now destruct al2 | ].
destruct al2; [ easy | cbn ].
now rewrite rngl_add_comm, IHal1.
Qed.

Theorem polyn_add_comm : ∀ a b, (a + b)%pol = (b + a)%pol.
Proof.
intros.
unfold "+"%pol.
now rewrite lap_add_comm.
Qed.

(* associativity of addition *)

Theorem strip_0s_idemp : ∀ la, strip_0s (strip_0s la) = strip_0s la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (bool_dec _) as [Haz| Haz]; [ easy | cbn ].
now rewrite Haz.
Qed.

Theorem lap_add_norm_idemp_l : ∀ la lb,
  lap_norm (lap_norm la + lb) = lap_norm (la + lb).
Proof.
intros.
unfold lap_norm; f_equal.
revert la.
induction lb as [| b]; intros. {
  do 2 rewrite lap_add_0_r.
  now rewrite rev_involutive, strip_0s_idemp.
}
destruct la as [| a]; [ easy | cbn ].
do 2 rewrite strip_0s_app; cbn.
rewrite <- IHlb.
remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [Haz| Haz]. {
    apply (rngl_eqb_eq Heb) in Haz.
    subst a; rewrite rngl_add_0_l; cbn.
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
  lap_norm (la + lap_norm lb) = lap_norm (la + lb).
Proof.
intros.
rewrite lap_add_comm, lap_add_norm_idemp_l.
now rewrite lap_add_comm.
Qed.

Theorem lap_sub_norm_idemp_l : ∀ la lb,
  lap_norm (lap_norm la - lb) = lap_norm (la - lb).
Proof.
intros.
unfold lap_sub.
now rewrite lap_add_norm_idemp_l.
Qed.

Theorem lap_opp_norm :
  rngl_has_opp = true →
  ∀ la, lap_norm (- la) = (- lap_norm la)%lap.
Proof.
intros Hop *.
unfold lap_norm, lap_opp.
rewrite map_rev.
f_equal.
rewrite fold_lap_opp.
induction la as [| a]; [ easy | cbn ].
rewrite fold_lap_opp.
do 2 rewrite strip_0s_app.
symmetry; rewrite fold_lap_opp; symmetry.
rewrite IHla; cbn.
clear IHla.
remember (strip_0s (rev la)) as lb; clear la Heqlb.
induction lb as [| b]; cbn. {
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [Hoaz| Hoaz]. {
    apply (rngl_eqb_eq Heb) in Hoaz.
    apply (f_equal rngl_opp) in Hoaz.
    rewrite (rngl_opp_involutive Hop) in Hoaz.
    rewrite (rngl_opp_0 Hop) in Hoaz; subst a.
    now rewrite (rngl_eqb_refl Heb).
  }
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [Haz| Haz]; [ | easy ].
  apply (rngl_eqb_eq Heb) in Haz; subst a.
  rewrite (rngl_opp_0 Hop) in Hoaz.
  now rewrite (rngl_eqb_refl Heb) in Hoaz.
}
f_equal.
now rewrite map_app.
Qed.

Theorem lap_sub_norm_idemp_r :
  rngl_has_opp = true →
  ∀ la lb, lap_norm (la - lap_norm lb) = lap_norm (la - lb).
Proof.
intros Hop *.
unfold lap_sub.
rewrite <- (lap_opp_norm Hop).
now rewrite lap_add_norm_idemp_r.
Qed.

Theorem lap_add_assoc : ∀ al1 al2 al3,
  (al1 + (al2 + al3))%lap = ((al1 + al2) + al3)%lap.
Proof.
intros al1 al2 al3.
revert al2 al3.
induction al1; intros; [ easy | ].
destruct al2; [ easy | cbn ].
destruct al3; [ easy | cbn ].
rewrite rngl_add_assoc.
now rewrite IHal1.
Qed.

Theorem polyn_add_assoc : ∀ pa pb pc,
  (pa + (pb + pc) = (pa + pb) + pc)%pol.
Proof.
intros (la, lapr) (lb, lbpr) (lc, lcpr).
apply eq_polyn_eq.
cbn - [ lap_norm ].
rewrite lap_add_norm_idemp_l.
rewrite lap_add_norm_idemp_r.
now rewrite lap_add_assoc.
Qed.

(* addition to 0 *)

Theorem last_lap_neq_0_lap_norm : ∀ la,
  has_polyn_prop la = true
  → lap_norm la = la.
Proof.
intros * lapr.
unfold has_polyn_prop in lapr.
apply Bool.orb_true_iff in lapr.
destruct lapr as [lapr| lapr]; [ now destruct la | ].
apply (rngl_neqb_neq Heb) in lapr.
destruct la as [| a] using rev_ind; [ easy | cbn ].
clear IHla.
rewrite last_last in lapr.
unfold lap_norm.
rewrite rev_app_distr; cbn.
apply (rngl_eqb_neq Heb) in lapr.
rewrite lapr; cbn.
now rewrite rev_involutive.
Qed.

Theorem polyn_add_0_l : ∀ p, (0 + p)%pol = p.
Proof.
intros (la, lapr).
apply eq_polyn_eq; cbn.
now apply last_lap_neq_0_lap_norm.
Qed.

Theorem polyn_add_0_r : ∀ p, (p + 0)%pol = p.
Proof.
intros (la, lapr).
apply eq_polyn_eq; cbn.
rewrite lap_add_0_r.
now apply last_lap_neq_0_lap_norm.
Qed.

(* associativity of multiplication *)

Theorem lap_convol_mul_0_l : ∀ la lb i len,
  (∀ i, nth i la 0%F = 0%F)
  → lap_norm (lap_convol_mul la lb i len) = [].
Proof.
intros * Ha.
revert i.
induction len; intros; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (rev _)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  rewrite all_0_rngl_summation_0. 2: {
    intros j Hj.
    now rewrite Ha, rngl_mul_0_l.
  }
  cbn.
  now rewrite rngl_eqb_refl.
}
unfold lap_norm in IHlen.
specialize (IHlen (S i)).
rewrite Hlc in IHlen.
now apply List_eq_rev_nil in IHlen.
Qed.

Theorem lap_convol_mul_0_r : ∀ la lb i len,
  (∀ i, nth i lb 0%F = 0%F)
  → lap_norm (lap_convol_mul la lb i len) = [].
Proof.
intros * Hb.
revert i.
induction len; intros; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (rev _)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  rewrite all_0_rngl_summation_0. 2: {
    intros j Hj.
    rewrite Hb, rngl_mul_0_r; [ easy | easy ].
  }
  cbn.
  now rewrite rngl_eqb_refl.
}
unfold lap_norm in IHlen.
specialize (IHlen (S i)).
rewrite Hlc in IHlen.
now apply List_eq_rev_nil in IHlen.
Qed.

Theorem lap_convol_mul_cons_with_0_l : ∀ a la lb i len,
  (∀ i, nth i la 0%F = 0%F)
  → lap_convol_mul (a :: la) lb i len = lap_convol_mul [a] lb i len.
Proof.
intros * Hla.
revert i.
induction len; intros; [ easy | ].
cbn.
f_equal; [ | apply IHlen ].
apply rngl_summation_eq_compat.
intros j Hj.
destruct j; [ easy | ].
rewrite Tauto_match_nat_same.
now rewrite Hla.
Qed.

Theorem lap_convol_mul_succ : ∀ la lb i len,
  lap_convol_mul la lb i (S len) =
  lap_convol_mul la lb i len ++
    [∑ (j = 0, i + len),
     List.nth j la 0 * List.nth (i + len - j) lb 0]%F.
Proof.
intros.
cbn.
revert i.
induction len; intros. {
  now rewrite Nat.add_0_r.
}
cbn.
f_equal.
specialize (IHlen (S i)).
cbn in IHlen.
rewrite Nat.add_succ_r.
apply IHlen.
Qed.

Theorem lap_norm_app_0_r : ∀ la lb,
  (∀ i, nth i lb 0%F = 0%F)
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
  now rewrite rngl_eqb_refl.
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
intros * Habl.
induction n; [ rewrite Nat.add_0_r; reflexivity | idtac ].
rewrite Nat.add_succ_r.
rewrite lap_convol_mul_succ.
rewrite IHn.
apply lap_norm_app_0_r.
intros j.
rewrite all_0_rngl_summation_0. {
  destruct j; [ easy | now destruct j ].
}
clear j.
intros j (_, Hj).
destruct (le_dec (length la) j) as [H1| H1]. {
  rewrite List.nth_overflow; [ | easy ].
  now apply rngl_mul_0_l.
} {
  apply Nat.nle_gt in H1.
  destruct (le_dec (length lb) (i + (len + n) - j)) as [H2| H2]. {
    rewrite (nth_overflow _ _ H2).
    now apply rngl_mul_0_r.
  } {
    exfalso; apply H2; clear H2.
    flia Habl H1.
  }
}
Qed.

Theorem lap_convol_mul_app_rep_0_l : ∀ la lb i len n,
  lap_norm (lap_convol_mul (la ++ repeat 0%F n) lb i len) =
  lap_norm (lap_convol_mul la lb i len).
Proof.
intros.
revert la i len.
induction n; intros. {
  now cbn; rewrite app_nil_r.
}
cbn.
rewrite List_cons_is_app.
rewrite app_assoc.
rewrite IHn; clear n IHn.
revert la i.
induction len; intros; [ easy | ].
cbn.
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
  apply rngl_summation_eq_compat.
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
  apply rngl_summation_eq_compat.
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

Theorem lap_convol_mul_app_rep_0_r : ∀ la lb i len n,
  lap_norm (lap_convol_mul la (lb ++ repeat 0%F n) i len) =
  lap_norm (lap_convol_mul la lb i len).
Proof.
intros.
revert lb i len.
induction n; intros; [ now cbn; rewrite app_nil_r | cbn ].
rewrite List_cons_is_app.
rewrite app_assoc.
rewrite IHn; clear n IHn.
revert la i.
induction len; intros; [ easy | cbn ].
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
  apply rngl_summation_eq_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec (i - j) (length lb)) as [Hjla| Hjla]. {
    now rewrite app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (nth_overflow lb); [ | easy ].
  rewrite app_nth2; [ | easy ].
  destruct (Nat.eq_dec (i - j) (length lb)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
} {
  f_equal; f_equal.
  apply rngl_summation_eq_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec (i - j) (length lb)) as [Hjla| Hjla]. {
    now rewrite app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (nth_overflow lb); [ | easy ].
  rewrite app_nth2; [ | easy ].
  destruct (Nat.eq_dec (i - j) (length lb)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
}
Qed.

Theorem lap_norm_convol_mul_norm_r : ∀ la lb i len,
  lap_norm (lap_convol_mul la (lap_norm lb) i len) =
  lap_norm (lap_convol_mul la lb i len).
Proof.
intros.
rewrite (lap_norm_app_repeat_0 lb) at 2.
now rewrite lap_convol_mul_app_rep_0_r.
Qed.

Theorem lap_norm_cons_norm : ∀ a la lb i len,
  length (a :: la) + length lb - 1 ≤ i + len
  → lap_norm (lap_convol_mul (a :: lap_norm la) lb i len) =
    lap_norm (lap_convol_mul (a :: la) lb i len).
Proof.
intros * Hlen.
rewrite (lap_norm_app_repeat_0 la) at 2.
rewrite app_comm_cons.
now rewrite lap_convol_mul_app_rep_0_l.
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
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [Haz| Haz]. {
    cbn.
    apply (rngl_eqb_eq Heb) in Haz.
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

Theorem all_0_all_rev_0 : ∀ la : list T,
  (∀ i, nth i la 0%F = 0%F)
  ↔ (∀ i, nth i (rev la) 0%F = 0%F).
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

Theorem eq_strip_0s_rev_nil : ∀ la,
  strip_0s (rev la) = [] ↔ ∀ i, nth i la 0%F = 0%F.
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

Theorem lap_mul_norm_idemp_r : ∀ la lb,
  lap_norm (la * lap_norm lb)%lap = lap_norm (la * lb)%lap.
Proof.
intros.
unfold "*"%lap; cbn.
destruct la as [| a]; [ easy | cbn ].
unfold lap_norm.
remember (strip_0s (rev lb)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  specialize (proj1 (eq_strip_0s_nil _) Hlc) as H1.
  destruct lb as [| b]; [ easy | ].
  cbn.
  rewrite fold_lap_norm.
  symmetry; apply lap_convol_mul_0_r.
  intros i.
  specialize (H1 (length lb - i)).
  rewrite rev_nth in H1; [ | cbn; flia ].
  cbn in H1.
  destruct (le_dec i (length lb)) as [Hib| Hib]. 2: {
    apply Nat.nle_gt in Hib.
    now rewrite nth_overflow.
  }
  now replace (length lb - (length lb - i)) with i in H1 by flia Hib.
}
cbn.
rewrite fold_lap_norm.
destruct lb as [| b]; [ easy | ].
remember (b :: lb) as d eqn:Hd.
replace (rev lc ++ [c]) with (rev (c :: lc)) by easy.
rewrite <- Hlc.
rewrite fold_lap_norm.
do 2 rewrite Nat.sub_0_r.
clear c lc b lb Hlc Hd.
rename d into lb.
remember (lap_norm lb) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]. {
  rewrite fold_lap_norm.
  unfold lap_norm in Hlc.
  apply List_eq_rev_nil in Hlc.
  specialize (proj1 (eq_strip_0s_rev_nil lb) Hlc) as H1.
  clear Hlc; rename H1 into Hlb.
  now rewrite lap_convol_mul_0_r.
}
cbn.
rewrite fold_lap_norm.
rewrite (lap_convol_mul_more (length lb - S (length lc))). 2: {
  now cbn; rewrite Nat.sub_0_r.
}
rewrite <- Nat.add_assoc.
rewrite (Nat.add_comm (S (length lc))).
rewrite Nat.sub_add. 2: {
  etransitivity; [ | apply lap_norm_length_le ].
  now rewrite Hlc.
}
rewrite <- Hlc.
apply lap_norm_convol_mul_norm_r.
Qed.

Theorem eq_lap_norm_eq_length : ∀ la lb,
  lap_norm la = lap_norm lb
  → length la = length lb
  → la = lb.
Proof.
intros * Hll Hlen.
unfold lap_norm in Hll.
apply List_rev_rev in Hll.
setoid_rewrite <- rev_length in Hlen.
enough (H : rev la = rev lb) by now apply List_rev_rev in H.
remember (rev la) as l; clear la Heql; rename l into la.
remember (rev lb) as l; clear lb Heql; rename l into lb.
revert la Hll Hlen.
induction lb as [| b]; intros. {
  now apply length_zero_iff_nil in Hlen.
}
destruct la as [| a]; [ easy | ].
cbn in Hll, Hlen.
apply Nat.succ_inj in Hlen.
do 2 rewrite if_bool_if_dec in Hll.
destruct (bool_dec _) as [Haz| Haz]. {
  apply (rngl_eqb_eq Heb) in Haz; subst a.
  destruct (bool_dec _) as [Hbz| Hbz]. {
    apply (rngl_eqb_eq Heb) in Hbz; subst b.
    f_equal.
    now apply IHlb.
  }
  exfalso; clear - Hbz Hll Hlen.
  assert (H : length la ≤ length lb) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction la as [| a]; [ easy | ].
  cbn in Hll.
  rewrite if_bool_if_dec in Hll.
  destruct (bool_dec _) as [Haz| Haz]. {
    cbn in Hlen.
    clear a Haz.
    apply IHla; [ easy | flia Hlen ].
  }
  rewrite Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
destruct (bool_dec _) as [Hbz| Hbz]. {
  exfalso; clear b Hbz.
  clear - Haz Hll Hlen.
  assert (H : length lb ≤ length la) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction lb as [| b]; [ easy | ].
  cbn in Hll.
  rewrite if_bool_if_dec in Hll.
  destruct (bool_dec _) as [Hbz| Hbz]. {
    cbn in Hlen.
    clear b Hbz.
    apply IHlb; [ easy | flia Hlen ].
  }
  rewrite <- Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
easy.
Qed.

Theorem list_nth_lap_eq : ∀ la lb,
  (∀ i, (List.nth i la 0 = List.nth i lb 0)%F)
  → lap_norm la = lap_norm lb.
Proof.
intros la lb Hi.
unfold lap_norm; f_equal.
revert lb Hi.
induction la as [| a]; intros. {
  induction lb as [| b]; [ reflexivity | ].
  specialize (Hi 0) as H; cbn in H.
  subst b; cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (rev lb)) as lc eqn:Hlc; symmetry in Hlc.
  rewrite (rngl_eqb_refl Heb).
  destruct lc as [| c]; [ easy | ].
  assert (H : lap_norm [] = lap_norm lb). {
    unfold lap_norm; cbn.
    cbn in IHlb.
    change (rev [] = rev (strip_0s (rev lb))).
    f_equal.
    rewrite Hlc.
    apply IHlb.
    intros i; cbn; rewrite Tauto_match_nat_same.
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
    assert (Hla : ∀ i, nth i la 0%F = 0%F). {
      intros i.
      clear - Heb Hlc.
      revert i.
      induction la as [| a]; intros; cbn. {
        now rewrite Tauto_match_nat_same.
      }
      destruct i. {
        cbn in Hlc.
        rewrite strip_0s_app in Hlc; cbn in Hlc.
        remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
        destruct lb as [| b]; [ | easy ].
        rewrite if_bool_if_dec in Hlc.
        destruct (bool_dec _) as [Haz| Haz]; [ | easy ].
        now apply (rngl_eqb_eq Heb) in Haz.
      }
      apply IHla.
      cbn in Hlc.
      rewrite strip_0s_app in Hlc; cbn in Hlc.
      remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
      destruct lb as [| b]; [ easy | easy ].
    }
    cbn.
    rewrite if_bool_if_dec.
    destruct (bool_dec _) as [Haz| Haz]. {
      apply (rngl_eqb_eq Heb) in Haz.
      assert (Hlb : ∀ i, nth i lb 0%F = 0%F). {
        intros.
        rewrite <- Hi; cbn.
        destruct i; [ easy | ].
        apply Hla.
      }
      clear - Heb Hlb.
      induction lb as [| b]; [ easy | cbn ].
      specialize (Hlb 0) as H1; cbn in H1; subst b.
      rewrite strip_0s_app; cbn.
      rewrite (rngl_eqb_refl Heb).
      rewrite <- IHlb; [ easy | ].
      intros i.
      now specialize (Hlb (S i)).
    }
    apply (rngl_eqb_neq Heb) in Haz.
    destruct lb as [| b]; [ now specialize (Hi 0); cbn in Hi | cbn ].
    rewrite strip_0s_app; cbn.
    remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
    destruct ld as [| d]. {
      rewrite if_bool_if_dec.
      destruct (bool_dec _) as [Hbz| Hbz]. {
        apply (rngl_eqb_eq Heb) in Hbz; subst b.
        now specialize (Hi 0).
      }
      f_equal.
      now specialize (Hi 0).
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, nth i la 0%F = nth i lb 0%F). {
      intros i.
      now specialize (Hi (S i)); cbn in Hi.
    }
    specialize (IHla H); clear H.
    now rewrite Hld in IHla.
  }
  destruct lb as [| b]. {
    specialize (IHla []).
    assert (H : ∀ i : nat, nth i la 0%F = nth i [] 0%F). {
      intros i; cbn; rewrite Tauto_match_nat_same.
      now specialize (Hi (S i)).
    }
    now specialize (IHla H).
  }
  cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
  destruct ld as [| d]. {
    rewrite if_bool_if_dec.
    destruct (bool_dec _) as [Hbz| Hbz]. {
      apply (rngl_eqb_eq Heb) in Hbz; subst b.
      specialize (IHla lb).
      assert (H : ∀ i : nat, nth i la 0%F = nth i lb 0%F). {
        intros i.
        now specialize (Hi (S i)); cbn in Hi.
      }
      specialize (IHla H); clear H.
      now rewrite Hld in IHla.
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, nth i la 0%F = nth i lb 0%F). {
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

Theorem eq_lap_convol_mul_nil : ∀ la lb i len,
  lap_convol_mul la lb i len = [] → len = 0.
Proof. now intros; induction len. Qed.

Theorem list_nth_lap_convol_mul_aux : ∀ la lb n i len,
  List.length la + List.length lb - 1 = (i + len)%nat
  → (List.nth n (lap_convol_mul la lb i len) 0%F =
     ∑ (j = 0, n + i),
     List.nth j la 0 * List.nth (n + i - j) lb 0)%F.
Proof.
intros * Hlen.
revert la lb i n Hlen.
induction len; intros. {
  cbn.
  rewrite Nat.add_0_r in Hlen.
  rewrite all_0_rngl_summation_0; [ now destruct n | ].
  intros j (_, Hj).
  destruct (le_dec (length la) j) as [H1| H1]. {
    rewrite List.nth_overflow; [ | easy ].
    now rewrite rngl_mul_0_l.
  }
  destruct (le_dec (length lb) (n + i - j)) as [H2| H2]. {
    rewrite (nth_overflow _ _ H2).
    now apply rngl_mul_0_r.
  }
  exfalso; apply H2; clear Hj H2.
  apply Nat.nle_gt in H1; subst i.
  flia H1.
}
cbn.
destruct n; [ easy | ].
rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
rewrite IHlen; [ | easy ].
now rewrite Nat.add_succ_r, <- Nat.add_succ_l.
Qed.

(* to be unified perhaps with list_nth_convol_mul below *)
Theorem list_nth_lap_convol_mul : ∀ la lb i len,
  len = length la + length lb - 1
  → (List.nth i (lap_convol_mul la lb 0 len) 0 =
     ∑ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%F.
Proof.
intros * Hlen.
symmetry in Hlen.
rewrite list_nth_lap_convol_mul_aux; [ | easy ].
now rewrite Nat.add_0_r.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul_r : ∀ la lb lc k,
   (∑ (i = 0, k),
      nth i lc 0 *
      nth (k - i) (lap_convol_mul la lb 0 (length la + length lb - 1))  0 =
    ∑ (i = 0, k),
      nth (k - i) lc 0 *
      ∑ (j = 0, i), nth j la 0 * nth (i - j) lb 0)%F.
Proof.
intros la lb lc k.
rewrite rngl_summation_rtl.
apply rngl_summation_eq_compat; intros i (_, Hi).
rewrite Nat.add_0_r.
f_equal.
rewrite Nat_sub_sub_distr; [ | easy ].
rewrite Nat.add_comm, Nat.add_sub.
now apply list_nth_lap_convol_mul.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul_l : ∀ la lb lc k,
  ∑ (i = 0, k),
    nth i (lap_convol_mul la lb 0 (length la + length lb - 1)) 0 *
    nth (k - i) lc 0 =
  ∑ (i = 0, k),
    (∑ (j = 0, i), nth j la 0 * nth (i - j) lb 0) *
    nth (k - i) lc 0.
Proof.
intros la lb lc k.
apply rngl_summation_eq_compat; intros i (_, Hi).
f_equal.
now rewrite list_nth_lap_convol_mul.
Qed.

Theorem lap_norm_mul_assoc : ∀ la lb lc,
  lap_norm (la * (lb * lc))%lap = lap_norm (la * lb * lc)%lap.
Proof.
intros la lb lc.
unfold lap_mul.
destruct lc as [| c]. {
  destruct la as [| a]; [ easy | ].
  destruct lb as [| b]; [ easy | cbn ].
  now rewrite <- Nat.add_succ_comm.
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
  rewrite Tauto_match_nat_same.
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
  cbn; rewrite Tauto_match_nat_same.
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
rewrite list_nth_lap_convol_mul; [ | easy ].
rewrite list_nth_lap_convol_mul; [ | easy ].
rewrite <- Hld, <- Hle.
rewrite summation_mul_list_nth_lap_convol_mul_r.
rewrite summation_mul_list_nth_lap_convol_mul_l.
move d before c; move e before d.
move lb' before la'; move ld before lc; move lc' before lb'.
move le before ld.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_mul_summation_distr_r; [ | easy ].
  remember (∑ (j = 0, i), _) as x; subst x.
  easy.
}
cbn.
rewrite rngl_summation_summation_exch.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite <- rngl_mul_assoc.
  }
  cbn.
  rewrite <- rngl_mul_summation_distr_l; [ | easy ].
  remember (∑ (j = _, _), _) as x; subst x.
  easy.
}
cbn.
symmetry.
rewrite rngl_summation_rtl.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite Nat.add_0_r.
  rewrite Nat_sub_sub_distr; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  easy.
}
cbn.
apply rngl_summation_eq_compat.
intros i Hi.
f_equal.
symmetry.
rewrite (rngl_summation_shift i); [ | easy ].
rewrite Nat.sub_diag.
remember (∑ (j = _, _), _) as x; subst x.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite Nat.sub_add_distr.
  rewrite Nat_sub_sub_swap.
  easy.
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

Theorem lap_mul_length : ∀ la lb,
  length (la * lb)%lap =
    match (la, lb) with
    | ([], _) | (_, []) => 0
    | _ => length (la ++ lb) - 1
    end.
Proof.
intros.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | cbn ].
rewrite Nat.sub_0_r, Nat.add_succ_r; cbn.
f_equal.
rewrite lap_convol_mul_length.
rewrite Nat.sub_0_r, app_length; cbn.
now rewrite Nat.add_succ_r.
Qed.

Theorem lap_mul_assoc : ∀ la lb lc,
  (la * (lb * lc))%lap = ((la * lb) * lc)%lap.
Proof.
intros.
apply eq_lap_norm_eq_length. 2: {
  destruct la as [| a]; [ easy | ].
  destruct lb as [| b]; [ easy | ].
  destruct lc as [| c]. {
    unfold "*"%lap.
    now destruct (lap_convol_mul _ _ _ _).
  }
  cbn.
  do 4 (rewrite Nat.add_succ_r; cbn); f_equal.
  rewrite rngl_summation_only_one; cbn.
  rewrite rngl_summation_only_one; cbn.
  do 4 rewrite lap_convol_mul_length.
  apply Nat.add_assoc.
}
apply lap_norm_mul_assoc.
Qed.

Theorem polyn_mul_assoc : ∀ p1 p2 p3,
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
unfold polyn_norm at 1 3.
apply eq_polyn_eq; cbn.
rewrite lap_mul_norm_idemp_l.
rewrite lap_mul_norm_idemp_r.
now rewrite lap_mul_assoc.
Qed.

Theorem lap_convol_mul_const_l : ∀ a la i len,
  length la = i + len
  → lap_convol_mul [a] la i len =
    map (λ b, (a * b)%F) (skipn i la).
Proof.
intros * Hlen.
revert i Hlen.
induction len; intros. {
  rewrite Nat.add_0_r in Hlen; rewrite <- Hlen.
  now rewrite skipn_all.
}
cbn - [ nth ].
rewrite rngl_summation_split_first; [ | easy ].
rewrite all_0_rngl_summation_0. 2: {
  intros j Hj.
  destruct j; [ flia Hj | cbn ].
  rewrite Tauto_match_nat_same.
  now apply rngl_mul_0_l.
}
rewrite Nat.sub_0_r, rngl_add_0_r; cbn.
rewrite IHlen; [ | now rewrite Nat.add_succ_r in Hlen ].
symmetry.
rewrite (List_skipn_is_cons 0%F); [ easy | flia Hlen ].
Qed.

Theorem lap_convol_mul_const_r : ∀ a la i len,
  length la = i + len
  → lap_convol_mul la [a] i len =
    map (λ b, (b * a)%F) (skipn i la).
Proof.
intros * Hlen.
revert i Hlen.
induction len; intros. {
  rewrite Nat.add_0_r in Hlen; rewrite <- Hlen.
  now rewrite skipn_all.
}
cbn - [ nth ].
rewrite rngl_summation_split_last; [ | easy ].
rewrite all_0_rngl_summation_0. 2: {
  intros j Hj.
  replace (i - (j - 1)) with (S (i - j)) by flia Hj; cbn.
  rewrite Tauto_match_nat_same.
  now apply rngl_mul_0_r.
}
rewrite Nat.sub_diag, rngl_add_0_l; cbn.
rewrite IHlen; [ | flia Hlen ].
symmetry.
rewrite (List_skipn_is_cons 0%F); [ easy | flia Hlen ].
Qed.

Theorem lap_convol_mul_1_l : ∀ la i len,
  length la = i + len
  → lap_convol_mul [1%F] la i len = skipn i la.
Proof.
intros * Hlen.
rewrite lap_convol_mul_const_l; [ | easy ].
erewrite map_ext_in. 2: {
  intros a Ha.
  now rewrite rngl_mul_1_l.
}
apply map_id.
Qed.

Theorem lap_convol_mul_1_r : ∀ la i len,
  length la = i + len
  → lap_convol_mul la [1%F] i len = skipn i la.
Proof.
intros * Hlen.
rewrite lap_convol_mul_const_r; [ | easy ].
erewrite map_ext_in. 2: {
  intros a Ha.
  now rewrite rngl_mul_1_r.
}
apply map_id.
Qed.

Theorem lap_mul_1_l : ∀ la, (1 * la)%lap = la.
Proof.
intros.
unfold lap_mul, lap_one.
destruct (bool_dec true) as [H| ]; [ clear H | easy ].
destruct la as [| a]; [ easy | cbn ].
rewrite rngl_summation_only_one.
rewrite rngl_mul_1_l; f_equal.
now rewrite lap_convol_mul_1_l.
Qed.

Theorem lap_mul_1_r : ∀ la, (la * 1)%lap = la.
Proof.
intros la.
unfold lap_mul, lap_one; cbn.
destruct la as [| a]; [ easy | cbn ].
rewrite Nat.sub_0_r.
apply lap_convol_mul_1_r.
now rewrite Nat.add_1_r.
Qed.

Theorem polyn_mul_1_l : ∀ p, (1 * p)%pol = p.
Proof.
intros (la, lapr).
unfold "*"%pol.
cbn - [ lap_mul ].
rewrite lap_mul_1_l.
apply eq_polyn_eq; cbn.
now apply last_lap_neq_0_lap_norm.
Qed.

(* distributivity *)

Fixpoint lap_convol_mul_add_l (al1 al2 al3 : list T) i len :=
  match len with
  | O => []
  | S len1 =>
      (∑ (j = 0, i),
       (List.nth j al1 0 + List.nth j al2 0) *
       List.nth (i - j) al3 0)%F ::
       lap_convol_mul_add_l al1 al2 al3 (S i) len1
  end.

Fixpoint lap_convol_mul_add_r (al1 al2 al3 : list T) i len :=
  match len with
  | O => []
  | S len1 =>
      (∑ (j = 0, i),
       List.nth j al1 0 *
       (List.nth (i - j) al2 0 + List.nth (i - j) al3 0))%F ::
       lap_convol_mul_add_r al1 al2 al3 (S i) len1
  end.

Theorem list_nth_lap_add : ∀ k la lb,
  (List.nth k (lap_add la lb) 0 =
   List.nth k la 0 + List.nth k lb 0)%F.
Proof.
intros k la lb.
revert la lb.
induction k; intros. {
  destruct la as [| a]; cbn; [ now rewrite rngl_add_0_l | ].
  destruct lb as [| b]; cbn; [ now rewrite rngl_add_0_r | ].
  easy.
} {
  destruct la as [| a]; cbn; [ now rewrite rngl_add_0_l | ].
  destruct lb as [| b]; cbn; [ now rewrite rngl_add_0_r | ].
  apply IHk.
}
Qed.

Theorem list_nth_lap_opp :
  rngl_has_opp = true →
  ∀ k la, (List.nth k (lap_opp la) 0 = - List.nth k la 0)%F.
Proof.
intros Hop *.
revert la.
induction k; intros. {
  destruct la as [| a]; cbn; [ now rewrite rngl_opp_0 | easy ].
}
destruct la as [| a]; cbn; [ now rewrite rngl_opp_0 | ].
apply IHk.
Qed.

Theorem list_nth_lap_sub :
  rngl_has_opp = true →
  ∀ k la lb,
  (List.nth k (lap_sub la lb) 0 =
   List.nth k la 0 - List.nth k lb 0)%F.
Proof.
intros Hop *.
unfold lap_sub.
rewrite list_nth_lap_add.
rewrite (list_nth_lap_opp Hop).
now rewrite (fold_rngl_sub Hop).
Qed.

Theorem lap_convol_mul_lap_add_l : ∀ la lb lc i len,
  lap_convol_mul (la + lb)%lap lc i len = lap_convol_mul_add_l la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
apply rngl_summation_eq_compat; intros j (_, Hj).
f_equal.
now rewrite list_nth_lap_add.
Qed.

Theorem lap_convol_mul_lap_add_r : ∀ la lb lc i len,
  lap_convol_mul la (lb + lc)%lap i len = lap_convol_mul_add_r la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
apply rngl_summation_eq_compat; intros j (_, Hj).
f_equal.
now rewrite list_nth_lap_add.
Qed.

Theorem lap_add_lap_convol_mul_l : ∀ la lb lc i len,
  (lap_convol_mul la lc i len + lap_convol_mul lb lc i len)%lap =
  lap_convol_mul_add_l la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
rewrite <- rngl_summation_add_distr.
apply rngl_summation_eq_compat; intros j (_, Hj).
now rewrite rngl_mul_add_distr_r.
Qed.

Theorem lap_add_lap_convol_mul_r : ∀ la lb lc i len,
  (lap_convol_mul la lb i len + lap_convol_mul la lc i len)%lap =
  lap_convol_mul_add_r la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
rewrite <- rngl_summation_add_distr.
apply rngl_summation_eq_compat; intros j (_, Hj).
now rewrite rngl_mul_add_distr_l.
Qed.

Theorem lap_norm_mul_add_distr_l : ∀ la lb lc,
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
rewrite lap_convol_mul_lap_add_r.
now rewrite lap_add_lap_convol_mul_r.
Qed.

Theorem lap_mul_opp_l :
  rngl_has_opp = true →
  ∀ la lb, (- la * lb = - (la * lb))%lap.
Proof.
intros Hop *.
unfold lap_opp, lap_mul.
destruct la as [| a]; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
do 2 rewrite Nat.sub_0_r.
rewrite map_length.
remember 0 as i; clear Heqi.
remember (length la + S (length lb)) as len; clear Heqlen.
revert i.
induction len; intros; [ easy | cbn ].
f_equal; [ | apply IHlen ].
rewrite (rngl_opp_summation Hop).
apply rngl_summation_eq_compat.
intros j Hj.
destruct j; [ now rewrite (rngl_mul_opp_l Hop) | ].
rewrite <- (rngl_mul_opp_l Hop).
f_equal.
destruct (lt_dec j (length la)) as [Hjla| Hjla]. 2: {
  apply Nat.nlt_ge in Hjla.
  rewrite nth_overflow; [ | now rewrite map_length ].
  rewrite nth_overflow; [ | easy ].
  symmetry; apply (rngl_opp_0 Hop).
}
now rewrite (List_map_nth' 0%F).
Qed.

Theorem lap_mul_opp_r :
  rngl_has_opp = true →
  ∀ la lb, (la * - lb = - (la * lb))%lap.
Proof.
intros Hop *.
unfold lap_opp, lap_mul.
destruct la as [| a]; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
do 2 rewrite Nat.sub_0_r.
rewrite map_length.
remember 0 as i; clear Heqi.
remember (length la + S (length lb)) as len; clear Heqlen.
revert i.
induction len; intros; [ easy | cbn ].
f_equal; [ | apply IHlen ].
rewrite (rngl_opp_summation Hop).
apply rngl_summation_eq_compat.
intros j Hj.
destruct j. {
  rewrite Nat.sub_0_r.
  rewrite <- (rngl_mul_opp_r Hop); f_equal.
  destruct i; [ easy | cbn ].
  destruct (lt_dec i (length lb)) as [Hilb| Hilb]. 2: {
    apply Nat.nlt_ge in Hilb.
    rewrite nth_overflow; [ | now rewrite map_length ].
    rewrite nth_overflow; [ | easy ].
    symmetry; apply (rngl_opp_0 Hop).
  }
  now rewrite (List_map_nth' 0%F).
}
rewrite <- (rngl_mul_opp_r Hop); f_equal.
destruct (i - S j) as [| k]; [ easy | ].
destruct (lt_dec k (length lb)) as [Hklb| Hklb]. 2: {
  apply Nat.nlt_ge in Hklb.
  rewrite nth_overflow; [ | now rewrite map_length ].
  rewrite nth_overflow; [ | easy ].
  symmetry; apply (rngl_opp_0 Hop).
}
now rewrite (List_map_nth' 0%F).
Qed.

Theorem lap_norm_mul_sub_distr_l :
  rngl_has_opp = true →
  ∀ la lb lc,
  lap_norm (la * (lb - lc))%lap = lap_norm (la * lb - la * lc)%lap.
Proof.
intros Hop *.
unfold lap_sub.
rewrite lap_norm_mul_add_distr_l.
now rewrite (lap_mul_opp_r Hop).
Qed.

Theorem lap_norm_mul_add_distr_r : ∀ la lb lc : list T,
  lap_norm ((la + lb) * lc) = lap_norm (la * lc + lb * lc).
Proof.
intros la lb lc.
unfold lap_mul.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]. {
  cbn.
  destruct lc as [| c]; [ easy | ].
  cbn; rewrite Nat.sub_0_r.
  now rewrite lap_add_0_r.
}
destruct lc as [| c]; [ easy | ].
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
remember (length (la' + lb')%lap + length lc' - 1) as labc.
remember (length la' + length lc' - 1) as lac.
remember (length lb' + length lc' - 1) as lbc.
rewrite Heqlabc.
remember (la' + lb')%lap as lab.
symmetry in Heqlab.
destruct lab as [| ab]; [ now subst la' lb' | ].
rewrite <- Heqlab in Heqlabc |-*.
rewrite lap_convol_mul_more with (n := (lac + lbc)%nat). 2: {
  subst; flia.
}
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite <- lap_add_norm_idemp_l.
rewrite lap_convol_mul_more with (n := (labc + lbc)%nat); [ | now subst lac ].
rewrite <- Heqlab.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_comm.
rewrite <- lap_add_norm_idemp_l.
rewrite Heqlbc.
rewrite lap_convol_mul_more with (n := (labc + lac)%nat); [ | flia ].
rewrite lap_add_norm_idemp_l.
rewrite <- Heqlbc.
rewrite Nat.add_comm.
rewrite lap_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite lap_convol_mul_lap_add_l.
now rewrite lap_add_lap_convol_mul_l.
Qed.

Theorem lap_mul_add_distr_l : ∀ la lb lc,
  (la * (lb + lc))%lap = (la * lb + la * lc)%lap.
Proof.
intros la lb lc.
apply eq_lap_norm_eq_length. 2: {
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
}
apply lap_norm_mul_add_distr_l.
Qed.

Theorem lap_mul_sub_distr_l :
  rngl_has_opp = true →
  ∀ la lb lc, (la * (lb - lc))%lap = (la * lb - la * lc)%lap.
Proof.
intros Hop *.
unfold lap_sub.
rewrite <- (lap_mul_opp_r Hop).
now rewrite <- lap_mul_add_distr_l.
Qed.

Theorem lap_mul_add_distr_r : ∀ la lb lc,
  ((la + lb) * lc)%lap = (la * lc + lb * lc)%lap.
Proof.
intros la lb lc.
apply eq_lap_norm_eq_length. 2: {
  destruct la as [| a]; [ easy | ].
  destruct lb as [| b]. {
    destruct lc as [| c]; [ easy | ].
    now cbn; rewrite lap_add_0_r.
  }
  cbn.
  destruct lc as [| c]; [ easy | ].
  cbn; do 3 rewrite Nat.sub_0_r.
  do 3 (rewrite Nat.add_succ_r; cbn); f_equal.
  rewrite lap_convol_mul_length.
  do 2 rewrite lap_add_length; cbn.
  do 2 rewrite lap_convol_mul_length.
  now rewrite Nat.add_max_distr_r.
}
apply lap_norm_mul_add_distr_r.
Qed.

Theorem lap_mul_sub_distr_r :
  rngl_has_opp = true →
  ∀ la lb lc, ((la - lb) * lc)%lap = (la * lc - lb * lc)%lap.
Proof.
intros Hop *.
unfold lap_sub.
rewrite <- (lap_mul_opp_l Hop).
now rewrite <- lap_mul_add_distr_r.
Qed.

Theorem polyn_mul_add_distr_l : ∀ pa pb pc,
  (pa * (pb + pc))%pol = (pa * pb + pa * pc)%pol.
Proof.
intros.
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm.
rewrite lap_mul_norm_idemp_r.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_norm_idemp_r.
f_equal.
now rewrite lap_mul_add_distr_l.
Qed.

Theorem polyn_mul_add_distr_r :
  ∀ a b c : polyn T, ((a + b) * c)%pol = (a * c + b * c)%pol.
Proof.
intros.
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm.
rewrite lap_mul_norm_idemp_l.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_norm_idemp_r.
f_equal.
now rewrite lap_mul_add_distr_r.
Qed.

Theorem polyn_mul_sub_distr_r :
  rngl_has_opp = true →
  ∀ a b c : polyn T, ((a - b) * c)%pol = (a * c - b * c)%pol.
Proof.
intros Hop *.
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm.
rewrite lap_add_norm_idemp_r.
rewrite lap_mul_norm_idemp_l.
rewrite lap_add_norm_idemp_l.
rewrite fold_lap_norm.
rewrite (fold_lap_opp (lap_norm _)).
rewrite <- (lap_opp_norm Hop).
do 2 rewrite lap_add_norm_idemp_r.
do 2 rewrite fold_lap_sub.
f_equal.
apply (lap_mul_sub_distr_r Hop).
Qed.

(* 1 is not 0 *)

Theorem polyn_1_neq_0 :
  if rngl_has_1_neq_0 then 1%pol ≠ 0%pol else not_applicable.
Proof.
rewrite H10.
now intros H; apply eq_polyn_eq in H.
Qed.

(* optional multiplication commutativity *)

Theorem lap_convol_mul_comm : rngl_mul_is_comm = true →
  ∀ l1 l2 i len,
  lap_convol_mul l1 l2 i len = lap_convol_mul l2 l1 i len.
Proof.
intros Hic l1 l2 i len.
revert i.
induction len; intros; [ easy | cbn ].
rewrite IHlen; f_equal.
rewrite rngl_summation_rtl.
apply rngl_summation_eq_compat; intros j (_, Hj).
rewrite Nat.add_0_r.
rewrite (rngl_mul_comm Hic).
rewrite Nat_sub_sub_distr; [ | easy ].
now rewrite Nat.add_comm, Nat.add_sub.
Qed.

Theorem lap_mul_comm : rngl_mul_is_comm = true →
  ∀ a b, lap_mul a b = lap_mul b a.
Proof.
intros Hic la lb.
unfold lap_mul.
destruct la as [| a]; [ now destruct lb | cbn ].
rewrite <- Nat.add_succ_comm; cbn.
rewrite (Nat.add_comm (length lb)).
now rewrite lap_convol_mul_comm.
Qed.

Theorem polyn_opt_mul_comm :
  if rngl_mul_is_comm then ∀ a b : polyn T, (a * b)%pol = (b * a)%pol
  else not_applicable.
Proof.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply eq_polyn_eq; cbn.
now rewrite (lap_mul_comm Hic).
Qed.

(* optional right multiplication by 1; not required if multiplication
   is commutative *)

Theorem lap_mul_const_r : ∀ la a,
  (la * [a])%lap = map (λ b, (b * a)%F) la.
Proof.
intros.
unfold "*"%lap; cbn.
destruct la as [| b]; [ easy | cbn ].
rewrite Nat.sub_0_r.
rewrite Nat.add_1_r; cbn.
rewrite rngl_summation_only_one.
f_equal.
now apply lap_convol_mul_const_r.
Qed.

Theorem polyn_mul_1_r : ∀ a : polyn T, (a * 1)%pol = a.
Proof.
intros.
apply eq_polyn_eq; cbn.
rewrite lap_mul_1_r.
apply last_lap_neq_0_lap_norm.
now destruct a.
Qed.

Theorem polyn_opt_mul_1_r :
  if rngl_mul_is_comm then not_applicable else ∀ a : polyn T, (a * 1)%pol = a.
Proof.
destruct rngl_mul_is_comm; [ easy | ].
now apply polyn_mul_1_r.
Qed.

(* optional right distributivity; not required if multiplication
   is commutative *)

Theorem polyn_opt_mul_add_distr_r :
   if rngl_mul_is_comm then not_applicable
   else ∀ a b c : polyn T, ((a + b) * c)%pol = (a * c + b * c)%pol.
Proof.
destruct rngl_mul_is_comm; [ easy | ].
apply polyn_mul_add_distr_r.
Qed.

(* optional left addition of opposite; not existing if there is
   no opposite *)

Theorem lap_add_opp_l :
  rngl_has_opp = true
  → ∀ la, (- la + la)%lap = repeat 0%F (length la).
Proof.
intros Hop *.
induction la as [| a]; [ easy | cbn ].
rewrite (rngl_add_opp_l Hop).
now f_equal.
Qed.

Theorem lap_add_opp_r :
  rngl_has_opp = true
  → ∀ la, (la + - la)%lap = repeat 0%F (length la).
Proof.
intros Hop *.
induction la as [| a]; [ easy | cbn ].
rewrite fold_lap_opp.
rewrite fold_rngl_sub; [ | easy ].
rewrite rngl_sub_diag; [ | easy ].
now f_equal.
Qed.

Theorem lap_norm_repeat_0 : ∀ n, lap_norm (repeat 0%F n) = [].
Proof.
intros.
unfold lap_norm.
rewrite List_rev_repeat.
induction n; [ easy | cbn ].
now rewrite (rngl_eqb_refl Heb).
Qed.

Theorem lap_norm_add_opp_l :
  rngl_has_opp = true
  → ∀ la, lap_norm (- la + la)%lap = [].
Proof.
intros Hop *.
rewrite (lap_add_opp_l Hop).
apply lap_norm_repeat_0.
Qed.

Theorem lap_norm_add_opp_r :
  rngl_has_opp = true
  → ∀ la, lap_norm (la + - la)%lap = [].
Proof.
intros Hop *.
rewrite (lap_add_opp_r Hop).
apply lap_norm_repeat_0.
Qed.

Theorem polyn_add_opp_l :
  rngl_has_opp = true
  → ∀ a : polyn T, (- a + a)%pol = 0%pol.
Proof.
intros Hop *.
apply eq_polyn_eq.
destruct a as (la, Ha); cbn.
do 2 rewrite fold_lap_norm.
rewrite lap_add_norm_idemp_l.
now apply lap_norm_add_opp_l.
Qed.

Theorem polyn_add_opp_r :
  rngl_has_opp = true
  → ∀ a : polyn T, (a + - a)%pol = 0%pol.
Proof.
intros Hop *.
apply eq_polyn_eq.
destruct a as (la, Ha); cbn.
do 2 rewrite fold_lap_norm.
rewrite lap_add_norm_idemp_r.
now apply lap_norm_add_opp_r.
Qed.

Theorem polyn_opt_add_opp_l :
  let _ := polyn_ring_like_op in
  if rngl_has_opp then ∀ a : polyn T, (- a + a)%F = 0%F else not_applicable.
Proof.
intros rop; subst rop.
remember rngl_has_opp as op eqn:Hop; symmetry in Hop.
intros.
destruct op; [ | easy ].
intros a.
unfold rngl_opp; cbn.
unfold polyn_opt_opp_or_sous.
specialize polyn_add_opp_l as add_opp_l.
unfold rngl_has_opp in Hop, add_opp_l.
cbn in Hop, add_opp_l.
unfold polyn_opt_opp_or_sous in Hop, add_opp_l.
destruct rngl_opt_opp_or_sous as [opp| ]; [ | easy ].
destruct opp as [opp| ]; [ | easy ].
now apply add_opp_l.
Qed.

(* *)

Theorem polyn_opt_has_no_sous : ∀ P,
  let _ := polyn_ring_like_op in
  if rngl_has_sous then P else not_applicable.
Proof.
intros.
unfold rngl_has_sous; cbn.
unfold polyn_opt_opp_or_sous.
destruct rngl_opt_opp_or_sous as [opp| ]; [ | easy ].
now destruct opp.
Qed.

Theorem polyn_opt_has_no_inv : ∀ P,
  let _ := polyn_ring_like_op in
  if rngl_has_inv then P else not_applicable.
Proof.
intros.
unfold rngl_has_inv; cbn.
unfold polyn_opt_inv_or_quot.
destruct (bool_dec rngl_mul_is_comm) as [Hic| Hic]; [ | easy ].
destruct (bool_dec rngl_has_opp) as [Hop| Hop]; [ | easy ].
destruct (bool_dec rngl_has_inv); [ | easy ].
now destruct rngl_opt_inv_or_quot.
Qed.

Theorem polyn_opt_has_no_inv_and : ∀ e P,
  let _ := polyn_ring_like_op in
  if (rngl_has_inv && e)%bool then P else not_applicable.
Proof.
intros.
unfold rngl_has_inv; cbn.
unfold polyn_opt_inv_or_quot.
destruct (bool_dec rngl_mul_is_comm); [ | easy ].
destruct (bool_dec rngl_has_opp); [ | easy ].
destruct (bool_dec rngl_has_inv); [ | easy ].
now destruct rngl_opt_inv_or_quot.
Qed.

(* *)

Theorem map_opp_repeat : ∀ (x : T) n,
  map rngl_opp (repeat x n) = repeat (rngl_opp x) n.
Proof.
intros.
induction n; [ easy | cbn ].
f_equal; apply IHn.
Qed.

Theorem lap_convol_mul_l_succ_l : ∀ la lb i len,
  lap_convol_mul (0%F :: la) lb (S i) len =
  lap_convol_mul la lb i len.
Proof.
intros.
revert la lb i.
induction len; intros; [ easy | cbn ].
rewrite rngl_summation_split_first; [ | easy ].
rewrite rngl_summation_shift with (s := 1); [ | flia ].
rewrite Nat.sub_diag, Nat_sub_succ_1.
rewrite (rngl_mul_0_l Hos), rngl_add_0_l.
f_equal.
apply IHlen.
Qed.

Theorem lap_convol_mul_r_succ_l : ∀ la lb i len,
  lap_convol_mul la (0%F :: lb) (S i) len =
  lap_convol_mul la lb i len.
Proof.
intros.
revert la lb i.
induction len; intros; [ easy | cbn ].
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_shift with (s := 1); [ | flia ].
rewrite Nat.sub_diag, Nat_sub_succ_1.
rewrite Nat.sub_diag.
rewrite (rngl_mul_0_r Hos), rngl_add_0_r.
rewrite IHlen; f_equal.
apply rngl_summation_eq_compat.
intros j Hj.
rewrite Nat.add_comm, Nat.add_sub; f_equal.
destruct j; [ now rewrite Nat.sub_0_r | ].
now replace (i - j) with (S (i - S j)) by flia Hj.
Qed.

Theorem lap_repeat_0_app_is_mul_power_l : ∀ n la,
  la ≠ []
  → repeat 0%F n ++ la = ((repeat 0%F n ++ [1%F]) * la)%lap.
Proof.
intros * Haz.
revert la Haz.
induction n; intros. {
  destruct la as [| a]; [ easy | clear Haz; cbn ].
  rewrite rngl_summation_only_one.
  rewrite rngl_mul_1_l; f_equal.
  now rewrite lap_convol_mul_1_l.
}
cbn.
destruct la as [| a]; [ easy | clear Haz ].
rewrite app_length, repeat_length; cbn.
rewrite Nat.sub_0_r, Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos); f_equal.
rewrite lap_convol_mul_l_succ_l.
rewrite IHn; [ | easy ].
destruct n; [ easy | cbn ].
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos).
rewrite Nat.sub_0_r.
rewrite app_length, repeat_length; cbn.
rewrite lap_convol_mul_l_succ_l.
rewrite Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos); f_equal.
apply lap_convol_mul_l_succ_l.
Qed.

Theorem lap_repeat_0_app_is_mul_power_r : ∀ n la,
  la ≠ []
  → repeat 0%F n ++ la = (la * (repeat 0%F n ++ [1%F]))%lap.
Proof.
intros * Haz.
revert la Haz.
induction n; intros. {
  destruct la as [| a]; [ easy | clear Haz; cbn ].
  rewrite Nat.sub_0_r, Nat.add_1_r; cbn.
  rewrite rngl_summation_only_one.
  rewrite rngl_mul_1_r; f_equal.
  now rewrite lap_convol_mul_1_r.
}
cbn.
destruct la as [| a]; [ easy | clear Haz ].
cbn.
rewrite app_length, repeat_length, Nat.sub_0_r; cbn.
rewrite Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_r Hos); f_equal.
rewrite IHn; [ | easy ].
rewrite lap_convol_mul_r_succ_l.
cbn.
destruct n; cbn; [ now rewrite Nat.sub_0_r | ].
now rewrite app_length, repeat_length, Nat.sub_0_r.
Qed.

Theorem eq_lap_add_0 : ∀ la lb, (la + lb = [])%lap → (la = [] ∧ lb = [])%lap.
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros; [ easy | now destruct lb ].
Qed.

Theorem lap_add_app_l : ∀ la lb lc,
  length lc ≤ length la
  → (((la ++ lb) + lc) = (la + lc) ++ lb)%lap.
Proof.
intros * Hca.
revert lb lc Hca.
induction la as [| a]; intros; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Hca; subst lc.
  now rewrite lap_add_0_r.
}
destruct lc as [| c]; [ easy | ].
cbn in Hca |-*; f_equal.
apply Nat.succ_le_mono in Hca.
now apply IHla.
Qed.

Theorem lap_add_app_r : ∀ la lb lc,
  length la ≤ length lb
  → (la + (lb ++ lc) = (la + lb) ++ lc)%lap.
Proof.
intros * Hab.
revert lb lc Hab.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
cbn in Hab; apply Nat.succ_le_mono in Hab.
f_equal.
now apply IHla.
Qed.

Theorem lap_add_app_app :
  ∀ la lb lc ld,
  length la = length lb
  → ((la ++ lc) + (lb ++ ld))%lap = (la + lb)%lap ++ (lc + ld)%lap.
Proof.
intros * Hab.
revert lb lc ld Hab.
induction la as [| a]; intros. {
  now symmetry in Hab; apply length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | ].
cbn in Hab.
apply Nat.succ_inj in Hab.
cbn; f_equal.
now apply IHla.
Qed.

Theorem lap_opp_app_distr : ∀ la lb,
  (- (la ++ lb) = (- la) ++ (- lb))%lap.
Proof.
intros.
unfold lap_opp.
now rewrite map_app.
Qed.

Theorem lap_sub_app_app :
  ∀ la lb lc ld,
  length la = length lb
  → ((la ++ lc) - (lb ++ ld))%lap = (la - lb)%lap ++ (lc - ld)%lap.
Proof.
intros * Hab.
revert lb lc ld Hab.
induction la as [| a]; intros. {
  now symmetry in Hab; apply length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | ].
cbn in Hab.
apply Nat.succ_inj in Hab.
cbn; f_equal.
now apply IHla.
Qed.

Theorem length_strip_0s_eq : ∀ la,
  length (strip_0s la) = length la
  → strip_0s la = la.
Proof.
intros * Ha.
destruct la as [| a]; [ easy | cbn ].
cbn in Ha.
rewrite if_bool_if_dec.
destruct (bool_dec _) as [Haz| Haz]; [ | easy ].
rewrite Haz in Ha.
specialize (strip_0s_length_le la) as H1.
rewrite Ha in H1.
apply Nat.nlt_ge in H1.
now exfalso; apply H1.
Qed.

Theorem rev_lap_opp : ∀ la, (rev (- la) = - rev la)%lap.
Proof.
intros.
unfold lap_opp.
now rewrite map_rev.
Qed.

Theorem lap_add_repeat_0_l : ∀ la len,
  len ≤ length la
  → (repeat 0%F len + la = la)%lap.
Proof.
intros * Hlen.
revert len Hlen.
induction la as [| a]; intros. {
  now apply Nat.le_0_r in Hlen; subst len.
}
cbn.
destruct len; [ easy | cbn ].
cbn in Hlen; apply Nat.succ_le_mono in Hlen.
rewrite rngl_add_0_l; f_equal.
now apply IHla.
Qed.

Theorem lap_add_repeat_0_r : ∀ la len,
  len ≤ length la
  → (la + repeat 0%F len = la)%lap.
Proof.
intros * Hlen.
rewrite lap_add_comm.
now apply lap_add_repeat_0_l.
Qed.

Theorem rev_lap_add : ∀ la lb,
  length la = length lb
  → (rev (la + lb) = rev la + rev lb)%lap.
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
cbn in Hab |-*.
apply Nat.succ_inj in Hab.
rewrite IHla; [ | easy ].
rewrite lap_add_app_app; [ easy | ].
now do 2 rewrite rev_length.
Qed.

Theorem rev_lap_sub : ∀ la lb,
  length la = length lb
  → (rev (la - lb) = rev la - rev lb)%lap.
Proof.
intros * Hab.
unfold lap_sub.
rewrite rev_lap_add; [ | now rewrite lap_opp_length ].
now rewrite rev_lap_opp.
Qed.

Theorem lap_add_norm : ∀ la lb,
  (la + lb)%lap =
    ((la ++ repeat 0%F (length lb - length la)) +
     (lb ++ repeat 0%F (length la - length lb)))%lap.
Proof.
intros.
revert lb.
induction la as [| a]; intros. {
  cbn; rewrite Nat.sub_0_r, app_nil_r.
  now symmetry; apply lap_add_repeat_0_l.
}
cbn.
destruct lb as [| b]. {
  cbn; rewrite app_nil_r, rngl_add_0_r; f_equal.
  now symmetry; apply lap_add_repeat_0_r.
}
cbn; f_equal.
apply IHla.
Qed.

Theorem rev_lap_add_norm : ∀ la lb,
  rev (la + lb)%lap =
    ((repeat 0%F (length lb - length la) ++ rev la) +
     (repeat 0%F (length la - length lb) ++ rev lb))%lap.
Proof.
intros.
rewrite <- (List_rev_repeat _ (length lb - _)).
rewrite <- (List_rev_repeat _ (length la - _)).
do 2 rewrite <- rev_app_distr.
rewrite lap_add_norm.
apply rev_lap_add.
do 2 rewrite app_length, repeat_length.
destruct (le_dec (length lb) (length la)) as [Hab| Hab]. {
  rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
  rewrite Nat.add_0_r, Nat.add_comm; symmetry.
  now apply Nat.sub_add.
} {
  apply Nat.nle_gt, Nat.lt_le_incl in Hab; symmetry.
  rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
  rewrite Nat.add_0_r, Nat.add_comm; symmetry.
  now apply Nat.sub_add.
}
Qed.

Theorem rev_lap_sub_norm :
  rngl_has_opp = true →
  ∀ la lb,
  rev (la - lb)%lap =
    ((repeat 0%F (length lb - length la) ++ rev la) -
     (repeat 0%F (length la - length lb) ++ rev lb))%lap.
Proof.
intros Hop *.
unfold lap_sub.
rewrite rev_lap_add_norm.
rewrite lap_opp_length.
f_equal.
rewrite lap_opp_app_distr.
rewrite rev_lap_opp.
f_equal.
rewrite map_opp_repeat.
now rewrite rngl_opp_0.
Qed.

Theorem lap_sub_add :
  rngl_has_opp = true →
  ∀ la lb,
  length lb ≤ length la
  → (la - lb + lb = la)%lap.
Proof.
intros Hop * Hba.
unfold lap_sub.
rewrite <- lap_add_assoc.
rewrite (lap_add_opp_l Hop).
revert lb Hba.
induction la as [| a]; intros; cbn. {
  now apply Nat.le_0_r, length_zero_iff_nil in Hba; subst lb.
}
destruct lb as [| b]; [ easy | cbn ].
cbn in Hba; apply Nat.succ_le_mono in Hba.
rewrite rngl_add_0_r; f_equal.
now apply IHla.
Qed.

Theorem gen_lap_add : ∀ la lb,
  (la + lb =
   (la ++ repeat 0%F (length lb - length la)) +
   (lb ++ repeat 0%F (length la - length lb)))%lap.
Proof.
intros.
revert lb.
induction la as [| a]; intros; cbn. {
  rewrite Nat.sub_0_r, app_nil_r.
  now symmetry; apply lap_add_repeat_0_l.
}
destruct lb as [| b]; cbn. {
  rewrite rngl_add_0_r, app_nil_r; f_equal.
  now symmetry; apply lap_add_repeat_0_r.
}
f_equal.
apply IHla.
Qed.

Theorem lap_opp_involutive :
  rngl_has_opp = true →
  ∀ la, (- - la = la)%lap.
Proof.
intros Hop *.
induction la as [| a]; [ easy | cbn ].
now rewrite (rngl_opp_involutive Hop); f_equal.
Qed.

Theorem lap_sub_diag :
  rngl_has_opp = true →
  ∀ la, (la - la = repeat 0%F (length la))%lap.
Proof.
intros Hop *.
induction la as [| a]; [ easy | cbn ].
rewrite (fold_rngl_sub Hop).
rewrite rngl_sub_diag; [ now f_equal | easy ].
Qed.

Theorem rlap_quot_rem_step_Some :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  ∀ rla rlb rlr cq,
  hd 0%F rlb ≠ 0%F
  → rlap_quot_rem_step rla rlb = (Some cq, rlr)
  → rev rla =
      (rev rlb * rev (cq :: repeat 0%F (length rla - length rlb)) +
       rev rlr)%lap ∧
    length rla = S (length rlr) ∧
    cq = (hd 0 rla / hd 0 rlb)%F.
Proof.
intros Hco Hop Hiv * Hbz Hrl.
destruct rlb as [| b]; [ easy | cbn in Hbz, Hrl ].
destruct rla as [| a]; [ easy | ].
rewrite if_bool_if_dec in Hrl.
destruct (bool_dec _) as [Hab| Hab]; [ easy | ].
apply Nat.ltb_ge in Hab.
injection Hrl; clear Hrl; intros H1 H2; subst cq rlr.
remember (a / b)%F as cq eqn:Hcq.
move b before a.
cbn; rewrite List_rev_repeat.
rewrite lap_repeat_0_app_is_mul_power_l; [ | easy ].
rewrite lap_mul_assoc; cbn.
rewrite <- lap_repeat_0_app_is_mul_power_r. 2: {
  now intros H; apply app_eq_nil in H.
}
rewrite lap_mul_const_r.
do 2 rewrite map_app; cbn.
rewrite List_map_repeat.
rewrite (rngl_mul_0_l Hos).
rewrite map_rev.
replace (b * cq)%F with (b * (a / b))%F by now rewrite Hcq.
rewrite (rngl_mul_div_r Hco Hiv _ _ Hbz).
rewrite <- List_rev_repeat at 1.
rewrite app_assoc.
rewrite <- rev_app_distr.
remember (map _ _ ++ repeat _ _) as rlc eqn:Hrlc.
rewrite rev_lap_sub_norm; [ | easy ].
rewrite map_length.
remember (repeat _ _ ++ _) as x.
rewrite <- List_rev_repeat.
rewrite <- rev_app_distr.
rewrite <- Hrlc.
subst x.
rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
cbn.
rewrite fold_lap_sub.
assert (Hca : length rlc = length rla). {
  rewrite Hrlc, app_length, map_length, repeat_length.
  now rewrite Nat.add_comm, Nat.sub_add.
}
rewrite <- rev_lap_sub; [ | easy ].
rewrite lap_add_app_l. 2: {
  do 2 rewrite rev_length.
  rewrite lap_sub_length.
  now rewrite Hca, Nat.max_id.
}
rewrite lap_sub_length, map_length.
rewrite Nat.max_l; [ | easy ].
split; [ | easy ].
f_equal.
specialize (strip_0s_length_le (rla - rlc)%lap) as Hrac.
remember (rla - rlc)%lap as rlac eqn:Hrlac.
symmetry in Hrlac.
assert (rla = (rlc + rlac)%lap). {
  rewrite <- Hrlac, lap_add_comm.
  symmetry.
  apply (lap_sub_add Hop).
  now rewrite Hca.
}
subst rla.
rewrite lap_add_length in Hca.
symmetry in Hca.
apply Nat.max_l_iff in Hca.
apply (f_equal length) in Hrlac.
rewrite lap_sub_length in Hrlac.
rewrite lap_add_length in Hrlac.
rewrite Nat.max_l in Hrlac; [| apply Nat.le_max_l ].
rewrite Nat.max_l in Hrlac; [ | easy ].
destruct rlac as [| ac]; intros. {
  apply length_zero_iff_nil in Hrlac; subst rlc; cbn.
  rewrite lap_add_0_l in Hab.
  now apply Nat.le_0_r, length_zero_iff_nil in Hab; subst rlb.
}
now rewrite rev_lap_add.
Qed.

Theorem rlap_quot_rem_length :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  ∀ it (rla rlb rlq rlr : list T),
  hd 0%F rlb ≠ 0%F
  → rlap_quot_rem_loop it rla rlb = (rlq, rlr)
  → S (length rla) ≤ it
  → length rlq = length rla - (length rlb - 1).
Proof.
intros Hco Hop * Hbn Hqr Hit.
destruct rlb as [| b]; [ easy | ].
cbn; rewrite Nat.sub_0_r.
cbn in Hbn.
revert rla rlq rlr Hqr Hit.
induction it; intros; [ easy | ].
apply Nat.succ_le_mono in Hit.
remember (b :: rlb) as l; cbn in Hqr; subst l.
remember (rlap_quot_rem_step rla (b :: rlb)) as qrlr eqn:Hqrlr.
symmetry in Hqrlr.
destruct qrlr as (q, rlr').
destruct q as [cq| ]. 2: {
  injection Hqr; clear Hqr; intros; subst rlq rlr; cbn.
  apply rlap_quot_rem_step_None in Hqrlr.
  destruct Hqrlr as [H1| H1]; [ easy | ].
  destruct H1 as [H1| H1]; [ now destruct H1; subst rla | ].
  rewrite (proj2 (Nat.sub_0_le _ _)); [ easy | ].
  destruct H1 as (H1, _); cbn in H1.
  now apply Nat.lt_succ_r.
}
generalize Hqrlr; intros Hb.
apply rlap_quot_rem_step_length_r_a in Hb.
remember (rlap_quot_rem_loop it _ _) as qr eqn:Hqr'.
symmetry in Hqr'.
destruct qr as (rlq', rlr'').
injection Hqr; clear Hqr; intros; subst rlq rlr; cbn.
generalize Hqr'; intros Hqr.
apply IHit in Hqr; [ | now rewrite Hb ].
rewrite <- Hb, Hqr.
destruct (le_dec (length rlb) (length rlr')) as [Hrr| Hrr]. {
  now symmetry; rewrite Nat.sub_succ_l.
}
apply Nat.nle_gt in Hrr.
rewrite (proj2 (Nat.sub_0_le _ _)); [ | flia Hrr ].
rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
apply Nat.succ_lt_mono in Hrr.
rewrite Hb in Hrr.
cbn in Hqrlr.
destruct rla as [| a]; [ easy | ].
cbn in Hrr.
apply Nat.succ_lt_mono in Hrr.
apply Nat.ltb_lt in Hrr.
now rewrite Hrr in Hqrlr.
Qed.

Theorem rlap_quot_rem_loop_prop :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  ∀ it (rla rlb rlq rlr : list T),
  hd 0%F rlb ≠ 0%F
  → rlap_quot_rem_loop it rla rlb = (rlq, rlr)
  → S (length rla) ≤ it
  → rev rla = (rev rlb * rev rlq + rev rlr)%lap.
Proof.
intros Hco Hop Hiv * Hbn Hqr Hit.
revert rla rlq rlr Hqr Hit.
induction it; intros; [ easy | ].
apply Nat.succ_le_mono in Hit.
cbn in Hqr.
remember (rlap_quot_rem_step rla rlb) as qrlr eqn:Hqrlr.
symmetry in Hqrlr.
destruct qrlr as (q, rlr').
destruct q as [cq| ]. 2: {
  injection Hqr; clear Hqr; intros; subst rlq rlr; cbn.
  rewrite lap_mul_0_r, lap_add_0_l.
  f_equal.
  destruct rlb as [| b]; [ easy | ].
  destruct rla as [| a]; [ now destruct rlb; injection Hqrlr; intros | ].
  cbn in Hqrlr.
  destruct (length rla <? length rlb); [ | easy ].
  now injection Hqrlr.
}
generalize Hqrlr; intros Hqrlr'.
apply (rlap_quot_rem_step_Some Hco Hop Hiv) in Hqrlr'; [ | easy ].
destruct Hqrlr' as (Hqrlr' & Hra & Hcq).
remember (rlap_quot_rem_loop it _ _) as qr eqn:Hqr'.
symmetry in Hqr'.
destruct qr as (rlq', rlr'').
injection Hqr; clear Hqr; intros; subst rlq rlr.
rename rlq' into rlq; rename rlr' into rlr.
rename Hqr' into Hqr.
move rla after rlb.
move rlq before rlb.
move rlr before rlq.
generalize Hqr; intros Hqrb.
apply (rlap_quot_rem_length Hco Hop _ _ Hbn) in Hqrb; [ | flia Hra Hit ].
apply IHit in Hqr. 2: {
  etransitivity; [ | apply Hit ].
  apply lt_le_S.
  destruct rlb as [| b]; [ easy | ].
  cbn in Hqrlr.
  destruct rla as [| a]; [ easy | ].
  rewrite if_bool_if_dec in Hqrlr.
  destruct (bool_dec _) as [Hab| Hab]; [ easy | ].
  apply Nat.ltb_ge in Hab.
  injection Hqrlr; clear Hqrlr; intros; subst cq rlr.
  rewrite lap_sub_length.
  now cbn; rewrite map_length, Nat.max_l.
}
rewrite Hqrlr', Hqr.
rewrite lap_add_assoc.
f_equal; cbn.
rewrite List_rev_repeat.
rewrite <- lap_mul_add_distr_l.
f_equal.
rewrite lap_add_comm.
rewrite lap_add_app_r; cycle 1. {
  rewrite rev_length, repeat_length.
  flia Hra Hqrb.
}
f_equal.
apply lap_add_repeat_0_r.
rewrite rev_length.
rewrite Hra, Hqrb.
destruct rlb as [| b]; [ easy | ].
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem rlap_quot_rem_prop :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  ∀ (rla rlb rlq rlr : list T),
  hd 0%F rlb ≠ 0%F
  → rlap_quot_rem rla rlb = (rlq, rlr)
  → rev rla = (rev rlb * rev rlq + rev rlr)%lap.
Proof.
intros Hco Hop Hiv * Hbn Hqr.
now apply rlap_quot_rem_loop_prop in Hqr.
Qed.

Theorem lap_add_rev_strip : ∀ la lb,
  length lb ≤ length la
  → (la + rev (strip_0s lb) = la + rev lb)%lap.
Proof.
intros * Hba.
revert lb Hba.
induction la as [| a]; intros. {
  now apply Nat.le_0_r, length_zero_iff_nil in Hba; subst lb.
}
cbn.
remember (rev lb) as lc eqn:Hlc; symmetry in Hlc.
apply List_rev_symm in Hlc; subst lb.
destruct lc as [| c]; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (rev lc)) as lb eqn:Hlb; symmetry in Hlb.
rewrite rev_length in Hba; cbn in Hba.
apply Nat.succ_le_mono in Hba.
destruct lb as [| b]. {
  cbn.
  specialize (proj1 (eq_strip_0s_rev_nil _) Hlb) as H1.
  clear Hlb IHla.
  rewrite if_bool_if_dec, lap_add_comm.
  destruct (bool_dec _) as [Hcz| Hcz]. {
    apply (rngl_eqb_eq Heb) in Hcz; subst c; cbn.
    rewrite rngl_add_0_r; f_equal.
    symmetry.
    clear a.
    revert la Hba.
    induction lc as [| c]; intros; [ apply lap_add_0_l | cbn ].
    destruct la as [| a]; [ easy | ].
    cbn in Hba.
    apply Nat.succ_le_mono in Hba.
    specialize (H1 0) as H2; cbn in H2.
    subst c; rewrite rngl_add_0_l; f_equal.
    apply IHlc; [ | easy ].
    intros i.
    now specialize (H1 (S i)).
  } {
    cbn; f_equal; clear c Hcz.
    rewrite lap_add_0_r.
    symmetry.
    clear a.
    revert la Hba.
    induction lc as [| c]; intros; [ apply lap_add_0_l | cbn ].
    destruct la as [| a]; [ easy | ].
    cbn in Hba.
    apply Nat.succ_le_mono in Hba.
    specialize (H1 0) as H2; cbn in H2.
    subst c; rewrite rngl_add_0_l; f_equal.
    apply IHlc; [ | easy ].
    intros i.
    now specialize (H1 (S i)).
  }
}
rewrite <- Hlb.
rewrite rev_app_distr; cbn; f_equal.
rewrite IHla; [ | now rewrite rev_length ].
now rewrite rev_involutive.
Qed.

Theorem is_empty_list_empty : ∀ A (la : list A),
  is_empty_list la = true → la = [].
Proof.
intros * Ha.
unfold is_empty_list in Ha.
now destruct la.
Qed.

Theorem polyn_length_strip_length : ∀ la,
  has_polyn_prop la = true
  → length (strip_0s (rev la)) = length la.
Proof.
intros * Ha.
unfold has_polyn_prop in Ha.
apply Bool.orb_true_iff in Ha.
destruct Ha as [Ha| Ha]. {
  apply is_empty_list_empty in Ha.
  now subst la.
}
apply (rngl_neqb_neq Heb) in Ha.
destruct la as [| a] using rev_ind; [ easy | ].
rewrite last_last in Ha.
rewrite rev_app_distr; cbn.
apply (rngl_eqb_neq Heb) in Ha.
rewrite Ha, app_length, Nat.add_comm; cbn.
now rewrite rev_length.
Qed.

Theorem lap_quot_rem_prop :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  ∀ la lb lq lr : list T,
  has_polyn_prop la = true
  → last lb 0%F ≠ 0%F
  → has_polyn_prop lr = true
  → lap_quot_rem la lb = (lq, lr)
  → la = (lb * lq + lr)%lap ∧
    length lr < length lb ∧
    has_polyn_prop lq = true.
Proof.
intros Hco Hop Hiv * Ha Hb Hr Hab.
assert (Hrb : length lr < length lb). {
  eapply (lap_rem_length_lt Hop Hco); [ | | apply Hab ]. {
    now intros H; subst lb.
  } {
    unfold has_polyn_prop.
    apply (rngl_eqb_neq Heb) in Hb.
    now rewrite Hb, Bool.orb_true_r.
  }
}
rewrite and_comm, and_assoc.
split; [ easy | ].
rewrite and_comm.
assert (Hbz : hd 0%F (rev lb) ≠ 0%F). {
  remember (rev lb) as lc eqn:Hlc; symmetry in Hlc.
  apply List_rev_symm in Hlc; subst lb.
  destruct lc as [| c]; [ easy | ].
  cbn in Hb.
  now rewrite last_last in Hb.
}
apply Bool.orb_true_iff in Hr.
destruct Hr as [Hr| Hr]. {
  apply is_empty_list_empty in Hr.
  subst lr.
  rewrite lap_add_0_r.
  unfold lap_quot_rem in Hab.
  remember (rlap_quot_rem _ _) as qr eqn:Hqr; symmetry in Hqr.
  destruct qr as (rlq, rlr).
  injection Hab; clear Hab; intros Hr H; subst lq.
  apply List_eq_rev_nil in Hr.
  generalize Hqr; intros Hqr'.
  apply (rlap_quot_prop Hiv) in Hqr'; cycle 1. {
    unfold has_polyn_prop in Ha.
    apply Bool.orb_true_iff in Ha.
    destruct Ha as [Ha| Ha]. {
      apply is_empty_list_empty in Ha; subst la.
      now left.
    }
    right.
    apply (rngl_neqb_neq Heb) in Ha.
    now rewrite <- List_last_rev, rev_involutive.
  } {
    right.
    now rewrite <- List_last_rev, rev_involutive.
  }
  specialize (rlap_quot_rem_loop_prop Hco Hop Hiv) as H1.
  specialize (H1 (S (length (rev la))) (rev la) (rev lb) rlq rlr).
  specialize (H1 Hbz Hqr (Nat.le_refl _)).
  do 2 rewrite rev_involutive in H1.
  destruct Hqr' as [Hqr'| Hqr']. {
    subst rlq.
    rewrite lap_mul_0_r.
    rewrite lap_mul_0_r, lap_add_0_l in H1.
    symmetry in H1; apply List_rev_symm in H1; subst rlr.
    apply Bool.orb_true_iff in Ha.
    destruct Ha as [Ha| Ha]. {
      now apply is_empty_list_empty in Ha.
    }
    destruct la as [| a] using rev_ind; [ easy | ].
    rewrite last_last in Ha.
    rewrite rev_app_distr in Hr; cbn in Hr.
    apply Bool.negb_true_iff in Ha.
    now rewrite Ha in Hr.
  }
  rewrite <- lap_add_rev_strip in H1. {
    rewrite Hr, lap_add_0_r in H1.
    split; [ easy | ].
    apply Bool.orb_true_iff; right.
    rewrite List_last_rev.
    now apply (rngl_neqb_neq Heb).
  }
  rewrite lap_mul_length.
  destruct lb as [| b]; [ easy | ].
  remember (rev rlq) as lq eqn:Hlq; symmetry in Hlq.
  destruct lq as [| q]. {
    now apply List_eq_rev_nil in Hlq; subst rlq.
  }
  cbn; rewrite Nat.sub_0_r.
  rewrite app_length; cbn.
  apply rlap_rem_prop in Hqr. 2: {
    intros H.
    now apply List_eq_rev_nil in H.
  }
  rewrite rev_length in Hqr; cbn in Hqr; flia Hqr.
}
unfold lap_quot_rem in Hab.
remember (rlap_quot_rem _ _) as qr eqn:Hqr; symmetry in Hqr.
destruct qr as (rlq, rlr).
injection Hab; clear Hab; intros; subst lq lr.
specialize (rlap_quot_rem_loop_prop Hco Hop Hiv) as H1.
specialize (H1 (S (length (rev la))) (rev la) (rev lb) rlq rlr).
specialize (H1 Hbz Hqr (Nat.le_refl _)).
do 2 rewrite rev_involutive in H1.
rewrite rev_length in Hrb.
remember (rev rlq) as lq eqn:Hlq; symmetry in Hlq.
destruct lq as [| q]. {
  split; [ | easy ].
  rewrite lap_mul_0_r, lap_add_0_l in H1.
  rewrite lap_mul_0_r, lap_add_0_l.
  rewrite H1; f_equal; symmetry.
  destruct rlr as [| r]; [ easy | ].
  cbn in Hr |-*.
  rewrite if_bool_if_dec in Hr |-*.
  destruct (bool_dec _) as [Hrz| Hrz]; [ | easy ].
  apply (rngl_eqb_eq Heb) in Hrz.
  subst r.
  cbn in H1.
  apply Bool.orb_true_iff in Ha.
  destruct Ha as [Ha| Ha]. {
    apply is_empty_list_empty in Ha; subst la.
    now symmetry in H1; apply app_eq_nil in H1.
  }
  rewrite H1 in Ha.
  rewrite last_last in Ha.
  now apply rngl_neqb_neq in Ha.
}
rewrite lap_add_rev_strip. {
  split; [ easy | ].
  apply Bool.orb_true_iff; right.
  rewrite <- Hlq, List_last_rev.
  apply (rngl_neqb_neq Heb).
  apply (rlap_quot_prop Hiv) in Hqr; [ | | now right ]. 2: {
    apply Bool.orb_true_iff in Ha.
    destruct Ha as [Ha| Ha]. {
      apply is_empty_list_empty in Ha; subst la.
      now left.
    }
    right.
    rewrite <- List_last_rev, rev_involutive.
    now apply (rngl_neqb_neq Heb) in Ha.
  }
  destruct Hqr as [Hqr| Hqr]; [ now subst rlq | easy ].
}
rewrite lap_mul_length.
destruct lb as [| b]; [ easy | ].
cbn; rewrite Nat.sub_0_r.
rewrite app_length; cbn.
apply rlap_rem_prop in Hqr. 2: {
  intros H.
  now apply List_eq_rev_nil in H.
}
rewrite rev_length in Hqr; cbn in Hqr; flia Hqr.
Qed.

Arguments polyn_quot_rem (pa pb)%pol.

Theorem polyn_quot_rem_prop :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  ∀ pa pb pq pr : polyn T,
  pb ≠ 0%pol
  → polyn_quot_rem pa pb = (pq, pr)
  → pa = (pb * pq + pr)%pol ∧ length (lap pr) < length (lap pb).
Proof.
intros * Hic Hop Hiv * Hbz Hab.
destruct pa as (la, Hpa).
destruct pb as (lb, Hpb).
destruct pq as (lq, Hpq).
destruct pr as (lr, Hpr); cbn.
move lb before la; move lq before lb; move lr before lq.
specialize (lap_quot_rem_prop Hic Hop Hiv la lb) as H1.
specialize (H1 lq lr Hpa).
assert (H : (last lb 0 ≠ 0)%F). {
  apply (rngl_neqb_neq Heb).
  destruct lb; [ | easy ].
  exfalso; apply Hbz.
  now apply eq_polyn_eq.
}
specialize (H1 H Hpr); clear H.
assert (H : lap_quot_rem la lb = (lq, lr)). {
  unfold polyn_quot_rem in Hab.
  unfold polyn_quot, polyn_rem in Hab; cbn in Hab.
  destruct (bool_dec rngl_has_inv) as [Hiv2| Hiv2]. {
    injection Hab; clear Hab; intros; subst lr lq.
    unfold lap_quot_rem.
    unfold lap_quot, lap_rem.
    now destruct (rlap_quot_rem _ _).
  }
  now rewrite Hiv in Hiv2.
}
specialize (H1 H); clear H.
destruct H1 as (H1, H2).
split; [ | easy ].
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm.
rewrite lap_add_norm_idemp_l.
rewrite <- H1; symmetry.
now apply last_lap_neq_0_lap_norm.
Qed.

Notation "a / b" := (polyn_quot a b) : polyn_scope.
Notation "a 'mod' b" := (polyn_rem a b) : polyn_scope.

Declare Scope polyn_scope.
Delimit Scope polyn_scope with pol.

Notation "a + b" := (polyn_add a b) : polyn_scope.
Notation "a * b" := (polyn_mul a b) : polyn_scope.
Notation "a / b" := (polyn_quot a b) : polyn_scope.
Notation "a 'mod' b" := (polyn_rem a b) : polyn_scope.

Theorem polyn_add_sub_eq_l :
  rngl_has_opp = true →
  ∀ a b c : polyn T,
  (a + b)%pol = c → (c - a)%pol = b.
Proof.
intros Hop * Habc.
subst c.
rewrite polyn_add_comm.
unfold polyn_sub.
unfold lap_sub.
rewrite <- polyn_add_assoc.
rewrite (polyn_add_opp_r Hop).
apply polyn_add_0_r.
Qed.

Theorem lap_add_sub :
  rngl_has_opp = true →
  ∀ la lb, (la + lb - lb)%lap = la ++ repeat 0%F (length lb - length la).
Proof.
intros Hop *.
unfold lap_sub.
rewrite <- lap_add_assoc.
rewrite (lap_add_opp_r Hop).
destruct (le_dec (length lb) (length la)) as [Hlba| Hlba]. {
  rewrite lap_add_repeat_0_r; [ | easy ].
  rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
  symmetry; apply app_nil_r.
}
apply Nat.nle_gt in Hlba.
replace (length lb) with (length la + (length lb - length la)) at 1
  by flia Hlba.
rewrite repeat_app.
rewrite lap_add_app_r; [ | now rewrite repeat_length ].
f_equal.
now apply lap_add_repeat_0_r.
Qed.

Theorem last_lap_convol_mul_last : ∀ la lb a b i len d,
  len ≠ 0
  → length la + length lb + 1 = i + len
  → last (lap_convol_mul (la ++ [a]) (lb ++ [b]) i len) d = (a * b)%F.
Proof.
intros * Hlen Hlab.
revert la lb i Hlab.
induction len; intros; [ easy | clear Hlen ].
cbn.
destruct len. {
  cbn.
  rewrite rngl_summation_split3 with (j := length la); [ | flia Hlab ].
  rewrite app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag; cbn.
  replace (i - length la) with (length lb) by flia Hlab.
  rewrite app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag; cbn.
  rewrite all_0_rngl_summation_0. 2: {
    intros j Hj.
    rewrite (nth_overflow (lb ++ [b])). 2: {
      rewrite app_length; cbn; flia Hlab Hj.
    }
    apply (rngl_mul_0_r Hos).
  }
  rewrite rngl_add_0_l.
  rewrite all_0_rngl_summation_0. 2: {
    intros j Hj.
    rewrite (nth_overflow (la ++ [a])). 2: {
      now rewrite app_length.
    }
    apply (rngl_mul_0_l Hos).
  }
  apply rngl_add_0_r.
}
rewrite IHlen; [ easy | easy | flia Hlab ].
Qed.

Theorem last_lap_mul : ∀ la lb,
  last (la * lb)%lap 0%F = (last la 0%F * last lb 0%F)%F.
Proof.
intros.
unfold lap_mul.
destruct la as [| a] using rev_ind. {
  now symmetry; apply rngl_mul_0_l.
}
clear IHla.
destruct lb as [| b] using rev_ind. {
  cbn.
  rewrite rngl_mul_0_r; [ | easy ].
  now destruct (la ++ [a]).
}
clear IHlb.
move b before a.
remember (la ++ [a]) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]; [ now apply app_eq_nil in Hlc | ].
remember (lb ++ [b]) as ld eqn:Hld.
symmetry in Hld.
destruct ld as [| d]; [ now apply app_eq_nil in Hld | ].
rewrite <- Hlc, <- Hld.
clear c d lc ld Hlc Hld.
do 2 rewrite last_last.
do 2 rewrite app_length.
cbn.
apply last_lap_convol_mul_last; flia.
Qed.

Theorem lap_add_move_l :
  rngl_has_opp = true →
  ∀ la lb lc : list T,
  (la + lb)%lap = lc
  → lb ++ repeat 0%F (length la - length lb) = (lc - la)%lap.
Proof.
intros Hop * Hab.
subst lc.
symmetry; rewrite lap_add_comm.
now rewrite (lap_add_sub Hop).
Qed.

Theorem lap_add_sub_eq_l :
  rngl_has_opp = true →
  ∀ la lb lc,
  (la + lb)%lap = lc
  → (lc - la)%lap = lb ++ repeat 0%F (length la - length lb).
Proof.
intros Hop * Hlab; subst lc.
rewrite lap_add_comm.
apply (lap_add_sub Hop).
Qed.

Theorem lap_add_sub_eq_r :
  rngl_has_opp = true →
  ∀ la lb lc,
  (la + lb)%lap = lc
  → (lc - lb)%lap = la ++ repeat 0%F (length lb - length la).
Proof.
intros Hop * Habc.
subst lc.
apply (lap_add_sub Hop).
Qed.

Theorem lap_add_sub_distr : ∀ la lb lc,
  (la + (lb - lc))%lap = (la + lb - lc)%lap.
Proof.
intros.
unfold lap_sub.
apply lap_add_assoc.
Qed.

Theorem lap_eucl_div_quot_uniq : ∀ la lb lq lr lq' lr',
  length lr < length lb
  → length lr' < length lb
  → la = (lb * lq + lr)%lap
  → la = (lb * lq' + lr')%lap
  → length lq' = length lq.
Proof.
intros * Hrb Hr'b Hr Hr'.
apply (f_equal length) in Hr, Hr'.
rewrite lap_add_length in Hr, Hr'.
rewrite lap_mul_length in Hr, Hr'.
destruct lb as [| b]; [ easy | ].
destruct lq' as [| q']. {
  rewrite Nat.max_0_l in Hr'.
  destruct lq as [| q]; [ easy | ].
  cbn in Hr.
  rewrite app_length in Hr; cbn in Hr.
  rewrite Nat.sub_0_r in Hr.
  cbn in Hrb.
  rewrite Nat.max_l in Hr; [ | flia Hrb ].
  cbn in Hr'b.
  flia Hr'b Hr Hr'.
}
cbn in Hr'.
rewrite app_length in Hr'; cbn in Hr'.
rewrite Nat.sub_0_r in Hr'.
cbn in Hr'b.
rewrite Nat.max_l in Hr'; [ | flia Hr'b ].
destruct lq as [| q]. {
  rewrite Nat.max_0_l in Hr.
  cbn in Hrb.
  flia Hrb Hr Hr'.
}
cbn in Hr.
rewrite app_length in Hr; cbn in Hr.
rewrite Nat.sub_0_r in Hr.
cbn in Hrb.
rewrite Nat.max_l in Hr; [ cbn | flia Hrb ].
flia Hr Hr'.
Qed.

Theorem lap_add_cancel_l :
  rngl_has_opp = true →
  ∀ la lb lc,
  (la + lb = la + lc)%lap
  → (lb ++ repeat 0%F (length lc - length lb)  =
     lc ++ repeat 0%F (length lb - length lc))%lap.
Proof.
intros Hop * Habc.
revert lb lc Habc.
induction la as [| a]; intros; cbn. {
  do 2 rewrite lap_add_0_l in Habc.
  now subst lc.
}
cbn in Habc.
destruct lb as [| b]. {
  rewrite app_nil_r.
  destruct lc as [| c]; [ easy | cbn ].
  injection Habc; clear Habc; intros Hla Ha.
  symmetry in Hla, Ha.
  apply (rngl_add_sub_eq_l Hos) in Ha.
  rewrite (rngl_sub_diag Hos) in Ha; subst c.
  f_equal.
  apply (lap_add_sub_eq_l Hop) in Hla.
  rewrite (lap_sub_diag Hop) in Hla.
  symmetry in Hla.
  specialize (proj1 (List_eq_iff _ _) Hla) as H1.
  destruct H1 as (H, Hnth).
  rewrite app_length, repeat_length in H.
  rewrite repeat_length in H.
  rewrite Nat.add_comm in H.
  assert (Hlen : length lc ≤ length la) by flia H; clear H.
  apply List_eq_iff.
  rewrite repeat_length.
  split; [ easy | ].
  intros d i.
  rewrite List_nth_repeat; symmetry.
  destruct (lt_dec i (length lc)) as [Hic| Hic]. 2: {
    apply Nat.nlt_ge in Hic.
    now apply nth_overflow.
  }
  specialize (Hnth d i) as H1.
  rewrite app_nth1 in H1; [ | easy ].
  rewrite List_nth_repeat in H1.
  destruct (lt_dec i (length la)) as [Hia| Hia]; [ easy | ].
  exfalso; apply Hia.
  now apply (lt_le_trans _ (length lc)).
}
destruct lc as [| c]. {
  cbn; rewrite app_nil_r.
  injection Habc; clear Habc; intros Hla Ha.
  apply (rngl_add_sub_eq_l Hos) in Ha.
  rewrite (rngl_sub_diag Hos) in Ha; subst b.
  f_equal.
  apply (lap_add_sub_eq_l Hop) in Hla.
  rewrite (lap_sub_diag Hop) in Hla.
  symmetry in Hla; symmetry.
  (* TODO: make an assert to group together with the same
     case with lc above *)
  specialize (proj1 (List_eq_iff _ _) Hla) as H1.
  destruct H1 as (H, Hnth).
  rewrite app_length, repeat_length in H.
  rewrite repeat_length in H.
  rewrite Nat.add_comm in H.
  assert (Hlen : length lb ≤ length la) by flia H; clear H.
  apply List_eq_iff.
  rewrite repeat_length.
  split; [ easy | ].
  intros d i.
  rewrite List_nth_repeat; symmetry.
  destruct (lt_dec i (length lb)) as [Hib| Hib]. 2: {
    apply Nat.nlt_ge in Hib.
    now apply nth_overflow.
  }
  specialize (Hnth d i) as H1.
  rewrite app_nth1 in H1; [ | easy ].
  rewrite List_nth_repeat in H1.
  destruct (lt_dec i (length la)) as [Hia| Hia]; [ easy | ].
  exfalso; apply Hia.
  now apply (lt_le_trans _ (length lb)).
}
injection Habc; clear Habc; intros Hla Ha.
apply (rngl_add_sub_eq_l Hos) in Ha.
rewrite rngl_add_comm in Ha.
rewrite (rngl_add_sub Hos) in Ha; subst c.
cbn; f_equal.
now apply IHla.
Qed.

Theorem lap_opp_sub_distr :
  rngl_has_opp = true →
  ∀ la lb, (- (la - lb) = lb - la)%lap.
Proof.
intros Hop *.
revert lb.
induction la as [| a]; intros; cbn. {
  now rewrite (lap_opp_involutive Hop), lap_sub_0_r.
}
destruct lb as [| b]; [ easy | cbn ].
rewrite fold_lap_opp.
do 2 rewrite fold_lap_sub.
rewrite IHla; f_equal.
do 2 rewrite (fold_rngl_sub Hop).
apply (rngl_opp_sub_distr Hop).
Qed.

Theorem lap_sub_move_0_r_le :
  rngl_has_opp = true →
  ∀ la lb,
  length la ≤ length lb
  → (la - lb)%lap = repeat 0%F (max (length la) (length lb)) ↔
    la ++ repeat 0%F (length lb - length la) =
    lb ++ repeat 0%F (length la - length lb).
Proof.
intros Hop * Hlab.
rewrite Nat.max_r; [ | easy ].
rewrite (proj2 (Nat.sub_0_le _ _) Hlab).
rewrite app_nil_r.
split; intros Hab. {
  revert la Hlab Hab.
  induction lb as [| b]; intros. {
    now rewrite lap_sub_0_r in Hab; cbn in Hab; subst la.
  }
  destruct la as [| a]; cbn in Hab |-*. {
    injection Hab; clear Hab; intros Hlb Hb.
    apply (f_equal rngl_opp) in Hb.
    rewrite (rngl_opp_involutive Hop) in Hb.
    rewrite (rngl_opp_0 Hop) in Hb; subst b; f_equal.
    rewrite fold_lap_opp in Hlb.
    apply (f_equal lap_opp) in Hlb.
    rewrite (lap_opp_involutive Hop) in Hlb.
    unfold lap_opp in Hlb.
    rewrite map_opp_repeat in Hlb.
    now rewrite (rngl_opp_0 Hop) in Hlb.
  }
  rewrite (fold_rngl_sub Hop) in Hab.
  injection Hab; clear Hab; intros Hab Ha.
  apply -> (rngl_sub_move_0_r Hop) in Ha; subst b; f_equal.
  cbn in Hlab; apply Nat.succ_le_mono in Hlab.
  now apply IHlb.
}
rewrite <- (app_nil_r la).
rewrite <- Hab.
rewrite lap_sub_app_app; [ | easy ].
rewrite (lap_sub_diag Hop); cbn.
rewrite app_length, repeat_length.
rewrite map_opp_repeat.
rewrite (rngl_opp_0 Hop).
now rewrite <- repeat_app.
Qed.

Theorem lap_sub_move_0_r :
  rngl_has_opp = true →
  ∀ la lb,
  (la - lb)%lap = repeat 0%F (max (length la) (length lb)) ↔
  la ++ repeat 0%F (length lb - length la) =
  lb ++ repeat 0%F (length la - length lb).
Proof.
intros Hop *.
destruct (le_dec (length la) (length lb)) as [Hlab| Hlab]. {
  now apply lap_sub_move_0_r_le.
}
apply Nat.nle_gt, Nat.lt_le_incl in Hlab.
apply (lap_sub_move_0_r_le Hop) in Hlab.
split; intros H. {
  symmetry.
  apply Hlab.
  rewrite Nat.max_comm.
  rewrite <- (rngl_opp_0 Hop) at 1.
  rewrite <- map_opp_repeat.
  rewrite fold_lap_opp.
  rewrite <- H.
  symmetry; apply (lap_opp_sub_distr Hop).
} {
  symmetry in H.
  specialize (proj2 Hlab H) as H1.
  apply (f_equal lap_opp) in H1.
  rewrite (lap_opp_sub_distr Hop) in H1.
  rewrite H1.
  rewrite map_opp_repeat, (rngl_opp_0 Hop).
  now rewrite Nat.max_comm.
}
Qed.

Theorem lap_mul_has_polyn_prop :
  rngl_has_inv = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → has_polyn_prop (la * lb)%lap = true.
Proof.
intros Hiv * Ha Hb.
unfold has_polyn_prop in Ha, Hb |-*.
apply Bool.orb_true_iff in Ha, Hb.
apply Bool.orb_true_iff.
destruct Ha as [Ha| Ha]. {
  apply is_empty_list_empty in Ha; subst la.
  rewrite lap_mul_0_l.
  now left.
}
destruct Hb as [Hb| Hb]. {
  apply is_empty_list_empty in Hb; subst lb.
  rewrite lap_mul_0_r.
  now left.
}
right.
apply (rngl_neqb_neq Heb) in Ha, Hb.
apply (rngl_neqb_neq Heb).
rewrite last_lap_mul.
intros Hab.
apply (rngl_integral Hos) in Hab; [ now destruct Hab | ].
apply Bool.orb_true_iff; right.
rewrite Heb, Bool.andb_true_r.
apply rngl_has_inv_or_quot_iff.
now rewrite Hiv; left.
Qed.

Theorem lap_norm_mul :
  rngl_has_inv = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → lap_norm (la * lb) = (la * lb)%lap.
Proof.
intros Hiv * Ha Hb.
apply last_lap_neq_0_lap_norm.
now apply lap_mul_has_polyn_prop.
Qed.

Theorem last_lap_norm : ∀ la,
  last (lap_norm la) 0%F = 0%F
  → lap_norm la = [].
Proof.
intros * Ha.
induction la as [| a] using rev_ind; [ easy | cbn ].
destruct (rngl_eq_dec Heb a 0%F) as [Haz| Haz]. {
  subst a.
  rewrite <- lap_norm_app_0_r in Ha. 2: {
    intros i.
    destruct i; [ easy | cbn ].
    apply Tauto_match_nat_same.
  }
  rewrite <- lap_norm_app_0_r. 2: {
    intros i.
    destruct i; [ easy | cbn ].
    apply Tauto_match_nat_same.
  }
  now apply IHla.
}
rewrite last_lap_neq_0_lap_norm in Ha; [ now rewrite last_last in Ha | ].
apply Bool.orb_true_iff; right.
rewrite last_last.
now apply (rngl_neqb_neq Heb).
Qed.

Theorem lap_mul_div :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → lb ≠ []
  → (la * lb / lb)%lap = la.
Proof.
intros Hco Hop Hiv * pa pb Hbz.
remember (lap_quot_rem (la * lb) lb) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (lq, lr).
specialize (lap_quot_rem_prop Hco Hop Hiv) as H1.
specialize (H1 (la * lb)%lap lb lq lr).
specialize (H1 (lap_mul_has_polyn_prop Hiv la lb pa pb)).
assert (H : last lb 0%F ≠ 0%F). {
  apply (rngl_neqb_neq Heb).
  apply Bool.orb_true_iff in pb.
  destruct pb as [pb| ]; [ | easy ].
  now apply is_empty_list_empty in pb.
}
specialize (H1 H); clear H.
assert (pr : has_polyn_prop lr = true). {
  specialize (lap_rem_is_norm (la * lb)%lap lb) as H2.
  specialize (H2 (lap_mul_has_polyn_prop Hiv la lb pa pb) pb).
  assert (H : lr = ((la * lb) mod lb)%lap). {
    unfold lap_rem.
    unfold lap_quot_rem in Hqr.
    destruct (rlap_quot_rem _ _).
    now injection Hqr.
  }
  now rewrite <- H in H2.
}
move lq before lb; move lr before lq.
move pr before pb.
specialize (H1 pr Hqr).
destruct H1 as (Hab & Hrb & pq).
move pq before pb.
generalize Hab; intros Hab1.
symmetry in Hab1.
apply (lap_add_move_l Hop) in Hab1.
symmetry in Hab1.
rewrite (lap_mul_comm Hco) in Hab1.
rewrite <- (lap_mul_sub_distr_l Hop) in Hab1.
apply (f_equal lap_norm) in Hab1.
rewrite <- lap_norm_app_0_r in Hab1 by apply nth_repeat.
rewrite (last_lap_neq_0_lap_norm lr pr) in Hab1.
rewrite <- lap_mul_norm_idemp_r in Hab1.
rewrite (lap_norm_mul Hiv) in Hab1; [ | easy | apply polyn_norm_prop ].
generalize Hab1; intros Hab2.
apply (f_equal length) in Hab2.
rewrite lap_mul_length in Hab2.
destruct lb as [| b]; [ easy | clear Hbz ].
remember (lap_norm (la - lq)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. 2: {
  rewrite app_length in Hab2; cbn in Hab2.
  cbn in Hrb; flia Hrb Hab2.
}
apply eq_sym, length_zero_iff_nil in Hab2.
clear Hab Hab1 Hrb pr; subst lr.
unfold lap_quot.
unfold lap_quot_rem in Hqr.
remember (rlap_quot_rem _ _) as qr eqn:Hqr'.
symmetry in Hqr'.
destruct qr as (rlq, rlr).
injection Hqr; clear Hqr; intros Hr Hq; rewrite Hq.
specialize (proj2 (all_0_lap_norm_nil _) Hlc) as H1.
rewrite <- (last_lap_neq_0_lap_norm la pa).
rewrite <- (last_lap_neq_0_lap_norm lq pq).
apply list_nth_lap_eq.
intros i.
specialize (H1 i).
rewrite (list_nth_lap_sub Hop) in H1.
now apply -> (rngl_sub_move_0_r Hop) in H1.
Qed.

Theorem polyn_mul_div :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  ∀ a b,
  b ≠ 0%pol
  → (a * b / b)%pol = a.
Proof.
intros Hco Hop Hiv * Hbz.
destruct a as (la, pa).
destruct b as (lb, pb).
move lb before la.
unfold polyn_mul.
assert (H : lb ≠ []). {
  intros H; apply Hbz.
  now apply eq_polyn_eq.
}
clear Hbz; rename H into Hbz.
apply eq_polyn_eq; cbn.
unfold polyn_norm; cbn.
unfold polyn_quot; cbn.
destruct (bool_dec _) as [Hiv2| Hiv2]. {
  cbn; rewrite (lap_norm_mul Hiv _ _ pa pb).
  now apply lap_mul_div.
}
now rewrite Hiv in Hiv2.
Qed.

Theorem polyn_opt_mul_div :
  let _ := polyn_ring_like_op in
  if rngl_has_quot then ∀ a b, b ≠ 0%F → (a * b / b)%F = a
  else not_applicable.
Proof.
intros rop; subst rop.
unfold rngl_has_quot; cbn.
unfold polyn_opt_inv_or_quot.
destruct (bool_dec rngl_mul_is_comm) as [Hco| ]; [ | easy ].
destruct (bool_dec rngl_has_opp) as [Hop| ]; [ | easy ].
destruct (bool_dec rngl_has_inv) as [Hiv| ]; [ | easy ].
remember rngl_opt_inv_or_quot as iq eqn:Hiq; symmetry in Hiq.
destruct iq as [inv| ]; [ | easy ].
intros a b Hbz.
unfold rngl_div, rngl_has_inv; cbn.
unfold polyn_opt_inv_or_quot.
unfold rngl_has_quot, polyn_opt_inv_or_quot; cbn.
unfold rngl_quot; cbn.
unfold polyn_opt_inv_or_quot.
rewrite Hco, Hop, Hiv, Hiq.
destruct (bool_dec true); [ | easy ].
now apply polyn_mul_div.
Qed.

Theorem polyn_opt_mul_quot_r :
  let _ := polyn_ring_like_op in
  if (rngl_has_quot && negb rngl_mul_is_comm)%bool then
    ∀ a b, b ≠ 0%F → (b * a / b)%F = a
  else not_applicable.
Proof.
intros rop.
unfold rngl_has_quot; cbn.
unfold polyn_opt_inv_or_quot.
destruct (bool_dec rngl_mul_is_comm) as [Hco| Hco]; rewrite Hco; [ | easy ].
now rewrite Bool.andb_false_r.
Qed.

Theorem polyn_opt_eqb_eq :
  let _ := polyn_ring_like_op in
  if rngl_has_eqb then ∀ a b : polyn T, (a =? b)%F = true ↔ a = b
  else not_applicable.
Proof.
intros rop; subst rop.
rewrite Heb.
apply polyn_eqb_eq.
intros a b.
split. 2: {
  intros; subst b.
  apply (rngl_eqb_refl Heb).
}
intros Hab.
now apply (rngl_eqb_eq Heb) in Hab.
Qed.

Theorem polyn_opt_le_dec :
  let _ := polyn_ring_like_op in
  if rngl_has_dec_le then ∀ a b : polyn T, {(a ≤ b)%F} + {¬ (a ≤ b)%F}
  else not_applicable.
Proof.
intros rop; subst rop.
destruct rngl_has_dec_le; [ | easy ].
now intros; right; cbn.
Qed.

Theorem polyn_opt_integral :
  let _ := polyn_ring_like_op in
  if rngl_is_integral then
    ∀ a b : polyn T, (a * b)%F = 0%F → a = 0%F ∨ b = 0%F
  else not_applicable.
Proof.
intros rop; subst rop.
destruct (bool_dec rngl_is_integral) as [Hii| Hii]; rewrite Hii; [ | easy ].
intros * Hab.
cbn in Hab.
apply (f_equal lap) in Hab.
cbn in Hab.
specialize (proj2 (all_0_lap_norm_nil _) Hab) as H1.
destruct a as (la, pa).
destruct b as (lb, pb).
cbn in Hab, H1 |-*.
enough (H : la = [] ∨ lb = []). {
  destruct H as [H| Ha]; [ left; subst la | right; subst lb ].
  now apply eq_polyn_eq.
  now apply eq_polyn_eq.
}
apply Bool.orb_true_iff in pa, pb.
destruct pa as [pa| pa]. {
  now left; apply is_empty_list_empty in pa.
}
destruct pb as [pb| pb]. {
  now right; apply is_empty_list_empty in pb.
}
destruct la as [| a] using rev_ind; [ now left | clear IHla ].
rewrite last_last in pa.
destruct lb as [| b] using rev_ind; [ now right | clear IHlb ].
rewrite last_last in pb.
specialize (last_lap_mul (la ++ [a]) (lb ++ [b])) as H2.
do 2 rewrite last_last in H2.
rewrite List_last_nth in H2.
rewrite H1 in H2.
symmetry in H2.
apply (rngl_neqb_neq Heb) in pa, pb.
apply (rngl_integral Hos) in H2; [ | now rewrite Hii ].
now destruct H2.
Qed.

Theorem lap_rngl_mul_nat_l :
  let lop := lap_ring_like_op in
  ∀ i, i ≠ 0 → (rngl_mul_nat_l i 1)%lap = [rngl_mul_nat_l i 1].
Proof.
intros lop * Hiz.
subst lop.
induction i; [ easy | clear Hiz; cbn ].
destruct i; [ now cbn; rewrite rngl_add_0_r | ].
cbn in IHi |-*.
now rewrite IHi.
Qed.

Theorem lap_polyn_rngl_mul_nat_l :
  let _ := polyn_ring_like_op in
  rngl_characteristic = 0
  → ∀ i, i ≠ 0 → lap (rngl_mul_nat_l i 1) = [rngl_mul_nat_l i 1].
Proof.
intros rop Hch * Hiz.
subst rop.
induction i; [ easy | clear Hiz; cbn ].
destruct i. {
  cbn; rewrite rngl_add_0_r.
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [H11| H11]; [ | easy ].
  apply (rngl_eqb_eq Heb) in H11.
  now apply rngl_1_neq_0 in H11.
}
cbn in IHi |-*.
rewrite IHi; [ cbn | easy ].
rewrite if_bool_if_dec.
destruct (bool_dec _) as [H11| H11]; [ | easy ].
clear IHi; exfalso.
apply (rngl_eqb_eq Heb) in H11.
specialize rngl_characteristic_prop as H1.
rewrite Hch in H1; cbn in H1.
now specialize (H1 (S i)); cbn in H1.
Qed.

Theorem lap_polyn_rngl_mul_nat_l_2 :
  let rop := polyn_ring_like_op in
  ∀ i, 0 < i < rngl_characteristic
  → lap (rngl_mul_nat_l i 1) = [rngl_mul_nat_l i 1].
Proof.
intros * Hi.
specialize (rngl_1_neq_0 H10) as H11.
specialize rngl_characteristic_prop as Hch.
rewrite if_bool_if_dec in Hch.
destruct (bool_dec _) as [Hchz| Hchz]. {
  apply Nat.eqb_eq in Hchz.
  now rewrite Hchz in Hi.
}
clear Hchz.
destruct Hch as (Hbef, Hch).
induction i; [ easy | cbn ].
remember (lap (rngl_mul_nat_l i 1)) as la eqn:Hla; symmetry in Hla.
destruct la as [| a]; cbn. {
  rewrite if_bool_if_dec.
  apply (rngl_eqb_neq Heb) in H11; rewrite H11.
  destruct (bool_dec _) as [| H]; [ easy | clear H ].
  cbn; f_equal; symmetry.
  rewrite <- rngl_add_0_r.
  apply rngl_add_compat_l.
  destruct i; [ easy | ].
  assert (H : 0 < S i < rngl_characteristic) by flia Hi.
  now specialize (IHi H).
}
symmetry; apply List_rev_symm; symmetry; cbn.
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [H12| H12]. {
    exfalso; apply (rngl_eqb_eq Heb) in H12.
    destruct i; [ easy | ].
    assert (H : 0 < S i < rngl_characteristic) by flia Hi.
    specialize (IHi H); clear H.
    injection IHi; clear IHi; intros; subst a la.
    clear Hlb.
    cbn in Hla.
    remember (lap (rngl_mul_nat_l i 1)) as lb eqn:Hlb; symmetry in Hlb.
    destruct lb as [| b]; cbn in Hla. {
      rewrite if_bool_if_dec in Hla.
      apply (rngl_eqb_neq Heb) in H11.
      rewrite H11 in Hla.
      destruct (bool_dec _) as [| H]; [ easy | clear H ].
      cbn in Hla.
      injection Hla; clear Hla; intros Hla; symmetry in Hla.
      rewrite <- rngl_add_0_r in Hla.
      apply (rngl_add_cancel_l Hos) in Hla.
      rewrite Hla in H12.
      apply (Hbef 2); [ flia Hi | easy ].
    }
    now specialize (Hbef (S (S i)) Hi) as H1.
  }
  f_equal.
  apply rngl_add_compat_l; symmetry.
  destruct i; [ easy | ].
  assert (H : 0 < S i < rngl_characteristic) by flia Hi.
  specialize (IHi H).
  now injection IHi; clear IHi; intros; subst a la.
}
exfalso.
destruct i; [ easy | ].
assert (H : 0 < S i < rngl_characteristic) by flia Hi.
specialize (IHi H); clear H.
now injection IHi; clear IHi; intros; subst a la.
Qed.

Theorem polyn_characteristic_prop :
  let rop := polyn_ring_like_op in
  if rngl_characteristic =? 0 then ∀ i : nat, rngl_mul_nat_l (S i) 1 ≠ 0%F
  else
    (∀ i : nat, 0 < i < rngl_characteristic → rngl_mul_nat_l i 1 ≠ 0%F) ∧
    rngl_mul_nat_l rngl_characteristic 1 = 0%F.
Proof.
intros rop; subst rop.
specialize rngl_characteristic_prop as H1.
rewrite if_eqb_eq_dec in H1 |-*.
destruct (Nat.eq_dec rngl_characteristic 0) as [Hcz| Hcz]. {
  intros i.
  specialize (H1 i) as H.
  intros Hi; apply H; clear H.
  apply (f_equal lap) in Hi.
  now rewrite lap_polyn_rngl_mul_nat_l in Hi.
} {
  destruct H1 as (Hbef, Hch).
  assert (Hbeg :
    let rop := polyn_ring_like_op in
    ∀ i : nat, 0 < i < rngl_characteristic → (i × 1)%F ≠ 0%F). {
    intros rop i Hi; cbn.
    specialize (Hbef _ Hi) as H1.
    intros H; apply H1; clear H1; rename H into H1.
    generalize H1; intros H2.
    apply (f_equal lap) in H2; cbn in H2.
    now rewrite lap_polyn_rngl_mul_nat_l_2 in H2.
  }
  move Hbeg before Hbef.
  split; [ easy | ].
  apply eq_polyn_eq; cbn.
...
  remember (rngl_mul_nat_l rngl_characteristic) as p eqn:Hp in |-*.
  symmetry in Hp.
  destruct p as (la, pa); cbn.
  apply (f_equal lap) in Hp; cbn in Hp.
  apply Bool.orb_true_iff in pa.
  destruct pa as [pa| pa]; [ now destruct la | ].
  apply (rngl_neqb_neq Heb) in pa.
  destruct la as [| a] using rev_ind; [ easy | clear IHla ].
  rewrite last_last in pa; exfalso.
  specialize (rngl_1_neq_0 H10) as H11.
...
  destruct la as [| b]. {
    cbn in Hp.
    clear IHla.
    induction rngl_characteristic as [| n]; [ easy | clear Hcz ].
    destruct n. {
      cbn in Hch.
      now rewrite rngl_add_0_r in Hch.
    }
    specialize (IHn (Nat.neq_succ_0 _)).
    cbn in Hch, Hp.
...
    cbn in Hch, Hp.
...
Theorem eq_lap_nil_iff : ∀ p, lap p = [] ↔ ∀ i, i < length (lap p) → nth i (lap p) 0%F = 0%F
...
(**)
  clear Hbef.
  destruct rngl_characteristic as [| i]; [ easy | clear Hcz ].
  cbn in Hch |-*.
  specialize (rngl_1_neq_0 H10) as H11.
  remember (lap (rngl_mul_nat_l i)) as la eqn:Hla; symmetry in Hla.
  destruct la as [| a]. {
    exfalso.
    destruct i; [ now cbn in Hch; rewrite rngl_add_0_r in Hch | ].
    cbn in Hla.
    remember (lap (rngl_mul_nat_l i)) as lb eqn:Hlb; symmetry in Hlb.
    destruct lb as [| b]. {
      cbn in Hla.
      apply (rngl_eqb_neq Heb) in H11.
      now rewrite H11 in Hla.
    }
    cbn in Hla.
    rewrite strip_0s_app in Hla.
    remember (strip_0s (rev lb)) as lc eqn:Hlc; symmetry in Hlc.
    destruct lc as [| c]. 2: {
      cbn in Hla.
      now apply app_eq_nil in Hla.
    }
    cbn in Hla.
    rewrite if_bool_if_dec in Hla.
    destruct (bool_dec _) as [Hbz| Hbz]. {
      clear Hla.
      apply (rngl_eqb_eq Heb) in Hbz.
      rewrite <- Hch in Hbz.
      apply (rngl_add_cancel_l Hos) in Hbz.
      subst b.
      clear Hch.
      induction i; [ easy | cbn in Hlb ].
(*
      assert (H : ∀ i0 : nat, 0 < i0 < S (S i) → rngl_mul_nat_l i0 ≠ 0%F). {
        intros j Hj.
        apply Hbef; flia Hj.
      }
      specialize (IHi H); clear H.
*)
      remember (lap (rngl_mul_nat_l i)) as la eqn:Hla; symmetry in Hla.
      destruct la as [| a]. {
        clear IHi.
        cbn in Hlb.
        apply (rngl_eqb_neq Heb) in H11.
        rewrite H11 in Hlb; cbn in Hlb.
        apply (rngl_eqb_neq Heb) in H11.
        injection Hlb; clear Hlb; intros H Hlb; subst lb.
        symmetry in Hlb.
        clear Hlc.
        rewrite <- rngl_add_0_r in Hlb.
        apply (rngl_add_cancel_l Hos) in Hlb.
        induction i. {
          now cbn in Hlb; rewrite rngl_add_0_r in Hlb.
        }
        cbn in Hla.
        remember (lap (rngl_mul_nat_l i)) as lc eqn:Hlc; symmetry in Hlc.
        destruct lc as [| c]. {
          cbn in Hla.
          apply (rngl_eqb_neq Heb) in H11.
          now rewrite H11 in Hla.
        }
        clear IHi.
        cbn in Hla.
        rewrite strip_0s_app in Hla.
        remember (strip_0s (rev lc)) as ld eqn:Hld; symmetry in Hld.
        destruct ld as [| d]. {
          cbn in Hla.
          rewrite if_bool_if_dec in Hla.
          destruct (bool_dec _) as [Hcz| Hcz]; [ | easy ].
          clear Hla.
          apply (rngl_eqb_eq Heb) in Hcz.
...
        specialize (Hbef (S i)) as H1.
        apply H1, Hlb; flia.
      }
      cbn in Hlb, IHi.
      rewrite strip_0s_app in Hlb.
      remember (strip_0s (rev la)) as ld eqn:Hld; symmetry in Hld.
      destruct ld as [| d]. {
        cbn in Hlb.
        rewrite if_bool_if_dec in Hlb.
        destruct (bool_dec _) as [Haz| Haz]; [ easy | ].
        injection Hlb; clear Hlb; intros H1 Hlb; subst lb.
        apply (rngl_add_cancel_l Hos) in Hlb.
        subst a.
        clear Hlc.
        destruct la as [| a]; [ now apply IHi | ].
        clear IHi.
        cbn in Hld.
        rewrite strip_0s_app in Hld.
        remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
        destruct lb; [ | easy ].
        cbn in Hld.
        rewrite if_bool_if_dec in Hld.
        destruct (bool_dec _) as [Haz'| Haz']; [ | easy ].
        clear Hld.
        apply (rngl_eqb_eq Heb) in Haz'; subst a.
...
  specialize (rngl_1_neq_0 H10) as H11.
  cbn in Hch |-*.
  destruct i; [ now cbn in Hch; rewrite rngl_add_0_r in Hch | ].
...
  rewrite lap_rngl_mul_nat_l; try easy. 2: {


Search (lap (rngl_mul_nat_l _)).
Inspect 4.
rewrite lap_rngl_mul_nat_l.
Search (lap (rngl_mul_nat_l _)).
...
  rewrite lap_polyn_rngl_mul_nat_l; try easy. 2: {
Set Printing Implicit.

  induction rngl_characteristic as [| i]; [ easy | clear Hcz ].
  specialize (rngl_1_neq_0 H10) as H11.
  cbn in Hch |-*.
  destruct i; [ now cbn in Hch; rewrite rngl_add_0_r in Hch | ].
  cbn in Hch |-*.
...
  destruct i. {
    cbn in Hch.
    now rewrite rngl_add_0_r in Hch.
  }
  specialize (IHi (Nat.neq_succ_0 _)).
...
    exfalso; clear H1.
    induction i; [ easy | ].
    cbn in H2.
    destruct i. {
      cbn in H2.
      rewrite if_bool_if_dec in H2.
      destruct (bool_dec _) as [H11| H11]; [ | easy ].
      apply (rngl_eqb_eq Heb) in H11.
      now specialize (rngl_1_neq_0 H10) as H12.
    }
Inspect 1.
...
assert (H : 0 < S i < rngl_characteristic) by flia Hi.
specialize (IHi H); clear H.
remember (lap (rngl_mul_nat_l (S i))) as la eqn:Hla; symmetry in Hla.
destruct la as [| a]; [ easy | clear IHi ].
cbn in H2.
rewrite strip_0s_app in H2.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb; [ | now cbn in H2; apply app_eq_nil in H2 ].
apply List_rev_symm in H2; cbn in H2.
rewrite if_bool_if_dec in H2.
destruct (bool_dec _) as [Haz| Haz]; [ clear H2 | easy ].
apply (rngl_eqb_eq Heb) in Haz.
...
cbn in Hla.
remember (lap (rngl_mul_nat_l i)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn in Hla.
  rewrite if_bool_if_dec in Hla.
  destruct (bool_dec _) as [H11| H11]. {
    apply (rngl_eqb_eq Heb) in H11.
    now specialize (rngl_1_neq_0 H10) as H12.
  }
  cbn in Hla; injection Hla; clear Hla; intros; subst a la.
  specialize (Hbef 2).
  cbn in Hbef.
  assert (H : 0 < 2 < rngl_characteristic) by flia Hi.
  specialize (Hbef H); clear H.
  now rewrite rngl_add_0_r in Hbef.
}
cbn in Hla.
rewrite strip_0s_app in Hla.
remember (strip_0s (rev lc)) as ld eqn:Hld; symmetry in Hld.
destruct ld as [| d]. {
  cbn in Hla.
  rewrite if_bool_if_dec in Hla.
  destruct (bool_dec _) as [H11| H11]; [ easy | ].
  cbn in Hla.
  injection Hla; clear Hla; intros; subst a la.
  clear Hlb.
  induction i; [ easy | ].
  rewrite lap_polyn_rngl_mul_nat_l_2 in Hlc; [ | flia Hi ].
  injection Hlc; clear Hlc; intros; subst c lc.
...
  now specialize (Hbef (S (S i)) Hi).
...
Search (lap (rngl_mul_nat_l _)).
Set Printing All.
...
    apply (rngl_eqb_neq Heb) in H11.
      now specialize (rngl_1_neq_0 H10) as H12.
    }
...
Check lap_rngl_mul_nat_l.
Set Printing Implicit.
...
  remember (rngl_mul_nat_l rngl_characteristic) as a eqn:Ha in |-*.
  destruct a as (la, pa).
  apply eq_polyn_eq; cbn.
  apply (f_equal lap) in Ha; cbn in Ha.
  apply Bool.orb_true_iff in pa.
  destruct pa as [pa| pa]; [ now apply is_empty_list_empty in pa | ].
  apply (rngl_neqb_neq Heb) in pa.
  destruct la as [| a] using rev_ind; [ easy | exfalso ].
  rewrite last_last in pa.
  symmetry in Ha.
... ...
rewrite rngl_mul_nat_l_char in Ha; [ | easy ].
now symmetry in Ha; apply app_eq_nil in Ha.
... ...
generalize Ha; intros H.
apply (f_equal length) in H.
rewrite rngl_mul_nat_l_char_length in H; [ | easy ].
rewrite app_length, Nat.add_comm in H; cbn in H.
easy.
destruct la; [ | easy ].
cbn in Ha.
...
  clear IHla.
...
Set Printing Implicit.
Check lap_rngl_mul_nat_l.
Inspect 2.
rewrite lap_polyn_rngl_mul_nat_l in Ha; try easy.
...
  Search rngl_characteristic.
rewrite lap_polyn_rngl_mul_nat_l in Ha; try easy.
2: {
...
Inspect 2.
rewrite lap_rngl_mul_nat_l in H1.
  rewrite lap_polyn_rngl_mul_nat_l in Ha; [ | | easy ]. 2: {
...
...
  cbn in H1 |-*.
  remember rngl_characteristic as n eqn:Hn.

  unfold polyn_ring_like_op.
  cbn.
cbn.
  apply eq_polyn_eq; cbn.

  rewrite lap_polyn_rngl_mul_nat_l; [ | | easy ].
  remember rngl_characteristic as i eqn:Hi; symmetry in Hi.
  destruct i; [ easy | clear Hcz ].
...
  remember (rngl_mul_nat_l (S i)) as a eqn:Ha in |-*.
  symmetry in Ha.
  destruct a as (la, pa); cbn.
  cbn in Ha.
  induction la as [| a]; [ easy | exfalso ].
  cbn in pa.
  destruct la as [| b]. {
...
  cbn in H1 |-*.
...
destruct (Nat.eq_dec rngl_characteristic 0) as [Hcz| Hcz]. {
  specialize rngl_characteristic_prop as H1.
  rewrite Hcz in H1; cbn in H1.
  intros i Hi.
  apply (f_equal lap) in Hi.
  cbn in Hi.
  remember (lap (rngl_mul_nat_l i)) as la eqn:Hla.
  symmetry in Hla.
  destruct la as [| a]. {
    cbn in Hi.
    rewrite if_bool_if_dec in Hi.
    destruct (bool_dec _) as [H1az| H1az]; [ | easy ].
    apply (rngl_eqb_eq Heb) in H1az.
    now apply (rngl_1_neq_0 H10) in H1az.
  }
  cbn in Hi.
  rewrite strip_0s_app in Hi.
  remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb; [ cbn in Hi | now apply app_eq_nil in Hi ].
  rewrite if_bool_if_dec in Hi.
  destruct (bool_dec _) as [H1az| H1az]; [ clear Hi | easy ].
  apply (rngl_eqb_eq Heb) in H1az.
  destruct i; [ easy | cbn in Hla ].
  remember (lap (rngl_mul_nat_l i)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]. {
    cbn in Hla.
    rewrite if_bool_if_dec in Hla.
    destruct (bool_dec _) as [H2az| H2az]; [ easy | ].
    cbn in Hla.
    injection Hla; clear Hla; intros; subst a la.
    clear Hlb H2az.
    specialize (H1 1); cbn in H1.
    now rewrite rngl_add_0_r in H1.
  }
  cbn in Hla.
  rewrite strip_0s_app in Hla.
  remember (strip_0s (rev lc)) as ld eqn:Hld; symmetry in Hld.
  destruct ld as [| d]. {
    cbn in Hla.
    rewrite if_bool_if_dec in Hla.
    destruct (bool_dec _) as [H2az| H2az]; [ easy | ].
    cbn in Hla.
    injection Hla; clear Hla; intros; subst a la.
    clear Hlb.
...
    specialize (H1 1); cbn in H1.
    now rewrite rngl_add_0_r in H1.
...
(* ce théorème ci-dessous, suppose que la caractéristique soit
   nulle. Si non, contre-exemple : car=2 et lap (rngl_mul_nat_l 2)
   vaut [] et non pas [2] *)
Theorem lap_rngl_mul_nat_l :
  let _ := polyn_ring_like_op in
  ∀ i, i ≠ 0 → lap (rngl_mul_nat_l i) = [(rngl_mul_nat_l i)%F].
Proof.
intros rop * Hiz.
remember (rngl_mul_nat_l i) as a eqn:Ha.
symmetry in Ha.
destruct a as (la, pa); cbn.
apply (f_equal lap) in Ha; cbn in Ha.
apply Bool.orb_true_iff in pa.
destruct pa as [pa| pa]. {
  apply is_empty_list_empty in pa; subst la.
  exfalso.
(**)
  destruct i; [ easy | clear Hiz ].
  cbn in Ha.
  apply List_rev_symm in Ha; cbn in Ha.
  remember (lap (rngl_mul_nat_l i)) as la eqn:Hla.
  symmetry in Hla.
  destruct la as [| a]. {
    cbn in Ha.
    rewrite if_bool_if_dec in Ha.
    destruct (bool_dec _) as [H1az| H1az]; [ | easy ].
    apply (rngl_eqb_eq Heb) in H1az.
    now apply (rngl_1_neq_0 H10) in H1az.
  }
  cbn in Ha.
  rewrite strip_0s_app in Ha.
  remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb; [ cbn in Ha | easy ].
  rewrite if_bool_if_dec in Ha.
  destruct (bool_dec _) as [H1az| H1az]; [ clear Ha | easy ].
  apply (rngl_eqb_eq Heb) in H1az.
  destruct i; [ easy | cbn in Hla ].
  remember (lap (rngl_mul_nat_l i)) as lb eqn:Hlb'; symmetry in Hlb'.
  destruct lb. {
    cbn in Hla.
    rewrite if_bool_if_dec in Hla.
    destruct (bool_dec _) as [H2az| H2az]; [ easy | ].
    cbn in Hla.
    injection Hla; clear Hla; intros; subst a la.
    clear Hlb H2az.
...
  induction i; [ easy | clear Hiz ].
  destruct i. {
    cbn in Ha; rewrite if_bool_if_dec in Ha.
    destruct (bool_dec _) as [H1az| H1az]; [ | easy ].
    apply (rngl_eqb_eq Heb) in H1az.
    now apply (rngl_1_neq_0 H10) in H1az.
  }
  specialize (IHi (Nat.neq_succ_0 _)).
...
  remember (S i) as si; cbn in Ha; subst si.
  remember (lap (rngl_mul_nat_l (S i))) as la eqn:Hla.
  symmetry in Hla.
  destruct la as [| a]; [ now apply IHi | ].
  cbn in Ha; clear IHi.
  rewrite strip_0s_app in Ha.
  remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| b]; [ | now apply app_eq_nil in Ha ].
  cbn in Ha.
  rewrite if_bool_if_dec in Ha.
    destruct (bool_dec _) as [H1az| H1az]; [ | easy ].
    apply (rngl_eqb_eq Heb) in H1az.
    cbn in Hla.
...
    now apply (rngl_1_neq_0 H10) in H1az.
...
induction i; [ easy | clear Hiz ].
cbn.
destruct i. {
  cbn; rewrite if_bool_if_dec.
  destruct (bool_dec _) as [H1az| H1az]. {
    apply (rngl_eqb_eq Heb) in H1az.
    now apply (rngl_1_neq_0 H10) in H1az.
  }
  now rewrite rngl_add_0_r.
}
rewrite IHi; [ | easy ].
cbn.
rewrite if_bool_if_dec.
destruct (bool_dec _) as [H1| H1]; [ | easy ].
exfalso.
apply (rngl_eqb_eq Heb) in H1.
destruct (Nat.eq_dec rngl_characteristic 0) as [Hcz| Hcz]. {
  specialize rngl_characteristic_prop as H11.
  rewrite Hcz in H11.
  cbn in H11.
  now specialize (H11 (S i)); cbn in H11.
}
... ...
now rewrite lap_rngl_mul_nat_l in Hi.
...
(**)
  cbn in Hi.
  remember (lap (rngl_mul_nat_l i)) as la eqn:Hla; symmetry in Hla.
  destruct la as [| a]. {
    cbn in Hi.
    rewrite if_bool_if_dec in Hi.
    destruct (bool_dec (1 =? 0)%F) as [H11| H11]; [ | easy ].
    apply (rngl_eqb_eq Heb) in H11.
    now apply rngl_1_neq_0 in H11.
  }
  cbn in Hi.
  rewrite strip_0s_app in Hi.
  remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| b]. {
    cbn in Hi.
    rewrite if_bool_if_dec in Hi.
    destruct (bool_dec _) as [H1az| H1az]; [ | easy ].
    apply (rngl_eqb_eq Heb) in H1az.
    specialize (H1
...
  cbn - [ lap_norm ] in Hi.
  remember (lap (rngl_mul_nat_l i)) as la eqn:Hla; symmetry in Hla.
  destruct la as [| a]. {
    cbn in Hi.
    rewrite if_bool_if_dec in Hi.
    destruct (bool_dec (1 =? 0)%F) as [H11| H11]; [ | easy ].
    apply (rngl_eqb_eq Heb) in H11.
    now apply rngl_1_neq_0 in H11.
  }
  cbn in Hi.
  rewrite strip_0s_app in Hi.
  remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| b]. {
    cbn in Hi.
...
eq_lap_add_0: ∀ la lb : list T, (la + lb)%lap = [] → la = [] ∧ lb = []
...
  induction i. {
    cbn.
    rewrite polyn_add_0_r.
    specialize polyn_1_neq_0 as H1.
    now rewrite H10 in H1.
  }
  intros H; apply IHi; clear IHi.
Search rngl_mul_nat_l.
...
rngl_mul_nat_l_inj:
  ∀ (T : Type) (ro : ring_like_op T) (rp : ring_like_prop T),
    rngl_has_opp_or_sous = true → rngl_characteristic = 0 → ∀ i j : nat, rngl_mul_nat_l i = rngl_mul_nat_l j → i = j
...
  intros i; cbn.
  induction i. {
    rewrite polyn_add_0_r.
    specialize polyn_1_neq_0 as H1.
    now rewrite H10 in H1.
  }
  cbn.
  intros H; apply IHi; clear IHi.
Search ((_ + _) = _)%pol.
Check polyn_add_sub_eq_l.
Check rngl_add_sub_eq_l.
...
  intros i; cbn.
  intros H.
  apply polyn_add_sub_eq_l in H.
  induction i. {
    rewrite polyn_add_0_r.
    specialize polyn_1_neq_0 as H1.
    now rewrite H10 in H1.
  }
  cbn.
  intros H; apply IHi; clear IHi.
Search ((_ + _) = 0)%pol.
...
  specialize rngl_characteristic_prop as H1.
  rewrite Hcz in H1; cbn in H1.
  specialize (H1 i).
  cbn.
...
rewrite if_bool_if_dec.
destruct (bool_dec (rngl_characteristic =? 0)) as [Hcz| Hcz].
...
*)

Definition polyn_ring_like_prop : ring_like_prop (polyn T) :=
  {| rngl_mul_is_comm := rngl_mul_is_comm;
     rngl_has_eqb := rngl_has_eqb;
     rngl_has_dec_le := rngl_has_dec_le;
     rngl_has_1_neq_0 := rngl_has_1_neq_0;
     rngl_is_ordered := rngl_is_ordered;
     rngl_is_integral := rngl_is_integral;
     rngl_characteristic := rngl_characteristic;
     rngl_add_comm := polyn_add_comm;
     rngl_add_assoc := polyn_add_assoc;
     rngl_add_0_l := polyn_add_0_l;
     rngl_mul_assoc := polyn_mul_assoc;
     rngl_mul_1_l := polyn_mul_1_l;
     rngl_mul_add_distr_l := polyn_mul_add_distr_l;
     rngl_opt_1_neq_0 := polyn_1_neq_0;
     rngl_opt_mul_comm := polyn_opt_mul_comm;
     rngl_opt_mul_1_r := polyn_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := polyn_opt_mul_add_distr_r;
     rngl_opt_add_opp_l := polyn_opt_add_opp_l;
     rngl_opt_add_sub := polyn_opt_has_no_sous _;
     rngl_opt_sub_sub_sub_add := polyn_opt_has_no_sous _;
     rngl_opt_mul_sub_distr_l := polyn_opt_has_no_sous _;
     rngl_opt_mul_sub_distr_r := polyn_opt_has_no_sous _;
     rngl_opt_mul_inv_l := polyn_opt_has_no_inv _;
     rngl_opt_mul_inv_r := polyn_opt_has_no_inv_and _ _;
     rngl_opt_mul_div := polyn_opt_mul_div;
     rngl_opt_mul_quot_r := polyn_opt_mul_quot_r;
     rngl_opt_eqb_eq := polyn_opt_eqb_eq;
     rngl_opt_le_dec := polyn_opt_le_dec;
     rngl_opt_integral := polyn_opt_integral;
     rngl_characteristic_prop := polyn_characteristic_prop;
     rngl_opt_le_refl := 5;
     rngl_opt_le_antisymm := ?rngl_opt_le_antisymm;
     rngl_opt_le_trans := ?rngl_opt_le_trans;
     rngl_opt_add_le_compat := ?rngl_opt_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := ?rngl_opt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := ?rngl_opt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := ?rngl_opt_mul_le_compat;
     rngl_opt_not_le := ?rngl_opt_not_le |}.

...

End a.

Arguments polyn_ring_like_op T%type {ro rp Heb H10 Hop Hiv}.
Arguments lap_mul {T ro} (la lb)%list.
Arguments polyn_norm_prop {T ro rp} {Heb H10 la}.

(*
Declare Scope lap_scope.
Delimit Scope lap_scope with lap.
(*
Notation "1" := [1%F] : lap_scope.
*)
Notation "- a" := (lap_opp a) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
(*
Notation "a ^ b" := (lap_power a b) : lap_scope.
*)
*)

(*
Notation "'ⓧ' ^ a" := (monom a) (at level 30, format "'ⓧ' ^ a") : poly_scope.
Notation "'ⓧ'" := (monom 1) (at level 30, format "'ⓧ'") : poly_scope.
*)

(*
Require Import ZArith RnglAlg.Zrl.
Global Existing Instance Z_ring_like_prop.
Open Scope Z_scope.
Compute (lap_add [1;2;3] [4;5;6]).
Check (lap_add [1;2;3] [4;5;6]).
Compute ([1;2;3] + [4;5;6])%lap.
(* (x-1)(x+1) *)
Compute ([1; 1] * [-1; 1])%lap.
Compute (monom 3).
Compute (ⓧ^4)%pol.
Compute (ⓧ^4+ⓧ)%pol.
Compute (ⓧ^4-ⓧ)%pol.
Compute (3*ⓧ^4)%pol.
...
Compute (ⓧ^4-ⓧ+2%F)%pol.
Compute (ⓧ)%pol.
(* ah bin zut, non seulement ça n'affiche pas la notation, mais
   ça affiche le long Z_ring_like_prop *)
(* peut-être que, finalement, faut que je laisse tomber ce champ
   "lap_prop" dans le type polyn ? *)
*)

(*
Definition list_nth_def_0 {α} {R : ring α} n l := List.nth n l 0%Rng.
*)

Section a.

(* ring-like properties *)

Existing Instance polyn_ring_like_op.

...

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

Section lap.

Context {α : Type}.
Context {r : ring α}.

Theorem lap_norm_idemp : ∀ la, lap_norm (lap_norm la) = lap_norm la.
Proof.
intros.
unfold lap_norm.
rewrite rev_involutive.
now rewrite strip_0s_idemp.
Qed.

(* addition theorems *)

Theorem lap_add_add_swap : ∀ la lb lc,
  lap_add (lap_add la lb) lc = lap_add (lap_add la lc) lb.
Proof.
intros la lb lc.
do 2 rewrite <- lap_add_assoc.
now rewrite (lap_add_comm lb).
Qed.

(* multiplication theorems *)

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

Theorem lap_mul_mul_swap : ∀ la lb lc,
  lap_mul (lap_mul la lb) lc = lap_mul (lap_mul la lc) lb.
Proof.
intros la lb lc.
do 2 rewrite <- lap_mul_assoc.
now rewrite (lap_mul_comm lb).
Qed.

(* *)

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

Theorem poly_add_opp_r {α} {r : ring α} : ∀ p, (p - p)%pol = 0%pol.
Proof.
intros p.
unfold poly_sub.
rewrite poly_add_comm.
apply poly_add_opp_l.
Qed.

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
