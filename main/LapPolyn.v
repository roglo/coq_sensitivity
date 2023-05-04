(* LapPolyn.v *)

(* lists as polynomials ; the fact that the coefficient of the highest degree
   is not zero is not tested. It is going to be tested in Polynomial.v. *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List ListNotations (*Init.Nat*).

Require Import Misc RingLike IterAdd (*IterAnd*).
(*
Require Import PermutationFun SortingFun.
*)

(* (lap : list as polynomial) *)
(* e.g. polynomial ax²+bx+c is implemented by the list [c;b;a] *)

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
(*
Context {Hos : rngl_has_opp_or_subt = true}.
Context {Heb : rngl_has_eqb = true}.
*)

(* addition *)

Definition lap_add la lb :=
  map2 rngl_add
    (la ++ repeat 0%L (length lb - length la))
    (lb ++ repeat 0%L (length la - length lb)).

Definition lap_subt la lb :=
  map2 rngl_subt
    (la ++ repeat 0%L (length lb - length la))
    (lb ++ repeat 0%L (length la - length lb)).

Definition lap_opp la := map rngl_opp la.
Definition lap_sub la lb :=
  if rngl_has_opp then lap_add la (lap_opp lb)
  else if rngl_has_subt then lap_subt la lb
  else repeat 0%L (max (length la) (length lb)).

Theorem fold_lap_opp : ∀ la, map rngl_opp la = lap_opp la.
Proof. easy. Qed.

(* multiplication *)

Fixpoint lap_convol_mul la lb i len :=
  match len with
  | O => []
  | S len1 =>
      (∑ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%L ::
      lap_convol_mul la lb (S i) len1
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

(* power *)

Fixpoint lap_power la n :=
  match n with
  | O => [1%L]
  | S m => lap_mul la (lap_power la m)
  end.

(* euclidean division *)

Fixpoint strip_0s la :=
  match la with
  | [] => []
  | a :: la' => if (a =? 0)%L then strip_0s la' else la
  end.

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
            let cq := (a / b)%L in
            let rlr := lap_sub rla' (map (λ cb, (cb * cq)%L) rlb') in
            (Some cq, rlr)
      end
  end.

Fixpoint rlap_quot_rem_loop it (rla rlb : list T) : list T * list T :=
  match it with
  | 0 => ([], [rngl_of_nat 97]) (* algo err: not enough iterations *)
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
Proof.
intros; cbn.
rewrite Nat.sub_0_r, app_nil_r.
induction la as [| a]; [ easy | cbn ].
now rewrite rngl_add_0_l; f_equal.
Qed.

Theorem lap_add_0_r : ∀ la, lap_add la [] = la.
Proof.
intros.
unfold lap_add; cbn.
rewrite Nat.sub_0_r, app_nil_r.
induction la as [| a]; [ easy | cbn ].
now rewrite rngl_add_0_r; f_equal.
Qed.

Theorem lap_mul_0_l : ∀ la, lap_mul [] la = [].
Proof. easy. Qed.

Theorem lap_mul_0_r : ∀ la, lap_mul la [] = [].
Proof. now intros; destruct la. Qed.

Theorem eq_lap_mul_0 : ∀ la lb, lap_mul la lb = [] → la = [] ∨ lb = [].
Proof.
intros * Hab.
destruct la as [| a]; [ now left | right ].
destruct lb as [| b]; [ easy | exfalso ].
cbn in Hab.
now rewrite Nat.add_succ_r in Hab.
Qed.

Theorem strip_0s_length_le : ∀ l, length (strip_0s l) ≤ length l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
destruct (a =? 0)%L; cbn; [ | easy ].
flia IHl.
Qed.

(* could be moved to Misc.v *)
Theorem min_add_sub_max : ∀ a b, min (a + (b - a)) (b + (a - b)) = max a b.
Proof.
intros.
destruct (le_dec a b) as [Hab| Hab]. {
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  rewrite Nat.add_0_r, Nat.min_id; symmetry.
  now apply Nat.max_r.
} {
  apply Nat.nle_gt, Nat.lt_le_incl in Hab.
  rewrite Nat.min_comm, Nat.max_comm.
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  rewrite Nat.add_0_r, Nat.min_id; symmetry.
  now apply Nat.max_r.
}
Qed.

Theorem lap_add_length : ∀ la lb,
  length (lap_add la lb) = max (length la) (length lb).
Proof.
intros.
unfold lap_add.
rewrite map2_length.
do 2 rewrite app_length, repeat_length.
apply min_add_sub_max.
Qed.

Theorem lap_subt_length : ∀ la lb,
  length (lap_subt la lb) = max (length la) (length lb).
Proof.
intros.
unfold lap_subt.
rewrite map2_length.
do 2 rewrite app_length, repeat_length.
apply min_add_sub_max.
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
unfold lap_sub.
destruct rngl_has_opp; [ now rewrite lap_add_length, lap_opp_length | ].
destruct rngl_has_subt; [ now rewrite lap_subt_length | ].
now rewrite repeat_length.
Qed.

End a.

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.

Arguments lap_add {T ro} (la lb)%lap.
Arguments lap_add_length {T ro} (la lb)%lap.
Arguments lap_add_0_l {T ro rp} la%lap.
Arguments lap_add_0_r {T ro rp} la%lap.
Arguments lap_convol_mul {T ro} (la lb)%lap (i len)%nat.
Arguments lap_mul {T ro} (la lb)%lap.
Arguments lap_opp {T ro} la%lap.
Arguments lap_quot {T ro} (la lb)%lap.
Arguments lap_quot_rem {T ro} (la lb)%lap.
Arguments lap_rem {T ro} (la lb)%lap.
Arguments lap_sub {T ro} (la lb)%lap.
Arguments lap_subt {T ro} (la lb)%lap.
Arguments rlap_quot_rem {T ro} (rla rlb)%list.
Arguments rlap_quot_rem_loop {T ro} it%nat (rla rlb)%list.
Arguments rlap_quot_rem_step {T ro} (rla rlb)%list.
Arguments strip_0s {T ro} la%list.
Arguments strip_0s_length_le {T ro} l%list.
