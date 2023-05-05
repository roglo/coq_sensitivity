(* LapPolyn.v *)

(* lists as polynomials ; the fact that the coefficient of the highest degree
   is not zero is not tested. It is going to be tested in Polynomial.v. *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List ListNotations Init.Nat.

Require Import Misc RingLike IterAdd.

(* (lap : list as polynomial) *)
(* e.g. polynomial ax²+bx+c is implemented by the list [c;b;a] *)

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
Context {Heb : rngl_has_eqb = true}.

(* normalization: lap not ending with 0s *)

Fixpoint strip_0s la :=
  match la with
  | [] => []
  | a :: la' => if (a =? 0)%L then strip_0s la' else la
  end.

Definition lap_norm la := rev (strip_0s (rev la)).

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
destruct (a =? 0)%L; [ apply IHla | easy ].
Qed.

Theorem strip_0s_idemp : ∀ la, strip_0s (strip_0s la) = strip_0s la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ easy | cbn ].
now rewrite Haz.
Qed.

(* *)

Definition lap_zero : list T := [].
Definition lap_one := [1%L].

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

(* evaluation of a polynomial in x *)
(* and composition of polynomials *)

Definition rlap_horner A (zero : A) (add mul : A → A → A) rla x :=
  iter_list rla (λ accu a, add (mul accu x) a) zero.

Definition lap_horner A (zero : A) (add mul : A → A → A) la x :=
  rlap_horner zero add mul (rev la) x.

Definition eval_rlap :=
  rlap_horner 0%L rngl_add rngl_mul.

Definition eval_lap la x :=
  eval_rlap (rev la) x.

Definition rlap_compose rla rlb :=
  rlap_horner [] lap_add lap_mul (map (λ a, [a]) rla) (rev rlb).

Definition lap_compose la lb :=
  rlap_compose (rev la) (rev lb).

End a.

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.

Arguments eval_lap {T ro} la%lap x%L.
Arguments lap_add {T ro} (la lb)%lap.
Arguments lap_convol_mul {T ro} (la lb)%lap (i len)%nat.
Arguments lap_mul {T ro} (la lb)%lap.
Arguments lap_norm {T ro} la%lap.
Arguments lap_one {T ro}.
Arguments lap_opp {T ro} la%lap.
Arguments lap_quot {T ro} (la lb)%lap.
Arguments lap_rem {T ro} (la lb)%lap.
Arguments lap_sub {T ro} (la lb)%lap.
Arguments lap_subt {T ro} (la lb)%lap.
Arguments rlap_quot_rem_loop {T ro} it%nat (rla rlb)%list.
Arguments rlap_quot_rem_step {T ro} (rla rlb)%list.
Arguments strip_0s {T ro} la%list.

Notation "0" := lap_zero : lap_scope.
Notation "1" := lap_one : lap_scope.
Notation "- a" := (lap_opp a) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
Notation "a / b" := (lap_quot a b) : lap_scope.
Notation "a 'mod' b" := (lap_rem a b) : lap_scope.
Notation "a '°' b" := (lap_compose a b) (at level 40, left associativity) :
  lap_scope.

(*
Arguments lap_quot_rem {T ro} (la lb)%list.
Arguments rlap_quot_rem {T ro} (rla rlb)%list.
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.
Local Existing Instance Q_ring_like_op.
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

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
Context {Heb : rngl_has_eqb = true}.

Theorem lap_add_0_l : ∀ la, (0 + la)%lap = la.
Proof.
intros; cbn.
rewrite Nat.sub_0_r, app_nil_r.
induction la as [| a]; [ easy | cbn ].
now rewrite rngl_add_0_l; f_equal.
Qed.

Theorem lap_add_0_r : ∀ la, (la + 0)%lap = la.
Proof.
intros.
unfold lap_add; cbn.
rewrite Nat.sub_0_r, app_nil_r.
induction la as [| a]; [ easy | cbn ].
now rewrite rngl_add_0_r; f_equal.
Qed.

Theorem lap_mul_0_l : ∀ la, (0 * la = 0)%lap.
Proof. easy. Qed.

Theorem lap_mul_0_r : ∀ la, (la * 0 = 0)%lap.
Proof. now intros; destruct la. Qed.

Theorem eq_lap_mul_0 : ∀ la lb, (la * lb = 0)%lap → la = 0%lap ∨ lb = 0%lap.
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

Theorem lap_add_length : ∀ la lb,
  length (la + lb)%lap = max (length la) (length lb).
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

Theorem lap_opp_length : ∀ la, length (- la)%lap = length la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
f_equal; apply IHla.
Qed.

Theorem lap_sub_length : ∀ la lb,
  length (la - lb)%lap = max (length la) (length lb).
Proof.
intros.
unfold lap_sub.
destruct rngl_has_opp; [ now rewrite lap_add_length, lap_opp_length | ].
destruct rngl_has_subt; [ now rewrite lap_subt_length | ].
now rewrite repeat_length.
Qed.

(* *)

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
destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]; [ easy | ].
apply Nat.ltb_ge in Hab.
injection Hrab; clear Hrab; intros; subst cq rlr.
rewrite lap_sub_length, map_length.
now rewrite max_l.
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

(* lap opposite or subtraction *)

Definition lap_opt_opp_or_subt :
  option ((list T → list T) + (list T → list T → list T)) :=
  None.

(* lap quotient *)

Definition lap_opt_inv_or_quot :
  option ((list T → list T) + (list T → list T → list T)) :=
(**)
  None.
(*
  match Sumbool.sumbool_of_bool rngl_has_opp with
  | left Hop =>
      match Sumbool.sumbool_of_bool rngl_has_inv with
      | left Hiv =>
          match rngl_opt_inv_or_quot with
          | Some _ => Some (inr lap_quot)
          | None => None
          end
      | right _ => None
      end
  | right _ => None
  end.
*)

(**)

Fixpoint lap_all_0 zero (eqb : T → T → bool) (la : list T) :=
  match la with
  | [] => true
  | a :: la' => if eqb a zero then lap_all_0 zero eqb la' else false
  end.

Fixpoint lap_eqb zero (eqb : T → _) (la lb : list T) :=
  match la with
  | [] => lap_all_0 zero eqb lb
  | a :: la' =>
      match lb with
      | [] => lap_all_0 zero eqb la
      | b :: lb' => if eqb a b then lap_eqb zero eqb la' lb' else false
      end
  end.

(* lap ring-like operators *)

Definition lap_ring_like_op : ring_like_op (list T) :=
  {| rngl_zero := [];
     rngl_one := lap_one;
     rngl_add := lap_add;
     rngl_mul := lap_mul;
     rngl_opt_opp_or_subt := lap_opt_opp_or_subt;
     rngl_opt_inv_or_quot := lap_opt_inv_or_quot;
     rngl_opt_eqb := None; (*Some (lap_eqb rngl_zero rngl_eqb);*)
     rngl_opt_le := None |}.

(* commutativity of addition *)

Theorem lap_add_comm : ∀ al1 al2,
  (al1 + al2)%lap = (al2 + al1)%lap.
Proof.
intros al1 al2.
unfold lap_add.
rewrite map2_swap.
apply map2_ext_in.
intros * Ha Hb.
apply rngl_add_comm.
Qed.

(* associativity of addition *)

Theorem map2_rngl_add_0_l :
  ∀ la, map2 rngl_add (repeat 0%L (length la)) la = la.
Proof.
intros.
induction la as [| la]; [ easy | cbn ].
now rewrite rngl_add_0_l; f_equal.
Qed.

Theorem map2_rngl_add_0_r :
  ∀ la, map2 rngl_add la (repeat 0%L (length la)) = la.
Proof.
intros.
induction la as [| la]; [ easy | cbn ].
now rewrite rngl_add_0_r; f_equal.
Qed.

Theorem map2_rngl_subt_0_r :
  rngl_has_subt = true →
  ∀ la, map2 rngl_subt la (repeat 0%L (length la)) = la.
Proof.
intros Hsu *.
induction la as [| la]; [ easy | cbn ].
now rewrite (rngl_subt_0_r Hsu); f_equal.
Qed.

Theorem fold_lap_add :
  ∀ la lb,
  map2 rngl_add (la ++ repeat 0%L (length lb - length la))
    (lb ++ repeat 0%L (length la - length lb)) =
  lap_add la lb.
Proof. easy. Qed.

Theorem lap_add_assoc : ∀ al1 al2 al3,
  (al1 + (al2 + al3))%lap = (al1 + al2 + al3)%lap.
Proof.
intros al1 al2 al3.
revert al2 al3.
induction al1; intros; [ now do 2 rewrite lap_add_0_l | ].
cbn.
destruct al2. {
  cbn.
  rewrite Nat.sub_0_r, app_nil_r.
  rewrite map2_length, repeat_length, Nat.min_id.
  rewrite map2_length, app_nil_r, repeat_length.
  rewrite Nat.min_id.
  rewrite map2_rngl_add_0_l.
  rewrite rngl_add_0_r.
  remember (al3 ++ _) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]; [ easy | ].
  f_equal.
  now rewrite map2_rngl_add_0_r.
}
destruct al3. {
  cbn.
  rewrite rngl_add_assoc; f_equal.
  do 2 rewrite map2_length.
  rewrite app_nil_r, repeat_length, Nat.min_id.
  rewrite map2_rngl_add_0_r, app_nil_r.
  do 2 rewrite app_length, repeat_length.
  rewrite fold_lap_add.
  rewrite min_add_sub_max.
  rewrite <- lap_add_length.
  now rewrite map2_rngl_add_0_r.
}
cbn.
rewrite rngl_add_assoc; f_equal.
do 2 rewrite map2_length.
do 4 rewrite app_length, repeat_length.
do 2 rewrite min_add_sub_max.
do 2 rewrite fold_lap_add.
do 2 rewrite <- lap_add_length.
do 2 rewrite fold_lap_add.
apply IHal1.
Qed.

(* associativity of multiplication *)

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
destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
  apply (rngl_eqb_eq Heb) in Haz; subst a.
  destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
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
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    cbn in Hlen.
    clear a Haz.
    apply IHla; [ easy | flia Hlen ].
  }
  rewrite Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
  exfalso; clear b Hbz.
  clear - Haz Hll Hlen.
  assert (H : length lb ≤ length la) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction lb as [| b]; [ easy | ].
  cbn in Hll.
  rewrite if_bool_if_dec in Hll.
  destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
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

Theorem list_nth_lap_eq : ∀ la lb,
  (∀ i, (List.nth i la 0 = List.nth i lb 0)%L)
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
    assert (Hla : ∀ i, nth i la 0%L = 0%L). {
      intros i.
      clear - ro rp Heb Hlc.
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
        destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ | easy ].
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
    destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
      apply (rngl_eqb_eq Heb) in Haz.
      assert (Hlb : ∀ i, nth i lb 0%L = 0%L). {
        intros.
        rewrite <- Hi; cbn.
        destruct i; [ easy | ].
        apply Hla.
      }
      clear - ro rp Heb Hlb.
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
      destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
        apply (rngl_eqb_eq Heb) in Hbz; subst b.
        now specialize (Hi 0).
      }
      f_equal.
      now specialize (Hi 0).
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, nth i la 0%L = nth i lb 0%L). {
      intros i.
      now specialize (Hi (S i)); cbn in Hi.
    }
    specialize (IHla H); clear H.
    now rewrite Hld in IHla.
  }
  destruct lb as [| b]. {
    specialize (IHla []).
    assert (H : ∀ i : nat, nth i la 0%L = nth i [] 0%L). {
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
    destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
      apply (rngl_eqb_eq Heb) in Hbz; subst b.
      specialize (IHla lb).
      assert (H : ∀ i : nat, nth i la 0%L = nth i lb 0%L). {
        intros i.
        now specialize (Hi (S i)); cbn in Hi.
      }
      specialize (IHla H); clear H.
      now rewrite Hld in IHla.
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, nth i la 0%L = nth i lb 0%L). {
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

Theorem list_nth_lap_convol_mul_aux :
  rngl_has_opp_or_subt = true →
  ∀ la lb n i len,
  List.length la + List.length lb - 1 = (i + len)%nat
  → (List.nth n (lap_convol_mul la lb i len) 0%L =
     ∑ (j = 0, n + i),
     List.nth j la 0 * List.nth (n + i - j) lb 0)%L.
Proof.
intros Hos * Hlen.
revert la lb i n Hlen.
induction len; intros. {
  cbn.
  rewrite Nat.add_0_r in Hlen.
  rewrite all_0_rngl_summation_0; [ now destruct n | ].
  intros j (_, Hj).
  destruct (le_dec (length la) j) as [H1| H1]. {
    rewrite List.nth_overflow; [ | easy ].
    apply (rngl_mul_0_l Hos).
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

(* to be unified perhaps with list_nth_convol_mul *)
Theorem list_nth_lap_convol_mul :
  rngl_has_opp_or_subt = true →
  ∀ la lb i len,
  len = length la + length lb - 1
  → (List.nth i (lap_convol_mul la lb 0 len) 0 =
     ∑ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%L.
Proof.
intros Hos * Hlen.
symmetry in Hlen.
rewrite (list_nth_lap_convol_mul_aux Hos); [ | easy ].
now rewrite Nat.add_0_r.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul_r :
  rngl_has_opp_or_subt = true →
  ∀ la lb lc k,
   (∑ (i = 0, k),
      nth i lc 0 *
      nth (k - i) (lap_convol_mul la lb 0 (length la + length lb - 1))  0 =
    ∑ (i = 0, k),
      nth (k - i) lc 0 *
      ∑ (j = 0, i), nth j la 0 * nth (i - j) lb 0)%L.
Proof.
intros Hos la lb lc k.
rewrite rngl_summation_rtl.
apply rngl_summation_eq_compat; intros i (_, Hi).
rewrite Nat.add_0_r.
f_equal.
rewrite Nat_sub_sub_distr; [ | easy ].
rewrite Nat.add_comm, Nat.add_sub.
now apply list_nth_lap_convol_mul.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul_l :
  rngl_has_opp_or_subt = true →
  ∀ la lb lc k,
  ∑ (i = 0, k),
    nth i (lap_convol_mul la lb 0 (length la + length lb - 1)) 0 *
    nth (k - i) lc 0 =
  ∑ (i = 0, k),
    (∑ (j = 0, i), nth j la 0 * nth (i - j) lb 0) *
    nth (k - i) lc 0.
Proof.
intros Hos la lb lc k.
apply rngl_summation_eq_compat; intros i (_, Hi).
f_equal.
now rewrite list_nth_lap_convol_mul.
Qed.

Theorem lap_norm_mul_assoc :
  rngl_has_opp_or_subt = true →
  ∀ la lb lc, lap_norm (la * (lb * lc)) = lap_norm (la * lb * lc).
Proof.
intros Hos la lb lc.
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
rewrite (list_nth_lap_convol_mul Hos); [ | easy ].
rewrite (list_nth_lap_convol_mul Hos); [ | easy ].
rewrite <- Hld, <- Hle.
rewrite (summation_mul_list_nth_lap_convol_mul_r Hos).
rewrite (summation_mul_list_nth_lap_convol_mul_l Hos).
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

Theorem lap_mul_assoc :
  rngl_has_opp_or_subt = true →
  ∀ la lb lc, (la * (lb * lc))%lap = (la * lb * lc)%lap.
Proof.
intros Hos *.
apply eq_lap_norm_eq_length. 2: {
  destruct la as [| a]; [ easy | ].
  destruct lb as [| b]; [ easy | ].
  destruct lc as [| c]. {
    now cbn; destruct (lap_convol_mul _ _ _ _).
  }
  cbn.
  do 4 (rewrite Nat.add_succ_r; cbn); f_equal.
  rewrite rngl_summation_only_one; cbn.
  rewrite rngl_summation_only_one; cbn.
  do 4 rewrite lap_convol_mul_length.
  apply Nat.add_assoc.
}
apply (lap_norm_mul_assoc Hos).
Qed.

(* multiplication by 1 *)

Theorem lap_convol_mul_const_l :
  rngl_has_opp_or_subt = true →
  ∀ a la i len,
  length la = i + len
  → lap_convol_mul [a] la i len =
    map (λ b, (a * b)%L) (skipn i la).
Proof.
intros Hos * Hlen.
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
  apply (rngl_mul_0_l Hos).
}
rewrite Nat.sub_0_r, rngl_add_0_r; cbn.
rewrite IHlen; [ | now rewrite Nat.add_succ_r in Hlen ].
symmetry.
rewrite (List_skipn_is_cons 0%L); [ easy | flia Hlen ].
Qed.

Theorem lap_convol_mul_const_r :
  rngl_has_opp_or_subt = true →
  ∀ a la i len,
  length la = i + len
  → lap_convol_mul la [a] i len =
    map (λ b, (b * a)%L) (skipn i la).
Proof.
intros Hos * Hlen.
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
  apply (rngl_mul_0_r Hos).
}
rewrite Nat.sub_diag, rngl_add_0_l; cbn.
rewrite IHlen; [ | flia Hlen ].
symmetry.
rewrite (List_skipn_is_cons 0%L); [ easy | flia Hlen ].
Qed.

Theorem lap_mul_const_l :
  rngl_has_opp_or_subt = true →
  ∀ a la, ([a] * la)%lap = map (λ b : T, (a * b)%L) la.
Proof.
intros Hos *.
unfold lap_mul.
destruct la as [| b]; [ easy | ].
now rewrite (lap_convol_mul_const_l Hos).
Qed.

Theorem lap_mul_const_r :
  rngl_has_opp_or_subt = true →
  ∀ a la, (la * [a])%lap = map (λ b : T, (b * a)%L) la.
Proof.
intros Hos *.
unfold lap_mul.
destruct la as [| b]; [ easy | ].
rewrite Nat.add_sub.
now rewrite (lap_convol_mul_const_r Hos).
Qed.

Theorem lap_mul_1_l :
  rngl_has_opp_or_subt = true →
  ∀ la, (1 * la)%lap = la.
Proof.
intros Hos *.
unfold lap_one.
rewrite (lap_mul_const_l Hos).
induction la as [| a]; [ easy | cbn ].
rewrite rngl_mul_1_l; f_equal.
apply IHla.
Qed.

Theorem lap_mul_1_r :
  rngl_has_opp_or_subt = true →
  ∀ la, (la * 1)%lap = la.
Proof.
intros Hos *.
unfold lap_one.
rewrite (lap_mul_const_r Hos).
induction la as [| a]; [ easy | cbn ].
rewrite rngl_mul_1_r; f_equal.
apply IHla.
Qed.

(* distributivity *)

Fixpoint lap_convol_mul_add_l (al1 al2 al3 : list T) i len :=
  match len with
  | O => []
  | S len1 =>
      (∑ (j = 0, i),
       (List.nth j al1 0 + List.nth j al2 0) *
       List.nth (i - j) al3 0)%L ::
       lap_convol_mul_add_l al1 al2 al3 (S i) len1
  end.

Fixpoint lap_convol_mul_add_r (al1 al2 al3 : list T) i len :=
  match len with
  | O => []
  | S len1 =>
      (∑ (j = 0, i),
       List.nth j al1 0 *
       (List.nth (i - j) al2 0 + List.nth (i - j) al3 0))%L ::
       lap_convol_mul_add_r al1 al2 al3 (S i) len1
  end.

Theorem lap_convol_mul_succ : ∀ la lb i len,
  lap_convol_mul la lb i (S len) =
  lap_convol_mul la lb i len ++
    [∑ (j = 0, i + len),
     List.nth j la 0 * List.nth (i + len - j) lb 0]%L.
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
  (∀ i, nth i lb 0%L = 0%L)
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

Theorem lap_convol_mul_more :
  rngl_has_opp_or_subt = true →
  ∀ n la lb i len,
  length la + length lb - 1 ≤ i + len
  → lap_norm (lap_convol_mul la lb i len) =
    lap_norm (lap_convol_mul la lb i (len + n)).
Proof.
intros Hos * Habl.
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
  apply (rngl_mul_0_l Hos).
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
rewrite fold_lap_add.
rewrite <- IHlb.
remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    apply (rngl_eqb_eq Heb) in Haz.
    subst a; rewrite rngl_add_0_l; cbn.
    rewrite app_nil_r, rngl_add_0_l, Nat.sub_0_r.
    rewrite map2_rngl_add_0_l.
    now rewrite strip_0s_app.
  }
  cbn.
  now rewrite strip_0s_app.
}
cbn.
rewrite rev_app_distr; cbn.
now rewrite strip_0s_app.
Qed.

Theorem list_nth_lap_add : ∀ k la lb,
  (List.nth k (lap_add la lb) 0 =
   List.nth k la 0 + List.nth k lb 0)%L.
Proof.
intros k la lb.
revert la lb.
induction k; intros. {
  destruct la as [| a]; cbn. {
    rewrite rngl_add_0_l, Nat.sub_0_r, app_nil_r.
    f_equal.
    apply map2_rngl_add_0_l.
  }
  destruct lb as [| b]; cbn; [ now rewrite rngl_add_0_r | ].
  easy.
} {
  destruct la as [| a]; cbn. {
    rewrite rngl_add_0_l, Nat.sub_0_r, app_nil_r.
    f_equal.
    apply map2_rngl_add_0_l.
  }
  destruct lb as [| b]; cbn. {
    rewrite app_nil_r, rngl_add_0_r.
    f_equal.
    apply map2_rngl_add_0_r.
  }
  apply IHk.
}
Qed.

Theorem lap_convol_mul_lap_add_r : ∀ la lb lc i len,
  lap_convol_mul la (lb + lc) i len = lap_convol_mul_add_r la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
apply rngl_summation_eq_compat; intros j (_, Hj).
f_equal.
now rewrite list_nth_lap_add.
Qed.

Theorem lap_add_lap_convol_mul_r : ∀ la lb lc i len,
  (lap_convol_mul la lb i len + lap_convol_mul la lc i len)%lap =
  lap_convol_mul_add_r la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ easy | cbn ].
rewrite <- IHlen; f_equal.
rewrite <- rngl_summation_add_distr.
apply rngl_summation_eq_compat; intros j (_, Hj).
now rewrite rngl_mul_add_distr_l.
Qed.

Theorem lap_norm_mul_add_distr_l :
  rngl_has_opp_or_subt = true →
  ∀ la lb lc, lap_norm (la * (lb + lc)) = lap_norm (la * lb + la * lc).
Proof.
intros Hos la lb lc.
unfold lap_mul.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ now do 2 rewrite lap_add_0_l | ].
destruct lc as [| c]. {
  cbn.
  rewrite rngl_add_0_r.
  do 2 rewrite app_nil_r.
  do 3 rewrite Nat.sub_0_r.
  now do 2 rewrite map2_rngl_add_0_r.
}
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
remember (length la' + length (lap_add lb' lc') - 1) as labc.
remember (length la' + length lb' - 1) as lab.
remember (length la' + length lc' - 1) as lac.
rewrite Heqlabc.
remember (lap_add lb' lc') as lbc.
symmetry in Heqlbc.
destruct lbc as [| bc]. {
  cbn.
  now subst lb' lc'.
}
rewrite <- Heqlbc in Heqlabc |-*.
rewrite (lap_convol_mul_more Hos) with (n := (lab + lac)%nat). 2: {
  subst; flia.
}
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite <- lap_add_norm_idemp_l.
rewrite (lap_convol_mul_more Hos) with (n := (labc + lac)%nat); [ | flia ].
rewrite <- Heqlab.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_comm.
rewrite <- lap_add_norm_idemp_l.
rewrite Heqlac.
rewrite (lap_convol_mul_more Hos) with (n := (labc + lab)%nat); [ | flia ].
rewrite lap_add_norm_idemp_l.
rewrite <- Heqlac.
rewrite Nat.add_comm.
rewrite lap_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite lap_convol_mul_lap_add_r.
now rewrite lap_add_lap_convol_mul_r.
Qed.

Theorem lap_mul_add_distr_l :
  rngl_has_opp_or_subt = true →
  ∀ la lb lc, (la * (lb + lc))%lap = (la * lb + la * lc)%lap.
Proof.
intros Hos la lb lc.
apply eq_lap_norm_eq_length. 2: {
  destruct la as [| a]; [ easy | ].
  destruct lb as [| b]. {
    rewrite lap_mul_0_r.
    now do 2 rewrite lap_add_0_l.
  }
  destruct lc as [| c]. {
    rewrite lap_mul_0_r.
    now do 2 rewrite lap_add_0_r.
  }
  cbn.
  do 3 (rewrite Nat.add_succ_r; cbn); f_equal.
  do 2 rewrite lap_convol_mul_length.
  do 2 rewrite map2_length.
  do 4 rewrite app_length.
  do 2 rewrite lap_convol_mul_length.
  do 4 rewrite repeat_length.
  do 2 rewrite min_add_sub_max.
  now rewrite Nat.add_max_distr_l.
}
apply (lap_norm_mul_add_distr_l Hos).
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
  ∀ la lb, (la * lb)%lap = (lb * la)%lap.
Proof.
intros Hic la lb.
unfold lap_mul.
destruct la as [| a]; [ now destruct lb | cbn ].
rewrite <- Nat.add_succ_comm; cbn.
rewrite (Nat.add_comm (length lb)).
now rewrite lap_convol_mul_comm.
Qed.

Theorem lap_opt_mul_comm :
  if rngl_mul_is_comm then ∀ a b : list T, (a * b)%lap = (b * a)%lap
  else not_applicable.
Proof.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply (lap_mul_comm Hic).
Qed.

(* multiplication with 1 *)

Theorem lap_opt_mul_1_r :
  rngl_has_opp_or_subt = true →
  if rngl_mul_is_comm then not_applicable else ∀ a, (a * 1)%lap = a.
Proof.
intros Hos.
destruct rngl_mul_is_comm; [ easy | ].
apply (lap_mul_1_r Hos).
Qed.

(* *)

Theorem lap_convol_mul_lap_add_l : ∀ la lb lc i len,
  lap_convol_mul (la + lb) lc i len = lap_convol_mul_add_l la lb lc i len.
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
induction len; intros; [ easy | cbn ].
rewrite <- IHlen; f_equal.
rewrite <- rngl_summation_add_distr.
apply rngl_summation_eq_compat; intros j (_, Hj).
now rewrite rngl_mul_add_distr_r.
Qed.

Theorem lap_norm_mul_add_distr_r :
  rngl_has_opp_or_subt = true →
  ∀ la lb lc : list T,
  lap_norm ((la + lb) * lc) = lap_norm (la * lc + lb * lc).
Proof.
intros Hos la lb lc.
unfold lap_mul.
destruct la as [| a]; [ now do 2 rewrite lap_add_0_l | ].
destruct lb as [| b]. {
  cbn.
  destruct lc as [| c]; [ easy | ].
  cbn; rewrite Nat.sub_0_r.
  rewrite rngl_add_0_r, app_nil_r, map2_length, repeat_length.
  rewrite Nat.min_id, Nat.sub_0_r, lap_add_0_r.
  now rewrite map2_rngl_add_0_r.
}
destruct lc as [| c]; [ easy | ].
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
remember (length (lap_add la' lb') + length lc' - 1) as labc.
remember (length la' + length lc' - 1) as lac.
remember (length lb' + length lc' - 1) as lbc.
rewrite Heqlabc.
remember (lap_add la' lb') as lab.
symmetry in Heqlab.
destruct lab as [| ab]; [ now subst la' lb' | ].
rewrite <- Heqlab in Heqlabc |-*.
rewrite (lap_convol_mul_more Hos) with (n := (lac + lbc)%nat). 2: {
  subst; flia.
}
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite <- lap_add_norm_idemp_l.
rewrite (lap_convol_mul_more Hos) with (n := (labc + lbc)%nat); [ | now subst lac ].
rewrite <- Heqlab.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_comm.
rewrite <- lap_add_norm_idemp_l.
rewrite Heqlbc.
rewrite (lap_convol_mul_more Hos) with (n := (labc + lac)%nat); [ | flia ].
rewrite lap_add_norm_idemp_l.
rewrite <- Heqlbc.
rewrite Nat.add_comm.
rewrite lap_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite lap_convol_mul_lap_add_l.
now rewrite lap_add_lap_convol_mul_l.
Qed.

Theorem lap_mul_add_distr_r :
  rngl_has_opp_or_subt = true →
  ∀ la lb lc, ((la + lb) * lc)%lap = (la * lc + lb * lc)%lap.
Proof.
intros Hos la lb lc.
apply eq_lap_norm_eq_length. 2: {
  destruct la as [| a]. {
    rewrite lap_mul_0_l.
    now do 2 rewrite lap_add_0_l.
  }
  destruct lb as [| b]. {
    rewrite lap_mul_0_l.
    now do 2 rewrite lap_add_0_r.
  }
  cbn.
  destruct lc as [| c]; [ easy | ].
  cbn; do 3 rewrite Nat.sub_0_r.
  do 3 (rewrite Nat.add_succ_r; cbn); f_equal.
  rewrite lap_convol_mul_length.
  do 2 rewrite map2_length.
  do 4 rewrite app_length, repeat_length.
  do 2 rewrite lap_convol_mul_length.
  do 2 rewrite min_add_sub_max.
  now rewrite Nat.add_max_distr_r.
}
apply (lap_norm_mul_add_distr_r Hos).
Qed.

Theorem lap_opt_mul_add_distr_r :
  rngl_has_opp_or_subt = true →
  if rngl_mul_is_comm then not_applicable
  else ∀ a b c, ((a + b) * c)%lap = (a * c + b * c)%lap.
Proof.
intros Hos.
destruct rngl_mul_is_comm; [ easy | ].
apply (lap_mul_add_distr_r Hos).
Qed.

(* *)

Theorem lap_opt_le_dec :
  let rol := lap_ring_like_op in
  if rngl_has_dec_le then ∀ a b, {(a ≤ b)%L} + {¬ (a ≤ b)%L}
  else not_applicable.
Proof.
intros rol; subst rol.
destruct rngl_has_dec_le; [ | easy ].
now intros; right; cbn.
Qed.

(* *)

Theorem last_lap_convol_mul_last :
  rngl_has_opp_or_subt = true →
  ∀ la lb a b i len d,
  len ≠ 0
  → length la + length lb + 1 = i + len
  → last (lap_convol_mul (la ++ [a]) (lb ++ [b]) i len) d = (a * b)%L.
Proof.
intros Hos * Hlen Hlab.
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

Theorem last_lap_mul :
  rngl_has_opp_or_subt = true →
  ∀ la lb, last (la * lb)%lap 0%L = (last la 0 * last lb 0)%L.
Proof.
intros Hos *.
unfold lap_mul.
destruct la as [| a] using rev_ind. {
  now symmetry; apply (rngl_mul_0_l Hos).
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
apply (last_lap_convol_mul_last Hos); flia.
Qed.

Theorem lap_opt_integral :
  rngl_has_opp_or_subt = true →
  let rol := lap_ring_like_op in
  if rngl_is_integral then
    ∀ a b, (a * b)%L = 0%L → a = 0%L ∨ b = 0%L
  else not_applicable.
Proof.
intros Hos rol; subst rol.
remember rngl_is_integral as it eqn:Hii; symmetry in Hii.
destruct it; [ | easy ].
intros la lb Hab.
cbn in Hab.
enough (H : la = [] ∨ lb = []). {
  destruct H as [H| Ha]; [ left; subst la | right; subst lb ].
  easy.
  easy.
}
destruct la as [| a] using rev_ind; [ now left | clear IHla ].
destruct lb as [| b] using rev_ind; [ now right | clear IHlb ].
specialize (last_lap_mul Hos (la ++ [a]) (lb ++ [b])) as H2.
do 2 rewrite last_last in H2.
rewrite Hab in H2.
symmetry in H2; cbn in H2.
apply (rngl_integral Hos) in H2; [ | now rewrite Hii ].
destruct H2 as [H2| H2]. {
  subst a.
  unfold lap_mul in Hab; cbn in Hab.
  destruct la as [| a']; [ now destruct lb | ].
  cbn in Hab.
  rewrite app_length, Nat.add_1_r in Hab; cbn in Hab.
  now destruct lb.
} {
  subst b.
  unfold lap_mul in Hab; cbn in Hab.
  destruct la as [| a']; [ now destruct lb | ].
  cbn in Hab.
  rewrite app_length, Nat.add_1_r in Hab; cbn in Hab.
  now destruct lb.
}
Qed.

(* *)

Theorem lap_characteristic_prop :
  let rol := lap_ring_like_op in
  if 0 =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
  else (∀ i : nat, 0 < i < 0 → rngl_of_nat i ≠ 0%L) ∧ rngl_of_nat 0 = 0%L.
Proof.
intros; subst rol.
cbn - [ rngl_of_nat ].
intros; cbn.
now destruct (rngl_of_nat i).
Qed.

(* *)

Theorem lap_opt_has_no_inv : ∀ P,
  let _ := lap_ring_like_op in
  if rngl_has_inv then P else not_applicable.
Proof.
intros.
unfold rngl_has_inv; cbn.
unfold lap_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool rngl_has_opp) as [Hop| Hop]; [ | easy ].
destruct (Sumbool.sumbool_of_bool rngl_has_inv); [ | easy ].
now destruct rngl_opt_inv_or_quot.
Qed.

Theorem lap_opt_has_no_inv_and : ∀ e P,
  let _ := lap_ring_like_op in
  if (rngl_has_inv && e)%bool then P else not_applicable.
Proof.
intros.
unfold rngl_has_inv; cbn.
unfold lap_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool rngl_has_opp); [ | easy ].
destruct (Sumbool.sumbool_of_bool rngl_has_inv); [ | easy ].
now destruct rngl_opt_inv_or_quot.
Qed.

(* *)

Theorem map2_rngl_subt_diag :
  rngl_has_opp_or_subt = true →
  ∀ la, map2 rngl_subt la la = repeat 0%L (length la).
Proof.
intros Hos *.
induction la as [| a]; [ easy | cbn ].
f_equal; [ | apply IHla ].
now apply rngl_subt_diag.
Qed.

Theorem lap_opt_add_sub :
  rngl_has_subt = true →
  ∀ la lb : list T,
  (la + lb - lb)%lap = la ++ repeat 0%L (length lb - length la).
Proof.
intros Hsu *.
remember rngl_has_opp as op eqn:Hop.
symmetry in Hop.
destruct op. {
  move Hsu at bottom.
  unfold rngl_has_opp in Hop.
  unfold rngl_has_subt in Hsu.
  destruct rngl_opt_opp_or_subt; [ now destruct s | easy ].
}
move Hop after Hsu.
assert (Hos : rngl_has_opp_or_subt = true). {
  now apply rngl_has_opp_or_subt_iff; right.
}
move Hos after Heb.
unfold lap_sub.
rewrite Hop, Hsu.
unfold lap_add, lap_subt.
rewrite map2_length.
do 2 rewrite app_length, repeat_length.
rewrite min_add_sub_max.
rewrite <- Nat.sub_min_distr_l.
rewrite Nat.sub_diag, Nat.min_0_r.
rewrite <- Nat.sub_max_distr_r.
rewrite Nat.sub_diag, Nat.max_0_r.
destruct (le_dec (length la) (length lb)) as [Hab| Hab]. {
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  do 2 rewrite app_nil_r.
  revert lb Hab.
  induction la as [| a]; intros; cbn. {
    rewrite Nat.sub_0_r.
    rewrite map2_rngl_add_0_l.
    now apply map2_rngl_subt_diag.
  }
  destruct lb as [| b]; [ easy | cbn ].
  cbn in Hab.
  apply Nat.succ_le_mono in Hab.
  f_equal; [ | now apply IHla ].
  specialize (rngl_add_sub Hos) as H1.
  unfold rngl_sub in H1.
  rewrite Hop, Hsu in H1.
  apply H1.
} {
  apply Nat.nle_gt, Nat.lt_le_incl in Hab.
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  do 2 rewrite app_nil_r.
  revert lb Hab.
  induction la as [| a]; intros; [ easy | cbn ].
  destruct lb as [| b]; cbn. {
    rewrite rngl_add_0_r.
    rewrite (rngl_subt_0_r Hsu); f_equal.
    rewrite map2_rngl_add_0_r.
    apply (map2_rngl_subt_0_r Hsu).
  }
  cbn in Hab.
  apply Nat.succ_le_mono in Hab.
  f_equal; [ | now apply IHla ].
  specialize (rngl_add_sub Hos) as H1.
  unfold rngl_sub in H1.
  rewrite Hop, Hsu in H1.
  apply H1.
}
Qed.

Theorem lap_opt_sub_add_distr :
  rngl_has_subt = true →
  ∀ la lb lc : list T, (la - (lb + lc))%lap = (la - lb - lc)%lap.
Proof.
intros Hsu *.
remember rngl_has_opp as op eqn:Hop.
symmetry in Hop.
destruct op. {
  move Hsu at bottom.
  unfold rngl_has_opp in Hop.
  unfold rngl_has_subt in Hsu.
  destruct rngl_opt_opp_or_subt; [ now destruct s | easy ].
}
move Hop after Hsu.
assert (Hos : rngl_has_opp_or_subt = true). {
  now apply rngl_has_opp_or_subt_iff; right.
}
move Hos after Heb.
unfold lap_sub.
rewrite Hop, Hsu.
unfold lap_add, lap_subt.
do 2 rewrite map2_length.
do 4 rewrite app_length, repeat_length.
do 2 rewrite min_add_sub_max.
do 2 rewrite <- Nat.sub_min_distr_l.
do 2 rewrite <- Nat.sub_max_distr_r.
destruct (le_dec (length la) (length lb)) as [Hab| Hab]. {
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  do 2 rewrite app_nil_r.
  destruct (le_dec (length lb) (length lc)) as [Hbc| Hbc]. {
    rewrite (proj2 (Nat.sub_0_le _ _) Hbc); cbn.
    rewrite app_nil_r.
    assert (Hac : length la ≤ length lc) by now transitivity (length lb).
    rewrite (proj2 (Nat.sub_0_le _ _) Hac); cbn.
    rewrite app_nil_r.
...

(* lap ring-like properties *)

Definition lap_ring_like_prop (Hos : rngl_has_opp_or_subt = true) :
    ring_like_prop (list T) :=
  let rol := lap_ring_like_op in
  {| rngl_mul_is_comm := rngl_mul_is_comm;
     rngl_has_dec_le := rngl_has_dec_le;
     rngl_is_integral := rngl_is_integral;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := lap_add_comm;
     rngl_add_assoc := lap_add_assoc;
     rngl_add_0_l := lap_add_0_l;
     rngl_mul_assoc := lap_mul_assoc Hos;
     rngl_mul_1_l := lap_mul_1_l Hos;
     rngl_mul_add_distr_l := lap_mul_add_distr_l Hos;
     rngl_opt_mul_comm := lap_opt_mul_comm;
     rngl_opt_mul_1_r := lap_opt_mul_1_r Hos;
     rngl_opt_mul_add_distr_r := lap_opt_mul_add_distr_r Hos;
     rngl_opt_add_opp_l := NA;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := lap_opt_has_no_inv False;
     rngl_opt_mul_inv_r := lap_opt_has_no_inv_and false False;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eqb_eq := NA;
     rngl_opt_le_dec := lap_opt_le_dec;
     rngl_opt_integral := lap_opt_integral Hos;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := lap_characteristic_prop;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA |}.

(* roots *)

Theorem eval_lap_is_rngl_eval_polyn :
  ∀ la x, eval_lap la x = rngl_eval_polyn la x.
Proof.
intros.
unfold eval_lap, eval_rlap, rlap_horner, iter_list.
induction la as [| a]; [ easy | cbn ].
rewrite fold_left_app; cbn.
now rewrite IHla.
Qed.

End a.

Arguments eq_lap_norm_eq_length {T ro rp} Heb (la lb)%lap.
Arguments lap_add_assoc {T ro rp} (al1 al2 al3)%lap.
Arguments lap_add_comm {T ro rp} (al1 al2)%lap.
Arguments lap_add_length {T ro} (la lb)%lap.
Arguments lap_add_norm_idemp_l {T ro rp} Heb (la lb)%lap.
Arguments lap_add_0_l {T ro rp} la%lap.
Arguments lap_add_0_r {T ro rp} la%lap.
Arguments lap_convol_mul_const_l {T ro rp} Hos a%L la%lap (i len)%nat.
Arguments lap_convol_mul_const_r {T ro rp} Hos a%L la%lap (i len)%nat.
Arguments lap_convol_mul_more {T ro rp} Heb Hos n%nat (la lb)%lap (i len)%nat.
Arguments lap_convol_mul_add_l {T ro} (al1 al2 al3)%lap (i len)%nat.
Arguments lap_mul_add_distr_l {T ro rp} Heb Hos (la lb lc)%lap.
Arguments lap_mul_assoc {T ro rp} Heb Hos (la lb lc)%lap.
Arguments lap_mul_comm {T ro rp} Hic (la lb)%lap.
Arguments lap_mul_const_l {T ro rp} Hos a la%lap.
Arguments lap_mul_const_r {T ro rp} Hos a la%lap.
Arguments lap_mul_1_l {T ro rp} Hos la%lap.
Arguments lap_mul_1_r {T ro rp} Hos la%lap.
Arguments lap_norm_app_0_r {T ro rp} Heb (la lb)%lap.
Arguments lap_opt_add_sub {T ro rp} Hsu (la lb)%lap.
Arguments lap_quot_rem {T ro} (la lb)%lap.
Arguments last_lap_mul {T ro rp} Hos (la lb)%lap.
Arguments list_nth_lap_add {T ro rp} k%nat (la lb)%lap.
Arguments list_nth_lap_eq {T ro rp} Heb (la lb)%lap.
Arguments map2_rngl_add_0_l {T ro rp} la%lap.
Arguments map2_rngl_add_0_r {T ro rp} la%lap.
Arguments map2_rngl_subt_0_r {T ro rp} Hsu la%lap.
Arguments rlap_quot_rem {T ro} (rla rlb)%list.
Arguments strip_0s_length_le {T ro} l%list.

