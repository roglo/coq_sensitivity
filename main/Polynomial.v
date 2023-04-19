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

Definition is_empty_list {A} (la : list A) :=
  match la with [] => true | _ => false end.
Definition has_polyn_prop T {ro : ring_like_op T} (la : list T) :=
  (is_empty_list la || (last la 0 ≠? 0)%L)%bool.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
Context {Hos : rngl_has_opp_or_subt = true}.
Context {Heb : rngl_has_eqb = true}.

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

(*
End a.
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.
Compute (lap_eqb 0%Q Q.eqb [1;0;0;0] [1;0;3]).
*)

Definition lap_one := [1%L].

(* normalization *)

Fixpoint strip_0s la :=
  match la with
  | [] => []
  | a :: la' => if (a =? 0)%L then strip_0s la' else la
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
destruct (a =? 0)%L; [ apply IHla | easy ].
Qed.

Theorem eq_strip_0s_nil : ∀ la,
  strip_0s la = [] ↔ ∀ i, nth i la 0%L = 0%L.
Proof.
intros.
split. {
  intros Hla *.
  revert i.
  induction la as [| a]; intros; [ now destruct i | cbn ].
  cbn in Hla.
  rewrite if_bool_if_dec in Hla.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ | easy ].
  apply (rngl_eqb_eq Heb) in Haz.
  destruct i; [ easy | ].
  now apply IHla.
} {
  intros Hla.
  induction la as [| a]; [ easy | cbn ].
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    apply IHla.
    intros i.
    now specialize (Hla (S i)).
  }
  apply (rngl_eqb_neq Heb) in Haz.
  now specialize (Hla 0).
}
Qed.

Theorem eq_strip_0s_cons : ∀ la lb b,
  strip_0s la = b :: lb → b ≠ 0%L.
Proof.
intros * Hab.
intros H; subst b.
induction la as [| a]; [ easy | cbn in Hab ].
rewrite if_bool_if_dec in Hab.
destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ congruence | ].
injection Hab; clear Hab; intros Hab Ha; subst a.
now rewrite (rngl_eqb_refl Heb) in Haz.
Qed.

Definition lap_norm la := rev (strip_0s (rev la)).

Theorem is_empty_list_empty : ∀ A (la : list A),
  is_empty_list la = true → la = [].
Proof.
intros * Ha.
unfold is_empty_list in Ha.
now destruct la.
Qed.

Theorem polyn_norm_prop : ∀ la, has_polyn_prop (lap_norm la) = true.
Proof.
intros.
unfold has_polyn_prop, lap_norm.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; cbn. {
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ easy | cbn ].
  now apply Bool.negb_true_iff.
}
cbn in IHla.
rewrite last_last in IHla.
apply Bool.orb_true_iff in IHla.
apply Bool.orb_true_iff; right.
rewrite last_last.
destruct IHla as [H1| H1]; [ | easy ].
apply is_empty_list_empty in H1.
now apply app_eq_nil in H1.
Qed.

(* addition *)

Fixpoint lap_add la lb :=
  match la with
  | [] => lb
  | a1 :: bl1 =>
      match lb with
      | [] => la
      | a2 :: bl2 => (a1 + a2)%L :: lap_add bl1 bl2
      end
  end.

Fixpoint lap_subt la lb :=
  match la with
  | [] => [] (* x-x²=x the same way 1-2=0 in nat *)
  | a1 :: bl1 =>
      match lb with
      | [] => la
      | a2 :: bl2 => (a1 - a2)%L :: lap_subt bl1 bl2
      end
  end.

Definition lap_opp la := map rngl_opp la.
Definition lap_sub la lb :=
  if rngl_has_opp then lap_add la (lap_opp lb)
  else if rngl_has_subt then lap_subt la lb
  else [].

Theorem fold_lap_opp : ∀ la, map rngl_opp la = lap_opp la.
Proof. easy. Qed.

(*
Theorem fold_lap_sub : ∀ la lb, lap_add la (lap_opp lb) = lap_sub la lb.
Proof. easy. Qed.
*)

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

Theorem lap_subt_length : ∀ la lb, length (lap_subt la lb) = length la.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal; apply IHla.
Qed.

Theorem lap_sub_length : ∀ la lb,
  length (lap_sub la lb) =
    if rngl_has_opp then max (length la) (length lb)
    else if rngl_has_subt then length la
    else 0.
Proof.
intros.
unfold lap_sub.
destruct rngl_has_opp. {
  revert lb.
  induction la as [| a]; intros; [ apply lap_opp_length | cbn ].
  destruct lb as [| b]; [ easy | cbn ].
  f_equal; apply IHla.
}
destruct rngl_has_subt; [ apply lap_subt_length | easy ].
Qed.

Theorem all_0_lap_norm_nil : ∀ la,
  (∀ i, nth i la 0%L = 0%L)
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
    destruct (Sumbool.sumbool_of_bool _) as [H1| H1]; [ easy | exfalso ].
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
  la = lap_norm la ++ repeat 0%L (length la - length (lap_norm la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
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
remember rngl_has_opp as op eqn:Hop; symmetry in Hop.
destruct op; [ now rewrite Nat.max_l | ].
remember rngl_has_subt as su eqn:Hsu; symmetry in Hsu.
destruct su; [ easy | ].
apply rngl_has_opp_or_subt_iff in Hos.
destruct Hos; congruence.
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
  ∀ la lb lq lr : list T,
  lb ≠ []
  → has_polyn_prop lb = true
  → lap_quot_rem la lb = (lq, lr)
  → length lr < length lb.
Proof.
intros * Hbz Hbn Hab.
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
  la = [] ∨ hd 0%L la ≠ 0%L
  → lb = [] ∨ hd 0%L lb ≠ 0%L
  → rlap_quot_rem la lb = (lq, lr)
  → lq = [] ∨ hd 0%L lq ≠ 0%L.
Proof.
intros Hiv * Ha Hb Hab.
destruct (Nat.eq_dec rngl_characteristic 1) as [Hch| Hch]. {
  specialize (rngl_characteristic_1 Hos Hch) as H1.
  destruct lq as [| q]; [ now left | right; cbn ].
  destruct Hb as [Hb| Hb]; [ now subst lb | ].
  destruct lb as [| b]; [ easy | cbn in Hb ].
  now specialize (H1 b).
}
move Hch before Hiv.
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
apply (rngl_eq_mul_0_l Hos) in Hq; [ easy | | ]. {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_or_quot_iff; left.
}
apply rngl_inv_neq_0; [ easy | easy | easy ].
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
destruct (Sumbool.sumbool_of_bool _) as [Hrz| Hrz]. {
  rewrite List_last_rev.
  remember (strip_0s rlr) as rl eqn:Hrl;symmetry in Hrl.
  destruct rl as [| a]; [ now left | right; cbn ].
  apply eq_strip_0s_cons in Hrl.
  now apply (rngl_neqb_neq Heb).
}
right; cbn; rewrite last_last.
now rewrite Hrz.
Qed.

(* lap opposite or subtraction *)

Definition lap_opt_opp_or_subt :
  option ((list T → list T) + (list T → list T → list T)) :=
  match rngl_opt_opp_or_subt with
  | Some (inl _) => Some (inl lap_opp)
  | Some (inr _) => Some (inr lap_subt)
  | None => None
  end.

(* lap quotient *)

Definition lap_opt_inv_or_quot :
  option ((list T → list T) + (list T → list T → list T)) :=
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

(* ring-like operators *)

Definition lap_ring_like_op : ring_like_op (list T) :=
  {| rngl_zero := [];
     rngl_one := lap_one;
     rngl_add := lap_add;
     rngl_mul := lap_mul;
     rngl_opt_opp_or_subt := lap_opt_opp_or_subt;
     rngl_opt_inv_or_quot := lap_opt_inv_or_quot;
     rngl_opt_eqb := Some (lap_eqb rngl_zero rngl_eqb);
     rngl_opt_le := None |}.

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.

Arguments lap_add (la lb)%lap.
Arguments lap_mul (la lb)%lap.
Arguments lap_quot_rem (la lb)%lap.
Arguments lap_quot (la lb)%lap.
Arguments lap_rem (la lb)%lap.

Notation "1" := lap_one : lap_scope.
Notation "- a" := (lap_opp a) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
Notation "a / b" := (lap_quot a b) : lap_scope.
Notation "a 'mod' b" := (lap_rem a b) : lap_scope.

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

(* associativity of addition *)

Theorem strip_0s_idemp : ∀ la, strip_0s (strip_0s la) = strip_0s la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ easy | cbn ].
now rewrite Haz.
Qed.

Theorem lap_norm_idemp : ∀ la, lap_norm (lap_norm la) = lap_norm la.
Proof.
intros.
unfold lap_norm.
rewrite rev_involutive.
now rewrite strip_0s_idemp.
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
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
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

(* addition to 0 *)

Theorem has_polyn_prop_lap_norm : ∀ la,
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

(* associativity of multiplication *)

Theorem lap_convol_mul_0_l : ∀ la lb i len,
  (∀ i, nth i la 0%L = 0%L)
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
  (∀ i, nth i lb 0%L = 0%L)
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
  (∀ i, nth i la 0%L = 0%L)
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
  lap_norm (lap_convol_mul (la ++ repeat 0%L n) lb i len) =
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
  lap_norm (lap_convol_mul la (lb ++ repeat 0%L n) i len) =
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
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
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
  (∀ i, nth i la 0%L = 0%L)
  ↔ (∀ i, nth i (rev la) 0%L = 0%L).
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
  strip_0s (rev la) = [] ↔ ∀ i, nth i la 0%L = 0%L.
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

Theorem list_nth_lap_convol_mul_aux : ∀ la lb n i len,
  List.length la + List.length lb - 1 = (i + len)%nat
  → (List.nth n (lap_convol_mul la lb i len) 0%L =
     ∑ (j = 0, n + i),
     List.nth j la 0 * List.nth (n + i - j) lb 0)%L.
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
     ∑ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%L.
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
      ∑ (j = 0, i), nth j la 0 * nth (i - j) lb 0)%L.
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

Theorem lap_convol_mul_const_l : ∀ a la i len,
  length la = i + len
  → lap_convol_mul [a] la i len =
    map (λ b, (a * b)%L) (skipn i la).
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
rewrite (List_skipn_is_cons 0%L); [ easy | flia Hlen ].
Qed.

Theorem lap_convol_mul_const_r : ∀ a la i len,
  length la = i + len
  → lap_convol_mul la [a] i len =
    map (λ b, (b * a)%L) (skipn i la).
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
rewrite (List_skipn_is_cons 0%L); [ easy | flia Hlen ].
Qed.

Theorem lap_convol_mul_1_l : ∀ la i len,
  length la = i + len
  → lap_convol_mul [1%L] la i len = skipn i la.
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
  → lap_convol_mul la [1%L] i len = skipn i la.
Proof.
intros * Hlen.
rewrite lap_convol_mul_const_r; [ | easy ].
erewrite map_ext_in. 2: {
  intros a Ha.
  now rewrite rngl_mul_1_r.
}
apply map_id.
Qed.

Theorem lap_add_const_l : ∀ a la, ([a] + la)%lap = (a + hd 0 la)%L :: tl la.
Proof.
intros.
destruct la as [| b]; cbn; f_equal; symmetry; apply rngl_add_0_r.
Qed.

Theorem lap_add_const_r : ∀ a la, (la + [a])%lap = (hd 0 la + a)%L :: tl la.
Proof.
intros.
destruct la as [| b]; cbn; f_equal; [ symmetry; apply rngl_add_0_l | ].
apply lap_add_0_r.
Qed.

Theorem lap_mul_const_l : ∀ a la, ([a] * la)%lap = map (λ b, (a * b)%L) la.
Proof.
intros.
unfold lap_mul.
destruct la as [| b]; [ easy | ].
now rewrite lap_convol_mul_const_l.
Qed.

Theorem lap_mul_const_r : ∀ a la, (la * [a])%lap = map (λ b, (b * a)%L) la.
Proof.
intros.
unfold lap_mul.
destruct la as [| b]; [ easy | ].
rewrite Nat.add_sub.
now rewrite lap_convol_mul_const_r.
Qed.

Theorem lap_mul_1_l : ∀ la, (1 * la)%lap = la.
Proof.
intros.
unfold lap_one.
rewrite lap_mul_const_l.
induction la as [| a]; [ easy | cbn ].
rewrite rngl_mul_1_l; f_equal.
apply IHla.
Qed.

Theorem lap_mul_1_r : ∀ la, (la * 1)%lap = la.
Proof.
intros.
unfold lap_one.
rewrite lap_mul_const_r; cbn.
induction la as [| a]; [ easy | cbn ].
rewrite rngl_mul_1_r; f_equal.
apply IHla.
Qed.

Theorem lap_opt_mul_1_r :
  if rngl_mul_is_comm then not_applicable else ∀ a, (a * 1)%lap = a.
Proof.
destruct rngl_mul_is_comm; [ easy | ].
apply lap_mul_1_r.
Qed.

Theorem lap_convol_mul_x_l :
  ∀ la lb i len,
  i = S (length la)
  → len = length lb
  → lap_convol_mul [0%L; 1%L] (la ++ lb) i len = lb.
Proof.
intros * Hi Hlen.
revert la lb i Hi Hlen.
induction len; intros. {
  now symmetry in Hlen; apply length_zero_iff_nil in Hlen.
}
cbn.
destruct lb as [| b]; [ easy | ].
cbn in Hlen.
apply Nat.succ_inj in Hlen.
f_equal. {
  rewrite (rngl_summation_split3 1); [ | flia Hi ].
  rewrite rngl_summation_only_one.
  rewrite Nat.sub_diag, (rngl_mul_0_l Hos).
  rewrite rngl_add_0_l, rngl_mul_1_l.
  rewrite Hi, Nat_sub_succ_1.
  rewrite app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag.
  rewrite List_nth_0_cons.
  rewrite all_0_rngl_summation_0; [ apply rngl_add_0_r | ].
  intros j Hj.
  destruct j; [ flia Hj | ].
  destruct j; [ flia Hj | ].
  rewrite Tauto_match_nat_same.
  apply (rngl_mul_0_l Hos).
}
rewrite (List_cons_is_app b).
rewrite app_assoc.
apply IHlen; [ | easy ].
rewrite app_length, Nat.add_1_r.
now f_equal.
Qed.

Theorem lap_mul_x_l :
  ∀ la, la ≠ [] → ([0; 1]%L * la)%lap = 0%L :: la.
Proof.
intros * Hla; cbn.
destruct la as [| a]; [ easy | clear Hla ].
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos).
f_equal; cbn.
unfold iter_seq, iter_list; cbn.
rewrite rngl_add_0_l, (rngl_mul_0_l Hos).
rewrite rngl_add_0_l, rngl_mul_1_l.
f_equal.
rewrite (List_cons_is_app a).
now apply lap_convol_mul_x_l.
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

Theorem list_nth_lap_add : ∀ k la lb,
  (List.nth k (lap_add la lb) 0 =
   List.nth k la 0 + List.nth k lb 0)%L.
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
  ∀ k la, (List.nth k (lap_opp la) 0 = - List.nth k la 0)%L.
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
   List.nth k la 0 - List.nth k lb 0)%L.
Proof.
intros Hop *.
unfold lap_sub.
rewrite Hop.
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
remember 0 as i in |-*; clear Heqi.
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
  now rewrite (List_map_nth' 0%L).
}
rewrite <- (rngl_mul_opp_r Hop); f_equal.
destruct (i - S j) as [| k]; [ easy | ].
destruct (lt_dec k (length lb)) as [Hklb| Hklb]. 2: {
  apply Nat.nlt_ge in Hklb.
  rewrite nth_overflow; [ | now rewrite map_length ].
  rewrite nth_overflow; [ | easy ].
  symmetry; apply (rngl_opp_0 Hop).
}
now rewrite (List_map_nth' 0%L).
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
rewrite Hop.
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

Theorem lap_opt_mul_add_distr_r :
   if rngl_mul_is_comm then not_applicable
   else ∀ a b c : list T, ((a + b) * c)%lap = (a * c + b * c)%lap.
Proof.
destruct rngl_mul_is_comm; [ easy | ].
apply lap_mul_add_distr_r.
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

Theorem lap_opt_mul_comm :
  if rngl_mul_is_comm then ∀ a b : list T, (a * b)%lap = (b * a)%lap
  else not_applicable.
Proof.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply (lap_mul_comm Hic).
Qed.

(* optional left addition of opposite; not existing if there is
   no opposite *)

Theorem lap_add_opp_l :
  rngl_has_opp = true
  → ∀ la, (- la + la)%lap = repeat 0%L (length la).
Proof.
intros Hop *.
induction la as [| a]; [ easy | cbn ].
rewrite (rngl_add_opp_l Hop).
now f_equal.
Qed.

Theorem lap_add_opp_r :
  rngl_has_opp = true
  → ∀ la, (la + - la)%lap = repeat 0%L (length la).
Proof.
intros Hop *.
clear Hos.
induction la as [| a]; [ easy | cbn ].
rewrite fold_lap_opp.
rewrite fold_rngl_sub; [ | easy ].
rewrite rngl_sub_diag; [ | now apply rngl_has_opp_has_opp_or_subt ].
now f_equal.
Qed.

Theorem lap_norm_repeat_0 : ∀ n, lap_norm (repeat 0%L n) = [].
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

(*
Theorem lap_opt_add_opp_l :
  let rol := lap_ring_like_op in
  if rngl_has_opp then ∀ a : list T, (- a + a)%L = 0%L else not_applicable.
Proof.
intros rol; subst rol.
remember rngl_has_opp as op eqn:Hop; symmetry in Hop.
intros.
destruct op; [ | easy ].
intros la.
unfold rngl_opp; cbn.
unfold lap_opt_opp_or_subt.
specialize lap_add_opp_l as add_opp_l.
unfold rngl_has_opp in Hop, add_opp_l.
cbn in Hop, add_opp_l.
unfold lap_opt_opp_or_subt in Hop, add_opp_l.
destruct rngl_opt_opp_or_subt as [opp| ]; [ | easy ].
destruct opp as [opp| ]; [ | easy ].
rewrite add_opp_l; [ | easy ].
(* question of equality *)
...
  ============================
  repeat 0%L (length la) = []
Qed.
*)

(* *)

(*
Theorem lap_opt_has_no_subt : ∀ P,
  let _ := lap_ring_like_op in
  if rngl_has_subt then P else not_applicable.
Proof.
intros.
unfold rngl_has_subt; cbn.
unfold rngl_has_opp_or_subt in Hos.
unfold lap_opt_opp_or_subt.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ easy | ].
...
intros.
unfold rngl_has_subt; cbn.
unfold lap_opt_opp_or_subt.
destruct rngl_opt_opp_or_subt as [opp| ]; [ | easy ].
now destruct opp.
Qed.
*)

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

Theorem map_opp_repeat : ∀ (x : T) n,
  map rngl_opp (repeat x n) = repeat (rngl_opp x) n.
Proof.
intros.
induction n; [ easy | cbn ].
f_equal; apply IHn.
Qed.

Theorem lap_convol_mul_l_succ_l : ∀ la lb i len,
  lap_convol_mul (0%L :: la) lb (S i) len =
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
  lap_convol_mul la (0%L :: lb) (S i) len =
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

Definition lap_x_power n := repeat 0%L n ++ [1%L].

Theorem lap_repeat_0_app_is_mul_power_l : ∀ n la,
  la ≠ []
  → repeat 0%L n ++ la = (lap_x_power n * la)%lap.
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
  → repeat 0%L n ++ la = (la * lap_x_power n)%lap.
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

Theorem rev_lap_opp : ∀ la, (rev (- la) = - rev la)%lap.
Proof.
intros.
unfold lap_opp.
now rewrite map_rev.
Qed.

Theorem lap_add_repeat_0_l : ∀ la len,
  len ≤ length la
  → (repeat 0%L len + la = la)%lap.
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
  → (la + repeat 0%L len = la)%lap.
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
destruct rngl_has_opp. {
  rewrite rev_lap_add; [ | now rewrite lap_opp_length ].
  now rewrite rev_lap_opp.
}
destruct rngl_has_subt; [ | easy ].
revert lb Hab.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
cbn in Hab; apply Nat.succ_inj in Hab.
rewrite IHla; [ | easy ].
clear IHla.
rewrite <- (rev_length la) in Hab.
rewrite <- (rev_length lb) in Hab.
remember (rev la) as lc.
remember (rev lb) as ld.
clear la lb Heqlc Heqld.
rename lc into la; rename ld into lb.
revert lb Hab.
induction la as [| a']; intros; cbn. {
  now symmetry in Hab; apply length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b']; [ easy | cbn ].
cbn in Hab; apply Nat.succ_inj in Hab.
now f_equal; apply IHla.
Qed.

Theorem lap_add_norm : ∀ la lb,
  (la + lb)%lap =
    ((la ++ repeat 0%L (length lb - length la)) +
     (lb ++ repeat 0%L (length la - length lb)))%lap.
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
    ((repeat 0%L (length lb - length la) ++ rev la) +
     (repeat 0%L (length la - length lb) ++ rev lb))%lap.
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
    ((repeat 0%L (length lb - length la) ++ rev la) -
     (repeat 0%L (length la - length lb) ++ rev lb))%lap.
Proof.
intros Hop *.
unfold lap_sub.
rewrite Hop.
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
rewrite Hop.
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

Theorem rlap_quot_rem_step_Some :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  ∀ rla rlb rlr cq,
  hd 0%L rlb ≠ 0%L
  → rlap_quot_rem_step rla rlb = (Some cq, rlr)
  → rev rla =
      (rev rlb * rev (cq :: repeat 0%L (length rla - length rlb)) +
       rev rlr)%lap ∧
    length rla = S (length rlr) ∧
    cq = (hd 0 rla / hd 0 rlb)%L.
Proof.
intros Hic Hop Hiv * Hbz Hrl.
destruct rlb as [| b]; [ easy | cbn in Hbz, Hrl ].
destruct rla as [| a]; [ easy | ].
rewrite if_bool_if_dec in Hrl.
destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]; [ easy | ].
apply Nat.ltb_ge in Hab.
injection Hrl; clear Hrl; intros H1 H2; subst cq rlr.
remember (a / b)%L as cq eqn:Hcq.
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
replace (b * cq)%L with (b * (a / b))%L by now rewrite Hcq.
rewrite (rngl_mul_div_r Hic Hiv _ _ Hbz).
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
rewrite (proj2 (Nat.sub_0_le _ _)); [ cbn | easy ].
assert (Hca : length rlc = length rla). {
  rewrite Hrlc, app_length, map_length, repeat_length.
  now rewrite Nat.add_comm, Nat.sub_add.
}
rewrite <- rev_lap_sub; [ | easy ].
rewrite lap_add_app_l. 2: {
  do 2 rewrite rev_length.
  rewrite lap_sub_length.
  rewrite Hop.
  now rewrite Hca, Nat.max_id.
}
rewrite lap_sub_length, map_length.
rewrite Hop.
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
rewrite Hop in Hrlac.
destruct rlac as [| ac]; intros. {
  apply length_zero_iff_nil in Hrlac; subst rlc; cbn.
  rewrite lap_add_0_l in Hab.
  now apply Nat.le_0_r, length_zero_iff_nil in Hab; subst rlb.
}
now rewrite rev_lap_add.
Qed.

Theorem rlap_quot_rem_length :
  ∀ it (rla rlb rlq rlr : list T),
  hd 0%L rlb ≠ 0%L
  → rlap_quot_rem_loop it rla rlb = (rlq, rlr)
  → S (length rla) ≤ it
  → length rlq = length rla - (length rlb - 1).
Proof.
intros * Hbn Hqr Hit.
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
  hd 0%L rlb ≠ 0%L
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
apply (rlap_quot_rem_length _ _ Hbn) in Hqrb; [ | flia Hra Hit ].
apply IHit in Hqr. 2: {
  etransitivity; [ | apply Hit ].
  apply lt_le_S.
  destruct rlb as [| b]; [ easy | ].
  cbn in Hqrlr.
  destruct rla as [| a]; [ easy | ].
  rewrite if_bool_if_dec in Hqrlr.
  destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]; [ easy | ].
  apply Nat.ltb_ge in Hab.
  injection Hqrlr; clear Hqrlr; intros; subst cq rlr.
  rewrite lap_sub_length.
  rewrite Hop.
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
  destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
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

Theorem lap_quot_rem_prop :
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  ∀ la lb lq lr : list T,
  has_polyn_prop la = true
  → last lb 0%L ≠ 0%L
  → has_polyn_prop lr = true
  → lap_quot_rem la lb = (lq, lr)
  → la = (lb * lq + lr)%lap ∧
    length lr < length lb ∧
    has_polyn_prop lq = true.
Proof.
intros Hco Hop Hiv * Ha Hb Hr Hab.
clear Hos.
assert (Hos : rngl_has_opp_or_subt = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (Hrb : length lr < length lb). {
  eapply lap_rem_length_lt; [ | | apply Hab ]. {
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
assert (Hbz : hd 0%L (rev lb) ≠ 0%L). {
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
  destruct (Sumbool.sumbool_of_bool _) as [Hrz| Hrz]; [ | easy ].
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

Theorem lap_subt_diag :
  ∀ la, lap_subt la la = repeat 0%L (length la).
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
rewrite (rngl_sub_diag Hos).
now f_equal.
Qed.

Theorem lap_add_sub :
  ∀ la lb, (la + lb - lb)%lap = la ++ repeat 0%L (length lb - length la).
Proof.
intros.
unfold lap_sub.
remember rngl_has_opp as op eqn:Hop; symmetry in Hop.
destruct op. {
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
}
remember rngl_has_subt as su eqn:Hsu; symmetry in Hsu.
destruct su. {
  revert lb.
  induction la as [| a]; intros; cbn. {
    rewrite Nat.sub_0_r.
    apply lap_subt_diag.
  }
  destruct lb as [| b]; cbn; [ now rewrite app_nil_r | ].
  rewrite (rngl_add_sub Hos); f_equal.
  apply IHla.
}
apply rngl_has_opp_or_subt_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem last_lap_convol_mul_last : ∀ la lb a b i len d,
  len ≠ 0
  → length la + length lb + 1 = i + len
  → last (lap_convol_mul (la ++ [a]) (lb ++ [b]) i len) d = (a * b)%L.
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
  last (la * lb)%lap 0%L = (last la 0%L * last lb 0%L)%L.
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
  ∀ la lb lc : list T,
  (la + lb)%lap = lc
  → lb ++ repeat 0%L (length la - length lb) = (lc - la)%lap.
Proof.
intros * Hab.
subst lc.
symmetry; rewrite lap_add_comm.
now rewrite lap_add_sub.
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
apply (rngl_eq_mul_0_r Hos) in Hab; [ easy | |  easy].
apply Bool.orb_true_iff; right.
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
apply has_polyn_prop_lap_norm.
now apply lap_mul_has_polyn_prop.
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
assert (H : last lb 0%L ≠ 0%L). {
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
apply lap_add_move_l in Hab1.
symmetry in Hab1.
rewrite (lap_mul_comm Hco) in Hab1.
rewrite <- (lap_mul_sub_distr_l Hop) in Hab1.
apply (f_equal lap_norm) in Hab1.
rewrite <- lap_norm_app_0_r in Hab1 by apply nth_repeat.
rewrite (has_polyn_prop_lap_norm lr pr) in Hab1.
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
rewrite <- (has_polyn_prop_lap_norm la pa).
rewrite <- (has_polyn_prop_lap_norm lq pq).
apply list_nth_lap_eq.
intros i.
specialize (H1 i).
rewrite (list_nth_lap_sub Hop) in H1.
now apply -> (rngl_sub_move_0_r Hop) in H1.
Qed.

(*
Theorem lap_opt_mul_div :
  let lop := lap_ring_like_op in
  if rngl_has_quot then ∀ a b, b ≠ 0%L → (a * b / b)%L = a
  else not_applicable.
Proof.
intros rol; subst rol.
unfold rngl_has_quot; cbn.
unfold lap_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool rngl_mul_is_comm) as [Hco| ]; [ | easy ].
destruct (Sumbool.sumbool_of_bool rngl_has_opp) as [Hop| ]; [ | easy ].
destruct (Sumbool.sumbool_of_bool rngl_has_inv) as [Hiv| ]; [ | easy ].
remember rngl_opt_inv_or_quot as iq eqn:Hiq; symmetry in Hiq.
destruct iq as [inv| ]; [ | easy ].
intros a b Hbz.
unfold rngl_div, rngl_has_inv; cbn.
unfold lap_opt_inv_or_quot.
unfold rngl_has_quot, lap_opt_inv_or_quot; cbn.
unfold rngl_quot; cbn.
unfold lap_opt_inv_or_quot.
rewrite Hco, Hop, Hiv, Hiq.
destruct (Sumbool.sumbool_of_bool true) as [H| H]; [ clear H | easy ].
apply lap_mul_div; try easy.
...
Qed.
*)

(*
Theorem lap_opt_mul_quot_r :
  let rol := lap_ring_like_op in
  if (rngl_has_quot && negb rngl_mul_is_comm)%bool then
    ∀ a b, b ≠ 0%L → (b * a / b)%L = a
  else not_applicable.
Proof.
(*
easy.
*)
intros rol.
unfold rngl_has_quot; cbn.
unfold lap_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool rngl_mul_is_comm) as [Hco| Hco];
  rewrite Hco; [ | easy ].
now rewrite Bool.andb_false_r.
Qed.
*)

(*
Theorem lap_opt_eqb_eq :
  let rol := lap_ring_like_op in
  if rngl_has_eqb then ∀ a b, (a =? b)%L = true ↔ a = b
  else not_applicable.
Proof.
intros rol; subst rol.
intros a b; cbn.
...
apply lap_eqb_eq.
intros c d.
split; intros Hcd. {
  now apply (rngl_eqb_eq Heb) in Hcd.
}
subst c.
now apply rngl_eqb_eq.
Qed.
*)

Theorem lap_opt_le_dec :
  let rol := lap_ring_like_op in
  if rngl_has_dec_le then ∀ a b, {(a ≤ b)%L} + {¬ (a ≤ b)%L}
  else not_applicable.
Proof.
intros rol; subst rol.
destruct rngl_has_dec_le; [ | easy ].
now intros; right; cbn.
Qed.

Theorem lap_opt_integral :
  let rol := lap_ring_like_op in
  if rngl_is_integral then
    ∀ a b, (a * b)%L = 0%L → a = 0%L ∨ b = 0%L
  else not_applicable.
Proof.
intros rol; subst rol.
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
specialize (last_lap_mul (la ++ [a]) (lb ++ [b])) as H2.
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

Theorem lap_rngl_of_nat :
  let lop := lap_ring_like_op in
  ∀ n, rngl_of_nat n = if Nat.eq_dec n 0 then [] else [rngl_of_nat n].
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
induction n; [ easy | clear Hnz; cbn ].
destruct n; [ now cbn; rewrite rngl_add_0_r | ].
now rewrite IHn.
Qed.

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

(*
Check rngl_opt_add_opp_l.
Check rngl_opt_mul_div.
Check rngl_opt_eqb_eq.
*)

(*
Definition lap_ring_like_prop : ring_like_prop (list T) :=
  let rol := lap_ring_like_op in
  {| rngl_mul_is_comm := rngl_mul_is_comm;
     rngl_has_dec_le := rngl_has_dec_le;
     rngl_is_integral := rngl_is_integral;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := lap_add_comm;
     rngl_add_assoc := lap_add_assoc;
     rngl_add_0_l := lap_add_0_l;
     rngl_mul_assoc := lap_mul_assoc;
     rngl_mul_1_l := lap_mul_1_l;
     rngl_mul_add_distr_l := lap_mul_add_distr_l;
     rngl_opt_mul_comm := lap_opt_mul_comm;
     rngl_opt_mul_1_r := lap_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := lap_opt_mul_add_distr_r;
     rngl_opt_add_opp_l := NA; (*lap_opt_add_opp_l;*)
     rngl_opt_add_sub := NA; (*lap_opt_has_no_subt _;*)
     rngl_opt_sub_sub_sub_add := NA; (*lap_opt_has_no_subt _;*)
     rngl_opt_mul_sub_distr_l := NA; (*lap_opt_has_no_subt _;*)
     rngl_opt_mul_sub_distr_r := NA; (*lap_opt_has_no_subt _;*)
     rngl_opt_mul_inv_l := NA; (*lap_opt_has_no_inv _;*)
     rngl_opt_mul_inv_r := NA; (*lap_opt_has_no_inv_and _ _;*)
     rngl_opt_mul_div := NA; (*lap_opt_mul_div;*)
     rngl_opt_mul_quot_r := lap_opt_mul_quot_r;
     rngl_opt_eqb_eq := NA; (*lap_opt_eqb_eq;*)
     rngl_opt_le_dec := lap_opt_le_dec;
     rngl_opt_integral := lap_opt_integral;
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
*)

Theorem eq_lap_add_nil : ∀ la lb, (la + lb = [])%lap → la = [] ∧ lb = [].
Proof.
intros * Hab.
destruct la as [| a]; cbn in Hab; [ subst lb; easy | ].
now destruct lb.
Qed.

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

(* examples *)

(* polynomials of nat *)

(* commented because locally don't want to depend here on NatRingLike
Require Import NatRingLike.

Definition nat_polyn_ring_like_op : ring_like_op (polyn nat) :=
  @polyn_ring_like_op _ nat_ring_like_op nat_ring_like_prop
    eq_refl eq_refl.

Definition nat_polyn_ring_like_prop : ring_like_prop (polyn nat) :=
  @polyn_ring_like_prop _ nat_ring_like_op nat_ring_like_prop
    eq_refl eq_refl.
*)

(* polynomials of Z *)

(* commented because locally don't want to depend here on ZArith & Zrl
Require Import ZArith.
Require Import RnglAlg.Zrl.

Definition Z_polyn_ring_like_op : ring_like_op (polyn Z) :=
  @polyn_ring_like_op Z Z_ring_like_op Z_ring_like_prop
    eq_refl eq_refl.

Definition Z_polyn_ring_like_prop : ring_like_prop (polyn Z) :=
  @polyn_ring_like_prop Z Z_ring_like_op Z_ring_like_prop
    eq_refl eq_refl.
*)

(* polynomials of Q *)

(* commented because don't want to depend here on Rational & Qrl
Require Import RnglAlg.Rational.
Require Import RnglAlg.Qrl.

Definition Q_polyn_ring_like_op : ring_like_op (polyn Q) :=
  @polyn_ring_like_op _ Q_ring_like_op Q_ring_like_prop
    eq_refl eq_refl.

Definition Q_polyn_ring_like_prop : ring_like_prop (polyn Q) :=
  @polyn_ring_like_prop _ Q_ring_like_op Q_ring_like_prop
    eq_refl eq_refl.
*)

(* polynomials of square matrices *)

(* locally don't want this module to depend on Matrix & MatRl
Require Import Matrix.
Require Import RnglAlg.MatRl.

Definition mat_polyn_ring_like_op n T ro rp eqb
  (Hop : rngl_has_opp = true) :
    ring_like_op (polyn (square_matrix n T)) :=
  @polyn_ring_like_op _
    (mat_ring_like_op ro eqb) (@mat_ring_like_prop T ro rp Hop eqb n)
    eq_refl eq_refl.

Definition mat_polyn_ring_like_prop n T ro rp eqb
  (Hop : rngl_has_opp = true) :
    ring_like_prop (polyn (square_matrix n T)) :=
  @polyn_ring_like_prop _
    (mat_ring_like_op ro eqb) (@mat_ring_like_prop T ro rp Hop eqb n)
    eq_refl eq_refl.
*)

(* square matrices of polynomials *)

(* locally don't want this module to depend on Matrix & MatRl
Require Import Matrix.
Require Import RnglAlg.MatRl.

Definition mat_of_polyn_ring_like_op n T
  (ro : ring_like_op T) (rp : ring_like_prop T) eqb
  (Heq : rngl_has_eqb = true)
  (Hos : rngl_has_opp_or_subt = true) :
    ring_like_op (square_matrix n (polyn T)) :=
  mat_ring_like_op (polyn_ring_like_op Heq Hos) (polyn_eqb eqb).

Theorem polyn_has_opp :
  ∀ T (ro : ring_like_op T) (rp : ring_like_prop T) Heq Hop,
  @rngl_has_opp (polyn T)
    (polyn_ring_like_op Heq (rngl_has_opp_has_opp_or_subt Hop)) = true.
Proof.
intros.
unfold rngl_has_opp in Hop |-*.
unfold polyn_ring_like_op; cbn.
unfold polyn_opt_opp_or_subt; cbn.
remember rngl_opt_opp_or_subt as os eqn:Hos; symmetry in Hos.
destruct os as [os| ]; [ | easy ].
now destruct os.
Qed.

Definition mat_of_polyn_ring_like_prop n T ro rp eqb
  (Heq : rngl_has_eqb = true) (Hop : rngl_has_opp = true) :
    ring_like_prop (square_matrix n (polyn T)) :=
  @mat_ring_like_prop _
    (polyn_ring_like_op Heq (rngl_has_opp_has_opp_or_subt Hop))
    (@polyn_ring_like_prop _ ro rp Heq (rngl_has_opp_has_opp_or_subt Hop))
    (polyn_has_opp rp Heq Hop) (polyn_eqb eqb) n.
*)

(* to be completed

Definition rlap_horner_1 {A} (to_T : A → _) rla x :=
  iter_list rla (λ accu a, (accu * x + to_T a)%L) 0%L.

Definition lap_horner_1 {A} (to_T : A → _) la x :=
  rlap_horner_1 to_T (rev la) x.

Definition eval_rlap_1 := rlap_horner_1 id.
Definition eval_lap_1 := lap_horner_1 id.
Definition eval_polyn_1 pol := eval_lap_1 (lap pol).

Check polyn_ring_like_op.

Definition rlap_compose {A} :=
  @rlap_horner_1 (polyn A).

Print rlap_compose.
...
*)

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.

Arguments eval_lap {T ro} la%lap x%L.
Arguments eval_rlap {T ro} rla%lap x%L.
Arguments has_polyn_prop {T ro} la%lap.
Arguments lap_add {T ro} (la lb)%lap.
Arguments lap_sub {T ro} (la lb)%lap.
Arguments lap_subt {T ro} (la lb)%lap.
Arguments lap_one {T ro}.
Arguments lap_opp {T ro} la%lap.
Arguments lap_mul {T ro} (la lb)%lap.
Arguments lap_norm {T ro} la%lap.
Arguments lap_quot_rem {T ro} (la lb)%lap.
Arguments lap_quot {T ro} (la lb)%lap.
Arguments lap_rem {T ro} (la lb)%lap.
Arguments lap_compose {T ro} (la lb)%lap.
Arguments lap_convol_mul {T ro} (la lb)%lap (i len)%nat.
Arguments polyn_norm_prop {T ro} la%lap.
Arguments rlap_compose {T ro} (rla rlb)%lap.
Arguments strip_0s {T ro} la%lap.

Arguments lap_quot_is_norm {T ro rp} Hos Heb Hiv (la lb)%lap.
Arguments lap_rem_is_norm {T ro rp} Heb (la lb)%lap.
Arguments lap_add_norm_idemp_l {T ro rp} Heb (la lb)%lap.
Arguments lap_add_norm_idemp_r {T ro rp} Heb (la lb)%lap.
Arguments lap_mul_norm_idemp_l {T ro rp} Hos Heb (la lb)%lap.
Arguments lap_mul_norm_idemp_r {T ro rp} Hos Heb (la lb)%lap.
Arguments lap_mul_1_l {T ro rp} Hos la%lap.
Arguments lap_mul_1_r {T ro rp} Hos la%lap.
Arguments lap_mul_comm {T ro rp} Hic (a b)%lap.
Arguments has_polyn_prop_lap_norm {T ro rp} Heb la%lap.
Arguments lap_quot_rem_prop {T ro rp} Hos Heb Hic Hop Hiv (la lb lq lr)%lap.
Arguments lap_norm_mul {T ro rp} Hos Heb Hiv (la lb)%lap.
Arguments lap_mul_div {T ro rp} Hos Heb Hic Hop Hiv (la lb)%lap.
Arguments all_0_lap_norm_nil {T ro rp} Heb la%lap.
Arguments last_lap_mul {T ro rp} Hos (la lb)%lap.
Arguments lap_ring_like_op {T ro}.
Arguments lap_x_power {T ro} n%nat.

Notation "1" := lap_one : lap_scope.
Notation "- a" := (lap_opp a) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
Notation "a / b" := (lap_quot a b) : lap_scope.
Notation "a 'mod' b" := (lap_rem a b) : lap_scope.
Notation "a '°' b" := (lap_compose a b) (at level 40, left associativity) :
  lap_scope.

(* polynomials *)

(* TODO: use an intermediate type like this:
      Record polyn T := mk_polyn { lap : list T }.
   and another type for the condition that the last value in lap
   is not null.
*)

Record polyn T {ro : ring_like_op T} := mk_polyn
  { lap : list T;
    lap_prop : has_polyn_prop lap = true }.

Arguments polyn T {ro}.
Arguments mk_polyn {T ro} lap%list.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
Context {Hos : rngl_has_opp_or_subt = true}.
Context {Heb : rngl_has_eqb = true}.

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

Definition polyn_of_norm_lap la :=
  mk_polyn (lap_norm la) (polyn_norm_prop la).

Definition polyn_of_const c :=
  polyn_of_norm_lap [c].

Arguments polyn_of_const c%L.

Definition polyn_zero := mk_polyn [] eq_refl.
Definition polyn_one := polyn_of_const 1.

Definition polyn_norm la := mk_polyn (lap_norm la) (polyn_norm_prop la).
Definition polyn_add p1 p2 := polyn_norm (lap_add (lap p1) (lap p2)).
Definition polyn_opp pol := polyn_norm (lap_opp (lap pol)).

Definition polyn_subt p1 p2 := polyn_norm (lap_subt (lap p1) (lap p2)).
Definition polyn_sub p1 p2 :=
  if rngl_has_opp then polyn_add p1 (polyn_opp p2)
  else if rngl_has_subt then polyn_subt p1 p2
  else polyn_zero.

Definition polyn_mul p1 p2 := polyn_norm (lap_mul (lap p1) (lap p2)).

Definition polyn_quot (pa pb : polyn T) : polyn T :=
  match Sumbool.sumbool_of_bool rngl_has_inv with
  | left Hiv =>
      let lq := lap_quot (lap pa) (lap pb) in
      mk_polyn lq
        (lap_quot_is_norm Hos Heb Hiv (lap pa) (lap pb) (lap_prop pa)
           (lap_prop pb))
  | right _ =>
      polyn_zero
  end.

Definition polyn_rem (pa pb : polyn T) : polyn T :=
  let lq := lap_rem (lap pa) (lap pb) in
  mk_polyn lq
    (lap_rem_is_norm Heb (lap pa) (lap pb) (lap_prop pa) (lap_prop pb)).

Definition polyn_quot_rem (pa pb : polyn T) : polyn T * polyn T :=
  (polyn_quot pa pb, polyn_rem pa pb).

Definition polyn_x_power n := polyn_of_norm_lap (lap_x_power n).

(* polyn opposite or subtraction *)

Definition polyn_opt_opp_or_subt :
  option ((polyn T → polyn T) + (polyn T → polyn T → polyn T)) :=
  match rngl_opt_opp_or_subt with
  | Some (inl _) => Some (inl polyn_opp)
  | Some (inr _) => Some (inr polyn_subt)
  | None => None
  end.

(* polyn quotient *)

Definition polyn_opt_inv_or_quot :
  option ((polyn T → polyn T) + (polyn T → polyn T → polyn T)) :=
  match Sumbool.sumbool_of_bool rngl_mul_is_comm with
  | left Hco =>
      match Sumbool.sumbool_of_bool rngl_has_opp with
      | left Hop =>
          match Sumbool.sumbool_of_bool rngl_has_inv with
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

Definition polyn_ring_like_op : ring_like_op (polyn T) :=
  {| rngl_zero := polyn_zero;
     rngl_one := polyn_one;
     rngl_add := polyn_add;
     rngl_mul := polyn_mul;
     rngl_opt_opp_or_subt := polyn_opt_opp_or_subt;
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
Notation "'mkp' x" := (mk_polyn x _) (at level 0, x at level 0): polyn_scope.

Theorem polyn_add_comm : ∀ a b, (a + b)%pol = (b + a)%pol.
Proof.
intros.
unfold "+"%pol.
now rewrite lap_add_comm.
Qed.

Theorem polyn_add_assoc : ∀ pa pb pc,
  (pa + (pb + pc) = (pa + pb) + pc)%pol.
Proof.
intros (la, lapr) (lb, lbpr) (lc, lcpr).
apply eq_polyn_eq.
cbn - [ lap_norm ].
rewrite (lap_add_norm_idemp_l Heb).
rewrite (lap_add_norm_idemp_r Heb).
now rewrite lap_add_assoc.
Qed.

Theorem polyn_add_0_l : ∀ p, (0 + p)%pol = p.
Proof.
intros (la, lapr).
apply eq_polyn_eq; cbn.
now apply has_polyn_prop_lap_norm.
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
rewrite (lap_mul_norm_idemp_l Hos Heb).
rewrite (lap_mul_norm_idemp_r Hos Heb).
now rewrite lap_mul_assoc.
Qed.

Theorem polyn_mul_1_l : ∀ p, (1 * p)%pol = p.
Proof.
intros (la, lapr).
unfold "*"%pol.
unfold polyn_one.
apply eq_polyn_eq; cbn.
destruct (Nat.eq_dec rngl_characteristic 1) as [Hch| Hch]. {
  rewrite (rngl_characteristic_1 Hos Hch 1), (rngl_eqb_refl Heb); cbn.
  apply Bool.orb_true_iff in lapr.
  destruct lapr as [lapr| lapr]; [ now apply is_empty_list_empty in lapr | ].
  apply (rngl_neqb_neq Heb) in lapr.
  exfalso; apply lapr.
  apply (rngl_characteristic_1 Hos Hch).
}
apply rngl_1_neq_0_iff, (rngl_eqb_neq Heb) in Hch; rewrite Hch.
cbn - [ lap_mul ].
rewrite (lap_mul_1_l Hos).
now apply (has_polyn_prop_lap_norm Heb).
Qed.

Theorem polyn_mul_add_distr_l : ∀ pa pb pc,
  (pa * (pb + pc))%pol = (pa * pb + pa * pc)%pol.
Proof.
intros.
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm.
rewrite (lap_mul_norm_idemp_r Hos Heb).
rewrite (lap_add_norm_idemp_l Heb).
rewrite (lap_add_norm_idemp_r Heb).
f_equal.
now rewrite lap_mul_add_distr_l.
Qed.

Theorem polyn_mul_add_distr_r :
  ∀ a b c : polyn T, ((a + b) * c)%pol = (a * c + b * c)%pol.
Proof.
intros.
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm.
rewrite (lap_mul_norm_idemp_l Hos Heb).
rewrite (lap_add_norm_idemp_l Heb).
rewrite (lap_add_norm_idemp_r Heb).
f_equal.
now rewrite lap_mul_add_distr_r.
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

Theorem polyn_mul_comm :
  rngl_mul_is_comm = true →
  ∀ a b : polyn T, (a * b)%pol = (b * a)%pol.
Proof.
intros Hic *.
specialize polyn_opt_mul_comm as H1.
rewrite Hic in H1.
apply H1.
Qed.

(* optional right multiplication by 1; not required if multiplication
   is commutative *)

Theorem polyn_mul_1_r : ∀ a : polyn T, (a * 1)%pol = a.
Proof.
intros.
apply eq_polyn_eq; cbn.
unfold polyn_one.
destruct (Nat.eq_dec rngl_characteristic 1) as [Hch| Hch]. {
  destruct a as (la, pa); cbn.
  apply Bool.orb_true_iff in pa.
  destruct pa as [pa| pa]. {
    now apply is_empty_list_empty in pa; subst la.
  }
  apply (rngl_neqb_neq Heb) in pa.
  exfalso; apply pa.
  apply (rngl_characteristic_1 Hos Hch).
}
apply rngl_1_neq_0_iff, (rngl_eqb_neq Heb) in Hch; rewrite Hch.
cbn - [ lap_mul ].
rewrite (lap_mul_1_r Hos).
apply (has_polyn_prop_lap_norm Heb).
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

Theorem polyn_add_opp_l :
  rngl_has_opp = true
  → ∀ a : polyn T, (- a + a)%pol = 0%pol.
Proof.
intros Hop *.
apply eq_polyn_eq.
destruct a as (la, Ha); cbn.
do 2 rewrite fold_lap_norm.
rewrite (lap_add_norm_idemp_l Heb).
now apply lap_norm_add_opp_l.
Qed.

Theorem polyn_opt_add_opp_l :
  let rop := polyn_ring_like_op in
  if rngl_has_opp then ∀ a : polyn T, (- a + a)%L = 0%L else not_applicable.
Proof.
intros rop; subst rop.
remember rngl_has_opp as op eqn:Hop; symmetry in Hop.
intros.
destruct op; [ | easy ].
intros a.
unfold rngl_opp; cbn.
unfold polyn_opt_opp_or_subt.
specialize polyn_add_opp_l as add_opp_l.
unfold rngl_has_opp in Hop, add_opp_l.
cbn in Hop, add_opp_l.
unfold polyn_opt_opp_or_subt in Hop, add_opp_l.
destruct rngl_opt_opp_or_subt as [opp| ]; [ | easy ].
destruct opp as [opp| ]; [ | easy ].
now apply add_opp_l.
Qed.

(*
Theorem polyn_opt_has_no_subt : ∀ P,
  let _ := polyn_ring_like_op in
  if rngl_has_subt then P else not_applicable.
Proof.
intros.
unfold rngl_has_subt; cbn.
unfold polyn_opt_opp_or_subt.
destruct rngl_opt_opp_or_subt as [opp| ]; [ | easy ].
now destruct opp.
Qed.
*)

Theorem polyn_opt_has_no_inv : ∀ P,
  let _ := polyn_ring_like_op in
  if rngl_has_inv then P else not_applicable.
Proof.
intros.
unfold rngl_has_inv; cbn.
unfold polyn_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool rngl_mul_is_comm) as [Hic| Hic]; [ | easy ].
destruct (Sumbool.sumbool_of_bool rngl_has_opp) as [Hop| Hop]; [ | easy ].
destruct (Sumbool.sumbool_of_bool rngl_has_inv); [ | easy ].
now destruct rngl_opt_inv_or_quot.
Qed.

Theorem polyn_opt_has_no_inv_and : ∀ e P,
  let _ := polyn_ring_like_op in
  if (rngl_has_inv && e)%bool then P else not_applicable.
Proof.
intros.
unfold rngl_has_inv; cbn.
unfold polyn_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool rngl_mul_is_comm); [ | easy ].
destruct (Sumbool.sumbool_of_bool rngl_has_opp); [ | easy ].
destruct (Sumbool.sumbool_of_bool rngl_has_inv); [ | easy ].
now destruct rngl_opt_inv_or_quot.
Qed.

Arguments lap {T ro} p%pol.
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
specialize (lap_quot_rem_prop Hos Heb Hic Hop Hiv la lb) as H1.
specialize (H1 lq lr Hpa).
assert (H : (last lb 0 ≠ 0)%L). {
  apply (rngl_neqb_neq Heb).
  destruct lb; [ | easy ].
  exfalso; apply Hbz.
  now apply eq_polyn_eq.
}
specialize (H1 H Hpr); clear H.
assert (H : lap_quot_rem la lb = (lq, lr)). {
  unfold polyn_quot_rem in Hab.
  unfold polyn_quot, polyn_rem in Hab; cbn in Hab.
  destruct (Sumbool.sumbool_of_bool rngl_has_inv) as [Hiv2| Hiv2]. {
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
rewrite (lap_add_norm_idemp_l Heb).
rewrite <- H1; symmetry.
now apply has_polyn_prop_lap_norm.
Qed.

Notation "a + b" := (polyn_add a b) : polyn_scope.
Notation "a * b" := (polyn_mul a b) : polyn_scope.
Notation "a / b" := (polyn_quot a b) : polyn_scope.
Notation "a 'mod' b" := (polyn_rem a b) : polyn_scope.

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
destruct (Sumbool.sumbool_of_bool _) as [Hiv2| Hiv2]. {
  cbn; rewrite (lap_norm_mul Hos Heb Hiv _ _ pa pb).
  now apply lap_mul_div.
}
now rewrite Hiv in Hiv2.
Qed.

Theorem polyn_opt_mul_div :
  let _ := polyn_ring_like_op in
  if rngl_has_quot then ∀ a b, b ≠ 0%L → (a * b / b)%L = a
  else not_applicable.
Proof.
intros rop; subst rop.
unfold rngl_has_quot; cbn.
unfold polyn_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool rngl_mul_is_comm) as [Hco| ]; [ | easy ].
destruct (Sumbool.sumbool_of_bool rngl_has_opp) as [Hop| ]; [ | easy ].
destruct (Sumbool.sumbool_of_bool rngl_has_inv) as [Hiv| ]; [ | easy ].
remember rngl_opt_inv_or_quot as iq eqn:Hiq; symmetry in Hiq.
destruct iq as [inv| ]; [ | easy ].
intros a b Hbz.
unfold rngl_div, rngl_has_inv; cbn.
unfold polyn_opt_inv_or_quot.
unfold rngl_has_quot, polyn_opt_inv_or_quot; cbn.
unfold rngl_quot; cbn.
unfold polyn_opt_inv_or_quot.
rewrite Hco, Hop, Hiv, Hiq.
destruct (Sumbool.sumbool_of_bool true); [ | easy ].
now apply polyn_mul_div.
Qed.

Theorem polyn_opt_mul_quot_r :
  let _ := polyn_ring_like_op in
  if (rngl_has_quot && negb rngl_mul_is_comm)%bool then
    ∀ a b, b ≠ 0%L → (b * a / b)%L = a
  else not_applicable.
Proof.
intros rop.
unfold rngl_has_quot; cbn.
unfold polyn_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool _) as [Hco| Hco]; rewrite Hco; [ | easy ].
now rewrite Bool.andb_false_r.
Qed.

Theorem polyn_opt_eqb_eq :
  let rop := polyn_ring_like_op in
  if rngl_has_eqb then ∀ a b : polyn T, (a =? b)%L = true ↔ a = b
  else not_applicable.
Proof.
intros rop; subst rop.
intros a b; cbn.
apply polyn_eqb_eq.
intros c d.
split; intros Hcd. {
  now apply (rngl_eqb_eq Heb) in Hcd.
}
subst c.
now apply rngl_eqb_eq.
Qed.

Theorem polyn_opt_le_dec :
  let _ := polyn_ring_like_op in
  if rngl_has_dec_le then ∀ a b : polyn T, {(a ≤ b)%L} + {¬ (a ≤ b)%L}
  else not_applicable.
Proof.
intros rop; subst rop.
destruct rngl_has_dec_le; [ | easy ].
now intros; right; cbn.
Qed.

Theorem polyn_opt_integral :
  let _ := polyn_ring_like_op in
  if rngl_is_integral then
    ∀ a b : polyn T, (a * b)%L = 0%L → a = 0%L ∨ b = 0%L
  else not_applicable.
Proof.
intros rop; subst rop.
destruct (Sumbool.sumbool_of_bool rngl_is_integral) as [Hii| Hii]; rewrite Hii; [ | easy ].
intros * Hab.
cbn in Hab.
apply (f_equal lap) in Hab.
cbn in Hab.
specialize (proj2 (all_0_lap_norm_nil Heb _) Hab) as H1.
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
specialize (last_lap_mul Hos (la ++ [a]) (lb ++ [b])) as H2.
do 2 rewrite last_last in H2.
rewrite List_last_nth in H2.
rewrite H1 in H2.
symmetry in H2.
apply (rngl_neqb_neq Heb) in pa, pb.
apply (rngl_integral Hos) in H2; [ | now rewrite Hii ].
now destruct H2.
Qed.

Theorem lap_polyn_rngl_of_nat_char_0 :
  let _ := polyn_ring_like_op in
  rngl_characteristic = 0
  → ∀ i, i ≠ 0 → lap (rngl_of_nat i) = [rngl_of_nat i].
Proof.
intros rop Hch * Hiz.
subst rop.
induction i; [ easy | clear Hiz; cbn ].
assert (H : rngl_characteristic ≠ 1) by now rewrite Hch.
specialize (proj1 rngl_1_neq_0_iff H) as H1; clear H.
apply (rngl_eqb_neq Heb) in H1; rewrite H1.
cbn - [ lap_add ].
destruct i; [ now cbn; rewrite rngl_add_0_r, H1 | ].
rewrite IHi; [ cbn | easy ].
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [H11| H11]; [ | easy ].
clear IHi; exfalso.
apply (rngl_eqb_eq Heb) in H11.
specialize rngl_characteristic_prop as H2.
rewrite Hch in H2; cbn in H2.
now specialize (H2 (S i)).
Qed.

Theorem lap_polyn_rngl_of_nat_2 :
  let rop := polyn_ring_like_op in
  ∀ i, 0 < i < rngl_characteristic
  → lap (rngl_of_nat i) = [rngl_of_nat i].
Proof.
intros * Hi.
destruct (Nat.eq_dec rngl_characteristic 1) as [Hc1| Hc1]. {
  flia Hi Hc1.
}
specialize (proj1 rngl_1_neq_0_iff Hc1) as H11.
specialize rngl_characteristic_prop as Hch.
rewrite if_bool_if_dec in Hch.
destruct (Sumbool.sumbool_of_bool _) as [Hchz| Hchz]. {
  apply Nat.eqb_eq in Hchz.
  now rewrite Hchz in Hi.
}
clear Hchz.
destruct Hch as (Hbef, Hch).
induction i; [ easy | cbn ].
remember (lap (rngl_of_nat i)) as la eqn:Hla; symmetry in Hla.
apply (rngl_eqb_neq Heb) in H11; rewrite H11.
cbn - [ lap_add ].
destruct la as [| a]; cbn. {
  rewrite H11.
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
  destruct (Sumbool.sumbool_of_bool _) as [H12| H12]. {
    exfalso; apply (rngl_eqb_eq Heb) in H12.
    destruct i; [ easy | ].
    assert (H : 0 < S i < rngl_characteristic) by flia Hi.
    specialize (IHi H); clear H.
    injection IHi; clear IHi; intros; subst a la.
    clear Hlb.
    cbn in Hla.
    rewrite H11 in Hla.
    cbn - [ lap_add ] in Hla.
    remember (lap (rngl_of_nat i)) as lb eqn:Hlb; symmetry in Hlb.
    destruct lb as [| b]; cbn in Hla. {
      rewrite H11 in Hla.
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

Theorem lap_polyn_rngl_of_nat :
  let lop := lap_ring_like_op in
  let rop := polyn_ring_like_op in
  ∀ n, lap (rngl_of_nat n) = lap_norm (rngl_of_nat n).
Proof.
intros.
induction n; [ easy | cbn ].
unfold polyn_one.
rewrite IHn; cbn.
rewrite fold_lap_norm.
remember (@rngl_of_nat _ lop n) as la eqn:Hla; symmetry in Hla.
destruct (Nat.eq_dec rngl_characteristic 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite (H1 1%L), (rngl_eqb_refl Heb); cbn.
  destruct la as [| a]; [ now cbn; rewrite (rngl_eqb_refl Heb) | ].
  cbn; rewrite rev_involutive.
  now rewrite strip_0s_idemp, rngl_add_0_l.
}
specialize (proj1 rngl_1_neq_0_iff Hc1) as H1.
apply (rngl_eqb_neq Heb) in H1; rewrite H1; cbn.
destruct la as [| a]; [ easy | cbn ].
do 2 rewrite strip_0s_app.
cbn.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ cbn | easy ].
  apply (rngl_eqb_eq Heb) in Haz; subst a.
  now rewrite rngl_add_0_r.
}
cbn; rewrite rev_app_distr; cbn.
rewrite rev_app_distr; cbn.
rewrite rev_involutive.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]; [ | easy ].
apply (rngl_eqb_eq Heb) in Hbz; subst b.
now apply eq_strip_0s_cons in Hlb.
Qed.

Theorem polyn_characteristic_prop :
  let rop := polyn_ring_like_op in
  if rngl_characteristic =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
  else
    (∀ i : nat, 0 < i < rngl_characteristic → rngl_of_nat i ≠ 0%L) ∧
    rngl_of_nat rngl_characteristic = 0%L.
Proof.
intros rop; subst rop.
specialize rngl_characteristic_prop as H1.
rewrite if_eqb_eq_dec in H1 |-*.
destruct (Nat.eq_dec rngl_characteristic 0) as [Hcz| Hcz]. {
  intros i.
  specialize (H1 i) as H.
  intros Hi; apply H; clear H.
  apply (f_equal lap) in Hi.
  now rewrite lap_polyn_rngl_of_nat_char_0 in Hi.
} {
  destruct H1 as (Hbef, Hch).
  split. {
    intros i Hi; cbn.
    specialize (Hbef _ Hi) as H1.
    intros H; apply H1; clear H1; rename H into H1.
    generalize H1; intros H2.
    apply (f_equal lap) in H2; cbn in H2.
    now rewrite lap_polyn_rngl_of_nat_2 in H2.
  }
  apply eq_polyn_eq; cbn.
  rewrite lap_polyn_rngl_of_nat.
  rewrite (lap_rngl_of_nat rp).
  destruct (Nat.eq_dec _ _) as [Hc1| Hc1]; [ easy | ].
  rewrite Hch; cbn.
  now rewrite (rngl_eqb_refl Heb).
}
Qed.

(* *)

Definition polyn_opt_has_no_subt (_ : True) := 12.

Theorem polyn_opt_add_sub :
  let rop := polyn_ring_like_op in
  if rngl_has_subt then ∀ a b : polyn T, (a + b - b)%L = a
  else not_applicable.
Proof.
intros; subst rop.
unfold rngl_has_subt; cbn.
unfold rngl_sub, rngl_has_opp; cbn.
unfold polyn_opt_opp_or_subt.
unfold rngl_subt.
unfold rngl_has_subt; cbn.
unfold polyn_opt_opp_or_subt.
remember rngl_opt_opp_or_subt as os eqn:Hos'; symmetry in Hos'.
destruct os as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ easy | ].
intros (la, pa) (lb, pb).
unfold polyn_subt.
apply eq_polyn_eq; cbn - [ lap_norm ].
move lb before la.
...

Definition polyn_ring_like_prop : ring_like_prop (polyn T) :=
  {| rngl_mul_is_comm := rngl_mul_is_comm;
     rngl_has_dec_le := rngl_has_dec_le;
     rngl_is_integral := rngl_is_integral;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic;
     rngl_add_comm := polyn_add_comm;
     rngl_add_assoc := polyn_add_assoc;
     rngl_add_0_l := polyn_add_0_l;
     rngl_mul_assoc := polyn_mul_assoc;
     rngl_mul_1_l := polyn_mul_1_l;
     rngl_mul_add_distr_l := polyn_mul_add_distr_l;
     rngl_opt_mul_comm := polyn_opt_mul_comm;
     rngl_opt_mul_1_r := polyn_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := polyn_opt_mul_add_distr_r;
     rngl_opt_add_opp_l := polyn_opt_add_opp_l;
(*
     rngl_opt_add_sub := polyn_opt_has_no_subt _;
*)
     rngl_opt_add_sub := polyn_opt_add_sub;
(**)
     rngl_opt_sub_sub_sub_add := polyn_opt_has_no_subt _;
     rngl_opt_mul_sub_distr_l := polyn_opt_has_no_subt _;
     rngl_opt_mul_sub_distr_r := polyn_opt_has_no_subt _;
     rngl_opt_mul_inv_l := polyn_opt_has_no_inv _;
     rngl_opt_mul_inv_r := polyn_opt_has_no_inv_and _ _;
     rngl_opt_mul_div := polyn_opt_mul_div;
     rngl_opt_mul_quot_r := polyn_opt_mul_quot_r;
     rngl_opt_eqb_eq := polyn_opt_eqb_eq;
     rngl_opt_le_dec := polyn_opt_le_dec;
     rngl_opt_integral := polyn_opt_integral;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := polyn_characteristic_prop;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA |}.

Definition eval_polyn pol :=
  eval_lap (lap pol).

Definition polyn_compose p q :=
  polyn_of_norm_lap (lap_compose (lap p) (lap q)).

Definition monom (p : polyn T) i :=
  polyn_of_norm_lap [nth i (lap p) 0%L].

Theorem lap_norm_lap : ∀ p, lap_norm (lap p) = lap p.
Proof.
intros p.
apply (has_polyn_prop_lap_norm Heb).
apply lap_prop.
Qed.

Theorem lap_norm_lap_rngl_summation :
  let rol := lap_ring_like_op in
  let rop := polyn_ring_like_op in
  ∀ b e f,
  lap_norm (lap (∑ (i = b, e), f i)) = lap_norm (∑ (i = b, e), lap (f i)).
Proof.
intros.
unfold iter_seq, iter_list.
remember (S e - b) as n eqn:Hn.
clear e Hn.
cbn.
revert b.
induction n; intros; [ easy | ].
rewrite seq_S; cbn.
do 2 rewrite fold_left_app.
cbn - [ lap_norm ].
rewrite <- (lap_add_norm_idemp_l Heb).
rewrite IHn.
rewrite (lap_add_norm_idemp_l Heb).
apply lap_norm_idemp.
Qed.

Theorem lap_norm_rngl_summation_idemp :
  let rol := lap_ring_like_op in
  ∀ b e f,
  lap_norm (∑ (i = b, e), lap_norm (f i)) = lap_norm (∑ (i = b, e), f i).
Proof.
intros.
unfold iter_seq, iter_list.
remember (S e - b) as n eqn:Hn.
clear e Hn.
revert b.
induction n; intros; [ easy | ].
rewrite seq_S.
do 2 rewrite fold_left_app.
cbn - [ lap_norm ].
rewrite <- (lap_add_norm_idemp_l Heb).
rewrite IHn.
rewrite (lap_add_norm_idemp_l Heb).
rewrite (lap_add_norm_idemp_r Heb).
easy.
Qed.

Arguments lap_convol_mul_1_l {T ro rp} Hos la%lap (i len)%nat.
Arguments lap_convol_mul_l_succ_l {T ro rp} Hos (la lb)%lap (i len)%nat.

Theorem lap_cons : ∀ a la, a :: la = ([a] + [0; 1]%L * la)%lap.
Proof.
intros.
destruct la as [| a2]; [ easy | cbn ].
unfold iter_seq, iter_list; cbn.
rewrite rngl_mul_1_l.
do 2 rewrite (rngl_mul_0_l Hos).
do 2 rewrite rngl_add_0_r.
rewrite rngl_add_0_l.
f_equal; f_equal.
rewrite (lap_convol_mul_l_succ_l Hos).
now symmetry; apply (lap_convol_mul_1_l Hos).
Qed.

End a.

Arguments lap_add_assoc {T ro rp} (al1 al2 al3)%lap.
Arguments lap_cons {T ro rp} Hos a%L la%lap.
Arguments lap_mul_assoc {T ro rp} Hos Heb (la lb lc)%lap.
Arguments lap_mul_const_l {T ro rp} Hos a la%lap.
Arguments lap_mul_const_r {T ro rp} Hos a la%lap.
Arguments lap_mul_x_l {T ro rp} Hos [la]%lap.
Arguments lap_norm_lap_rngl_summation {T ro rp} Hos Heb (b e)%nat.
Arguments lap_norm_rngl_summation_idemp {T ro rp} Heb (b e)%nat.
Arguments list_nth_lap_eq {T ro rp} Heb (la lb)%lap.

Declare Scope polyn_scope.
Delimit Scope polyn_scope with pol.

Arguments lap {T ro} p%pol.
Arguments polyn_zero {T ro}.
Arguments polyn_one {T ro}.
Arguments polyn_add {T ro} p1 p2.
Arguments polyn_mul {T ro} p1 p2.
Arguments polyn_norm {T ro} la%lap.
Arguments polyn_quot {T ro rp Hos Heb} pa pb.
Arguments polyn_rem {T ro rp Heb} pa pb.
Arguments polyn_ring_like_op {T ro rp} Hos Heb.
Arguments polyn_x_power {T ro} n%nat.

Notation "0" := polyn_zero : polyn_scope.
Notation "1" := polyn_one : polyn_scope.

Notation "a + b" := (polyn_add a b) : polyn_scope.
Notation "a * b" := (polyn_mul a b) : polyn_scope.
Notation "a / b" := (polyn_quot a b) : polyn_scope.
Notation "a 'mod' b" := (polyn_rem a b) : polyn_scope.
Notation "- a" := (polyn_opp a) : polyn_scope.
Notation "'mkp' x" := (mk_polyn x _) (at level 0, x at level 0): polyn_scope.

Arguments mk_polyn {T ro} lap%lap.
Arguments polyn_mul_comm {T ro rp} Hic a b.
Arguments polyn_of_const {T ro} c%L.
Arguments polyn_of_norm_lap {T ro} la%lap.
