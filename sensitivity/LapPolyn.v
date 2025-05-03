(* LapPolyn.v *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
Import List.ListNotations Init.Nat.

Require Import RingLike.RingLike.
Require Import RingLike.IterAdd.
Require Import RingLike.LapRingLike.

Require Import Misc.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem strip_0s_idemp : ∀ la, strip_0s (strip_0s la) = strip_0s la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ easy | cbn ].
now rewrite Haz.
Qed.

(* *)

Definition lap_subt la lb :=
  List_map2 rngl_subt
    (la ++ List.repeat 0%L (length lb - length la))
    (lb ++ List.repeat 0%L (length la - length lb)).

Definition lap_opp la := List.map rngl_opp la.

Definition lap_sub la lb :=
  if rngl_has_opp T then lap_add la (lap_opp lb)
  else if rngl_has_subt T then lap_subt la lb
  else List.repeat 0%L (max (length la) (length lb)).

(* *)

Theorem fold_lap_subt :
  ∀ la lb,
  List_map2 rngl_subt (la ++ List.repeat 0%L (length lb - length la))
    (lb ++ List.repeat 0%L (length la - length lb)) =
  lap_subt la lb.
Proof. easy. Qed.

Theorem fold_lap_opp : ∀ la, List.map rngl_opp la = lap_opp la.
Proof. easy. Qed.

Theorem fold_lap_norm : ∀ la, List.rev (strip_0s (List.rev la)) = lap_norm la.
Proof. easy. Qed.

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
            let rlr := lap_sub rla' (List.map (λ cb, (cb * cq)%L) rlb') in
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
  let (rlq, rlr) := rlap_quot_rem (List.rev la) (List.rev lb) in
  (List.rev rlq, List.rev (strip_0s rlr)).

Definition lap_quot la lb :=
  let (rlq, rlr) := rlap_quot_rem (List.rev la) (List.rev lb) in
  List.rev rlq.

Definition lap_rem la lb :=
  let (rlq, rlr) := rlap_quot_rem (List.rev la) (List.rev lb) in
  List.rev (strip_0s rlr).

(* evaluation of a polynomial in x *)
(* and composition of polynomials *)

Definition rlap_horner {A} (zero : A) (add mul : A → A → A) rla x :=
  iter_list rla (λ accu a, add (mul accu x) a) zero.

Definition lap_horner A (zero : A) (add mul : A → A → A) la x :=
  rlap_horner zero add mul (List.rev la) x.

Definition eval_rlap :=
  rlap_horner 0%L rngl_add rngl_mul.

Definition eval_lap la x :=
  eval_rlap (List.rev la) x.

Definition rlap_compose rla rlb :=
  rlap_horner [] lap_add lap_mul (List.map (λ a, [a]) rla) (List.rev rlb).

Definition lap_compose la lb :=
  rlap_compose (List.rev la) (List.rev lb).

End a.

Arguments lap_subt {T ro} (la lb)%_lap.

Notation "- a" := (lap_opp a) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a / b" := (lap_quot a b) : lap_scope.
Notation "a 'mod' b" := (lap_rem a b) : lap_scope.
Notation "a '°' b" := (lap_compose a b) (at level 40, left associativity) :
  lap_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hed : rngl_has_eq_dec T = true).

Theorem List_map2_rngl_subt_0_r :
  rngl_has_subt T = true →
  ∀ n la,
  n = length la
  → List_map2 rngl_subt la (List.repeat 0%L n) = la.
Proof.
intros Hsu * Hn; subst n.
induction la as [| la]; [ easy | cbn ].
now rewrite (rngl_subt_0_r Hsu); f_equal.
Qed.

Theorem lap_subt_0_r :
  rngl_has_subt T = true →
  ∀ la, lap_subt la 0 = la.
Proof.
intros Hsu *.
unfold lap_subt.
rewrite Nat.sub_0_r; cbn.
rewrite List.app_nil_r.
now apply (List_map2_rngl_subt_0_r Hsu).
Qed.

(* *)

Theorem strip_0s_length_le : ∀ l, length (strip_0s l) ≤ length l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
destruct (a =? 0)%L; cbn; [ | easy ].
flia IHl.
Qed.

Theorem lap_subt_length : ∀ la lb,
  length (lap_subt la lb) = max (length la) (length lb).
Proof.
intros.
unfold lap_subt.
rewrite List_length_map2.
do 2 rewrite List.length_app, List.repeat_length.
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
now rewrite List.repeat_length.
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
rewrite lap_sub_length, List.length_map.
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

Theorem lap_mul_length : ∀ la lb,
  length (la * lb)%lap =
    match length la with
    | 0 => 0
    | S a =>
        match length lb with
        | 0 => 0
        | S b => S (a + b)
        end
    end.
Proof.
intros.
unfold lap_mul.
destruct la; [ easy | ].
destruct lb; [ easy | ].
rewrite lap_convol_mul_length; cbn.
now rewrite Nat.add_succ_r, Nat.sub_0_r.
Qed.

Theorem lap_norm_List_map2_app_app_idemp_r :
  ∀ f, (∀ a, f a 0%L = a) →
  ∀ la lb,
  lap_norm
    (List_map2 f (la ++ List.repeat 0%L (length (lap_norm lb) - length la))
       (lap_norm lb ++ List.repeat 0%L (length la - length (lap_norm lb)))) =
  lap_norm
    (List_map2 f (la ++ List.repeat 0%L (length lb - length la))
       (lb ++ List.repeat 0%L (length la - length lb))).
Proof.
intros * Hf *.
unfold lap_norm; f_equal.
revert lb.
induction la as [| a]; intros. {
  cbn.
  do 2 rewrite List.app_nil_r, Nat.sub_0_r.
  rewrite List.length_rev.
  rewrite fold_lap_norm.
  rewrite List_rev_map2. 2: {
    unfold lap_norm.
    now rewrite List.repeat_length, List.length_rev.
  }
  rewrite List_rev_map2; [ | apply List.repeat_length ].
  do 2 rewrite List.rev_repeat.
  unfold lap_norm.
  rewrite List.rev_involutive.
  rewrite <- (List.length_rev lb).
  remember (List.rev lb) as la eqn:Hla.
  clear lb Hla.
  induction la as [| a]; [ easy | cbn ].
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ | easy ].
  apply (rngl_eqb_eq Hed) in Haz; subst a.
  rewrite Hf.
  rewrite (rngl_eqb_refl Hed).
  apply IHla.
}
destruct lb as [| b]; [ easy | cbn ].
do 2 rewrite strip_0s_app; cbn.
rewrite <- IHla.
remember (strip_0s (List.rev lb)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
    cbn.
    apply (rngl_eqb_eq Hed) in Hbz.
    subst b; cbn.
    rewrite List.app_nil_r, Hf, Nat.sub_0_r.
    rewrite List_rev_map2; [ | symmetry; apply List.repeat_length ].
    rewrite List.rev_repeat.
    now rewrite strip_0s_app.
  }
  cbn.
  now rewrite strip_0s_app.
}
cbn.
rewrite List.rev_app_distr; cbn.
now rewrite strip_0s_app.
Qed.

(* *)

Theorem lap_subt_norm_idemp_l :
  rngl_has_subt T = true →
  ∀ la lb,
  lap_norm (lap_subt (lap_norm la) lb) = lap_norm (lap_subt la lb).
Proof.
intros Hsu *.
apply (lap_norm_List_map2_app_app_idemp_l Hed).
apply (rngl_subt_0_r Hsu).
Qed.

Theorem lap_subt_norm_idemp_r :
  rngl_has_subt T = true →
  ∀ la lb,
  lap_norm (lap_subt la (lap_norm lb)) = lap_norm (lap_subt la lb).
Proof.
intros Hsu *.
apply lap_norm_List_map2_app_app_idemp_r.
apply (rngl_subt_0_r Hsu).
Qed.

(* *)

Theorem lap_mul_1_l :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ la, (1 * la)%lap = la.
Proof.
intros Hon Hos *.
unfold lap_one.
rewrite (lap_mul_const_l Hos).
induction la as [| a]; [ easy | cbn ].
rewrite (rngl_mul_1_l Hon); f_equal.
apply IHla.
Qed.

Theorem lap_mul_1_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ la, (la * 1)%lap = la.
Proof.
intros Hon Hos *.
unfold lap_one.
rewrite (lap_mul_const_r Hos).
induction la as [| a]; [ easy | cbn ].
rewrite (rngl_mul_1_r Hon); f_equal.
apply IHla.
Qed.

(* *)

Theorem last_lap_convol_mul_last :
  rngl_has_opp_or_subt T = true →
  ∀ la lb a b i len d,
  len ≠ 0
  → length la + length lb + 1 = i + len
  → List.last (lap_convol_mul (la ++ [a]) (lb ++ [b]) i len) d = (a * b)%L.
Proof.
intros Hos * Hlen Hlab.
revert la lb i Hlab.
induction len; intros; [ easy | clear Hlen ].
cbn.
destruct len. {
  cbn.
  rewrite rngl_summation_split3 with (j := length la); [ | flia Hlab ].
  rewrite List.app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag; cbn.
  replace (i - length la) with (length lb) by flia Hlab.
  rewrite List.app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag; cbn.
  rewrite all_0_rngl_summation_0. 2: {
    intros j Hj.
    rewrite (List.nth_overflow (lb ++ [b])). 2: {
      rewrite List.length_app; cbn; flia Hlab Hj.
    }
    apply (rngl_mul_0_r Hos).
  }
  rewrite rngl_add_0_l.
  rewrite all_0_rngl_summation_0. 2: {
    intros j Hj.
    rewrite (List.nth_overflow (la ++ [a])). 2: {
      now rewrite List.length_app.
    }
    apply (rngl_mul_0_l Hos).
  }
  apply rngl_add_0_r.
}
rewrite IHlen; [ easy | easy | flia Hlab ].
Qed.

Theorem last_lap_mul :
  rngl_has_opp_or_subt T = true →
  ∀ la lb, List.last (la * lb)%lap 0%L = (List.last la 0 * List.last lb 0)%L.
Proof.
intros Hos *.
unfold lap_mul.
destruct la as [| a] using List.rev_ind. {
  now symmetry; apply (rngl_mul_0_l Hos).
}
clear IHla.
destruct lb as [| b] using List.rev_ind. {
  cbn.
  rewrite rngl_mul_0_r; [ | easy ].
  now destruct (la ++ [a]).
}
clear IHlb.
move b before a.
remember (la ++ [a]) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]; [ now apply List.app_eq_nil in Hlc | ].
remember (lb ++ [b]) as ld eqn:Hld.
symmetry in Hld.
destruct ld as [| d]; [ now apply List.app_eq_nil in Hld | ].
rewrite <- Hlc, <- Hld.
clear c d lc ld Hlc Hld.
do 2 rewrite List.last_last.
do 2 rewrite List.length_app.
cbn.
apply (last_lap_convol_mul_last Hos); flia.
Qed.

(* *)

Theorem List_map2_rngl_subt_diag :
  rngl_has_opp_or_subt T = true →
  ∀ la, List_map2 rngl_subt la la = List.repeat 0%L (length la).
Proof.
intros Hos *.
induction la as [| a]; [ easy | cbn ].
f_equal; [ | apply IHla ].
now apply rngl_subt_diag.
Qed.

Theorem lap_opt_add_sub :
  rngl_has_subt T = true →
  ∀ la lb : list T,
  (la + lb - lb)%lap = la ++ List.repeat 0%L (length lb - length la).
Proof.
intros Hsu *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  move Hsu at bottom.
  unfold rngl_has_opp in Hop.
  unfold rngl_has_subt in Hsu.
  destruct rngl_opt_opp_or_subt; [ now destruct s | easy ].
}
move Hop after Hsu.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; right.
}
move Hos after Hed.
unfold lap_sub.
rewrite Hop, Hsu.
unfold lap_add, lap_subt.
rewrite List_length_map2.
do 2 rewrite List.length_app, List.repeat_length.
rewrite min_add_sub_max.
rewrite <- Nat.sub_min_distr_l.
rewrite Nat.sub_diag, Nat.min_0_r.
rewrite <- Nat.sub_max_distr_r.
rewrite Nat.sub_diag, Nat.max_0_r.
destruct (le_dec (length la) (length lb)) as [Hab| Hab]. {
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  do 2 rewrite List.app_nil_r.
  revert lb Hab.
  induction la as [| a]; intros; cbn. {
    rewrite Nat.sub_0_r.
    rewrite List_map2_rngl_add_0_l.
    now apply List_map2_rngl_subt_diag.
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
  do 2 rewrite List.app_nil_r.
  revert lb Hab.
  induction la as [| a]; intros; [ easy | cbn ].
  destruct lb as [| b]; cbn. {
    rewrite rngl_add_0_r.
    rewrite (rngl_subt_0_r Hsu); f_equal.
    rewrite List_map2_rngl_add_0_r.
    now apply (List_map2_rngl_subt_0_r Hsu).
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

Theorem lap_subt_add_distr :
  rngl_has_subt T = true →
  ∀ la lb lc, lap_subt la (lb + lc) = lap_subt (lap_subt la lb) lc.
Proof.
intros Hsu *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  move Hsu at bottom.
  unfold rngl_has_opp in Hop.
  unfold rngl_has_subt in Hsu.
  destruct rngl_opt_opp_or_subt; [ now destruct s | easy ].
}
move Hop after Hsu.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; right.
}
move Hos after Hed.
unfold lap_subt, lap_add.
do 2 rewrite List_length_map2.
do 4 rewrite List.length_app, List.repeat_length.
do 2 rewrite <- Nat.sub_min_distr_r.
destruct (le_dec (length lb) (length lc)) as [Hbc| Hbc]. {
  rewrite (proj2 (Nat.sub_0_le _ _) Hbc).
  rewrite List.app_nil_r, Nat.add_0_r.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  do 2 rewrite Nat.min_id.
  destruct (le_dec (length la) (length lb)) as [Hab| Hab]. {
    rewrite (proj2 (Nat.sub_0_le _ _) Hab).
    rewrite List.app_nil_r, Nat.add_0_r.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    do 2 rewrite Nat.min_id.
    rewrite (proj2 (Nat.sub_0_le _ _) Hbc).
    assert (Hac : length la ≤ length lc) by now transitivity (length lb).
    rewrite (proj2 (Nat.sub_0_le _ _) Hac).
    do 2 rewrite List.app_nil_r.
    rewrite (List_map2_map2_seq_r 0%L).
    rewrite List_length_map2, List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
    rewrite (List_map2_map2_seq_l 0%L).
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    symmetry.
    rewrite (List_map2_map2_seq_r 0%L).
    rewrite (List_map2_map2_seq_l 0%L).
    rewrite List.length_app, List.repeat_length.
    rewrite List_length_map2, List.length_app, List.repeat_length.
    rewrite (Nat.add_sub_assoc (length la)); [ | easy ].
    rewrite (Nat.add_comm (length la)), Nat.add_sub, Nat.min_id.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    symmetry.
    apply List_map2_ext_in.
    intros (i, j) Hi; cbn.
    assert (H : i = j) by now apply List_in_combine_same in Hi.
    subst j.
    apply List.in_combine_l in Hi.
    apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
    do 2 rewrite List_nth_app_repeat_r.
    rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
      rewrite List.length_app, List.repeat_length.
      rewrite Nat.add_sub_assoc; [ | easy ].
      now rewrite Nat.add_comm, Nat.add_sub.
    }
    rewrite List_nth_app_repeat_r.
    destruct (lt_dec i (length lb)) as [Hilb| Hilb]. {
      rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
        rewrite List.length_app, List.repeat_length.
        rewrite Nat.add_sub_assoc; [ | easy ].
        now rewrite Nat.add_comm, Nat.add_sub.
      }
      rewrite List_nth_app_repeat_r.
      specialize (rngl_sub_add_distr Hos) as H1.
      unfold rngl_sub in H1.
      rewrite Hop, Hsu in H1.
      apply H1.
    }
    apply Nat.nlt_ge in Hilb.
    assert (Hila : length la ≤ i) by now transitivity (length lb).
    rewrite List.nth_overflow; [ | easy ].
    rewrite List.nth_overflow; [ | easy ].
    rewrite rngl_add_0_l.
    rewrite (List.nth_overflow (List_map2 _ _ _)). 2: {
      rewrite List_length_map2, List.length_app, List.repeat_length.
      rewrite Nat.add_sub_assoc; [ | easy ].
      now rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
    }
    easy.
  }
  apply Nat.nle_gt in Hab.
  apply Nat.lt_le_incl in Hab.
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  rewrite List.app_nil_r, Nat.add_0_r.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  do 2 rewrite Nat.min_id.
  destruct (le_dec (length la) (length lc)) as [Hac| Hac]. {
    rewrite (proj2 (Nat.sub_0_le _ _) Hac).
    do 2 rewrite List.app_nil_r.
    rewrite (List_map2_map2_seq_r 0%L).
    rewrite List_length_map2, List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
    rewrite (List_map2_map2_seq_l 0%L).
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    symmetry.
    rewrite (List_map2_map2_seq_r 0%L).
    rewrite (List_map2_map2_seq_l 0%L).
    rewrite List.length_app, List.repeat_length.
    rewrite List_length_map2, List.length_app, List.repeat_length.
    rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
    rewrite (Nat.add_comm (length lb)), Nat.add_sub, Nat.min_id.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    symmetry.
    apply List_map2_ext_in.
    intros (i, j) Hi; cbn.
    assert (H : i = j) by now apply List_in_combine_same in Hi.
    subst j.
    apply List.in_combine_l in Hi.
    apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
    do 2 rewrite List_nth_app_repeat_r.
    rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
      rewrite List.length_app, List.repeat_length.
      rewrite Nat.add_sub_assoc; [ | easy ].
      now rewrite Nat.add_comm, Nat.add_sub.
    }
    rewrite List_nth_app_repeat_r.
    destruct (lt_dec i (length la)) as [Hila| Hila]. {
      rewrite (List_map2_nth 0%L 0%L); [ | easy | ]. 2: {
        rewrite List.length_app, List.repeat_length.
        rewrite Nat.add_sub_assoc; [ | easy ].
        now rewrite Nat.add_comm, Nat.add_sub.
      }
      rewrite List_nth_app_repeat_r.
      specialize (rngl_sub_add_distr Hos) as H1.
      unfold rngl_sub in H1.
      rewrite Hop, Hsu in H1.
      apply H1.
    }
    apply Nat.nlt_ge in Hila.
    assert (Hilb : length lb ≤ i) by now transitivity (length la).
    rewrite List.nth_overflow; [ | easy ].
    rewrite List.nth_overflow; [ | easy ].
    rewrite rngl_add_0_l.
    rewrite (List.nth_overflow (List_map2 _ _ _)). 2: {
      rewrite List_length_map2, List.length_app, List.repeat_length.
      rewrite Nat.add_sub_assoc; [ | easy ].
      now rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
    }
    easy.
  }
  apply Nat.nle_gt in Hac.
  apply Nat.lt_le_incl in Hac.
  rewrite (proj2 (Nat.sub_0_le _ _) Hac).
  do 2 rewrite List.app_nil_r.
  rewrite (List_map2_map2_seq_r 0%L).
  rewrite List.length_app, List_length_map2, List.length_app.
  do 2 rewrite List.repeat_length.
  rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
  rewrite (Nat.add_comm (length lb)), Nat.add_sub, Nat.min_id.
  rewrite (List_map2_map2_seq_l 0%L).
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  symmetry.
  rewrite (List_map2_map2_seq_r 0%L).
  rewrite (List_map2_map2_seq_l 0%L).
  rewrite List.length_app, List.repeat_length.
  rewrite List_length_map2, List.length_app, List.repeat_length.
  rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
  rewrite (Nat.add_comm (length lb)), Nat.add_sub, Nat.min_id.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  symmetry.
  apply List_map2_ext_in.
  intros (i, j) Hi; cbn.
  assert (H : i = j) by now apply List_in_combine_same in Hi.
  subst j.
  apply List.in_combine_l in Hi.
  apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
  do 2 rewrite List_nth_app_repeat_r.
  rewrite (List_map2_nth 0%L 0%L _ _ la); [ | easy | ]. 2: {
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite List_nth_app_repeat_r.
  destruct (lt_dec i (length lc)) as [Hilc| Hilc]. {
    rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
      rewrite List.length_app, List.repeat_length.
      rewrite Nat.add_sub_assoc; [ | easy ].
      now rewrite Nat.add_comm, Nat.add_sub.
    }
    rewrite List_nth_app_repeat_r.
    specialize (rngl_sub_add_distr Hos) as H1.
    unfold rngl_sub in H1.
    rewrite Hop, Hsu in H1.
    apply H1.
  }
  apply Nat.nlt_ge in Hilc.
  assert (Hilb : length lb ≤ i) by now transitivity (length lc).
  rewrite (List.nth_overflow lc); [ | easy ].
  rewrite (List.nth_overflow lb); [ | easy ].
  do 2 rewrite (rngl_subt_0_r Hsu).
  rewrite (List.nth_overflow (List_map2 _ _ _)). 2: {
    rewrite List_length_map2, List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
  }
  rewrite (rngl_subt_0_r Hsu).
  easy.
}
apply Nat.nle_gt in Hbc.
apply Nat.lt_le_incl in Hbc.
rewrite (proj2 (Nat.sub_0_le _ _) Hbc).
rewrite List.app_nil_r, Nat.add_0_r.
rewrite Nat.add_sub_assoc; [ | easy ].
rewrite Nat.add_comm, Nat.add_sub.
do 2 rewrite Nat.min_id.
destruct (le_dec (length la) (length lb)) as [Hab| Hab]. {
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  rewrite List.app_nil_r, Nat.add_0_r.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  do 2 rewrite Nat.min_id.
  rewrite (proj2 (Nat.sub_0_le _ _) Hbc).
  do 2 rewrite List.app_nil_r.
  rewrite (List_map2_map2_seq_r 0%L).
  rewrite List_length_map2, List.length_app, List.repeat_length.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
  rewrite (List_map2_map2_seq_l 0%L).
  rewrite List.length_app, List.repeat_length.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  symmetry.
  rewrite (List_map2_map2_seq_r 0%L).
  rewrite (List_map2_map2_seq_l 0%L).
  rewrite List.length_app, List.repeat_length.
  rewrite List_length_map2, List.length_app, List.repeat_length.
  rewrite (Nat.add_sub_assoc (length la)); [ | easy ].
  rewrite (Nat.add_comm (length la)), Nat.add_sub, Nat.min_id.
  rewrite (Nat.add_sub_assoc (length lc)); [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  symmetry.
  apply List_map2_ext_in.
  intros (i, j) Hi; cbn.
  assert (H : i = j) by now apply List_in_combine_same in Hi.
  subst j.
  apply List.in_combine_l in Hi.
  apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
  do 2 rewrite List_nth_app_repeat_r.
  rewrite (List_map2_nth 0%L 0%L); [ | easy | ]. 2: {
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite List_nth_app_repeat_r.
  rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite List_nth_app_repeat_r.
  specialize (rngl_sub_add_distr Hos) as H1.
  unfold rngl_sub in H1.
  rewrite Hop, Hsu in H1.
  apply H1.
}
apply Nat.nle_gt in Hab.
apply Nat.lt_le_incl in Hab.
assert (Hca : length lc ≤ length la) by now transitivity (length lb).
rewrite (proj2 (Nat.sub_0_le _ _) Hab).
rewrite List.app_nil_r, Nat.add_0_r.
rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
rewrite (Nat.add_comm (length lb)), Nat.add_sub, Nat.min_id.
rewrite (proj2 (Nat.sub_0_le _ _) Hca).
rewrite List.app_nil_r, Nat.min_id.
rewrite (List_map2_map2_seq_l 0%L).
rewrite (List_map2_map2_seq_r 0%L).
rewrite List.length_app, List.repeat_length.
rewrite List_length_map2.
rewrite List.length_app, List.repeat_length.
rewrite (Nat.add_sub_assoc (length lc)); [ | easy ].
rewrite (Nat.add_comm (length lc)), Nat.add_sub, Nat.min_id.
rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
rewrite (Nat.add_comm (length lb)), Nat.add_sub.
symmetry.
rewrite (List_map2_map2_seq_r 0%L).
rewrite (List_map2_map2_seq_l 0%L).
rewrite List.length_app, List.repeat_length.
rewrite List_length_map2, List.length_app, List.repeat_length.
rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
rewrite (Nat.add_comm (length lb)), Nat.add_sub, Nat.min_id.
rewrite Nat.add_sub_assoc; [ | easy ].
rewrite Nat.add_comm, Nat.add_sub.
symmetry.
apply List_map2_ext_in.
intros (i, j) Hi; cbn.
assert (H : i = j) by now apply List_in_combine_same in Hi.
subst j.
apply List.in_combine_l in Hi.
apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
do 2 rewrite List_nth_app_repeat_r.
rewrite (List_map2_nth 0%L 0%L _ _ la); [ | easy | ]. 2: {
  rewrite List.length_app, List.repeat_length.
  rewrite Nat.add_sub_assoc; [ | easy ].
  now rewrite Nat.add_comm, Nat.add_sub.
}
rewrite List_nth_app_repeat_r.
destruct (lt_dec i (length lb)) as [Hilb| Hilb]. {
  rewrite (List_map2_nth 0%L 0%L); [ | easy | ]. 2: {
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite List_nth_app_repeat_r.
  specialize (rngl_sub_add_distr Hos) as H1.
  unfold rngl_sub in H1.
  rewrite Hop, Hsu in H1.
  apply H1.
}
apply Nat.nlt_ge in Hilb.
assert (Hilc : length lc ≤ i) by now transitivity (length lb).
rewrite (List.nth_overflow lc); [ | easy ].
rewrite (List.nth_overflow lb); [ | easy ].
do 2 rewrite (rngl_subt_0_r Hsu).
rewrite (List.nth_overflow (List_map2 _ _ _)). 2: {
  rewrite List_length_map2, List.length_app, List.repeat_length.
  rewrite Nat.add_sub_assoc; [ | easy ].
  now rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
}
rewrite (rngl_subt_0_r Hsu).
easy.
Qed.

Theorem lap_opt_sub_add_distr :
  rngl_has_subt T = true →
  ∀ la lb lc : list T, (la - (lb + lc))%lap = (la - lb - lc)%lap.
Proof.
intros Hsu *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  move Hsu at bottom.
  unfold rngl_has_opp in Hop.
  unfold rngl_has_subt in Hsu.
  destruct rngl_opt_opp_or_subt; [ now destruct s | easy ].
}
move Hop after Hsu.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; right.
}
move Hos after Hed.
unfold lap_sub.
rewrite Hop, Hsu.
apply (lap_subt_add_distr Hsu).
Qed.

(* *)

Theorem lap_mul_opp_r :
  rngl_has_opp T = true →
  ∀ la lb, (la * - lb = - (la * lb))%lap.
Proof.
intros Hop *.
unfold lap_opp, lap_mul.
destruct la as [| a]; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
do 2 rewrite Nat.sub_0_r.
rewrite List.length_map.
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
    rewrite List.nth_overflow; [ | now rewrite List.length_map ].
    rewrite List.nth_overflow; [ | easy ].
    symmetry; apply (rngl_opp_0 Hop).
  }
  now rewrite (List_map_nth' 0%L).
}
rewrite <- (rngl_mul_opp_r Hop); f_equal.
destruct (i - S j) as [| k]; [ easy | ].
destruct (lt_dec k (length lb)) as [Hklb| Hklb]. 2: {
  apply Nat.nlt_ge in Hklb.
  rewrite List.nth_overflow; [ | now rewrite List.length_map ].
  rewrite List.nth_overflow; [ | easy ].
  symmetry; apply (rngl_opp_0 Hop).
}
now rewrite (List_map_nth' 0%L).
Qed.

Theorem lap_mul_sub_distr_l :
  rngl_has_opp T = true →
  ∀ la lb lc, (la * (lb - lc))%lap = (la * lb - la * lc)%lap.
Proof.
intros Hop *.
unfold lap_sub.
rewrite <- (lap_mul_opp_r Hop).
rewrite Hop.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
apply (lap_mul_add_distr_l Hed Hos).
Qed.

(* *)

Definition is_empty_list {A} (la : list A) :=
  match la with [] => true | _ => false end.
Definition has_polyn_prop {T} {ro : ring_like_op T} (la : list T) :=
  (is_empty_list la || (List.last la 0 ≠? 0)%L)%bool.

Theorem rlap_rem_prop : ∀ rla rlb rlq rlr,
  rlb ≠ []
  → rlap_quot_rem rla rlb = (rlq, rlr)
  → List.length rlr < List.length rlb.
Proof.
intros * Hbz Hqr.
unfold rlap_quot_rem in Hqr.
remember (rlap_quot_rem_nb_iter rla rlb) as it eqn:Hit.
unfold rlap_quot_rem_nb_iter in Hit.
assert (H : S (List.length rla) ≤ it) by flia Hit.
now apply rlap_rem_loop_prop in Hqr.
Qed.

Theorem lap_rem_length_lt :
  ∀ la lb lq lr : list T,
  lb ≠ []
  → has_polyn_prop lb = true
  → lap_quot_rem la lb = (lq, lr)
  → List.length lr < List.length lb.
Proof.
intros * Hbz Hbn Hab.
unfold lap_quot_rem in Hab.
remember (rlap_quot_rem (List.rev la) (List.rev lb)) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (rlq, rlr).
injection Hab; clear Hab; intros; subst lq lr.
apply rlap_rem_prop in Hqr. 2: {
  now intros H; apply List_eq_rev_nil in H.
}
rewrite List.length_rev in Hqr |-*.
eapply Nat.le_lt_trans; [ | apply Hqr ].
apply strip_0s_length_le.
Qed.

Theorem is_empty_list_empty : ∀ A (la : list A),
  is_empty_list la = true → la = [].
Proof.
intros * Ha.
unfold is_empty_list in Ha.
now destruct la.
Qed.

Theorem rlap_quot_prop :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ la lb lq lr,
  la = [] ∨ List.hd 0%L la ≠ 0%L
  → lb = [] ∨ List.hd 0%L lb ≠ 0%L
  → rlap_quot_rem la lb = (lq, lr)
  → lq = [] ∨ List.hd 0%L lq ≠ 0%L.
Proof.
intros Hon Hos Hiv * Ha Hb Hab.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hch| Hch]. {
  specialize (rngl_characteristic_1 Hon Hos Hch) as H1.
  destruct lq as [| q]; [ now left | right; cbn ].
  destruct Hb as [Hb| Hb]; [ now subst lb | ].
  destruct lb as [| b]; [ easy | cbn in Hb ].
  now specialize (H1 b).
}
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
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
apply rngl_inv_neq_0; [ easy | easy | easy | easy ].
Qed.

Theorem lap_convol_mul_1_l :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ la i len,
  List.length la = i + len
  → lap_convol_mul [1%L] la i len = List.skipn i la.
Proof.
intros Hon Hos * Hlen.
rewrite (lap_convol_mul_const_l Hos); [ | easy ].
erewrite List.map_ext_in. 2: {
  intros a Ha.
  now rewrite rngl_mul_1_l.
}
apply List.map_id.
Qed.

Theorem lap_convol_mul_l_succ_l :
  rngl_has_opp_or_subt T = true →
  ∀ la lb i len,
  lap_convol_mul (0%L :: la) lb (S i) len =
  lap_convol_mul la lb i len.
Proof.
intros Hos *.
revert la lb i.
induction len; intros; [ easy | cbn ].
rewrite rngl_summation_split_first; [ | easy ].
rewrite rngl_summation_shift with (s := 1); [ | flia ].
rewrite Nat.sub_diag, Nat_sub_succ_1.
rewrite (rngl_mul_0_l Hos), rngl_add_0_l.
f_equal.
apply IHlen.
Qed.

Definition lap_x_power n := List.repeat 0%L n ++ [1%L].

Theorem lap_repeat_0_app_is_mul_power_l :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ n la,
  la ≠ []
  → List.repeat 0%L n ++ la = (lap_x_power n * la)%lap.
Proof.
intros Hon Hos * Haz.
revert la Haz.
induction n; intros. {
  destruct la as [| a]; [ easy | clear Haz; cbn ].
  rewrite rngl_summation_only_one.
  rewrite (rngl_mul_1_l Hon); f_equal.
  now rewrite (lap_convol_mul_1_l Hon Hos).
}
cbn.
destruct la as [| a]; [ easy | clear Haz ].
rewrite List.length_app, List.repeat_length; cbn.
rewrite Nat.sub_0_r, Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos); f_equal.
rewrite (lap_convol_mul_l_succ_l Hos).
rewrite IHn; [ | easy ].
destruct n; [ easy | cbn ].
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos).
rewrite Nat.sub_0_r.
rewrite List.length_app, List.repeat_length; cbn.
rewrite (lap_convol_mul_l_succ_l Hos).
rewrite Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos); f_equal.
apply (lap_convol_mul_l_succ_l Hos).
Qed.

Theorem lap_convol_mul_1_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ la i len,
  List.length la = i + len
  → lap_convol_mul la [1%L] i len = List.skipn i la.
Proof.
intros Hon Hos * Hlen.
rewrite (lap_convol_mul_const_r Hos); [ | easy ].
erewrite List.map_ext_in. 2: {
  intros a Ha.
  now rewrite rngl_mul_1_r.
}
apply List.map_id.
Qed.

Theorem lap_convol_mul_r_succ_l :
  rngl_has_opp_or_subt T = true →
  ∀ la lb i len,
  lap_convol_mul la (0%L :: lb) (S i) len =
  lap_convol_mul la lb i len.
Proof.
intros Hos *.
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

Theorem lap_repeat_0_app_is_mul_power_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ n la,
  la ≠ []
  → List.repeat 0%L n ++ la = (la * lap_x_power n)%lap.
Proof.
intros Hon Hos * Haz.
revert la Haz.
induction n; intros. {
  destruct la as [| a]; [ easy | clear Haz; cbn ].
  rewrite Nat.sub_0_r, Nat.add_1_r; cbn.
  rewrite rngl_summation_only_one.
  rewrite (rngl_mul_1_r Hon); f_equal.
  now rewrite (lap_convol_mul_1_r Hon Hos).
}
cbn.
destruct la as [| a]; [ easy | clear Haz ].
cbn.
rewrite List.length_app, List.repeat_length, Nat.sub_0_r; cbn.
rewrite Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_r Hos); f_equal.
rewrite IHn; [ | easy ].
rewrite (lap_convol_mul_r_succ_l Hos).
cbn.
destruct n; cbn; [ now rewrite Nat.sub_0_r | ].
now rewrite List.length_app, List.repeat_length, Nat.sub_0_r.
Qed.

Theorem lap_add_repeat_0_l : ∀ la len,
  len ≤ List.length la
  → (List.repeat 0%L len + la = la)%lap.
Proof.
intros * Hlen.
revert len Hlen.
induction la as [| a]; intros. {
  now apply Nat.le_0_r in Hlen; subst len.
}
cbn.
destruct len. {
  cbn - [ lap_add ].
  now rewrite lap_add_0_l.
}
cbn.
cbn in Hlen; apply Nat.succ_le_mono in Hlen.
rewrite rngl_add_0_l; f_equal.
now apply IHla.
Qed.

Theorem lap_add_repeat_0_r : ∀ la len,
  len ≤ List.length la
  → (la + List.repeat 0%L len = la)%lap.
Proof.
intros * Hlen.
rewrite lap_add_comm.
now apply lap_add_repeat_0_l.
Qed.

Theorem lap_add_app_app :
  ∀ la lb lc ld,
  List.length la = List.length lb
  → ((la ++ lc) + (lb ++ ld))%lap = (la + lb)%lap ++ (lc + ld)%lap.
Proof.
intros * Hab.
revert lb lc ld Hab.
induction la as [| a]; intros. {
  now symmetry in Hab; apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | ].
cbn in Hab.
apply Nat.succ_inj in Hab.
cbn; f_equal.
now apply IHla.
Qed.

Theorem rev_lap_add : ∀ la lb,
  List.length la = List.length lb
  → (List.rev (la + lb) = List.rev la + List.rev lb)%lap.
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros. {
  cbn - [ lap_add ].
  now do 2 rewrite lap_add_0_l.
}
cbn.
destruct lb as [| b]; [ easy | ].
cbn in Hab |-*.
apply Nat.succ_inj in Hab.
do 2 rewrite fold_lap_add.
rewrite IHla; [ | easy ].
rewrite lap_add_app_app; [ easy | ].
now do 2 rewrite List.length_rev.
Qed.

Theorem lap_add_norm : ∀ la lb,
  (la + lb)%lap =
    ((la ++ List.repeat 0%L (List.length lb - List.length la)) +
     (lb ++ List.repeat 0%L (List.length la - List.length lb)))%lap.
Proof.
intros.
revert lb.
induction la as [| a]; intros. {
  cbn; rewrite Nat.sub_0_r, List.app_nil_r.
  rewrite fold_lap_add.
  rewrite List_map2_rngl_add_0_l.
  now symmetry; apply lap_add_repeat_0_l.
}
cbn.
destruct lb as [| b]. {
  cbn; rewrite List.app_nil_r, rngl_add_0_r; f_equal.
  rewrite fold_lap_add.
  rewrite List_map2_rngl_add_0_r.
  now symmetry; apply lap_add_repeat_0_r.
}
cbn; f_equal.
apply IHla.
Qed.

Theorem rev_lap_add_norm : ∀ la lb,
  List.rev (la + lb)%lap =
    ((List.repeat 0%L (List.length lb - List.length la) ++ List.rev la) +
     (List.repeat 0%L (List.length la - List.length lb) ++ List.rev lb))%lap.
Proof.
intros.
rewrite <- (List.rev_repeat (List.length lb - _)).
rewrite <- (List.rev_repeat (List.length la - _)).
do 2 rewrite <- List.rev_app_distr.
rewrite lap_add_norm.
apply rev_lap_add.
do 2 rewrite List.length_app, List.repeat_length.
destruct (le_dec (List.length lb) (List.length la)) as [Hab| Hab]. {
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

Theorem lap_opp_app_distr : ∀ la lb,
  (- (la ++ lb) = (- la) ++ (- lb))%lap.
Proof.
intros.
unfold lap_opp.
now rewrite List.map_app.
Qed.

Theorem rev_lap_opp : ∀ la, (List.rev (- la) = - List.rev la)%lap.
Proof.
intros.
unfold lap_opp.
now rewrite List.map_rev.
Qed.

Theorem map_opp_repeat : ∀ (x : T) n,
  List.map rngl_opp (List.repeat x n) = List.repeat (rngl_opp x) n.
Proof.
intros.
induction n; [ easy | cbn ].
f_equal; apply IHn.
Qed.

Theorem rev_lap_sub : ∀ la lb,
  List.length la = List.length lb
  → (List.rev (la - lb) = List.rev la - List.rev lb)%lap.
Proof.
intros * Hab.
unfold lap_sub.
destruct rngl_has_opp. {
  rewrite rev_lap_add; [ | now rewrite lap_opp_length ].
  now rewrite rev_lap_opp.
}
destruct rngl_has_subt. 2: {
  do 2 rewrite List.length_rev.
  now rewrite List.rev_repeat.
}
revert lb Hab.
induction la as [| a]; intros; cbn. {
  now symmetry in Hab; apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | cbn ].
cbn in Hab; apply Nat.succ_inj in Hab.
do 2 rewrite fold_lap_subt.
rewrite IHla; [ | easy ].
clear IHla.
rewrite <- (List.length_rev la) in Hab.
rewrite <- (List.length_rev lb) in Hab.
remember (List.rev la) as lc.
remember (List.rev lb) as ld.
clear la lb Heqlc Heqld.
rename lc into la; rename ld into lb.
revert lb Hab.
induction la as [| a']; intros; cbn. {
  now symmetry in Hab; apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b']; [ easy | cbn ].
cbn in Hab; apply Nat.succ_inj in Hab.
now f_equal; apply IHla.
Qed.

Theorem lap_add_app_l : ∀ la lb lc,
  List.length lc ≤ List.length la
  → (((la ++ lb) + lc) = (la + lc) ++ lb)%lap.
Proof.
intros * Hca.
revert lb lc Hca.
induction la as [| a]; intros; cbn. {
  apply Nat.le_0_r, List.length_zero_iff_nil in Hca; subst lc.
  cbn.
  rewrite List.app_nil_r, Nat.sub_0_r.
  apply List_map2_rngl_add_0_r.
}
destruct lc as [| c]. {
  cbn.
  now do 2 rewrite List.app_nil_r, List_map2_rngl_add_0_r.
}
cbn.
cbn in Hca |-*; f_equal.
apply Nat.succ_le_mono in Hca.
now apply IHla.
Qed.

Theorem lap_add_opp_diag_l :
  rngl_has_opp T = true
  → ∀ la, (- la + la)%lap = List.repeat 0%L (List.length la).
Proof.
intros Hop *.
induction la as [| a]; [ easy | cbn ].
rewrite (rngl_add_opp_diag_l Hop).
now f_equal.
Qed.

Theorem lap_sub_add :
  rngl_has_opp T = true →
  ∀ la lb,
  List.length lb ≤ List.length la
  → (la - lb + lb = la)%lap.
Proof.
intros Hop * Hba.
unfold lap_sub.
rewrite Hop.
rewrite <- lap_add_assoc.
rewrite (lap_add_opp_diag_l Hop).
revert lb Hba.
induction la as [| a]; intros; cbn. {
  now apply Nat.le_0_r, List.length_zero_iff_nil in Hba; subst lb.
}
destruct lb as [| b]. {
  rewrite List.app_nil_l, List.repeat_length; cbn.
  rewrite rngl_add_0_r, List.app_nil_r.
  now rewrite List_map2_rngl_add_0_r.
}
cbn in Hba |-*; apply Nat.succ_le_mono in Hba.
rewrite rngl_add_0_r; f_equal.
now apply IHla.
Qed.

Theorem rev_lap_sub_norm :
  rngl_has_opp_or_subt T = true →
  ∀ la lb,
  List.rev (la - lb)%lap =
    ((List.repeat 0%L (List.length lb - List.length la) ++ List.rev la) -
     (List.repeat 0%L (List.length la - List.length lb) ++ List.rev lb))%lap.
Proof.
intros Hos *.
unfold lap_sub.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  rewrite rev_lap_add_norm.
  rewrite lap_opp_length.
  f_equal.
  rewrite lap_opp_app_distr.
  rewrite rev_lap_opp.
  f_equal.
  unfold lap_opp.
  rewrite map_opp_repeat.
  now rewrite rngl_opp_0.
}
remember (rngl_has_subt T) as su eqn:Hsu.
symmetry in Hsu.
destruct su. {
  progress unfold lap_subt.
  rewrite List_rev_map2. 2: {
    do 2 rewrite List.length_app.
    do 2 rewrite List.repeat_length.
    flia.
  }
  do 2 rewrite List.length_app.
  do 2 rewrite List.repeat_length.
  do 2 rewrite List.length_rev.
  do 2 rewrite Nat.sub_add_distr.
  do 2 rewrite List.rev_app_distr.
  do 2 rewrite List.rev_repeat.
  progress replace (_ - _ + _ - _ - _) with 0 by flia.
  progress replace (_ - _ + _ - _ - _) with 0 by flia.
  cbn.
  do 2 rewrite List.app_nil_r.
  easy.
}
apply rngl_has_opp_or_subt_iff in Hos.
rewrite Hop, Hsu in Hos.
now destruct Hos.
Qed.

Theorem rlap_quot_rem_step_Some :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ rla rlb rlr cq,
  List.hd 0%L rlb ≠ 0%L
  → rlap_quot_rem_step rla rlb = (Some cq, rlr)
  → List.rev rla =
      (List.rev rlb *
         List.rev
           (cq :: List.repeat 0%L (List.length rla - List.length rlb)) +
       List.rev rlr)%lap ∧
    List.length rla = S (List.length rlr) ∧
    cq = (List.hd 0 rla / List.hd 0 rlb)%L.
Proof.
intros Hon Hic Hop Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hbz Hrl.
destruct rlb as [| b]; [ easy | cbn in Hbz, Hrl ].
destruct rla as [| a]; [ easy | ].
rewrite if_bool_if_dec in Hrl.
destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]; [ easy | ].
apply Nat.ltb_ge in Hab.
injection Hrl; clear Hrl; intros H1 H2; subst cq rlr.
remember (a / b)%L as cq eqn:Hcq.
move b before a.
cbn; rewrite List.rev_repeat.
rewrite (lap_repeat_0_app_is_mul_power_l Hon Hos); [ | easy ].
rewrite (lap_mul_assoc Hed Hos); cbn.
rewrite <- (lap_repeat_0_app_is_mul_power_r Hon Hos). 2: {
  now intros H; apply List.app_eq_nil in H.
}
rewrite (lap_mul_const_r Hos).
do 2 rewrite List.map_app; cbn.
rewrite List.map_repeat.
rewrite (rngl_mul_0_l Hos).
rewrite List.map_rev.
replace (b * cq)%L with (b * (a / b))%L by now rewrite Hcq.
rewrite <- List.rev_repeat at 1.
rewrite List.app_assoc.
rewrite <- List.rev_app_distr.
remember (List.map _ _ ++ List.repeat _ _) as rlc eqn:Hrlc.
rewrite rev_lap_sub_norm; [ | easy ].
rewrite List.length_map.
remember (List.repeat _ _ ++ _) as x.
rewrite <- List.rev_repeat.
rewrite <- List.rev_app_distr.
rewrite <- Hrlc.
subst x.
rewrite (proj2 (Nat.sub_0_le _ _)); [ cbn | easy ].
assert (Hca : List.length rlc = List.length rla). {
  rewrite Hrlc, List.length_app, List.length_map, List.repeat_length.
  now rewrite Nat.add_comm, Nat.sub_add.
}
rewrite <- rev_lap_sub; [ | easy ].
rewrite lap_add_app_l. 2: {
  do 2 rewrite List.length_rev.
  rewrite lap_sub_length.
  now rewrite Hca, Nat.max_id.
}
rewrite lap_sub_length, List.length_map.
rewrite Nat.max_l; [ | easy ].
split; [ | easy ].
rewrite (rngl_mul_comm Hic b).
rewrite (rngl_div_mul Hon Hiv _ _ Hbz).
f_equal.
specialize (strip_0s_length_le (rla - rlc)%lap) as Hrac.
remember (rla - rlc)%lap as rlac eqn:Hrlac.
symmetry in Hrlac.
rewrite <- Hrlac.
rewrite rev_lap_sub; [ | easy ].
rewrite lap_add_comm.
symmetry.
apply (lap_sub_add Hop).
do 2 rewrite List.length_rev.
now rewrite Hca.
Qed.

Theorem rlap_quot_rem_length :
  ∀ {it} {rla rlb : list T} rlq rlr,
  List.hd 0%L rlb ≠ 0%L
  → rlap_quot_rem_loop it rla rlb = (rlq, rlr)
  → S (List.length rla) ≤ it
  → List.length rlq = List.length rla - (List.length rlb - 1).
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
destruct (le_dec (List.length rlb) (List.length rlr')) as [Hrr| Hrr]. {
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

Theorem lap_add_app_r : ∀ la lb lc,
  List.length la ≤ List.length lb
  → (la + (lb ++ lc) = (la + lb) ++ lc)%lap.
Proof.
intros * Hab.
revert lb lc Hab.
induction la as [| a]; intros; [ now do 2 rewrite lap_add_0_l | cbn ].
destruct lb as [| b]; [ easy | cbn ].
cbn in Hab; apply Nat.succ_le_mono in Hab.
f_equal.
now apply IHla.
Qed.

Theorem rlap_quot_rem_loop_prop :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ it (rla rlb rlq rlr : list T),
  List.hd 0%L rlb ≠ 0%L
  → rlap_quot_rem_loop it rla rlb = (rlq, rlr)
  → S (List.length rla) ≤ it
  → List.rev rla = (List.rev rlb * List.rev rlq + List.rev rlr)%lap.
Proof.
intros Hon Hco Hop Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hbn Hqr Hit.
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
  destruct (List.length rla <? List.length rlb); [ | easy ].
  now injection Hqrlr.
}
generalize Hqrlr; intros Hqrlr'.
apply (rlap_quot_rem_step_Some Hon Hco Hop Hiv) in Hqrlr'; [ | easy ].
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
  apply Nat.le_succ_l.
  destruct rlb as [| b]; [ easy | ].
  cbn in Hqrlr.
  destruct rla as [| a]; [ easy | ].
  rewrite if_bool_if_dec in Hqrlr.
  destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]; [ easy | ].
  apply Nat.ltb_ge in Hab.
  injection Hqrlr; clear Hqrlr; intros; subst cq rlr.
  rewrite lap_sub_length.
  now cbn; rewrite List.length_map, Nat.max_l.
}
rewrite Hqrlr', Hqr.
rewrite lap_add_assoc.
f_equal; cbn.
rewrite List.rev_repeat.
rewrite <- (lap_mul_add_distr_l Hed Hos).
f_equal.
rewrite lap_add_comm.
rewrite lap_add_app_r; cycle 1. {
  rewrite List.length_rev, List.repeat_length.
  flia Hra Hqrb.
}
f_equal.
apply lap_add_repeat_0_r.
rewrite List.length_rev.
rewrite Hra, Hqrb.
destruct rlb as [| b]; [ easy | ].
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem all_0_all_rev_0 : ∀ A (d a : A) la,
  (∀ i, i < List.length la → List.nth i la d = a)
  ↔ (∀ i, i < List.length la → List.nth i (List.rev la) d = a).
Proof.
intros *.
split; intros H i Hi. {
  rewrite List.rev_nth; [ apply H | easy ].
  now apply Nat.sub_lt.
} {
  rewrite <- (List.rev_involutive la).
  rewrite List.rev_nth; [ apply H | now rewrite List.length_rev ].
  rewrite List.length_rev.
  now apply Nat.sub_lt.
}
Qed.

Theorem eq_strip_0s_nil : ∀ d la,
  strip_0s la = [] ↔ ∀ i, i < length la → List.nth i la d = 0%L.
Proof.
intros.
split. {
  intros Hla * Hil.
  revert i Hil.
  induction la as [| a]; intros; [ now destruct i | cbn ].
  cbn in Hla.
  rewrite if_bool_if_dec in Hla.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ | easy ].
  apply (rngl_eqb_eq Hed) in Haz.
  destruct i; [ easy | cbn in Hil ].
  apply Nat.succ_lt_mono in Hil.
  now apply IHla.
} {
  intros Hla.
  induction la as [| a]; [ easy | cbn ].
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    apply IHla.
    intros i Hil.
    apply Nat.succ_le_mono in Hil.
    apply (Hla (S i) Hil).
  }
  apply (rngl_eqb_neq Hed) in Haz.
  now specialize (Hla 0 (Nat.lt_0_succ _)).
}
Qed.

Theorem eq_strip_0s_rev_nil : ∀ la,
  strip_0s (List.rev la) = [] ↔
    ∀ i, i < List.length la → List.nth i la 0%L = 0%L.
Proof.
intros.
split; intros Hla. {
  apply all_0_all_rev_0.
  rewrite <- List.length_rev.
  now apply (eq_strip_0s_nil 0%L).
} {
  apply (eq_strip_0s_nil 0%L).
  apply all_0_all_rev_0.
  now rewrite List.length_rev, List.rev_involutive.
}
Qed.

Theorem lap_add_rev_strip : ∀ la lb,
  List.length lb ≤ List.length la
  → (la + List.rev (strip_0s lb) = la + List.rev lb)%lap.
Proof.
intros * Hba.
revert lb Hba.
induction la as [| a]; intros. {
  now apply Nat.le_0_r, List.length_zero_iff_nil in Hba; subst lb.
}
cbn.
remember (List.rev lb) as lc eqn:Hlc; symmetry in Hlc.
apply List_rev_symm in Hlc; subst lb.
destruct lc as [| c]; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (List.rev lc)) as lb eqn:Hlb; symmetry in Hlb.
rewrite List.length_rev in Hba; cbn in Hba.
apply Nat.succ_le_mono in Hba.
destruct lb as [| b]. {
  cbn.
  rewrite List.length_rev.
  specialize (proj1 (eq_strip_0s_rev_nil _) Hlb) as H1.
  clear Hlb IHla.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
    apply (rngl_eqb_eq Hed) in Hcz; subst c; cbn.
    rewrite List.app_nil_r; f_equal.
    rewrite List_map2_rngl_add_0_r.
    rewrite fold_lap_add; symmetry.
    clear a.
    revert la Hba.
    induction lc as [| c]; intros; [ apply lap_add_0_r | cbn ].
    destruct la as [| a]; [ easy | ].
    cbn in Hba.
    apply Nat.succ_le_mono in Hba.
    specialize (H1 0 (Nat.lt_0_succ _)) as H2; cbn in H2.
    subst c; cbn; rewrite rngl_add_0_r; f_equal.
    apply IHlc; [ | easy ].
    intros i Hi.
    apply Nat.succ_lt_mono in Hi.
    specialize (H1 (S i) Hi).
    apply H1.
  } {
    cbn; f_equal; clear c Hcz.
    rewrite List.app_nil_r, Nat.sub_0_r.
    rewrite List_map2_rngl_add_0_r, fold_lap_add.
    symmetry.
    clear a.
    revert la Hba.
    induction lc as [| c]; intros; [ apply lap_add_0_r | cbn ].
    destruct la as [| a]; [ easy | ].
    cbn in Hba.
    apply Nat.succ_le_mono in Hba.
    specialize (H1 0 (Nat.lt_0_succ _)) as H2; cbn in H2.
    subst c; cbn; rewrite rngl_add_0_r; f_equal.
    apply IHlc; [ | easy ].
    intros i Hi.
    apply Nat.succ_lt_mono in Hi.
    now specialize (H1 (S i) Hi).
  }
}
rewrite <- Hlb.
rewrite List.rev_app_distr; cbn; f_equal.
do 2 rewrite fold_lap_add.
rewrite IHla; [ | now rewrite List.length_rev ].
now rewrite List.rev_involutive.
Qed.

Theorem lap_div_mod :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ la lb lq lr : list T,
  has_polyn_prop la = true
  → List.last lb 0%L ≠ 0%L
  → has_polyn_prop lr = true
  → lap_quot_rem la lb = (lq, lr)
  → la = (lb * lq + lr)%lap ∧
    List.length lr < List.length lb ∧
    has_polyn_prop lq = true.
Proof.
intros Hon Hco Hop Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Ha Hb Hr Hab.
assert (Hrb : List.length lr < List.length lb). {
  eapply lap_rem_length_lt; [ | | apply Hab ]. {
    now intros H; subst lb.
  } {
    unfold has_polyn_prop.
    apply (rngl_eqb_neq Hed) in Hb.
    now rewrite Hb, Bool.orb_true_r.
  }
}
rewrite and_comm, and_assoc.
split; [ easy | ].
rewrite and_comm.
assert (Hbz : List.hd 0%L (List.rev lb) ≠ 0%L). {
  remember (List.rev lb) as lc eqn:Hlc; symmetry in Hlc.
  apply List_rev_symm in Hlc; subst lb.
  destruct lc as [| c]; [ easy | ].
  cbn in Hb.
  now rewrite List.last_last in Hb.
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
  apply (rlap_quot_prop Hon Hos Hiv) in Hqr'; cycle 1. {
    unfold has_polyn_prop in Ha.
    apply Bool.orb_true_iff in Ha.
    destruct Ha as [Ha| Ha]. {
      apply is_empty_list_empty in Ha; subst la.
      now left.
    }
    right.
    apply (rngl_neqb_neq Hed) in Ha.
    now rewrite <- List_last_rev, List.rev_involutive.
  } {
    right.
    now rewrite <- List_last_rev, List.rev_involutive.
  }
  specialize (rlap_quot_rem_loop_prop Hon Hco Hop Hiv) as H1.
  specialize (H1 (S (List.length (List.rev la)))).
  specialize (H1 (List.rev la) (List.rev lb) rlq rlr).
  specialize (H1 Hbz Hqr (Nat.le_refl _)).
  do 2 rewrite List.rev_involutive in H1.
  destruct Hqr' as [Hqr'| Hqr']. {
    subst rlq.
    cbn in H1 |-*.
    rewrite lap_mul_0_r.
    rewrite lap_mul_0_r, lap_add_0_l in H1.
    symmetry in H1; apply List_rev_symm in H1; subst rlr.
    apply Bool.orb_true_iff in Ha.
    destruct Ha as [Ha| Ha]. {
      now apply is_empty_list_empty in Ha.
    }
    destruct la as [| a] using List.rev_ind; [ easy | ].
    rewrite List.last_last in Ha.
    rewrite List.rev_app_distr in Hr; cbn in Hr.
    apply Bool.negb_true_iff in Ha.
    now rewrite Ha in Hr.
  }
  rewrite <- lap_add_rev_strip in H1. {
    rewrite Hr in H1.
    cbn in H1.
    rewrite lap_add_0_r in H1.
    split; [ easy | ].
    apply Bool.orb_true_iff; right.
    rewrite List_last_rev.
    now apply (rngl_neqb_neq Hed).
  }
  rewrite lap_mul_length.
  destruct lb as [| b]; [ easy | ].
  remember (List.rev rlq) as lq eqn:Hlq; symmetry in Hlq.
  destruct lq as [| q]. {
    now apply List_eq_rev_nil in Hlq; subst rlq.
  }
  apply rlap_rem_prop in Hqr. 2: {
    intros H.
    now apply List_eq_rev_nil in H.
  }
  cbn.
  rewrite List.length_rev in Hqr; cbn in Hqr; flia Hqr.
}
unfold lap_quot_rem in Hab.
remember (rlap_quot_rem _ _) as qr eqn:Hqr; symmetry in Hqr.
destruct qr as (rlq, rlr).
injection Hab; clear Hab; intros; subst lq lr.
specialize (rlap_quot_rem_loop_prop Hon Hco Hop Hiv) as H1.
specialize (H1 (S (List.length (List.rev la)))).
specialize (H1 (List.rev la) (List.rev lb) rlq rlr).
specialize (H1 Hbz Hqr (Nat.le_refl _)).
do 2 rewrite List.rev_involutive in H1.
rewrite List.length_rev in Hrb.
remember (List.rev rlq) as lq eqn:Hlq; symmetry in Hlq.
destruct lq as [| q]. {
  split; [ | easy ].
  rewrite lap_mul_0_r, lap_add_0_l in H1.
  rewrite lap_mul_0_r, lap_add_0_l.
  rewrite H1; f_equal; symmetry.
  destruct rlr as [| r]; [ easy | ].
  cbn in Hr |-*.
  rewrite if_bool_if_dec in Hr |-*.
  destruct (Sumbool.sumbool_of_bool _) as [Hrz| Hrz]; [ | easy ].
  apply (rngl_eqb_eq Hed) in Hrz.
  subst r.
  cbn in H1.
  apply Bool.orb_true_iff in Ha.
  destruct Ha as [Ha| Ha]. {
    apply is_empty_list_empty in Ha; subst la.
    now symmetry in H1; apply List.app_eq_nil in H1.
  }
  rewrite H1 in Ha.
  rewrite List.last_last in Ha.
  now apply rngl_neqb_neq in Ha.
}
rewrite lap_add_rev_strip. {
  split; [ easy | ].
  apply Bool.orb_true_iff; right.
  rewrite <- Hlq, List_last_rev.
  apply (rngl_neqb_neq Hed).
  apply (rlap_quot_prop Hon Hos Hiv) in Hqr; [ | | now right ]. 2: {
    apply Bool.orb_true_iff in Ha.
    destruct Ha as [Ha| Ha]. {
      apply is_empty_list_empty in Ha; subst la.
      now left.
    }
    right.
    rewrite <- List_last_rev, List.rev_involutive.
    now apply (rngl_neqb_neq Hed) in Ha.
  }
  destruct Hqr as [Hqr| Hqr]; [ now subst rlq | easy ].
}
rewrite lap_mul_length.
destruct lb as [| b]; [ easy | ].
cbn.
apply rlap_rem_prop in Hqr. 2: {
  intros H.
  now apply List_eq_rev_nil in H.
}
rewrite List.length_rev in Hqr; cbn in Hqr; flia Hqr.
Qed.

End a.

Arguments lap_quot_rem {T ro} (la lb)%_lap.
