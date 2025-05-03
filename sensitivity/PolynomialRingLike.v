(* PolynomialRingLike.v *)

(* polynomials on a RingLike *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
Import List.ListNotations Init.Nat.

Require Import RingLike.RingLike.
Require Import RingLike.IterAdd.
Require Import RingLike.LapRingLike.

Require Import Misc.
Require Import LapPolyn.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hos : rngl_has_opp_or_subt T = true).
Context (Hed : rngl_has_eq_dec T = true).

Theorem eq_strip_0s_cons : ∀ la lb b,
  strip_0s la = b :: lb
  → b ≠ 0%L ∧
    ∃ i,
    i < length la ∧
    (∀ j, j < i → List.nth j la 0%L = 0%L) ∧
    List.nth i la 0%L = b.
Proof.
intros * Hab.
induction la as [| a]; [ easy | ].
cbn in Hab.
rewrite if_bool_if_dec in Hab.
destruct (Sumbool.sumbool_of_bool (a =? 0)%L) as [Haz| Haz]. {
  apply (rngl_eqb_eq Hed) in Haz; subst a.
  specialize (IHla Hab).
  destruct IHla as (Hbz & i & Hil & Hbef & Hi).
  split; [ easy | ].
  exists (S i).
  cbn - [ List.nth ].
  split; [ now apply -> Nat.succ_lt_mono | ].
  split; [ | easy ].
  intros j Hj.
  destruct j; [ easy | cbn ].
  apply Nat.succ_lt_mono in Hj.
  now apply Hbef.
}
injection Hab; clear Hab; intros; subst b lb.
apply (rngl_eqb_neq Hed) in Haz.
split; [ easy | ].
exists 0.
now cbn.
Qed.

Theorem polyn_norm_prop : ∀ la, has_polyn_prop (lap_norm la) = true.
Proof.
intros.
unfold has_polyn_prop, lap_norm.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; cbn. {
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ easy | cbn ].
  now apply Bool.negb_true_iff.
}
cbn in IHla.
rewrite List.last_last in IHla.
apply Bool.orb_true_iff in IHla.
apply Bool.orb_true_iff; right.
rewrite List.last_last.
destruct IHla as [H1| H1]; [ | easy ].
apply is_empty_list_empty in H1.
now apply List.app_eq_nil in H1.
Qed.

Theorem all_0_lap_norm_nil : ∀ la,
  (∀ i, List.nth i la 0%L = 0%L)
  ↔ lap_norm la = [].
Proof.
intros *.
split; intros Hla. {
  induction la as [| a]; [ easy | cbn ].
  rewrite strip_0s_app.
  remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| b]. {
    cbn.
    rewrite if_bool_if_dec.
    destruct (Sumbool.sumbool_of_bool _) as [H1| H1]; [ easy | exfalso ].
    apply (rngl_eqb_neq Hed) in H1.
    now specialize (Hla 0); cbn in Hla.
  }
  exfalso.
  assert (H : strip_0s (List.rev la) = []). {
    clear - rp Hed Hla.
    apply (eq_strip_0s_nil Hed 0%L).
    intros i Hil.
    rewrite List.length_rev in Hil.
    rewrite List.rev_nth; [ | easy ].
    specialize (Hla (S (List.length la - S i))).
    now cbn in Hla.
  }
  now rewrite Hlb in H.
} {
  intros i.
  destruct (lt_dec i (List.length la)) as [Hila| Hila]. 2: {
    apply Nat.nlt_ge in Hila.
    now apply List.nth_overflow.
  }
  unfold lap_norm in Hla.
  apply List_eq_rev_nil in Hla.
  apply (eq_strip_0s_nil Hed 0%L) with (i := List.length la - S i) in Hla. {
    rewrite List.rev_nth in Hla; [ | flia Hila ].
    rewrite <- Nat_succ_sub_succ_r in Hla; [ | easy ].
    rewrite Nat_sub_sub_distr in Hla; [ | flia Hila ].
    now rewrite Nat.add_comm, Nat.add_sub in Hla.
  }
  now rewrite List.length_rev; apply Nat.sub_lt.
}
Qed.

Theorem lap_norm_app_repeat_0 : ∀ la,
  la =
    lap_norm la ++
    List.repeat 0%L (List.length la - List.length (lap_norm la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    apply (rngl_eqb_eq Hed) in Haz.
    cbn; subst a; f_equal.
    assert (H : lap_norm la = []). {
      apply all_0_lap_norm_nil.
      intros i.
      specialize (proj1 (eq_strip_0s_nil Hed 0%L _) Hlb) as H1.
      destruct (lt_dec i (List.length la)) as [Hila| Hila]. {
        rewrite <- (List.rev_involutive la).
        rewrite List.rev_nth; rewrite List.length_rev; [ | easy ].
        apply H1.
        now rewrite List.length_rev; apply Nat.sub_lt.
      }
      apply Nat.nlt_ge in Hila.
      now rewrite List.nth_overflow.
    }
    rewrite H in IHla; cbn in IHla.
    now rewrite Nat.sub_0_r in IHla.
  } {
    cbn; f_equal.
    assert (H : lap_norm la = []). {
      apply all_0_lap_norm_nil.
      intros i.
      specialize (proj1 (eq_strip_0s_nil Hed 0%L _) Hlb) as H1.
      destruct (lt_dec i (List.length la)) as [Hila| Hila]. {
        rewrite <- (List.rev_involutive la).
        rewrite List.rev_nth; rewrite List.length_rev; [ | easy ].
        apply H1.
        now rewrite List.length_rev; apply Nat.sub_lt.
      }
      apply Nat.nlt_ge in Hila.
      now rewrite List.nth_overflow.
    }
    now rewrite H in IHla; cbn in IHla.
  }
} {
  cbn.
  rewrite List.rev_app_distr; cbn; f_equal.
  replace (List.rev lb ++ [b]) with (List.rev (b :: lb)) by easy.
  rewrite <- Hlb.
  now rewrite fold_lap_norm.
}
Qed.

Theorem lap_norm_length_le : ∀ la, List.length (lap_norm la) ≤ List.length la.
Proof.
intros.
rewrite (lap_norm_app_repeat_0 la) at 2.
rewrite List.length_app; flia.
Qed.

Theorem lap_quot_is_norm :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → has_polyn_prop (lap_quot la lb) = true.
Proof.
intros Hon Hiv * Ha Hb.
unfold lap_quot.
remember (rlap_quot_rem (List.rev la) (List.rev lb)) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (rlq, rlr); cbn.
unfold has_polyn_prop.
apply Bool.orb_true_iff.
destruct rlq as [| q]; [ now left | right ].
cbn; rewrite List.last_last.
apply (rlap_quot_prop Hon Hos Hiv) in Hqr; cycle 1. {
  apply Bool.orb_true_iff in Ha.
  destruct Ha as [Ha| Ha]; [ now left; destruct la | right ].
  destruct la as [| a] using List.rev_ind. {
    cbn in Ha.
    now rewrite (rngl_eqb_refl Hed) in Ha.
  }
  rewrite List.last_last in Ha.
  rewrite List.rev_app_distr; cbn.
  now apply (rngl_neqb_neq Hed) in Ha.
} {
  unfold has_polyn_prop in Hb.
  apply Bool.orb_true_iff in Hb.
  destruct Hb as [Hb| Hb]; [ now left; destruct lb | right ].
  destruct lb as [| b] using List.rev_ind. {
    cbn in Hb.
    now rewrite (rngl_eqb_refl Hed) in Hb.
  }
  rewrite List.last_last in Hb.
  rewrite List.rev_app_distr; cbn.
  now apply (rngl_neqb_neq Hed) in Hb.
}
destruct Hqr as [Hqr| Hqr]; [ easy | ].
cbn in Hqr.
now apply (rngl_neqb_neq Hed).
Qed.

Theorem lap_rem_is_norm : ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → has_polyn_prop (lap_rem la lb) = true.
Proof.
intros * Ha Hb.
unfold lap_rem.
remember (rlap_quot_rem (List.rev la) (List.rev lb)) as qr eqn:Hqr.
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
  now apply (rngl_neqb_neq Hed).
}
right; cbn; rewrite List.last_last.
now rewrite Hrz.
Qed.

Theorem lap_add_norm_idemp_r : ∀ la lb,
  lap_norm (la + lap_norm lb) = lap_norm (la + lb).
Proof.
intros.
rewrite lap_add_comm.
rewrite (lap_add_norm_idemp_l Hed).
f_equal; apply lap_add_comm.
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
apply (rngl_neqb_neq Hed) in lapr.
destruct la as [| a] using List.rev_ind; [ easy | cbn ].
clear IHla.
rewrite List.last_last in lapr.
unfold lap_norm.
rewrite List.rev_app_distr; cbn.
apply (rngl_eqb_neq Hed) in lapr.
rewrite lapr; cbn.
now rewrite List.rev_involutive.
Qed.

Theorem lap_convol_mul_0_l : ∀ la lb i len,
  (∀ i, List.nth i la 0%L = 0%L)
  → lap_norm (lap_convol_mul la lb i len) = [].
Proof.
intros * Ha.
revert i.
induction len; intros; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (List.rev _)) as lc eqn:Hlc; symmetry in Hlc.
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
  (∀ i, List.nth i lb 0%L = 0%L)
  → lap_norm (lap_convol_mul la lb i len) = [].
Proof.
intros * Hb.
revert i.
induction len; intros; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (List.rev _)) as lc eqn:Hlc; symmetry in Hlc.
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
  (∀ i, List.nth i la 0%L = 0%L)
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

Theorem lap_convol_mul_app_rep_0_l : ∀ la lb i len n,
  lap_norm (lap_convol_mul (la ++ List.repeat 0%L n) lb i len) =
  lap_norm (lap_convol_mul la lb i len).
Proof.
intros.
revert la i len.
induction n; intros. {
  now cbn; rewrite List.app_nil_r.
}
cbn.
rewrite List_cons_is_app.
rewrite List.app_assoc.
rewrite IHn; clear n IHn.
revert la i.
induction len; intros; [ easy | ].
cbn.
do 2 rewrite strip_0s_app.
rewrite <- (List.rev_involutive (strip_0s _)).
rewrite fold_lap_norm.
rewrite <- (List.rev_involutive (strip_0s (List.rev _))).
rewrite fold_lap_norm.
rewrite IHlen.
remember (List.rev (lap_norm _)) as lc eqn:Hlc; symmetry in Hlc.
f_equal.
destruct lc as [| c]. {
  apply List_eq_rev_nil in Hlc.
  f_equal; f_equal.
  apply rngl_summation_eq_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec j (List.length la)) as [Hjla| Hjla]. {
    now rewrite List.app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (List.nth_overflow la); [ | easy ].
  rewrite List.app_nth2; [ | easy ].
  destruct (Nat.eq_dec j (List.length la)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite List.nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
} {
  f_equal; f_equal.
  apply rngl_summation_eq_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec j (List.length la)) as [Hjla| Hjla]. {
    now rewrite List.app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (List.nth_overflow la); [ | easy ].
  rewrite List.app_nth2; [ | easy ].
  destruct (Nat.eq_dec j (List.length la)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite List.nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
}
Qed.

Theorem lap_convol_mul_app_rep_0_r : ∀ la lb i len n,
  lap_norm (lap_convol_mul la (lb ++ List.repeat 0%L n) i len) =
  lap_norm (lap_convol_mul la lb i len).
Proof.
intros.
revert lb i len.
induction n; intros; [ now cbn; rewrite List.app_nil_r | cbn ].
rewrite List_cons_is_app.
rewrite List.app_assoc.
rewrite IHn; clear n IHn.
revert la i.
induction len; intros; [ easy | cbn ].
do 2 rewrite strip_0s_app.
rewrite <- (List.rev_involutive (strip_0s _)).
rewrite fold_lap_norm.
rewrite <- (List.rev_involutive (strip_0s (List.rev _))).
rewrite fold_lap_norm.
rewrite IHlen.
remember (List.rev (lap_norm _)) as lc eqn:Hlc; symmetry in Hlc.
f_equal.
destruct lc as [| c]. {
  apply List_eq_rev_nil in Hlc.
  f_equal; f_equal.
  apply rngl_summation_eq_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec (i - j) (List.length lb)) as [Hjla| Hjla]. {
    now rewrite List.app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (List.nth_overflow lb); [ | easy ].
  rewrite List.app_nth2; [ | easy ].
  destruct (Nat.eq_dec (i - j) (List.length lb)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite List.nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
} {
  f_equal; f_equal.
  apply rngl_summation_eq_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec (i - j) (List.length lb)) as [Hjla| Hjla]. {
    now rewrite List.app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (List.nth_overflow lb); [ | easy ].
  rewrite List.app_nth2; [ | easy ].
  destruct (Nat.eq_dec (i - j) (List.length lb)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite List.nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
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
  List.length (a :: la) + List.length lb - 1 ≤ i + len
  → lap_norm (lap_convol_mul (a :: lap_norm la) lb i len) =
    lap_norm (lap_convol_mul (a :: la) lb i len).
Proof.
intros * Hlen.
rewrite (lap_norm_app_repeat_0 la) at 2.
rewrite List.app_comm_cons.
now rewrite lap_convol_mul_app_rep_0_l.
Qed.

Theorem lap_mul_norm_idemp_l : ∀ la lb,
  lap_norm (lap_norm la * lb)%lap = lap_norm (la * lb)%lap.
Proof.
intros.
unfold "*"%lap; cbn.
destruct la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (List.rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    cbn.
    apply (rngl_eqb_eq Hed) in Haz.
    destruct lb as [| b]; [ easy | cbn ].
    rewrite lap_convol_mul_0_l; [ easy | ].
    intros i; cbn.
    destruct i; [ easy | ].
    specialize (proj1 (eq_strip_0s_nil Hed 0%L _) Hlc) as H1.
    destruct (lt_dec i (List.length la)) as [Hil| Hil]. {
      specialize (H1 (List.length la - S i)).
      rewrite List.length_rev in H1.
      assert (H : List.length la - S i < List.length la) by
        now apply Nat.sub_lt.
      specialize (H1 H); clear H.
      rewrite List.rev_nth in H1. {
        rewrite <- Nat_succ_sub_succ_r in H1; [ | easy ].
        rewrite Nat_sub_sub_distr in H1; [ | now apply Nat.lt_le_incl ].
        now rewrite Nat.add_comm, Nat.add_sub in H1.
      }
      now apply Nat.sub_lt.
    }
    apply Nat.nlt_ge in Hil.
    now rewrite List.nth_overflow.
  }
  cbn.
  destruct lb as [| b]; [ easy | ].
  remember (b :: lb) as ld eqn:Hld; symmetry in Hld.
  do 2 rewrite Nat.sub_0_r.
  rewrite fold_lap_norm.
  rewrite (lap_convol_mul_cons_with_0_l _ la). 2: {
    intros i.
    specialize (proj1 (eq_strip_0s_nil Hed 0%L _) Hlc) as H1.
    destruct (lt_dec i (List.length la)) as [Hil| Hil]. {
      specialize (H1 (List.length la - S i)).
      rewrite List.length_rev in H1.
      assert (H : List.length la - S i < List.length la) by
        now apply Nat.sub_lt.
      specialize (H1 H); clear H.
      rewrite List.rev_nth in H1. {
        rewrite <- Nat_succ_sub_succ_r in H1; [ | easy ].
        rewrite Nat_sub_sub_distr in H1; [ | now apply Nat.lt_le_incl ].
        now rewrite Nat.add_comm, Nat.add_sub in H1.
      }
      now apply Nat.sub_lt.
    }
    apply Nat.nlt_ge in Hil.
    now rewrite List.nth_overflow.
  }
  rewrite Nat.add_comm.
  apply (lap_convol_mul_more Hed Hos); cbn.
  now rewrite Nat.sub_0_r.
}
rewrite List.rev_app_distr; cbn.
rewrite fold_lap_norm.
destruct lb as [| b]; [ easy | ].
remember (b :: lb) as d eqn:Hd.
replace (List.rev lc ++ [c]) with (List.rev (c :: lc)) by easy.
rewrite <- Hlc.
rewrite fold_lap_norm.
do 2 rewrite Nat.sub_0_r.
clear c lc b lb Hlc Hd.
rename d into lb.
rewrite
  (lap_convol_mul_more Hed Hos (List.length la - List.length (lap_norm la))).
    2: {
  now cbn; rewrite Nat.sub_0_r.
}
rewrite (Nat.add_comm _ (List.length lb)).
rewrite <- Nat.add_assoc.
rewrite Nat.add_sub_assoc; [ | apply lap_norm_length_le ].
rewrite (Nat.add_comm _ (List.length la)).
rewrite Nat.add_sub.
rewrite Nat.add_comm.
apply lap_norm_cons_norm.
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem lap_mul_norm_idemp_r : ∀ la lb,
  lap_norm (la * lap_norm lb)%lap = lap_norm (la * lb)%lap.
Proof.
intros.
unfold "*"%lap; cbn.
destruct la as [| a]; [ easy | cbn ].
unfold lap_norm.
remember (strip_0s (List.rev lb)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  specialize (proj1 (eq_strip_0s_nil Hed 0%L _) Hlc) as H1.
  rewrite List.length_rev in H1.
  destruct lb as [| b]; [ easy | cbn ].
  rewrite fold_lap_norm.
  symmetry; apply lap_convol_mul_0_r.
  intros i.
  specialize (H1 (List.length lb - i)).
  rewrite List.rev_nth in H1; [ | cbn; flia ].
  cbn in H1.
  destruct (le_dec i (List.length lb)) as [Hib| Hib]. 2: {
    apply Nat.nle_gt in Hib.
    now rewrite List.nth_overflow.
  }
  assert (H : List.length lb - i < S (List.length lb)) by flia Hib.
  specialize (H1 H).
  now replace (List.length lb - (List.length lb - i)) with i in H1
    by flia Hib.
}
cbn.
rewrite fold_lap_norm.
destruct lb as [| b]; [ easy | ].
remember (b :: lb) as d eqn:Hd.
replace (List.rev lc ++ [c]) with (List.rev (c :: lc)) by easy.
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
  specialize (proj1 (eq_strip_0s_rev_nil Hed lb) Hlc) as H1.
  clear Hlc; rename H1 into Hlb.
  rewrite lap_convol_mul_0_r; [ easy | ].
  intros i.
  destruct (lt_dec i (List.length lb)) as [Hil| Hil]. 2: {
    apply Nat.nlt_ge in Hil.
    now apply List.nth_overflow.
  }
  now apply Hlb.
}
cbn.
rewrite fold_lap_norm.
rewrite
    (lap_convol_mul_more Hed Hos (List.length lb - S (List.length lc))).
    2: {
  now cbn; rewrite Nat.sub_0_r.
}
rewrite <- Nat.add_assoc.
rewrite (Nat.add_comm (S (List.length lc))).
rewrite Nat.sub_add. 2: {
  etransitivity; [ | apply lap_norm_length_le ].
  now rewrite Hlc.
}
rewrite <- Hlc.
apply lap_norm_convol_mul_norm_r.
Qed.

Theorem list_nth_lap_opp :
  rngl_has_opp T = true →
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
  rngl_has_opp T = true →
  ∀ k la lb,
  (List.nth k (lap_sub la lb) 0 =
   List.nth k la 0 - List.nth k lb 0)%L.
Proof.
intros Hop *.
unfold lap_sub.
rewrite Hop.
rewrite list_nth_lap_add.
rewrite (list_nth_lap_opp Hop).
now rewrite (rngl_add_opp_r Hop).
Qed.

Theorem lap_add_opp_diag_r :
  rngl_has_opp T = true
  → ∀ la, (la + - la)%lap = List.repeat 0%L (List.length la).
Proof.
intros Hop *.
clear Hos.
induction la as [| a]; [ easy | cbn ].
rewrite fold_lap_opp.
rewrite rngl_add_opp_r; [ | easy ].
rewrite rngl_sub_diag; [ | now apply rngl_has_opp_has_opp_or_subt ].
now f_equal.
Qed.

Theorem lap_norm_repeat_0 : ∀ n, lap_norm (List.repeat 0%L n) = [].
Proof.
intros.
unfold lap_norm.
rewrite List.rev_repeat.
induction n; [ easy | cbn ].
now rewrite (rngl_eqb_refl Hed).
Qed.

Theorem lap_norm_add_opp_diag_l :
  rngl_has_opp T = true
  → ∀ la, lap_norm (- la + la)%lap = [].
Proof.
intros Hop *.
rewrite (lap_add_opp_diag_l Hop).
apply lap_norm_repeat_0.
Qed.

(* *)

Theorem lap_subt_diag :
  ∀ la, lap_subt la la = List.repeat 0%L (List.length la).
Proof.
intros.
unfold lap_subt.
rewrite Nat.sub_diag, List.app_nil_r.
induction la as [| a]; [ easy | cbn ].
rewrite IHla; f_equal.
apply (rngl_subt_diag Hos).
Qed.

Theorem lap_add_sub :
  ∀ la lb,
  (la + lb - lb)%lap =
    la ++ List.repeat 0%L (List.length lb - List.length la).
Proof.
intros.
unfold lap_sub.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
destruct op. {
rewrite <- lap_add_assoc.
rewrite (lap_add_opp_diag_r Hop).
destruct (le_dec (List.length lb) (List.length la)) as [Hlba| Hlba]. {
  rewrite lap_add_repeat_0_r; [ | easy ].
  rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
  symmetry; apply List.app_nil_r.
}
apply Nat.nle_gt in Hlba.
replace (List.length lb) with
  (List.length la + (List.length lb - List.length la)) at 1 by flia Hlba.
rewrite List.repeat_app.
rewrite lap_add_app_r; [ | now rewrite List.repeat_length ].
f_equal.
now apply lap_add_repeat_0_r.
}
remember (rngl_has_subt T) as su eqn:Hsu; symmetry in Hsu.
destruct su. {
  revert lb.
  induction la as [| a]; intros. {
    rewrite lap_add_0_l, List.app_nil_l, Nat.sub_0_r.
    apply lap_subt_diag.
  }
  destruct lb as [| b]. {
    cbn - [ lap_subt ].
    rewrite rngl_add_0_r, List.app_nil_r.
    rewrite List_map2_rngl_add_0_r.
    apply (lap_subt_0_r Hsu).
  }
  cbn.
  rewrite fold_lap_add, fold_lap_subt.
  rewrite IHla; f_equal.
  specialize (rngl_add_sub Hos a b) as H1.
  unfold rngl_sub in H1.
  now rewrite Hop, Hsu in H1.
}
apply rngl_has_opp_or_subt_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem lap_add_move_l :
  ∀ la lb lc : list T,
  (la + lb)%lap = lc
  → lb ++ List.repeat 0%L (List.length la - List.length lb) = (lc - la)%lap.
Proof.
intros * Hab.
subst lc.
symmetry; rewrite lap_add_comm.
now rewrite lap_add_sub.
Qed.

Theorem lap_mul_has_polyn_prop :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → has_polyn_prop (la * lb)%lap = true.
Proof.
intros Hon Hiv * Ha Hb.
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
apply (rngl_neqb_neq Hed) in Ha, Hb.
apply (rngl_neqb_neq Hed).
rewrite (last_lap_mul Hos).
intros Hab.
apply (rngl_eq_mul_0_r Hos) in Hab; [ easy | |  easy].
apply Bool.orb_true_iff; right.
apply rngl_has_inv_and_1_or_quot_iff.
now left; rewrite Hon, Hiv.
Qed.

Theorem lap_norm_mul :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → lap_norm (la * lb) = (la * lb)%lap.
Proof.
intros Hon Hiv * Ha Hb.
apply has_polyn_prop_lap_norm.
now apply (lap_mul_has_polyn_prop Hon Hiv).
Qed.

Theorem lap_mul_div :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → lb ≠ []
  → (la * lb / lb)%lap = la.
Proof.
intros Hon Hco Hop Hiv * pa pb Hbz.
remember (lap_quot_rem (la * lb) lb) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (lq, lr).
specialize (lap_div_mod Hed Hon Hco Hop Hiv) as H1.
specialize (H1 (la * lb)%lap lb lq lr).
specialize (H1 (lap_mul_has_polyn_prop Hon Hiv la lb pa pb)).
assert (H : List.last lb 0%L ≠ 0%L). {
  apply (rngl_neqb_neq Hed).
  apply Bool.orb_true_iff in pb.
  destruct pb as [pb| ]; [ | easy ].
  now apply is_empty_list_empty in pb.
}
specialize (H1 H); clear H.
assert (pr : has_polyn_prop lr = true). {
  specialize (lap_rem_is_norm (la * lb)%lap lb) as H2.
  specialize (H2 (lap_mul_has_polyn_prop Hon Hiv la lb pa pb) pb).
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
rewrite <- (lap_mul_sub_distr_l Hed Hop) in Hab1.
apply (f_equal lap_norm) in Hab1.
rewrite (lap_norm_app_0_r Hed) in Hab1 by apply List.nth_repeat.
rewrite (has_polyn_prop_lap_norm lr pr) in Hab1.
rewrite <- lap_mul_norm_idemp_r in Hab1.
rewrite (lap_norm_mul Hon Hiv) in Hab1; [ | easy | apply polyn_norm_prop ].
generalize Hab1; intros Hab2.
apply (f_equal (λ l, List.length l)) in Hab2.
rewrite lap_mul_length in Hab2.
destruct lb as [| b]; [ easy | clear Hbz ].
remember (lap_norm (la - lq)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. 2: {
  cbn in Hab2.
  cbn in Hrb; flia Hrb Hab2.
}
apply eq_sym, List.length_zero_iff_nil in Hab2.
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
apply (list_nth_lap_eq Hed).
intros i.
specialize (H1 i).
rewrite (list_nth_lap_sub Hop) in H1.
now apply -> (rngl_sub_move_0_r Hop) in H1.
Qed.

Theorem lap_rngl_of_nat :
  let lop := lap_ring_like_op Hed in
  rngl_has_1 (list T) = true →
  ∀ n, rngl_of_nat n = if Nat.eq_dec n 0 then [] else [rngl_of_nat n].
Proof.
intros * Honl *; cbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
progress unfold rngl_of_nat.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn.
induction n; [ easy | clear Hnz; cbn ].
destruct n. {
  cbn; rewrite rngl_add_0_r, lap_add_0_r.
  progress unfold rngl_one; cbn.
  progress unfold lap_opt_one.
  progress unfold rngl_has_1 in Honl; cbn in Honl.
  progress unfold lap_opt_one in Honl.
  now destruct (rngl_opt_one T).
}
rewrite IHn; [ | easy ].
progress unfold rngl_one; cbn.
progress unfold lap_opt_one.
now destruct (rngl_opt_one T).
Qed.

End a.

(* polynomials *)

Record polyn T {ro : ring_like_op T} := mk_polyn
  { lap : list T;
    lap_prop : has_polyn_prop lap = true }.

Arguments mk_polyn {T ro} lap%_lap.
Arguments lap {T ro}.
Arguments lap_prop {T ro}.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hon : rngl_has_1 T = true).
Context (Hos : rngl_has_opp_or_subt T = true).
Context (Hed : rngl_has_eq_dec T = true).

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

Theorem polyn_eq_dec : ∀ P Q : polyn T, {P = Q} + {P ≠ Q}.
Proof.
intros.
unfold rngl_has_eq_dec in Hed.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
specialize (List.list_eq_dec rngl_eq_dec (lap P) (lap Q)) as H1.
destruct H1 as [H1| H1]. {
  now apply eq_polyn_eq in H1; left.
} {
  right; intros H; apply H1.
  now apply eq_polyn_eq.
}
Qed.

Definition polyn_of_norm_lap la :=
  mk_polyn (lap_norm la) (polyn_norm_prop la).

Definition polyn_of_const c :=
  polyn_of_norm_lap [c].

Arguments polyn_of_const c%_L.

Definition polyn_zero := mk_polyn [] eq_refl.
Definition polyn_one := polyn_of_const 1.

Definition polyn_norm la := mk_polyn (lap_norm la) (polyn_norm_prop la).
Definition polyn_add p1 p2 := polyn_norm (lap_add (lap p1) (lap p2)).
Definition polyn_opp pol := polyn_norm (lap_opp (lap pol)).

Definition polyn_subt p1 p2 := polyn_norm (lap_subt (lap p1) (lap p2)).

Definition polyn_mul p1 p2 := polyn_norm (lap_mul (lap p1) (lap p2)).

Definition polyn_quot (pa pb : polyn T) : polyn T :=
  match Sumbool.sumbool_of_bool (rngl_has_1 T) with
  | left Hon =>
      match Sumbool.sumbool_of_bool (rngl_has_inv T) with
      | left Hiv =>
          let lq := lap_quot (lap pa) (lap pb) in
          mk_polyn lq
            (lap_quot_is_norm Hos Hed Hon Hiv (lap pa) (lap pb) (lap_prop pa)
               (lap_prop pb))
      | right _ =>
          polyn_zero
      end
  | right _ =>
      polyn_zero
  end.

(* polyn opposite or subtraction *)

Definition polyn_opt_opp_or_subt :
  option ((polyn T → polyn T) + (polyn T → polyn T → polyn T)) :=
  match rngl_opt_opp_or_subt T with
  | Some (inl _) => Some (inl polyn_opp)
  | Some (inr _) => Some (inr polyn_subt)
  | None => None
  end.

(* polyn quotient *)

Definition polyn_opt_inv_or_quot :
  option ((polyn T → polyn T) + (polyn T → polyn T → polyn T)) :=
  match Sumbool.sumbool_of_bool (rngl_mul_is_comm T) with
  | left Hco =>
      match Sumbool.sumbool_of_bool (rngl_has_opp T) with
      | left Hop =>
          match Sumbool.sumbool_of_bool (rngl_has_inv T) with
         | left Hiv =>
             match rngl_opt_inv_or_quot T with
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
     rngl_add := polyn_add;
     rngl_mul := polyn_mul;
     rngl_opt_one := Some polyn_one;
     rngl_opt_opp_or_subt := polyn_opt_opp_or_subt;
     rngl_opt_inv_or_quot := polyn_opt_inv_or_quot;
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := Some polyn_eq_dec;
     rngl_opt_leb := None |}.

(* allows to use ring-like theorems on polynomials
Canonical Structure polyn_ring_like_op.
*)

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
Notation "a * b" := (polyn_mul a b) : polyn_scope.

Theorem polyn_add_comm :
  let rop := polyn_ring_like_op in
  ∀ a b : polyn T, (a + b)%L = (b + a)%L.
Proof.
intros.
cbn.
progress unfold "+"%pol.
now rewrite lap_add_comm.
Qed.

Theorem polyn_add_assoc : ∀ pa pb pc,
  (pa + (pb + pc) = (pa + pb) + pc)%pol.
Proof.
intros (la, lapr) (lb, lbpr) (lc, lcpr).
apply eq_polyn_eq.
cbn - [ lap_norm ].
do 4 rewrite fold_lap_add.
rewrite (lap_add_norm_idemp_l Hed).
rewrite (lap_add_norm_idemp_r Hed).
now rewrite lap_add_assoc.
Qed.

Theorem polyn_add_0_l : ∀ p, (0 + p)%pol = p.
Proof.
intros (la, lapr).
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm, Nat.sub_0_r, List.app_nil_r.
rewrite List_map2_rngl_add_0_l.
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
rewrite (lap_mul_norm_idemp_l Hos Hed).
rewrite (lap_mul_norm_idemp_r Hos Hed).
now rewrite lap_mul_assoc.
Qed.

Theorem polyn_mul_1_l : ∀ p, (1 * p)%pol = p.
Proof.
intros (la, lapr).
unfold "*"%pol.
unfold polyn_one.
apply eq_polyn_eq; cbn.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hch| Hch]. {
  rewrite (rngl_characteristic_1 Hon Hos Hch 1), (rngl_eqb_refl Hed); cbn.
  apply Bool.orb_true_iff in lapr.
  destruct lapr as [lapr| lapr]; [ now apply is_empty_list_empty in lapr | ].
  apply (rngl_neqb_neq Hed) in lapr.
  exfalso; apply lapr.
  apply (rngl_characteristic_1 Hon Hos Hch).
}
apply (rngl_1_neq_0_iff Hon), (rngl_eqb_neq Hed) in Hch; rewrite Hch.
cbn - [ lap_mul ].
rewrite (lap_mul_1_l Hon Hos).
now apply (has_polyn_prop_lap_norm Hed).
Qed.

Theorem polyn_mul_add_distr_l : ∀ pa pb pc,
  (pa * (pb + pc))%pol = (pa * pb + pa * pc)%pol.
Proof.
intros.
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm, fold_lap_add.
rewrite (lap_mul_norm_idemp_r Hos Hed).
rewrite (lap_add_norm_idemp_l Hed).
rewrite (lap_add_norm_idemp_r Hed).
f_equal.
now rewrite lap_mul_add_distr_l.
Qed.

Theorem polyn_mul_add_distr_r :
  ∀ a b c : polyn T, ((a + b) * c)%pol = (a * c + b * c)%pol.
Proof.
intros.
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm, fold_lap_add.
rewrite (lap_mul_norm_idemp_l Hos Hed).
rewrite (lap_add_norm_idemp_l Hed).
rewrite (lap_add_norm_idemp_r Hed).
f_equal.
now rewrite lap_mul_add_distr_r.
Qed.

Theorem polyn_opt_mul_comm :
  if rngl_mul_is_comm T then ∀ a b : polyn T, (a * b)%pol = (b * a)%pol
  else not_applicable.
Proof.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply eq_polyn_eq; cbn.
now rewrite (lap_mul_comm Hic).
Qed.

(* optional right multiplication by 1; not required if multiplication
   is commutative *)

Theorem polyn_mul_1_r : ∀ a : polyn T, (a * 1)%pol = a.
Proof.
intros.
apply eq_polyn_eq; cbn.
unfold polyn_one.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hch| Hch]. {
  destruct a as (la, pa); cbn.
  apply Bool.orb_true_iff in pa.
  destruct pa as [pa| pa]. {
    now apply is_empty_list_empty in pa; subst la.
  }
  apply (rngl_neqb_neq Hed) in pa.
  exfalso; apply pa.
  apply (rngl_characteristic_1 Hon Hos Hch).
}
apply (rngl_1_neq_0_iff Hon), (rngl_eqb_neq Hed) in Hch; rewrite Hch.
cbn - [ lap_mul ].
rewrite (lap_mul_1_r Hon Hos).
apply (has_polyn_prop_lap_norm Hed).
now destruct a.
Qed.

Theorem polyn_opt_mul_1_r :
  if rngl_mul_is_comm T then not_applicable
  else ∀ a : polyn T, (a * 1)%pol = a.
Proof.
destruct rngl_mul_is_comm; [ easy | ].
now apply polyn_mul_1_r.
Qed.

(* optional right distributivity; not required if multiplication
   is commutative *)

Theorem polyn_opt_mul_add_distr_r :
   if rngl_mul_is_comm T then not_applicable
   else ∀ a b c : polyn T, ((a + b) * c)%pol = (a * c + b * c)%pol.
Proof.
destruct rngl_mul_is_comm; [ easy | ].
apply polyn_mul_add_distr_r.
Qed.

Theorem polyn_add_opp_diag_l :
  rngl_has_opp T = true
  → ∀ a : polyn T, (- a + a)%pol = 0%pol.
Proof.
intros Hop *.
apply eq_polyn_eq.
destruct a as (la, Ha); cbn.
rewrite fold_lap_add.
do 2 rewrite fold_lap_norm.
rewrite (lap_add_norm_idemp_l Hed).
now apply lap_norm_add_opp_diag_l.
Qed.

Theorem polyn_opt_add_opp_diag_l :
  let rop := polyn_ring_like_op in
  if rngl_has_opp (polyn T) then ∀ a : polyn T, (- a + a)%L = 0%L
  else not_applicable.
Proof.
intros rop; subst rop.
remember (rngl_has_opp (polyn T)) as op eqn:Hop; symmetry in Hop.
intros.
destruct op; [ | easy ].
intros a.
unfold rngl_opp; cbn.
unfold polyn_opt_opp_or_subt.
specialize polyn_add_opp_diag_l as add_opp_diag_l.
unfold rngl_has_opp in Hop, add_opp_diag_l.
cbn in Hop, add_opp_diag_l.
unfold polyn_opt_opp_or_subt in Hop, add_opp_diag_l.
destruct rngl_opt_opp_or_subt as [opp| ]; [ | easy ].
destruct opp as [opp| ]; [ | easy ].
now apply add_opp_diag_l.
Qed.

Theorem polyn_opt_has_no_inv : ∀ P,
  let rop := polyn_ring_like_op in
  if (rngl_has_inv (polyn T) && rngl_has_1 (polyn T))%bool then P
  else not_applicable.
Proof.
intros.
progress unfold rngl_has_inv; cbn.
progress unfold polyn_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool (rngl_mul_is_comm T)) as [Hic| Hic];
  [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_opp T)) as [Hop| Hop]; [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_inv T)); [ | easy ].
now destruct rngl_opt_inv_or_quot.
Qed.

Theorem polyn_opt_has_no_inv_and : ∀ e P,
  let rop := polyn_ring_like_op in
  if (rngl_has_inv (polyn T) && rngl_has_1 (polyn T) && e)%bool then P
  else not_applicable.
Proof.
intros.
progress unfold rngl_has_inv; cbn.
progress unfold polyn_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool (rngl_mul_is_comm T)); [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_opp T)); [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_inv T)); [ | easy ].
now destruct rngl_opt_inv_or_quot.
Qed.

Notation "a / b" := (polyn_quot a b) : polyn_scope.

Theorem polyn_mul_div :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
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
destruct (Sumbool.sumbool_of_bool _) as [Hon2| Hon2]. {
  destruct (Sumbool.sumbool_of_bool _) as [Hiv2| Hiv2]. {
    cbn; rewrite (lap_norm_mul Hos Hed Hon Hiv _ _ pa pb).
    now apply lap_mul_div.
  }
  congruence.
}
congruence.
Qed.

Theorem polyn_opt_mul_div :
  let _ := polyn_ring_like_op in
  if rngl_has_quot (polyn T) then ∀ a b, b ≠ 0%L → (a * b / b)%L = a
  else not_applicable.
Proof.
intros rop; subst rop.
progress unfold rngl_has_quot; cbn.
progress unfold polyn_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool (rngl_mul_is_comm T)) as [Hco| ];
  [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_opp T)) as [Hop| ]; [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_inv T)) as [Hiv| ]; [ | easy ].
remember (rngl_opt_inv_or_quot T) as iq eqn:Hiq; symmetry in Hiq.
destruct iq as [inv| ]; [ | easy ].
intros a b Hbz.
progress unfold rngl_div, rngl_has_inv; cbn.
progress unfold polyn_opt_inv_or_quot.
progress unfold rngl_has_quot, polyn_opt_inv_or_quot; cbn.
progress unfold rngl_quot; cbn.
progress unfold polyn_opt_inv_or_quot.
rewrite Hco, Hop, Hiv, Hiq.
destruct (Sumbool.sumbool_of_bool true); [ | easy ].
now apply polyn_mul_div.
Qed.

Theorem polyn_opt_mul_quot_r :
  let _ := polyn_ring_like_op in
  if (rngl_has_quot (polyn T) && negb (rngl_mul_is_comm T))%bool then
    ∀ a b, b ≠ 0%L → (b * a / b)%L = a
  else not_applicable.
Proof.
intros rop.
unfold rngl_has_quot; cbn.
unfold polyn_opt_inv_or_quot.
destruct (Sumbool.sumbool_of_bool _) as [Hco| Hco]; rewrite Hco; [ | easy ].
now rewrite Bool.andb_false_r.
Qed.

Theorem lap_polyn_rngl_of_nat_char_0 :
  let _ := polyn_ring_like_op in
  rngl_characteristic T = 0
  → ∀ i, i ≠ 0 → lap (rngl_of_nat i) = [rngl_of_nat i].
Proof.
intros rop Hch * Hiz; cbn.
subst rop.
progress unfold rngl_of_nat.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn.
induction i; [ easy | clear Hiz; cbn ].
assert (H : rngl_characteristic T ≠ 1) by now rewrite Hch.
specialize (proj1 (rngl_1_neq_0_iff Hon) H) as H1; clear H.
apply (rngl_eqb_neq Hed) in H1; rewrite H1.
cbn - [ lap_add ].
destruct i; [ now cbn; rewrite rngl_add_0_r, H1 | ].
rewrite IHi; [ cbn | easy ].
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [H11| H11]; [ | easy ].
clear IHi; exfalso.
apply (rngl_eqb_eq Hed) in H11.
specialize (rngl_characteristic_0 Hon Hch) as H2.
now specialize (H2 (S i)).
Qed.

Theorem lap_polyn_rngl_of_nat_2 :
  let rop := polyn_ring_like_op in
  ∀ i, 0 < i < rngl_characteristic T
  → lap (rngl_of_nat i) = [rngl_of_nat i].
Proof.
intros * Hi; cbn.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  flia Hi Hc1.
}
specialize (proj1 (rngl_1_neq_0_iff Hon) Hc1) as H11.
specialize rngl_opt_characteristic_prop as Hch.
rewrite Hon in Hch; cbn in Hch.
rewrite if_bool_if_dec in Hch.
destruct (Sumbool.sumbool_of_bool _) as [Hchz| Hchz]. {
  apply Nat.eqb_eq in Hchz.
  now rewrite Hchz in Hi.
}
clear Hchz.
destruct Hch as (Hbef, Hch).
progress unfold rngl_of_nat.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
induction i; [ easy | cbn ].
cbn in IHi.
remember (lap (List.fold_right polyn_add 0%pol (List.repeat 1%pol i)))
  as la eqn:Hla.
symmetry in Hla.
apply (rngl_eqb_neq Hed) in H11; rewrite H11.
cbn - [ lap_add rngl_mul_nat ].
destruct la as [| a]. {
  cbn.
  rewrite rngl_add_0_r, H11.
  cbn; f_equal; symmetry.
  rewrite <- rngl_add_0_r.
  apply rngl_add_compat_l.
  destruct i; [ easy | ].
  assert (H : 0 < S i < rngl_characteristic T) by flia Hi.
  now specialize (IHi H).
}
symmetry; apply List_rev_symm; symmetry; cbn.
rewrite strip_0s_app.
remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H12| H12]. {
    exfalso; apply (rngl_eqb_eq Hed) in H12.
    destruct i; [ easy | ].
    assert (H : 0 < S i < rngl_characteristic T) by flia Hi.
    specialize (IHi H); clear H.
    injection IHi; clear IHi; intros; subst a la.
    clear Hlb.
    cbn - [ lap_add ] in Hla.
    rewrite H11 in Hla.
    cbn - [ lap_add ] in Hla.
    remember (lap (List.fold_right polyn_add 0%pol _)) as lb eqn:Hlb.
    symmetry in Hlb.
    destruct lb as [| b]; cbn in Hla. {
      rewrite rngl_add_0_r, H11 in Hla.
      cbn in Hla.
      injection Hla; clear Hla; intros Hla; symmetry in Hla.
      rewrite <- rngl_add_0_r in Hla.
      apply (rngl_add_cancel_l Hos) in Hla.
      cbn in H12.
      rewrite Hla in H12.
      apply (Hbef 2); [ flia Hi | easy ].
    }
    now specialize (Hbef (S (S i)) Hi) as H1.
  }
  rewrite Nat.sub_0_r, List.app_nil_r, List_map2_rngl_add_0_l, Hlb.
  f_equal.
  apply rngl_add_compat_l; symmetry.
  destruct i; [ easy | ].
  assert (H : 0 < S i < rngl_characteristic T) by flia Hi.
  specialize (IHi H).
  now injection IHi; clear IHi; intros; subst a la.
}
exfalso.
destruct i; [ easy | ].
assert (H : 0 < S i < rngl_characteristic T) by flia Hi.
specialize (IHi H); clear H.
now injection IHi; clear IHi; intros; subst a la.
Qed.

Theorem lap_polyn_rngl_of_nat :
  let lop := lap_ring_like_op Hed in
  let rop := polyn_ring_like_op in
  ∀ n, lap (rngl_of_nat n) = lap_norm (rngl_of_nat n).
Proof.
intros; cbn.
progress unfold rngl_of_nat.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn.
induction n; [ easy | ].
cbn - [ lap_add ].
rewrite IHn; cbn.
rewrite fold_lap_norm.
remember (List.fold_right lap_add [] (List.repeat 1%L n)) as la eqn:Hla.
symmetry in Hla.
progress unfold rngl_one.
progress unfold lop; cbn.
progress unfold lap_opt_one.
generalize Hon; intros H.
progress unfold rngl_has_1 in H.
specialize (proj1 (rngl_1_neq_0_iff Hon)) as H1.
progress unfold rngl_one in H1.
destruct rngl_opt_one as [one| ]; [ cbn; clear H | easy ].
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H2.
  rewrite (H2 one), (rngl_eqb_refl Hed); cbn.
  rewrite fold_lap_norm, Nat.sub_0_r, List.app_nil_r, List_map2_rngl_add_0_l.
  rewrite fold_lap_norm.
  destruct la as [| a]. {
    now cbn; rewrite rngl_add_0_l, (rngl_eqb_refl Hed).
  }
  cbn; rewrite List.rev_involutive.
  rewrite Nat.sub_0_r, List.app_nil_r, List_map2_rngl_add_0_l.
  now rewrite strip_0s_idemp, rngl_add_0_l.
}
specialize (H1 Hc1).
apply (rngl_eqb_neq Hed) in H1; rewrite H1; cbn.
destruct la as [| a]; [ easy | cbn ].
do 2 rewrite strip_0s_app.
cbn.
remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  rewrite if_bool_if_dec.
  rewrite Nat.sub_0_r, List.app_nil_r, List_map2_rngl_add_0_l.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ cbn | ]. 2: {
    now rewrite Hlb.
  }
  apply (rngl_eqb_eq Hed) in Haz; subst a.
  now rewrite rngl_add_0_r, H1, Hlb.
}
cbn; rewrite List.rev_app_distr; cbn.
rewrite Nat.sub_0_r, List.app_nil_r, List_map2_rngl_add_0_l.
rewrite List.rev_app_distr; cbn.
rewrite List.rev_involutive.
rewrite if_bool_if_dec.
rewrite Nat.sub_0_r, List.app_nil_r, List_map2_rngl_add_0_l.
rewrite Hlb.
destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]; [ | easy ].
apply (rngl_eqb_eq Hed) in Hbz; subst b.
now apply eq_strip_0s_cons in Hlb.
Qed.

Theorem polyn_integral :
  let rop := polyn_ring_like_op in
  ∀ a b : polyn T,
  (a * b)%L = 0%L
  → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
now right; right; left.
Qed.

Theorem polyn_characteristic_prop : let rop := polyn_ring_like_op in
  if rngl_has_1 (polyn T) then
    if rngl_characteristic T =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
    else
      (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L)
       ∧ rngl_of_nat (rngl_characteristic T) = 0%L
  else not_applicable.
Proof.
intros rop; subst rop.
set (rol := lap_ring_like_op Hed).
assert (Honl : rngl_has_1 (list T) = true). {
  progress unfold rngl_has_1; cbn.
  progress unfold lap_opt_one; cbn.
  progress unfold rngl_has_1 in Hon.
  now destruct rngl_opt_one.
}
cbn - [ rngl_mul_nat ].
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1; cbn in H1.
rewrite if_eqb_eq_dec in H1 |-*.
destruct (Nat.eq_dec (rngl_characteristic T) 0) as [Hcz| Hcz]. {
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
  rewrite (lap_rngl_of_nat Hed Honl).
  destruct (Nat.eq_dec _ _) as [Hc1| Hc1]; [ easy | ].
  rewrite Hch; cbn.
  now rewrite (rngl_eqb_refl Hed).
}
Qed.

(* *)

Theorem rngl_has_opp_rngl_polyn_has_opp :
  let rop := polyn_ring_like_op in
  rngl_has_opp T = rngl_has_opp (polyn T).
Proof.
intros.
unfold rngl_has_opp; cbn.
unfold polyn_opt_opp_or_subt.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem rngl_has_subt_rngl_polyn_has_subt :
  let rop := polyn_ring_like_op in
  rngl_has_subt T = rngl_has_subt (polyn T).
Proof.
intros.
unfold rngl_has_subt; cbn.
unfold polyn_opt_opp_or_subt.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem polyn_opt_add_sub :
  let rop := polyn_ring_like_op in
  if rngl_has_subt (polyn T) then ∀ a b : polyn T, (a + b - b)%L = a
  else not_applicable.
Proof.
intros.
remember (rngl_has_subt (polyn T)) as su eqn:Hsup; symmetry in Hsup.
destruct su; [ | easy ].
specialize (rngl_has_subt_has_no_opp Hsup) as Hopp.
specialize rngl_has_opp_rngl_polyn_has_opp as Hop; cbn in Hop.
specialize rngl_has_subt_rngl_polyn_has_subt as Hsu; cbn in Hsu.
fold rop in Hop; rewrite Hopp in Hop.
fold rop in Hsu; rewrite Hsup in Hsu.
intros.
apply eq_polyn_eq; cbn.
unfold rngl_sub.
rewrite Hopp, Hsup.
unfold rngl_subt; cbn.
unfold polyn_opt_opp_or_subt.
remember (rngl_opt_opp_or_subt T) as os eqn:Hos'; symmetry in Hos'.
destruct os as [os| ]. 2: {
  unfold rngl_has_opp_or_subt in Hos.
  clear - Hos Hos'.
  now rewrite Hos' in Hos.
}
destruct os as [opp| subt]. {
  unfold rngl_has_opp in Hop; cbn in Hop.
  unfold polyn_opt_opp_or_subt in Hop.
  exfalso; clear - Hop Hos'.
  now rewrite Hos' in Hop.
}
unfold polyn_subt.
destruct a as (la, pa).
destruct b as (lb, pb).
move lb before la.
cbn - [ lap_norm lap_add lap_subt ].
rewrite (lap_subt_norm_idemp_l Hed Hsu).
specialize (lap_opt_add_sub Hsu) as H2.
unfold lap_sub in H2.
rewrite Hop, Hsu in H2.
rewrite H2.
rewrite (lap_norm_app_0_r Hed); [ | intros; apply List.nth_repeat ].
now apply (has_polyn_prop_lap_norm Hed).
Qed.

(* *)

Theorem polyn_opt_sub_add_distr :
  let rop := polyn_ring_like_op in
  if rngl_has_subt (polyn T) then
    ∀ a b c : polyn T, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_subt (polyn T)) as su eqn:Hsup; symmetry in Hsup.
destruct su; [ | easy ].
specialize (rngl_has_subt_has_no_opp Hsup) as Hopp.
specialize rngl_has_opp_rngl_polyn_has_opp as Hop; cbn in Hop.
specialize rngl_has_subt_rngl_polyn_has_subt as Hsu; cbn in Hsu.
fold rop in Hop; rewrite Hopp in Hop.
fold rop in Hsu; rewrite Hsup in Hsu.
intros.
apply eq_polyn_eq; cbn.
unfold rngl_sub.
rewrite Hopp, Hsup.
unfold rngl_subt; cbn.
unfold polyn_opt_opp_or_subt.
remember (rngl_opt_opp_or_subt T) as os eqn:Hos'; symmetry in Hos'.
destruct os as [os| ]. 2: {
  unfold rngl_has_opp_or_subt in Hos.
  clear - Hos Hos'.
  now rewrite Hos' in Hos.
}
destruct os as [opp| subt]. {
  unfold rngl_has_opp in Hop; cbn in Hop.
  unfold polyn_opt_opp_or_subt in Hop.
  exfalso; clear - Hop Hos'.
  now rewrite Hos' in Hop.
}
unfold polyn_subt.
destruct a as (la, pa).
destruct b as (lb, pb).
destruct c as (lc, pc).
move lb before la; move lc before lb.
cbn - [ lap_norm lap_add lap_subt ].
rewrite (lap_subt_norm_idemp_l Hed Hsu).
rewrite (lap_subt_norm_idemp_r Hed Hsu).
specialize (lap_opt_sub_add_distr Hsu) as H1.
unfold lap_sub in H1.
rewrite Hop, Hsu in H1.
f_equal; apply H1.
Qed.

Theorem polyn_opt_sub_0_l :
  let rop := polyn_ring_like_op in
  if rngl_has_subt (polyn T) then ∀ a : polyn T, (0 - a)%L = 0%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_subt (polyn T)) as su eqn:Hsup; symmetry in Hsup.
destruct su; [ | easy ].
specialize (rngl_has_subt_has_no_opp Hsup) as Hopp.
specialize rngl_has_opp_rngl_polyn_has_opp as Hop; cbn in Hop.
specialize rngl_has_subt_rngl_polyn_has_subt as Hsu; cbn in Hsu.
fold rop in Hop; rewrite Hopp in Hop.
fold rop in Hsu; rewrite Hsup in Hsu.
intros.
apply eq_polyn_eq; cbn.
unfold rngl_sub.
rewrite Hopp, Hsup.
unfold rngl_subt; cbn.
unfold polyn_opt_opp_or_subt.
remember (rngl_opt_opp_or_subt T) as os eqn:Hos'; symmetry in Hos'.
destruct os as [os| ]. 2: {
  unfold rngl_has_opp_or_subt in Hos.
  clear - Hos Hos'.
  now rewrite Hos' in Hos.
}
destruct os as [opp| subt]. {
  unfold rngl_has_opp in Hop; cbn in Hop.
  unfold polyn_opt_opp_or_subt in Hop.
  exfalso; clear - Hop Hos'.
  now rewrite Hos' in Hop.
}
unfold polyn_subt.
destruct a as (la, pa).
cbn.
rewrite List.app_nil_r, Nat.sub_0_r.
rewrite List_rev_map2; [ | now rewrite List.repeat_length ].
rewrite List.rev_repeat.
(* lemma *)
apply List.rev_inj; cbn.
rewrite List.rev_involutive.
(* end lemma *)
remember (List.rev la) as lb eqn:Hlb.
apply (f_equal (@List.rev _)) in Hlb.
rewrite List.rev_involutive in Hlb.
subst la.
rewrite List.length_rev.
rename lb into la.
clear pa.
induction la as [| a]; [ easy | cbn ].
rewrite IHla.
remember (rngl_subt 0 a =? 0)%L as za eqn:Hza.
symmetry in Hza.
destruct za; [ easy | exfalso ].
apply (rngl_eqb_neq Hed) in Hza.
apply Hza; clear Hza.
specialize rngl_opt_sub_0_l as H1.
progress unfold rngl_sub in H1.
rewrite Hop, Hsu in H1.
apply H1.
Qed.

Definition polyn_ring_like_prop : ring_like_prop (polyn T) :=
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_archimedean := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := polyn_add_comm;
     rngl_add_assoc := polyn_add_assoc;
     rngl_add_0_l := polyn_add_0_l;
     rngl_mul_assoc := polyn_mul_assoc;
     rngl_opt_mul_1_l := polyn_mul_1_l;
     rngl_mul_add_distr_l := polyn_mul_add_distr_l;
     rngl_opt_mul_comm := polyn_opt_mul_comm;
     rngl_opt_mul_1_r := polyn_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := polyn_opt_mul_add_distr_r;
     rngl_opt_add_opp_diag_l := polyn_opt_add_opp_diag_l;
     rngl_opt_add_sub := polyn_opt_add_sub;
     rngl_opt_sub_add_distr := polyn_opt_sub_add_distr;
     rngl_opt_sub_0_l := polyn_opt_sub_0_l;
     rngl_opt_mul_inv_diag_l := polyn_opt_has_no_inv _;
     rngl_opt_mul_inv_diag_r := polyn_opt_has_no_inv_and _ _;
     rngl_opt_mul_div := polyn_opt_mul_div;
     rngl_opt_mul_quot_r := polyn_opt_mul_quot_r;
     rngl_opt_integral := polyn_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := polyn_characteristic_prop;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.
