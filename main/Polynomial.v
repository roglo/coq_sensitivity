(* Polynomial.v *)

(* polynomials on a RingLike *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations Init.Nat.

Require Import Misc RingLike IterAdd IterAnd.
Require Import PermutationFun SortingFun.
Require Import LapPolyn.

Definition is_empty_list {A} (la : list A) :=
  match la with [] => true | _ => false end.
Definition has_polyn_prop {T} {ro : ring_like_op T} (la : list T) :=
  (is_empty_list la || (List.last la 0 ≠? 0)%L)%bool.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hos : rngl_has_opp_or_subt T = true).
Context (Hed : rngl_has_eq_dec T = true).

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
    apply (eq_strip_0s_nil 0%L).
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
  apply (eq_strip_0s_nil 0%L) with (i := List.length la - S i) in Hla. {
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
      specialize (proj1 (eq_strip_0s_nil 0%L _) Hlb) as H1.
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
      specialize (proj1 (eq_strip_0s_nil 0%L _) Hlb) as H1.
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

Theorem rlap_quot_prop :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ la lb lq lr,
  la = [] ∨ List.hd 0%L la ≠ 0%L
  → lb = [] ∨ List.hd 0%L lb ≠ 0%L
  → rlap_quot_rem la lb = (lq, lr)
  → lq = [] ∨ List.hd 0%L lq ≠ 0%L.
Proof.
intros Hon Hiv * Ha Hb Hab.
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
apply (rlap_quot_prop Hon Hiv) in Hqr; cycle 1. {
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

Theorem lap_norm_idemp : ∀ la, lap_norm (lap_norm la) = lap_norm la.
Proof.
intros.
unfold lap_norm.
rewrite List.rev_involutive.
now rewrite strip_0s_idemp.
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
    specialize (proj1 (eq_strip_0s_nil 0%L _) Hlc) as H1.
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
    specialize (proj1 (eq_strip_0s_nil 0%L _) Hlc) as H1.
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
  specialize (proj1 (eq_strip_0s_nil 0%L _) Hlc) as H1.
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
  specialize (proj1 (eq_strip_0s_rev_nil lb) Hlc) as H1.
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

Theorem lap_mul_length : ∀ la lb,
  List.length (la * lb)%lap =
    match (la, lb) with
    | ([], _) | (_, []) => 0
    | _ => List.length (la ++ lb) - 1
    end.
Proof.
intros.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | cbn ].
rewrite Nat.sub_0_r, Nat.add_succ_r; cbn.
f_equal.
rewrite lap_convol_mul_length.
rewrite Nat.sub_0_r, List.length_app; cbn.
now rewrite Nat.add_succ_r.
Qed.

Theorem lap_convol_mul_1_l :
  rngl_has_1 T = true →
  ∀ la i len,
  List.length la = i + len
  → lap_convol_mul [1%L] la i len = List.skipn i la.
Proof.
intros Hon * Hlen.
rewrite (lap_convol_mul_const_l Hos); [ | easy ].
erewrite List.map_ext_in. 2: {
  intros a Ha.
  now rewrite rngl_mul_1_l.
}
apply List.map_id.
Qed.

Theorem lap_convol_mul_1_r :
  rngl_has_1 T = true →
  ∀ la i len,
  List.length la = i + len
  → lap_convol_mul la [1%L] i len = List.skipn i la.
Proof.
intros Hon * Hlen.
rewrite (lap_convol_mul_const_r Hos); [ | easy ].
erewrite List.map_ext_in. 2: {
  intros a Ha.
  now rewrite rngl_mul_1_r.
}
apply List.map_id.
Qed.

Theorem lap_add_const_l :
  ∀ a la, ([a] + la)%lap = (a + List.hd 0 la)%L :: List.tl la.
Proof.
intros.
destruct la as [| b]; [ easy | ].
cbn; f_equal.
rewrite Nat.sub_0_r, List.app_nil_r.
apply List_map2_rngl_add_0_l.
Qed.

Theorem lap_add_const_r :
  ∀ a la, (la + [a])%lap = (List.hd 0 la + a)%L :: List.tl la.
Proof.
intros.
destruct la as [| b]; [ easy | ].
cbn; f_equal.
rewrite Nat.sub_0_r, List.app_nil_r.
apply List_map2_rngl_add_0_r.
Qed.

Theorem lap_convol_mul_x_l :
  rngl_has_1 T = true →
  ∀ la lb i len,
  i = S (List.length la)
  → len = List.length lb
  → lap_convol_mul [0%L; 1%L] (la ++ lb) i len = lb.
Proof.
intros Hon * Hi Hlen.
revert la lb i Hi Hlen.
induction len; intros. {
  now symmetry in Hlen; apply List.length_zero_iff_nil in Hlen.
}
cbn.
destruct lb as [| b]; [ easy | ].
cbn in Hlen.
apply Nat.succ_inj in Hlen.
f_equal. {
  rewrite (rngl_summation_split3 1); [ | flia Hi ].
  rewrite rngl_summation_only_one.
  rewrite Nat.sub_diag, (rngl_mul_0_l Hos).
  rewrite rngl_add_0_l, (rngl_mul_1_l Hon).
  rewrite Hi, Nat_sub_succ_1.
  rewrite List.app_nth2; [ | now unfold ge ].
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
rewrite List.app_assoc.
apply IHlen; [ | easy ].
rewrite List.length_app, Nat.add_1_r.
now f_equal.
Qed.

Theorem lap_mul_x_l :
  rngl_has_1 T = true →
  ∀ la, la ≠ [] → ([0; 1]%L * la)%lap = 0%L :: la.
Proof.
intros Hon * Hla; cbn.
destruct la as [| a]; [ easy | clear Hla ].
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos).
f_equal; cbn.
unfold iter_seq, iter_list; cbn.
rewrite rngl_add_0_l, (rngl_mul_0_l Hos).
rewrite rngl_add_0_l, (rngl_mul_1_l Hon).
f_equal.
rewrite (List_cons_is_app a).
now apply (lap_convol_mul_x_l Hon).
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

(* optional left addition of opposite; not existing if there is
   no opposite *)

Theorem lap_add_opp_diag_l :
  rngl_has_opp T = true
  → ∀ la, (- la + la)%lap = List.repeat 0%L (List.length la).
Proof.
intros Hop *.
induction la as [| a]; [ easy | cbn ].
rewrite (rngl_add_opp_diag_l Hop).
now f_equal.
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
rewrite List_rev_repeat.
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

Theorem map_opp_repeat : ∀ (x : T) n,
  List.map rngl_opp (List.repeat x n) = List.repeat (rngl_opp x) n.
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

Definition lap_x_power n := List.repeat 0%L n ++ [1%L].

Theorem lap_repeat_0_app_is_mul_power_l :
  rngl_has_1 T = true →
  ∀ n la,
  la ≠ []
  → List.repeat 0%L n ++ la = (lap_x_power n * la)%lap.
Proof.
intros Hon * Haz.
revert la Haz.
induction n; intros. {
  destruct la as [| a]; [ easy | clear Haz; cbn ].
  rewrite rngl_summation_only_one.
  rewrite (rngl_mul_1_l Hon); f_equal.
  now rewrite (lap_convol_mul_1_l Hon).
}
cbn.
destruct la as [| a]; [ easy | clear Haz ].
rewrite List.length_app, List.repeat_length; cbn.
rewrite Nat.sub_0_r, Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos); f_equal.
rewrite lap_convol_mul_l_succ_l.
rewrite IHn; [ | easy ].
destruct n; [ easy | cbn ].
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos).
rewrite Nat.sub_0_r.
rewrite List.length_app, List.repeat_length; cbn.
rewrite lap_convol_mul_l_succ_l.
rewrite Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos); f_equal.
apply lap_convol_mul_l_succ_l.
Qed.

Theorem lap_repeat_0_app_is_mul_power_r :
  rngl_has_1 T = true →
  ∀ n la,
  la ≠ []
  → List.repeat 0%L n ++ la = (la * lap_x_power n)%lap.
Proof.
intros Hon * Haz.
revert la Haz.
induction n; intros. {
  destruct la as [| a]; [ easy | clear Haz; cbn ].
  rewrite Nat.sub_0_r, Nat.add_1_r; cbn.
  rewrite rngl_summation_only_one.
  rewrite (rngl_mul_1_r Hon); f_equal.
  now rewrite (lap_convol_mul_1_r Hon).
}
cbn.
destruct la as [| a]; [ easy | clear Haz ].
cbn.
rewrite List.length_app, List.repeat_length, Nat.sub_0_r; cbn.
rewrite Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_r Hos); f_equal.
rewrite IHn; [ | easy ].
rewrite lap_convol_mul_r_succ_l.
cbn.
destruct n; cbn; [ now rewrite Nat.sub_0_r | ].
now rewrite List.length_app, List.repeat_length, Nat.sub_0_r.
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

Theorem lap_subt_app_app :
  ∀ la lb lc ld,
  List.length la = List.length lb
  → lap_subt (la ++ lc) (lb ++ ld) = lap_subt la lb ++ lap_subt lc ld.
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
  now rewrite List_rev_repeat.
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
rewrite <- (List_rev_repeat _ (List.length lb - _)).
rewrite <- (List_rev_repeat _ (List.length la - _)).
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

Theorem rev_lap_sub_norm :
  rngl_has_opp T = true →
  ∀ la lb,
  List.rev (la - lb)%lap =
    ((List.repeat 0%L (List.length lb - List.length la) ++ List.rev la) -
     (List.repeat 0%L (List.length la - List.length lb) ++ List.rev lb))%lap.
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
unfold lap_opp.
rewrite map_opp_repeat.
now rewrite rngl_opp_0.
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
intros Hon Hic Hop Hiv * Hbz Hrl.
destruct rlb as [| b]; [ easy | cbn in Hbz, Hrl ].
destruct rla as [| a]; [ easy | ].
rewrite if_bool_if_dec in Hrl.
destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]; [ easy | ].
apply Nat.ltb_ge in Hab.
injection Hrl; clear Hrl; intros H1 H2; subst cq rlr.
remember (a / b)%L as cq eqn:Hcq.
move b before a.
cbn; rewrite List_rev_repeat.
rewrite (lap_repeat_0_app_is_mul_power_l Hon); [ | easy ].
rewrite (lap_mul_assoc Hed Hos); cbn.
rewrite <- (lap_repeat_0_app_is_mul_power_r Hon). 2: {
  now intros H; apply List.app_eq_nil in H.
}
rewrite (lap_mul_const_r Hos).
do 2 rewrite List.map_app; cbn.
rewrite List_map_repeat.
rewrite (rngl_mul_0_l Hos).
rewrite List.map_rev.
replace (b * cq)%L with (b * (a / b))%L by now rewrite Hcq.
rewrite (rngl_mul_comm Hic b).
rewrite (rngl_div_mul Hon Hiv _ _ Hbz).
rewrite <- List_rev_repeat at 1.
rewrite List.app_assoc.
rewrite <- List.rev_app_distr.
remember (List.map _ _ ++ List.repeat _ _) as rlc eqn:Hrlc.
rewrite rev_lap_sub_norm; [ | easy ].
rewrite List.length_map.
remember (List.repeat _ _ ++ _) as x.
rewrite <- List_rev_repeat.
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
apply (f_equal (λ l, List.length l)) in Hrlac.
rewrite lap_sub_length in Hrlac.
rewrite lap_add_length in Hrlac.
rewrite Nat.max_l in Hrlac; [| apply Nat.le_max_l ].
rewrite Nat.max_l in Hrlac; [ | easy ].
destruct rlac as [| ac]; intros. {
  apply List.length_zero_iff_nil in Hrlac; subst rlc; cbn.
  rewrite lap_add_0_l in Hab.
  now apply Nat.le_0_r, List.length_zero_iff_nil in Hab; subst rlb.
}
now rewrite rev_lap_add.
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
intros Hon Hco Hop Hiv * Hbn Hqr Hit.
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
rewrite List_rev_repeat.
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

Theorem lap_quot_rem_prop :
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
clear Hos.
intros Hon Hco Hop Hiv * Ha Hb Hr Hab.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
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
  apply (rlap_quot_prop Hon Hiv) in Hqr'; cycle 1. {
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
  cbn; rewrite Nat.sub_0_r.
  rewrite List.length_app; cbn.
  apply rlap_rem_prop in Hqr. 2: {
    intros H.
    now apply List_eq_rev_nil in H.
  }
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
  apply (rlap_quot_prop Hon Hiv) in Hqr; [ | | now right ]. 2: {
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
cbn; rewrite Nat.sub_0_r.
rewrite List.length_app; cbn.
apply rlap_rem_prop in Hqr. 2: {
  intros H.
  now apply List_eq_rev_nil in H.
}
rewrite List.length_rev in Hqr; cbn in Hqr; flia Hqr.
Qed.

(* to be completed
Theorem lap_div_mod :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ la lb,
  lap_norm la = la
  → lap_norm lb = lb
  → lb ≠ 0%lap
  → la = (lb * (la / lb) + la mod lb)%lap.
Proof.
intros Hon Hic Hop Hiv.
intros * Hla Hlb Hlbz.
specialize (lap_quot_rem_prop Hon Hic Hop Hiv) as H1.
specialize (H1 la lb (la / lb)%lap (la mod lb)%lap).
assert (H : has_polyn_prop la = true). {
  progress unfold has_polyn_prop.
  cbn.
  remember (List.rev la) as rla eqn:Hrla.
  symmetry in Hrla.
  apply List_rev_symm in Hrla.
  subst la.
  progress unfold lap_norm in Hla.
  rewrite List.rev_involutive in Hla.
  apply List_rev_rev in Hla.
  rename rla into la.
  apply Bool.orb_true_iff.
  destruct la as [| a]; [ now left | right ].
  cbn; rewrite List.last_last.
  apply Bool.negb_true_iff.
  apply Bool.not_true_iff_false.
  intros H.
  apply (rngl_eqb_eq Hed) in H.
  cbn in Hla.
  subst a.
  rewrite (rngl_eqb_refl Hed) in Hla.
  exfalso.
  specialize (strip_0s_length_le la) as H2.
  apply Nat.nlt_ge in H2.
  apply H2; clear H2.
  now rewrite Hla; cbn.
}
specialize (H1 H); clear H.
assert (H : List.last lb 0%L ≠ 0%L). {
  intros H2.
  destruct lb as [| b] using List.rev_ind; [ easy | ].
  rewrite List.last_last in H2.
  subst b.
...
*)

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
specialize (lap_quot_rem_prop Hon Hco Hop Hiv) as H1.
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
  rewrite List.length_app in Hab2; cbn in Hab2.
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

Arguments rngl_opt_one T {ring_like_op}.

Theorem lap_rngl_of_nat :
  let lop := lap_ring_like_op in
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

Theorem eq_lap_add_nil : ∀ la lb, (la + lb = [])%lap → la = [] ∧ lb = [].
Proof.
intros * Hab.
destruct la as [| a]; cbn in Hab. {
  rewrite Nat.sub_0_r, List.app_nil_r in Hab.
  now rewrite List_map2_rngl_add_0_l in Hab.
}
now destruct lb.
Qed.

End a.

(* to be completed

Definition rlap_horner_1 {A} (to_T : A → _) rla x :=
  iter_list rla (λ accu a, (accu * x + to_T a)%L) 0%L.

Definition lap_horner_1 {A} (to_T : A → _) la x :=
  rlap_horner_1 to_T (List.rev la) x.

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

(* polynomials *)

(* TODO: use an intermediate type like this:
      Record polyn T := mk_polyn { lap : list T }.
   and another type for the condition that the List.last value in lap
   is not null.
*)

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

Arguments polyn_of_const c%_L.

Definition polyn_zero := mk_polyn [] eq_refl.
Definition polyn_one := polyn_of_const 1.

Definition polyn_norm la := mk_polyn (lap_norm la) (polyn_norm_prop la).
Definition polyn_add p1 p2 := polyn_norm (lap_add (lap p1) (lap p2)).
Definition polyn_opp pol := polyn_norm (lap_opp (lap pol)).

Definition polyn_subt p1 p2 := polyn_norm (lap_subt (lap p1) (lap p2)).
Definition polyn_sub p1 p2 :=
  if rngl_has_opp T then polyn_add p1 (polyn_opp p2)
  else if rngl_has_subt T then polyn_subt p1 p2
  else polyn_zero.

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

Definition polyn_rem (pa pb : polyn T) : polyn T :=
  let lq := lap_rem (lap pa) (lap pb) in
  mk_polyn lq
    (lap_rem_is_norm Hed (lap pa) (lap pb) (lap_prop pa) (lap_prop pb)).

Definition polyn_quot_rem (pa pb : polyn T) : polyn T * polyn T :=
  (polyn_quot pa pb, polyn_rem pa pb).

Definition polyn_x_power n := polyn_of_norm_lap (lap_x_power n).

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

(* had to add this version for polyn_ring_like_prop, I don't know
   why (othewize, Coq error). Not required for polyn_add_assoc, I
   don't understand. *)
Theorem polyn_add_comm' :
  let rop := polyn_ring_like_op in
  ∀ a b : polyn T, (a + b)%L = (b + a)%L.
Proof.
intros.
apply polyn_add_comm.
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

Theorem polyn_mul_comm :
  rngl_mul_is_comm T = true →
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

Theorem polyn_quot_rem_prop :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ pa pb pq pr : polyn T,
  pb ≠ 0%pol
  → polyn_quot_rem pa pb = (pq, pr)
  → pa = (pb * pq + pr)%pol ∧ List.length (lap pr) < List.length (lap pb).
Proof.
intros * Hic Hop Hiv * Hbz Hab.
destruct pa as (la, Hpa).
destruct pb as (lb, Hpb).
destruct pq as (lq, Hpq).
destruct pr as (lr, Hpr); cbn.
move lb before la; move lq before lb; move lr before lq.
specialize (lap_quot_rem_prop Hos Hed Hon Hic Hop Hiv la lb) as H1.
specialize (H1 lq lr Hpa).
assert (H : (List.last lb 0 ≠ 0)%L). {
  apply (rngl_neqb_neq Hed).
  destruct lb; [ | easy ].
  exfalso; apply Hbz.
  now apply eq_polyn_eq.
}
specialize (H1 H Hpr); clear H.
assert (H : lap_quot_rem la lb = (lq, lr)). {
  unfold polyn_quot_rem in Hab.
  unfold polyn_quot, polyn_rem in Hab; cbn in Hab.
  destruct (Sumbool.sumbool_of_bool (rngl_has_1 T)) as [Hon2| Hon2]. {
    destruct (Sumbool.sumbool_of_bool (rngl_has_inv T)) as [Hiv2| Hiv2]. {
      injection Hab; clear Hab; intros; subst lr lq.
      unfold lap_quot_rem.
      unfold lap_quot, lap_rem.
      now destruct (rlap_quot_rem _ _).
    }
    congruence.
  }
  congruence.
}
specialize (H1 H); clear H.
destruct H1 as (H1, H2).
split; [ | easy ].
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm, fold_lap_add.
rewrite (lap_add_norm_idemp_l Hed).
rewrite <- H1; symmetry.
now apply has_polyn_prop_lap_norm.
Qed.

Notation "a + b" := (polyn_add a b) : polyn_scope.
Notation "a * b" := (polyn_mul a b) : polyn_scope.
Notation "a / b" := (polyn_quot a b) : polyn_scope.
Notation "a 'mod' b" := (polyn_rem a b) : polyn_scope.

(* to be removed
Theorem polyn_div_mod : ∀ x y, (y ≠ 0 → x = y * (x / y) + x mod y)%pol.
Proof.
intros * Hyz.
progress unfold polyn_quot.
progress unfold polyn_rem.
destruct x as (la, Hla).
destruct y as (lb, Hlb).
cbn.
destruct (Sumbool.sumbool_of_bool (rngl_has_1 T)) as [Hon'| ]. 2: {
  congruence.
}
move Hon' before Hon.
assert (Hon = Hon') by apply (Eqdep_dec.UIP_dec Bool.bool_dec).
subst Hon'.
destruct (Sumbool.sumbool_of_bool (rngl_has_inv T)) as [Hiv| ]. {
  move lb before la.
  move Hiv before Hed.
  progress unfold has_polyn_prop in Hla.
  progress unfold has_polyn_prop in Hlb.
  progress unfold polyn_add.
  progress unfold polyn_mul.
  cbn.
Search (lap_norm (_ * _)).
Search (length (lap_norm _)).
Search lap_quot.
...
*)

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

(* is it provable?
Theorem polyn_opt_div_mul_distr :
  let _ := polyn_ring_like_op in (* utiliser Instance *)
  if rngl_has_quot (polyn T) then
    ∀ a b c : polyn T, (a / (b * c))%L = (a / c / b)%L
  else not_applicable.
Proof.
intros rop.
remember (rngl_has_quot (polyn T)) as qu eqn:Hqu.
symmetry in Hqu.
destruct qu; [ | easy ].
intros.
progress unfold rngl_div.
rewrite Hqu.
remember (rngl_has_inv (polyn T)) as iv eqn:Hiv.
symmetry in Hiv.
destruct iv. {
  apply rngl_has_quot_has_no_inv in Hqu.
  congruence.
}
progress unfold rngl_quot.
cbn.
progress unfold rngl_has_quot in Hqu.
progress unfold rngl_has_inv in Hiv.
cbn in Hqu, Hiv.
remember polyn_opt_inv_or_quot as iq eqn:Hiq.
symmetry in Hiq.
destruct iq as [op| ]; [ | easy ].
destruct op; [ easy | ].
clear Hqu Hiv.
progress unfold polyn_opt_inv_or_quot in Hiq.
destruct (Sumbool.sumbool_of_bool _) as [Hco| Hco]. {
  destruct (Sumbool.sumbool_of_bool _) as [Hop| Hop]. {
    progress unfold rngl_has_inv in Hiq.
    destruct (Sumbool.sumbool_of_bool _) as [Hiv| Hiv]. {
      remember (rngl_opt_inv_or_quot T) as iqt eqn:Hiqt.
      symmetry in Hiqt.
      destruct iqt as [iqt| ]; [ | easy ].
      injection Hiq; clear Hiq; intros; subst p.
Search (_ / _)%pol.
Print polyn_quot.
...
Print rngl_quot.
Search rngl_quot.
...
 rngl_has_quot_has_no_inv:
  ∀ {T : Type} {ro : ring_like_op T}, rngl_has_quot T = true → rngl_has_inv T = false
 progress unfold rngl_inv.
  cbn.
Search rngl_has_quot.
  progress unfold rngl_has_quot in Hqu.
  progress unfold rngl_has
Search (_ * _)⁻¹%L.
rewrite rngl_inv_mul_distr.
...
rewrite rngl_inv_mul_distr.
  rewrite rngl_mul_inv.
  rewrite Hqu.
...
progress unfold rngl_has_quot; cbn.
progress unfold polyn_opt_inv_or_quot.
progress unfold rngl_div.
cbn.
progress unfold rngl_has_inv.
progress unfold rngl_opt_inv_or_quot; cbn.
progress unfold polyn_opt_inv_or_quot.
cbn.
destruct (Sumbool.sumbool_of_bool _) as [Hco| Hco]. {
  destruct (Sumbool.sumbool_of_bool _) as [Hop| Hop]. {
    progress unfold rngl_has_inv.
    destruct (Sumbool.sumbool_of_bool _) as [Hiv| Hiv]. {
...
      destruct (rngl_opt_inv_or_quot T); [ | easy ].
      destruct s; [ | easy ].
      cbn.
...
  cbn.
...
now rewrite Bool.andb_false_r.
...
*)

Theorem polyn_opt_eqb_eq :
  let rop := polyn_ring_like_op in
  if rngl_has_eq_dec (polyn T) then ∀ a b : polyn T, (a =? b)%L = true ↔ a = b
  else not_applicable.
Proof.
intros rop; subst rop.
intros a b; cbn.
now destruct (polyn_eq_dec a b).
Qed.

Theorem polyn_opt_integral :
  let _ := polyn_ring_like_op in
  if rngl_is_integral_domain T then
    ∀ a b : polyn T, (a * b)%L = 0%L → a = 0%L ∨ b = 0%L
  else not_applicable.
Proof.
intros rop; subst rop.
destruct (Sumbool.sumbool_of_bool (rngl_is_integral_domain T)) as [Hii| Hii];
  rewrite Hii; [ | easy ].
intros * Hab.
cbn in Hab.
apply (f_equal lap) in Hab.
cbn in Hab.
specialize (proj2 (all_0_lap_norm_nil Hed _) Hab) as H1.
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
destruct la as [| a] using List.rev_ind; [ now left | clear IHla ].
rewrite List.last_last in pa.
destruct lb as [| b] using List.rev_ind; [ now right | clear IHlb ].
rewrite List.last_last in pb.
specialize (last_lap_mul Hos (la ++ [a]) (lb ++ [b])) as H2.
do 2 rewrite List.last_last in H2.
rewrite List_last_nth in H2.
rewrite H1 in H2.
symmetry in H2.
apply (rngl_neqb_neq Hed) in pa, pb.
apply (rngl_integral Hos) in H2; [ | now rewrite Hii ].
now destruct H2.
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
  let lop := lap_ring_like_op in
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

Theorem polyn_characteristic_prop : let rop := polyn_ring_like_op in
  if rngl_has_1 (polyn T) then
    if rngl_characteristic T =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
    else
      (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L)
       ∧ rngl_of_nat (rngl_characteristic T) = 0%L
  else not_applicable.
Proof.
intros rop; subst rop.
set (rol := lap_ring_like_op).
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
  rewrite (lap_rngl_of_nat Honl).
  destruct (Nat.eq_dec _ _) as [Hc1| Hc1]; [ easy | ].
  rewrite Hch; cbn.
  now rewrite (rngl_eqb_refl Hed).
}
Qed.

(* *)

Theorem eq_nth_lap_subt_0 :
  rngl_has_subt T = true →
  ∀ la lb,
  (∀ i, List.nth i la 0%L = List.nth i lb 0%L)
  → ∀ i, List.nth i (lap_subt la lb) 0%L = 0%L.
Proof.
intros Hsu * Hab *.
revert i lb Hab.
induction la as [| a]; intros; cbn. {
  rewrite Nat.sub_0_r, List.app_nil_r.
  destruct (lt_dec i (List.length lb)) as [Hil| Hil]. {
    rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
      now rewrite List.repeat_length.
    }
    rewrite <- Hab, List_nth_nil.
    rewrite List_nth_repeat.
    destruct (lt_dec _ _) as [H| H]; [ clear H | easy ].
    unfold rngl_subt.
    unfold rngl_has_opp_or_subt in Hos.
    specialize (rngl_add_sub Hos 0 0) as H1.
    rewrite rngl_add_0_r in H1.
    unfold rngl_sub, rngl_has_opp, rngl_has_subt, rngl_subt in H1.
    remember (rngl_opt_opp_or_subt T) as os eqn:Hos'; symmetry in Hos'.
    destruct os as [os| ]; [ | easy ].
    now destruct os.
  }
  apply Nat.nlt_ge in Hil.
  apply List.nth_overflow.
  now rewrite List_length_map2, List.repeat_length, Nat.min_id.
}
destruct lb as [| b]. {
  cbn - [ List.nth ].
  rewrite List.app_nil_r, (rngl_subt_0_r Hsu).
  rewrite (List_map2_rngl_subt_0_r Hsu); [ | easy ].
  now rewrite Hab, List_nth_nil.
}
destruct i; cbn. {
  specialize (Hab 0); cbn in Hab; subst b.
  apply (rngl_subt_diag Hos).
}
apply IHla.
intros j.
now specialize (Hab (S j)).
Qed.

(**)

Theorem lap_subt_app_r :
  ∀ la lb lc,
  List.length la ≤ List.length lb
  → lap_subt la (lb ++ lc) = lap_subt la lb ++ List.map (rngl_subt 0) lc.
Proof.
intros * Hab.
revert lb lc Hab.
induction la as [| a]; intros. {
  cbn.
  do 2 rewrite List.app_nil_r, Nat.sub_0_r.
  rewrite List.length_app.
  rewrite List.repeat_app.
  rewrite List_map2_app_app; [ | apply List.repeat_length ].
  f_equal.
  rewrite (List_map2_map_min 0%L 0%L).
  rewrite List.repeat_length, Nat.min_id.
  symmetry.
  rewrite (List_map_map_seq 0%L).
  apply List.map_ext_in.
  intros i Hi.
  apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
  rewrite List_nth_repeat.
  now destruct (lt_dec _ _).
}
destruct lb as [| b]; [ easy | ].
cbn in Hab; apply Nat.succ_le_mono in Hab.
cbn; do 2 rewrite fold_lap_subt.
now f_equal; apply IHla.
Qed.

Theorem lap_norm_add_subt :
  rngl_has_subt T = true →
  ∀ la lb,
  List.length la = List.length lb
  → lap_subt (lap_norm (la + lb)) lb = la.
Proof.
intros Hsu * Hab.
assert (Hop : rngl_has_opp T = false). {
  unfold rngl_has_subt in Hsu.
  unfold rngl_has_opp.
  destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
  now destruct os.
}
move Hop after Hsu.
specialize (lap_subt_norm_idemp_l Hed Hsu) as H1.
specialize (H1 (la + lb)%lap lb).
apply (eq_lap_norm_eq_length Hed) in H1. 2: {
  do 2 rewrite lap_subt_length.
  rewrite lap_add_length.
  rewrite <- Hab, Nat.max_id, Nat.max_id.
  apply Nat.max_r.
  etransitivity; [ apply (lap_norm_length_le Hed) | ].
  rewrite lap_add_length.
  now rewrite Hab, Nat.max_id.
}
rewrite H1; clear H1.
unfold lap_subt.
rewrite lap_add_length.
rewrite Hab, Nat.max_id.
rewrite Nat.sub_diag.
do 2 rewrite List.app_nil_r.
revert lb Hab.
induction la as [| a]; intros. {
  now symmetry in Hab; apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | ].
cbn in Hab; apply Nat.succ_inj in Hab; cbn.
rewrite Hab, Nat.sub_diag.
do 2 rewrite List.app_nil_r.
specialize (rngl_add_sub Hos) as H1.
unfold rngl_sub in H1.
rewrite Hop, Hsu in H1.
rewrite H1; f_equal.
specialize (IHla _ Hab) as H2.
unfold lap_add in H2.
rewrite Hab, Nat.sub_diag in H2.
now do 2 rewrite List.app_nil_r in H2.
Qed.

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
(**)

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
(**)

(*
Theorem polyn_opt_mul_subt_distr_l :
  let rop := polyn_ring_like_op in
  if rngl_has_subt then ∀ a b c : polyn T, (a * (b - c))%L = (a * b - a * c)%L
  else not_applicable.
Proof.
intros rop.
remember rngl_has_subt as su eqn:Hsup; symmetry in Hsup.
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
remember rngl_opt_opp_or_subt as os eqn:Hos'; symmetry in Hos'.
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
rewrite (lap_subt_norm_idemp_r Hed Hsu).
rewrite (lap_mul_norm_idemp_r Hos Hed).
... ...
f_equal.
apply (lap_mul_subt_distr_l Hsu).
...
specialize (lap_opt_mul_subt_distr_l Hsu) as H2.
unfold lap_sub in H2.
rewrite Hop, Hsu in H2.
rewrite H2.
rewrite (lap_norm_app_0_r Hed); [ | intros; apply List.nth_repeat ].
now apply (has_polyn_prop_lap_norm Hed).
...
*)

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
Definition polyn_opt_has_no_subt (_ : True) := 12.
(**)

Definition polyn_ring_like_prop : ring_like_prop (polyn T) :=
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_integral_domain := rngl_is_integral_domain T;
     rngl_is_archimedean := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := polyn_add_comm';
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
     rngl_opt_mul_inv_diag_l := polyn_opt_has_no_inv _;
     rngl_opt_mul_inv_diag_r := polyn_opt_has_no_inv_and _ _;
     rngl_opt_mul_div := polyn_opt_mul_div;
     rngl_opt_mul_quot_r := polyn_opt_mul_quot_r;
(*
     rngl_opt_div_mul_distr := polyn_opt_div_mul_distr;
*)
     rngl_opt_integral := polyn_opt_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := polyn_characteristic_prop;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.

Definition eval_polyn pol :=
  eval_lap (lap pol).

Definition polyn_compose p q :=
  polyn_of_norm_lap (lap_compose (lap p) (lap q)).

Definition monom (p : polyn T) i :=
  polyn_of_norm_lap [List.nth i (lap p) 0%L].

Theorem lap_norm_lap : ∀ p, lap_norm (lap p) = lap p.
Proof.
intros p.
apply (has_polyn_prop_lap_norm Hed).
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
rewrite List.seq_S; cbn.
do 2 rewrite List.fold_left_app.
cbn - [ lap_norm ].
rewrite <- (lap_add_norm_idemp_l Hed).
rewrite IHn.
rewrite (lap_add_norm_idemp_l Hed).
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
rewrite List.seq_S.
do 2 rewrite List.fold_left_app.
cbn - [ lap_norm ].
rewrite <- (lap_add_norm_idemp_l Hed).
rewrite IHn.
rewrite (lap_add_norm_idemp_l Hed).
rewrite (lap_add_norm_idemp_r Hed).
easy.
Qed.

Theorem lap_cons : ∀ a la, a :: la = ([a] + [0; 1]%L * la)%lap.
Proof.
intros.
destruct la as [| a2]; [ now cbn; rewrite rngl_add_0_r | cbn ].
unfold iter_seq, iter_list; cbn.
rewrite (rngl_mul_1_l Hon).
do 2 rewrite (rngl_mul_0_l Hos), rngl_add_0_r.
do 3 rewrite rngl_add_0_l.
rewrite List.app_nil_r.
f_equal; f_equal.
rewrite (lap_convol_mul_l_succ_l Hos).
rewrite List_map2_rngl_add_0_l.
now symmetry; apply (lap_convol_mul_1_l Hos).
Qed.

End a.

Declare Scope polyn_scope.
Delimit Scope polyn_scope with pol.

Notation "0" := polyn_zero : polyn_scope.
Notation "1" := polyn_one : polyn_scope.

Notation "a + b" := (polyn_add a b) : polyn_scope.
Notation "a * b" := (polyn_mul a b) : polyn_scope.
Notation "a / b" := (polyn_quot a b) : polyn_scope.
Notation "a 'mod' b" := (polyn_rem a b) : polyn_scope.
Notation "- a" := (polyn_opp a) : polyn_scope.
Notation "'mkp' x" := (mk_polyn x _) (at level 0, x at level 0): polyn_scope.

Arguments polyn_norm {T ro} la%_lap.
Arguments polyn_of_const {T ro} c%_L.
Arguments polyn_of_norm_lap {T ro} la%_lap.

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
  (Hop : rngl_has_opp T = true) :
    ring_like_op (polyn (square_matrix n T)) :=
  @polyn_ring_like_op _
    (mat_ring_like_op ro eqb) (@mat_ring_like_prop T ro rp Hop eqb n)
    eq_refl eq_refl.

Definition mat_polyn_ring_like_prop n T ro rp eqb
  (Hop : rngl_has_opp T = true) :
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
  (Heq : rngl_has_eq_dec T = true)
  (Hos : rngl_has_opp_or_subt T = true) :
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
  (Heq : rngl_has_eq_dec T = true) (Hop : rngl_has_opp T = true) :
    ring_like_prop (square_matrix n (polyn T)) :=
  @mat_ring_like_prop _
    (polyn_ring_like_op Heq (rngl_has_opp_has_opp_or_subt Hop))
    (@polyn_ring_like_prop _ ro rp Heq (rngl_has_opp_has_opp_or_subt Hop))
    (polyn_has_opp rp Heq Hop) (polyn_eqb eqb) n.
*)
