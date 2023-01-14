(* attempt to define algebraic numbers *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List ListNotations Init.Nat.

Require Import Misc RingLike IterAdd IterMul.
Require Import Polynomial Matrix Determinant.

(* Sylvester matrix *)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition rlap_sylvester_list_list (rla rlb : list T) : list (list T) :=
  let m := length rla - 1 in
  let n := length rlb - 1 in
  map (λ i, repeat 0%L i ++ rla ++ repeat 0%L (n - 1 - i)) (seq 0 n) ++
  map (λ i, repeat 0%L i ++ rlb ++ repeat 0%L (m - 1 - i)) (seq 0 m).

Definition rlap_sylvester_mat (rla rlb : list T) : matrix T :=
  mk_mat (rlap_sylvester_list_list rla rlb).

Definition polyn_sylvester_mat (p q : polyn T) : matrix T :=
  mk_mat (rlap_sylvester_list_list (rev (lap p)) (rev (lap q))).

Definition resultant (p q : polyn T) :=
  det (polyn_sylvester_mat p q).

Theorem last_fold_left_lap_mul_const_add_const : ∀ la b c,
  last (fold_left (λ accu a, (accu * [b] + [a])%lap) la [c]) 0%L =
  fold_left (λ x y, (x * b + y)%L) la c.
Proof.
intros.
revert c.
induction la as [| a]; intros; [ easy | cbn ].
rewrite rngl_summation_only_one.
apply IHla.
Qed.

Theorem last_lap_add : ∀ la lb,
  last (la + lb)%lap 0%L =
    if length la <? length lb then last lb 0%L
    else if length lb <? length la then last la 0%L
    else (last la 0 + last lb 0)%L.
Proof.
intros.
rewrite if_bool_if_dec.
destruct (bool_dec _) as [Hab| Hab]. {
  apply Nat.ltb_lt in Hab.
  revert lb Hab.
  induction la as [| a]; intros; [ easy | cbn ].
  destruct lb as [| b]; [ cbn in Hab; flia Hab | ].
  cbn in Hab.
  apply Nat.succ_lt_mono in Hab.
  specialize (IHla _ Hab).
  destruct lb as [| b1]; [ easy | ].
  rewrite List_last_cons_cons.
  destruct la as [| a1]; [ | easy ].
  cbn - [ last ].
  now rewrite List_last_cons_cons.
}
rewrite if_bool_if_dec.
destruct (bool_dec _) as [Hba| Hba]. {
  clear Hab.
  apply Nat.ltb_lt in Hba.
  revert la Hba.
  induction lb as [| b]; intros; [ now rewrite lap_add_0_r | ].
  destruct la as [| a]; [ cbn in Hba; flia Hba | ].
  cbn in Hba.
  apply Nat.succ_lt_mono in Hba.
  specialize (IHlb _ Hba).
  destruct la as [| a1]; [ easy | ].
  rewrite List_last_cons_cons.
  destruct lb as [| b1]; [ | easy ].
  cbn - [ last ].
  now rewrite List_last_cons_cons.
}
apply Nat.ltb_ge in Hab, Hba.
apply Nat.le_antisymm in Hab; [ clear Hba | easy ].
remember (length la) as len eqn:Ha.
rename Hab into Hb.
symmetry in Ha, Hb.
revert la lb Ha Hb.
induction len; intros; cbn. {
  apply length_zero_iff_nil in Ha, Hb; subst la lb.
  cbn; symmetry; apply rngl_add_0_l.
}
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
cbn in Ha, Hb.
apply Nat.succ_inj in Ha, Hb.
cbn - [ last ].
destruct la as [| a1]. {
  subst len.
  now apply length_zero_iff_nil in Hb; subst lb.
}
destruct lb as [| b1]; [ now rewrite <- Hb in Ha | ].
cbn - [ last ].
do 3 rewrite List_last_cons_cons.
now rewrite <- IHlen.
Qed.

Theorem List_last_map : ∀ A B a b (f : A → B) la,
  f a = b → last (map f la) b = f (last la a).
Proof.
intros * Hab.
induction la as [| a1]; [ easy | ].
cbn - [ last ].
destruct la as [| a2]; [ easy | ].
cbn - [ last ].
do 2 rewrite List_last_cons_cons.
apply IHla.
Qed.

Theorem last_lap_mul_const_l_add_const_r :
  rngl_has_opp_or_sous = true →
  ∀ a b la,
  last ([a] * la + [b])%lap 0%L =
    match length la with
    | 0 => b
    | 1 => (a * hd 0 la + b)%L
    | _ => last (map (λ b, (a * b)%L) (tl la)) 0%L
    end.
Proof.
intros Hos *.
induction la as [| a0]; [ easy | ].
destruct la as [| a1]. {
  cbn; unfold iter_seq, iter_list; cbn.
  now rewrite rngl_add_0_l.
}
cbn - [ lap_mul ].
rewrite last_lap_add.
cbn - [ last lap_mul ].
rewrite lap_mul_length.
rewrite app_length.
cbn - [ last lap_mul ].
rewrite if_bool_if_dec.
destruct (bool_dec _) as [H| H]; [ apply Nat.leb_le in H; flia H | clear H ].
rewrite if_bool_if_dec.
destruct (bool_dec _) as [H| H]; [ clear H | apply Nat.ltb_ge in H; flia H ].
cbn - [ last lap_mul ] in IHla.
rewrite last_lap_add in IHla.
cbn - [ last lap_mul ] in IHla.
rewrite if_bool_if_dec in IHla.
destruct (bool_dec _) as [H| H]. {
  cbn in H; apply Nat.leb_le in H; flia H.
}
clear H.
rewrite if_bool_if_dec in IHla.
destruct (bool_dec _) as [H| H]. 2: {
  cbn in H; apply Nat.leb_gt in H.
  rewrite lap_convol_mul_length in H.
  apply Nat.succ_lt_mono, Nat.lt_1_r in H.
  apply length_zero_iff_nil in H; subst la.
  cbn; unfold iter_seq, iter_list; cbn.
  now rewrite rngl_add_0_l, (rngl_mul_0_l Hos), rngl_add_0_r.
}
apply Nat.ltb_lt in H; cbn in H.
rewrite lap_convol_mul_length in H.
apply Nat.succ_lt_mono in H.
destruct la as [| a2]; [ easy | clear H ].
rewrite lap_mul_const_l; [ | easy | easy ].
rewrite (List_last_map 0%L); [ | apply (rngl_mul_0_r Hos) ].
rewrite (List_last_map 0%L); [ | apply (rngl_mul_0_r Hos) ].
now do 2 rewrite List_last_cons_cons.
Qed.

Theorem glop :
  rngl_has_eqb = true →
  ∀ p q,
  lap q ≠ []
  → has_polyn_prop (lap p ° lap q) = true.
Proof.
intros Heb * Hq.
destruct p as (la, pa).
destruct q as (lb, pb).
move lb before la.
cbn in Hq.
cbn - [ lap_compose ].
apply Bool.orb_true_iff in pa, pb.
apply Bool.orb_true_iff.
destruct pa as [pa| pa]. {
  now apply is_empty_list_empty in pa; subst la; left.
}
destruct pb as [pb| pb]. {
  now apply is_empty_list_empty in pb; subst lb.
}
right.
apply (rngl_neqb_neq Heb) in pa, pb.
Theorem last_lap_compose :
  rngl_has_opp_or_sous = true →
  ∀ la lb,
  last (la ° lb)%lap 0%L =
    match length lb with
    | 0 => hd 0%L la
    | 1 => eval_lap la (hd 0%L lb)
    | _ => (last la 0 * last lb 0 ^ (length la - 1))%L
    end.
Proof.
intros Hos *.
(* vérifier le cas "> 1" *)
(**)
destruct lb as [| b0]. {
  cbn; unfold lap_compose, rlap_compose; cbn.
  unfold rlap_horner, iter_list; cbn.
  erewrite List_fold_left_ext_in. 2: {
    intros b lb Hb.
    now rewrite lap_mul_0_r, lap_add_0_l.
  }
  destruct la as [| a]; [ easy | cbn ].
  now rewrite map_app, fold_left_app.
}
cbn - [ last ].
destruct lb as [| b1]. {
  cbn; unfold lap_compose, rlap_compose; cbn.
  unfold rlap_horner, iter_list; cbn.
  erewrite List_fold_left_ext_in. 2: {
    intros b lb Hb.
    rewrite lap_mul_const_r; [ | easy | easy ].
    easy.
  }
  destruct la as [| a]; [ easy | cbn ].
  rewrite map_app, fold_left_app; cbn.
  rewrite last_lap_add.
  rewrite map_length.
  remember (fold_left _ _ _) as lb eqn:Hlb.
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [H1| H1]. {
    subst lb.
    apply Nat.ltb_lt in H1; cbn in H1 |-*.
    apply Nat.lt_1_r, length_zero_iff_nil in H1.
    unfold eval_lap, eval_rlap, rlap_horner, iter_list; cbn.
    rewrite fold_left_app; cbn.
    destruct la as [| a0]; cbn. {
      now rewrite rngl_mul_0_l, rngl_add_0_l.
    }
    cbn in H1.
    rewrite map_app in H1; cbn in H1.
    rewrite fold_left_app in H1; cbn in H1.
    now apply eq_lap_add_nil in H1.
  }
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [H2| H2]. 2: {
    apply Nat.ltb_ge in H1, H2; cbn in H1, H2 |-*.
    apply Nat.le_antisymm in H1; [ clear H2 | easy ].
    destruct lb as [| b1]; [ easy | ].
    destruct lb; [ clear H1 | easy ].
    symmetry in Hlb; cbn.
...
    unfold eval_lap, eval_rlap, rlap_horner, iter_list; cbn.
    rewrite fold_left_app; cbn; f_equal; symmetry.
    destruct la as [| a0]; [ easy | ].
    cbn in Hlb |-*.
    rewrite map_app, fold_left_app in Hlb; cbn in Hlb.
    rewrite fold_left_app; cbn.
    destruct la as [| a1]; cbn. {
      rewrite rngl_mul_0_l; [ | easy ].
      rewrite rngl_add_0_l.
      cbn in Hlb.
      now injection Hlb; clear Hlb; intros; subst a0.
    }
    cbn in Hlb.
    rewrite map_app, fold_left_app in Hlb; cbn in Hlb.
...
}
cbn - [ last ].
...
unfold lap_compose.
remember (length lb) as blen eqn:Hbl; symmetry in Hbl.
destruct blen. {
  apply length_zero_iff_nil in Hbl; subst lb.
  unfold rlap_compose, rlap_horner, iter_list; cbn.
  erewrite List_fold_left_ext_in. 2: {
    intros b lb Hb.
    now rewrite lap_mul_0_r, lap_add_0_l.
  }
  destruct la as [| a]; [ easy | cbn ].
  now rewrite map_app, fold_left_app.
}
destruct blen. {
  unfold eval_lap, eval_rlap, rlap_horner, iter_list.
  remember (rev la) as rla; clear la Heqrla.
  destruct lb as [| b]; [ easy | ].
  destruct lb; [ cbn; clear Hbl | easy ].
  destruct rla as [| a2]; intros; [ easy | cbn ].
  rewrite (rngl_mul_0_l Hos), rngl_add_0_l.
  unfold rlap_compose, rlap_horner, iter_list; cbn.
  rewrite List_fold_left_map.
  apply last_fold_left_lap_mul_const_add_const.
}
unfold rlap_compose, rlap_horner, iter_list.
rewrite rev_involutive.
rewrite List_fold_left_map.
remember (rev la) as rla eqn:Hrla.
rewrite <- (rev_involutive la).
rewrite <- Hrla.
rewrite List_last_rev.
rewrite rev_length.
clear la Hrla.
destruct lb as [| b0]; [ easy | ].
cbn in Hbl.
apply Nat.succ_inj in Hbl.
destruct lb as [| b1]; intros; [ easy | ].
cbn in Hbl; apply Nat.succ_inj in Hbl.
destruct rla as [| a]. {
  now cbn; rewrite (rngl_mul_0_l Hos).
}
cbn - [ last ].
Theorem last_fold_left_lap_mul_cons_cons_add_const :
  ∀ (la lb lc : list T) (b0 b1 : T),
  last (fold_left (λ accu a, (accu * (b0 :: b1 :: lb) + [a])%lap) la lc)
    0%L =
  last (fold_left (λ accu a, (accu * (b1 :: lb) + [a])%lap) la lc) 0%L.
Admitted.
rewrite last_fold_left_lap_mul_cons_cons_add_const.
rewrite List_last_cons_cons.
clear b0 blen Hbl.
rewrite Nat.sub_0_r.
revert b1.
induction lb as [| b2]; intros. {
  cbn.
  rewrite last_fold_left_lap_mul_const_add_const.
  (* bin non *)
...
}
rewrite last_fold_left_lap_mul_cons_cons_add_const.
apply IHlb.
...
last_fold_left_lap_mul_add:
  ∀ (la : list T) (b c : T),
    last (fold_left (λ (accu : list T) (a : T), (accu * [b] + [a])%lap) la [c])
      0%L = fold_left (λ x y : T, (x * b + y)%L) la c
...
...
revert lb Hbl.
induction la as [| a]; intros; cbn. {
  symmetry; apply rngl_mul_1_r.
}
rewrite fold_left_app; cbn.
destruct la as [| a1]; [ now cbn; rewrite rngl_mul_1_r | cbn ].
rewrite List_cons_length in IHla.
rewrite Nat_sub_succ_1 in IHla.
destruct la as [| a2]. {
  rewrite app_nil_l, rngl_pow_0_r, rngl_mul_1_r.
  cbn - [ lap_mul ].
  rewrite lap_mul_0_l, lap_add_0_l.
  rewrite (last_lap_mul_const_l_add_const_r Hos).
  destruct lb as [| b0]; [ easy | ].
  destruct lb as [| b1]; [ easy | ].
  rewrite List_last_cons_cons.
  cbn - [ last ].
  clear Hbl.
  revert b1.
  induction lb as [| b2]; intros; [ easy | ].
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  apply IHlb.
}
specialize (IHla _ Hbl) as H1.
rewrite List_last_cons_cons in H1.
rewrite last_lap_add.
cbn - [ last ].
rewrite if_bool_if_dec.
destruct (bool_dec _) as [H2| H2]. {
  apply Nat.ltb_lt, Nat.lt_1_r, length_zero_iff_nil in H2.
  rewrite fold_left_app in H2.
  rewrite fold_left_app in H2.
  cbn in H2.
...
remember (a2 :: la) as l; cbn - [ last ] in H1; subst l.
...
  destruct lb as [| b1]; [ easy | ].
  rewrite List_last_cons_cons.
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l.
...
  rewrite lap_mul_const_l; [ | easy | easy ].
  rewrite lap_add_const_r; [ | easy ].
  rewrite List_map_tl.
...
rewrite map_tl.
Search ((_ + [_])%lap).
Search ((_ * [_])%lap).
...
Theorem List_last_map : ∀ A B (f : A → B) l d e,
  f e = d → last (map f l) d = f (last l e).
...
rewrite List_last_map.
...
  cbn.
  destruct lb as [| b0]; [ easy | ].
  cbn in Hbl; apply Nat.succ_inj in Hbl.
  destruct lb as [| b1]; [ easy | ].
  cbn in Hbl; apply Nat.succ_inj in Hbl.
  rewrite Nat.sub_0_r, rngl_mul_1_r.
  rewrite lap_convol_mul_const_l; [ | easy | easy | easy ].
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  clear Hbl.
  revert b1.
  induction lb as [| b2]; intros; [ easy | ].
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  apply IHlb.
}
rewrite fold_left_app; cbn.
rewrite List_last_cons_cons in IHla.
rewrite List_cons_length in IHla.
destruct la as [| a3]. {
  rewrite app_nil_l, rngl_pow_0_r, rngl_mul_1_r.
  cbn - [ lap_mul ].
  rewrite lap_mul_0_l, lap_add_0_l.
...
  cbn.
  destruct lb as [| b0]; [ easy | ].
  cbn in Hbl; apply Nat.succ_inj in Hbl.
  destruct lb as [| b1]; [ easy | ].
  cbn in Hbl; apply Nat.succ_inj in Hbl.
  rewrite Nat.sub_0_r, rngl_mul_1_r.
  rewrite List_last_cons_cons.
  do 2 rewrite List_cons_length.
  rewrite lap_convol_mul_const_l; [ | easy | easy | easy ].
  rewrite skipn_O.
  cbn - [ last ].
  rewrite Nat.add_succ_r.
  cbn - [ last ].
  rewrite List_last_cons_cons.
  rewrite Nat.add_succ_r.
  cbn - [ last ].
  rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l, map_length.
  destruct lb as [| b2]. {
    cbn.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    symmetry; apply rngl_mul_assoc.
  }
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l, Nat.add_succ_r.
  cbn - [ last ].
  rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l.
  destruct lb as [| b3]. {
    cbn.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    symmetry; apply rngl_mul_assoc.
  }
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l.
  destruct lb as [| b4]. {
    cbn.
    unfold iter_seq, iter_list; cbn.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite rngl_add_0_l.
    symmetry; apply rngl_mul_assoc.
  }
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l.
  destruct lb as [| b5]. {
    cbn.
    unfold iter_seq, iter_list; cbn.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite rngl_add_0_l.
    symmetry; apply rngl_mul_assoc.
  }
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l.
  rewrite Nat.add_succ_r; cbn - [ last ]; rewrite List_last_cons_cons.
  rewrite Nat.add_succ_r; cbn - [ last ]; rewrite List_last_cons_cons.
  rewrite Nat.add_succ_r; cbn - [ last ]; rewrite List_last_cons_cons.
  unfold iter_seq, iter_list; cbn - [ last ].
...
  ============================
  last
    ((0 + (a2 * b0 + a1) * nth 4 lb 0 + a2 * b1 * nth 3 lb 0 +
      a2 * b2 * nth 2 lb 0 + a2 * b3 * nth 1 lb 0 + 
      a2 * b4 * nth 0 lb 0 + a2 * b5 * b5 +
      nth 0 (map (λ b : A, a2 * b) lb) 0 * b4 +
      nth 1 (map (λ b : A, a2 * b) lb) 0 * b3 +
      nth 2 (map (λ b : A, a2 * b) lb) 0 * b2 +
      nth 3 (map (λ b : A, a2 * b) lb) 0 * b1 +
      nth 4 (map (λ b : A, a2 * b) lb) 0 * b0)%L
     :: lap_convol_mul
          ((a2 * b0 + a1)%L
           :: (a2 * b1)%L
              :: (a2 * b2)%L
                 :: (a2 * b3)%L
                    :: (a2 * b4)%L
                       :: (a2 * b5)%L :: map (λ b : A, (a2 * b)%L) lb)
          (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: lb) 11 
          (length lb + length lb)) 0%L =
  (a2 * (last (b5 :: lb) 0 * last (b5 :: lb) 0))%L
...

(*
résultant (selon le X) des polynomes Q et P(Y-X)
*)

End a.

(**)
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.

Compute (
  let rla := [2;3;5] in
  let rlb := [7;11] in
  last (rlap_compose rla rlb) 0).
...
2*7²
Compute (
  let la := [7;5;3;2] in
  let lb := [11;13] in
  last (lap_compose la lb) 0).
2*13³
(*
Compute (lap_compose Q_ring_like_op [-1;1] [1;0;1]).
Compute (lap_compose Q_ring_like_op [1;0;1] [-1;1]).
*)

Definition polyn_Q_ring_like_op :=
  @polyn_ring_like_op Q Q_ring_like_op Q_ring_like_prop eq_refl eq_refl
    (n_Sn _).

Check (@polyn_sylvester_mat _ polyn_Q_ring_like_op).
Check [mk_polyn [1;0;1] eq_refl]. (* x²+1) *)

Check (@lap_compose Q Q_ring_like_op).
Check lap_compose.
.
Print fold_right.
Theorem last_list_fold_right : ∀ A B (f : B → list A → list A) a l,
  last (fold_right f a l) = a.
...
erewrite List_fold_right_ext_in. 2: {
  intros c lc Hc.
  rewrite (lap_add_comm rp); cbn.
  easy.
}
...
  destruct la as [| a] using rev_ind; [ now left | right; cbn ].
  rewrite fold_right_app; cbn.
  rewrite last_last in pa.
  cbn.
...
}
...
Definition polyn_compose {A} {ro} (p q : polyn A) :=
  mk_polyn (lap_compose ro (lap p) (lap q)) (glop p q).

Print polyn_compose.

(* p sur K[x], p' sur L[x]
   calculer p (p') dans L[x]
ah non : tous les polynômes dans L[x]
voir lap_compose.
...
   Q[x] inclus dans Q[Q[x]].
*)
...

Check [mk_polyn [1;0;1] eq_refl]. (* x²+1) *)
Check [mk_polyn [-2;0;1] eq_refl]. (* x²-2) *)
Check (@mk_polyn (polyn Q)).
(*
Theorem glop :
  (@rngl_characteristic Q Q_ring_like_op Q_ring_like_prop) ≠ 1%nat.
Proof. easy. Show Proof.
...

Check (polyn_ring_like_op Q_ring_like_prop (n_Sn _)).
Check
  (@polyn_ring_like_op Q Q_ring_like_op Q_ring_like_prop eq_refl eq_refl (n_Sn _)).
Search rngl_characteristic.

Check mk_polyn.
Search has_polyn_prop.
*)

Compute (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4;5]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl)).
Compute (mat_nrows (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4;5]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl))).
Time Compute (det (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl))).
...
Compute (det (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4;5]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl))).
...
Compute (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9]).
Compute (mat_nrows (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (mat_ncols (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (is_square_matrix (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (let m := rlap_sylvester_mat [1;2;3;4] [6;7;8] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute (let m := rlap_sylvester_mat [1;2;3] [6;7] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute (let m := rlap_sylvester_mat [2] [6;7] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute (let m := rlap_sylvester_mat [2;3] [6] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
*)
