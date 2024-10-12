(* Misc2.v *)
(* Theorems of general usage, which could be (or not) in Coq library *)
(* Second file not used in ../trigo_without_pi *)

Require Import Utf8 Arith (*Psatz*).
Import List.ListNotations (*Init.Nat*).
(*
Open Scope list.
*)

Require Import Misc1.

Definition AllLt l u := ∀ i, i ∈ l → i < u.

Theorem List_app_cons : ∀ A la lb (b : A), la ++ b :: lb = la ++ [b] ++ lb.
Proof. easy. Qed.

Theorem List_app_eq_app' :
  ∀ (X : Type) (x1 x2 y1 y2 : list X),
    length x1 = length y1
    → x1 ++ x2 = y1 ++ y2
    → x1 = y1 ∧ x2 = y2.
Proof.
intros * Hxy Haa.
revert x2 y1 y2 Hxy Haa.
induction x1 as [| a1]; intros; cbn. {
  cbn in Hxy, Haa.
  symmetry in Hxy; apply List.length_zero_iff_nil in Hxy.
  now subst x2 y1.
}
destruct y1 as [| b1]; [ easy | ].
injection Haa; clear Haa; intros H1 H2; subst b1.
cbn in Hxy.
apply Nat.succ_inj in Hxy.
specialize (IHx1 x2 y1 y2 Hxy H1).
now destruct IHx1; subst y1 y2.
Qed.

Theorem List_hd_nth_0 {A} : ∀ l (d : A), List.hd d l = List.nth 0 l d.
Proof. intros; now destruct l. Qed.

Theorem List_app_hd1 : ∀ A (l l' : list A) d,
  0 < length l → List.hd d (l ++ l') = List.hd d l.
Proof.
intros.
do 2 rewrite List_hd_nth_0.
now apply List.app_nth1.
Qed.

Theorem List_app_hd2 : ∀ A (l l' : list A) d,
  length l = 0 → List.hd d (l ++ l') = List.hd d l'.
Proof.
intros.
do 2 rewrite List_hd_nth_0.
rewrite List.app_nth2; [ easy | ].
now apply Nat.le_0_r.
Qed.

Theorem List_butn_0_cons : ∀ A (a : A) la, List_butn 0 (a :: la) = la.
Proof. easy. Qed.

Theorem if_ltb_lt_dec : ∀ A i j (a b : A),
  (if i <? j then a else b) = (if lt_dec i j then a else b).
Proof.
intros.
destruct (lt_dec i j) as [H1| H1]. {
  now apply Nat.ltb_lt in H1; rewrite H1.
}
now apply Nat.ltb_nlt in H1; rewrite H1.
Qed.

Theorem List_butn_app : ∀ A (l1 l2 : list A) i,
  List_butn i (l1 ++ l2) =
    if i <? length l1 then List_butn i l1 ++ l2
    else l1 ++ List_butn (i - length l1) l2.
Proof.
intros.
rewrite if_ltb_lt_dec.
progress unfold List_butn.
rewrite List.firstn_app, List.skipn_app.
destruct (lt_dec i (length l1)) as [Hil| Hil]. {
  rewrite (proj2 (Nat.sub_0_le i _)); [ | now apply Nat.lt_le_incl ].
  rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
  rewrite List.firstn_O, List.skipn_O, List.app_nil_r.
  apply List.app_assoc.
} {
  apply Nat.nlt_ge in Hil.
  rewrite List.firstn_all2; [ | easy ].
  rewrite List.skipn_all2. 2: {
    now apply Nat.lt_le_incl; apply -> Nat.succ_le_mono.
  }
  rewrite List.app_nil_l.
  rewrite Nat.sub_succ_l; [ | easy ].
  symmetry; apply List.app_assoc.
}
Qed.

Theorem List_butn_app_cons :
  ∀ A i b (la lb : list A),
  i = length la
  → List_butn i (la ++ b :: lb) = la ++ lb.
Proof.
intros * Hia.
progress unfold List_butn.
rewrite List.firstn_app.
rewrite Hia, Nat.sub_diag, List.firstn_O, List.app_nil_r.
rewrite List.firstn_all2; [ | easy ].
rewrite List.skipn_app.
rewrite Nat.sub_succ_l, Nat.sub_diag; [ | easy ].
rewrite List.skipn_all2; [ | flia ].
now rewrite List.skipn_cons, List.skipn_O.
Qed.

Theorem List_cons_is_app : ∀ {A} (a : A) la, a :: la = [a] ++ la.
Proof. easy. Qed.

Theorem List_cons_length : ∀ A (a : A) la, length (a :: la) = S (length la).
Proof. easy. Qed.

Theorem List_eq_iff : ∀ A (l1 l2 : list A),
  l1 = l2 ↔
    (length l1 = length l2 ∧ ∀ d i, List.nth i l1 d = List.nth i l2 d).
Proof.
split; [ now intros; subst l2 | ].
intros (Hlen & Hll).
revert l2 Hlen Hll.
induction l1 as [| a1]; intros. {
  symmetry in Hlen.
  now apply List.length_zero_iff_nil in Hlen.
}
destruct l2 as [| a2]; [ easy | ].
cbn in Hlen.
apply Nat.succ_inj in Hlen.
f_equal; [ apply (Hll a1 0) | ].
apply IHl1; [ easy | ].
intros.
now specialize (Hll d (S i)).
Qed.

Theorem List_eq_map2_nil : ∀ A B C (f : A → B → C) la lb,
  List_map2 f la lb = [] → la = [] ∨ lb = [].
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros; [ now left | right ].
cbn in Hab.
now destruct lb.
Qed.

Theorem List_eq_rev_nil {A} : ∀ (l : list A), List.rev l = [] → l = [].
Proof.
intros * Hl.
destruct l as [| a]; [ easy | cbn in Hl ].
now apply List.app_eq_nil in Hl.
Qed.

Theorem List_filter_nil_iff {A} : ∀ f (l : list A),
  List.filter f l = [] ↔ (∀ a, a ∈ l → f a = false).
Proof.
intros.
split. {
  intros Hf a Ha.
  induction l as [| b l]; [ easy | ].
  cbn in Hf.
  remember (f b) as c eqn:Hc; symmetry in Hc.
  destruct c; [ easy | ].
  destruct Ha as [Ha| Ha]; [ now subst b | ].
  now apply IHl.
} {
  intros Hf.
  induction l as [| a]; [ easy | cbn ].
  rewrite Hf; [ | now left ].
  apply IHl.
  intros b Hb.
  now apply Hf; right.
}
Qed.

Theorem List_fold_butn : ∀ A n (l : list A),
  List.firstn n l ++ List.skipn (S n) l = List_butn n l.
Proof. easy. Qed.

Theorem List_fold_left_map2 :
  ∀ A B C D (f : A → B → A) (g : C → D → B) lc ld (a : A),
  List.fold_left f (List_map2 g lc ld) a =
  List.fold_left (λ b c, f b (g (fst c) (snd c))) (List.combine lc ld) a.
Proof.
intros.
revert ld a.
induction lc as [| c]; intros; [ easy | cbn ].
destruct ld as [| d]; [ easy | cbn ].
apply IHlc.
Qed.

Theorem List_fold_left_map_nth_len : ∀ A (la : list A) sta len f d,
  List.fold_left
    (λ lb k, List.map (λ i, List.nth (f k i) lb d) (List.seq 0 (length lb)))
    (List.seq sta len) la =
  List.fold_left
    (λ lb k, List.map (λ i, List.nth (f k i) lb d) (List.seq 0 (length la)))
    (List.seq sta len) la.
Proof.
intros.
revert sta la.
induction len; intros; [ easy | cbn ].
rewrite IHlen.
apply List_fold_left_ext_in.
intros i lb Hi; apply List.in_seq in Hi.
now rewrite List.length_map, List.length_seq.
Qed.

Theorem List_fold_left_nop_r : ∀ A B (a : A) (lb : list B) (f : A → _),
  List.fold_left (λ c _, f c) lb a = List_repeat_apply (length lb) f a.
Proof.
intros.
revert a.
induction lb as [| b]; intros; [ easy | cbn ].
apply IHlb.
Qed.

Theorem List_fold_right_max_ge : ∀ m l, m ≤ List.fold_right max m l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
etransitivity; [ apply IHl | ].
apply Nat.le_max_r.
Qed.

Theorem List_hd_in : ∀ A (l : list A) d, 0 < length l → List.hd d l ∈ l.
Proof.
intros.
rewrite List_hd_nth_0.
now apply List.nth_In.
Qed.

Theorem List_butn_nil : ∀ A n, List_butn n ([] : list A) = [].
Proof. now intros; destruct n. Qed.

Theorem List_butn_succ_cons :
  ∀ A (a : A) la n, List_butn (S n) (a :: la) = a :: List_butn n la.
Proof.
intros.
progress unfold List_butn.
now rewrite List.firstn_cons, List.skipn_cons.
Qed.

Theorem List_in_butn : ∀ A (l : list A) i a, a ∈ List_butn i l → a ∈ l.
Proof.
intros * Ha.
revert i Ha.
induction l as [| b]; intros. {
  now rewrite List_butn_nil in Ha.
}
destruct i; [ now right | ].
rewrite List_butn_succ_cons in Ha.
destruct Ha as [Ha| Ha]; [ now left | right ].
now apply IHl in Ha.
Qed.

Theorem List_in_combine_same :
  ∀ A (i j : A) l, (i, j) ∈ List.combine l l → i = j.
Proof.
intros * Hij.
induction l as [| a la]; [ easy | cbn in Hij ].
destruct Hij as [Hij| Hij]; [ now injection Hij; intros; subst i j | ].
now apply IHla.
Qed.

Theorem List_in_map2_iff : ∀ A B C (f : A → B → C) la lb c,
  c ∈ List_map2 f la lb ↔
  ∃ i,
  i < min (length la) (length lb) ∧
  ∃ a b, f (List.nth i la a) (List.nth i lb b) = c.
Proof.
intros.
split. {
  intros Hc.
  revert lb Hc.
  induction la as [| a]; intros; [ easy | ].
  destruct lb as [| b]; [ easy | ].
  cbn in Hc.
  destruct Hc as [Hc| Hc]. {
    exists 0.
    split; [ cbn; flia | now exists a, b ].
  }
  specialize (IHla _ Hc) as H1.
  destruct H1 as (i & Him & a' & b' & Hi).
  exists (S i).
  split; [ cbn; flia Him | ].
  now exists a', b'.
} {
  intros (i & Him & a' & b' & Hi).
  revert lb i Him Hi.
  induction la as [| a]; intros; [ easy | ].
  destruct lb as [| b]; [ easy | ].
  cbn in Him, Hi |-*.
  destruct i; [ now left | right ].
  apply Nat.succ_lt_mono in Him.
  now apply IHla in Hi.
}
Qed.

Theorem List_last_nth : ∀ A (la : list A) d,
  List.last la d = List.nth (length la - 1) la d.
Proof.
intros.
destruct la as [| a] using List.rev_ind; [ easy | cbn ].
rewrite List.last_last, List.length_app, Nat.add_sub.
rewrite List.app_nth2; [ | now progress unfold ge ].
now rewrite Nat.sub_diag.
Qed.

Theorem List_last_rev : ∀ A (l : list A) d,
  List.last (List.rev l) d = List.hd d l.
Proof.
intros.
destruct l as [| a]; [ easy | apply List.last_last ].
Qed.

Theorem List_butn_out : ∀ A (l : list A) i, length l ≤ i → List_butn i l = l.
Proof.
intros * Hi.
revert i Hi.
induction l as [| a]; intros; [ apply List_butn_nil | ].
destruct i; [ easy | ].
cbn in Hi; apply Nat.succ_le_mono in Hi.
rewrite List_butn_succ_cons.
now rewrite IHl.
Qed.

Theorem List_length_butn : ∀ A n (l : list A),
  length (List_butn n l) = length l - Nat.b2n (n <? length l).
Proof.
intros.
progress unfold Nat.b2n; rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool (n <? length l)) as [Hnl| Hnl]. 2: {
  apply Nat.ltb_ge in Hnl; rewrite Nat.sub_0_r.
  now rewrite List_butn_out.
}
apply Nat.ltb_lt in Hnl.
revert n Hnl.
induction l as [| a]; intros; [ easy | ].
cbn; rewrite Nat.sub_0_r.
destruct n; [ easy | ].
rewrite List_butn_succ_cons; cbn.
cbn in Hnl.
apply Nat.succ_lt_mono in Hnl.
rewrite IHl; [ | easy ].
destruct (length l); [ easy | ].
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem List_length_map2 : ∀ A B C (f : A → B → C) la lb,
  length (List_map2 f la lb) = min (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem List_length_map_seq : ∀ A (f : _ → A) a len,
  length (List.map f (List.seq a len)) = len.
Proof.
intros.
now rewrite List.length_map, List.length_seq.
Qed.

Theorem List_map2_app_app :
  ∀ A B C la lb lc ld (f : A → B → C),
  length la = length lb
  → List_map2 f (la ++ lc) (lb ++ ld) =
    List_map2 f la lb ++ List_map2 f lc ld.
Proof.
intros * Hab.
revert lb lc ld Hab.
induction la as [| a]; intros; cbn. {
  now symmetry in Hab; apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | cbn ].
cbn in Hab; apply Nat.succ_inj in Hab; f_equal.
now apply IHla.
Qed.

Theorem List_map2_diag : ∀ A B (f : A → A → B) la,
  List_map2 f la la = List.map (λ i, f i i) la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem List_map2_map_l :
  ∀ A B C D (f : C → B → D) g (la : list A) (lb : list B),
  List_map2 f (List.map g la) lb = List_map2 (λ a b, f (g a) b) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
apply IHla.
Qed.

Theorem List_map2_map2_seq_l : ∀ {A B C} d (f : A → B → C) la lb,
  List_map2 f la lb =
    List_map2 (λ i b, f (List.nth i la d) b) (List.seq 0 (length la)) lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
f_equal.
rewrite <- List.seq_shift.
rewrite List_map2_map_l.
apply IHla.
Qed.

Theorem List_map2_map_r :
  ∀ A B C D (f : A → C → D) g (la : list A) (lb : list B),
  List_map2 f la (List.map g lb) = List_map2 (λ a b, f a (g b)) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
apply IHla.
Qed.

Theorem List_map2_map2_seq_r : ∀ {A B C} d (f : A → B → C) la lb,
  List_map2 f la lb =
    List_map2 (λ a i, f a (List.nth i lb d)) la (List.seq 0 (length lb)).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
rewrite <- List.seq_shift.
rewrite List_map2_map_r.
apply IHla.
Qed.

Theorem List_nth_0_cons : ∀ A (a : A) la d, List.nth 0 (a :: la) d = a.
Proof. easy. Qed.

Theorem List_map_seq : ∀ A (f : _ → A) sta len,
  List.map f (List.seq sta len) =
    List.map (λ i, f (sta + i)) (List.seq 0 len).
Proof.
intros.
revert sta.
induction len; intros; [ easy | cbn ].
symmetry.
rewrite <- List.seq_shift, List.map_map.
rewrite Nat.add_0_r; f_equal.
symmetry.
rewrite IHlen.
apply List.map_ext_in.
intros i Hi.
now rewrite Nat.add_succ_comm.
Qed.

Theorem List_map2_map_min :
  ∀ {A B C} ad bd la lb (f : A → B → C),
  List_map2 f la lb =
    List.map (λ i, f (List.nth i la ad) (List.nth i lb bd))
      (List.seq 0 (min (length la) (length lb))).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | ].
destruct lb as [| b]; [ easy | ].
cbn - [ List.nth ].
do 2 rewrite List_nth_0_cons.
f_equal.
rewrite List_map_seq.
rewrite IHla.
apply List.map_ext_in.
intros i Hi.
do 2 rewrite List_nth_succ_cons.
easy.
Qed.

Theorem List_map2_nil_l : ∀ A B C (f : A → B → C) la, List_map2 f [] la = [].
Proof.
intros.
now destruct la.
Qed.

Theorem List_map2_nth : ∀ {A B C} a b c (f : A → B → C) la lb n,
  n < length la
  → n < length lb
  → List.nth n (List_map2 f la lb) c = f (List.nth n la a) (List.nth n lb b).
Proof.
intros * Hla Hlb.
revert n lb Hla Hlb.
induction la as [| a']; intros; [ easy | cbn ].
destruct lb as [| b']; [ easy | cbn ].
destruct n; [ easy | cbn ].
cbn in Hla, Hlb.
apply Nat.succ_lt_mono in Hla.
apply Nat.succ_lt_mono in Hlb.
destruct n; [ now apply IHla | ].
now apply IHla.
Qed.

Theorem List_map2_nil_r : ∀ A B C (f : A → B → C) la, List_map2 f la [] = [].
Proof.
intros.
now destruct la.
Qed.

Theorem List_map2_swap : ∀ A B C (f : A → B → C) la lb,
  List_map2 f la lb = List_map2 (λ a b, f b a) lb la.
Proof.
intros.
revert lb.
induction la as [| a]; intros; cbn; [ symmetry; apply List_map2_nil_r | ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
apply IHla.
Qed.

Theorem List_map2_ext_in : ∀ A B C (f g : A → B → C) la lb,
  (∀ ab, ab ∈ List.combine la lb → f (fst ab) (snd ab) = g (fst ab) (snd ab))
  → List_map2 f la lb = List_map2 g la lb.
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
f_equal. {
  apply (Hab _ (or_introl eq_refl)).
}
apply IHla.
intros i Hi.
now apply Hab; right.
Qed.

Theorem List_map2_rev_seq_r : ∀ A B (f : A → _ → B) la sta len,
  List_map2 f la (List.rev (List.seq sta len)) =
  List_map2 (λ a i, f a (2 * sta + len - 1 - i)) la (List.seq sta len).
Proof.
intros.
rewrite List_map2_swap; symmetry.
rewrite List_map2_swap; symmetry.
revert la sta.
induction len; intros; [ easy | ].
replace (2 * sta + S len - 1) with (2 * sta + len) by flia.
rewrite List.seq_S at 1.
cbn - [ List_map2 ].
rewrite Nat.add_0_r.
rewrite List.rev_app_distr.
cbn - [ List_map2 ].
cbn.
destruct la as [| a]; [ easy | ].
rewrite Nat.add_shuffle0, Nat.add_sub; f_equal.
rewrite IHlen.
rewrite <- List.seq_shift.
rewrite List_map2_map_l.
clear a.
apply List_map2_ext_in.
intros (i, a) Hia; cbn.
f_equal; flia.
Qed.

Theorem List_map_butn : ∀ A B (f : A → B) la n,
  List.map f (List_butn n la) = List_butn n (List.map f la).
Proof.
intros.
revert n.
induction la as [| a]; intros; cbn; [ now do 2 rewrite List_butn_nil | ].
destruct n; [ easy | ].
do 2 rewrite List_butn_succ_cons.
cbn; f_equal.
apply IHla.
Qed.

Theorem if_leb_le_dec : ∀ A i j (a b : A),
  (if i <=? j then a else b) = (if le_dec i j then a else b).
Proof.
intros.
destruct (le_dec i j) as [H1| H1]. {
  now apply Nat.leb_le in H1; rewrite H1.
}
now apply Nat.leb_nle in H1; rewrite H1.
Qed.

Theorem List_map_butn_seq : ∀ A (f : _ → A) n sta len,
  List.map f (List_butn n (List.seq sta len)) =
  List.map (λ i, f (i + Nat.b2n (sta + n <=? i)))
    (List.seq sta (len - Nat.b2n (n <? len))).
Proof.
intros.
revert n sta.
induction len; intros; [ now rewrite List_butn_nil | ].
destruct n. {
  cbn; rewrite Nat.sub_0_r, Nat.add_0_r.
  rewrite <- List.seq_shift.
  rewrite List.map_map.
  apply List.map_ext_in.
  intros i Hi.
  apply List.in_seq in Hi.
  rewrite <- Nat.add_1_r.
  destruct (le_dec sta i) as [H| H]; [ | easy ].
  now apply Nat.leb_le in H; rewrite H.
}
progress unfold Nat.b2n.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool (S n <? S len)) as [Hn| Hn]. {
  apply Nat.ltb_lt in Hn.
  cbn - [ List_butn ].
  rewrite Nat.sub_0_r, List_butn_succ_cons; cbn.
  apply Nat.succ_lt_mono in Hn.
  rewrite IHlen.
  destruct len; [ easy | ].
  progress unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec n (S len)) as [H| H]; [ clear H | easy ].
  rewrite Nat_sub_succ_1; cbn - [ "<=?" ].
  f_equal. {
    rewrite if_leb_le_dec.
    destruct (le_dec (sta + S n) sta) as [H| H]; [ flia H | clear H ].
    now rewrite Nat.add_0_r.
  }
  apply List.map_ext_in.
  intros i Hi.
  now rewrite (Nat.add_succ_r sta).
} {
  apply Nat.ltb_ge in Hn.
  rewrite Nat.sub_0_r.
  rewrite List_butn_out; [ | now rewrite List.length_seq ].
  apply List.map_ext_in.
  intros i Hi.
  apply List.in_seq in Hi.
  rewrite if_leb_le_dec.
  destruct (le_dec (sta + S n) i) as [H| H]; [ flia Hn Hi H | ].
  now rewrite Nat.add_0_r.
}
Qed.

Theorem List_map_fun : ∀ A B d l l' (f g : A → B),
  length l = length l'
  → (∀ i, i < length l → f (List.nth i l d) = g (List.nth i l' d))
  → List.map f l = List.map g l'.
Proof.
intros * Hlen Hf.
revert l' Hlen Hf.
induction l as [| a l]; intros; [ now destruct l' | ].
destruct l' as [| a' l']; [ easy | cbn ].
specialize (Hf 0 (Nat.lt_0_succ _)) as H1; cbn in H1.
rewrite H1; f_equal.
cbn in Hlen; apply Nat.succ_inj in Hlen.
apply IHl; [ easy | ].
intros i Hi.
apply Hf with (i := S i); cbn.
now apply -> Nat.succ_lt_mono.
Qed.

Theorem List_map_nth' : ∀ {A B} a b (f : A → B) l n,
  n < length l → List.nth n (List.map f l) b = f (List.nth n l a).
Proof.
intros * Hnl.
revert n Hnl.
induction l as [| c l]; intros; [ easy | ].
cbn in Hnl; cbn.
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hnl.
now apply IHl.
Qed.

Theorem List_map_hd : ∀ {A B} a b (f : A → B) l,
  0 < length l → List.hd b (List.map f l) = f (List.hd a l).
Proof.
intros.
do 2 rewrite List_hd_nth_0.
now apply List_map_nth'.
Qed.

Theorem List_map_map2 : ∀ A B C D (f : A → B) (g : C → D → A) la lb,
  List.map f (List_map2 g la lb) = List_map2 (λ a b, f (g a b)) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem List_map_map_seq : ∀ {A B} d (f : A → B) la,
  List.map f la =
    List.map (λ i, f (List.nth i la d)) (List.seq 0 (length la)).
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
f_equal.
rewrite <- List.seq_shift.
now rewrite List.map_map.
Qed.

Theorem List_map_nth_seq : ∀ {A} d (la : list A),
  la = List.map (λ i, List.nth i la d) (List.seq 0 (length la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn; f_equal.
rewrite <- List.seq_shift.
now rewrite List.map_map.
Qed.

Theorem List_map_nth_seq' : ∀ A d (la : list A) n,
  n = length la
  → la = List.map (λ i, List.nth i la d) (List.seq 0 n).
Proof.
intros * Hn.
subst n.
apply List_map_nth_seq.
Qed.

Theorem List_map_repeat : ∀ A B x n (f : A → B),
  List.map f (List.repeat x n) = List.repeat (f x) n.
Proof.
intros.
induction n; [ easy | cbn ].
f_equal; apply IHn.
Qed.

Theorem List_map_rev_seq : ∀ A (f : _ → A) sta len,
  List.map f (List.rev (List.seq sta len)) =
    List.map (λ i, f (2 * sta + len - 1 - i)) (List.seq sta len).
Proof.
intros.
revert sta.
induction len; intros; [ easy | ].
rewrite List.seq_S at 1.
rewrite List.rev_app_distr.
cbn.
rewrite Nat.add_0_r.
rewrite Nat.add_succ_r.
rewrite Nat_sub_succ_1.
rewrite Nat.add_shuffle0, Nat.add_sub.
f_equal.
rewrite IHlen.
rewrite <- List.seq_shift.
rewrite List.map_map.
apply List.map_ext_in.
intros; f_equal; flia.
Qed.

Theorem List_nth_app_repeat_r :
  ∀ A (d : A) i n la,
  List.nth i (la ++ List.repeat d n) d = List.nth i la d.
Proof.
intros.
destruct (lt_dec i (length la)) as [Hila| Hila]. {
  now apply List.app_nth1.
}
apply Nat.nlt_ge in Hila.
rewrite List.app_nth2; [ | easy ].
now rewrite List.nth_repeat, List.nth_overflow.
Qed.

Theorem List_nth_butn_before : ∀ A (l : list A) i j d,
  j ≤ i
  → List.nth i (List_butn j l) d = List.nth (i + 1) l d.
Proof.
intros * Hji.
revert i j Hji.
induction l as [| a]; intros; cbn. {
  rewrite List_butn_nil.
  now destruct i.
}
destruct j; [ now rewrite Nat.add_1_r | ].
destruct i; [ easy | ].
apply Nat.succ_le_mono in Hji.
rewrite List_butn_succ_cons; cbn.
now apply IHl.
Qed.

Theorem List_nth_butn_after : ∀ A (l : list A) i j d,
  i < j
  → List.nth i (List_butn j l) d = List.nth i l d.
Proof.
intros * Hij.
revert i j Hij.
induction l as [| a]; intros; cbn. {
  rewrite List_butn_nil.
  now destruct i.
}
destruct j; [ easy | ].
destruct i; [ easy | ].
apply Nat.succ_lt_mono in Hij.
rewrite List_butn_succ_cons; cbn.
now apply IHl.
Qed.

Theorem List_nth_butn : ∀ A (l : list A) i j d,
  List.nth i (List_butn j l) d = List.nth (i + Nat.b2n (j <=? i)) l d.
Proof.
intros.
remember (j <=? i) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply Nat.leb_le in Hb.
  now rewrite List_nth_butn_before.
} {
  apply Nat.leb_gt in Hb.
  rewrite List_nth_butn_after; [ | easy ].
  now rewrite Nat.add_0_r.
}
Qed.

Theorem List_nth_firstn : ∀ A (l : list A) i j d,
  i < j
  → List.nth i (List.firstn j l) d = List.nth i l d.
Proof.
intros * Hij.
revert i j Hij.
induction l as [| a la]; intros; [ now rewrite List.firstn_nil | ].
destruct j; [ easy | ].
rewrite List.firstn_cons.
destruct i; [ easy | cbn ].
apply IHla.
now apply Nat.succ_lt_mono.
Qed.

Theorem List_nth_nil : ∀ A i (d : A), List.nth i [] d = d.
Proof. now intros; destruct i. Qed.

Theorem List_nth_repeat : ∀ A (a d : A) i n,
  List.nth i (List.repeat a n) d = if lt_dec i n then a else d.
Proof.
intros A *.
destruct (lt_dec i n) as [Hin| Hin]. {
  revert i Hin.
  induction n; intros; [ easy | cbn ].
  destruct i; [ easy | ].
  apply Nat.succ_lt_mono in Hin.
  now apply IHn.
}
apply Nat.nlt_ge in Hin.
apply List.nth_overflow.
now rewrite List.repeat_length.
Qed.

Theorem List_nth_skipn : ∀ A (l : list A) i j d,
  List.nth i (List.skipn j l) d = List.nth (i + j) l d.
Proof.
intros.
revert i j.
induction l as [| a la]; intros. {
  rewrite List.skipn_nil; cbn.
  now destruct i, j.
}
destruct j; [ now rewrite Nat.add_0_r | ].
rewrite Nat.add_succ_r; cbn.
apply IHla.
Qed.

Theorem List_rank_loop_interv : ∀ {A} f (l : list A) i,
  i ≤ List_rank_loop i f l ≤ i + length l.
Proof.
intros.
revert i.
induction l as [| a]; intros; cbn; [ now rewrite Nat.add_0_r | ].
destruct (f a). {
  split; [ easy | ].
  apply Nat.le_add_r.
}
specialize (IHl (S i)).
rewrite Nat.add_succ_comm in IHl.
split; [ flia IHl | easy ].
Qed.

Theorem List_rank_loop_if : ∀ A d f (l : list A) i j,
  List_rank_loop i f l = j
  → (∀ k, i ≤ k < j → f (List.nth (k - i) l d) = false) ∧
    (j < i + length l ∧ f (List.nth (j - i) l d) = true ∨
     j = i + length l).
Proof.
intros * Hi.
split. {
  intros p Hp.
  remember (p - i) as k eqn:Hk.
  replace p with (i + k) in Hp by flia Hp Hk.
  destruct Hp as (_, Hp).
  clear p Hk.
  revert i l Hi Hp.
  induction k; intros. {
    rewrite Nat.add_0_r in Hp.
    destruct l as [| a]. {
      now subst j; apply Nat.lt_irrefl in Hp.
    }
    cbn in Hi |-*.
    destruct (f a); [ | easy ].
    now subst j; apply Nat.lt_irrefl in Hp.
  }
  destruct l as [| a]; [ subst j; cbn in Hp; flia Hp | ].
  cbn in Hi |-*.
  rewrite <- Nat.add_succ_comm in Hp.
  remember (f a) as b eqn:Hb; symmetry in Hb.
  destruct b; [ subst j; flia Hp | ].
  now apply IHk with (i := S i).
}
remember (j - i) as k eqn:Hk.
replace j with (i + k) in Hi |-*. 2: {
  specialize (List_rank_loop_interv f l i) as H1.
  rewrite Hi in H1.
  flia Hk H1.
}
clear j Hk.
revert i l Hi.
induction k; intros. {
  rewrite Nat.add_0_r in Hi |-*.
  destruct l; [ now right; symmetry; apply Nat.add_0_r | ].
  left; cbn in Hi |-*.
  split; [ flia | ].
  destruct (f a); [ easy | ].
  specialize (List_rank_loop_interv f l (S i)) as H1.
  rewrite Hi in H1; flia H1.
}
destruct l; cbn in Hi; [ flia Hi | ].
destruct (f a); [ flia Hi | cbn in Hi ].
rewrite <- Nat.add_succ_comm in Hi.
apply IHk in Hi; cbn.
now do 2 rewrite <- Nat.add_succ_comm.
Qed.

Theorem List_rank_if : ∀ {A} d f (l : list A) {i},
  List_rank f l = i
  → (∀ j, j < i → f (List.nth j l d) = false) ∧
    (i < length l ∧ f (List.nth i l d) = true ∨ i = length l).
Proof.
intros * Hi.
apply List_rank_loop_if with (d := d) in Hi.
rewrite Nat.sub_0_r in Hi; cbn in Hi.
destruct Hi as (Hbef, Hat).
split; [ | easy ].
intros j Hj.
specialize (Hbef j).
rewrite Nat.sub_0_r in Hbef.
now apply Hbef.
Qed.

Theorem List_repeat_apply_id : ∀ A len f (a : A),
  (∀ a, f a = a)
  → List_repeat_apply len f a = a.
Proof.
intros * Hid.
revert a.
induction len; intros; [ easy | cbn ].
rewrite IHlen.
apply Hid.
Qed.

Theorem List_map2_app_l : ∀ A B C l1 l2 l (f : A → B → C),
  List_map2 f (l1 ++ l2) l =
    List_map2 f l1 (List.firstn (length l1) l) ++
    List_map2 f l2 (List.skipn (length l1) l).
Proof.
intros.
revert l2 l.
induction l1 as [| a1]; intros; [ easy | cbn ].
destruct l as [| a]; [ now rewrite List_map2_nil_r | cbn ].
f_equal.
apply IHl1.
Qed.

Theorem List_rev_map2 : ∀ A B C (f : A → B → C) la lb,
  length la = length lb
  → List.rev (List_map2 f la lb) = List_map2 f (List.rev la) (List.rev lb).
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; cbn; [ symmetry; apply List_map2_nil_r | ].
cbn in Hab; apply Nat.succ_inj in Hab.
rewrite (IHla _ Hab).
rewrite List_map2_app_l.
rewrite List.firstn_app.
do 2 rewrite List.length_rev.
rewrite Hab, Nat.sub_diag; cbn.
rewrite List.app_nil_r.
rewrite <- (List.length_rev lb).
rewrite List.firstn_all.
f_equal.
rewrite List.length_rev.
rewrite List.skipn_app.
rewrite List.length_rev, Nat.sub_diag; cbn.
rewrite <- (List.length_rev lb).
rewrite List.skipn_all.
easy.
Qed.

Theorem List_rev_repeat : ∀ {A} (x : A) n,
  List.rev (List.repeat x n) = List.repeat x n.
Proof.
intros.
induction n; [ easy | cbn ].
rewrite List.repeat_cons; f_equal.
apply IHn.
Qed.

Theorem List_rev_rev :
  ∀ A (la lb : list A), List.rev la = List.rev lb → la = lb.
Proof.
intros * Hab.
apply (f_equal (λ l, List.rev l)) in Hab.
now do 2 rewrite List.rev_involutive in Hab.
Qed.

Theorem List_rev_seq_nth :
  ∀ len sta n d, n < len →
  List.nth n (List.rev (List.seq sta len)) d = sta + len - S n.
Proof.
intros * Hn.
revert sta.
induction len; intros; [ easy | ].
cbn.
destruct (Nat.eq_dec n len) as [Hnl| Hnl]. {
  subst n.
  rewrite List.app_nth2. 2: {
    now rewrite List.length_rev, List.length_seq; progress unfold ge.
  }
  rewrite List.length_rev, List.length_seq, Nat.sub_diag; cbn.
  now rewrite Nat.add_sub.
}
assert (H : n < len) by flia Hn Hnl.
specialize (IHlen H).
rewrite List.app_nth1; [ | now rewrite List.length_rev, List.length_seq ].
rewrite IHlen.
now rewrite Nat.add_succ_r.
Qed.

Theorem List_rev_symm :
  ∀ A (la lb : list A), List.rev la = lb → la = List.rev lb.
Proof.
intros * Hab.
now subst lb; rewrite List.rev_involutive.
Qed.

Theorem List_seq_cut : ∀ i sta len,
  i ∈ List.seq sta len
  → List.seq sta len = List.seq sta (i - sta) ++ List.seq i (sta + len - i).
Proof.
intros * His.
apply List.in_seq in His.
replace len with (i - sta + (len - (i - sta))) at 1 by flia His.
rewrite List.seq_app.
f_equal.
replace (sta + (i - sta)) with i by flia His.
f_equal.
flia His.
Qed.

Theorem List_seq_cut3 : ∀ i sta len,
  i ∈ List.seq sta len
  → List.seq sta len =
      List.seq sta (i - sta) ++ [i] ++ List.seq (S i) (sta + len - S i).
Proof.
intros * His.
apply List.in_seq in His.
replace len with (i - sta + (len - (i - sta))) at 1 by flia His.
rewrite List.seq_app.
f_equal.
replace (sta + (i - sta)) with i by flia His.
replace (len - (i - sta)) with (1 + (sta + len - S i)) by flia His.
rewrite List.seq_app; cbn.
now rewrite Nat.add_1_r.
Qed.

Theorem List_seq_eq_nil : ∀ b len, List.seq b len = [] → len = 0.
Proof.
intros * Hb.
now induction len.
Qed.

Theorem List_seq_hd :
  ∀ len start d, 0 < len → List.hd d (List.seq start len) = start.
Proof.
intros.
rewrite List_hd_nth_0.
rewrite List.seq_nth; [ | easy ].
apply Nat.add_0_r.
Qed.

Theorem List_seq_shift' : ∀ i sta len,
  List.map (Nat.add i) (List.seq sta len) = List.seq (i + sta) len.
Proof.
intros.
revert i sta.
induction len; intros; [ easy | cbn ].
f_equal.
rewrite IHlen.
now rewrite <- Nat.add_succ_comm.
Qed.

Theorem List_skipn_is_cons : ∀ {A} (d : A) la n,
  n < length la
  → List.skipn n la = List.nth n la d :: List.skipn (S n) la.
Proof.
intros * Hn.
revert n Hn.
induction la as [| a]; intros; [ easy | ].
destruct n; [ easy | ].
cbn in Hn; apply Nat.succ_lt_mono in Hn.
rewrite List_nth_succ_cons.
do 2 rewrite List.skipn_cons.
now apply IHla.
Qed.

Theorem List_skipn_seq :
  ∀ n start len,
  n ≤ len
  → List.skipn n (List.seq start len) = List.seq (start + n) (len - n).
Proof.
intros * Hnlen.
revert n start Hnlen.
induction len; intros; [ now rewrite List.skipn_nil | cbn ].
destruct n; [ now cbn; rewrite Nat.add_0_r | cbn ].
rewrite <- Nat.add_succ_comm.
apply Nat.succ_le_mono in Hnlen.
now apply IHlen.
Qed.

Theorem iter_list_empty : ∀ T A d (op : T → T → T) (l : list A) g,
  l = []
  → iter_list l (λ c i, op c (g i)) d = d.
Proof.
now intros * Hl; subst l.
Qed.

Theorem List_flat_length_map : ∀ A B (f : A → list B) l,
  length (List.flat_map f l) = iter_list l (fun c a => c + length (f a)) 0.
Proof.
intros.
induction l as [| a]; [ now rewrite iter_list_empty | cbn ].
rewrite List.length_app.
rewrite iter_list_cons; cycle 1. {
  apply Nat.add_0_l.
} {
  apply Nat.add_0_r.
} {
  apply Nat.add_assoc.
}
now cbn; f_equal.
Qed.

Theorem Nat_1_le_sub_lt : ∀ i j, 1 ≤ i ≤ j → i - 1 < j.
Proof.
intros * Hij.
destruct i; [ easy | ].
rewrite Nat_sub_succ_1.
apply Hij.
Qed.

Theorem Nat_b2n_upper_bound : ∀ b, Nat.b2n b ≤ 1.
Proof.
intros; destruct b; cbn; flia.
Qed.

Theorem Nat_fact_succ : ∀ n, fact (S n) = S n * fact n.
Proof. easy. Qed.

Theorem Nat_leb_add_mono_l : ∀ a b c, (a + b <=? a + c) = (b <=? c).
Proof.
intros.
remember (b <=? c) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Nat.leb_le in Hx.
  now apply Nat.leb_le, Nat.add_le_mono_l.
}
apply Nat.leb_gt in Hx.
apply Nat.leb_gt.
now apply Nat.add_lt_mono_l.
Qed.

Theorem Nat_mod_add_l_mul_r : ∀ a b c,
  (c * b + a) mod b = a mod b.
Proof.
intros.
rewrite Nat.add_comm.
apply Nat.Div0.mod_add.
Qed.

Theorem Nat_sub_sub_distr : ∀ n m p, p ≤ m → n - (m - p) = n + p - m.
Proof.
intros n m p Hpm.
rewrite Nat.add_comm.
revert n m Hpm.
induction p; intros. {
  now rewrite Nat.sub_0_r, Nat.add_0_l.
}
destruct m as [| m]. {
  exfalso; revert Hpm; apply Nat.nle_succ_0.
}
rewrite Nat.sub_succ; cbn.
apply Nat.succ_le_mono in Hpm.
now apply IHp.
Qed.

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem Nat_succ_sub_succ_r : ∀ a b, b < a → a - b = S (a - S b).
Proof. intros * Hba; flia Hba. Qed.

Theorem NoDup_app_remove_r :
  ∀ A (l l' : list A), List.NoDup (l ++ l') → List.NoDup l.
Proof.
intros * Hnd.
apply NoDup_app_comm in Hnd.
now apply NoDup_app_remove_l in Hnd.
Qed.

Theorem NoDup_app_iff : ∀ A (l l' : list A),
  List.NoDup (l ++ l') ↔
    List.NoDup l ∧ List.NoDup l' ∧ (∀ a, a ∈ l → a ∉ l').
Proof.
intros.
split. {
  intros Hnd.
  split; [ now apply NoDup_app_remove_r in Hnd | ].
  split; [ now apply NoDup_app_remove_l in Hnd | ].
  intros a Ha Ha'.
  revert l' Hnd Ha'.
  induction l as [| b]; intros; [ easy | ].
  destruct Ha as [Ha| Ha]. {
    subst b.
    apply NoDup_app_comm in Hnd.
    apply List.NoDup_remove_2 in Hnd.
    apply Hnd.
    now apply List.in_app_iff; left.
  }
  apply (IHl Ha l'); [ | easy ].
  cbn in Hnd.
  now apply List.NoDup_cons_iff in Hnd.
} {
  intros * (Hnl & Hnl' & Hll).
  revert l' Hnl' Hll.
  induction l as [| b l]; intros; [ easy | cbn ].
  constructor. {
    intros Hb.
    apply List.in_app_or in Hb.
    destruct Hb as [Hb| Hb]. {
      now apply List.NoDup_cons_iff in Hnl.
    } {
      now specialize (Hll b (or_introl eq_refl)) as H1.
    }
  } {
    apply List.NoDup_cons_iff in Hnl.
    apply IHl; [ easy | easy | ].
    intros a Ha.
    now apply Hll; right.
  }
}
Qed.

Theorem NoDup_concat_if : ∀ A (ll : list (list A)),
  (∀ l, l ∈ ll → List.NoDup l)
  → (∀ i j, i ≠ j → ∀ a, a ∈ List.nth i ll [] → a ∉ List.nth j ll [])
  → List.NoDup (List.concat ll).
Proof.
intros * Hnd Hll.
induction ll as [| l]; [ constructor | cbn ].
apply NoDup_app_iff.
split; [ now apply Hnd; left | ].
split. {
  apply IHll. {
    intros l1 Hl1.
    now apply Hnd; right.
  }
  intros i j Hij a Ha.
  specialize (Hll (S i) (S j)).
  apply Hll; [ now intros H; injection H | easy ].
}
clear - Hnd Hll.
intros i Hi Hll'.
revert i l Hnd Hi Hll Hll'.
induction ll as [| l1]; intros; [ easy | ].
cbn in Hll'.
apply List.in_app_or in Hll'.
destruct Hll' as [Hll'| Hll']. 2: {
  apply IHll with (i := i) (l := l); [ | easy | | easy ]. {
    intros l2 Hl2.
    apply Hnd.
    destruct Hl2 as [Hl2| Hl2]; [ now left | now right; right ].
  }
  intros u v Huv a Ha.
  destruct u. {
    cbn in Ha.
    destruct v; [ easy | cbn ].
    specialize (Hll 0 (S (S v))) as H1.
    assert (H : 0 ≠ S (S v)) by easy.
    now specialize (H1 H a Ha).
  }
  cbn in Ha.
  destruct v. {
    specialize (Hll (S (S u)) 0) as H1.
    assert (H : S (S u) ≠ 0) by easy.
    now specialize (H1 H a Ha).
  }
  cbn.
  apply Nat.succ_inj_wd_neg in Huv.
  specialize (Hll _ _ Huv).
  now apply Hll.
}
now specialize (Hll 0 1 (Nat.neq_0_succ _) _ Hi).
Qed.

Theorem NoDup_filter {A} :
  ∀ (f : A → _) {l}, List.NoDup l → List.NoDup (List.filter f l).
Proof.
intros * Hnd.
induction l as [| a l]; [ easy | cbn ].
remember (f a) as b eqn:Hb; symmetry in Hb.
apply List.NoDup_cons_iff in Hnd.
destruct Hnd as (Hal, Hl).
destruct b. {
  constructor; [ | now apply IHl ].
  intros H; apply Hal.
  now apply List.filter_In in H.
}
now apply IHl.
Qed.

Theorem NoDup_map_iff {A B} : ∀ d l (f : A → B),
  List.NoDup (List.map f l)
  ↔ (∀ i j,
      i < length l
      → j < length l
      → f (List.nth i l d) = f (List.nth j l d) → i = j).
Proof.
intros.
split. {
  intros Hnd i j Hi Hj Hij.
  revert i j Hi Hj Hij.
  induction l as [| a l]; intros; [ easy | ].
  cbn in Hnd.
  apply List.NoDup_cons_iff in Hnd.
  destruct Hnd as (Hnin, Hnd).
  specialize (IHl Hnd).
  destruct i. {
    destruct j; [ easy | exfalso ].
    cbn in Hij, Hj; clear Hi.
    apply Nat.succ_lt_mono in Hj.
    rewrite Hij in Hnin; apply Hnin; clear Hnin.
    now apply List.in_map, List.nth_In.
  }
  cbn in Hi, Hj.
  destruct j; [ exfalso | ]. {
    cbn in Hij, Hj; clear Hj.
    apply Nat.succ_lt_mono in Hi.
    rewrite <- Hij in Hnin; apply Hnin; clear Hnin.
    now apply List.in_map, List.nth_In.
  }
  apply Nat.succ_lt_mono in Hi.
  apply Nat.succ_lt_mono in Hj.
  cbn in Hij.
  f_equal.
  now apply IHl.
} {
  intros Hinj.
  induction l as [| a l]; [ constructor | cbn ].
  apply List.NoDup_cons. {
    intros Hcon.
    apply List.in_map_iff in Hcon.
    destruct Hcon as (b & Hba & Hb).
    symmetry in Hba.
    apply (List.In_nth _ _ d) in Hb.
    destruct Hb as (n & Hlen & Hnth).
    specialize (Hinj 0 (S n)) as H1.
    cbn in H1; rewrite Hnth in H1.
    apply Nat.succ_lt_mono in Hlen.
    now specialize (H1 (Nat.lt_0_succ _) Hlen Hba).
  }
  apply IHl.
  intros i j Hi Hj Hij.
  apply Nat.succ_lt_mono in Hi.
  apply Nat.succ_lt_mono in Hj.
  specialize (Hinj (S i) (S j) Hi Hj Hij) as H1.
  now apply Nat.succ_inj in H1.
}
Qed.

Theorem Tauto_match_nat_same : ∀ A a (b : A),
  match a with 0 => b | S _ => b end = b.
Proof. now intros; destruct a. Qed.

Theorem binomial_lt : ∀ n k, n < k → binomial n k = 0.
Proof.
intros * Hnk.
revert k Hnk.
induction n; intros; [ now destruct k | cbn ].
destruct k; [ flia Hnk | ].
apply Nat.succ_lt_mono in Hnk.
rewrite IHn; [ | easy ].
rewrite Nat.add_0_l.
apply IHn; flia Hnk.
Qed.

Theorem binomial_succ_diag_r : ∀ n, binomial n (S n) = 0.
Proof.
intros.
apply binomial_lt; flia.
Qed.

Theorem binomial_succ_succ : ∀ n k,
  binomial (S n) (S k) = binomial n k + binomial n (S k).
Proof. easy. Qed.

Theorem cart_prod_length : ∀ A (ll : list (list A)),
  ll ≠ []
  → length (cart_prod ll) = iter_list ll (fun c l => c * length l) 1.
Proof.
intros * Hll.
revert Hll.
induction ll as [| l1]; intros; [ easy | clear Hll; cbn ].
rewrite iter_list_cons; cycle 1. {
  apply Nat.mul_1_l.
} {
  apply Nat.mul_1_r.
} {
  apply Nat.mul_assoc.
}
rewrite List_flat_length_map.
erewrite iter_list_eq_compat. 2: {
  intros i Hi.
  now rewrite List.length_map.
}
cbn.
destruct ll as [| l2]. {
  rewrite iter_list_empty with (l := []); [ | easy ].
  rewrite Nat.mul_1_r; cbn.
  induction l1 as [| a]; [ easy | ].
  rewrite iter_list_cons; cycle 1.
    apply Nat.add_0_l.
    apply Nat.add_0_r.
    apply Nat.add_assoc.
  now cbn; rewrite IHl1.
}
rewrite IHll; [ | easy ].
induction l1 as [| a]; [ easy | ].
rewrite iter_list_cons; cycle 1.
  apply Nat.add_0_l.
  apply Nat.add_0_r.
  apply Nat.add_assoc.
now cbn; rewrite IHl1.
Qed.

Theorem equality_in_dec :
  ∀ {A} {eqb : A → _} (Heqb : equality eqb) (a : A) la,
  { a ∈ la } + { a ∉ la }.
Proof.
intros.
induction la as [| b]; [ now right | ].
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ now apply Heqb in Hab; subst b; left; left | ].
destruct IHla as [H1| H1]; [ now left; right | right ].
intros H2; apply H1; clear H1.
destruct H2 as [H2| H2]; [ | easy ].
subst b.
now rewrite (equality_refl Heqb) in Hab.
Qed.

Theorem equality_list_eqv : ∀ A (eqb : A → _),
  equality eqb ↔ equality (list_eqv eqb).
Proof.
intros.
split. {
  intros Heqb la lb.
  now apply list_eqb_eq.
} {
  intros Heqb a b.
  progress unfold equality in Heqb.
  split. {
    intros Hab.
    specialize (Heqb [a] [b]).
    cbn in Heqb.
    rewrite Hab in Heqb.
    specialize (proj1 Heqb eq_refl) as H1.
    now injection H1.
  } {
    intros Hab; subst b.
    specialize (Heqb [a] [a]).
    cbn in Heqb.
    specialize (proj2 Heqb eq_refl) as H1.
    now destruct (eqb a a).
  }
}
Qed.

Theorem extract_None_iff : ∀ {A} (f : A → _) l,
  extract f l = None ↔ ∀ a, a ∈ l → f a = false.
Proof.
intros.
split. {
  intros He * Ha.
  revert a Ha.
  induction l as [| b]; intros; [ easy | ].
  cbn in He.
  remember (f b) as fb eqn:Hfb; symmetry in Hfb.
  destruct fb; [ easy | ].
  destruct Ha as [Ha| Ha]; [ now subst b | ].
  apply IHl; [ | easy ].
  now destruct (extract f l) as [((bef, x), aft)| ].
} {
  intros Hf.
  induction l as [| a]; [ easy | cbn ].
  rewrite Hf; [ | now left ].
  rewrite IHl; [ easy | ].
  intros c Hc.
  now apply Hf; right.
}
Qed.

Theorem eq_list_eq : ∀ {A} d (la lb : list A),
  length la = length lb
  → (∀ i, i < length la → List.nth i la d = List.nth i lb d)
  → la = lb.
Proof.
intros * Hlab Hab.
revert lb Hlab Hab.
induction la as [| a]; intros. {
  now symmetry in Hlab; apply List.length_zero_iff_nil in Hlab.
}
destruct lb as [| b]; [ easy | ].
cbn in Hlab; apply Nat.succ_inj in Hlab.
f_equal; [ now specialize (Hab 0 (Nat.lt_0_succ _)) | ].
apply (IHla _ Hlab).
intros i Hi.
apply (Hab (S i)); cbn.
now apply Nat.succ_lt_mono in Hi.
Qed.

Theorem extract_Some_iff : ∀ A (f : A → _) l a bef aft,
  extract f l = Some (bef, a, aft)
  ↔ (∀ x, x ∈ bef → f x = false) ∧ f a = true ∧ l = bef ++ a :: aft.
Proof.
intros.
split. {
  intros He.
  revert a bef aft He.
  induction l as [| b]; intros; [ easy | cbn ].
  cbn in He.
  remember (f b) as fb eqn:Hfb; symmetry in Hfb.
  destruct fb. {
    now injection He; clear He; intros; subst bef b aft.
  }
  remember (extract f l) as lal eqn:Hlal; symmetry in Hlal.
  destruct lal as [((bef', x), aft') | ]; [ | easy ].
  injection He; clear He; intros; subst bef x aft'.
  rename bef' into bef.
  specialize (IHl _ _ _ eq_refl) as H1.
  destruct H1 as (H1 & H2 & H3).
  split. {
    intros c Hc.
    destruct Hc as [Hc| Hc]; [ now subst c | ].
    now apply H1.
  }
  split; [ easy | ].
  now cbn; f_equal.
} {
  intros He.
  destruct He as (Hbef & Hf & Hl).
  subst l.
  revert a aft Hf.
  induction bef as [| b]; intros; cbn; [ now rewrite Hf | ].
  rewrite Hbef; [ | now left ].
  rewrite IHbef; [ easy | | easy ].
  now intros c Hc; apply Hbef; right.
}
Qed.

Theorem fold_iter_seq : ∀ A b e f (d : A),
  iter_list (List.seq b (S e - b)) f d = iter_seq b e f d.
Proof. easy. Qed.

Theorem fold_iter_seq' : ∀ A b len f (d : A),
  iter_list (List.seq b len) f d =
    if b + len =? 0 then d
    else iter_seq b (b + len - 1) f d.
Proof.
intros.
progress unfold iter_seq.
f_equal; f_equal.
remember (b + len =? 0) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Nat.eqb_eq in Hx.
  now apply Nat.eq_add_0 in Hx; destruct Hx; subst b len.
}
apply Nat.eqb_neq in Hx.
destruct len. {
  rewrite Nat.add_0_r in Hx.
  destruct b; [ easy | cbn ].
  now rewrite Nat.add_sub, Nat.sub_diag.
}
rewrite Nat.sub_succ_l; [ cbn | flia ].
f_equal; f_equal; f_equal.
flia.
Qed.

Theorem fold_not : ∀ (P : Prop), not P → P → False.
Proof. easy. Qed.

Theorem if_eqb_eq_dec : ∀ {A} i j (a b : A),
  (if i =? j then a else b) = (if Nat.eq_dec i j then a else b).
Proof.
intros.
destruct (Nat.eq_dec i j) as [H1| H1]. {
  now apply Nat.eqb_eq in H1; rewrite H1.
}
now apply Nat.eqb_neq in H1; rewrite H1.
Qed.

Theorem App_list_concat_map : ∀ A B (l : list A) (f : A → list B),
  App (a ∈ l), f a = List.concat (List.map f l).
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
rewrite App_list_cons.
now rewrite IHl.
Qed.

Theorem in_App_list : ∀ A B (f : A → list B) l y,
  y ∈ App (i ∈ l), f i ↔ (∃ x : A, x ∈ l ∧ y ∈ f x).
Proof.
intros.
rewrite App_list_concat_map.
rewrite <- List.flat_map_concat_map.
apply List.in_flat_map.
Qed.

Theorem in_cart_prod_length : ∀ A (ll : list (list A)) l,
  l ∈ cart_prod ll → length l = length ll.
Proof.
intros * Hl.
revert l Hl.
induction ll as [| l1]; intros. {
  cbn in Hl.
  destruct Hl as [Hl| Hl]; [ now subst l | easy ].
}
cbn in Hl.
apply List.in_flat_map in Hl.
destruct Hl as (a & Hl1 & Ha).
apply List.in_map_iff in Ha.
destruct Ha as (l3 & Hl & Hl3).
subst l; cbn; f_equal.
now apply IHll.
Qed.

Theorem in_cart_prod_iff : ∀ {A} (d : A) ll la,
  la ∈ cart_prod ll
  ↔ length la = length ll ∧
    ∀ i, i < length la → List.nth i la d ∈ List.nth i ll [].
Proof.
intros.
split. {
  intros Hla.
  split; [ now apply in_cart_prod_length in Hla | ].
  intros i Hi.
  apply nth_in_cart_prod; [ | easy ].
  apply in_cart_prod_length in Hla.
  congruence.
} {
  intros (Hla & Hnth).
  revert la Hla Hnth.
  induction ll as [| lb]; intros. {
    now apply List.length_zero_iff_nil in Hla; subst la; left.
  }
  cbn.
  destruct la as [| a]; [ easy | ].
  cbn in Hla; apply Nat.succ_inj in Hla.
  apply List.in_flat_map.
  exists a.
  specialize (Hnth 0 (Nat.lt_0_succ _)) as H1; cbn in H1.
  split; [ easy | ].
  apply List.in_map_iff.
  exists la.
  split; [ easy | ].
  apply IHll; [ easy | ].
  intros i Hi.
  specialize (Hnth (S i)) as H2.
  cbn in H2.
  apply Nat.succ_lt_mono in Hi.
  now specialize (H2 Hi).
}
Qed.

Theorem iter_list_op_fun_from_d : ∀ T A d op a l (f : A → _)
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_list l (λ (c : T) (i : A), op c (f i)) a =
  op a (iter_list l (λ (c : T) (i : A), op c (f i)) d).
Proof.
intros.
progress unfold iter_list.
revert a.
induction l as [| x l]; intros; [ symmetry; apply op_d_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite op_d_l.
apply op_assoc.
Qed.

Theorem iter_list_seq : ∀ T d (op : T → T → T) b len f,
  len ≠ 0
  → iter_list (List.seq b len) (λ c i, op c (f i)) d =
    iter_seq b (b + len - 1) (λ c i, op c (f i)) d.
Proof.
intros * Hlen.
progress unfold iter_seq.
f_equal; f_equal.
flia Hlen.
Qed.

Theorem iter_list_split_first : ∀ T A d op l z f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  l ≠ []
  → iter_list l (λ (c : T) (i : A), op c (f i)) d =
    op (f (List.hd z l))
      (iter_list (List.tl l) (λ (c : T) (i : A), op c (f i)) d).
Proof.
intros * op_d_l op_d_r op_assoc Hl.
progress unfold iter_list.
destruct l as [| a]; [ easy | cbn ].
rewrite op_d_l.
now rewrite fold_left_op_fun_from_d with (d := d).
Qed.

Theorem iter_list_split_last : ∀ T A d (op : T → T → T) l (g : A → T) z,
  l ≠ []
  → iter_list l (λ c i, op c (g i)) d =
    op (iter_list (List.removelast l) (λ c i, op c (g i)) d)
      (g (List.last l z)).
Proof.
intros * Hlz.
progress unfold iter_list.
induction l as [| a] using List.rev_ind; [ easy | clear IHl Hlz ].
rewrite List.removelast_last.
rewrite List.last_last.
now rewrite List.fold_left_app.
Qed.

Theorem iter_list_app : ∀ A B (d : A) (f : A → B → A) la lb,
  iter_list (la ++ lb) f d = iter_list lb f (iter_list la f d).
Proof.
intros.
progress unfold iter_list.
now rewrite List.fold_left_app.
Qed.

Theorem iter_seq_all_d : ∀ T d op b e f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  (∀ i : nat, b ≤ i ≤ e → f i = d)
  → iter_seq b e (λ (c : T) (i : nat), op c (f i)) d = d.
Proof.
intros * op_d_l od_d_r op_assoc Hz.
apply iter_list_all_d; [ easy | easy | easy | ].
intros i Hi.
apply List.in_seq in Hi.
apply Hz; flia Hi.
Qed.

Theorem iter_seq_distr : ∀ T d op g h b k
  (op_d_l : ∀ x, op d x = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_seq b k (λ (c : T) (i : nat), (op c (op (g i) (h i)))) d =
  op
    (iter_seq b k (λ (c : T) (i : nat), op c (g i)) d)
    (iter_seq b k (λ (c : T) (i : nat), op c (h i)) d).
Proof.
intros.
now apply iter_list_distr.
Qed.

Theorem iter_seq_empty : ∀ T d (op : T → T → T) b k g,
  k < b
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d = d.
Proof.
intros * Hkb.
progress unfold iter_seq.
now replace (S k - b) with 0 by flia Hkb.
Qed.

Theorem iter_seq_eq_compat : ∀ T d (op : T → T → T) b k g h,
  (∀ i, b ≤ i ≤ k → g i = h i)
  → iter_seq b k (λ c i, op c (g i)) d =
    iter_seq b k (λ c i, op c (h i)) d.
Proof.
intros * Hgh.
apply iter_list_eq_compat.
intros i Hi.
apply Hgh.
apply List.in_seq in Hi.
flia Hi.
Qed.

Theorem iter_seq_inv : ∀ T d op inv b e f
  (inv_op_distr : ∀ a b, inv (op a b) = op (inv a) (inv b)),
  inv (iter_seq b e (λ (c : T) (i : nat), op c (f i)) d) =
  iter_seq b e (λ (c : T) (i : nat), op c (inv (f i))) (inv d).
Proof.
intros.
now apply iter_list_inv.
Qed.

Theorem iter_seq_only_one : ∀ T d (op : T → T → T) g n
  (op_d_l : ∀ x, op d x = x),
  iter_seq n n (λ c i, op c (g i)) d = g n.
Proof.
intros * op_d_l.
progress unfold iter_seq.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.sub_diag.
now apply iter_list_only_one.
Qed.

Theorem iter_seq_rtl : ∀ T d op b k f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_seq b k (λ (c : T) (i : nat), op c (f i)) d =
  iter_seq b k (λ (c : T) (i : nat), op c (f (k + b - i))) d.
Proof.
intros.
destruct (le_dec (S k) b) as [Hkb| Hkb]. {
  progress unfold iter_seq.
  now replace (S k - b) with 0 by flia Hkb.
}
apply Nat.nle_gt in Hkb.
apply -> Nat.lt_succ_r in Hkb.
progress unfold iter_seq, iter_list.
remember (S k - b) as len eqn:Hlen.
replace k with (b + len - 1) by flia Hkb Hlen.
clear Hlen Hkb.
revert b.
induction len; intros; [ easy | ].
rewrite List.seq_S at 1; cbn.
rewrite List.fold_left_app; cbn.
symmetry.
rewrite fold_left_op_fun_from_d with (d := d); [ | easy | easy | easy ].
rewrite op_comm.
f_equal; [ | rewrite op_d_l; f_equal; flia ].
rewrite IHlen.
rewrite <- List.seq_shift.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros j c Hj.
apply List.in_seq in Hj.
f_equal; f_equal; flia.
Qed.

Theorem iter_seq_split3 : ∀ T d op j g b k
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  b ≤ j ≤ k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (op (iter_seq (S b) j (λ (c : T) (i : nat), op c (g (i - 1))) d) (g j))
      (iter_seq (j + 1) k (λ (c : T) (i : nat), op c (g i)) d).
Proof.
intros * op_d_l op_d_r op_assoc Hj.
rewrite iter_seq_split with (j := j); [ | easy | easy | easy | flia Hj ].
now rewrite iter_seq_split_last.
Qed.

Theorem iter_seq_split_first : ∀ T d op b k g
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  b ≤ k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (g b) (iter_seq (S b) k (λ (c : T) (i : nat), op c (g i)) d).
Proof.
intros * op_d_l op_d_r op_assoc Hbk.
progress unfold iter_seq, iter_list.
remember (S k - b) as len eqn:Hlen.
replace (S k - S b) with (len - 1) by flia Hlen.
assert (H : len ≠ 0) by flia Hlen Hbk.
clear k Hbk Hlen.
rename H into Hlen.
destruct len; [ easy | cbn ].
rewrite op_d_l, Nat.sub_0_r.
apply fold_left_op_fun_from_d. {
  apply op_d_l.
} {
  apply op_d_r.
} {
  apply op_assoc.
}
Qed.

Theorem iter_seq_succ_succ' : ∀ {T} (d : T) b k f,
  iter_seq (S b) (S k) (λ c i, f c (i - 1)) d =
  iter_seq b k (λ c i, f c i) d.
Proof.
intros.
progress unfold iter_seq, iter_list.
rewrite Nat.sub_succ.
rewrite <- List.seq_shift.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros j i Hj.
f_equal.
rewrite Nat.sub_succ.
apply Nat.sub_0_r.
Qed.

Arguments "<?" : simpl never.
