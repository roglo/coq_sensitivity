(* Theorems of general usage, which could be (or not) in Coq library *)

From Stdlib Require Import Utf8 Arith Psatz.

Import List.ListNotations Init.Nat.
Open Scope list.

Require Export RingLike.Misc RingLike.Utils.

Notation "n !" := (fact n) (at level 1, format "n !").

Notation "l .( i )" := (List.nth (i - 1) l 0) (at level 1, format "l .( i )").

Notation "∃! x .. y , p" :=
  (ex (unique (λ x, .. (ex (unique (λ y, p))) ..)))
    (at level 200, x binder, right associativity)
  : type_scope.

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

Definition AllLt l u := ∀ i, i ∈ l → i < u.

(*
(* maximum of several values *)

(* commented because Max could apply only on nat because it needs
   a minimum, which is 0 in nat, but not in all ring-like types *)

Notation "'Max' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, max c (g)) 0)
  (at level 45, i at level 0, b at level 60, e at level 60) : nat_scope.

Notation "'Max' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, max c (g)) 0)
  (at level 45, i at level 0, l at level 60) : nat_scope.
*)

Theorem fold_iter_seq : ∀ A b e f (d : A),
  iter_list (List.seq b (S e - b)) f d = iter_seq b e f d.
Proof. easy. Qed.

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

Theorem List_fold_right_max_ge : ∀ m l, m ≤ List.fold_right max m l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
etransitivity; [ apply IHl | ].
apply Nat.le_max_r.
Qed.

(* *)

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

Theorem Nat_1_le_sub_lt : ∀ i j, 1 ≤ i ≤ j → i - 1 < j.
Proof.
intros * Hij.
destruct i; [ easy | ].
rewrite Nat_sub_succ_1.
apply Hij.
Qed.

Theorem Nat_lt_lt_add_mul : ∀ a b c n, a < b → c < n → c + n * a < n * b.
Proof.
intros * Hab Hcn.
revert a b c Hab Hcn.
induction n; intros; [ easy | cbn ].
destruct c. {
  cbn.
  apply Nat.add_lt_le_mono; [ easy | ].
  now apply Nat.mul_le_mono_l, Nat.lt_le_incl.
}
apply Nat.succ_lt_mono in Hcn.
specialize (IHn a b c Hab Hcn).
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm.
apply Nat.add_lt_le_mono; [ easy | ].
apply IHn.
Qed.

Theorem List_hd_nth_0 {A} : ∀ l (d : A), List.hd d l = List.nth 0 l d.
Proof. intros; now destruct l. Qed.

Theorem List_hd_in : ∀ A (l : list A) d, 0 < length l → List.hd d l ∈ l.
Proof.
intros.
rewrite List_hd_nth_0.
now apply List.nth_In.
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

Theorem List_map_hd : ∀ {A B} a b (f : A → B) l,
  0 < length l → List.hd b (List.map f l) = f (List.hd a l).
Proof.
intros.
do 2 rewrite List_hd_nth_0.
now apply List_map_nth'.
Qed.

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

Theorem Nat_b2n_upper_bound : ∀ b, Nat.b2n b ≤ 1.
Proof.
intros; destruct b; cbn; flia.
Qed.

Theorem Nat_mod_fact_upper_bound : ∀ k n, k mod n! < n!.
Proof.
intros.
apply Nat.mod_upper_bound, fact_neq_0.
Qed.

(* butn: list without its nth element *)

Definition List_butn {A} n (l : list A) :=
  List.firstn n l ++ List.skipn (S n) l.

Theorem List_fold_butn : ∀ A n (l : list A),
  List.firstn n l ++ List.skipn (S n) l = List_butn n l.
Proof. easy. Qed.

Theorem List_butn_nil : ∀ A n, List_butn n ([] : list A) = [].
Proof. now intros; destruct n. Qed.

Theorem List_butn_0_cons : ∀ A (a : A) la, List_butn 0 (a :: la) = la.
Proof. easy. Qed.

Theorem List_butn_succ_cons :
  ∀ A (a : A) la n, List_butn (S n) (a :: la) = a :: List_butn n la.
Proof.
intros.
progress unfold List_butn.
now rewrite List.firstn_cons, List.skipn_cons.
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

(* end butn *)

(* insert in a list (List.reverse of List_butn) *)

Definition insert_at A k (la : list A) e :=
  List.firstn k la ++ e :: List.skipn k la.

(* end insert_at *)

(* replace in a list *)

Definition replace_at {A} k (la : list A) e :=
  List.firstn k la ++ e :: List.skipn (S k) la.

Theorem replace_at_succ_cons : ∀ A i a b (l : list A),
  replace_at (S i) (a :: l) b = a :: replace_at i l b.
Proof. easy. Qed.

(* end replace_at *)

(* List_repeat_apply: applying a function n times *)

Fixpoint List_repeat_apply {A} n (f : A → A) a :=
  match n with
  | 0 => a
  | S n' => List_repeat_apply n' f (f a)
  end.

Theorem List_fold_left_nop_r : ∀ A B (a : A) (lb : list B) (f : A → _),
  List.fold_left (λ c _, f c) lb a = List_repeat_apply (length lb) f a.
Proof.
intros.
revert a.
induction lb as [| b]; intros; [ easy | cbn ].
apply IHlb.
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

(* end List.repeat_apply *)

(* equivalence & equality *)

Definition equivalence {A} (eqv : A → A → bool) :=
  (∀ a, eqv a a = true) ∧
  (∀ a b, eqv a b = true → eqv b a = true) ∧
  (∀ a b c, eqv a b = true → eqv b c = true → eqv a c = true).

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

(* *)

Theorem option_eq_dec : ∀ A : Type,
  (∀ x y : A, {x = y} + {x ≠ y})
  → (∀ x y : option A, {x = y} + {x ≠ y}).
Proof.
intros * Hed *.
destruct x as [x| ]. {
  destruct y as [y| ]; [ | now right ].
  destruct (Hed x y) as [H1| H1]; [ now left; subst y | right ].
  intros H; apply H1.
  now injection H.
}
destruct y as [y| ]; [ now right | now left ].
Qed.

(* *)

Fixpoint list_compare {A} (compare : A → A → comparison) la lb :=
  match la with
  | [] =>
      match lb with
      | [] => Eq
      | b :: lb' => Lt
      end
  | a :: la' =>
      match lb with
      | [] => Gt
      | b :: lb' =>
          match compare a b with
          | Eq => list_compare compare la' lb'
          | Lt => Lt
          | Gt => Gt
          end
      end
  end.

(* list_eqv *)

Fixpoint list_eqv {A} (eqv : A → A → bool) la lb :=
  match la with
  | [] =>
      match lb with
      | [] => true
      | b :: lb' => false
      end
  | a :: la' =>
      match lb with
      | [] => false
      | b :: lb' => if eqv a b then list_eqv eqv la' lb' else false
      end
  end.

Theorem list_eqb_eq : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb, list_eqv eqb la lb = true ↔ la = lb.
Proof.
intros * Heqb *.
split; intros Hlab. {
  revert lb Hlab.
  induction la as [| a]; intros; [ now destruct lb | cbn ].
  destruct lb as [| b]; [ easy | cbn in Hlab ].
  remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  apply Heqb in Hab; subst b; f_equal.
  now apply IHla.
} {
  subst lb.
  induction la as [| a]; [ easy | cbn ].
  now rewrite (equality_refl Heqb).
}
Qed.

Theorem list_eqb_neq : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb, list_eqv eqb la lb = false → la ≠ lb.
Proof.
intros * Heqb * Hab H; subst lb.
induction la as [| a]; [ easy | cbn in Hab ].
rewrite (equality_refl Heqb) in Hab.
congruence.
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

(* end list_eqv *)

(* list_leb *)

Fixpoint list_leb {A} (leb : A → A → bool) la lb :=
  match la with
  | [] => true
  | a :: la' =>
      match lb with
      | [] => false
      | b :: lb' =>
          if leb a b then
            if leb b a then list_leb leb la' lb' else true
          else false
      end
  end.

(* end list_leb *)

(* list_ltb *)

Fixpoint list_ltb {A} (ltb : A → A → bool) la lb :=
  match lb with
  | [] => false
  | b :: lb' =>
      match la with
      | [] => true
      | a :: la' =>
          if ltb a b then true
          else if ltb b a then false
          else list_ltb ltb la' lb'
      end
  end.

(* end list_ltb *)

(* pair_eqb *)

Definition pair_eqb {A B} (eqba : A → A → bool) (eqbb : B → B → bool) ab cd :=
  (eqba (fst ab) (fst cd) && eqbb (snd ab) (snd cd))%bool.

Theorem pair_eqb_eq : ∀ A B (eqba : A → _) (eqbb : B → _),
  equality eqba →
  equality eqbb →
  ∀ a b, pair_eqb eqba eqbb a b = true ↔ a = b.
Proof.
intros * Heqba Heqbb *.
split; intros Hab. {
  progress unfold pair_eqb in Hab.
  destruct a as (a1, a2).
  destruct b as (b1, b2).
  cbn in Hab.
  apply Bool.andb_true_iff in Hab.
  destruct Hab as (Ha, Hb).
  apply Heqba in Ha.
  apply Heqbb in Hb.
  congruence.
} {
  subst b.
  progress unfold pair_eqb.
  destruct a as (a1, a2); cbn.
  apply Bool.andb_true_iff.
  split. {
    apply (equality_refl Heqba).
  } {
    apply (equality_refl Heqbb).
  }
}
Qed.

(* end pair_eqb *)

(* member: a computable "In" *)

Fixpoint member {A} (eqb : A → A → bool) a la :=
  match la with
  | [] => false
  | b :: lb => if eqb a b then true else member eqb a lb
  end.

Theorem member_true_iff : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ a la, member eqb a la = true ↔ ∃ l1 l2, la = l1 ++ a :: l2.
Proof.
intros * Heqb *.
split. {
  intros Hma.
  induction la as [| b]; [ easy | cbn in Hma ].
  remember (member eqb a la) as mal eqn:Hmal; symmetry in Hmal.
  destruct mal. {
    specialize (IHla eq_refl).
    destruct IHla as (l1 & l2 & Hla).
    subst la.
    now exists (b :: l1), l2.
  }
  remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  apply Heqb in Hab; subst b.
  now exists [], la.
} {
  intros (l1 & l2 & Hla).
  subst la.
  induction l1 as [| b]; cbn. {
    now rewrite (equality_refl Heqb).
  }
  now destruct (eqb a b).
}
Qed.

Theorem member_false_iff : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ a la, member eqb a la = false ↔ ∀ b, b ∈ la → a ≠ b.
Proof.
intros * Heqb *.
split. {
  intros Hma * Hb Hab; subst b.
  induction la as [| b]; [ easy | ].
  cbn in Hma.
  destruct Hb as [Hb| Hb]. {
    subst b.
    now rewrite (equality_refl Heqb) in Hma.
  }
  apply IHla; [ | easy ].
  now destruct (eqb a b).
} {
  intros Hla.
  induction la as [| b]; [ easy | cbn ].
  remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab. {
    apply Heqb in Hab; subst b.
    now specialize (Hla _ (or_introl eq_refl)).
  }
  apply IHla.
  intros c Hc.
  now apply Hla; right.
}
Qed.

(* end member *)

(* no_dup: a computable "NoDup" *)

Fixpoint no_dup {A} (eqb : A → A → bool) la :=
  match la with
  | [] => true
  | a :: la' => if member eqb a la' then false else no_dup eqb la'
  end.

Theorem no_dup_NoDup : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la, no_dup eqb la = true ↔ List.NoDup la.
Proof.
intros * Heqb *.
split; intros Hla. {
  induction la as [| a]; [ constructor | ].
  apply List.NoDup_cons_iff.
  cbn in Hla.
  rewrite if_bool_if_dec in Hla.
  destruct (Sumbool.sumbool_of_bool _) as [Hal| Hal]; [ easy | ].
  split; [ | now apply IHla ].
  intros H.
  now specialize (proj1 (member_false_iff Heqb _ _) Hal a H).
} {
  induction la as [| a]; [ easy | cbn ].
  rewrite if_bool_if_dec.
  apply List.NoDup_cons_iff in Hla.
  destruct (Sumbool.sumbool_of_bool _) as [Hal| Hal]; [ | now apply IHla ].
  apply (member_true_iff Heqb) in Hal.
  destruct Hla as (Hala & Hnd).
  destruct Hal as (l1 & l2 & H); subst la.
  exfalso; apply Hala.
  now apply List.in_or_app; right; left.
}
Qed.

Theorem no_dup_false_iff : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la, no_dup eqb la = false ↔
  ∃ l1 l2 l3 a, la = l1 ++ a :: l2 ++ a :: l3.
Proof.
intros * Heqb *.
split. {
  intros Had.
  induction la as [| a]; [ easy | cbn in Had ].
  remember (member eqb a la) as mal eqn:Hmal; symmetry in Hmal.
  destruct mal. 2: {
    specialize (IHla Had).
    destruct IHla as (l1 & l2 & l3 & b & Hlb).
    exists (a :: l1), l2, l3, b.
    now subst la.
  }
  clear Had.
  apply member_true_iff in Hmal; [ | easy ].
  destruct Hmal as (l1 & l2 & Hla); subst la.
  now exists [], l1, l2, a.
} {
  intros (l1 & l2 & l3 & a & Hla); subst la.
  induction l1 as [| b]; cbn. {
    remember (member eqb a (l2 ++ a :: l3)) as mal eqn:Hmal; symmetry in Hmal.
    destruct mal; [ easy | ].
    specialize (proj1 (member_false_iff Heqb _ _) Hmal a) as H1.
    assert (H : a ∈ l2 ++ a :: l3) by now apply List.in_or_app; right; left.
    now specialize (H1 H).
  }
  remember (member eqb b _) as mbl eqn:Hmbl; symmetry in Hmbl.
  now destruct mbl.
}
Qed.

(* end no_dup *)

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

Theorem List_map_nth_seq' : ∀ A d (la : list A) n,
  n = length la
  → la = List.map (λ i, List.nth i la d) (List.seq 0 n).
Proof.
intros * Hn.
subst n.
apply List_map_nth_seq.
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

(* common for all iterators *)

Theorem fold_left_op_fun_from_d' : ∀ {T A} d op a l (f : A → _)
  (op_d_l : ∀ x, x ∈ List.map f l → op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  List.fold_left (λ (c : T) i, op c (f i)) l a =
  op a (List.fold_left (λ (c : T) i, op c (f i)) l d).
Proof.
intros.
revert a.
induction l as [| x l]; intros. {
  cbn; symmetry; apply op_d_r.
}
cbn.
rewrite IHl. 2: {
  intros y Hy.
  apply op_d_l.
  now right.
}
symmetry.
rewrite IHl. 2: {
  intros y Hy.
  apply op_d_l.
  now right.
}
rewrite op_d_l; [ | now left ].
apply op_assoc.
Qed.

Theorem iter_list_only_one' : ∀ T A d (op : T → T → T) (g : A → T) a
  (op_d_l : ∀ x, op d (g x) = g x),
  iter_list [a] (λ c i, op c (g i)) d = g a.
Proof.
intros * op_d_l.
progress unfold iter_list; cbn.
apply op_d_l.
Qed.

Theorem iter_seq_only_one' : ∀ T d (op : T → T → T) g n
  (op_d_l : ∀ x, op d (g x) = g x),
  iter_seq n n (λ c i, op c (g i)) d = g n.
Proof.
intros * op_d_l.
progress unfold iter_seq.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.sub_diag.
now apply iter_list_only_one'.
Qed.

(* *)

(*
Theorem fold_left_max_from_0 : ∀ A a l (f : A → _),
  fold_left (λ c i, max c (f i)) l a =
  max a (List.fold_left (λ c i, max c (f i)) l 0).
Proof.
intros.
apply fold_left_op_fun_from_d. {
  now intros; apply max_r.
} {
  now intros; rewrite Nat.max_l.
} {
  apply Nat.max_assoc.
}
Qed.

Theorem max_list_app : ∀ A (la lb : list A) f,
  Max (i ∈ la ++ lb), f i = max (Max (i ∈ la), f i) (Max (i ∈ lb), f i).
Proof.
intros.
rewrite iter_list_app.
progress unfold iter_list.
apply fold_left_max_from_0.
Qed.

Theorem max_list_cons : ∀ A (a : A) la f,
  Max (i ∈ a :: la), f i = max (f a) (Max (i ∈ la), f i).
Proof.
intros.
apply iter_list_cons. {
  now intros; apply max_r.
} {
  now intros; rewrite Nat.max_l.
} {
  apply Nat.max_assoc.
}
Qed.
*)

(* App : a notation for iterating concatenation of a list of lists *)

Notation "'App' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, c ++ g) [])
  (at level 45, i at level 0, b at level 60, e at level 60).

Notation "'App' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, c ++ g) [])
  (at level 45, i at level 0, l at level 60).

Theorem App_list_cons : ∀ A B (a : A) la (f : A → list B),
  App (i ∈ a :: la), f i = f a ++ App (i ∈ la), f i.
Proof.
intros.
apply iter_list_cons; [ easy | apply List.app_nil_r | ].
apply List.app_assoc.
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

(* "to_radix_loop u r i" is the last u digits of i in base r
   (in List.reverse) *)
Fixpoint to_radix_loop it r i :=
  match it with
  | 0 => []
  | S it' => i mod r :: to_radix_loop it' r (i / r)
  end.

(* conversion natural into radix r as a list of digits; i must be
   less than r^r; always return r digits; e.g. radix 10 37 =
   7; 3; 0 ... (eight 0s) *)
Definition to_radix r i := to_radix_loop r r i.

Definition to_radix_list r := List.map (to_radix r) (List.seq 0 (r ^ r)).

Fixpoint to_radix_inv r l :=
  match l with
  | [] => 0
  | d :: l' => d + r * to_radix_inv r l'
  end.

Theorem to_radix_loop_ub : ∀ it n k i,
  n ≠ 0 → List.nth i (to_radix_loop it n k) 0 < n.
Proof.
intros * Hnz.
revert n k i Hnz.
induction it; intros; [ destruct i; cbn; flia Hnz | cbn ].
destruct i; [ now apply Nat.mod_upper_bound | ].
now apply IHit.
Qed.

Theorem to_radix_ub : ∀ n k i, n ≠ 0 → List.nth i (to_radix n k) 0 < n.
Proof.
intros * Hnz.
now apply to_radix_loop_ub.
Qed.

Theorem to_radix_inv_to_radix_loop : ∀ it n k,
  to_radix_inv n (to_radix_loop it n k) = k mod (n ^ it).
Proof.
intros.
revert k.
induction it; intros; [ easy | cbn ].
rewrite IHit.
symmetry.
apply Nat.Div0.mod_mul_r.
Qed.

Theorem to_radix_loop_to_radix_inv : ∀ l d n it,
  length l + d = n
  → (∀ i, i ∈ l → i < n)
  → n ≤ it + d
  → to_radix_loop it n (to_radix_inv n l) = l ++ List.repeat 0 (it + d - n).
Proof.
intros * Hlen Hl Hit.
revert d n it Hlen Hl Hit.
induction l as [| a]; intros. {
  cbn - [ "-" ].
  cbn in Hlen; subst d.
  clear Hl Hit.
  rewrite Nat.add_sub.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    subst n; cbn.
    induction it; cbn; [ easy | now cbn; f_equal ].
  }
  induction it; [ easy | cbn ].
  rewrite Nat.mod_small; [ | flia Hnz ].
  rewrite Nat.div_small; [ | flia Hnz ].
  now f_equal.
}
cbn - [ "-" ].
destruct it; [ cbn in Hlen; flia Hlen Hit | ].
cbn - [ "-" ].
f_equal. {
  rewrite Nat.mul_comm, Nat.Div0.mod_add.
  now apply Nat.mod_small, Hl; left.
}
rewrite Nat.mul_comm, Nat.div_add; [ | now subst n ].
rewrite Nat.div_small; [ | now apply Hl; left ].
rewrite Nat.add_0_l.
cbn in Hlen, Hit.
rewrite <- Nat.add_succ_r in Hlen, Hit |-*.
apply IHl; [ easy | | easy ].
intros i Hi.
now apply Hl; right.
Qed.

(* *)

Theorem to_radix_inv_to_radix : ∀ n k,
  k < n ^ n → to_radix_inv n (to_radix n k) = k.
Proof.
intros * Hkn.
progress unfold to_radix.
rewrite to_radix_inv_to_radix_loop.
now apply Nat.mod_small.
Qed.

Theorem to_radix_to_radix_inv : ∀ n l,
  length l = n
  → (∀ i, i ∈ l → i < n)
  → to_radix n (to_radix_inv n l) = l.
Proof.
intros * Hlen Hl.
progress unfold to_radix.
specialize to_radix_loop_to_radix_inv as H1.
specialize (H1 l 0 n n).
do 2 rewrite Nat.add_0_r in H1.
specialize (H1 Hlen Hl (Nat.le_refl _)).
now rewrite Nat.sub_diag, List.app_nil_r in H1.
Qed.

Theorem to_radix_loop_length : ∀ n l it, length (to_radix_loop it n l) = it.
Proof.
intros.
revert n l.
induction it; intros; cbn; [ easy | f_equal; apply IHit ].
Qed.

Theorem to_radix_length : ∀ n l, length (to_radix n l) = n.
Proof.
intros.
progress unfold to_radix.
apply to_radix_loop_length.
Qed.

Theorem to_radix_inv_ub : ∀ n l,
  n ≠ 0
  → (∀ i, i < length l → List.nth i l 0 < n)
  → to_radix_inv n l < n ^ length l.
Proof.
intros * Hnz Hl.
revert n Hnz Hl.
induction l as [| a]; intros; cbn; [ easy | ].
apply Nat.neq_0_lt_0 in Hnz.
specialize (Hl 0 (Nat.lt_0_succ _)) as H1; cbn in H1.
apply Nat.neq_0_lt_0 in Hnz.
specialize (IHl n Hnz) as H2.
assert (H : ∀ i, i < length l → List.nth i l 0 < n). {
  intros i Hi.
  apply (Hl (S i)); cbn.
  now apply -> Nat.succ_lt_mono.
}
specialize (H2 H); clear H.
now apply Nat_lt_lt_add_mul.
Qed.

Theorem to_radix_inj : ∀ n i j,
  i < n ^ n
  → j < n ^ n
  → to_radix n i = to_radix n j
  → i = j.
Proof.
intros * Hi Hj Hij.
apply (f_equal (to_radix_inv n)) in Hij.
rewrite to_radix_inv_to_radix in Hij; [ | easy ].
rewrite to_radix_inv_to_radix in Hij; [ | easy ].
easy.
Qed.

(* *)

Arguments "<?" : simpl never.

Global Hint Resolve Nat_mod_fact_upper_bound : core.

