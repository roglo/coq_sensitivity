(* Pigeonhole
   f : A → B & card B < card A → f non injective *)

(* borrowed 2021-01-17 from my development "coq_euler_prod_form" *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Misc.

Fixpoint find_dup f (la : list nat) :=
  match la with
  | [] => None
  | n :: la' =>
      match find (λ n', f n' =? f n) la' with
      | None => find_dup f la'
      | Some n' => Some (n, n')
      end
  end.

Definition pigeonhole_fun a (f : nat → nat) :=
  match find_dup f (seq 0 a) with
  | Some (n, n') => (n, n')
  | None => (0, 0)
  end.

Theorem find_dup_some : ∀ f x x' la,
  find_dup f la = Some (x, x')
  → f x = f x' ∧
     ∃ la1 la2 la3, la = la1 ++ x :: la2 ++ x' :: la3.
Proof.
intros * Hfd.
induction la as [| a]; [ easy | ].
cbn in Hfd.
remember (find (λ x', f x' =? f a) la) as r eqn:Hr.
symmetry in Hr.
destruct r as [n'| ]. {
  injection Hfd; clear Hfd; intros; subst x x'.
  apply find_some in Hr; cbn in Hr.
  destruct Hr as (Hx'la, Hba).
  apply Nat.eqb_eq in Hba.
  split; [ easy | ].
  exists []; cbn.
  apply in_split in Hx'la.
  destruct Hx'la as (l1 & l2 & Hll).
  exists l1, l2.
  now rewrite Hll.
} {
  specialize (IHla Hfd).
  destruct IHla as (H & la1 & la2 & la3 & Hll).
  split; [ easy | ].
  now exists (a :: la1), la2, la3; rewrite Hll.
}
Qed.

Theorem find_dup_none : ∀ f la,
  find_dup f la = None → NoDup (map f la).
Proof.
intros * Hnd.
induction la as [| a]; [ constructor | cbn ].
constructor. {
  cbn in Hnd.
  remember (find _ _) as b eqn:Hb; symmetry in Hb.
  destruct b; [ easy | ].
  specialize (find_none _ _ Hb) as H1; cbn in H1; cbn.
  intros Ha.
  specialize (IHla Hnd).
  clear - IHla H1 Ha.
  induction la as [ | b]; [ easy | ].
  cbn in Ha.
  cbn in IHla.
  destruct Ha as [Ha| Ha]. {
    specialize (H1 b (or_introl eq_refl)).
    now apply Nat.eqb_neq in H1.
  } {
    apply NoDup_cons_iff in IHla.
    destruct IHla as (Hn, Hnd).
    specialize (IHla0 Hnd).
    apply IHla0; [ | easy ].
    intros x Hx.
    now apply H1; right.
  }
} {
  apply IHla.
  cbn in Hnd.
  remember (find _ _) as b eqn:Hb; symmetry in Hb.
  now destruct b.
}
Qed.

Theorem not_NoDup_map_f_seq : ∀ a b f,
  b < a
  → (∀ x, x < a → f x < b)
  → NoDup (map f (seq 0 a))
  → False.
Proof.
intros * Hba Hf Hfd.
revert a f Hba Hf Hfd.
induction b; intros; [ now specialize (Hf _ Hba) | ].
destruct a; [ flia Hba | ].
apply Nat.succ_lt_mono in Hba.
remember (filter (λ i, f i =? b) (seq 0 (S a))) as la eqn:Hla.
symmetry in Hla.
destruct la as [| x1]. {
  assert (H : ∀ x, x < a → f x < b). {
    intros x Hx.
    destruct (Nat.eq_dec (f x) b) as [Hfxb| Hfxb]. {
      specialize (List_filter_nil _ _ Hla x) as H1.
      assert (H : x ∈ seq 0 (S a)). {
        apply in_seq.
        flia Hx.
      }
      specialize (H1 H); clear H; cbn in H1.
      now apply Nat.eqb_neq in H1.
    }
    assert (H : x < S a) by flia Hx.
    specialize (Hf x H); clear H.
    flia Hf Hfxb.
  }
  specialize (IHb a f Hba H); clear H.
  rewrite <- Nat.add_1_r in Hfd.
  rewrite seq_app in Hfd; cbn in Hfd.
  rewrite map_app in Hfd; cbn in Hfd.
  specialize (NoDup_remove_1 _ _ _ Hfd) as H1.
  now rewrite app_nil_r in H1.
}
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  subst b.
  destruct a; [ flia Hba | ].
  specialize (Hf a) as H1.
  assert (H : a < S (S a)) by flia.
  specialize (H1 H); clear H.
  specialize (Hf (S a) (Nat.lt_succ_diag_r _)) as H2.
  apply Nat.lt_1_r in H1.
  apply Nat.lt_1_r in H2.
  do 2 rewrite <- Nat.add_1_r in Hfd.
  do 2 rewrite seq_app in Hfd; cbn in Hfd.
  rewrite <- app_assoc in Hfd.
  do 2 rewrite map_app in Hfd.
  cbn in Hfd.
  apply NoDup_remove_2 in Hfd.
  apply Hfd.
  apply in_app_iff; right.
  now rewrite H1, Nat.add_1_r, H2; left.
}
destruct la as [| x2]. {
  specialize (IHb a (λ i, if lt_dec i x1 then f i else f (i + 1)) Hba).
  cbn in IHb.
  assert (H : ∀ x, x < a → (if lt_dec x x1 then f x else f (x + 1)) < b). {
    intros x Hx.
    destruct (lt_dec x x1) as [Hxx| Hxx]. {
      assert (Hxb : f x ≠ b). {
        intros Hxb.
        assert (H : x ∈ filter (λ i, f i =? b) (seq 0 (S a))). {
          apply filter_In.
          split; [ apply in_seq; cbn; flia Hx | ].
          now apply Nat.eqb_eq.
        }
        rewrite Hla in H.
        destruct H as [H| H]; [ flia Hxx H| easy ].
      }
      specialize (Hf x).
      assert (H : x < S a) by flia Hx.
      specialize (Hf H); clear H.
      flia Hf Hxb.
    }
    apply Nat.nlt_ge in Hxx.
    specialize (Hf (x + 1)).
    assert (H : x + 1 < S a) by flia Hx.
    specialize (Hf H); clear H.
    assert (Hxb : f (x + 1) ≠ b). {
      intros Hxb.
      assert (H : x + 1 ∈ filter (λ i, f i =? b) (seq 0 (S a))). {
        apply filter_In.
        split; [ apply in_seq; cbn; flia Hx | ].
        now apply Nat.eqb_eq.
      }
      rewrite Hla in H.
      destruct H as [H| H]; [ flia Hxx H| easy ].
    }
    flia Hf Hxb.
  }
  specialize (IHb H); clear H.
  apply IHb; clear - Hfd.
  specialize (proj1 (NoDup_map_iff 0 _ _) Hfd) as H1.
  apply (NoDup_map_iff 0).
  intros x x' Hx Hx' Hxx.
  rewrite seq_length in Hx, Hx', H1.
  rewrite seq_nth in Hxx; [ | easy ].
  rewrite seq_nth in Hxx; [ cbn | easy ].
  cbn in Hxx.
  destruct (lt_dec x x1) as [Hxx1| Hxx1]. {
    destruct (lt_dec x' x1) as [Hx'x1| Hx'x1]. {
      apply H1; [ flia Hx | flia Hx' | ].
      rewrite seq_nth; [ | flia Hx ].
      rewrite seq_nth; [ easy | flia Hx' ].
    } {
      apply Nat.nlt_ge in Hx'x1.
      assert (H : x = x' + 1). {
        apply H1; [ flia Hx | flia Hx' | ].
        rewrite seq_nth; [ | flia Hx ].
        rewrite seq_nth; [ easy | flia Hx' ].
      }
      flia Hxx1 Hx'x1 H.
    }
  }
  apply Nat.nlt_ge in Hxx1.
  destruct (lt_dec x' x1) as [Hx'x1| Hx'x1]. {
    assert (H : x + 1 = x'). {
      apply H1; [ flia Hx | flia Hx' | ].
      rewrite seq_nth; [ | flia Hx ].
      rewrite seq_nth; [ easy | flia Hx' ].
    }
    flia Hxx1 Hx'x1 H.
  } {
    apply Nat.nlt_ge in Hx'x1.
    apply (Nat.add_cancel_r _ _ 1).
    apply H1; [ flia Hx | flia Hx' | ].
    rewrite seq_nth; [ | flia Hx ].
    rewrite seq_nth; [ easy | flia Hx' ].
  }
}
assert (Hx1 : x1 ∈ x1 :: x2 :: la) by now left.
assert (Hx2 : x2 ∈ x1 :: x2 :: la) by now right; left.
rewrite <- Hla in Hx1.
rewrite <- Hla in Hx2.
apply filter_In in Hx1.
apply filter_In in Hx2.
destruct Hx1 as (Hx1, Hfx1).
destruct Hx2 as (Hx2, Hfx2).
apply Nat.eqb_eq in Hfx1.
apply Nat.eqb_eq in Hfx2.
assert (H : x1 ≠ x2). {
  intros H; subst x2.
  clear - Hla.
  specialize (seq_NoDup (S a) 0) as H1.
  specialize (NoDup_filter (λ i, f i =? b) H1) as H2.
  rewrite Hla in H2.
  apply NoDup_cons_iff in H2.
  destruct H2 as (H2, _); apply H2.
  now left.
}
clear - Hfd Hx1 Hx2 H Hfx1 Hfx2.
remember (seq 0 (S a)) as l; clear a Heql.
apply H; clear H.
specialize (proj1 (NoDup_map_iff 0 l (λ x, f x)) Hfd) as H1.
cbn in H1.
apply (In_nth _ _ 0) in Hx1.
apply (In_nth _ _ 0) in Hx2.
destruct Hx1 as (n1 & Hn1 & Hx1).
destruct Hx2 as (n2 & Hn2 & Hx2).
specialize (H1 _ _ Hn1 Hn2) as H2.
rewrite Hx1, Hx2, Hfx1, Hfx2 in H2.
rewrite <- Hx1, <- Hx2.
f_equal.
now apply H2.
Qed.

Theorem pigeonhole : ∀ a b f,
  b < a
  → (∀ x, x < a → f x < b)
  → ∀ x x', pigeonhole_fun a f = (x, x')
  → x < a ∧ x' < a ∧ x ≠ x' ∧ f x = f x'.
Proof.
intros * Hba Hf * Hpf.
unfold pigeonhole_fun in Hpf.
remember (find_dup _ _) as fd eqn:Hfd.
symmetry in Hfd.
destruct fd as [(n, n') |]. {
  injection Hpf; clear Hpf; intros; subst n n'.
  specialize (find_dup_some f _ _ _ Hfd) as (Hfxx & la1 & la2 & la3 & Hll).
  assert (Hxy : x ∈ seq 0 a). {
    rewrite Hll.
    apply in_app_iff.
    now right; left.
  }
  apply in_seq in Hxy; cbn in Hxy.
  destruct Hxy as (_, Hxa).
  assert (Hx' : x' ∈ seq 0 a). {
    rewrite Hll.
    apply in_app_iff; right; right.
    now apply in_app_iff; right; left.
  }
  apply in_seq in Hx'.
  split; [ easy | ].
  split; [ easy | ].
  split; [ | easy ].
  specialize (seq_NoDup a 0) as H.
  rewrite Hll in H.
  apply NoDup_remove_2 in H.
  intros Hxx; apply H; subst x'.
  apply in_app_iff; right.
  now apply in_app_iff; right; left.
} {
  apply find_dup_none in Hfd.
  exfalso.
  now apply not_NoDup_map_f_seq in Hf.
}
Qed.

Theorem pigeonhole_exist : ∀ a b f,
  b < a
  → (∀ x, x < a → f x < b)
  → ∃ x x', x < a ∧ x' < a ∧ x ≠ x' ∧ f x = f x'.
Proof.
intros * Hba Hf.
remember (pigeonhole_fun a f) as xx' eqn:Hpf.
symmetry in Hpf.
destruct xx' as (x, x').
exists x, x'.
now apply (pigeonhole a b).
Qed.

(* version list instead of fun *)

Definition pigeonhole_comp_list l :=
  match find_dup (λ i, nth i l 0) (seq 0 (length l)) with
  | Some (n, n') => (n, n')
  | None => (0, 0)
  end.

Theorem better_pigeonhole_list : ∀ a l,
  a < length l
  → (∀ x, x ∈ l → x < a)
  → ∀ x x', pigeonhole_comp_list l = (x, x')
  → x < length l ∧ x' < length l ∧ x ≠ x' ∧ nth x l 0 = nth x' l 0.
Proof.
intros * Hal Hla * Hpcl.
remember (λ i, nth i l 0) as f.
rename a into b.
(*
  b < a
  → (∀ x, x < a → f x < b)
  → ∀ x x', pigeonhole_fun a f = (x, x')
  → x < a ∧ x' < a ∧ x ≠ x' ∧ f x = f x'.
intros * Hba Hf * Hpf.
*)
unfold pigeonhole_comp_list in Hpcl.
rewrite <- Heqf in Hpcl.
remember (find_dup _ _) as fd eqn:Hfd.
symmetry in Hfd.
destruct fd as [(n, n') |]. {
  injection Hpcl; clear Hpcl; intros; subst n n'.
  specialize (find_dup_some f _ _ _ Hfd) as (Hfxx & la1 & la2 & la3 & Hll).
  assert (Hxy : x ∈ seq 0 (length l)). {
    rewrite Hll.
    apply in_app_iff.
    now right; left.
  }
  apply in_seq in Hxy; cbn in Hxy.
  destruct Hxy as (_, Hxa).
  assert (Hx' : x' ∈ seq 0 (length l)). {
    rewrite Hll.
    apply in_app_iff; right; right.
    now apply in_app_iff; right; left.
  }
  apply in_seq in Hx'.
  split; [ easy | ].
  split; [ easy | ].
  split; [ | now rewrite Heqf in Hfxx ].
  specialize (seq_NoDup (length l) 0) as H.
  rewrite Hll in H.
  apply NoDup_remove_2 in H.
  intros Hxx; apply H; subst x'.
  apply in_app_iff; right.
  now apply in_app_iff; right; left.
} {
  apply find_dup_none in Hfd.
  exfalso.
  apply not_NoDup_map_f_seq with (b := b) in Hfd; [ easy | easy | ].
  intros y Hy.
  apply Hla.
  rewrite Heqf.
  now apply nth_In.
}
Qed.

...

Theorem pigeonhole_list : ∀ a l,
  a < length l
  → (∀ x, x ∈ l → x < a)
  → ∀ x x', pigeonhole_comp_list l = (x, x')
  → x < length l ∧ x' < length l ∧ x ≠ x' ∧ nth x l 0 = nth x' l 0.
Proof.
intros * Hal Hla * Hpcl.
remember (λ i, nth i l 0) as f.
rename a into b.
remember (length l) as a.
assert (Hf : ∀ x, x < a → f x < b). {
  subst a f; cbn.
  intros y Hy.
  now apply Hla, nth_In.
}
assert (Hpf : pigeonhole_fun a f = (x, x')) by now subst f a.
specialize (pigeonhole a b f Hal Hf _ _ Hpf) as H1.
now subst f.
Qed.

Theorem pigeonhole_list_exist : ∀ a l,
  a < length l
  → (∀ x, x ∈ l → x < a)
  → ∃ x x', x < length l ∧ x' < length l ∧ x ≠ x' ∧ nth x l 0 = nth x' l 0.
Proof.
intros * Hal Hla.
remember (pigeonhole_comp_list l) as xx' eqn:Hpf.
symmetry in Hpf.
destruct xx' as (x, x').
exists x, x'.
now apply (pigeonhole_list a l).
Qed.

(* fin_t : finite type, implemented with type "sig" *)

Definition fin_t n := {a : nat | (a <? n) = true}.

Theorem fin_t_fun_le : ∀ m n (f : fin_t m → fin_t n) g,
  (∀ y, f (g y) = y) → n ≤ m.
Proof.
intros * Hfg.
specialize (pigeonhole) as H1.
specialize (H1 n m).
apply Nat.nlt_ge; intros Hmn.
set (f' := λ y : nat,
  match lt_dec y n with
  | left Hyn =>
      let H := proj2 (Nat.ltb_lt y n) Hyn in
      proj1_sig (g (exist (λ a, (a <? n) = true) y H))
  | right b => 0
  end).
specialize (H1 f' Hmn).
assert (H : ∀ x, x < n → f' x < m). {
  intros x Hx; unfold f'; cbn - [ "<?" ].
  destruct (lt_dec x n) as [H| H]; [ | flia Hx H ].
  remember (g _) as y eqn:Hy.
  destruct y as (y, py).
  now apply Nat.ltb_lt.
}
specialize (H1 H); clear H.
unfold pigeonhole_fun in H1.
remember (find_dup f' (seq 0 n)) as x eqn:Hx; symmetry in Hx.
destruct x as [(n1, n2)| ]; [ | now apply (H1 0 0 eq_refl) ].
specialize (H1 n1 n2 eq_refl).
destruct H1 as (Hn1n & Hn2n & Hnn & Hfnn).
unfold f' in Hfnn.
destruct (lt_dec n1 n) as [H1| H]; [ | flia Hn1n H ].
destruct (lt_dec n2 n) as [H2| H]; [ | flia Hn2n H ].
remember (g _) as x eqn:Hx' in Hfnn.
remember (g _) as y eqn:Hy' in Hfnn.
destruct x as (x, px).
destruct y as (y, py).
cbn in Hfnn.
subst y.
move py before px.
assert (H : px = py). {
  clear - px py.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
}
destruct H.
rewrite Hy' in Hx'.
apply (f_equal f) in Hx'.
do 2 rewrite Hfg in Hx'.
now injection Hx'; intros H; symmetry in H.
Qed.

Theorem bijective_fin_t : ∀ m n (f : fin_t m → fin_t n),
  FinFun.Bijective f → m = n.
Proof.
intros * Hf.
destruct Hf as (g & Hgf & Hfg).
destruct (Nat.lt_trichotomy m n) as [Hmn| [Hmn| Hmn]]; [ | easy | ]. {
  exfalso.
  apply Nat.nle_gt in Hmn; apply Hmn; clear Hmn.
  now apply fin_t_fun_le in Hfg.
} {
  exfalso.
  apply Nat.nle_gt in Hmn; apply Hmn; clear Hmn.
  now apply fin_t_fun_le in Hgf.
}
Qed.

(* end fin_t *)
