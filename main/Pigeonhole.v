(* Pigeonhole
   f : A → B & card B < card A → f non injective *)

(* borrowed 2021-01-17 from my development "coq_euler_prod_form" *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require FinFun.
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

Theorem List_in_split' :
  ∀ (A : Type) (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (x : A) (l : list A),
  x ∈ l → ∃ l1 l2 : list A, l = l1 ++ x :: l2 ∧ x ∉ l1.
Proof.
intros * eq_dec * Hx.
revert x Hx.
induction l as [| y]; intros; [ easy | ].
destruct Hx as [Hx| Hx]. {
  subst y.
  now exists [], l.
}
specialize (IHl _ Hx) as H1.
destruct H1 as (l1 & l2 & Hll & Hl1).
rewrite Hll.
destruct (eq_dec y x) as [Hxy| Hxy]. {
  subst y.
  now exists [], (l1 ++ x :: l2).
}
exists (y :: l1), l2.
split; [ easy | ].
intros H; apply Hl1.
now destruct H.
Qed.

Theorem List_eq_dec_In_nth :
  ∀ (A : Type) (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (l : list A) (x d : A),
  x ∈ l →
  ∃ n : nat, n < length l ∧ nth n l d = x ∧ ∀ m, m < n → nth m l d ≠ x.
Proof.
intros * eq_dec * Hxl.
revert x Hxl.
induction l as [| y]; intros; [ easy | ].
rewrite List_cons_length.
destruct Hxl as [Hxl| Hxl]. {
  subst y.
  exists 0.
  rewrite List_nth_0_cons.
  split; [ flia | easy ].
}
specialize (IHl x Hxl) as H1.
destruct H1 as (n & Hnl & Hyx & Hm).
destruct (eq_dec y x) as [Hxy| Hxy]. {
  subst y.
  exists 0.
  split; [ flia | easy ].
}
exists (S n).
rewrite List_nth_succ_cons.
split; [ now apply Nat.succ_lt_mono in Hnl | ].
split; [ easy | ].
intros m Hm'.
destruct m; [ easy | cbn ].
apply Nat.succ_lt_mono in Hm'.
now apply Hm.
Qed.

Theorem List_find_some_if :
  ∀ (A : Type) (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) f d (l : list A) x,
  find f l = Some x →
  ∃ i, i < length l ∧ x = nth i l d ∧ f x = true ∧
  ∀ j, j < i → f (nth j l d) = false.
Proof.
intros * eq_dec * Hf.
specialize (find_some _ _ Hf) as H1.
destruct H1 as (Hx, Hfx).
apply (List_eq_dec_In_nth A eq_dec l x d) in Hx.
destruct Hx as (i & Hi & Hix & Hx).
exists i.
split; [ easy | ].
split; [ easy | ].
split; [ easy | ].
intros j Hj.
revert i j Hi Hix Hx Hj.
induction l as [| a]; intros; [ easy | ].
cbn in Hf.
remember (f a) as b eqn:Hb; symmetry in Hb.
destruct b. {
  injection Hf; clear Hf; intros; subst a.
  clear Hb.
  destruct i; [ easy | ].
  now specialize (Hx 0 (Nat.lt_0_succ _)) as H1.
}
destruct i; [ easy | ].
cbn in Hi, Hix; apply Nat.succ_lt_mono in Hi.
destruct j; [ easy | cbn ].
apply Nat.succ_lt_mono in Hj.
apply IHl with (i := i); [ easy | easy | easy | | easy ].
intros m Hm.
specialize (Hx (S m)); cbn in Hx.
apply Hx.
now apply -> Nat.succ_lt_mono.
Qed.

Theorem find_dup_some : ∀ f x x' la,
  find_dup f la = Some (x, x')
  → f x = f x' ∧
    ∃ la1 la2 la3, la = la1 ++ x :: la2 ++ x' :: la3 ∧
    (∀ y y', y ∈ la1 → y' ∈ la → f y = f y' → y = y') ∧
    (∀ x'', x'' ∈ la1 ++ la2 → f x'' ≠ f x).
Proof.
intros * Hfd.
induction la as [| a]; [ easy | ].
cbn in Hfd.
remember (find (λ x', f x' =? f a) la) as r eqn:Hr.
symmetry in Hr.
destruct r as [n'| ]. {
  injection Hfd; clear Hfd; intros; subst x x'.
  apply (List_find_some_if _ Nat.eq_dec _ 0) in Hr.
  destruct Hr as (i & Hi & Hn'i & Heq & Hbef).
  apply Nat.eqb_eq in Heq.
  split; [ easy | ].
  exists []; cbn.
  assert (Hx'la : n' ∈ la) by now rewrite Hn'i; apply nth_In.
  apply (List_in_split' _ Nat.eq_dec) in Hx'la.
  destruct Hx'la as (l1 & l2 & Hla & Hn').
  exists l1, l2.
  rewrite Hla.
  split; [ easy | ].
  split; [ easy | ].
  intros n'' Hx''.
  assert (Hil : i = length l1). {
    rewrite Hla in Hn'i.
    destruct (Nat.lt_trichotomy i (length l1)) as [Hil| [Hil| Hil]]. {
      rewrite app_nth1 in Hn'i; [ | easy ].
      exfalso; apply Hn'; clear Hn'.
      now subst n'; apply nth_In.
    } {
      easy.
    } {
      rewrite app_nth2 in Hn'i; [ | flia Hil ].
      specialize (Hbef (length l1) Hil) as H1.
      apply Nat.eqb_neq in H1.
      rewrite Hla in H1.
      rewrite app_nth2 in H1; [ | now unfold ge ].
      now rewrite Nat.sub_diag in H1; cbn in H1.
    }
  }
  apply (List_eq_dec_In_nth _ Nat.eq_dec _ _ 0) in Hx''.
  destruct Hx'' as (j & Hj & Hjn & Hbefn).
  rewrite <- Hil in Hj.
  specialize (Hbef _ Hj) as H1.
  apply Nat.eqb_neq in H1.
  rewrite Hla in H1.
  rewrite app_nth1 in H1; [ | now rewrite Hil in Hj ].
  now rewrite Hjn in H1.
} {
  specialize (IHla Hfd).
  destruct IHla as (Hxx & la1 & la2 & la3 & Hll & H1stx & H1stx').
  split; [ easy | ].
  exists (a :: la1), la2, la3; rewrite Hll.
  split; [ easy | ].
  split. {
    intros y y' Hy Hy' Hyy.
    rewrite <- Hll in Hy'.
    destruct Hy as [Hy| Hy]. {
      subst y.
      destruct Hy' as [Hy'| Hy']; [ easy | ].
      specialize (find_none _ _ Hr y' Hy') as H1; cbn in H1.
      apply Nat.eqb_neq in H1.
      now symmetry in Hyy.
    }
    destruct Hy' as [Hy'| Hy']. {
      subst y'.
      specialize (find_none _ _ Hr y) as H1.
      assert (H : y ∈ la) by now rewrite Hll; apply in_or_app; left.
      specialize (H1 H); clear H.
      now apply Nat.eqb_neq in H1.
    }
    now apply H1stx.
  }
  intros x'' Hx''.
  destruct Hx'' as [Hx''| Hx'']. {
    subst x''.
    specialize (find_none _ _ Hr x) as H1.
    assert (H : x ∈ la). {
      rewrite Hll.
      now apply in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    apply Nat.eqb_neq in H1.
    now apply Nat.neq_sym in H1.
  }
  now apply H1stx'.
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
      specialize (proj1 (List_filter_nil_iff _ _) Hla x) as H1.
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
  specialize (find_dup_some f _ _ _ Hfd) as H.
  destruct H as (Hfxx & la1 & la2 & la3 & Hll & Hbef).
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

(* version list instead of fun *)

Fixpoint search_double_loop {A} eqb i (l : list A) :=
  match l with
  | a :: l' =>
      let j := List_rank (eqb a) l' in
      if lt_dec j (length l') then (i, j + 1)
      else search_double_loop eqb (S i) l'
  | [] => (0, 0)
  end.

Definition pigeonhole_comp_list l :=
  match find_dup (λ i, nth i l 0) (seq 0 (length l)) with
  | Some (n, n') => (n, n')
  | None => (0, 0)
  end.

Theorem seq_app_cons_app_cons : ∀ sta len x y la1 la2 la3,
  seq sta len = la1 ++ x :: la2 ++ y :: la3
  ↔ len = length la1 + length la2 + length la3 + 2 ∧
    x = sta + length la1 ∧
    y = S x + length la2 ∧
    la1 = seq sta (length la1) ∧
    la2 = seq (S x) (length la2) ∧
    la3 = seq (S y) (sta + len - S y).
Proof.
intros.
split. {
  intros Hs.
  generalize Hs; intros Hsv.
  move Hsv after Hs.
  rewrite (List_seq_cut3 (sta + length la1)) in Hs. 2: {
    apply in_seq.
    split; [ flia | ].
    apply Nat.add_lt_mono_l.
    clear Hsv.
    revert sta la1 Hs.
    induction len; intros; cbn. {
      now symmetry in Hs; apply app_eq_nil in Hs.
    }
    destruct la1 as [| a]; cbn; [ flia | ].
    apply -> Nat.succ_lt_mono.
    cbn in Hs.
    injection Hs; clear Hs; intros Hs Ha.
    now apply IHlen in Hs.
  }
  apply List_app_eq_app' in Hs. 2: {
    rewrite seq_length, Nat.add_comm.
    apply Nat.add_sub.
  }
  destruct Hs as (Hla1 & Hs); symmetry in Hla1.
  rewrite Nat.add_comm, Nat.add_sub in Hla1.
  cbn in Hs.
  injection Hs; clear Hs; intros Hs Hx; symmetry in Hx.
  move Hx after Hla1.
  split. {
    apply (f_equal length) in Hsv.
    rewrite seq_length in Hsv.
    rewrite app_length in Hsv; cbn in Hsv.
    rewrite app_length in Hsv; cbn in Hsv.
    flia Hsv.
  }
  split; [ easy | ].
  rewrite <- Hx in Hs.
  rewrite (List_seq_cut3 (S x + length la2)) in Hs. 2: {
    apply in_seq.
    split; [ flia | ].
    apply Nat.add_lt_mono_l.
    apply (f_equal length) in Hs.
    rewrite seq_length in Hs.
    rewrite app_length in Hs.
    cbn in Hs; flia Hs.
  }
  rewrite Nat.add_comm, Nat.add_sub in Hs.
  apply List_app_eq_app' in Hs; [ | now rewrite seq_length ].
  destruct Hs as (Hla2, Hs); symmetry in Hla2; cbn in Hs.
  injection Hs; clear Hs; intros Hla3 Hy.
  move Hy before Hx; symmetry in Hy.
  symmetry in Hla3; rewrite <- Hy in Hla3.
  rewrite Nat.add_sub_assoc in Hla3. 2: {
    rewrite Hx, <- Nat.add_succ_r.
    apply Nat.add_le_mono_l.
    apply (f_equal length) in Hsv.
    rewrite seq_length, app_length in Hsv; cbn in Hsv.
    flia Hsv.
  }
  rewrite Nat.add_comm in Hla3.
  rewrite <- (Nat.add_1_r x) in Hla3.
  rewrite Nat.sub_add_distr, Nat.add_sub in Hla3.
  rewrite <- Nat.sub_add_distr in Hla3; cbn in Hla3.
  now rewrite Nat.add_comm.
} {
  intros (Hlen & Hx & Hy & Hla1 & Hla2 & Hla3).
  rewrite (List_seq_cut3 x). 2: {
    apply in_seq; rewrite Hx.
    split; [ flia | ].
    apply Nat.add_lt_mono_l.
    flia Hlen.
  }
  cbn; rewrite Hx at 1.
  rewrite Nat.add_comm, Nat.add_sub, <- Hla1, Hla2.
  f_equal; f_equal.
  rewrite Hla3.
  rewrite cons_seq.
  rewrite Hy at 1.
  rewrite <- seq_app.
  f_equal.
  flia Hx Hy Hlen.
}
Qed.

Theorem pigeonhole_list : ∀ a l,
  a < length l
  → (∀ x, x ∈ l → x < a)
  → ∀ x x', pigeonhole_comp_list l = (x, x')
  → x < length l ∧ x' < length l ∧ x ≠ x' ∧ nth x l 0 = nth x' l 0.
Proof.
intros * Hal Hla * Hpcl.
unfold pigeonhole_comp_list in Hpcl.
remember (find_dup _ _) as fd eqn:Hfd.
symmetry in Hfd.
destruct fd as [(n, n') |]. {
  injection Hpcl; clear Hpcl; intros; subst n n'.
  apply find_dup_some in Hfd.
  destruct Hfd as (Hxx & la1 & la2 & la3 & Hll & H1stx & H1stx').
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
  split; [ | easy ].
  specialize (seq_NoDup (length l) 0) as H.
  rewrite Hll in H.
  apply NoDup_remove_2 in H.
  intros Hxix; apply H; subst x'.
  apply in_app_iff; right.
  now apply in_app_iff; right; left.
} {
  apply find_dup_none in Hfd.
  exfalso; clear Hpcl.
  apply not_NoDup_map_f_seq with (b := a) in Hfd; [ easy | easy | ].
  intros y Hy.
  apply Hla.
  now apply nth_In.
}
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
