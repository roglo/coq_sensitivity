(* Testing if a list is a permutation of another one *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.

Import List List.ListNotations.
Require Import Misc.

Fixpoint extract {A} (f : A → bool) l :=
  match l with
  | [] => None
  | a :: la =>
      if f a then Some ([], a, la)
      else
        match extract f la with
        | None => None
        | Some (bef, b, aft) => Some (a :: bef, b, aft)
        end
  end.

Fixpoint is_permutation {A} (eqb : A → A → bool) (la lb : list A) :=
  match la with
  | [] => match lb with [] => true | _ => false end
  | a :: la' =>
      match extract (eqb a) lb with
      | None => false
      | Some (bef, _, aft) => is_permutation eqb la' (bef ++ aft)
      end
  end.

Definition equality {A} (eqb : A → A → bool) := ∀ a b, eqb a b = true ↔ a = b.

Theorem equality_refl {A} (eqb : A → _) : equality eqb → ∀ a, eqb a a = true.
Proof.
intros * Heqb *.
now apply Heqb.
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

Theorem extract_None_iff : ∀ A (f : A → _) l,
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

Theorem permutation_in : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  is_permutation eqb la lb = true →
  (∀ a, a ∈ la ↔ a ∈ lb).
Proof.
intros * Heqb * Hab *.
split. {
  intros Hla.
  revert a lb Hab Hla.
  induction la as [| b]; intros; [ easy | cbn ].
  cbn in Hab.
  remember (extract (eqb b) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlb).
  apply Heqb in H; subst x lb.
  destruct Hla as [Hla| Hla]. {
    now subst b; apply in_or_app; right; left.
  }
  assert (Ha : a ∈ bef ++ aft) by now apply IHla.
  apply in_app_or in Ha.
  apply in_or_app.
  now destruct Ha; [ left | right; right ].
} {
  intros Hlb.
  revert a lb Hab Hlb.
  induction la as [| b]; intros; cbn in Hab; [ now destruct lb | ].
  remember (extract (eqb b) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlba).
  apply Heqb in H; subst x lb.
  apply in_app_or in Hlb.
  destruct Hlb as [Hlb| Hlb]. 2: {
    destruct Hlb as [Hlb| Hlb]; [ now left | right ].
    apply (IHla a (bef ++ aft) Hab).
    now apply in_or_app; right.
  }
  right; apply (IHla a (bef ++ aft) Hab).
  now apply in_or_app; left.
}
Qed.

Theorem permutation_app_inv : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb lc ld a,
  a ∉ la
  → a ∉ lc
  → is_permutation eqb (la ++ a :: lb) (lc ++ a :: ld) = true
  → is_permutation eqb (la ++ lb) (lc ++ ld) = true.
Proof.
intros * Heqb * Hala Halc Hp.
revert lb lc ld a Hp Hala Halc.
induction la as [| b]; intros; cbn in Hp |-*. {
  clear Hala.
  remember (extract (eqb a) (lc ++ a :: ld)) as lxl eqn:Hlxl.
  symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlb).
  apply Heqb in H; subst x.
  apply app_eq_app in Hlb.
  destruct Hlb as (l & Hlb).
  destruct Hlb as [(H1, H2)| (H1, H2)]. {
    subst lc.
    destruct l as [| b]; cbn in H2. {
      injection H2; clear H2; intros; subst aft.
      now rewrite app_nil_r.
    }
    injection H2; clear H2; intros H2 H; subst b.
    exfalso; apply Halc.
    now apply in_or_app; right; left.
  }
  subst bef.
  destruct l as [| b]; cbn in H2. {
    injection H2; clear H2; intros; subst aft.
    now rewrite app_nil_r in Hp.
  }
  injection H2; clear H2; intros H2 H; subst b.
  specialize (Hbef a) as H1.
  assert (H : a ∈ lc ++ a :: l) by now apply in_or_app; right; left.
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
remember (extract (eqb b) (lc ++ a :: ld)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply app_eq_app in Hlb.
destruct Hlb as (l & Hlb).
destruct Hlb as [(H1, H2)| (H1, H2)]. {
  subst lc.
  destruct l as [| c]; cbn in H2. {
    injection H2; clear H2; intros; subst aft b.
    now exfalso; apply Hala; left.
  }
  injection H2; clear H2; intros H2 H; subst c aft.
  rewrite <- app_assoc.
  remember (extract (eqb b) (bef ++ (b :: l) ++ ld)) as lxl eqn:Hlxl.
  symmetry in Hlxl.
  destruct lxl as [((bef', x), aft')| ]. 2: {
    specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
    specialize (H1 b).
    assert (H : b ∈ bef ++ (b :: l) ++ ld). {
      now apply in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    now rewrite (equality_refl Heqb) in H1.
  }
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef' & H & Hlb).
  apply Heqb in H; subst x.
  apply app_eq_app in Hlb.
  destruct Hlb as (l' & Hlb).
  destruct Hlb as [(H1, H2)| (H1, H2)]. {
    subst bef.
    destruct l' as [| c]; cbn in H2. 2: {
      injection H2; clear H2; intros H2 H; subst c aft'.
      specialize (Hbef b) as H1.
      assert (H : b ∈ bef' ++ b :: l'). {
        now apply in_or_app; right; left.
      }
      specialize (H1 H); clear H.
      now rewrite (equality_refl Heqb) in H1.
    }
    injection H2; clear H2; intros; subst aft'.
    rewrite app_nil_r in Hp, Halc.
    rewrite app_assoc.
    apply IHla with (a := a); cycle 1. {
      now intros H; apply Hala; right.
    } {
      intros H; apply Halc.
      apply in_app_or in H.
      apply in_or_app.
      now destruct H as [H| H]; [ left | right; right ].
    }
    now rewrite <- app_assoc.
  }
  subst bef'.
  destruct l' as [| c]; cbn in H2. 2: {
    injection H2; clear H2; intros H2 H; subst c.
    specialize (Hbef' b) as H1.
    assert (H : b ∈ bef ++ b :: l'). {
      now apply in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    now rewrite (equality_refl Heqb) in H1.
  }
  injection H2; clear H2; intros H2; subst aft'.
  rewrite app_nil_r in Hbef' |-*.
  rewrite app_assoc.
  apply IHla with (a := a); cycle 1. {
    now intros H; apply Hala; right.
  } {
    intros H; apply Halc.
    apply in_app_or in H.
    apply in_or_app.
    now destruct H as [H| H]; [ left | right; right ].
  }
  now rewrite <- app_assoc.
}
subst bef.
remember (extract (eqb b) (lc ++ ld)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft')| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 b).
  assert (H : b ∈ lc ++ ld). {
    apply in_or_app; right.
    specialize (in_elt b l aft) as H3.
    rewrite <- H2 in H3.
    destruct H3 as [H3| H3]; [ subst b | easy ].
    now exfalso; apply Hala; left.
  }
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb).
apply Heqb in H; subst x.
apply app_eq_app in Hlb.
destruct Hlb as (l' & Hlb).
destruct Hlb as [(H1, H3)| (H1, H3)]. 2: {
  subst bef ld.
  rewrite app_comm_cons in H2.
  apply app_eq_app in H2.
  destruct H2 as (l'' & H2).
  destruct H2 as [(H2, H4)| (H2, H4)]. {
    destruct l'' as [| c]. {
      rewrite app_nil_r in H2; subst l; cbn in H4.
      injection H4; clear H4; intros; subst aft'.
      rewrite <- app_assoc.
      apply IHla with (a := a); [ | | easy ]. 2: {
        now intros H; apply Hala; right.
      }
      now rewrite app_comm_cons, app_assoc.
    }
    cbn in H4.
    injection H4; clear H4; intros H4 H; subst c aft.
    specialize (Hbef' b) as H1.
    assert (H : b ∈ lc ++ l'). {
      apply in_or_app; right.
      specialize (in_elt b l l'') as H3.
      rewrite <- H2 in H3.
      destruct H3 as [H3| H3]; [ subst b | easy ].
      now exfalso; apply Hala; left.
    }
    specialize (H1 H); clear H.
    now rewrite (equality_refl Heqb) in H1.
  }
  subst l.
  destruct l'' as [| c]. {
    rewrite app_nil_r in Hp.
    cbn in H4.
    injection H4; clear H4; intros; subst aft'.
    rewrite <- app_assoc.
    apply IHla with (a := a); [ | | easy ]. 2: {
      now intros H; apply Hala; right.
    }
    now rewrite app_comm_cons, app_assoc.
  }
  cbn in H4.
  injection H4; clear H4; intros H4 H; subst c aft'.
  specialize (Hbef b) as H1.
  assert (H : b ∈ lc ++ (a :: l') ++ b :: l''). {
    apply in_or_app; right.
    now apply in_or_app; right; left.
  }
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
subst lc.
move H2 before H3.
destruct l as [| c]. {
  cbn in H2.
  injection H2; clear H2; intros; subst b aft.
  now exfalso; apply Hala; left.
}
cbn in H2.
injection H2; clear H2; intros H2 H; subst c ld.
destruct l' as [| c]. {
  cbn in H3.
  rewrite app_nil_r in Hp, Hbef, Halc.
  destruct l as [| c]. {
    cbn in H3.
    injection H3; clear H3; intros; subst aft'.
    rewrite <- app_assoc in Hp; cbn in Hp.
    apply IHla with (a := a); [ easy | | easy ].
    now intros H; apply Hala; right.
  }
  cbn in H3.
  injection H3; clear H3; intros H3 H; subst c aft'.
  specialize (Hbef b) as H1.
  assert (H : b ∈ bef ++ a :: b :: l). {
    now apply in_or_app; right; right; left.
  }
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
cbn in H3.
injection H3; clear H3; intros H3 H; subst c.
specialize (Hbef b) as H1.
assert (H : b ∈ (bef ++ b :: l') ++ a :: l). {
  apply in_or_app; left.
  now apply in_or_app; right; left.
}
specialize (H1 H); clear H.
now rewrite (equality_refl Heqb) in H1.
Qed.

Theorem permutation_sym : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  is_permutation eqb la lb = true → is_permutation eqb lb la = true.
Proof.
intros * Heqb * Hab.
revert la Hab.
induction lb as [| b]; intros; [ now destruct la | cbn ].
remember (extract (eqb b) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1; clear Hlxl.
  specialize (permutation_in Heqb _ _ Hab) as H2.
  specialize (proj2 (H2 b) (or_introl eq_refl)) as H3.
  specialize (H1 _ H3).
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (H1 & H2 & H3).
apply Heqb in H2; subst x.
subst la.
apply IHlb.
replace lb with ([] ++ lb) by easy.
apply permutation_app_inv with (a := b); [ easy | | easy | easy ].
intros H; specialize (H1 _ H).
now rewrite (equality_refl Heqb) in H1.
Qed.

Theorem permutation_trans : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb lc,
  is_permutation eqb la lb = true
  → is_permutation eqb lb lc = true
  → is_permutation eqb la lc = true.
Proof.
intros * Heqb * Hab Hbc.
revert lb lc Hab Hbc.
induction la as [| a]; intros; cbn. {
  now cbn in Hab, Hbc; destruct lb.
}
cbn in Hab.
remember (extract (eqb a) lc) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  clear Hlxl.
  remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft) | ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlb).
  apply Heqb in H; subst x.
  specialize (permutation_in Heqb lb lc Hbc) as H2.
  specialize (H2 a) as H3.
  assert (H : a ∈ lb) by now subst lb; apply in_or_app; right; left.
  specialize (proj1 H3 H) as H4; clear H.
  specialize (H1 _ H4).
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb').
apply Heqb in H; subst x.
subst lb lc.
apply IHla with (lb := bef' ++ aft'); [ easy | ].
assert (Hanb : a ∉ bef). {
  intros H; apply Hbef in H.
  now rewrite (equality_refl Heqb) in H.
}
assert (Hanb' : a ∉ bef'). {
  intros H; apply Hbef' in H.
  now rewrite (equality_refl Heqb) in H.
}
clear Hbef Hbef'.
clear la IHla Hab.
now apply permutation_app_inv in Hbc.
Qed.

Theorem permutation_refl : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l, is_permutation eqb l l = true.
Proof.
intros * Heqb *.
induction l as [| a]; [ easy | cbn ].
now rewrite (equality_refl Heqb).
Qed.

Theorem permutation_app_head : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l tl tl',
  is_permutation eqb tl tl' = true
  → is_permutation eqb (l ++ tl) (l ++ tl') = true.
Proof.
intros * Heqb * Hll'.
revert tl tl' Hll'.
induction l as [| a]; intros; [ easy | cbn ].
rewrite (equality_refl Heqb).
now apply IHl.
Qed.

Theorem permutation_app_tail : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l l' tl,
  is_permutation eqb l l' = true
  → is_permutation eqb (l ++ tl) (l' ++ tl) = true.
Proof.
intros * Heqb * Hll'.
revert l' tl Hll'.
induction l as [| a]; intros. {
  destruct l'; [ apply (permutation_refl Heqb) | easy ].
}
rewrite <- app_comm_cons; cbn in Hll' |-*.
remember (extract (eqb a) l') as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
remember (extract (eqb a) (l' ++ tl)) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1; clear Hlxl.
  specialize (H1 a).
  assert (H : a ∈ l' ++ tl). {
    subst l'.
    apply in_or_app; left.
    now apply in_or_app; right; left.
  }
  specialize (H1 H).
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb').
apply Heqb in H; subst x.
subst l'.
rewrite <- app_assoc in Hlb'; cbn in Hlb'.
apply app_eq_app in Hlb'.
destruct Hlb' as (l' & H1).
destruct H1 as [(H1, H2)| (H1, H2)]. {
  subst bef'.
  destruct l' as [| b]. {
    cbn in H2.
    injection H2; clear H2; intros H2; subst aft.
    rewrite app_assoc.
    rewrite app_nil_r in Hll'.
    now apply IHl.
  }
  cbn in H2.
  injection H2; clear H2; intros H2 H; subst b aft.
  specialize (Hbef a).
  assert (H : a ∈ bef ++ a :: l') by now apply in_or_app; right; left.
  specialize (Hbef H); clear H.
  now rewrite (equality_refl Heqb) in Hbef.
}
subst bef.
destruct l' as [| b]. {
  cbn in H2.
  injection H2; clear H2; intros; subst aft.
  rewrite app_nil_r, app_assoc.
  now apply IHl.
}
cbn in H2.
injection H2; clear H2; intros H2 H; subst b.
specialize (Hbef' a).
assert (H : a ∈ bef' ++ a :: l') by now apply in_or_app; right; left.
specialize (Hbef' H); clear H.
now rewrite (equality_refl Heqb) in Hbef'.
Qed.

Theorem permutation_app : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l m l' m',
  is_permutation eqb l l' = true
  → is_permutation eqb m m' = true
  → is_permutation eqb (l ++ m) (l' ++ m') = true.
Proof.
intros * Heqb * Hll' Hmm'.
apply (permutation_trans Heqb) with (lb := l ++ m'). {
  now apply permutation_app_head.
}
now apply permutation_app_tail.
Qed.

(* to be completed
Theorem permutation_cons_append : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l x, is_permutation eqb (x :: l) (l ++ [x]) = true.
Proof.
intros * Heqb *; cbn.
remember (extract (eqb x) (l ++ [x])) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef', y), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 x).
  assert (H : x ∈ l ++ [x]) by now apply in_or_app; right; left.
  specialize (H1 H); clear H.
  now rewrite equality_refl in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply app_eq_app in Hlb.
destruct Hlb as (l' & Hlb).
destruct Hlb as [(H1, H2)| (H1, H2)]. {
  subst l.
  apply (permutation_app_head Heqb).
  clear bef' Hbef.
  revert y aft H2.
  induction l' as [| x]; intros; cbn. {
    cbn in H2.
    now injection H2; clear H2; intros; subst aft.
  }
  cbn in H2.
  injection H2; clear H2; intros H2 H; subst y aft.
  remember (extract (eqb x) (l' ++ [x])) as lxl eqn:Hlxl.
  symmetry in Hlxl.
  destruct lxl as [((bef, y), aft)| ]. 2: {
    specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
    specialize (H1 x).
    assert (H : x ∈ l' ++ [x]) by now apply in_or_app; right; left.
    specialize (H1 H); clear H.
    now rewrite equality_refl in H1.
  }
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlb).
  apply Heqb in H; subst x.
  apply app_eq_app in Hlb.
  destruct Hlb as (l'' & Hlb).
  destruct Hlb as [(H1, H2)| (H1, H2)]. {
    subst l'.
    apply (permutation_app_head Heqb).
    destruct l'' as [| x]. {
      cbn in H2.
      now injection H2; clear H2; intros; subst aft.
    }
    injection H2; clear H2; intros H2 H; subst y aft.
...
  eapply IHl'.
    destruct l' as [| b]. {
      cbn in H2 |-*.
      now injection H2; clear H2; intros; subst aft.
    }
    cbn in H2.
    injection H2; clear H2; intros H2 H; subst b aft.
...
intros * Heqb *.
revert l.
induction l' as [| a]; intros; cbn. {
  rewrite app_nil_r.
  now apply permutation_refl.
}
rewrite List_app_cons.
replace (a :: l' ++ l) with ([a] ++ l' ++ l) by easy.
...

Theorem permutation_app_comm : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l l', is_permutation eqb (l ++ l') (l' ++ l) = true.
Proof.
intros * Heqb *.
revert l'.
induction l as [| a]; intros. {
  rewrite app_nil_r.
  now apply permutation_refl.
}
cbn.
remember (extract (eqb a) (l' ++ a :: l)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 a).
  assert (H : a ∈ l' ++ a :: l) by now apply in_or_app; right; left.
  specialize (H1 H); clear H.
  now rewrite equality_refl in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply app_eq_app in Hlb.
destruct Hlb as (l'' & Hlb).
destruct Hlb as [(H1, H2)| (H1, H2)]. {
  subst l'.
  destruct l'' as [| b]; cbn in H2. {
    rewrite app_nil_r.
    injection H2; clear H2; intros; subst aft.
    apply IHl.
  }
  injection H2; clear H2; intros H2 H; subst b aft.
  do 2 rewrite List_app_cons.
  do 4 rewrite app_assoc.
  do 2 rewrite <- app_assoc.
  eapply (permutation_trans Heqb); [ apply IHl | ].
  do 4 rewrite <- app_assoc.
  apply (permutation_app_head Heqb).
  do 2 rewrite app_assoc.
  apply (permutation_app_tail Heqb).
...
  apply permutation_cons_append.
...

Theorem permutation_cons_app : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l l1 l2 a,
  is_permutation eqb l (l1 ++ l2) = true
  → is_permutation eqb (a :: l) (l1 ++ a :: l2) = true.
Proof.
intros * Heqb * H12; cbn.
remember (extract (eqb a) (l1 ++ a :: l2)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  clear Hlxl.
  specialize (H1 a).
  rewrite (equality_refl Heqb) in H1.
  symmetry; apply H1.
  now apply in_or_app; right; left.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply app_eq_app in Hlb.
destruct Hlb as (l' & Hlb).
destruct Hlb as [(H1, H2)| (H1, H2)]. {
  subst l1.
  destruct l' as [| b]; cbn in H2. {
    rewrite app_nil_r in H12.
    now injection H2; clear H2; intros; subst aft.
  }
  injection H2; clear H2; intros H2 H; subst b aft.
  remember ((bef ++ a :: l') ++ l2) as lb eqn:Hlb.
  apply (permutation_trans Heqb) with (lb := lb); [ easy | subst lb ].
  rewrite <- app_assoc.
  apply (permutation_app_head Heqb).
  rewrite List_app_cons, app_assoc.
  apply (permutation_app_tail Heqb).
  replace (a :: l') with ([a] ++ l') by easy.
...
  apply permutation_app_comm.
}
...
remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb').
apply Heqb in H; subst x.
subst lb lc.
...
*)

Require Import Permutation.

Theorem Permutation_permutation : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  Permutation la lb
  ↔ is_permutation eqb la lb = true.
Proof.
intros * Heqb *.
split. {
  intros Hpab.
  revert lb Hpab.
  induction la as [| a]; intros; cbn. {
    now apply Permutation_nil in Hpab; subst lb.
  }
  remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft) | ]. {
    apply extract_Some_iff in Hlxl.
    destruct Hlxl as (Hbef & Hax & Hlb).
    apply Heqb in Hax; subst x.
    apply IHla.
    apply Permutation_cons_app_inv with (a := a).
    now rewrite <- Hlb.
  }
  specialize (Permutation_in a Hpab (or_introl eq_refl)) as H.
  specialize (proj1 (extract_None_iff _ _) Hlxl a H) as Hla; clear H.
  now rewrite (equality_refl Heqb) in Hla.
} {
  intros Hpab.
  revert lb Hpab.
  induction la as [| a]; intros; cbn in Hpab; [ now destruct lb | ].
  remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft) | ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & Hax & Hlb).
  apply Heqb in Hax; subst x.
  subst lb.
  apply Permutation_cons_app.
  now apply IHla.
}
Qed.
