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
  ∀ a, a ∈ la → a ∈ lb.
Proof.
intros * Heqb * Hab * Hla.
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
Qed.

(* to be completed
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
  specialize (H3 H); clear H.
  specialize (H1 _ H3) as H4.
  now rewrite (equality_refl Heqb) in H4.
}
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
