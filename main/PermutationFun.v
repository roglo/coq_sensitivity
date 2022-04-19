(* Testing if a list is a permutation of another one *)

(*
Set Nested Proofs Allowed.
Set Implicit Arguments.
*)

Require Import Utf8 Arith (*Permutation*).

Import List List.ListNotations.
(*
Require Import Misc.
*)

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

Theorem extract_Some : ∀ A (f : A → _) l a bef aft,
  extract f l = Some (bef, a, aft) → f a = true ∧ l = bef ++ a :: aft.
Proof.
intros * He.
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
split; [ easy | ].
now cbn; f_equal.
Qed.
