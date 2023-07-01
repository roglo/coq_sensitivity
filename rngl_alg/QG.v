(* Attempt to implement rationals with the normal rationals of
   coq (library QArith) together with a field saying that the
   numerator and the denominator are coprimes. This allows to
   use normal equality instead of ==. Therefore rewrite is
   possible. *)

Set Implicit Arguments.
Require Import Utf8.

Require Import QArith.

Definition Z_pos_gcd z p :=
  match z with
  | Z0 => p
  | Zpos zp => Pos.gcd zp p
  | Zneg zp => Pos.gcd zp p
  end.

Record QG := mk_qg
  {qg_q : Q; qg_gcd : Z_pos_gcd (Qnum qg_q) (Qden qg_q) = 1%positive}.

Theorem eq_QG_eq : ∀ q1 q2, q1 = q2 ↔ qg_q q1 = qg_q q2.
Proof.
intros.
split; intros Hq; [ now subst q2 | ].
destruct q1 as (q1, Hq1).
destruct q2 as (q2, Hq2).
cbn in Hq; subst q2.
f_equal.
apply (Eqdep_dec.UIP_dec Pos.eq_dec).
Qed.

Search (positive → positive → positive).
Print positive.
Search (Z → positive).
Print Z.to_pos.

Theorem QG_of_Q_prop : ∀ q,
  let g := Z_pos_gcd (Qnum q) (Qden q) in
  Z_pos_gcd (Qnum (Qnum q / Z.pos g # Z.to_pos (QDen q / Z.pos g)))
    (Qden (Qnum q / Z.pos g # Z.to_pos (QDen q / Z.pos g))) = 1%positive.
Proof.
intros; cbn.
subst g; cbn.
progress unfold Z_pos_gcd.
remember (Qnum q) as qn eqn:Hqn; symmetry in Hqn.
destruct qn as [| qn| qn]. {
  now cbn; rewrite Z.div_same.
} {
(*
  rewrite Pos2Z.inj_gcd.
*)
  remember (Z.pos qn / _)%Z as z eqn:Hz; symmetry in Hz.
  destruct z as [| z| z]. {
    apply Z.div_small_iff in Hz; [ | easy ].
    destruct Hz as [(Hz1, Hz2)| Hz]; [ | easy ].
    exfalso.
    apply Z.nle_gt in Hz2; apply Hz2; clear Hz2.
    apply Pos2Z.pos_le_pos.
    specialize Pos.gcd_divide_l as H1.
    specialize (H1 qn (Qden q)).
    apply Z.divide_Zpos in H1.
    apply Znumtheory.Zdivide_mod in H1.
    apply Zdiv.Zmod_divides in H1; [ | easy ].
    destruct H1 as (c & Hc).
    destruct c as [| c| c]; [ easy | | easy ].
    cbn in Hc.
    apply Pos2Z.inj in Hc.
    rewrite Hc at 2.
    specialize (Pos.mul_le_mono_l (Pos.gcd qn (Qden q)) 1 c) as H1.
    rewrite Pos.mul_1_r in H1.
    apply H1.
    apply Pos.le_1_l.
  } {
    apply Pos2Z.inj; cbn.
(*
...
    cbn in Hz.
...
*)
    rewrite Pos2Z.inj_gcd.
    rewrite Z2Pos.id. 2: {
      apply Z.div_str_pos.
      split; [ easy | ].
      rewrite Pos2Z.inj_gcd.
...
Search (Z.gcd _ _ <= _)%Z.
Search (Z.gcd (_ / _)).
Z.gcd_div_factor:
  ∀ a b c : Z,
    (0 < c)%Z
    → (c | a)%Z → (c | b)%Z → Z.gcd (a / c) (b / c) = (Z.gcd a b / c)%Z
Z.gcd_div_gcd:
  ∀ a b g : Z, g ≠ 0%Z → g = Z.gcd a b → Z.gcd (a / g) (b / g) = 1%Z
...
    apply Z.bezout_1_gcd.
    unfold Z.Bezout.
...
Search (Z.gcd _ _ = 1)%Z.
Search (Z.pos _ = Z.pos _).
Search Pos.gcd.
Search (_ = 1)%positive.
Search (_ * Pos.gcd _ _)%positive.
Pos.mul_eq_1_r:
  ∀ p q : positive, (p * q)%positive = 1%positive → q = 1%positive
Pos.mul_eq_1_l:
  ∀ p q : positive, (p * q)%positive = 1%positive → p = 1%positive
...
Require Import ZArith.
Search (_ / _)%Z.
Search (_ / Z.gcd _ _)%Z.
Search (_ / _ = _ → _)%Z.
Search (_ = _ / _ → _)%Z.
Search (_ / _ = _ ↔ _)%Z.
Search (_ = _ / _ ↔ _)%Z.
Search (_ ↔ _ / _ = _)%Z.
Search (_ ↔ _ = _ / _)%Z.
...
Search (_ mod _ = 0)%Z.
Zdiv.Z_div_exact_full_2:
  ∀ a b : Z, b ≠ 0%Z → (a mod b)%Z = 0%Z → a = (b * (a / b))%Z
Zdiv.Zmod_divides:
  ∀ a b : Z, b ≠ 0%Z → (a mod b)%Z = 0%Z ↔ (∃ c : Z, a = (b * c)%Z)
Z.mod_opp_r_nz:
Search ((_ | _)%positive ↔ _).
Search (_ ↔ (_ | _)%positive).
Search ((_ | _)%positive -> _).
Search ((_ | _)%Z ↔ _).
Search (_ ↔ (_ | _)%Z).
Search ((_ | _)%Z → _).
...
Search (Pos.gcd _ _ <= _)%positive.
Search (Pos.gcd).
Search Z.gcd.
Search (Z.gcd _ _ <= _)%Z.
Search (_ < Z.gcd _ _)%Z.
...
  rewrite <- Hqn.
Search (_ / Z.gcd _ _)%Z.
...

Definition QG_of_Q (q : Q) :=
  let g := Z_pos_gcd (Qnum q) (Qden q) in
  mk_qg (Qmake (Qnum q / Zpos g) (Z.to_pos (Zpos (Qden q) / Zpos g)%Z))
    (QG_of_Q_prop q).

...
