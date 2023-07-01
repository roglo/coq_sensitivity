(* Attempt to implement rationals with the normal rationals of
   coq (library QArith) together with a field saying that the
   numerator and the denominator are coprimes. This allows to
   use normal equality instead of ==. Therefore rewrite is
   possible. *)

Set Nested Proofs Allowed.
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

Theorem Pos_gcd_comm : ∀ a b, Pos.gcd a b = Pos.gcd b a.
Proof.
intros.
apply Pos2Z.inj.
do 2 rewrite Pos2Z.inj_gcd.
apply Z.gcd_comm.
Qed.

Theorem Pos_gcd_le_l : ∀ a b, (Pos.gcd a b <= a)%positive.
Proof.
intros.
specialize (Pos.gcd_divide_l a b) as H1.
apply Z.divide_Zpos in H1.
apply Znumtheory.Zdivide_mod in H1.
apply Zdiv.Zmod_divides in H1; [ | easy ].
destruct H1 as (c & Hc).
destruct c as [| c| c]; [ easy | | easy ].
cbn in Hc.
apply Pos2Z.inj in Hc.
rewrite Hc at 2.
remember (_ * _)%positive as x.
rewrite <- (Pos.mul_1_r (Pos.gcd _ _)); subst x.
apply Pos.mul_le_mono_l.
apply Pos.le_1_l.
Qed.

Theorem Pos_gcd_le_r : ∀ a b, (Pos.gcd a b <= b)%positive.
Proof.
intros.
rewrite Pos_gcd_comm.
apply Pos_gcd_le_l.
Qed.

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
  remember (Z.pos qn / _)%Z as z eqn:Hz; symmetry in Hz.
  destruct z as [| z| z]. {
    apply Z.div_small_iff in Hz; [ | easy ].
    destruct Hz as [(Hz1, Hz2)| Hz]; [ | easy ].
    exfalso.
    apply Z.nle_gt in Hz2; apply Hz2; clear Hz2.
    apply Pos2Z.pos_le_pos.
    apply Pos_gcd_le_l.
  } {
    apply Pos2Z.inj; cbn.
    rewrite Pos2Z.inj_gcd.
    rewrite <- Hz.
    rewrite Z2Pos.id. 2: {
      apply Z.div_str_pos.
      split; [ easy | ].
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_r.
    }
    now apply Z.gcd_div_gcd.
  } {
Search (Z.pos _ / Z.pos _)%Z.
...
Print Module Z2Pos.
...
apply Z2Pos.inj_iff in Hz.
cbn in Hz.
...
Search (Pos.gcd _ _ = Pos.gcd _ _).
Search (Z.gcd _ _ = Z.gcd _ _).
rewrite Pos.gcd_com.
...
Search Pos.gcd.
  ============================
  (Pos.gcd qn (Qden q) <= Qden q)%positive
...
      rewrite Pos2Z.inj_gcd.
...
unfold Z.gcd.
Print QDen.
Search (Z.pos _ <= Z.pos _)%Z.
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
