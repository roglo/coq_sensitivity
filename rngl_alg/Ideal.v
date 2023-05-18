(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.

Require Import Utf8.

Require Import Main.RingLike.

Class ideal_prop {A} {ro : ring_like_op A} (P : A → bool) := mk_I
  { i_zero_in : P rngl_zero = true;
    i_one_in : P rngl_one = true;
    i_prop_add :
      ∀ a b, P a = true → P b = true → P (a + b)%L = true;
    i_prop_mul_l : ∀ a b, P b = true → P (a * b)%L = true;
    i_prop_mul_r : ∀ a b, P a = true → P (a * b)%L = true }.

Record ideal_elem {A} (P : A → bool) := mk_ie
  { ie_value : A;
    ie_prop : P ie_value = true }.

(* 0 and 1 *)

Theorem I_zero_prop :
  ∀ {A} {ro : ring_like_op A} {P : A → bool} {ip : ideal_prop P},
  P 0%L = true.
Proof. now intros; destruct ip. Qed.

Theorem I_one_prop :
  ∀ {A} {ro : ring_like_op A} {P : A → bool} {ip : ideal_prop P},
  P 1%L = true.
Proof. now intros; destruct ip. Qed.

Definition I_zero {A} {ro : ring_like_op A} {P : A → bool} {ip : ideal_prop P}
  : ideal_elem P :=
  mk_ie A P 0%L I_zero_prop.

Definition I_one {A} {ro : ring_like_op A} {P : A → bool} {ip : ideal_prop P}
  : ideal_elem P :=
  mk_ie A P 1%L I_one_prop.

(* addition *)

Definition I_add_prop {A} {ro : ring_like_op A} {P} {ip : ideal_prop P} a b
  : P (ie_value P a + ie_value P b)%L = true :=
  i_prop_add (ie_value P a) (ie_value P b) (ie_prop P a) (ie_prop P b).

Definition I_add {A} {ro : ring_like_op A} {P : A → bool} {ip : ideal_prop P}
    (a b : ideal_elem P)
  : ideal_elem P :=
  mk_ie A P (ie_value P a + ie_value P b)%L (I_add_prop a b).

(* multiplication *)

Definition I_mul_prop {A} {ro : ring_like_op A} {P} {ip : ideal_prop P} a b
  : P (ie_value P a * ie_value P b)%L = true :=
  i_prop_mul_l (ie_value P a) (ie_value P b) (ie_prop P b).

Definition I_mul {A} {ro : ring_like_op A} {P : A → bool} {ip : ideal_prop P}
    (a b : ideal_elem P)
  : ideal_elem P :=
  mk_ie A P (ie_value P a * ie_value P b)%L (I_mul_prop a b).

(* ideal ring like op *)

Definition I_ring_like_op {A} {ro : ring_like_op A} {P : A → bool}
    (ip : ideal_prop P) : ring_like_op (ideal_elem P) :=
  {| rngl_zero := I_zero;
     rngl_one := I_one;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_opp_or_subt := None;
     rngl_opt_inv_or_quot := None;
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

...

Definition I_zero {A} {ro : ring_like_op A} (i_mem : A → bool) :
  ideal_elem i_mem.

...

Definition I_zero {A} {ro : ring_like_op A} {P} (Ia : ideal P) := rngl_zero.
Definition I_one {A} {ro : ring_like_op A} {P} (Ia : ideal P) := rngl_one.

Theorem I_zero_in :
  ∀ {A} {ro : ring_like_op A} P (Ia : ideal P),
  P (I_zero Ia) = true.
Proof.
intros.
unfold I_zero; cbn.
now destruct Ia.
Qed.

Theorem I_one_in :
  ∀ {A} {ro : ring_like_op A} P (Ia : ideal P),
  P (I_one Ia) = true.
Proof.
intros.
unfold I_one; cbn.
now destruct Ia.
Qed.

Print I_zero.

...

Definition I_ring_like_op {A} {ro : ring_like_op A} {P : A → bool}
    (Ia : ideal P) : ring_like_op A :=
  {| rngl_zero := I_zero Ia;
     rngl_one := I_one Ia;
     rngl_add := rngl_add;
     rngl_mul := rngl_mul;
     rngl_opt_opp_or_subt := rngl_opt_opp_or_subt;
     rngl_opt_inv_or_quot := rngl_opt_inv_or_quot;
     rngl_opt_eqb := rngl_opt_eqb;
     rngl_opt_le := rngl_opt_le |}.
...

Definition I_ring_like_op A (ro : ring_like_op A) (rp : ring_like_prop A)
    (Hos : rngl_has_opp_or_subt = true) (Heb : rngl_has_eqb = true) :
      ring_like_op (ideal A) :=
  {| rngl_zero := I_zero;
     rngl_one := I_one |}.
...
  {| rngl_zero := I_zero Hos Heb;
     rngl_one := I_one;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_opp_or_subt := None;
     rngl_opt_inv_or_quot := None;
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.
...

Theorem I_zero_prop_add A {ro : ring_like_op A} {rp : ring_like_prop A}
    (Heb : rngl_has_eqb = true) :
  ∀ a b : A, (a =? 0)%L = true → (b =? 0)%L = true → (a + b =? 0)%L = true.
Proof.
intros * Ha Hb.
apply (rngl_eqb_eq Heb) in Ha.
apply (rngl_eqb_eq Heb) in Hb.
apply (rngl_eqb_eq Heb).
subst a b.
apply rngl_add_0_l.
Qed.

Theorem I_zero_prop_mul_l A {ro : ring_like_op A} {rp : ring_like_prop A}
   (Hos : rngl_has_opp_or_subt = true) (Heb : rngl_has_eqb = true) :
  ∀ (a b : A),
  (b =? 0)%L = true
  → ((a * b) =? 0)%L = true.
Proof.
intros * Hb.
apply (rngl_eqb_eq Heb) in Hb.
apply (rngl_eqb_eq Heb).
subst b.
apply (rngl_mul_0_r Hos).
Qed.

Theorem I_zero_prop_mul_r A {ro : ring_like_op A} {rp : ring_like_prop A}
   (Hos : rngl_has_opp_or_subt = true) (Heb : rngl_has_eqb = true) :
  ∀ (a b : A),
  (a =? 0)%L = true
  → ((a * b) =? 0)%L = true.
Proof.
intros * Ha.
apply (rngl_eqb_eq Heb) in Ha.
apply (rngl_eqb_eq Heb).
subst a.
apply (rngl_mul_0_l Hos).
Qed.

Arguments I_zero_prop_add A%type {ro rp} Heb (a b)%L.
Arguments I_zero_prop_mul_l A%type {ro rp} Hos Heb (a b)%L.
Arguments I_zero_prop_mul_r A%type {ro rp} Hos Heb (a b)%L.

Definition I_zero A {ro : ring_like_op A} {rp : ring_like_prop A}
    (Hos : rngl_has_opp_or_subt = true) (Heb : rngl_has_eqb = true) :
      ideal A :=
  mk_I A (λ a, (a =? 0)%L)
    (I_zero_prop_add A Heb)
    (I_zero_prop_mul_l A Hos Heb)
    (I_zero_prop_mul_r A Hos Heb).

Definition I_one A {ro : ring_like_op A} {rp : ring_like_prop A} :
    ideal A :=
  mk_I A (λ a, true) (λ _ _ _ _, eq_refl) (λ _ _ _, eq_refl)
    (λ _ _ _, eq_refl).

(**)

...

Definition I_add {A} {ro : ring_like_op A} (Ia : ideal A) (a b : Ia) :=
  (a + b)%L.

...

Definition I_add {A} {ro : ring_like_op A} (Ia Ib : ideal A) : ideal A :=
  mk_I A (λ c : A, (i_mem Ia c || i_mem Ib c)%bool)
    (I_add_prop_add Ia Ib) (I_add_prop_mul_l Ia Ib) (I_add_prop_mul_r Ia Ib).

...

Theorem I_add_prop_add :
  ∀ [A] {ro : ring_like_op A} (Ia Ib : ideal A),
  ∀ (a b : A),
  (i_mem Ia a || i_mem Ib a)%bool = true
  → (i_mem Ia b || i_mem Ib b)%bool = true
  → (i_mem Ia (a + b)%L || i_mem Ib (a + b)%L)%bool = true.
Proof.
intros * Ha Hb.
apply Bool.orb_true_iff in Ha, Hb.
apply Bool.orb_true_iff.
destruct Ha as [Ha| Ha]. {
  destruct Hb as [Hb| Hb]. {
...
    apply i_prop_add.
...
now destruct Hab as [Hab| Hab]; [ left | right ]; apply i_prop_mul_l.
...

Theorem I_add_prop_mul_l :
  ∀ [A] {ro : ring_like_op A} (Ia Ib : ideal A),
  ∀ a b : A,
  (i_mem Ia b || i_mem Ib b)%bool = true
  → (i_mem Ia (a * b)%L || i_mem Ib (a * b)%L)%bool = true.
Proof.
intros * Hab.
apply Bool.orb_true_iff in Hab.
apply Bool.orb_true_iff.
now destruct Hab as [Hab| Hab]; [ left | right ]; apply i_prop_mul_l.
Qed.

Theorem I_add_prop_mul_r :
  ∀ [A] {ro : ring_like_op A} (Ia Ib : ideal A),
  ∀ a b : A,
  (i_mem Ia a || i_mem Ib a)%bool = true
  → (i_mem Ia (a * b)%L || i_mem Ib (a * b)%L)%bool = true.
Proof.
intros * Hab.
apply Bool.orb_true_iff in Hab.
apply Bool.orb_true_iff.
now destruct Hab as [Hab| Hab]; [ left | right ]; apply i_prop_mul_r.
Qed.

Theorem I_mul_prop_l :
  ∀ [A] {ro : ring_like_op A} (Ia Ib : ideal A),
  ∀ a b : A,
  (i_mem Ia b && i_mem Ib b)%bool = true
  → (i_mem Ia (a * b)%L && i_mem Ib (a * b)%L)%bool = true.
Proof.
intros * Hab.
apply Bool.andb_true_iff in Hab.
apply Bool.andb_true_iff.
destruct Hab as (Ha, Hb).
now split; apply i_prop_mul_l.
Qed.

Theorem I_mul_prop_r :
  ∀ A {ro : ring_like_op A} (Ia Ib : ideal A),
  ∀ a b : A,
  (i_mem Ia a && i_mem Ib a)%bool = true
  → (i_mem Ia (a * b)%L && i_mem Ib (a * b)%L)%bool = true.
Proof.
intros * Hab.
apply Bool.andb_true_iff in Hab.
apply Bool.andb_true_iff.
destruct Hab as (Ha, Hb).
now split; apply i_prop_mul_r.
Qed.

...

Definition I_add {A} {ro : ring_like_op A} (Ia Ib : ideal A) : ideal A :=
  mk_I A (λ c : A, (i_mem Ia c || i_mem Ib c)%bool)
    (I_add_prop_add Ia Ib) (I_add_prop_mul_l Ia Ib) (I_add_prop_mul_r Ia Ib).

Definition I_mul {A} {ro : ring_like_op A} (Ia Ib : ideal A) : ideal A :=
  mk_I A (λ c : A, (i_mem Ia c && i_mem Ib c)%bool)
42
    (I_mul_prop_l Ia Ib) (I_mul_prop_r Ia Ib).

...

Definition I_ring_like_op A (ro : ring_like_op A) (rp : ring_like_prop A)
    (Hos : rngl_has_opp_or_subt = true) (Heb : rngl_has_eqb = true) :
      ring_like_op (ideal A) :=
  {| rngl_zero := I_zero Hos Heb;
     rngl_one := I_one;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_opp_or_subt := None;
     rngl_opt_inv_or_quot := None;
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

Require Import ZArith.
Require Import Zrl.
Definition ZI := I_ring_like_op Z_ring_like_prop eq_refl eq_refl.

Compute (i_mem (@rngl_zero _ ZI)).
Compute (i_mem (@rngl_one _ ZI)).
Compute (
  let ro := ZI in
  i_mem (@rngl_one _ ZI + @rngl_one _ ZI)%L).

(* ouais, chais pas *)
