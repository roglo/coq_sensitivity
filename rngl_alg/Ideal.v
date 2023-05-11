(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.

Require Import Utf8.

Require Import Main.RingLike.

Class ideal A {ro : ring_like_op A} := mk_I
  { i_mem : A → bool;
    i_prop_add :
      ∀ a b, i_mem a = true → i_mem b = true → i_mem (a + b)%L = true;
    i_prop_mul_l : ∀ a b, i_mem b = true → i_mem (a * b)%L = true;
    i_prop_mul_r : ∀ a b, i_mem a = true → i_mem (a * b)%L = true }.

Arguments ideal A%type {ro}.
Arguments mk_I A%type {ro}.
Arguments i_mem {A ro} ideal.


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
