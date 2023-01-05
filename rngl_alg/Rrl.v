Set Nested Proofs Allowed.
Require Import Utf8 Reals.
Require Import Main.RingLike.

Canonical Structure reals_ring_like_op : ring_like_op R :=
  {| rngl_zero := R0;
     rngl_one := R1;
     rngl_add := Rplus;
     rngl_mul := Rmult;
     rngl_opt_opp_or_sous := Some (inl Ropp);
     rngl_opt_inv_or_quot := Some (inl Rinv);
     rngl_opt_eqb := None;
     rngl_opt_le := Some Rle |}.

Theorem Rplus_assoc' : ∀ a b c : R, (a + (b + c))%R = (a + b + c)%R.
Proof. intros; now rewrite Rplus_assoc. Qed.

Theorem Rmult_assoc' : ∀ a b c : R, (a * (b * c))%R = (a * b * c)%R.
Proof. intros; now rewrite Rmult_assoc. Qed.

Theorem Rcharacteristic_prop :
  let ror := reals_ring_like_op in
  ∀ i : nat, rngl_of_nat (S i) ≠ 0%L.
Proof.
intros.
assert (H : ∀ n, rngl_of_nat n = INR n). {
  intros.
  induction n; [ easy | cbn ].
  destruct n; [ apply Rplus_0_r | ].
  rewrite IHn.
  apply Rplus_comm.
}
rewrite H.
now apply not_0_INR.
Qed.

Theorem Ropt_mul_le_compat_nonneg :
  let ror := reals_ring_like_op in
  ∀ a b c d : R, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros * Hac Hbd.
now apply Rmult_le_compat.
Qed.

Theorem Ropt_mul_le_compat_nonpos :
  let ror := reals_ring_like_op in
  ∀ a b c d : R, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros * Hca Hdb; cbn.
apply Rle_trans with (r2 := (a * d)%R). {
  now apply Rmult_le_compat_neg_l.
}
rewrite (Rmult_comm a), (Rmult_comm c).
apply Rmult_le_compat_neg_l; [ | easy ].
now apply Rle_trans with (r2 := b).
Qed.

Theorem Ropt_not_le :
  let ror := reals_ring_like_op in
  ∀ a b : R, ¬ (a ≤ b)%L → a = b ∨ (b ≤ a)%L.
Proof.
intros * Hab.
cbn in Hab |-*.
apply Rnot_le_lt in Hab.
specialize (Rle_or_lt b a) as H1.
destruct H1 as [| Hba]; [ now right | left ].
now apply Rlt_asym in Hba.
Qed.

Canonical Structure reals_ring_like_prop : ring_like_prop R :=
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := false;
     rngl_is_integral := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Rplus_comm;
     rngl_add_assoc := Rplus_assoc';
     rngl_add_0_l := Rplus_0_l;
     rngl_mul_assoc := Rmult_assoc';
     rngl_mul_1_l := Rmult_1_l;
     rngl_mul_add_distr_l := Rmult_plus_distr_l;
     rngl_opt_mul_comm := Rmult_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := Rplus_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_sub_sub_add := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := Rinv_l;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eqb_eq := NA;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := Rmult_integral;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := Rcharacteristic_prop;
     rngl_opt_le_refl := Rle_refl;
     rngl_opt_le_antisymm := Rle_antisym;
     rngl_opt_le_trans := Rle_trans;
     rngl_opt_add_le_compat := Rplus_le_compat;
     rngl_opt_mul_le_compat_nonneg := Ropt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := Ropt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := Ropt_not_le |}.

(* experiment, to make, perhaps, an implementation of algebraic numbers
   where a first step is to generate all monic polynomials with values
   in ℕ; since monic, it is not required to append the coefficient 1 to
   the list representing the polynomial, so we have to generate all
   lists of nat *)

Require Import Arith.
Import List List.ListNotations.
Require Import Main.Misc Main.IterAdd Main.NatRingLike.

Fixpoint llnls k s i :=
  match k with
  | 0 => [[]]
  | S k' =>
      if k =? s then []
      else
        match s with
        | 0 => []
        | S s' => llnls k' s' (S i)
        end ++
        map (λ l, i :: l) (llnls k' s 0)
   end.

(* list of lists of nat of length n whose sum is s *)
Definition list_list_nat_len_sum (n s : nat) :=
  llnls (n + s) s 0.

(* list of lists of nat of step k *)
Definition list_list_step k :=
  App (s = 0, k), list_list_nat_len_sum (k - s) s.

(* list of lists of nat up to step k *)
Definition list_list_up_to_step k :=
  App (k1 = 0, k), list_list_step k1.

(*
Compute (map (λ i, (i, Nat.log2 i)) (seq 1 32)).

Compute (map (λ l, 1 :: rev l) (list_list_up_to_step 5)).
...
     = [[1]; [1; 0]; [1; 0; 0]; [1; 1]; [1; 0; 0; 0]; [1; 0; 1]; [1; 1; 0]; [1; 2]; [1; 0; 0; 0; 0]; 
       [1; 0; 0; 1]; [1; 0; 1; 0]; [1; 1; 0; 0]; [1; 0; 2]; [1; 1; 1]; [1; 2; 0]; [1; 3]; 
       [1; 0; 0; 0; 0; 0]; [1; 0; 0; 0; 1]; [1; 0; 0; 1; 0]; [1; 0; 1; 0; 0]; [1; 1; 0; 0; 0]; 
       [1; 0; 0; 2]; [1; 0; 1; 1]; [1; 1; 0; 1]; [1; 0; 2; 0]; [1; 1; 1; 0]; [1; 2; 0; 0]; 
       [1; 0; 3]; [1; 1; 2]; [1; 2; 1]; [1; 3; 0]; [1; 4]]
     : list (list nat)
...
(* polynomials
   1,
   x,
   x2, x+1,
   x3, x2+1, x2+x, x+2,
   x4, x3+1, x3+x, x3+x2, x2+2, x2+x+1, x2+2x, x+3,
   x5, x4+1, x4+x, x4+x2, x4+x3, x3+2, x3+x+1, x3+x2+1, x3+2x, x3+x2+x,
     x3+2x2, x2+3, x2+x+2, x2+2x+1, x2+3x, x+4
   x6, ...
...
       [1; 0; 0; 0; 0; 1]; [1; 0; 0; 0; 1; 0];
       [1; 0; 0; 1; 0; 0]; [1; 0; 1; 0; 0; 0]; [1; 1; 0; 0; 0; 0];
       [1; 0; 0; 0; 2]; [1; 0; 0; 1; 1]; [1; 0; 1; 0; 1]; 
       [1; 1; 0; 0; 1]; [1; 0; 0; 2; 0]; [1; 0; 1; 1; 0]; 
       [1; 1; 0; 1; 0]; [1; 0; 2; 0; 0]; [1; 1; 1; 0; 0]; 
       [1; 2; 0; 0; 0]; [1; 0; 0; 3]; [1; 0; 1; 2]; 
       [1; 1; 0; 2]; [1; 0; 2; 1]; [1; 1; 1; 1]; [1; 2; 0; 1]; 
       [1; 0; 3; 0]; [1; 1; 2; 0]; [1; 2; 1; 0]; [1; 3; 0; 0]; 
       [1; 0; 4]; [1; 1; 3]; [1; 2; 2]; [1; 3; 1]; [1; 4; 0]; 
...
   1,
   x,
   x², x+1,
   x³, x²+x, x²+1, x+2,
   x⁴, x³+x², x³+x, x³+1, x²+2x, x²+x+1, x²+2, x+3,
   x⁵, x⁴+x³, x⁴+x² x⁴+x, x⁴+1, x³+2x², x³+x²+x,
     x³+2x, x³+x²+1, x³+x+1, x³+2, x²+3x, x²+2x+1, x²+x+2, x²+3, x+4,
   x⁶, x⁵+x⁴, x⁵+x³, x⁵+x², x⁵+x, x⁵+1, x⁴+2x³ x⁴+x³+x², x⁴+2x,
     x⁴+x³+x, x⁴+x²+x, x⁴+2x, x⁴+x³+1, x⁴+x²+1, x⁴+x+1, x⁴+2, x³+3x²,
     x³+2x²+x, x³+x²+2x, x³+3x, x³+2x²+1, x³+x²+x+1, x³+2x+1, x³+x²+2,
     x³+x+2, x³+3, x²+4x, x²+3x+1, x²+2x+2, x²+x+3, x²+4, x+5, ...
*)
...
Compute (list_list_up_to_step 0).
Compute (list_list_up_to_step 1).
Compute (list_list_up_to_step 2).
Compute (list_list_up_to_step 3).
Compute (list_list_up_to_step 4).
Compute (list_list_up_to_step 5).
Require Import Main.Polynomial.
Theorem glop : ∀ l, has_polyn_prop (l ++ [1]) = true.
Proof.
intros.
apply Bool.orb_true_iff; right.
now rewrite last_last.
Qed.
Compute (map (λ l, mk_polyn (l ++ [1]) (glop l)) (list_list_up_to_step 5)).
*)
(*
...
Compute (list_list_step 0).
Compute (list_list_step 1).
Compute (list_list_step 2).
Compute (list_list_step 3).
Compute (list_list_step 4).
Compute (list_list_step 5).
...
Compute (list_list_nat_len_sum 0 0).
Compute (list_list_nat_len_sum 0 1).
Compute (list_list_nat_len_sum 1 0).
Compute (list_list_nat_len_sum 1 1).
Compute (list_list_nat_len_sum 1 2).
Compute (list_list_nat_len_sum 1 3).
Compute (list_list_nat_len_sum 1 4).
Compute (list_list_nat_len_sum 2 0).
Compute (list_list_nat_len_sum 2 1).
Compute (list_list_nat_len_sum 2 2).
Compute (list_list_nat_len_sum 2 3).
Compute (list_list_nat_len_sum 2 4).
Compute (list_list_nat_len_sum 3 0).
Compute (list_list_nat_len_sum 3 1).
Compute (list_list_nat_len_sum 3 2).
Compute (list_list_nat_len_sum 3 3).
Compute (list_list_nat_len_sum 3 4).
Compute (list_list_nat_len_sum 3 5).
Compute (list_list_nat_len_sum 3 10).
...
*)

(* I don't know how to call that; I temporarily call it "step". It is
   a number associated with a list; the next list must have a "step"
   whose value is nat successor (next of a step 42 must have a step 43 *)
Definition step l := length l + ∑ (i = 1, length l), l.(i).

Definition generate_next_step (n : nat) := [[n]; repeat 0 (S n)].

(*
Compute (generate_next_step 0).
Compute (generate_next_step 1).
Compute (generate_next_step 2).
*)

(* I need a function where, when n = 4, should result
     [[0;0;0;0]; [0;0;1]; [0;1;0]; [1;0;0]; [0;2]; [2;0]; [3]
   i.e. 2^n lists: all lists whose "step" is 4
     Doing that, we can generate all lists of nat;
   but, perhaps with an inductive type, it could be the same?
   but not computable *)

Definition glop l :=
  (0 :: l) :: (l ++ [0]) ::
  map (λ i, replace_at (i - 1) l (S (l.(i)))) (seq 1 (length l)).

Require Import Main.SortingFun.

Fixpoint list_nat_le la lb :=
  match (la, lb) with
  | ([], _) => true
  | (_, []) => false
  | (a :: la', b :: lb') =>
      match a ?= b with
      | Eq => list_nat_le la' lb'
      | Lt => true
      | Gt => false
      end
  end.

Fixpoint list_list_nat_leb lla llb :=
  match (lla, llb) with
  | ([], _) => true
  | (_, []) => false
  | (la :: lla', lb :: llb') =>
      if list_nat_le la lb then
        if list_nat_le lb la then list_list_nat_leb lla' llb'
        else true
      else false
  end.

Fixpoint uniq {A} (eqb : A → A → bool) (l : list A) :=
  match l with
  | [] => l
  | a :: l' =>
      match l' with
      | [] => [a]
      | b :: l'' => if eqb a b then uniq eqb l' else a :: uniq eqb l'
      end
  end.

(*
Compute (glop [0;0;0;0;0]).
Compute (isort list_nat_le (glop [0;0;0;0;0])).
Compute (glop [0;0;0;1]).
Compute (glop [0;2]).
Compute (isort list_nat_le (glop [0;2])).
*)

Definition list_nat_le' (la lb : list nat) :=
  if lt_dec (length lb) (length la) then true
  else false.

Definition pouet (ll : list (list nat)) :=
  isort list_nat_le'
    (uniq (list_eqv Nat.eqb) (isort list_nat_le (concat (map glop ll)))).

Fixpoint tagada n :=
  match n with
  | 0 => [[]]
  | S n' => pouet (tagada n')
  end.

Definition gloup ll :=
  (0 :: hd [] ll) ::
  concat
    (map
       (λ l, map (λ i, replace_at (i - 1) l (S (l.(i)))) (seq 1 (length l)))
       ll).

(*
Fixpoint toto len d :=
  match d with
(**)
  | 0 => [[len]]
(*
  | 0 => [repeat 0 len]
*)
  | S d' =>
      match d' with
      | 0 =>
          map (λ i, replace_at (i - 1) (repeat 0 len) 1)
            (seq 0 len) ++
          toto len d'
      | S d'' => [42] :: toto len d'
      end
  end.

Compute (toto 3 3).
...
(* ouais, c'est nul tout ça *)
*)

(*
Compute (let ll := [[]] in (pouet ll, gloup ll)).
Compute (let ll := [[0]] in (pouet ll, gloup ll)).
Compute (let ll := [[0; 0]; [1]] in (pouet ll, gloup ll)).
Compute (let ll := [[0; 0; 0]; [0; 1]; [1; 0]; [2]] in (pouet ll, gloup ll)).
Compute (let ll := [[0; 0; 0; 0]; [1; 0; 0]; [0; 1; 0]; [0; 0; 1]; [2; 0]; [1; 1]; [0; 2]; [3]] in (pouet ll, gloup ll)).
...
Compute (tagada 0).
Compute (tagada 1).
Compute (tagada 2).
Compute (tagada 3).
Compute (tagada 4).
Compute (tagada 5).

Compute (pouet [[]]).
Compute (pouet [[0]]).
Compute (pouet [[0; 0]; [1]]).
Compute (pouet [[0; 0; 0]; [0; 1]; [1; 0]; [2]]).
Compute
  (pouet
     [[0; 0; 0; 0]; [1; 0; 0]; [0; 1; 0]; [0; 0; 1];
      [2; 0]; [1; 1]; [0; 2]; [3]]).
Compute
  (pouet
     [[0; 0; 0; 0; 0];
      [1; 0; 0; 0]; [0; 1; 0; 0]; [0; 0; 1; 0]; [0; 0; 0; 1];
      [2; 0; 0]; [1; 1; 0]; [1; 0; 1]; [0; 2; 0]; [0; 1; 1]; [0; 0; 2];
      [3; 0]; [2; 1]; [1; 2]; [0; 3]; [4]]).
*)
