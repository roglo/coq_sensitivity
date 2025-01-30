(* attempt to implement projective geometry *)

Require Import Utf8.

Require Import Main.RingLike.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
(*
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
*)

Definition proj_point_prop x y := (x² + y² =? 1)%L = true.

(* proj_point is a triplet (ppx, ppy, pp_prop)
   - either a point (pp_x, pp_y) when pp_prop is None
   - or a point at the infinite whose direction is from the
     segment (0, 0) to (pp_x, pp_y) and, in that case, the 3rd
     component is Some (the proof that (pp_x, pp_y) is in the unit
     circle) *)

Record proj_point := mk_pp
  { pp_x : T;
    pp_y : T;
    pp_prop : option (proj_point_prop pp_x pp_y) }.
