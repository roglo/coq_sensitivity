(* $Id: permut.ml,v 1.7 2008/10/30 18:59:48 deraugla Exp $ *)

(* The function "next" returns the next permutation of a list.
   Returns [] if no more permutation. *)

(*
   initial:
                       | <---------------------------------------< increasing
       ----------------+-------------------------------------------
       |             |x|       <--A         |y|       <--B        |
       ----------------+----------------------+--------------------
                       | <--greater than x--> | <--less than x--> |

   result:

       ------------------------------------------------------------
       |             |y|         B-->     |x|           A-->      |
       ------------------------------------------------------------
*)

value rec rev_next right =
  fun
  [ [x :: rlist] ->
      loop [] right where rec loop rleft =
        fun
        [ [y :: right] ->
            if x < y then
              List.rev_append rlist [y :: List.rev_append rleft [x :: right]]
            else
              loop [y :: rleft] right
        | [] ->
            rev_next (List.rev [x :: rleft]) rlist ]
  | [] -> [] ]
;

value next list = rev_next [] (List.rev list);

(* *)

value rec rev_rnext right =
  fun
  [ [x :: rlist] ->
      loop [] right where rec loop rleft =
        fun
        [ [y :: right] ->
            if x < y then
              List.rev_append (List.rev_append rleft [x :: right])
                [y :: rlist]
            else
              loop [y :: rleft] right
        | [] ->
            rev_rnext (List.rev [x :: rleft]) rlist ]
  | [] -> [] ]
;

value rnext x = rev_rnext [] x;

(* *)

value rec rev_rnext2 rleft right rlist =
  match (right, rlist) with
  [ ([y :: right], [x :: rlist]) ->
      if x < y then
        List.rev_append (List.rev_append rleft [x :: right]) [y :: rlist]
      else
        rev_rnext2 [y :: rleft] right [x :: rlist]
  | ([], [x :: rlist]) ->
      rev_rnext2 [] (List.rev [x :: rleft]) rlist
  | (_, []) -> [] ]
;

value rec rev_rnext3 rleft right =
  fun
  [ [x :: rlist] ->
      match right with
      [ [y :: right] ->
          if x < y then
            List.rev_append (List.rev_append rleft [x :: right]) [y :: rlist]
          else
            rev_rnext3 [y :: rleft] right [x :: rlist]
      | [] ->
          rev_rnext3 [] (List.rev [x :: rleft]) rlist ]
  | [] -> [] ]
;

(* *)

value ex =
  ["1 belle marquise"; "2 vos beaux yeux"; "3 me font"; "4 mourir";
   "5 d'amour"]
;

value seq n =
  loop n [] where rec loop i list =
    if i <= 0 then list else loop (i - 1) [i - 1 :: list]
;

value rseq n =
  loop 0 [] where rec loop i list =
    if i >= n then list else loop (i + 1) [i :: list]
;

value rec fact n = if n <= 1 then 1 else n * fact (n - 1);

value rec iter next list n =
  if n <= 0 then list else iter next (next list) (n - 1)
;
