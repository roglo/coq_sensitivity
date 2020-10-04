(* $Id: permut.ml,v 1.7 2008/10/30 18:59:48 deraugla Exp $ *)

(* The function "next_permut" returns the next permutation of a list.
   Returns [] if no more permutation.
   Next permutation in lexical order *)

(*
   Algorithm for "next_permut" (below):
   - taking the initial list from right to left,
        (e.g. [894765321] from right to left is [123567498])
   - x is the first such that the list decreases
        ([123567] are increasing, 4 is smaller than 7, therefore x=4)
   - cut that increasing list ([123567]) into three parts:
     * the first ones less than x, named "lb" (lb=[123])
     * the first one greater than x, named "y" (y=5)
     * the rest, named "la" (la=[67])
   - the rest is unchanged, named "lc" (lc=[98])
   - in summary:
     * initial: (rev lc)  x (rev la) y (rev lb)
                89        4 76       5 321
     * result:  (rev lc)  y lb   x la
                89        5 123  4 67

   initial:
                       | <---------------------------------------< increasing
       ----------------+-------------------------------------------
       |     lc      |x|       <--la        |y|       <--lb       |
       ----------------+----------------------+--------------------
                       | <--greater than x--> | <--less than x--> |

   result:

       ------------------------------------------------------------
       |     lc      |y|        lb-->     |x|          la-->      |
       ------------------------------------------------------------
*)

value rec rev_next_permut list right =
  match list with
  | [x :: lc] ->
      loop [] right where rec loop lb list =
        match list with
        | [y :: la] ->
            if x < y then
              List.append (List.append (List.rev lc) [y :: lb]) [x :: la]
            else
              loop (List.append lb [y]) la
        | [] ->
            rev_next_permut lc (List.append lb [x])
        end
  | [] -> []
  end.

value next_permut list = rev_next_permut (List.rev list) [].

[8;9;4;7;6;5;3;2;1].
next_permut [8;9;4;7;6;5;3;2;1].

(* optimized version, using List.rev_append and nicely ordered parameters *)

value rec rev_next_permut' right =
  fun
  | [x :: lc] ->
      loop [] right where rec loop rleft =
        fun
        [ [y :: right] ->
            if x < y then
              List.rev_append lc [y :: List.rev_append rleft [x :: right]]
            else
              loop [y :: rleft] right
        | [] ->
            rev_next_permut' (List.rev [x :: rleft]) lc ]
  | [] -> []
  end
;

value next_permut' list = rev_next_permut' [] (List.rev list);

(* borrowed from Molière, "Le bourgeois gentilhomme" *)

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
