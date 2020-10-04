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
   - the rest is named "lc" (lc=[98]): it will be unchanged
   - cut the increasing list above ([123567]) into three parts:
     * the first ones less than x, named "lb" (lb=[123])
     * the first one greater than x, named "y" (y=5)
     * the rest, named "la" (la=[67])
   - the result is the concatenation of "rev lc", "y", "lb" and "la"
   - the example, in summary:
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

(* returns Some(inc,x,lc) of None if x not found *)
value rec next_permut_find_x rlist =
  match rlist with
  | [] | [_] -> None
  | [y; z :: lc] ->
      if z < y then Some ([y], z, lc)
      else
        match next_permut_find_x [z :: lc] with
        | None -> None
        | Some (inc, x, lc) -> Some ([y :: inc], x, lc)
        end
  end.

(* returns Some(lb,y,la) or None if y not found *)
value rec next_permut_find_y x inc =
  match inc with
  | [] -> None
  | [z :: lz] ->
      if x < z then Some ([], z, lz)
      else
        match next_permut_find_y x lz with
        | None -> None
        | Some (lb, y, la) -> Some ([z :: lb], y, la)
	end
  end.

(* next permutation of a list *)
value next_permut list =
  match next_permut_find_x (List.rev list) with
  | None -> []
  | Some (inc, x, lc) ->
      match next_permut_find_y x inc with
      | None -> []
      | Some (lb, y, la) ->
          List.append (List.append (List.rev lc) [y :: lb]) [x :: la]
      end
  end.

(* *)

[8;9;4;7;6;5;3;2;1].
next_permut [8;9;4;7;6;5;3;2;1].

(* short version, computing x and y in a row and
   using List.rev_append, and nicely ordered parameters *)

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
