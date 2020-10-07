(* ocaml -I $(camlp5 -where) camlp5r.cma *)

(* The function "next_permut" returns the next permutation of a list
   in lexical order. Returns [] if no more permutation. *)

(*
   Algorithm for "next_permut":
   - take the initial list from right to left,
        (e.g. [894765321] from right to left is [123567498])
   - x is the first such that the list decreases
        ([123567] are increasing, 4 is smaller than 7, therefore x=4)
   - the rest is named "lc" (lc=[98]): it will be unchanged
   - cut the increasing list above ([123567]) into three parts:
     * the first ones less than x, named "lb" (lb=[123])
     * the first one greater than x, named "y" (y=5)
     * the rest, named "la" (la=[67])
   - the result is the concatenation of "rev lc", "y", "lb", "x" and "la"
   - if no "x" found, the initial list is all decreasing, result is []
   - by the algorithm, if "x" is found, "y" must be found
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
(* if "x" and "inc" come from next_permut_find_x above, cannot return None *)
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

value rec rev_next_permut' la =
  fun
  | [x :: lc] ->
      loop [] la where rec loop lb =
        fun
        | [y :: la] ->
            if x < y then
              List.rev_append lc [y :: List.rev_append lb [x :: la]]
            else
              loop [y :: lb] la
        | [] ->
            rev_next_permut' (List.rev [x :: lb]) lc
        end
  | [] -> []
  end
;

value next_permut' list = rev_next_permut' [] (List.rev list);

(* borrowed from Molière, "Le bourgeois gentilhomme" *)

value ex =
  ["1 belle marquise"; "2 vos beaux yeux"; "3 me font"; "4 mourir";
   "5 d'amour"]
;

value rec iter next list n =
  if n <= 0 then list else iter next (next list) (n - 1)
;

iter next_permut ex 109;

(* *)

value seq n =
  loop n [] where rec loop i list =
    if i <= 0 then list else loop (i - 1) [i - 1 :: list]
;

value rseq n =
  loop 0 [] where rec loop i list =
    if i >= n then list else loop (i + 1) [i :: list]
;

(* all permutations *)

value rec all_permut_from list =
  match next_permut list with
  | [] -> [list]
  | list' -> [list :: all_permut_from list']
  end.

all_permut_from [1;2;3].

(* all permutations and parities in a row;
   parity = even = false (signature =+1);
   parity = odd = true (signature=-1) *)

value rec insert n l p =
  match l with
  | [] -> [([n], p)]
  | [m :: l'] ->
      [([n; m :: l'], p) ::
       List.map (fun (l, p) -> ([m :: l], p)) (insert n l' (not p))]
  end.

value rec distrib n ppl =
  match ppl with
  | [] -> []
  | [(l, p) :: ppl'] -> List.append (insert n l p) (distrib n ppl')
  end.

value rec all_permut_and_parity list =
  match list with
  | [] -> [([], False)]
  | [n :: list'] ->
      let ppl = all_permut_and_parity list' in
      distrib n ppl
  end.

(* https://gist.github.com/Bamco/6151962 *)

(* interleave 1 [2;3] = [ [1;2;3]; [2;1;3]; [2;3;1] ] *)
value rec interleave x lst =
  match lst with
  [ [] → [[x]]
  | [hd :: tl] →
      [[x :: lst] :: List.map (fun y → [hd :: y]) (interleave x tl)] ]
;

(*permutations [1; 2; 3] =
   [[1; 2; 3]; [2; 1; 3]; [2; 3; 1]; [1; 3; 2]; [3; 1; 2]; [3; 2; 1]] *)
value rec permutations lst =
  match lst with
  [ [hd :: tl] → List.concat (List.map (interleave hd) (permutations tl))
  | _ → [lst] ]
;
