type nat = int;

type matrix 'a = { matel : nat → nat → 'a };

value matel m = m.matel.

value nth i l d =
  try List.nth l i with [ Failure _ → d ].

value rec seq start len =
  if len ≤ 0 then [] else [start :: seq (start + 1) (len - 1)].

value rec pow a b =
  if b ≤ 0 then 1 else a * pow a (b - 1).

type mmatrix 'a =
  [ MM_1 of nat and nat and matrix 'a
  | MM_M of nat and nat and matrix (mmatrix 'a) ].

value mat_of_list d ll =
  { matel i j = nth i (nth j ll []) d }.

value mmat_of_list d (ll : list (list (mmatrix 'a))) :
    matrix (mmatrix 'a) =
  { matel i j = nth i (nth j ll []) (MM_1 0 0 { matel i j = d }) }.

value mI = { matel i j = if i = j then 1 else 0 }.

value mat_opp m = { matel i j = - (matel m i j) }.

value rec mmat_opp mm =
  match mm with
  | MM_1 r c m → MM_1 r c (mat_opp m)
  | MM_M r c mm -> MM_M r c { matel i j = mmat_opp (matel mm i j) }
  end.

value rec mA n =
  match n with
  | 0 → MM_1 0 0 (mat_of_list 0 [])
  | 1 → MM_1 2 2 (mat_of_list 0 [[0; 1]; [1; 0]])
  | _ →
       let n' = n - 1 in
       MM_M 2 2
         (mmat_of_list 0
            [[mA n'; MM_1 (pow 2 n') (pow 2 n') mI];
             [MM_1 (pow 2 n') (pow 2 n') mI; mmat_opp (mA n')]])
  end.

value rec mmat_number_of_rows (mm : mmatrix 'a) =
  match mm with
  | MM_1 r _ _ -> r
  | MM_M r _ mm ->
      List.fold_left
        (fun acc i -> acc + mmat_number_of_rows (matel mm i 0)) 0 (seq 0 r)
  end.

mmat_number_of_rows (mA 3).
(* 8 *)

...

value rec mat_of_mmat mm =
  match mm with
  | MM_1 _ _ m -> m
  | MM_M nr nc mm ->
      let mll =
	List.map
	  (fun r ->
	     List.map
	        (fun c -> mat_of_mmat (matel mm r c)) (seq 0 nc)) (seq 0 nr)
      in
      { matel i j = nth i (nth j mll []) { matel _ _ = 0 } }
  end.
