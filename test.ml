open Printf.

type nat = int;
value rec firstn n l =
  match n with
  | 0 -> []
  | _ ->
      let n0 = n - 1 in
      match l with
      | [] -> []
      | [a :: l0] -> [a :: firstn n0 l0]
      end
  end.
value length = List.length;
value hd d l = try List.hd l with [ Failure _ → d ];
value nth n l d = try List.nth l n with [ Failure _ → d ].
value map = List.map.
value rec seq (start : nat) (len : nat) : list nat =
  match len with
  | 0 → []
  | _ → let len0 = len - 1 in [start :: seq (start + 1) len0]
  end.
value rec repeat x n =
  match n with
  | 0 -> []
  | _ -> [x :: repeat x (n - 1)]
  end.
value rec nat_pow n m : nat =
  match m with
  | 0 → 1
  | _ → n * nat_pow n (m - 1)
  end.

(* *)

type semiring_op 'a =
  { srng_zero : 'a;
    srng_one : 'a;
    srng_add : 'a → 'a → 'a;
    srng_mul : 'a → 'a → 'a }.

value srng_zero so = so.srng_zero.
value srng_one so = so.srng_one.
value srng_add so = so.srng_add.

type ring_op 'a =
  { rng_semiring : semiring_op 'a;
    rng_opp : 'a → 'a }.

value rng_semiring ro = ro.rng_semiring.
value rng_opp ro = ro.rng_opp.

(**)

type matrix 'a =
  { mat_list : list (list 'a);
    mat_nrows : nat;
    mat_ncols : nat }.

value mat_list ll = ll.mat_list;
value mat_nrows ll = ll.mat_nrows;
value mat_ncols ll = ll.mat_ncols;

value list_list_nrows (ll  : list (list 'a)) =
  length ll.

value list_list_ncols (ll  : list (list 'a)) =
  length (hd [] ll).

value mat_of_list (ll : list (list 'a)) : matrix 'a =
  { mat_list = ll;
    mat_nrows = list_list_nrows ll;
    mat_ncols = list_list_ncols ll }.

mat_of_list [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]].

value list_list_el d (ll : list (list 'a)) i j =
  nth j (nth i ll []) d.

let (i, j) = (2, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j.
let (i, j) = (7, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j.

value mat_el d (m : matrix 'a) i j =
  list_list_el d (mat_list m) i j.

let (i, j) = (2, 1) in mat_el 42 (mat_of_list [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] : matrix nat) i j.
let (i, j) = (7, 1) in mat_el 42 (mat_of_list [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] : matrix nat) i j.

value list_list_transpose d (ll : list (list 'a)) : list (list 'a) =
  let r = list_list_nrows ll in
  let c = list_list_ncols ll in
  map (fun i → map (fun j → list_list_el d ll j i) (seq 0 r)) (seq 0 c).

list_list_transpose 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]].

value mat_transpose (d : 'a) (m : matrix 'a) : matrix 'a =
  { mat_list = list_list_transpose d (mat_list m);
    mat_nrows = mat_ncols m;
    mat_ncols = mat_nrows m }.

mat_transpose 0 (mat_of_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]).

value list_list_add zero (add : 'a → 'a → 'a) r c
    (ll1 : list (list 'a)) (ll2 : list (list 'a)) =
  map
    (fun i →
     map
	(fun j → add (list_list_el zero ll1 i j) (list_list_el zero ll2 i j))
       (seq 0 c))
    (seq 0 r).

value list_list_mul (ro : semiring_op 'a) r cr c
    (ll1 : list (list 'a)) (ll2 : list (list 'a)) =
  map
    (fun i →
     map
       (fun k →
        let vl =
          map
            (fun j →
             ro.srng_mul (list_list_el ro.srng_zero ll1 i j)
               (list_list_el ro.srng_zero ll2 j k))
            (seq 0 cr)
        in
	match vl with
        | [] → ro.srng_zero
        | [v :: vl'] → List.fold_left ro.srng_add v vl'
        end)
       (seq 0 c))
    (seq 0 r).

value nat_semiring_op : semiring_op nat =
  { srng_zero = 0;
    srng_one = 1;
    srng_add = \+;
    srng_mul = \* }.

value int_ring_op : ring_op int =
  { rng_semiring = nat_semiring_op;
    rng_opp i = - i }.

let so = nat_semiring_op in list_list_mul so 3 4 2 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] [[1; 2]; [3; 4]; [5; 6]; [0; 0]].

let so = nat_semiring_op in list_list_mul so 3 3 3 [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]].

value mat_err : matrix 'a =
  { mat_list = []; mat_nrows = 0; mat_ncols = 0 }.

value mat_add zero add (m1 : matrix 'a) (m2 : matrix 'a) : matrix 'a =
  if mat_nrows m1 = mat_nrows m2 && mat_ncols m1 = mat_ncols m2 then
    { mat_list =
        list_list_add zero add (mat_nrows m1) (mat_ncols m1) (mat_list m1)
          (mat_list m2);
      mat_nrows = mat_nrows m1;
      mat_ncols = mat_ncols m1 }
  else
let _ = failwith (sprintf "mat_add (%d,%d) (%d,%d)" (mat_nrows m1) (mat_ncols m1) (mat_nrows m2) (mat_ncols m2)) in
    mat_err.

value mat_mul (ro : semiring_op 'a) (m1 : matrix 'a) (m2 : matrix 'a) :
    matrix 'a =
  if mat_ncols m1 = mat_nrows m2 then
    { mat_list =
        list_list_mul ro (mat_nrows m1) (mat_ncols m1) (mat_ncols m2)
          (mat_list m1) (mat_list m2);
      mat_nrows = mat_nrows m1;
      mat_ncols = mat_ncols m2 }
  else
let _ = failwith (sprintf "mat_mul (%d,%d) (%d,%d)" (mat_nrows m1) (mat_ncols m1) (mat_nrows m2) (mat_ncols m2)) in
    mat_err.

42;
let so = nat_semiring_op in mat_mul so (mat_of_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list [[1; 2]; [3; 4]; [5; 6]; [0; 0]]).
43;
(*
let so = nat_semiring_op in mat_mul so (mat_of_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list [[1; 2]; [3; 4]; [5; 6]]).
44;
let so = nat_semiring_op in mat_mul so (mat_of_list [[1; 2]; [3; 4]; [5; 6]]) (mat_of_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]).
*)

let so = nat_semiring_op in mat_ncols (mat_mul so (mat_of_list [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]) (mat_of_list [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]])).

value list_list_opp (ro : ring_op 'a) (ll : list (list 'a)) =
  map (map (rng_opp ro)) ll.

value mat_opp (ro : ring_op 'a) (m : matrix 'a) =
  { mat_list = list_list_opp ro (mat_list m);
    mat_nrows = mat_nrows m;
    mat_ncols = mat_ncols m }.

(* matrices of matrices *)

type mmatrix 'a =
  [ MM_1 of matrix 'a
  | MM_M of matrix (mmatrix 'a) ].

value rec concat_list_in_list ll1 ll2 =
  match ll1 with
  | [] → ll2
  | [l1 :: ll1'] →
       match ll2 with
       | [] → ll1
       | [l2 :: ll2'] → [l1 @ l2 :: concat_list_in_list ll1' ll2']
       end
  end.

value concat_list_list_list lll =
  List.fold_left concat_list_in_list [] lll.

value rec list_list_of_mmat (mm : mmatrix 'a) : list (list 'a) =
  match mm with
  | MM_1 m → m.mat_list
  | MM_M mmm →
      let ll =
        map
          (fun mml → concat_list_list_list (map list_list_of_mmat mml))
          mmm.mat_list
      in
      List.concat ll
  end.

value mat_of_mmat (mm : mmatrix 'a) : matrix 'a =
  mat_of_list (list_list_of_mmat mm).

value mmat_err : mmatrix 'a =
  MM_1 mat_err;

value zero_list_list zero r c : list (list 'a) =
  map (fun i → map (fun j → zero) (seq 0 c)) (seq 0 r).
value zero_mat zero r c : matrix 'a =
  { mat_list = zero_list_list zero r c;
    mat_nrows = r; mat_ncols = c }.
value zero_mmat zero r c : mmatrix 'a =
  MM_1 (zero_mat zero r c).

value one_list_list zero one r c : list (list 'a) =
  map
    (fun i → map (fun j → if i = j then one else zero) (seq 0 c))
    (seq 0 r).
value one_mat zero one r c : matrix 'a =
  { mat_list = one_list_list zero one r c;
    mat_nrows = r; mat_ncols = c }.
value one_mmat zero one r c : mmatrix 'a =
  MM_1 (one_mat zero one r c).

value rec mmat_opp (ro : ring_op 'a) mm : mmatrix 'a =
  match mm with
  | MM_1 m → MM_1 (mat_opp ro m)
  | MM_M mmm →
      MM_M
        { mat_list = map (map (mmat_opp ro)) (mat_list mmm);
          mat_nrows = mat_nrows mmm;
          mat_ncols = mat_ncols mmm }
  end.

value mmat_of_list (ll : list (list (mmatrix 'a))) :
    matrix (mmatrix 'a) =
  { mat_list = ll;
    mat_nrows = list_list_nrows ll;
    mat_ncols = list_list_ncols ll }.

value rec mIZ_2_pow (ro : ring_op 'a) u n =
  match n with
  | 0 → MM_1 {mat_list = [[u]]; mat_nrows = 1; mat_ncols = 1}
  | _ →
      let n' = n - 1 in
      MM_M
        {mat_list =
	   [[mIZ_2_pow ro 1 n'; mIZ_2_pow ro 0 n'];
	    [mIZ_2_pow ro 0 n'; mIZ_2_pow ro 1 n']];
         mat_nrows = 2; mat_ncols = 2}
  end.

value rec mA (ro : ring_op 'a) n =
  match n with
  | 0 → MM_1 (mat_of_list [[srng_zero (rng_semiring ro)]])
  | _ →
       let n' = n - 1 in
       MM_M
         (mmat_of_list
            [[mA ro n'; mIZ_2_pow ro 1 n'];
             [mIZ_2_pow ro 1 n'; mmat_opp ro (mA ro n')]])
  end.

list_list_of_mmat (mA int_ring_op 2);
mat_of_mmat (mA int_ring_op 2);

value rec mmat_depth (mm : mmatrix 'a) =
  match mm with
  | MM_1 _ → 1
  | MM_M mmm →
      match mmm with
      | {mat_list = []} → 0
      | {mat_list = [mml :: _]} →
          match mml with
          | [] → 0
          | [mm' :: _] → 1 + mmat_depth mm'
          end
      end
  end.

mmat_depth (mA int_ring_op 0).
mmat_depth (mA int_ring_op 1).
mmat_depth (mA int_ring_op 2).
mmat_depth (mA int_ring_op 3).
mmat_depth (mA int_ring_op 4).

value mmmat_depth (mmm : matrix (mmatrix 'a)) =
  mmat_depth (mat_el mmat_err mmm 0 0).

value rec mmat_add_loop it zero add (mm1 : mmatrix 'a) (mm2 : mmatrix 'a) =
  match it with
  | 0 →
let _ = failwith (sprintf "mat_add_loop it=0") in
      mmat_err
  | _ →
      let it' = it - 1 in
      match mm1 with
      | MM_1 ma →
          match mm2 with
          | MM_1 mb → MM_1 (mat_add zero add ma mb)
          | MM_M mmb →
let _ = failwith (sprintf "mat_add_loop MM_1+MM_M") in
              mmat_err
          end
      | MM_M mma →
          match mm2 with
          | MM_1 mb →
let _ = failwith (sprintf "mat_add_loop MM_M(%d,%d)+MM_1(%d,%d)" (mat_nrows mma) (mat_ncols mma) (mat_nrows mb) (mat_ncols mb)) in
              mmat_err
          | MM_M mmb →
              MM_M (mat_add mmat_err (mmat_add_loop it' zero add) mma mmb)
          end
      end
  end.

value mmat_add (so : semiring_op 'a) (mm1 : mmatrix 'a) (mm2 : mmatrix 'a) =
  mmat_add_loop (mmat_depth mm1) (srng_zero so) (srng_add so) mm1 mm2.

value rec mmat_mul_loop it (so : semiring_op 'a) (mm1 : mmatrix 'a)
    (mm2 : mmatrix 'a) =
  match it with
  | 0 → mmat_err
  | _ →
      let it' = it - 1 in
      match mm1 with
      | MM_1 ma ->
          match mm2 with
          | MM_1 mb -> MM_1 (mat_mul so ma mb)
          | MM_M mmb -> mmat_err
          end
      | MM_M mmma ->
          match mm2 with
          | MM_1 mb -> mmat_err
          | MM_M mmmb ->
              let mso =
                { srng_zero =
                    zero_mmat (srng_zero so)
		      (mat_nrows mmma) (mat_ncols mmmb);
                  srng_one =
                    one_mmat (srng_zero so) (srng_one so)
                      (mat_nrows mmma) (mat_ncols mmmb);
                  srng_add = mmat_add so;
                  srng_mul = mmat_mul_loop it' so }
              in
              MM_M (mat_mul mso mmma mmmb)
          end
      end
  end.

value mmat_mul (so : semiring_op 'a) mm1 mm2 =
  mmat_mul_loop (mmat_depth mm1) so mm1 mm2.

let ro = int_ring_op in let so = nat_semiring_op in
mat_of_mmat (mmat_mul so (mA ro 0) (mA ro 0)).

let ro = int_ring_op in let so = nat_semiring_op in
mat_of_mmat (mmat_mul so (mA ro 1) (mA ro 1)).

let ro = int_ring_op in let so = nat_semiring_op in
mat_of_mmat (mmat_mul so (mA ro 2) (mA ro 2)).

(* wrong result *)
let ro = int_ring_op in let so = nat_semiring_op in
mat_of_mmat (mmat_mul so (mA ro 3) (mA ro 3)).

(*
let ro = int_ring_op in let so = nat_semiring_op in
mat_of_mmat (mmat_mul so (mA ro 4) (mA ro 4)).

value mso so sz =
  { srng_zero = zero_mmat (srng_zero so) sz sz;
    srng_one = one_mmat (srng_zero so) (srng_one so) sz sz;
    srng_add = mmat_add so;
    srng_mul = mmat_mul so }
;

(* *)

value m =
  MM_M
    {mat_list=
      [[MM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1};
        MM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1}];
       [MM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1};
        MM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1}]];
     mat_nrows=2; mat_ncols=2};

45;

let so = nat_semiring_op in
mmat_mul_loop 2 so m m;

46;

value mso1 =
  let so = nat_semiring_op in
  { srng_zero = zero_mmat (srng_zero so) 2 2;
    srng_one = one_mmat (srng_zero so) (srng_one so) 2 2;
    srng_add = mmat_add so;
    srng_mul = mmat_mul_loop 42 so }
;
mat_mul mso1
  {mat_list =
     [[MM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1};
       MM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1}];
      [MM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1};
       MM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1}]];
   mat_nrows = 2; mat_ncols = 2}
  {mat_list =
     [[MM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1};
       MM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1}];
      [MM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1};
       MM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1}]];
   mat_nrows = 2; mat_ncols = 2};

42;

list_list_mul (mso nat_semiring_op 2) 2 2 2
  [[MM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1};
    MM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1}];
   [MM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1};
    MM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1}]]
  [[MM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1};
    MM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1}];
   [MM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1};
    MM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1}]];

let n = 1 in mmat_mul nat_semiring_op (mA int_ring_op n) (mA int_ring_op n);
let n = 2 in mA int_ring_op n;
let n = 2 in mmat_mul nat_semiring_op (mA int_ring_op n) (mA int_ring_op n);
42;
let n = 3 in mA int_ring_op n;
43;
let n = 3 in mmat_mul nat_semiring_op (mA int_ring_op n) (mA int_ring_op n);
44;
*)
