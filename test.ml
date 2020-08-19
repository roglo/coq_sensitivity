#load "pa_coq.cmo";

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
    srng_mul : 'a → 'a → 'a;
    srng_to_string : 'a → string }.

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

Fixpoint list_add (add : 'a → 'a → 'a) (l1 l2 : list 'a) :=
  match l1 with
  | [e1 :: l'1] =>
      match l2 with
      | [e2 :: l'2] => [add e1 e2 :: list_add add l'1 l'2]
      | [] => []
      end
  | [] => []
  end.

Fixpoint list_list_add' (add : 'a → 'a → 'a) (ll1 ll2 : list (list 'a)) :=
  match ll1 with
   | [l1 :: ll'1] =>
       match ll2 with
       | [l2 :: ll'2] => [list_add add l1 l2 :: list_list_add' add ll'1 ll'2]
       | [] => []
       end
  | [] => []
  end.

value list_list_add zero (add : 'a → 'a → 'a) r c
    (ll1 : list (list 'a)) (ll2 : list (list 'a)) =
  map
    (fun i →
     map
	(fun j → add (list_list_el zero ll1 i j) (list_list_el zero ll2 i j))
       (seq 0 c))
    (seq 0 r).

value nat_semiring_op : semiring_op nat =
  { srng_zero = 0;
    srng_one = 1;
    srng_add = \+;
    srng_mul = \*;
    srng_to_string x = string_of_int x }.

let so = nat_semiring_op in list_list_add' so.srng_add [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] [[1; 2]; [3; 4]; [5; 6]; [0; 0]].
let so = nat_semiring_op in list_list_add so.srng_zero so.srng_add 3 2 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] [[1; 2]; [3; 4]; [5; 6]; [0; 0]].

Fixpoint list_mul (so : semiring_op 'a) (l1 l2 : list 'a) : 'a :=
  match l1 with
  | [e1 :: l'1] =>
      match l2 with
      | [e2 :: l'2] => so.srng_add (so.srng_mul e1 e2) (list_mul so l'1 l'2)
      | [] => so.srng_zero
      end
  | [] => so.srng_zero
  end.

Definition list_list_mul' (so : semiring_op 'a) (ll1 ll2 : list (list 'a)) :=
  map (λ l1, map (list_mul so l1) (list_list_transpose so.srng_zero ll2))
    ll1.

Definition list_list_mul (ro : semiring_op 'a) r cr c
    (ll1 : list (list 'a)) (ll2 : list (list 'a)) :=
  map
    (λ i,
     map
       (λ k,
        let vl :=
          map
            (λ j,
             ro.srng_mul (list_list_el ro.srng_zero ll1 i j)
               (list_list_el ro.srng_zero ll2 j k))
            (seq 0 cr)
        in
	match vl with
        | [] => srng_zero ro
        | [v :: vl'] => List.fold_left ro.srng_add v vl'
        end)
       (seq 0 c))
    (seq 0 r).

value int_ring_op : ring_op int =
  { rng_semiring = nat_semiring_op;
    rng_opp i = - i }.

let so = nat_semiring_op in list_list_mul so 3 4 2 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] [[1; 2]; [3; 4]; [5; 6]; [0; 0]].

let so = nat_semiring_op in list_list_mul so 3 3 3 [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]].

value void_mat : matrix 'a =
  { mat_list = []; mat_nrows = 0; mat_ncols = 0 }.

Definition mat_def_add (add : 'a → 'a → 'a) (vM1 vM2 : matrix 'a) :
    matrix 'a :=
  if (mat_nrows vM1) = (mat_nrows vM2) then
    if (mat_ncols vM1) = (mat_ncols vM2) then
      {| mat_list := list_list_add' add (mat_list vM1) (mat_list vM2);
         mat_nrows := mat_nrows vM1;
         mat_ncols := mat_ncols vM1 |}
    else void_mat
  else void_mat.

value mat_add zero add (m1 : matrix 'a) (m2 : matrix 'a) : matrix 'a =
  if mat_nrows m1 = mat_nrows m2 && mat_ncols m1 = mat_ncols m2 then
    { mat_list =
        list_list_add zero add (mat_nrows m1) (mat_ncols m1) (mat_list m1)
          (mat_list m2);
      mat_nrows = mat_nrows m1;
      mat_ncols = mat_ncols m1 }
  else
let _ = failwith (sprintf "mat_add (%d,%d) (%d,%d)" (mat_nrows m1) (mat_ncols m1) (mat_nrows m2) (mat_ncols m2)) in
    void_mat.

Definition mat_mul' (so : semiring_op 'a) (m1 m2 : matrix 'a) :
    matrix 'a :=
  if (mat_ncols m1) = (mat_nrows m2) then
    {| mat_list := list_list_mul' so (mat_list m1) (mat_list m2);
       mat_nrows := mat_nrows m1;
       mat_ncols := mat_ncols m2 |}
  else
let _ = failwith (sprintf "mat_mul' (%d,%d) (%d,%d)" (mat_nrows m1) (mat_ncols m1) (mat_nrows m2) (mat_ncols m2)) in
    void_mat.

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
    void_mat.

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

(* block matrices *)

type bmatrix_def 'a =
  [ BMD_1 of 'a
  | BMD_M of matrix (bmatrix_def 'a) ].

type bmatrix 'a =
  [ BM_1 of matrix 'a
  | BM_M of matrix (bmatrix 'a) ].

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

value rec list_list_of_bmat (mm : bmatrix 'a) : list (list 'a) =
  match mm with
  | BM_1 m → m.mat_list
  | BM_M mmm →
      let ll =
        map
          (fun mml → concat_list_list_list (map list_list_of_bmat mml))
          mmm.mat_list
      in
      List.concat ll
  end.

value mat_of_bmat (mm : bmatrix 'a) : matrix 'a =
  mat_of_list (list_list_of_bmat mm).

value void_bmat : bmatrix 'a =
  BM_1 void_mat;

value void_bmat_def : bmatrix_def 'a =
  BMD_1 void_mat;

Definition zero_list_list zero r c : list (list 'a) :=
  map (λ i, map (λ j, zero) (seq 0 c)) (seq 0 r).
Definition zero_mat zero r c : matrix 'a :=
  {| mat_list := zero_list_list zero r c;
     mat_nrows := r; mat_ncols := c |}.
Definition zero_bmat zero r c : bmatrix 'a :=
  BM_1 (zero_mat zero r c).

value rec bmat_opp (ro : ring_op 'a) mm : bmatrix 'a =
  match mm with
  | BM_1 m → BM_1 (mat_opp ro m)
  | BM_M mmm →
      BM_M
        { mat_list = map (map (bmat_opp ro)) (mat_list mmm);
          mat_nrows = mat_nrows mmm;
          mat_ncols = mat_ncols mmm }
  end.

value bmat_of_list (ll : list (list (bmatrix 'a))) :
    matrix (bmatrix 'a) =
  { mat_list = ll;
    mat_nrows = list_list_nrows ll;
    mat_ncols = list_list_ncols ll }.

value rec mIZ_2_pow (ro : ring_op 'a) u n =
  match n with
  | 0 → BM_1 {mat_list = [[u]]; mat_nrows = 1; mat_ncols = 1}
  | _ →
      let n' = n - 1 in
      BM_M
        {mat_list =
	   [[mIZ_2_pow ro u n'; mIZ_2_pow ro 0 n'];
	    [mIZ_2_pow ro 0 n'; mIZ_2_pow ro u n']];
         mat_nrows = 2; mat_ncols = 2}
  end.

value rec mA (ro : ring_op 'a) n =
  match n with
  | 0 → BM_1 (mat_of_list [[srng_zero (rng_semiring ro)]])
  | _ →
       let n' = n - 1 in
       BM_M
         (bmat_of_list
            [[mA ro n'; mIZ_2_pow ro 1 n'];
             [mIZ_2_pow ro 1 n'; bmat_opp ro (mA ro n')]])
  end.

list_list_of_bmat (mA int_ring_op 2);
mat_of_bmat (mA int_ring_op 2);

Fixpoint bmat_depth' (vBM : bmatrix_def 'a) :=
  match vBM with
  | BMD_1 _ => 1
  | BMD_M vBMM =>
      1 +
      List.fold_left (λ m la, List.fold_left max m la)
        0 (List.map (List.map (bmat_depth')) (mat_list vBMM))
  end.

value rec bmat_depth (mm : bmatrix 'a) =
  match mm with
  | BM_1 _ → 1
  | BM_M mmm →
      match mmm with
      | {mat_list = []} → 0
      | {mat_list = [mml :: _]} →
          match mml with
          | [] → 0
          | [mm' :: _] → 1 + bmat_depth mm'
          end
      end
  end.

bmat_depth (mA int_ring_op 0).
bmat_depth (mA int_ring_op 1).
bmat_depth (mA int_ring_op 2).
bmat_depth (mA int_ring_op 3).
bmat_depth (mA int_ring_op 4).

value mbmat_depth (mmm : matrix (bmatrix 'a)) =
  bmat_depth (mat_el void_bmat mmm 0 0).

Fixpoint bmat_def_add_loop (so : semiring_op 'a) it
    (vMM1 vMM2 : bmatrix_def 'a) :=
  match it with
  | 0 => void_bmat_def
  | S it' =>
      match vMM1 with
      | BMD_1 xa =>
          match vMM2 with
          | BMD_1 xb => BMD_1 (so.srng_add xa xb)
          | BMD_M vMMB => void_bmat_def
          end
      | BMD_M vMMA =>
          match vMM2 with
          | BMD_1 vMB => void_bmat_def
          | BMD_M vMMB =>
              BMD_M (mat_def_add (bmat_def_add_loop so it') vMMA vMMB)
          end
      end
  end.

Definition bmat_def_add (so : semiring_op 'a) (vMM1 vMM2 : bmatrix_def 'a) :=
  bmat_def_add_loop so (bmat_depth' vMM1) vMM1 vMM2.

value rec bmat_add_loop it zero add (mm1 : bmatrix 'a) (mm2 : bmatrix 'a) =
  match it with
  | 0 →
let _ = failwith (sprintf "mat_add_loop it=0") in
      void_bmat
  | _ →
      let it' = it - 1 in
      match mm1 with
      | BM_1 ma →
          match mm2 with
          | BM_1 mb → BM_1 (mat_add zero add ma mb)
          | BM_M mmb →
let _ = failwith (sprintf "mat_add_loop BM_1(%d,%d)+BM_M(%d,%d)" (mat_nrows ma) (mat_ncols ma) (mat_nrows mmb) (mat_ncols mmb)) in
              void_bmat
          end
      | BM_M mma →
          match mm2 with
          | BM_1 mb →
let _ = failwith (sprintf "mat_add_loop BM_M(%d,%d)+BM_1(%d,%d)" (mat_nrows mma) (mat_ncols mma) (mat_nrows mb) (mat_ncols mb)) in
              void_bmat
          | BM_M mmb →
              BM_M (mat_add void_bmat (bmat_add_loop it' zero add) mma mmb)
          end
      end
  end.

value bmat_add (so : semiring_op 'a) (mm1 : bmatrix 'a) (mm2 : bmatrix 'a) =
  bmat_add_loop (bmat_depth mm1) (srng_zero so) (srng_add so) mm1 mm2.

Definition bmat_nrows mm :=
  match mm with
  | BM_1 m => mat_nrows m
  | BM_M mmm => mat_nrows mmm
  end.

Definition bmat_ncols mm :=
  match mm with
  | BM_1 m => mat_ncols m
  | BM_M mmm => mat_ncols mmm
  end.

Fixpoint bmat_mul_loop' (so : semiring_op 'a) (it : nat)
  (vMM1 vMM2 : bmatrix_def 'a) : bmatrix_def 'a :=
  match it with
  | 0 => void_bmat_def
  | S it' =>
      match vMM1 with
      | BMD_1 xa =>
          match vMM2 with
          | BMD_1 xb => BMD_1 (so.srng_mul xa xb)
          | BMD_M _ => void_bmat_def
          end
      | BMD_M vMMA =>
          match vMM2 with
          | BMD_1 _ => void_bmat_def
          | BMD_M vMMB =>
              let bso :=
                {| srng_zero := void_bmat_def;
                   srng_one := void_bmat_def;
                   srng_add := bmat_def_add so;
                   srng_mul := bmat_mul_loop' so it';
		   srng_to_string _ := failwith "srng_to_string bmat_mul" |}
              in
              BMD_M (mat_mul' bso vMMA vMMB)
          end
      end
  end.

Definition bmat_def_mul' (so : semiring_op 'a) (vMM1 vMM2 : bmatrix_def 'a) :=
  bmat_mul_loop' so (bmat_depth' vMM1) vMM1 vMM2.

Fixpoint bmat_mul_loop it (so : semiring_op 'a) (mm1 : bmatrix 'a)
    (mm2 : bmatrix 'a) :=
  match it with
  | 0 => void_bmat
  | _ =>
      let it' := it - 1 in
      match mm1 with
      | BM_1 ma =>
          match mm2 with
          | BM_1 mb => BM_1 (mat_mul so ma mb)
          | BM_M mmb => void_bmat
          end
      | BM_M mmma =>
          match mm2 with
          | BM_1 mb => void_bmat
          | BM_M mmmb =>
              let mso :=
               {| srng_zero := void_bmat;
                   srng_one := void_bmat;
                   srng_add := bmat_add so;
                   srng_mul := bmat_mul_loop it' so;
	           srng_to_string mm :=
		     match mm with
                     | BM_1 m =>
                          sprintf "BM_1(%d,%d)" m.mat_nrows m.mat_ncols
		     | BM_M mmm =>
                          sprintf "BM_M(%d,%d)" mmm.mat_nrows mmm.mat_ncols
                     end |}
              in
              BM_M (mat_mul mso mmma mmmb)
          end
      end
  end.

Definition bmat_mul (so : semiring_op 'a) mm1 mm2 :=
  bmat_mul_loop (bmat_depth mm1) so mm1 mm2.

let ro = int_ring_op in let so = nat_semiring_op in mat_of_bmat (bmat_mul so (mA ro 0) (mA ro 0)).

let ro = int_ring_op in let so = nat_semiring_op in mat_of_bmat (bmat_mul so (mA ro 1) (mA ro 1)).

let ro = int_ring_op in let so = nat_semiring_op in mat_of_bmat (bmat_mul so (mA ro 2) (mA ro 2)).

let ro = int_ring_op in let so = nat_semiring_op in mat_of_bmat (bmat_mul so (mA ro 3) (mA ro 3)).

let ro = int_ring_op in let so = nat_semiring_op in mat_of_bmat (bmat_mul so (mA ro 4) (mA ro 4)).

(*
value mso so sz =
  { srng_zero = zero_bmat (srng_zero so) sz sz;
    srng_one = one_bmat (srng_zero so) (srng_one so) sz sz;
    srng_add = bmat_add so;
    srng_mul = bmat_mul so }
;

(* *)

value m =
  BM_M
    {mat_list=
      [[BM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1};
        BM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1}];
       [BM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1};
        BM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1}]];
     mat_nrows=2; mat_ncols=2};

45;

let so = nat_semiring_op in
bmat_mul_loop 2 so m m;

46;

value mso1 =
  let so = nat_semiring_op in
  { srng_zero = zero_bmat (srng_zero so) 2 2;
    srng_one = one_bmat (srng_zero so) (srng_one so) 2 2;
    srng_add = bmat_add so;
    srng_mul = bmat_mul_loop 42 so }
;
mat_mul mso1
  {mat_list =
     [[BM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1};
       BM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1}];
      [BM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1};
       BM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1}]];
   mat_nrows = 2; mat_ncols = 2}
  {mat_list =
     [[BM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1};
       BM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1}];
      [BM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1};
       BM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1}]];
   mat_nrows = 2; mat_ncols = 2};

42;

list_list_mul (mso nat_semiring_op 2) 2 2 2
  [[BM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1};
    BM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1}];
   [BM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1};
    BM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1}]]
  [[BM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1};
    BM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1}];
   [BM_1 {mat_list=[[1]]; mat_nrows=1; mat_ncols=1};
    BM_1 {mat_list=[[0]]; mat_nrows=1; mat_ncols=1}]];

let n = 1 in bmat_mul nat_semiring_op (mA int_ring_op n) (mA int_ring_op n);
let n = 2 in mA int_ring_op n;
let n = 2 in bmat_mul nat_semiring_op (mA int_ring_op n) (mA int_ring_op n);
42;
let n = 3 in mA int_ring_op n;
43;
let n = 3 in bmat_mul nat_semiring_op (mA int_ring_op n) (mA int_ring_op n);
44;
*)
