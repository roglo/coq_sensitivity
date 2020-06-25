(* $Id: pa_coq.ml,v 1.60 2013-10-11 12:27:21 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pcaml;

EXTEND
  GLOBAL: str_item;
  str_item:
    [ [ "Fixpoint"; l = V (LIST1 coq_binding SEP "and") →
          <:str_item< value rec $_list:l$ >> ] ]
  ;
  coq_binding:
    [ [ p = ipatt; LIST0 GIDENT; e = coq_fun_binding → (p, e) ] ]
  ;
  coq_fun_binding:
    [ RIGHTA
      [ "("; pl = LIST1 LIDENT; ":"; t = ctyp; ")"; e = SELF →
          List.fold_right (fun p e → <:expr< fun ($lid:p$ : $t$) → $e$ >>)
            pl e
      | p = ipatt; e = SELF → <:expr< fun $p$ → $e$ >>
      | ":="; e = coq_expr → <:expr< $e$ >>
      | ":"; t = ctyp; ":="; e = coq_expr → <:expr< ($e$ : $t$) >> ] ]
  ;
  coq_expr:
     [ [ "match"; e = SELF; "with"; l = V (LIST0 coq_match_case); "end" →
            <:expr< match $e$ with [ $_list:l$ ] >>
      | "let"; l = V (LIST1 coq_binding SEP "and"); "in"; x = SELF →
          <:expr< let $_list:l$ in $x$ >>
       | e = expr → e ] ]
  ;
  coq_match_case:
    [ [ "|"; p = patt; "=>"; e = coq_expr →
        let (p, e) =
          match p with
          [ <:patt< S $lid:n$ >> →
              (<:patt< $lid:n$ >>,
               <:expr< let $lid:n$ = pred $lid:n$ in $e$ >>)
          | <:patt< Term $p₁$ $lid:n$ >> →
              (<:patt< Term $p₁$ $lid:n$ >>,
               <:expr< let $lid:n$ = Lazy.force $lid:n$ in $e$ >>)
          | _ →
              (p, e) ]
        in
        (p, <:vala< None >>, e) ] ]
  ;
END;
