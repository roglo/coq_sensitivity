(* $Id: pa_coq.ml,v 1.60 2013-10-11 12:27:21 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pcaml;

EXTEND
  GLOBAL: str_item;
  str_item:
    [ [ "Fixpoint"; l = V (LIST1 let_binding SEP "and") →
          <:str_item< value rec $_list:l$ >> ] ]
  ;
END;
