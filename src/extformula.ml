open Relation
open Predicate
open MFOTL
open Tuple

module NEval = Dllist
module Sk = Dllist
module Sj = Dllist

type info  = (int * timestamp * relation) Queue.t
type linfo = {mutable llast: (int * timestamp) NEval.cell}
type ainfo = {mutable arel: relation option}
type pinfo = {mutable ptsq: timestamp}
type ninfo = {mutable init: bool}
type oainfo = {mutable ores: relation;
         oaauxrels: (timestamp * relation) Mqueue.t}


type int_map = Intmap.int_map 


type t_agg =
  | C_aux of int 
  | SA_aux of int * cst
  | Med_aux of (int * int_map)

type agg_once_state = {
  tw_rels: (timestamp * (tuple * tuple * cst) list) Queue.t;
  other_rels: (timestamp * relation) Queue.t;
  mutable mset: (tuple, int) Hashtbl.t;
  mutable hres: (tuple, t_agg) Hashtbl.t;
}

type aggMM_once_state = {
  non_tw_rels: (timestamp * relation) Queue.t;
  mutable tbl: (tuple, (timestamp * cst) Dllist.dllist) Hashtbl.t;
}

type ozinfo = {mutable oztree: (int, relation) Sliding.stree;
               mutable ozlast: (int * timestamp * relation) Dllist.cell;
               ozauxrels: (int * timestamp * relation) Dllist.dllist}
type oinfo = {mutable otree: (timestamp, relation) Sliding.stree;
              mutable olast: (timestamp * relation) Dllist.cell;
              oauxrels: (timestamp * relation) Dllist.dllist}
type sainfo = {mutable sres: relation;
               mutable sarel2: relation option;
               saauxrels: (timestamp * relation) Mqueue.t}
type sinfo = {mutable srel2: relation option;
              sauxrels: (timestamp * relation) Mqueue.t}
type ezinfo = {mutable ezlastev: (int * timestamp) NEval.cell;
               mutable eztree: (int, relation) Sliding.stree;
               mutable ezlast: (int * timestamp * relation) Dllist.cell;
               ezauxrels: (int * timestamp * relation) Dllist.dllist}
type einfo = {mutable elastev: (int * timestamp) NEval.cell;
              mutable etree: (timestamp, relation) Sliding.stree;
              mutable elast: (timestamp * relation) Dllist.cell;
              eauxrels: (timestamp * relation) Dllist.dllist}
type uinfo = {mutable ulast: (int * timestamp) NEval.cell;
              mutable ufirst: bool;
              mutable ures: relation;
              mutable urel2: relation option;
              raux: (int * timestamp * (int * relation) Sk.dllist) Sj.dllist;
              mutable saux: (int * relation) Sk.dllist}
type uninfo = {mutable last1: (int * timestamp) NEval.cell;
               mutable last2: (int * timestamp) NEval.cell;
               mutable listrel1: (int * timestamp * relation) Dllist.dllist;
               mutable listrel2: (int * timestamp * relation) Dllist.dllist}

type comp_one = relation -> relation
type comp_two = relation -> relation -> relation

type extformula =
  | ERel of relation
  | EPred of predicate * comp_one * info
  | ELet of predicate * extformula * extformula * linfo
  | ENeg of extformula
  | EAnd of comp_two * extformula * extformula * ainfo
  | EOr of comp_two * extformula * extformula * ainfo
  | EExists of comp_one * extformula
  | EAggreg of comp_one * extformula
  | EAggOnce of extformula * interval * agg_once_state *
                (agg_once_state -> (tuple * tuple * cst) list -> unit) *
                (agg_once_state -> relation -> (tuple * tuple * cst) list) *
                (agg_once_state -> relation)
  | EAggMMOnce of extformula * interval * aggMM_once_state *
                  (aggMM_once_state -> timestamp -> unit) *
                  (aggMM_once_state -> timestamp -> relation -> unit) *
                  (aggMM_once_state -> relation)
  | EPrev of interval * extformula * pinfo
  | ENext of interval * extformula * ninfo
  | ESinceA of comp_two * interval * extformula * extformula * sainfo
  | ESince of comp_two * interval * extformula * extformula * sinfo
  | EOnceA of interval * extformula * oainfo
  | EOnceZ of interval * extformula * ozinfo
  | EOnce of interval * extformula * oinfo
  | ENUntil of comp_two * interval * extformula * extformula * uninfo
  | EUntil of comp_two * interval * extformula * extformula * uinfo
  | EEventuallyZ of interval * extformula * ezinfo
  | EEventually of interval * extformula * einfo


  let rec contains_eventually = function
  | ERel           (rel)                                      -> false
  | EPred          (p, comp, inf)                             -> false
  | ELet           (p, f1, f2, inf)                           -> contains_eventually f1 || contains_eventually f2
  | ENeg           (f1)                                       -> contains_eventually f1
  | EAnd           (c, f1, f2, ainf)                          -> contains_eventually f1 || contains_eventually f2
  | EOr            (c, f1, f2, ainf)                          -> contains_eventually f1 || contains_eventually f2
  | EExists        (c, f1)                                    -> contains_eventually f1
  | EAggreg        (c, f1)                                    -> contains_eventually f1
  | EAggOnce       (f1, dt, agg, upd_old, upd_new, get_res)   -> contains_eventually f1
  | EAggMMOnce     (f1, dt, aggMM, upd_old, upd_new, get_res) -> contains_eventually f1
  | EPrev          (dt, f1, pinf)                             -> contains_eventually f1
  | ENext          (dt, f1, ninf)                             -> contains_eventually f1
  | ESinceA        (c2, dt, f1, f2, sainf)                    -> contains_eventually f1 || contains_eventually f2
  | ESince         (c2, dt, f1, f2, sinf)                     -> contains_eventually f1 || contains_eventually f2
  | EOnceA         (dt, f1, oainf)                            -> contains_eventually f1
  | EOnceZ         (dt, f1, ozinf)                            -> contains_eventually f1
  | EOnce          (dt, f1, oinf)                             -> contains_eventually f1
  | ENUntil        (c1, dt, f1, f2, muninf)                   -> contains_eventually f1 || contains_eventually f2
  | EUntil         (c1, dt, f1, f2, muinf)                    -> contains_eventually f1 || contains_eventually f2
  | EEventuallyZ   (dt, f1, mezinf)                           -> true
  | EEventually    (dt, f1, meinf)                            -> true

(* 
  Print functions used for debugging
 *)  

let print_bool b =
  if b then
    print_string "true"
  else
    print_string "false"

let print_neval str neval =
  print_string str;
  Misc.print_dllist
    (fun (q,tsq) ->
        Printf.printf "(%d,%s)" q (MFOTL.string_of_ts tsq)
    ) neval;
  print_newline()

let print_ainf str ainf =
  print_string str;
  match ainf with
  | None -> print_string "None"
  | Some rel -> Relation.print_rel "" rel

let print_auxel =
  (fun (k,rel) ->
      Printf.printf "(%d->" k;
      Relation.print_rel "" rel;
      print_string ")"
  )
let print_sauxel =
  (fun (tsq,rel) ->
      Printf.printf "(%s," (MFOTL.string_of_ts tsq);
      Relation.print_rel "" rel;
      print_string ")"
  )

let print_rauxel (j,tsj,rrelsj) =
  Printf.printf "(j=%d,tsj=" j;
  MFOTL.print_ts tsj;
  print_string ",r=";
  Misc.print_dllist print_auxel rrelsj;
  print_string "),"


let print_aauxel (q,tsq,rel) =
  Printf.printf "(%d,%s," q (MFOTL.string_of_ts tsq);
  Relation.print_rel "" rel;
  print_string ")"

let print_inf inf =
  Misc.print_queue print_aauxel inf

let print_predinf str inf =
  print_string str;
  print_inf inf;
  print_newline()

let print_linf str inf =
  Printf.printf "%s{" str;
  if inf.llast == NEval.void then
    print_string "last=None; "
  else
    begin
      let (i,tsi) = NEval.get_data inf.llast in
      Printf.printf "last=(%d,%s)" i (MFOTL.string_of_ts tsi)
    end;
  print_endline "}"

let print_ozinf str inf =
  print_string str;
  if inf.ozlast == Dllist.void then
    print_string "ozlast = None; "
  else
    begin
      let (j,_,_) = Dllist.get_data inf.ozlast in
      Printf.printf "ozlast (index) = %d; " j
    end;
  Misc.print_dllist print_aauxel inf.ozauxrels;
  Sliding.print_stree
    string_of_int
    (Relation.print_rel " ztree = ")
    "; ozinf.ztree = "
    inf.oztree

let print_oinf str inf =
  print_string (str ^ "{");
  if inf.olast == Dllist.void then
    print_string "last = None; "
  else
    begin
      let (ts,_) = Dllist.get_data inf.olast in
      Printf.printf "last (ts) = %s; " (MFOTL.string_of_ts ts)
    end;
  print_string "oauxrels = ";
  Misc.print_dllist print_sauxel inf.oauxrels;
  Sliding.print_stree MFOTL.string_of_ts (Relation.print_rel "") ";\n oinf.tree = " inf.otree;
  print_string "}"


let print_sainf str inf =
  print_string str;
  print_ainf "{srel2 = " inf.sarel2;
  Relation.print_rel "; sres=" inf.sres;
  print_string "; sauxrels=";
  Misc.print_mqueue print_sauxel inf.saauxrels;
  print_string "}"

let print_sinf str inf =
  print_string str;
  print_ainf "{srel2=" inf.srel2  ;
  print_string ", sauxrels=";
  Misc.print_mqueue print_sauxel inf.sauxrels;
  print_string "}"


let print_uinf str inf =
  Printf.printf "%s{first=%b; " str inf.ufirst;
  if inf.ulast == NEval.void then
    print_string "last=None; "
  else
    begin
      let (i,tsi) = NEval.get_data inf.ulast in
      Printf.printf "last=(%d,%s); " i (MFOTL.string_of_ts tsi)
    end;
  Relation.print_rel "res=" inf.ures;
  print_string "; raux=";
  Misc.print_dllist print_rauxel inf.raux;
  print_string "; saux=";
  Misc.print_dllist print_auxel inf.saux;
  print_endline "}"

let print_uninf str uninf =
  let get_last last =
    if last == NEval.void then "None"
    else
      begin
        let i,tsi = NEval.get_data last in
        Printf.sprintf "(%d,%s)" i (MFOTL.string_of_ts tsi)
      end
  in
  Printf.printf "%s{last1=%s; last2=%s; " str
    (get_last uninf.last1) (get_last uninf.last2);
  print_string "listrel1=";
  Misc.print_dllist print_aauxel uninf.listrel1;
  print_string "; listrel2=";
  Misc.print_dllist print_aauxel uninf.listrel2;
  print_string "}\n"

let print_ezinf str inf =
  Printf.printf "%s{" str;
  if inf.ezlastev == NEval.void then
    print_string "ezlastev = None; "
  else
    begin
      let (i,tsi) = NEval.get_data inf.ezlastev in
      Printf.printf "ezlastev = (%d,%s); " i (MFOTL.string_of_ts tsi)
    end;
  if inf.ezlast == Dllist.void then
    print_string "ezlast = None; "
  else
    begin
      let (_,ts,_) = Dllist.get_data inf.ezlast in
      Printf.printf "elast (ts) = %s; " (MFOTL.string_of_ts ts)
    end;
  print_string "eauxrels=";
  Misc.print_dllist print_aauxel inf.ezauxrels;
  Sliding.print_stree string_of_int (Relation.print_rel "") "; ezinf.eztree = " inf.eztree;
  print_string "}\n"


let print_einf str inf =
  Printf.printf "%s{" str;
  if inf.elastev == NEval.void then
    print_string "elastev = None; "
  else
    begin
      let (i,tsi) = NEval.get_data inf.elastev in
      Printf.printf "elastev = (%d,%s); " i (MFOTL.string_of_ts tsi)
    end;
  if inf.elast == Dllist.void then
    print_string "elast = None; "
  else
    begin
      let ts = fst (Dllist.get_data inf.elast) in
      Printf.printf "elast (ts) = %s; " (MFOTL.string_of_ts ts)
    end;
  print_string "eauxrels=";
  Misc.print_dllist print_sauxel inf.eauxrels;
  Sliding.print_stree MFOTL.string_of_ts (Relation.print_rel "") "; einf.etree = " inf.etree;
  print_string "}"

let print_einfn str inf =
  print_einf str inf;
  print_newline()


let print_extf str ff =
  let print_spaces d =
    for i = 1 to d do print_string " " done
  in
  let rec print_f_rec d f =
    print_spaces d;
    (match f with
      | ERel _ ->
        print_string "ERel\n";

      | EPred (p,_,inf) ->
        Predicate.print_predicate p;
        print_string ": inf=";
        print_inf inf;
        print_string "\n"

      | _ ->
        (match f with
        | ENeg f ->
          print_string "NOT\n";
          print_f_rec (d+1) f;

        | EExists (_,f) ->
          print_string "EXISTS\n";
          print_f_rec (d+1) f;

        | EPrev (intv,f,pinf) ->
          print_string "PREVIOUS";
          MFOTL.print_interval intv;
          print_string ": ptsq=";
          MFOTL.print_ts pinf.ptsq;
          print_string "\n";
          print_f_rec (d+1) f

        | ENext (intv,f,ninf) ->
          print_string "NEXT";
          MFOTL.print_interval intv;
          print_string ": init=";
          print_bool ninf.init;
          print_string "\n";
          print_f_rec (d+1) f

        | EOnceA (intv,f,inf) ->
          print_string "ONCE";
          MFOTL.print_interval intv;
          Relation.print_rel ": rel = " inf.ores;
          print_string "; oaauxrels = ";
          Misc.print_mqueue print_sauxel inf.oaauxrels;
          print_string "\n";
          print_f_rec (d+1) f

        | EOnceZ (intv,f,oinf) ->
          print_string "ONCE";
          MFOTL.print_interval intv;
          print_ozinf ": ozinf=" oinf;
          print_f_rec (d+1) f

        | EOnce (intv,f,oinf) ->
          print_string "ONCE";
          MFOTL.print_interval intv;
          print_oinf ": oinf = " oinf;
          print_string "\n";
          print_f_rec (d+1) f

        | EEventuallyZ (intv,f,einf) ->
          print_string "EVENTUALLY";
          MFOTL.print_interval intv;
          print_ezinf ": ezinf=" einf;
          print_f_rec (d+1) f

        | EEventually (intv,f,einf) ->
          print_string "EVENTUALLY";
          MFOTL.print_interval intv;
          print_einf ": einf=" einf;
          print_string "\n";
          print_f_rec (d+1) f

        | _ ->
          (match f with
            | ELet (p,f1,f2,linf) ->
              print_string "LET: ";
              Predicate.print_predicate p;
              print_linf " linf=" linf;
              print_f_rec (d+1) f1;
              print_f_rec (d+1) f2

            | EAnd (_,f1,f2,ainf) ->
              print_ainf "AND: ainf=" ainf.arel;
              print_string "\n";
              print_f_rec (d+1) f1;
              print_f_rec (d+1) f2

            | EOr (_,f1,f2,ainf) ->
              print_ainf "OR: ainf=" ainf.arel;
              print_string "\n";
              print_f_rec (d+1) f1;
              print_f_rec (d+1) f2

            | ESinceA (_,intv,f1,f2,sinf) ->
              print_string "SINCE";
              MFOTL.print_interval intv;
              print_sainf ": sinf = " sinf;
              print_string "\n";
              print_f_rec (d+1) f1;
              print_f_rec (d+1) f2

            | ESince (_,intv,f1,f2,sinf) ->
              print_string "SINCE";
              MFOTL.print_interval intv;
              print_sinf ": sinf=" sinf;
              print_string "\n";
              print_f_rec (d+1) f1;
              print_f_rec (d+1) f2

            | EUntil (_,intv,f1,f2,uinf) ->
              print_string "UNTIL";
              MFOTL.print_interval intv;
              print_uinf ": uinf=" uinf;
              print_f_rec (d+1) f1;
              print_f_rec (d+1) f2

            | ENUntil (_,intv,f1,f2,uninf) ->
              print_string "NUNTIL";
              MFOTL.print_interval intv;
              print_uninf ": uninf=" uninf;
              print_f_rec (d+1) f1;
              print_f_rec (d+1) f2

            | _ -> failwith "[print_formula] internal error"
          );
        );
    );
  in
  print_string str;
  print_f_rec 0 ff  
