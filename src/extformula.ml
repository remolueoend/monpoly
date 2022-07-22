open Relation
open Predicate
open MFOTL
open Tuple

module Sk = Dllist
module Sj = Dllist

type info  = (int * timestamp * relation) Queue.t
type linfo = {
  mutable llast: Neval.cell;
}
type ainfo = {mutable arel: relation option}
type pinfo = {mutable plast: Neval.cell}
type ninfo = {mutable init: bool}
type oainfo = {mutable ores: relation;
         oaauxrels: (timestamp * relation) Mqueue.t}

type agg_info = {op: agg_op; default: cst}

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
type ezinfo = {mutable ezlastev: Neval.cell;
               mutable eztree: (int, relation) Sliding.stree;
               mutable ezlast: (int * timestamp * relation) Dllist.cell;
               ezauxrels: (int * timestamp * relation) Dllist.dllist}
type einfo = {mutable elastev: Neval.cell;
              mutable etree: (timestamp, relation) Sliding.stree;
              mutable elast: (timestamp * relation) Dllist.cell;
              eauxrels: (timestamp * relation) Dllist.dllist}
type uinfo = {mutable ulast: Neval.cell;
              mutable ufirst: bool;
              mutable ures: relation;
              mutable urel2: relation option;
              raux: (int * timestamp * (int * relation) Sk.dllist) Sj.dllist;
              mutable saux: (int * relation) Sk.dllist}
type uninfo = {mutable last1: Neval.cell;
               mutable last2: Neval.cell;
               mutable listrel1: (int * timestamp * relation) Dllist.dllist;
               mutable listrel2: (int * timestamp * relation) Dllist.dllist}

type comp_one = relation -> relation
type comp_two = relation -> relation -> relation

type extformula =
  | ERel of relation * int
  | EPred of predicate * comp_one * info * int
  | ELet of predicate * comp_one * extformula * extformula * linfo * int
  | ENeg of extformula * int
  | EAnd of comp_two * extformula * extformula * ainfo * int
  | EOr of comp_two * extformula * extformula * ainfo * int
  | EExists of comp_one * extformula * int
  | EAggreg of agg_info * Aggreg.aggregator * extformula * int
  | EAggOnce of agg_info * Aggreg.once_aggregator * extformula * int
  | EPrev of interval * extformula * pinfo * int
  | ENext of interval * extformula * ninfo * int
  | ESinceA of comp_two * interval * extformula * extformula * sainfo * int
  | ESince of comp_two * interval * extformula * extformula * sinfo * int
  | EOnceA of interval * extformula * oainfo * int
  | EOnceZ of interval * extformula * ozinfo * int
  | EOnce of interval * extformula * oinfo * int
  | ENUntil of comp_two * interval * extformula * extformula * uninfo * int
  | EUntil of comp_two * interval * extformula * extformula * uinfo * int
  | EEventuallyZ of interval * extformula * ezinfo * int
  | EEventually of interval * extformula * einfo * int


  let rec contains_eventually = function
  | ERel           (rel, _)                                      -> false
  | EPred          (p, comp, inf, _)                             -> false
  | ELet           (p, comp, f1, f2, inf, _)                     -> contains_eventually f1 || contains_eventually f2
  | ENeg           (f1, _)                                       -> contains_eventually f1
  | EAnd           (c, f1, f2, ainf, _)                          -> contains_eventually f1 || contains_eventually f2
  | EOr            (c, f1, f2, ainf, _)                          -> contains_eventually f1 || contains_eventually f2
  | EExists        (c, f1, _)                                    -> contains_eventually f1
  | EAggreg        (_inf, _comp, f1, _)                          -> contains_eventually f1
  | EAggOnce       (_inf, _state, f1, _)                         -> contains_eventually f1
  | EPrev          (dt, f1, pinf, _)                             -> contains_eventually f1
  | ENext          (dt, f1, ninf, _)                             -> contains_eventually f1
  | ESinceA        (c2, dt, f1, f2, sainf, _)                    -> contains_eventually f1 || contains_eventually f2
  | ESince         (c2, dt, f1, f2, sinf, _)                     -> contains_eventually f1 || contains_eventually f2
  | EOnceA         (dt, f1, oainf, _)                            -> contains_eventually f1
  | EOnceZ         (dt, f1, ozinf, _)                            -> contains_eventually f1
  | EOnce          (dt, f1, oinf, _)                             -> contains_eventually f1
  | ENUntil        (c1, dt, f1, f2, muninf, _)                   -> contains_eventually f1 || contains_eventually f2
  | EUntil         (c1, dt, f1, f2, muinf, _)                    -> contains_eventually f1 || contains_eventually f2
  | EEventuallyZ   (dt, f1, mezinf, _)                           -> true
  | EEventually    (dt, f1, meinf, _)                            -> true

(* 
  Print functions used for debugging
 *)  

let prerr_bool b =
  if b then
    prerr_string "true"
  else
    prerr_string "false"

let prerr_ainf str ainf =
  prerr_string str;
  match ainf with
  | None -> prerr_string "None"
  | Some rel -> Relation.prerr_rel "" rel

let prerr_auxel =
  (fun (k,rel) ->
      Printf.eprintf "(%d->" k;
      Relation.prerr_rel "" rel;
      prerr_string ")"
  )
let prerr_sauxel =
  (fun (tsq,rel) ->
      Printf.eprintf "(%s," (MFOTL.string_of_ts tsq);
      Relation.prerr_rel "" rel;
      prerr_string ")"
  )

let prerr_rauxel (j,tsj,rrelsj) =
  Printf.eprintf "(j=%d,tsj=" j;
  MFOTL.prerr_ts tsj;
  prerr_string ",r=";
  Dllist.iter prerr_auxel rrelsj;
  prerr_string "),"


let prerr_aauxel (q,tsq,rel) =
  Printf.eprintf "(%d,%s," q (MFOTL.string_of_ts tsq);
  Relation.prerr_rel "" rel;
  prerr_string ")"

let prerr_inf inf =
  Misc.prerr_queue prerr_aauxel inf

let prerr_predinf str inf =
  prerr_string str;
  prerr_inf inf;
  prerr_newline()

let prerr_linf str inf =
  Printf.eprintf "%s{llast=%s}\n" str (Neval.string_of_cell inf.llast)

let prerr_ozinf str inf =
  prerr_string str;
  if inf.ozlast == Dllist.void then
    prerr_string "ozlast = None; "
  else
    begin
      let (j,_,_) = Dllist.get_data inf.ozlast in
      Printf.eprintf "ozlast (index) = %d; " j
    end;
  Dllist.iter prerr_aauxel inf.ozauxrels;
  Sliding.prerr_stree
    string_of_int
    (Relation.prerr_rel " ztree = ")
    "; ozinf.ztree = "
    inf.oztree

let prerr_oinf str inf =
  prerr_string (str ^ "{");
  if inf.olast == Dllist.void then
    prerr_string "last = None; "
  else
    begin
      let (ts,_) = Dllist.get_data inf.olast in
      Printf.eprintf "last (ts) = %s; " (MFOTL.string_of_ts ts)
    end;
  prerr_string "oauxrels = ";
  Dllist.iter prerr_sauxel inf.oauxrels;
  Sliding.prerr_stree MFOTL.string_of_ts (Relation.prerr_rel "") ";\n oinf.tree = " inf.otree;
  prerr_string "}"


let prerr_sainf str inf =
  prerr_string str;
  prerr_ainf "{srel2 = " inf.sarel2;
  Relation.prerr_rel "; sres=" inf.sres;
  prerr_string "; sauxrels=";
  Misc.prerr_mqueue prerr_sauxel inf.saauxrels;
  prerr_string "}"

let prerr_sinf str inf =
  prerr_string str;
  prerr_ainf "{srel2=" inf.srel2  ;
  prerr_string ", sauxrels=";
  Misc.prerr_mqueue prerr_sauxel inf.sauxrels;
  prerr_string "}"


let prerr_uinf str inf =
  Printf.eprintf "%s{first=%b; last=%s; " str inf.ufirst
    (Neval.string_of_cell inf.ulast);
  Relation.prerr_rel "res=" inf.ures;
  prerr_string "; raux=";
  Dllist.iter prerr_rauxel inf.raux;
  prerr_string "; saux=";
  Dllist.iter prerr_auxel inf.saux;
  prerr_endline "}"

let prerr_uninf str uninf =
  Printf.eprintf "%s{last1=%s; last2=%s; " str
    (Neval.string_of_cell uninf.last1) (Neval.string_of_cell uninf.last2);
  prerr_string "listrel1=";
  Dllist.iter prerr_aauxel uninf.listrel1;
  prerr_string "; listrel2=";
  Dllist.iter prerr_aauxel uninf.listrel2;
  prerr_string "}\n"

let prerr_ezinf str inf =
  Printf.eprintf "%s{ezlastev=%s; " str (Neval.string_of_cell inf.ezlastev);
  if inf.ezlast == Dllist.void then
    prerr_string "ezlast = None; "
  else
    begin
      let (_,ts,_) = Dllist.get_data inf.ezlast in
      Printf.eprintf "elast (ts) = %s; " (MFOTL.string_of_ts ts)
    end;
  prerr_string "eauxrels=";
  Dllist.iter prerr_aauxel inf.ezauxrels;
  Sliding.prerr_stree string_of_int (Relation.prerr_rel "") "; ezinf.eztree = " inf.eztree;
  prerr_string "}\n"


let prerr_einf str inf =
  Printf.eprintf "%s{elastev=%s; " str (Neval.string_of_cell inf.elastev);
  if inf.elast == Dllist.void then
    prerr_string "elast = None; "
  else
    begin
      let ts = fst (Dllist.get_data inf.elast) in
      Printf.eprintf "elast (ts) = %s; " (MFOTL.string_of_ts ts)
    end;
  prerr_string "eauxrels=";
  Dllist.iter prerr_sauxel inf.eauxrels;
  Sliding.prerr_stree MFOTL.string_of_ts (Relation.prerr_rel "") "; einf.etree = " inf.etree;
  prerr_string "}"

let prerr_einfn str inf =
  prerr_einf str inf;
  prerr_newline()


let prerr_extf str ff =
  let prerr_spaces d =
    for i = 1 to d do prerr_string " " done
  in
  let rec prerr_f_rec d f =
    prerr_spaces d;
    (match f with
      | ERel (_, loc) ->
        prerr_string "ERel\n";

      | EPred (p,_,inf,loc) ->
        Predicate.prerr_predicate p;
        prerr_string ": inf=";
        prerr_inf inf;
        prerr_string "\n"

      | _ ->
        (match f with
        | ENeg (f,loc) ->
          prerr_string "NOT\n";
          prerr_f_rec (d+1) f;

        | EExists (_,f,loc) ->
          prerr_string "EXISTS\n";
          prerr_f_rec (d+1) f;

        | EPrev (intv,f,pinf,loc) ->
          prerr_string "PREVIOUS";
          MFOTL.prerr_interval intv;
          prerr_string ": plast=";
          prerr_string (Neval.string_of_cell pinf.plast);
          prerr_string "\n";
          prerr_f_rec (d+1) f

        | ENext (intv,f,ninf,loc) ->
          prerr_string "NEXT";
          MFOTL.prerr_interval intv;
          prerr_string ": init=";
          prerr_bool ninf.init;
          prerr_string "\n";
          prerr_f_rec (d+1) f

        | EOnceA (intv,f,inf,loc) ->
          prerr_string "ONCE";
          MFOTL.prerr_interval intv;
          Relation.prerr_rel ": rel = " inf.ores;
          prerr_string "; oaauxrels = ";
          Misc.prerr_mqueue prerr_sauxel inf.oaauxrels;
          prerr_string "\n";
          prerr_f_rec (d+1) f

        | EOnceZ (intv,f,oinf,loc) ->
          prerr_string "ONCE";
          MFOTL.prerr_interval intv;
          prerr_ozinf ": ozinf=" oinf;
          prerr_f_rec (d+1) f

        | EOnce (intv,f,oinf,loc) ->
          prerr_string "ONCE";
          MFOTL.prerr_interval intv;
          prerr_oinf ": oinf = " oinf;
          prerr_string "\n";
          prerr_f_rec (d+1) f

        | EEventuallyZ (intv,f,einf,loc) ->
          prerr_string "EVENTUALLY";
          MFOTL.prerr_interval intv;
          prerr_ezinf ": ezinf=" einf;
          prerr_f_rec (d+1) f

        | EEventually (intv,f,einf,loc) ->
          prerr_string "EVENTUALLY";
          MFOTL.prerr_interval intv;
          prerr_einf ": einf=" einf;
          prerr_string "\n";
          prerr_f_rec (d+1) f

        | EAggreg (info,_,f,loc) -> 
          prerr_string (string_of_agg_op info.op);
          prerr_string "_";
          prerr_string (string_of_cst info.default);
          prerr_string "\n";
          prerr_f_rec (d+1) f

        | EAggOnce (info,aggr,f,loc) -> 
            prerr_string (string_of_agg_op info.op);
            prerr_string "ONCE";
            prerr_string "_";
            prerr_string (string_of_cst info.default);
            prerr_string " ";
            Aggreg.prerr_state aggr;
            prerr_string "\n";
            prerr_f_rec (d+1) f

        | _ ->
          (match f with
            | ELet (p,_,f1,f2,linf,loc) ->
              prerr_string "LET: ";
              Predicate.prerr_predicate p;
              prerr_linf " linf=" linf;
              prerr_f_rec (d+1) f1;
              prerr_f_rec (d+1) f2

            | EAnd (_,f1,f2,ainf,loc) ->
              prerr_ainf "AND: ainf=" ainf.arel;
              prerr_string "\n";
              prerr_f_rec (d+1) f1;
              prerr_f_rec (d+1) f2

            | EOr (_,f1,f2,ainf,loc) ->
              prerr_ainf "OR: ainf=" ainf.arel;
              prerr_string "\n";
              prerr_f_rec (d+1) f1;
              prerr_f_rec (d+1) f2

            | ESinceA (_,intv,f1,f2,sinf,loc) ->
              prerr_string "SINCE";
              MFOTL.prerr_interval intv;
              prerr_sainf ": sinf = " sinf;
              prerr_string "\n";
              prerr_f_rec (d+1) f1;
              prerr_f_rec (d+1) f2

            | ESince (_,intv,f1,f2,sinf,loc) ->
              prerr_string "SINCE";
              MFOTL.prerr_interval intv;
              prerr_sinf ": sinf=" sinf;
              prerr_string "\n";
              prerr_f_rec (d+1) f1;
              prerr_f_rec (d+1) f2

            | EUntil (_,intv,f1,f2,uinf,loc) ->
              prerr_string "UNTIL";
              MFOTL.prerr_interval intv;
              prerr_uinf ": uinf=" uinf;
              prerr_f_rec (d+1) f1;
              prerr_f_rec (d+1) f2

            | ENUntil (_,intv,f1,f2,uninf,loc) ->
              prerr_string "NUNTIL";
              MFOTL.prerr_interval intv;
              prerr_uninf ": uninf=" uninf;
              prerr_f_rec (d+1) f1;
              prerr_f_rec (d+1) f2

            | _ -> failwith "[prerr_formula] internal error"
          );
        );
    );
  in
  prerr_string str;
  prerr_f_rec 0 ff

let pp_print_comma ppf () =
  Format.pp_print_string ppf ",";
  Format.pp_print_space ppf ()

let pp_print_term ppf t = Format.pp_print_string ppf (Predicate.string_of_term t)

let rec pp_structure ppf ff =
  let open Format in
  let pp_unary name loc f1 =
    fprintf ppf "@[(%d:@;<1 2>%s@;<1 2>%a@,)@]" loc name pp_structure f1
  in
  let pp_binary name loc f1 f2 =
    fprintf ppf "@[(%d:@;<1 2>%s@;<1 2>@[<hv>%a@ %a@]@,)@]"
      loc
      name
      pp_structure f1
      pp_structure f2
  in
  match ff with
  | ERel (rel, loc) ->
      if Relation.is_empty rel then
        fprintf ppf "@[<h>(%d:@ FALSE)@]" loc
      else
        fprintf ppf "@[<h>(%d:@ TRUE)@]" loc
  | EPred ((p, _, args), _, _, loc) ->
      fprintf ppf "@[<h>(%d:@ @[<hov 2>%s(@,%a)@])@]"
        loc
        p
        (pp_print_list ~pp_sep:pp_print_comma pp_print_term) args
  | ELet ((p, _, args), _, f1, f2, _, loc) ->
      fprintf ppf "@[<hv>@[<hov 4>%d: LET@ %s(@,%a)@ =@]@;<1 2>%a@ IN@ %a@]"
        loc
        p
        (pp_print_list ~pp_sep:pp_print_comma pp_print_term) args
        pp_structure f1
        pp_structure f2
  | ENeg (f1, loc) -> pp_unary "NEG" loc f1
  | EAnd (_, f1, f2, _, loc) -> pp_binary "AND" loc f1 f2
  | EOr (_, f1, f2, _, loc) -> pp_binary "OR" loc f1 f2
  | EExists (_, f1, loc) -> pp_unary "EXISTS" loc f1
  | EAggreg (_, _, f1, loc) -> pp_unary "AGGREG" loc f1
  | EAggOnce (_, _, f1, loc) -> pp_unary "AGG ONCE" loc f1
  | EPrev (_, f1, _, loc) -> pp_unary "PREV" loc f1
  | ENext (_, f1, _, loc) -> pp_unary "NEXT" loc f1
  | ESinceA (_, _, f1, f2, _, loc) -> pp_binary "SINCE(A)" loc f1 f2
  | ESince (_, _, f1, f2, _, loc) -> pp_binary "SINCE" loc f1 f2
  | EOnceA (_, f1, _, loc) -> pp_unary "ONCE(A)" loc f1
  | EOnceZ (_, f1, _, loc) -> pp_unary "ONCE(Z)" loc f1
  | EOnce (_, f1, _, loc) -> pp_unary "ONCE" loc f1
  | ENUntil (_, _, f1, f2, _, loc) -> pp_binary "NUNTIL" loc f1 f2
  | EUntil (_, _, f1, f2, _, loc) -> pp_binary "UNTIL" loc f1 f2
  | EEventuallyZ (_, f1, _, loc) -> pp_unary "EVENTUALLY(Z)" loc f1
  | EEventually (_, f1, _, loc) -> pp_unary "EVENTUALLY" loc f1

let extf_structure ff =
  pp_structure Format.str_formatter ff;
  Format.flush_str_formatter ()
