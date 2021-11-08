/*
 * This file is part of MONPOLY.
 *
 * Copyright © 2011 Nokia Corporation and/or its subsidiary(-ies).
 * Contact:  Nokia Corporation (Debmalya Biswas: debmalya.biswas@nokia.com)
 *
 * Copyright (C) 2012 ETH Zurich.
 * Contact:  ETH Zurich (Eugen Zalinescu: eugen.zalinescu@inf.ethz.ch)
 *
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, version 2.1 of the
 * License.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library. If not, see
 * http://www.gnu.org/licenses/lgpl-2.1.html.
 *
 * As a special exception to the GNU Lesser General Public License,
 * you may link, statically or dynamically, a "work that uses the
 * Library" with a publicly distributed version of the Library to
 * produce an executable file containing portions of the Library, and
 * distribute that executable file under terms of your choice, without
 * any of the additional requirements listed in clause 6 of the GNU
 * Lesser General Public License. By "a publicly distributed version
 * of the Library", we mean either the unmodified Library as
 * distributed by Nokia, or a modified version of the Library that is
 * distributed under the conditions defined in clause 3 of the GNU
 * Lesser General Public License. This exception does not however
 * invalidate any other reasons why the executable file might be
 * covered by the GNU Lesser General Public License.
 */



%{
  open Misc
  open Predicate
  open MFOTL
  open Tuple
  open Db
  open Helper
  open Filter_rel
  open Domain_set

  let f str =
    if Misc.debugging Dbg_log then
      Printf.eprintf "[Log_parser] %s with start=%d and end=%d\n%!" str (symbol_start()) (symbol_end())
    else
      ()

  let preds = ref []

  let update_slicer_preds e =
    Domain_set.predicates := e :: !Domain_set.predicates

  let update_preds l =
    preds := l;
    List.iter (fun e -> update_slicer_preds (Domain_set.convert_predicate e)) l;
    l

  let get_type = function
    | "int" -> TInt
    | "string" -> TStr
    | "float" -> TFloat
    | "regexp" -> TRegexp
    | t -> let spos = Parsing.symbol_start_pos() in
           let str = Printf.sprintf
             "[Log_parser.check_fields] Unknown type %s in signature at line %d."
             t spos.Lexing.pos_lnum
           in
           failwith str

  let make_predicate p attr =
    let tl =
      List.map
        (fun str ->
          match Misc.nsplit str ":" with
          | [] -> failwith "[Log_parser.make_predicate] internal error"
          | [type_str] -> "", get_type type_str
          | var_name :: type_str :: _ ->
             var_name, get_type type_str
        )
        attr
    in
    (p, tl)


  let get_schema pname =
    try
      List.find (fun (p, _) -> pname = p) !preds
    with Not_found ->
      let spos = Parsing.symbol_start_pos() in
      let str = Printf.sprintf
        "[Log_parser.get_schema] The predicate %s at line %d was not found in the signature."
        pname spos.Lexing.pos_lnum
      in
      failwith str



  let process_tuple pname attr ar t =
    if List.length t = ar then
      try
        Tuple.make_tuple2 t attr
      with Type_error str_err ->
        let str = Printf.sprintf
          "[Log_parser.make_tuple] Wrong type for predicate %s at line %d in the log file: %s"
          pname (Parsing.symbol_start_pos()).Lexing.pos_lnum str_err
        in
        failwith str
    else
      let str = Printf.sprintf
        "[Log_parser.make_tuple] Wrong tuple length for predicate %s at line %d in the log file."
        pname (Parsing.symbol_start_pos()).Lexing.pos_lnum
      in
      failwith str

  let process_tuples s tuples =
    let pname, attr = s in
    let ar = List.length attr in
    (* we only reverse because [rev_map] is tail-recursive, while [map] is not *)
    List.rev_map (process_tuple pname attr ar) tuples

  (* a tuple is a list of strings here, not a value of type Tuple.tuple *)
  let make_table p tuples =
    let s = get_schema p in
    let rel =
      if !Filter_rel.enabled then
        if Filter_rel.rel_OK p then
          List.filter (Filter_rel.tuple_OK p) (process_tuples s tuples)
        else
          []
      else
        process_tuples s tuples
    in
    s, (Relation.make_relation rel)



  (* db is seen here as an association list *)
  let add_table db (s,rel) =
    if Relation.is_empty rel then
      db
    else if List.mem_assoc s db then
      let rel' = List.assoc s db in
      let new_rel = Relation.union rel rel' in
      (s,new_rel)::(List.remove_assoc s db)
    else
      (s,rel)::db

  let make_db db =
     Db.make_db (List.map (fun (s,r) -> Table.make_table s r) db)

  (* let parse_error str = () *)

  let invalid_db complete =
    if !Misc.ignore_parse_errors then
      DataTuple { ts = ts_invalid; db = Db.make_db []; complete; }
    else
      raise Parsing.Parse_error


(*
  Below functions are only relevant for the manual specification of the mappings from values to state partitions
  in the split_and_save command. Useful for manual testing involving small sample log files.

  Example: 
  > split_state (a:string)(f:int)(m:string),  (Alice,Charlie)(160,187,152)(Mallory),   (0,2)
                                              (Bob)(163)(Merlin),                      (1)
  <
 *)
let make_slicing_test vars tuple destinations =
  let dest = Array.of_list (List.map (fun e -> int_of_string e) destinations) in
  SlicingTestTuple { vars = vars; tuple = tuple; output = dest }

let get_2 (_, a) = a

let return_split_restore_parameters heavy_list shares seeds =
  let heavy_arr = Array.of_list heavy_list in
  SplitSave (heavy_arr, shares, seeds)

let convert_str_list l =  
  Array.of_list (List.map(fun e -> int_of_string e) l)

let convert_nested_str_list l =
  Array.of_list (List.map(fun a -> convert_str_list a) l) 
  

(* Creates a SplitParameters by converting value lists to their appropriate type as defined by the matching key *)
let make_split kwt group  =
  let convert_lists valueLists = 
    let pos = ref 0 in
    List.map2
    (fun k values ->
      List.map (fun v ->
        incr pos;
        let t = get_2 k in 
        Predicate.cst_of_str t v
      ) values
    )
    kwt valueLists
  in
  let g    = List.map (fun sb  -> let vals, parts = sb in {values = (convert_lists vals); partitions = parts}) group in
  let keys = List.map (fun kwt -> let k, t = kwt in k) kwt in
  let max  = Helper.get_max g in
  SplitParameters { keys = keys; constraints = g; num_partitions = max }
  
(* Combines partition lists to state partition group
   State partition group represents the mappings of different value partitions to different state partitions, with a subgroup
   representing the mapping of one value partition to one state partition.
 *)  
let make_group group subgroup = subgroup::group

(* Creates list of integers representing the state partitions a value partition is mapped to*)
let make_subgroup valueLists partitions = (valueLists, List.map (fun p -> try (int_of_string p) with Failure _ -> raise (Type_error ("Partitions list expects integers"))) partitions)

(* Creates a list of keys consisting of a name and type each *)
let make_key str = match Misc.nsplit str ":" with
        | [] -> failwith "[Log_parser.make_predicate] internal error"
        | [type_str] -> "", get_type type_str
        | var_name :: type_str :: _ ->
            var_name, get_type type_str
%}


%token AT LPA RPA LCB RCB COM SEP
%token <string> STR
%token EOF
%token CMD
%token EOC
%token ERR

%start signature
%type <(Db.schema)> signature

%start tsdb
%type <(Helper.parser_feed)> tsdb

%%


signature:
      | predicate signature     { f "signature(list)"; update_preds ($1::$2) }
      |                         { f "signature(end)"; update_preds [] }

predicate:
      | STR LPA fields RPA      { f "predicate"; make_predicate $1 $3 }




tsdb:
      | CMD STR slicing EOC     { CommandTuple { c = $2; parameters = Some $3 } }
      | CMD STR EOC             { CommandTuple { c = $2; parameters = None    } }
      | CMD STR parameters EOC  { CommandTuple { c = $2; parameters = Some $3 } }
      | CMD slicing_test EOC    { $2 }
      | AT STR db SEP           { f "tsdb(next)";   DataTuple { ts = MFOTL.ts_of_string "Log_parser" $2; db = make_db $3; complete = true } }
      | AT STR db AT            { f "tsdb(next)";   DataTuple { ts = MFOTL.ts_of_string "Log_parser" $2; db = make_db $3; complete = false} }
      | AT STR db CMD           { f "tsdb(next)";   DataTuple { ts = MFOTL.ts_of_string "Log_parser" $2; db = make_db $3; complete = false} }
      | AT STR db EOF           { f "tsdb(last)";   DataTuple { ts = MFOTL.ts_of_string "Log_parser" $2; db = make_db $3; complete = false} }
      | AT EOF                  { f "tsdb(ts eof)"; ErrorTuple "end of file" }
      | CMD EOF                 { f "tsdb(cmd eof)"; ErrorTuple "end of file" }
      | EOF                     { f "tsdb(eof)";    ErrorTuple "enf of file" }

      | AT STR error SEP        { f "tsdb(tr-err)";   invalid_db true }
      | AT STR error AT         { f "tsdb(next-err)"; invalid_db false }
      | AT STR error CMD        { f "tsdb(next-err)"; invalid_db false }
      | AT STR error EOF        { f "tsdb(last-err)"; invalid_db false }

db:
      | table db                { f "db(list)"; add_table $2 $1 }
      |                         { f "db()"; [] }

table:
      | STR relation            { f "table";
                                  try
                                    make_table $1 $2
                                  with (Failure str) as e ->
                                    if !Misc.ignore_parse_errors then
                                      begin
                                        prerr_endline str;
                                        raise Parsing.Parse_error
                                      end
                                    else
                                      raise e
                                }
      | STR                     { f "table";
                                  try
                                    make_table $1 [[]]
                                  with (Failure str) as e ->
                                    if !Misc.ignore_parse_errors then
                                      begin
                                        prerr_endline str;
                                        raise Parsing.Parse_error
                                      end
                                    else
                                      raise e
                                }

relation:
      | tuple relation          { f "relation(list)"; $1::$2 }
      | tuple                   { f "relation(list)"; [$1] }

tuple:
      | LPA fields RPA          { f "tuple"; $2 }


fields:
      | STR COM fields          { f "fields(list)"; $1::$3 }
      | STR                     { f "fields(end)"; [$1] }
      |                         { f "fields()"; [] }
  
slicing: 
      | LCB heavies COM shares_seeds COM shares_seeds RCB 
                                { return_split_restore_parameters $2 (convert_nested_str_list $4) (convert_nested_str_list $6) }

heavies:
      | LCB heavy RCB           { $2 }
heavy:
      | tupleseq COM heavy      { $1::$3 }
      | tupleseq                { [$1] }
tupleseq:
      | LPA STR COM nested_field RPA  { (int_of_string $2), $4 }

shares_seeds:
      | LCB nested_fields RCB   { $2 }
nested_fields:
      | nested_field COM nested_fields  { $1::$3 }  
      | nested_field            { [$1] }
nested_field:
      | LPA fields RPA          { $2 }


parameters:
      | STR                     { Argument   $1    }
      | keys COM group          { make_split $1 $3 }
keys: 
      | key      keys           { (make_key $1)::$2}
      |                         { [] }
key:
      | LPA STR RPA             { $2 }

group:
      | subgroup group          { make_group $2 $1 } 
      |                         { [] }
    
subgroup:
      | constraintList COM LPA fields RPA   { make_subgroup $1 $4 }

constraintList:
      | constraintSet constraintList      { $1::$2  }
      |                                   { [] }
constraintSet:
      | LPA fields RPA                    { $2 }

slicing_test:
      | LCB tuple COM tuple COM tuple RCB { make_slicing_test $2 $4 $6}
