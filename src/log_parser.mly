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

  let f str =
    if Misc.debugging Dbg_log then
      Printf.printf "[Log_parser] %s with start=%d and end=%d\n%!" str (symbol_start()) (symbol_end())
    else
      ()

  let preds = ref []

  let update_preds l =
    preds := l;
    l

  let get_type = function
    | "int" -> TInt
    | "string" -> TStr
    | "float" -> TFloat
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


  let make_split group = ConstraintSet group


 let make_group2 subgroup1 subgroup2 = 
    let group = Helper.singleton subgroup2 in
    Helper.add subgroup1 group

let make_group group subgroup = 
  if Helper.is_empty group then
    Helper.singleton subgroup
  else 
    Helper.add subgroup group


let get_1 (a, _) = a
let get_2 (_, a) = a


let make_subgroup relname values = 
  let schema = get_schema relname in 
  (* attr is list of types belonging to list in values *)
  let pname, attr = schema in 
  let convert_lists p l = 
    let t = get_2 p in
    let pos = ref 0 in
    List.map
    (fun s ->
       incr pos;
       match t with
       | TInt ->
         (try Int (int_of_string s)
          with Failure _ ->
            raise (Type_error ("Expected type int for field number "
                               ^ (string_of_int !pos))))
       | TStr -> Str s
       | TFloat ->
         (try Float (float_of_string s)
          with Failure _ ->
            raise (Type_error ("Expected type float for field number "
                               ^ (string_of_int !pos))))
    )
    l
  in  
  let cstlists = List.map2 convert_lists attr values in
  { relname = relname; values = cstlists } 

  let make_tuple l1 l2 = 
    match l1 with
    | [[]] -> [l2]
    | _ -> List.append l1 [l2]
%}


%token AT LPA RPA LCB RCB COM
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
      | CMD STR EOC             { CommandTuple { c = $2; parameters = None    } }
      | CMD STR parameters EOC  { CommandTuple { c = $2; parameters = Some $3 } }
      | AT STR db AT            { f "tsdb(next)";  DataTuple { ts = MFOTL.ts_of_string "Log_parser" $2; db = make_db $3; } }
      | AT STR db CMD           { f "tsdb(next)";  DataTuple { ts = MFOTL.ts_of_string "Log_parser" $2; db = make_db $3; } }
      | AT STR db EOF           { f "tsdb(last)";  DataTuple { ts = MFOTL.ts_of_string "Log_parser" $2; db = make_db $3; } }
      | AT EOF                  { f "tsdb(ts eof)"; ErrorTuple "end of file" }
      | CMD EOF                 { f "tsdb(ts eof)"; ErrorTuple "end of file" }
      | EOF                     { f "tsdb(eof)";    ErrorTuple "enf of file" }

      | AT STR error AT         { f "tsdb(next-err)";
          if !Misc.ignore_parse_errors then
             DataTuple { ts = ts_invalid; db = Db.make_db []; }
          else
            raise Parsing.Parse_error
        }

      | AT STR error EOF        { f "tsdb(last-err)";
                                  if !Misc.ignore_parse_errors then
                                     DataTuple { ts = ts_invalid; db = Db.make_db []; }
                                  else
                                    raise Parsing.Parse_error
                                }

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

relation:
      | tuple relation          { f "relation(list)"; $1::$2 }
      |                         { f "relation(end)"; [] }

tuple:
      | LPA fields RPA          { f "tuple"; $2 }


fields:
      | STR COM fields          { f "fields(list)"; $1::$3 }
      | STR                     { f "fields(end)"; [$1] }
      |                         { f "fields()"; [] }

parameters:
      | STR                     { Argument $1  }
      | LCB group RCB           { make_split $2}
group:
      | subgroup subgroup       { make_group2 $2 $1 } 
    
subgroup:
      | LCB STR COM LPA tuple RPA RCB  { make_subgroup $2 [$5] }    
tuple:
      | RPA fields LPA          { $2 }
/*tuple:
      | RPA fields LPA tuple    { make_tuple $4 $2 }
      |                         { [[]] }*/
