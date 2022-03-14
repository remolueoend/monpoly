%{
open Signature_ast

let args_to_fields (args : ty list) : field list =
  List.map (fun ty -> {fname=""; ftyp=ty}) args

%}

%token EOF
%token <string> IDENT
%token <string> CTOR
%token TINT TSTRING TFLOAT TBOOL
%token LPA RPA LCB RCB COM SEP COL

%start signatures

%type <signatures> signatures

%%

signatures:
  | s=list(decl) EOF { s }

decl:
  (* declaration of a predicate without args names: predicate_name(type1, type2, ..., typeN) *)
  // | name=IDENT LPA args=separated_list(COM, ty) RPA
  //   { Predicate (loc $startpos $endpos (name, args_to_fields args)) }
  (* declaration of a predicate with args names: predicate_name(arg1: type1, arg2: type2, ..., argN: typeN) *)
  | name=IDENT LPA fs=separated_list(COM, field_decl) RPA
    { Predicate (loc $startpos $endpos (name, fs)) }
  (* declaration of a record type: TypeName { field1: type1, field2: type2, ..., fieldN: typeN } *)
  | name=CTOR LCB fs=separated_list(COM, field_decl) RCB
    { Record (loc $startpos $endpos (name, fs) ) }

(* declaration of single record field: field1: type *)
field_decl:
  | id=IDENT COL t=ty { { fname=id; ftyp=t } }

ty:
  | TINT   { TInt }
  | TFLOAT   { TFloat }
  | r=rtyp { TRef r }
  | LPA t=ty RPA { t } 
  | TBOOL  { TBool } 
  | TSTRING { TString }

%inline rtyp:
  | id=CTOR { RRecord id }