(*
 * Parser generator instructions for signature files.
 *
 * Supports following syntax (EBNF):
 * lowercase        = 'a' | 'b' | .. | 'z'
 * uppercase        = 'A' | 'B' | .. | 'Z'
 * letter           = uppercase | lowercase
 * digit            = '0' | '1' | '2' | ... | '9'
 * newline          = '\n' | '\r' | '\r\n'
 * whitespace       = ' ' | '\t'
 * char             = { letter | digit }
 * ident            = letter , { char }
 *
 * native_ty        = 'int' | 'float' | 'string' | 'bool'
 * ty               = native_ty | ident
 * 
 * record_field     = ident , ':' , ty
 * record           = ident , '{' , { record_field } , '}'
 *
 * pred_named_arg   = ident , ':' , native_ty
 * pred_arg         = pred_named_arg | native_ty
 * predicate        = ident , '(' , { pred_arg } , ')'
 *
 * signature        = predicate | record
 * signatures       = { signature }
 *)

%{
open Signature_ast

%}

%token EOF
%token <string> IDENT
%token TINT TSTRING TFLOAT TBOOL
%token LPA RPA LCB RCB COM SEP COL

%start signatures

%type <signatures> signatures

%%

signatures:
  | s=list(decl) EOF { s }

decl:
  (* declaration of a predicate:
   * 1. predicate_name(type1, type2, ..., typeN)
   * 2. predicate_name(arg1: type1, arg2: type2, ..., argN: typeN)
  *)
  | name=IDENT LPA args=separated_list(COM, pred_arg) RPA
    { Predicate (loc $startpos $endpos (name, args)) }
  (* declaration of a record type: TypeName { field1: type1, field2: type2, ..., fieldN: typeN } *)
  | name=IDENT LCB fs=separated_list(COM, rec_field) RCB
    { Record (loc $startpos $endpos (name, fs) ) }

(* declaration of single record field: field1: type *)
rec_field:
  | id=IDENT COL t=ty { { fname=id; ftyp=t } }
  
pred_arg:
  | id=IDENT COL t=native_ty { { aname=id; atyp=t } }
  | t=native_ty { { aname=""; atyp=t } }

ty:
  | t=native_ty { Native t }
  | id=IDENT { Complex id }

native_ty:
  | TINT   { TInt }
  | TFLOAT   { TFloat }
  | TBOOL  { TBool } 
  | TSTRING { TString }
