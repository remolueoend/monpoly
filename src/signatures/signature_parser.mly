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
 * ident            = letter , { char | '_' }
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
open CMFOTL

(** returns a fresh record type declaration with its fields sorted alphanumerically. *)
let sort_rec_decl ((name, fields) : record_decl) : record_decl =
  (name, List.sort (fun a b -> compare a.elt.fname b.elt.fname) fields)
  
%}


%token EOF
%token <string> IDENT
%token TINT TSTRING TFLOAT TREGEXP
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
  | name=IDENT body=record_body
    { Record (loc $startpos $endpos (sort_rec_decl (name, body)) ) }
    
(* declaration of a record body: { field1: type1, field2: type2, ..., fieldN: typeN } *)
record_body:
  | LCB fields=separated_list(COM, rec_field) RCB { fields }

(* declaration of single record field: field1: type *)
rec_field:
  | id=IDENT COL t=ty { (loc $startpos $endpos { fname=id; ftyp=t }) }
  
pred_arg:
  | id=IDENT COL t=native_ty { (loc $startpos $endpos { aname=id; atyp=t }) }
  | t=native_ty { (loc $startpos $endpos { aname=""; atyp=t }) }

ty:
  | t=native_ty { t }
  | fields=record_body { TInline (extr_nodes fields) }
  | id=IDENT { TRef id }

native_ty:
  | TINT   { TInt }
  | TFLOAT   { TFloat }
  | TSTRING { TStr }
  | TREGEXP { TRegexp }
