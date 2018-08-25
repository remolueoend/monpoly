open Predicate

type domain = 
  | Some of cst
  | None

type formula_pred = { pvar: var; ptcst: tcst}  

module Domain_Set = Set.Make (
  struct type t = domain
    let compare = Pervasives.compare
  end)

include Domain_Set

type domain_set = Domain_Set.t

type heavy = int * domain_set
type heavy_unproc = int * string list

type integral_value = int
type string_value   = string

type split_save_parameters = (heavy_unproc array * int array array * int array array)

let domain_empty = Domain_Set.empty

let predicates = ref []

let domain_of_string t str : domain =
  match str with
    | "null" -> None
    | _ -> Some (cst_of_str t str)

let domain_of_string_basic str : domain =
  match str with
    | "null" -> None
    | _ -> Some (cst_of_str_basic str)    


let domain_set_from_list t l = 
  let ds = Domain_Set.empty in
  let rec iter ds tl =
    if List.length tl > 0 then 
      let ds = Domain_Set.add (domain_of_string t (List.hd tl)) ds in
      iter ds (List.tl tl)
    else ds
  in
  iter ds l

let domain_set_from_list_basic l = 
  let ds = Domain_Set.empty in
  let rec iter ds tl =
    if List.length tl > 0 then 
      let ds = Domain_Set.add (domain_of_string_basic (List.hd tl)) ds in
      iter ds (List.tl tl)
    else ds
  in
  iter ds l


let contains_cst cst ds =
  Domain_Set.exists (fun x -> 
    match x with
    | None -> false
    | Some v -> cst_eq cst v
  ) ds