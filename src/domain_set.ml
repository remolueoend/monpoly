open Predicate

type domain = 
  | Some of cst
  | None

module Domain_Set = Set.Make (
  struct type t = domain
    let compare = Pervasives.compare
  end)

include Domain_Set

type domain_set = Domain_Set.t

type heavy = int * domain_set

type integral_value = int
type string_value   = string

type split_save_parameters = (string * heavy array * int array array * int array array)

let domain_empty = Domain_Set.empty

let contains_cst cst ds =
  Domain_Set.exists (fun x -> 
    match x with
    | None -> false
    | Some v -> cst_eq cst v
  ) ds