open Predicate

module IntMap = Map.Make (
  struct type t = cst
    let compare = Pervasives.compare
  end)

type int_map = int IntMap.t 
type key = IntMap.key 

let singleton k e = IntMap.singleton k e
let choose (a : int_map) : ( Predicate.cst * int) = IntMap.choose a
let iter (f: Predicate.cst -> int -> unit) (m : int_map) = IntMap.iter f m

let find (k: Predicate.cst) (m: int_map) = IntMap.find k m
let remove (k: Predicate.cst) (m: int_map) : int_map = IntMap.remove k m
let add (k: Predicate.cst) (e: int) (m: int_map) : int_map = IntMap.add k e m