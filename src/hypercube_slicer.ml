open Murmur_hash3
open Predicate
open Helper
open Tuple
open Mformula
open Domain_set

exception Error of string

type integral_value = int
type string_value   = string
type var_id = { var: Predicate.var; free_id: int; tcst: Predicate.tcst }

type hypercube_slicer = {
  formula: mformula;
  variables_in_order: var_id array;
  heavy:  heavy array;
  shares: int array array;
  seeds: int array array;
  strides: int array array;
  degree: int;
}

module Result_Set = Set.Make (
  struct type t = int
    let compare = Stdlib.compare
  end)

include Result_Set

type result_set = Result_Set.t

let rec filter i pos l res =
  if List.length l <> 0 then begin
    if pos.(i) > -1 then 
      filter (i+1) pos (List.tl l) (List.hd l :: res)
    else 
      filter (i+1) pos (List.tl l) res  
  end
  else res

let dimensions formula = List.length (Mformula.free_vars formula) 

let rec remove_duplicates l = match l with
  | [] -> []
  | h::t -> h::(remove_duplicates (List.filter (fun x -> x.var <> h.var) t))

let build_var_ids_preds free_vars preds_form preds_sig =
  let sorted = (List.sort Stdlib.compare free_vars) in

  let sorted_free_vars = List.map (fun e -> Predicate.string_of_var e) sorted in

  let rec check_preds preds res_total =
    if List.length preds != 0 then begin
      let (name, arity, args) = List.hd preds in
      let str_args = List.map (fun e -> Predicate.string_of_term e) args in

      let pred = List.find (fun el -> el.name = name) preds_sig in
      let pos_in_free  = Array.of_list (List.map (fun v -> Misc.get_pos_no_e v free_vars) str_args) in
      let vars = filter 0 pos_in_free pred.vars [] in
      

      (*let vars = Array.of_list pred.vars in
      let res = List.map (fun i -> vars.(i)) pos in
      let pos = Array.of_list pos in *)
      let free_vars_arr = Array.of_list free_vars in
      let res = List.mapi (fun i e -> 
        let name = free_vars_arr.(i) in
        { tcst = e.ptcst; var = name; free_id = (Misc.get_pos name sorted_free_vars) }
      ) vars in
      check_preds (List.tl preds) (List.append res res_total) 
    end else res_total
  in
  remove_duplicates (check_preds preds_form [])

let degree shares = 
  let simple_shares = shares.(0) in
  if (Array.length simple_shares == 0) then 1
  else Array.fold_left (fun acc b -> acc * b) 1 simple_shares

let strides shares dimensions = 
  let dims = dimensions in
  let strides = Array.init (Array.length shares) 
      (fun _ -> Array.init dims (fun _ -> 1))
  in
  let () = Array.iteri (
    fun h s ->
      for i = 1 to dims-1 do s.(i) <- s.(i - 1) * shares.(h).(i - 1) done
    ) strides in
  strides


let handle_hash x seed = 
  let lo = x in
  let hi = x lsr 32 in
  let res = Int32.to_int (Murmur_hash3.finalize_hash (Murmur_hash3.mix_last (Murmur_hash3.mix seed lo) (Int32.of_int hi)) 0) in
  res

let hash value seed = 
  let str_hash s = 
    Int32.to_int (Murmur_hash3.string_hash s (Int32.of_int seed)) in
  match value with
  (* TODO(JS): Overflow possible. *)
  | Int   x -> handle_hash (Z.to_int x) seed
  | Str   x -> str_hash x
    (*TODO*)
  | Float x -> handle_hash (int_of_float x) seed
  | Regexp (s,r) -> str_hash s

let string_of_some_cst cst =
  match cst with 
  | Some v -> Predicate.string_of_cst v
  | None -> "null"

let return_shares slicer valuation =
  let set = Dllist.empty() in
  let heavy_set = ref 0 in
  let unconstrained_set = ref 0 in

  let heavy = slicer.heavy in

  let rec calc_heavy i = 
    if i < Array.length valuation then begin
      let v, s = heavy.(i) in
      if (v >= 0) then begin
        let value = valuation.(i) in
        match value with 
          | None     ->
            unconstrained_set := !unconstrained_set + (shift_left 1 v);
            calc_heavy (i+1)
          | Some cst -> 
            if contains_cst cst s then begin
                heavy_set := !heavy_set + (shift_left 1 v); 
            end else ();
            calc_heavy (i+1)
        end else
          calc_heavy (i+1)
    end  
    else ()
  in
  let () = calc_heavy 0 in

  let add_slices_for_heavy_set heavy_set =
    let the_seeds   = (slicer.seeds).(heavy_set) in
    let the_strides = (slicer.strides).(heavy_set) in
    let the_shares  = (slicer.shares).(heavy_set) in

    let rec calc_slice slice_index i = 
      if i < (Array.length valuation) then
        let value = valuation.(i) in
        match value with 
          | Some v -> 
            let index = slice_index + the_strides.(i) * (abs ((mod) (hash v the_seeds.(i)) the_shares.(i))) in
            calc_slice index (i+1)
          | None   -> 
            calc_slice slice_index (i+1)
      else 
      slice_index 
    in     
    let slice_index = calc_slice 0 0 in

    let rec broadcast i k =
      if i < 0 then begin
        Dllist.add_last k set;
      end else begin  
        let value = valuation.(i) in
        match value with 
          | Some cst -> 
            broadcast (i - 1) k
          | None     -> 
              let rec iterate j =
                if (j < the_shares.(i)) then begin
                  broadcast (i - 1) (k + the_strides.(i) * j);
                  iterate (j + 1)
                end   
                else ()
              in  
              iterate 0 
      end  
    in
    broadcast (Array.length valuation - 1) slice_index  
  in

  let rec cover_unconstrained m h =
    let check_cond m = 
      if (logand !unconstrained_set m != 0) then
        cover_unconstrained (shift_right m 1) (logor h m)
    in
    if (m == 0) then add_slices_for_heavy_set h
    else begin
      check_cond m;
      cover_unconstrained (shift_right m 1) h
    end   
  in

  let res = if (Array.length valuation == 0) then begin
    set
  end  
  else begin
    cover_unconstrained (shift_left 1 ((Array.length valuation) - 1)) !heavy_set;
    set
  end  
  in
  let rec create_set set =
    if Dllist.is_empty res == false then
      create_set (Result_Set.add (Dllist.pop_first res) set)
    else set
  in
  let result_set = create_set Result_Set.empty in
  Array.of_list (Result_Set.elements result_set)
  

let add_slices_of_valuation slicer tuple free_vars =
  let tuple = Array.of_list tuple in
  let free_vars_full = Mformula.free_vars slicer.formula in
  let valuation = Array.init (List.length free_vars_full) (fun _ -> None) in
  (* mapping of vars array of subformula to vars_full *)

  let pos = List.map (fun v -> Misc.get_pos_no_e v free_vars_full) free_vars in
  (*Printf.printf "free_vars: %d, val: %d, tuple: %d, list: %d" (List.length free_vars) (Array.length valuation) (Array.length tuple) (List.length pos);
  print_endline "";
  Printf.printf "item: %d, val: %d, tuple: %d, list: %d" (List.length free_vars) (Array.length valuation) (Array.length tuple) (List.length pos);
  List.iter (fun p -> Printf.printf "Pos: %d, " p) pos;*)
  List.iteri (fun i e -> if e >= 0 then begin valuation.(e) <- Some tuple.(i) end) pos;
  (*print_endline "past iter";*)
  let res = return_shares slicer valuation
  in
  (*print_endline "Returned shares";*)
  res
  

let convert_heavy formula heavy_unproc =
  let preds = Mformula.predicates formula in
  let variables_in_order = build_var_ids_preds (Mformula.free_vars formula) preds !Domain_set.predicates in
  let heavy = Array.init (Array.length heavy_unproc) (fun i -> (-1, Domain_set.domain_empty)) in
  List.iter (fun e -> 
    let (i, h) = heavy_unproc.(e.free_id) in 
    heavy.(e.free_id) <- (i, domain_set_from_list e.tcst h)
  ) variables_in_order;
  heavy

let create_slicer formula heavy shares seeds =
  let degree = degree shares in
  let dimensions = dimensions formula in  
  let preds = Mformula.predicates formula in
  let variables_in_order = build_var_ids_preds (Mformula.free_vars formula) preds !Domain_set.predicates in
  let strides = strides shares dimensions in
  
  { formula = formula; variables_in_order = Array.of_list variables_in_order; heavy = heavy; shares = shares; seeds = seeds; strides = strides; degree = degree }


let convert_slicing_tuple slicer vars values =
  let vars_in_order = slicer.variables_in_order in

  let tuple = Array.init (List.length vars) (fun _ -> None) in
  let values = Array.of_list values in 
  Array.iteri (fun i var -> 
    if String.compare values.(var.free_id) "null" <> 0 then begin
      tuple.(var.free_id) <- Some (Predicate.cst_of_str var.tcst values.(var.free_id))
    end) vars_in_order;

  tuple
