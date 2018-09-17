open Murmur_hash3
open Predicate
open Helper
open Tuple
open Mformula
open Log_parser
open Domain_set


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


let dimensions formula = List.length (Mformula.free_vars formula) 

let rec remove_duplicates l = match l with
  | [] -> []
  | h::t -> h::(remove_duplicates (List.filter (fun x -> x.var <> h.var) t))

let build_var_ids_preds free_vars preds_form preds_sig =
  let sorted = (List.sort Pervasives.compare free_vars) in

  let sorted_free_vars = List.map (fun e -> Predicate.string_of_var e) sorted in

  let rec check_preds preds res_total =
    if List.length preds != 0 then begin
      let (name, arity, args) = List.hd preds in
      let str_args = List.map (fun e -> Predicate.string_of_term e) args in

      let pred = List.find (fun el -> el.name = name) preds_sig in
      let pos  = List.filter (fun e -> e > -1) (List.map (fun v -> Misc.get_pos_no_e v str_args) free_vars) in
     
      let vars = Array.of_list pred.vars in
      let res = List.map (fun i -> vars.(i)) pos in
      let pos = Array.of_list pos in
      let str_args = Array.of_list str_args in
      let res = List.mapi (fun i e -> 
        let name = str_args.(pos.(i)) in
        { tcst = e.ptcst; var = name; free_id = (Misc.get_pos name sorted_free_vars) }
      ) res in
      check_preds (List.tl preds) (List.append res res_total) 
    end else res_total
  in
  remove_duplicates (check_preds preds_form [])

let degree shares = 
  let simple_shares = shares.(0) in
  if (Array.length simple_shares == 0) then 1
  else Array.fold_left (fun acc b -> acc * b) 1 simple_shares

let strides shares dimensions = 
  let shares = shares in
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
  let hi = shift_left x 32 in
  Murmur_hash3.finalize_hash (Murmur_hash3.mix_last (Murmur_hash3.mix seed lo) hi) 0

let hash value seed = match value with
  | Int   x -> handle_hash x seed
  | Str   x -> Murmur_hash3.string_hash x seed
  (*TODO*)
  | Float x -> handle_hash (int_of_float x) seed

(* TODO: check ordering *)
let variables_in_order slicer = Mformula.free_vars slicer.formula

let return_shares slicer valuation =
  (*Do not actually need a set here (verify)*)
  let slices = [] in
  let heavy_set = ref 0 in
  let unconstrained_set = ref 0 in

  let heavy = slicer.heavy in

  let rec calc_heavy i = 
    if i < Array.length valuation then begin
      let v, s = heavy.(i) in
      if (v >= 0) then
        let value = valuation.(i) in
        match value with 
          | None     -> unconstrained_set := !unconstrained_set + (shift_left 1 v);
          | Some cst -> 
            if contains_cst cst s then 
                heavy_set := !heavy_set + (shift_left 1 v);     
      calc_heavy (i+1)
    end  
    else ()
  in
  let () = calc_heavy 0 in

  let add_slices_for_heavy_set heavy_set =
    let the_seeds   = (slicer.seeds).(heavy_set) in
    let the_strides = (slicer.strides).(heavy_set) in
    let the_shares  = (slicer.shares).(heavy_set) in

    let slice_index = ref 0 in

    let rec calc_slice i = 
      if i < (Array.length valuation) then
        let value = valuation.(i) in
        match value with 
          | Some v -> 
            (*TODO Verify: should this be abs*)
            slice_index := the_strides.(i) * (abs ((mod) (hash v the_seeds.(i)) the_shares.(i)));
          | None   -> ();
        calc_slice (i+1)
      else ()  
    in     
    let () = calc_slice 0 in

    let rec broadcast slices i k =
      if i < 0 then 
        k :: slices
      else begin  
        let value = valuation.(i) in
        match value with 
          | Some cst -> broadcast slices (i - 1) k
          | None     -> 
              let rec iterate slices j =
                if (j < the_shares.(i)) then begin
                  let slices = broadcast slices (i - 1) (k + the_strides.(i) * j) in
                  iterate slices (j + 1)
                end   
                else slices
              in  
              iterate slices 0 
      end  
    in
    broadcast slices (Array.length valuation - 1) !slice_index  
  in

  let rec cover_unconstrained m h =
    if (h == 0) then add_slices_for_heavy_set h
    else begin
      if (logand !unconstrained_set m != 0) then
        cover_unconstrained (shift_right m 1) (logor h m)
      else cover_unconstrained (shift_right m 1) h
    end   
  in

  let res = if (Array.length valuation == 0) then begin
    Array.of_list (add_slices_for_heavy_set !heavy_set)
  end  
  else begin
    Array.of_list (cover_unconstrained (shift_left 1 ((Array.length valuation) - 1)) !heavy_set)
  end  
  in
  res
  

let add_slices_of_valuation slicer tuple free_vars =
  let tuple = Array.of_list tuple in

  let free_vars_full = Mformula.free_vars slicer.formula in

  let valuation = Array.init (List.length free_vars_full) (fun _ -> None) in
  (* mapping of vars array of subformula to vars_full *)
  let pos = List.map (fun v -> Misc.get_pos_no_e v free_vars_full) free_vars in
  List.iteri (fun i e -> if e >= 0 then begin valuation.(e) <- Some tuple.(i) end) pos;

  return_shares slicer valuation

let mk_verdict_filter slicer slice verdict =
  let heavy_set = ref 0 in
  let vars_in_order = slicer.variables_in_order in
  let rec calc_heavy i = 
    if i < Array.length vars_in_order then
      let var_id = vars_in_order.(i).free_id in
      let value = verdict.(i) in
      let heavyMap = slicer.heavy.(var_id) in
    
      let v, s = heavyMap in
      if (v >= 0 && (contains_cst value s)) then
        heavy_set := !heavy_set + (shift_left 1 v);

      calc_heavy (i+1)
    else ()
  in
  let () = calc_heavy 0 in
  let heavy_set = !heavy_set in

  let the_seeds = (slicer.seeds).(heavy_set) in
  let the_strides = (slicer.strides).(heavy_set) in
  let the_shares = (slicer.shares).(heavy_set) in

  let expected_slice = ref 0 in

  let rec calc_expected i = 
    if i < (Array.length vars_in_order) then
      let var_id = vars_in_order.(i).free_id in
      let value = verdict.(i) in
      expected_slice := the_strides.(var_id) * ((mod) (hash value the_seeds.(var_id)) the_shares.(var_id));
      calc_expected (i+1)
    else ()  
  in    
  let () = calc_expected 0 in

  calc_expected 0 == slice  

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
  let strides = strides seeds dimensions in
  
  { formula = formula; variables_in_order = Array.of_list variables_in_order; heavy = heavy; shares = shares; seeds = seeds; strides = strides; degree = degree }


let rec filter i pos l res =
  if List.length l == 0 then begin
    if pos.(i) > -1 then 
      filter (i+1) pos (List.tl l) (List.hd l :: res)
    else 
      filter (i+1) pos (List.tl l) res  
  end
  else res

let convert_slicing_tuple slicer vars values =
  let vars_in_order = slicer.variables_in_order in
  let str_vars = Array.to_list (Array.map (fun e -> (Predicate.string_of_var e.var)) vars_in_order) in

  let raw_pos = List.map (fun v -> Misc.get_pos_no_e v str_vars) vars in
  let pos = Array.of_list (List.filter (fun e -> e > -1) raw_pos) in

  let tuple = Array.init (Array.length pos) (fun _ -> None) in
  let values = Array.of_list values in 
  Array.iteri (fun i v -> tuple.(i) <- Some (Predicate.cst_of_str vars_in_order.(v).tcst values.(i))) pos;
  tuple