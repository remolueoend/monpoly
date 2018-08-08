open Murmur_hash3
open Predicate
open Helper
open Tuple
open Mformula


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

type share = int array

type integral_value = int
type string_value   = string

type split_resume_parameters = (string * heavy array * int array array * int array array)

type hypercube_slicer = {
  formula: mformula;
  heavy:  heavy array;
  shares: int array array;
  seeds: int array array;
  strides: int array array;
  degree: int;
}

let contains_cst cst ds =
  Domain_Set.exists (fun x -> 
    match x with
    | None -> false
    | Some v -> cst_eq cst v
  ) ds

let dimensions formula = List.length (Mformula.free_vars formula)

let degree shares = 
  let simple_shares = shares.(0) in
  if (Array.length simple_shares == 0) then 1
  else Array.fold_left (fun acc b -> acc * b) 1 simple_shares

(*let seeds slicer =
  (* Now passed as parameter *)
  let bound = Int32.max_int in
  let () = Random.init slicer.seed in
  Array.init (Array.length slicer.shares) (fun _ -> 
    Array.init (dimensions slicer) (fun _ -> Int32.to_int (Random.int32 bound)))*)

let strides shares dimensions = 
  let shares = shares in
  let dims = dimensions in
  let strides = Array.init (Array.length shares) 
      (fun _ -> Array.init dims (fun _ -> 1))
  in
  (*let rec update s h i = 
    if i < dims then begin
      let () = s.(i) <- s.(i - 1) * shares.(h).(i - 1) in
      update s h (i+1)
    end
    else ()
  in*)
  let () = Array.iteri (
    fun h s -> for i = 1 to dims do s.(i) <- s.(i - 1) * shares.(h).(i - 1) done
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

let add_slices_of_valuation slicer tuple free_vars =
  (*let slices = Slice_Set.empty in*)
  let slices = [] in
  let tuple = Array.of_list tuple in

  let free_vars_full = variables_in_order slicer in

  let valuation = Array.init (List.length free_vars_full) (fun _ -> None) in

  (* TODO: mapping of vars to vars_full *)
  let pos     = Array.of_list (List.map (fun v -> Misc.get_pos v free_vars_full ) free_vars) in
  Array.iteri (fun i e -> valuation.(pos.(i)) <- Some e ) tuple;


  let heavy_set = ref 0 in
  let unconstrained_set = ref 0 in

  let heavy = slicer.heavy in
  
  let rec calc_heavy i = 
    if i < Array.length valuation then
      (*
      TODO: check this
      let var_id = free_id vars_in_order.(i)  in *)
      let v, s = heavy.(i) in
      if (v >= 0) then
        let value = valuation.(i) in
        match value with 
          | None     -> unconstrained_set := !unconstrained_set + (shift_left 1 v);
          | Some cst -> 
            if contains_cst cst s then 
               heavy_set := !heavy_set + (shift_left 1 v);
      calc_heavy (i+1)
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
        (*
        TODO: check this
        let var_id = free_id vars_in_order.(i)  in *)
        let value = valuation.(i) in
        match value with 
          | Some v -> slice_index := the_strides.(i) * ((mod) (hash v the_seeds.(i)) the_shares.(i));
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

  if (Array.length valuation == 0) then
    Array.of_list (add_slices_for_heavy_set !heavy_set)
  else 
    Array.of_list (cover_unconstrained (shift_left 1 ((Array.length valuation) - 1)) !heavy_set)

let mk_verdict_filter slicer slice verdict =
  let heavy_set = ref 0 in
  let vars_in_order = variables_in_order slicer in
  let vars_in_order = Array.init (List.length vars_in_order) (fun _ -> List.hd vars_in_order) in
  let rec calc_heavy i = 
    if i < Array.length vars_in_order then
      (*
      TODO: check this
      let var_id = free_id vars_in_order.(i)  in *)
      let var_id = i in
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
      (*let var_id = free_id vars_in_order.(i)  in *)
      let var_id = i in
      let value = verdict.(i) in
      expected_slice := the_strides.(var_id) * ((mod) (hash value the_seeds.(var_id)) the_shares.(var_id));
      calc_expected (i+1)
    else ()  
  in    
  let () = calc_expected 0 in

  calc_expected 0 == slice  

let create_slicer formula heavy shares seeds =
  let degree = degree shares in
  let dimensions = dimensions formula in  
  let strides = strides seeds dimensions in
  
  { formula = formula; heavy = heavy; shares = shares; seeds = seeds; strides = strides; degree = degree }