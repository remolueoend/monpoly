open Murmur_hash3
open Predicate
open MFOTL

type share = int array

type integral_value = int
type string_value   = string

type domain = 
  | Some of cst
  | None

module Domain_Set = Set.Make (
  struct type t = domain
    let compare = Pervasives.compare
  end)

let contains_cst cst ds =
  Domain_Set.exists (fun x -> 
    match x with
    | None -> false
    | Some v -> cst == v
  ) ds

include Domain_Set
type domain_set = Domain_Set.t
type heavy = int * domain_set

type hypercube_slicer = {
  formula: MFOTL.formula;
  heavy:  heavy array;
  shares: share array;
  seed: int
}

let dimensions slicer = List.length (MFOTL.free_vars slicer.formula)

let degree slicer = 
  let simple_shares = slicer.shares.(0) in
  if (Array.length simple_shares == 0) then 1
  else Array.fold_left (fun acc b -> acc * b) 1 simple_shares

let seeds slicer =
  (* TODO: verify how this should be done *)
  let bound = Int32.max_int in
  let () = Random.init slicer.seed in
  Array.init (Array.length slicer.shares) (fun _ -> 
    Array.init (dimensions slicer) (fun _ -> Int32.to_int (Random.int32 bound)))

let strides slicer = 
  let shares = slicer.shares in
  let dims = dimensions slicer in
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

let add_slices_of_valuation slicer valuation slices =
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
    let the_seeds = (seeds slicer).(heavy_set) in
    let the_strides = (strides slicer).(heavy_set) in
    let the_shares = (slicer.shares).(heavy_set) in

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

    let rec broadcast i k =
      if i < 0 then 
        slices := !slices + k
      else begin  
        let value = valuation.(i) in
        match value with 
          | Some cst -> broadcast (i - 1) k
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
    broadcast (Array.length valuation - 1) !slice_index  
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
    add_slices_for_heavy_set !heavy_set
  else 
    cover_unconstrained (shift_left 1 ((Array.length valuation) - 1)) !heavy_set

(* TODO: check ordering *)
let variables_in_order slicer = MFOTL.free_vars slicer.formula

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

  let the_seeds = (seeds slicer).(heavy_set) in
  let the_strides = (strides slicer).(heavy_set) in
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