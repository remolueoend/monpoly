open Murmur_hash3
open MFOTL

type share = int array

type integral_value = int
type string_value   = string

type domain = 
  | IntegralValue of integral_value
  | StringValue   of string_value

module Domain_Set = Set.Make (
  struct type t = domain
    let compare = Pervasives.compare
  end)

include Domain_Set

type domain_set = Domain_Set.t

type heavy = int * domain_set

type hypercube_slicer = {
  formula: MFOTL.formula;
  heavy:  heavy array;
  shares: share array;
  seed: int
}

let degree slicer = 
  let simple_shares = slicer.shares.(0) in
  if (Array.length simple_shares == 0) then 1
  else Array.fold_left (fun acc b -> acc * b) 1 simple_shares

let dimensions slicer = List.length (MFOTL.free_vars slicer.formula)

let variables_in_order slicer = MFOTL.free_vars slicer.formula

let hash value seed = match value with
  | IntegralValue x ->
    let lo = x in
    let hi = x lsr 32 in
    Murmur_hash3.finalize_hash (Murmur_hash3.mix_last (Murmur_hash3.mix seed lo) hi) 0
  | StringValue   x -> Murmur_hash3.string_hash x seed


let seeds slicer =
  let () = Random.init slicer.seed in
  Array.init (Array.length slicer.shares) (fun _ -> 
   (* TODO: which int to use *)
    Array.init (dimensions slicer) (fun _ -> Random.int (int_of_float (2. ** 30.))))

let strides slicer = 
  let shares = slicer.shares in
  let dims = dimensions slicer in
  let strides = Array.init (Array.length shares) 
      (fun _ -> Array.init dims (fun _ -> 1))
  in
  let rec update s h i = 
    if i < dims then begin
      let () = s.(i) <- s.(i - 1) * shares.(h).(i - 1) in
      update s h (i+1)
    end
    else ()
  in
  let () = Array.iteri (fun h s -> update s h 1) strides in
  strides

let add_slices_of_valuation slicer valuation slices =
  let heavy_set = ref 0 in
  let unconstrained_set = ref 0 in

  let heavy = slicer.heavy in
  
  let rec calc_heavy i = 
    if i < Array.length valuation then
      (*let var_id = free_id vars_in_order.(i)  in *)
      let i, s = heavy.(i) in
      if (i >= 0) then
        let value = valuation.(i) in
        (* TODO: conditions *)
        if (value == value) then
          unconstrained_set := !unconstrained_set + (1 lsl i);  
        else if (0 == 0) then
          heavy_set := !heavy_set + (1 lsl i);
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
        (*let var_id = free_id vars_in_order.(i)  in *)
        let value = valuation.(i) in
        slice_index := the_strides.(i) * ((mod) (hash value the_seeds.(i)) the_shares.(i));
        calc_slice (i+1)
      else ()  
    in     
    let () = calc_slice 0 in

    let rec broadcast i k =
      if i < 0 then 
        slices := !slices + k
      else begin  
        let value = valuation.(i) in
        if (value == value) then begin
          let rec iterate j =
            if (j < the_shares.(i)) then begin
              broadcast (i - 1) (k + the_strides.(i) * j);
              iterate (j + 1)
            end   
            else ()
           in  
           iterate 0 
          end   
        else 
          broadcast (i - 1) k
      end  
    in
    broadcast (Array.length valuation - 1) !slice_index  
  in

  let rec cover_unconstrained m h =
    if (h == 0) then add_slices_for_heavy_set h
    else begin
      if (!unconstrained_set land m != 0) then
        cover_unconstrained (m lsr 1) (h lor m)
      else cover_unconstrained (m lsr 1) h  
    end   
  in
  if (Array.length valuation == 0) then
    add_slices_for_heavy_set !heavy_set
  else 
    cover_unconstrained (1 lsr ((Array.length valuation) - 1)) !heavy_set

let mk_verdict_filter slicer slice verdict =
  let heavy_set = ref 0 in
  let vars_in_order = variables_in_order slicer in
  let vars_in_order = Array.init (List.length vars_in_order) (fun _ -> List.hd vars_in_order) in
  let rec calc_heavy i = 
    if i < Array.length vars_in_order then
      (*let var_id = free_id vars_in_order.(i)  in *)
      let var_id = i in
      let value = verdict.(i) in
      let heavyMap = slicer.heavy.(var_id) in
    
      let i, s = heavyMap in
      if (i >= 0 && (Domain_Set.exists (fun e -> e = value) s)) then
        heavy_set := !heavy_set + (1 lsl i);

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