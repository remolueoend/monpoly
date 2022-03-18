open Stdlib
exception Error of string

(* Helper implementations for Int32 *)
let shift_right l r =
  if r < 0 then
    raise (Error "[shift_right] r must be positive")
  else
    Int32.to_int (Int32.shift_right (Int32.of_int l) r)

let shift_right_logical l r =
  if r < 0 then
    raise (Error "[shift_right_logical] r must be positive")
  else
    Int32.to_int (Int32.shift_right_logical (Int32.of_int l) r)

let shift_left l r =
  if r < 0 then
    raise (Error "[shift_left] r must be positive")
  else
    Int32.to_int (Int32.shift_left (Int32.of_int l) r)

let logand l r =
  Int32.to_int (Int32.logand (Int32.of_int l) (Int32.of_int r))

let logor l r =
  Int32.to_int (Int32.logor (Int32.of_int l) (Int32.of_int r))

let logxor l r = 
  Int32.to_int (Int32.logxor (Int32.of_int l) (Int32.of_int r))

(* Implementation of scala rotate left in Int library *)
let rotate_left i distance =
  if distance < 0 then
    raise (Error "[rotate_left] distance must be positive")
  else begin
    let left = (Int32.shift_left i distance) in
    let shift_right = 32 - distance in
    let right = Int32.shift_right_logical i shift_right in
    let res = Int32.logor left right in
    res
  end
  
(*
  OCAML Implementation of MurmurHash3 parts relevant for Hypercube slicing
*)
let mix_last hash k =
  (*Printf.printf "Mix last inputs: %d %d \n" (Int32.to_int hash) (Int32.to_int k);*)
  let k = Int32.mul k 0xcc9e2d51l in
  let k = rotate_left k 15 in
  let k = Int32.mul k 0x1b873593l in
  let res = Int32.logxor hash k in
  (*Printf.printf "Mix last res: %d \n" (Int32.to_int res);*)
  res

let mix32 hash data =
  (*Printf.printf "Mix inputs: %d %d \n" (Int32.to_int hash) (Int32.to_int data);*)
  let h = mix_last hash data in
  let h = rotate_left h 13 in
  let res = (Int32.add (Int32.mul h 5l) 0xe6546b64l) in
  (*Printf.printf "Mix res: %d \n" (Int32.to_int res);*)
  res

let mix h d = mix32 (Int32.of_int h) (Int32.of_int d)

let avalanche hash =
  (*Printf.printf "Avalanche input: %d \n" (Int32.to_int hash);*)
  let h = Int32.logxor hash (Int32.shift_right_logical hash 16) in
  let h = Int32.mul h 0x85ebca6bl in
  let h = Int32.logxor h (Int32.shift_right_logical h 13) in
  let h = Int32.mul h 0xc2b2ae35l in
  let h = Int32.logxor h (Int32.shift_right_logical h 16) in
  (*Printf.printf "Avalanche ouput: %d \n" (Int32.to_int h);*)
  h

let finalize_hash hash length = 
  (*Printf.printf "Finalize hash inputs: %d %d \n" (Int32.to_int hash) length;*)
  let res = avalanche (Int32.logxor hash (Int32.of_int length)) in
  (*Printf.printf "Finalize hash output: %d \n" (Int32.to_int res);*)
  res

let string_hash str seed =
  let h = seed in 

  let rec hash h i =
    if (i + 1 < String.length str) then 
      let data = Int32.of_int ((shift_left (int_of_char (String.get str i)) 16) + (int_of_char (String.get str (i + 1)))) in
      let h = mix32 h data in
      hash h (i + 2)
    else h, i in
  let hash_res, i = (hash h 0) in
  let h =
  if(i < String.length str) then
    mix_last hash_res (Int32.of_int (int_of_char (String.get str i)))
  else 
    hash_res
  in
  let res = finalize_hash h (String.length str) in
  res
