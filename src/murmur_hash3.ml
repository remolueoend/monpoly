open Pervasives

(* Helper implementations for Int32 *)
let shift_right l r =
  Int32.to_int (Int32.shift_right (Int32.of_int l) r)

let shift_right_logical l r =
  Int32.to_int (Int32.shift_right_logical (Int32.of_int l) r)

let shift_left l r =
  Int32.to_int (Int32.shift_left (Int32.of_int l) r)  

let logand l r =
  Int32.to_int (Int32.logand (Int32.of_int l) (Int32.of_int r))

let logor l r =
  Int32.to_int (Int32.logor (Int32.of_int l) (Int32.of_int r))

let logxor l r = 
  Int32.to_int (Int32.logxor (Int32.of_int l) (Int32.of_int r))

(* Implementation of scala rotate left in Int library *)
let rotate_left i distance =
  logor (shift_left i distance) (shift_right_logical i (-distance))

  
(*
  OCAML Implementation of MurmurHash3 parts relevant for Hypercube slicing
*)

let mix_last hash k =
  let k = k * (int_of_string "0xcc9e2d51") in
  let k = rotate_left k 15 in
  let k = k * (int_of_string "0x1b873593") in
  logxor hash k

let mix hash data =
  let h = mix_last hash data in
  let h = rotate_left h 13 in
  (h * 5 + (int_of_string "0xe6546b64"))

let avalanche hash =
  let h = logxor hash (shift_right_logical hash 16) in
  let h = h * (int_of_string "0x85ebca6b") in
  let h = logxor h (shift_right_logical h 13) in
  let h = h * (int_of_string "0xc2b2ae35") in
  let h = logxor h (shift_right_logical h 16) in
  h

let finalize_hash hash length = avalanche (logxor hash length)

let string_hash str seed =
  let h = seed in 

  let rec hash h i =
    if (i + 1 < String.length str) then 
      let data = (shift_left (int_of_char (String.get str i)) 16) + (int_of_char (String.get str (i + 1))) in
      let h = mix h data in
      hash h (i + 2)
    else h in
  
  finalize_hash (hash h 0) (String.length str)