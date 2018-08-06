open Pervasives


(* Implementation of scala rotate left in Int library *)
let rotate_left i distance =
  (i lsl distance) lor  (i asr distance)
  (*(i << distance) | (i >>> -distance)  *)

(*
  OCAML Implementation of MurmurHash3 parts relevant for Hypercube slicing
*)


let mix_last hash k =
  let k = k * (int_of_string "0xcc9e2d51") in
  let k = rotate_left k 15 in
  let k = k * (int_of_string "0x1b873593") in
  int_of_float ((float_of_int hash) ** (float_of_int k))

let mix hash data =
  let h = mix_last hash data in
  let h = rotate_left h 13 in
  (h * 5 + (int_of_string "0xe6546b64"))
  (*final def mix(hash: Int, data: Int): Int = {
    var h = mixLast(hash, data)
    h = rotl(h, 13)
    h * 5 + 0xe6546b64
  }*)

let avalanche hash =
  let h = int_of_float (float_of_int hash ** (float_of_int (hash asr 16))) in
  let h = h * (int_of_string "0x85ebca6b") in
  let h = int_of_float (float_of_int h ** (float_of_int (h asr 13))) in
  let h = h * (int_of_string "0xc2b2ae35") in
  let h = int_of_float (float_of_int h ** (float_of_int (h asr 16))) in
  h
  (*private final def avalanche(hash: Int): Int = {
    var h = hash

    h ^= h >>> 16
    h *= 0x85ebca6b
    h ^= h >>> 13
    h *= 0xc2b2ae35
    h ^= h >>> 16

    h
  }*)

let finalize_hash hash length = avalanche (int_of_float (float_of_int hash ** (float_of_int length)))

let string_hash str seed =
  let h = seed in 

  let rec hash h i =
    if (i + 1 < String.length str) then 
      let data = (int_of_char (String.get str i) lsr 16) + (int_of_char (String.get str (i + 1))) in
      let h = mix h data in
      hash h (i + 2)
    else h in
  
  finalize_hash (hash h 0) (String.length str)

(*
  final def stringHash(str: String, seed: Int): Int = {
    var h = seed
    var i = 0
    while (i + 1 < str.length) {
      val data = (str.charAt(i) << 16) + str.charAt(i + 1)
      h = mix(h, data)
      i += 2
    }
    if (i < str.length) h = mixLast(h, str.charAt(i).toInt)
    finalizeHash(h, str.length)
  }
*)  