open Libmonpoly
open Predicate

let rep_map size1 size2 =
  if size1 * size2 < 1024 then 1000
  else if size1 * size2 < 65536 then 200
  else 40

let sizes = [2; 4; 8; 16; 32; 64; 256; 512]
let configs =
  [[0; 1], 1, [0; 2], 1;
   [0; 1], 1, [2; 0], 0;
   [1; 0], 0, [0; 2], 1;
   [1; 0], 0, [2; 0], 0;
   [0; 1], 1, [0; 2; 3], 2;
   [3; 0; 2], 0, [0; 1], 1;
   [0; 1; 2], 1, [2; 0; 3], 2]

let make_rel perm dupidx nmax n =
  let a = List.length perm in
  let off = Array.of_list (List.map (fun k -> k * nmax) perm) in
  let make_cst i j =
    let x = if j = dupidx then i else i / 2 in
    Int (Z.of_int (off.(j) + x))
  in
  let make_tuple i = List.init a (make_cst i) in
  let tl = List.init n make_tuple in
  Relation.make_relation tl

let time_join reps f =
  let relj = Array.make reps Relation.empty in
  let starttime = Sys.time () in
  for r = 0 to reps-1 do
    relj.(r) <- f()
  done;
  let endtime = Sys.time () in
  let card0 = Relation.cardinal relj.(0) in
  for r = 1 to reps-1 do
    if Relation.cardinal relj.(r) <> card0 then
      failwith "[time_join] nondeterministic result"
  done;
  relj.(0), ((endtime -. starttime) /. float_of_int reps) *. 1000.

let compare_join_impls reps matches card1 rel1 card2 rel2 =
  let rel_nlj, time_nlj = time_join reps (fun () ->
    Relation.nested_loop_join matches rel1 rel2) in
  let rel_hj, time_hj = time_join reps (fun () ->
    Relation.hash_join_with_cards matches card1 rel1 card2 rel2) in
  if not (Relation.equal rel_nlj rel_hj) then
    begin
      Printf.printf "*** Test failure ***\n";
      Printf.printf "rel1:\n";
      Relation.print_bigrel rel1;
      Printf.printf "rel2:\n";
      Relation.print_bigrel rel2;
      Printf.printf "result (nested loop join):\n";
      Relation.print_bigrel rel_nlj;
      Printf.printf "result (hash join):\n";
      Relation.print_bigrel rel_hj;
      Printf.printf "*** Test failure ***\n";
      exit 1
    end;
  time_nlj, time_hj

let matches_of_perms perm1 perm2 =
  let rec go pos2 = function
    | k::kl -> 
        (try
          let pos1 = Misc.get_pos k perm1 in
          (pos2, pos1) :: go (pos2+1) kl
        with Not_found -> go (pos2+1) kl)
    | [] -> []
  in
  go 0 perm2

let test_join_config i (perm1, dupidx1, perm2, dupidx2) =
  let matches = matches_of_perms perm1 perm2 in
  let nmax = List.fold_left max 1 sizes in
  List.iter (fun size1 ->
    let rel1 = make_rel perm1 dupidx1 nmax size1 in
    List.iter (fun size2 ->
      let rel2 = make_rel perm2 dupidx2 nmax size2 in
      let reps = rep_map size1 size2 in
      let nlj, hj = compare_join_impls reps matches size1 rel1 size2 rel2 in
      Printf.printf "%d,%d,%d,%.3f,%.3f\n" i size1 size2 nlj hj
    )
    sizes
  )
  sizes

let test_join_configs () = List.iteri test_join_config configs

let _ = test_join_configs()
