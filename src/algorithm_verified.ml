open MFOTL
open Verified_adapter

let no_mw = ref false

let rec show_results closed i q tsq rel =
  if !Misc.stop_at_first_viol && Relation.cardinal rel > 1 then
    let rel2 = Relation.singleton (Relation.choose rel) in
    show_results closed i q tsq rel2
  else if !Misc.verbose then
    if closed then
      Printf.printf "@%s (time point %d): %b\n%!"
        (MFOTL.string_of_ts tsq) q (rel <> Relation.empty)
    else
      begin
        Printf.printf "@%s (time point %d): " (MFOTL.string_of_ts tsq) q;
        Relation.print_reln "" rel
      end
  else
    begin
      if Misc.debugging Dbg_perf then
        Perf.show_results q tsq;
      if rel <> Relation.empty then (* formula satisfied *)
        if closed then (* no free variables *)
          Printf.printf "@%s (time point %d): true\n%!" (MFOTL.string_of_ts tsq) q
        else (* free variables *)
          begin
            Printf.printf "@%s (time point %d): " (MFOTL.string_of_ts tsq) q;
            Relation.print_rel4 "" rel;
            print_newline()
          end
    end


module IntMap = Map.Make(struct type t = int let compare = Pervasives.compare end)
open IntMap

let monitor logfile f =
  let closed = (free_vars f = []) in
  let cf = convert_formula f in
  let cf = if !no_mw then cf else Verified.Monitor.convert_multiway_e cf in
  let init_state = Verified.Monitor.minit_safe cf in
  let lexbuf = Log.log_open logfile in
  let init_i = 0 in
  let init_ts = MFOTL.ts_invalid in
  let rec loop state tpts tp ts =
    let finish () =
      if Misc.debugging Dbg_perf then
        Perf.check_log_end tp ts
    in
    if Misc.debugging Dbg_perf then
      Perf.check_log tp ts;
    match Log.get_next_entry lexbuf with
    | MonpolyCommand {c; parameters} -> finish ()
    | MonpolyTestTuple st -> finish ()
    | MonpolyError s -> finish ()
    | MonpolyData d ->
    if d.ts >= ts then
      (* let _ = Printf.printf "Last: %b TS: %f TP: %d !Log.TP: %d d.TP: %d\n" !Log.last d.ts tp !Log.tp d.tp in *)
      let tpts = add d.tp d.ts tpts in
      let (vs, new_state) = Verified.Monitor.mstep (convert_db d) state in
      let vs = convert_violations vs in
      List.iter (fun (qtp, rel) -> show_results closed d.tp qtp (find qtp tpts) rel) vs;
      let tpts = List.fold_left (fun map (qtp,_) -> remove qtp map) tpts vs in
      loop new_state tpts d.tp d.ts
    else
      if !Misc.stop_at_out_of_order_ts then
        let msg = Printf.sprintf "[Algorithm.check_log] Error: OUT OF ORDER TIMESTAMP: %s \
                                  (last_ts: %s)" (MFOTL.string_of_ts d.ts) (MFOTL.string_of_ts ts) in
        failwith msg
      else
        let _ = Printf.eprintf "[Algorithm.check_log] skipping OUT OF ORDER TIMESTAMP: %s \
                          (last_ts: %s)\n%!" (MFOTL.string_of_ts d.ts) (MFOTL.string_of_ts ts) in
        loop state tpts tp ts
  in
  loop init_state empty init_i init_ts
