let no_mw = ref false

module Monitor = struct
  type t = {
    fv_pos: int list;
    mutable cur_tp: int;
    mutable cur_ts: MFOTL.timestamp;
    mutable cur_db: Verified_adapter.db;
    mutable cur_state: Verified_adapter.state;
  }

  let begin_tp ctxt ts = ctxt.cur_ts <- ts

  let tuple ctxt s sl =
    ctxt.cur_db <- Verified_adapter.insert_into_db s sl ctxt.cur_db

  let end_tp ctxt =
    let db = ctxt.cur_db in
    ctxt.cur_db <- Verified_adapter.empty_db;
    let (vs, new_state) = Verified_adapter.step ctxt.cur_ts db ctxt.cur_state in
    ctxt.cur_state <- new_state;
    List.iter (fun (q, tsq, rel) ->
      Helper.show_results ctxt.fv_pos ctxt.cur_tp q tsq rel) vs;
    ctxt.cur_tp <- ctxt.cur_tp + 1
end

module P = Simple_log_parser.Make (Monitor)

let monitor dbschema logfile fv f =
  (* compute permutation for output tuples *)
  let fv_pos = List.map snd (Table.get_matches (MFOTL.free_vars f) fv) in
  assert (List.length fv_pos = List.length fv);

  let cf = Verified_adapter.convert_formula dbschema f in
  let cf = if !no_mw then cf else Verified.Monitor.convert_multiway cf in
  let ctxt = Monitor.{
    fv_pos;
    cur_tp = 0;
    cur_ts = MFOTL.ts_invalid;
    cur_db = Verified_adapter.empty_db;
    cur_state = Verified_adapter.init cf;
  } in
  let lexbuf = Log.log_open logfile in
  ignore (P.parse dbschema lexbuf ctxt)
