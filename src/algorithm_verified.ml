let no_mw = ref false

module IntMap = Map.Make(struct type t = int let compare = Stdlib.compare end)

module Monitor = struct
  type ctxt = {
    c_fv_pos: int list;
    mutable c_tp: int;
    mutable c_tpts: MFOTL.timestamp IntMap.t;
    mutable c_ts: MFOTL.timestamp;
    mutable c_vst: Verified_adapter.state;
  }

  let begin_tp c ts =
    c.c_ts <- ts;
    c.c_tpts <- IntMap.add c.c_tp ts c.c_tpts

  let observe c e t =
    c.c_vst <- Verified_adapter.observe e t c.c_vst

  let end_tp c =
    let (vs, new_state) = Verified_adapter.conclude c.c_ts c.c_vst in
    List.iter (fun (qtp, rel) ->
        let qts = IntMap.find qtp c.c_tpts in
        if qts < MFOTL.ts_max then
          Helper.show_results c.c_fv_pos c.c_tp qtp qts rel
      ) vs;
    c.c_tpts <- List.fold_left (fun m (qtp,_) -> IntMap.remove qtp m) c.c_tpts vs;
    c.c_vst <- new_state;
    c.c_tp <- c.c_tp + 1
end

module P = Simple_log_parser.Make (Monitor)

let monitor dbschema logfile fv f =
  (* compute permutation for output tuples *)
  let fv_pos = List.map snd (Table.get_matches (MFOTL.free_vars f) fv) in
  assert (List.length fv_pos = List.length fv);

  let cf = Verified_adapter.convert_formula dbschema f in
  let cf = if !no_mw then cf else Verified.Monitor.convert_multiway cf in
  let ctxt = Monitor.{
    c_fv_pos = fv_pos;
    c_tp = 0;
    c_tpts = IntMap.empty;
    c_ts = MFOTL.ts_invalid;
    c_vst = Verified_adapter.init cf;
  } in
  let lexbuf = Log.log_open logfile in
  ignore (P.parse dbschema lexbuf ctxt)
