type cell = {
  tp: int;
  ts: MFOTL.timestamp;
  mutable next: cell;
}

type queue = cell
(* The purpose of this hack is that [insert_after] works also for the last cell
   without needing the queue itself, and without storing the queue in the cells.
   For a value [q] of type queue, [q.next] points to the last proper cell. *)

let create () =
  let rec c = {tp = -1; ts = MFOTL.ts_invalid; next = q}
  and q = {tp = -2; ts = MFOTL.ts_invalid; next = c} in q

let is_sentinel c = (c.tp = -2)

let get_last q = q.next

let prepend (tp, ts) c = {tp = tp; ts = ts; next = c}

let insert_after (tp, ts) c1 =
  let c3 = c1.next in
  let c2 = {tp = tp; ts = ts; next = c3} in
  c1.next <- c2;
  if is_sentinel c3 then c3.next <- c2; (* adjust queue tail reference *)
  c2

let append p q = insert_after p (get_last q)

let is_last c = is_sentinel (c.next)

let is_valid c = (c.tp >= 0)

let get_data c = (c.tp, c.ts)

let get_next c =
  assert (not (is_last c));
  c.next

let string_of_cell c = if c.tp < 0 then "<none>" else
  Printf.sprintf "(%d,%s)" c.tp (MFOTL.string_of_ts c.ts)
