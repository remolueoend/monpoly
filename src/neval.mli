(** The neval ("not yet evaluated") queue keeps track of timepoint-timestamp
    pairs that are still needed by the evaluation algorithm.

    The queue is mutable but append-only. There is no pop or remove operation.
    Instead, there can be many "heads" pointing to different cells in the same
    queue. Using the heads, one can move efficiently from one cell to the next.
    Every head belongs to a unique queue.

    The queue is implemented as a singly linked list with mutable references.
    Cells that are no longer referenced (directly or indirectly from some
    predecessor) are collected by the garbage collector. *)

type cell (** Reference to a cell ("head"). *)
type queue (** Reference to the queue ("tail"). *)

val create: unit -> queue
(** Create a new queue, which is initialized with a single invalid cell. *)

val get_last: queue -> cell
(** Return the last cell in the queue, which is never empty. *)

val prepend: int * MFOTL.timestamp -> cell -> cell
(** [prepend p c] inserts a new cell storing the pair [p] before the cell [c].
    Note that this only has the intended behavior if no reference to cells
    before [c] remains. Otherwise, the new cell is not reachable from those. *)

val insert_after: int * MFOTL.timestamp -> cell -> cell
(** [insert_after p c] inserts a new cell storing the pair [p] after the cell
    [c]. Returns the new cell. *)

val append: int * MFOTL.timestamp -> queue -> cell
(** [append p q] adds the pair [p] to the end of the queue. It is equivalent to
    [insert_after p (get_last q)]. *)

val is_last: cell -> bool
(** Test whether a cell is currently the last cell in the queue that it belongs
    to. The result changes from [true] to [false] after [append]ing to the
    queue. *)

val is_valid: cell -> bool
(** Test whether a cell contains a valid timepoint. *)

val get_data: cell -> int * MFOTL.timestamp
(** Return the pair stored in the cell. *)

val get_next: cell -> cell
(** [get_next c] returns a reference to the next cell after [c].
    Precondition: [not (is_last c)]. *)

val string_of_cell: cell -> string
(** Format the cell's content. *)
