open MFOTL
open Db

type split = { key: string; lvalues: string list; rvalues: string list }

type dataTuple    = { ts: MFOTL.timestamp; db: Db.db; }
type commandTuple = { c: string; split: split option; }

type parser_feed =
    | CommandTuple of commandTuple
    | DataTuple    of dataTuple
    | ErrorTuple   of string

type monpolyData    = { tp: int; ts: MFOTL.timestamp; db: Db.db; }
type monpolyCommand = { c: string; split: split option}


type monpoly_feed =
    | MonpolyCommand of commandTuple
    | MonpolyData    of monpolyData
    | MonpolyError   of string