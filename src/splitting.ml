open Dllist
open Misc
open Predicate
open MFOTL
open Tuple
open Relation
open Log
open Sliding
open Helper
open Extformula
open Marshalling
open Mformula

type state = (int * timestamp * bool * mformula * (int * timestamp) array * int * int * bool)

exception Type_error of string

(* SPLITTING & COMBINING STATE *)

let rel_u r1 r2 = Relation.union r1 r2

let combine_queues1 q1 q2 =  
  let tmp = Queue.create() in
  let nq = Queue.create() in
  Queue.iter (fun e ->
    let i, ts, r1 = e in
    let _, _,  r2 = Queue.pop q2 in
    Queue.add (i, ts, (rel_u r1 r2)) tmp;
  ) q1;
  (* Need to reverse the queue *)
  Queue.iter (fun _ -> Queue.add (Queue.pop tmp) nq) tmp;
  nq

let combine_queues2 q1 q2 =  
  let tmp = Queue.create() in
  let nq = Queue.create() in
  Queue.iter (fun e ->
    let ts, r1 = e in
    let _,  r2 = Queue.pop q2 in
    Queue.add (ts, (rel_u r1 r2)) tmp;
  ) q1;
  (* Need to reverse the queue *)
  Queue.iter (fun _ -> Queue.add (Queue.pop tmp) nq) tmp;
  nq

let combine_mq q1 q2 =
  Mqueue.update (fun e ->
  let ts, r1  = e in
  let _,  r2  = Mqueue.pop q2 in (ts, (rel_u r1 r2))) q1;
  q1

let combine_dll1 l1 l2 =  
  let res = Dllist.empty() in
    Dllist.iter (fun e ->
      let i, ts, r1 = e in
      let _, _,  r2 = Dllist.pop_first l2 in
      Dllist.add_last (i, ts, (rel_u r1 r2)) res
    ) l1;
    res

let combine_dll2 l1 l2 =  
  let res = Dllist.empty() in
    Dllist.iter (fun e ->
      let ts, r1 = e in
      let _,  r2 = Dllist.pop_first l2 in
      Dllist.add_last (ts, (rel_u r1 r2)) res
    ) l1;
    res   

let combine_info  inf1 inf2 =
  combine_queues1 inf1 inf2

let combine_ainfo ainf1 ainf2 =
  let urel = match (ainf1.arel, ainf2.arel) with
  | (Some r1, Some r2) -> Some (rel_u r1 r2)
  | (None, None) -> None
  | _ -> raise (Type_error ("Mismatched states in ainfo"))
  in
  { arel = urel; }

let combine_agg  agg1 agg2 =
  let other_rels = combine_queues2 agg1.other_rels agg2.other_rels in
  {tw_rels = agg1.tw_rels; other_rels = other_rels; mset = agg1.mset; hres = agg1.hres }

let combine_aggMM agg1 agg2 =
  let non_tw_rels = combine_queues2 agg1.non_tw_rels agg2.non_tw_rels in
  {non_tw_rels = non_tw_rels; tbl = agg1.tbl }

let combine_sainfo sainf1 sainf2 =
  let sarel2 = match (sainf1.sarel2, sainf2.sarel2) with
  | (Some r1, Some r2) -> Some (rel_u r1 r2)
  | (None, None) -> None
  | _ -> raise (Type_error ("Mismatched states in ainfo"))
  in
  (* Verify correctness *)
  let saauxrels = combine_mq sainf1.saauxrels sainf2.saauxrels in
  {sres = (rel_u sainf1.sres sainf2.sres); sarel2 = sarel2; saauxrels = saauxrels}

let combine_sinfo sinf1 sinf2  =
  let srel2 = match (sinf1.srel2, sinf2.srel2) with
  | (Some r1, Some r2) -> Some (rel_u r1 r2)
  | (None, None) -> None
  | _ -> raise (Type_error ("Mismatched states in ainfo"))
  in
  (* Verify correctness *)
  let sauxrels = combine_mq sinf1.sauxrels sinf2.sauxrels in
  {srel2 = srel2; sauxrels = sauxrels}

let combine_muninfo uninf1 uninf2 =
    (* Verify correctness *)
  let listrel1 = combine_dll1 uninf1.listrel1 uninf2.listrel1 in 
  let listrel2 = combine_dll1 uninf1.listrel2 uninf2.listrel2 in 
  { last1 = uninf1.last1; last2 = uninf1.last2; listrel1 = listrel1;  listrel2 = listrel2 }

let combine_muinfo uinf1 uinf2 =
  (* Helper function to combine raux and saux fields *)
  let sklist l1 l2 =
    let nl = Sk.empty() in
    Sk.iter (fun e ->
      let i, r1 = e in
      (* Verify correctness *)
      let _, r2 = Sk.pop_first l2 in
      Sk.add_last (i, (rel_u r1 r2)) nl
    ) l1;
    nl
  in
  let raux =
    let nl = Sj.empty() in
    Sj.iter (fun e ->
      let (i, ts, l1) = e in
      let (_, _,  l2) = Sj.pop_first uinf2.raux in
      Sj.add_last (i, ts, (sklist l1 l2)) nl
    ) uinf1.raux;
    nl
  in
  let urel2 = match (uinf1.urel2, uinf2.urel2) with
  | (Some r1, Some r2) -> Some (rel_u r1 r2)
  | (None, None) -> None
  | _ -> raise (Type_error ("Mismatched states in ainfo"))
  in
  { ulast = uinf1.ulast; ufirst = uinf1.ufirst; ures = (rel_u uinf1.ures uinf2.ures);
    urel2 = urel2; raux = raux; saux = (sklist uinf1.saux uinf2.saux) }

let combine_ozinfo ozinf1 ozinf2 =
  (* Discuss this at meeting *)

  (* Need to get index, and get cell for that index on new combined auxrels
     Would work better with mformula, however that might have issues with neval indices for different reasons
    *)
  let index = Dllist.get_index ozinf1.ozlast ozinf1.ozauxrels in
  let ozauxrels = combine_dll1 ozinf1.ozauxrels ozinf2.ozauxrels in
  let ozlast = Dllist.get_cell_at_index index ozauxrels in

  (*Should this be done on each union or rather at the end? *)
  let f = fun (j,_,rel) -> (j,rel) in
  let tree_list = Helper.convert_dll ozauxrels Dllist.void f in 
  {oztree = Sliding.build_rl_tree_from_seq Relation.union tree_list; ozlast = ozlast; ozauxrels = ozauxrels }

let combine_oainfo oainf1 oainf2 =
  let oaauxrels = combine_mq oainf1.oaauxrels oainf2.oaauxrels in
  { ores = (rel_u oainf1.ores oainf2.ores); oaauxrels = oaauxrels }
  
let combine_oinfo oinf1 oinf2 =
  (* Verify, see combine_ozinfo *)
  let index = Dllist.get_index oinf1.olast oinf1.oauxrels in
  let oauxrels = combine_dll2 oinf1.oauxrels oinf2.oauxrels in
  let olast = Dllist.get_cell_at_index index oauxrels in

  let tree_list = Helper.convert_dll oauxrels Dllist.void (fun x -> x) in 
  {otree = Sliding.build_rl_tree_from_seq Relation.union tree_list; olast = olast; oauxrels = oauxrels }

let combine_ezinfo ezinf1 ezinf2 =
  (* Verify, see combine_ozinfo *)
  let index = Dllist.get_index ezinf1.ezlast ezinf2.ezauxrels in
  let ezauxrels = combine_dll1 ezinf1.ezauxrels ezinf2.ezauxrels in
  let ezlast = Dllist.get_cell_at_index index ezauxrels in

  let f = fun (j,_,rel) -> (j,rel) in
  let tree_list = Helper.convert_dll ezauxrels Dllist.void f in 
  {ezlastev = ezinf1.ezlastev; eztree = Sliding.build_rl_tree_from_seq Relation.union tree_list; ezlast = ezlast; ezauxrels = ezauxrels }

let combine_einfo einf1 einf2 =
   (* Verify, see combine_ozinfo *)
   let index = Dllist.get_index einf1.elast einf2.eauxrels in
   let eauxrels = combine_dll2 einf1.eauxrels einf2.eauxrels in
   let elast = Dllist.get_cell_at_index index eauxrels in
 
   let tree_list = Helper.convert_dll eauxrels Dllist.void (fun x -> x) in 
  {elastev = einf1.elastev; etree = Sliding.build_rl_tree_from_seq Relation.union tree_list; elast = elast; eauxrels = eauxrels }

let rec comb_e f1 f2  =
  match (f1,f2) with
    | (ERel  (rel1),          ERel(rel2))
      -> ERel (Relation.union rel1 rel2)
    | (EPred (p, comp, inf1), EPred(_, _, inf2))
      -> EPred(p, comp, combine_info inf1 inf2)
    | (ENeg  (f11), ENeg(f21))
      -> ENeg (comb_e f11 f21)
    | (EAnd  (c, f11, f12, ainf1), EAnd(_, f21, f22, ainf2))
      -> EAnd (c, comb_e f11 f21, comb_e f12 f22, (combine_ainfo ainf1 ainf2))
    | (EOr   (c, f11, f12, ainf1), EOr (_, f21, f22, ainf2))
      -> EOr  (c, comb_e f11 f21, comb_e f12 f22, (combine_ainfo ainf1 ainf2))
    | (EExists (c, f11), EExists(_,f21))
      -> EExists        (c, comb_e f11 f21)
    | (EAggreg (c, f11), EAggreg(_,f21))
      -> EAggreg        (c, comb_e f11 f21)
    | (EAggOnce (f11, dt, agg1, update_old, update_new, get_result), EAggOnce (f21, _, agg2, _, _, _))
      -> EAggOnce  (comb_e f11 f21, dt, combine_agg agg1 agg2, update_old, update_new, get_result)
    | (EAggMMOnce (f11, dt, aggMM1, update_old, update_new, get_result), EAggMMOnce (f21, _, aggMM2, _, _, _))
      -> EAggMMOnce (comb_e f11 f21, dt, combine_aggMM aggMM1 aggMM2, update_old, update_new, get_result)
    | (EPrev (dt, f11, pinf1), EPrev ( _, f21, pinf2))
      -> EPrev          (dt, comb_e f11 f21, pinf1)
    | (ENext (dt, f11, ninf1), ENext ( _, f21, ninf2))
      -> ENext          (dt, comb_e f11 f21, ninf1)
    | (ESinceA (c2, dt, f11, f12, sainf1), ESinceA( _, _, f21, f22, sainf2))
      -> ESinceA        (c2, dt, comb_e f11 f21, comb_e f12 f22, combine_sainfo sainf1 sainf2)
    | (ESince (c2, dt, f11, f12, sinf1), ESince( _, _, f21, f22, sinf2))
      -> ESince         (c2, dt, comb_e f11 f21, comb_e f12 f22, combine_sinfo sinf1 sinf2)
    | (EOnceA (dt, f11, oainf1), EOnceA ( _, f21, oainf2))
      -> EOnceA         (dt, comb_e f11 f21, combine_oainfo oainf1 oainf2)
    | (EOnceZ (dt, f11, ozinf1), EOnceZ ( _, f21, ozinf2))
      -> EOnceZ         (dt, comb_e f11 f21, combine_ozinfo ozinf1 ozinf2)
    | (EOnce (dt, f11, oinf1), EOnce ( _, f21, oinf2))
      -> EOnce        (dt, comb_e f11 f21, combine_oinfo oinf1 oinf2)
    | (ENUntil (c1, dt, f11, f12, muninf1), ENUntil  ( _, _, f21, f22, muninf2))
      -> ENUntil        (c1, dt, comb_e f11 f21, comb_e f12 f22, combine_muninfo muninf1 muninf2)
    | (EUntil (c1, dt, f11, f12, muinf1), EUntil ( _, _, f21, f22, muinf2))
      -> EUntil         (c1, dt, comb_e f11 f21, comb_e f12 f22, combine_muinfo muinf1 muinf2)
    | (EEventuallyZ (dt, f11, ezinf1), EEventuallyZ (_, f21, ezinf2))
      -> EEventuallyZ   (dt, comb_e f11 f21, combine_ezinfo ezinf1 ezinf2)
    | (EEventually (dt, f11, einf1), EEventually (_, f21, einf2))
      -> EEventually   (dt, comb_e f11 f21, combine_einfo einf1 einf2)
    | _ -> raise (Type_error ("Mismatched formulas in combine_states")) 

(* END COMBINING STATES *)


(* SPLITTING STATE *)
let get_predicate f =
  let pvars p = Predicate.pvars p in
  let rec get_pred = function
    (* Equal, Less, LessEq all mapped to free vars;  ForAll not used *)
  | MRel           (_)                    -> raise (Type_error ("Predicate function should not be entering ERel"))
  | MPred          (p, _, _)              -> pvars p
  | MNeg           (f1)                   -> get_pred f1
  | MAnd           (_, f1, f2, _)         -> Misc.union (get_pred f1) (get_pred f2)
  | MOr            (_, f1, f2, _)         -> Misc.union (get_pred f1) (get_pred f2)
  | MExists        (comp, f1)             -> Helper.rel_to_pvars (comp (Helper.pvars_to_rel(get_pred f1))   )
  | MAggreg        (_, f1)                -> get_pred f1
  | MAggOnce       (f1, _, _, _, _, _)    -> get_pred f1
  | MAggMMOnce     (f1, _, _, _, _, _)    -> get_pred f1
  | MPrev          (_, f1, _)             -> get_pred f1
  | MNext          (_, f1, _)             -> get_pred f1
  | MSinceA        (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MSince         (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MOnceA         (_, f1, _)             -> get_pred f1
  | MOnceZ         (_, f1, _)             -> get_pred f1
  | MOnce          (_, f1, _)             -> get_pred f1
  | MNUntil        (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MUntil         (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MEventuallyZ   (_, f1, _)             -> get_pred f1
  | MEventually    (_, f1, _)             -> get_pred f1
  in
  get_pred f

let get_predicate2 f1 f2 =
  Misc.union (get_predicate f1) (get_predicate f2)

let list_to_string l =
  let str = ref "" in
  let append s = str := !str ^ s ^ ", " in
  List.iter (fun s -> append s ) l;
  !str

let int_list_to_string l =
  let str = ref "" in
  let append s = str := !str ^ (string_of_int s) ^ ", " in
  List.iter (fun s -> append s ) l;
  !str

let int_arr_to_string l =
  let str = ref "" in
  let append s = str := !str ^ (string_of_int s) ^ ", " in
  Array.iter (fun s -> append s ) l;
  !str
  

let pred_list_to_string l =
  let str = ref "" in
  let append s = str := !str ^ (Predicate.string_of_cst false s) ^ ", " in
  List.iter (fun s -> append s ) l;
  !str

let split_debug f op =
  Printf.printf "Predicate Names: (%s) for formula: '%s' \n" (list_to_string (get_predicate f)) op

let split_debug2 f1 f2 op =
  Printf.printf "Predicate Names: (%s) for formula: '%s' \n" (list_to_string (get_predicate2 f1 f2)) op

let get_1 (a,_) = a
let get_2 (_,b) = b

let comb_preds preds1 preds2 = List.append preds1 preds2

let check_tuple t vl =
  (*Printf.printf "Tlength: %d; VLength: %d \n" (List.length t) (List.length vl);*)
  (* Lists always have same length due to filtering in split function *)
  let eval = List.mapi (fun i e -> List.exists (fun e2 -> (List.nth t i) = e2) e) vl in
  List.fold_right (fun a agg -> (a || agg)) eval false

let split_state mapping mf size =
  let split rel preds =
    let res = Array.make size Relation.empty in
    (* Iterate over relation, adding tuples to relations of partitions where they are relevant *)
    Relation.iter (fun t -> let parts = mapping t preds in Array.iter (fun p -> res.(p) <- Relation.add t res.(p)) parts) rel;
    res
  in

  let split_queue1 q p =
    let res = Array.init size (fun i -> Queue.create()) in 
    Queue.iter (
      fun e -> 
      let i, ts, r  = e in
      let states = split r p in 
      Array.iteri (fun index s -> Queue.add (i, ts, s) res.(index)) states
    ) q;
    res
  in  
  let split_queue2 q p =
    let res = Array.init size (fun i -> Queue.create()) in 
    Queue.iter (
    fun e -> 
      let ts, r  = e in
      let states = split r p in 
      Array.iteri (fun index s -> Queue.add (ts, s) res.(index)) states
    ) q;   
    res
  in  
  let split_mqueue q p =
    let res = Array.init size (fun i -> Mqueue.create()) in 
    Mqueue.iter (
    fun e -> 
      let ts, r  = e in
      let states = split r p in 
      Array.iteri (fun index s -> Mqueue.add (ts, s) res.(index)) states
    ) q;    
    res
  in  
  let split_dll1 l p = 
    let res = Array.init size (fun i -> Dllist.empty()) in 
    Dllist.iter (
      fun e -> let i, ts, r  = e in
      let states = split r p in 
      Array.iteri (fun index s -> Dllist.add_last (i, ts, s) res.(index)) states
    ) l;
    res
  in
  let split_dll2 l p = 
    let res = Array.init size (fun i -> Dllist.empty()) in 
    Dllist.iter (
      fun e -> let ts, r  = e in
      let states = split r p in 
      Array.iteri (fun index s -> Dllist.add_last (ts, s) res.(index)) states
    ) l;
    res
  in
  let split_info inf p =
    split_queue1 inf p
  in
  let split_ainfo ainf p =
    let arr = Array.make size { arel = None } in 
    let res = match ainf.arel with
    | Some r -> let states = (split r p) in Array.map (fun s -> {arel = Some s}) states
    | None -> arr
    in
    res
  in
  let split_agg  agg p =
    let res = split_queue2 agg.other_rels p in
    Array.map (fun e ->   {tw_rels = agg.tw_rels; other_rels = e; mset = agg.mset; hres = agg.hres }) res   
  in
  let split_aggMM agg p =
    let res = split_queue2 agg.non_tw_rels p in      
    Array.map (fun e -> {non_tw_rels = e; tbl = agg.tbl }) res
  in
  let split_sainfo sainf p =
    let arr = Array.init size (fun i -> None) in 
    let sarels = match sainf.sarel2 with
    | Some r -> let states = (split r p) in Array.map (fun s ->  Some s) states
    | None -> arr
    in
    let queues = split_mqueue sainf.saauxrels p in    
    let sres = split sainf.sres p in 
    Array.mapi (fun i e ->  {sres = e; sarel2 = sarels.(i); saauxrels = queues.(i)}) sres
  in
  let split_sinfo sinf p =
    let arr = Array.init size (fun i -> None) in 
    let srels = match sinf.srel2 with
    | Some r -> let states = (split r p) in Array.map (fun s ->  Some s) states
    | None -> arr
    in
    let queues = split_mqueue sinf.sauxrels p in    
    Array.map2 (fun srel2 nq -> {srel2 = srel2; sauxrels = nq}) srels queues
  in
  let split_oainfo oainf p =
    let queues = split_mqueue oainf.oaauxrels p in   
    let ores = split oainf.ores p in 
    Array.map2 (fun ores nq ->  {ores = ores; oaauxrels = nq}) ores queues
  in
  let split_mozinfo mozinf p =
    print_endline "Splitting mozinfo:";
    let dllists = Array.init size (fun i -> Dllist.empty()) in 
      Dllist.iter (
        fun e -> let i, ts, r  = e in
        let states = split r p in 
        Array.iteri (fun index s -> Dllist.add_last (i, ts, s) dllists.(index)) states
      ) mozinf.mozauxrels;
    Printf.printf "%d \n" mozinf.mozlast;
    Array.iteri (fun index l -> Printf.printf "%d: " index; Dllist.iter (fun e -> let i,ts,r = e in Relation.print_rel "'" r) l; print_endline "") dllists;
    (* TODO: handle tree by either getting rid of it for mformulas and reconstructing or actually splitting it aswell *)
    Array.map (fun e -> {moztree = mozinf.moztree; mozlast = mozinf.mozlast; mozauxrels = e }) dllists
  in
  let split_moinfo moinf p =
    let dllists = split_dll2 moinf.moauxrels p in
    (* TODO: handle tree by either getting rid of it for mformulas and reconstructing or actually splitting it aswell *)
    Array.map (fun e -> {motree = moinf.motree; molast = moinf.molast; moauxrels = e }) dllists
  in
  let split_muninfo muninf p =
    let listrels1 = split_dll1 muninf.mlistrel1 p in
    let listrels2 = split_dll1 muninf.mlistrel2 p in
    Array.map2 (fun listrel1 listrel2 -> { mlast1 = muninf.mlast1; mlast2 = muninf.mlast2; mlistrel1 = listrel1;  mlistrel2 = listrel2 }) listrels1 listrels2
  in
  let split_muinfo muinf p =
    (* Helper function for raux and saux fields, creates split Sk.dllist *)
    let sklist l =
      let sklists = Array.init size (fun i -> Sk.empty()) in 
      Sk.iter (fun e ->
        let i, r = e in
        let states = split r p in 
        Array.iteri (fun index s -> Sk.add_last (i, s) sklists.(i)) states
      ) l;
      sklists
    in
    let mraux = Array.init size (fun i -> Sj.empty()) in 
      Sj.iter (fun e ->
        let (i, ts, l) = e in
        let lists = sklist l in
        Array.iteri (fun index l -> Sj.add_last (i, ts, l) mraux.(i)) lists
      ) muinf.mraux;
    let arr = Array.make size None in 
    let murels = match muinf.murel2 with
    | Some r -> let states = (split r p) in Array.map (fun s ->  Some s) states
    | None -> arr
    in
    let msaux = sklist muinf.msaux in
    let mures = split muinf.mures p in
    Array.mapi (fun i e -> 
    { mulast = muinf.mulast; mufirst = muinf.mufirst; mures = mures.(i);
      murel2 = e; mraux = mraux.(i); msaux = msaux.(i) })
    murels   
  in
  let split_mezinfo mezinf p =
    let dllists = split_dll1 mezinf.mezauxrels p in
    (* TODO: handle tree by either getting rid of it for mformulas and reconstructing or actually splitting it aswell *)
    Array.map (fun e -> {mezlastev = mezinf.mezlastev; meztree = mezinf.meztree; mezlast = mezinf.mezlast; mezauxrels = e }) dllists
  in
  let split_meinfo meinf p =
    let dllists = split_dll2 meinf.meauxrels p in
    (* TODO: handle tree by either getting rid of it for mformulas and reconstructing or actually splitting it aswell *)
    Array.map (fun e -> {melastev = meinf.melastev; metree = meinf.metree; melast = meinf.melast; meauxrels = e }) dllists
  in
  let p1 f1 = get_predicate f1 in
  let p2 f1 f2 = get_predicate2 f1 f2 in
  let rec split_f = function
    (* Don't think MRel is relevant *)
    | MRel           (rel)                                      -> Array.make size (MRel(rel)) 
    | MPred          (p, comp, inf)                             -> let arr = split_info inf [Predicate.get_name p] in Array.map (fun e -> MPred(p, comp, e)) arr
    | MNeg           (f1)                                       -> Array.map (fun e -> MNeg(e)) (split_f f1)                                                             
    | MAnd           (c, f1, f2, ainf)                          -> let a1 = (split_f f1) in let a2 = (split_f f2) in  Array.mapi (fun i e -> MAnd(c, a1.(i), a2.(i), e)) (split_ainfo ainf (p2 f1 f2))
    | MOr            (c, f1, f2, ainf)                          -> let a1 = (split_f f1) in let a2 = (split_f f2) in  Array.mapi (fun i e -> MOr (c, a1.(i), a2.(i), e)) (split_ainfo ainf (p2 f1 f2))
    | MExists        (c, f1)                                    -> Array.map (fun e -> MExists(c, e)) (split_f f1)                                                                    
    | MAggreg        (c, f1)                                    -> Array.map (fun e -> MAggreg(c, e)) (split_f f1)  
    | MAggOnce       (f1, dt, agg, upd_old, upd_new, get_res)   -> let a1 = (split_f f1) in  Array.mapi (fun i e -> MAggOnce(a1.(i), dt, e, upd_old, upd_new, get_res)) (split_agg agg (p1 f1))   
    | MAggMMOnce     (f1, dt, aggMM, upd_old, upd_new, get_res) -> let a1 = (split_f f1) in  Array.mapi (fun i e -> MAggMMOnce(a1.(i), dt, e, upd_old, upd_new, get_res)) (split_aggMM aggMM (p1 f1))
    | MPrev          (dt, f1, pinf)                             -> Array.map (fun e -> MPrev(dt, e, pinf)) (split_f f1)
    | MNext          (dt, f1, ninf)                             -> Array.map (fun e -> MNext(dt, e, ninf)) (split_f f1)
    | MSinceA        (c2, dt, f1, f2, sainf)                    -> let a1 = (split_f f1) in let a2 = (split_f f2) in  Array.mapi (fun i e -> MSinceA(c2, dt, a1.(i), a2.(i), e)) (split_sainfo sainf (p2 f1 f2))
    | MSince         (c2, dt, f1, f2, sinf)                     -> let a1 = (split_f f1) in let a2 = (split_f f2) in  Array.mapi (fun i e -> MSince(c2, dt, a1.(i), a2.(i), e)) (split_sinfo sinf (p2 f1 f2))
    | MOnceA         (dt, f1, oainf)                            -> let a1 = (split_f f1) in Array.mapi (fun i e -> MOnceA(dt, a1.(i), e)) (split_oainfo oainf (p1 f1))                      
    | MOnceZ         (dt, f1, ozinf)                            -> let a1 = (split_f f1) in Array.mapi (fun i e -> MOnceZ(dt, a1.(i), e)) (split_mozinfo ozinf (p1 f1))                                
    | MOnce          (dt, f1, oinf)                             -> let a1 = (split_f f1) in Array.mapi (fun i e -> MOnce(dt, a1.(i), e)) (split_moinfo oinf (p1 f1)) 
    | MNUntil        (c1, dt, f1, f2, muninf)                   -> let a1 = (split_f f1) in let a2 = (split_f f2) in Array.mapi (fun i e -> MNUntil(c1, dt, a1.(i), a2.(i), e)) (split_muninfo muninf (p2 f1 f2))   
    | MUntil         (c1, dt, f1, f2, muinf)                    -> let a1 = (split_f f1) in let a2 = (split_f f2) in Array.mapi (fun i e -> MUntil(c1, dt, a1.(i), a2.(i), e)) (split_muinfo muinf (p2 f1 f2))   
    | MEventuallyZ   (dt, f1, mezinf)                           -> let a1 = (split_f f1) in Array.mapi (fun i e -> MEventuallyZ(dt, a1.(i), e)) (split_mezinfo mezinf (p1 f1))            
    | MEventually    (dt, f1, meinf)                            -> let a1 = (split_f f1) in Array.mapi (fun i e -> MEventually(dt, a1.(i), e)) (split_meinfo meinf (p1 f1))
    in
  split_f mf
    

let split_formula sconsts dumpfile i lastts ff closed neval =
  let numparts = (sconsts.num_partitions+1) in

  let keys = sconsts.keys in
  let constraints = sconsts.constraints in
  let a, mf = ext_to_m ff neval in

  let split_paramater_function t p = 
    Printf.printf "Tuple: %s    -> " (pred_list_to_string t);
    let pos = List.map (fun p -> try Misc.get_pos p keys with e -> -1 ) p in
    (* columns not in cs.keys are filtered -> so ignored for checking tuples *)
    let pos = List.filter (fun e -> e >= 0) pos in
    (* If no specified keys are in the predicate list, return all partitions *)
    if List.length pos = 0 then let res = Array.make numparts 0 in Array.mapi (fun i e -> i) res else
    (* Else we create a mapping to reorder our partition input values *)
    let mapping t = List.map (fun e -> List.nth t e) pos in
    let output = Array.of_list (List.flatten (List.map (fun cs -> if check_tuple t (mapping cs.values) then cs.partitions else []) constraints)) in
    Printf.printf "Partitions: %s \n" (int_arr_to_string output);
    output
  in  
  split_state split_paramater_function mf numparts


(* END SPLITTING STATE *)

let files_to_list f = 
  String.split_on_char ',' f   
  
  
let combine_neval nv1 nv2 =
  (* What should be done with the i *)
  let rec combine l nl c : unit = 
    let e = NEval.pop_first l in 
    let i, ts = e in 
    (* l1 list element ts is < l2 ts2, pop from l2 and add to new list *)
    if c < ts then 
      NEval.add_last e nl
    (* if timestamp already contained, skip *)
    else if c = ts then () 
    (* otherwise readd popped element *)
    else NEval.add_first e l;
    if c < ts then combine l nl c
  in
  let n = NEval.empty() in
  NEval.iter (fun e -> 
    let _, ts = e in 
    combine nv2 n ts;
  ) nv1;
  n

let rec print_ef = function
  | ERel           (rel)                                      -> print_endline "Rel" 
  | EPred          (p, comp, inf)                             -> print_endline "Pred"
  | ENeg           (f1)                                       -> print_endline "Neg";print_ef f1
  | EAnd           (c, f1, f2, ainf)                          -> print_endline "And";print_ef f1; print_ef f2
  | EOr            (c, f1, f2, ainf)                          -> print_endline "Or";print_ef f1; print_ef f2
  | EExists        (c, f1)                                    -> print_endline "Exists";print_ef f1
  | EAggreg        (c, f1)                                    -> print_endline "Aggreg";print_ef f1
  | EAggOnce       (f1, dt, agg, upd_old, upd_new, get_res)   -> print_endline "AggOnce";print_ef f1
  | EAggMMOnce     (f1, dt, aggMM, upd_old, upd_new, get_res) -> print_endline "AggMMOnce";print_ef f1
  | EPrev          (dt, f1, pinf)                             -> print_endline "Prev";print_ef f1
  | ENext          (dt, f1, ninf)                             -> print_endline "Next";print_ef f1
  | ESinceA        (c2, dt, f1, f2, sainf)                    -> print_endline "SinceA";print_ef f1;print_ef f2
  | ESince         (c2, dt, f1, f2, sinf)                     -> print_endline "Since";print_ef f1;print_ef f2
  | EOnceA         (dt, f1, oainf)                            -> print_endline "OnceA";print_ef f1
  | EOnceZ         (dt, f1, ozinf)                            -> print_endline "OnceZ";print_ef f1
  | EOnce          (dt, f1, oinf)                             -> print_endline "Once";print_ef f1
  | ENUntil        (c1, dt, f1, f2, muninf)                   -> print_endline "NUntil";print_ef f1;print_ef f2
  | EUntil         (c1, dt, f1, f2, muinf)                    -> print_endline "Until";print_ef f1;print_ef f2
  | EEventuallyZ   (dt, f1, mezinf)                           -> print_endline "EventuallyZ";print_ef f1
  | EEventually    (dt, f1, meinf)                            -> print_endline "Eventually";print_ef f1