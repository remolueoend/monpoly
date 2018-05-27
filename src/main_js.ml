module Html = Dom_html

let (>>=) = Lwt.bind

open Dom
open Predicate
open MFOTL

let sign = ref []
let formula = ref None
let examples =
  [ "small", "ex"
  ; "publish/approve", "rv11"
  ; "publish/approve/manager", "rv11b"
  ]

let http_get url =
  XmlHttpRequest.get url >>= fun r ->
  let cod = r.XmlHttpRequest.code in
  let msg = r.XmlHttpRequest.content in
  if cod = 0 || cod = 200
  then Lwt.return msg
  else fst (Lwt.wait ())

let getfile f =
  try
    Lwt.return (Sys_js.file_content f)
  with Not_found ->
    http_get f

let onload _ =
  let d = Html.document in
  let body = Js.Opt.get (d##getElementById (Js.string "monpoly_demo")) (fun () -> assert false) in

  let title = Html.createH1 d in
  title##innerHTML <- Js.string "MONPOLY <font size=3>Monitoring Metric First-Order Temporal Properties</font>";

  let ex = Html.createDiv d in
  let ed_name = "*edited*" in
  let ex_names = List.map fst examples in

  let append_opt e s = Dom.appendChild e (d##createTextNode (Js.string s)) in
  append_opt ex "Select example ";
  let select = Html.createSelect d in
  List.iter
    (fun text ->
       let option = Html.createOption d in
       append_opt option text;
       Dom.appendChild select option)
    (ed_name :: ex_names);
  Dom.appendChild ex select;
  append_opt ex " or edit";

  let tab = Html.createTable d in
  let tr1 = Html.createTr d in
  let tdl1 = Html.createTd d in
  let tdr1 = Html.createTd d in
  let tr2 = Html.createTr d in
  let tdl2 = Html.createTd d in
  let tdr2 = Html.createTd d in
  let tr3 = Html.createTr d in
  let tdl3 = Html.createTd d in
  let tr4 = Html.createTr d in
  let tdl4 = Html.createTd d in
  let tr5 = Html.createTr d in
  let tdl5 = Html.createTd d in
  let tr6 = Html.createTr d in
  let tdl6 = Html.createTd d in

  tdl1##vAlign <- Js.string "top";
  tdr1##vAlign <- Js.string "top";
  tdl2##vAlign <- Js.string "top";
  tdr2##vAlign <- Js.string "top";
  tdr2##rowSpan <- 5;
  tdl3##vAlign <- Js.string "top";
  tdl4##vAlign <- Js.string "top";
  tdl5##vAlign <- Js.string "top";
  tdl6##vAlign <- Js.string "top";

  let sigtext = Html.createB d in
  sigtext##innerHTML <- Js.string "Signature ";
  let sigin = Html.createInput ?_type:(Some (Js.string "file")) d in
  let sigframe = Html.createTextarea d in
  sigframe##style##border <- Js.string "2px green solid";
  sigframe##rows <- 10;
  sigframe##id  <- Js.string "sig";

  let formulatext = Html.createB d in
  formulatext##innerHTML <- Js.string "MFOTL formula ";
  let formulain = Html.createInput ?_type:(Some (Js.string "file")) d in
  let formulaframe = Html.createTextarea d in
  formulaframe##style##border <- Js.string "2px green solid";
  formulaframe##rows <- 15;
  formulaframe##id  <- Js.string "formula";

  let logtext = Html.createB d in
  logtext##innerHTML <- Js.string "Log ";
  let login = Html.createInput ?_type:(Some (Js.string "file")) d in
  let logframe = Html.createTextarea d in
  logframe##style##border <- Js.string "2px green solid";
  logframe##rows <- 35;
  logframe##id  <- Js.string "log";

  let restext = Html.createB d in
  restext##innerHTML <- Js.string "Violations ";
  let resframe = Html.createTextarea d in
  resframe##style##border <- Js.string "2px red solid";
  resframe##style##backgroundColor <- Js.string "lightgrey";
  resframe##rows <- 3;
  resframe##id  <- Js.string "res";
  resframe##disabled  <- Js._true;

  Dom.appendChild body title;
  Dom.appendChild body ex;
  Dom.appendChild body (Html.createHr d);
  Dom.appendChild tdl1 sigtext;
  Dom.appendChild tdl1 sigin;
  Dom.appendChild tdr1 logtext;
  Dom.appendChild tdr1 login;
  Dom.appendChild tdl2 sigframe;
  Dom.appendChild tdr2 logframe;
  Dom.appendChild tdl3 formulatext;
  Dom.appendChild tdl3 formulain;
  Dom.appendChild tdl4 formulaframe;
  Dom.appendChild tdl5 restext;
  Dom.appendChild tdl6 resframe;
  Dom.appendChild tr1 tdl1;
  Dom.appendChild tr1 tdr1;
  Dom.appendChild tr2 tdl2;
  Dom.appendChild tr2 tdr2;
  Dom.appendChild tr3 tdl3;
  Dom.appendChild tr4 tdl4;
  Dom.appendChild tr5 tdl5;
  Dom.appendChild tr6 tdl6;
  Dom.appendChild tab tr1;
  Dom.appendChild tab tr2;
  Dom.appendChild tab tr3;
  Dom.appendChild tab tr4;
  Dom.appendChild tab tr5;
  Dom.appendChild tab tr6;
  Dom.appendChild body tab;

  let append_string s =
    resframe##value <- Js.string (Js.to_string (resframe##value) ^ s) in

  let append_err err s =
    err##title <- Js.string (Js.to_string (err##title) ^ s) in

  Sys_js.set_channel_flusher stdout append_string;

  let color_frame border deact xframe =
    xframe##style##border <- Js.string border;
    xframe##style##backgroundColor <-
      Js.string (if deact then "lightgrey" else "white");
    xframe##style##backgroundImage <- Js.string "none";
    xframe##disabled <- Js.bool deact in

  let deactivate = color_frame "2px grey solid" true in
  let error = color_frame "2px red solid" false in
  let warn = color_frame "2px yellow solid" false in
  let ok = color_frame "2px green solid" false in

  let visibility_res vis =
    resframe##style##display <- Js.string vis;
    restext##style##display <- Js.string vis in

  let hide_res () = visibility_res "none" in
  let show_res () = visibility_res "inline" in

  let register xin xframe xcheck =
    xframe##oninput <- Html.handler (fun _ ->
        xcheck ();
        select##value <- Js.string ed_name;
        xin##value <- Js.string "";
        Js._true);
    xin##onchange <- Html.handler (fun _ ->
        Js.Optdef.iter (xin##files) (fun fs ->
            Js.Opt.iter (fs##item(0)) (fun file ->
                ignore (File.readAsText file >>= (fun text ->
                    xframe##value <- text;
                    xcheck ();
                    select##value <- Js.string ed_name;
                    Lwt.return_unit));
                ()));
        Js._true) in

  let reset_errs () =
    sigframe##title <- Js.string "";
    formulaframe##title <- Js.string "";
    logframe##title <- Js.string "" in

  let check_log () =
    logframe##style##border <- Js.string "2px green solid";
    match !formula with
    | None -> ()
    | Some f ->
      try
        resframe##value <- Js.string "";
        reset_errs ();
        Sys_js.set_channel_flusher stderr (append_err logframe);
        logframe##style##backgroundImage <- Js.string "none";
        Algorithm.monitor_string (Js.to_string (logframe##value) ^ "\n") f;
        if Js.to_string (resframe##value) = ""
        then
          (ok logframe; hide_res ();
           logframe##style##backgroundImage <- Js.string "url(\"check.png\")")
        else
          (warn logframe; show_res ())
      with e ->
        error logframe; hide_res ()
  in

  let check_formula () =
    (try
       reset_errs ();
       Sys_js.set_channel_flusher stderr (append_err formulaframe);
       let f = Neg (Formula_parser.formula Formula_lexer.token
                      (Lexing.from_string (Js.to_string (formulaframe##value)))) in
       let is_mon, pf, vartypes = Rewriting.check_formula !sign f in
       if is_mon then
         (formula := Some pf;
          check_log ();
          ok formulaframe)
       else
         (formula := None;
          warn formulaframe;
          deactivate logframe;
          hide_res ();
          formulaframe##style##backgroundImage <- Js.string "url(\"tel.png\")")
     with e ->
       (formula := None;
        error formulaframe;
        deactivate logframe;
        hide_res ())) in

  let check_sig () =
    (try
       reset_errs ();
       Sys_js.set_channel_flusher stderr (append_err sigframe);
       sign := Log.get_signature_string (Js.to_string (sigframe##value));
       ok sigframe;
       check_formula ()
     with e ->
       sign := [];
       error sigframe;
       deactivate formulaframe;
       deactivate logframe;
       hide_res ()) in

  register sigin sigframe check_sig;
  register formulain formulaframe check_formula;
  register login logframe check_log;

  let load name xending xframe =
    ignore (getfile ("examples/" ^ List.assoc name examples ^ xending) >>=
            (fun s -> Lwt.return (xframe##value <- Js.string s))) in
  let load_ex name =
    load name ".sig" sigframe;
    load name ".mfotl" formulaframe;
    load name ".log" logframe;
    check_sig (); in
  select##onchange <- Html.handler
      (fun _ ->
         let i = select##selectedIndex - 1 in
         if i >= 0 && i < List.length ex_names then
           load_ex (List.nth ex_names i);
         Js._false);
  select##value <- Js.string (List.nth ex_names 1);
  load_ex (List.nth ex_names 1);

  Js._false

let _ = Html.window##onload <- Html.handler onload
