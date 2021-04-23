let seed = Random.State.make_self_init ()

let previous : Report.id option ref = ref Option.none

let parents : Report.id Stack.t = Stack.create ()

let make
    ?title
    ~(content : Loggable.loggable)
    ~(type_ : string)
    ?(severity = Report.Log)
    () =
  let title =
    match title with
    | None       -> type_
    | Some title -> title
  in
  let report : Report.t =
    {
      id = (Unix.getpid (), Uuidm.v4_gen seed ());
      title;
      elapsed_time = Sys.time ();
      previous = !previous;
      parent = Stack.top_opt parents;
      content;
      severity;
      type_;
    }
  in
  previous := Some report.id;
  report

let start_phase level ?title ?severity () =
  if Mode.should_log level then (
    let report =
      make ?title
        ~content:(Loggable.make_string "*** Phase ***")
        ~type_:LoggingConstants.ContentType.phase ?severity ()
    in
    previous := None;
    Stack.push report.id parents;
    Default.log report;
    Some report.id)
  else None

let end_phase = function
  | None                   -> ()
  | Some (pid, uuid) as id ->
      let p, u = Stack.pop parents in
      assert (Int.equal pid p && Uuidm.equal uuid u);
      previous := id
