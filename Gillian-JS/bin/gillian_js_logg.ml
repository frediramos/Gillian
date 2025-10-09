module CLI =
  Gillian.Command_line.Make
    (Gillian.General.Init_data.Dummy)
    (Semantics_logging.Concrete)
    (Semantics_logging.Symbolic)
    (Js2jsil_lib.JS2GIL_ParserAndCompiler)
    (Semantics_logging.External)
    (struct
      let runners : Gillian.Bulk.Runner.t list =
        [ (module Test262.Test262_runner); (module CosetteRunner) ]
    end)
    (Debugging_logging.JSLifter.Make)

let () = CLI.main ()
