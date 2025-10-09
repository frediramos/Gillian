module CLI =
  Gillian.Command_line.Make
    (Gillian.General.Init_data.Dummy)
    (Semantics_loglifting.Concrete)
    (Semantics_loglifting.Symbolic)
    (Js2jsil_lib.JS2GIL_ParserAndCompiler)
    (Semantics_loglifting.External)
    (struct
      let runners : Gillian.Bulk.Runner.t list =
        [ (module Test262.Test262_runner); (module CosetteRunner) ]
    end)
    (Debugging_loglifting.JSLifter.Make)

let () = CLI.main ()
