module Legacy_symbolic = LoggingMemory.M

(* module Lifting = Gillian.Symbolic.Legacy_s_memory.Modernize (JSILSMemory.M) *)

module Symbolic = Gillian.Symbolic.Legacy_s_memory.Modernize (Legacy_symbolic)
module Concrete = JSILCMemory.M
module External = External.M
module SHeap = SHeap
