module Legacy_symbolic = LogLiftMemory.M
module Symbolic = Gillian.Symbolic.Legacy_s_memory.Modernize (Legacy_symbolic)
module Concrete = Semantics_shared.JSILCMemory.M
module External = Semantics_shared.External.M
module SHeap = Semantics_shared.SHeap
