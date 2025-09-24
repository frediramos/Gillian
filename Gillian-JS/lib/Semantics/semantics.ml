module Lifting = Gillian.Symbolic.Legacy_s_memory.Modernize (JSILSMemory.M)
module Logging = Gillian.Symbolic.Legacy_s_memory.Modernize (LoggingMemory.M)
module Symbolic = Logging
module Concrete = JSILCMemory.M
module External = External.M
module SHeap = SHeap
