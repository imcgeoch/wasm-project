||| As defined in https://webassembly.github.io/spec/core/exec/runtime.html
module Execution.Runtime

import Data.Vect

||| Wasm computations manipulate values of the four basic types.
|||
||| Note: We can possibly remove this as we are just wrapping Idris values, but
|||       I'm keeping it in for now to conform to the spec.
|||
||| Spec: https://webassembly.github.io/spec/core/exec/runtime.html#syntax-val
data Value = I32Val Bits32
           | I64Val Void    -- XXX: Can't be created yet
           | F32Val Void    -- XXX: Can't be created yet
           | F64Val Void    -- XXX: Can't be created yet

||| A result is the outcome of a computation. It is either a sequence of values
||| or a trap.
|||
||| Note: In the current version of WASM, a result can consist of at most one
||| value.
|||
||| Spec: https://webassembly.github.io/spec/core/exec/runtime.html#syntax-result
data Result = ResultVal (Maybe Value) | TrapVal

mutual 
    ||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-store
    record Store where
        constructor MkStore
        funcs   : Vect n FuncInst
        tables  : Vect n TableInst
        mems    : Vect n MemInst
        globals : Vect n GlobalInst



    data FuncInst : Type where

    data TableInst : Type where

    data MemInst : Type where

    data GlobalInst : Type where

