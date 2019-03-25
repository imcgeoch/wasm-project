||| Prototype interpreter, this should be stand alone for now. We can pull stuff
||| like type defs out into a separate file later when we want to get the
||| validator hooked up
module Interp
import Data.Vect

namespace types

    ||| Basic machine types
    data WasmType = I32 | I64 | F32 | F64

    ||| Packed types
    data PackedType = P8 | P16 | P32

    ||| Function types
    data FnType : Type where
        Maps : List WasmType -> List WasmType -> FnType

    data GlobalType = Mut WasmType | Val WasmType

    wasmToIdrisType : WasmType -> Type
    wasmToIdrisType I32 = Bits32
    wasmToIdrisType I64 = Bits64
    wasmToIdrisType F32 = Void   -- Can't handle this currently
    wasmToIdrisType F64 = Double


namespace instructions

    ||| Signed or unsigned
    data Sign = S | U

    ||| Gives a literal value of a given type
    data Value = I32Const Bits32
               | I64Const Bits64
               | F32Const Void
               | F64Const Double

    ||| Bytecode Instructions: These are taken from Fig 1 of the PLDI paper
    data Insn = Unreachable
              | Nop
              | Drop
              | Select
              | Block FnType (List Insn)
           -- | Loop  FnType (List Insn)
              | If FnType (List Insn) (List Insn)
              | Br Int
              | BrIf Int
           -- | BrTable (List Insn) -- XXX: Need to ensure that list is non-empty
              | Return
              | Call Int
              | CallIndirect FnType
              | GetLocal Int
              | SetLocal Int
              | TeeLocal Int
              | GetGlobal Int
              | SetGlobal Int
           -- Hold of on load and store--these is somewhat involved
           -- | Load  WasmType TODO
           -- | Store WasmType TODO
              | CurrMem
              | GrowMem
              | Constant Value
              -- TODO: Finish Unary/Binary/Test/Relop/etc

namespace program
    data Export = Ex String

    ||| A Wasm Function. TODO: Finish
    record Function where
        constructor MkFn
        exports : List Export
        fnType  : FnType
        wtfIsThis1 : List WasmType
        code    : List Insn

    record Import where
        constructor MkImport
        mod  : String
        item : String

    record Global where
        constructor MkGlobal
        exports   : List Export
        globTypes : List GlobalType
        init      : Either (List Insn) Import

    record Table where
        constructor MkTable
        exports : List Export
        size    : Int
        body    : Either (List Int) Import -- XXX Not sure if this is correct

    record Memory where
        constructor MkMemory
        exports : List Export
        body    : Either Int Import

    record Module where
        constructor MkModule
        functions : List Function
        globals   : List Global
        table     : Maybe Table
        memory    : Maybe Memory

--- The following is taken from Figure 2 in PLDI
namespace execution
    mutual
        ||| XXX: Closures have special requirements for their function (namely,
        ||| not an import and have all exports erased). We need to make a new
        ||| type to handle this once we have a grasp on what's happening
        record Closure where
            constructor MkClosure
            inst : Instance
            code : Function  -- XXX: Where f is not an import and has all exports erased

        ||| An instantiated module
        record Instance where
            constructor MkInstance
            fns     : List Closure
            globals : List Value

    record Store where
        constructor MkStore
        inst    : Instance
        tables  : List Table
        memory  : List Memory

data Interp : Type where -- empty for now

