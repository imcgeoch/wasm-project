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

        data Export = Ex String

        ||| A Wasm Function. TODO: Finish
        record Function where
            constructor MkFn
            exports    : List Export
            fnType     : FnType
            wtfIsThis1 : List WasmType
            code       : List Insn

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
                  | Clz      | Ctz      | Popcnt

                  -- Bin op
                  | IAdd     | ISub     | IMul     | IDiv Sign
                  | Rem Sign | And      | Or       | Xor
                  | Shl      | Shr Sign | Rotl     | Rotr

                  -- Test op
                  | Eqz

                  -- Rel op
                  | IEq | INe | ILt Sign | IGt Sign | ILe Sign | IGe Sign

                  -- Conversion op
                  | Convert | Reinterpret

                  ----------------------------------------
                  ---      Administrative  Syntax      ---
                  ----------------------------------------
                  | Trap
                  | CallCl Closure
                  | Label Nat (List Insn) (List Insn)
                  | Local Nat Int (List Value) (List Insn)

namespace program

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

    ||| A memory declaration in a Module, this represents how the memory is defined,
    ||| not the instantiation of memory (which is defined under MemInst)
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

    ||| LocalContext: a convenient notation to help us reason about control flow.
    ||| TODO: Do we need to define this? It makes our type system a little tricky
    ||| For instance, in LCNest, we only want to accept labels instead of
    ||| arbitrary Insns (which is doable) and we will need to have this exist in our
    ||| list of instructions --- does this count as administrative syntax? Should we
    ||| include this in our Insn type?
    data LocalContext : Nat -> Type where
        ||| The base case of a local context is v* [-] e*, which is just a list of values and a
        ||| list of instructions.
        LCBase : (List Value) -> (List Insn) -> LocalContext Z

        ||| Inductively build a new local context from a previous one.
        ||| TODO: This isn't quite correct
        LCNest : (List Value) -> (label:Insn) -> LocalContext k -> (List Insn) -> LocalContext (S k)

    ||| An instance of a linear memory.
    ||| NOTE: This is SUUUUPER inefficient since we don't have random access. This
    ||| would need to be improved for any sort of runtime use
    MemInst : Type
    MemInst = List Bits8

    ||| An instance of a function table at runtime.
    ||| NOTE: This is SUUUUPER inefficient since we don't have random access. This
    ||| would need to be improved for any sort of runtime use
    TabInst : Type
    TabInst = List Closure

    record Store where
        constructor MkStore
        inst    : List Instance
        tables  : List TabInst
        memory  : List MemInst

data Interp : Type where -- empty for now

