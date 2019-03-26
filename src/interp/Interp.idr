||| Prototype interpreter, this should be stand alone for now. We can pull stuff
||| like type defs out into a separate file later when we want to get the
||| validator hooked up
module Interp
import Data.Vect
import Data.Bits

-- Definitions from https://webassembly.github.io/spec/core/syntax/modules.html#syntax-localidx
namespace indices
    TypeIdx : Type
    TypeIdx = Bits32

    FuncIdx : Type
    FuncIdx = Bits32

    TableIdx : Type
    TableIdx = Bits32

    MemIdx : Type
    MemIdx = Bits32

    GlobalIdx : Type
    GlobalIdx = Bits32

    LocalIdx : Type
    LocalIdx = Bits32

    LabelIdx : Type
    LabelIdx = Bits32

-- Definitions from https://webassembly.github.io/spec/core/syntax/types.html
namespace types

    ||| ValType: Basic machine types
    |||
    ||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-valtype
    data ValType = I32 | I64 | F32 | F64

    ||| Packed types
    data PackedType = P8 | P16 | P32

    ||| width: return the width in bits of ValType
    width : ValType -> Nat
    width I32 = 32
    width I64 = 64
    width F32 = 32
    width F64 = 64

    ||| ResultType: classifies the result of executing instructions or blocks
    |||
    ||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-resulttype
    ResultType : Type
    ResultType = Maybe ValType

    ||| FuncType: Function types classify the signature of functions, mapping a
    ||| vector of parameters to a vector of results
    |||
    ||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-functype
    record FuncType where
        constructor MkFuncType
        domain   : Vect n ValType
        -- The spec has this as a vect of length 0 or 1
        codomain : Maybe ValType

    ||| Limits: Limits classify the size range of resizeable storage associated
    ||| with memory types and table types.
    |||
    ||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-limits
    record Limits where
        constructor MkLimits
        min : Int
        max : Maybe Int

    ||| MemType: Memory types classify linear memories and their size range.
    ||| This is currently just an alias to Limits, but to conform to the doc
    ||| and increase readability we separate this out into its own definition.
    |||
    ||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-memtype
    MemType : Type
    MemType = Limits

    ||| ElemType: The element type `funcref` is the infinite union of all
    ||| function types. A table of that type thus contains references to
    ||| functions of heterogeneous type.
    |||
    ||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-elemtype
    ElemType : Type
    -- TODO: Is this correct?
    ElemType = FuncType

    ||| TableType: Table types classify tables over elements of _element types_
    ||| within a size range.
    TableType : Type
    TableType = (Limits, ElemType)

    ||| Is this piece of data mutable or not?
    |||
    ||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-mut
    data Mut = Const | Var

    ||| GlobalType: global types classify `global` variables, which hold a value
    ||| and can either be mutable or immutable
    |||
    ||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-globaltype
    record GlobalType where
        constructor MkGlobalType
        mut  : Mut
        type : ValType

    ||| ExternType: External types classify imports and external values with
    ||| their respective types.
    |||
    ||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-externtype
    data ExternType = ExtFunc   FuncType
                    | ExtTable  TableType
                    | ExtMem    MemType
                    | ExtGlobal GlobalType

    --- Conventions From https://webassembly.github.io/spec/core/syntax/types.html#id1:
    funcs : Vect n ExternType -> (m ** Vect m ExternType)
    funcs = filter (\x => case x of ExtFunc arg => True
                                    _           => False)

    tables : Vect n ExternType -> (m ** Vect m ExternType)
    tables = filter (\x => case x of ExtTable arg => True
                                     _            => False)

    mems : Vect n ExternType -> (m ** Vect m ExternType)
    mems = filter (\x => case x of ExtMem arg => True
                                   _          => False)

    globals : Vect n ExternType -> (m ** Vect m ExternType)
    globals = filter (\x => case x of ExtGlobal arg => True
                                      _             => False)

namespace instructions

    ||| An argument to a memory instruction
    record MemArg where
        constructor MkMemArg
        offset : Bits32
        align  : Bits32

    data Instruction =
        -- Numeric Instructions
        -- For now, I32 only
          I32Const Bits32
        | I32_clz
        | I32_ctz
        | I32_add
        | I32_sub
        | I32_mul
        | I32_div_s
        | I32_div_u
        | I32_rem_s
        | I32_rem_u
        | I32_or
        | I32_xor
        | I32_shl
        | I32_shr_s
        | I32_shr_u
        | I32_rotl
        | I32_rotr
        | I32_eqz
        | I32_eq
        | I32_ne
        | I32_lt_s
        | I32_lt_u
        | I32_gt_s
        | I32_gt_u
        | I32_le_s
        | I32_le_u
        | I32_ge_s
        | I32_ge_u
        -- Parametric Instructions
        | Drop
        | Select
        -- Variable Instructions
        | Local_get LocalIdx
        | Local_set LocalIdx
        | Local_tee LocalIdx
        | Global_get GlobalIdx
        | Global_set GlobalIdx
        -- Memory Instructions
        | I32_load  MemArg
        | I32_store MemArg
        | I32_load8_s  MemArg
        | I32_load8_u  MemArg
        | I32_load16_s MemArg
        | I32_load16_u MemArg
        | I32_store8_s  MemArg
        | I32_store8_u  MemArg
        | I32_store16_s MemArg
        | I32_store16_u MemArg
        | Mem_size
        | Mem_grow
        -- Control Instructions
        | Nop
        | Unreachable
        | Block ResultType (Vect _ Instruction)
        | Loop  ResultType (Vect _ Instruction)
        | If    ResultType (Vect _ Instruction) (Vect _ Instruction)
        | Br    LabelIdx
        | BrIf  LabelIdx
        -- br_table, the first argument (the Vect) is a `vec` type in the WASM
        -- spec, which has the additional constraint that n < 2^32. We will need
        -- to create a new type for this, but creating 2^32 in Nats will be
        -- super expensive. Work around? Just don't worry about it?
        | BrTable (Vect n LabelIdx) LabelIdx
        | Return
        | FnCall FuncIdx
        | FnCall_Indirect TypeIdx

    Expr : Type
    Expr = List Instruction

-- Definitions from https://webassembly.github.io/spec/core/syntax/modules.html
namespace modules
    mutual
        ||| Define the Module type.
        |||
        ||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#syntax-module
        record Module where
            constructor MkModule
            types   : Vect n FuncType
            funcs   : Vect n Func
            tables  : Vect n Table
            mems    : Vect n Mem
            globals : Vect n Global
            elem    : Vect n Elem
            datums  : Vect n Data
            start   : Maybe Start
            imports : Vect n Import
            exports : Vect n Export


        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-start
        record Start where
            constructor MkStart
            func : FuncIdx

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-func
        record Func where
            constructor MkFunc
            type   : TypeIdx
            locals : Vect n ValType
            body   : Expr

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-table
        record Table where
            constructor MkTable
            type : TableType

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-mem
        record Mem where
            constructor MkMem
            type : MemType

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-global
        data Global : Type where

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-elem
        record Elem where
            constructor MkElem
            table  : TableIdx
            offset : Expr     -- XXX: ConstExpr
            init   : Vect n FuncIdx

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-data
        record Data where
            constructor MkData
            datums : MemIdx  -- XXX: Currently, only valid MemIdx is 0 (see note
                             --      at above link for more info)
            offset : Expr    -- XXX: ConstExpr
            init   : Vect n Bits8

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-import
        record Import where
            constructor MkImport
            modul : String
            name  : String
            desc  : ImportDesc

        record ImportDesc where
            constructor MkImportDesc
            func   : TypeIdx
            table  : TableType
            mem    : MemType
            global : GlobalType

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-export
        record Export where
            constructor MkExport
            name : String
            desc : ExportDesc

        record ExportDesc where
            constructor MkExportDesc
            func   : FuncIdx
            table  : TableIdx
            mem    : MemIdx
            global : GlobalIdx


