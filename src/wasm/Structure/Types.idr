module Types

import Data.Vect

%access public export

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
