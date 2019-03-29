||| Implementation of the Spec, defs taken from
||| https://webassembly.github.io/spec/core/syntax/types.html
module Types

import Data.Vect

%access public export

-- Definitions from https://webassembly.github.io/spec/core/syntax/types.html
data Width = W32 | W64

%name Width width

data IntType : Width -> Type where
    ITp : (w : Width) -> IntType w

%name IntType int_t

data FloatType : Width -> Type where
    FTp : (w : Width) -> FloatType w

%name FloatType float_t

data PackedType = Packed8
                | Packed16
                | Packed32
    
%name PackedType pack_t

||| ValType: Basic machine types
|||
||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-valtype
data ValType = IValTp (IntType w) | FValTp (FloatType w)

%name ValType val_t

I32_t : ValType
I32_t = IValTp (ITp W32)

I64_t : ValType
I64_t = IValTp (ITp W64)

F32_t : ValType
F32_t = FValTp (FTp W32)

F64_t : ValType
F64_t = FValTp (FTp W64)

width' : Width -> Nat
width' W32 = 32
width' W64 = 64

||| Get the width in bits of a ValType
width : ValType -> Nat
width (IValTp (ITp w)) = width' w
width (FValTp (FTp w)) = width' w



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

%name FuncType func_t

||| Limits: Limits classify the size range of resizeable storage associated
||| with memory types and table types.
|||
||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-limits
record Limits where
    constructor MkLimits
    min : Int
    max : Maybe Int

%name Limits lims

||| MemType: Memory types classify linear memories and their size range.
||| This is currently just an alias to Limits, but to conform to the doc
||| and increase readability we separate this out into its own definition.
|||
||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#syntax-memtype
MemType : Type
MemType = Limits

%name MemType mem_t

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
data ExternType = ExtFuncTp   FuncType
                | ExtTableTp  TableType
                | ExtMemTp    MemType
                | ExtGlobalTp GlobalType

--- Conventions From https://webassembly.github.io/spec/core/syntax/types.html#id1:
funcs : Vect n ExternType -> (m ** Vect m ExternType)
funcs = filter (\x => case x of ExtFuncTp arg => True
                                _           => False)

tables : Vect n ExternType -> (m ** Vect m ExternType)
tables = filter (\x => case x of ExtTableTp arg => True
                                 _            => False)

mems : Vect n ExternType -> (m ** Vect m ExternType)
mems = filter (\x => case x of ExtMemTp arg => True
                               _          => False)

globals : Vect n ExternType -> (m ** Vect m ExternType)
globals = filter (\x => case x of ExtGlobalTp arg => True
                                  _             => False)
