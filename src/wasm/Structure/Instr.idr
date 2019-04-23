||| Implementation of the Idris spec, these definitions are taken from
||| https://webassembly.github.io/spec/core/syntax/instructions.html
module Structure.Instr

import Structure.Indices
import Structure.Types
import Data.Vect
import Data.Bits

%access public export

||| An argument to a memory instruction
record MemArg where
    constructor MkMemArg
    offset : Bits32
    align  : Bits32

%name MemArg memarg

||| Wasm computations manipulate values of the four basic types.
|||
||| Note: We can possibly remove this as we are just wrapping Idris values, but
|||       I'm keeping it in for now to conform to the spec.
|||
||| Spec: https://webassembly.github.io/spec/core/exec/runtime.html#syntax-val
data Val = I32Val Bits32
         | I64Val Bits64
         | F32Val Void    -- XXX: Can't be created yet
         | F64Val Void    -- XXX: Can't be created yet

implementation Eq Val where
    (I32Val x) == (I32Val y) = x == y
    (I64Val x) == (I64Val y) = x == y
    _ == _ = False

mutual
    ||| https://webassembly.github.io/spec/core/syntax/instructions.html#instructions
    data Instr = Const    Val
               -- Unary operators
               | IUnOp    IUnaryOp       Width
               | FUnOp    FUnaryOp       Width
               -- Binary operators
               | IBinOp   IBinaryOp      Width
               | FBinOp   FBinaryOp      Width
               -- Int Test instructions
               | ITest    ITestOp        Width
               -- Int Relational Ops
               | IRel     IRelationalOp  Width
               | FRel     FRelationalOp  Width
               -- Conversion Instructions
               | I32WrapI64
               | I64ExtendI32  Sign
               | ITruncF       (IntType   w) (FloatType w) Sign
               | F32DemoteF64
               | F64DemoteF32
               | FConvertI     (FloatType w) (IntType   w) Sign
               | IReinterpretF (IntType   w) (FloatType w)
               | FReinterpretI (FloatType w) (IntType   w)
               | Drop
               | Select
               | LocalGet  LocalIdx
               | LocalSet  LocalIdx
               | LocalTee  LocalIdx
               | GlobalGet GlobalIdx
               | GlobalSet GlobalIdx
               -- Memory Instructions
               | ILoad      (IntType   w)         MemArg
               | FLoad      (FloatType w)         MemArg
               | IStore     (IntType   w)         MemArg
               | FStore     (FloatType w)         MemArg
               | ILoad8     (IntType   w) Sign    MemArg
               | ILoad16    (IntType   w) Sign    MemArg
               | I64Load32                Sign    MemArg
               | IStore8    (IntType w)   Sign    MemArg
               | IStore16   (IntType w)   Sign    MemArg
               | I64Store32               Sign    MemArg
               | MemorySize
               | MemoryGrow
               -- Control Instructions
               | Nop
               | Unreachable
               | Block ResultType Expr
               | Loop  ResultType Expr
               | If    ResultType Expr (List Instr)
               | Br    LabelIdx
               | BrIf  LabelIdx
               -- TODO: br_table, the first argument (the Vect) is a `vec` type in the WASM
               -- spec, which has the additional constraint that n < 2^32. We will need
               -- to create a new type for this, but creating 2^32 in Nats will be
               -- super expensive. Work around? Just don't worry about it?
               | BrTable (Vect _ LabelIdx) LabelIdx
               | Return
               | FnCall FuncIdx
               | FnCall_Indirect TypeIdx


    data IUnaryOp = Clz
                  | Ctz
                  | Popcnt

    data FUnaryOp = Abs
                  | Neg
                  | Sqrt
                  | Ceil
                  | Floor
                  | Trunc
                  | Nearest

    data Sign = Signed | Unsigned

    data IBinaryOp = IAdd
                   | ISub
                   | IMul
                   | IDiv Sign
                   | IRem Sign
                   | And
                   | Or
                   | Xor
                   | Shl
                   | Shr Sign
                   | Rotl
                   | Rotr

    data FBinaryOp = FAdd
                   | FSub
                   | FMul
                   | FDiv
                   | FMin
                   | FMax
                   | FCopySign

    data ITestOp = Eqz

    data IRelationalOp = IEq
                       | INe
                       | ILt Sign
                       | IGt Sign
                       | ILe Sign
                       | IGe Sign

    data FRelationalOp = FEq
                       | FNe
                       | FLt
                       | FGt
                       | FLe
                       | FGe






    ||| https://webassembly.github.io/spec/core/syntax/instructions.html#expressions
    Expr : Type
    Expr = List Instr

%name Instr instr
%name Expr expr
%name IUnaryOp op
%name FUnaryOp op
%name IBinaryOp op
%name FBinaryOp op
%name IRelationalOp op
%name FRelationalOp op
%name Sign sx
%name ITestOp op
