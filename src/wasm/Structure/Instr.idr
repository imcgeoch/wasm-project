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

mutual
    ||| https://webassembly.github.io/spec/core/syntax/instructions.html#instructions
    data Instr = Const    (Constant vt)
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
               | ConvInstr ConversionInstr
               -- Memory Instructions
               | MemInstr MemoryInstr
               -- Control Instructions
               | ContInstr ControlInstr

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

    ||| Create a const of a given type
    data Constant : (vt : ValType) ->  Type where
        AConst : (vt : ValType) -> (val : machineType vt) -> Constant vt

    data ParametricInstr = Drop | Select

    data VariableInstr = LocalGet  LocalIdx
                       | LocalSet  LocalIdx
                       | LocalTee  LocalIdx
                       | GlobalGet GlobalIdx
                       | GlobalSet GlobalIdx

    data MemoryInstr = ILoad      (IntType   w)         MemArg
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

    data ConversionInstr = I32WrapI64
                         | I64ExtendI32  Sign
                         | ITruncF       (IntType   w) (FloatType w) Sign
                         | F32DemoteF64
                         | F64DemoteF32
                         | FConvertI     (FloatType w) (IntType   w) Sign
                         | IReinterpretF (IntType   w) (FloatType w)
                         | FReinterpretI (FloatType w) (IntType   w)
                         | ParamInstr ParametricInstr
                         | VarInstr  VariableInstr

    data ControlInstr = Nop
                      | Unreachable
                      | Block ResultType (Vect _ Instr)
                      | Loop  ResultType (Vect _ Instr)
                      | If    ResultType (Vect _ Instr) (Vect _ Instr)
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



    ||| https://webassembly.github.io/spec/core/syntax/instructions.html#expressions
    Expr : Nat -> Type
    Expr n = Vect n Instr

%name Instr instr
%name Expr expr
%name ControlInstr cont
%name ConversionInstr conv
%name IUnaryOp op
%name FUnaryOp op
%name IBinaryOp op
%name FBinaryOp op
%name IRelationalOp op
%name FRelationalOp op
%name Sign sx
%name Constant constant
%name MemoryInstr mem
%name ITestOp op
