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
    offset : Nat
    align  : Bits32

%name MemArg memarg

||| Wasm computations manipulate values of the four basic types.
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

Show Val where
    show (I32Val x) = "(i32 " ++ (show x) ++ ")"
    show (I64Val x) = "(i64 " ++ (show x) ++ ")"
    show (F32Val x) = "(f32 ???)"
    show (F64Val x) = "(f64 ???)"

Show IUnaryOp where
    show Clz = "clz"
    show Ctz = "ctz"
    show Popcnt = "popcnt"

Show FUnaryOp where
    show Abs = "abs"
    show Neg = "neg"
    show Sqrt = "sqrt"
    show Ceil = "ceil"
    show Floor = "floor"
    show Trunc = "trunc"
    show Nearest = "nearest"

Show Sign where
    show Signed = "s"
    show Unsigned = "u"

Show MemArg where
    show (MkMemArg offset align) = "(memarg " ++ (show offset) ++ "," ++ (show align) ++ ")"

Show IBinaryOp where
    show IAdd = "iadd"
    show ISub = "isub"
    show IMul = "imul"
    show (IDiv sx) = "idiv" ++ (show sx)
    show (IRem sx) = "irem" ++ (show sx)
    show And = "iand"
    show Or = "ior"
    show Xor = "ixor"
    show Shl = "ishl"
    show (Shr sx) = "ishr" ++ (show sx)
    show Rotl = "irotl"
    show Rotr = "irotr"

total
Show Instr where
    show (Const x) = show  x
    show (IUnOp op w) = (show op) ++ "_" ++ (show w)
    show (FUnOp op w) = (show op) ++ "_" ++ (show w)
    show (IBinOp op w) = (show op) ++ "_" ++ (show w)
    show (FBinOp op w) = "<fbinop>"
    show (ITest op w) = "<itestop>"
    show (IRel op w) = "<irelop>"
    show (FRel op w) = "<frelop>"
    show I32WrapI64 = "<i32wrapi64>"
    show (I64ExtendI32 sx) = "<i64extendi32 " ++ (show sx) ++ ">"
    show (ITruncF int_t float_t sx) = "<itruncf>"
    show F32DemoteF64 = "f32demotef64"
    show F64DemoteF32 = "f64demotef32"
    show (FConvertI float_t int_t sx) = "<fconverti>"
    show (IReinterpretF int_t float_t) = "ireinterpretf"
    show (FReinterpretI float_t int_t) = "freinterpteti"
    show Drop = "drop"
    show Select = "select"
    show (LocalGet x) = "(local-get " ++ (show x) ++ ")"
    show (LocalSet x) = "(local-set " ++ (show x) ++ ")"
    show (LocalTee x) = "(local-tee " ++ (show x) ++ ")"
    show (GlobalGet x) = "(global-get " ++ (show x) ++ ")"
    show (GlobalSet x) = "(global-set " ++ (show x) ++ ")"
    show (ILoad (ITp w) memarg) = "(i" ++ (show w) ++ "load " ++ (show memarg) ++ ")"
    show (FLoad (FTp w) memarg) = "(f" ++ (show w) ++ "load " ++ (show memarg) ++ ")"
    show (IStore (ITp w) memarg) = "(i" ++ (show w) ++ "store " ++ (show memarg) ++ ")"
    show (FStore (FTp w) memarg) = "(f" ++ (show w) ++ "store " ++ (show memarg) ++ ")"
    --show (ILoad8 (ITp w) sx memarg) = ?rhs_2
    --show (ILoad16 (ITp w) sx memarg) = ?rhs_3
    --show (I64Load32 sx memarg) = ?rhs_30
    --show (IStore8 int_t sx memarg) = ?rhs_31
    --show (IStore16 int_t sx memarg) = ?rhs_32
    --show (I64Store32 sx memarg) = ?rhs_33
    show MemorySize = "mem_size"
    show MemoryGrow = "mem_grow"
    show Nop = "nop"
    show Unreachable = "unreachable"
    show (Block rt xs) = assert_total $ "(block " ++ (show rt) ++ ", " ++ (show xs) ++ ")"
    show (Loop x xs)   = assert_total $ "(loop " ++ (show x) ++ ", " ++ (show xs) ++ ")"
    show (If x xs ys)  = assert_total $ "(if " ++ (show x) ++ " then " ++ (show xs) ++ " else " ++ (show ys) ++ ")"
    show (Br x) = "br"
    show (BrIf x) = "(br-if " ++ (show x) ++ ")"
    -- show (BrTable xs x) = ?rhs_43
    show Return = "return"
    -- show (FnCall x) = ?rhs_45
    -- show (FnCall_Indirect x) = ?rhs_46
    show _ = "(instr not showable yet!)"
