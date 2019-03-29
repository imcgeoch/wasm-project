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

machineType : ValType -> Type
machineType (IValTp (ITp W32)) = Bits32
machineType (IValTp (ITp W64)) = Void
machineType (FValTp (FTp W32)) = Void
machineType (FValTp (FTp W64)) = Void

||| Create a const of a given type
data Const : (vt : ValType) -> machineType vt -> Type where
    AConst : (vt : ValType) -> (val : machineType vt) -> Const vt val

||| https://webassembly.github.io/spec/core/syntax/instructions.html#instructions
data Instr =
    -- Numeric Instructions
    -- For now, I32 only
      I32Const Bits32
    | IUnOp    IUnaryOp       Width
    | IBinOp   IBinaryOp      Width
    | FUnOp    FUnaryOp       Width
    | FBinOp   FBinaryOp      Width
    | ITest    ITestOp        Width
    | IRel     IRelationalOp  Width
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
    | Block ResultType (Vect _ Instr)
    | Loop  ResultType (Vect _ Instr)
    | If    ResultType (Vect _ Instr) (Vect _ Instr)
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

		--- ADMINISTRATIVE INSTRUCTIONS ---
		-- The following are administrative instructions that are defined in
    -- https://webassembly.github.io/spec/core/exec/runtime.html#administrative-instructions
    -- These are not available to the programmer and are only introduced at
    -- runtime. As such, it would be good practice to mirror the Instructions
    -- datatype, call this ExecInstructions, with the obvious injection
    -- Instructions -> ExecInstructions, and simply add in the extra
    -- administrative instructions. For simplicity we list the admin
    -- instructions here, but if this becomes an issue this can be fixed down
    -- the line with relatively little pain.

||| https://webassembly.github.io/spec/core/syntax/instructions.html#expressions
Expr : Nat -> Type
Expr n = Vect n Instr

