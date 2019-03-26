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

||| https://webassembly.github.io/spec/core/syntax/instructions.html#instructions
data Instr =
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

