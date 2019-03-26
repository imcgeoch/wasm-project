||| Prototype interpreter, this should be stand alone for now. We can pull stuff
||| like type defs out into a separate file later when we want to get the
||| validator hooked up

module Structure.Instructions

import Structure.Indices
import Structure.Types
import Data.Vect
import Data.Bits

%access public export

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



