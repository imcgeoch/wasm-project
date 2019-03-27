module Execution.JankInterp

import Execution.Runtime
import Structure.Instr
import Data.Vect

%access public export
%default total

record Interp where
    constructor MkInterp
    config : Config n
    stack  : Stack m
    expr   : ExecExpr k

-- TODO: It might be useful to pass along a reference to the interp that we
-- tried to execute on
||| When an interpreters execution completes, return a code and a possible
||| message.
data Terminate = Complete | Trapped | OtherErr String | NotImpl String

mutual
    ||| Make a single small-step reduction
    oneStep : Interp -> Either Interp Terminate
    oneStep (MkInterp config stack []) = Right Complete
    oneStep (MkInterp config stack ((AdIns ins) :: xs)) = oneStepAdmin config stack xs ins
    oneStep (MkInterp config stack ((Ins ins) :: xs)) = oneStepInstr config stack xs ins

    oneStepAdmin : Config l -> Stack m -> ExecExpr n -> AdminInstr -> Either Interp Terminate
    oneStepAdmin conf stack expr Trap = Right $ Trapped
    oneStepAdmin conf stack expr (Invoke k) = Right $ NotImpl "Invoke"
    oneStepAdmin conf stack expr (InitData k x xs) = Right $ NotImpl "InitData"
    oneStepAdmin conf stack expr (Lab x xs) = Right $ NotImpl "Lab"
    oneStepAdmin conf stack expr (Frm x xs) = Right $ NotImpl "Frame"

    oneStepInstr : Config l -> Stack m -> ExecExpr n -> Instr -> Either Interp Terminate
    oneStepInstr conf stack expr (I32Const x) = Left $ MkInterp conf ((StVal (I32Val x)) :: stack) expr
    oneStepInstr conf stack expr I32_clz = ?oneStepInstr_rhs_2
    oneStepInstr conf stack expr I32_ctz = ?oneStepInstr_rhs_3
    oneStepInstr conf stack expr I32_add = ?oneStepInstr_rhs_4
    oneStepInstr conf stack expr I32_sub = ?oneStepInstr_rhs_5
    oneStepInstr conf stack expr I32_mul = ?oneStepInstr_rhs_6
    oneStepInstr conf stack expr I32_div_s = ?oneStepInstr_rhs_7
    oneStepInstr conf stack expr I32_div_u = ?oneStepInstr_rhs_8
    oneStepInstr conf stack expr I32_rem_s = ?oneStepInstr_rhs_9
    oneStepInstr conf stack expr I32_rem_u = ?oneStepInstr_rhs_10
    oneStepInstr conf stack expr I32_or = ?oneStepInstr_rhs_11
    oneStepInstr conf stack expr I32_xor = ?oneStepInstr_rhs_12
    oneStepInstr conf stack expr I32_shl = ?oneStepInstr_rhs_13
    oneStepInstr conf stack expr I32_shr_s = ?oneStepInstr_rhs_14
    oneStepInstr conf stack expr I32_shr_u = ?oneStepInstr_rhs_15
    oneStepInstr conf stack expr I32_rotl = ?oneStepInstr_rhs_16
    oneStepInstr conf stack expr I32_rotr = ?oneStepInstr_rhs_17
    oneStepInstr conf stack expr I32_eqz = ?oneStepInstr_rhs_18
    oneStepInstr conf stack expr I32_eq = ?oneStepInstr_rhs_19
    oneStepInstr conf stack expr I32_ne = ?oneStepInstr_rhs_20
    oneStepInstr conf stack expr I32_lt_s = ?oneStepInstr_rhs_21
    oneStepInstr conf stack expr I32_lt_u = ?oneStepInstr_rhs_22
    oneStepInstr conf stack expr I32_gt_s = ?oneStepInstr_rhs_23
    oneStepInstr conf stack expr I32_gt_u = ?oneStepInstr_rhs_24
    oneStepInstr conf stack expr I32_le_s = ?oneStepInstr_rhs_25
    oneStepInstr conf stack expr I32_le_u = ?oneStepInstr_rhs_26
    oneStepInstr conf stack expr I32_ge_s = ?oneStepInstr_rhs_27
    oneStepInstr conf stack expr I32_ge_u = ?oneStepInstr_rhs_28
    oneStepInstr conf stack expr Drop = ?oneStepInstr_rhs_29
    oneStepInstr conf stack expr Select = ?oneStepInstr_rhs_30
    oneStepInstr conf stack expr (I32_load x) = ?oneStepInstr_rhs_31
    oneStepInstr conf stack expr (I32_store x) = ?oneStepInstr_rhs_32
    oneStepInstr conf stack expr (I32_load8_s x) = ?oneStepInstr_rhs_33
    oneStepInstr conf stack expr (I32_load8_u x) = ?oneStepInstr_rhs_34
    oneStepInstr conf stack expr (I32_load16_s x) = ?oneStepInstr_rhs_35
    oneStepInstr conf stack expr (I32_load16_u x) = ?oneStepInstr_rhs_36
    oneStepInstr conf stack expr (I32_store8_s x) = ?oneStepInstr_rhs_37
    oneStepInstr conf stack expr (I32_store8_u x) = ?oneStepInstr_rhs_38
    oneStepInstr conf stack expr (I32_store16_s x) = ?oneStepInstr_rhs_39
    oneStepInstr conf stack expr (I32_store16_u x) = ?oneStepInstr_rhs_40
    oneStepInstr conf stack expr Mem_size = ?oneStepInstr_rhs_41
    oneStepInstr conf stack expr Mem_grow = ?oneStepInstr_rhs_42
    oneStepInstr conf stack expr Nop = ?oneStepInstr_rhs_43
    oneStepInstr conf stack expr Unreachable = ?oneStepInstr_rhs_44
    oneStepInstr conf stack expr Return = ?oneStepInstr_rhs_45

