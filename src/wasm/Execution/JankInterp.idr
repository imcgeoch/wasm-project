module Execution.JankInterp


import Execution.Runtime
import Structure.Instr
import Structure.Types
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


data InterpError : Type where
  Err_StackUnderflow : Interp -> InterpError
  Err_StackTypeError : Interp -> InterpError

data InterpStatus : Type where
  StatusRunning : Interp -> InterpStatus
  StatusSuccess : Interp -> InterpStatus
  StatusTrapped : Interp -> InterpStatus
  StatusError   : InterpError -> InterpStatus

mutual
    ||| Make a single small-step reduction
    oneStep : (interp : Interp) -> InterpStatus
    oneStep (MkInterp config stack expr) = oneStep' config stack expr

    oneStep' : Config l -> Stack m -> ExecExpr n -> InterpStatus
    oneStep' config stack [] = StatusSuccess $ MkInterp config stack []
    oneStep' config stack ((Ins   instr) :: expr) = oneStepInstr config stack expr instr
    oneStep' config stack ((AdIns instr) :: expr) = oneStepAdmin config stack expr instr

    oneStepAdmin : Config l -> Stack m -> ExecExpr n -> AdminInstr -> InterpStatus

    total
    oneStepInstr : Config l -> Stack m -> ExecExpr n -> Instr -> InterpStatus
    oneStepInstr config stack expr (Const constant) = ?oneStepInstr_rhs_1
    oneStepInstr config stack expr (IUnOp op width) = ?oneStepInstr_rhs_2
    oneStepInstr config stack expr (FUnOp op width) = ?oneStepInstr_rhs_3
    oneStepInstr config stack expr (IBinOp op width) = ?oneStepInstr_rhs_4
    oneStepInstr config stack expr (FBinOp op width) = ?oneStepInstr_rhs_5
    oneStepInstr config stack expr (ITest op width) = ?oneStepInstr_rhs_6
    oneStepInstr config stack expr (IRel op width) = ?oneStepInstr_rhs_7
    oneStepInstr config stack expr (FRel op width) = ?oneStepInstr_rhs_8
    oneStepInstr config stack expr (ConvInstr conv) = ?oneStepInstr_rhs_9
    oneStepInstr config stack expr (MemInstr mem) = ?oneStepInstr_rhs_10
    oneStepInstr config stack expr (ContInstr cont) = ?oneStepInstr_rhs_11
