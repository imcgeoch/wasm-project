module Execution.JankInterp


import Execution.Runtime
import Structure.Instr
import Structure.Types
import Data.Vect
import Data.Bits

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
  Err_StackUnderflow : String -> InterpError
  Err_StackTypeError : String -> InterpError
  Err_StackWidthError : String -> InterpError
  Err_InvalidInstruction : String -> InterpError

data InterpStatus : Type where
  StatusRunning :  InterpStatus
  StatusSuccess :  InterpStatus
  StatusTrapped :  InterpStatus
  StatusError   :  InterpError -> InterpStatus

mutual
    ||| Make a single small-step reduction
    oneStep : (interp : Interp) -> InterpStatus
    oneStep (MkInterp config stack expr) = oneStep' config stack expr

    oneStep' : Config l -> Stack m -> ExecExpr n -> InterpStatus
    oneStep' config stack [] = StatusSuccess
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

    oneStepConst : Config l -> Stack m -> ExecExpr n -> Constant vt val -> InterpStatus
    oneStepConst config stack expr (AConst vt val) = ?oneStepConst_rhs_1

    oneStepIUnOp : Config l -> Stack m -> ExecExpr n -> IUnaryOp -> Width -> InterpStatus
    oneStepIUnOp config stack expr Clz width = ?oneStepIUnOp_rhs_1
    oneStepIUnOp config stack expr Ctz width = ?oneStepIUnOp_rhs_2
    oneStepIUnOp config stack expr Popcnt width = ?oneStepIUnOp_rhs_3

    oneStepFUnOp : Config l -> Stack m -> ExecExpr n -> FUnaryOp -> Width -> InterpStatus

    oneStepIBinOp : Config l -> Stack m -> ExecExpr n -> IBinaryOp -> Width -> InterpStatus
    oneStepIBinOp _ [] _ _ _ = StatusError $ Err_StackUnderflow "IBinOp applied to empty stack"
    oneStepIBinOp _ (x :: []) _ _ _ = StatusError $ Err_StackUnderflow "IBinOp applied to size-1 stack"
    oneStepIBinOp config ((StVal (AConst vt bits)) :: ((StVal (AConst vt' bits')) :: xs)) expr op width =
        case (decEq vt vt') of
             (Yes prf) => case machineType vt of
                               case_val => ?rhs_1 --let res = applyI32BinOp bits bits' op in ?rhs
             (No contra) => StatusError $ Err_StackTypeError "BinOp applied to different types"

    oneStepIBinOp _ ((StVal _) :: (_ :: xs)) _ _ _ = ?oneStepIBinOp_rhs_7
    oneStepIBinOp _ _ _ _ _ = ?oneStepIBinOp_rhs_5

    -- TODO: We need to add a div-by-zero error and a Bits32-Not-0 type that we can pass in
    partial
    applyI32BinOp : Bits32 -> Bits32 -> IBinaryOp -> Bits32
    applyI32BinOp top nxt IAdd = prim__addB32 nxt top
    applyI32BinOp top nxt ISub = prim__subB32 nxt top
    applyI32BinOp top nxt IMul = prim__mulB32 nxt top
    applyI32BinOp top nxt (IDiv Signed) = prim__sdivB32 nxt top
    applyI32BinOp top nxt (IDiv Unsigned) = prim__udivB32 nxt top
    applyI32BinOp top nxt (IRem Signed) = ?applyI32BinOp_rhs_3
    applyI32BinOp top nxt (IRem Unsigned) = ?applyI32BinOp_rhs_4
    applyI32BinOp top nxt And = ?applyI32BinOp_rhs_7
    applyI32BinOp top nxt Or = ?applyI32BinOp_rhs_8
    applyI32BinOp top nxt Xor = ?applyI32BinOp_rhs_9
    applyI32BinOp top nxt Shl = ?applyI32BinOp_rhs_10
    applyI32BinOp top nxt (Shr sx) = ?applyI32BinOp_rhs_11
    applyI32BinOp top nxt Rotl = ?applyI32BinOp_rhs_12
    applyI32BinOp top nxt Rotr = ?applyI32BinOp_rhs_13

    oneStepFBinOp : Config l -> Stack m -> ExecExpr n -> FBinaryOp -> Width -> InterpStatus

    oneStepITest : Config l -> Stack m -> ExecExpr n -> ITestOp -> Width -> InterpStatus

    oneStepIRel : Config l -> Stack m -> ExecExpr n -> IRelationalOp -> Width -> InterpStatus

    oneStepFRel : Config l -> Stack m -> ExecExpr n -> FRelationalOp -> Width -> InterpStatus

    oneStepConvInstr : Config l -> Stack m -> ExecExpr n -> ConversionInstr -> InterpStatus

    oneStepMemInstr : Config l -> Stack m -> ExecExpr n -> MemoryInstr -> InterpStatus

    oneStepContInstr : Config l -> Stack m -> ExecExpr n -> ControlInstr -> InterpStatus
