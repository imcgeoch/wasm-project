module Execution.JankInterp


import Execution.Runtime
import Structure.Instr
import Structure.Types
import Util.BitUtil
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

    oneStepIUnOp : Stack m -> IUnaryOp -> Either InterpError (Stack m)
    oneStepIUnOp [] _           = Left (Err_StackUnderflow "Unop on empty stack")
    oneStepIUnOp ((StLabel x) :: xs) _ = Left $ Err_InvalidInstruction "insert pun here"
    oneStepIUnOp ((StFrame x) :: xs) _ = Left $ Err_InvalidInstruction ""
    oneStepIUnOp ((StVal (AConst vt bits)) :: xs) op =
        case op of
             Clz => (case vt of
                          (IValTp (ITp W32)) => ?rhs_1
                          (IValTp (ITp W64)) => ?rhs_7
                          (FValTp float_t) => Left (Err_StackTypeError "IUnOp CLZ applied to float"))
             Ctz => ?rhs_2
             Popcnt => ?rhs_3

    oneStepFUnOp : Stack m -> FUnaryOp -> Either InterpError (Stack m)

    oneStepIBinOp : Stack (S m) -> IBinaryOp -> Either InterpError (Stack m)
    -- oneStepIBinOp [] _
    --       = Left $ Err_StackUnderflow "IBinOp applied to empty stack"
    oneStepIBinOp (x :: []) _
           = Left $ Err_StackUnderflow "IBinOp applied to size-1 stack"
    oneStepIBinOp ((StVal (AConst vt bits)) :: ((StVal (AConst vt' bits')) :: xs)) op
           =  case (decEq vt vt') of
                (Yes Refl) => case vt' of
                               (IValTp (ITp W32)) =>
                                    (case applyI32BinOp bits bits' op of
                                         Right bits'' =>
                                               let x = StVal (AConst (IValTp (ITp W32)) bits'') in
                                                 Right (x :: xs)
                                         Left err => Left err)
                               (IValTp (ITp W64)) => ?rhs_4
                               _  => Left $ Err_InvalidInstruction "Float operation applied to Int"
                (No contra) => Left $ Err_StackTypeError "BinOp applied to different types"

    oneStepIBinOp ((StVal _) :: (_ :: xs)) _ = ?oneStepIBinOp_rhs_7
    oneStepIBinOp _ _ = ?oneStepIBinOp_rhs_5


    -- TODO: We need to add a div-by-zero error and a Bits32-Not-0 type that we can pass in
    partial
    applyI32BinOp : Bits32 -> Bits32 -> IBinaryOp -> Either InterpError Bits32
    applyI32BinOp top nxt IAdd = Right $ prim__addB32 nxt top
    applyI32BinOp top nxt ISub = Right $ prim__subB32 nxt top
    applyI32BinOp top nxt IMul = Right $ prim__mulB32 nxt top
    applyI32BinOp top nxt (IDiv Signed) = ?sdiv_rhs
    applyI32BinOp top nxt (IDiv Unsigned) = ?udiv_rhs  -- prim__udivB32 nxt top
    applyI32BinOp top nxt (IRem Signed) = ?applyI32BinOp_rhs_3
    applyI32BinOp top nxt (IRem Unsigned) = ?applyI32BinOp_rhs_4
    applyI32BinOp top nxt And = ?applyI32BinOp_rhs_7
    applyI32BinOp top nxt Or = ?applyI32BinOp_rhs_8
    applyI32BinOp top nxt Xor = ?applyI32BinOp_rhs_9
    applyI32BinOp top nxt Shl = ?applyI32BinOp_rhs_10
    applyI32BinOp top nxt (Shr sx) = ?applyI32BinOp_rhs_11
    applyI32BinOp top nxt Rotl = ?applyI32BinOp_rhs_12
    applyI32BinOp top nxt Rotr = ?applyI32BinOp_rhs_13

    applyI64BinOp : Bits64 -> Bits64 -> IBinaryOp -> Either InterpError Bits64
    applyI64BinOp _ _ = ?applyI64BinOp_rhs

    oneStepFBinOp : Stack (S m) -> FBinaryOp -> Either (InterpError) (Stack m)

    applyF32BinOp : Bits32 -> Bits32 -> FBinaryOp -> Either InterpError Bits32

    oneStepITest : Config l -> Stack m -> ExecExpr n -> ITestOp -> Width -> InterpStatus

    oneStepIRel : Config l -> Stack m -> ExecExpr n -> IRelationalOp -> Width -> InterpStatus

    oneStepFRel : Config l -> Stack m -> ExecExpr n -> FRelationalOp -> Width -> InterpStatus

    oneStepConvInstr : Config l -> Stack m -> ExecExpr n -> ConversionInstr -> InterpStatus

    oneStepMemInstr : Config l -> Stack m -> ExecExpr n -> MemoryInstr -> InterpStatus

    oneStepContInstr : Config l -> Stack m -> ExecExpr n -> ControlInstr -> InterpStatus
