module Execution.JankInterp


import Execution.Runtime
import Structure.Instr
import Structure.Types
import Util.BitUtil
import Data.Vect
import Data.Bits

%access public export
%default total

data InterpError : Type where
  Err_StackUnderflow : String -> InterpError
  Err_StackTypeError : String -> InterpError
  Err_StackWidthError : String -> InterpError
  Err_InvalidInstruction : String -> InterpError

data InterpStatus : Type where
  StatusRunning   :  InterpStatus
  StatusSuccess   :  InterpStatus
  StatusTrapped   :  InterpStatus
  StatusError     :  InterpError -> InterpStatus
  StatusInitiated :  InterpStatus

record Interp where
    constructor MkInterp
    config : Config n
    stack  : Stack m
    expr   : ExecExpr k
    status : InterpStatus

-- TODO: It might be useful to pass along a reference to the interp that we
-- tried to execute on

mutual
    ||| Make a single small-step reduction
    oneStep : (interp : Interp) -> Interp
    oneStep (MkInterp config stack expr status) = oneStep' config stack expr

    oneStep' : Config l -> Stack m -> ExecExpr n -> Interp
    oneStep' config stack [] = ?status_success_rhs
    oneStep' config stack ((Ins   instr) :: expr) = oneStepInstr config stack expr instr
    oneStep' config stack ((AdIns instr) :: expr) = oneStepAdmin config stack expr instr

    oneStepAdmin : Config l -> Stack m -> ExecExpr n -> AdminInstr -> Interp

    total
    oneStepInstr : Config l -> Stack m -> ExecExpr n -> Instr -> Interp
    oneStepInstr config stack expr (Const constant) = ?oneStepInstr_rhs_1
    oneStepInstr config stack expr (IUnOp op w) = ?oneStepInstr_rhs_2
    oneStepInstr config stack expr (FUnOp op w) = ?oneStepInstr_rhs_3
    oneStepInstr config stack expr (IBinOp op _) = 
        case stack of
            [] => ?empty
            x :: [] => ?one_thing
            x :: y :: xs => 
                case (oneStepIBinOp stack op) of
                    Left err => ?arsarst
                    Right s => ?status_running_interp
    oneStepInstr config stack expr (FBinOp op w) = ?oneStepInstr_rhs_5
    oneStepInstr config stack expr (ITest op w) = ?oneStepInstr_rhs_6
    oneStepInstr config stack expr (IRel op w) = ?oneStepInstr_rhs_7
    oneStepInstr config stack expr (FRel op w) = ?oneStepInstr_rhs_8
    oneStepInstr config stack expr (ConvInstr conv) = ?oneStepInstr_rhs_9
    oneStepInstr config stack expr (MemInstr mem) = ?oneStepInstr_rhs_10
    oneStepInstr config stack expr (ContInstr cont) = ?oneStepInstr_rhs_11

    oneStepConst : Config l -> Stack m -> ExecExpr n -> Constant vt val -> Interp
    oneStepConst config stack expr (AConst vt val) = ?oneStepConst_rhs_1

    oneStepIUnOp : Stack m -> IUnaryOp -> Either InterpError (Stack m)
    oneStepIUnOp [] _           = Left (Err_StackUnderflow "Unop on empty stack")
    oneStepIUnOp ((StLabel x) :: xs) _ = Left $ Err_InvalidInstruction "insert pun here"
    oneStepIUnOp ((StFrame x) :: xs) _ = Left $ Err_InvalidInstruction ""
    oneStepIUnOp ((StVal (AConst vt bits)) :: xs) op =
        case op of
             Clz => (case vt of
                          (IValTp (ITp W32)) => let top : Bits32 = clz32 bits in
                                                    Right $ (StVal (AConst (IValTp (ITp W32)) top)) :: xs
                          (IValTp (ITp W64)) => let top : Bits32 = clz64 bits in
                                                    Right $ (StVal (AConst (IValTp (ITp W32)) top)) :: xs
                          (FValTp float_t) => Left (Err_StackTypeError "IUnOp CLZ applied to float"))
             Ctz => (case vt of
                          (IValTp (ITp W32)) => let top : Bits32 = ctz32 bits in
                                                    Right $ (StVal (AConst (IValTp (ITp W32)) top)) :: xs
                          (IValTp (ITp W64)) => let top : Bits32 = ctz64 bits in
                                                    Right $ (StVal (AConst (IValTp (ITp W32)) top)) :: xs
                          (FValTp float_t) => Left (Err_StackTypeError "IUnOp CTZ applied to float"))

             Popcnt => ?rhs_3

    oneStepFUnOp : Stack m -> FUnaryOp -> Either InterpError (Stack m)

    oneStepIBinOp : Stack (S (S m)) -> IBinaryOp -> Either InterpError (Stack (S m))
    oneStepIBinOp ((StVal (AConst vt bits)) :: ((StVal (AConst vt' bits')) :: xs)) op
           =  case (decEq vt vt') of
                (Yes Refl) => case vt' of
                               (IValTp (ITp W32)) =>
                                    (case applyI32BinOp bits bits' op of
                                         Right bits2 =>
                                               let x = StVal (AConst (IValTp (ITp W32)) bits2) in
                                                 Right (x :: xs)
                                         Left err => Left err)
                               (IValTp (ITp W64)) =>
                                   (case applyI64BinOp bits bits' op of
                                         Right bits2 =>
                                               let x = StVal (AConst (IValTp (ITp W64)) bits2) in
                                                 Right (x :: xs)
                                         Left err => Left err)
                               _  => Left $ Err_InvalidInstruction "Float operation applied to Int"
                (No contra) => Left $ Err_StackTypeError "BinOp applied to different types"

    oneStepIBinOp ((StVal _) :: (_ :: xs)) _ = Left $ Err_InvalidInstruction "Bad 1"
    oneStepIBinOp _ _ = Left $ Err_InvalidInstruction "Bad 2"


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

    {-
    oneStepFBinOp : Stack (S m) -> FBinaryOp -> Either (InterpError) (Stack m)

    applyF32BinOp : Bits32 -> Bits32 -> FBinaryOp -> Either InterpError Bits32

    oneStepITest : Config l -> Stack m -> ExecExpr n -> ITestOp -> Width -> Interp

    oneStepIRel : Config l -> Stack m -> ExecExpr n -> IRelationalOp -> Width -> Interp

    oneStepFRel : Config l -> Stack m -> ExecExpr n -> FRelationalOp -> Width -> Interp

    oneStepConvInstr : Config l -> Stack m -> ExecExpr n -> ConversionInstr -> Interp

    oneStepMemInstr : Config l -> Stack m -> ExecExpr n -> MemoryInstr -> Interp

    oneStepContInstr : Config l -> Stack m -> ExecExpr n -> ControlInstr -> Interp
    -}
