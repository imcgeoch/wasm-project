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
    config : Config
    stack  : Stack
    expr   : ExecExpr
    status : InterpStatus

-- TODO: It might be useful to pass along a reference to the interp that we
-- tried to execute on

mutual
    ||| Make a single small-step reduction
    oneStep : (interp : Interp) -> Interp
    oneStep (MkInterp config stack expr status) = oneStep' config stack expr

    oneStep' : Config -> Stack -> ExecExpr -> Interp
    oneStep' config stack [] = MkInterp config stack [] StatusSuccess
    oneStep' config stack ((Ins   instr) :: expr) = oneStepInstr config stack expr instr
    oneStep' config stack ((AdIns instr) :: expr) = oneStepAdmin config stack expr instr

    oneStepAdmin : Config -> Stack -> ExecExpr -> AdminInstr -> Interp

    total
    oneStepInstr : Config -> Stack -> ExecExpr -> Instr -> Interp
    oneStepInstr config stack expr (Const constant) = let stack' = ((StVal constant) :: stack) in 
                                                          MkInterp config stack' expr StatusRunning
    oneStepInstr config stack expr (IUnOp op w) = ?oneStepInstr_rhs_2
    oneStepInstr config stack expr (FUnOp op w) = ?oneStepInstr_rhs_3
    oneStepInstr config stack expr instr@(IBinOp op _) =
        case stack of
            [] => ?empty
            x :: [] => ?one_thing
            x :: y :: xs =>
                case (oneStepIBinOp stack op) of
                    Left err => MkInterp config stack ((Ins instr) :: expr) (StatusError $ err)
                    Right s => MkInterp config s expr StatusRunning
    oneStepInstr config stack expr (FBinOp op w) = ?oneStepInstr_rhs_5
    oneStepInstr config stack expr (ITest op w) = ?oneStepInstr_rhs_6
    oneStepInstr config stack expr (IRel op w) = ?oneStepInstr_rhs_7
    oneStepInstr config stack expr (FRel op w) = ?oneStepInstr_rhs_8
    oneStepInstr config stack expr (ConvInstr conv) = ?oneStepInstr_rhs_9
    oneStepInstr config stack expr (MemInstr mem) = ?oneStepInstr_rhs_10
    oneStepInstr config stack expr (ContInstr cont) = oneStepContInstr config stack expr cont

    oneStepConst : Config -> Stack -> ExecExpr -> Constant vt -> Interp
    oneStepConst config stack expr (AConst vt val) = ?oneStepConst_rhs_1

    oneStepIUnOp : Stack -> IUnaryOp -> Either InterpError Stack
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

    oneStepFUnOp : Stack -> FUnaryOp -> Either InterpError Stack

    oneStepIBinOp : Stack -> IBinaryOp -> Either InterpError Stack
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
    applyI32BinOp top nxt (IDiv Unsigned) = ?udiv_rhs
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
    applyI64BinOp top nxt IAdd = Right $ prim__addB64 nxt top
    applyI64BinOp top nxt ISub = Right $ prim__subB64 nxt top
    applyI64BinOp top nxt IMul = Right $ prim__mulB64 nxt top
    applyI64BinOp top nxt (IDiv Signed) = ?sdiv_rhs
    applyI64BinOp top nxt (IDiv Unsigned) = ?udiv_rhs
    applyI64BinOp top nxt (IRem Signed) = ?applyI32BinOp_rhs_3
    applyI64BinOp top nxt (IRem Unsigned) = ?applyI32BinOp_rhs_4
    applyI64BinOp top nxt And = ?applyI32BinOp_rhs_7
    applyI64BinOp top nxt Or = ?applyI32BinOp_rhs_8
    applyI64BinOp top nxt Xor = ?applyI32BinOp_rhs_9
    applyI64BinOp top nxt Shl = ?applyI32BinOp_rhs_10
    applyI64BinOp top nxt (Shr sx) = ?applyI32BinOp_rhs_11
    applyI64BinOp top nxt Rotl = ?applyI32BinOp_rhs_12
    applyI64BinOp top nxt Rotr = ?applyI32BinOp_rhs_13

    {-
    oneStepFBinOp : Stack -> FBinaryOp -> Either (InterpError) Stack

    applyF32BinOp : Bits32 -> Bits32 -> FBinaryOp -> Either InterpError Bits32

    oneStepITest : Config -> Stack -> ExecExpr -> ITestOp -> Width -> Interp

    oneStepIRel : Config -> Stack -> ExecExpr -> IRelationalOp -> Width -> Interp

    oneStepFRel : Config -> Stack -> ExecExpr -> FRelationalOp -> Width -> Interp

    oneStepConvInstr : Config -> Stack -> ExecExpr -> ConversionInstr -> Interp

    oneStepMemInstr : Config -> Stack -> ExecExpr -> MemoryInstr -> Interp
    -}

    oneStepContInstr : Config -> Stack -> ExecExpr -> ControlInstr -> Interp
    oneStepContInstr config stack expr Nop = ?oneStepContInstr_rhs_1
    oneStepContInstr config stack expr Unreachable = ?oneStepContInstr_rhs_2
    oneStepContInstr config stack expr (Block x xs) = ?oneStepContInstr_rhs_3
    oneStepContInstr config stack expr (Loop x xs) = ?oneStepContInstr_rhs_4
    oneStepContInstr config stack expr Return = ?oneStepContInstr_rhs_6
    oneStepContInstr config stack expr (If x thens elses)
       = case stack of
          ((StVal (AConst (IValTp (ITp W32)) val)) :: stack') =>
               let block = (map toExecInstr (if val /= 0 then thens else elses))
               in MkInterp config stack' (block ++ expr) StatusRunning
          _ => MkInterp config stack expr (StatusError $ Err_StackUnderflow "No if cond")

