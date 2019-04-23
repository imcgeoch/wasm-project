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
    oneStepAdmin config stack expr Trap = MkInterp config stack ((AdIns Trap) :: expr) StatusTrapped
    oneStepAdmin config stack expr (Invoke k) = ?oneStepAdmin_rhs_2
    oneStepAdmin config stack expr (InitData k x xs) = ?oneStepAdmin_rhs_3
    oneStepAdmin config stack expr (Lab (MkLabel arity cont) vs []) = MkInterp config (vs ++ stack) expr StatusRunning
    oneStepAdmin config stack expr (Lab (MkLabel arity cont) vs (e :: es)) =
        case e of
             (Ins instr) => ?oneStepAdmin_rhs_1
             (AdIns instr) =>
                    (case instr of
                          (Breaking Z vs') => if length vs' < arity then MkInterp config stack expr (StatusError $ Err_StackUnderflow "Underflow while breaking")
                                                                    else MkInterp config ((take arity vs') ++ stack) expr StatusRunning
                          (Breaking (S k) vs') => MkInterp config stack (AdIns (Breaking k vs') :: expr) StatusRunning
                          Trap => MkInterp config stack expr StatusTrapped
                          (Invoke k) => ?oneStepAdmin_rhs_7
                          (InitData k x xs) => ?oneStepAdmin_rhs_8
                          (Lab (MkLabel arity cont) vs es') => ?oneStepAdmin_rhs_4
                          (Frm x xs) => ?oneStepAdmin_rhs_10)

    oneStepAdmin config stack expr (Frm x xs) = ?oneStepAdmin_rhs_5
    oneStepAdmin c s e (Breaking n es) = MkInterp c s e (StatusError $ Err_InvalidInstruction "Breaking error")

    total
    oneStepInstr : Config -> Stack -> ExecExpr -> Instr -> Interp
    oneStepInstr config stack expr instr =
        case instr of
             (Const x) => ?oneStepInstr_rhs_1
             (IUnOp op w) => ?oneStepInstr_rhs_2
             (FUnOp op w) => ?oneStepInstr_rhs_3
             (IBinOp op w) => ?oneStepInstr_rhs_4
             (FBinOp op w) => ?oneStepInstr_rhs_5
             (ITest op w) => ?oneStepInstr_rhs_6
             (IRel op w) => ?oneStepInstr_rhs_7
             (FRel op w) => ?oneStepInstr_rhs_8
             I32WrapI64 => ?oneStepInstr_rhs_9
             (I64ExtendI32 sx) => ?oneStepInstr_rhs_10
             (ITruncF int_t float_t sx) => ?oneStepInstr_rhs_11
             F32DemoteF64 => ?oneStepInstr_rhs_12
             F64DemoteF32 => ?oneStepInstr_rhs_13
             (FConvertI float_t int_t sx) => ?oneStepInstr_rhs_14
             (IReinterpretF int_t float_t) => ?oneStepInstr_rhs_15
             (FReinterpretI float_t int_t) => ?oneStepInstr_rhs_16
             Drop => ?oneStepInstr_rhs_17
             Select => ?oneStepInstr_rhs_18
             (ILoad int_t memarg) => ?oneStepInstr_rhs_19
             (FLoad float_t memarg) => ?oneStepInstr_rhs_20
             (IStore int_t memarg) => ?oneStepInstr_rhs_21
             (FStore float_t memarg) => ?oneStepInstr_rhs_22
             (ILoad8 int_t sx memarg) => ?oneStepInstr_rhs_23
             (ILoad16 int_t sx memarg) => ?oneStepInstr_rhs_24
             (I64Load32 sx memarg) => ?oneStepInstr_rhs_25
             (IStore8 int_t sx memarg) => ?oneStepInstr_rhs_26
             (IStore16 int_t sx memarg) => ?oneStepInstr_rhs_27
             (I64Store32 sx memarg) => ?oneStepInstr_rhs_28
             MemorySize => ?oneStepInstr_rhs_29
             MemoryGrow => ?oneStepInstr_rhs_30
             Nop => ?oneStepInstr_rhs_31
             Unreachable => ?oneStepInstr_rhs_32
             (Block x xs) => ?oneStepInstr_rhs_33
             (Loop x xs) => ?oneStepInstr_rhs_34
             (If x xs ys) => ?oneStepInstr_rhs_35
             Return => ?oneStepInstr_rhs_36

--    oneStepInstr config stack expr (Const val) = MkInterp config (val :: stack) expr StatusRunning
--    oneStepInstr config stack expr (IUnOp op w) = ?oneStepInstr_rhs_2
--    oneStepInstr config stack expr (FUnOp op w) = ?oneStepInstr_rhs_3
--    oneStepInstr config stack expr instr@(IBinOp op _) =
--        case stack of
--            [] => ?empty
--            x :: [] => ?one_thing
--            x :: y :: xs =>
--                case (oneStepIBinOp stack op) of
--                    Left err => MkInterp config stack ((Ins instr) :: expr) (StatusError $ err)
--                    Right s => MkInterp config s expr StatusRunning
--    oneStepInstr config stack expr (FBinOp op w) = ?oneStepInstr_rhs_5
--    oneStepInstr config stack expr (ITest op w) = ?oneStepInstr_rhs_6
--    oneStepInstr config stack expr (IRel op w) = ?oneStepInstr_rhs_7
--    oneStepInstr config stack expr (FRel op w) = ?oneStepInstr_rhs_8
--    oneStepInstr config stack expr (ConvInstr conv) = ?oneStepInstr_rhs_9
--    oneStepInstr config stack expr (MemInstr mem) = ?oneStepInstr_rhs_10
--    oneStepInstr config stack expr (ContInstr cont) = oneStepContInstr config stack expr cont

    oneStepConst : Config -> Stack -> ExecExpr -> Val -> Interp
    oneStepConst config stack expr val = ?oneStepConst_rhs_1

    oneStepIUnOp : Stack -> IUnaryOp -> Either InterpError Stack
    oneStepIUnOp [] _           = Left (Err_StackUnderflow "Unop on empty stack")
    oneStepIUnOp (val :: xs) op =
        case op of
             Clz => (case val of
                          (I32Val bits) => let top : Bits32 = clz32 bits in
                                                    Right $ I32Val top :: xs
                          (I64Val bits) => let top : Bits32 = clz64 bits in
                                                    Right $ I32Val top :: xs
                          _ => Left (Err_StackTypeError "IUnOp CLZ applied to float"))
             Ctz => (case val of
                          (I32Val bits) => let top : Bits32 = ctz32 bits in
                                                    Right $ I32Val top :: xs
                          (I64Val bits) => let top : Bits32 = ctz64 bits in
                                                    Right $ I32Val top :: xs
                          _ => Left (Err_StackTypeError "IUnOp CTZ applied to float"))

             Popcnt => ?rhs_3

    oneStepFUnOp : Stack -> FUnaryOp -> Either InterpError Stack

    oneStepIBinOp : Stack -> IBinaryOp -> Either InterpError Stack
    oneStepIBinOp (val1 :: val2 :: tl) op
           =  case (val1, val2) of
                (I32Val bits, I32Val bits') => 
                                (case applyI32BinOp bits bits' op of
                                         Right top => Right ((I32Val top) :: tl)
                                         Left err => Left err)
                (I64Val bits, I64Val bits') => 
                                (case applyI64BinOp bits bits' op of
                                         Right top => Right ((I64Val top) :: tl)
                                         Left err => Left err)
                _ => Left $ Err_StackTypeError "IBinOp applied to invalid different types"
    oneStepIBinOp _ _ = Left $ Err_InvalidInstruction "Bad 1"


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

--    oneStepContInstr : Config -> Stack -> ExecExpr -> ControlInstr -> Interp
--    oneStepContInstr config stack expr Nop = ?oneStepContInstr_rhs_1
--    oneStepContInstr config stack expr Unreachable = ?oneStepContInstr_rhs_2
--    oneStepContInstr config stack expr (Block tp es) = MkInterp config stack (AdIns (Lab (MkLabel (rt_size tp) []) [] (map toExecInstr es)) :: expr) StatusRunning
--    oneStepContInstr config stack expr (Loop x xs) = ?oneStepContInstr_rhs_4
--    oneStepContInstr config stack expr Return = ?oneStepContInstr_rhs_6
--    oneStepContInstr config stack expr (If x thens elses)
--       = case stack of
--          (I32Val val) :: stack' =>
--               let block = (map toExecInstr (if val /= 0 then thens else elses))
--               in MkInterp config stack' (block ++ expr) StatusRunning
--          _ => MkInterp config stack expr (StatusError $ Err_StackUnderflow "No if cond")

