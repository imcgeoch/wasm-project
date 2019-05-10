module Execution.JankInterp


import Execution.Runtime
import Structure.Instr
import Structure.Types
import Util.BitUtil
import Util.ListUtil
import Data.Vect
import Data.Bits
import Structure.Indices

%access public export

%default total

record Interp where
    constructor MkInterp
    config : Config
    expr   : ExecExpr
    stack  : Stack

i32binop : IBinaryOp -> Bits32 -> Bits32 -> Val
i32binop IAdd v1 v2 = I32Val (prim__addB32 v1 v2)
i32binop ISub v1 v2 = I32Val (prim__subB32 v1 v2)
i32binop IMul v1 v2 = I32Val (prim__mulB32 v1 v2)

i64binop : IBinaryOp -> Bits64 -> Bits64 -> Val
i64binop IAdd v1 v2 = I64Val (prim__addB64 v1 v2)
i64binop ISub v1 v2 = I64Val (prim__subB64 v1 v2)
i64binop IMul v1 v2 = I64Val (prim__mulB64 v1 v2)

||| Make a single small-step reduction
step : (interp : Interp) -> Maybe Interp
step (MkInterp config [] vs) = Just (MkInterp config [] vs)
step (MkInterp config ((Ins (Const val)) :: es) vs) = Just $ MkInterp config es (val :: vs)
step (MkInterp config ((Ins (IBinOp op W32)) :: es) (I32Val v1 :: I32Val v2 :: vs) ) =
      Just $ MkInterp config es ((i32binop op v1 v2) :: vs)
step (MkInterp config ((Ins (IBinOp op W64)) :: es) (I64Val v1 :: I64Val v2 :: vs) ) =
      Just $ MkInterp config es ((i64binop op v1 v2) :: vs)

step (MkInterp config ((Ins Nop) :: es) vs) = Just $ MkInterp config es vs
step (MkInterp config ((Ins (Block tp es')) :: es) vs) = Just $ MkInterp config expr vs
     where
       label : AdminInstr
       label = Label (rt_size tp) [] (map toExecInstr es') []

       expr : ExecExpr
       expr = AdIns label :: es

step (MkInterp config ((Ins (If tp thn els)) :: es) (I32Val v :: vs)) =
      Just $ MkInterp config (block :: es) vs
      where
        block = Ins (Block tp (if v /= 0 then thn else els))

step (MkInterp config (AdIns Trap :: es) vs) = Just $ MkInterp config (AdIns Trap :: es) vs
step (MkInterp config (AdIns (Label k cont [] vs') :: es) vs) =
      Just $ MkInterp config es ((take k vs') ++ vs)

step (MkInterp config (AdIns (Label k cont (AdIns Trap :: es') vs') :: es) vs) =
      Just $ MkInterp config (AdIns Trap :: es') vs

step (MkInterp config (AdIns (Label k cont (AdIns (Breaking Z rvs) :: es') vs') :: es) vs) =
      if length rvs < k
          then Nothing
          else Just $ MkInterp config ((map toExecInstr cont) ++ es) ((take k rvs) ++ vs)

step (MkInterp config (AdIns (Label k cont (AdIns (Breaking (S d) rvs) :: es') vs') :: es) vs) =
    Just $ MkInterp config (AdIns (Breaking d rvs) :: es) vs

step (MkInterp config (AdIns (Label k cont (e :: es') vs') :: es) vs) with (assert_total $ step (MkInterp config (e :: es') vs'))
  step (MkInterp config (AdIns (Label k cont (e :: es') vs') :: es) vs) | Nothing = Nothing
  step (MkInterp config (AdIns (Label k cont (e :: es') vs') :: es) vs) | (Just (MkInterp cnf' expr stack)) =
      Just $ MkInterp cnf' (AdIns (Label k cont expr stack) :: es) vs

step _ = Nothing


mutual
    partial
    Show AdminInstr where
        show Trap = "trap"
        show (Label k cont es vs) = "{label\n    arity: " ++ (show k) ++ ",\n    cont: " ++ (show cont) ++ ",\n    vs: " ++ (show vs) ++ "\n    es:" ++ (show es) ++ ")"
        show (Breaking k xs) = "(breaking " ++ (show k) ++ ", " ++ (show xs) ++ ")"

    partial
    Show ExecInstr where
        show (Ins instr) = (show instr)
        show (AdIns instr) = (show instr)
