import Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.PatternValidator
import Structure.Types
import Structure.Instr

total
preservation : OneStep i j -> HasType i t -> HasType j t
preservation {t=t} (Step i j prf) (HasTp i t x) with (i)
  preservation {t=t} (Step i j prf) (HasTp i t x) | i_pat with (j)

-- Non-implemented cases are on one line to support case splitting.
-- Implemented ones should be broken up for readability as so
    preservation {t=t} (Step i j prf) (HasTp i t x) 
    | (MkInterp cf vs [] st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_2

    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf vs ((AdIns Trap) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_13
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf vs ((AdIns (Invoke k)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_18
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf vs ((AdIns (Label k ys zs ws)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_19
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf vs ((AdIns (Breaking k ys)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_20

    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf vs ((Ins (Const y)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_3
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf vs ((Ins Nop) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_6
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf vs ((Ins (Block ys zs)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_7
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf vs ((Ins (If ys zs ws)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_8
    
    --- binops where execution is the same, hopefully we don't need to split on op 
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf ((I64Val y) :: ((I64Val z) :: ys)) ((Ins (IBinOp op W64)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_17
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf ((I32Val y) :: ((I32Val z) :: ys)) ((Ins (IBinOp op W32)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_11
    
    --- Binops where stack is too small
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf [] ((Ins (IBinOp op w)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_1
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf (y :: []) ((Ins (IBinOp op w)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_5

    --- Begin binops that don't match: perhaps we can get away with one line with _ _ _ for this
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf ((I32Val y) :: ((I32Val z) :: ys)) ((Ins (IBinOp op W64)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_14
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf ((I32Val y) :: ((I64Val z) :: ys)) ((Ins (IBinOp op W32)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_10
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf ((I32Val y) :: ((I64Val z) :: ys)) ((Ins (IBinOp op W64)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_15
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf ((I64Val y) :: ((I32Val z) :: ys)) ((Ins (IBinOp op W32)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_12
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf ((I64Val y) :: ((I32Val z) :: ys)) ((Ins (IBinOp op W64)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_16
    preservation {t=t} (Step i j prf) (HasTp i t x) | (MkInterp cf ((I64Val y) :: ((I64Val z) :: ys)) ((Ins (IBinOp op W32)) :: xs) st) | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_9
    --- End binops that don't match
