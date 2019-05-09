import Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.PatternValidator
import Structure.Types
import Structure.Instr

total
preservation : OneStep i j -> HasType i t -> HasType j t
preservation (Step i j prf) (HasTp i t x) with (i)
  preservation (Step i j prf) (HasTp i t x) | i_pat with (j)
------------------
-- No Instructions
-----------------
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs [] st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_1
-----------------
--- Instructions
-----------------
-------Const
-----------------
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (Const y)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = ?preservation_rhs_3
-----------------
-------Binops
-----------------
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (IBinOp IAdd W32)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_5
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (IBinOp IAdd W64)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_11
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (IBinOp ISub W32)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_2
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (IBinOp ISub W64)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_12
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (IBinOp IMul W32)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_9
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (IBinOp IMul W64)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_13
----------------
-------Nop
----------------
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins Nop) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_6
----------------
-------Block
----------------
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (Block ys zs)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_7
----------------
-------If
----------------
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (If ys zs ws)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_8
----------------------
--- Admin Instructions
---------------------
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((AdIns Trap) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_10
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((AdIns (Invoke k)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_14
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((AdIns (Label k ys zs ws)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_15
    preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((AdIns (Breaking k ys)) :: xs) st) 
    | (MkInterp cf0 vs0 es0 st0) = 
      ?preservation_rhs_16
