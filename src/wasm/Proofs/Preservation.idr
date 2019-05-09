import Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.PatternValidator
import Structure.Types
import Structure.Instr

preservation : OneStep i j -> HasType i t -> HasType j t
preservation (Step i j prf) (HasTp i t x) with (i)
  -- No instructions
  preservation (Step i j prf) (HasTp i t x) | (MkInterp _ vs [] st) = 
    ?preservation_Nil_rhs
  -- Admin Instructions
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((AdIns Trap) :: xs) st) = 
      ?preservation_trap_rhs
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((AdIns (Invoke k)) :: xs) st) = 
      ?preservation_invoke_rhs
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((AdIns (Label k ys zs ws)) :: xs) st) = 
      ?preservation_label_rhs
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((AdIns (Breaking k ys)) :: xs) st) = 
      ?preservation_breaking_rhs
  -- Instructions
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (Const y)) :: xs) st) = ?pres_const_rhs
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins Nop) :: xs) st) = ?pres_nop_rhs
  -- Binops 
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (IBinOp IAdd w)) :: xs) st) = ?pres_add_rhs
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (IBinOp ISub w)) :: xs) st) = ?pres_sub_rhs 
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (IBinOp IMul w)) :: xs) st) = ?pres_mul_rhs
  -- Block
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (Block ys zs)) :: xs) st) = ?pres_block_rhs
  -- If
  preservation (Step i j prf) (HasTp i t x) 
    | (MkInterp _ vs ((Ins (If ys zs ws)) :: xs) st) = ?pres_if_rhs






--preservation (Step i j prf) (HasTp i t x) = ?preservation_rhs_2
