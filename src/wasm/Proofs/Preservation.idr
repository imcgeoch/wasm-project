import Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.PatternValidator
import Structure.Types
import Structure.Instr

total
preservation : OneStep i j -> HasType i t -> HasType j t
preservation (Step i j prf) (HasTp i t x) with (i)
  preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) with (j)
    preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) with (es)
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | [] = ?preservation_rhs_1
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins (Const y)) :: xs) = ?preservation_rhs_2
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins (IBinOp op w)) :: xs) = ?preservation_rhs_5
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins Nop) :: xs) = ?preservation_rhs_6
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins (Block ys zs)) :: xs) = ?preservation_rhs_7
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins (If ys zs ws)) :: xs) = ?preservation_rhs_8
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((AdIns Trap) :: xs) = ?preservation_rhs_3
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((AdIns (Invoke k)) :: xs) = ?preservation_rhs_9
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((AdIns (Label k ys zs ws)) :: xs) = ?preservation_rhs_10
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((AdIns (Breaking k ys)) :: xs) = ?preservation_rhs_11

    
