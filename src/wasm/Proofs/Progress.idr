import Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.PatternValidator
import Structure.Types
import Structure.Instr


maybe_to_eq : (mx : Maybe _) -> Either (x ** mx = Just x) (mx = Nothing)
maybe_to_eq Nothing = Right Refl
maybe_to_eq (Just x) = Left (x ** Refl)

total
progress : HasType i t -> Progress i
progress (HasTp i t prf) with (i)
  progress (HasTp i t prf) | i_pat with (t)
    progress (HasTp i t prf) | (MkInterp cf vs [] st)       | t_pat = ProgNormal Norm 
    progress (HasTp i t prf) | (MkInterp cf vs (x :: xs) st)       | t_pat = ?rhs_2 
