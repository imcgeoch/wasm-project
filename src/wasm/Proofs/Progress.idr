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
    progress (HasTp i t prf) 
             | (MkInterp cf [] vs)        
             | zs 
               = ProgNormal Norm 
    progress (HasTp i t prf) 
              | (MkInterp cf (e :: es) vs) 
              | (z :: zs) 
                = case maybe_to_eq $ step $ MkInterp cf (e :: es) vs of
                  Left (i' ** mi) => 
                       ProgStep $ Step (MkInterp cf (e :: es) vs) i' mi 
                  Right Refl impossible 
    progress (HasTp i t prf) | (MkInterp cf (e :: es) vs ) | [] = ?unpossible1
    progress (HasTp i t prf) | (MkInterp cf es (v :: vs)) | [] = ?unpossible2
