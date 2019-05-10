import Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.AdminValidator
import Structure.Types
import Structure.Instr


maybe_to_eq : (mx : Maybe a) -> Either (x ** mx = Just x) (mx = Nothing)
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
    -- I think this is to facile. Shouldn't we have to rely on the fact it type checks?
    -- I think we might eb getting a "convenient" unification failure
    -- that is saying it's impossible for step to return nothing.
    progress (HasTp i t prf) 
              | (MkInterp cf (e :: es) vs) 
              | (z :: zs) 
                = case maybe_to_eq $ step $ MkInterp cf (e :: es) vs of
                  Left (i' ** mi) => 
                       ProgStep $ Step (MkInterp cf (e :: es) vs) i' mi 
                  Right r => ?why_does_idris_think_this_is_impossible 
    progress (HasTp i t prf) | (MkInterp cf (e :: es) vs ) | [] = ?unpossible1
    progress (HasTp i t prf) | (MkInterp cf es (v :: vs)) | [] = ?unpossible2
