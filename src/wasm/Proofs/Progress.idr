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
    progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) with (maybe_to_eq $ step $ MkInterp cf (e :: es) vs)
      progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) | Left (i' ** mi) = ProgStep $ Step (MkInterp cf (e :: es) vs) i' mi 

      progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) | Right r with (e)
        progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) | Right r | (Ins (Const x)) = case r of Refl impossible
        progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) | Right r | (Ins (IBinOp op w)) = case r of Refl impossible
        progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) | Right r | (Ins Nop) = case r of Refl impossible
        progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) | Right r | (Ins (Block xs ys)) = case r of Refl impossible
        progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) | Right r | (Ins (If xs ys ws)) = case r of Refl impossible
        progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) | Right r | (AdIns Trap) = case r of Refl impossible
        progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) | Right r | (AdIns (Label k xs ys ws)) = case r of Refl impossible
        progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | (z :: zs) | Right r | (AdIns (Breaking k xs)) = ?progress_rhs_9
    
    progress (HasTp i t prf) | (MkInterp cf (e :: es) vs ) | [] = ?unpossible1
    progress (HasTp i t prf) | (MkInterp cf es (v :: vs)) | [] = ?unpossible2
