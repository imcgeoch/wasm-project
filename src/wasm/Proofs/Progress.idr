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
  progress (HasTp i t prf) | (MkInterp cf [] vs) = ProgNormal Norm 
  progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) with (maybe_to_eq $ step $ MkInterp cf (e :: es) vs)
    progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | Left (i' ** mi) = ProgStep $ Step (MkInterp cf (e :: es) vs) i' mi 
    progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) | Right r with (e)
      progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) |  Right r | (Ins (Const x)) = case r of Refl impossible
      progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) |  Right r | (Ins (IBinOp op w)) = case r of Refl impossible
      progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) |  Right r | (Ins Nop) = case r of Refl impossible
      progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) |  Right r | (Ins (Block xs ys)) = case r of Refl impossible
      progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) |  Right r | (Ins (If xs ys ws)) = case r of Refl impossible
      progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) |  Right r | (AdIns Trap) = ProgTrapped $ Trpd 
      progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) |  Right r | (AdIns (Label k xs ys ws)) = case r of Refl impossible
      progress (HasTp i t prf) | (MkInterp cf (e :: es) vs) |  Right r | (AdIns (Breaking k xs)) = case prf of Refl impossible
