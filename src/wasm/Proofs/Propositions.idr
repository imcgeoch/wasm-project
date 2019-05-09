module Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.PatternValidator
import Structure.Types

valInterp : Interp -> Maybe (List ValType)

data HasType : Interp -> List ValType -> Type where
  HasTp : (i : Interp) -> (lst : List ValType) -> (valInterp i = (Just lst)) -> HasType i lst

data OneStep : Interp -> Interp -> Type where
  Step : (i : Interp) -> (j : Interp) -> (oneStep i = j) -> OneStep i j

data NormalForm : Interp -> Type where
  Norm : NormalForm (MkInterp _ _ [] _) 
 
data Trapped : Interp -> Type where
  Trpd : Trapped (MkInterp _ _ _ StatusTrapped)

data Progress : Interp -> Type where
  ProgNormal  : NormalForm i  -> Progress i
  ProgStep    : OneStep i j   -> Progress i
  ProgTrapped : Trapped i     -> Progress i 
