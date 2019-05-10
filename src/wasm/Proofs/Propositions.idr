module Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.PatternValidator
import Structure.Types
import Structure.Instr

%access public export

%default total

-- to be replaced with vaidate and step as the become available
valInterp : Interp -> Maybe (List ValType)

dumbStep : Interp -> Maybe Interp

data HasType : Interp -> List ValType -> Type where
  HasTp : (i : Interp) -> (lst : List ValType) -> (valInterp i = (Just lst)) -> HasType i lst

data OneStep : Interp -> Interp -> Type where
  Step : (i : Interp) -> (j : Interp) -> (dumbStep i = (Just j)) -> OneStep i j

data NormalForm : Interp -> Type where
  Norm : NormalForm (MkInterp _ [] _) 
 
data Trapped : Interp -> Type where
  Trpd : Trapped (MkInterp _ (AdIns Trap :: es) _)

data Progress : Interp -> Type where
  ProgNormal  : NormalForm i  -> Progress i
  ProgStep    : OneStep i j   -> Progress i
  ProgTrapped : Trapped i     -> Progress i 
