import Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.PatternValidator
import Structure.Types
import Structure.Instr

%default total

--total _injective_on_arg0 : (Cd x1 _) = (Cd x2 _) -> x1 = x2
--cd_injective_on_arg0 Refl = Refl

interp_injective_es : (MkInterp _ es1 _) = (MkInterp _ es2 _) -> es1 = es2  
interp_injective_es Refl = Refl

interp_injective_vs : (MkInterp _ _ vs1) = (MkInterp _ _ vs2) -> vs1 = vs2  
interp_injective_vs Refl = Refl

typeOfVal : Val -> ValType
typeOfVal (I32Val x) = IValTp (ITp W32)
typeOfVal (I64Val x) = IValTp (ITp W64)

typeOfStack : Stack -> TypeStack
typeOfStack [] = []
typeOfStack (x :: xs) = typeOfVal x :: (typeOfStack xs)

total
preservation : OneStep i j -> HasType i t -> HasType j t
preservation (Step i j prf) (HasTp i t x) with (i)
  preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) with (j)
    preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) with (es)
      {-
        MATCHING ON EXPRESSIONS
      -}
      preservation (Step i j prf) (HasTp i t x) 
                   | (MkInterp c es vs) 
                   | (MkInterp cj esj vsj) 
                   | [] = 
                     let j = (MkInterp cj esj vsj)
                         just_prf = justInjective prf
                         esj_eq_es = sym $ interp_injective_es just_prf
                         vsj_eq_vs = sym $ interp_injective_vs just_prf
                         in HasTp j t ?preservation_rhs_1
      preservation (Step i j prf) (HasTp i t x)
                   | (MkInterp c es vs)
                   | (MkInterp cj esj vsj)
                   | (Ins (Const (I32Val y)) :: xs) =
                     let j = MkInterp cj esj vsj
                         x = 1
                     in HasTp j t ?a_proof

      preservation (Step i j prf) (HasTp i t x) 
                   | (MkInterp c es vs) 
                   | (MkInterp cj esj vsj) 
                   | ((Ins (Const (I64Val y))) :: xs) = 
                     let j = MkInterp cj esj vsj
                         just_prf  = justInjective prf
                         esj_eq_es = sym $ interp_injective_es just_prf
                         vsj_eq_vs = sym $ interp_injective_vs just_prf
                         tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
                         in HasTp j t ?c64_prf  

      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W32)) :: xs) = ?preservation_rhs_4
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W64)) :: xs) = ?preservation_rhs_9

      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins Nop) :: xs) = ?preservation_rhs_6
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins (Block ys zs)) :: xs) = ?preservation_rhs_7
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins (If ys zs ws)) :: xs) = ?preservation_rhs_8
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((AdIns Trap) :: xs) = ?preservation_rhs_3
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((AdIns (Label k ys zs ws)) :: xs) = ?preservation_rhs_10
      preservation (Step i j prf) (HasTp i t x) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((AdIns (Breaking k ys)) :: xs) = ?preservation_rhs_11

    
