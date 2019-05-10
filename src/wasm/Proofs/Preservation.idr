import Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.AdminValidator
import Structure.Types
import Structure.Instr

%default total

interp_injective_es : (MkInterp _ es1 _) = (MkInterp _ es2 _) -> es1 = es2
interp_injective_es Refl = Refl

interp_injective_vs : (MkInterp _ _ vs1) = (MkInterp _ _ vs2) -> vs1 = vs2
interp_injective_vs Refl = Refl


total
preservation : OneStep i j -> HasType i t -> HasType j t
preservation (Step i j prf) (HasTp i t tp_prf) with (i)
  preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es vs) with (j)
    preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es vs) | (MkInterp cj esj vsj) with (es)
      {-
        MATCHING ON EXPRESSIONS
      -}
      preservation (Step i j prf) (HasTp i t tp_prf) 
                   | (MkInterp c es vs) 
                   | (MkInterp cj esj vsj) 
                   | [] = 
                     let j = (MkInterp cj esj vsj)
                         just_prf = justInjective prf
                         esj_eq_es = sym $ interp_injective_es just_prf
                         vsj_eq_vs = sym $ interp_injective_vs just_prf
                         tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
                         in HasTp j t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)

      preservation (Step i j prf) (HasTp i t tp_prf)
                   | (MkInterp c es vs)
                   | (MkInterp cj esj vsj)
                   | (Ins (Const (I32Val y)) :: xs) =
                     let j' = MkInterp cj esj vsj
                         just_prf  = justInjective prf
                         esj_eq_es = sym  $ interp_injective_es just_prf
                         vsj_eq_vs = sym  $ interp_injective_vs just_prf
                         tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
                     in HasTp j' t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)

      preservation (Step i j prf) (HasTp i t tp_prf) 
                   | (MkInterp c es vs) 
                   | (MkInterp cj esj vsj) 
                   | ((Ins (Const (I64Val y))) :: xs) = 
                     let j' = MkInterp cj esj vsj
                         just_prf  = justInjective prf
                         esj_eq_es = sym $ interp_injective_es just_prf
                         vsj_eq_vs = sym $ interp_injective_vs just_prf
                         tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
                         in HasTp j' t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)  

      ---------------------------------------------------------------------------
      ----                        BINARY OPERATORS                           ----
      ---------------------------------------------------------------------------

      -- IMPOSSIBILITY CLAIMS (TYPE ERRORS)
      -- ==================================

      -- STACK UNDERFLOWS
      -------------------
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es []) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W32)) :: es') = case tp_prf of Refl impossible
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es (v :: [])) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W32)) :: xs) = 
        case v of
             (I32Val x) => case tp_prf of Refl impossible
             (I64Val x) => case tp_prf of Refl impossible

      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es []) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W64)) :: es') = case tp_prf of Refl impossible
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es (v :: [])) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W64)) :: xs) = 
        case v of
             (I32Val x) => case tp_prf of Refl impossible
             (I64Val x) => case tp_prf of Refl impossible

      -- OPERAND WIDTH MISMATCH ERRORS
      --------------------------------
      -- W32
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es ((I32Val v1) :: ((I64Val v2) :: vs))) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W32)) :: xs) = case tp_prf of Refl impossible
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es ((I64Val v1) :: ((I32Val v2) :: vs))) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W32)) :: xs) = case tp_prf of Refl impossible
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es ((I64Val v1) :: ((I64Val v2) :: vs))) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W32)) :: xs) = case tp_prf of Refl impossible
      -- W32
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es ((I32Val v1) :: ((I64Val v2) :: vs))) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W64)) :: xs) = case tp_prf of Refl impossible
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es ((I64Val v1) :: ((I32Val v2) :: vs))) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W64)) :: xs) = case tp_prf of Refl impossible
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es ((I32Val v1) :: ((I32Val v2) :: vs))) | (MkInterp cj esj vsj) | ((Ins (IBinOp op W64)) :: xs) = case tp_prf of Refl impossible

      -- VALID CASES
      -- ===========
      preservation (Step i j prf) (HasTp i t tp_prf)
          | (MkInterp c es ((I32Val v1) :: ((I32Val v2) :: vs)))
          | (MkInterp cj esj vsj)
          | ((Ins (IBinOp op W32)) :: es') =
            case op of
                 IAdd => let j' = MkInterp cj esj vsj
                             just_prf  = justInjective prf
                             esj_eq_es = sym $ interp_injective_es just_prf
                             vsj_eq_vs = sym $ interp_injective_vs just_prf
                             tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
                         in HasTp j' t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)

                 ISub => let j' = MkInterp cj esj vsj
                             just_prf  = justInjective prf
                             esj_eq_es = sym $ interp_injective_es just_prf
                             vsj_eq_vs = sym $ interp_injective_vs just_prf
                             tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
                         in HasTp j' t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)

                 IMul => let j' = MkInterp cj esj vsj
                             just_prf  = justInjective prf
                             esj_eq_es = sym $ interp_injective_es just_prf
                             vsj_eq_vs = sym $ interp_injective_vs just_prf
                             tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
                         in HasTp j' t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)

      preservation (Step i j prf) (HasTp i t tp_prf)
          | (MkInterp c es ((I64Val v1) :: ((I64Val v2) :: vs)))
          | (MkInterp cj esj vsj)
          | ((Ins (IBinOp op W64)) :: es') =
            case op of
                 IAdd => let j' = MkInterp cj esj vsj
                             just_prf  = justInjective prf
                             esj_eq_es = sym $ interp_injective_es just_prf
                             vsj_eq_vs = sym $ interp_injective_vs just_prf
                             tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
                         in HasTp j' t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)

                 ISub => let j' = MkInterp cj esj vsj
                             just_prf  = justInjective prf
                             esj_eq_es = sym $ interp_injective_es just_prf
                             vsj_eq_vs = sym $ interp_injective_vs just_prf
                             tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
                         in HasTp j' t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)

                 IMul => let j' = MkInterp cj esj vsj
                             just_prf  = justInjective prf
                             esj_eq_es = sym $ interp_injective_es just_prf
                             vsj_eq_vs = sym $ interp_injective_vs just_prf
                             tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
                         in HasTp j' t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)

      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins Nop) :: es') = ?nop
      -- -- TODO: Uncomment the following code when Nop gets implemented in the validator
--         let j' = MkInterp cj esj vsj
--             just_prf  = justInjective prf
--             esj_eq_es = sym  $ interp_injective_es just_prf
--             vsj_eq_vs = sym  $ interp_injective_vs just_prf
--             tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
--         in HasTp j' t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)

      preservation (Step i j prf) (HasTp i t tp_prf)
          | (MkInterp c es vs) 
          | (MkInterp cj esj vsj) 
          | ((Ins (Block ys zs)) :: xs) = ?block
      -- -- TODO: Uncomment the following code when case expr is factored out of validate
--             let j' = MkInterp cj esj vsj
--                 just_prf  = justInjective prf
--                 esj_eq_es = sym  $ interp_injective_es just_prf
--                 vsj_eq_vs = sym  $ interp_injective_vs just_prf
--                 tsj_eq_ts = cong {f=typeOfStack} vsj_eq_vs
--             in HasTp j' t (rewrite esj_eq_es in rewrite tsj_eq_ts in tp_prf)
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((Ins (If ys zs ws)) :: xs) = ?preservation_rhs_8

      preservation (Step i j prf) (HasTp i t tp_prf) 
                   | (MkInterp c es vs) 
                   | (MkInterp cj esj vsj) 
                   | ((AdIns Trap) :: xs) 
                     = case tp_prf of
                       Refl impossible
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((AdIns (Label k ys zs ws)) :: xs) = ?preservation_rhs_10
      preservation (Step i j prf) (HasTp i t tp_prf) | (MkInterp c es vs) | (MkInterp cj esj vsj) | ((AdIns (Breaking k ys)) :: xs) = ?preservation_rhs_11

    
