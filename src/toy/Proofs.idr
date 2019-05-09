module Proofs
import Toy

||| A helper function for a special case of the LEM
total
decBool : (b:Bool) -> Either (b = False) (b = True)
decBool False = Left Refl
decBool True = Right Refl

||| Given a value m of type Maybe a, return either a proof that m is nothing or
||| that there exists an x of type a such that m = Just x. Similar to decBool
||| above.
total
proof_maybe : {a : Type} -> (m : Maybe a) -> Either (m = Nothing) (x ** m = Just x)
proof_maybe Nothing = Left Refl
proof_maybe (Just x)  = Right (x ** Refl)

--------------------------------------------------------------------------------
-----                          PRESERVATION PROOF                          -----
--------------------------------------------------------------------------------

||| OneStep is a proof that `c R c'`, where R is the one-step reduction relation
data OneStep : Code -> Code -> Type where
    Step : (c : Code) -> (c' : Code) -> (step c = Just c') -> OneStep c c'

||| This proves that a piece of code has a given type.
data HasType : Code -> CodeTp -> Type where
    HasTp : (c : Code) -> (t : CodeTp) -> (typeCode c = Just t) ->  HasType c t

||| Preservation: Given that code has type t, and that code c' is the result of
||| executing a small-step reduction on c, we would like to prove that c' has
||| type t.
|||
||| This isn't complete---if statements need some more work, but they are close.
total
pres : OneStep c d -> HasType c t -> HasType d t
pres {c=Cd [] vs} {d=Cd es0 vs0} {t = t} (Step (Cd [] vs) (Cd es0 vs0) prf) (HasTp (Cd [] vs) t jstacktype_eq_jt) = 
  let cd_nil_vs_eq_cd_es0_vs0 : (Cd [] vs = Cd es0 vs0) = justInjective prf
      nil_eq_es0 : ([] = es0) = cd_injective_on_arg0 cd_nil_vs_eq_cd_es0_vs0
      vs_eq_vs0 : (vs = vs0) = cd_injective_on_arg1 cd_nil_vs_eq_cd_es0_vs0
      in rewrite (sym vs_eq_vs0) in
         rewrite (sym nil_eq_es0) in HasTp (Cd [] vs) t jstacktype_eq_jt

pres {c=Cd (I32Add :: es) ((I32 v1) :: (I32 v2)  :: vs)} {d=Cd es0 vs0} {t = t}
     (Step (Cd (I32Add :: es) ((I32 v1) :: (I32 v2) :: vs)) (Cd es0 vs0) prf)
     (HasTp (Cd (I32Add :: es) ((I32 v1) :: (I32 v2) :: vs)) t typexpr_eq_jt) =
        let lemma1 : ((Cd es (I32 (prim__addBigInt v1 v2) :: vs)) = (Cd es0 vs0)) = justInjective prf
            lemma2 : (es = es0) = cd_injective_on_arg0 lemma1
            lemma3 : ((I32 (prim__addBigInt v1 v2) :: vs) = vs0) = cd_injective_on_arg1 lemma1
            lemma4 : (T32 :: typeOfStack vs = typeOfStack vs0) = cong {f=typeOfStack} lemma3
            lemma5 : (typeExpr es (typeOfStack vs0) = Just t) = rewrite (sym lemma4) in typexpr_eq_jt
            lemma6 : (typeExpr es0 (typeOfStack vs0) = Just t) = rewrite (sym lemma2) in lemma5
        in HasTp (Cd es0 vs0) t lemma6

pres {c=Cd (I32Add :: es) []} {d=Cd es0 vs0} {t = t} (Step (Cd (I32Add :: es) []) (Cd es0 vs0) prf) (HasTp (Cd (I32Add :: es) []) t typexpr_eq_jt) =
  case prf of Refl impossible

pres {c=Cd (I32Add :: es) ((I32 v) :: [])} {d=Cd es0 vs0} {t = t} (Step (Cd (I32Add :: es) ((I32 v) :: [])) (Cd es0 vs0) prf) (HasTp (Cd (I32Add :: es) ((I32 v) :: [])) t typexpr_eq_jt) =
  case prf of Refl impossible

pres {c=Cd ((If thn els) :: es) []} {d=Cd es0 vs0} {t = t} (Step (Cd ((If thn els) :: es) []) (Cd es0 vs0) prf) (HasTp (Cd ((If thn els) :: es) []) t x) =
  case prf of Refl impossible

pres {c=Cd ((If thn els) :: es) ((I32 v) :: vs)} {d=Cd es0 vs0} {t = t}
      (Step (Cd ((If thn els) :: es) ((I32 v) :: vs)) (Cd es0 vs0) prf)
      (HasTp (Cd ((If thn els) :: es) ((I32 v) :: vs)) t p_tp) =
          let cond = (not (intToBool (prim__eqBigInt v 0))) in
              case decBool (not (intToBool (prim__eqBigInt v 0))) of
              (Left l) =>
                  let
                      lemma0 : ((ifThenElse (not (intToBool (prim__eqBigInt v 0))) (Delay (Just (Cd (thn ++ es) vs)))
                                                  (Delay (Just (Cd (els ++ es) vs)))) = (Just (Cd (els ++ es) vs))) = rewrite l in Refl
                      lemma1 : ((Just (Cd (els ++ es) vs)) = (Just (Cd es0 vs0))) = rewrite (sym lemma0) in prf
                      lemma2 : (Cd (els ++ es) vs = Cd es0 vs0) = justInjective lemma1
                      lemma3 : (vs = vs0) = cd_injective_on_arg1 lemma2
                      lemma4 : ((els ++ es) = es0) = cd_injective_on_arg0 lemma2
                      lemma_f : (typeExpr es0 (typeOfStack vs0) = Just t) = ?l_lemma_f_rhs
                  in HasTp (Cd es0 vs0) t lemma_f
              (Right r) =>
                  let
                      lemma0 : ((ifThenElse (not (intToBool (prim__eqBigInt v 0))) (Delay (Just (Cd (thn ++ es) vs)))
                                                  (Delay (Just (Cd (els ++ es) vs)))) = (Just (Cd (thn ++ es) vs))) = rewrite r in Refl
                      lemma1 : ((Just (Cd (thn ++ es) vs)) = (Just (Cd es0 vs0))) = rewrite (sym lemma0) in prf
                      lemma2 : (Cd (thn ++ es) vs = Cd es0 vs0) = justInjective lemma1
                      lemma3 : (vs = vs0) = cd_injective_on_arg1 lemma2
                      lemma4 : ((thn ++ es) = es0) = cd_injective_on_arg0 lemma2
                      lemma_f : (typeExpr es0 (typeOfStack vs0) = Just t) = ?r_lemma_f_rhs
                  in HasTp (Cd es0 vs0) t lemma_f

pres {c=Cd ((Const (I32 y)) :: es) vs} {d=Cd es0 vs0} {t = t} (Step (Cd ((Const (I32 y)) :: es) vs) (Cd es0 vs0) prf) (HasTp (Cd ((Const (I32 y)) :: es) vs) t x) 
 = let prf_inj   : (Cd es (I32 y :: vs) = Cd es0 vs0)         = justInjective prf 
       es_eq_es0 : (es = es0)                               = cd_injective_on_arg0 prf_inj
       vs_eq_vs0 : ((I32 y) :: vs = vs0)                     = cd_injective_on_arg1 prf_inj
       on_stack  : (T32 :: (typeOfStack vs) = typeOfStack vs0) = cong {f=typeOfStack} vs_eq_vs0 
         in HasTp (Cd es0 vs0) t (rewrite (sym es_eq_es0) in rewrite (sym on_stack) in x)

--------------------------------------------------------------------------------
-----                            PROGRESS PROOF                            -----
--------------------------------------------------------------------------------

||| We say that something is in normal form when there are no more expressions
||| to execute.
data NormalForm : Code -> Type where
  Norm : {vs : Stack} -> NormalForm (Cd [] vs)

||| In our language, there are two types of progress. Either there is a one-step
||| reduction that can be performed, or the code is in normal form.
data Progress : Code -> Type where
  ProgNormal : NormalForm c -> Progress c
  ProgStep   : (OneStep c c') -> Progress c

maybe_to_eq : (mx : Maybe _) -> Either (x ** mx = Just x) (mx = Nothing)
maybe_to_eq Nothing = Right Refl
maybe_to_eq (Just x) = Left (x ** Refl)

||| As long as a program has a type, it is either in normal form or it can be
||| reduced by a small-step reduction (i.e., it can progress).
total
progress : HasType c t -> Progress c
progress (HasTp c t prf) with (c)
  progress (HasTp c t prf) | (Cd xs ys) with (t)
    progress (HasTp c t prf) | (Cd []  ys) | zs = ProgNormal Norm
    progress (HasTp c t prf) | (Cd (x :: xs) ys) | (z :: zs) =
      case maybe_to_eq (step (Cd (x :: xs) ys)) of
        Left (c' ** mc) => ProgStep (Step (Cd (x :: xs) ys) c' mc)
        Right Refl impossible
    progress (HasTp _ _ Refl) | (Cd es (_ :: _) ) | [] impossible
    progress (HasTp _ _ Refl) | (Cd (_ :: _) vs ) | [] impossible

