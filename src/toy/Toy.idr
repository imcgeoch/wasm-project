module Toy

data Val = I32 Integer

Stack : Type
Stack = List Val

mutual
    data Instr = I32Add | If Expr Expr | Const Val

    Expr : Type
    Expr = List Instr

data Code = Cd Expr Stack

%name Expr es
%name Stack vs

data Tp = T32

CodeTp : Type
CodeTp = List Tp

total
type' : Val -> Tp
type' (I32 x) = T32

total
decBool : (b:Bool) -> Either (b = False) (b = True)
decBool False = Left Refl
decBool True = Right Refl

total
typeOfStack : Stack -> CodeTp
typeOfStack [] = []
typeOfStack ((I32 x) :: xs) = T32 :: typeOfStack xs
--------------------------------------------------------------------------------
-----           BEGIN AUTOGENERATED DecEq IMPLEMENTATION FOR Tp            -----
--------------------------------------------------------------------------------
DecEq Tp where
    decEq (T32 ) (T32 ) = Yes Refl
--------------------------------------------------------------------------------
-----            END AUTOGENERATED DecEq IMPLEMENTATION FOR Tp             -----
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-----           BEGIN AUTOGENERATED DecEq IMPLEMENTATION FOR Val           -----
--------------------------------------------------------------------------------
total
i32_injective_on_arg0 : (I32 x1) = (I32 x2) -> x1 = x2
i32_injective_on_arg0 Refl = Refl

DecEq Val where
    decEq (I32 a) (I32 a') = (case decEq a a' of
        Yes Refl  => Yes Refl
        No contra => No $ \h => (contra . i32_injective_on_arg0) h)
--------------------------------------------------------------------------------
-----            END AUTOGENERATED DecEq IMPLEMENTATION FOR Val            -----
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-----          BEGIN AUTOGENERATED DecEq IMPLEMENTATION FOR Instr          -----
--------------------------------------------------------------------------------
total
if_injective_on_arg0 : (If x1 _) = (If x2 _) -> x1 = x2
if_injective_on_arg0 Refl = Refl

total
if_injective_on_arg1 : (If _ x1) = (If _ x2) -> x1 = x2
if_injective_on_arg1 Refl = Refl

total
const_injective_on_arg0 : (Const x1) = (Const x2) -> x1 = x2
const_injective_on_arg0 Refl = Refl

total
not_I32Add_If : (I32Add ) = (If y z) -> Void
not_I32Add_If Refl impossible

total
not_I32Add_Const : (I32Add ) = (Const z) -> Void
not_I32Add_Const Refl impossible

total
not_If_Const : (If a b) = (Const z) -> Void
not_If_Const Refl impossible

DecEq Instr where
    decEq (I32Add ) (I32Add ) = Yes Refl
    decEq (I32Add ) (If y z) = No not_I32Add_If
    decEq (I32Add ) (Const z) = No not_I32Add_Const
    decEq (If a b) (I32Add ) = No $ negEqSym not_I32Add_If
    decEq (If a b) (If a' b') = assert_total 
        (case decEq a a' of
            Yes Refl  => (case decEq b b' of
                Yes Refl  => Yes Refl
                No contra => No $ \h => (contra . if_injective_on_arg1) h)
            No contra => No $ \h => (contra . if_injective_on_arg0) h)
    decEq (If a b) (Const z) = No not_If_Const
    decEq (Const a) (I32Add ) = No $ negEqSym not_I32Add_Const
    decEq (Const a) (If y z) = No $ negEqSym not_If_Const
    decEq (Const a) (Const a') = (case decEq a a' of
        Yes Refl  => Yes Refl
        No contra => No $ \h => (contra . const_injective_on_arg0) h)
--------------------------------------------------------------------------------
-----           END AUTOGENERATED DecEq IMPLEMENTATION FOR Instr           -----
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-----          BEGIN AUTOGENERATED DecEq IMPLEMENTATION FOR Code           -----
--------------------------------------------------------------------------------
||| Auto generated theorem proving injectivity of value constructor Cd.
||| Generated to assist in proving cd_injective_on_arg0
total cd_injective_on_arg0 : (Cd x1 _) = (Cd x2 _) -> x1 = x2
cd_injective_on_arg0 Refl = Refl

||| Auto generated theorem proving injectivity of value constructor Cd.
||| Generated to assist in proving cd_injective_on_arg1
total cd_injective_on_arg1 : (Cd _ x1) = (Cd _ x2) -> x1 = x2
cd_injective_on_arg1 Refl = Refl


||| Automatic implementation of DecEq for Code type.
DecEq Code where
    decEq (Cd a b) (Cd a' b') = (case decEq a a' of
        Yes Refl  => (case decEq b b' of
            Yes Refl  => Yes Refl
            No contra => No $ \h => (contra . cd_injective_on_arg1) h)
        No contra => No $ \h => (contra . cd_injective_on_arg0) h)
--------------------------------------------------------------------------------
-----           END AUTOGENERATED DecEq IMPLEMENTATION FOR Code            -----
--------------------------------------------------------------------------------


total
step : Code -> Maybe Code
step (Cd [] vs) = Just (Cd [] vs)
step (Cd (Const v :: es) vs) = Just $ Cd es (v :: vs)
step (Cd (I32Add :: es) (I32 v :: I32 v' :: vs)) = Just $ Cd es (I32 (v + v') :: vs)
step (Cd (If thn els ::es) (I32 v :: vs))  = if v /= 0 then Just $ Cd (thn ++ es) vs
                                                       else Just $ Cd (els ++ es) vs
step _ = Nothing

mutual

  total
  typeExpr : Expr -> CodeTp -> Maybe CodeTp
  typeExpr [] ts = Just ts
  typeExpr (I32Add :: es) (T32 :: T32 :: ts) = let ts' = T32 :: ts in
                                                   typeExpr es ts'
  typeExpr ((If thn els) :: es) (T32 :: ts) =
    case typeExpr thn ts of
         Nothing => Nothing
         Just tt => case typeExpr els ts of
                         Nothing => Nothing
                         Just te => case decEq tt te of
                                              Yes prf => typeExpr es tt
                                              No contra => Nothing
  typeExpr ((Const (I32 x)) :: es) ts = typeExpr es (T32 :: ts)
  typeExpr _ _ = Nothing

  total
  typeCode : Code -> Maybe CodeTp
  typeCode (Cd es vs) = typeExpr es (typeOfStack vs)

data OneStep : Code -> Code -> Type where
    Step : (c : Code) -> (c' : Code) -> (step c = Just c') -> OneStep c c'

data HasType : Code -> CodeTp -> Type where
    HasTp : (c : Code) -> (t : CodeTp) -> (typeCode c = Just t) ->  HasType c t


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

data NormalForm : Code -> Type where
  Norm : {vs : Stack} -> NormalForm (Cd [] vs)

data Progress : Code -> Type where
  ProgTrapped : {c : Code} -> (step c = Nothing) -> Progress c
  ProgNormal : NormalForm c -> Progress c
  ProgStep   : (OneStep c c') -> Progress c

holy_shit_this_is_a_dumb_solution : (mc : Maybe Code) -> Either (c ** mc = Just c) (mc = Nothing)
holy_shit_this_is_a_dumb_solution Nothing = Right Refl
holy_shit_this_is_a_dumb_solution (Just x) = Left (x ** Refl)

total
progress : HasType c t -> Progress c 
progress (HasTp c t prf) with (c)
  progress (HasTp c t prf) | (Cd xs ys) with (t)
    progress (HasTp c t prf) | (Cd []  ys) | zs = ProgNormal Norm 
    progress (HasTp _ _ Refl) | (Cd [] (_ :: _) ) | [] impossible
    progress (HasTp _ _ Refl) | (Cd (_ :: _) []) | [] impossible
    progress (HasTp _ _ Refl) | (Cd (_ :: _) (_ :: _)) | [] impossible
    progress (HasTp c t prf) | (Cd (x :: xs) ys) | (z :: zs) = case holy_shit_this_is_a_dumb_solution (step (Cd (x :: xs) ys)) of
                                                             (Left (c' ** mc)) => ProgStep (Step (Cd (x :: xs) ys) c' mc) 
                                                             (Right Refl) impossible

{-
  --- cheaty trapped version for reference
  = case holy_shit_this_is_a_dumb_solution (step (Cd (x :: xs) vs)) of
            (Left (c0 ** l)) => let onstp = Step (Cd (x :: xs) vs) c0 l in ProgStep onstp 
            (Right rfl)      => ProgTrapped rfl -- Should be impossible
            -}
--------------------------------------------------------------------------------
---                             EXAMPLES OF NORM                             ---
--------------------------------------------------------------------------------
exValidNorm : NormalForm (Cd [] [])
exValidNorm = Norm

exInvalidNorm : NormalForm (Cd [Const (I32 7)] []) -> Void
exInvalidNorm Norm impossible 

