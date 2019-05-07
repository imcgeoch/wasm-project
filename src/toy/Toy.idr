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
step (Cd (I32Add :: es) []) = Nothing
step (Cd (Const v :: es) []) = Just $ Cd es [v]
step (Cd (If thn els ::es) []) = Nothing
step (Cd (I32Add :: es) (I32 v :: I32 v' :: vs)) = Just $ Cd es (I32 (v + v') :: vs)
step (Cd (Const (I32 v) ::es) (I32 v'::vs)) = Just $ Cd es (I32 v :: I32 v' :: vs)
step (Cd (If thn els ::es) (I32 v :: vs))  = Just $ Cd (if v /= 0 then thn ++ es else els ++ es) vs
step _ = Nothing

mutual
  total
  typeInstr : Instr -> CodeTp -> Maybe CodeTp
  typeInstr I32Add (T32 :: T32 :: ts) = Just (T32 :: ts)
  typeInstr (If thn els) (T32 :: ts) = 
          case (typeExpr thn ts, typeExpr els ts) of 
               (Just tt, Just te) => case decEq tt te of
                                          Yes prf => Just tt
                                          No contra => Nothing
               (_, _) => Nothing
  typeInstr (Const x) ts = Just (T32 :: ts)
  typeInstr _ _ = Nothing

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

pres {c=Cd (I32Add :: es) vs} {d=Cd es0 vs0} {t = t} (Step (Cd (I32Add :: es) vs) (Cd es0 vs0) prf) (HasTp (Cd (I32Add :: es) vs) t x) = ?pres_i32add

pres {c=Cd ((If xs ys) :: es) vs} {d=Cd es0 vs0} {t = t} (Step (Cd ((If xs ys) :: es) vs) (Cd es0 vs0) prf) (HasTp (Cd ((If xs ys) :: es) vs) t x) = ?pres_if_stmt
pres {c=Cd ((Const y) :: es) vs} {d=Cd es0 vs0} {t = t} (Step (Cd ((Const y) :: es) vs) (Cd es0 vs0) prf) (HasTp (Cd ((Const y) :: es) vs) t x) = ?pres_const
