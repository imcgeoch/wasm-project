module Toy

data Val = I32 Integer

Stack : Type
Stack = List Val

mutual
    data Instr = I32Add | If Expr Expr | Const Val

    Expr : Type
    Expr = List Instr

Code : Type
Code = (Expr, Stack)

data Tp = T32

CodeTp : Type
CodeTp = List Tp

type' : Val -> Tp
type' (I32 x) = T32

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
if_injective_on_arg0 : (If x1 _) = (If x2 _) -> x1 = x2
if_injective_on_arg0 Refl = Refl

if_injective_on_arg1 : (If _ x1) = (If _ x2) -> x1 = x2
if_injective_on_arg1 Refl = Refl

const_injective_on_arg0 : (Const x1) = (Const x2) -> x1 = x2
const_injective_on_arg0 Refl = Refl

not_I32Add_If : (I32Add ) = (If y z) -> Void
not_I32Add_If Refl impossible

not_I32Add_Const : (I32Add ) = (Const z) -> Void
not_I32Add_Const Refl impossible

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

step : Code -> Maybe Code
step code@([], vs) = Just code
step (I32Add :: es, []) = Nothing
step (Const v ::es, []) = Just (es, [v])
step (If thn els ::es, []) = Nothing
step (I32Add :: es, I32 v :: I32 v' :: vs) = Just (es, I32 (v + v') :: vs)
step (Const (I32 v) ::es, I32 v'::vs) = Just (es, I32 v :: I32 v' :: vs)
step (If thn els ::es, I32 v :: vs)  = Just (if v /= 0 then thn ++ es else els ++ es, vs)

mutual
  typeInstr : Instr -> CodeTp -> Maybe CodeTp
  typeInstr I32Add (T32 :: T32 :: ts) = Just (T32 :: ts)
  typeInstr (If thn els) (T32 :: ts) = 
          case (typeExpr thn ts, typeExpr els ts) of 
               (Just tt, Just te) => case decEq tt te of
                                          Yes prf => Just tt
                                          No contra => Nothing

  typeInstr (Const x) ts = Just (T32 :: ts)

  typeExpr : Expr -> CodeTp -> Maybe CodeTp
  typeExpr [] ts = Just ts
  typeExpr (e :: es) ts = (typeInstr e ts) >>= (typeExpr es)

  typeCode : Code -> Maybe CodeTp
  typeCode (es, vs) = typeExpr es (typeOfStack vs)

data OneStep : Code -> Code -> Type where
    Step : (c : Code) -> (c' : Code) -> (step c = Just c') -> OneStep c c'

data HasType : Code -> CodeTp -> Type where
    HasTp : (c : Code) -> (t : CodeTp) -> (typeCode c = Just t) ->  HasType c t

preservation : OneStep c c' -> HasType c t -> HasType c' t
preservation {c=([],vs)} {c'=([],vs')} {t} (Step ([], vs) ([], vs') prf) (HasTp ([], vs) t prf_t) with (step ([], vs))
  preservation {c=([],_)} {c'=([],_')} {t = _} (Step ([], _) ([], _') Refl) (HasTp ([], _) _ _) | Nothing impossible
  preservation {c=([],vs)} {c'=([],vs')} {t = t} (Step ([], vs) ([], vs') Refl) (HasTp ([], vs) t prf_t) | (Just ([], vs')) with (typeCode ([], vs))
    preservation {c=([],_)} {c'=([],_')} {t = _} (Step ([], _) ([], _') Refl) (HasTp ([], _) _ Refl) | (Just ([], _')) | Nothing impossible
    preservation {c=([],vs)} {c'=([],vs')} {t = t} (Step ([], vs) ([], vs') Refl) (HasTp ([], vs) t Refl) | (Just ([], vs')) | (Just t) with (typeCode ([], vs'))
      preservation {c=([],vs)} {c'=([],vs')} {t = t} (Step ([], vs) ([], vs') Refl) (HasTp ([], vs) t Refl) | (Just ([], vs')) | (Just t) | Nothing with (t)
        preservation {c=([],vs)} {c'=([],vs')} {t = t} (Step ([], vs) ([], vs') Refl) (HasTp ([], vs) t Refl) | (Just ([], vs')) | (Just t) | Nothing | [] = ?preservation_rhs_9
        preservation {c=([],vs)} {c'=([],vs')} {t = t} (Step ([], vs) ([], vs') Refl) (HasTp ([], vs) t Refl) | (Just ([], vs')) | (Just t) | Nothing | (x :: xs) = ?preservation_rhs_8
      preservation {c=([],vs)} {c'=([],vs')} {t = t} (Step ([], vs) ([], vs') Refl) (HasTp ([], vs) t Refl) | (Just ([], vs')) | (Just t) | (Just x) = ?preservation_rhs_4

preservation {c=([],vs)} {c'=(e'::es',vs')} (Step ([], vs) (e'::es', vs') prf) (HasTp ([], vs) t prf_t) = ?preservation_rhs_1
preservation {c=(I32Add :: es,vs)} {c'=([],vs')} (Step (I32Add :: es, vs) ([], vs') prf) (HasTp (I32Add :: es, vs) t prf_t) = ?preservation_rhs_5
preservation {c=(Const v :: es,vs)} {c'=([],vs')} (Step (Const v :: es, vs) ([], vs') prf) (HasTp (Const v::es, vs) t prf_t) = ?preservation_rhs_6
preservation {c=(If thn els :: es,vs)} {c'=([],vs')} (Step (If thn els ::es, vs) ([], vs') prf) (HasTp (If thn els ::es, vs) t prf_t) = ?preservation_rhs_7
preservation {c=(e :: es,vs)} {c'=(e'::es',vs')} (Step (e::es, vs) (e'::es', vs') prf) (HasTp (e::es, vs) t prf_t) = ?preservation_rhs_1

