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
step cd@(es, vs) = case es of
     [] => Just cd
     (I32Add :: es') => case vs of
           (I32 x) :: (I32 y) :: vs' => Just (es', I32 (x + y) :: vs')
           _ => Nothing

     ((If thn els) :: es') => case vs of
            (I32 x) :: vs' => Just ((if x /= 0 then thn else els) ++ es', vs')

     (Const x) :: es' => ?rhs

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

data OneStep : Code -> Code -> Type where
    Step : (c : Code) -> (c' : Code) -> (step c = Just c') -> OneStep c c'

data HasType : Code -> CodeTp -> Type where
    HasTp : (c : Code) -> (t : CodeTp) -> HasType c t

preservation : OneStep c1 c2 -> HasType c1 t -> HasType c2 t
preservation {c1=([], vs)} (Step ([], vs) c2 prf) (HasTp ([], vs) t) = ?preservation_rhs_2
preservation {c1=(e::es, vs)} (Step (e::es, vs) c2 prf) (HasTp (e::es, vs) t) = ?preservation_rhs_2

foo : List Nat -> Maybe (List Nat)
foo [] = Just []
foo (Z :: xs) = Nothing
foo (S x :: xs) = (foo xs) >>= (\ys => Just $ x :: ys)

fooLen : List Nat -> Maybe Nat
fooLen [] = Just Z
fooLen (Z :: xs) = Nothing
fooLen ((S k) :: xs) = (fooLen xs) >>= (\n => Just $ S n)

data HasFooLen : (xs : List Nat) -> Nat -> Type where
    HFL : (xs : List Nat) -> (fooLen xs = Just len) -> HasFooLen xs len

fooStep : List Nat -> Maybe (List Nat)
fooStep [] = Just []
fooStep (Z :: xs) = Nothing
fooStep ((S k) :: xs) = Just xs

data FooStep : (xs : List Nat) -> (ys : List Nat) -> Type where
    FStep : (xs : List Nat) -> (fooStep xs = Just ys) -> FooStep xs ys

emptyWithPosFooLenImpossible : HasFooLen [] (S n) -> Void
emptyWithPosFooLenImpossible (HFL [] Refl) impossible

Uninhabited (HasFooLen [] (S n)) where
   uninhabited = emptyWithPosFooLenImpossible

fooThm : FooStep xs ys -> HasFooLen xs (S n) -> HasFooLen ys n
fooThm {xs=[]} {ys=[]} {n = Z} (FStep [] Refl) (HFL [] x) = HFL [] Refl
fooThm {xs=[]} {ys=[]} {n = (S _)} (FStep [] Refl) (HFL [] Refl) impossible
fooThm {xs=Z::_} (FStep (Z::_) Refl) (HFL (Z::_) _) impossible
fooThm {xs=(S k)::zs} {ys} {n=n} (FStep ((S k)::zs) prf) (HFL ((S k)::zs) x) = ?fooThm_rhs_4








