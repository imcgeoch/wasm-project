module Toy

data Val = I32 Bits32 | I64 Bits64

Stack : Type
Stack = List Val

mutual
    data Instr = I32Add | I64Add | If Expr Expr | Const Val

    Expr : Type
    Expr = List Instr

Code : Type
Code = (Expr, Stack)

step : Code -> Maybe Code
step cd@(es, vs) = case es of
     [] => Just cd
     (I32Add :: es') => case vs of
           (I32 x) :: (I32 y) :: vs' => Just (es', I32 (prim__addB32 x y) :: vs')
           _ => Nothing
     (I64Add :: es') => case vs of
           (I64 x) :: (I64 y) :: vs' => Just (es', I64 (prim__addB64 x y) :: vs')
           _ => Nothing

     ((If thn els) :: es') => case vs of
            (I32 x) :: vs' => Just ((if x /= 0 then thn else els) ++ es', vs')

     (Const x) :: es' => ?rhs

data OneStep : Code -> Code -> Type where
    OStep : (c : Code) -> (c' : Code) -> (step c = Just c') -> OneStep c c'

data Tp = T32 | T64

CodeTp : Type
CodeTp = List Tp

type' : Val -> Tp
type' (I32 x) = T32
type' (I64 x) = T64


