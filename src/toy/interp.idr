||| So they aren't really different widths, but we can pretend
data Val = I32 Integer | I64 Integer

mutual
  data BOp = Add64 | Eq64 | Sub64 
           | Add32 | Eq32 | Sub32
  data UOp = Neg64 | Neg32 

  data Instr = BinOp BOp | UnOp UOp | ConstOp Val 
             | If (List Instr) (List Instr) 

data Error = StackUnderflow | TypeError

record Interp where
  constructor MkInterp
  stack : List Val 
  instr : List Instr

data Tp = T32 | T64
data IntrpTp = List Tp


oneStepBinOp : Val -> Val -> BOp -> Either Error Val
oneStepBinOp (I32 x) (I32 y) Add32 = Right $ I32 (x + y) 
oneStepBinOp (I32 x) (I32 y) Sub32 = Right $ I32 (x - y)  
oneStepBinOp (I32 x) (I32 y) Eq32 =  let val = case decEq x y of
                                                 (Yes Refl) => 1 
                                                 (No contra) => 0 
                                     in Right $ I32 val
oneStepBinOp (I64 x) (I64 y) Add64 = Right $ I64 (x + y) 
oneStepBinOp (I64 x) (I64 y) Sub64 = Right $ I64 (x - y)  
oneStepBinOp (I64 x) (I64 y) Eq64 =  let val = case decEq x y of
                                                 (Yes Refl) => 1 
                                                 (No contra) => 0 
                                     in Right $ I64 val
oneStepBinOp _ _ _ = Left TypeError 

oneStepUnOp : Val -> UOp -> Either Error Val
oneStepUnOp (I32 x) Neg32 = Right $ I32 (0 - x)
oneStepUnOp (I64 x) Neg64 = Right $ I64 (0 - x)
oneStepUnOp _ _ = Left TypeError

step : Interp ->  Either Error Interp
step (MkInterp [] []) = ?step_rhs_1
step (MkInterp xs (ConstOp y :: ys)) = Right $ MkInterp (y :: xs) ys 
step (MkInterp (x :: xs) []) = ?step_rhs_2
step (MkInterp (x :: []) ((BinOp y) :: ys)) = Left StackUnderflow 
step (MkInterp (x :: (x' :: xs)) ((BinOp y) :: ys)) 
  = case oneStepBinOp x x' y of
         (Left error) => Left error
         (Right val) => Right $ MkInterp (val :: xs) ys
step (MkInterp (x :: xs) ((UnOp y) :: ys)) 
  = case oneStepUnOp x y of
         (Left error) => Left error
         (Right val) => Right $ MkInterp (val :: xs) ys
step (MkInterp xs ((ConstOp c) :: ys)) = Right $ MkInterp (c :: xs) (ys) 
step (MkInterp ((I32 x) :: xs) ((If lst1 lst2) :: ys)) 
  = case decEq x 0 of
         (Yes Refl) => Right $ MkInterp xs (lst2 ++ ys)
         (No contra) => Right $ MkInterp xs (lst1 ++ ys) 
step (MkInterp ((I64 x) :: xs) ((If lst1 lst2) :: ys)) 
  = case decEq x 0 of
         (Yes Refl) => Right $ MkInterp xs (lst2 ++ ys)
         (No contra) => Right $ MkInterp xs (lst1 ++ ys) 

interp : Interp -> Either Error (List Val) 
interp (MkInterp stack []) = Right stack 
interp interperter = case step interperter of
                                  (Left error) => Left error
                                  (Right interperter') => interp interperter' 


data OneStep : Interp -> Interp -> Type where
  Step : (i : Interp) -> (i' : Interp) -> (step i = Right i') -> OneStep i i' 

data OneStepDec : Interp -> Interp -> Type where
  DStep : (i : Interp) -> (i' : Interp) -> Dec (step i = Right i') -> OneStepDec i i' 

errorsDiff1 : (Left StackUnderflow = Left TypeError) -> Void
errorsDiff1 Refl impossible

errorsDiff2 : (Left TypeError = Left StackUnderflow) -> Void
errorsDiff2 Refl impossible

errorNotSuccess1 : (Left l = Right r) -> Void
errorNotSuccess1 Refl impossible

errorNotSuccess2 : (Right r = Left l) -> Void
errorNotSuccess2 Refl impossible


checkInterpSame : (x : Interp) -> (y : Interp) -> Dec (x = y)
checkInterpSame (MkInterp [] []) (MkInterp [] []) = Yes Refl 
checkInterpSame (MkInterp [] []) (MkInterp [] (x :: xs)) = No ?instrDiff1 
checkInterpSame (MkInterp [] (x :: xs)) (MkInterp [] []) = No ?instrDiff2 
checkInterpSame (MkInterp [] (x :: xs)) (MkInterp [] (y :: ys)) = ?checkInterpSame_rhs_2
checkInterpSame (MkInterp [] ws) (MkInterp (x :: xs) ys) = ?checkInterpSame_rhs_4
checkInterpSame (MkInterp (x :: zs) ws) (MkInterp xs ys) = ?checkInterpSame_rhs_3


checkEInterpSame : (x : Either Error Interp) -> (y : Either Error Interp) -> Dec (x = y)
checkEInterpSame (Left StackUnderflow) (Left StackUnderflow) = Yes Refl 
checkEInterpSame (Left TypeError) (Left TypeError) = Yes Refl 
checkEInterpSame (Left StackUnderflow) (Left TypeError) = No errorsDiff1 
checkEInterpSame (Left TypeError) (Left StackUnderflow) = No errorsDiff2
checkEInterpSame (Left l) (Right r) = No errorNotSuccess1 
checkEInterpSame (Right r) (Left l) = No errorNotSuccess2 
checkEInterpSame (Right r) (Right x) = ?rhs 


typeOf : Val -> Tp
typeOf (I32 _) = T32
typeOf (I64 _) = T64

int1 : Interp
int1 = MkInterp [I64 1, I64 2] [BinOp Add64]

int2 : Interp
int2 = MkInterp [I64 1] [BinOp Add64]

int3 : Interp
int3 = MkInterp [I64 3] []

justThreeIsJustThree : (Right (MkInterp [I64 3] [])) = (Right (MkInterp [I64 3] []))
justThreeIsJustThree = Refl

