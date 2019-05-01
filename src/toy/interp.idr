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

typeOf : Val -> Tp
typeOf (I32 x) = T32
typeOf (I64 x) = T64

int1 : Interp
int1 = MkInterp [I64 1, I64 2] [BinOp Add64]

int2 : Interp
int2 = MkInterp [I64 1] [BinOp Add64]
