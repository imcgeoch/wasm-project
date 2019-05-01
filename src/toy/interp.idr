mutual
  data BOp = Add | Eq | Sub
  data UOp = Neg 

  data Instr = BinOp BOp | UnOp UOp | ConstOp Integer

data Error = StackUnderflow

record Interp where
  constructor MkInterp
  stack : List Integer 
  instr : List Instr

oneStepBinOp : Integer -> Integer -> BOp -> Integer
oneStepBinOp x y Add = x + y 
oneStepBinOp x y Eq = (case decEq x y of
                            (Yes Refl) => 1 
                            (No contra) => 0 ) 
oneStepBinOp x y Sub = x - y 

oneStepUnOp : Integer -> UOp -> Integer

interp : Interp -> Either Error Interp 
interp (MkInterp [] []) = Right (MkInterp [] []) 
interp (MkInterp xs ((ConstOp y) :: ys)) = interp $ MkInterp (y :: xs) (ys) 
interp (MkInterp [] (_ :: xs)) = Left StackUnderflow
interp (MkInterp xs []) = Right $ MkInterp xs []
interp (MkInterp (x :: []) ((BinOp y) :: ys)) = Left StackUnderflow 
interp (MkInterp (x :: (z :: xs)) ((BinOp y) :: ys)) 
  = interp $ MkInterp (oneStepBinOp x z y :: xs) (ys)
interp (MkInterp (x :: xs) ((UnOp y) :: ys)) 
  = interp $ MkInterp (oneStepUnOp x y :: xs) (ys) 


int1 : Interp
int1 = MkInterp [1, 2] [BinOp Add]

int2 : Interp
int2 = MkInterp [1] [BinOp Add]
