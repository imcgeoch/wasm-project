||| So they aren't really different widths, but we can pretend
data Val = I32 Integer | I64 Integer

total
i32Noti64 : I32 x = I64 y -> Void
i32Noti64 Refl impossible

total
i32Injective : I32 x = I32 y -> x = y
i32Injective Refl = Refl

total
i64Injective : I64 x = I64 y -> x = y
i64Injective Refl = Refl

DecEq Val where
    decEq (I32 x) (I32 y) = case decEq x y of
                                 (Yes Refl) => Yes Refl
                                 (No contra) => No $ \h => contra (i32Injective h)
    decEq (I32 x) (I64 y) = No i32Noti64
    decEq (I64 x) (I32 y) = No (negEqSym i32Noti64)
    decEq (I64 x) (I64 y) = case decEq x y of
                                 (Yes Refl) => Yes Refl
                                 (No contra) => No $ \h => contra (i64Injective h)

mutual
  data BOp = Add64 | Eq64 | Sub64
           | Add32 | Eq32 | Sub32
  data UOp = Neg64 | Neg32

  data Instr = BinOp BOp | UnOp UOp | ConstOp Val
             | If (List Instr) (List Instr)

-- autogen lemmas to assist implementing DecEq for UOp
neg64_not_Neg32 : Neg64 = Neg32 -> Void
neg64_not_Neg32 Refl impossible


||| autogen implementation of DecEq for UOp
DecEq UOp where
    decEq Neg64 Neg64 = Yes Refl
    decEq Neg64 Neg32 = No neg64_not_Neg32
    decEq Neg32 Neg64 = No (negEqSym neg64_not_Neg32)
    decEq Neg32 Neg32 = Yes Refl

-- autogen lemmas to assist implementing DecEq for BOp
add64_not_Eq64 : Add64 = Eq64 -> Void
add64_not_Eq64 Refl impossible

add64_not_Sub64 : Add64 = Sub64 -> Void
add64_not_Sub64 Refl impossible

add64_not_Add32 : Add64 = Add32 -> Void
add64_not_Add32 Refl impossible

add64_not_Eq32 : Add64 = Eq32 -> Void
add64_not_Eq32 Refl impossible

add64_not_Sub32 : Add64 = Sub32 -> Void
add64_not_Sub32 Refl impossible

eq64_not_Sub64 : Eq64 = Sub64 -> Void
eq64_not_Sub64 Refl impossible

eq64_not_Add32 : Eq64 = Add32 -> Void
eq64_not_Add32 Refl impossible

eq64_not_Eq32 : Eq64 = Eq32 -> Void
eq64_not_Eq32 Refl impossible

eq64_not_Sub32 : Eq64 = Sub32 -> Void
eq64_not_Sub32 Refl impossible

sub64_not_Add32 : Sub64 = Add32 -> Void
sub64_not_Add32 Refl impossible

sub64_not_Eq32 : Sub64 = Eq32 -> Void
sub64_not_Eq32 Refl impossible

sub64_not_Sub32 : Sub64 = Sub32 -> Void
sub64_not_Sub32 Refl impossible

add32_not_Eq32 : Add32 = Eq32 -> Void
add32_not_Eq32 Refl impossible

add32_not_Sub32 : Add32 = Sub32 -> Void
add32_not_Sub32 Refl impossible

eq32_not_Sub32 : Eq32 = Sub32 -> Void
eq32_not_Sub32 Refl impossible


||| autogen implementation of DecEq for BOp
DecEq BOp where
    decEq Add64 Add64 = Yes Refl
    decEq Add64 Eq64 = No add64_not_Eq64
    decEq Add64 Sub64 = No add64_not_Sub64
    decEq Add64 Add32 = No add64_not_Add32
    decEq Add64 Eq32 = No add64_not_Eq32
    decEq Add64 Sub32 = No add64_not_Sub32
    decEq Eq64 Add64 = No (negEqSym add64_not_Eq64)
    decEq Eq64 Eq64 = Yes Refl
    decEq Eq64 Sub64 = No eq64_not_Sub64
    decEq Eq64 Add32 = No eq64_not_Add32
    decEq Eq64 Eq32 = No eq64_not_Eq32
    decEq Eq64 Sub32 = No eq64_not_Sub32
    decEq Sub64 Add64 = No (negEqSym add64_not_Sub64)
    decEq Sub64 Eq64 = No (negEqSym eq64_not_Sub64)
    decEq Sub64 Sub64 = Yes Refl
    decEq Sub64 Add32 = No sub64_not_Add32
    decEq Sub64 Eq32 = No sub64_not_Eq32
    decEq Sub64 Sub32 = No sub64_not_Sub32
    decEq Add32 Add64 = No (negEqSym add64_not_Add32)
    decEq Add32 Eq64 = No (negEqSym eq64_not_Add32)
    decEq Add32 Sub64 = No (negEqSym sub64_not_Add32)
    decEq Add32 Add32 = Yes Refl
    decEq Add32 Eq32 = No add32_not_Eq32
    decEq Add32 Sub32 = No add32_not_Sub32
    decEq Eq32 Add64 = No (negEqSym add64_not_Eq32)
    decEq Eq32 Eq64 = No (negEqSym eq64_not_Eq32)
    decEq Eq32 Sub64 = No (negEqSym sub64_not_Eq32)
    decEq Eq32 Add32 = No (negEqSym add32_not_Eq32)
    decEq Eq32 Eq32 = Yes Refl
    decEq Eq32 Sub32 = No eq32_not_Sub32
    decEq Sub32 Add64 = No (negEqSym add64_not_Sub32)
    decEq Sub32 Eq64 = No (negEqSym eq64_not_Sub32)
    decEq Sub32 Sub64 = No (negEqSym sub64_not_Sub32)
    decEq Sub32 Add32 = No (negEqSym add32_not_Sub32)
    decEq Sub32 Eq32 = No (negEqSym eq32_not_Sub32)
    decEq Sub32 Sub32 = Yes Refl


binOp_not_unOp : (BinOp x) = (UnOp y) -> Void
binOp_not_unOp Refl impossible

binOp_not_const : (BinOp x) = (ConstOp y) -> Void
binOp_not_const Refl impossible

binOp_not_if : (BinOp x) = (If xs ys) -> Void
binOp_not_if Refl impossible

binOpInjective : BinOp x = BinOp y -> x = y
binOpInjective Refl = Refl

unOpInjective : UnOp x = UnOp y -> x = y
unOpInjective Refl = Refl

unOp_not_const : (UnOp x) = (ConstOp y) -> Void
unOp_not_const Refl impossible

unOp_not_if : (UnOp x) = (If xs ys) -> Void
unOp_not_if Refl impossible

constOpInjective : ConstOp x = ConstOp y -> x = y
constOpInjective Refl = Refl

constOp_not_if : (ConstOp x) = (If xs ys) -> Void
constOp_not_if Refl impossible

ifInjectiveLeft : (If t1 e1) = (If t2 e2) -> t1 = t2
ifInjectiveLeft Refl = Refl

ifInjectiveRight : (If t1 e1) = (If t2 e2) -> e1 = e2
ifInjectiveRight Refl = Refl

||| autogen implementation of DecEq for Instr
DecEq Instr where
    decEq (BinOp x) (BinOp y) =
        case decEq x y of
             Yes Refl  => Yes Refl
             No contra => No $ \h => contra (binOpInjective h)
    decEq (BinOp x) (UnOp y) = No binOp_not_unOp
    decEq (BinOp x) (ConstOp y) = No binOp_not_const
    decEq (BinOp x) (If xs ys) = No binOp_not_if
    decEq (UnOp x) (BinOp y) = No $ negEqSym binOp_not_unOp
    decEq (UnOp x) (UnOp y) =
            case decEq x y of
                 Yes Refl  => Yes Refl
                 No contra => No $ \h => (contra . unOpInjective) h
    decEq (UnOp x) (ConstOp y) = No unOp_not_const
    decEq (UnOp x) (If xs ys) = No unOp_not_if
    decEq (ConstOp x) (BinOp y) = No $ negEqSym binOp_not_const
    decEq (ConstOp x) (UnOp y) = No $ negEqSym unOp_not_const
    decEq (ConstOp x) (ConstOp y) =
            case decEq x y of
                 Yes Refl => Yes Refl
                 No contra => No $ \h => (contra . constOpInjective) h
    decEq (ConstOp x) (If xs ys) = No constOp_not_if
    decEq (If xs ys) (BinOp x) = No $ negEqSym binOp_not_if
    decEq (If xs ys) (UnOp x) = No $ negEqSym unOp_not_if
    decEq (If xs ys) (ConstOp x) = No $ negEqSym constOp_not_if
    decEq (If t e) (If t' e') = assert_total (case decEq t t' of
            Yes Refl => (case decEq e e' of
                              Yes Refl => Yes Refl
                              No contra => No $ \h => (contra .  ifInjectiveRight) h )
            No contra => No $ \h => (contra . ifInjectiveLeft) h)

data Error = StackUnderflow | TypeError

record Interp where
  constructor MkInterp
  vs : List Val 
  es : List Instr

data Tp = T32 | T64
data IntrpTp = List Tp

mkInterpInjectiveVs : (MkInterp vs1 _) = (MkInterp vs2 _) -> vs1 = vs2
mkInterpInjectiveVs Refl = Refl

mkInterpInjectiveEs : (MkInterp _ es1) = (MkInterp _ es2) -> es1 = es2
mkInterpInjectiveEs Refl = Refl

DecEq Interp where
    decEq (MkInterp vs es) (MkInterp vs' es') 
     = case (decEq vs vs', decEq es es')  of
       (Yes Refl, Yes Refl) => Yes Refl 
       (No contra, _) => No $ \h => contra (mkInterpInjectiveVs h) 
       (_ , No contra) => No $ \h => contra (mkInterpInjectiveEs h) 

typNotStack : TypeError = StackUnderflow -> Void
typNotStack Refl impossible


DecEq Error where
  decEq TypeError TypeError = Yes Refl
  decEq TypeError StackUnderflow = No typNotStack 
  decEq StackUnderflow StackUnderflow = Yes Refl
  decEq StackUnderflow TypeError = No $ negEqSym typNotStack

{-        
case decEq vs vs' of
             (Yes Refl) => ?rasdf_3
             (No contra) => ?rasdf_2
           -}

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
interp (MkInterp vs []) = Right vs 
interp interperter = case step interperter of
                                  (Left error) => Left error
                                  (Right interperter') => interp interperter' 


data OneStep : Interp -> Interp -> Type where
  Step : (i : Interp) -> (i' : Interp) -> (step i = Right i') -> OneStep i i' 

data OneStepDec : Interp -> Interp -> Type where
  DStep : (i : Interp) -> (i' : Interp) -> Dec (step i = Right i') -> OneStepDec i i' 

errorsDiff : (Left StackUnderflow = Left TypeError) -> Void
errorsDiff Refl impossible

errorNotSuccess : (Left l = Right r) -> Void
errorNotSuccess Refl impossible

checkInterpSame : (x : Interp) -> (y : Interp) -> Dec (x = y)
checkInterpSame x y = decEq x y

checkEInterpSame : (x : Either Error Interp) -> (y : Either Error Interp) -> Dec (x = y)
checkEInterpSame (Left l) (Right r) = No errorNotSuccess 
checkEInterpSame (Right r) (Left l) = No $ negEqSym errorNotSuccess 
checkEInterpSame (Left x) (Left y) 
  = case decEq x y of
       Yes Refl => Yes Refl
       No contra => No $ \h => contra (leftInjective h) 
checkEInterpSame (Right x) (Right y) 
  = case decEq x y of
       Yes Refl => Yes Refl
       No contra => No $ \h => contra (rightInjective h) 


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

