module Tests.JankInterpTestHelp

import Execution.JankInterp
import Execution.Runtime
import Structure.Types
import Structure.Instr
import Util.BitUtil
import Data.Vect

%access public export

{-
--b32_1 : Bits32
--b32_1 = prim__zextInt_B32 1

--b32_2 : Bits32
--b32_2 = prim__zextInt_B32 2

const2 : Constant I32_t
const2 = AConst I32_t 2

const1 : Constant I32_t
const1 = AConst I32_t 1

expr : ExecExpr
expr = (Ins (Const const2)) :: (Ins (Const const1)) :: (Ins (IBinOp IAdd W32)) :: []

config : Config
config = MkStore [] [] [] []

interp : Interp
interp = MkInterp config [] expr StatusRunning

interp1 : Interp
interp1 = oneStep interp

interp2 : Interp
interp2 = oneStep interp1

interp3 : Interp
interp3 = oneStep interp2
-}

strToIns : String -> ExecInstr
strToIns str = case str of
                  "clz" => Ins (IUnOp Clz W32)
                  "ctz" => Ins (IUnOp Ctz W32) 
                  "pop" => Ins (IUnOp Popcnt W32) 
                  "+" => Ins (IBinOp IAdd W32) 
                  "-" => Ins (IBinOp ISub W32)
                  -- fails silently and produces zero on bad input
                  x => Ins (Const (AConst I32_t (prim__zextInt_B32 (cast x)))) 

makeExpr : Vect n String -> ExecExpr
makeExpr [] = [] 
makeExpr (x :: xs) = (strToIns x) :: makeExpr xs

partial
runInterp : Interp -> Interp
runInterp interp = case interp of
                         (MkInterp config stack [] status) => interp 
                         (MkInterp config stack (x :: xs) status) => runInterp (oneStep interp) 

partial
runExpr : ExecExpr -> Interp
runExpr expr = let config = MkStore [] [] [] []
                   interp = MkInterp config [] expr StatusRunning in
                   runInterp interp 

