module JankInterpTest

import Execution.JankInterp
import Execution.Runtime
import Structure.Types
import Structure.Instr
import Util.BitUtil
import Data.Vect

b32_1 : Bits32
b32_1 = prim__zextInt_B32 1

b32_2 : Bits32
b32_2 = prim__zextInt_B32 2

const2 : Constant I32_t
const2 = AConst I32_t b32_2

const1 : Constant I32_t
const1 = AConst I32_t b32_1

expr : ExecExpr 3
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

