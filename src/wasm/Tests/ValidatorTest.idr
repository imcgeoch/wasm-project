module Tests.ValidatorTest

import Validation.JankValidator
import Structure.Types
import Structure.Instr
-- import Data.Vect


%access export


init_ctrl_stack: CtrlStack
init_ctrl_stack = [MkCtrlFrame [] [] 0 False]


testOnePlusOne : IO ()
testOnePlusOne = let prog = [Const (I32Val 1), Const (I32Val 1), IBinOp IAdd W32]
                     os = []
                     cs = init_ctrl_stack
                 in case validate prog os cs of
                        Just (os_out, cs_out) => putStrLn ("Valid with os: " ++ (show os_out) ++ " " ++ "and cs: " ++ (show cs_out))
                        Nothing => putStrLn "Not valid!"
