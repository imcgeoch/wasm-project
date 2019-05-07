module Tests.JankInterpTest

import Tests.JankInterpTestHelp 
import Execution.JankInterp
import Execution.Runtime
import Structure.Types
import Structure.Instr
import Util.BitUtil
import Data.Vect


%access export

assertResultStack : Interp -> Stack -> IO ()
assertResultStack (MkInterp config stack expr status) expected
  = case status of
         StatusRunning => if stack == expected
                             then putStrLn "Test Passed"
                             else putStrLn $ "[!] Test Failed:  Stacks not equal.\n    Expected: "   ++ (show expected) ++ "\n       Found: " ++ (show stack) ++ "\n"
         _ => putStrLn "Test Failed: Not Successful"

partial
testOnePlusOne : IO ()
testOnePlusOne = let expr = [Const (I32Val 1), Const (I32Val 1), IBinOp IAdd W32]
                     result = runExpr expr
                     expected = [I32Val 2]
                     in assertResultStack result expected

partial
testIf_1 : IO ()
testIf_1 = let result = runExpr [Const (I32Val 1), If (Just I32_t) [Const (I32Val 2)] [Const (I32Val 3)]]
            in assertResultStack result [I32Val 2]

--- TEST BLOCKS

p : Expr
p = [Block Nothing []]

