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
assertResultStack (MkInterp config expr stack) expected =
  if stack == expected
     then putStrLn "[+] Test Passed"
     else putStrLn $ "[!] Test Failed:  Stacks not equal.\n    Expected: "   ++ (show expected) ++ "\n       Found: " ++ (show stack) ++ "\n"

partial test_program : Expr -> Stack -> IO ()
test_program expr expected = let res = runExpr expr in
                                 case res of
                                      Nothing => putStrLn "[!] Runtime Error: Interpreter failed to execute"
                                      Just result => assertResultStack result expected

partial
testOnePlusOne : IO ()
testOnePlusOne = test_program [Const (I32Val 1), Const (I32Val 1), IBinOp IAdd W32] [I32Val 2]

partial
testIf : IO ()
testIf = test_program [Const (I32Val 1), If [I32_t] [Const (I32Val 2)] [Const (I32Val 3)]] [I32Val 2]
