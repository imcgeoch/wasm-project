module Tests.JankInterpTest

import Tests.JankInterpTestHelp 
import Execution.JankInterp
import Execution.Runtime
import Structure.Types
import Structure.Instr
import Util.BitUtil
import Data.Vect


%access export

valsEq : {vt : ValType} -> machineType vt -> machineType vt -> Bool
valsEq {vt} x y = case vt of
                       (IValTp (ITp W32)) => x == y 
                       (IValTp (ITp W64)) => x == y 
                       (FValTp (FTp W32)) => x == y 
                       (FValTp (FTp W64)) => x == y 

stacksEq : Stack -> Stack -> Bool
stacksEq [] [] = True 
stacksEq [] (x :: xs) = False 
stacksEq (x :: xs) [] = False 
stacksEq (x :: xs) (y :: ys) = if x == y then stacksEq xs ys
                                         else False

assertCorrect : Interp -> Stack -> IO ()
assertCorrect (MkInterp config stack expr status) expected
  = case status of
         StatusRunning => if stack == expected
                             then putStrLn "Test Passed"
                             else putStrLn "Test Failed: Stacks not equal"  
         _ => putStrLn "Test Failed: Not Successful"

twoOnStack : Stack
twoOnStack = [I32Val 2]

partial
testOnePlusOne : IO ()
testOnePlusOne = let expr = makeExpr ["1", "1", "+"]
                     result = runExpr expr
                     expected = twoOnStack
                     in assertCorrect result expected 

testEasy : IO ()
testEasy = putStrLn "Test Passed" 

--- TEST BLOCKS

p : Expr
p = [Block Nothing []]

