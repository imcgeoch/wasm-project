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

compareStacks : (x : StackEntry) -> (y : StackEntry) -> Bool
compareStacks (StVal (AConst vt val)) (StVal (AConst vt' val')) 
  = (case decEq vt vt' of
          (Yes Refl) => valsEq val val' 
          (No contra) => False) 

compareStacks (StLabel (MkLabel arity cont)) (StLabel (MkLabel arity' cont')) = ?compareStacks_rhs_3
compareStacks (StFrame (MkFrame locals modul)) (StFrame (MkFrame locals' modul')) = ?compareStacks_rhs_4
compareStacks _ _ = False 

stacksEq : Stack n -> Stack m -> Bool
stacksEq [] [] = True 
stacksEq [] (x :: xs) = False 
stacksEq (x :: xs) [] = False 
stacksEq (x :: xs) (y :: ys) = if (compareStacks x y)
                                 then stacksEq xs ys
                                 else False

assertCorrect : Interp -> Stack n -> IO ()
assertCorrect (MkInterp config stack expr status) stack' 
  = case status of
         StatusRunning => if stacksEq stack stack' 
                             then putStrLn "Test Passed"
                             else putStrLn "Test Failed: Stacks not equal"  
         _ => putStrLn "Test Failed: Not Successful"

twoOnStack : Stack 1
twoOnStack = [StVal (AConst (IValTp (ITp W32)) 2)]

partial
testOnePlusOne : IO ()
testOnePlusOne = let expr = makeExpr ["1", "1", "+"]
                     result = runExpr expr
                     expected = twoOnStack
                     in assertCorrect result expected 

testEasy : IO ()
testEasy = putStrLn "Test Passed" 

