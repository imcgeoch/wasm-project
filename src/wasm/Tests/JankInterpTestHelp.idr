module Tests.JankInterpTestHelp

import Execution.JankInterp
import Execution.Runtime
import Structure.Types
import Structure.Instr
import Util.BitUtil
import Data.Vect
import Tests.SamplePrograms

%access public export

||| Create a new interp with n bytes of memory
newInterpWithMemory : Nat -> Expr -> Interp
newInterpWithMemory n expr = MkInterp store es [] where
    store : Store
    store = (MkStore [] [] (MkMemInst (replicate n 0) Nothing) [])
    es : ExecExpr
    es = (map toExecInstr expr)


newInterp : Expr -> Interp
newInterp = newInterpWithMemory 0

strToIns : String -> ExecInstr
strToIns str = case str of
                  -- "clz" => Ins (IUnOp Clz W32)
                  -- "ctz" => Ins (IUnOp Ctz W32) 
                  -- "pop" => Ins (IUnOp Popcnt W32) 
                  "+" => Ins (IBinOp IAdd W32) 
                  "-" => Ins (IBinOp ISub W32)
                  -- fails silently and produces zero on bad input
                  x => Ins (Const (I32Val (prim__zextInt_B32 (cast x)))) 

makeExpr : Vect n String -> ExecExpr
makeExpr [] = [] 
makeExpr (x :: xs) = (strToIns x) :: makeExpr xs

partial
runInterp : Interp -> Maybe Interp
runInterp interp = case step interp of
                        Nothing => Nothing
                        (Just (MkInterp config [] stack)) => Just $ MkInterp config [] stack
                        (Just (MkInterp config (e :: es) stack)) => runInterp $ MkInterp config (e :: es) stack

partial
runExpr : Expr -> Maybe Interp
runExpr expr = runInterp (newInterp expr)

welcomeWagon : String
welcomeWagon = unlines [ "+------------------------------------------------------------------------------+"
                       , "| Welcome to the WASM Debugger                                                 |"
                       , "| Author: Ben Kushigian                                                        |"
                       , "| Date: 2019                                                                   |"
                       , "| Reason: Coffee                                                               |"
                       , "| Usage: Don't                                                                 |"
                       , "|                                                                              |"
                       , "| This is a simple debugger that lets you step through wasm programs using the |"
                       , "| JankInterpreter. It's pretty simple: `(n)ext` steps through the next         |"
                       , "| instruction, `(d)ump` dumps the interpreter to screen, and `e(x)it`          |"
                       , "| terminates the debugging session. For information, enter `(h)elp`.           |"
                       , "+------------------------------------------------------------------------------+"
                       ]

dumpInterp : Interp -> String
dumpInterp (MkInterp config expr stack) =
    unlines [ "--------------------------------------------------------------------------------"
            , "                            INTERPRETER DUMP"
            , "mem: " ++ (show (mems config))
            , "stack: " ++ (show stack)
            , "expr:  " ++ (show expr)
            , "--------------------------------------------------------------------------------\n"
            ]
                                  
helpStr : String
helpStr = unlines [ "--------------------------------------------------------------------------------"
                  , "                          WASM DEBUGGER HELP"
                  , "(n)ext: Execute next instruction"
                  , "(d)ump: Dump current state"
                  , "e(x)it: Exit the debugger"
                  , "(h)elp: Display this help message"
                  , "(r)un n: Run program for n steps; if n is not specified, run to end of program"
                  , "--------------------------------------------------------------------------------"
                  ]

procInput : Interp -> String -> Maybe (String, Interp)
procInput interp "next" = case step interp of
                               Nothing => Just ("Terminated", interp)
                               Just x  => Just (dumpInterp x, x)
procInput interp "run" = let result = runInterp interp in Just (dumpInterp interp, interp)
procInput interp "dump" = Just (dumpInterp interp, interp)
procInput interp "exit" = Nothing
procInput interp "help" = Just (helpStr, interp)
procInput interp "n" = procInput interp "next"
procInput interp "d" = procInput interp "dump"
procInput interp "r" = procInput interp "run"
procInput interp "x" = procInput interp "exit"
procInput interp "h" = procInput interp "help"
procInput interp _ = Just ((dumpInterp interp) ++ "Error: couldn't read input\n", interp)

debug' : Interp -> IO ()
debug' interp = replWith interp "DEBUG> " procInput

debugWithMemory : Nat -> Expr -> IO()
debugWithMemory k expr = do
    putStrLn $ welcomeWagon
    debug' (newInterpWithMemory k expr)

debug : Expr -> IO ()
debug = debugWithMemory 0

printAThing : IO ()
printAThing = putStrLn "a thing"
