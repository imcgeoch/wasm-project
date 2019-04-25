module SamplePrograms

import Structure.Instr
import Structure.Types
import Structure.Indices

%access export

||| ifProg1: This program pushes 1 onto the stack and then runs an if statement.
|||          This if statement should evaluate the `then` clause and push a single
|||          value to the stack of the parent (top level) stack.
|||
||| Expected final stack: [2)
ifProg1 : Expr
ifProg1 = [Const (I32Val 1), If (Just I32_t) [Const (I32Val 2)] [Const (I32Val 3)]]

||| ifProg2: This program pushes 1 onto the stack and then runs an if statement.
|||     This if statement should evaluate the `then` clause and not push any
|||     value to the stack of the parent (top level) stack (since the return
|||     type is `Nothing`)
|||
||| Expected final stack: [)
ifProg2 : Expr
ifProg2 = [Const (I32Val 1), If Nothing [Const (I32Val 2)] [Const (I32Val 3)]]

||| storeLocal1: This program stores the I32 const `123` to memory location 0.
|||
||| Expected final state: 
|||        stack: [)
|||        mem:   [123]
storeLocal1 : Expr
storeLocal1 = [Const (I32Val 123), IStore (ITp W32) (MkMemArg 0 0)]

loadLocal1 : Expr
loadLocal1 = [ILoad (ITp W32) (MkMemArg 0 0)]


storeLoadLoadAdd : Expr
storeLoadLoadAdd = [ Const (I32Val 13)
                   , IStore (ITp W32) (MkMemArg 0 0)
                   , ILoad  (ITp W32) (MkMemArg 0 0) 
                   , ILoad  (ITp W32) (MkMemArg 0 0) 
                   , IBinOp IAdd W32
                   , IStore (ITp W32) (MkMemArg 0 0)
                   ]
                    
loopProg1 : Expr
loopProg1 = [ Const (I32Val 5)
            , IStore (ITp W32) (MkMemArg 0 0)
            , Loop (Just I32_t) [ ILoad (ITp W32) (MkMemArg 0 0)   -- Load x
                                , Const (I32Val 1)                 -- push 1
                                , IBinOp ISub W32                  -- sub
                                , IStore (ITp W32) (MkMemArg 0 0)  -- save
                                , ILoad (ITp W32) (MkMemArg 0 0)   -- load
                                , BrIf 0]]
