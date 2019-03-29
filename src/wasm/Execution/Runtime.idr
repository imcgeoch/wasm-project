||| As defined in https://webassembly.github.io/spec/core/exec/runtime.html
module Execution.Runtime

import Structure.Indices
import Structure.Instr
import Structure.Modules
import Structure.Types
import Data.Vect

%access public export

||| Wasm computations manipulate values of the four basic types.
|||
||| Note: We can possibly remove this as we are just wrapping Idris values, but
|||       I'm keeping it in for now to conform to the spec.
|||
||| Spec: https://webassembly.github.io/spec/core/exec/runtime.html#syntax-val
data Val = I32Val Bits32
         | I64Val Void    -- XXX: Can't be created yet
         | F32Val Void    -- XXX: Can't be created yet
         | F64Val Void    -- XXX: Can't be created yet


||| A result is the outcome of a computation. It is either a sequence of values
||| or a trap.
|||
||| Note: In the current version of WASM, a result can consist of at most one
||| value.
|||
||| Spec: https://webassembly.github.io/spec/core/exec/runtime.html#syntax-result
data Result = ResultVal (Maybe Val) | TrapVal

--- Addresses: https://webassembly.github.io/spec/core/exec/runtime.html#syntax-addr

||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-addr
Addr : Type
Addr = Nat

||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-funcaddr
FuncAddr : Type
FuncAddr = Addr

||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-tableaddr
TableAddr : Type
TableAddr = Addr

||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-memaddr
MemAddr : Type
MemAddr = Addr

||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-globaladdr
GlobalAddr : Type
GlobalAddr = Addr

mutual
    ||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-store
    record Store where
        constructor MkStore
        funcs   : Vect n1 FuncInst
        tables  : Vect n2 TableInst
        mems    : Vect n3 MemInst
        globals : Vect n4 GlobalInst



    ||| A _module instance_ is the runtime representation of a `module`. It is
    ||| created by instantiating a module and collects runtime representations
    ||| of all entities that are imported, defined, or exported by the module.
    |||
    ||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-moduleinst
    record ModuleInst where
        constructor MkModuleInst
        types       : Vect numTypes FuncType
        funcAddrs   : Vect numFuncs FuncAddr
        tableAddrs  : Vect numTabs  TableAddr
        memAddrs    : Vect numMems  MemAddr
        globalAddrs : Vect numGlobs GlobalAddr
        exports     : Vect numExports ExportInst


    ||| A _function instance_ is a runtime representation of a `function`. It
    ||| effectively is a _closure_ of the original function over the runtime
    ||| module instance of its originating module.
    |||
    ||| Note: We could simplify this by not including HostFuncInst
    |||
    ||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-funcinst
    FuncInst : Type
    FuncInst = Either NativeFuncInst HostFuncInst

    record NativeFuncInst where
        constructor MkNativeFuncInst
        type  : FuncType
        modul : ModuleInst
        code  : Func

    ||| A host function is a function expressed outside of Wasm but passed to a
    ||| module as an import. The definition and behavior of host functions are
    ||| outside the scope of this specification. For the purpose of this
    ||| specification, it is assumed that when invoked, the host function
    ||| behaves non-deterministically, but withing certain constraints that
    ||| ensure integrity at runtime.
    |||
    ||| I've defined a HostFuncInst as an Idris function from some type a to b
    record HostFuncInst where
        constructor MkHostFuncInst
        type     : FuncType
        code     : a -> b

    ||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-tableinst
    record TableInst where
        constructor MkTableInst
        elem : Vect size FuncElem
        max  : Maybe Bits32

    ||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-funcelem
    FuncElem : Type
    FuncElem = Maybe FuncAddr

    ||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-meminst
    record MemInst where
        constructor MkMemInst
        datums : Vect len Bits8
        max    : Maybe Bits32

    ||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-globalinst
    record GlobalInst where
        constructor MkGlobalInst
        value : Val
        mut   : Mut

    ||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-exportinst
    record ExportInst where
        constructor MkExportInst
        name  : String
        value : ExternVal

    ||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-externval
    data ExternVal = ExtFunc Func
                   | ExtTable Table
                   | ExtMem Mem
                   | ExtGlobal GlobalAddr

    --- Conventions
    --- from https://webassembly.github.io/spec/core/exec/runtime.html#conventions
    funcs : Vect n ExternVal -> (m ** Vect m ExternVal)
    funcs = filter (\x => case x of ExtFunc arg => True
                                    _           => False)

    tables : Vect n ExternVal -> (m ** Vect m ExternVal)
    tables = filter (\x => case x of ExtTable arg => True
                                     _            => False)

    mems : Vect n ExternVal -> (m ** Vect m ExternVal)
    mems = filter (\x => case x of ExtMem arg => True
                                   _          => False)

    globals : Vect n ExternVal -> (m ** Vect m ExternVal)
    globals = filter (\x => case x of ExtGlobal arg => True
                                      _             => False)

mutual
    ||| https://webassembly.github.io/spec/core/exec/runtime.html#labels
    record Label where
        constructor MkLabel
        arity : Nat
        cont  : Expr m

    ||| https://webassembly.github.io/spec/core/exec/runtime.html#frames
    record Activation where
        constructor MkActivation
        arity : Nat
        frame : Frame

    ||| https://webassembly.github.io/spec/core/exec/runtime.html#frames<Paste>
    record Frame where
        constructor MkFrame
        locals : Vect numVals Val
        modul  : ModuleInst


||| https://webassembly.github.io/spec/core/exec/runtime.html#stack
data StackEntry = StVal Val
                | StLabel Label
                | StFrame Frame

||| https://webassembly.github.io/spec/core/exec/runtime.html#stack
Stack : Nat ->  Type
Stack n = Vect n StackEntry

%name Stack stack

mutual
    data AdminInstr = Trap
                    | Invoke FuncAddr
                    | InitElem TableAddr Bits32 (Vect _ FuncIdx)
                    | InitData MemAddr   Bits32 (Vect _ Bits8)
                    | Lab Label (Vect _ ExecInstr)
                    | Frm Frame (Vect _ ExecInstr)

    data ExecInstr = Ins Instr | AdIns AdminInstr

    ExecExpr : Nat -> Type
    ExecExpr n = Vect n ExecInstr

    %name ExecExpr expr

||| Convenience function to transform an Instr into ExecInstr
toExecInstr : Instr -> ExecInstr
toExecInstr ins = Ins ins

||| Convenience function to map a Vect of Instrs to a Vect n of ExecInstrs
toExecInstrs : Vect n Instr -> Vect n ExecInstr
toExecInstrs = map toExecInstr

||| A thread is a computation over instructions that operates relative to a
||| current frame referring to the home module instance that the computation
||| runs in.
|||
||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-thread
Thread : Nat -> Type
Thread n = (Frame, ExecExpr n)

||| A configuration consists of the current store and an executing thread.
|||
||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-config
Config : Nat -> Type
Config n = (Store, Thread n)

%name Config config

--------------------------------------------------------------------------------
---                            Evaluation Context                            ---
--------------------------------------------------------------------------------

{-
  TODO: I'm not sure what to do for evaluation contexts, defined at
  https://webassembly.github.io/spec/core/exec/runtime.html#evaluation-contexts.
  Do we need to define these explicitly, or can we just model reductions to
  respect them?
-}


