||| As defined in https://webassembly.github.io/spec/core/exec/runtime.html
module Execution.Runtime

import Structure.Indices
import Structure.Instr
import Structure.Modules
import Structure.Types
import Data.Vect

%access public export


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
        funcs   : List FuncInst
        tables  : List TableInst
        mems    : MemInst    --- XXX: Only using single memory for now!!!
        globals : List GlobalInst



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
        datums : List Bits8
        max    : Maybe Bits32

    Show MemInst where
        show (MkMemInst datums max) = "{mem-inst max: " ++ (show max) ++ "\n               data: " ++ (show datums) ++ "}"

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
Stack : Type
Stack = List Val

%name Stack stack

mutual
    data AdminInstr = Trap
                    | Label Nat Expr ExecExpr Stack
                    | Breaking Nat Stack
                    -- | Invoke FuncAddr
                    -- | InitElem TableAddr Bits32 (Vect _ FuncIdx)
                    -- | InitData MemAddr   Bits32 (Vect _ Bits8)
                    -- | Frm Frame (Vect _ ExecInstr)

    data ExecInstr = Ins Instr | AdIns AdminInstr

    ExecExpr : Type
    ExecExpr = List ExecInstr

    %name ExecExpr expr

||| Convenience function to transform an Instr into ExecInstr
toExecInstr : Instr -> ExecInstr
toExecInstr ins = Ins ins

||| A configuration consists of the current store and an executing thread.
|||
||| https://webassembly.github.io/spec/core/exec/runtime.html#syntax-config
Config : Type
Config = Store

%name Config config

emptyStore : Store
emptyStore = MkStore [] [] (MkMemInst [] Nothing) []
--------------------------------------------------------------------------------
---                            Evaluation Context                            ---
--------------------------------------------------------------------------------

{-
  TODO: I'm not sure what to do for evaluation contexts, defined at
  https://webassembly.github.io/spec/core/exec/runtime.html#evaluation-contexts.
  Do we need to define these explicitly, or can we just model reductions to
  respect them?
-}


