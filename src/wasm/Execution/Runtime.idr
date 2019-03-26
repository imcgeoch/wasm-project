||| As defined in https://webassembly.github.io/spec/core/exec/runtime.html
module Execution.Runtime

import Structure.Indices
import Structure.Instr
import Structure.Modules
import Structure.Types
import Data.Vect

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
        hostcode : a -> b

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
                | StFrame

||| https://webassembly.github.io/spec/core/exec/runtime.html#stack
Stack : Nat ->  Type
Stack n = Vect n StackEntry

mutual
    ExecExpr : Nat -> Type
    ExecExpr n = Vect n ExecInstr

    data ExecInstr =
          I32Const Bits32
        | I32_clz
        | I32_ctz
        | I32_add
        | I32_sub
        | I32_mul
        | I32_div_s
        | I32_div_u
        | I32_rem_s
        | I32_rem_u
        | I32_or
        | I32_xor
        | I32_shl
        | I32_shr_s
        | I32_shr_u
        | I32_rotl
        | I32_rotr
        | I32_eqz
        | I32_eq
        | I32_ne
        | I32_lt_s
        | I32_lt_u
        | I32_gt_s
        | I32_gt_u
        | I32_le_s
        | I32_le_u
        | I32_ge_s
        | I32_ge_u
        -- Parametric Instructions
        | Drop
        | Select
        -- Variable Instructions
        | Local_get LocalIdx
        | Local_set LocalIdx
        | Local_tee LocalIdx
        | Global_get GlobalIdx
        | Global_set GlobalIdx
        -- Memory Instructions
        | I32_load  MemArg
        | I32_store MemArg
        | I32_load8_s  MemArg
        | I32_load8_u  MemArg
        | I32_load16_s MemArg
        | I32_load16_u MemArg
        | I32_store8_s  MemArg
        | I32_store8_u  MemArg
        | I32_store16_s MemArg
        | I32_store16_u MemArg
        | Mem_size
        | Mem_grow
        -- Control Instructions
        | Nop
        | Unreachable
        | Block ResultType (Vect _ ExecInstr)
        | Loop  ResultType (Vect _ ExecInstr)
        | If    ResultType (Vect _ ExecInstr) (Vect _ ExecInstr)
        | Br    LabelIdx
        | BrIf  LabelIdx
        -- br_table, the first argument (the Vect) is a `vec` type in the WASM
        -- spec, which has the additional constraint that n < 2^32. We will need
        -- to create a new type for this, but creating 2^32 in Nats will be
        -- super expensive. Work around? Just don't worry about it?
        | BrTable (Vect n LabelIdx) LabelIdx
        | Return
        | FnCall FuncIdx
        | FnCall_Indirect TypeIdx
        -- Admin Syntax
        | Trap
        | Invoke FuncAddr
        | InitElem TableAddr Bits32 (Vect _ FuncIdx)
        | InitData MemAddr   Bits32 (Vect _ Bits8  )
        | Lbl Label (Vect _ ExecInstr)
        | Frm Frame (Vect _ ExecInstr)

||| Convert static instructions to dynamic instructions
instrToExecInstr : Instr -> ExecInstr
instrToExecInstr (I32Const x) = I32Const x
instrToExecInstr I32_clz = I32_clz
instrToExecInstr I32_ctz = I32_ctz
instrToExecInstr I32_add = I32_add
instrToExecInstr I32_sub = I32_sub
instrToExecInstr I32_mul = I32_mul
instrToExecInstr I32_div_s = I32_div_s
instrToExecInstr I32_div_u = I32_div_u
instrToExecInstr I32_rem_s = I32_rem_s
instrToExecInstr I32_rem_u = I32_rem_u
instrToExecInstr I32_or = I32_or
instrToExecInstr I32_xor = I32_xor
instrToExecInstr I32_shl = I32_shl
instrToExecInstr I32_shr_s = I32_shr_s
instrToExecInstr I32_shr_u = I32_shr_u
instrToExecInstr I32_rotl = I32_rotl
instrToExecInstr I32_rotr = I32_rotr
instrToExecInstr I32_eqz = I32_eqz
instrToExecInstr I32_eq = I32_eq
instrToExecInstr I32_ne = I32_ne
instrToExecInstr I32_lt_s = I32_lt_s
instrToExecInstr I32_lt_u = I32_lt_u
instrToExecInstr I32_gt_s = I32_gt_s
instrToExecInstr I32_gt_u = I32_gt_u
instrToExecInstr I32_le_s = I32_le_s
instrToExecInstr I32_le_u = I32_le_u
instrToExecInstr I32_ge_s = I32_ge_s
instrToExecInstr I32_ge_u = I32_ge_u
instrToExecInstr Drop = Drop
instrToExecInstr Select = Select
instrToExecInstr (Local_get x)     = (Local_get x)
instrToExecInstr (Local_set x)     = (Local_set x)
instrToExecInstr (Local_tee x)     = (Local_tee x)
instrToExecInstr (Global_get x)    = (Global_get x)
instrToExecInstr (Global_set x)    = (Global_set x)
instrToExecInstr (I32_load x)      = (I32_load x)
instrToExecInstr (I32_store x)     = (I32_store x)
instrToExecInstr (I32_load8_s x)   = I32_load8_s x
instrToExecInstr (I32_load8_u x)   = (I32_load8_u x)
instrToExecInstr (I32_load16_s x)  = (I32_load16_s x)
instrToExecInstr (I32_load16_u x)  = (I32_load16_u x)
instrToExecInstr (I32_store8_s x)  = (I32_store8_s x)
instrToExecInstr (I32_store8_u x)  = (I32_store8_u x)
instrToExecInstr (I32_store16_s x) = (I32_store16_s x)
instrToExecInstr (I32_store16_u x) = (I32_store16_u x)
instrToExecInstr Mem_size = Mem_size
instrToExecInstr Mem_grow = Mem_grow
instrToExecInstr Nop = Nop
instrToExecInstr Unreachable = Unreachable
instrToExecInstr (Block x xs) = (Block x (map instrToExecInstr xs))
instrToExecInstr (Loop x xs) = (Loop x (map instrToExecInstr xs))
instrToExecInstr (If x xs ys) = (If x (map instrToExecInstr xs)
                                      (map instrToExecInstr xs))
instrToExecInstr (Br labIdx) = Br labIdx
instrToExecInstr (BrIf labIdx) =  BrIf labIdx
instrToExecInstr (BrTable labIdxs labIdx) = BrTable labIdxs labIdx
instrToExecInstr Return = Return
instrToExecInstr (FnCall fnIdx) = FnCall fnIdx
instrToExecInstr (FnCall_Indirect tpIdx) = FnCall_Indirect tpIdx

mapInstrs : Expr n -> ExecExpr n
