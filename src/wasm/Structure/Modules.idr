module Modules

import Structure.Indices
import Structure.Instructions
import Structure.Types

import Data.Vect

%access public export

-- Definitions from https://webassembly.github.io/spec/core/syntax/modules.html
namespace modules
    mutual
        ||| Define the Module type.
        |||
        ||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#syntax-module
        record Module where
            constructor MkModule
            types   : Vect n FuncType
            funcs   : Vect n Func
            tables  : Vect n Table
            mems    : Vect n Mem
            globals : Vect n Global
            elem    : Vect n Elem
            datums  : Vect n Data
            start   : Maybe Start
            imports : Vect n Import
            exports : Vect n Export


        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-start
        record Start where
            constructor MkStart
            func : FuncIdx

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-func
        record Func where
            constructor MkFunc
            type   : TypeIdx
            locals : Vect n ValType
            body   : Expr

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-table
        record Table where
            constructor MkTable
            type : TableType

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-mem
        record Mem where
            constructor MkMem
            type : MemType

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-global
        data Global : Type where

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-elem
        record Elem where
            constructor MkElem
            table  : TableIdx
            offset : Expr     -- XXX: ConstExpr
            init   : Vect n FuncIdx

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-data
        record Data where
            constructor MkData
            datums : MemIdx  -- XXX: Currently, only valid MemIdx is 0 (see note
                             --      at above link for more info)
            offset : Expr    -- XXX: ConstExpr
            init   : Vect n Bits8

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-import
        record Import where
            constructor MkImport
            modul : String
            name  : String
            desc  : ImportDesc

        record ImportDesc where
            constructor MkImportDesc
            func   : TypeIdx
            table  : TableType
            mem    : MemType
            global : GlobalType

        ||| https://webassembly.github.io/spec/core/syntax/modules.html#syntax-export
        record Export where
            constructor MkExport
            name : String
            desc : ExportDesc

        record ExportDesc where
            constructor MkExportDesc
            func   : FuncIdx
            table  : TableIdx
            mem    : MemIdx
            global : GlobalIdx
