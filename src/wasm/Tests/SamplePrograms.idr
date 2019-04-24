module SamplePrograms

import Structure.Instr
import Structure.Types

%access export

ifProg1 : Expr
ifProg1 = [Const (I32Val 1), If (Just I32_t) [Const (I32Val 2)] [Const (I32Val 3)]]

ifProg2 : Expr
ifProg2 = [Const (I32Val 1), If Nothing [Const (I32Val 2)] [Const (I32Val 3)]]
