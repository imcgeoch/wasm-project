module Validation.AdminValidator

import Structure.Instr
import Structure.Types
import Execution.Runtime

%access public export


TypeStack : Type
TypeStack = List ValType

Labels : Type
Labels = List TypeStack

validate: ExecExpr -> TypeStack -> Labels -> Maybe TypeStack
validate _ _ _ = Nothing
