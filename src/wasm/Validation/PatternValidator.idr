module Validation.PatternValidator

import Structure.Instr
import Structure.Types

%access public export

validate: Expr -> List ValType -> Maybe (List ValType)
validate [] ts = Just ts
validate ((Const (I32Val _)) :: rest) ts = validate rest (I32_t :: ts)
validate ((Const (I64Val _)) :: rest) ts = validate rest (I64_t :: ts)
validate ((Const (F32Val _)) :: rest) ts = validate rest (F32_t :: ts)
validate ((Const (F64Val _)) :: rest) ts = validate rest (F64_t :: ts)
validate ((IBinOp IAdd W32) :: rest) (I32_t :: I32_t :: ts) = validate rest (I32_t :: ts)
validate _ _ = Nothing
