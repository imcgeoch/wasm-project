module Validation.PatternValidator

import Structure.Instr
import Structure.Types

%access public export

validate: Expr -> List ValType -> Maybe (List ValType)
validate [] ts = Just ts
validate ((Const (I32Val _)) :: is) ts = validate is (I32_t :: ts)
validate ((Const (I64Val _)) :: is) ts = validate is (I64_t :: ts)
validate ((Const (F32Val _)) :: is) ts = validate is (F32_t :: ts)
validate ((Const (F64Val _)) :: is) ts = validate is (F64_t :: ts)
validate ((IBinOp IAdd W32) :: is) (I32_t :: I32_t :: ts) = validate is (I32_t :: ts)
validate ((If res thn els) :: is) (I32_t :: ts) =
    let thn_valid = validate thn []
        els_valid = validate els []
    in case (thn_valid, els_valid) of
            (Just res, Just res) => Just ts
            (_, _) => Nothing
validate ((Block res ex) :: is) [] =
    case validate ex [] of
        Just res => Just res
        _ => Nothing
validate _ _ = Nothing
