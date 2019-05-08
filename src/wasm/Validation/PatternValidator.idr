module Validation.PatternValidator

import Structure.Instr
import Structure.Types

%access public export

validate: Expr -> List ValType -> Maybe (List ValType)
validate [] ts = Just ts
validate ((Const (I32Val _)) :: is) ts = validate is (I32_t :: ts)
validate ((Const (I64Val _)) :: is) ts = validate is (I64_t :: ts)
-- validate ((Const (F32Val _)) :: is) ts = validate is (F32_t :: ts)
-- validate ((Const (F64Val _)) :: is) ts = validate is (F64_t :: ts)
validate ((IBinOp _ W32) :: is) ((IValTp (ITp W32)) :: (IValTp (ITp W32)) :: ts) =
    validate is (I32_t :: ts)
validate ((IBinOp _ W64) :: is) ((IValTp (ITp W64)) :: (IValTp (ITp W64)) :: ts) =
    validate is (I64_t :: ts)
validate ((If res thn els) :: is) (I32_t :: ts) =
    case (validate thn [], validate els []) of
        (Nothing, _) => Nothing
        (_, Nothing) => Nothing
        (Just ts_thn, Just ts_els) =>
            case decEq ts_thn ts_els of
                No contra => Nothing
                Yes prf => case decEq ts_thn res of
                        No contra => Nothing
                        Yes prf => validate is (res ++ ts)
validate ((Block res ex) :: is) ts =
    case validate ex [] of
        Just res => validate is (res ++ ts)
        _ => Nothing
validate (Nop :: is) ts = validate is ts
validate _ _ = Nothing
