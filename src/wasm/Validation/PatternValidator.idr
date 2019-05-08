module Validation.PatternValidator

import Structure.Instr
import Structure.Types

%access public export

Labels : Type
Labels = List ValType

TypeStack : Type
TypeStack = List ValType


validate: Expr -> TypeStack -> Labels -> Maybe (TypeStack, Labels)
validate [] ts labs = Just (ts, labs)
validate ((Const (I32Val _)) :: is) ts labs = validate is (I32_t :: ts) labs
validate ((Const (I64Val _)) :: is) ts labs = validate is (I64_t :: ts) labs
-- validate ((Const (F32Val _)) :: is) ts labs = validate is (F32_t :: ts) labs
-- validate ((Const (F64Val _)) :: is) ts labs = validate is (F64_t :: ts) labs
validate ((IBinOp _ W32) :: is) ((IValTp (ITp W32)) :: (IValTp (ITp W32)) :: ts) labs =
    validate is (I32_t :: ts) labs
validate ((IBinOp _ W64) :: is) ((IValTp (ITp W64)) :: (IValTp (ITp W64)) :: ts) labs =
    validate is (I64_t :: ts) labs
validate ((Block res ex) :: is) ts labs =
    case validate ex [] (res ++ labs) of
        -- Do we agree the following line is correct?
        Just (res, _) => validate is (res ++ ts) labs
        _ => Nothing
validate ((If res thn els) :: is) (I32_t :: ts) labs =
    case ( validate thn [] (res ++ labs), validate els [] (res ++ labs) )  of
        (Nothing, _) => Nothing
        (_, Nothing) => Nothing
        ( Just (ts_thn, _), Just (ts_els, _) )  =>
            case decEq ts_thn ts_els of
                No contra => Nothing
                Yes prf => case decEq ts_thn res of
                        No contra => Nothing
                        -- Do we agree the following line is correct?
                        Yes prf => validate is (res ++ ts) labs
validate (Nop :: is) ts labs = validate is ts labs
validate _ _ _ = Nothing
