module Validation.AdminValidator

import Structure.Instr
import Structure.Types
import Execution.Runtime

%access public export


TypeStack : Type
TypeStack = List ValType

Labels : Type
Labels = List TypeStack

total
validate : ExecExpr -> TypeStack -> Labels -> Maybe TypeStack
validate [] ts labs = Just ts
validate ((Ins (Const (I32Val _))) :: is) ts labs = validate is (I32_t :: ts) labs
validate ((Ins (Const (I64Val _))) :: is) ts labs = validate is (I64_t :: ts) labs
validate ((Ins (IBinOp _ W32)) :: is) ((IValTp (ITp W32)) :: (IValTp (ITp W32)) :: ts) labs =
    validate is (I32_t :: ts) labs
validate ((Ins (IBinOp _ W64)) :: is) ((IValTp (ITp W64)) :: (IValTp (ITp W64)) :: ts) labs =
    validate is (I64_t :: ts) labs
validate ((Ins (Block res ex)) :: is) ts labs =
    let validated = assert_total $ validate (map Ins ex) [] (res :: labs)
    in case validated of
            Just res => assert_total $ validate is (res ++ ts) labs
            _ => Nothing
validate ((Ins (If res thn els)) :: is) (I32_t :: ts) labs =
    case ( assert_total $ validate (map Ins thn) [] (res :: labs)
         , assert_total $ validate (map Ins els) [] (res :: labs) )  of
        (Nothing, _) => Nothing
        (_, Nothing) => Nothing
        ( Just ts_thn , Just ts_els )  =>
            case decEq ts_thn ts_els of
                No contra => Nothing
                Yes prf => case decEq ts_els res of
                        No contra => Nothing
                        Yes prf => assert_total $ validate is (res ++ ts) labs
validate _ _ _ = Nothing
