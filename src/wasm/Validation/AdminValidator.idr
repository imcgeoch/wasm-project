module Validation.AdminValidator

import Structure.Instr
import Structure.Types
import Execution.Runtime

%access public export
%default total

TypeStack : Type
TypeStack = List ValType

Labels : Type
Labels = List TypeStack

mutual
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
        in case_wrap_1 validated
        where
            -- Wraps case validated of ...
            case_wrap_1 : Maybe TypeStack -> Maybe TypeStack
            case_wrap_1 Nothing = Nothing
            case_wrap_1 (Just ret_stack) = case_wrap_2 (decEq ret_stack res)
            where
                -- Wraps case (decEq ret_stack res) of ...
                case_wrap_2 : Dec (ret_stack = res) -> Maybe TypeStack
                case_wrap_2 (No contra) = Nothing
                case_wrap_2 (Yes prf) = assert_total $ validate is (res ++ ts) labs
    validate ((Ins (If res thn els)) :: is) (I32_t :: ts) labs =
        case_wrap_1 ( assert_total $ validate (map Ins thn) [] (res :: labs)
                    , assert_total $ validate (map Ins els) [] (res :: labs) )
        where
            -- Wraps case (validate thn, validate els) of ...
            case_wrap_1 : (Maybe TypeStack, Maybe TypeStack) -> Maybe TypeStack
            case_wrap_1 (Nothing, _) = Nothing
            case_wrap_1 (_, Nothing) = Nothing
            case_wrap_1 (Just ts_thn, Just ts_els) = case_wrap_2 (decEq ts_thn ts_els)
            where
                -- Wraps case (decEq thn els) of ...
                case_wrap_2 : Dec (ts_thn = ts_els) -> Maybe TypeStack
                case_wrap_2 (No contra) = Nothing
                case_wrap_2 (Yes prf) = case_wrap_3 (decEq ts_els res)
                where
                    -- Wraps case (decEq els res) of ...
                    case_wrap_3 : Dec (ts_els = res) -> Maybe TypeStack
                    case_wrap_3 (No contra) = Nothing
                    case_wrap_3 (Yes prf) = assert_total $ validate is (res ++ ts) labs
    validate ((Ins Nop) :: is) ts labs = validate is ts labs
    validate _ _ _ = Nothing

    -- validate_label : Nat -> ExecExpr -> ExecExpr -> List (Maybe ValType) -> (List (Maybe ValType), List (Maybe ValType))
    -- validate_label k cont is dom = ([], [])