module Validation.JankValidator

import Structure.Instr
import Structure.Types

%access public export

OpdStack : Type
OpdStack = List (Maybe ValType)

record CtrlFrame where
  constructor MkCtrlFrame
  label_types : List ValType
  end_types : List ValType
  height : Nat
  unreachable : Bool

CtrlStack : Type
CtrlStack = List CtrlFrame

data ErrorStatus : Type where
  ValidatorError : String -> ErrorStatus  -- validator returns and ERROR
  InternalError : String -> ErrorStatus

push_opd : Maybe ValType -> OpdStack -> OpdStack
push_opd type opd_stack = type :: opd_stack

pop_opd : OpdStack -> CtrlStack -> Either (Maybe ValType, OpdStack) ErrorStatus
pop_opd opd_stack [] = Right (InternalError "pop with empty ctrl stack")
pop_opd opd_stack@(op::rest) ((MkCtrlFrame _ _ height unreachable) :: _) = let l = length opd_stack in
                                                       case (height, unreachable) of
                                                         (l, True) => Left (Nothing, opd_stack)
                                                         (l, False) => Right (ValidatorError "pop helper not valid")
                                                         _ => Left (op, rest)

pop_opd_expect : Maybe ValType -> OpdStack -> CtrlStack -> Either (Maybe ValType, OpdStack) ErrorStatus
pop_opd_expect expect opd_stack ctrl_stack = let actual = pop_opd opd_stack ctrl_stack in
                         case (actual, expect) of
                           (Left (Nothing, ret_opd_stack), _) => Left (expect, ret_opd_stack)
                           (Left (real_actual, ret_opd_stack), Nothing) => Left (real_actual, ret_opd_stack)
                           (Left (real_actual, ret_opd_stack), _) => if real_actual /= expect
                                                                       then Right (ValidatorError "pop not valid")
                                                                       else actual
                           _ => Right (InternalError "pop internal error")

-- maybe valtype??
push_opds : List ValType -> OpdStack -> OpdStack
push_opds [] opd_stack = opd_stack
push_opds (h :: t) opd_stack = let new_stack = push_opd (Just h) opd_stack in
                               push_opds t new_stack

-- list is NOT already reversed
pop_opds : List ValType -> OpdStack -> CtrlStack -> Either OpdStack ErrorStatus
pop_opds [] opd_stack _ = Left opd_stack
pop_opds vtypes opd_stack ctrl_stack = let (h :: tail) = (reverse vtypes) in
                                       case (pop_opd_expect (Just h) opd_stack ctrl_stack) of
                                         Left (_, new_opd_stack) => pop_opds (reverse tail) new_opd_stack ctrl_stack
                                         Right (InternalError _) => Right (InternalError "multi pop internal error")
                                         Right (ValidatorError _) => Right (ValidatorError "multi pop validator error")

push_ctrl : List ValType -> List ValType -> OpdStack -> CtrlStack -> CtrlStack
push_ctrl label out opd_stack ctrl_stack = let frame = MkCtrlFrame label out (length opd_stack) False in
                                           frame :: ctrl_stack

pop_ctrl : OpdStack -> CtrlStack -> Either (List ValType, OpdStack, CtrlStack) ErrorStatus
pop_ctrl _ [] = Right (ValidatorError "empty ctrl stack")
pop_ctrl opd_stack ctrl_stack@((MkCtrlFrame _ end_types height _) :: rest_ctrl_stack) =
          case (pop_opds end_types opd_stack ctrl_stack) of
            Left new_opd_stack => if length new_opd_stack /= height
                                  then Right (ValidatorError "pop ctrl underflow")
                                  else Left (end_types, new_opd_stack, rest_ctrl_stack)
            Right (InternalError _) => Right (InternalError "pop ctrl internal error")
            Right (ValidatorError _) => Right (ValidatorError "pop ctrl validator error")

-- resizes from top of stack
resize : List a -> Nat -> Either (List a) ErrorStatus
resize l Z = Left l
resize [] _ = Right (InternalError "resize error")
resize l@(h :: t) (S n) = case (compare (length l) (S n)) of
               EQ => Left []
               LT => Right (InternalError "resize error")
               GT => resize t n

unreachable : OpdStack -> CtrlStack -> Either (OpdStack, CtrlStack) ErrorStatus
unreachable opd_stack ((MkCtrlFrame l e height _) :: rest_ctrl_stack) =
  case (resize opd_stack height) of
    Left new_opd_stack => Left (new_opd_stack, (MkCtrlFrame l e height True) :: rest_ctrl_stack)
    _ => Right (InternalError "unreachable error")
