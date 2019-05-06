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

push_opd : Maybe ValType -> OpdStack -> OpdStack
push_opd type opd_stack = type :: opd_stack

pop_opd : OpdStack -> CtrlStack -> Maybe (Maybe ValType, OpdStack)
pop_opd opd_stack [] = Nothing
pop_opd opd_stack@(op::rest) ((MkCtrlFrame _ _ height unreachable) :: _) = let l = length opd_stack in
                                                       case (height, unreachable) of
                                                         (l, True) => Just (Nothing, opd_stack)
                                                         (l, False) => Nothing
                                                         _ => Just (op, rest)

pop_opd_expect : Maybe ValType -> OpdStack -> CtrlStack -> Maybe (Maybe ValType, OpdStack)
pop_opd_expect expect opd_stack ctrl_stack = let actual = pop_opd opd_stack ctrl_stack in
                         case (actual, expect) of
                           (Just (Nothing, ret_opd_stack), _) => Just (expect, ret_opd_stack)
                           (Just (real_actual, ret_opd_stack), Nothing) => Just (real_actual, ret_opd_stack)
                           (Just (real_actual, ret_opd_stack), _) => if real_actual /= expect
                                                                       then Nothing
                                                                       else actual
                           _ => Nothing

-- maybe valtype??
push_opds : List ValType -> OpdStack -> OpdStack
push_opds [] opd_stack = opd_stack
push_opds (h :: t) opd_stack = let new_stack = push_opd (Just h) opd_stack in
                               push_opds t new_stack

-- list is NOT already reversed
pop_opds : List ValType -> OpdStack -> CtrlStack -> Maybe OpdStack
pop_opds [] opd_stack _ = Just opd_stack
pop_opds vtypes opd_stack ctrl_stack = let (h :: tail) = (reverse vtypes) in
                                       case (pop_opd_expect (Just h) opd_stack ctrl_stack) of
                                         Just (_, new_opd_stack) => pop_opds (reverse tail) new_opd_stack ctrl_stack
                                         _ => Nothing

push_ctrl : List ValType -> List ValType -> OpdStack -> CtrlStack -> CtrlStack
push_ctrl label out opd_stack ctrl_stack = let frame = MkCtrlFrame label out (length opd_stack) False in
                                           frame :: ctrl_stack

pop_ctrl : OpdStack -> CtrlStack -> Maybe (List ValType, OpdStack, CtrlStack)
pop_ctrl _ [] = Nothing
pop_ctrl opd_stack ctrl_stack@((MkCtrlFrame _ end_types height _) :: rest_ctrl_stack) =
          case (pop_opds end_types opd_stack ctrl_stack) of
            Just new_opd_stack => if length new_opd_stack /= height
                                  then Nothing
                                  else Just (end_types, new_opd_stack, rest_ctrl_stack)
            _ => Nothing

-- resizes from top of stack
resize : List a -> Nat -> Maybe (List a)
resize l Z = Just l
resize [] _ = Nothing
resize l@(h :: t) (S n) = case (compare (length l) (S n)) of
               EQ => Just []
               LT => Nothing
               GT => resize t n

unreachable : OpdStack -> CtrlStack -> Maybe (OpdStack, CtrlStack)
unreachable opd_stack ((MkCtrlFrame l e height _) :: rest_ctrl_stack) =
  case (resize opd_stack height) of
    Just new_opd_stack => Just (new_opd_stack, (MkCtrlFrame l e height True) :: rest_ctrl_stack)
    _ => Nothing


validate : Instr -> OpdStack -> CtrlStack -> Maybe (OpdStack, CtrlStack)
validate (IBinOp op w) opd_stack ctrl_stack =
          case (op, w) of
            -- i32 add
            (IAdd, W32) => let result1 = pop_opd_expect (Just (IValTp (ITp W32))) opd_stack ctrl_stack in
            -- result of 1st pop
              case result1 of
                Just ((Just (IValTp (ITp W32))), new_opd_stack1) => -- first pop successful
                  let result2 = pop_opd_expect (Just (IValTp (ITp W32))) new_opd_stack1 ctrl_stack in
                  -- result of 2nd pop
                  case result2 of
                    Just ((Just (IValTp (ITp W32))), new_opd_stack2) => -- second pop successful, now push
                      Just (push_opd (Just (IValTp (ITp W32))) new_opd_stack2, ctrl_stack)
                    _ => Nothing -- error
                _ => Nothing -- error
            _ => Nothing -- not implemented
validate (Const (I32Val _)) opd_stack ctrl_stack = Just (push_opd (Just (IValTp (ITp W32))) opd_stack, ctrl_stack)
validate (Const (I64Val _)) opd_stack ctrl_stack = Just (push_opd (Just (IValTp (ITp W64))) opd_stack, ctrl_stack)
validate (Const (F32Val _)) opd_stack ctrl_stack = Just (push_opd (Just (FValTp (FTp W32))) opd_stack, ctrl_stack)
validate (Const (F64Val _)) opd_stack ctrl_stack = Just (push_opd (Just (FValTp (FTp W64))) opd_stack, ctrl_stack)
validate Unreachable opd_stack ctrl_stack = unreachable opd_stack ctrl_stack
validate (Block result_type expr) opd_stack ctrl_stack = ?rhs1
validate (Loop result_type expr) opd_stack ctrl_stack = ?rhs2
validate (If result_type expr instr_list) opd_stack ctrl_stack = ?rhs3
