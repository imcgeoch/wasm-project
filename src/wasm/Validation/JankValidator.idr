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

pop_opd : OpdStack -> CtrlStack -> Maybe (Maybe ValType ,OpdStack)
pop_opd opd_stack [] = Nothing
pop_opd (top :: rest) ((MkCtrlFrame _ _ h unreachable) :: _) =
    let will_underflow = length (top :: rest) == h in
        case (will_underflow, unreachable) of
            (True, True) => Just (Nothing, top :: rest)
            (True, _) => Nothing
            _ => Just (top, rest)

pop_opd_expect : Maybe ValType -> OpdStack -> CtrlStack -> Maybe (Maybe ValType, OpdStack)
pop_opd_expect expect opd_stack ctrl_stack = let actual = pop_opd opd_stack ctrl_stack in
                         case (actual, expect) of
                           (Just (Nothing, ret_opd_stack), _) => Just (expect, ret_opd_stack)
                           (Just (popped_type, ret_opd_stack), Nothing) => Just (popped_type, ret_opd_stack)
                           (Just (popped_type, ret_opd_stack), _) => if popped_type /= expect
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


validate_op : Instr -> OpdStack -> CtrlStack -> Maybe (OpdStack, CtrlStack)
validate_op (IBinOp op w) opd_stack ctrl_stack =
          case (op, w) of
            -- i32 add
            (IAdd, W32) => do
              (_, opd_stack1) <- pop_opd_expect (Just I32_t) opd_stack ctrl_stack
              (_, opd_stack2) <- pop_opd_expect (Just I32_t) opd_stack1 ctrl_stack
              let opd_stack3 = push_opd (Just I32_t) opd_stack2
              Just (opd_stack3, ctrl_stack)
            _ => Nothing -- not implemented

validate_op Drop opd_stack ctrl_stack =
  do (_, opd_stack1) <- pop_opd opd_stack ctrl_stack
     Just (opd_stack1, ctrl_stack)

validate_op Select opd_stack ctrl_stack =
  do (_, opd_stack1) <- pop_opd_expect (Just I32_t) opd_stack ctrl_stack
     (t1, opd_stack2) <- pop_opd opd_stack1 ctrl_stack
     (t2, opd_stack3) <- pop_opd_expect t1 opd_stack2 ctrl_stack
     let opd_stack4 = push_opd t2 opd_stack3
     Just (opd_stack4, ctrl_stack)


validate_op (Const (I32Val _)) opd_stack ctrl_stack = Just (push_opd (Just I32_t) opd_stack, ctrl_stack)
validate_op (Const (I64Val _)) opd_stack ctrl_stack = Just (push_opd (Just I64_t) opd_stack, ctrl_stack)
validate_op (Const (F32Val _)) opd_stack ctrl_stack = Just (push_opd (Just F32_t) opd_stack, ctrl_stack)
validate_op (Const (F64Val _)) opd_stack ctrl_stack = Just (push_opd (Just F64_t) opd_stack, ctrl_stack)

validate_op Unreachable opd_stack ctrl_stack = unreachable opd_stack ctrl_stack

validate_op (Block result_type expr) opd_stack ctrl_stack =
  let ts = case result_type of
              Just v => [v]
              Nothing => []
  in Just (opd_stack, push_ctrl ts ts opd_stack ctrl_stack)

validate_op (Loop result_type expr) opd_stack ctrl_stack =
  let ts = case result_type of
              Just v => [v]
              Nothing => []
  in Just (opd_stack, push_ctrl [] ts opd_stack ctrl_stack)

-- when I tried to write If the same way as Loop, I got weird type inference errors???
-- validate_op (If result_type expr instr_list) opd_stack ctrl_stack =
  -- let ts = case result_type of
  --             Just v => [v]
  --             Nothing => []
  -- in do (_, opd_stack1) <- pop_opd_expect (Just I32_t) opd_stack ctrl_stack
  --       Just (opd_stack1, push_ctrl ts ts opd_stack1 ctrl_stack)

-- But this version, which I expected to be equivalent to the commented one, compiles fine
validate_op (If result_type expr instr_list) opd_stack ctrl_stack =
  case result_type of
    Just v => do
        (_, opd_stack1) <- pop_opd_expect (Just I32_t) opd_stack ctrl_stack
        Just (opd_stack1, push_ctrl [v] [v] opd_stack1 ctrl_stack)
    Nothing => do
        (_, opd_stack1) <- pop_opd_expect (Just I32_t) opd_stack ctrl_stack
        Just (opd_stack1, push_ctrl [] [] opd_stack1 ctrl_stack)


validate : List Instr -> OpdStack -> CtrlStack -> Maybe (OpdStack, CtrlStack)
validate [] opd_stack ctrl_stack = Just (opd_stack, ctrl_stack)
validate (instr::rest) opd_stack ctrl_stack =
  do (opd_stack1, ctrl_stack1) <- validate_op instr opd_stack ctrl_stack
     (opd_stack2, ctrl_stack2) <- validate rest opd_stack1 ctrl_stack1
     Just (opd_stack2, ctrl_stack2)


Show CtrlFrame where
    show (MkCtrlFrame labels ends h unreach) = "Control frame {"
                                                ++ "label types: " ++ (show labels) ++ ", "
                                                ++ "end types: " ++ (show ends) ++ ", "
                                                ++ "height: " ++ (show h) ++ ", "
                                                ++ "unreachable: " ++ (show unreach)
                                                ++ "} End Control Frame"