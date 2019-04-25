module Structure.Indices

import Data.Bits

-- Definitions from https://webassembly.github.io/spec/core/syntax/modules.html#syntax-localidx
%access public export

TypeIdx : Type
TypeIdx = Bits32

FuncIdx : Type
FuncIdx = Bits32

TableIdx : Type
TableIdx = Bits32

MemIdx : Type
MemIdx = Bits32

GlobalIdx : Type
GlobalIdx = Bits32

LocalIdx : Type
LocalIdx = Bits32

LabelIdx : Type
LabelIdx = Nat
