module BitUtil

import Data.Bits
import Data.Fin

%access public export
%default total

natToBits32 : Nat -> Bits32
natToBits32 n = prim__zextInt_B32 $ toIntNat n

clz' : List Char -> Nat
clz' xs = length $ takeWhile (\c => c == '0') xs

clz32 : Bits32 -> Bits32
clz32 x = let chars = unpack $ b32ToBinString x in
              natToBits32 $ clz' chars

clz64 : Bits64 ->  Bits32
clz64 x = let chars = unpack $ b64ToBinString x in
              natToBits32 (clz' chars)

ctz32 : Bits32 ->  Bits32
ctz32 x = natToBits32 (clz' $ reverse (unpack $ b32ToBinString x))

ctz64 : Bits64 ->  Bits32
ctz64 x = natToBits32 (clz' $ reverse (unpack $ b64ToBinString x))

countOnes' : List Char -> Nat
countOnes' xs = length $ filter (\x => x == '1') xs

countOnes32 : Bits32 -> Bits32
countOnes32 x = natToBits32 (countOnes' (unpack $ b32ToBinString x))

countOnes64 : Bits64 -> Bits32
countOnes64 x = natToBits32 (countOnes' (unpack $ b64ToBinString x))

bytesToB32 : List Bits8 -> Bits32
bytesToB32 xs = foldl (\acc, elem => prim__addB32 (prim__shlB32 acc 8) (prim__zextB8_B32 elem)) 0 xs

bytesToB64 : List Bits8 -> Bits64
bytesToB64 xs = foldl (\acc, elem => prim__addB64 (prim__shlB64 acc 16) (prim__zextB8_B64 elem)) 0 xs
