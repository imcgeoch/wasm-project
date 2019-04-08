module BitUtil

import Data.Bits
import Data.Fin

%access public export
%default total

clz : Bits (S k) -> Nat
clz {k} bits = let lastFin : Fin (S k) = last in
                   case getBit lastFin bits of
                        False => ?clz_rhs_1
                        True => (S k) `minus` (the Nat (cast lastFin))

ctz' : (bits : Bits (S k)) -> Fin (S k) -> Nat
ctz' {k} bits fin = case getBit fin bits of
                     True  => cast fin                          -- Found a 1
                     False => (let val = the Nat (cast fin) in  -- Found a 0
                               let val' : Maybe (Fin (S k)) = natToFin (S val) (S k) in
                                  (case val' of
                                        Nothing => (S k)
                                        (Just fin') => ctz' bits fin'))

ctz : Bits (S k) -> Nat
ctz {k} bits = ctz' bits (the (Fin (S k)) FZ)

