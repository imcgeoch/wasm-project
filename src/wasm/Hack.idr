bar : Nat -> Type
bar n = (case n of
             Z => Z
             S m => Z) = Z

foo : Nat -> ()
foo n = let x : bar n = ?rhs -- type of x : (Z = Z)
        in ?blah

