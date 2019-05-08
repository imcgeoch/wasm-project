module ListUtil

%access export

||| Update list at a particular location
updateAt : List a -> Nat -> a -> Maybe (List a)
updateAt [] k x = Nothing
updateAt (y :: xs) Z x = Just $ x :: xs
updateAt (y :: xs) (S k) x = (updateAt xs k x) >>= (\res => Just (y :: res))

||| Update a list, xs, starting at index k by replacing each value with ys
||| If there isn't room in xs, return Nothing
|||
||| Example: updateWithSpliceAt [0,1,2,3,4,5] 2 [0,0] will yield [0,1,0,0,4,5]
updateWithSpliceAt : List a -> Nat -> List a -> Maybe (List a)
updateWithSpliceAt xs k [] = Just xs
updateWithSpliceAt [] k (x :: ys) = Nothing
updateWithSpliceAt (x :: xs) Z (y :: ys) = (updateWithSpliceAt xs Z ys) >>= (\zs => Just (y :: zs))
updateWithSpliceAt (x :: xs) (S k) (y :: ys) = (updateWithSpliceAt xs k (y :: ys)) >>= (\zs => Just (x :: zs))
