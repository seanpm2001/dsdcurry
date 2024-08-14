-- A specification of sorting a list

perm []     = []
perm (x:xs) = insert (perm xs)
 where insert ys     = x:ys
       insert (y:ys) = y : insert ys

sorted []       = True
sorted [_]      = True
sorted (x:y:ys) = x<=y && sorted (y:ys)

-- Postcondition: input and output lists should have the same length
sort'post xs ys = length xs == length ys

-- Specification of sort:
-- A list is a sorted result of an input if it is a permutation and sorted.
sort'spec :: [Int] -> [Int]
sort'spec x | y =:= perm x & sorted y = y  where y free

-- We do not provide an implementation yet:
sort :: [Int] -> [Int]
sort _ = unknown

input = [26,18,5,4,16,8,22,17]
