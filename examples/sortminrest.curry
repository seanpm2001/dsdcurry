-- straight selection sort with specification
import Control.SetFunctions

perm []     = []
perm (x:xs) = insert (perm xs)
 where insert ys     = x:ys
       insert (y:ys) = y : insert ys

sorted [] = True
sorted [_] = True
sorted (x:y:ys) = x<=y && sorted (y:ys)

-- Contract of sort:
sort'pre _ = True
sort'post xs ys = length xs == length ys

-- Specification of sort:
sort'spec :: [Int] -> [Int]
sort'spec x | y =:= perm x & sorted y = y  where y free

-- Implementation of sort as minsort:
sort :: [Int] -> [Int]
sort [] = []
sort (x:xs) = min : sort rest
  where (min,rest) = minRest (x:xs)

-- Contract of minRest:
-- Precondition: the argument must be a non-empty list
minRest'pre = not . null
-- Postcondition: the result is a pair of the minimum and the remaining
-- elements that must be some permutation of the input list
minRest'post :: [Int] -> (Int,[Int]) -> Bool
minRest'post xs (min,rest) =
  (min:rest) `valueOf` (set1 perm xs) && all (>= min) xs

-- Implementations of minRest:
minRest :: [Int] -> (Int,[Int])
minRest xs = minRest2 xs

-- Implementation 1: Find the minimum and then delete it in the list:
minRest1 (x:xs) = let m = min x xs in (m, del m (x:xs))
 where
   min z [] = z
   min z (y:ys) = if z <= y then min z ys else min y ys

   del z (y:ys) = if z == y then ys else y : del z ys

-- Implementation 2: Find minimum and delete it in one pass:
minRest2 (x:xs) = mr x [] xs
 where mr m r [] = (m,r)
       mr m r (y:ys) = if m <= y then mr m (y:r) ys else mr y (m:r) ys

main = sort [26,18,5,4,16,8,22,17]
