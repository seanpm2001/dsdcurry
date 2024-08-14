-- Solving the n-queens problem

import Data.List
import Control.SetFunctions

-- Specification: queens are represented by a list of their (x,y)-positions
-- and we directly specify all the "non-capture" conditions

queens'pre :: Int -> Bool
queens'pre n = (n>0)

-- We provide a trivial user-defined postcondition in order to use
-- the postcondition in this program.
queens'post :: Int -> [(Int,Int)] -> Bool
queens'post _ _ = True

queens'spec :: Int -> [(Int,Int)]
queens'spec n 
  | all onboard qs && capture (allpairs qs) =:= False
  = qs
 where
  qs = map (\_->unknown) [1..n] -- create a list of unknown values

  onboard (x,y) = x `isIn` [1..n] & y `isIn` [1..n]
    where u `isIn` (_++[v]++_) = u =:= v -- is-element constraint

  -- Compute all distinct pairs of queens
  allpairs []     = []
  allpairs (x:xs) = map (\y -> (x,y)) xs ++ allpairs xs

  -- A placement is bad if two queens capture each other, i.e.,
  -- they are on a same horizontal, vertical or diagonal line
  capture [] = False
  capture (((x1,y1),(x2,y2)):rest) =
    x1==x2 || y1==y2 || abs(x1-x2)==abs(y1-y2) || capture rest

-- from this, the system should generate the postcondition:
-- queens'post n qs = contains qs (set1 queens'spec n)

-------------------------------------------------------------------------------
-- If one applies the transformation tool to this program,
-- one obtains an implementation of queens.
-- However, it is quite slow due to the generation of many permutations
-- of the same solution, like
--
-- Result: [(1,2),(2,4),(3,1),(4,3)]
-- Result: [(1,2),(2,4),(4,3),(3,1)]
-- Result: [(1,2),(3,1),(2,4),(4,3)]
-- ...
--
-- In order to get a more efficient solution, we can choose another
-- representation of placements where the queen at row x is the x-th element
-- of a list containing only the y-coordinate of this queen.
-- Thus, horizontal captures need not be checked in this presentation.
-- Moreover, we can avoid vertical capture checking by computing
-- permutations of the list [1..n]. Thus, we only have to check
-- diagonal captures. The resulting program is:

perm [] = []
perm (x:xs) = ndinsert x (perm xs)

ndinsert x ys     = x : ys
ndinsert x (y:ys) = y : ndinsert x ys


fqueens n | isEmpty ((set1 unsafe) p) = p
 where p = perm [1..n]

unsafe (_++[x]++y++[z]++_) = abs (x-z) =:= length y + 1


--> Example call:
--> fqueens 6

-- In order to use the postcondition of our initial program,
-- we have to map the new efficient (concrete) representation
-- into the original (abstract) representation (this can be also
-- considered as the semantics of the concrete representation):

conc2abstr :: [Int] -> [(Int,Int)]
conc2abstr qs = zip [1..] qs

-- Now we can define a postcondition of our more efficient queens
-- algorithm by mapping the result into the original postcondition:

fqueens'post n qs = queens'post n (conc2abstr qs)

-- Similarly, we reuse the precondition:

fqueens'pre n = queens'pre n

-- This solution remains efficient since checking the postcondition
-- could be faster than using it to enumerate solutions.
-- However, this remains on the implementation of set functions
-- used in the generated postcondition. In a strict implementation
-- like in PAKCS it is still slow, but in a lazy implementation
-- it should be much better.

