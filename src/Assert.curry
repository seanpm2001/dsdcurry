------------------------------------------------------------------------
-- Auxiliaries for assertion checking w.r.t. pre/postconditions.
------------------------------------------------------------------------

module Assert(Assert,makeAssert,waitOf,ddunifOf,
              aInt,aFloat,aChar,aBool,aOrdering,aSuccess,
              aList,aString,aUnit,aPair,aTriple,aTuple4,aMaybe,aEither,
              aPolyType,
              enforce, enforceIO, enforceAssertions,
              AssertKind(..),
              withContract1, withContract2,
              withPreContract1, withPreContract2, withPostContract0,
              withPostContract1, withPostContract2,
              someValueOf1, someValueOf2
             )  where

import AssertParam
import Control.Search.SetFunctions
import Control.SearchTree  ( isDefined )
import Control.Applicative ( when )
import System.IO
import System.IO.Unsafe    ( unsafePerformIO, spawnConstraint, showAnyTerm )
import System.Environment  ( getEnv )
import GlobalVariable      ( GVar, gvar, readGVar, writeGVar )

--- Auxiliaries for pre/postcondition checking

--- The different kinds of assertion.
data AssertKind = Strict | Lazy | Enforceable

-- Should we show additional information about assertions?
debug :: Bool
debug = unsafePerformIO getDebugVar

getDebugVar :: IO Bool
getDebugVar = do
  v <- getEnv "ASSERTDEBUG"
  return (v=="yes")

---------------------------------------------------------------------------
--- The main operation for enforceable assertions.
--- (enforce e) evaluates the expression e (with assertions)
--- so that unevaluated assertions are enforced before returning the result.
enforce :: Data a => a -> a
enforce exp | (unsafePerformIO initAssertionQueue =:= ())
              &> exp=:=exp
            = (unsafePerformIO enforceAssertions =:= ())
              &> exp

--- Evaluate an I/O action with enforceable assertions.
--- (enforceIO a) evaluates the I/O action a (with assertions)
--- so that unevaluated assertions are enforced after performing action a.
enforceIO :: IO () -> IO ()
enforceIO a = initAssertionQueue >> a >> enforceAssertions

--- Enforce immediate checking of all (delayed) assertions.
enforceAssertions :: IO ()
enforceAssertions = activateAssertions

---------------------------------------------------------------------------
-- Report the result of checking the pre/postconditions.
-- The first argument is a tag (the name of the operation).
-- The second argument is unified with () (used by enforceable constraints).
-- The third argument is a Boolean result that must not be False for
-- a satisfied condition.
-- The fourth argument is a string describing the context (arguments,result).

checkPre :: String -> () -> CheckResult -> String -> Success
checkPre fname eflag result arg = case isViolation result of
  True  -> eflag=:=() &>
           traceLines
             ["Precondition of operation '"++fname++"' violated for:",arg]
             (error "Execution aborted due to contract violation!")
  False -> eflag=:=() &> 
           if debug
           then traceLines ["Precondition of '"++fname++"' satisfied for:",arg]
                           success
           else success

checkPost :: String -> () -> () -> CheckResult -> String -> Success
checkPost fname eflag preflag result arg = case isViolation result of
  True  -> eflag=:=() &>
           traceLines
             ["Postcondition of operation '"++fname++"' violated "++
              (if isVar preflag then "(but precondition unchecked!) " else "")
              ++"for:",arg]
             (error "Execution aborted due to contract violation!")
  False -> eflag=:=() &> 
           if debug
           then traceLines
                  ["Postcondition of '"++fname++"' satisfied for:",arg]
                  success
           else success

-- print some lines of output on stderr with flushing after each line
traceLines :: [String] -> a -> a
traceLines ls e = unsafePerformIO (flushLines ls) `seq` e
 where
  flushLines []     = return ()
  flushLines (x:xs) = hPutStrLn stderr x >> hFlush stderr >> flushLines xs

-- show operation used to show argument or result terms to the user:
-- could be Prelude.show but this suspends if we want to show unevaluated
-- terms, therefore, we use Unsafe.showAnyTerm
showATerm :: _ -> String
showATerm = showAnyTerm

---------------------------------------------------------------------------
-- Combinators for checking of contracts having pre- and postconditions

withContract1 :: (Data a, Data b) => AssertKind -> Assert a -> Assert b -> String
              -> (a -> CheckResult) -> (a -> b -> CheckResult)
              -> (a -> b) -> a -> b

withContract1 Strict _ _ fname precond postcond fun arg
  |  checkPre fname () (precond arg) (showATerm arg)
  &> checkPost fname () () (postcond arg result)
               (unwords [showATerm arg,"->",showATerm result])
  = result
 where result = fun arg

withContract1 Lazy (Assert waita ddunifa) (Assert waitb ddunifb)
              fname precond postcond fun arg =
  spawnConstraint (checkPre fname pref (precond (waita argx)) (showATerm argx)
                   &
                   checkPost fname () pref (postcond (waita argx) (waitb fx))
                             (unwords [showATerm argx,"->",showATerm fx]))
                  (ddunifb fx (fun (ddunifa argx arg)))
 where
  argx, fx, pref free

withContract1 Enforceable (Assert waita ddunifa) (Assert waitb ddunifb)
              fname precond postcond fun arg
  | registerAssertion ef1 fname "Pre"
                      (checkPre fname ef1 (precond arg) (showATerm arg))
  & registerAssertion ef2 fname "Post"
      (let res = fun arg
        in checkPost fname () ef1 (postcond arg res)
                     (unwords [showATerm arg,"->",showATerm res]))
  = spawnConstraint (checkPre fname ef1 (precond (waita argx)) (showATerm argx)
                     & 
                     checkPost fname ef2 ef1 (postcond (waita argx) (waitb fx))
                               (unwords [showATerm argx,"->",showATerm fx]))
                    (ddunifb fx (fun (ddunifa argx arg)))
 where
  argx,fx,ef1,ef2 free


withContract2 :: (Data a, Data b, Data c) => AssertKind -> Assert a -> Assert b -> Assert c -> String
              -> (a -> b -> CheckResult) -> (a -> b -> c -> CheckResult)
              -> (a -> b -> c) -> a -> b -> c

withContract2 Strict _ _ _ fname precond postcond fun arg1 arg2
  |  checkPre fname () (precond arg1 arg2)
                       (unwords [showATerm arg1,showATerm arg2])
  &> checkPost fname () () (postcond arg1 arg2 result)
               (unwords [showATerm arg1,showATerm arg2,"->",showATerm result])
  = result
 where result = fun arg1 arg2

withContract2 Lazy (Assert waita ddunifa) (Assert waitb ddunifb)
              (Assert waitc ddunifc) fname precond postcond fun arg1 arg2 =
  spawnConstraint (checkPre fname pref
                        (precond (waita x1) (waitb x2))
                        (unwords [showATerm x1,showATerm x2])
                   &
                   checkPost fname () pref
                        (postcond (waita x1) (waitb x2) (waitc fx))
                        (unwords [showATerm x1,showATerm x2,"->",showATerm fx]))
                  (ddunifc fx (fun (ddunifa x1 arg1) (ddunifb x2 arg2)))
 where
  x1,x2,fx,pref free

withContract2 Enforceable (Assert waita ddunifa) (Assert waitb ddunifb)
              (Assert waitc ddunifc) fname precond postcond fun arg1 arg2
  | registerAssertion ef1 fname "Pre"
                      (checkPre fname ef1 (precond arg1 arg2)
                                (unwords [showATerm arg1,showATerm arg2]))
  & registerAssertion ef2 fname "Post"
      (let res = fun arg1 arg2
        in checkPost fname () ef1 (postcond arg1 arg2 res)
             (unwords [showATerm arg1,showATerm arg2,"->",showATerm res]))
  = spawnConstraint (checkPre fname ef1 (precond (waita x1) (waitb x2))
                              (unwords [showATerm x1,showATerm x2])
                     & 
                     checkPost fname ef2 ef1
                       (postcond (waita x1) (waitb x2) (waitc fx))
                       (unwords [showATerm x1,showATerm x2,"->",showATerm fx]))
                    (ddunifc fx (fun (ddunifa x1 arg1) (ddunifb x2 arg2)))
 where
  x1,x2,fx,ef1,ef2 free

---------------------------------------------------------------------------
-- Combinators for checking contracts without postconditions:

withPreContract1 :: Data a => AssertKind -> Assert a -> Assert b -> String
                 -> (a -> CheckResult) -> (a -> b) -> a -> b

withPreContract1 Strict _ _ fname precond fun arg
  | checkPre fname () (precond arg) (showATerm arg)
  = fun arg

withPreContract1 Lazy (Assert waita ddunifa) _ fname precond fun arg =
  spawnConstraint (checkPre fname () (precond (waita argx)) (showATerm argx))
                  (fun (ddunifa argx arg))
 where
  argx free

withPreContract1 Enforceable (Assert waita ddunifa) _ fname precond fun arg
  | registerAssertion ef1 fname "Pre"
                      (checkPre fname () (precond arg) (showATerm arg))
  = spawnConstraint (checkPre fname ef1 (precond (waita argx)) (showATerm argx))
                    (fun (ddunifa argx arg))
 where
  argx,ef1 free


withPreContract2 :: (Data a, Data b) => AssertKind -> Assert a -> Assert b -> Assert c -> String
                 -> (a -> b -> CheckResult) -> (a -> b -> c) -> a -> b -> c

withPreContract2 Strict _ _ _ fname precond fun arg1 arg2
  | checkPre fname () (precond arg1 arg2)
                      (unwords [showATerm arg1,showATerm arg2])
  = fun arg1 arg2

withPreContract2 Lazy (Assert waita ddunifa) (Assert waitb ddunifb) _
                 fname precond fun arg1 arg2 =
  spawnConstraint (checkPre fname () (precond (waita x1) (waitb x2))
                            (unwords [showATerm x1,showATerm x2]))
                  (fun (ddunifa x1 arg1) (ddunifb x2 arg2))
 where
  x1,x2 free

withPreContract2 Enforceable (Assert waita ddunifa) (Assert waitb ddunifb) _
                 fname precond fun arg1 arg2
  | registerAssertion ef1 fname "Pre"
                      (checkPre fname () (precond arg1 arg2)
                                (unwords [showATerm arg1,showATerm arg2]))
  = spawnConstraint (checkPre fname ef1 (precond (waita x1) (waitb x2))
                              (unwords [showATerm x1,showATerm x2]))
                    (fun (ddunifa x1 arg1) (ddunifb x2 arg2))
 where
  x1,x2,ef1 free

---------------------------------------------------------------------------
-- Combinators for checking contracts without preconditions:

-- Add postcondition contract to 0-ary operation:
withPostContract0 :: Data a => AssertKind -> Assert a -> String -> (a -> CheckResult)
                  -> a -> a

withPostContract0 Strict _ fname postcond val
  | checkPost fname () () (postcond val) (unwords [showATerm val])
  = val

withPostContract0 Lazy (Assert waita ddunifa) fname postcond val =
  spawnConstraint (checkPost fname () () (postcond (waita valx))
                             (unwords [showATerm valx]))
                  (ddunifa valx val)
 where
  valx free

withPostContract0 Enforceable (Assert waita ddunifa) fname postcond val
  | registerAssertion ef fname "Post"
      (checkPost fname () () (postcond val) (unwords [showATerm val]))
  = spawnConstraint (checkPost fname ef () (postcond (waita valx))
                               (unwords [showATerm valx]))
                    (ddunifa valx val)
 where
  valx,ef free


withPostContract1 :: (Data b, Data a) => AssertKind -> Assert a -> Assert b -> String
                         -> (a -> b -> CheckResult)
                         -> (a -> b) -> a -> b

withPostContract1 Strict _ _ fname postcond fun arg
  | checkPost fname () () (postcond arg result)
              (unwords [showATerm arg,"->",showATerm result])
  = result
 where result = fun arg

withPostContract1 Lazy (Assert waita ddunifa) (Assert waitb ddunifb)
                  fname postcond fun arg =
  spawnConstraint (checkPost fname () () (postcond (waita argx) (waitb fx))
                             (unwords [showATerm argx,"->",showATerm fx]))
                  (ddunifb fx (fun (ddunifa argx arg)))
 where
  argx,fx free

withPostContract1 Enforceable (Assert waita ddunifa) (Assert waitb ddunifb)
                  fname postcond fun arg
  | registerAssertion ef fname "Post"
      (let res = fun arg
        in checkPost fname () () (postcond arg res)
                      (unwords [showATerm arg,"->",showATerm res]))
  = spawnConstraint (checkPost fname ef () (postcond (waita argx) (waitb fx))
                               (unwords [showATerm argx,"->",showATerm fx]))
                    (ddunifb fx (fun (ddunifa argx arg)))
 where
  argx,fx,ef free


withPostContract2 :: (Data a, Data b, Data c) => AssertKind -> Assert a -> Assert b -> Assert c -> String
                         -> (a -> b -> c -> CheckResult)
                         -> (a -> b -> c) -> a -> b -> c

withPostContract2 Strict _ _ _ fname postcond fun arg1 arg2
  | checkPost fname () () (postcond arg1 arg2 result)
              (unwords [showATerm arg1,showATerm arg2,"->",showATerm result])
  = result
 where result = fun arg1 arg2

withPostContract2 Lazy (Assert waita ddunifa) (Assert waitb ddunifb)
                  (Assert waitc ddunifc) fname postcond fun arg1 arg2 =
  spawnConstraint (checkPost fname () ()
                        (postcond (waita x1) (waitb x2) (waitc fx))
                        (unwords [showATerm x1,showATerm x2,"->",showATerm fx]))
                  (ddunifc fx (fun (ddunifa x1 arg1) (ddunifb x2 arg2)))
 where
  x1,x2,fx free

withPostContract2 Enforceable (Assert waita ddunifa) (Assert waitb ddunifb)
                  (Assert waitc ddunifc) fname postcond fun arg1 arg2
  | registerAssertion ef fname "Post"
      (let res = fun arg1 arg2
        in checkPost fname () () (postcond arg1 arg2 res)
             (unwords [showATerm arg1,showATerm arg2,"->",showATerm res]))
  = spawnConstraint (checkPost fname ef ()
                       (postcond (waita x1) (waitb x2) (waitc fx))
                       (unwords [showATerm x1,showATerm x2,"->",showATerm fx]))
                    (ddunifc fx (fun (ddunifa x1 arg1) (ddunifb x2 arg2)))
 where
  x1,x2,fx,ef free

---------------------------------------------------------------------------
-- Auxiliaries to implement assertions.

--- Transform a unary set function into a function that returns some element
--- of the result set instead of the complete set.
someValueOf1 :: Ord b => (a -> Values b) -> a -> b
someValueOf1 setfun x = head (sortValues (setfun x))

--- Transform a binary set function into a function that returns some element
--- of the result set instead of the complete set.
someValueOf2 :: Ord c => (a -> b -> Values c) -> a -> b -> c
someValueOf2 setfun x y = head (sortValues (setfun x y))

---------------------------------------------------------------------------
--- Generic type to encapsulate the functionality of assertions on various
--- concrete types.
data Assert a = Assert (a->a) (a->a->a)

--- Constructor for Assert instances.
--- It creates from a wait and a demand-driven unification operation for
--- a given type an Assert instance for this type by adding a generic handler
--- for logic variables as expressions in the demand-driven unification.
makeAssert :: Data a => (a->a) -> (a->a->a) -> Assert a
makeAssert wait ddunif = Assert wait (withVarCheck ddunif)

--- Returns the wait operation of an Assert instance.
waitOf :: Assert a -> (a->a)
waitOf (Assert wait _) = wait

--- Returns the ddunif operation of an Assert instance.
ddunifOf :: Assert a -> (a->a->a)
ddunifOf (Assert _ ddunif) = ddunif

-- Auxiliary operation for demand-driven unification.
-- If the third argument is a logic variable, unify it with the second
-- (which is always a logic variable for passing the result) and return it,
-- otherwise apply the first argument (the "real" demand-driven unification).
withVarCheck :: Data a => (a -> a -> a) -> a -> a -> a
withVarCheck ddunif x e = if isVar e then (x=:=e) &> e else ddunif x e

-- Assert instances for various concrete types:

--- Assert instance for integers.
aInt :: Assert Int
aInt = aPrimType

--- Assert instance for floats.
aFloat :: Assert Float
aFloat = aPrimType

--- Assert instance for characters.
aChar :: Assert Char
aChar = aPrimType

--- Assert instance for Booleans.
aBool :: Assert Bool
aBool = aPrimType

--- Assert instance for Ordering.
aOrdering :: Assert Ordering
aOrdering = aPrimType

--- Assert instance for Success.
aSuccess :: Assert Success
aSuccess = aPrimType

--- Assert instance for Unit type.
aUnit :: Assert ()
aUnit = aPrimType

--- Assert instance scheme for primitive (unstructured) types.
aPrimType :: Data a => Assert a
aPrimType = Assert ensureNotFree ddunifPrimType
  where
   ddunifPrimType x i | x =:= i = i

--- Assert instance scheme for polymorphic values.
--- Since we cannot examine the concrete structure of polymorphic values,
--- we simply wait until the complete value becomes evaluated to a ground term.
aPolyType :: Data a => Assert a
aPolyType = Assert ensureGround ddunifPolyType
  where
   ensureGround x = ensureNotFree (id $## x)
   ddunifPolyType x i | x =:= i = i

--- Assert instance for lists.
aList :: Data a => Assert a -> Assert [a]
aList (Assert waita ddunifa) = makeAssert waitList ddunifList
 where
  waitList l = case l of []     -> []
                         (x:xs) -> waita x : waitList xs

  ddunifList x e = case e of
      []   -> (x=:=[])   &> []
      y:ys -> let z,zs free
               in (x=:=z:zs) &> (ddunifa z y : ddunifList zs ys)

--- Assert instance for string.
aString :: Assert String
aString = aList aChar

--- Assert instance for pairs.
aPair :: (Data a, Data b) => Assert a -> Assert b -> Assert (a,b)
aPair (Assert waita ddunifa) (Assert waitb ddunifb) =
  makeAssert waitPair ddunifPair
 where
  waitPair l = case l of (a,b) -> (waita a, waitb b)

  ddunifPair x e =
    case e of
      (a1,a2) -> let x1,x2 free
                  in x=:=(x1,x2) &> (ddunifa x1 a1, ddunifb x2 a2)

--- Assert instance for triples.
aTriple :: (Data a, Data b, Data c) => Assert a -> Assert b -> Assert c -> Assert (a,b,c)
aTriple (Assert waita ddunifa) (Assert waitb ddunifb) (Assert waitc ddunifc) =
  makeAssert waitTriple ddunifTriple
 where
  waitTriple l = case l of (a,b,c) -> (waita a, waitb b, waitc c)

  ddunifTriple x e =
    case e of
      (a1,a2,a3) -> let x1,x2,x3 free
                     in x=:=(x1,x2,x3) &>
                        (ddunifa x1 a1, ddunifb x2 a2, ddunifc x3 a3)

--- Assert instance for 4-tuples.
aTuple4 :: (Data a, Data b, Data c, Data d)
             => Assert a -> Assert b -> Assert c -> Assert d -> Assert (a,b,c,d)
aTuple4 (Assert waita ddunifa) (Assert waitb ddunifb) (Assert waitc ddunifc)
        (Assert waitd ddunifd) =
  makeAssert waitTuple ddunifTuple
 where
  waitTuple l = case l of (a,b,c,d) -> (waita a, waitb b, waitc c, waitd d)

  ddunifTuple x e =
    case e of
      (a1,a2,a3,a4) ->
         let x1,x2,x3,x4 free
          in x=:=(x1,x2,x3,x4) &>
             (ddunifa x1 a1, ddunifb x2 a2, ddunifc x3 a3, ddunifd x4 a4)

--- Assert instance for Maybe values.
aMaybe :: Data a => Assert a -> Assert (Maybe a)
aMaybe (Assert waita ddunifa) = makeAssert waitMaybe ddunifMaybe
 where
  waitMaybe e = case e of Nothing  -> Nothing
                          (Just x) -> Just (waita x)

  ddunifMaybe x e =
    case e of
      Nothing -> (x=:=Nothing) &> Nothing
      (Just y) ->  let z free
                    in (x =:= Just z) &> Just (ddunifa z y)

--- Assert instance for Either values.
aEither :: (Data a, Data b) => Assert a -> Assert b -> Assert (Either a b)
aEither (Assert waita ddunifa) (Assert waitb ddunifb) =
   makeAssert waitEither ddunifEither
 where
  waitEither e = case e of (Left  x) -> Left  (waita x)
                           (Right x) -> Right (waitb x)

  ddunifEither x e =
    case e of
      (Left  y) ->  let z free
                    in (x =:= Left  z) &> Left  (ddunifa z y)
      (Right y) ->  let z free
                    in (x =:= Right z) &> Right (ddunifb z y)


------------------------------------------------------------------------
-- Implement delaying and activating of assertion via global variables:

-- The global variable for assertion control:
assertionControl :: GVar ()
assertionControl = gvar unknown

-- Initialize assertion control:
initAssertionQueue :: IO ()
initAssertionQueue = do
  --putStrLn "INIT ASSERTION QUEUE"
  writeGVar assertionControl unknown

-- Get control variable for assertion. It is a logic variable
-- until the strict assertion checking is activated.
getAssertionControlVariable :: IO ()
getAssertionControlVariable = do
  v <- readGVar assertionControl
  --putStrLn ("Contol variable: "++showAnyExpression v)
  return v

-- Activate strict assertion checking by instantiation of control variable:
activateAssertions :: IO ()
activateAssertions = do
  --putStrLn "ACTIVATE ASSERTIONS"
  v <- getAssertionControlVariable
  doSolve (v=:=())
  initAssertionQueue -- new assertion control

------------------
-- Registers a new assertion for activation at some later point.
-- If the first argument is instantiated at the time of activation,
-- the assertion will be ignored, otherwise it will be evaluated.
registerAssertion :: () -> String -> String -> Success -> Success
registerAssertion eflag fname pp asrt
  | -- in order to be sure that the global control variable is initialized
    -- in the spawned constraint:
    unsafePerformIO (getAssertionControlVariable >> return ()) =:= ()
  = spawnConstraint (delayedAssertion eflag fname pp asrt =:= ())
                    success

delayedAssertion :: () -> String -> String -> Success -> ()
delayedAssertion eflag fname pp asrt = unsafePerformIO $ do
  v <- getAssertionControlVariable
  --putStrLn ("Delay assertion '"++fname++"': "++showAnyExpression asrt)
  ensureNotFree v =:= () &> return ()
  --putStrLn ("Assertion '"++fname++"' activated: "++showAnyExpression asrt)
  when (isVar eflag) $ do 
    when debug $ putStrLn (pp++"condition of '"++fname++"' enforced...")
    asrt &> return ()
------------------------------------------------------------------------

--- Returns True iff the argument is a free variable, i.e., has no value.
isVar :: a -> Bool
isVar = not . isDefined