------------------------------------------------------------------------
--- A transformation from a Curry program with pre/postconditions
--- into a Curry program where these conditions are integrated
--- into the code
------------------------------------------------------------------------

import AbstractCurry.Types
import AbstractCurry.Files
import AbstractCurryComments
import AbstractCurry.Pretty
import AbstractCurry.Build
import AbstractCurry.Select
import AbstractCurry.Transform

import System.Directory
import System.Environment  ( getArgs, setEnv )
import System.CurryPath    ( stripCurrySuffix )
import System.FilePath     ( (</>) )
import System.Process      ( system )

import Data.List           
import Data.Maybe          ( fromJust )
import Data.Time           ( compareClockTime )
import Control.Applicative ( when )
import Control.Monad       ( void )
import Curry.Compiler.Distribution ( installDir )

import DSDCurryPackageConfig(packagePath)

dsdSourceDir :: String
dsdSourceDir = packagePath </> "src"

banner :: String
banner = unlines [bannerLine,bannerText,bannerLine]
 where
   bannerText = "DSDCurry Transformation Tool (Version of 01/08/24)"
   bannerLine = take (length bannerText) (repeat '=')

------------------------------------------------------------------------
-- Data type for transformation parameters
data TParam = TParam Bool -- generate code for lazy assertions?
                     Bool -- use enforcable lazy assertions?
                     Bool -- encapsulate assertion checking by set functions?
                     Bool -- use single results of postconds as implement.s?
                     Bool -- load and execute transformed program?
                     Bool -- debug assertions during execution?

defaultTParam :: TParam
defaultTParam = TParam False False False False False False

setStrictAssert  (TParam _ _ sf pcs ep db) = TParam False False sf pcs ep db

setLazyAssert    (TParam _ _ sf pcs ep db) = TParam True False sf pcs ep db

setEnforceAssert (TParam _ _ sf pcs ep db) = TParam True True sf pcs ep db

setEncapsulate   (TParam la fa _ pcs ep db) = TParam la fa True pcs ep db

withEncapsulate  (TParam _ _ sf _ _ _) = sf

setSinglePostSpecs (TParam la fa sf _ ep db) = TParam la fa sf True ep db

withSinglePostSpecs (TParam _ _ _ pcs _ _) = pcs

executeProg      (TParam _ _ _ _ execprog _) = execprog

setExecuteProg   (TParam la fa sf pcs _ db) = TParam la fa sf pcs True db

withDebugging    (TParam _ _ _ _ _ db) = db

setDebugging     (TParam la fa sf pcs ep _) = TParam la fa sf pcs ep True

-- get kind of assertion checking from parameters:
checkKind :: TParam -> CExpr
checkKind (TParam la fa _ _ _ _) =
  constF (aMod $ if la && fa  then "Enforceable" else
                 if la then "Lazy" else "Strict")

------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn banner
  args <- getArgs
  processArgs defaultTParam args
 where
  processArgs tparam args = case args of
     ("-s":moreargs) -> processArgs (setStrictAssert  tparam) moreargs
     ("-l":moreargs) -> processArgs (setLazyAssert    tparam) moreargs
     ("-f":moreargs) -> processArgs (setEnforceAssert tparam) moreargs
     ("-e":moreargs) -> processArgs (setEncapsulate   tparam) moreargs
     ("-pcs":moreargs) -> processArgs (setSinglePostSpecs tparam) moreargs
     ("-r":moreargs) -> processArgs (setExecuteProg   tparam) moreargs
     ("-d":moreargs) -> processArgs (setDebugging     tparam) moreargs
     [mname]         -> transform tparam (stripCurrySuffix mname)
     _ -> putStrLn $
          "ERROR: Illegal arguments for transformation: " ++
          unwords args ++ "\n" ++
          "Usage: dsdcurry [-s|-f|-l|-e|-pcs|-r|-d] <module_name>\n"++
          "-s   : generate strict assertions (default)\n"++
          "-l   : generate lazy assertions\n"++
          "-f   : generate lazy enforceable assertions\n"++
          "-e   : encapsulate nondeterminism of assertions\n"++
          "-pcs : take single result of functions generated from postconditions\n"++
          "-r   : load the transformed program into PAKCS\n"++
          "-d   : show assertion results during execution (with -r)\n"

-- Specifies how the name of the transformed module is built from the
-- name of the original module.
transformedModName :: String -> String
transformedModName m = m++"C"

-- start PAKCS and load a module:
loadPAKCS :: TParam -> String -> IO ()
loadPAKCS tparam m = do
  putStrLn $ "\nStarting PAKCS and loading module '"++m++"'..."
  when (withDebugging tparam) $ setEnv "ASSERTDEBUG" "yes"
  void $ system $ installDir </> "bin" </> "pakcs :l " ++ m

-- The main transformation function.
transform :: TParam -> String -> IO ()
transform tparam modname = do
  let acyfile = abstractCurryFileName modname
  doesFileExist acyfile >>= \b -> when b $ removeFile acyfile
  prog <- readCurryWithComments modname >>= return . addCmtFuncInProg
  doesFileExist acyfile >>= \b -> when (not b) $ error "Source program incorrect"
  let realfdecls = filter isRealFuncDecl (functions prog)
      funspecs  = getFunSpecifications prog
      specnames = map (dropSpecName . snd . funcName) funspecs
      preconds  = getPreConditions prog
      prenames  = map (dropPreCondName  . snd . funcName) preconds
      postconds = getPostConditions prog
      postnames = map (dropPostCondName  . snd . funcName) postconds
      newfuns   = union specnames postnames \\ (map (snd . funcName) realfdecls)
      checkfuns = union specnames (union prenames postnames)
      onlyprecond = prenames
                  \\ (specnames ++ postnames ++ map (snd . funcName) realfdecls)
      saveprog  = transformProgram tparam realfdecls funspecs preconds
                                   postconds prog
      savefile  = transformedModName modname ++ ".curry"
  when (not $ null onlyprecond) $
   error ("Operations with precondition but without implemenation/specification: "
          ++ unwords onlyprecond)
  when (not $ null newfuns) $ 
   putStrLn $ "Generating new definitions for operations: " ++ unwords newfuns
  when (not $ null checkfuns) $
   putStrLn $ "Adding pre/postcondition checking to: " ++ unwords checkfuns
  if null (funspecs++preconds++postconds)
   then putStrLn "No specifcations or pre/postconditions found, no transformation required!"
   else do putStrLn $ "Writing transformed module to '" ++ savefile ++ "'..."
           writeFile savefile (showCProg saveprog)
           copyImportModules tparam
           when (executeProg tparam) $ 
            loadPAKCS tparam (transformedModName modname)
  
-- Is a function declaration a real implementation, i.e.,
-- is the body different from "unknown"?
isRealFuncDecl :: CFuncDecl -> Bool
isRealFuncDecl (CFunc _ _ _ _ rs) = not (isUnknown rs)
isRealFuncDecl (CmtFunc _ _ _ _ _ rs) = not (isUnknown rs)

isUnknown :: [CRule] -> Bool
isUnknown rules = case rules of
  [CRule _ (CSimpleRhs e [])] -> e == CSymbol ("Prelude","unknown")
  _ -> False

-- copy imported modules if necessary:
copyImportModules tparam = do
  cdir <- getCurrentDirectory
  when (cdir /= dsdSourceDir) $
   mapM_ (\m -> copyFileOnDemand (dsdSourceDir </> m++".curry")
                                         (cdir </> m++".curry"))
               ["Assert"]
  let paramMod = if withEncapsulate tparam then "AssertParamEncapsulate"
                                           else "AssertParamNonEncapsulate"
  copyFileOnDemand (dsdSourceDir </> paramMod++".curry")
                   (cdir </> "AssertParam.curry")

-- get the specifcation functions from a Curry module
getFunSpecifications :: CurryProg -> [CFuncDecl]
getFunSpecifications prog = filter (isSpecName . snd . funcName)
                                   (functions prog)

-- get the preconditions from a Curry module
getPreConditions :: CurryProg -> [CFuncDecl]
getPreConditions prog = filter (isPreCondName . snd . funcName)
                               (functions prog)

-- get the postconditions from a Curry module
getPostConditions :: CurryProg -> [CFuncDecl]
getPostConditions prog = filter (isPostCondName . snd . funcName)
                                (functions prog)

-- Transform a given program w.r.t. given specifications and pre/postconditions
transformProgram :: TParam -> [CFuncDecl] -> [CFuncDecl] -> [CFuncDecl]
                 -> [CFuncDecl] -> CurryProg -> CurryProg
transformProgram tparam allfdecls specdecls predecls postdecls
                 (CurryProg mname imps _ _ _ tdecls fdecls opdecls) =
 let newspecfuns  = concatMap (genFunction4Spec tparam fdecls) specdecls
     newpostspecs = concatMap (genFunction4PostCond tparam fdecls) postdecls
     newpostspecnames = map (snd . funcName) newpostspecs
     newpostconds = concatMap (genPostCond4Spec tparam allfdecls postdecls)
                              specdecls
     newfunnames  = map (snd . funcName)
                        (newpostconds ++ newspecfuns ++ newpostspecs)
     wonewfuns    = filter (\fd -> snd (funcName fd) `notElem` newfunnames)
                           fdecls -- remove functions having new gen. defs.
     -- compute postconditions actually used for contract checking:
     contractpcs  = filter (\fd -> dropPostCondName (snd (funcName fd))
                                   `notElem` newpostspecnames)
                           (postdecls++newpostconds)
     rename (mn,fn) = (if mn==mname then transformedModName mname else mn, fn)
  in renameCurryModule (transformedModName mname) $
       CurryProg mname
                 (nub ("Assert":"SetFunctions":imps))
                 Nothing [] []
                 tdecls
                 (map deleteCmtIfEmpty
                      (map (addContract tparam predecls contractpcs)
                           (newspecfuns++newpostspecs++wonewfuns)
                       ++ newpostconds
                       ++ map genAssertInstance tdecls))
                 opdecls

-- Add an empty comment to each function which has no comment
addCmtFuncInProg :: CurryProg -> CurryProg
addCmtFuncInProg (CurryProg mname imps _ _ _ tdecls fdecls opdecls) =
  CurryProg mname imps Nothing [] [] tdecls (map addCmtFunc fdecls) opdecls
 where
  addCmtFunc (CFunc qn ar vis texp rs) = CmtFunc "" qn ar vis texp rs
  addCmtFunc (CmtFunc cmt qn ar vis texp rs) = CmtFunc cmt qn ar vis texp rs

-- Generate a function definition from a specification if there is no function
-- for this specification present:
genFunction4Spec :: TParam -> [CFuncDecl] -> CFuncDecl -> [CFuncDecl]
genFunction4Spec _ allfuncs (CmtFunc cmt (m,f) ar vis texp _) =
 let fname     = dropSpecName f
     deffuncs  = filter (\fd -> isRealFuncDecl fd && snd (funcName fd) == fname)
                        allfuncs
     argvars   = map (\i -> (i,"y"++show i)) [1..ar]
  in if null deffuncs
     then [cmtfunc cmt
                   (m,fname) ar vis texp
                   [simpleRule (map CPVar argvars)
                               (applyF (m,f) (map CVar argvars))]]
     else []

-- Generate a postcondition from a specification that is parameterized
-- by an "observation function".
-- If the specification is deterministic, generate an equality check,
-- otherwise generate a set containment check.
genPostCond4Spec :: TParam -> [CFuncDecl] -> [CFuncDecl] -> CFuncDecl
                 -> [CFuncDecl]
genPostCond4Spec _ allfdecls postdecls (CmtFunc _ (m,f) ar vis qt _) =
 let fname     = dropSpecName f
     detspec   = isDetSpecName f -- determ. spec? (later: use prog.ana.)
     fpostname = fname++"'post"
     fpgenname = fpostname++"'generic"
     oldfpostc = filter (\fd -> snd (funcName fd) == fpostname) postdecls
     oldcmt    = if null oldfpostc then ""
                                   else '\n' : funcComment (head oldfpostc)
     varg      = (0,"g")
     argvars   = map (\i -> (i,"x"++show i)) [1..(ar+1)]
     spargvars = take ar argvars
     resultvar = last argvars
     (c, texp) = (qualType2Context qt, qualType2Type qt)
     gtype     = CTVar (0,"grt") -- result type of observation function
     varz      = (ar+2,"z")
     obsfun    = maybe (pre "id")
                       funcName
                       (find (\fd -> snd (funcName fd) == fpostname++"'observe")
                             allfdecls)
     postcheck = CLetDecl
                  [CLocalPat (CPVar varz)
                       (CSimpleRhs (CApply (CVar varg) (CVar resultvar)) []),
                   CLocalFunc (cfunc (m,"gspec") ar Private
                      (addContext c (replaceResultType texp gtype))
                      [let gsargvars = map (\i -> (i,"y"++show i)) [1..ar] in
                       simpleRule (map CPVar gsargvars)
                                  (CApply (CVar varg)
                                        (applyF (m,f) (map CVar gsargvars)))])]
                  (if detspec
                   then applyF (pre "==")
                          [CVar varz, applyF (m,"gspec") (map CVar spargvars)]
                   else applyF (pre "&&")
                         [applyF (pre "==") [CVar varz, CVar varz],
                          applyF (sfMod "valueOf")
                           [CVar varz,
                            applyF (sfMod $ "set"++show ar)
                                   (constF (m,"gspec") : map CVar spargvars)]])
     rename qf = if qf==(m,fpostname) then (m,fpostname++"'org") else qf
  in [cmtfunc
       ("Parametric postcondition for '"++fname++
        "' (generated from specification). "++oldcmt)
       (m,fpgenname) (ar+2) vis
       (addContext c $ (resultType texp ~> gtype) ~> extendFuncType texp boolType)
       [if null oldfpostc
        then simpleRule (map CPVar (varg:argvars)) postcheck
        else simpleRuleWithLocals
                (map CPVar (varg:argvars))
                (applyF (pre "&&")
                             [applyF (rename (funcName (head oldfpostc)))
                                     (map CVar argvars),
                              postcheck])
                [updQNamesInCLocalDecl rename
                        (CLocalFunc (deleteCmt (head oldfpostc)))]]
     ,cmtfunc
       ("Postcondition for '"++fname++"' (generated from specification). "++
        oldcmt)
       (m,fpostname) (ar+1) vis
       (addContext c $ extendFuncType texp boolType)
       [simpleRule (map CPVar argvars)
                   (applyF (m,fpgenname)
                           (constF obsfun : map CVar argvars))]
     ]

-- Generate a function definition from a postcondition if there is
-- neither a specification nor an implementation for this function,
-- i.e., consider this postcondition as a specification for an implementation:
genFunction4PostCond :: TParam -> [CFuncDecl] -> CFuncDecl -> [CFuncDecl]
genFunction4PostCond tparam allfuncs (CmtFunc cmt (m,f) _ vis qt _) =
 let fname     = dropPostCondName f
     flname    = if withSinglePostSpecs tparam then fname++"''" else fname
     (c, texp) = (qualType2Context qt, qualType2Type qt)
     ar        = arityOfType texp - 1
     ftype     = addContext c $ transPCType f texp
     deffuncs  = filter (\fd -> isRealFuncDecl fd &&
                                (snd (funcName fd) == fname ||
                                 dropSpecName (snd (funcName fd)) == fname))
                        allfuncs
     argvars   = map (\i -> (i,"y"++show i)) [1..ar]
     resultvar = (ar+1,"y0")
     postcall  = applyF (m,f) (map CVar (argvars++[resultvar]))
  in if null deffuncs
     then let postfun = cmtfunc cmt (m,flname) ar vis ftype
                                [guardedRule (map CPVar argvars)
                                       [(postcall, CVar resultvar)]
                                       [CLocalVars [resultvar]]]
           in [if withSinglePostSpecs tparam
               then cmtfunc "" (m,fname) ar vis ftype
                      [simpleRuleWithLocals []
                             (applyF (aMod $ "someValueOf"++show ar)
                                              [setFun ar (m,flname) []])
                             [CLocalFunc postfun]]
               else postfun]
     else []


-- adds contract checking to a function if it has a pre- or postcondition
addContract :: TParam -> [CFuncDecl] -> [CFuncDecl] -> CFuncDecl -> CFuncDecl
addContract tparam predecls postdecls fdecl@(CmtFunc cmt (m,f) ar vis qt _) =
 let texp      = qualType2Type qt
     asrttypes = map toPolymorphicAssertTypes (getArgResultTypes texp)
     argvars   = map (\i -> (i,"x"++show i)) [1..ar]
     predecl   = find (\fd -> dropPreCondName(snd(funcName fd)) == f) predecls
     prename   = funcName (fromJust predecl)
     postdecl  = find (\fd-> dropPostCondName(snd(funcName fd)) == f) postdecls
     postname  = funcName (fromJust postdecl)
     encaps fn n = if withEncapsulate tparam
                   then setFun n fn []
                   else constF fn
     asrtCall  = if predecl==Nothing
                 then applyF (aMod $ "withPostContract" ++ show ar)
                        (checkKind tparam : asrttypes ++
                         [string2ac f, encaps postname (ar+1),
                          constF (m,f++"'")] ++
                         map CVar argvars)
                 else if postdecl==Nothing
                 then applyF (aMod $ "withPreContract" ++ show ar)
                        (checkKind tparam : asrttypes ++
                         [string2ac f, encaps prename ar, constF (m,f++"'")] ++
                         map CVar argvars)
                 else applyF (aMod $ "withContract" ++ show ar)
                        (checkKind tparam : asrttypes ++
                         [string2ac f, encaps prename ar,
                          encaps postname (ar+1), constF (m,f++"'")] ++
                         map CVar argvars)
     rename qf = if qf==(m,f) then (m,f++"'") else qf
  in if predecl==Nothing && postdecl==Nothing then fdecl else
       cmtfunc cmt (transformedModName m,f) ar vis qt
         [simpleRuleWithLocals (map CPVar argvars)
                asrtCall
                [updQNamesInCLocalDecl rename (CLocalFunc (deleteCmt fdecl))]]


-- Get types of arguments and result
getArgResultTypes :: CTypeExpr -> [CTypeExpr]
getArgResultTypes t = case t of
  CFuncType t1 t2 -> t1 : getArgResultTypes t2
  _               -> [t]

-- Transforms a monomorphic type expression into an assertion instance
-- expression of this type.
toPolymorphicAssertTypes :: CTypeExpr -> CExpr
toPolymorphicAssertTypes =
  toAssertTypes (\_ -> constF (aMod "aPolyType"))

-- Transforms a type expression into an assertion instance expression
-- of this type. The first argument specifies the mapping for
-- type variables.
toAssertTypes :: ((Int,String) -> CExpr) -> CTypeExpr -> CExpr
toAssertTypes mapvar (CTVar tv) = mapvar tv
toAssertTypes mapvar (CFuncType t1 t2) =
  applyF (aMod "aFun") (map (toAssertTypes mapvar) [t1,t2])
toAssertTypes _      (CTCons (tm,tc)) =
  applyF (if tm=="Prelude" then aMod (preludeTCons2Assert tc) else (tm,'a':tc)) []
 where
  preludeTCons2Assert c = case c of
    "Int"      -> "aInt"
    "Float"    -> "aFloat"
    "Char"     -> "aChar"
    "Bool"     -> "aBool"
    "Success"  -> "aSuccess"
    "Ordering" -> "aOrdering"
    "[]"       -> "aList"
    "String"   -> "aString"
    "Maybe"    -> "aMaybe"
    "Either"   -> "aEither"
    "()"       -> "aUnit"
    "(,)"      -> "aPair"
    "(,,)"     -> "aTriple"
    "(,,,)"    -> "aTuple4"
    _          -> error ("Lazy assertion of type '" ++ c ++" ' not yet supported!")

 
-- Transforms the type of a postcondition into a type for the
-- corresponding function.
transPCType f t = case t of
  CFuncType t1 (CTCons _) -> t1
  CFuncType t1 t2         -> CFuncType t1 (transPCType f t2)
  _ -> error ("Illegal type of postcondition \""++f++"\"!")

-- Computes the (first-order) arity of a qualified type.
arityOfQualType :: CQualTypeExpr -> Int
arityOfQualType (CQualType _ t) = arityOfType t

-- Computes the (first-order) arity of a type.
arityOfType :: CTypeExpr -> Int
arityOfType t = case t of
  CFuncType _ t' -> 1 + arityOfType t'
  _ -> 0

-- Is this the name of a specification?
isSpecName :: String -> Bool
isSpecName f = let rf = reverse f
                in take 5 rf == "ceps'" || take 6 rf == "dceps'"

-- Is this the name of a deterministic specification?
isDetSpecName :: String -> Bool
isDetSpecName f = take 6 (reverse f) == "dceps'"

-- Drop the specification suffix from the name:
dropSpecName :: String -> String
dropSpecName f =
  let rf = reverse f
   in reverse (drop (if take 5 rf == "ceps'" then 5 else
                     if take 6 rf == "dceps'" then 6 else 0) rf)

-- Is this the name of a precondition?
isPreCondName :: String -> Bool
isPreCondName f = take 4 (reverse f) == "erp'"

-- Drop the precondition suffix from the name:
dropPreCondName :: String -> String
dropPreCondName f =
  let rf = reverse f
   in reverse (drop (if take 4 rf == "erp'" then 4 else 0) rf)

-- Is this the name of a precondition?
isPostCondName :: String -> Bool
isPostCondName f = take 5 (reverse f) == "tsop'"

-- Drop the postcondition suffix from the name:
dropPostCondName :: String -> String
dropPostCondName f =
  let rf = reverse f
   in reverse (drop (if take 5 rf == "tsop'" then 5 else 0) rf)

-- An operation of the module Assert:
aMod f = ("Assert",f)

-- An operation of the module SetFunctions:
sfMod f = ("SetFunctions",f)

-- Set function for a function name with given arity and arguments:
setFun :: Int -> QName -> [CExpr] -> CExpr
setFun n qn args = applyF (sfMod $ "set"++show n) (constF qn : args)

------------------------------------------------------------------------
-- Generate code for Assert instances on user-defined types.

genAssertInstance :: CTypeDecl -> CFuncDecl
genAssertInstance (CTypeSyn (mn,tc) _ targs texp) =
  cfunc
   (mn,'a':tc) 1 Public
   (emptyClassType $ foldr (\tv t -> applyTC (aMod "Assert") [CTVar tv] ~> t)
                           (applyTC (aMod "Assert") 
                             [applyTC (mn,tc) (map CTVar targs)])
                           targs)
   [simpleRule (map (\ (i,s) -> CPVar (i,"assert_"++s)) targs)
               (toLocalAssertType texp)]

genAssertInstance (CType (mn,tc) _ targs tcs _) =
  cfunc
   (mn,'a':tc) 1 Public
   (emptyClassType $ foldr (\tv t -> applyTC (aMod "Assert") [CTVar tv] ~> t)
          (applyTC (aMod "Assert") [mtype])
          targs)
   [simpleRuleWithLocals
     (map (\ (i,s) -> CPVar (i,"assert_"++s)) targs)
     (applyF (aMod "makeAssert") [CSymbol (mn,"wait"++tc),
                                  CSymbol (mn,"ddunif"++tc)])
     [CLocalFunc $ 
        cfunc (mn,"wait"++tc) 1 Private
              (emptyClassType $ mtype ~> mtype)
              [simpleRule [CPVar wvar]
                          (CCase CRigid (CVar wvar) (map tc2waitbranch tcs))],
      CLocalFunc $
        cfunc (mn,"ddunif"++tc) 1 Private
              (emptyClassType $ mtype ~> mtype ~> mtype)
              [simpleRule [CPVar uvar1, CPVar uvar2]
                          (CCase CRigid (CVar uvar2) (map tc2unifbranch tcs))]
     ]]
 where
  mtype = applyTC (mn,tc) (map CTVar targs)
  wvar = (1,"wv")
  uvar1 = (1,"x")
  uvar2 = (2,"exp")

  tc2waitbranch (CCons (_,cons) _ texps) = let n = length texps in
    (CPComb (mn,cons) (map (\i -> CPVar (i,'x':show i)) [1..n]),
     CSimpleRhs
       (applyF (mn,cons)
               (map (\ (i,texp) -> texp2wait texp [CVar (i,'x':show i)])
                    (zip [1..n] texps))) [])

  tc2unifbranch (CCons (_,cons) _ texps) = let n = length texps in
    (CPComb (mn,cons) (map (\i -> CPVar (i,'x':show i)) [1..n]),
     CSimpleRhs
      (letExpr (map (\i -> CLocalVars [(i+100,'y':show i)]) [1..n])
               (applyF (pre "&>")
                       [applyF (pre "=:=")
                               [CVar uvar1,
                                applyF (mn,cons)
                                  (map (\i -> CVar (i+100,'y':show i)) [1..n])],
                        applyF (mn,cons)
                          (map (\ (i,texp) -> 
                                 texp2unif texp
                                  [CVar (i+100,'y':show i), CVar (i,'x':show i)])
                               (zip [1..n] texps))])) [])

  texp2wait (CTVar (i,tv)) args = applyF (aMod "waitOf")
                                         (CVar (i,"assert_"++tv) : args)
  texp2wait texp@(CFuncType _ _) args =
    applyF (aMod "waitOf") (toLocalAssertType texp : args)
  texp2wait texp@(CTCons (tm,tcons)) args =
    if texp==mtype -- recursive type?
    then applyF (tm,"wait"++tcons) args
    else applyF (aMod "waitOf") (toLocalAssertType texp : args)

  texp2unif (CTVar (i,tv)) args = applyF (aMod "ddunifOf")
                                         (CVar (i,"assert_"++tv) : args)
  texp2unif texp@(CFuncType _ _) args =
    applyF (aMod "ddunifOf") (toLocalAssertType texp : args)
  texp2unif texp@(CTCons (tm,tcons)) args =
    if texp==mtype -- recursive type?
    then applyF (tm,"ddunif"++tcons) args
    else applyF (aMod "ddunifOf") (toLocalAssertType texp : args)

-- Transforms a type expression into an assertion instance expression
-- of this type.
toLocalAssertType = toAssertTypes (\ (i,tv) -> CVar (i,"assert_"++tv))

-- Converts a type expression into qualified type expression
addContext :: CContext -> CTypeExpr -> CQualTypeExpr
addContext = CQualType

-- Extracts the type of a qualified type expression
qualType2Type :: CQualTypeExpr -> CTypeExpr
qualType2Type (CQualType _ t) = t

-- Extracts the context of a qualified type expression
qualType2Context :: CQualTypeExpr -> CContext
qualType2Context (CQualType c _) = c

-- Computes result type of a function type
resultType :: CTypeExpr -> CTypeExpr
resultType texp = case texp of CFuncType _ t -> resultType t
                               _             -> texp

-- Replaces a result type of a function type by a new type
replaceResultType :: CTypeExpr -> CTypeExpr -> CTypeExpr
replaceResultType texp ntype =
    case texp of CFuncType t1 t2 -> CFuncType t1 (replaceResultType t2 ntype)
                 _               -> ntype

-- Transform a n-ary function type into a (n+1)-ary function type with
-- a given new result type
extendFuncType :: CTypeExpr -> CTypeExpr -> CTypeExpr
extendFuncType t@(CTVar  _) texp = t ~> texp
extendFuncType t@(CTCons _) texp = t ~> texp
extendFuncType (CFuncType t1 t2) texp = t1 ~> (extendFuncType t2 texp)

------------------------------------------------------------------------
-- Auxiliary operations:

--- Copy a file on demand, i.e., do not copy it if the target file
--- exists with the same time stamp and size.
copyFileOnDemand :: String -> String -> IO ()
copyFileOnDemand source target = do
  let copycmd  = do putStrLn "Copying auxiliary module:"
                    putStrLn (source++" -> "++target)
                    copyFile source target
  exfile <- doesFileExist target
  if exfile
   then do odate <- getModificationTime source
           ndate <- getModificationTime target
           osize <- getFileSize source
           nsize <- getFileSize target
           when (compareClockTime ndate odate == LT || osize /= nsize) $
            copycmd
   else copycmd

------------------------------------------------------------------------
--- Deletes the comment in a function declaration.
deleteCmt (CFunc     qn ar vis texp rules) = CFunc qn ar vis texp rules
deleteCmt (CmtFunc _ qn ar vis texp rules) = CFunc qn ar vis texp rules

--- Deletes the comment in a function declaration if it is the empty string.
deleteCmtIfEmpty (CFunc qn ar vis texp rules)     = CFunc qn ar vis texp rules
deleteCmtIfEmpty (CmtFunc cmt qn ar vis texp rules) =
  if null cmt then CFunc qn ar vis texp rules
              else CmtFunc cmt qn ar vis texp rules

------------------------------------------------------------------------
