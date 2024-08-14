-- Parameters for Assert module if nondeterminism of assertion checking
-- is encapsulated.
-- This works for checking of non-values (e.g., infinite terms) only
-- if one has a lazy implementation of set functions available.

module AssertParam(CheckResult,isViolation) where

import Control.Search.SetFunctions

type CheckResult = Values Bool

isViolation :: CheckResult -> Bool
isViolation resultset = False `valueOf` resultset
