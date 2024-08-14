-- Parameters for Assert module if nondeterminism of assertion checking
-- is not encapsulated.

module AssertParam(CheckResult,isViolation) where

type CheckResult = Bool

isViolation :: CheckResult -> Bool
isViolation = not  -- violation is result if False

