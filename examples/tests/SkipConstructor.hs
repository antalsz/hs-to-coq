module SkipConstructor where

data T = Ok1
       | Ok2
       | NonPositive (T -> T)   -- Skipped – untranslatable, non-positive recursion
       | Record { field :: () } -- Skipped – testing record fields
       | SkipMe                 -- Skipped – boring

skipEquations :: T -> T
skipEquations Ok1             = Ok1
skipEquations Ok2             = Ok2
skipEquations (NonPositive f) = f (skipEquations (NonPositive f)) -- This equation should be skipped before becoming impossible recursion
skipEquations (Record u)      = Record u                          -- This equation should be skipped
skipEquations SkipMe          = SkipMe                            -- This equation should be skipped

skipCaseBranches :: T -> T
skipCaseBranches t = case t of
  Ok1           -> Ok1
  Ok2           -> Ok2
  NonPositive f -> f (skipCaseBranches (NonPositive f)) -- This case should be skipped before becoming impossible recursion
  Record u      -> Record u                             -- This case should be skipped
  SkipMe        -> SkipMe                               -- This case should be skipped

nestedPattern :: (Bool, Maybe T) -> Maybe T
nestedPattern (True, Just Ok1)    = Just Ok1
nestedPattern (True, Just Ok2)    = Just Ok1
nestedPattern (True, Just SkipMe) = Just SkipMe -- This case should be skipped
nestedPattern _                   = Nothing

-- Issue #130; see also issue #135
extraUnderscore :: T -> T
extraUnderscore Ok1             = Ok1
extraUnderscore Ok2             = Ok2
extraUnderscore _               = Ok1 -- This underscore case is redundant and needs to be eliminated

recordPattern :: T -> ()
recordPattern Record{field = u} = u  -- This pattern shouldn't fail on the record field
recordPattern _                 = ()

-- Issue #132 (duplicates: #133, #134)
multipleArguments :: T -> Bool -> Bool
multipleArguments Ok1             True  = False
multipleArguments Ok1             False = True
multipleArguments (NonPositive _) b     = b     -- The whole equation, not just the first argument, should be skipped
multipleArguments _               _     = False

listComprehension :: [T] -> [T]
listComprehension ts = [Ok1 | Ok1 <- ts] ++ [f SkipMe | NonPositive f <- ts, True]

patternGuard :: T -> T
patternGuard t | Ok1 <- t           = t
               | NonPositive f <- t = f t
patternGuard t | True
               , Record{} <- t
               , True               = t
patternGuard _                      = Ok2
