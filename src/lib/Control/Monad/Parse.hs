module Control.Monad.Parse (
  -- * The 'MonadParse' type class and 'MonadNewlinesParse' constraint
  MonadParse(..), MonadNewlinesParse,
  -- * The 'Parse' monad
  P.Parse, P.runParse, P.evalParse,
  -- * The 'ParseT' monad transformer
  P.ParseT(..), P.runParseT, P.evalParseT,
  -- * The 'NewlinesParse' monad
  NewlinesParse, evalNewlinesParse,
  -- * The 'NewlinesParseT' monad transformer
  NewlinesParseT(..), evalNewlinesParseT,
  -- * Derived 'ParseT' operations
  parseToken, parseCharTokenLookahead,
  -- ** Lower-level operations
  parseChar, parseChars,
  -- * Errors
  P.Location(..), P.ParseError(..), P.prettyParseError,
  -- * Newline status
  NewlineStatus(..)
) where

import qualified Control.Monad.Trans.Parse as P
import Control.Monad.Trans.NewlinesParse
import Control.Monad.Parse.Class
