module Control.Monad.Parse (
  -- * The 'MonadParse' type class and 'MonadNewlinesParse' constraint
  MonadParse(..), MonadNewlinesParse,
  -- * The 'Parse' monad
  Parse, runParse, evalParse,
  -- * The 'ParseT' monad transformer
  ParseT(..), runParseT, evalParseT,
  -- * The 'NewlinesParse' monad
  NewlinesParse, runNewlinesParse, evalNewlinesParse,
  -- * The 'NewlinesParseT' monad transformer
  NewlinesParseT(..), runNewlinesParseT, evalNewlinesParseT,
  -- * Derived 'ParseT' operations
  parseWithM', parseWith,
  parseToken, parseCharTokenLookahead,
  -- ** Lower-level operations
  parseChar, parseChars,
  -- * Newline status
  NewlineStatus(..)
) where

import Control.Monad.Trans.Parse ( Parse,      runParse,  evalParse
                                 , ParseT(..), runParseT, evalParseT )
import Control.Monad.Trans.NewlinesParse
import Control.Monad.Parse.Class
