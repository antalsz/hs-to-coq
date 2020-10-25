{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Control.Monad.Trans.Parse (
  -- * The 'Parse' monad
  Parse, runParse, evalParse,
  -- * The 'ParseT' monad transformer
  ParseT(..), runParseT, evalParseT, liftParse,
  -- * 'ParseT' operations
  parseWithM, parseWithM', parseWith,
  atEOF, parseToken, parseCharTokenLookahead,
  parseError,
  -- * Lower-level
  parseChar, parseChars, peekChar,
  -- * Errors
  Location(..), ParseError(..), prettyParseError
) where

import HsToCoq.Util.Coerce

import Data.Functor.Identity
import Control.Applicative
import Control.Monad
import Control.Monad.Fail
import Control.Monad.Fix
import Control.Monad.State
import Control.Monad.Except
import HsToCoq.Util.Function

import Data.Text (Text)
import qualified Data.Text as T

import qualified Control.Monad.Reader.Class    as R
import qualified Control.Monad.Writer.Class    as W
import qualified Control.Monad.Cont.Class      as C

--------------------------------------------------------------------------------

data ParseState = ParseState
  { parseLocation :: !Location
  , parseInput :: !Text
  } deriving (Eq, Ord, Show)

initialState :: Text -> ParseState
initialState = ParseState initialLocation

data Location = Location { line, column :: !Int }
  deriving (Eq, Ord, Show)

initialLocation :: Location
initialLocation = Location 1 1

data ParseError = ParseError Location String
  deriving (Eq, Ord, Show)

prettyParseError :: String -> ParseError -> String
prettyParseError filename (ParseError loc msg) =
  filename ++ ":" ++ show (line loc) ++ ":" ++ show (column loc) ++ ": parse error: " ++ msg

--------------------------------------------------------------------------------

newtype ParseT m a = ParseT { getParseT :: StateT ParseState (ExceptT [ParseError] m) a }
                   deriving ( Functor, Applicative, Monad
                            , Alternative, MonadPlus
                            , MonadFail, MonadFix, MonadIO
                            , R.MonadReader r, W.MonadWriter w, C.MonadCont
                            )

instance MonadTrans ParseT where lift = ParseT #. (lift . lift)

-- Can't autoderive 'MonadState' through 'StateT'
instance MonadState s m => MonadState s (ParseT m) where
  get = lift get
  put = lift . put

type Parse = ParseT Identity

runParseT :: ParseT m a -> Text -> m (Either [ParseError] (a, ParseState))
runParseT (ParseT act) = runExceptT . runStateT act . initialState

runParse :: Parse a -> Text -> Either [ParseError] (a, ParseState)
runParse = runIdentity .: runParseT

evalParseT :: Monad m => ParseT m a -> Text -> m (Either [ParseError] a)
evalParseT (ParseT act) t = runExceptT $ do
  (res, t') <- runStateT act (initialState t)
  if T.null (parseInput t')
  then pure res
  else throwError [ParseError (parseLocation t') "unused input"]

evalParse :: Parse a -> Text -> Either [ParseError] a
evalParse = runIdentity .: evalParseT

liftParse :: Monad m => Parse a -> ParseT m a
liftParse (ParseT act) = ParseT (mapStateT (mapExceptT (pure . runIdentity)) act)

--------------------------------------------------------------------------------

parseWithM :: Applicative f => (ParseState -> Either [ParseError] (a, ParseState)) -> ParseT f a
parseWithM f = ParseT . StateT $ ExceptT . pure . f

parseWithM' :: Applicative f => String -> (ParseState -> Maybe (a, ParseState)) -> ParseT f a
parseWithM' msg f = parseWithM $ \s -> note [ParseError (parseLocation s) msg] (f s)
  where note x = maybe (Left x) Right

parseWith :: Applicative f => (ParseState -> (a, ParseState)) -> ParseT f a
parseWith f = parseWithM $ Right . f

peekChar :: Monad m => ParseT m (Maybe Char)
peekChar = ParseT . gets $ fmap fst . T.uncons . parseInput

atEOF :: Monad m => ParseT m Bool
atEOF = ParseT . gets $ T.null . parseInput

parseError :: Monad m => String -> ParseT m void
parseError = ParseT . parseError_

parseError_ :: (MonadState ParseState m, MonadError [ParseError] m) => String -> m void
parseError_ msg = do
  l <- gets parseLocation
  throwError [ParseError l msg]

incrLocation :: Char -> Location -> Location
incrLocation c l
  | c == '\n' = Location (line l + 1) 1
  | otherwise = Location (line l) (column l + 1)

incrLocations :: Text -> Location -> Location
incrLocations = flip (T.foldl' (flip incrLocation))

parseChar_ :: ParseState -> Maybe (Char, ParseState)
parseChar_ s = do
  (c, i) <- T.uncons (parseInput s)
  let s' = ParseState (incrLocation c (parseLocation s)) i
  pure (c, s')

parseChar :: Monad m => (Char -> Bool) -> ParseT m Char
parseChar pred = ParseT $ do
  next <- gets parseChar_
  case next of
    Nothing -> parseError_ "unexpected EOF"
    Just (c, s') | not (pred c) -> parseError_ ("unexpected character " ++ show c)
                 | otherwise -> put s' >> pure c

parseChars_ :: (Char -> Bool) -> ParseState -> (Text, ParseState)
parseChars_ pred s =
  let (pre, suf) = T.span pred (parseInput s)
      s' = ParseState (incrLocations pre (parseLocation s)) suf
  in (pre, s')

parseChars :: Monad m => (Char -> Bool) -> ParseT m Text
parseChars = parseWith . parseChars_

parseToken :: Monad m
           => (Text -> a)
           -> (Char -> Bool)
           -> (Char -> Bool)
           -> ParseT m a
parseToken build isFirst isRest =
  build .: T.cons <$> parseChar isFirst <*> parseChars isRest

parseCharTokenLookahead :: Monad m
                        => (Text -> a)
                        -> (Char -> Bool)
                        -> (Maybe Char -> Bool)
                        -> ParseT m a
parseCharTokenLookahead build isFirst isNext = do
  c <- parseChar isFirst
  guard . isNext =<< peekChar
  pure . build $ T.singleton c
