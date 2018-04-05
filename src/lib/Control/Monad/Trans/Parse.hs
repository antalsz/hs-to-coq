{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             FlexibleInstances, UndecidableInstances #-}

module Control.Monad.Trans.Parse (
  -- * The 'Parse' monad
  Parse, runParse, evalParse,
  -- * The 'ParseT' monad transformer
  ParseT(..), runParseT, evalParseT,
  -- * 'ParseT' operations
  parseWithM, parseWithM', parseWith,
  atEOF, parseToken, parseCharTokenLookahead,
  -- * Lower-level
  parseChar, parseChars, peekChar
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

newtype ParseT m a = ParseT { getParseT :: StateT Text (ExceptT String m) a }
                   deriving ( Functor, Applicative, Monad
                            , Alternative, MonadPlus
                            , MonadFail, MonadFix, MonadIO, MonadError String
                            , R.MonadReader r, W.MonadWriter w, C.MonadCont
                            )

instance MonadTrans ParseT where lift = ParseT #. (lift . lift)

-- Can't autoderive 'MonadState' through 'StateT'
instance MonadState s m => MonadState s (ParseT m) where
  get = lift get
  put = lift . put

type Parse = ParseT Identity

runParseT :: ParseT m a -> Text -> m (Either String (a, Text))
runParseT (ParseT act) = runExceptT . runStateT act 

runParse :: Parse a -> Text -> Either String (a, Text)
runParse = runIdentity .: runParseT

evalParseT :: Monad m => ParseT m a -> Text -> m (Either String a)
evalParseT (ParseT act) t = runExceptT $ do
  (res, t') <- runStateT act t
  if T.null t'
  then pure res
  else throwError "unused input"

evalParse :: Parse a -> Text -> Either String a
evalParse = runIdentity .: evalParseT

--------------------------------------------------------------------------------

parseWithM :: Applicative f => (Text -> Either String (a, Text)) -> ParseT f a
parseWithM f = ParseT . StateT $ ExceptT . pure . f

parseWithM' :: Applicative f => String -> (Text -> Maybe (a, Text)) -> ParseT f a
parseWithM' msg f = parseWithM $ note msg . f
  where note x = maybe (Left x) Right

parseWith :: Applicative f => (Text -> (a, Text)) -> ParseT f a
parseWith f = parseWithM $ Right . f

peekChar :: Monad m => ParseT m (Maybe Char)
peekChar = ParseT . gets $ fmap fst . T.uncons

atEOF :: Monad m => ParseT m Bool
atEOF = ParseT $ gets T.null

parseChar :: Monad m => (Char -> Bool) -> ParseT m Char
parseChar pred = do
  c <- parseWithM' "unexpected EOF" T.uncons
  guard $ pred c
  pure c

parseChars :: Monad m => (Char -> Bool) -> ParseT m Text
parseChars pred = parseWith $ T.span pred

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
