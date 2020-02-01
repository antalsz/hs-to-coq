{-# LANGUAGE ScopedTypeVariables     #-}

module Server where

import           Control.Monad
import           Data.Proxy
import           Socket
import           StringUtil

-- TODO: better handling of this
somaxconn :: Int
somaxconn = 1024

bufSize :: Int
bufSize = 10 * 1024 * 1024

doOneConnection :: PosixMonad s m => s -> m ()
doOneConnection sock = do
  buf <- recv sock bufSize
  doOneConnectionMain sock buf

doOneConnectionMain :: forall m s. PosixMonad s m => s -> String -> m ()
doOneConnectionMain sock buf = do
  let (_, body, b) = sSplit buf "\r\n\r\n"
  if b then do
    let (_, s', b') = sSplit buf "\r\nContent-Length: "
    when b' $ do
      let (len, _) = sBreak s' "\r\n"
      case readString len of
        Nothing -> return ()
        Just l ->
          void $ doOneConnectionBody sock body l (length buf - length body)
    let (method, rest) = sBreak buf " "
    let (path, _) = sBreak rest "\r\n"
    result <- theApplication (Proxy :: Proxy s) method path
    let ok = "HTTP/1.1 200 OK\r\nContent-type: text/plain\r\n\r\n"
    send sock ok
    send sock result
    return ()
  else do
    s <- recv sock (bufSize - length buf)
    doOneConnectionMain sock $ buf ++ s
    return ()

doOneConnectionBody :: PosixMonad s m => s -> String -> Int -> Int -> m String
doOneConnectionBody sock body l l' =
  if length body < l then do
    s <- recv sock (bufSize - length body - l')
    doOneConnectionBody sock (body ++ s) l l'
  else return body

theApplication :: PosixMonad s m => Proxy s -> String -> String -> m String
theApplication _ _ _ = return "nothing yet"

serverMain :: forall m s. (PosixMonad s m, Recursive m) => Proxy s -> m ()
serverMain _ = do
  let addr = SocketAddrIn 8080 0
  sock <- socket AF_INET SOCK_STREAM 0 :: m s
  bind sock addr
  listen sock somaxconn
  loop $ do
    (newSock, _) <- accept sock
    doOneConnection newSock
