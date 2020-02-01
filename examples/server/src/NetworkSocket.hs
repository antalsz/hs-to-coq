{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}

module NetworkSocket where

import           Control.Monad.Except
import           Data.ByteString.Char8
import           Data.Int
import           Data.Proxy
import           Foreign.C.Types
import           Network.Socket
import           Network.Socket.ByteString (recv, send)
import           Server
import qualified Socket
import           Util

instance Socket.PosixMonad Socket IO where
  socket f t p = case familyMatcher f of
    Just f  -> socket f (typeMatcher t) $ CInt (fromIntegral p :: Int32)
    Nothing -> error "Unsupported protocol"
  bind s a = bind s $ addrMatcher a
  listen = listen
  accept s =  liftSnd addrMatcher' <$> accept s
  recv s n = unpack <$> recv s n
  send s = send s . pack
  trace _ = Prelude.putStrLn

instance Socket.Recursive IO where
  loop f = f >> Socket.loop f

familyMatcher :: Socket.SocketFamily -> Maybe Family
familyMatcher Socket.AF_UNIX      = Just AF_UNIX
familyMatcher Socket.AF_LOCAL     = Just AF_UNIX -- AF_LOCAL is a synonym for AF_UNIX
familyMatcher Socket.AF_INET      = Just AF_INET
familyMatcher Socket.AF_AX25      = Just AF_X25
familyMatcher Socket.AF_IPX       = Just AF_IPX
familyMatcher Socket.AF_APPLETALK = Just AF_APPLETALK
familyMatcher Socket.AF_X25       = Just AF_X25
familyMatcher Socket.AF_INET6     = Just AF_INET6
familyMatcher Socket.AF_DECnet    = Just AF_DECnet
familyMatcher Socket.AF_KEY       = Just Pseudo_AF_KEY
familyMatcher Socket.AF_NETLINK   = Just AF_ROUTE
familyMatcher Socket.AF_PACKET    = Just AF_PACKET
familyMatcher Socket.AF_PPPOX     = Just AF_PPPOX
familyMatcher Socket.AF_LLC       = Just AF_NETBEUI -- double check this
familyMatcher Socket.AF_MPLS      = Just AF_BRIDGE -- double check this
familyMatcher Socket.AF_CAN       = Just AF_CAN
familyMatcher Socket.AF_BLUETOOTH = Just AF_BLUETOOTH
familyMatcher _                   = Nothing

typeMatcher :: Socket.SocketType -> SocketType
typeMatcher Socket.SOCK_EMPTY     = NoSocketType
typeMatcher Socket.SOCK_STREAM    = Stream
typeMatcher Socket.SOCK_DGRAM     = Datagram
typeMatcher Socket.SOCK_SEQPACKET = SeqPacket
typeMatcher Socket.SOCK_RAW       = Raw
typeMatcher Socket.SOCK_RDM       = RDM

addrMatcher :: Socket.SocketAddr -> SockAddr
addrMatcher (Socket.SocketAddrIn p a) =
  SockAddrInet (fromIntegral p) (fromIntegral a)
addrMatcher (Socket.SocketAddrIn6 p f a s) =
  SockAddrInet6 (fromIntegral p) (fromIntegral f) a (fromIntegral s)
addrMatcher (Socket.SocketAddrUnix s) = SockAddrUnix s

addrMatcher' :: SockAddr -> Socket.SocketAddr
addrMatcher' (SockAddrInet p a) =
  Socket.SocketAddrIn (fromIntegral p) (fromIntegral a)
addrMatcher' (SockAddrInet6 p f a s) =
  Socket.SocketAddrIn6 (fromIntegral p) (fromIntegral f) a (fromIntegral s)
addrMatcher' (SockAddrUnix s) = Socket.SocketAddrUnix s

networkServerMain :: IO ()
networkServerMain = serverMain (Proxy :: Proxy Socket)
