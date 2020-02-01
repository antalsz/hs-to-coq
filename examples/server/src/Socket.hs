{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}


module Socket where

import           Data.Word

data SocketFamily =
  AF_UNIX  | --  Local communication                        unix(7)
  AF_LOCAL | --  Synonym for AF_UNIX
  AF_INET  | --  IPv4 Internet protocols                    ip(7)
  AF_AX25  | --  Amateur radio AX.25 protocol               ax25(4)
  AF_IPX   | --  IPX - Novell protocols
  AF_APPLETALK | -- AppleTalk                                  ddp(7)
  AF_X25   | --  ITU-T X.25 / ISO-8208 protocol             x25(7)
  AF_INET6 | --  IPv6 Internet protocols                    ipv6(7)
  AF_DECnet| --  DECet protocol sockets
  AF_KEY   | --  Key management protocol, originally
             --  developed for usage with IPsec
  AF_NETLINK   | -- Kernel user interface device               netlink(7)
  AF_PACKET| --   Low-level packet interface                 packet(7)
  AF_RDS   | --  Reliable Datagram Sockets (RDS) protocol   rds(7)
             --   rds-rdma(7)
  AF_PPPOX | --  Generic PPP transport layer, for setting
             --  up up L2 tunnels (L2TP and PPPoE)
  AF_LLC   | --  Logical link control (IEEE 802.2 LLC)
             -- protocol
  AF_IB    | -- InfiniBand native addressing
  AF_MPLS  | --  Multiprotocol Label Switching
  AF_CAN   | --  Controller Area Network automotive bus
             --  protocol
  AF_TIPC  | --   TIPC, "cluster domain sockets" protocol
  AF_BLUETOOTH | -- Bluetooth low-level socket protocol
  AF_ALG   | --  Interface to kernel crypto API
  AF_VSOCK | --  VSOCK (originally "VMWare VSockets")       vsock(7)
             --  protocol for hypervisor-guest
             --  communication
  AF_KCM   | --  KCM (kernel connection multiplexor)
             --  interface
  AF_XDP     --  XDP (express data path) interface

-- SOCK_NONBLOCK and SOCK_CLOEXEC are not supported at the moment. The
-- reason is that those configurations can be used in combined with
-- other SocketTypes (via a bitwise or operation), and thus can not be
-- defined using a simple algebraic data type.
data SocketType =
  SOCK_EMPTY     |
  SOCK_STREAM    | -- Provides sequenced, reliable, two-way, connection-
                   -- based byte streams.  An out-of-band data transmission
                   -- mechanism may be supported.
  SOCK_DGRAM     | -- Supports datagrams (connectionless, unreliable
                   -- messages of a fixed maximum length).
  SOCK_SEQPACKET | -- Provides a sequenced, reliable, two-way connection-
                   -- based data transmission path for datagrams of fixed
                   -- maximum length; a consumer is required to read an
                   -- entire packet with each input system call.
  SOCK_RAW       | -- Provides raw network protocol access.
  SOCK_RDM         -- Provides a reliable datagram layer that does not
                   -- guarantee ordering.
                   -- SOCK_PACKET is obsolete.

type ProtocolNumber = Int

type SocketLen = Int

type ErrorCode = Int -- should be an algebraic type

type In6Addr = (Word32, Word32, Word32, Word32)

data SocketAddr =
  SocketAddrIn Int Int |
  SocketAddrIn6 Int Int In6Addr Int |
  SocketAddrUnix String

class Recursive m where
  loop :: m a -> m a

class Monad m => PosixMonad s m where
  socket :: SocketFamily -> SocketType -> ProtocolNumber -> m s
  bind   :: s -> SocketAddr -> m ()
  listen :: s -> Int -> m ()
  accept :: s -> m (s, SocketAddr) -- the accept should return an
                                   -- address as well, but we are not
                                   -- using that
  -- For recv and send, there should be a Flag field, but we will
  -- ignore this for now as we will always be using 0 as the flag for
  -- our implementations
  recv :: s -> Int -> m String
  send :: s -> String -> m Int
  trace  :: s -> String -> m ()
