class C a where
  f :: a

data T = K

instance C T where
  f = K

instance C a => C [a] where
  f = [ f ]
