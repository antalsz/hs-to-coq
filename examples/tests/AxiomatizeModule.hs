module AxiomatizeModule where

data Harmless a = Helpful a (Harmless a)
                | Polite

data Sweet = Sugar

class Benign a where
  benign :: a

instance Benign Sweet where
  benign = Sugar

evil :: a -> Harmless a
evil x = Helpful x (evil x)

cruel :: Benign a => Harmless a
cruel = evil benign

kind :: Benign a => Harmless a
kind = Helpful benign Polite

saccharine :: Harmless Sweet
saccharine = Helpful Sugar (Helpful Sugar Polite)

malicious :: a
malicious = malicious
