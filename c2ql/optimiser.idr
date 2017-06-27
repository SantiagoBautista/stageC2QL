module Opti

import Privy
import C2QL

data Fonction: Nat -> Type where
  Id      : Fonction (S Z)
  Project : Schema -> Fonction (S Z)
  Join    : Fonction (S (S Z))
  Select  : C2QLPred -> Fonction (S Z)
  Group   : Schema -> Fonction (S Z)
  Fold    : Attribute -> (Ty -> Ty) -> Ty -> Fonction (S Z)
  -- C2QL specific
  Crypt   : Attribute -> CryptTy -> Fonction (S Z)
  Decrypt : Attribute -> CryptTy -> Fonction (S z)
  Frag    : Schema -> Fonction (S z)
  Defrag  : Fonction (S (S Z))
  Rel     : Schema -> Fonction Z
