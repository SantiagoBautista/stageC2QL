module Opti

import Privy
import C2QL

data Fonction: Nat -> Type where
  Id      : Fonction 1
  Project : Schema -> Fonction 1
  Join    : Fonction 2
  Select  : C2QLPred -> Fonction 1
  Group   : Schema -> Fonction 1
  Fold    : Attribute -> (Ty -> Ty) -> Ty -> Fonction 1
  -- C2QL specific
  Crypt   : Attribute -> CryptTy -> Fonction 1
  Decrypt : Attribute -> CryptTy -> Fonction 1
  Frag    : Schema -> Fonction 1
  Defrag  : Fonction 2

data Formule: Type where
  (.) : Fonction n -> Vect n Formule  -> Formule
  (-) : Fonction n -> Vect n Schema   -> Formule

-- exemple : Formule
-- exemple = Crypt N AES - [RendezVous]

sch: Formule -> List Schema
sch (f . v) with (f)
  | Id = sch (head v)
  | _  = []
sch (f - v) = ?casBaseFormule
