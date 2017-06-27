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

total ariteFonction : {n: Nat} -> (f: Fonction n) -> Nat
ariteFonction {n} f = n

data Formule: Type where
  (.) : Fonction n -> Vect n Formule  -> Formule
  (-) : Fonction n -> Vect n Schema   -> Formule

-- exemple : Formule
-- exemple = Crypt N AES - [RendezVous]

total ariteFormule : Formule -> Nat
ariteFormule (f . v) = ariteFonction f
ariteFormule (f - v) = ariteFonction f

sch: (f: Formule) -> Vect (ariteResultat f) Schema
sch (f . v) with (f)
  | Id          = sch (head v)
  | Project s   = [intersect s (sch (head v))]
  | _  = ?todo
sch (f - v) = ?casBaseFormule
