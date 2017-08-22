module Opti

import Privy
import C2QL

mutual
  infixl 5 .<
  infixl 6 >.
  data Fonction: (ariteArgs: Nat) -> (ariteRes: Nat) -> Type where
    Id      : Fonction 1 1
    Project : Schema -> Fonction 1 1
    Join    : Fonction 2 1
    Select  : C2QLPred -> Fonction 1 1
    Group   : Schema -> Fonction 1 1
    Fold    : Attribute -> (Ty -> Ty) -> Ty -> Fonction 1 1
    -- C2QL specific
    Crypt   : Attribute -> CryptTy -> Fonction 1 1
    Decrypt : Attribute -> CryptTy -> Fonction 1 1
    Frag    : Schema -> Fonction 1 2
    Defrag  : Fonction 2 1
    Rel     : Schema -> Fonction 0 1
    -- For composition
    (.) : Fonction b c -> Fonction a b -> Fonction a c
    (.<): Fonction 2 a -> Uncomplete b -> Fonction b a

  data Uncomplete : Nat -> Type where
    (>.) : (Fonction 1 1 , Fonction 1 1) -> Fonction a 2 -> Uncomplete a

pred: C2QLPred
pred = Equal A "Bureau"

example1 : Fonction 0 1
example1 = Defrag .< (Project [N], Select pred) >. Frag [N, D] . Rel RendezVous

schemaRes : Fonction args res -> Vect args Schema -> Vect res Schema
