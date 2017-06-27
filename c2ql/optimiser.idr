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


total ariteResFonction: Fonction n -> Nat
ariteResFonction (Frag s) = 2
ariteResFonction _        = 1

data NonNul: Nat -> Type where
  IsNextOf : (k: Nat) -> NonNul (S k)

pasCosmoFage : (f: Fonction n) -> NonNul (ariteResFonction f)
pasCosmoFage (Frag s) = IsNextOf 1
pasCosmoFage _        = IsNextOf 0

-- mutual
--   data Formule: Type where
--     (.) : (f: Fonction n) -> (args: List Formule) ->
--         {auto p : AriteCorrecte args n} -> Formule
--     (-) : Fonction n -> Vect n Schema   -> Formule
--
--   total ariteResFormule: Formule -> S k
--   ariteResFormule (f . v) = ariteResFonction f
--   ariteResFormule (f - v) = ariteResFonction f
--
--   data AriteCorrecte: List Formule -> Nat -> Type where
--     Pile: AriteCorrecte [] Z
--     Reste: AriteCorrecte fs n -> AriteCorrecte (f::fs) (n + ariteResFormule f)
--
-- -- exemple pour que je comprenne
-- ex : AriteCorrecte [Id - [RendezVous]] 1
-- ex = Reste Pile
--
--
-- ariteNonNule: AriteCorrecte (f::fs) (S k) -> NonEmpty (f::fs)
-- ariteNonNule (Reste a) = IsNonEmpty

-- sch: (f: Formule) -> Vect (ariteResFormule f) Schema
-- sch (f . v) with (f)
--   | Id          = sch (head v)
--   | Project s   = [intersect s (sch (head v))]
--   | _  = ?todo
-- sch (f - v) = ?casBaseFormule
