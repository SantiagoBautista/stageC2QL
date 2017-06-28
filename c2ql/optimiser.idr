module Opti

import Privy
import C2QL

mutual
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
    (>>) : Uncomplete a -> Fonction b 2 -> Fonction b a
    (<<): Fonction 2 a -> Uncomplete b -> Fonction b a

  data Uncomplete : Nat -> Type where
    (>) : (Fonction 1 1 , Fonction 1 1) -> Fonction a 2 -> Uncomplete a
    (<): Fonction 2 a -> (Fonction 1 1, Fonction 1 1) -> Uncomplete a

-- To set the priority right
-- infix 6 <
-- < = .<

pred: C2QLPred
pred = Equal A "Bureau"

example1 : Fonction 0 1
example1 = (Defrag < (Project [N], Select pred)) >> (Frag [N, D] . Rel RendezVous)
-- defrag < (proj s, select s') > frag d . rel rdv

-- total ariteResFonction: Fonction n -> Nat
-- ariteResFonction (Frag s) = 2
-- ariteResFonction _        = 1
--
-- mutual
--   data Formule: Type where
--     (.) : (f: Fonction n) -> (args: List Formule) ->
--         {auto p : AriteCorrecte args n} -> Formule
--     (-) : Fonction n -> Vect n Schema   -> Formule
--
--   total ariteResFormule: Formule -> Nat
--   ariteResFormule (f . v) = ariteResFonction f
--   ariteResFormule (f - v) = ariteResFonction f
--
--   data AriteCorrecte: List Formule -> Nat -> Type where
--     Pile: AriteCorrecte [] Z
--     Reste: AriteCorrecte fs n -> AriteCorrecte (f::fs) (n + ariteResFormule f)
--
-- -- -- exemple pour que je comprenne
-- -- ex : AriteCorrecte [Id - [RendezVous]] 1
-- -- ex = Reste Pile
-- --
-- --
-- data NonNul : Nat -> Type where
--   IsNextOf : (k: Nat) -> NonNul (S k)
--
-- Uninhabited (NonNul Z) where
--   uninhabited (IsNextOf k) impossible
--
-- nonNul : (n: Nat) -> Dec(NonNul n)
-- nonNul Z = No absurd
-- nonNul (S k) = Yes (IsNextOf k)
--
-- dAriteNonNule : (p1: AriteCorrecte l n) -> (p2: NonNul n) -> NonEmpty l
-- dAriteNonNule p1 p2 with (p1)
--  | Pile        = absurd p2
--  | (Reste a)   = IsNonEmpty
--
-- aucuneAriteNule: (f: Fonction n) -> NonNul (ariteResFonction f)
-- aucuneAriteNule (Frag s) = IsNextOf 1
-- aucuneAriteNule Id            = IsNextOf  0
-- aucuneAriteNule (Project s)   = IsNextOf  0
-- aucuneAriteNule Join          = IsNextOf  0
-- aucuneAriteNule (Select p)    = IsNextOf  0
-- aucuneAriteNule (Group s)     = IsNextOf  0
-- aucuneAriteNule (Fold a f c)  = IsNextOf  0
-- aucuneAriteNule (Crypt a c)   = IsNextOf  0
-- aucuneAriteNule (Decrypt a c) = IsNextOf  0
-- aucuneAriteNule Defrag        = IsNextOf  0
--
-- ariteNonNule: (f: Formule) -> NonNul(ariteResFormule f)
-- ariteNonNule (fc . v) = aucuneAriteNule fc
-- ariteNonNule (fc - v) = aucuneAriteNule fc
--
-- -- sch: (f: Formule) -> Vect (ariteResFormule f) Schema
-- -- sch ((.) f v {p}) with (f)
-- --   | Id          = sch (Prelude.List.head
-- --     {ok = dAriteNonNule p (aucuneAriteNule Id)} v)
-- --   | Project s   = [intersect s (sch (head v))]
-- --   | _  = ?todo
-- -- sch (f - v) = ?casBaseFormule
