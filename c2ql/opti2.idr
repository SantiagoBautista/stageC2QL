import public Data.List
import public Data.Vect

--------------------------- code pris dans Privy.idr
||| Universe for cryptographic's types
data CryptTy = AES -- | ElGamal | RSA | ...

-- This should use idris-crypto
-- see, https://github.com/idris-hackers/idris-crypto
interpCryptTy : CryptTy -> Type -> Type
interpCryptTy AES t = String

||| Universe for attribute's types
data Ty = NAT | BOOL | TEXT | DATE | CRYPT CryptTy Ty

||| An attribute is a name and a type.
|||
||| Example: `the Attribute ("Name", TEXT)`
Attribute : Type
Attribute = (String, Ty)

||| A schema is a list of attribute.
|||
||| Example: `the Schema [("Date", DATE),("Name", TEXT),("Address",TEXT)]`
Schema : Type
Schema = List Attribute

interpTy : Ty -> Type
interpTy NAT         = Nat    | List (InterpTy NAT)
interpTy BOOL        = Bool   | List (InterpTy BOOL)
interpTy TEXT        = String | List (InterpTy TEXT)
interpTy DATE        = String | List (InterpTy DATE)
interpTy (CRYPT c t) = interpCryptTy c (interpTy t)
------------------------------------------------------- Schema utils
Eq CryptTy where
  AES == AES = True
  _   == _   = False

Eq Ty where
  NAT           == NAT            = True
  BOOL          == BOOL           = True
  TEXT          == TEXT           = True
  DATE          == DATE           = True
  (CRYPT AES x) == (CRYPT AES y)  = x == y
  _             == _              = False

||| Specific attribute for the indexing of fragments.
Id : Attribute
Id = ("Id", NAT)

D : Attribute
D = ("Date", DATE)

N : Attribute
N = ("Nom", TEXT)

A : Attribute
A = ("Adresse", TEXT)

RendezVous : Schema
RendezVous = [D,N,A] -- D :: N :: A :: Nil
--------------------- Fin du code pris dans Privy.idr

--------------------- Code pris dans C2QL
data C2QLPred : Type where
  AND      : C2QLPred -> C2QLPred -> C2QLPred
  OR       : C2QLPred -> C2QLPred -> C2QLPred
  Like     : Attribute -> String -> C2QLPred
  NextWeek : Attribute -> C2QLPred
  Equal    : (a : Attribute) -> (v : interpTy (snd a)) ->
             Eq (interpTy (snd a)) => Show (interpTy (snd a)) => C2QLPred
---------------------- Fin Code pris dans C2QL

data C2QL : Type where
  Project : Schema -> C2QL -> C2QL
  Join   : C2QL -> C2QL -> C2QL
  Select  : C2QLPred -> C2QL -> C2QL
  Group   : Schema -> C2QL -> C2QL
  Fold    : Attribute -> (Ty -> Ty) -> Ty -> C2QL -> C2QL
  -- C2QL specific
  Crypt   : Attribute -> CryptTy -> C2QL -> C2QL
  Decrypt : Attribute -> CryptTy -> C2QL -> C2QL
  LFrag   : Schema -> C2QL -> C2QL
  RFrag   : Schema -> C2QL -> C2QL
  Defrag  : (C2QL, C2QL) -> C2QL
  Rel     : Schema -> C2QL

Frag: Schema -> C2QL -> (C2QL, C2QL)
Frag s q = (LFrag s q, RFrag s q)
