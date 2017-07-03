--- Int addition
data IntAddition : Type where
  MyInt : Int -> IntAddition

Semigroup IntAddition where
  (<+>) a b =
    let MyInt na = a in
    let MyInt nb = b in
    MyInt (na + nb)

Monoid IntAddition where
  neutral = MyInt 0

--- intMultiplication
data IntMultiplication: Type where
  MyFactor : Int -> IntMultiplication

Semigroup IntMultiplication where
  (<+>) a b =
    let MyFactor na = a in
    let MyFactor nb = b in
    MyFactor (na * nb)

Monoid IntMultiplication where
  neutral = MyFactor 1

--- BooleanOr
data BooleanOr : Type where
  TrueOr  : BooleanOr
  FalseOr : BooleanOr

Semigroup BooleanOr where
  (<+>) a b  with (a, b)
    | (TrueOr, _)         = TrueOr
    | (_, TrueOr)         = TrueOr
    | (FalseOr, FalseOr)  = FalseOr

Monoid BooleanOr where
  neutral = FalseOr

--- BooleanAnd
data BooleanAnd : Type where
  TrueAnd  : BooleanAnd
  FalseAnd : BooleanAnd

Semigroup BooleanAnd where
  (<+>) a b  with (a, b)
    | (TrueAnd, TrueAnd ) = TrueAnd
    | (_      , _       ) = FalseAnd

Monoid BooleanAnd where
  neutral = FalseAnd

--- one non-universal Monoïd for Options
data Option : Type -> Type where
  Nope : Option a
  Some : a -> Option a

Semigroup (Option t) where
  (<+>) a b with (a)
    | Some _  = a
    | Nope    = b

Monoid (Option t) where
  neutral = Nope

--- Monoïd of endofunctions
Endofunction : Type -> Type
Endofunction    a    = (a -> a)

Semigroup (Endofunction a) where
  (<+>) f g = f . g

Monoid (Endofunction a) where
  neutral = (\a => a)

--- Exercice 5
fold : List a -> b -> (b -> a -> b) -> b
fold []       zero _ = zero
fold (x::xs)  zero f = fold xs (f zero x) f

foldMap : Monoid b => List a -> (a -> b) -> b
foldMap [] _  = neutral
foldMap xs f  = fold xs neutral (\b, a => b <+> (f a))

--- Exercice 6
fold2: Monoid b => List a -> (b -> a -> b) -> b
fold2 l f = foldMap l (\a => f neutral a)
