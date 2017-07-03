--- In order to have an example to test on...
data Option : Type -> Type where
  None : Option a
  Some : a -> Option a

Functor Option where
  map f None      = None
  map f (Some a)  = Some (f a)

Applicative Option where
  pure a = Some a

  (<*>)  None  aOpt         = None
  (<*>) fOpt     None       = None
  (<*>) (Some f) (Some a)   = Some (f a)

Monad Option where
  (>>=) None      f  = None
  (>>=) (Some a)  f  = f a

--- Exercice 3
seq : Monad m => List (m a) -> m (List a)
seq [] = pure []
seq (x::xs) = do others  <- seq xs
                 one     <- x
                 pure (one::others)

seqExample1 : Option (List Int)
seqExample1 = seq [Some 1, None]

seqExample2 : Option (List Int)
seqExample2 = seq [Some 1, Some 2]

-- For traverse we could do a composition of sequence and map,
-- but that would go twice trought the list instead of once

trav : Monad m => List a -> (a -> m b) -> m (List b)
trav []       f = pure []
trav (x::xs)  f = do  resX  <- f x
                      resXs <- trav xs f
                      pure (resX::resXs)

oSqrt : Double -> Option Double
oSqrt x = if (x > 0) then Some (sqrt x) else None

travExample1 : Option (List Double)
travExample1 = trav [1.1, 2.3, -0.2, 8.5] oSqrt

travExample2 : Option (List Double)
travExample2 = trav [1.1, 2.3, 42.0, 8.5] oSqrt

--- Exercice 4
replicateM : Monad m => Nat -> m a -> m (List a)
replicateM Z      x = pure []
replicateM (S k)  x = do  valX <- x
                          rest <- replicateM k x
                          pure (valX::rest)
