import Data.Vect

data RNG : Type where
  SimpleRNG : Int -> RNG

data Rand : Type -> Type where
  R : (RNG -> (a, RNG)) -> Rand a

next: RNG -> (Int, RNG)
next (SimpleRNG seed) = let newSeed = (seed * 0x5DEECE + 0xB)  in
  (seed, SimpleRNG newSeed)

int : Rand Int
int = R next

pure      : a -> Rand a
pure val  = R (\rng => (val, rng))

extract : Rand a -> (RNG -> (a, RNG))
extract (R run) = run

(>>=) : Rand a -> (a -> Rand b) -> Rand b
(>>=) (R nexta) f =  R (\rng =>
  let (vala, nrng) = nexta rng in extract (f vala) nrng)

sequence : List (Rand a) -> Rand (List a)
sequence [] = pure []
sequence (f::fs) = do x   <- f
                      xs  <- sequence fs
                      pure (x::xs)

fill : (l: Nat) -> a -> List a
fill Z x      = []
fill (S k) x  = x::(fill k x)

ints2 : (n: Nat) -> Rand (List Int)
ints2 n = sequence (fill n int)

iton : Int -> Nat
iton k = if (abs k == 0) then Z else S (iton ((abs k) - 1))

ns : Rand (List Int)
ns = do x   <- int
        y   <- int
        xs  <- ints2 (iton x)
        pure (map (\x => mod x y) xs)

randomList : Int -> List Int
randomList seed = let (val, lastSeed) = extract ns (SimpleRNG seed) in val
--- Here randomList n will have length n because SimpleRNG returns its seed
--- as first value
