import Data.Vect

data RNG : Type where
  SimpleRNG : Int -> RNG

next: RNG -> (Int, RNG)
next (SimpleRNG seed) = let newSeed = (seed * 0x5DEECE + 0xB)  in
  (seed, SimpleRNG newSeed)

Rand : Type -> Type
Rand a = (RNG -> (a, RNG))

next2 : Rand Int
next2 = next

unit: a -> Rand a
unit result = (\x => (result, x))

map : Rand a -> (a -> b) -> Rand b
map gen f = (\rng => let (rl, nrng) = gen rng in (f rl, nrng) )

nextPair: Rand Int
nextPair = Main.map next (\x => x - (mod x 2))

--- Exercice 6.7
map2: Rand a -> Rand b -> (a -> b -> c) -> Rand c
map2 ra rb f = \rng =>
  let (resa, rng') = ra rng in
  let (resb, rng'') = rb rng' in
  (f resa resb, rng'')

nextBoth: Rand (Int, Int)
nextBoth = map2 next next (\x, y => (x, 2*y))

--- Exercice 6.7
sequence: Vect l (Rand a) -> Rand (Vect l a)
sequence [] = \rng => ([], rng)
sequence (f::fs) = \rng =>
  let genReste = sequence fs in
  let (res, rng')     = f         rng   in
  let (reste, rng'')  = genReste  rng'  in
  (res::reste, rng'')

fill : (l: Nat) -> a -> Vect l a
fill Z x      = []
fill (S k) x  = x::(fill k x)

ints : (l: Nat) -> RNG -> Vect l Int
ints l r = let (res, rng) = Main.sequence (fill l next) r in res

--- Exercice 6.8
flatMap : Rand a -> (a -> Rand b) -> Rand b
flatMap ra f = \rng =>
  let (res, rng') = ra rng in
  f res rng'

nonNegative : Rand Int
nonNegative = map next (\x => abs x)

withBound : Int -> Rand Int
withBound n = flatMap nonNegative (\poss => let reste = mod poss n in
                if (poss + (n - 1) - reste >= 0)
                then unit ( mod poss n)
                else withBound n)

intsBy : (l: Nat) -> Rand Int -> RNG -> Vect l Int
intsBy l gen r = let (res, rng) = Main.sequence (fill l gen) r in res

--- Exercice 6.9
nmap : Rand a -> (a-> b) -> Rand b
nmap gen f = flatMap gen (\x => unit (f x))

nmap2 : Rand a -> Rand b -> (a -> b -> c) -> Rand c
nmap2 ra rb f = flatMap ra (\aa => nmap rb (\bb => f aa bb))
