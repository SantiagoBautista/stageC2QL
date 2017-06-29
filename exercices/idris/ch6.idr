data RNG : Type -> Type where
  SimpleRNG : Int -> RNG Int

next: RNG a -> (a, RNG a)
next (SimpleRNG seed) = let newSeed = (seed * 0x5D + 0xB)  in
  let n =  newSeed + 72 in (n, SimpleRNG newSeed)

Rand : Type -> Type -> Type
Rand a b = ((RNG b) -> (a, RNG b))

next2 : Rand a a
next2 = next

unit: a -> Rand a b
unit result = (\x => (result, x))
