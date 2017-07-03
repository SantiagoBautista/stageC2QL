State : Type
State = Nat

data Action : Type -> Type where
  Update : (State -> (a, State)) -> Action a

apply : Action a -> State -> (a, State)
apply (Update f) s = f s

pure : a -> Action a
pure x = Update (\s => (x, s))

(>>=) : Action a -> (a -> Action b) -> Action b
(>>=) actA f = Update (\s => let (val, s') = apply actA s in
                              apply (f val) s')

repeat : String -> Nat -> String
repeat pattern Z      = ""
repeat pattern (S k)  = pattern ++ (repeat pattern k)

as : Action String
as = Update (\s => (repeat "a" s, S s))

bs : Action String
bs = Update (\s => (repeat "b" s, S s))

abs : Action String
abs = do  first   <- as
          second  <- bs
          third   <- as
          pure (first ++ second ++ third)

go               : State -> (String, State)
go initialState  = apply abs initialState

Functor Action where
  map f fa = (>>=) fa (\a => pure (f a))

Applicative Action where
  pure a = pure a

  (<*>) f fa = Update (\s =>
    let (a, s')   = apply fa s  in
    let (ff, s'') = apply f  s' in
    (ff a, s''))

Monad Action where
  (>>=) fa f = (>>=) fa f

example : Action Integer
example = (join . Prelude.Applicative.pure . Main.pure) 1
