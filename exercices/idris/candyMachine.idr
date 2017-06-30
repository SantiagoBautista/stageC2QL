data Input : Type where
  Coin : Input
  Turn : Input

data Output : Type where
  Candy   : Output
  NoCandy : Output

Eq Output where
  Candy   == Candy    = True
  NoCandy == NoCandy  = True
  _       ==  _       = False

data Lockage: Type where
  Locked   : Lockage
  Unlocked : Lockage

||| a State is composed of the number of candies, the number of coins and
||| the lockage (locked or unlocked)
|||
||| (candies, coins, lockage)
State : Type
State = (Nat, Nat, Lockage)

data Action : Type -> Type where
  Do : (State -> (a, State)) -> Action a

apply : Action a -> State -> (a, State)
apply (Do f) s = f s

(>>=) : Action a -> (a -> Action b) -> Action b
(>>=) doA aThenF = Do (\s =>
  let (outA, s') = apply doA s in apply (aThenF outA) s')

pure :  a -> Action a
pure    x = Do (\s => (x, s))

turn : State -> (Output, State)
turn state with (state)
  | (Z, _, _)               = (NoCandy, state) -- out of candies :'(
  | (_, _, Locked)          = (NoCandy, state) -- forgot to insert coin
  | (S k, coins, Unlocked)  = (Candy, (k, coins, Locked)) -- Yay :-D

insert : State -> (Output, State)
insert state with (state)
  | (Z, _, _)                = (NoCandy, state) -- out of candies :/
  | (_, _, Unlocked)         = (NoCandy, state) -- already unlocked
  | (candies, coins, Locked) = (NoCandy, (candies, S coins, Unlocked)) -- :)

doTurn : Action Output
doTurn = Do turn

doInsert : Action Output
doInsert = Do insert


routine : List (Action Output) -> Action Nat
routine   []      = pure 0
routine   (a::as) = let future = routine as in
              do  out <- a
                  candyNow <- pure $ if (out == Candy) then 1 else 0
                  candyLater <- future
                  pure (candyNow + candyLater)

exampleR : Action Nat
exampleR = routine
  [doTurn, doInsert, doInsert, doTurn, doTurn, doInsert, doTurn, doInsert]

example1 : (Nat, State)
example1 = apply exampleR (1, 10, Locked)

example2 : (Nat, State)
example2 = apply exampleR (5, 10, Locked)

example3 : (Nat, State)
example3 = apply exampleR (5, 10, Unlocked)
