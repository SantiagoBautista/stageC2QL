module Test

infixl 5 Test.<<

(<<) : Nat -> Nat -> Nat
(<<) x y = x + y

example: Nat
example = 3 << 2
