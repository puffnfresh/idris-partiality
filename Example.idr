module Main

import Control.Monad.Partiality

mccarthy91' : (Nat -> Partiality Nat) -> Nat -> Partiality Nat
mccarthy91' fn n =
  if n > 100
  then Now (n - 10)
  else fn (n + 11) >>= fn

mccarthy91 : Nat -> Partiality Nat
mccarthy91 = fix mccarthy91'

example : runForSteps 5 (mccarthy91 99) = Now 91
example = Refl
