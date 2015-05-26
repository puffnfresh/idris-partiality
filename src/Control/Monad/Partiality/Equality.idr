module Control.Monad.Partiality.Equality

import Control.Monad.Partiality

%default total

infix 5 =~=

data (=~=) : Partiality a -> Partiality b -> Type where
  Now' : x = y -> Now x =~= Now y
  Later' : Inf (x =~= y) -> Later x =~= Later y

neverNever : never =~= never
neverNever = Later' neverNever

functorIdentity : (p : Partiality a) -> map id p =~= p
functorIdentity (Now x) = Now' Refl
functorIdentity (Later (Delay x)) = Later' (functorIdentity x)

functorComposition : (p : Partiality a)
                  -> (g : a -> b)
                  -> (f : b -> c)
                  -> map (f . g) p =~= (map f . map g) p
functorComposition (Now x) g f = Now' Refl
functorComposition (Later (Delay x)) g f = Later' (functorComposition x g f)
