module Control.Monad.Partiality.All

import Control.Monad.Partiality

%default total

data All : (p : a -> Type) -> Partiality a -> Type where
  Here : p x -> All p (Now a)
  There : Inf (All p r) -> All p (Later r)
