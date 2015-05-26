module Control.Monad.Partiality

%default total

public
codata Partiality x = Now x
                    | Later (Partiality x)

public
mapPartiality : (a -> b) -> Partiality a -> Partiality b
mapPartiality f (Now x) = Now (f x)
mapPartiality f (Later p) = Later (mapPartiality f p)

instance Functor Partiality where
  map = mapPartiality

instance Applicative Partiality where
  pure a = Now a
  (<*>) (Now f) fb = map f fb
  (<*>) fa fb = Later (fa <*> fb)

instance Monad Partiality where
  (>>=) (Now x) f = f x
  (>>=) (Later fa) f = Later (fa >>= f)

public
runForSteps : Nat -> Partiality a -> Partiality a
runForSteps _ (Now x) = Now x
runForSteps Z (Later r) = Later r
runForSteps (S n) (Later r) = runForSteps n r

public
isNow : Partiality a -> Bool
isNow (Now _) = True
isNow (Later _) = False

public
never : Partiality a
never = Later never

private
fix' : (a -> Partiality b) -> ((a -> Partiality b) -> a -> Partiality b) -> a -> Partiality b
fix' f g x with (g f x)
  | Now x' = Now x'
  | Later _ = Later (fix' (g f) g x)

public
fix : ((a -> Partiality b) -> a -> Partiality b) -> a -> Partiality b
fix = fix' (const never)
