module Control.Monad.Partiality

%default total

public
codata Partiality x = Now x
                    | Later (Partiality x)

private
mapPartiality : (a -> b) -> Partiality a -> Partiality b
mapPartiality f (Now x) = Now (f x)
mapPartiality f (Later p) = Later (mapPartiality f p)

private
apPartiality : Partiality (a -> b) -> Partiality a -> Partiality b
apPartiality (Now f) a = mapPartiality f a
apPartiality (Later f) a = Later (f `apPartiality` a)

private
bindPartiality : Partiality a -> (a -> Partiality b) -> Partiality b
bindPartiality (Now x) f = f x
bindPartiality (Later fa) f = Later (fa `bindPartiality` f)

instance Functor Partiality where
  map = mapPartiality

instance Applicative Partiality where
  pure = Now
  (<*>) = apPartiality

instance Monad Partiality where
  (>>=) = bindPartiality

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
