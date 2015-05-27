module Control.Monad.Partiality.Equality

import Control.Monad.Partiality

%default total

infix 1 =~=

data (=~=) : Partiality a -> Partiality b -> Type where
  Now' : x = y -> Now x =~= Now y
  Later' : Inf (x =~= y) -> Later x =~= Later y

refl : x =~= x
refl {x=Now p} = Now' Refl
refl {x=Later (Delay p)} = Later' refl

sym : a =~= b -> b =~= a
sym (Now' prf) = Now' (sym prf)
sym (Later' prf) = Later' (sym prf)

trans : a =~= b -> b =~= c -> a =~= c
trans (Now' ab) (Now' bc) = Now' (trans ab bc)
trans (Later' ab) (Later' bc) = Later' (trans ab bc)

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

applicativeMap : (p : Partiality a)
              -> (f : a -> b)
              -> map f p = pure f <*> p
applicativeMap (Now x) f = Refl
applicativeMap (Later p) f = Refl

applicativeIdentity : (p : Partiality a) -> pure id <*> p =~= p
applicativeIdentity = functorIdentity

applicativeHomomorphism : (x : a)
                       -> (f : a -> b)
                       -> Now f <*> Now x = Now (f x)
applicativeHomomorphism x f = Refl

applicativeInterchange : (x : a)
                      -> (f : Partiality (a -> b))
                      -> f <*> pure x =~= pure (\g => g x) <*> f
applicativeInterchange x (Now f) = Now' Refl
applicativeInterchange x (Later (Delay f)) =
  Later' (applicativeInterchange x f)

monadApplicative : (mf : Partiality (a -> b))
                -> (mx : Partiality a)
                -> mf <*> mx =~= mf >>= (\f => mx >>= (\x => pure (f x)))
monadApplicative (Now f) (Now a) = Now' Refl
monadApplicative (Now f) (Later (Delay a)) = Later' (monadApplicative (Now f) a)
monadApplicative (Later (Delay f)) mx =
  Later' (monadApplicative f mx)

monadLeftIdentity : (x : a)
                 -> (f : a -> Partiality b)
                 -> return x >>= f = f x
monadLeftIdentity x f = Refl

monadRightIdentity : (mx : Partiality a)
                  -> mx >>= return =~= mx
monadRightIdentity (Now a) = Now' Refl
monadRightIdentity (Later (Delay a)) = Later' (monadRightIdentity a)

monadAssociativity : (mx : Partiality a)
                  -> (f : a -> Partiality b)
                  -> (g : b -> Partiality c)
                  -> mx >>= f >>= g =~= mx >>= (\x => f x >>= g)
monadAssociativity (Now a) f g = refl
monadAssociativity (Later (Delay a)) f g = Later' (monadAssociativity a f g)
