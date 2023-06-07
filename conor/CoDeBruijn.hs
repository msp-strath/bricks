{-# LANGUAGE DataKinds, GADTs, TypeOperators #-}

module CoDeBruijn where

import Data.Traversable

data Nat = Z | S Nat deriving (Eq, Ord)

natI :: Nat -> Int
natI Z = 0
natI (S n) = 1 + natI n

instance Show Nat where show = show . natI

data Natty :: Nat -> * where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)
  
nattyI :: Natty n -> Int
nattyI Zy = 0
nattyI (Sy n) = 1 + nattyI n

instance Show (Natty n) where show = show . nattyI

class NATTY n where
  natty :: Natty n

instance NATTY Z where
  natty = Zy
instance NATTY n => NATTY (S n) where
  natty = Sy natty

nattily :: Natty n -> (NATTY n => t) -> t
nattily Zy t = t
nattily (Sy n) t = nattily n t

data (<=) :: Nat -> Nat -> * where
  No :: n <= m ->   n <= S m
  Su :: n <= m -> S n <= S m
  Ze ::             Z <= Z

instance Show (n <= m) where
  show th = help th "]" where
    help :: forall n m. n <= m -> String -> String
    help (No th) s = help th ('0' : s)
    help (Su th) s = help th ('1' : s)
    help  Ze     s = '[' : s

bigEnd :: n <= m -> Natty m
bigEnd (No th) = Sy (bigEnd th)
bigEnd (Su th) = Sy (bigEnd th)
bigEnd  Ze     = Zy

weeEnd :: n <= m -> Natty n
weeEnd (No th) = weeEnd th
weeEnd (Su th) = Sy (weeEnd th)
weeEnd  Ze     = Zy

io :: forall m. Natty m -> m <= m
io (Sy n) = Su (io n)
io  Zy    = Ze

class Thinny (f :: Nat -> *) where
  (-<) :: forall n m. f n -> n <= m -> f m
  -- support :: forall n. f n -> Natty n -> Natty ^ n

instance Thinny ((<=) l) where
  th    -< No ph = No (th -< ph)
  No th -< Su ph = No (th -< ph)
  Su th -< Su ph = Su (th -< ph)
  Ze    -< Ze    = Ze
  -- support th _ = weeEnd th :^ th

no :: forall m. Natty m -> Z <= m
no (Sy m) = No (no m)
no  Zy    = Ze

data Cov :: Nat -> Nat -> Nat -> * where
  SN :: Cov l r m -> Cov (S l)    r  (S m)
  NS :: Cov l r m -> Cov    l  (S r) (S m)
  SS :: Cov l r m -> Cov (S l) (S r) (S m)
  ZZ :: Cov Z Z Z

instance Show (Cov l r m) where
  show u = help u "]" where
    help :: forall l r m. Cov l r m -> String -> String
    help (SN u) s = help u ("10." ++ s)
    help (NS u) s = help u ("01." ++ s)
    help (SS u) s = help u ("11." ++ s)
    help ZZ     s = "[" ++ s

covl :: Cov l r m -> l <= m
covl (SN u) = Su (covl u)
covl (NS u) = No (covl u)
covl (SS u) = Su (covl u)
covl  ZZ    = Ze

covr :: Cov l r m -> r <= m
covr (SN u) = No (covr u)
covr (NS u) = Su (covr u)
covr (SS u) = Su (covr u)
covr  ZZ    = Ze

type Cop l r m = Cov l r ^ m

cop :: l <= m -> r <= m -> Cop l r m
cop (No th) (No ph) = case cop th ph of u :^ ps ->    u :^ No ps
cop (No th) (Su ph) = case cop th ph of u :^ ps -> NS u :^ Su ps
cop (Su th) (No ph) = case cop th ph of u :^ ps -> SN u :^ Su ps
cop (Su th) (Su ph) = case cop th ph of u :^ ps -> SS u :^ Su ps
cop  Ze      Ze     =                              ZZ   :^ Ze

data (^) :: (Nat -> *) -> Nat -> * where
  (:^) :: p n -> n <= m -> p ^ m

data B :: (Nat -> *) -> Nat -> * where
  K :: p n     -> B p n
  L :: p (S n) -> B p n

bi :: p ^ S n -> B p ^ n
bi (p :^ No th) = K p :^ th
bi (p :^ Su th) = L p :^ th

data (&) :: (Nat -> *) -> (Nat -> *) -> (Nat -> *) where
  P :: s l -> Cov l r m -> t r -> (s & t) m

(^&^) :: s ^ m -> t ^ m -> (s & t) ^ m
(s :^ th) ^&^ (t :^ ph) = case cop th ph of u :^ ps -> P s u t :^ ps

thicken :: l <= m -> n <= m -> Maybe (l <= n)
thicken (Su th) (No ph) = Nothing
thicken (Su th) (Su ph) = Su <$> thicken th ph
thicken (No th) (Su ph) = No <$> thicken th ph
thicken (No th) (No ph) = thicken th ph
thicken  Ze      Ze     = pure Ze

data Vec :: Nat -> * -> * where
  VN   :: Vec Z x
  (:#) :: Vec n x -> x -> Vec (S n) x

vecL :: Vec n x -> [x] -> [x]
vecL VN ys = ys
vecL (xs :# x) ys = vecL xs (x : ys)

instance Show x => Show (Vec n x) where show xs = show $ vecL xs []

instance Traversable (Vec n) where
  traverse f VN = pure VN
  traverse f (xs :# x) = (:#) <$> traverse f xs <*> f x

instance Foldable (Vec n) where foldMap = foldMapDefault
instance Functor (Vec n) where fmap = fmapDefault

rep :: Natty n -> x -> Vec n x
rep  Zy    x = VN
rep (Sy n) x = rep n x :# x

instance NATTY n => Applicative (Vec n) where
  pure = rep natty
  fs <*> ss = help fs ss where
    help :: forall s t n. Vec n (s -> t) -> Vec n s -> Vec n t
    help VN VN = VN
    help (fs :# f) (ss :# s) = help fs ss :# f s

(?^) :: n <= m -> Vec m x -> Vec n x
No th ?^ (xs :# _) = th ?^ xs
Su th ?^ (xs :# x) = (th ?^ xs) :# x
Ze    ?^    VN     = VN

data Pub :: Nat -> Nat -> Nat -> * where
  Sqr :: n <= l -> n <= m -> n <= r -> Pub l m r

pub :: l <= m -> r <= m -> Pub l m r
pub (No th) (No ph) = case pub th ph of
  Sqr th' ps' ph' -> Sqr th' (No ps') ph'
pub (No th) (Su ph) = case pub th ph of
  Sqr th' ps' ph' -> Sqr th' (No ps') (No ph')
pub (Su th) (No ph) = case pub th ph of
  Sqr th' ps' ph' -> Sqr (No th') (No ps') ph'
pub (Su th) (Su ph) = case pub th ph of
  Sqr th' ps' ph' -> Sqr (Su th') (Su ps') (Su ph')
pub Ze Ze = Sqr Ze Ze Ze


data AddR :: Nat -> Nat -> Nat -> * where
  AddZ :: Natty n    -> AddR n Z n
  AddS :: AddR n l m -> AddR n (S l) (S m)

data Ex :: (Nat -> *) -> * where
  Wit :: Natty n -> p n -> Ex p

data (:*) :: (Nat -> *) -> (Nat -> *) -> (Nat -> *) where
  (:*) :: p n -> q n -> (p :* q) n

add :: Natty n -> Natty l -> Ex (AddR n l)
add n Zy = Wit n (AddZ n)
add n (Sy l) = case add n l of
  Wit m a -> Wit (Sy m) (AddS a)

wksThin :: n <= m -> AddR n l n' -> Ex ((<=) n' :* AddR m l)
wksThin th (AddZ n) = let m' = bigEnd th in Wit m' (th :* AddZ m')
wksThin th (AddS a) = case wksThin th a of
  Wit m' (th :* a) -> Wit (Sy m') (Su th :* AddS a)

thAdd :: AddR a b c -> a <= d -> b <= e -> AddR d e f -> c <= f
thAdd abc ad (No be) (AddS def) = No (thAdd abc ad be def)
thAdd (AddS abc) ad (Su be) (AddS def) = Su (thAdd abc ad be def)
thAdd (AddZ _) ad Ze (AddZ _) = ad
