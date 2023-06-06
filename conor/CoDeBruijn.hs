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

instance Thinny ((<=) l) where
  th    -< No ph = No (th -< ph)
  No th -< Su ph = No (th -< ph)
  Su th -< Su ph = Su (th -< ph)
  Ze    -< Ze    = Ze

no :: forall m. Natty m -> Z <= m
no (Sy m) = No (no m)
no  Zy    = Ze

data Cov :: Nat -> Nat -> Nat -> * where
  SN :: Cov l m r -> Cov (S l) (S m)    r
  NS :: Cov l m r -> Cov    l  (S m) (S r)
  SS :: Cov l m r -> Cov (S l) (S m) (S r)
  ZZ :: Cov Z Z Z

instance Show (Cov l m r) where
  show u = help u "]" where
    help :: forall l m r. Cov l m r -> String -> String
    help (SN u) s = help u ("10." ++ s)
    help (NS u) s = help u ("01." ++ s)
    help (SS u) s = help u ("11." ++ s)
    help ZZ     s = "[" ++ s

covl :: Cov l m r -> l <= m
covl (SN u) = Su (covl u)
covl (NS u) = No (covl u)
covl (SS u) = Su (covl u)
covl  ZZ    = Ze

covr :: Cov l m r -> r <= m
covr (SN u) = No (covr u)
covr (NS u) = Su (covr u)
covr (SS u) = Su (covr u)
covr  ZZ    = Ze

data Cop :: Nat -> Nat -> Nat -> * where
  Cop :: Cov l n r -> n <= m -> Cop l m r
instance Show (Cop l m r) where
  show (Cop u ps) = "Cop " ++ show u ++ " " ++ show ps

cop :: l <= m -> r <= m -> Cop l m r
cop (No th) (No ph) = case cop th ph of Cop u ps -> Cop u (No ps)
cop (No th) (Su ph) = case cop th ph of Cop u ps -> Cop (NS u) (Su ps)
cop (Su th) (No ph) = case cop th ph of Cop u ps -> Cop (SN u) (Su ps)
cop (Su th) (Su ph) = case cop th ph of Cop u ps -> Cop (SS u) (Su ps)
cop  Ze      Ze     = Cop ZZ Ze

data (^) :: (Nat -> *) -> Nat -> * where
  (:^) :: p n -> n <= m -> p ^ m

data B :: (Nat -> *) -> Nat -> * where
  K :: p n     -> B p n
  L :: p (S n) -> B p n

bi :: p ^ S n -> B p ^ n
bi (p :^ No th) = K p :^ th
bi (p :^ Su th) = L p :^ th

data (&) :: (Nat -> *) -> (Nat -> *) -> (Nat -> *) where
  P :: s l -> Cov l m r -> t r -> (s & t) m

(^&^) :: s ^ m -> t ^ m -> (s & t) ^ m
(s :^ th) ^&^ (t :^ ph) = case cop th ph of Cop u ps -> P s u t :^ ps

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
