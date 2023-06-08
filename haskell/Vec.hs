module Vec where

import Natty
import Thinning
import Data.Traversable

-- snoc vectors
data Vec :: Nat -> * -> * where
  VN   :: Vec Z x
  (:#) :: Vec n x -> x -> Vec (S n) x

vecL :: Vec n x -> [x] -> [x]
vecL VN ys = ys
vecL (xz :# x) ys = vecL xz (x : ys)

instance Show x => Show (Vec n x) where show xz = show $ vecL xz []

instance Traversable (Vec n) where
  traverse f VN = pure VN
  traverse f (xz :# x) = (:#) <$> traverse f xz <*> f x

instance Foldable (Vec n) where foldMap = foldMapDefault
instance Functor (Vec n) where fmap = fmapDefault

vrep :: Natty n -> x -> Vec n x
vrep  Zy    x = VN
vrep (Sy n) x = vrep n x :# x

vzap :: forall s t n. Vec n (s -> t) -> Vec n s -> Vec n t
vzap VN VN = VN
vzap (fz :# f) (sz :# s) = vzap fz sz :# f s

-- Vec n is applicative only if we know n at runtime
instance NATTY n => Applicative (Vec n) where
  pure = vrep natty
  (<*>) = vzap

instance Semigroup x => Semigroup (Vec n x) where
  xz <> yz = fmap (<>) xz `vzap` yz

instance (NATTY n, Monoid x) => Monoid (Vec n x) where
  mempty = pure mempty
  mappend = (<>)

vappend :: AddR l n m -> Vec l x -> Vec n x -> Vec m x
vappend (AddZ _) xz VN = xz
vappend (AddS a) xz (yz :# y) = vappend a xz yz :# y

-- Vec - x is a functor from (<=)^op to (->)
(?^) :: n <= m -> Vec m x -> Vec n x
No th ?^ (xs :# _) = th ?^ xs
Su th ?^ (xs :# x) = (th ?^ xs) :# x
Ze    ?^    VN     = VN
