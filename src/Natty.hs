{-# LANGUAGE DataKinds, GADTs, KindSignatures, RankNTypes, TypeOperators #-}
module Natty where

import Indexed

-- natural numbers, mostly used as a datakind
data Nat = Z | S Nat deriving (Eq, Ord)

natI :: Nat -> Int
natI Z = 0
natI (S n) = 1 + natI n

instance Show Nat where show = show . natI

-- runtime singletons for typelevel nats
data Natty :: Nat -> * where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)

type ExN (p :: Nat -> *) = Ex (Natty :* p)

nattyI :: Natty n -> Int
nattyI Zy = 0
nattyI (Sy n) = 1 + nattyI n

instance Show (Natty n) where show = show . nattyI

nattyEqEh :: Natty n -> Natty m -> Maybe (n == m)
nattyEqEh n m = case trichotomy n m of
   Equal -> pure Refl
   _ -> Nothing

-- the constraint that a singleton exist
-- used in instance declaration, e.g. for Vec
class NATTY n where
  natty :: Natty n

instance NATTY Z where
  natty = Zy
instance NATTY n => NATTY (S n) where
  natty = Sy natty

-- establishes NATTY, given the singleton
nattily :: Natty n -> (NATTY n => t) -> t
nattily Zy t = t
nattily (Sy n) t = nattily n t

-- addition relation, recursing on the right
data AddR :: Nat -> Nat -> Nat -> * where
  AddZ :: Natty n    -> AddR n Z n
  AddS :: AddR n l m -> AddR n (S l) (S m)

add :: Natty n -> Natty l -> ExN (AddR n l)
add n Zy = Ex (n :* AddZ n)
add n (Sy l) = case add n l of
  Ex (m :* a) -> Ex (Sy m :* AddS a)

data Trichotomy :: Nat -> Nat -> * where
  LessThan    :: Natty (S n) -> AddR (S n) l m -> Trichotomy l m
  Equal       :: Trichotomy n n
  GreaterThan :: Natty (S n) -> AddR (S n) l m -> Trichotomy m l

trichotomy :: Natty n -> Natty m -> Trichotomy n m
trichotomy Zy Zy = Equal
trichotomy (Sy n) (Sy m) = case trichotomy n m of
  LessThan d a -> LessThan d (AddS a)
  Equal        -> Equal
  GreaterThan d a -> GreaterThan d (AddS a)
trichotomy d@(Sy n) Zy = GreaterThan d (AddZ d)
trichotomy Zy d@(Sy n) = LessThan d (AddZ d)
