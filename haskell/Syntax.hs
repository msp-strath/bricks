module Syntax where

import Indexed
import Natty
import Thinning
import Vec

data Ty :: Nat -> * where
  Record :: Sg n m -> Ty n
  Brick ::
       Natty d -- how many dimensions has the brick
    -> Ty m  -- what is the cell type of the brick?
    -> Hd d n k m -- what are the headers of the brick?
    -> Ty n
  -- note Brick isn't properly cdb yet

-- left-nested record signatures (should they be right-nested?)
data Sg :: Nat -> Nat -> * where
  One :: Sg n n
  Field :: Sg n m -> (String, Ty m) -> Sg n (S m)

data Hd :: Nat -- dimensions
        -> Nat -- n free on the left
        -> Nat -- k many fields
        -> Nat -- n + k
        -> *
        where
  Empt :: Hd d n Z n
  Grow :: Hd d n k m -- existing fields
       -> i <= d  -- choose dimensions
       -> l <= k  -- choose permitted dependencies
       -> AddR n l s  -- compute extended scope
       -> Ty s    -- header cell type
       -> Ch n    -- header brick
       -> Hd d n (S k) (S m)

hdAddR :: Natty n -> Hd d n k m -> AddR n k m
hdAddR n Empt = AddZ n
hdAddR n (Grow hz _ _ _ _ _) = AddS (hdAddR n hz)

data Sy :: Nat -> * where
  V :: S Z <= n -> Sy n
  (:::) :: Ch n -> Ty n -> Sy n

data Ch :: Nat -> * where
  N    :: Ch n
  (:&) :: Ch n -> Ch n -> Ch n
  Br   :: Natty d -> Vec d (Ch n) -> Ch n -> Ch n
  E    :: Sy n -> Ch n

instance Thinny Ty where
  Record sg -< th = help th sg (const Record) where
    help :: forall n n' m t. n <= m -> Sg n n'
         -> (forall m'. n' <= m' -> Sg m m' -> t)
         -> t
    help th  One              k = k th One
    help th (Field sg (x, t)) k = help th sg $ \ th sg ->
      k (Su th) (Field sg (x, t -< th))
  Brick d t hz -< th = help th hz (\ ph hz -> Brick d (t -< ph) hz) where
    help :: forall d k n n' m t. n <= m -> Hd d n k n'
         -> (forall m'. n' <= m' -> Hd d m k m' -> t)
         -> t
    help th  Empt             k = k th Empt
    help th (Grow hz i d a s h) k = help th hz $ \ ph hz ->
      case wksThin th (weeEnd d) a of
        Ex (m :* ps :* a') ->
          k (Su ph) (Grow hz i d a' (s -< ps) (h -< th))

    wksThin :: forall n m l n' . n <= m -> Natty l -> AddR n l n' -> ExN ((<=) n' :* AddR m l)
    wksThin th l a = case add (bigEnd th) l of
      Ex (m' :* a') -> Ex (m' :* thAdd a th (io l) a' :* a')


instance Thinny Ch where
  N -< th = N
  (s :& t) -< th = (s -< th) :& (t -< th)
  Br d nz x -< th = Br d ((-< th) <$> nz) (x -< th)
  E e -< th = E (e -< th)

instance Thinny Sy where
  V i -< th = V (i -< th)
  (t ::: ty) -< th = (t -< th) ::: (ty -< th)

data m :=> n = Subst
  { getSubst :: Vec m (Sy n)
  , codSubst :: Natty n}

instance Thinny ((:=>) m) where
  Subst ez _ -< th = Subst ((-< th) <$> ez) (bigEnd th)

wkSubst :: m :=> n -> S m :=> S n
wkSubst (Subst ez n) = Subst (((-< No (io n)) <$> ez) :# V (Su (no n))) (Sy n)

class Substy (f :: Nat -> *) where
  (//) :: f m -> m :=> n -> f n

instance Substy ((:=>) m) where
 Subst ez _ // sig = Subst ((// sig) <$> ez) (codSubst sig)

instance Substy Sy where
  V i // Subst ez _ = vonly (i ?^ ez)
  (t ::: ty) // sig = (t // sig) ::: (ty // sig)

instance Substy Ch where
  N // _ = N
  (t :& s) // sig = (t // sig) :& (s // sig)
  Br d nz x // sig = Br d ((// sig) <$> nz) (x // sig)
  E t // sig = E (t // sig)

instance Substy Ty where
  Record rh // sig = help sig rh (const Record) where
    help :: forall n n' m t. n :=> m -> Sg n n'
         -> (forall m'. n' :=> m' -> Sg m m' -> t)
         -> t
    help sig One              k = k sig One
    help sig (Field rh (x, t)) k = help sig rh $ \ sig rh ->
      k (wkSubst sig) (Field rh (x, t // sig))
  Brick d t hz // sig = help sig hz (\ tau hz -> Brick d (t // tau) hz) where
    help :: forall d k n n' m t. n :=> m -> Hd d n k n'
         -> (forall m'. n' :=> m' -> Hd d m k m' -> t)
         -> t
    help sig  Empt             k = k sig Empt
    help sig (Grow hz i d a s h) k = help sig hz $ \ tau hz ->
      case wksSubst sig a of
        Ex (m :* ups :* a') ->
          k (wkSubst tau) (Grow hz i d a' (s // ups) (h // sig))

    wksSubst :: forall n m l n' . n :=> m -> AddR n l n' -> ExN ((:=>) n' :* AddR m l)
    wksSubst sig (AddZ n) = let m = codSubst sig in Ex (m :* sig :* AddZ m)
    wksSubst sig (AddS a) = case wksSubst sig a of
      Ex (m' :* sig' :* a') -> Ex (Sy m' :* wkSubst sig' :* AddS a')
