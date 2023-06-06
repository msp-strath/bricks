{-# LANGUAGE DataKinds, GADTs, TypeOperators #-}

module Brick where

import CoDeBruijn -- this file is de Bruijn, nvm

data Ty :: Nat -> * where
  Record :: Sg n m -> Ty n
  Brick ::
       Natty d -- how many dimensions has the brick
    -> Ty m  -- what is the cell type of the brick?
    -> Hd d n k m -- what are the headers of the brick?
    -> Ty n
  -- note Brick isn't properly cdb yet

data Sg :: Nat -> Nat -> * where
  One :: Sg n n
  Field :: Sg n m -> (String, Ty m) -> Sg n (S m)

data Hd :: Nat -- dimensions
        -> Nat -- n free on the left 
        -> Nat -- k many fields
        -> Nat -- n + k free on the right
        -> *
        where
  Empt :: Hd d n Z n
  Grow :: Hd d n k m -- existing fields
       -> i <= d  -- choose dimensions
       -> l <= k  -- choose permitted dependencies
       -> Ty m    -- header cell type (yikes at m!)
       -> Ch n    -- header
       -> Hd d n (S k) (S m)

data Sy :: Nat -> * where
  V :: S Z <= n -> Sy n
  (:::) :: Ch n -> Ty n -> Sy n

data Ch :: Nat -> * where
  N    :: Ch n
  (:&) :: Ch n -> Ch n -> Ch n
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
    help th (Grow hz i d s h) k = help th hz $ \ ph hz ->
      k (Su ph) (Grow hz i d (s -< ph) (h -< th))

instance Thinny Ch where
  N -< th = N
  (s :& t) -< th = (s -< th) :& (t -< th)
  E e -< th = E (e -< th)

instance Thinny Sy where
  V i -< th = V (i -< th)
  (t ::: ty) -< th = (t -< th) ::: (ty -< th)


type Cx n = (Vec n (Ty n), Natty n)

push :: Cx n -> Ty n -> Cx (S n)
push (ga, n) s = ((-< No (io n)) <$> (ga :# s), Sy n)

goodTy :: Cx n -> Ty n -> Maybe ()
goodTy ga (Record sg) = () <$ goodSg ga sg
goodTy ga (Brick d t hz) = do
  ga <- goodHd ga d hz
  goodTy ga t
-- goodTy ga t = Nothing

goodSg :: Cx n -> Sg n m -> Maybe (Cx m)
goodSg ga One = pure ga
goodSg ga (Field sg (x, s)) = do
  ga <- goodSg ga sg
  goodTy ga s
  pure (push ga s)

goodHd :: Cx n -> Natty d -> Hd d n k m -> Maybe (Cx m)
goodHd ga d Empt = pure ga
goodHd ga d (Grow hz th ph s h) = do
  de <- goodHd ga d hz
  goodTy de s
  legit d hz th ph
  -- check the support of s
  -- check h
  pure (push de s)
 where
  legit :: Natty d -> Hd d n k m -> i <= d -> l <= k -> Maybe ()
  legit _ Empt _ Ze = pure ()
  legit d (Grow hz th' ph' _ _) th (No ph) = legit d hz th ph
  legit d (Grow hz th' ph' _ _) th (Su ph) = do
    thicken th' th
    thicken ph' ph
    legit d hz th ph
