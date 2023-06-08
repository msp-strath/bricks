{-# LANGUAGE DataKinds, GADTs, TypeOperators, RankNTypes, KindSignatures #-}

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
      case wksThin th a of
        Wit m (ps :* a') ->
          k (Su ph) (Grow hz i d a' (s -< ps) (h -< th))
  {-
  support (Record sg) n = snd (help n sg) where
    help :: forall n m. Natty n -> Sg n m -> ((n <= m, Natty m), Natty ^ n)
    help n One = ((io n, n), Zy :^ no n)
    help n (Field sg (x, s)) = case help n sg of
      ((ph, m), (_ :^ la)) -> case support s m of
        (_ :^ rh) -> case pub rh ph of
          Sqr _ _ rh' -> case cop la rh' of
            _ :^ mu -> ((No ph, Sy m), weeEnd mu :^ mu)
  -}

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
goodHd ga d (Grow hz th ph a s h) = do
  de <- goodHd ga d hz
  -- but de is not the right scope for s
  -- make "legit" do that computation
  (xi, gz, ps) <- legit ga hz th ph a
  goodTy xi s
  let hty = Brick (weeEnd th) s gz
  goodCh ga hty h
  pure (push de (s -< ps))
 where
  legit :: Cx n -> Hd d n k m -> i <= d -> l <= k -> AddR n l s
        -> Maybe (Cx s, Hd i n l s, s <= m)
  legit ga Empt th ph (AddZ n) = pure (ga, Empt, io n)
  legit ga (Grow hz th' ph' a' s' h') th (No ph) a = do
    (xi, gz, ps) <- legit ga hz th ph a
    pure (xi, gz, No ps)
  legit ga (Grow hz th' ph' a' s' h') th (Su ph) (AddS a) = do
    (xi, gz, ps) <- legit ga hz th ph a
    th0 <- thicken th' th
    ph0 <- thicken ph' ph
    pure (push xi (s' -< thAdd a' (io (snd ga)) ph0 a), Grow gz th0 ph0 a' s' h', Su ps)

goodCh :: Cx n -> Ty n -> Ch n -> Maybe ()
goodCh ga (Record One) N = pure ()
goodCh ga _ _ = Nothing
