module Check where

import Syntax
import Indexed
import Natty
import Thinning
import Vec

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
  -- check also that x is different from the names in sg
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
  legit ga Empt th Ze (AddZ n) = pure (ga, Empt, io n)
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
