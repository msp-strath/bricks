{-# OPTIONS --no-unicode #-}
module Brick where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)

----------------------------------------
-- Thinnings
----------------------------------------

data _<=_ : Nat -> Nat -> Set where
  no : forall {n m} -> n <= m -> n <= suc m
  suc : forall {n m} -> n <= m -> suc n <= suc m
  zero : zero <= zero

data [_-_]~_ : forall {l n m} -> l <= n -> n <= m -> l <= m -> Set where
  nr : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m}
      -> [ th - ph ]~ ps
      -> [ th - no ph ]~ no ps
  nl : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m}
      -> [ th - ph ]~ ps
      -> [ no th - suc ph ]~ no ps
  suc : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m}
      -> [ th - ph ]~ ps
      -> [ suc th - suc ph ]~ suc ps
  zero : [ zero - zero ]~ zero

io : forall {m} -> m <= m
io {zero} = zero
io {suc m} = suc io

_-io : forall {n m}(th : n <= m) -> [ th - io ]~ th
no th -io = nl (th -io)
suc th -io = suc (th -io)
zero -io = zero

⟨_⟩ : forall {a b} -> {A : Set a} -> (B : A → Set b) → Set _
⟨_⟩ = Σ _

_~_ = _≡_
<_> = ⟨_⟩
One = ⊤
Sg = Σ
_:*_ : forall {X : Set} -> (X -> Set) -> (X -> Set) -> (X -> Set)
(P :* Q) x = Sg (P x) \ _ -> Q x
infixr 10 _:*_
infix 5 <_>
infix 20 [_-_]~_

co1 : forall {l n m}(th : l <= n)(ph : n <= m) -> ⟨ [ th - ph ]~_ ⟩
co1 th (no ph) = let _ , ps = co1 th ph in _ , nr ps
co1 (no th) (suc ph) = let _ , ps = co1 th ph in _ , nl ps
co1 (suc th) (suc ph) = let _ , ps = co1 th ph in _ , suc ps
co1 zero zero = _ , zero

co1q : forall {l n m}{th : l <= n}{ph : n <= m}(a b : ⟨ [ th - ph ]~_ ⟩) -> a ~ b
co1q (_ , nr a) (_ , nr b) with refl <- co1q (_ , a) (_ , b) = refl
co1q (_ , nl a) (_ , nl b) with refl <- co1q (_ , a) (_ , b) = refl
co1q (_ , suc a) (_ , suc b) with refl <- co1q (_ , a) (_ , b) = refl
co1q (_ , zero) (_ , zero) = refl

thinj : forall {l n m}{ps : l <= m}{ph : n <= m}(a b : ⟨ [_- ph ]~ ps ⟩) -> a ~ b
thinj (_ , nr a) (_ , nr b) with refl <- thinj (_ , a) (_ , b) = refl
thinj (_ , nl a) (_ , nl b) with refl <- thinj (_ , a) (_ , b) = refl
thinj (_ , suc a) (_ , suc b) with refl <- thinj (_ , a) (_ , b) = refl
thinj (_ , zero) (_ , zero) = refl

co2 : forall {x0 x1 x2 x3}
  {th01 : x0 <= x1}{th02 : x0 <= x2}{th13 : x1 <= x3}{th23 : x2 <= x3}
  {th12 : x1 <= x2}{th03 : x0 <= x3}
  -> [ th01 - th12 ]~ th02
  -> [ th01 - th13 ]~ th03
  -> [ th12 - th23 ]~ th13
  -> [ th02 - th23 ]~ th03
co2 a (nr b) (nr c) = nr (co2 a b c)
co2 (nr a) (nr b) (nl c) = nl (co2 a b c)
co2 (nl a) (nl b) (suc c) = nl (co2 a b c)
co2 (suc a) (suc b) (suc c) = suc (co2 a b c)
co2 zero zero zero = zero

assoc03 : forall {x0 x1 x2 x3}
  {th01 : x0 <= x1}{th02 : x0 <= x2}{th13 : x1 <= x3}{th23 : x2 <= x3}
  -> < [ th01 -_]~ th02 :* [_- th23 ]~ th13 >
  -> < [ th01 - th13 ]~_ :* [ th02 - th23 ]~_ >
assoc03 {th01 = th01} {th13 = th13} (_ , a , b)
  with _ , c <- co1 th01 th13
  = _ , c , co2 a c b

assoc02 : forall {x0 x1 x2 x3}
  {th01 : x0 <= x1}{th12 : x1 <= x2}{th03 : x0 <= x3}{th23 : x2 <= x3}
  -> < [ th01 -_]~ th03 :* [ th12 - th23 ]~_ >
  -> < [ th01 - th12 ]~_ :* [_- th23 ]~ th03 >
assoc02 {th01 = th01} {th12} (_ , a , b)
  with _ , c <- co1 th01 th12
  = _ , c , co2 c a b

thinj' : forall {x0 x1 x2 x3}
  {th01 : x0 <= x1}{th02 : x0 <= x2}{th13 : x1 <= x3}{th23 : x2 <= x3}
  {th12 : x1 <= x2}{th03 : x0 <= x3}
  -> [ th01 - th13 ]~ th03
  -> [ th02 - th23 ]~ th03
  -> [ th12 - th23 ]~ th13
  -> [ th01 - th12 ]~ th02
thinj' a b c
  with _ , d , e <- assoc02 (_ , a , c)
  with refl <- thinj (_ , b) (_ , e)
  = d



assoc13 : forall {x0 x1 x2 x3}
  {th01 : x0 <= x1}{th12 : x1 <= x2}{th03 : x0 <= x3}{th23 : x2 <= x3}
  -> < [ th01 - th12 ]~_ :* [_- th23 ]~ th03 >
  -> < [ th01 -_]~ th03 :* [ th12 - th23 ]~_ >
assoc13 {th01 = th01}{th12} {th23 = th23} (th02 , a , b)
  with th13 , c <- co1 th12 th23
  with _ , d , e <- assoc03 (_ , a , c)
  with refl <- co1q (_ , b) (_ , e)
  = _ , d , c


subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y} → x ≡ y → P y → P x
subst P refl px = px

K : ∀{ a } { A : Set a} { x y : A} (p q : x ≡ y) -> p ≡ q
K refl refl = refl

mutual
  data _-Context-_ (dims : Nat) : (length : Nat) -> Set1 where
    eps : dims -Context- 0
    ext : forall {m c n} -> (Gamma : dims -Context- m)
          (Delta : c -Context- n)(th : c <= dims)(ph : n <= m)(v : Sel Delta th ph Gamma)
          (T : [! Delta !] -> Set)
       -> dims -Context- suc m

  [!_!] : forall {d m} -> d -Context- m -> Set
  [! eps !] = One
  [! ext Gamma Delta th ph v T !] = Sg [! Gamma !] \ iz -> T ((proj v iz))

  data Sel : forall {c d n m}(Delta : c -Context- n)(th : c <= d)(ph : n <= m)
              (Gamma : d -Context- m) -> Set1 where
    no   : forall {c c' d n n' m}{Gamma : d -Context- m}
      {Delta : c -Context- n}{Delta' : c' -Context- n'}
      {th : c <= d}{th' : c' <= d}
      {ph : n <= m}{ph' : n' <= m}
      (v : Sel Delta th ph Gamma){v' : Sel Delta' th' ph' Gamma}
      {T' : [! Delta' !] -> Set}
      ->
      Sel Delta th (no ph) (ext Gamma Delta' th' ph' v' T')
              
    zero : Sel eps zero zero eps
    
    
  proj : forall {c d n m}{Delta : c -Context- n}{th : c <= d}{ph : n <= m}
              {Gamma : d -Context- m}
              -> Sel Delta th ph Gamma -> [! Gamma !] -> [! Delta !]
  proj v iz = {!!}


{-
  data OK {dims : Nat} {i : Nat} (th : i <= dims) : forall {m n} -> (ph : n <= m) (Gamma : dims -Context- m) -> Set where
    zero : OK th zero eps
    no : forall {m n i' n'}
       -> {ph : n <= m} {Gamma : dims -Context- m}
       -> {th' : i' <= dims} {ph' : n' <= m}
       -> {v' : OK th' ph' Gamma} {T' : [! v' !]v -> Set}
       -> OK th ph Gamma -> OK th (no ph) (ext Gamma th' ph' v' T')
    suc : forall {m n i' n'}
        -> {ph : n <= m} {Gamma : dims -Context- m}
        -> {th' : i' <= dims} {ph' : n' <= m}
        -> {v : OK th' ph' Gamma} {T : [! v !]v -> Set}
        -> OK th ph Gamma
        -> ⟨ [_- th ]~ th' ⟩
        -> ⟨ [_- ph ]~ ph' ⟩
        -> OK th (suc ph) (ext Gamma th' ph' v T)

  sub : {dims : Nat}{i : Nat}{th : i <= dims} -> forall {m n} -> {ph : n <= m} {Gamma : dims -Context- m} -> OK th ph Gamma
     -> i -Context- n
  sub zero = eps
  sub (no v) = sub v
  sub {Gamma = ext Gamma th' ph' v' T} (suc {T = T} v (th0 , a) (ph0 , b)) =
    let v0 , f = OKOK v v' a b in ext (sub v) th0 ph0 v0 \ iz -> T (f iz)

  [!_!]v : {dims : Nat}{i : Nat}{th : i <= dims} -> forall {m n} -> {ph : n <= m} {Gamma : dims -Context- m} -> OK th ph Gamma
     -> Set
  [! v !]v = [! sub v !]


  OKOK : {d m : Nat}{Gamma : d -Context- m}
    {i : Nat}{th : i <= d} -> forall {n} -> {ph : n <= m} (v : OK th ph Gamma) ->
    {i' : Nat}{th' : i' <= d} -> forall {n'} -> {ph' : n' <= m}(v' : OK th' ph' Gamma) ->
    {th0 : i' <= i} -> [ th0 - th ]~ th' -> {ph0 : n' <= n} -> [ ph0 - ph ]~ ph' ->
    Sg (OK th0 ph0 (sub v)) \ v0 -> [! v0 !]v -> [! v' !]v
  OKOK zero zero a zero = zero , \ _ -> tt
  OKOK (no v) (no v') a (nr b) = OKOK v v' a b
  OKOK (suc v x x1) (no v') a (nl b) = let v0 , f = OKOK v v' a b in no v0 , f
  OKOK (suc v (th1 , x0) (ph1 , x1)) (suc v' (th2 , x2) (ph2 , x3)) a (suc b) = let v0 , f = OKOK v v' a b in
    suc v0 (_ , thinj' x2 x0 a  ) (_ , thinj' x3 x1 b) , \ (iz , i) -> f iz , {!!}

  select : forall {dims : Nat} {i : Nat} (th : i <= dims){m n} -> (ph : n <= m) (Gamma : dims -Context- m)(v : OK th ph Gamma)
        -> [! Gamma !] -> [! v !]v
  select th .zero .eps zero tt = tt
  select th .(no _) .(ext _ _ _ _ _) (no v) (iz , _) = select _ _ _ v iz
  select th .(suc _) .(ext _ _ _ _ _) (suc v x x1) (iz , i) = select _ _ _ v iz , {!!}
-}
{-
  [[_]] : {dims : Nat}{i : Nat}{th : i <= dims} -> forall {m n} -> {ph : n <= m} {Gamma : dims -Context- m} -> OK th ph Gamma -> Set
  [[ zero ]] = ⊤
  [[ no v ]] = [[ v ]]
  [[ suc {v' = v'} {T'} v ⟨th⟩ ⟨ph⟩ ]] =  Σ [[ v ]] \ x -> T' (select v' v ⟨th⟩ ⟨ph⟩ x)

  select : forall {dims} {i} {th : i <= dims} {m} {n} {i'} {n'}
         -> {ph : n <= m} {Gamma : dims -Context- m}
            {th' : i' <= dims} {ph' : n' <= m} (v' : OK th' ph' Gamma)
            (v : OK th ph Gamma) (⟨th⟩ : ⟨ [_- th ]~ th' ⟩)
            (⟨ph⟩ : ⟨ [_- ph ]~ ph' ⟩)
         -> [[ v ]]
         -> [[ v' ]]
  select zero zero ⟨th⟩ ⟨ph⟩ x = tt
  select (no v') (no v) ⟨th⟩ (_ , nr ⟨ph⟩) x = select v' v ⟨th⟩ (_ , ⟨ph⟩) x
  select (no v') (suc v x1 x2) ⟨th⟩ (_ , nl ⟨ph⟩) (x , _)= select v' v ⟨th⟩ (_ , ⟨ph⟩) x
  select (suc {v' = v''} {T'} v' ⟨th'⟩ ⟨ph'⟩) (suc v ⟨th''⟩ ⟨ph''⟩) ⟨th⟩ (_ , suc ⟨ph⟩) (x , t) = ( select v' v ⟨th⟩ (_ , ⟨ph⟩) x) , subst T' (coherence v'' v' ⟨th'⟩ ⟨ph'⟩ v  ⟨th''⟩ ⟨ph''⟩ ⟨th⟩ (_ , ⟨ph⟩) x) t

  coherence : ∀ {dims} {i} {th : i <= dims} {i'} {th' : i' <= dims}
              {m} {n} { i''} {n'} {ph : n <= m} {Gamma : dims -Context- m}
              {th'' : i'' <= dims} {ph' : n' <= m}
              (v'' : OK th'' ph' Gamma)
              (v' : OK th' ph Gamma) (⟨th'⟩ : ⟨ [_- th' ]~ th'' ⟩)
              (⟨ph'⟩ : ⟨ [_- ph ]~ ph' ⟩) {n1} {ph1 : n1 <= m}
              (v : OK th ph1 Gamma) (⟨th''⟩ : ⟨ [_- th ]~ th'' ⟩)
              (⟨ph''⟩ : ⟨ [_- ph1 ]~ ph' ⟩) (⟨th⟩ : ⟨ [_- th ]~ th' ⟩)
              (⟨ph⟩ : ⟨ [_- ph1 ]~ ph ⟩) (x : [[ v ]]) ->
            select v'' v' ⟨th'⟩ ⟨ph'⟩ (select v' v ⟨th⟩ ⟨ph⟩ x) ≡
            select v'' v ⟨th''⟩ ⟨ph''⟩ x
  coherence zero zero ⟨th'⟩ ⟨ph'⟩ zero ⟨th''⟩ ⟨ph''⟩ ⟨th⟩ ⟨ph⟩ x = refl
  coherence (no v'') (no v') ⟨th'⟩ (_ , nr ⟨ph'⟩) (no v) ⟨th''⟩ (_ , nr ⟨ph''⟩) ⟨th⟩ (_ , nr ⟨ph⟩) x = coherence v'' v' ⟨th'⟩ (_ , ⟨ph'⟩) v ⟨th''⟩ (_ , ⟨ph''⟩) ⟨th⟩ (_ , ⟨ph⟩) x
  coherence (no v'') (no v') ⟨th'⟩ (_ , nr ⟨ph'⟩) (suc v x1 x2) ⟨th''⟩ (_ , nl ⟨ph''⟩) ⟨th⟩ (_ , nl ⟨ph⟩) (x , _) = coherence v'' v' ⟨th'⟩ (_ , ⟨ph'⟩) v ⟨th''⟩ (_ , ⟨ph''⟩) ⟨th⟩ (_ , ⟨ph⟩) x
  coherence (no v'') (suc v' x1 x2) ⟨th'⟩ (_ , nl ⟨ph'⟩) (suc v x3 x4) ⟨th''⟩ (_ , nl ⟨ph''⟩) ⟨th⟩ (_ , suc ⟨ph⟩) (x , _) = coherence v'' v' ⟨th'⟩ (_ , ⟨ph'⟩) v ⟨th''⟩ (_ , ⟨ph''⟩) ⟨th⟩ (_ , ⟨ph⟩) x
  coherence (suc {v' = v'''} v'' x1 x2) (suc {v' = v1} v' x3 x4) ⟨th'⟩ (_ , suc ⟨ph'⟩) (suc  {v' = v2} v x5 x6) ⟨th''⟩ (_ , suc ⟨ph''⟩) ⟨th⟩ (_ , suc ⟨ph⟩) (x , t)
    with p <- (coherence v''' v'' x1 x2 v' x3 x4 ⟨th'⟩ (_ , ⟨ph'⟩) (select v' v ⟨th⟩ (_ , ⟨ph⟩) x))
       | q <- (coherence v''' v' x3 x4 v x5 x6 ⟨th⟩ (_ , ⟨ph⟩) x)
       | r <- (coherence v''' v'' x1 x2 v x5 x6 ⟨th''⟩ (_ , ⟨ph''⟩) x)
       | s <- (coherence v'' v' ⟨th'⟩ (_ , ⟨ph'⟩) v ⟨th''⟩ (_ , ⟨ph''⟩) ⟨th⟩ (_ , ⟨ph⟩) x)
    with u <- (select v' v ⟨th⟩ (_ , ⟨ph⟩) x)
    with v <- (select v'' v' ⟨th'⟩ (_ , ⟨ph'⟩) u)
    with refl <- s
    with ql <- select v''' v' x3 x4 u
    with refl <- p
    with refl <- K q r
    = refl

allOK : forall {d m}(Gamma : d -Context- m) -> OK io io Gamma
allOK eps = zero
allOK (ext Gamma th ph v T) = suc (allOK Gamma) (_ , _ -io) (_ , _ -io)

One = ⊤
Sg = Σ

IC : (I O : Set)(S : O -> Set)(P : (o : O) -> S o -> Set)(r : (o : O)(s : S o)(p : P o s) -> I) -> (I -> Set) -> (O -> Set)
IC I O S P r X o = Sg (S o) \ s -> (p : P o s) -> X (r o s p)




BrickI : forall {d m} -> d -Context- m -> Set
BrickI Gamma = [[ allOK Gamma ]]
BrickO : forall {d m} -> d -Context- m -> Set
Brick : forall {d m} -> (Gamma : d -Context- m) -> (BrickI Gamma -> Set) -> (BrickO Gamma) -> Set
Brick {d}{m} Gamma = IC (BrickI Gamma) (BrickO Gamma) {!!} {!!} {!!}
BrickO eps = One
BrickO (ext Gamma th ph v T) = Sg (BrickO Gamma) \ Bz -> {!Brick !}
    
-}

