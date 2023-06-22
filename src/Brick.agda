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


⟨_⟩ : forall {a b} -> {A : Set a} -> (B : A → Set b) → Set _
⟨_⟩ = Σ _

subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y} → x ≡ y → P y → P x
subst P refl px = px

K : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) -> p ≡ q
K refl refl = refl

mutual
  data _-Context-_ (dims : Nat) : (length : Nat) -> Set1 where
    eps : dims -Context- 0
    ext : forall {m i n} ->
          (Gamma : dims -Context- m)
          (th : i <= dims) (ph : n <= m)
          (v : OK th ph Gamma)
          (T : [[ v ]] -> Set)
        -> dims -Context- suc m

  data OK {dims i : Nat} (th : i <= dims) : forall {m n} -> (ph : n <= m) (Gamma : dims -Context- m) -> Set where
    zero : OK th zero eps
    no : forall {m n i' n'}
       -> {ph : n <= m} {Gamma : dims -Context- m}
       -> {th' : i' <= dims} {ph' : n' <= m}
       -> {v' : OK th' ph' Gamma} {T' : [[ v' ]] -> Set}
       -> OK th ph Gamma -> OK th (no ph) (ext Gamma th' ph' v' T')
    suc : forall {m n i' n'}
        -> {ph : n <= m} {Gamma : dims -Context- m}
        -> {th' : i' <= dims} {ph' : n' <= m}
        -> {v' : OK th' ph' Gamma} {T' : [[ v' ]] -> Set}
        -> OK th ph Gamma
        -> ⟨ [_- th ]~ th' ⟩
        -> ⟨ [_- ph ]~ ph' ⟩
        -> OK th (suc ph) (ext Gamma th' ph' v' T')

  [[_]] : {dims i : Nat} {th : i <= dims} ->
          forall {m n} -> {ph : n <= m} {Gamma : dims -Context- m} -> OK th ph Gamma -> Set
  [[ zero ]] = ⊤
  [[ no v ]] = [[ v ]]
  [[ suc {v' = v'} {T'} v ⟨th⟩ ⟨ph⟩ ]] =  Σ [[ v ]] \ x -> T' (select v' v ⟨th⟩ ⟨ph⟩ x)

  select : forall {dims} {i} {m} {n} {i'} {n'}
         -> {Gamma : dims -Context- m}
            {th' : i' <= dims} {ph' : n' <= m} (v' : OK th' ph' Gamma)
            {th : i <= dims}   {ph : n <= m}   (v : OK th ph Gamma)
            (⟨th⟩ : ⟨ [_- th ]~ th' ⟩) (⟨ph⟩ : ⟨ [_- ph ]~ ph' ⟩)
         -> [[ v ]]
         -> [[ v' ]]
  select zero zero ⟨th⟩ ⟨ph⟩ x = tt
  select (no v') (no v) ⟨th⟩ (_ , nr ⟨ph⟩) x = select v' v ⟨th⟩ (_ , ⟨ph⟩) x
  select (no v') (suc v x1 x2) ⟨th⟩ (_ , nl ⟨ph⟩) (x , _)= select v' v ⟨th⟩ (_ , ⟨ph⟩) x
  select (suc {v' = v''} {T'} v' ⟨th'⟩ ⟨ph'⟩) (suc v ⟨th''⟩ ⟨ph''⟩) ⟨th⟩ (_ , suc ⟨ph⟩) (x , t)
    = ( select v' v ⟨th⟩ (_ , ⟨ph⟩) x) , subst T' (coherence v'' v' ⟨th'⟩ ⟨ph'⟩ v  ⟨th''⟩ ⟨ph''⟩ ⟨th⟩ (_ , ⟨ph⟩) x) t

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
