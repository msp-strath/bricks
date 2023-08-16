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

Fin = suc zero <=_

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

_×_ : forall {a b c} -> {A : Set a} ->
      (B : A → Set b) (C : A → Set c) → A → Set _
(B × C) a = Σ (B a) λ _ → C a


subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y} → x ≡ y → P y → P x
subst P refl px = px

K : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) -> p ≡ q
K refl refl = refl


interleaved mutual

  -- declarations
  data _-Context-_ (dims : Nat) : (length : Nat) -> Set1
  [[_]] : {dims m : Nat} (Gamma : dims -Context- m) -> Set

  data _<=[_∣_]_ :
    {wdims ldims wlen llen : Nat}
    (Gamma : wdims -Context- wlen)
    (th : wdims <= ldims) (ph : wlen <= llen)
    (Delta : ldims -Context- llen) ->
    Set1

  --data
  _<=[_]_ :
    {wdims wlen ldims llen : Nat}
    {Gamma : wdims -Context- wlen} ->
    {th : wdims <= ldims} {ph : wlen <= llen}
    {Delta : ldims -Context- llen} ->
    [[ Gamma ]] ->
    Gamma <=[ th ∣ ph ] Delta ->
    [[ Delta ]] ->
    Set


  -- 1. empty contexts
  data _-Context-_ dims where
    eps : dims -Context- 0

  [[ eps ]] = ⊤

  data _<=[_∣_]_ where
    zero : {wdims ldims : Nat} {th : wdims <= ldims} ->
           eps <=[ th ∣ zero ] eps

  tt <=[ zero ] tt = ⊤

  -- 2. context extension
  data _-Context-_ dims where
    ext : forall {wdims wlen llen} ->
          (Gamma : dims -Context- llen)
          {th : wdims <= dims} {ph : wlen <= llen}
          {Delta : wdims -Context- wlen}
        -> Delta <=[ th ∣ ph ] Gamma
        -> (T : [[ Delta ]] -> Set)
        -> dims -Context- suc llen

  [[ ext Gamma Ph T ]]
    = Σ [[ Gamma ]] λ gamma → ⟨ (_<=[ Ph ] gamma) × T ⟩

  data _<=[_∣_]_ where
    no : {wdims ldims wlen llen : Nat}
         {Gamma : wdims -Context- wlen}
         {th : wdims <= ldims} {ph : wlen <= llen}
         {Delta : ldims -Context- llen} ->

         -- initial selection
         Gamma <=[ th ∣ ph ] Delta ->

         forall {fdims flen} ->
         {fth : fdims <= ldims} {fph : flen <= llen}
         {Xi : fdims -Context- flen} ->
         {FPh : Xi <=[ fth ∣ fph ] Delta}
         {T : [[ Xi ]] -> Set} ->

         -- throwing T away
         Gamma <=[ th ∣ no ph ] ext Delta FPh T

    suc : {wdims ldims wlen llen : Nat}
          {Gamma : wdims -Context- wlen}
          {th : wdims <= ldims} {ph : wlen <= llen}
          {Delta : ldims -Context- llen} ->

          -- initial selection to be extended on both sides
          Gamma <=[ th ∣ ph ] Delta ->

          -- dependencies of the extension
          forall {fdims flen} -> {Xi : fdims -Context- flen} ->

          -- compatible selections of dimensions
          {wfth : fdims <= wdims} {lfth : fdims <= ldims} ->
          [ wfth - th ]~ lfth ->

          -- compatible selections of dependencies
          {wfph : flen <= wlen} {lfph : flen <= llen} ->
          [ wfph - ph ]~ lfph ->

          {wFPh : Xi <=[ wfth ∣ wfph ] Gamma}
          {lFPh : Xi <=[ lfth ∣ lfph ] Delta}

          {T : [[ Xi ]] -> Set} ->

          ext Gamma wFPh T <=[ th ∣ suc ph ] ext Delta lFPh T

  gamma <=[ no Th ] (delta , _) = gamma <=[ Th ] delta
  (gamma , xi , _ , t) <=[ suc Th v w {T = T} ] (delta , xi' , _ , t') =
    Σ (gamma  <=[ Th ] delta)
    \ _ -> _≡_  {_} {⟨ T ⟩} (_ , t) (_ , t')

triangle :  forall {wdims} {ldims} {th : wdims <= ldims} {wlen} {llen}
              {Gamma : wdims -Context- wlen} {ph : wlen <= llen}
              {Delta : ldims -Context- llen} (Ph : Gamma <=[ th ∣ ph ] Delta)
              {xs : [[ Delta ]]} {ys : [[ Gamma ]]}
              (q : ys <=[ Ph ] xs) {fdims} {flen} {Xi : fdims -Context- flen}
              {wfth : fdims <= wdims} {lfth : fdims <= ldims}
              (v : [ wfth - th ]~ lfth) {wfph : flen <= wlen}
              {lfph : flen <= llen} (w : [ wfph - ph ]~ lfph)
              (wFPh : Xi <=[ wfth ∣ wfph ] Gamma)
              (lFPh : Xi <=[ lfth ∣ lfph ] Delta) {xi : [[ Xi ]]}
              (p : xi <=[ lFPh ] xs) ->
                   xi <=[ wFPh ] ys
triangle (no Ph) q v (nr w) wFPh (no lFPh) p = triangle Ph q v w wFPh lFPh p
triangle (suc Ph _ _) (q , _) v (nl w) (no wFPh) (no lFPh) p = triangle Ph q v w wFPh lFPh p
triangle (suc Ph _ _) (q , refl) v (suc w) (suc wFPh _ _) (suc lFPh _ _) (p , refl)
  = triangle Ph q v w wFPh lFPh p , refl
triangle zero q v zero zero zero p = _


select : {wdims ldims wlen llen : Nat}
    {Gamma : wdims -Context- wlen}
    {th : wdims <= ldims}{ph : wlen <= llen}
    {Delta : ldims -Context- llen}
    (Ph : Gamma <=[ th ∣ ph ] Delta) ->
    (xs : [[ Delta ]]) ->
    ⟨ _<=[ Ph ] xs ⟩
select zero tt = _
select (no Ph) (xs , _) = select Ph xs
select (suc Ph v w {wFPh} {lFPh}) (xs , xi , p , t)
  with ys , q <- select Ph xs
  = (ys , xi , triangle Ph q v w wFPh lFPh p , t) , q , refl


data Vec : Nat -> Set -> Set where
  [] : forall {a} -> Vec zero a
  _::_ : forall {n a} -> a -> Vec n a -> Vec (suc n) a

data Indices : forall {n} -> Vec n Nat -> Set where
  [] : Indices []
  _::_ : forall {n d} {ds : Vec n Nat} ->
         Fin d -> Indices ds -> Indices (d :: ds)

data _<=[_]v_ {a} :
  forall {n m} ->
  Vec n a -> n <= m ->
  Vec m a -> Set where
  zero : [] <=[ zero ]v []
  no   : forall {n m vs w ws} {th : n <= m} ->
         vs <=[ th ]v ws -> vs <=[ no th ]v (w :: ws)
  suc  : forall {n m vs w ws} {th : n <= m} ->
         vs <=[ th ]v ws -> (w :: vs) <=[ suc th ]v (w :: ws)

selectI : forall {n m ns' ns} {th : n <= m} ->
          Indices ns -> ns' <=[ th ]v ns -> Indices ns'
selectI ks zero = ks
selectI (_ :: ks) (no th) = selectI ks th
selectI (k :: ks) (suc th) = k :: selectI ks th

record BrickTy : Set1 where
  constructor mkBrickTy
  field
    dims   : Nat
    {len}  : Nat
    ctx    : dims -Context- len
    cellTy : [[ ctx ]] -> Set
open BrickTy

Headers : forall {dims len} ->
          (ctx : dims -Context- len) ->
          Set

selectH :
  forall {wdims wlen ldims llen}
  {ph : wlen <= llen}
  {th : wdims <= ldims}
  {Gamma : ldims -Context- llen} ->
  {Delta : wdims -Context- wlen} ->
  Delta <=[ th ∣ ph ] Gamma ->
  Headers Gamma ->
  Headers Delta

Brick : (ty : BrickTy) → Headers (ctx ty) → Set

Headers eps = ⊤
Headers (ext ctx sel T) =
  let Hds = Headers ctx in
  Σ Hds λ hds → Brick (mkBrickTy _ _ T) (selectH sel hds)

selectH zero hds = hds
selectH (no sel) (hds , _) = selectH sel hds
selectH (suc sel cod col) (hds , brk)
  = selectH sel hds
  , subst (Brick _ ) {!!} brk

sizedH : forall {dims len} ->
    (ctx : dims -Context- len) ->
    Headers ctx -> Vec dims Nat -> Set

lookup : forall {dims len} {ctx : dims -Context- len} {ns}
         (hds : Headers ctx) -> sizedH ctx hds ns ->
         Indices ns -> [[ ctx ]]

Brick ty hds
  = Σ (Vec (dims ty) Nat) \ ns ->
    Σ (sizedH (ctx ty) hds ns) \ ok ->
    forall (ks : Indices ns) ->
    cellTy ty (lookup hds ok ks)


sizedH eps hds ns = ⊤
sizedH (ext ctx {th = th} sel T) (hds , (ns' , _ , _)) ns
  = Σ (sizedH ctx hds ns) \ _ -> ns' <=[ th ]v ns

lookup<= : forall {ldims wdims llen wlen ns ns' th ph} ->
  {Gamma   : ldims -Context- llen}
  {Delta : wdims -Context- wlen}
  (sel   : Delta <=[ th ∣ ph ] Gamma) ->
  (hds : Headers Gamma) ->
  (shds  : sizedH Gamma hds ns) ->
  (shds' : sizedH Delta (selectH sel hds) ns') ->
  (ks : Indices ns) ->
  (sbrk  : ns' <=[ th ]v ns) ->
  lookup (selectH sel hds) shds' (selectI ks sbrk)
    <=[ sel ]
  lookup hds shds ks

lookup {ctx = eps} hds shds ks = _
lookup {ctx = ext ctx sel T} (hds , (ns' , shds' , f)) (shds , sbrk) ks
  = lookup hds shds ks
  , _ , lookup<= sel hds shds shds' ks sbrk
  , f (selectI ks sbrk)

lookup<= zero hds shds shds' ks sbrk = _
lookup<= (no sel) (hds , _) (shds , _) shds' ks sbrk
  = lookup<= sel hds shds shds' ks sbrk
lookup<= (suc sel x x1) (hds , brk) (shds , sbrk1) (shds' , sbrk1') ks sbrk
  = lookup<= sel hds shds shds' ks sbrk
  , {!!}

{-
_∋[_,_] :
  forall {dims len} {ctx : dims -Context- len} ->
  [[ ctx ]] → Vec dims Nat → Headers ctx → Set
_∋[_,_] {ctx = eps} vs ns hds = {!!}
_∋[_,_] {ctx = ext ctx sel T} vs ns (hds , brk)
  = {!!}
-}


`listTy : Set → BrickTy
`listTy a = mkBrickTy 1 eps (\ _ -> a)

`list : Set → Set
`list a = Brick (`listTy a) _

`nil : ∀ {a} → `list a
`nil = (0 :: []) , (_ , \ where (() :: _))

`cons : ∀ {a} → a → `list a → `list a
`cons x (n :: [] , _ , xs)
  = suc n :: [] , _ , \ where
      (suc k :: _) -> x
      (no k :: _)  -> xs (k :: [])

_ : `list Nat
_ = `cons 1 (`cons 2 `nil)

`allTy : forall {a : Set} -> (a -> Set) → BrickTy
`allTy {a} p =
  mkBrickTy 1 (ext eps (zero {th = suc zero}) \ _ -> a)
  λ (_ , _ , _ , x) → p x

`all : forall {a : Set} → (a → Set) → (`list a → Set)
`all p xs = Brick (`allTy p) (_ , xs)

`nilp : forall {a : Set} {p : a -> Set} ->
        `all p `nil
`nilp = 0 :: [] , ((_ , suc zero) , \ where (() :: []))

`consp : forall {a : Set} {p : a -> Set} {x xs} ->
         p x -> `all p xs -> `all p (`cons x xs)
`consp {xs = n' :: [] , _ , xs} px (n :: [] , (_ , suc zero) , pxs)
  = suc n :: []
  , (_ , suc zero)
  ,  \ where
      (suc k :: _) -> px
      (no k :: _)  -> pxs (k :: [])
