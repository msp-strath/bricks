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

select : {wdims ldims wlen llen : Nat}
    {Gamma : wdims -Context- wlen}
    {th : wdims <= ldims}{ph : wlen <= llen}
    {Delta : ldims -Context- llen}
    (Ph : Gamma <=[ th ∣ ph ] Delta) ->
    (xs : [[ Delta ]]) ->
    ⟨ _<=[ Ph ] xs ⟩

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

select zero tt = _
select (no Ph) (xs , _) = select Ph xs
select (suc Ph v w {wFPh} {lFPh}) (xs , xi , p , t)
  with ys , q <- select Ph xs
  = (ys , xi , triangle Ph q v w wFPh lFPh p , t) , q , refl

triangle (no Ph) q v (nr w) wFPh (no lFPh) p = triangle Ph q v w wFPh lFPh p
triangle (suc Ph _ _) (q , _) v (nl w) (no wFPh) (no lFPh) p = triangle Ph q v w wFPh lFPh p
triangle (suc Ph _ _) (q , refl) v (suc w) (suc wFPh _ _) (suc lFPh _ _) (p , refl)
  = triangle Ph q v w wFPh lFPh p , refl
triangle zero q v zero zero zero p = _
