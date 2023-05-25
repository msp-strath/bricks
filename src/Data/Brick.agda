module Data.Brick where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)

data Bottom : Set where

record ⊥ : Set where
  field
   .bottom : Bottom

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

private
  variable
    l m n n₀ n₁ : Nat

data _⊆_ : (m n : Nat) → Set where
  drop : m ⊆ n → m ⊆ suc n
  suc  : m ⊆ n → suc m ⊆ suc n
  zero : zero ⊆ zero

ι : m ⊆ m
ι {zero } = zero
ι {suc _} = suc ι

_⊎_ : ∀ {a} (A B : Set a) → Set a
A ⊎ B = Σ Bool λ where
  true → B
  false → A

Dec : ∀ {p} (P : Set p) → Set p
Dec P = (P → ⊥) ⊎ P

pattern yes p = true , p
pattern no ¬p = false , ¬p

private
  variable
    l⊆n : l ⊆ n
    n⊆m : n ⊆ m
    l⊆m : l ⊆ m

data _⨾_≈_ : l ⊆ n → n ⊆ m → l ⊆ m → Set where
  dropʳ :      l⊆n ⨾      n⊆m ≈      l⊆m →
               l⊆n ⨾ drop n⊆m ≈ drop l⊆m
  dropˡ :      l⊆n ⨾      n⊆m ≈      l⊆m →
          drop l⊆n ⨾ suc  n⊆m ≈ drop l⊆m
  suc   :      l⊆n ⨾      n⊆m ≈      l⊆m →
          suc  l⊆n ⨾ suc  n⊆m ≈ suc  l⊆m
  zero :  zero     ⨾ zero     ≈ zero

private
  variable
    a b p q : Level
    A : Set a

⟨_⟩ : (B : A → Set b) → Set _
⟨_⟩ = Σ _

_×_ : (A : Set a) (B : Set b) → Set _
A × B = Σ A (λ _ → B)

_∩_ : (P : A → Set p) (Q : A → Set q) → (A → Set _)
(P ∩ Q) a = P a × Q a

infixr 4 -,_
pattern -,_ prf = _,_ _ prf

_⨾_ : (l⊆n : l ⊆ n) (n⊆m : n ⊆ m) → ⟨ l⊆n ⨾ n⊆m ≈_ ⟩
l⊆n      ⨾ drop n⊆m = -, dropʳ (snd (l⊆n ⨾ n⊆m))
drop l⊆n ⨾ suc n⊆m  = -, dropˡ (snd (l⊆n ⨾ n⊆m))
suc l⊆n  ⨾ suc n⊆m  = -, suc   (snd (l⊆n ⨾ n⊆m))
zero     ⨾ zero     = -, zero

⊂⇒⊆ : suc m ⊆ n → m ⊆ n
⊂⇒⊆ p = fst (drop ι ⨾ p)

n⊄n : suc n ⊆ n → ⊥
n⊄n {zero} ()
n⊄n {suc n} (drop p) = n⊄n (⊂⇒⊆ p)
n⊄n {suc n} (suc p) = n⊄n p

antisym : ∀ {m} (m⊆n : m ⊆ n) (n⊆m : n ⊆ m) →
          Σ (m ≡ n) λ where refl → (m⊆n ≡ ι) × (n⊆m ≡ ι)
antisym (drop m⊆n) n⊆m = ⊥-elim (n⊄n (fst (n⊆m ⨾ m⊆n)))
antisym (suc m⊆n) (drop n⊆m) = ⊥-elim (n⊄n (fst (n⊆m ⨾ m⊆n)))
antisym (suc m⊆n) (suc n⊆m)
  with refl , refl , refl ← antisym m⊆n n⊆m
  = refl , refl , refl
antisym zero zero = refl , refl , refl

ι? : ∀ {m} (n⊆m : n ⊆ m) →
       (m ⊆ n → ⊥) ⊎ (Σ (n ≡ m) (λ where refl → n⊆m ≡ ι))
ι? (drop n⊆m) = no λ m⊂n → n⊄n (fst (m⊂n ⨾ n⊆m))
ι? (suc n⊆m) with ι? n⊆m
... | no ¬m⊆n = no λ where
  (drop p) → ¬m⊆n (fst (drop ι ⨾ p))
  (suc p) → ¬m⊆n p
... | yes (refl , refl) = yes (refl , refl)
ι? zero = yes (refl , refl)

ι⨾_ : (n⊆m : n ⊆ m) → ι ⨾ n⊆m ≈ n⊆m
ι⨾ drop n⊆m = dropʳ (ι⨾ n⊆m)
ι⨾ suc  n⊆m = suc   (ι⨾ n⊆m)
ι⨾ zero     = zero

⨾-assoc03 :
  ∀ {i} {n⊆m : n ⊆ m} {l⊆i : l ⊆ i} {i⊆m} →
  ⟨ (l⊆i ⨾_≈ l⊆n) ∩ (_⨾ n⊆m ≈ i⊆m) ⟩ →
  ⟨ (l⊆i ⨾ i⊆m ≈_) ∩ (l⊆n ⨾ n⊆m ≈_) ⟩
⨾-assoc03 (-, lin , dropʳ inm)
  = let (-, lim , lnm ) = ⨾-assoc03 (-, lin , inm) in
    -, dropʳ lim , dropʳ lnm
⨾-assoc03 (-, dropʳ lin , dropˡ inm)
  = let (-, lim , lnm ) = ⨾-assoc03 (-, lin , inm) in
    -, dropʳ lim , dropˡ lnm
⨾-assoc03 (-, dropˡ lin , suc inm)
  = let (-, lim , lnm ) = ⨾-assoc03 (-, lin , inm) in
    -, dropˡ lim , dropˡ lnm
⨾-assoc03 (-, suc lin , suc inm)
  = let (-, lim , lnm ) = ⨾-assoc03 (-, lin , inm) in
    -, suc lim , suc lnm
⨾-assoc03 (-, zero , zero) = -, zero , zero


isFun-⨾ : {l⊆n : l ⊆ n} {n⊆m : n ⊆ m}
          (a b : ⟨ l⊆n ⨾ n⊆m ≈_ ⟩) → a ≡ b
isFun-⨾ (-, dropʳ a) (-, dropʳ b)
  with refl ← isFun-⨾ (-, a) (-, b) = refl
isFun-⨾ (-, dropˡ a) (-, dropˡ b)
  with refl ← isFun-⨾ (-, a) (-, b) = refl
isFun-⨾ (-, suc a)   (-, suc b)
  with refl ← isFun-⨾ (-, a) (-, b) = refl
isFun-⨾ (-, zero)    (-, zero)    = refl

⨾-assoc02 :
  ∀ {i} {n⊆m : n ⊆ m} {l⊆i : l ⊆ i} {i⊆n l⊆m} →
  ⟨ (l⊆i ⨾_≈ l⊆m) ∩ (i⊆n ⨾ n⊆m ≈_) ⟩ →
  ⟨ (l⊆i ⨾ i⊆n ≈_) ∩ (_⨾ n⊆m ≈ l⊆m) ⟩
⨾-assoc02 (-, lim , inm)
  with -, lin ← _ ⨾ _
  with (-, lim′ , lnm) ← ⨾-assoc03 (-, lin , inm)
  with refl ← isFun-⨾ (-, lim) (-, lim′)
  = -, lin , lnm


_%_ : ⟨ (_⊆ n₀) ∩ (_⊆ n₁) ⟩ →
      ⟨ (n₀ ⊆_) ∩ (n₁ ⊆_) ⟩ →
      Set
(-, l⊆n₀ , l⊆n₁) % (-, n₀⊆m , n₁⊆m)
  = ⟨ (l⊆n₀ ⨾ n₀⊆m ≈_) ∩ (l⊆n₁ ⨾ n₁⊆m ≈_) ⟩

data Pullback
  : ∀ {n₀ n₁} →
    {⌜ : ⟨ (_⊆ n₀) ∩ (_⊆ n₁) ⟩} →
    {⌟ : ⟨ (n₀ ⊆_) ∩ (n₁ ⊆_) ⟩} →
    ⌜ % ⌟ → Set where
  dropʳ  : ∀ {l⊆n₀} {n₀⊆m : n₀ ⊆ m} {l⊆n₁ : l ⊆ n₁} {n₁⊆m l⊆m}
           {◣ : l⊆n₀ ⨾ n₀⊆m ≈ l⊆m}
           {◥ : l⊆n₁ ⨾ n₁⊆m ≈ l⊆m} →
           Pullback (-, ◣ , ◥) →
           Pullback (-, dropˡ ◣ , dropʳ ◥)
  dropˡ  : ∀ {l⊆n₀} {n₀⊆m : n₀ ⊆ m} {l⊆n₁ : l ⊆ n₁} {n₁⊆m l⊆m}
           {◣ : l⊆n₀ ⨾ n₀⊆m ≈ l⊆m}
           {◥ : l⊆n₁ ⨾ n₁⊆m ≈ l⊆m} →
           Pullback (-, ◣ , ◥) →
           Pullback (-, dropʳ ◣ , dropˡ ◥)
  dropˡʳ : ∀ {l⊆n₀} {n₀⊆m : n₀ ⊆ m} {l⊆n₁ : l ⊆ n₁} {n₁⊆m l⊆m}
           {◣ : l⊆n₀ ⨾ n₀⊆m ≈ l⊆m}
           {◥ : l⊆n₁ ⨾ n₁⊆m ≈ l⊆m} →
           Pullback (-, ◣ , ◥) →
           Pullback (-, dropʳ ◣ , dropʳ ◥)
  suc    : ∀ {l⊆n₀} {n₀⊆m : n₀ ⊆ m} {l⊆n₁ : l ⊆ n₁} {n₁⊆m l⊆m}
           {◣ : l⊆n₀ ⨾ n₀⊆m ≈ l⊆m}
           {◥ : l⊆n₁ ⨾ n₁⊆m ≈ l⊆m} →
           Pullback (-, ◣ , ◥) →
           Pullback (-, suc ◣ , suc ◥)
  zero   : Pullback (-, zero , zero)

pullback :
  (⌟ : ⟨ (n₀ ⊆_) ∩ (n₁ ⊆_) ⟩) →
  Σ ⟨ _% ⌟ ⟩ (λ (-, ■) → Pullback ■)
pullback (-, drop n₀⊆m , drop n₁⊆m)
  = -, dropˡʳ (snd (pullback (-, n₀⊆m , n₁⊆m)))
pullback (-, drop n₀⊆m , suc n₁⊆m)
  = -, dropˡ  (snd (pullback (-, n₀⊆m , n₁⊆m)))
pullback (-, suc n₀⊆m  , drop n₁⊆m)
  = -, dropʳ  (snd (pullback (-, n₀⊆m , n₁⊆m)))
pullback (-, suc n₀⊆m  , suc n₁⊆m)
  = -, suc    (snd (pullback (-, n₀⊆m , n₁⊆m)))
pullback (-, zero      , zero)
  = -, zero

thicken : (n⊆m : n ⊆ m) (l⊆m : l ⊆ m) → Dec ⟨ _⨾ n⊆m ≈ l⊆m ⟩
thicken n⊆m l⊆m with pullback (-, n⊆m , l⊆m)
... | (((-, i⊆n , i⊆l) , (-, ◣ , ◥)) , p) with ι? i⊆l
... | no ¬l⊆i = no {!!} -- TODO: universal property of pullbacks
... | yes (refl , refl)
  with refl ← isFun-⨾ (-, ◥) (-, ι⨾ _)
  = yes (-, ◣)

subst : ∀ {p} (P : A → Set p) {x y} → x ≡ y → P y → P x
subst P refl px = px

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trivial : ∀ {a} {A : Set a} {x : A} {p : ⊥} → ⊥-elim p ≡ x
trivial {p = ()}

interleaved mutual

  data Context (m : Nat) : Set₁
  ⟦_⟧ : Context m → n ⊆ m → Set
  select : ∀ Γ {n⊆m : n ⊆ m} {l⊆m : l ⊆ m} →
           ⟨ _⨾ n⊆m ≈ l⊆m ⟩ → ⟦ Γ ⟧ n⊆m → ⟦ Γ ⟧ l⊆m
  select-⨾ :
    ∀ Γ {i} {n⊆m : n ⊆ m} {l⊆m : l ⊆ m} {i⊆m : i ⊆ m} →
    (lim : ⟨ _⨾ i⊆m ≈ l⊆m ⟩)
    (inm : ⟨ _⨾ n⊆m ≈ i⊆m ⟩)
    (lnm : ⟨ _⨾ n⊆m ≈ l⊆m ⟩)
    (ρ : ⟦ Γ ⟧ n⊆m) →
    select Γ lim (select Γ inm ρ) ≡ select Γ lnm ρ


  data Context m where ε : Context m
  ⟦ ε ⟧ th = ⊤
  select ε _ ρ = ρ
  select-⨾ ε lim inm lnm ρ = refl

  data Context m where
    bind : (Γ : Context m) (n⊆m : n ⊆ m) →
           (⟦ Γ ⟧ n⊆m → Set) → Context m
  ⟦ bind Γ l⊆m σ ⟧ n⊆m with thicken n⊆m l⊆m
  ... | no _ = ⟦ Γ ⟧ n⊆m
  ... | yes inm = Σ (⟦ Γ ⟧ n⊆m) (λ ρ → σ (select Γ inm ρ))
  select {n} {m} {i} (bind {l} Γ l⊆m σ) {n⊆m} {i⊆m} inm ρ
    with thicken n⊆m l⊆m | thicken i⊆m l⊆m
  ... | no ¬lnm | no ¬lim = select Γ inm ρ
  select (bind Γ l⊆m σ) {n⊆m} {i⊆m} inm (ρ , v)
      | yes lnm | yes lim
      = select Γ inm ρ
      , subst σ (select-⨾ Γ lim inm lnm ρ) v
  ... | no ¬lnm | yes lim
    = let (-, _ , lnm) = ⨾-assoc02 (-, snd lim , snd inm) in
      ⊥-elim (¬lnm (-, lnm))
  select (bind Γ l⊆m σ) {n⊆m} {i⊆m} ◣ (ρ , v)
      | yes lnm | no ¬lim  = select Γ ◣ ρ

  select-⨾ {n} {m} {i} (bind {l} Γ l⊆m x)
    {k} {n⊆m} {i⊆m} {k⊆m} ikm knm inm ρ
     with thicken i⊆m l⊆m
       | thicken k⊆m l⊆m
       | thicken n⊆m l⊆m
  select-⨾ {n} {m} {i} (bind {l} Γ l⊆m x)
    {k} {n⊆m} {i⊆m} {k⊆m} ikm knm inm (ρ , v)
    | no _ | no _ | yes r
    = select-⨾ Γ ikm knm inm ρ
  ... | no _ | no _ | no _
    = select-⨾ Γ ikm knm inm ρ
  ... | yes p | no ¬q | yes r = trivial
  ... | yes p | no ¬q | no ¬r = trivial
  select-⨾ {n} {m} {i} (bind {l} Γ l⊆m x)
    {k} {n⊆m} {i⊆m} {k⊆m} ikm knm inm (ρ , v)
     | no _ | yes q | yes r
     with ρ′ ← select Γ inm ρ
       | refl ← select-⨾ Γ ikm knm inm ρ
     with ρ′′ ← select Γ r ρ
       | refl ← select-⨾ Γ q knm r ρ
       = refl
  ... | no ¬p | yes q | no ¬r
    = ⊥-elim
       (¬r
        (⨾-assoc02 (k⊆m , snd q , snd knm) .fst ,
         ⨾-assoc02 (k⊆m , snd q , snd knm) .snd .snd))
  select-⨾ {n} {m} {i} (bind {l} Γ l⊆m σ)
    {k} {n⊆m} {i⊆m} {k⊆m} ikm knm inm (ρ , v)
     | yes p | yes q | yes r
     with ρ₁ ← select Γ r ρ
        | refl ← select-⨾ Γ q knm r ρ
        | eq₁ ← select-⨾ Γ p inm r ρ
     with eq₂ ← select-⨾ Γ p ikm q (select Γ knm ρ)
     with ρ₂ ← select Γ inm ρ
       | refl ← select-⨾ Γ ikm knm inm ρ
     with ρ₃ ← select Γ q (select Γ knm ρ)
       | refl ← eq₁
       | refl ← eq₂
       = refl
  ... | yes p | yes q | no ¬r = sym trivial

record Brick : Set₁ where
  field
    dimensions : Nat
    context    : Context dimensions
    payload    : ⟦ context ⟧ ι → Set
