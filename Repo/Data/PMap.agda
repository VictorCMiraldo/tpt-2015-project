open import Level using (_⊔_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List.Any as A hiding (map)
open import Relation.Binary.PropositionalEquality.Core as PropEq
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

open import Prelude hiding (map)
open Eq {{...}}

module Repo.Data.PMap (A : Set){{eqA : Eq A}} where

  private
    _≟_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)
    a₁ ≟ a₂ = Eq.cmp eqA a₁ a₂

  -- Naive Partial Map representation
  to_ : ∀{b} → Set b → Set b
  to B = List (A × B)

  -- Default values and it's projections
  to_default : ∀{b} → Set b → Set b
  to B default = B × List (A × B)

  onDef : ∀{b c}{B : Set b}{C : Set c}
        → (m : to B → C) → to B default → C
  onDef f (_ , m) = f m

  onDef' : ∀{b}{B : Set b}
         → (m : to B → to B) → to B default → to B default
  onDef' f (def , m) = def , f m

  -- Constants

  empty : ∀{b}{B : Set b}
        → to B
  empty = []

  -- Key Membership

  _∈_ : ∀{b}{B : Set b}
      → A → (to B) → Set _
  a ∈ m = A.Any ((_≡_ a) ∘ p1) m

  _∉_ : ∀{b}{B : Set b}
      → A → (to B) → Set _
  a ∉ m = (a ∈ m) → ⊥

  -- Decidable membership
  dec∈ : ∀{b}{B : Set b}
       → (a : A) → (m : to B) → Dec (a ∈ m)
  dec∈ a [] = no (λ ())
  dec∈ a (x ∷ m) with a ≟ (p1 x)
  ...| yes a≡x = yes (here a≡x)
  ...| no  a≢x with dec∈ a m
  ...| yes a∈m = yes (there a∈m)
  ...| no  a∉m = no (a∉m ∘ tail a≢x)
  

  -- Look up
  lkup : ∀{b}{B : Set b} → A → (to B) → Maybe B
  lkup k [] = nothing
  lkup k ((h , r) ∷ ts) 
    with k ≟ h
  ...| yes _ = just r
  ...| no  _ = lkup k ts

  -- Look up in a map with a default value
  lkupDef : ∀{b}{B : Set b} → A → to B default → B
  lkupDef a (b , m) = maybe id b (lkup a m)

  -- Total version
  lkup' : ∀{b}{B : Set b}
        → (a : A) → (m : to B) → a ∈ m → B
  lkup' a (m ∷ _)  (here px)   = p2 m
  lkup' a (_ ∷ ms) (there prf) = lkup' a ms prf

  -- Insertion / Removal
  alter : ∀{b}{B : Set b}
        → (Maybe B → Maybe B) → A → (to B) → (to B)
  alter f a [] with f nothing
  ...| just b  = (a , b) ∷ []
  ...| nothing = []
  alter f a (x ∷ m) with a ≟ p1 x
  ...| no  _ = x ∷ alter f a m
  ...| yes _ with f $ just (p2 x)
  ...| nothing = m
  ...| just b  = (a , b) ∷ m

  alterPrf : ∀{b}{B : Set b}
           → B → (a : A) → (m : to B) → Σ (to B) (_∈_ a)
  alterPrf b a m with dec∈ a m
  ...| yes a∈m = m , a∈m
  ...| no  a∉m = (a , b) ∷ m , here refl

  insert : ∀{b}{B : Set b}
         → A → B → (to B) → (to B)
  insert a b m = alter (const $ just b) a m

  delete : ∀{b}{B : Set b}
         → A → (to B) → (to B)
  delete a m = alter (const nothing) a m

  -- Map
  map : ∀{b}{B B′ : Set b} → (B → B′) → (to B) → (to B′)
  map f [] = []
  map f ((a , b) ∷ m) = (a , f b) ∷ map f m

  dom : ∀{b}{B : Set b} → (to B) → List A
  dom = Prelude.map p1

  -- Some predicates over maps

  lkup-inj : ∀{b}{B : Set b}(a₁ a₂ : A)
           → a₁ ≡ a₂ → (m : to B)
           → lkup a₁ m ≡ lkup a₂ m
  lkup-inj a2 .a2 refl m = refl

  lkup-∉ : ∀{b}{B : Set b}(a : A)(m : to B)
         → lkup a m ≡ nothing → a ∉ m
  lkup-∉ a [] _ ()
  lkup-∉ a (x ∷ m) hip a∈xm with a ≟ p1 x
  lkup-∉ a (x ∷ m) () a∈xm | yes a≡x
  ...| no  a≢x = lkup-∉ a m hip (tail a≢x a∈xm)

  isDisjoint : ∀{b}{B : Set b} → to B → to B → Set
  isDisjoint m1 m2 = isDisjointL (dom m1) (dom m2)
    where
      _∩_ : List A → List A → List A
      [] ∩ _ = []
      (h ∷ t) ∩ l with A.any (_≟_ h) l
      ...| yes _ = h ∷ t ∩ l
      ...| no  _ = t ∩ l

      isDisjointL : List A → List A → Set
      isDisjointL l1 l2 = l1 ∩ l2 ≡ []

  isFactor : ∀{b}{B : Set b} → to B → Set b
  isFactor {B = B} m 
    = Σ (to B) (λ m₁ → Σ (to B) (λ m₂ → isDisjoint m₁ m₂ × m ≡ m₁ ++ m₂))

  factorₗ : ∀{b}{B : Set b}{m : to B} → isFactor m → to B
  factorₗ (m₁ , _) = m₁

  factorᵣ : ∀{b}{B : Set b}{m : to B} → isFactor m → to B
  factorᵣ (_ , (m₂ , _)) = m₂

  {-
  isDisj : ∀{b}{B : Set b}{xa : A}{xb : B}{m′ : to B}(m : to B) 
          → m ≡ (xa , xb) ∷ m′ → xa ∉ m′
  isDisj {xa = a} {m′ = m′} m hip 
    = lkup-∉ a m′ {!!} -- ok... here we have a problem.
                       -- it is trivial to find a counter-example.
  -}
