open import Level using (_⊔_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List.Any as A hiding (map)
open import Relation.Binary.PropositionalEquality.Core as PropEq
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

open import Prelude hiding (map)
open Eq {{...}}

open import Repo.Data.List1

module Repo.Data.PMap1 (A : Set){{eqA : Eq A}} where
  
  private
    _≟_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)
    a₁ ≟ a₂ = Eq.cmp eqA a₁ a₂

  ----------------
  -- Unique Map --
  ----------------

  to1 : Set → Set
  to1 B = Σ (List (A × B)) (noDups-mod p1)

  empty : {B : Set} → to1 B
  empty = [] , unit
    
  ----------------
  -- Membership --
  ----------------

  _∈_ : {B : Set} → A → to1 B → Set
  a ∈ m = A.Any ((_≡_ a) ∘ p1) (p1 m)

  _∉_ : {B : Set} → A → to1 B → Set
  a ∉ m = a ∈ m → ⊥

  elem : {B : Set}(a : A)(m : to1 B) → Dec (a ∈ m)
  elem a ([] , _) = no (λ ())
  elem a ((x ∷ m) , prf) with a ≟ (p1 x)
  ...| yes a≡x = yes (here a≡x)
  ...| no  a≢x with elem a (m , p2 prf)
  ...| yes a∈m = yes (there a∈m)
  ...| no  a∉m = no (a∉m ∘ tail a≢x)

  ---------------
  -- Retrieval --
  ---------------

  lkup : {B : Set} → A → to1 B → Maybe B
  lkup k ([] , unit) = nothing
  lkup k (x ∷ m , prf) with k ≟ p1 x
  ...| yes _ = just (p2 x)
  ...| no  _ = lkup k (m , p2 prf)

  lift : {B : Set} → to1 B → A → Maybe B
  lift m a = lkup a m

  lkup-total : {B : Set}(a : A)(m : to1 B) → a ∈ m → B
  lkup-total k (m ∷ _ , _)    (here _)  = p2 m
  lkup-total k (_ ∷ ms , prf) (there x) = lkup-total k (ms , p2 prf) x

  ------------------------------------------
  -- Auxiliary Formulations of Properties --
  ------------------------------------------

  private
    any-map-commute-1 : {A B : Set}{l : List A}{f : A → B}{P : B → Set}
                      → Any (P ∘ f) l → Any P (Prelude.map f l)
    any-map-commute-1 (here px) = here px
    any-map-commute-1 (there hip) = there (any-map-commute-1 hip)

    any-map-commute-2 : {A B : Set}{l : List A}{f : A → B}{P : B → Set}
                      → Any P (Prelude.map f l) → Any (P ∘ f) l
    any-map-commute-2 {l = []} ()
    any-map-commute-2 {l = x ∷ l} (here px) = here px
    any-map-commute-2 {l = x ∷ l} (there hip) = there (any-map-commute-2 hip)

    ∈→∈l : {B : Set}{a : A}{m : to1 B}
     → a ∈ m → a ∈l Prelude.map p1 (p1 m)
    ∈→∈l = any-map-commute-1

    ∉→∉l : {B : Set}{a : A}{m : to1 B}
         → a ∉ m → a ∉l Prelude.map p1 (p1 m)
    ∉→∉l hip = hip ∘ any-map-commute-2

    ∉l→∉ : {B : Set}{a : A}{m : to1 B}
         → a ∉l Prelude.map p1 (p1 m) → a ∉ m
    ∉l→∉ hip = hip ∘ any-map-commute-1

    add-with-prf : {B : Set}(a : A)(b : B)(m : to1 B)
                 → a ∉ m → to1 B
    add-with-prf a b (m , prf) hip = (a , b) ∷ m , ∉→∉l {m = (m , prf)} hip , prf

  ---------------
  -- Insertion --
  ---------------

  mutual
    insert : {B : Set}(a : A)(b : B) → to1 B → to1 B
    insert a b ([] , prf) = (a , b) ∷ [] , (λ ()) , unit
    insert a b ((k , v) ∷ m , p , prf) with a ≟ k
    ...| yes a≡k = (k , b) ∷ m , p , prf
    ...| no  a≢k = add-with-prf k v 
                       (insert a b (m , prf)) 
                       (insert-lemma (∉l→∉ {m = (m , prf)} p) (a≢k ∘ sym))
    private
      insert-lemma : {B : Set}{k a : A}{b : B}{m : to1 B}
                   → k ∉ m → k ≢ a → k ∉ insert a b m
      insert-lemma {B} {k} {a} {b} {m} k∉m k≢a hip 
        = aux m (∉→∉l {m = m} k∉m) k≢a (any-map-commute-1 hip)
        where
          insert-stable : (m : to1 B) → k ∈ insert a b m → k ≢ a → k ∈ m
          insert-stable ([]    , p) hip k≢a = tail k≢a hip
          insert-stable ((x , xv) ∷ m , p , prf) hip k≢a with k ≟ x
          ...| yes k≡x = here k≡x
          ...| no  k≢x with a ≟ x
          ...| yes a≡x = there (tail k≢x hip)
          ...| no  a≢x = there (insert-stable (m , prf) (tail k≢x hip) k≢a)

          aux : (m : to1 B) → k ∉l Prelude.map p1 (p1 m) → k ≢ a → k ∉l Prelude.map p1 (p1 (insert a b m))
          aux ([]    , p) k∉m k≢a hip = k∉m (tail k≢a hip)
          aux (x ∷ m , p , prf) k∉m k≢a hip with a ≟ p1 x
          ...| yes a≡x = k∉m hip
          aux ((.k , v) ∷ m , p , prf) k∉m k≢a (here refl)   
            | no a≢x = k∉m (here refl)
          aux (x ∷ m , p , prf) k∉m k≢a (there hip) 
            | no a≢x = k∉m (there (∈→∈l {m = m , prf} (insert-stable (m , prf) (any-map-commute-2 hip) k≢a)))

  -------------
  -- Removal --
  -------------
  
  mutual
    remove : {B : Set}(a : A) → to1 B → to1 B
    remove a ([] , unit) = ([] , unit)
    remove a ((k , v) ∷ m , p , prf) with a ≟ k
    ...| yes a≡k = m , prf
    ...| no  a≢k = add-with-prf k v 
                       (remove a (m , prf)) 
                       (remove-lemma (m , prf) (∉l→∉ {m = m , prf} p))
    
    
    remove-lemma : {B : Set}{a k : A}(m : to1 B) → k ∉ m → k ∉ remove a m
    remove-lemma ([] , unit) hip ()
    remove-lemma {a = a} {k = k} ((x , xv) ∷ m , p , prf) hip k∈xm 
      with a ≟ x
    remove-lemma ((x , xv) ∷ ._ , p , prf) hip (here px) 
      | yes a≡x = hip (there (here px))
    remove-lemma ((x , xv) ∷ ._ , p , prf) hip (there k∈xm) 
      | yes a≡x = hip (there (there k∈xm))
    remove-lemma ((x , xv) ∷ m , p , prf) hip (here px) 
      | no a≢x = hip (here px)
    remove-lemma ((x , xv) ∷ m , p , prf) hip (there k∈xm) 
      | no a≢x = remove-lemma (m , prf) (hip ∘ there) k∈xm


  -----------
  -- Alter --
  -----------

  alter : {B : Set}(f : Maybe B → Maybe B) → A → to1 B → to1 B
  alter f k m with f (lift m k)
  ...| just b  = insert k b m
  ...| nothing = remove k m
