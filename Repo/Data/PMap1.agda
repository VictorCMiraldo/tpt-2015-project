open import Level using (_⊔_) renaming (zero to lz; suc to ls)
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

  lift-prf : {B : Set}(m : to1 B)(a : A) → Maybe (B × a ∈ m)
  lift-prf ([] , unit) a = nothing
  lift-prf ((x , v) ∷ m , p , prf) a with a ≟ x
  ...| yes a≡x = just (v , here a≡x)
  ...| no  a≢x = maybe (λ r → just (p1 r , there (p2 r))) nothing (lift-prf (m , prf) a)

  lkup-total : {B : Set}(a : A)(m : to1 B) → a ∈ m → B
  lkup-total k (m ∷ _ , _)    (here _)  = p2 m
  lkup-total k (_ ∷ ms , prf) (there x) = lkup-total k (ms , p2 prf) x

  dom : {B : Set} → to1 B → List1 A
  dom m = p1 (noDups-app p1 (p2 m))

  is-singleton-on : {B : Set} → to1 B → A → Set
  is-singleton-on m a = dom m ≡ (a ∷ [] , (λ ()), unit) 

  is-singleton-on-with : {B : Set} → to1 B → A → B → Set
  is-singleton-on-with m a b = m ≡ ((a , b) ∷ [] , (λ ()) , unit)

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

    ∈l→∈ : {B : Set}{a : A}{m : to1 B}
         → a ∈l Prelude.map p1 (p1 m) → a ∈ m 
    ∈l→∈ = any-map-commute-2

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

  remove-correct : {B : Set}{a : A}(m : to1 B)
                 → a ∉ remove a m
  remove-correct ([] , unit) ()
  remove-correct {a = a} ((x , v) ∷ m , p , prf) hip 
    with a ≟ x
  ...| yes a≡x rewrite a≡x = p (any-map-commute-1 hip)
  ...| no  a≢x = remove-correct (m , prf) (tail a≢x hip)


  -----------
  -- Alter --
  -----------

  alter : {B : Set}(f : Maybe B → Maybe B) → A → to1 B → to1 B
  alter f k m with f (lift m k)
  ...| just b  = insert k b m
  ...| nothing = remove k m

  mutual
    change : {B : Set}(a : A)(b : B)(m : to1 B)(p : a ∈ m) → to1 B
    change a b ((.a , _) ∷ m , p , prf) (here refl) 
      = ((a , b) ∷ m) , (p , prf)
    change a b ((x , xv) ∷ m , p , prf) (there h) 
      = add-with-prf x xv (change a b (m , prf) h) 
             (change-stable a (m , prf) h x (∉l→∉ {m = m , prf} p))

    change-stable : {B : Set}(a : A){b : B}(m : to1 B)(p : a ∈ m)
                  → (x : A) → x ∉ m → x ∉ change a b m p
    change-stable a (( k , v) ∷ m , p , prf) (there a∈m) x x∉m x∈m 
      = change-stable a (m , prf) a∈m x 
                 (x∉m ∘ there) 
                 (tail (x∉m ∘ here) x∈m)
    change-stable a ((.a , v) ∷ m , p , prf) (here refl) x x∉m x∈m 
      = x∉m (lemma m x∈m)
      where
        lemma : {B : Set}{f : A → Set}{a : A}{v v′ : B}(m : List (A × B))
              → Any (f ∘ p1) ((a , v) ∷ m) → Any (f ∘ p1) ((a , v′) ∷ m)
        lemma m (here px) = here px
        lemma (_ ∷ m) (there hip) = there (lemma m hip)
        lemma []      (there ())

  -------------------
  -- Disjoint Maps --
  -------------------

  disjoint : {B : Set} → to1 B × to1 B → Set
  disjoint (([] , unit)             , n) 
    = Unit
  disjoint (((x , v) ∷ m , p , prf) , n)
    = x ∉ n × disjoint ((m , prf) , n)

  disjoint-choose-2 : {B : Set}{m₁ m₂ : to1 B}{a : A} → disjoint (m₁ , m₂)
                      → a ∈ m₂ → a ∉ m₁
  disjoint-choose-2 {m₁ = [] , unit} hip a∈m₂ ()
  disjoint-choose-2 {m₁ = (x , v) ∷ m₁ , p , prf} hip a∈m₂ (here refl)   = p1 hip a∈m₂
  disjoint-choose-2 {m₁ = (x , v) ∷ m₁ , p , prf} hip a∈m₂ (there a∈m₁) = disjoint-choose-2 (p2 hip) a∈m₂ a∈m₁

  disjoint-comm : {B : Set}{m₁ m₂ : to1 B} → disjoint (m₁ , m₂) → disjoint (m₂ , m₁)
  disjoint-comm {m₂ = [] , unit} disj               
    = unit
  disjoint-comm {m₁ = [] , unit}                  {m₂ = ((x , v) ∷ m₂ , p2 , prf2)} disj 
    = (λ ()) , (disjoint-comm unit)
  disjoint-comm {m₁ = ((y , t) ∷ m₁ , p , prf1)} {m₂ = ((x , v) ∷ m₂ , _ , prf2)} (y∉xm2 , disj) 
    = disjoint-choose-2 {m₁ = (y , t) ∷ m₁ , p , prf1} (y∉xm2 , disj) (here refl) 
    , disjoint-comm (y∉xm2 ∘ there , disjoint-comm (p2 (disjoint-comm disj)))

  disjoint-choose-1 : {B : Set}{m₁ m₂ : to1 B}{a : A} → disjoint (m₁ , m₂)
                    → a ∈ m₁ → a ∉ m₂
  disjoint-choose-1 hip a∈m₁ a∈m₂ = disjoint-choose-2 (disjoint-comm hip) a∈m₁ a∈m₂

  -----------
  -- Union --
  -----------
  
  mutual
    union : {B : Set} → (m₁ m₂ : to1 B) → disjoint (m₁ , m₂) → to1 B
    union ([] , unit)             m₂ hip = m₂
    union ((x , v) ∷ m , p , prf) m₂ hip 
      = add-with-prf x v (union (m , prf) m₂ (p2 hip)) 
                         (¬union-uni x (p2 hip) (∉l→∉ {m = m , prf} p) (p1 hip))

    union-uni : {B : Set}{m₁ m₂ : to1 B}(a : A)(hip : disjoint (m₁ , m₂))
              → a ∈ union m₁ m₂ hip → (a ∈ m₁) ⊎ (a ∈ m₂)
    union-uni {m₁ = ([] , unit)}             a hip a∈mm = i2 a∈mm
    union-uni {m₁ = ((x , v) ∷ m , p , prf)} a hip a∈mm 
      with x ≟ a
    ...| yes x≡a = i1 (here (sym x≡a))
    ...| no  x≢a with union-uni a (p2 hip) (tail (x≢a ∘ sym) a∈mm)
    ...| i1 r = i1 (there r)
    ...| i2 r = i2 r

    ¬union-uni : {B : Set}{m₁ m₂ : to1 B}(a : A)(hip : disjoint (m₁ , m₂))
              → a ∉ m₁ → a ∉ m₂ → a ∉ union m₁ m₂ hip
    ¬union-uni a hip a∉m₁ a∉m₂ abs with union-uni a hip abs
    ...| i1 a∈m₁ = a∉m₁ a∈m₁
    ...| i2 a∈m₂ = a∉m₂ a∈m₂

  ¬union-uni-2 : {B : Set}{m₁ m₂ : to1 B}(a : A)(hip : disjoint (m₁ , m₂))
               → a ∉ union m₁ m₂ hip → (a ∉ m₁) × (a ∉ m₂)
  ¬union-uni-2 {m₁ = ([] , unit)} a hip a∈mm = (λ ()) , a∈mm
  ¬union-uni-2 {m₁ = ((x , v) ∷ m₁ , p , prf)} a hip a∈mm 
    with x ≟ a
  ...| yes x≡a = ⊥-elim (a∈mm (here (sym x≡a)))
  ...| no  x≢a with ¬union-uni-2 a (p2 hip) (a∈mm ∘ there)
  ...| r1 , r2 = r1 ∘ tail (x≢a ∘ sym) , r2

  union-ext-2 : {B : Set}{a : A}{m₁ m₂ : to1 B}(hip : disjoint (m₁ , m₂))
              → a ∈ m₂ → a ∈ union m₁ m₂ hip
  union-ext-2 {m₁ = [] , unit} disj a∈m2 = a∈m2
  union-ext-2 {a = a} {m₁ = (x , v) ∷ m , p , prf} disj a∈m2
    with x ≟ a
  ...| yes a≡x rewrite a≡x = ⊥-elim (p1 disj a∈m2)
  ...| no  a≢x = there (union-ext-2 (p2 disj) a∈m2)

  ¬union-ext-2 : {B : Set}{a : A}{m₁ m₂ : to1 B}(hip : disjoint (m₁ , m₂))
              → a ∈ m₂ → a ∈ union m₁ m₂ hip
  ¬union-ext-2 {m₁ = [] , unit} disj a∈m2 = a∈m2
  ¬union-ext-2 {a = a} {m₁ = (x , v) ∷ m , p , prf} disj a∈m2
    with x ≟ a
  ...| yes a≡x rewrite a≡x = ⊥-elim (p1 disj a∈m2)
  ...| no  a≢x = there (union-ext-2 (p2 disj) a∈m2)

  union-elim-2 : {B : Set}{a : A}{m₁ m₂ : to1 B}(hip : disjoint (m₁ , m₂))
               → a ∈ union m₁ m₂ hip → a ∉ m₂ → a ∈ m₁
  union-elim-2 {m₁ = [] , unit} disj a∈mm a∉m2 = ⊥-elim (a∉m2 a∈mm)
  union-elim-2 {a = a} {m₁ = (x , v) ∷ m , p , prf} disj a∈mm a∉m2 
    with a ≟ x
  ...| yes a≡x = here a≡x
  ...| no  a≢x = there (union-elim-2 (p2 disj) (tail a≢x a∈mm) a∉m2)
  
  disjoint-insert : {B : Set}{a : A}{b : B}(m₁ m₂ : to1 B)(prf : disjoint (m₁ , m₂))
                  → a ∉ union m₁ m₂ prf → disjoint (insert a b m₁ , m₂)
  disjoint-insert {a = a} ([] , unit) m2 disj hip = p2 (¬union-uni-2 {m₂ = m2} a disj hip) , unit
  disjoint-insert {a = a} ((x , v) ∷ m , p , prf) m2 disj hip
    with a ≟ x
  ...| no  a≢x = (p1 disj) , (disjoint-insert (m , prf) m2 (p2 disj) (hip ∘ there))
  ...| yes a≡x = ⊥-elim (hip (here a≡x))

  disjoint-remove : {B : Set}{a : A}(m₁ m₂ : to1 B)
                  → disjoint (m₁ , m₂) → disjoint (m₁ , remove a m₂)
  disjoint-remove ([] , unit) m2 disj = unit
  disjoint-remove {a = a} ((x , v) ∷ m , p , prf) m2 disj 
    = remove-lemma m2 (p1 disj) , disjoint-remove (m , prf) m2 (p2 disj)
 
  ----------------------------------
  -- Dividing and Merging of maps --
  ----------------------------------


  focus : {B : Set} → A → to1 B → Σ (to1 B × to1 B) disjoint
  focus a m with lift m a
  ...| nothing = (([] , unit) , m) , unit
  ...| just b  = ((((a , b) ∷ [] , (λ ()) , unit) , remove a m)
                 , remove-correct m , unit
                 )

  focus-step : {B : Set} → A → Σ (to1 B × to1 B) disjoint → Σ (to1 B × to1 B) disjoint
  focus-step a ((focus , rest) , disj) with lift-prf rest a
  ...| nothing = ((focus , rest) , disj)
  ...| just (b , a∈rest)  
               = (insert a b focus , remove a rest) 
               , disjoint-insert focus (remove a rest) (disjoint-remove focus rest disj) 
                  (λ x → disjoint-choose-2 disj a∈rest (lemma (disjoint-remove focus rest disj) x (remove-correct rest)))
    where
      lemma : {B : Set}{a : A}{m₁ m₂ : to1 B}(hip : disjoint (m₁ , m₂))
            → a ∈ union m₁ m₂ hip
            → a ∉ m₂
            → a ∈ m₁
      lemma {a = a} hip a∈mm a∉m2 = [ id , (⊥-elim ∘ a∉m2) ]′ (union-uni a hip a∈mm)

  focus* : {B : Set} → List A → to1 B → Σ (to1 B × to1 B) disjoint
  focus* {B} l m = foldr focus-step ((([] , unit) , m) , unit) l

  ---------------------------
  -- A Few Generalizations --
  ---------------------------

  disjoint3 : {B : Set} → to1 B → to1 B → to1 B → Set
  disjoint3 m1 m2 m3
    = Σ (disjoint (m2 , m3)) (λ p → disjoint (m1 , union m2 m3 p))

  union3 : {B : Set}(m1 m2 m3 : to1 B) → disjoint3 m1 m2 m3 → to1 B
  union3 m1 m2 m3 (p23 , p123) = union m1 (union m2 m3 p23) p123
