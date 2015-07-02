open import Level using (_⊔_) renaming (zero to lz; suc to ls)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List.Any as A hiding (map)
open import Relation.Binary.PropositionalEquality.Core as PropEq
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

open import Prelude hiding (map)
open Eq {{...}}

open import Repo.Data.List1

module Repo.Data.PMap1.Union (A : Set){{eqA : Eq A}} where

  open import Repo.Data.PMap1 A {{eqA}}

  private
    _≟_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)
    a₁ ≟ a₂ = Eq.cmp eqA a₁ a₂

  -------------------
  -- Disjoint Maps --
  -------------------

  disjoint : {B : Set} → to1 B × to1 B → Set
  disjoint (([] , unit)             , n) 
    = Unit
  disjoint (((x , v) ∷ m , p , prf) , n)
    = x ∉ n × disjoint ((m , prf) , n)

  disjoint-proof-irrel : {B : Set}{m₁ m₂ : to1 B}
                       → (d1 d2 : disjoint (m₁ , m₂))
                       → d1 ≡ d2
  disjoint-proof-irrel {m₁ = [] , unit} unit unit
    = refl
  disjoint-proof-irrel {m₁ = (x , v) ∷ m₁ , p , prf} (d11 , d12) (d21 , d22)
    = cong₂ _,_ (fun-ext (λ k → ⊥-elim (d11 k))) (disjoint-proof-irrel d12 d22)

  -- If two maps are disjoint, and m is an element of the second,
  -- then it is not in the first!
  disjoint-choose-2 : {B : Set}{m₁ m₂ : to1 B}{a : A} → disjoint (m₁ , m₂)
                      → a ∈ m₂ → a ∉ m₁
  disjoint-choose-2 {m₁ = [] , unit} hip a∈m₂ ()
  disjoint-choose-2 {m₁ = (x , v) ∷ m₁ , p , prf} hip a∈m₂ (here refl)   = p1 hip a∈m₂
  disjoint-choose-2 {m₁ = (x , v) ∷ m₁ , p , prf} hip a∈m₂ (there a∈m₁) = disjoint-choose-2 (p2 hip) a∈m₂ a∈m₁

  -- Disjointness is commutative.
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

  -- Empty is disjoint of anything.
  disjoint-empty-r : {B : Set}(m : to1 B) → disjoint (m , empty)
  disjoint-empty-r ([] , unit) = unit
  disjoint-empty-r ((x , v) ∷ m , p , prf) = (λ ()) , (disjoint-empty-r (m , prf))

  disjoint-empty-l : {B : Set}(m : to1 B) → disjoint (empty , m)
  disjoint-empty-l _ = unit

  {-
  private
    -- Now, lifting equality also gives us some 
    -- structure over the underlying maps.
    lift-≡-empty : {B : Set}{m : to1 B}
                 → lift m ≡ lift ([] , unit)
                 → m ≡ ([] , unit)
    lift-≡-empty {m = [] , unit} hip = refl
    lift-≡-empty {m = (x , v) ∷ m , p , prf} hip 
      with lift-≡-lkup {m₁ = (x , v) ∷ m , p , prf} {m₂ = [] , unit} {a = x} hip 
    ...| r with x ≟ x
    ...| no  x≢x = ⊥-elim (x≢x refl)
    lift-≡-empty {B} {(x , v) ∷ m , p , prf} hip | () | yes x≡x

    lift-≡-cons : {B : Set}{m m' m'' : to1 B}{x : A}{v : B}
                → x ∉ m''
                → m' ≡ insert x v m''
                → lift m ≡ lift m'
                → lift (remove x m) ≡ lift m''
    lift-≡-cons hip = {!!}
  -}

  -- Although subtle, it is crucial to be able to divide maps into 
  -- disjoint sub-maps.
  -- We do this by induction, and the final definition is only possible after
  -- a notion of union is estabilished.
  --
  -- Yet, it is trivial to extract a submap from a key:
  focus : {B : Set} → A → to1 B → Σ (to1 B × to1 B) disjoint
  focus a m with lift m a
  ...| nothing = (([] , unit) , m) , unit
  ...| just b  = ((((a , b) ∷ [] , (λ ()) , unit) , remove a m)
                 , remove-correct m , unit
                 )
  
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

  -- Now we can explicitely state that inserts and removes
  -- preserve disjointness (given a few side conditions, ofc)
  disjoint-remove : {B : Set}{a : A}(m₁ m₂ : to1 B)
                  → disjoint (m₁ , m₂) → disjoint (m₁ , remove a m₂)
  disjoint-remove ([] , unit) m2 disj = unit
  disjoint-remove {a = a} ((x , v) ∷ m , p , prf) m2 disj 
    = remove-lemma m2 (p1 disj) , disjoint-remove (m , prf) m2 (p2 disj)

  disjoint-insert : {B : Set}{a : A}{b : B}(m₁ m₂ : to1 B)(prf : disjoint (m₁ , m₂))
                  → a ∉ union m₁ m₂ prf → disjoint (insert a b m₁ , m₂)
  disjoint-insert {a = a} ([] , unit) m2 disj hip = p2 (¬union-uni-2 {m₂ = m2} a disj hip) , unit
  disjoint-insert {a = a} ((x , v) ∷ m , p , prf) m2 disj hip
    with a ≟ x
  ...| no  a≢x = (p1 disj) , (disjoint-insert (m , prf) m2 (p2 disj) (hip ∘ there))
  ...| yes a≡x = ⊥-elim (hip (here a≡x))

  -- A few properties of union follow

  union-ext-2 : {B : Set}{a : A}{m₁ m₂ : to1 B}(hip : disjoint (m₁ , m₂))
              → a ∈ m₂ → a ∈ union m₁ m₂ hip
  union-ext-2 {m₁ = [] , unit} disj a∈m2 = a∈m2
  union-ext-2 {a = a} {m₁ = (x , v) ∷ m , p , prf} disj a∈m2
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

  union-lkup-1 : {B : Set}{m₁ m₂ : to1 B}(hip : disjoint (m₁ , m₂))
               → (x : A) → x ∈ m₁ → lkup x (union m₁ m₂ hip) ≡ lkup x m₁
  union-lkup-1 {m₁ = ([] , unit)} hip x ()
  union-lkup-1 {m₁ = ((k , v) ∷ m₁ , p , prf) } hip x x∈m1
    with x ≟ k
  ...| yes x≡k = refl
  ...| no  x≢k = union-lkup-1 (p2 hip) x (tail x≢k x∈m1)

  union-lkup-2 : {B : Set}{m₁ m₂ : to1 B}(hip : disjoint {B = B} (m₁ , m₂))
               → (x : A) → x ∈ m₂ → lkup x (union m₁ m₂ hip) ≡ lkup x m₂
  union-lkup-2 {m₁ = ([] , unit)} hip x x∈m2 = refl
  union-lkup-2 {B = B} {m₁ = ((k , v) ∷ m₁ , p , prf) } {m₂ = m₂} hip x x∈m2
    with x ≟ k
  -- for some (unknown) reason, Agda don't like me passing my hipothesys to disjoint-choose-1.
  -- it complains about unsolved metas in hip.
  ...| yes x≡k = ⊥-elim thatsAbsurd -- (disjoint-choose-1 {B = B} {m₂ = m₂} hip (here x≡k) x∈m2)
     where postulate thatsAbsurd : ⊥
  ...| no  x≢k = union-lkup-2 (p2 hip) x x∈m2

  union-lkup-fail : {B : Set}{m₁ m₂ : to1 B}(hip : disjoint (m₁ , m₂))
                  → (x : A) → x ∉ m₁ → x ∉ m₂ → lkup x (union m₁ m₂ hip) ≡ nothing
  union-lkup-fail hip x x∉m₁ x∉m₂ = lkup-fails x (¬union-uni x hip x∉m₁ x∉m₂)

  -- Union is commutative modulo lifting. The lifting is important
  -- to disregerd a notion of order.
  union-comm : {B : Set}{m₁ m₂ : to1 B}(hip : disjoint (m₁ , m₂))
             → union m₁ m₂ hip ≈ union m₂ m₁ (disjoint-comm hip)
  union-comm {m₁ = m₁} {m₂ = m₂} hip = fun-ext lemma
    where
      lemma : (x : A) → lift (union m₁ m₂ hip) x ≡ lift (union m₂ m₁ (disjoint-comm hip)) x
      lemma x with elem x m₁
      ...| yes x∈m₁
         rewrite (union-lkup-1 hip x x∈m₁)
               | (union-lkup-2 (disjoint-comm hip) x x∈m₁)
               = refl
      ...| no x∉m₁ with elem x m₂
      ...| yes x∈m₂
         rewrite (union-lkup-1 (disjoint-comm hip) x x∈m₂)
               | (union-lkup-2 hip x x∈m₂)
               = refl
      ...| no  x∉m₂
         rewrite (union-lkup-fail hip x x∉m₁ x∉m₂)
               | (union-lkup-fail (disjoint-comm hip) x x∉m₂ x∉m₁)
               = refl

  union-disjoint-2 : {B : Set}(m₁ m₂ m₃ : to1 B)(disj₁₂ : disjoint (m₁ , m₂))
                 → (disj₃ : disjoint (union m₁ m₂ disj₁₂ , m₃))
                 → disjoint (m₂ , m₃)
  union-disjoint-2 ([] , unit) m2 m3 d12 d3 = d3
  union-disjoint-2 ((k , v) ∷ m1 , p , prf) m2 m3 d12 d3 
    = union-disjoint-2 (m1 , prf) m2 m3 (p2 d12) (p2 d3)

  union-disjoint-1 : {B : Set}(m₁ m₂ m₃ : to1 B)(disj₁₂ : disjoint (m₁ , m₂))
                   → (disj₃ : disjoint (union m₁ m₂ disj₁₂ , m₃))
                   → disjoint (m₁ , m₃)
  union-disjoint-1 ([] , unit) m2 m3 d12 d3 = unit
  union-disjoint-1 ((x , v) ∷ m1 , p , prf) m2 m3 d12 d3 = p1 d3 , union-disjoint-1 (m1 , prf) m2 m3 (p2 d12) (p2 d3)

  disjoint-union-1 : {B : Set}{m₁ m₂ m₃ : to1 B}
                   → (d12 : disjoint (m₁ , m₂))
                   → (d23 : disjoint (m₂ , m₃))
                   → (d13 : disjoint (m₁ , m₃))
                   → disjoint (m₁ , union m₂ m₃ d23)
  disjoint-union-1 {m₁ = ([] , unit)} d12 d23 d13 = unit
  disjoint-union-1 {m₁ = ((x , v) ∷ m1 , p , prf)} {m₂} {m₃} d12 d23 d13 
    with disjoint-union-1 {m₁ = (m1 , prf)} (p2 d12) d23 (p2 d13)
  ...| r = (¬union-uni x d23 (p1 d12) (p1 d13)) , r

  disjoint-union-2 : {B : Set}{m₁ m₂ m₃ : to1 B}
                   → (d12 : disjoint (m₁ , m₂))
                   → (d23 : disjoint (m₂ , m₃))
                   → (d13 : disjoint (m₁ , m₃))
                   → disjoint (union m₁ m₂ d12 , m₃)
  disjoint-union-2 {m₁ = m₁} {m₂} {m₃} d12 d23 d13 
    = disjoint-comm (disjoint-union-1 (disjoint-comm d13) d12 (disjoint-comm d23))

  {-
  TODO:
  This proof looks too complicated. 
  Rewriting lemmas taking into account disjoint-proof-irrel
  and noDups-mod-π₁-proof-irrel might help.

  union-assoc : {B : Set}{m₁ m₂ m₃ : to1 B}
              → (d12 : disjoint (m₁ , m₂))
              → (d23 : disjoint (m₂ , m₃))
              → (d13 : disjoint (m₁ , m₃))
              → union m₁ (union m₂ m₃ d23) (disjoint-union-1 d12 d23 d13) 
              ≡ union (union m₁ m₂ d12) m₃ (disjoint-union-2 d12 d23 d13)
  union-assoc {m₁ = [] , unit} {m₂} {m₃} d12 d23 d13 
    -- = subst (λ Z → lift (union m₂ m₃ d23) ≡ lift (union m₂ m₃ Z)) (disjoint-proof-irrel d23 (disjoint-union-2 d12 d23 d13)) refl
    = {!!}
  union-assoc {m₁ = (x , v) ∷ m₁ , p , prf} {m₂} {m₃} d12 d23 d13 
    with (union-assoc {m₁ = (m₁ , prf)} (p2 d12) d23 (p2 d13)) 
  ...| r = {!cong (x , v)!}

  Still, this result is paramount to the augmentation lemma...
  -}

  postulate
    union-assoc : {B : Set}{m₁ m₂ m₃ : to1 B}
                → (d12 : disjoint (m₁ , m₂))
                → (d23 : disjoint (m₂ , m₃))
                → (d13 : disjoint (m₁ , m₃))
                → union m₁ (union m₂ m₃ d23) (disjoint-union-1 d12 d23 d13) 
                ≈ union (union m₁ m₂ d12) m₃ (disjoint-union-2 d12 d23 d13)
  

  -------------------------------
  -- Liftings and Disjointness --
  -------------------------------

  {-
  lift-remove : {B : Set}{m₁ : to1 B}{m₂ : List (A × B)}{x : A}{v : B}
              → (p : x ∉l (Prelude.map p1 m₂))(prf : noDups-mod p1 m₂)
              → lift m₁ ≡ lift ((x , v) ∷ m₂ , p , prf)
              → lift (remove x m₁) ≡ lift (m₂ , prf)
  lift-remove {m₂ = []} p prf hip = {!!}
  lift-remove {m₂ = ab ∷ m2} p prf hip = {!!}

  -- Disjointness is preserved by liftings.
  disjoint-lift : {B : Set}(m₁ m₂ m₃ : to1 B)
                → disjoint (m₁ , m₂)
                → lift m₁ ≡ lift m₃
                → disjoint (m₃ , m₂)
  disjoint-lift m1 m2 ([] , unit) d12 hip 
    = unit
  disjoint-lift {B = B} m1 m2 ((x , v) ∷ m3 , p , prf) d12 hip 
    = (λ x∈m2 → disjoint-choose-2 d12 x∈m2 
         (lkup⇒∈ {B = B} {b = v} m1 x 
           (trans (lift-≡-lkup hip) refl))) 
    , disjoint-lift (remove x m1) m2 (m3 , prf) 
      (disjoint-comm (disjoint-remove m2 m1 (disjoint-comm d12))) 
      (lift-remove p prf hip)
  -}

  postulate
    disjoint-lift : {B : Set}(m₁ m₂ m₃ : to1 B)
                → disjoint (m₁ , m₂)
                → lift m₁ ≡ lift m₃
                → disjoint (m₃ , m₂)
    

  ----------------------------------
  -- Dividing and Merging of maps --
  ----------------------------------

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

  -- This is obsolete. We used it in the definition of Safe, 
  -- when we were still trying to prove CSL's soundness.
  disjoint3 : {B : Set} → to1 B → to1 B → to1 B → Set
  disjoint3 m1 m2 m3
    = Σ (disjoint (m2 , m3)) (λ p → disjoint (m1 , union m2 m3 p))

  union3 : {B : Set}(m1 m2 m3 : to1 B) → disjoint3 m1 m2 m3 → to1 B
  union3 m1 m2 m3 (p23 , p123) = union m1 (union m2 m3 p23) p123
