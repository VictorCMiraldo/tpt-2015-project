open import Prelude
open import Data.List.Any as A using ()
open import Data.List.Properties using (map-id)
open import Relation.Binary.PropositionalEquality

-- In this module we define the type of lists without duplicates
-- modulo a given function.
-- 
-- This can be seen as something close to a Set-theoretic set notion,
--
-- The operations provided over List1 are ineficient.
-- (we rely heavily on nub, which has a worst case complexity of O(n²) ).
--
module Repo.Data.List1 where

  -- A membership notion is paramount...
  -- We also stabilish a few other equivalent formulations.
  _∈l_ : {A : Set} → A → List A → Set _
  _∈l_ a m = A.Any (_≡_ a) m

  _∉l_ : {A : Set}{{eq : Eq A}}
      → A → List A → Set _
  a ∉l m = (a ∈l m) → ⊥
  
  -- no duplicates, modulo f, predicate
  noDups-mod : {A B : Set}{{eq : Eq B}} → (A → B) → List A → Set
  noDups-mod _ [] = Unit
  noDups-mod f (x ∷ l) = f x ∉l (map f l) × noDups-mod f l

  -- if f is the identity function, good for us.
  noDups⇒noDups-mod-id : {A : Set}{{eq : Eq A}}{a : A}{as : List A}
                       → a ∉l as
                       → id a ∉l map id as
  noDups⇒noDups-mod-id {as = as} hip a∈as 
    rewrite (map-id as) = hip a∈as

  -- Lists with no duplicates!
  List1 : (A : Set){{eq : Eq A}} → Set
  List1 A = Σ (List A) (noDups-mod id)

  -- Extracting a List from a List1 obj.
  list : {A : Set}{{eq : Eq A}} → List1 A → List A
  list = p1

  -- Constructing a List1, similarly to a List.
  -- The empty case is trivial.
  nil1 : {A : Set}{{eq : Eq A}} → List1 A
  nil1 = ([] , unit)

  -- For the cons case, however, we have two options.
  -- Either we add a new element to the list, provided it was
  -- not there already.
  cons1 : {A : Set}{{eq : Eq A}}
        → (a : A)(l : List1 A) → a ∉l (list l) → List1 A
  cons1 a (as , as-nodup) p 
    = a ∷ as , noDups⇒noDups-mod-id p , as-nodup

  -- Or, we check whether or not the new element is in the list,
  -- and then add it, if it's not there.
  cons1-dup : {A : Set}{{eq : Eq A}}
            → (a : A)(l : List1 A) → List1 A
  cons1-dup {{eq _≟_}} a (as , pas) with A.any (_≟_ a) as
  ...| yes _    = (as , pas)
  ...| no  a∉as = cons1 {{eq _≟_}} a (as , pas) (a∉as)

  nub : {A : Set}{{eq : Eq A}} → List A → List1 A
  nub [] = nil1
  nub (a ∷ as) = cons1-dup a (nub as)

  ----------------
  -- Operations --
  ----------------

  -- Intersection
  _∩_ : {A : Set}{{eq : Eq A}} → List1 A → List1 A → List1 A
  _∩_ ([] , _) _ = nil1
  _∩_ {{eq _≟_}} (h ∷ t , p) l with A.any (_≟_ h) (list l)
  ...| no  h∉l = _∩_ {{eq _≟_}} (t , p2 p) l
  ...| yes h∈l = cons1-dup {{eq _≟_}} h (_∩_ {{eq _≟_}} (t , p2 p) l)

  ∩-tail : {A : Set}{{eq : Eq A}}{a : A}{R S : List1 A}
         → a ∉l list S → (cons1-dup a R) ∩ S ≡ R ∩ S
  ∩-tail {{eq _≟_}} {a = a} {R = (rs , pR)} {(ss , pS)} hip 
    with A.any (_≟_ a) rs 
  ...| yes a∈R = refl
  ...| no  a∉R with A.any (_≟_ a) ss
  ...| yes a∈S = ⊥-elim (hip a∈S)
  ...| no  a∉S = refl

  -- Intersection of normal lists
  intersect : {A : Set}{{eq : Eq A}} → List A → List A → List1 A
  intersect [] l = nub l 
  intersect {{eq _≟_}} (a ∷ as) l with A.any (_≟_ a) l
  ...| yes a∈l = cons1-dup {{eq _≟_}} a (intersect {{eq _≟_}} as l)
  ...| no  a∉l = intersect {{eq _≟_}} as l
  
  -- Union
  _∪_ : {A : Set}{{eq : Eq A}} → List1 A → List1 A → List1 A
  ([] , unit)    ∪ l = l
  (a ∷ as , pas) ∪ b = cons1-dup a ((as , p2 pas) ∪ b)

  -- Concatenation 
  _++1_ : {A : Set}{{eq : Eq A}} → List A → List A → List1 A
  []       ++1 l = nub l
  (a ∷ as) ++1 b = cons1-dup a (as ++1 b)

  -- Mapping without guarantees from f.
  -- Note that by forcing non-duplicate elements we
  -- cannot guarantee that map is a list homomorphism.
  -- consider (map (const 1)), for instance.
  map1 : {A B : Set}{{eqA : Eq A}}{{eqB : Eq B}}
       → (A → B) → List1 A → List1 B
  map1 f ([] , unit)    = nil1
  map1 f (a ∷ as , pas) = cons1-dup (f a) (map1 f (as , p2 pas))

  concatMap1 : {A B : Set}{{eqA : Eq A}}{{eqB : Eq B}}
             → (A → List1 B) → List A → List1 B
  concatMap1 f []       = nil1
  concatMap1 f (a ∷ as) = f a ∪ (concatMap1 f as)
