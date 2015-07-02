\begin{code}
open import Prelude
open import Data.List.Any as A using ()
open import Data.List.Properties using (map-id)
open import Relation.Binary.PropositionalEquality

module PMapParts where

  _∈l_ : {A : Set} → A → List A → Set _
  _∈l_ a m = A.Any (_≡_ a) m

  _∉l_ : {A : Set}{{eq : Eq A}}
      → A → List A → Set _
  a ∉l m = (a ∈l m) → ⊥
\end{code}

%<*noDups-mod-def>
\begin{code}
  noDups-mod : {A B : Set}{{eq : Eq B}} → (A → B) → List A → Set
  noDups-mod _ [] = Unit
  noDups-mod f (x ∷ l) = f x ∉l (map f l) × noDups-mod f l
  
  List1 : (A : Set){{eq : Eq A}} → Set
  List1 A = Σ (List A) (noDups-mod id)
\end{code}
%</noDups-mod-def>

\begin{code}
  postulate
    A : Set
    eqA : Eq A
    
  open Eq {{...}}
  
  private
    _≟_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)
    a₁ ≟ a₂ = Eq.cmp eqA a₁ a₂
\end{code}

%<*pmap1-def>
\begin{code}
  to1 : Set → Set
  to1 B = Σ (List (A × B)) (noDups-mod {{eqA}} p1)
\end{code}
%</pmap1-def>

%<*lkup-lift-def>
\begin{code}
  lkup : {B : Set} → A → to1 B → Maybe B
  lkup k ([] , unit) = nothing
  lkup k (x ∷ m , prf) with k ≟ p1 x
  ...| yes _ = just (p2 x)
  ...| no  _ = lkup k (m , p2 prf)

  lift : {B : Set} → to1 B → A → Maybe B
  lift m a = lkup a m  
\end{code}
%</lkup-lift-def>

%<*eq-modulo>
\begin{code}
  _≈_ : {B : Set} → to1 B → to1 B → Set
  m₁ ≈ m₂ = lift m₁ ≡ lift m₂
\end{code}
%</eq-modulo>

\begin{code}
  _∈_ : {B : Set} → A → to1 B → Set
  a ∈ m = A.Any ((_≡_ a) ∘ p1) (p1 m)

  _∉_ : {B : Set} → A → to1 B → Set
  a ∉ m = a ∈ m → ⊥
\end{code}

%<*disjoint-def>
\begin{code}
  disjoint : {B : Set} → to1 B × to1 B → Set
  disjoint (([] , unit)             , n) = Unit
  disjoint (((x , v) ∷ m , p , prf) , n)
    = x ∉ n × disjoint ((m , prf) , n) 
\end{code}
%</disjoint-def>

%<*disjoint-pi-def>
\begin{code}
  disjoint-proof-irrel : {B : Set}{m₁ m₂ : to1 B}
                       → (d1 d2 : disjoint (m₁ , m₂))
                       → d1 ≡ d2
\end{code}
%</disjoint-pi-def>
\begin{code}
  disjoint-proof-irrel = ?
\end{code}

%<*lemmas>
\begin{code}
  insert : {B : Set}(a : A)(b : B) → to1 B → to1 B
  insert-lemma : {B : Set}{k a : A}{b : B}{m : to1 B}
               → k ∉ m → k ≢ a → k ∉ insert a b m
               
  remove : {B : Set}(a : A) → to1 B → to1 B
  remove-lemma : {B : Set}{a k : A}(m : to1 B) 
               → k ∉ m → k ∉ remove a m
  remove-correct : {B : Set}{a : A}(m : to1 B)
                 → a ∉ remove a m
\end{code}
%</lemmas>
\begin{code}
  insert = ?
  insert-lemma = ?
  remove = ?
  remove-lemma = ?
  remove-correct = ?
\end{code}

%<*focus-star-def>
\begin{code}
  focus* : {B : Set} → List A → to1 B → Σ (to1 B × to1 B) disjoint
\end{code}
%</focus-star-def>
\begin{code}
  focus* = ?
\end{code}

%<*union-def>
\begin{code}
  union : {B : Set} → (m₁ m₂ : to1 B) → disjoint (m₁ , m₂) → to1 B
\end{code}
%</union-def>
\begin{code}
  union = ?
\end{code}

