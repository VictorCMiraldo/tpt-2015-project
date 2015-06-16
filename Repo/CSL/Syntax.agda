open import Prelude
open import Repo.Data.PMap1 ℕ as ℕmap
open import Repo.Data.List1

-- In this module we define a subset of
-- the language introduced by Vafeiadis
--
module Repo.CSL.Syntax where

  -- Our simple language:
  data E : Set where
    E-Var   : ℕ → E
    E-Const : ℕ → E
    E-Plus  : E → E → E

  data B : Set where
    B-Eq   : E → E → B
    B-Conj : B → B → B
    B-Neg  : B → B

  data C : Set where
    C-Skip    : C
    C-Abort   : C
    C-Atomic  : C → C
    C-Seq     : C → C → C 
    C-Par     : C → C → C
    C-Assign  : ℕ → E → C
    C-Read    : ℕ → E → C
    C-Write   : E → E → C
    C-Alloc   : ℕ → E → C
    C-Dispose : E → C
    C-If      : B → C → C → C

  Val : Set
  Val = ℕ

  Stack : Set
  Stack = ℕ → Val

  _[_↦_] : Stack → ℕ → Val → Stack
  (s [ x ↦ j ]) n with x ≟-ℕ n
  ...| yes _ = j
  ...| no  _ = s n

  -- With denotations for expressions within a stack.
  ⟦_⟧e : E → Stack → Val
  ⟦ E-Var x     ⟧e s = s x
  ⟦ E-Const x   ⟧e s = x
  ⟦ E-Plus x x₁ ⟧e s = ⟦ x ⟧e s + ⟦ x₁ ⟧e s

  ⟦_⟧b : B → Stack → Bool
  ⟦_⟧b (B-Eq x x₁) s with ⟦ x ⟧e s ≟-ℕ ⟦ x₁ ⟧e s
  ...| no _   = false
  ...| yes _  = true
  ⟦_⟧b (B-Conj x x₁) s = ⟦ x ⟧b s and ⟦ x₁ ⟧b s
  ⟦_⟧b (B-Neg x) s = not (⟦ x ⟧b s)

  -- The heap is a finite map. 
  Heap : Set
  Heap = ℕmap.to1 Val

  -- Variables a command writes on.
  wr : C → List1 ℕ 
  wr C-Skip = nil1
  wr C-Abort = nil1
  wr (C-Atomic c) = wr c
  wr (C-Seq c c₁) = wr c ∪ wr c₁
  wr (C-Par c c₁) = wr c ∪ wr c₁
  wr (C-Assign x x₁) = [ x ]₁
  wr (C-Read x x₁) = nil1
  wr (C-Write x x₁) = nil1
  wr (C-Alloc x x₁) = [ x ]₁
  wr (C-Dispose x) = nil1
  wr (C-If x c c₁) = wr c ∪ wr c₁

  ------------------------
  -- Assertion Language --
  ------------------------

  data CSL : Set where
    Const : Bool → CSL
    _⇒_   : CSL → CSL → CSL
    _★-_  : CSL → CSL → CSL
    _★_   : CSL → CSL → CSL
    emp   : CSL
    _↦_   : E → E → CSL
    _∨_   : CSL → CSL → CSL
    _∧_   : CSL → CSL → CSL
    Exists : 

  _⊨_ : Stack × Heap → CSL → Set
  (s , h) ⊨ (Const true)  = Unit
  (s , h) ⊨ (Const false) = ⊥
  (s , h) ⊨ emp      = dom h ≡ nil1
  (s , h) ⊨ (e ↦ e′) = is-singleton-on-with h (⟦ e ⟧e s) (⟦ e′ ⟧e s)
  (s , h) ⊨ (p ★ q)  = Σ (Heap × Heap) pred
    where pred : (Heap × Heap) → Set
          pred (h₁ , h₂) = Σ (disjoint (h₁ , h₂)) (λ d → h ≡ union h₁ h₂ d)
                         × ((s , h₁) ⊨ p) × ((s , h₂) ⊨ q)
  (s , h) ⊨ (p ★- q) = (h₁ : Heap) (d : disjoint (h₁ , h)) →
                         (s , h₁) ⊨ p → (s , union h₁ h d) ⊨ q
  (s , h) ⊨ (p ⇒ q)  = (s , h) ⊨ p → (s , h) ⊨ q

  
