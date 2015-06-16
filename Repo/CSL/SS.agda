open import Prelude

open import Repo.Data.PMap1 ℕ {{eq-ℕ}} as ℕmap

open import Repo.Definitions
open import Repo.CSL.Syntax

-- Small step semantics for the syntax defined in `Repo.CSL.Syntax`.
module Repo.CSL.SS where

  Conf : Set
  Conf = C × (Stack × Heap)

  stack : Conf → Stack
  stack (_ , (s , _)) = s

  heap : Conf → Heap
  heap (_ , (_ , h)) = h

  com : Conf → C
  com (c , _) = c

  mutual
    data _⟶ₛ_ : Conf → Conf → Set where
      -- Base rules
      S-Assign : ∀{x e s h} 
        → (C-Assign x e , (s , h)) ⟶ₛ (C-Skip , (s [ x ↦ ⟦ e ⟧e s ] , h))
      S-Read : ∀{x e s h v}
        → lift h (⟦ e ⟧e s) ≡ just v
        → (C-Read x e , (s , h)) ⟶ₛ (C-Skip , (s [ x ↦ v ] , h))
      S-ReadAbort : ∀{x e s h}
        → lift h (⟦ e ⟧e s) ≡ nothing
        → (C-Read x e , (s , h)) ⟶ₛ (C-Abort , (s , h))
      S-Write : ∀{e e′ s h}
        → (p : ⟦ e ⟧e s ∈ h)
        → (C-Write e e′ , (s , h)) 
          ⟶ₛ (C-Skip , (s , change (⟦ e ⟧e s) (⟦ e′ ⟧e s) h p))
      S-WriteAbort : ∀{e e′ s h}
        → ⟦ e ⟧e s ∉ h
        → (C-Write e e′ , (s , h)) ⟶ₛ (C-Abort , (s , h))
      S-ParSkip : ∀{s h}
        → (C-Par C-Skip C-Skip , (s , h)) ⟶ₛ (C-Skip , (s , h))
      S-Alloc : ∀{x e s h l}
        → (p : l ∉ h) 
        → (C-Alloc x e , (s , h)) 
          ⟶ₛ (C-Skip , (s [ x ↦ l ] , add-with-prf l (⟦ e ⟧e s) h p))

      -- Inductive rules
      S-SeqSkip : ∀{c s h}
        → ((C-Seq C-Skip c) , (s , h)) ⟶ₛ (c , (s , h))
      S-SeqStep : ∀{c₁ c₂ s h c₁′ s′ h′}
        → (c₁ , (s , h)) ⟶ₛ (c₁′ , (s′ , h′))
        → ((C-Seq c₁ c₂) , (s , h)) ⟶ₛ ((C-Seq c₁′ c₂) , (s′ , h′)) 
      S-SeqAbort : ∀{c₁ c₂ s h s′ h′}
        → (c₁ , (s , h)) ⟶ₛ (C-Abort , (s′ , h′))
        → ((C-Seq c₁ c₂) , (s , h)) ⟶ₛ (C-Abort , (s′ , h′))
      S-AtomAbort : ∀{c s h s′ h′}
        → (c , (s , h)) ⟶ₛ* (C-Abort , (s′ , h′))
        → (C-Atomic c , (s , h)) ⟶ₛ (C-Abort , (s′ , h′))
      S-AtomSkip : ∀{c s h s′ h′}
        → (c , (s , h)) ⟶ₛ* (C-Skip , (s′ , h′))
        → (C-Atomic c , (s , h)) ⟶ₛ (C-Skip , (s′ , h′))
      S-IfTrue : ∀{b c₁ c₂ s h}
        → ⟦ b ⟧b s ≡ true
        → (C-If b c₁ c₂ , (s , h)) ⟶ₛ (c₁ , (s , h))
      S-IfFalse : ∀{b c₁ c₂ s h}
        → ⟦ b ⟧b s ≡ false
        → (C-If b c₁ c₂ , (s , h)) ⟶ₛ (c₂ , (s , h))
      S-Par1 : ∀{c₁ c₁′ c₂ s h s′ h′}
        → (c₁ , (s , h)) ⟶ₛ (c₁′ , (s′ , h′))
        → (C-Par c₁ c₂ , (s , h)) ⟶ₛ (C-Par c₁′ c₂ , (s′ , h′))
      S-Par2 : ∀{c₁ c₂ c₂′ s h s′ h′}
        → (c₂ , (s , h)) ⟶ₛ (c₂′ , (s′ , h′))
        → (C-Par c₁ c₂ , (s , h)) ⟶ₛ (C-Par c₁ c₂′ , (s′ , h′))
      S-Par1Abort : ∀{c₁ c₂ s h s′ h′}
        → (c₁ , (s , h)) ⟶ₛ (C-Abort , (s′ , h′))
        → (C-Par c₁ c₂ , (s , h)) ⟶ₛ (C-Abort , (s′ , h′))
      S-Par2Abort : ∀{c₁ c₂ s h s′ h′}
        → (c₂ , (s , h)) ⟶ₛ (C-Abort , (s′ , h′))
        → (C-Par c₁ c₂ , (s , h)) ⟶ₛ (C-Abort , (s′ , h′))
      
    data _⟶ₛ*_ : Conf → Conf → Set where
      nil   : ∀{c}        → c ⟶ₛ* c
      step  : ∀{c₁ c₂ c₃} → c₁ ⟶ₛ c₂ → c₂ ⟶ₛ* c₃ → c₁ ⟶ₛ* c₃ 
    
      
  DoesntAbort : Conf → Set
  DoesntAbort (c , (s , h)) 
    = {s' : Stack}{h' : Heap} → ¬ ((c , (s , h)) ⟶ₛ* (C-Abort , (s' , h')))
                              
