open import Prelude

open import Repo.Data.PMap1 ℕ
open import Repo.Definitions
open import Repo.CSL.Syntax
open import Repo.CSL.SS

module Repo.CSL.Judgments where

  data safe (J Q : CSL)(s : Stack)(h : Heap) : C → ℕ → Set
    where
      safe0     : {c : C} 
                → safe J Q s h c 0

      safeSkip  : {n : ℕ} 
                → (s , h) ⊨ Q 
                → safe J Q s h C-Skip n

      safeStep : {n : ℕ}{hJ hF h' : Heap}{c c' : C}{s' : Stack}
               → (s , hJ) ⊨ J
               → (p : disjoint3 h hJ hF)
               → (step : (c , (s , union3 h hJ hF p)) ⟶ₛ (c' , (s' , h')))
               → ¬ (c' ≡ C-Abort)
               → ∃ (λ { (H , hJ') 
                   → Σ (disjoint3 H hJ' hF) 
                       (λ p → h' ≡ union3 H hJ' hF p × safe J Q s' H c' n) 
                   })
               → safe J Q s h c (suc n)

  ----------------------------------
  -- Testing

  s : ℕ → ℕ
  s = id

  command : C
  command = C-Alloc 1 (E-Const 0)

  prf : safe emp (E-Var 1 ↦ E-Const 0) s empty command 1
  prf = safeStep {!!} ({!!} , unit) (S-Alloc {!!}) (λ ()) 
        ((({!!} , {!!}) , ({!!} , {!!})) , (({!!} , {!!}) , ({!!} , safe0)))
