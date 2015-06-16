open import Prelude
open import Repo.Definitions
open import Repo.Data.PMap FileId as FileMap 
  using (_∈_; isFactor; factorₗ; factorᵣ) renaming (lkup' to fetch)

open import Repo.Data.List1
open import Data.List.Any as A using ()

module Repo.Models.Abs1 where
  
  𝑴 : Set
  𝑴 = FileMap.to Bit*

  -- And a separation logic language.
  data M-sl : Set where
    Empty : M-sl
    Has   : FileId → Bit* → M-sl
    Frame : M-sl → M-sl → M-sl

  -- addresses used in the predicate P
  addr : M-sl → List1 FileId
  addr Empty       = nil1
  addr (Has f _)   = cons1 f nil1 (λ ())
  addr (Frame p q) = addr p ∪ addr q

  -- When does a repository satisfy a predicate?
  data _⊨_ (m : 𝑴) : M-sl → Set where
    Empty : FileMap.dom m ≡ [] → m ⊨ Empty
    Has   : {f : FileId}{c : Bit*}
          → (prf : f ∈ m) → (fetch f m prf ≡ c)
          → m ⊨ Has f c
    Frame : {p q : M-sl}
          → (hip : isFactor m)
          → (factorₗ hip) ⊨ p 
          → (factorᵣ hip) ⊨ q
          → m ⊨ Frame p q

  data Command : Set where
    add : FileId → Command
    rmv : FileId → Command
    upd : FileId → Bit* → Bit* → Command

  add-inj : ∀{f g} → add f ≡ add g → f ≡ g
  add-inj refl = refl

  rmv-inj : ∀{f g} → rmv f ≡ rmv g → f ≡ g
  rmv-inj refl = refl

  upd-inj-1 : ∀{f a b g c d} → upd f a b ≡ upd g c d → f ≡ g
  upd-inj-1 refl = refl

  upd-inj-2 : ∀{f a b g c d} → upd f a b ≡ upd g c d → a ≡ c
  upd-inj-2 refl = refl

  upd-inj-3 : ∀{f a b g c d} → upd f a b ≡ upd g c d → b ≡ d 
  upd-inj-3 refl = refl

  instance
    eq-command : Eq Command
    eq-command = eq decide
      where
        _≟-Bit*_ : (a b : Bit*) → Dec (a ≡ b)
        _≟-Bit*_ = Eq.cmp eq-List

        decide : (x y : Command) → Dec (x ≡ y)
        decide (add f) (add j) with f ≟-ℕ j
        ...| yes f≡j = yes (cong add f≡j)
        ...| no  f≢j = no (f≢j ∘ add-inj)
        decide (add _) (rmv _) = no (λ ())
        decide (add _) (upd _ _ _) = no (λ ())
        decide (rmv _) (add _) = no (λ ())
        decide (rmv f) (rmv j) with f ≟-ℕ j
        ...| yes f≡j = yes (cong rmv f≡j)
        ...| no  f≢j = no (f≢j ∘ rmv-inj)
        decide (rmv _) (upd _ _ _) = no (λ ())
        decide (upd _ _ _) (add _) = no (λ ())
        decide (upd _ _ _) (rmv _) = no (λ ())
        decide (upd f a b) (upd j c d) with f ≟-ℕ j
        ...| no  f≢j = no (f≢j ∘ upd-inj-1)
        ...| yes f≡j with a ≟-Bit* c
        ...| no a≢c = no (a≢c ∘ upd-inj-2)
        ...| yes a≡c with b ≟-Bit* d
        ...| no b≢d = no (b≢d ∘ upd-inj-3)
        ...| yes b≡d rewrite f≡j | a≡c | b≡d 
           = yes refl
        

  Command* : Set
  Command* = List Command

  mod-c : Command → List1 FileId
  mod-c (add f) = cons1 f nil1 (λ ())
  mod-c (rmv f) = cons1 f nil1 (λ ())
  mod-c (upd f _ _) = cons1 f nil1 (λ ())

  mod : Command* → List1 FileId
  mod = concatMap1 mod-c
  

  [_] : Command → Command*
  [ c ] = c ∷ []

  -- Let's then create a simplistic command apply function.
  -- Our function will check no pre-conditions whatsoever.
  apply : Command → 𝑴 → 𝑴
  apply (add x)       = FileMap.insert x []
  apply (rmv x)       = FileMap.delete x
  apply (upd x x₁ x₂) = FileMap.alter (const (just x₂)) x

  -- Ofc, we need a list extension.
  apply* : Command* → 𝑴 → 𝑴
  apply* []      = id
  apply* (h ∷ t) = apply* t ∘ apply h

  data _<_>_ : M-sl → Command* → M-sl → Set where
    r-add : ∀{f} →    Empty    < [ add f     ] > Has f [] 
    r-rmv : ∀{f} →    Has f [] < [ rmv f     ] > Empty
    r-upd : ∀{f c d} → Has f c < [ upd f c d ] > Has f d
    r-seq : ∀{p q r c d}
          → p <  [ c ]  > q
          → q <    d    > r
          → p < (c ∷ d) > r
    r-frame : ∀{p q r c} 
            → p < [ c ] > q 
            → mod-c c ∩ addr r ≡ nil1
            → Frame p r < [ c ] > Frame q r

  -- Now we can start to prove that we can consider
  -- other derivable rules in our system!
  -- 
  -- This is a much more useful version of r-add. Where
  -- our repository doesn't need to contain a single file.
  add-frame : ∀{f r} 
            → (Empty < [ add f ] > Has f [])
            → f ∉l list (addr r)
            → Frame Empty r < [ add f ] > Frame (Has f []) r
  add-frame {f = f} {r = r} r-add hip
    = r-frame r-add (∩-tail {R = nil1} hip)
  add-frame (r-seq hip ())

  -- Yet, the interesting part is to prove that our
  -- implementation of 𝑴, that is, a FileMap managed
  -- according to apply, is sound!

  private
    map≡[]→m≡[] : ∀{a b}{A : Set a}{B : Set b}{l : List A}{f : A → B}
                → map f l ≡ [] → l ≡ []
    map≡[]→m≡[] {l = []} _ = refl
    map≡[]→m≡[] {l = x ∷ l} ()

  mutual
    seq-sound : {m : 𝑴}{P Q Q' : M-sl}{c : Command}{cs : Command*}
              → m ⊨ P
              → Q <  cs   > Q'
              → P < [ c ] > Q
              → (apply* cs (apply c m)) ⊨ Q'
    seq-sound {cs = []} pre h hs = soundness pre (r-seq hs h)
    seq-sound {cs = ._ ∷ .[]} pre r-add hs = {!!}
    seq-sound {cs = ._ ∷ .[]} pre r-rmv hs = {!!}
    seq-sound {cs = ._ ∷ .[]} pre r-upd hs = {!!}
    seq-sound {cs = x ∷ cs} pre (r-seq h h₁) hs = {!!}
    seq-sound {cs = x ∷ .[]} pre (r-frame h x₁) hs = {!!}
  
    soundness : {m : 𝑴}{P Q : M-sl}{patch : Command*}
              → m ⊨ P → P < patch > Q → apply* patch m ⊨ Q
    soundness (Empty x) r-add
      rewrite (map≡[]→m≡[] x) = Has (A.here refl) refl
    soundness pre r-rmv = {!!}
    soundness pre r-upd = {!!} 
    soundness {patch = c ∷ cs} pre (r-seq h hs) = {!!}
    soundness pre (r-frame h x) = {!!}
