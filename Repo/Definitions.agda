open import Prelude

-- Some simple definitions we should stick to.
module Repo.Definitions where

  data Bit : Set where
    O : Bit
    I : Bit

  Bit* : Set
  Bit* = List Bit

  instance
    eq-bit : Eq Bit
    eq-bit = eq decide
      where
        decide : (a b : Bit) → Dec (a ≡ b)
        decide O O = yes refl
        decide O I = no (λ ())
        decide I I = yes refl
        decide I O = no (λ ())

  FileId : Set
  FileId = ℕ
