\begin{code}
open import Prelude
open import Repo.Definitions

open Eq {{...}}

open import Repo.Data.PMap1 FileId as FileMap 
  using (dom; lkup; empty; _≈_; ≈-trans;  _∉_; lkup⇒∈)
open import Repo.Data.PMap1.Union FileId

open import Repo.Data.List1
open import Data.List.Any as Any using ()
open import Data.List.All as All using ()

open import Data.Nat using (_≤_; _≤?_)

module Excerpts where
  -- We are going to present a slightly different model
  -- from the one presented in section 6.

  
  instance
    ℕ-eq : Eq ℕ
    ℕ-eq = eq-ℕ

    eq-× : {A B : Set}{{eqA : Eq A}}{{eqB : Eq B}}
         → Eq (A × B)
    eq-× {A} {B} {{eq _≟A_}} {{eq _≟B_}} = eq decide
      where
        pair-inj : {A B : Set}{a c : A}{b d : B}
                 → a , b ≡ c , d → a ≡ c × b ≡ d
        pair-inj refl = refl , refl

        decide : (ab ab' : A × B) → Dec (ab ≡ ab')
        decide (a1 , b1) (a2 , b2) with a1 ≟A a2
        ...| no  a1≢a2 = no (a1≢a2 ∘ p1 ∘ pair-inj)
        ...| yes a1≡a2 with b1 ≟B b2
        ...| no  b1≢b2 = no (b1≢b2 ∘ p2 ∘ pair-inj)
        ...| yes b1≡b2 = yes (cong₂ _,_ a1≡a2 b1≡b2)

  -- A Line is identified as the n-th line of a given file.
  Line : Set
  Line = FileId × ℕ
\end{code}


%<*file-defs>
\begin{code}
  init : {f : FileId} → Line
  init {f} = f , 0

  next : Line → Line
  next (f , n) = f , suc n
\end{code}
%</file-defs>

%<*repo-def>
\begin{code}
  𝑴 : Set
  𝑴 = FileMap.to1 ℕ × (Line → Maybe Bit*)
\end{code}
%</repo-def>
\begin{code}
  files : 𝑴 → FileMap.to1 ℕ
  files = p1

  content : 𝑴 → Line → Maybe Bit*
  content m l = (p2 m) l
\end{code}

%<*logic-def>
\begin{code}
  data Logic : Set where
    Hasnt : FileId → Logic
    Has   : FileId → ℕ → Logic
    _is_  : Line → Bit* → Logic
    _★_   : Logic → Logic → Logic
\end{code}
%</logic-def>

%<*sat-def>
\begin{code}
  data _⊨_ (m : 𝑴) : Logic → Set where
    V-Hasnt : ∀{f} 
            → f ∉ files m
            → m ⊨ Hasnt f

    V-Has : {f : FileId}{n n' : ℕ}
          → lkup f (files m) ≡ just n
          → n' ≤ n
          → m ⊨ Has f n'

    V-Is : {f : FileId}{n : ℕ}{b : Bit*}
         → content m (f , n) ≡ just b
         → m ⊨ ((f , n) is b)

    V-★ : {p q : Logic}{n₁ n₂ : FileMap.to1 ℕ}
        → (disj : disjoint {{eqA = eq-ℕ}} (n₁ , n₂))
        → files m ≈ union n₁ n₂ disj
        → (n₁ , content m) ⊨ p
        → (n₂ , content m) ⊨ q
        → m ⊨ (p ★ q)
\end{code}
%</sat-def>

%<*addr-f-def>
\begin{code}
  addr-f : Logic → List1 FileId
  addr-f (Hasnt x) = [ x ]₁
  addr-f (Has x x₁) = [ x ]₁
  addr-f (x is x₁) = [ p1 x ]₁
  addr-f (P ★ P₁) = addr-f P ∪ addr-f P₁
\end{code}
%</addr-f-def>

%<*addr-def>
\begin{code}
  addr : Logic → Line → Set
  addr (Hasnt _) l     = ⊥
  addr (Has x n) (f , fn) with x ≟-ℕ f
  ...| yes _ = fn ≤ n
  ...| no  _ = ⊥
  addr (x is v) l = x ≡ l
  addr (p ★ q) l  = addr p l × addr q l
\end{code}
%</addr-def>

%<*augmentation-lemma>
\begin{code}
  augment : {P : Logic}{c : Line → Maybe Bit*}
            (m m' : FileMap.to1 ℕ)(disj : disjoint {{eq-ℕ}} (m , m'))
          → addr-f P ∩ dom m' ≡ ([] , unit)
          → (m , c) ⊨ P
          → (union m m' disj , c) ⊨ P
\end{code}
%</augmentation-lemma>
\begin{code}
  augment = ?
\end{code}

%<*repo-language-def>
\begin{code}
  data Command : Set where
    touch : FileId → Command
    rmfile : FileId → Command
    insert : Line → Bit* → Command
    rmline : Line → Command
    replace : Line → Bit* → Bit* → Command
    _▸_ : Command → Command → Command
\end{code}
%</repo-language-def>

%<*mod-def>
\begin{code}
  mod : Command → List1 Line
  mod (touch x)       = [ (x , 0) ]₁
  mod (rmfile x)      = [ (x , 0) ]₁
  mod (insert line c) = [ line    ]₁
  mod (rmline x)      = [ x       ]₁
  mod (replace x x₁ x₂) = [ x     ]₁
  mod (c ▸ c₁) = mod c ∪ mod c₁
\end{code}
%</mod-def>

%<*isFrame-def>
\begin{code}
  not-addr : Logic → Line → Set
  not-addr R l = addr R l → ⊥

  isFrame : Logic → Command → Set
  isFrame R c with mod c
  ...| l , _ = All.All (not-addr R) l
\end{code}
%</isFrame-def>

\begin{code}
  postulate
    a-string : Bit*
    
  infixr 10 _▸_
  
  data Patch : Logic → Command → Logic → Set where
\end{code}

%<*repo-1>
\begin{code}
  repo1 : Command
  repo1 = touch 0 
        ▸ insert (init {0}) a-string
        ▸ touch 1
        ▸ replace (init {0}) a-string []
\end{code}
%</repo-1>

%<*proof-repo-1>
\begin{code}
  proof : Patch (Hasnt 0 ★ Hasnt 1) repo1 (((0 , 0) is []) ★ Has 1 0) 
\end{code}
%</proof-repo-1>
\begin{code}
  proof = ?
\end{code}
