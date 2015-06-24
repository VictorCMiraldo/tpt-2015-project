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

module Repo.Models.Abs2 where
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

  -- since lines are numbers, init is Zero, next is Succ.
  init : {f : FileId} → Line
  init {f} = f , 0

  next : Line → Line
  next (f , n) = f , suc n
  
  -- The repository, then, is a map of files and for every line
  -- a content map. Note that this map returns a Maybe,
  -- in case we ask for the 10th line in a 5-line file, for instance.
  -- 
  𝑴 : Set
  𝑴 = FileMap.to1 ℕ × (Line → Maybe Bit*)

  files : 𝑴 → FileMap.to1 ℕ
  files = p1

  content : 𝑴 → Line → Maybe Bit*
  content m l = (p2 m) l

  -- Having specified what a repository "is", we need
  -- an assertion language over it.
  --
  data Logic : Set where
    -- Repo-specific reasoning.
    Hasnt : FileId → Logic
    
    Has   : FileId → ℕ → Logic

    _is_  : Line → Bit* → Logic

    -- Separation Constructs.
    _★_   : Logic → Logic → Logic

    -- Classical consructs
    _∧_ : Logic → Logic → Logic

  infix 20 _is_ 
  infixl 35 _∧_ 
  infixl 30 _★_ 

  -- And a validity relation
  --
  data _⊨_ (m : 𝑴) : Logic → Set where
    -- A repository is empty when it has no files
    V-Hasnt : ∀{f} 
            → f ∉ files m
            → m ⊨ Hasnt f
    
    {-
    -- A repository has a given file if looking up how many lines it
    -- has returns a number.
    V-Has : {f : FileId}
          → (prf : ∃ (λ n → lkup {{eqA = eq-ℕ}} f (files m) ≡ just n))
          → m ⊨ Has f (p1 prf)
    -}

    -- Or, a file has at least n lines.
    V-Has : {f : FileId}{n n' : ℕ}
          → lkup f (files m) ≡ just n
          → n' ≤ n
          → m ⊨ Has f n'

    -- The contents of line n, in file f is b.
    V-Is : {f : FileId}{n : ℕ}{b : Bit*}
         → content m (f , n) ≡ just b
         → m ⊨ ((f , n) is b)

    -- A separation statement occurs at the file lvl.
    V-★ : {p q : Logic}{n₁ n₂ : FileMap.to1 ℕ}
        → (disj : disjoint {{eqA = eq-ℕ}} (n₁ , n₂))
        → files m ≈ union n₁ n₂ disj
        → (n₁ , content m) ⊨ p
        → (n₂ , content m) ⊨ q
        → m ⊨ (p ★ q)

    -- And some classical logical constructs, of course.
    V-∧ : {p q : Logic}
        → m ⊨ p
        → m ⊨ q
        → m ⊨ (p ∧ q)

  -- Which allows us to estabilish a implication notion.
  -- 
  -- TOTHINK: how does it relate to define operators outside our
  --          Logic datatype and use these operators on our side rules?
  --          I mean, what would happen by defining _∧_ in the same way?
  --          This kind of allows us to keep with the minimum core only.
  _⇒_ : Logic → Logic → Set
  R ⇒ S = (m : 𝑴) → m ⊨ R → m ⊨ S

  -- Now, we are also going to change a bit our address function.
  -- Given a formula and an address, does this formula references
  -- this specific address?
  addr : Logic → Line → Set
  addr (Hasnt _) l     = ⊥
  addr (Has x n) (f , fn) with x ≟-ℕ f
  ...| yes _ = fn ≤ n
  ...| no  _ = ⊥
  addr (x is v) l = x ≡ l
  addr (p ★ q) l  = addr p l × addr q l
  addr (p ∧ q) l  = addr p l ⊎ addr q l

  not-addr : Logic → Line → Set
  not-addr R l = addr R l → ⊥

  -- An address function is a good idea too!
  addr-f : Logic → List1 FileId
  addr-f (Hasnt x) = [ x ]₁
  addr-f (Has x x₁) = [ x ]₁
  addr-f (x is x₁) = [ p1 x ]₁
  addr-f (P ★ P₁) = addr-f P ∪ addr-f P₁
  addr-f (P ∧ P₁) = addr-f P ∪ addr-f P₁

  -----------------------------
  -- Command language

  data Command : Set where
    -- Creates a new file
    touch : FileId → Command

    -- Removes a file
    rmfile : FileId → Command

    -- Inserts a line after a given line
    insert : Line → Bit* → Command

    -- Removes a line
    rmline : Line → Command

    -- Replaces the contents of a line.
    replace : Line → Bit* → Bit* → Command
  
    -- A sequence of commands is a command
    _▸_ : Command → Command → Command

  infixr 10 _▸_

  -- Our commands must be injective.
  touch-inj : ∀{f g} → touch f ≡ touch g → f ≡ g
  touch-inj refl = refl

  rmfile-inj : ∀{f g} → rmfile f ≡ rmfile g → f ≡ g
  rmfile-inj refl = refl

  insert-inj : ∀{lf cf lg cg}
             → insert lf cf ≡ insert lg cg
             → (lf ≡ lg) × (cf ≡ cg)
  insert-inj refl = refl , refl

  rmline-inj : ∀{lf lg} → rmline lf ≡ rmline lg → lf ≡ lg
  rmline-inj refl = refl

  replace-inj-1 : ∀{lf lg bf bg bf' bg'}
                → replace lf bf bf' ≡ replace lg bg bg'
                → lf ≡ lg
  replace-inj-1 refl = refl

  replace-inj-2 : ∀{lf lg bf bg bf' bg'}
                → replace lf bf bf' ≡ replace lg bg bg'
                → bf ≡ bg
  replace-inj-2 refl = refl

  replace-inj-3 : ∀{lf lg bf bg bf' bg'}
                → replace lf bf bf' ≡ replace lg bg bg'
                → bf' ≡ bg'
  replace-inj-3 refl = refl

  seq-inj : ∀{c1 c2 d1 d2}
          → (c1 ▸ c2) ≡ (d1 ▸ d2) → (c1 ≡ d1) × (c2 ≡ d2)
  seq-inj refl = refl , refl

  -- What are the addresses a command modifies?
  mod : Command → List1 Line
  mod (touch x)       = [ (x , 0) ]₁
  mod (rmfile x)      = [ (x , 0) ]₁
  mod (insert line c) = [ line    ]₁
  mod (rmline x)      = [ x       ]₁
  mod (replace x x₁ x₂) = [ x     ]₁
  mod (c ▸ c₁) = mod c ∪ mod c₁

  -- Before talking about patches, we need a notion of
  -- "disjointness" between commands and formulas.
  -- A formula R is a frame for a given command iff:
  -- 
  --  No line "modified" by the command will be 
  --  referenced in the formula.
  -- 
  -- Or, 
  isFrame : Logic → Command → Set
  isFrame R c with mod c
  ...| l , _ = All.All (not-addr R) l

  -- Some auxiliar lemmas
  lemma-∩ : {A : Set}{{eqA : Eq A}}{P Q : List1 A}{x : A} 
          → P ∩ Q ≡ ([] , unit) → x ∈l list P → x ∉l list Q
  lemma-∩ hip x∈P = {!!}

  lemma-∩-∪-1 : {A : Set}{{eqA : Eq A}}{P Q R : List1 A}{x : A} 
              → (P ∪ R) ∩ Q ≡ ([] , unit)
              → P ∩ Q ≡ ([] , unit)
  lemma-∩-∪-1 hip = {!!}

  lemma-∩-∪-2 : {A : Set}{{eqA : Eq A}}{P Q R : List1 A}{x : A} 
              → (R ∪ P) ∩ Q ≡ ([] , unit)
              → P ∩ Q ≡ ([] , unit)
  lemma-∩-∪-2 hip = {!!}

  lemma-dom-lift : {m : FileMap.to1 ℕ}{x : FileId}
                 → x ∉l list (dom m)
                 → x ∉ m
  lemma-dom-lift = {!!} 


  -- The (Empty : Logic) represents a problem for this augment!
  -- We should have other means of refering to empty repositories.
  -- For instance, for adding files, we could require a "not have f" instead
  -- of requiring it to be empty! I mean, we know how to add files to non-empty folders.
  augment : {P : Logic}{c : Line → Maybe Bit*}
            (m m' : FileMap.to1 ℕ)(disj : disjoint {{eq-ℕ}} (m , m'))
          → addr-f P ∩ dom m' ≡ ([] , unit)
          → (m , c) ⊨ P
          → (union m m' disj , c) ⊨ P
  augment {P = Hasnt x} m m' disj Phip (V-Hasnt hip) 
    with ¬union-uni x disj hip (lemma-dom-lift (lemma-∩ Phip (Any.here refl)))
  ...| r = V-Hasnt r
  augment {Has x x₁} m m' disj Phip (V-Has f fn) 
    = V-Has (trans (union-lkup-1 disj x (lkup⇒∈ m x f)) f) fn
  augment {._ is x₁} m m' disj Phip (V-Is x) 
    = V-Is x
  augment {P ★ P₁} m m' disj Phip (V-★ {n₁ = n₁} {n₂} disj₁ x hip hip₁) 
    = let dn2m' = (union-disjoint-2 n₁ n₂ m' disj₁ (disjoint-lift m m' (union n₁ n₂ disj₁) disj x))
          dn1m' = (union-disjoint-1 n₁ n₂ m' disj₁ (disjoint-lift m m' (union n₁ n₂ disj₁) disj x))
      in V-★ lemma 
             (≈-trans x (sym (union-assoc disj₁ dn2m' dn1m'))) 
             hip 
             (augment n₂ m' dn2m' (lemma-∩-∪-2 {Q = dom m'} Phip) hip₁)
    where
      lemma : disjoint (n₁ , union n₂ m' _)
      lemma = {!!}
  augment {P ∧ P₁} m m' disj Phip (V-∧ hip hip₁) 
    = V-∧ (augment m m' disj (lemma-∩-∪-1 Phip) hip) 
          (augment m m' disj (lemma-∩-∪-2 Phip) hip₁)

  -- And, ofc, isomorphic maps satisfy the same formulas.
  ⊨-≈ : {P : Logic}{m₁ m₂ : FileMap.to1 ℕ}{c : Line → Maybe Bit*}
      → m₁ ≈ m₂ → (m₁ , c) ⊨ P → (m₂ , c) ⊨ P
  ⊨-≈ = {!!}

  data Patch : Logic → Command → Logic → Set where
    P-touch : ∀{f}
            → Patch (Hasnt f) (touch f) (Has f 0)

    P-rmfile : ∀{f}
             → Patch (Has f 0) (rmfile f) (Hasnt f)
    
    P-insert : ∀{f n bs}
             → Patch (Has f n) 
                          (insert (f , n) bs) 
                     (Has f (suc n) ∧ ((f , n) is bs))

    P-replace : ∀{f n bs bs'}
              → Patch (Has f n ∧ ((f , n) is bs)) 
                             (replace (f , n) bs bs') 
                      (Has f n ∧ ((f , n) is bs')) 

    P-seq : ∀{P S Q c d}
          → Patch P c S
          → Patch S d Q
          → Patch P (c ▸ d) Q

    P-frame-1 : ∀{P Q R c}
              → Patch P c Q
              → isFrame R c
              → Patch (P ★ R) c (Q ★ R)

    P-frame-2 : ∀{P Q R c}
              → Patch P c Q
              → isFrame R c
              → Patch (R ★ P) c (R ★ Q)

    -- I hope this makes sense... some soundness proof for this rule
    -- only would be desired. The others are more or less standard.
    --
    -- TOTHINK2: if I can prove that for R and c such that (isFrame R c)
    --           P ★ R ⇒ P , precondition-strengthtening saves me.
    {-
    P-frame-pre-elim-1 : ∀{P Q R c}
                       → Patch (P ★ R) c Q
                       → isFrame R c
                       → Patch P c Q
  
    P-pre-and-1 : ∀{P P' Q c}
                → Patch P c Q
                → Patch (P ∧ P') c Q

    P-pre-and-2 : ∀{P P' Q c}
                → Patch P c Q
                → Patch (P' ∧ P) c Q

    P-post-and : ∀{P Q Q' c}
               → Patch P c Q
               → Patch P c Q'
                 → Patch P c (Q ∧ Q')
    -}

    P-pre-str : ∀{P P' Q c}
              → P ⇒ P'
              → Patch P' c Q
              → Patch P c Q

    P-post-wk : ∀{P Q Q' c}
              → Q' ⇒ Q
              → Patch P c Q'
              → Patch P c Q

  Indep : ∀{P₁ Q₁ P₂ Q₂ c₁ c₂}
        → Patch P₁ c₁ Q₁
        → Patch P₂ c₂ Q₂
        → Set
  Indep {P1} {Q1} {P2} {Q2} {c1} {c2} _ _ 
    = isFrame (P2 ∧ Q2) c1 × isFrame (P1 ∧ Q1) c2

  ------------------------------
  -- Test case 1: Independent Patches

  patch1 : Patch (Hasnt 0) (touch 0) (Has 0 0)
  patch1 = P-touch

  mystring1 : List Bit
  mystring1 = []

  patch2 : Patch (Has 1 8) (insert (1 , 8) mystring1) 
                 ((Has 1 9) ∧ ((1 , 8) is mystring1))
  patch2 = P-insert

  prf : Indep patch1 patch2
  prf = (either id (either id (λ ())) All.∷ All.[]) , either id id All.∷ All.[]

  ------------------------------
  -- Test case 2: Repo structure

  mystring : List Bit
  mystring = []

  F_ : ℕ → ℕ
  F i = i

  repo1 : Command
  repo1 = touch (F 0) 
        ▸ insert (init {0}) mystring
        ▸ touch (F 1)
        ▸ replace (init {0}) mystring []

  -- Here we see we need to set up a different notion of equality too!
  -- Assuming (a b : to1 B) s.t. disjoint (a , b),
  -- we have: (a ∪ b) = (a ++ b) ≢ (b ++ a) = (b ∪ a)
  --
  -- our equality must not rely on order!
  --
  ★-comm : {R S : Logic} → R ★ S ⇒ S ★ R
  ★-comm mim (V-★ disj x hip hip₁) = V-★ (disjoint-comm disj) (trans x (union-comm disj)) hip₁ hip

  Hasn+1⇒Hasn : ∀{f n} → Has f (suc n) ⇒ Has f n
  Hasn+1⇒Hasn mim (V-Has x x₁) = V-Has x (dec-leq x₁)
    where   
      dec-leq : ∀{m n} → suc n ≤ m → n ≤ m
      dec-leq {zero} ()
      dec-leq {suc m} {zero}  hip = Data.Nat.z≤n
      dec-leq {suc m} {suc n} (Data.Nat.s≤s hip) = Data.Nat.s≤s (dec-leq hip)

  ∧-imp : ∀{P P' Q} → P ⇒ P' → P ∧ Q ⇒ P' ∧ Q
  ∧-imp hip1 mim (V-∧ hip hip₁) = V-∧ (hip1 mim hip) hip₁

  ∧-elim2 : ∀{P Q} → P ∧ Q ⇒ Q
  ∧-elim2 mim (V-∧ hip hip₁) = hip₁

  ∧-elim1 : ∀{P Q} → P ∧ Q ⇒ P
  ∧-elim1 mim (V-∧ hip hip₁) = hip

  experiment-1 : ∀{P R} → P ★ R ⇒ P
  experiment-1 mim (V-★ {n₁ = n1} {n₂ = n2} disj x hip hip₁) 
    = ⊨-≈ (sym x) (augment n1 n2 disj {!!} hip)

  -- Looks like pre-condition strenghtening and postcondition weakening
  -- is the easier way to manipulate contexts...
  -- 
  -- That was already expected, I mean, this is by far the most important
  -- rule of Hoare calculus... idk why I didn't consider this before.
  proof : Patch (Hasnt 0 ★ Hasnt 1) repo1 (((F 0 , 0) is []) ★ Has (F 1) 0)
  proof 
    = P-seq (P-frame-1 P-touch ((λ x → x) All.∷ All.[])) 
      (P-seq (P-frame-1 P-insert ((λ z → z) All.∷ All.[])) 
      (P-seq (P-frame-2 P-touch ((either (λ x → x) (λ ())) All.∷ All.[])) 
      (P-frame-1 (P-pre-str (∧-imp Hasn+1⇒Hasn) (P-post-wk ∧-elim2 P-replace)) (id All.∷ All.[])) ))  
        
