open import Prelude
open import Repo.Definitions

open Eq {{...}}

open import Repo.Data.PMap1 FileId as FileMap 
  using (dom; lkup; disjoint; union; empty)

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
    Empty : Logic
    Has   : FileId → ℕ → Logic
    -- Has-≤ : FileId → ℕ → Logic
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
    V-Empty : dom (files m) ≡ ([] , unit)
            → m ⊨ Empty
    
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
        → files m ≡ union n₁ n₂ disj
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
  addr Empty l     = ⊥
  addr (Has x n) (f , fn) with x ≟-ℕ f
  ...| yes _ = fn ≤ n
  ...| no  _ = ⊥
  addr (x is v) l = x ≡ l
  addr (p ★ q) l  = addr p l × addr q l
  addr (p ∧ q) l  = addr p l ⊎ addr q l

  not-addr : Logic → Line → Set
  not-addr R l = addr R l → ⊥

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

  data Patch : Logic → Command → Logic → Set where
    P-touch : ∀{f}
            → Patch Empty (touch f) (Has f 0)

    P-rmfile : ∀{f}
             → Patch (Has f 0) (rmfile f) Empty
    
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

    P-frame : ∀{P Q R c}
            → Patch P c Q
            → isFrame R c
            → Patch (P ★ R) c (Q ★ R)

    -- I hope this makes sense... some soundness proof for this rule
    -- only would be desired. The others are more or less standard.
    --
    -- TOTHINK2: if I can prove that for R and c such that (isFrame R c)
    --           P ★ R ⇒ P , precondition-strengthtening saves me.
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

  patch1 : Patch Empty (touch 0) (Has 0 0)
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

  ★-comm : {R S : Logic} → R ★ S ⇒ S ★ R
  ★-comm {R} {S} mim hip = {!!}

  Hasn+1⇒Hasn : ∀{f n} → Has f (suc n) ⇒ Has f n
  Hasn+1⇒Hasn mim hip = {!!}

  ∧-imp : ∀{P P' Q} → P ⇒ P' → P ∧ Q ⇒ P' ∧ Q
  ∧-imp hip1 mim hip = {!!}

  ∧-elim2 : ∀{P Q} → P ∧ Q ⇒ Q
  ∧-elim2 mim hip = {!!}

  -- Looks like pre-condition strenghtening and postcondition weakening
  -- is the easier way to manipulate contexts...
  -- 
  -- That was already expected, I mean, this is by far the most important
  -- rule of Hoare calculus... idk why I didn't consider this before.
  proof : Patch Empty repo1 (((F 0 , 0) is []) ★ Has (F 1) 0)
  proof 
    = P-seq 
        P-touch
        (P-seq 
          P-insert 
          (P-seq (P-frame-pre-elim-1 
                    (P-pre-str ★-comm (P-frame P-touch 
                      ((either id (λ ())) All.∷ All.[]))) 
                 ((λ x → x) All.∷ All.[])) 
             (P-pre-str ★-comm 
               (P-frame 
                 (P-pre-str (∧-imp Hasn+1⇒Hasn) 
                    (P-post-wk ∧-elim2 P-replace)) 
               (id All.∷ All.[]))) ))      
        
