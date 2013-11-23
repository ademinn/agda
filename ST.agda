{-
  Author: Jan Malakhovski
  Date: Nov 17, 2013
-}

-- An excercise on de Bruijn Church-style Simply Typed Lambda Calculus
-- and its properties.
module ST where

open import OXIj.BrutalDepTypes
open Data-List
open Data-Any
open ≡-Prop

module TransReflClosure where
  -- Transitive reflexive closure of a relation
  data _✴ {A} (R : A → A → Set) : A → A → Set where
    ε  : {a : A} → (R ✴) a a -- Reflexivity
    _∷✴_ : {a b c : A} → R a b → (R ✴) b c → (R ✴) a c
  -- Structurally ─ a list with two indexes, where each cons
  -- connects them by relation R.

  -- Transitivity
  _++✴_ : ∀ {A} {R : A → A → Set} {a b c} → (R ✴) a b → (R ✴) b c → (R ✴) a c
  ε ++✴ bs = bs
  (a ∷✴ as) ++✴ bs = a ∷✴ (as ++✴ bs)

  -- Closure of a closure is simply a closure
  concat✴ : ∀ {A} {R : A → A → Set} {x y} → ((R ✴) ✴) x y → (R ✴) x y
  concat✴ ε = ε
  concat✴ (y' ∷✴ y0) = y' ++✴ concat✴ y0

  -- General map between closures
  -- Comprehensible when (u ≡ id).
  map✴ : ∀ {A B} {R : A → A → Set} {S : B → B → Set} (u : A → B)
       → (∀ {x y} → R x y → S (u x) (u y))
       → ∀ {x y} → (R ✴) x y → (S ✴) (u x) (u y)
  map✴ u f ε = ε
  map✴ u f (y ∷✴ y') = f y ∷✴ map✴ u f y'

open TransReflClosure public

module GeneralizedCurchRosser where
  -- Confluent relation
  Confluent : ∀ {A} (R : A → A → Set) → Set
  Confluent {A} R = ∀ {a b c} → R a b → R a c → Σ A λ d → R b d ∧ R c d

  {- Given a, b, c, R a b, and R a c

        R
      a - b
     R|
      c

     Gives d, R b d, and R c d

         b
         ⋮ R
     c ⋯ d
       R

     to complete the square

     a - b
     |   ⋮
     c ⋯ d
  -}

  module Proof where
    -- column building
    yCR : ∀ {A : Set} {R : A → A → Set}
        → Confluent R → ∀ {a b c}
        → R a b → (R ✴) a c
        → Σ A λ d → (R ✴) b d ∧ R c d
    yCR cR {a} {b} .{a} r ε   = b , (ε , r)
    yCR cR {a} {b} {c} r (l ∷✴ ls)  = d , Rbb1 ∷✴ R✴b1d , Rcd
        where
        Rbb1 = _∧_.fst (Σ.projr (cR r l))
        Ra1b1 = _∧_.snd (Σ.projr (cR r l))
        R✴b1d = _∧_.fst (Σ.projr (yCR cR Ra1b1 ls))
        Rcd = _∧_.snd (Σ.projr (yCR cR Ra1b1 ls))
        d = Σ.projl (yCR cR Ra1b1 ls)

    -- concatenating columns into a table
    xCR : ∀ {A} {R : A → A → Set} → Confluent R → Confluent (R ✴)
    xCR cR {a} .{a} {c} ε R✴ac = c , R✴ac , ε
    xCR cR {a} {b} {c} (l ∷✴ ls) R✴ac = d , R✴bd , Rcc1 ∷✴ R✴c1d
        where
        R✴a1c1 = _∧_.fst (Σ.projr (yCR cR l R✴ac))
        Rcc1 = _∧_.snd (Σ.projr (yCR cR l R✴ac))
        R✴bd = _∧_.fst (Σ.projr (xCR cR ls R✴a1c1))
        R✴c1d = _∧_.snd (Σ.projr (xCR cR ls R✴a1c1))
        d = Σ.projl (xCR cR ls R✴a1c1)


  -- Confluent relations have confluent closures
  CR : ∀ {A} {R : A → A → Set} → Confluent R → Confluent (R ✴)
  CR = Proof.xCR

open GeneralizedCurchRosser public

module SimptyTypedLambdaCalculusAtomicallyTypedWith (T : Set) where
  -- Simple types
  infixr 5 _→'_
  data Type : Set where
    ✶_   : T → Type
    _→'_ : Type → Type → Type

  -- Context
  Ctx : Set
  Ctx = List Type

  open Membership {A = Type} _≡_

  -- Simply typed λ-term
  data Term (Γ : Ctx) : Type → Set where
    ⋆_  : ∀ {A} → A ∈ Γ → Term Γ A
    Λ   : ∀ {A B} → Term (A ∷ Γ) B → Term Γ (A →' B)
    _∙_ : ∀ {A B} → Term Γ (A →' B) → Term Γ A → Term Γ B

  -- Context (free variables) manipulations:

  -- Add free variable
  _↓w⋯_ : ∀ {Γ Δ} γ → Γ ⊆ Δ → Γ ⊆ (γ ∷ Δ)
  _↓w⋯_ γ f n = there (f n)

  -- Remove free variable
  _↑w⋯_ : ∀ {Γ Δ} γ → (γ ∷ Γ) ⊆ Δ → Γ ⊆ Δ
  _↑w⋯_ γ f n = f (there n)

  -- Skip free variable
  _∷w⋯_ : ∀ {Γ Δ} γ → Γ ⊆ Δ → (γ ∷ Γ) ⊆ (γ ∷ Δ)
  _∷w⋯_ γ f (here refl) = here refl
  _∷w⋯_ γ f (there n) = there (f n)

  -- Skip a bunch of free variables
  _w⋯_ : ∀ {Γ Δ} γs → Γ ⊆ Δ → (γs ++ Γ) ⊆ (γs ++ Δ)
  []     w⋯ f = f
  γ ∷ γs w⋯ f = γ ∷w⋯ γs w⋯ f

  -- Example:
  -- Adding a new free variable σ after free variables γs:
  --   γs w⋯ σ ∷w⋯ id
  -- .

  -- Weakening: apply context manipulation to a λ-term
  wk : ∀ {Γ Δ τ} → Term Γ τ → (Γ ⊆ Δ) → Term Δ τ
  wk (⋆ x) f = ⋆ (f x)
  wk (Λ {A} M) f = Λ (wk M (A ∷w⋯ f))
  wk (M ∙ N) f = wk M f ∙ wk N f

  -- Parallel substitution
  -- Change a term with context Γ to a term with
  -- context Δ by
  data Sub : (Γ Δ : Ctx) → Set where
    [[]]     : Sub [] []
    [_↦_]∷⋯_ : ∀ {Γ Δ} γ → Term Δ γ → Sub Γ Δ → Sub (γ ∷ Γ) Δ -- substituting
    _∷⋯_     : ∀ {Γ Δ} γ → Sub Γ Δ  → Sub (γ ∷ Γ) (γ ∷ Δ)     -- or skipping
  -- free variables.
  -- Sub is a function with finite domain, represented by a list of respective
  -- codomain elements.

  -- Skip a bunch of variables
  _⋯_      : ∀ {Γ Δ} γs → Sub Γ Δ → Sub (γs ++ Γ) (γs ++ Δ)
  [] ⋯ ss = ss
  (γ ∷ γs) ⋯ ss = γ ∷⋯ (γs ⋯ ss)

  -- Identity substitution
  [id] : ∀ {Γ} → Sub Γ Γ
  [id] {[]} = [[]]
  [id] {γ ∷ Γ} = γ ∷⋯ [id]

  -- Syntax sugar
  [_↦_] : ∀ {Γ} γ → Term Γ γ → Sub (γ ∷ Γ) Γ
  [ γ ↦ M ] = [ γ ↦ M ]∷⋯ [id]

  infixr 4 _∷⋯_ _⋯_
  infixr 4 _∷w⋯_ _↓w⋯_ _w⋯_

  -- Extract a term from a substitution by its number in a context
  _!_ : ∀ {Γ Δ τ} → Sub Γ Δ → τ ∈ Γ → Term Δ τ
  [[]]             ! ()
  ([ γ ↦ x ]∷⋯ ss) ! here refl = x
  ([ γ ↦ x ]∷⋯ ss) ! there n   = ss ! n
  (γ        ∷⋯ ss) ! here refl = ⋆ here refl
  (γ        ∷⋯ ss) ! there n   = wk (ss ! n) (γ ↓w⋯ id)

  -- Apply substitution to a term
  sub : ∀ {Γ Δ τ} → Term Γ τ → Sub Γ Δ → Term Δ τ
  sub (⋆ x) ss = ss ! x
  sub (Λ {A} M) ss = Λ (sub M (A ∷⋯ ss))
  sub (M ∙ N) ss = sub M ss ∙ sub N ss

  --id-proof : ∀ {Γ τ} → [id] ! Term Γ τ ≡ Term Γ τ
  --id-proof
  
  list-wk : ∀ Γ γ → Γ ⊆ (γ ∷ Γ)
  list-wk Γ γ = γ ↓w⋯ ⊆-refl

  wk' : ∀ {Γ τ} γ → Term Γ τ → Term (γ ∷ Γ) τ
  wk' {Γ} {τ} γ t = wk {Γ} {γ ∷ Γ} {τ} t (list-wk Γ γ)

  bar : ∀ {Γ τ} → (x : τ ∈ Γ) → [id] ! x ≡ ⋆ x
  bar (here refl) = refl
  bar {a ∷ as} (there .{a} .{as} x) = cong (wk' a) (bar x)

  foo : ∀ {Γ Δ τ} → (f : Γ ⊆ Δ) → (x : τ ∈ Γ) → ([id] ! f x) ≡ (wk ([id] ! x) f)  
  foo f (here refl) = bar (f (here refl))
  foo {a ∷ as} f (there .{a} .{as} x) = {!cong (wk' a) (foo (a ↑w⋯ f) x)!}

  -- Weakening commutes with substitution
  -- This is specific for the current term representation.
  lemma-wk : ∀ {γ Γ Δ τ}
           → (f : Γ ⊆ Δ)
           → (M : Term (γ ∷ Γ) τ) (s : Term Γ γ)
           → sub (wk M (γ ∷w⋯ f)) [ γ ↦ wk s f ]
           ≡ wk (sub M [ γ ↦ s ]) f
  lemma-wk f (⋆ here refl) s = refl
  lemma-wk f (⋆ there x) s = foo f x
  lemma-wk {γ} f (Λ {A} M) s = {!cong Λ (lemma-wk f (wk M (γ ∷w⋯ f)) s)!}
  lemma-wk f (M ∙ N) s = cong₂ _∙_ (lemma-wk f M s) (lemma-wk f N s)

  -- The Substitution Lemma: substitution commutes with itself
  -- This is general.
  lemma-sub : ∀ {Γ Δ σ τ}
              → (M : Term (σ ∷ Γ) τ) (N : Term Γ σ)
              → (ss : Sub Γ Δ)
              → sub (sub M (σ ∷⋯ ss)) [ σ ↦ sub N ss ]
              ≡ sub (sub M [ σ ↦ N ]) ss
  lemma-sub = {!!}

  -- β-reduction
  data _→β_ {Γ} : ∀ {τ} → Term Γ τ → Term Γ τ → Set where
    reduce : ∀ {τ γ} {M : Term (γ ∷ Γ) τ} {N : Term Γ γ} → ((Λ M) ∙ N) →β (sub M [ γ ↦ N ])
    under  : ∀ {τ γ} {M N : Term (γ ∷ Γ) τ} → M →β N → (Λ M) →β (Λ N)
    left   : ∀ {τ σ} {M N : Term Γ (σ →' τ)} {L : Term Γ σ} → M →β N → (M ∙ L) →β (N ∙ L)
    right  : ∀ {τ σ} {M N : Term Γ σ} {L : Term Γ (σ →' τ)} → M →β N → (L ∙ M) →β (L ∙ N)

  -- β-reduction sequence
  _→β✴_ : ∀ {Γ τ} → Term Γ τ → Term Γ τ → Set
  _→β✴_ = _→β_ ✴

  -- We want to prove that →β✴ is confluent, the problem is →β is not confluent
  -- (no free GeneralizedCR proof).
  -- That's why we define

  -- Parallel β-reduction
  data _⇉β_ {Γ} : ∀ {τ} → Term Γ τ → Term Γ τ → Set where
    parsame   : ∀ {τ} → {M : Term Γ τ} → M ⇉β M
    parreduce : ∀ {τ γ} {M M' : Term (γ ∷ Γ) τ} {N N' : Term Γ γ} → M ⇉β M' → N ⇉β N' → ((Λ M) ∙ N) ⇉β (sub M' [ γ ↦ N' ])
    parunder  : ∀ {τ γ} {M N : Term (γ ∷ Γ) τ} → M ⇉β N → (Λ M) ⇉β (Λ N)
    parapp    : ∀ {τ σ} {M M' : Term Γ (σ →' τ)} {N N' : Term Γ σ} → M ⇉β M' → N ⇉β N' → (M ∙ N) ⇉β (M' ∙ N')

  -- Parallel β-reduction sequence
  _⇉β✴_ : ∀ {Γ τ} → Term Γ τ → Term Γ τ → Set
  _⇉β✴_ = _⇉β_ ✴

  -- with ⇉β being confluent (GeneralizedCR!), and ⇉β✴ being the same thing as →β✴.
  -- The rest of the module proves this.

  module TechnicalReductionLemmas where
    -- Useful transformations:
    →β-≡ : ∀ {Γ τ} → {M N M' N' : Term Γ τ} → M ≡ M' → N ≡ N' → M →β N → M' →β N'
    →β-≡ refl refl red = red

    ⇉β-≡ : ∀ {Γ τ} → {M N M' N' : Term Γ τ} → M ≡ M' → N ≡ N' → M ⇉β N → M' ⇉β N'
    ⇉β-≡ refl refl red = red

    -- ?

    {- TechnicalReductionLemmas end -}

  -- Substitution is substitutive for →β✴
  →β✴-sub : ∀ {Γ τ γ}
          → {M M' : Term (γ ∷ Γ) τ} → M →β✴ M'
          → {N N' : Term Γ γ} → N →β✴ N'
          → sub M [ γ ↦ N ] →β✴ sub M' [ γ ↦ N' ]
  →β✴-sub = {!!}

  -- Substitution is substitutive for ⇉β
  ⇉β-sub : ∀ {Γ τ γ}
         → {M M' : Term (γ ∷ Γ) τ} → M ⇉β M'
         → {N N' : Term Γ γ} → N ⇉β N'
         → sub M [ γ ↦ N ] ⇉β sub M' [ γ ↦ N' ]
  ⇉β-sub = {!!}

  -- ⇉β is confluent
  ⇉β-confluent : ∀ {Γ τ} → Confluent {Term Γ τ} _⇉β_
  ⇉β-confluent = {!!}

  -- Transformations between →β✴ and ⇉β✴ show that they are equivalent:

  →β-⇉β : ∀ {Γ τ} {M N : Term Γ τ} → M →β N → M ⇉β N
  →β-⇉β = {!!}

  →β-⇉β✴ : ∀ {Γ τ} {M N : Term Γ τ} → M →β✴ N → M ⇉β✴ N
  →β-⇉β✴ = map✴ id →β-⇉β

  ⇉β-→β : ∀ {Γ τ} {M N : Term Γ τ} → M ⇉β N → M →β✴ N
  ⇉β-→β = {!!}

  ⇉β-→β✴ : ∀ {Γ τ} {M N : Term Γ τ} → M ⇉β✴ N → M →β✴ N
  ⇉β-→β✴ = concat✴ ∘ map✴ id ⇉β-→β

  -- →β✴ is confluent
  →β✴-confluent : ∀ {Γ τ} → Confluent (_→β✴_ {Γ = Γ} {τ = τ})
  →β✴-confluent ra rx with CR ⇉β-confluent (→β-⇉β✴ ra) (→β-⇉β✴ rx)
  ... | L , (rb , ry) = L , (⇉β-→β✴ rb , ⇉β-→β✴ ry)
