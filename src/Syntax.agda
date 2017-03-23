module Syntax where

open import Stack public


-- Abstract symbols, or atoms.

abstract
  Atom : Set
  Atom = Nat


-- Types, or propositions in constructive logic.

infixl 9 _⩕_
infixr 7 _⇒_
data Type : Set where
  α_   : Atom → Type
  _⇒_ : Type → Type → Type
  _⩕_  : Type → Type → Type
  ⫪   : Type


-- Contexts, or stacks of types.

Context : Set
Context = Stack Type


-- Derivations, or syntactic entailment.

infix 3 _⊢_
data _⊢_ : Context → Type → Set where
  var   : ∀ {A Γ}   → A ∈ Γ → Γ ⊢ A
  lam   : ∀ {A B Γ} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  app   : ∀ {A B Γ} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  pair  : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ⩕ B
  fst   : ∀ {A B Γ} → Γ ⊢ A ⩕ B → Γ ⊢ A
  snd   : ∀ {A B Γ} → Γ ⊢ A ⩕ B → Γ ⊢ B
  unit  : ∀ {Γ}     → Γ ⊢ ⫪


-- Shorthand for variables.

v₀ : ∀ {A Γ} → Γ , A ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ} → Γ , A , B ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ} → Γ , A , B , C ⊢ A
v₂ = var i₂


-- Stacks of derivations, or simultaneous syntactic entailment.

infix 3 _⊢⋆_
_⊢⋆_ : Context → Stack Type → Set
Γ ⊢⋆ ∅     = ⊤
Γ ⊢⋆ Ξ , A = Γ ⊢⋆ Ξ ∧ Γ ⊢ A


-- Monotonicity of syntactic entailment with respect to context inclusion.

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ p (var i)      = var (mono∈ p i)
mono⊢ p (lam d)      = lam (mono⊢ (keep p) d)
mono⊢ p (app d e)    = app (mono⊢ p d) (mono⊢ p e)
mono⊢ p (pair d e)   = pair (mono⊢ p d) (mono⊢ p e)
mono⊢ p (fst d)      = fst (mono⊢ p d)
mono⊢ p (snd d)      = snd (mono⊢ p d)
mono⊢ p unit         = unit

mono⊢⋆ : ∀ {Ξ Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ Ξ → Γ′ ⊢⋆ Ξ
mono⊢⋆ {∅}     p ∙       = ∙
mono⊢⋆ {Ξ , A} p (ζ , d) = mono⊢⋆ p ζ , mono⊢ p d


-- TODO: Naming things.

idmono⊢ : ∀ {A Γ} → (d : Γ ⊢ A) → mono⊢ refl⊆ d ≡ d
idmono⊢ (var {A} i) = cong var (idmono∈ i)
idmono⊢ (lam d)     = cong lam (idmono⊢ d)
idmono⊢ (app d e)   = cong² app (idmono⊢ d) (idmono⊢ e)
idmono⊢ (pair d e)  = cong² pair (idmono⊢ d) (idmono⊢ e)
idmono⊢ (fst d)     = cong fst (idmono⊢ d)
idmono⊢ (snd d)     = cong snd (idmono⊢ d)
idmono⊢ unit        = refl

idmono⊢⋆ : ∀ {Ξ Γ} → (ζ : Γ ⊢⋆ Ξ) → mono⊢⋆ refl⊆ ζ ≡ ζ
idmono⊢⋆ {∅}     ∙       = refl
idmono⊢⋆ {Ξ , A} (ζ , d) = cong² _,_ (idmono⊢⋆ ζ) (idmono⊢ d)


-- Reflexivity of simultaneous syntactic entailment.

refl⊢⋆ : ∀ {Γ} → Γ ⊢⋆ Γ
refl⊢⋆ {∅}     = ∙
refl⊢⋆ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆ , v₀


-- Substitution.

[_≔_]∈_ : ∀ {A C Γ} → (i : C ∈ Γ) → Γ ∖ i ⊢ C → A ∈ Γ → Γ ∖ i ⊢ A
[ i ≔ c ]∈  j      with i ≟∈ j
[ i ≔ c ]∈ .i      | same   = c
[ i ≔ c ]∈ ._      | diff j = var j

[_≔_]_ : ∀ {A C Γ} → (i : C ∈ Γ) → Γ ∖ i ⊢ C → Γ ⊢ A → Γ ∖ i ⊢ A
[ i ≔ c ] var j    = [ i ≔ c ]∈ j
[ i ≔ c ] lam d    = lam ([ pop i ≔ mono⊢ weak⊆ c ] d)
[ i ≔ c ] app d e  = app ([ i ≔ c ] d) ([ i ≔ c ] e)
[ i ≔ c ] pair d e = pair ([ i ≔ c ] d) ([ i ≔ c ] e)
[ i ≔ c ] fst d    = fst ([ i ≔ c ] d)
[ i ≔ c ] snd d    = snd ([ i ≔ c ] d)
[ i ≔ c ] unit     = unit


-- Grafting of derivation trees, or simultaneous substitution, or cut.

graft∈ : ∀ {A Ξ Γ} → Γ ⊢⋆ Ξ → A ∈ Ξ → Γ ⊢ A
graft∈ (ζ , d) top     = d
graft∈ (ζ , d) (pop i) = graft∈ ζ i

graft⊢ : ∀ {A Ξ Γ} → Γ ⊢⋆ Ξ → Ξ ⊢ A → Γ ⊢ A
graft⊢ ζ (var i)      = graft∈ ζ i
graft⊢ ζ (lam d)      = lam (graft⊢ (mono⊢⋆ weak⊆ ζ , v₀) d)
graft⊢ ζ (app d e)    = app (graft⊢ ζ d) (graft⊢ ζ e)
graft⊢ ζ (pair d e)   = pair (graft⊢ ζ d) (graft⊢ ζ e)
graft⊢ ζ (fst d)      = fst (graft⊢ ζ d)
graft⊢ ζ (snd d)      = snd (graft⊢ ζ d)
graft⊢ ζ unit         = unit


-- Derivations, or syntactic entailment, in normal form.

mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : Context → Type → Set where
    neⁿᶠ   : ∀ {A Γ}   → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B Γ} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ⇒ B
    pairⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ⩕ B
    unitⁿᶠ : ∀ {Γ}     → Γ ⊢ⁿᶠ ⫪

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : Context → Type → Set where
    varⁿᵉ  : ∀ {A Γ}   → A ∈ Γ → Γ ⊢ⁿᵉ A
    appⁿᵉ  : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ⇒ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
    fstⁿᵉ  : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ⩕ B → Γ ⊢ⁿᵉ A
    sndⁿᵉ  : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ⩕ B → Γ ⊢ⁿᵉ B


-- Shorthand for variables.

v₀ⁿᵉ : ∀ {A Γ} → Γ , A ⊢ⁿᵉ A
v₀ⁿᵉ = varⁿᵉ top


-- Stacks of derivations, or simultaneous syntactic entailment, in normal form.

infix 3 _⊢⋆ⁿᵉ_
_⊢⋆ⁿᵉ_ : Context → Stack Type → Set
Γ ⊢⋆ⁿᵉ ∅     = ⊤
Γ ⊢⋆ⁿᵉ Ξ , A = Γ ⊢⋆ⁿᵉ Ξ ∧ Γ ⊢ⁿᵉ A


-- Translation from normal form to arbitrary form.

mutual
  nf→af : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→af (neⁿᶠ d)     = ne→af d
  nf→af (lamⁿᶠ d)    = lam (nf→af d)
  nf→af (pairⁿᶠ d e) = pair (nf→af d) (nf→af e)
  nf→af unitⁿᶠ       = unit

  ne→af : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→af (varⁿᵉ i)    = var i
  ne→af (appⁿᵉ d e)  = app (ne→af d) (nf→af e)
  ne→af (fstⁿᵉ d)    = fst (ne→af d)
  ne→af (sndⁿᵉ d)    = snd (ne→af d)


-- Monotonicity of syntactic entailment with respect to context inclusion, in normal form.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ p (neⁿᶠ d)     = neⁿᶠ (mono⊢ⁿᵉ p d)
  mono⊢ⁿᶠ p (lamⁿᶠ d)    = lamⁿᶠ (mono⊢ⁿᶠ (keep p) d)
  mono⊢ⁿᶠ p (pairⁿᶠ d e) = pairⁿᶠ (mono⊢ⁿᶠ p d) (mono⊢ⁿᶠ p e)
  mono⊢ⁿᶠ p unitⁿᶠ       = unitⁿᶠ

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ p (varⁿᵉ i)    = varⁿᵉ (mono∈ p i)
  mono⊢ⁿᵉ p (appⁿᵉ d e)  = appⁿᵉ (mono⊢ⁿᵉ p d) (mono⊢ⁿᶠ p e)
  mono⊢ⁿᵉ p (fstⁿᵉ d)    = fstⁿᵉ (mono⊢ⁿᵉ p d)
  mono⊢ⁿᵉ p (sndⁿᵉ d)    = sndⁿᵉ (mono⊢ⁿᵉ p d)

mono⊢⋆ⁿᵉ : ∀ {Ξ Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ⁿᵉ Ξ → Γ′ ⊢⋆ⁿᵉ Ξ
mono⊢⋆ⁿᵉ {∅}     p ∙       = ∙
mono⊢⋆ⁿᵉ {Ξ , A} p (ζ , d) = mono⊢⋆ⁿᵉ p ζ , mono⊢ⁿᵉ p d


-- TODO: Naming things.

mutual
  idmono⊢ⁿᶠ : ∀ {A Γ} → (d : Γ ⊢ⁿᶠ A) → mono⊢ⁿᶠ refl⊆ d ≡ d
  idmono⊢ⁿᶠ (neⁿᶠ d)     = cong neⁿᶠ (idmono⊢ⁿᵉ d)
  idmono⊢ⁿᶠ (lamⁿᶠ d)    = cong lamⁿᶠ (idmono⊢ⁿᶠ d)
  idmono⊢ⁿᶠ (pairⁿᶠ d e) = cong² pairⁿᶠ (idmono⊢ⁿᶠ d) (idmono⊢ⁿᶠ e)
  idmono⊢ⁿᶠ unitⁿᶠ       = refl

  idmono⊢ⁿᵉ : ∀ {A Γ} → (d : Γ ⊢ⁿᵉ A) → mono⊢ⁿᵉ refl⊆ d ≡ d
  idmono⊢ⁿᵉ (varⁿᵉ i)    = cong varⁿᵉ (idmono∈ i)
  idmono⊢ⁿᵉ (appⁿᵉ d e)  = cong² appⁿᵉ (idmono⊢ⁿᵉ d) (idmono⊢ⁿᶠ e)
  idmono⊢ⁿᵉ (fstⁿᵉ d)    = cong fstⁿᵉ (idmono⊢ⁿᵉ d)
  idmono⊢ⁿᵉ (sndⁿᵉ d)    = cong sndⁿᵉ (idmono⊢ⁿᵉ d)

idmono⊢⋆ⁿᵉ : ∀ {Ξ Γ} → (ζ : Γ ⊢⋆ⁿᵉ Ξ) → mono⊢⋆ⁿᵉ refl⊆ ζ ≡ ζ
idmono⊢⋆ⁿᵉ {∅}     ∙       = refl
idmono⊢⋆ⁿᵉ {Ξ , A} (ζ , d) = cong² _,_ (idmono⊢⋆ⁿᵉ ζ) (idmono⊢ⁿᵉ d)


-- Reflexivity of simultaneous syntactic entailment, in normal form.

refl⊢⋆ⁿᵉ : ∀ {Γ} → Γ ⊢⋆ⁿᵉ Γ
refl⊢⋆ⁿᵉ {∅}     = ∙
refl⊢⋆ⁿᵉ {Γ , A} = mono⊢⋆ⁿᵉ weak⊆ refl⊢⋆ⁿᵉ , v₀ⁿᵉ
