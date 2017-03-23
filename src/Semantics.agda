module Semantics where

open import Syntax public


-- Kripke models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    World     : Set
    _≤_       : World → World → Set
    refl≤     : ∀ {w} → w ≤ w
    trans≤    : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″
    idtrans≤  : ∀ {w w′} → (p : w ≤ w′) → trans≤ refl≤ p ≡ p
    _⊩ᵅ_     : World → Atom → Set
    mono⊩ᵅ   : ∀ {P w w′} → w ≤ w′ → w ⊩ᵅ P → w′ ⊩ᵅ P
    idmono⊩ᵅ : ∀ {P w} → (s : w ⊩ᵅ P) → mono⊩ᵅ {P} refl≤ s ≡ s

open Model {{…}} public


-- Forcing in a particular world.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Type → Set
  w ⊩ α P    = w ⊩ᵅ P
  w ⊩ A ⇒ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ A ⩕ B  = w ⊩ A ∧ w ⊩ B
  w ⊩ ⫪     = ⊤

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Stack Type → Set
  w ⊩⋆ ∅     = ⊤
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ ∧ w ⊩ A


-- Function extensionality.

postulate
  funext  : ∀ {X : Set} {Y : X → Set} {f g : ∀ x → Y x} →
            (∀ x → f x ≡ g x) →
            (λ x → f x) ≡ (λ x → g x)

  ⟨funext⟩ : ∀ {X : Set} {Y : X → Set} {f g : ∀ {x} → Y x} →
             (∀ {x} → f {x} ≡ g {x}) →
             (λ {x} → f {x}) ≡ (λ {x} → g {x})

extfun : ∀ {X : Set} {Y : X → Set} {f g : ∀ x → Y x} →
         (λ x → f x) ≡ (λ x → g x) →
         (∀ x → f x ≡ g x)
extfun refl = λ x → refl

⟨extfun⟩ : ∀ {X : Set} {Y : X → Set} {f g : ∀ {x} → Y x} →
           (λ {x} → f {x}) ≡ (λ {x} → g {x}) →
           (∀ {x} → f {x} ≡ g {x})
⟨extfun⟩ refl = refl


-- Monotonicity of forcing with respect to constructive accessibility.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}    p s = mono⊩ᵅ p s
  mono⊩ {A ⇒ B} p s = λ p′ → s (trans≤ p p′)
  mono⊩ {A ⩕ B}  p s = mono⊩ {A} p (π₁ s) , mono⊩ {B} p (π₂ s)
  mono⊩ {⫪}     p s = ∙

  mono⊩⋆ : ∀ {Ξ w w′} → w ≤ w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     p ∙       = ∙
  mono⊩⋆ {Ξ , A} p (σ , s) = mono⊩⋆ {Ξ} p σ , mono⊩ {A} p s


-- TODO: Naming things.

module _ {{_ : Model}} where
  idmono⊩ : ∀ {A w} → (s : w ⊩ A) → mono⊩ {A} refl≤ s ≡ s
  idmono⊩ {α P}    s = idmono⊩ᵅ s
  idmono⊩ {A ⇒ B} s = ⟨funext⟩ λ {w′} → funext λ p → cong s (idtrans≤ p)
  idmono⊩ {A ⩕ B}  s = cong² _,_ (idmono⊩ {A} (π₁ s)) (idmono⊩ {B} (π₂ s))
  idmono⊩ {⫪}     s = refl

  idmono⊩⋆ : ∀ {Ξ w} → (γ : w ⊩⋆ Ξ) → mono⊩⋆ refl≤ γ ≡ γ
  idmono⊩⋆ {∅}     ∙       = refl
  idmono⊩⋆ {Ξ , A} (σ , s) = cong² _,_ (idmono⊩⋆ σ) (idmono⊩ {A} s)


-- TODO: Naming things.

module _ {{_ : Model}} where
  _⟪_⊫_⟫ : World → Context → Type → Set
  w ⟪ Γ ⊫ A ⟫ = w ⊩⋆ Γ → w ⊩ A


-- Evaluation equipment.

module _ {{_ : Model}} where
  ⟪var⟫ : ∀ {A Γ w} → A ∈ Γ → w ⟪ Γ ⊫ A ⟫
  ⟪var⟫ top     = λ { (γ , s) → s }
  ⟪var⟫ (pop i) = λ { (γ , s) → ⟪var⟫ i γ }

  ⟪lam⟫ : ∀ {A B Γ w} → (∀ {w′} → w′ ⟪ Γ , A ⊫ B ⟫) → w ⟪ Γ ⊫ A ⇒ B ⟫
  ⟪lam⟫ ⟪d⟫ = λ γ p s → ⟪d⟫ (mono⊩⋆ p γ , s)

  ⟪app⟫ : ∀ {A B Γ w} → w ⟪ Γ ⊫ A ⇒ B ⟫ → w ⟪ Γ ⊫ A ⟫ → w ⟪ Γ ⊫ B ⟫
  ⟪app⟫ ⟪d⟫ ⟪e⟫ = λ γ → ⟪d⟫ γ refl≤ (⟪e⟫ γ)

  ⟪pair⟫ : ∀ {A B Γ w} → w ⟪ Γ ⊫ A ⟫ → w ⟪ Γ ⊫ B ⟫ → w ⟪ Γ ⊫ A ⩕ B ⟫
  ⟪pair⟫ ⟪d⟫ ⟪e⟫ = λ γ → ⟪d⟫ γ , ⟪e⟫ γ

  ⟪fst⟫ : ∀ {A B Γ w} → w ⟪ Γ ⊫ A ⩕ B ⟫ → w ⟪ Γ ⊫ A ⟫
  ⟪fst⟫ ⟪d⟫ = λ γ → π₁ (⟪d⟫ γ)

  ⟪snd⟫ : ∀ {A B Γ w} → w ⟪ Γ ⊫ A ⩕ B ⟫ → w ⟪ Γ ⊫ B ⟫
  ⟪snd⟫ ⟪d⟫ = λ γ → π₂ (⟪d⟫ γ)

  ⟪unit⟫ : ∀ {Γ w} → w ⟪ Γ ⊫ ⫪ ⟫
  ⟪unit⟫ = λ γ → ∙


-- Shorthand for variables.

module _ {{_ : Model}} where
  ⟪v₀⟫ : ∀ {A Γ w} → w ⟪ Γ , A ⊫ A ⟫
  ⟪v₀⟫ {A} = ⟪var⟫ {A} i₀


-- Forcing in all worlds, or semantic entailment.

module _ {{_ : Model}} where
  infix 3 _⊨_
  _⊨_ : Context → Type → Set
  Γ ⊨ A = ∀ {w} → w ⟪ Γ ⊫ A ⟫


-- Evaluation, or soundness of the semantics with respect to the syntax.

module _ {{_ : Model}} where
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
  eval (var i)            = ⟪var⟫ i
  eval (lam {A} {B} d)    = ⟪lam⟫ {A} {B} (eval d)
  eval (app {A} {B} d e)  = ⟪app⟫ {A} {B} (eval d) (eval e)
  eval (pair {A} {B} d e) = ⟪pair⟫ {A} {B} (eval d) (eval e)
  eval (fst {A} {B} d)    = ⟪fst⟫ {A} {B} (eval d)
  eval (snd {A} {B} d)    = ⟪snd⟫ {A} {B} (eval d)
  eval unit               = ⟪unit⟫


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { World     = Context
      ; _≤_       = _⊆_
      ; refl≤     = refl⊆
      ; trans≤    = trans⊆
      ; idtrans≤  = idtrans⊆
      ; _⊩ᵅ_     = λ Γ P → Γ ⊢ⁿᵉ α P
      ; mono⊩ᵅ   = mono⊢ⁿᵉ
      ; idmono⊩ᵅ = idmono⊢ⁿᵉ
      }


-- Soundness and completeness of the canonical model with respect to the syntax.

mutual
  evalᶜ : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  evalᶜ {α P}    d = d
  evalᶜ {A ⇒ B} d = λ p e → evalᶜ (appⁿᵉ (mono⊢ⁿᵉ p d) (quotᶜ e))
  evalᶜ {A ⩕ B}  d = evalᶜ (fstⁿᵉ d) , evalᶜ (sndⁿᵉ d)
  evalᶜ {⫪}     d = ∙

  quotᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  quotᶜ {α P}    s = neⁿᶠ s
  quotᶜ {A ⇒ B} s = lamⁿᶠ (quotᶜ (s weak⊆ (evalᶜ {A} v₀ⁿᵉ)))
  quotᶜ {A ⩕ B}  s = pairⁿᶠ (quotᶜ (π₁ s)) (quotᶜ (π₂ s))
  quotᶜ {⫪}     s = unitⁿᶠ


-- Reflexivity of simultaneous forcing.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {∅}     = ∙
refl⊩⋆ {Γ , A} = mono⊩⋆ weak⊆ refl⊩⋆ , evalᶜ {A} v₀ⁿᵉ


-- Quotation, or completeness of the semantics with respect to the syntax.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ⁿᶠ A
quot s = quotᶜ (s refl⊩⋆)


-- Normalisation by evaluation.

nbe : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ⁿᶠ A
nbe = quot ∘ eval
