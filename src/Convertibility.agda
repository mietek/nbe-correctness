module Convertibility where

open import Syntax public


-- β-η-equivalence.

infix 4 _≡ᵝᵑ_
data _≡ᵝᵑ_ : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≡ᵝᵑ  : ∀ {A Γ} {d : Γ ⊢ A} → d ≡ᵝᵑ d

  trans≡ᵝᵑ : ∀ {A Γ} {d d′ d″ : Γ ⊢ A} → d ≡ᵝᵑ d′ → d′ ≡ᵝᵑ d″ → d ≡ᵝᵑ d″

  sym≡ᵝᵑ   : ∀ {A Γ} {d d′ : Γ ⊢ A} → d ≡ᵝᵑ d′ → d′ ≡ᵝᵑ d


  -- Congruences.

  cong≡ᵝᵑlam  : ∀ {A B Γ} {d d′ : Γ , A ⊢ B} →
                d ≡ᵝᵑ d′ → lam d ≡ᵝᵑ lam d′

  cong≡ᵝᵑapp  : ∀ {A B Γ} {d d′ : Γ ⊢ A ⇒ B} {e e′ : Γ ⊢ A} →
                d ≡ᵝᵑ d′ → e ≡ᵝᵑ e′ → app d e ≡ᵝᵑ app d′ e′

  cong≡ᵝᵑpair : ∀ {A B Γ} {d d′ : Γ ⊢ A} {e e′ : Γ ⊢ B} →
                d ≡ᵝᵑ d′ → e ≡ᵝᵑ e′ → pair d e ≡ᵝᵑ pair d′ e′

  cong≡ᵝᵑfst  : ∀ {A B Γ} {d d′ : Γ ⊢ A ⩕ B} →
                d ≡ᵝᵑ d′ → fst d ≡ᵝᵑ fst d′

  cong≡ᵝᵑsnd  : ∀ {A B Γ} {d d′ : Γ ⊢ A ⩕ B} →
                d ≡ᵝᵑ d′ → snd d ≡ᵝᵑ snd d′


  -- Reductions, or β-conversions.

  reduce⇒ : ∀ {A B Γ} → (d : Γ , A ⊢ B) (e : Γ ⊢ A) →
             app (lam d) e ≡ᵝᵑ [ top ≔ e ] d

  reduce⩕₁ : ∀ {A B Γ} → (d : Γ ⊢ A) (e : Γ ⊢ B) →
             fst (pair d e) ≡ᵝᵑ d

  reduce⩕₂ : ∀ {A B Γ} → (d : Γ ⊢ A) (e : Γ ⊢ B) →
             snd (pair d e) ≡ᵝᵑ e


  -- Expansions, or η-conversions.

  expand⇒ : ∀ {A B Γ} → (d : Γ ⊢ A ⇒ B) →
             d ≡ᵝᵑ lam (app (mono⊢ weak⊆ d) v₀)

  expand⩕  : ∀ {A B Γ} → (d : Γ ⊢ A ⩕ B) →
             d ≡ᵝᵑ pair (fst d) (snd d)

  expand⫪ : ∀ {Γ} → (d : Γ ⊢ ⫪) →
             d ≡ᵝᵑ unit


≡→≡ᵝᵑ : ∀ {A Γ} {d d′ : Γ ⊢ A} → d ≡ d′ → d ≡ᵝᵑ d′
≡→≡ᵝᵑ refl = refl≡ᵝᵑ


-- Syntax for equational reasoning with β-η-equivalence.

module ≡ᵝᵑ-Reasoning where
  infix 1 begin≡ᵝᵑ_
  begin≡ᵝᵑ_ : ∀ {A Γ} {d d′ : Γ ⊢ A} → d ≡ᵝᵑ d′ → d ≡ᵝᵑ d′
  begin≡ᵝᵑ_ p = p

  infixr 2 _≡→≡ᵝᵑ⟨⟩_
  _≡→≡ᵝᵑ⟨⟩_ : ∀ {A Γ} (d {d′} : Γ ⊢ A) → d ≡ d′ → d ≡ᵝᵑ d′
  d ≡→≡ᵝᵑ⟨⟩ p = ≡→≡ᵝᵑ p

  infixr 2 _≡ᵝᵑ⟨⟩_
  _≡ᵝᵑ⟨⟩_ : ∀ {A Γ} (d {d′} : Γ ⊢ A) → d ≡ᵝᵑ d′ → d ≡ᵝᵑ d′
  d ≡ᵝᵑ⟨⟩ p = p

  infixr 2 _≡ᵝᵑ⟨_⟩_
  _≡ᵝᵑ⟨_⟩_ : ∀ {A Γ} (d {d′ d″} : Γ ⊢ A) → d ≡ᵝᵑ d′ → d′ ≡ᵝᵑ d″ → d ≡ᵝᵑ d″
  d ≡ᵝᵑ⟨ p ⟩ q = trans≡ᵝᵑ p q

  infix 3 _∎≡ᵝᵑ
  _∎≡ᵝᵑ : ∀ {A Γ} (d : Γ ⊢ A) → d ≡ᵝᵑ d
  _∎≡ᵝᵑ _ = refl≡ᵝᵑ

open ≡ᵝᵑ-Reasoning public
