module Stack where

open import Prelude public


-- Stacks, or snoc-lists.

data Stack (X : Set) : Set where
  ∅   : Stack X
  _,_ : Stack X → X → Stack X


-- Stack membership, or de Bruijn indices.

module _ {X : Set} where
  infix 3 _∈_
  data _∈_ (A : X) : Stack X → Set where
    top : ∀ {Γ}   → A ∈ Γ , A
    pop : ∀ {B Γ} → A ∈ Γ → A ∈ Γ , B

  i₀ : ∀ {A Γ} → A ∈ Γ , A
  i₀ = top

  i₁ : ∀ {A B Γ} → A ∈ Γ , A , B
  i₁ = pop i₀

  i₂ : ∀ {A B C Γ} → A ∈ Γ , A , B , C
  i₂ = pop i₁


-- Stack inclusion, or order-preserving embeddings.

module _ {X : Set} where
  infix 3 _⊆_
  data _⊆_ : Stack X → Stack X → Set where
    done : ∅ ⊆ ∅
    skip : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ Γ′ , A
    keep : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ , A ⊆ Γ′ , A

  bot⊆ : ∀ {Γ} → ∅ ⊆ Γ
  bot⊆ {∅}     = done
  bot⊆ {Γ , A} = skip bot⊆

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {∅}     = done
  refl⊆ {Γ , A} = keep refl⊆

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ p        done      = p
  trans⊆ p        (skip p′) = skip (trans⊆ p p′)
  trans⊆ (skip p) (keep p′) = skip (trans⊆ p p′)
  trans⊆ (keep p) (keep p′) = keep (trans⊆ p p′)

  weak⊆ : ∀ {A Γ} → Γ ⊆ Γ , A
  weak⊆ = skip refl⊆

  idtrans⊆ : ∀ {Γ Γ′ } → (p : Γ ⊆ Γ′) → trans⊆ refl⊆ p ≡ p
  idtrans⊆ done     = refl
  idtrans⊆ (skip p) = cong skip (idtrans⊆ p)
  idtrans⊆ (keep p) = cong keep (idtrans⊆ p)

  idtrans⊆′ : ∀ {Γ Γ′} → (p : Γ ⊆ Γ′) → trans⊆ p refl⊆ ≡ p
  idtrans⊆′ done     = refl
  idtrans⊆′ (skip p) = cong skip (idtrans⊆′ p)
  idtrans⊆′ (keep p) = cong keep (idtrans⊆′ p)

  assoctrans⊆ : ∀ {Γ Γ′ Γ″ Γ‴} → (p : Γ ⊆ Γ′) (p′ : Γ′ ⊆ Γ″) (p″ : Γ″ ⊆ Γ‴) →
                trans⊆ (trans⊆ p p′) p″ ≡ trans⊆ p (trans⊆ p′ p″)
  assoctrans⊆ p        p′        done      = refl
  assoctrans⊆ p        p′        (skip p″) = cong skip (assoctrans⊆ p p′ p″)
  assoctrans⊆ p        (skip p′) (keep p″) = cong skip (assoctrans⊆ p p′ p″)
  assoctrans⊆ (skip p) (keep p′) (keep p″) = cong skip (assoctrans⊆ p p′ p″)
  assoctrans⊆ (keep p) (keep p′) (keep p″) = cong keep (assoctrans⊆ p p′ p″)


-- Monotonicity of stack membership with respect to stack inclusion.

module _ {X : Set} where
  mono∈ : ∀ {A : X} {Γ Γ′} → Γ ⊆ Γ′ → A ∈ Γ → A ∈ Γ′
  mono∈ done     ()
  mono∈ (skip p) i       = pop (mono∈ p i)
  mono∈ (keep p) top     = top
  mono∈ (keep p) (pop i) = pop (mono∈ p i)

  idmono∈ : ∀ {A : X} {Γ} → (i : A ∈ Γ) → mono∈ refl⊆ i ≡ i
  idmono∈ top     = refl
  idmono∈ (pop i) = cong pop (idmono∈ i)


-- Stack thinning.

module _ {X : Set} where
  _∖_ : ∀ {A} → (Γ : Stack X) → A ∈ Γ → Stack X
  ∅       ∖ ()
  (Γ , A) ∖ top   = Γ
  (Γ , B) ∖ pop i = Γ ∖ i , B

  thin⊆ : ∀ {A Γ} → (i : A ∈ Γ) → Γ ∖ i ⊆ Γ
  thin⊆ top     = weak⊆
  thin⊆ (pop i) = keep (thin⊆ i)


-- Decidable equality of stack membership.

module _ {X : Set} where
  data _=∈_ {A} {Γ : Stack X} (i : A ∈ Γ) : ∀ {B} → B ∈ Γ → Set where
    same : i =∈ i
    diff : ∀ {B} → (j : B ∈ Γ ∖ i) → i =∈ mono∈ (thin⊆ i) j

  _≟∈_ : ∀ {A B Γ} → (i : A ∈ Γ) (j : B ∈ Γ) → i =∈ j
  top   ≟∈ top    = same
  top   ≟∈ pop j  rewrite sym (idmono∈ j) = diff j
  pop i ≟∈ top    = diff top
  pop i ≟∈ pop j  with i ≟∈ j
  pop i ≟∈ pop .i | same   = same
  pop i ≟∈ pop ._ | diff j = diff (pop j)
