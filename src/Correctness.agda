{-# OPTIONS --rewriting #-}

module Correctness where

open import Convertibility public
open import Semantics public

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE idmono⊩⋆ #-}


-- TODO: Naming things.

module _ {{_ : Model}} where
  ⟦_≔_⟧∈ : ∀ {C Γ w} → (i : C ∈ Γ) → w ⟪ Γ ∖ i ⊫ C ⟫ →
           ∀ {A} → A ∈ Γ → w ⟪ Γ ∖ i ⊫ A ⟫
  ⟦ i ≔ ⟪c⟫ ⟧∈ j  with i ≟∈ j
  ⟦ i ≔ ⟪c⟫ ⟧∈ .i | same   = ⟪c⟫
  ⟦ i ≔ ⟪c⟫ ⟧∈ ._ | diff j = ⟪var⟫ j

  lem≔∈ : ∀ {A C Γ w} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (j : A ∈ Γ) →
          ⟦ i ≔ eval c ⟧∈ j ≡ eval ([ i ≔ c ]∈ j) {w}
  lem≔∈ i c j  with i ≟∈ j
  lem≔∈ i c .i | same   = refl
  lem≔∈ i c ._ | diff j = refl


-- TODO: Naming things.

module _ {{_ : Model}} where
  plug : ∀ {C Γ w} → (i : C ∈ Γ) → w ⊩⋆ Γ ∖ i → w ⊩ C → w ⊩⋆ Γ
  plug top     γ       s = γ , s
  plug (pop i) (γ , r) s = plug i γ s , r

  ⟦_≔_⟧ : ∀ {C Γ w} → (i : C ∈ Γ) → w ⟪ Γ ∖ i ⊫ C ⟫ →
          ∀ {A} → (∀ {w′} → w′ ⟪ Γ ⊫ A ⟫) → w ⟪ Γ ∖ i ⊫ A ⟫
  ⟦ i ≔ ⟪c⟫ ⟧ ⟪d⟫ = λ γ → ⟪d⟫ (plug i γ (⟪c⟫ γ))


  -- TODO: The var case in lem≔.

  postulate
    oops≔var₁ : ∀ {C Γ w} → (i : C ∈ Γ) (⟪c⟫ : w ⟪ Γ ∖ i ⊫ C ⟫) (γ : w ⊩⋆ Γ ∖ i) →
                ⟪var⟫ {C} i (plug i γ (⟪c⟫ γ)) ≡ ⟪c⟫ γ
  -- oops≔var₁ top     ⟪c⟫ γ       = refl
  -- oops≔var₁ (pop i) ⟪c⟫ (γ , s) = {!!}

  postulate
    oops≔var₂ : ∀ {A C Γ w} → (i : C ∈ Γ) (⟪c⟫ : w ⟪ Γ ∖ i ⊫ C ⟫) (j : A ∈ Γ ∖ i) (γ : w ⊩⋆ Γ ∖ i) →
                ⟪var⟫ {A} (mono∈ (thin⊆ i) j) (plug i γ (⟪c⟫ γ)) ≡ ⟪var⟫ {A} j γ
  -- oops≔var₂ top     ⟪c⟫ j γ       = cong² ⟪var⟫ (idmono∈ j) refl
  -- oops≔var₂ (pop i) ⟪c⟫ j (γ , s) = {!!}

  oops≔var : ∀ {A C Γ w} → (i : C ∈ Γ) (⟪c⟫ : w ⟪ Γ ∖ i ⊫ C ⟫) (j : A ∈ Γ) →
             ⟦ i ≔ ⟪c⟫ ⟧ {A} (⟪var⟫ {A} j) ≡ ⟦ i ≔ ⟪c⟫ ⟧∈ {A} j
  oops≔var i ⟪c⟫ j  with i ≟∈ j
  oops≔var i ⟪c⟫ .i | same   = funext (λ γ → oops≔var₁ i ⟪c⟫ γ)
  oops≔var i ⟪c⟫ ._ | diff j = funext (λ γ → oops≔var₂ i ⟪c⟫ j γ)


  -- TODO: The lam case in lem≔.

  lem₁ : ∀ {C Γ w w′} → (i : C ∈ Γ) (γ : w ⊩⋆ Γ ∖ i) (s : w ⊩ C) (p : w ≤ w′) →
         mono⊩⋆ p (plug i γ s) ≡ plug i (mono⊩⋆ p γ) (mono⊩ {C} p s)
  lem₁ top     γ       s p = refl
  lem₁ (pop i) (γ , r) s p = cong² _,_ (lem₁ i γ s p) refl

  mutual
    postulate
      lem₂ : ∀ {A Γ w w′} → (p : w ≤ w′) (d : Γ ⊢ A) (γ : w ⊩⋆ Γ) →
             mono⊩ {A} p (eval d γ) ≡ eval d (mono⊩⋆ p γ)
    -- lem₂ p (var {A} j)        γ = {!!}
    -- lem₂ p (lam {A} {B} d)    γ = {!!}
    -- lem₂ p (app {A} {B} d e)  γ = {!!}
    -- lem₂ p (pair {A} {B} d e) γ = lem₂pair p d e γ
    -- lem₂ p (fst {A} {B} d)    γ = lem₂fst p d γ
    -- lem₂ p (snd {A} {B} d)    γ = lem₂snd p d γ
    -- lem₂ p unit               γ = refl

    lem₂pair : ∀ {A B Γ w w′} → (p : w ≤ w′) (d : Γ ⊢ A) (e : Γ ⊢ B) (γ : w ⊩⋆ Γ) →
               mono⊩ {A ⩕ B} p (⟪pair⟫ {A} {B} (eval d) (eval e) γ) ≡ ⟪pair⟫ {A} {B} (eval d) (eval e) (mono⊩⋆ p γ)
    lem₂pair {A} {B} p d e γ =
      begin
        mono⊩ {A ⩕ B} p (⟪pair⟫ {A} {B} (eval d) (eval e) γ)
      ≡⟨⟩
        ⟪pair⟫ {A} {B} (λ γ′ → mono⊩ {A} p (eval d γ)) (λ γ′ → mono⊩ {B} p (eval e γ)) (mono⊩⋆ p γ)
      ≡⟨ cong² (λ ⟪d⟫ ⟪e⟫ → ⟪pair⟫ {A} {B} ⟪d⟫ ⟪e⟫ (mono⊩⋆ p γ)) (funext (λ γ′ → lem₂ p d γ)) (funext (λ γ′ → lem₂ p e γ)) ⟩
        ⟪pair⟫ {A} {B} (λ γ′ → eval d (mono⊩⋆ p γ)) (λ γ′ → eval e (mono⊩⋆ p γ)) (mono⊩⋆ p γ)
      ≡⟨⟩
        ⟪pair⟫ {A} {B} (eval d) (eval e) (mono⊩⋆ p γ)
      ∎

    lem₂fst : ∀ {A B Γ w w′} → (p : w ≤ w′) (d : Γ ⊢ A ⩕ B) (γ : w ⊩⋆ Γ) →
              mono⊩ {A} p (⟪fst⟫ {A} {B} (eval d) γ) ≡ ⟪fst⟫ {A} {B} (eval d) (mono⊩⋆ p γ)
    lem₂fst {A} {B} p d γ =
      begin
        mono⊩ {A} p (⟪fst⟫ {A} {B} (eval d) γ)
      ≡⟨⟩
        ⟪fst⟫ {A} {B} (λ γ′ → mono⊩ {A ⩕ B} p (eval d γ)) (mono⊩⋆ p γ)
      ≡⟨ cong (λ ⟪d⟫ → ⟪fst⟫ {A} {B} ⟪d⟫ (mono⊩⋆ p γ)) (funext (λ γ′ → lem₂ p d γ)) ⟩
        ⟪fst⟫ {A} {B} (λ γ′ → eval d (mono⊩⋆ p γ)) (mono⊩⋆ p γ)
      ≡⟨⟩
        ⟪fst⟫ {A} {B} (eval d) (mono⊩⋆ p γ)
      ∎

    lem₂snd : ∀ {A B Γ w w′} → (p : w ≤ w′) (d : Γ ⊢ A ⩕ B) (γ : w ⊩⋆ Γ) →
              mono⊩ {B} p (⟪snd⟫ {A} {B} (eval d) γ) ≡ ⟪snd⟫ {A} {B} (eval d) (mono⊩⋆ p γ)
    lem₂snd {A} {B} p d γ =
      begin
        mono⊩ {B} p (⟪snd⟫ {A} {B} (eval d) γ)
      ≡⟨⟩
        ⟪snd⟫ {A} {B} (λ γ′ → mono⊩ {A ⩕ B} p (eval d γ)) (mono⊩⋆ p γ)
      ≡⟨ cong (λ ⟪d⟫ → ⟪snd⟫ {A} {B} ⟪d⟫ (mono⊩⋆ p γ)) (funext (λ γ′ → lem₂ p d γ)) ⟩
        ⟪snd⟫ {A} {B} (λ γ′ → eval d (mono⊩⋆ p γ)) (mono⊩⋆ p γ)
      ≡⟨⟩
        ⟪snd⟫ {A} {B} (eval d) (mono⊩⋆ p γ)
      ∎


  postulate
    oops≔lam₂ : ∀ {A C Γ w w′} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (γ : w ⊩⋆ Γ ∖ i) (p : w ≤ w′) (s : w′ ⊩ A) →
                mono⊩ {C} p (eval c γ) ≡ eval (mono⊢ (weak⊆ {A = A}) c) (mono⊩⋆ p γ , s)
  -- oops≔lam₂ i c γ p s = {!!}

  oops≔lam₁ : ∀ {A B C Γ w w′} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (d : Γ , A ⊢ B) (γ : w ⊩⋆ Γ ∖ i) (p : w ≤ w′) (s : w′ ⊩ A) →
              eval d (mono⊩⋆ p (plug i γ (eval c γ)) , s) ≡ eval d (plug i (mono⊩⋆ p γ) (eval (mono⊢ (weak⊆ {A = A}) c) (mono⊩⋆ p γ , s)) , s)
  oops≔lam₁ {A} {B} {C} i c d γ p s =
    begin
      eval d (mono⊩⋆ p (plug i γ (eval c γ)) , s)
    ≡⟨ cong (eval d) (cong² _,_ (lem₁ i γ (eval c γ) p) refl) ⟩
      eval d (plug i (mono⊩⋆ p γ) (mono⊩ {C} p (eval c γ)) , s)
    ≡⟨ cong (eval d) (cong² _,_ (cong² (plug i) refl (oops≔lam₂ i c γ p s)) refl) ⟩
      eval d (plug i (mono⊩⋆ p γ) (eval (mono⊢ weak⊆ c) (mono⊩⋆ p γ , s)) , s)
    ∎

  oops≔lam : ∀ {A B C Γ w} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (d : Γ , A ⊢ B) →
             ⟦ i ≔ eval c {w} ⟧ {A ⇒ B} (⟪lam⟫ {A} {B} (eval d)) ≡
               ⟪lam⟫ {A} {B} (⟦ pop {A = C} {B = A} i ≔ eval (mono⊢ (weak⊆ {A = A}) c) ⟧ {B} (eval d))
  oops≔lam i c d = funext (λ γ → ⟨funext⟩ (funext (λ p → funext (λ s → oops≔lam₁ i c d γ p s))))


  mutual
    lem≔ : ∀ {A C Γ w} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (d : Γ ⊢ A) →
           ⟦ i ≔ eval c ⟧ {A} (eval d) ≡ eval ([ i ≔ c ] d) {w}
    lem≔ i c (var j)    = lem≔var i c j
    lem≔ i c (lam d)    = lem≔lam i c d
    lem≔ i c (app d e)  = lem≔app i c d e
    lem≔ i c (pair d e) = lem≔pair i c d e
    lem≔ i c (fst d)    = lem≔fst i c d
    lem≔ i c (snd d)    = lem≔snd i c d
    lem≔ i c unit       = lem≔unit i c

    lem≔var : ∀ {A C Γ w} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (j : A ∈ Γ) →
              ⟦ i ≔ eval c ⟧ {A} (⟪var⟫ {A} j) ≡ eval ([ i ≔ c ] (var j)) {w}
    lem≔var {A} i c j =
      begin
        ⟦ i ≔ eval c ⟧ {A} (⟪var⟫ {A} j)
      ≡⟨ oops≔var i (eval c) j ⟩
        ⟦ i ≔ eval c ⟧∈ {A} j
      ≡⟨ lem≔∈ i c j ⟩
        eval ([ i ≔ c ]∈ j)
      ≡⟨⟩
        eval ([ i ≔ c ] (var j))
      ∎

    lem≔lam : ∀ {A B C Γ w} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (d : Γ , A ⊢ B) →
              ⟦ i ≔ eval c ⟧ {A ⇒ B} (⟪lam⟫ {A} {B} (eval d)) ≡ eval ([ i ≔ c ] (lam d)) {w}
    lem≔lam {A} {B} {C} i c d =
      begin
        ⟦ i ≔ eval c ⟧ {A ⇒ B} (⟪lam⟫ {A} {B} (eval d))
      ≡⟨ oops≔lam i c d ⟩
        ⟪lam⟫ {A} {B} (⟦ pop {A = C} {B = A} i ≔ eval (mono⊢ (weak⊆ {A = A}) c) ⟧ {B} (eval d))
      ≡⟨ cong (⟪lam⟫ {A} {B}) (⟨funext⟩ (lem≔ (pop i) (mono⊢ (weak⊆ {A = A}) c) d)) ⟩
        ⟪lam⟫ {A} {B} (eval ([ pop {A = C} {B = A} i ≔ mono⊢ (weak⊆ {A = A}) c ] d))
      ≡⟨⟩
        eval (lam ([ pop i ≔ mono⊢ weak⊆ c ] d))
      ≡⟨⟩
        eval ([ i ≔ c ] (lam d))
      ∎

    lem≔app : ∀ {A B C Γ w} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (d : Γ ⊢ A ⇒ B) (e : Γ ⊢ A) →
              ⟦ i ≔ eval c ⟧ {B} (⟪app⟫ {A} {B} (eval d) (eval e)) ≡ eval ([ i ≔ c ] (app d e)) {w}
    lem≔app {A} {B} i c d e =
      begin
        ⟦ i ≔ eval c ⟧ {B} (⟪app⟫ {A} {B} (eval d) (eval e))
      ≡⟨⟩
        ⟪app⟫ {A} {B} (⟦ i ≔ eval c ⟧ {A ⇒ B} (eval d)) (⟦ i ≔ eval c ⟧ {A} (eval e))
      ≡⟨ cong² (⟪app⟫ {A} {B}) (lem≔ i c d) (funext (λ γ → extfun (lem≔ i c e) γ)) ⟩
        ⟪app⟫ {A} {B} (eval ([ i ≔ c ] d)) (eval ([ i ≔ c ] e))
      ≡⟨⟩
        eval (app ([ i ≔ c ] d) ([ i ≔ c ] e))
      ≡⟨⟩
        eval ([ i ≔ c ] (app d e))
      ∎

    lem≔pair : ∀ {A B C Γ w} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (d : Γ ⊢ A) (e : Γ ⊢ B) →
               ⟦ i ≔ eval c ⟧ {A ⩕ B} (⟪pair⟫ {A} {B} (eval d) (eval e)) ≡ eval ([ i ≔ c ] (pair d e)) {w}
    lem≔pair {A} {B} i c d e =
      begin
        ⟦ i ≔ eval c ⟧ {A ⩕ B} (⟪pair⟫ {A} {B} (eval d) (eval e))
      ≡⟨⟩
        ⟪pair⟫ {A} {B} (⟦ i ≔ eval c ⟧ {A} (eval d)) (⟦ i ≔ eval c ⟧ {B} (eval e))
      ≡⟨ cong² (⟪pair⟫ {A} {B}) (lem≔ i c d) (lem≔ i c e) ⟩
        ⟪pair⟫ {A} {B} (eval ([ i ≔ c ] d)) (eval ([ i ≔ c ] e))
      ≡⟨⟩
        eval (pair ([ i ≔ c ] d) ([ i ≔ c ] e))
      ≡⟨⟩
        eval ([ i ≔ c ] (pair d e))
      ∎

    lem≔fst : ∀ {A B C Γ w} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (d : Γ ⊢ A ⩕ B) →
              ⟦ i ≔ eval c ⟧ {A} (⟪fst⟫ {A} {B} (eval d)) ≡ eval ([ i ≔ c ] (fst d)) {w}
    lem≔fst {A} {B} i c d =
      begin
        ⟦ i ≔ eval c ⟧ {A} (⟪fst⟫ {A} {B} (eval d))
      ≡⟨⟩
        ⟪fst⟫ {A} {B} (⟦ i ≔ eval c ⟧ {A ⩕ B} (eval d))
      ≡⟨ cong (⟪fst⟫ {A} {B}) (lem≔ i c d) ⟩
        ⟪fst⟫ {A} {B} (eval ([ i ≔ c ] d))
      ≡⟨⟩
        eval (fst ([ i ≔ c ] d))
      ≡⟨⟩
        eval ([ i ≔ c ] (fst d))
      ∎

    lem≔snd : ∀ {A B C Γ w} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) (d : Γ ⊢ A ⩕ B) →
              ⟦ i ≔ eval c ⟧ {B} (⟪snd⟫ {A} {B} (eval d)) ≡ eval ([ i ≔ c ] (snd d)) {w}
    lem≔snd {A} {B} i c d =
      begin
        ⟦ i ≔ eval c ⟧ {B} (⟪snd⟫ {A} {B} (eval d))
      ≡⟨⟩
        ⟪snd⟫ {A} {B} (⟦ i ≔ eval c ⟧ {A ⩕ B} (eval d))
      ≡⟨ cong (⟪snd⟫ {A} {B}) (lem≔ i c d) ⟩
        ⟪snd⟫ {A} {B} (eval ([ i ≔ c ] d))
      ≡⟨⟩
        eval (snd ([ i ≔ c ] d))
      ≡⟨⟩
        eval ([ i ≔ c ] (snd d))
      ∎

    lem≔unit : ∀ {C Γ w} → (i : C ∈ Γ) (c : Γ ∖ i ⊢ C) →
               ⟦ i ≔ eval c ⟧ {⫪} ⟪unit⟫ ≡ eval ([ i ≔ c ] unit) {w}
    lem≔unit i c = refl


-- TODO: Naming things.

-- NOTE: This is using {-# REWRITE idmono⊩⋆ #-}.

module _ {{_ : Model}} where
  lemreduce⇒ : ∀ {A B Γ w} → (d : Γ , A ⊢ B) (e : Γ ⊢ A) →
                ⟪app⟫ {A} {B} (⟪lam⟫ {A} {B} (eval d)) (eval e {w}) ≡ eval ([ top ≔ e ] d) {w}
  lemreduce⇒ d e = lem≔ top e d


-- TODO: The expand⇒ case in eval✓.

module _ {{_ : Model}} where
  postulate
    lemexpand⇒ : ∀ {A B Γ w} → (d : Γ ⊢ A ⇒ B) →
                  eval d {w} ≡ ⟪lam⟫ {A} {B} (⟪app⟫ {A} {B} {Γ , A} (eval (mono⊢ {A ⇒ B} (weak⊆ {A = A}) d)) (⟪v₀⟫ {A}))
  -- lemexpand⇒ d = {!!}


-- Correctness of evaluation with respect to β-η-equivalence.

module _ {{_ : Model}} where
  eval✓ : ∀ {A Γ} {d d′ : Γ ⊢ A} {w} → d ≡ᵝᵑ d′ → eval d {w} ≡ eval d′ {w}
  eval✓ refl≡ᵝᵑ                   = refl
  eval✓ (trans≡ᵝᵑ p q)            = trans (eval✓ p) (eval✓ q)
  eval✓ (sym≡ᵝᵑ p)                = sym (eval✓ p)
  eval✓ (cong≡ᵝᵑlam {A} {B} p)    = cong (⟪lam⟫ {A} {B}) (⟨funext⟩ (eval✓ p))
  eval✓ (cong≡ᵝᵑapp {A} {B} p q)  = cong² (⟪app⟫ {A} {B}) (eval✓ p) (eval✓ q)
  eval✓ (cong≡ᵝᵑpair {A} {B} p q) = cong² (⟪pair⟫ {A} {B}) (eval✓ p) (eval✓ q)
  eval✓ (cong≡ᵝᵑfst {A} {B} p)    = cong (⟪fst⟫ {A} {B}) (eval✓ p)
  eval✓ (cong≡ᵝᵑsnd {A} {B} p)    = cong (⟪snd⟫ {A} {B}) (eval✓ p)
  eval✓ (reduce⇒ d e)            = lemreduce⇒ d e
  eval✓ (reduce⩕₁ d e)            = refl
  eval✓ (reduce⩕₂ d e)            = refl
  eval✓ (expand⇒ d)              = lemexpand⇒ d
  eval✓ (expand⩕ d)               = refl
  eval✓ (expand⫪ d)              = refl
