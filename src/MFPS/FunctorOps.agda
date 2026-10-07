------------------------------------------------------------------------
-- The categories FreydOp and FreydPROP (§3.5): identity and composition
-- of Freyd operad functors and of Freyd PROP functors, and pointwise
-- equality of functors (the equality used for the hom-set bijection of
-- Theorem 3.21).
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude hiding (_∘_; id)
open import MFPS.Preoperad
open import MFPS.PROP

module MFPS.FunctorOps where

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- FreydOp
------------------------------------------------------------------------

idᴾ : {C : Preoperad} → PreoperadFunctor C C
idᴾ {C} = record { F = λ x → x ; F-cong = λ e → e ; F-id = ≈.refl ; F-sub = λ _ _ → ≈.refl }
  where open Preoperad C

_∘ᴾ_ : {C₁ C₂ C₃ : Preoperad} → PreoperadFunctor C₂ C₃ → PreoperadFunctor C₁ C₂ → PreoperadFunctor C₁ C₃
_∘ᴾ_ {C₃ = C₃} G₂ G₁ = record
  { F      = λ x → G₂.F (G₁.F x)
  ; F-cong = λ e → G₂.F-cong (G₁.F-cong e)
  ; F-id   = ≈.trans (G₂.F-cong G₁.F-id) G₂.F-id
  ; F-sub  = λ f g → ≈.trans (G₂.F-cong (G₁.F-sub f g)) (G₂.F-sub _ _) }
  where
    open Preoperad C₃
    module G₁ = PreoperadFunctor G₁
    module G₂ = PreoperadFunctor G₂

idᴼ : {M : FreydOperad} → FreydOperadFunctor M M
idᴼ {M} = record
  { Gᵛ = idᴾ ; Gᵛ-ren = record { F-ren = λ _ _ → 𝕍.≈.refl }
  ; Gᶜ = idᴾ ; Gᶜ-ren = record { F-ren = λ _ _ → ℂ.≈.refl }
  ; G-J = λ _ → ℂ.≈.refl }
  where open FreydOperad M

_∘ᴼ_ : {M₁ M₂ M₃ : FreydOperad} → FreydOperadFunctor M₂ M₃ → FreydOperadFunctor M₁ M₂ → FreydOperadFunctor M₁ M₃
_∘ᴼ_ {M₃ = M₃} G₂ G₁ = record
  { Gᵛ     = G₂.Gᵛ ∘ᴾ G₁.Gᵛ
  ; Gᵛ-ren = record { F-ren = λ x r → 𝕍.≈.trans (G₂.𝒢ᵛ-cong (G₁.𝒢ᵛ-ren x r)) (G₂.𝒢ᵛ-ren _ r) }
  ; Gᶜ     = G₂.Gᶜ ∘ᴾ G₁.Gᶜ
  ; Gᶜ-ren = record { F-ren = λ x r → ℂ.≈.trans (G₂.𝒢ᶜ-cong (G₁.𝒢ᶜ-ren x r)) (G₂.𝒢ᶜ-ren _ r) }
  ; G-J    = λ v → ℂ.≈.trans (G₂.𝒢ᶜ-cong (G₁.G-J v)) (G₂.G-J _) }
  where
    open FreydOperad M₃
    module G₁ = FreydOperadFunctor G₁
    module G₂ = FreydOperadFunctor G₂

-- pointwise equality of Freyd operad functors
infix 4 _≈ᴼ_
_≈ᴼ_ : {M₁ M₂ : FreydOperad} → FreydOperadFunctor M₁ M₂ → FreydOperadFunctor M₁ M₂ → Set
_≈ᴼ_ {M₁} {M₂} G G' =
  (∀ {n} (v : M₁.𝕍.Op n) → G.𝒢ᵛ v M₂.𝕍.≈ G'.𝒢ᵛ v) × (∀ {n} (f : M₁.ℂ.Op n) → G.𝒢ᶜ f M₂.ℂ.≈ G'.𝒢ᶜ f)
  where
    module M₁ = FreydOperad M₁
    module M₂ = FreydOperad M₂
    module G = FreydOperadFunctor G
    module G' = FreydOperadFunctor G'

------------------------------------------------------------------------
-- FreydPROP
------------------------------------------------------------------------

idᴴ : {D : PrePROP} → PrePROPFunctor D D
idᴴ {D} = record
  { F = λ f → f ; F-cong = λ e → e ; F-id = ≈.refl ; F-∘ = λ _ _ → ≈.refl
  ; F-⊣ = λ _ → ≈.refl ; F-⊢ = λ _ → ≈.refl ; F-σ = ≈.refl }
  where open PrePROP D

_∘ᴴ_ : {D₁ D₂ D₃ : PrePROP} → PrePROPFunctor D₂ D₃ → PrePROPFunctor D₁ D₂ → PrePROPFunctor D₁ D₃
_∘ᴴ_ {D₃ = D₃} F₂ F₁ = record
  { F      = λ f → F₂.F (F₁.F f)
  ; F-cong = λ e → F₂.F-cong (F₁.F-cong e)
  ; F-id   = ≈.trans (F₂.F-cong F₁.F-id) F₂.F-id
  ; F-∘    = λ f g → ≈.trans (F₂.F-cong (F₁.F-∘ f g)) (F₂.F-∘ _ _)
  ; F-⊣    = λ f → ≈.trans (F₂.F-cong (F₁.F-⊣ f)) (F₂.F-⊣ _)
  ; F-⊢    = λ f → ≈.trans (F₂.F-cong (F₁.F-⊢ f)) (F₂.F-⊢ _)
  ; F-σ    = ≈.trans (F₂.F-cong F₁.F-σ) F₂.F-σ }
  where
    open PrePROP D₃
    module F₁ = PrePROPFunctor F₁
    module F₂ = PrePROPFunctor F₂

idᶜᴾ : {V : CartesianPROP} → CartesianPROPFunctor V V
idᶜᴾ {V} = record { functor = idᴴ ; F-ρ = λ _ → ≈.refl }
  where open CartesianPROP V

_∘ᶜᴾ_ : {V₁ V₂ V₃ : CartesianPROP} → CartesianPROPFunctor V₂ V₃ → CartesianPROPFunctor V₁ V₂ → CartesianPROPFunctor V₁ V₃
_∘ᶜᴾ_ {V₃ = V₃} F₂ F₁ = record
  { functor = F₂.functor ∘ᴴ F₁.functor
  ; F-ρ = λ r → ≈.trans (F₂.F-cong (F₁.F-ρ r)) (F₂.F-ρ r) }
  where
    open CartesianPROP V₃
    module F₁ = CartesianPROPFunctor F₁
    module F₂ = CartesianPROPFunctor F₂

idᶠ : {D : FreydPROP} → FreydPROPFunctor D D
idᶠ {D} = record { Fᵛ = idᶜᴾ ; Fᶜ = idᴴ ; F-J = λ _ → ℂ.≈.refl }
  where open FreydPROP D

_∘ᶠ_ : {D₁ D₂ D₃ : FreydPROP} → FreydPROPFunctor D₂ D₃ → FreydPROPFunctor D₁ D₂ → FreydPROPFunctor D₁ D₃
_∘ᶠ_ {D₃ = D₃} F₂ F₁ = record
  { Fᵛ  = F₂.Fᵛ ∘ᶜᴾ F₁.Fᵛ
  ; Fᶜ  = F₂.Fᶜ ∘ᴴ F₁.Fᶜ
  ; F-J = λ v → ℂ.≈.trans (F₂.ℱᶜ-cong (F₁.F-J v)) (F₂.F-J _) }
  where
    open FreydPROP D₃
    module F₁ = FreydPROPFunctor F₁
    module F₂ = FreydPROPFunctor F₂

-- pointwise equality of Freyd PROP functors
infix 4 _≈ᶠ_
_≈ᶠ_ : {D₁ D₂ : FreydPROP} → FreydPROPFunctor D₁ D₂ → FreydPROPFunctor D₁ D₂ → Set
_≈ᶠ_ {D₁} {D₂} F F' =
  (∀ {m n} (f : D₁.𝕍.Hom m n) → F.ℱᵛ f D₂.𝕍.≈ F'.ℱᵛ f) × (∀ {m n} (f : D₁.ℂ.Hom m n) → F.ℱᶜ f D₂.ℂ.≈ F'.ℱᶜ f)
  where
    module D₁ = FreydPROP D₁
    module D₂ = FreydPROP D₂
    module F = FreydPROPFunctor F
    module F' = FreydPROPFunctor F'

≈ᶠ-sym : {D₁ D₂ : FreydPROP} {F F' : FreydPROPFunctor D₁ D₂} → F ≈ᶠ F' → F' ≈ᶠ F
≈ᶠ-sym {D₂ = D₂} (eᵛ , eᶜ) = (λ f → D₂.𝕍.≈.sym (eᵛ f)) , (λ f → D₂.ℂ.≈.sym (eᶜ f))
  where module D₂ = FreydPROP D₂

≈ᶠ-trans : {D₁ D₂ : FreydPROP} {F F' F'' : FreydPROPFunctor D₁ D₂} → F ≈ᶠ F' → F' ≈ᶠ F'' → F ≈ᶠ F''
≈ᶠ-trans {D₂ = D₂} (eᵛ , eᶜ) (eᵛ' , eᶜ') = (λ f → D₂.𝕍.≈.trans (eᵛ f) (eᵛ' f)) , (λ f → D₂.ℂ.≈.trans (eᶜ f) (eᶜ' f))
  where module D₂ = FreydPROP D₂
