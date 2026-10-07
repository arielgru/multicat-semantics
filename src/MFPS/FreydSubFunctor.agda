------------------------------------------------------------------------
-- Proposition 3.14(iv) / Definition 3.20 on morphisms: a Freyd operad
-- functor (Gᵛ, Gᶜ) : (𝕍₁, ℂ₁, J₁) → (𝕍₂, ℂ₂, J₂) induces a Freyd PROP
-- functor (G^Sub×, G^Sub) : F(𝕍₁, ℂ₁, J₁) → F(𝕍₂, ℂ₂, J₂), "obtained by
-- applying Gᵛ and Gᶜ to each substitution step and leaving renamings
-- unchanged".
--
-- Both components are instances of MFPS.SubFunctor.  The only point
-- needing care is the cartesian congruence of Sub_ℂ: a J₁-image step
-- {Jv} is mapped to {Gᶜ(J₁ v)}, which is only ≈ to the J₂-image
-- {J₂(Gᵛ v)}; rule (I) bridges the gap.  Compatibility with J^Sub is
-- likewise the axiom G-J applied step by step.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.FreydSubFunctor {M₁ M₂ : FreydOperad} (G : FreydOperadFunctor M₁ M₂) where

open FreydOperadFunctor G
private
  module M₁ = FreydOperad M₁
  module M₂ = FreydOperad M₂

import MFPS.FreydSub M₁ as F₁
import MFPS.FreydSub M₂ as F₂
import MFPS.Sub F₁.𝕊ᵥ as V₁
import MFPS.Sub F₂.𝕊ᵥ as V₂
import MFPS.Sub M₁.ℂ as C₁
import MFPS.Sub M₂.ℂ as C₂
import MFPS.SubFunctor F₁.𝕊ᵥ F₂.𝕊ᵥ Gᵛ Gᵛ-ren as GV
import MFPS.SubFunctor M₁.ℂ M₂.ℂ Gᶜ Gᶜ-ren as GC
import MFPS.SubCartesian F₁.𝕊ᵥ as VC₁
import MFPS.SubCartesian F₂.𝕊ᵥ as VC₂
open import MFPS.PROP

private
  variable
    m n : ℕ

-- cartesian steps are mapped to cartesian steps (up to ≈)
cart-mapᵛ : ∀ {n} {g : M₁.𝕍.Op n} → ⊤ → Σ (M₂.𝕍.Op n) λ g' → ⊤ × (𝒢ᵛ g M₂.𝕍.≈ g')
cart-mapᵛ {g = g} _ = 𝒢ᵛ g , tt , M₂.𝕍.≈.refl

cart-mapᶜ : ∀ {n} {g : M₁.ℂ.Op n} → F₁.JImg g → Σ (M₂.ℂ.Op n) λ g' → F₂.JImg g' × (𝒢ᶜ g M₂.ℂ.≈ g')
cart-mapᶜ (v , refl) = M₂.𝒥 (𝒢ᵛ v) , (𝒢ᵛ v , refl) , G-J v

-- the value component is a cartesian PROP functor (it is the identity
-- on renaming steps, hence preserves ρ on the nose)
GSubᵛ : CartesianPROPFunctor VC₁.Sub×PROP VC₂.Sub×PROP
GSubᵛ = record { functor = GV.GSubFunctor cart-mapᵛ ; F-ρ = λ r → V₂.≅-refl }

-- compatibility with J^Sub
GSub-J : (Γ : V₁.Word m n) → C₂.Cong F₂.JImg (GC.GSub (F₁.JSub Γ)) (F₂.JSub (GV.GSub Γ))
GSub-J V₁.ε = C₂.≅-refl
GSub-J (V₁.rn r V₁.∷ Γ) = C₂.≅-∷ (GSub-J Γ)
GSub-J (V₁.ins n₁ n₂ p q v V₁.∷ Γ) =
  C₂.≅-trans (C₂.≅-∷ˡ (C₂.I∙ n₁ n₂ p q (G-J v))) (C₂.≅-∷ (GSub-J Γ))

-- Proposition 3.14(iv)
FSub : FreydPROPFunctor F₁.FreydSubPROP F₂.FreydSubPROP
FSub = record
  { Fᵛ  = GSubᵛ
  ; Fᶜ  = GC.GSubFunctor cart-mapᶜ
  ; F-J = GSub-J
  }
