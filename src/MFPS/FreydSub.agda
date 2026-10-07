------------------------------------------------------------------------
-- Definition 3.13, Proposition 3.14(iii) (well-definedness of J^Sub)
-- and Theorem 3.18(iii) (J is natural) for a Freyd operad (𝕍, ℂ, J).
--
-- Sub×_𝕍 is the quotient of words over 𝕍 by all rules of Fig. 3;
-- Sub_ℂ is the quotient of words over ℂ by the symmetric rules together
-- with the cartesian rules for steps whose operation is a J-image (see
-- the note in MFPS.Sub).
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.FreydSub (M : FreydOperad) where

open FreydOperad M

private
  variable
    k m n : ℕ

-- the value side as a symmetric preoperad
𝕊ᵥ : SymPreoperad
𝕊ᵥ = record { C = 𝕍.V ; ren = 𝕍.ren ; symm = 𝕍.symm }

import MFPS.Sub 𝕊ᵥ as V
import MFPS.Sub ℂ as C
import MFPS.SubSound 𝕊ᵥ as VS
import MFPS.SubSound ℂ as CS
import MFPS.Representable 𝕊ᵥ as VR
import MFPS.Representable ℂ as CR

-- "is a J-image"
JImg : ∀ {n} → ℂ.Op n → Set
JImg {n} g = Σ (𝕍.Op n) λ v → 𝒥 v ≡ g

-- the two congruences
_≅ᵛ_ : V.Word m n → V.Word m n → Set
_≅ᵛ_ = V.Cong (λ _ → ⊤)

_≅ᶜ_ : C.Word m n → C.Word m n → Set
_≅ᶜ_ = C.Cong JImg

-- both are sound for ⋆ (Theorem 3.16 (i) and (ii))
cartRulesᵥ : VS.CartRules (λ _ → ⊤)
cartRulesᵥ = record
  { central = λ {_} {g} _ → 𝕍.operad g
  ; discard = λ {_} {g} _ f → 𝕍.!-nat f g
  ; copy    = λ {_} {g} _ f p q → 𝕍.Δ-nat f g p q }

cartRulesᶜ : CS.CartRules JImg
cartRulesᶜ = record
  { central = λ { (v , refl) → J-central v }
  ; discard = λ { (v , refl) f → J-discard f v }
  ; copy    = λ { (v , refl) f p q → J-copy f v p q } }

open VS.Soundness cartRulesᵥ public renaming (⋆-sound to ⋆-soundᵛ)
open CS.Soundness cartRulesᶜ public renaming (⋆-sound to ⋆-soundᶜ)

------------------------------------------------------------------------
-- Definition 3.13: J^Sub, as the instance of the general construction
-- of MFPS.SubFunctor for the functor J
------------------------------------------------------------------------

open import MFPS.SubFunctor 𝕊ᵥ ℂ J J-ren public
  renaming (GStep to JStep; GSub to JSub; GSub-++ to JSub-++; GSub-⊣ to JSub-⊣; GSub-⊢ to JSub-⊢;
            GSub-⋆₁ to J-nat₁; GSub-⋆ to J-nat; GSub-cong to GSub-congJ; GSubFunctor to GSubFunctorJ)

JSub-sub! : ∀ n₁ n₂ {m} (v : 𝕍.Op m) → JStep (V.sub! n₁ n₂ v) ≡ C.sub! n₁ n₂ (𝒥 v)
JSub-sub! n₁ n₂ v = refl

------------------------------------------------------------------------
-- Proposition 3.14(iii): J^Sub respects the congruences.  A cartesian
-- step {n₁ ⊣ v ⊢ n₂} of Sub×_𝕍 is mapped to the step {n₁ ⊣ Jv ⊢ n₂},
-- which is a J-image, hence cartesian in Sub_ℂ.
------------------------------------------------------------------------

cart-mapJ : ∀ {n} {g : 𝕍.Op n} → ⊤ → Σ (ℂ.Op n) λ g' → JImg g' × (𝒥 g ℂ.≈ g')
cart-mapJ {g = g} _ = 𝒥 g , (g , refl) , ℂ.≈.refl

JSub-cong : {Γ Δ : V.Word m n} → Γ ≅ᵛ Δ → JSub Γ ≅ᶜ JSub Δ
JSub-cong = GSub-congJ cart-mapJ

-- Theorem 3.18(iii), J : 𝕍 ⇒ ℂ ∘ J^Sub is natural:  `J-nat`
--   J-nat : (v : 𝕍.Op n) (Γ : V.Word m n) → 𝒥 v C.⋆ JSub Γ ℂ.≈ 𝒥 (v V.⋆ Γ)

------------------------------------------------------------------------
-- Proposition 3.14(iii): (Sub×_𝕍, Sub_ℂ, J^Sub) is a Freyd PROP.
-- J^Sub is a pre-PROP functor (identity on renamings and symmetries,
-- commutes with concatenation and whiskering on the nose), and its
-- image is central: every step of J^Sub Γ is a renaming or a J-image
-- step, and such words are central in Sub_ℂ (MFPS.SubCentral).
------------------------------------------------------------------------

import MFPS.SubPROP ℂ as CP
import MFPS.SubCartesian 𝕊ᵥ as VC
import MFPS.SubCentral ℂ as CC
open import MFPS.PROP using (PrePROPFunctor; FreydPROP)

JSubFunctor : PrePROPFunctor (MFPS.PROP.CartesianPROP.P VC.Sub×PROP) (CP.SubPrePROP JImg)
JSubFunctor = GSubFunctorJ cart-mapJ

JSub-allCart : (Γ : V.Word m n) → CC.AllCart {Cart = JImg} (JSub Γ)
JSub-allCart V.ε = tt
JSub-allCart (V.ins _ _ _ _ v V.∷ Γ) = (v , refl) , JSub-allCart Γ
JSub-allCart (V.rn r V.∷ Γ) = JSub-allCart Γ

FreydSubPROP : FreydPROP
FreydSubPROP = record
  { 𝕍 = VC.Sub×PROP
  ; ℂ = CP.SubPrePROP JImg
  ; J = JSubFunctor
  ; J-central = λ Γ → CC.central-word (JSub Γ) (JSub-allCart Γ)
  }

-- J^Sub commutes with the representations of Thm. 3.18
JSub-η : (v : 𝕍.Op n) → JSub (VR.ηʷ v) ≡ CR.ηʷ (𝒥 v)
JSub-η v = refl
