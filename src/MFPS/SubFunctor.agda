------------------------------------------------------------------------
-- Functoriality of the substitution construction in the preoperad
-- (Proposition 3.14(iv), Definition 3.20 on morphisms).
--
-- A Ren-preserving preoperad functor 𝒢 : ℂ₁ → ℂ₂ acts on words by
-- applying 𝒢 to every substitution step and leaving renamings
-- unchanged.  This module shows that the induced map respects the
-- congruence of Fig. 3 (for any choice of the cartesian predicates,
-- provided 𝒢 maps cartesian steps to cartesian steps up to ≈), that it
-- is a pre-PROP functor, and that it is compatible with the action ⋆
-- (this is Thm. 3.18(iii) for 𝒢 in place of J).
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.SubFunctor (𝕊₁ 𝕊₂ : SymPreoperad)
  (G : PreoperadFunctor (SymPreoperad.C 𝕊₁) (SymPreoperad.C 𝕊₂))
  (G-ren : CartesianFunctor (SymPreoperad.ren 𝕊₁) (SymPreoperad.ren 𝕊₂) G)
  where

private
  module S₁ = SymPreoperad 𝕊₁
  module S₂ = SymPreoperad 𝕊₂

open PreoperadFunctor G renaming (F to 𝒢; F-cong to 𝒢-cong; F-id to 𝒢-id; F-sub to 𝒢-sub; F-subst to 𝒢-subst)
open CartesianFunctor G-ren renaming (F-ren to 𝒢-ren)

import MFPS.Sub 𝕊₁ as W₁
import MFPS.Sub 𝕊₂ as W₂
import MFPS.SubPROP 𝕊₁ as P₁
import MFPS.SubPROP 𝕊₂ as P₂
open import MFPS.PROP using (PrePROPFunctor)

private
  variable
    k m n : ℕ

------------------------------------------------------------------------
-- the action on steps and words
------------------------------------------------------------------------

GStep : W₁.Step m n → W₂.Step m n
GStep (W₁.ins n₁ n₂ p q v) = W₂.ins n₁ n₂ p q (𝒢 v)
GStep (W₁.rn r)            = W₂.rn r

GSub : W₁.Word m n → W₂.Word m n
GSub W₁.ε       = W₂.ε
GSub (s W₁.∷ Γ) = GStep s W₂.∷ GSub Γ

GSub-++ : (Γ₁ : W₁.Word k n) (Γ₂ : W₁.Word m k) → GSub (Γ₁ W₁.++ Γ₂) ≡ GSub Γ₁ W₂.++ GSub Γ₂
GSub-++ W₁.ε        Γ₂ = refl
GSub-++ (s W₁.∷ Γ₁) Γ₂ = cong (GStep s W₂.∷_) (GSub-++ Γ₁ Γ₂)

GSub-⊣ : ∀ k (Γ : W₁.Word m n) → GSub (k W₁.⊣ʷ Γ) ≡ k W₂.⊣ʷ GSub Γ
GSub-⊣ k W₁.ε = refl
GSub-⊣ k (W₁.ins n₁ n₂ p q v W₁.∷ Γ) = cong (_ W₂.∷_) (GSub-⊣ k Γ)
GSub-⊣ k (W₁.rn r W₁.∷ Γ)            = cong (_ W₂.∷_) (GSub-⊣ k Γ)

GSub-⊢ : ∀ k (Γ : W₁.Word m n) → GSub (Γ W₁.⊢ʷ k) ≡ GSub Γ W₂.⊢ʷ k
GSub-⊢ k W₁.ε = refl
GSub-⊢ k (W₁.ins n₁ n₂ p q v W₁.∷ Γ) = cong (_ W₂.∷_) (GSub-⊢ k Γ)
GSub-⊢ k (W₁.rn r W₁.∷ Γ)            = cong (_ W₂.∷_) (GSub-⊢ k Γ)

------------------------------------------------------------------------
-- compatibility with ⋆ (Thm. 3.18(iii), for an arbitrary functor):
--   𝒢 f ⋆ GSub Γ ≈ 𝒢 (f ⋆ Γ)
------------------------------------------------------------------------

GSub-⋆₁ : (f : S₁.Op n) (s : W₁.Step m n) → 𝒢 f W₂.⋆₁ GStep s S₂.≈ 𝒢 (f W₁.⋆₁ s)
GSub-⋆₁ f (W₁.rn r) = S₂.≈.sym (𝒢-ren f r)
GSub-⋆₁ f (W₁.ins n₁ n₂ p q g) =
  S₂.≈.trans (S₂.subst-cong (sym p) (S₂.sub-cong (S₂.≈.reflexive (sym (𝒢-subst q f))) S₂.≈.refl))
  (S₂.≈.trans (S₂.subst-cong (sym p) (S₂.≈.sym (𝒢-sub (subst S₁.Op q f) g)))
              (S₂.≈.reflexive (sym (𝒢-subst (sym p) _))))

GSub-⋆ : (f : S₁.Op n) (Γ : W₁.Word m n) → 𝒢 f W₂.⋆ GSub Γ S₂.≈ 𝒢 (f W₁.⋆ Γ)
GSub-⋆ f W₁.ε       = S₂.≈.refl
GSub-⋆ f (s W₁.∷ Γ) = S₂.≈.trans (W₂.⋆-cong (GSub-⋆₁ f s) (GSub Γ)) (GSub-⋆ (f W₁.⋆₁ s) Γ)

------------------------------------------------------------------------
-- the induced map respects the congruences
------------------------------------------------------------------------

module _ {Cart₁ : ∀ {n} → S₁.Op n → Set} {Cart₂ : ∀ {n} → S₂.Op n → Set}
  (cart-map : ∀ {n} {g : S₁.Op n} → Cart₁ g → Σ (S₂.Op n) λ g' → Cart₂ g' × (𝒢 g S₂.≈ g'))
  where

  GSub-cong : {Γ Δ : W₁.Word m n} → W₁.Cong Cart₁ Γ Δ → W₂.Cong Cart₂ (GSub Γ) (GSub Δ)
  GSub-cong W₁.≅-refl = W₂.≅-refl
  GSub-cong (W₁.≅-sym e) = W₂.≅-sym (GSub-cong e)
  GSub-cong (W₁.≅-trans e e') = W₂.≅-trans (GSub-cong e) (GSub-cong e')
  GSub-cong (W₁.≅-cong {Γ₁ = Γ₁} {Γ₁'} {Γ₂} {Γ₂'} e₁ e₂) =
    W₂.≅-trans (W₂.≅-≡ (GSub-++ Γ₁ Γ₂))
    (W₂.≅-trans (W₂.≅-cong (GSub-cong e₁) (GSub-cong e₂))
                (W₂.≅-≡ (sym (GSub-++ Γ₁' Γ₂'))))
  -- administrative rules
  GSub-cong (W₁.I∙ n₁ n₂ p q e) = W₂.I∙ n₁ n₂ p q (𝒢-cong e)
  GSub-cong (W₁.E∙ e) = W₂.E∙ e
  GSub-cong (W₁.S∙ n₁ n₂ p q g) = W₂.S∙ n₁ n₂ p q (𝒢 g)
  -- symmetric rules: each is the corresponding rule in the target,
  -- corrected by (I) using the functor laws of 𝒢
  GSub-cong (W₁.U₁∙ n₁ n₂ p) = W₂.≅-trans (W₂.I∙ n₁ n₂ p p 𝒢-id) (W₂.U₁∙ n₁ n₂ p)
  GSub-cong W₁.U₂∙ = W₂.U₂∙
  GSub-cong (W₁.A∙ m₁ m₂ n₁ n₂ g h p₁ q₁ p₂ q₂ p₃) =
    W₂.≅-trans (W₂.A∙ m₁ m₂ n₁ n₂ (𝒢 g) (𝒢 h) p₁ q₁ p₂ q₂ p₃)
               (W₂.I∙ m₁ m₂ p₃ q₁ (S₂.≈.sym (𝒢-sub g h)))
  GSub-cong (W₁.R∙ r₁ r₂) = W₂.R∙ r₁ r₂
  GSub-cong (W₁.N∙ v r₁ s r₂) =
    W₂.≅-trans (W₂.N∙ (𝒢 v) r₁ s r₂)
               (W₂.≅-∷ (W₂.I∙ _ _ refl refl (S₂.≈.sym (𝒢-ren v s))))
  GSub-cong (W₁.Sℓ∙ m₁ m₂ g p q q') = W₂.Sℓ∙ m₁ m₂ (𝒢 g) p q q'
  GSub-cong (W₁.Sr∙ m₁ m₂ g p q q' q'') = W₂.Sr∙ m₁ m₂ (𝒢 g) p q q' q''
  -- cartesian rules: the cartesian step is replaced (by (I)) by the
  -- cartesian step of the target provided by `cart-map`
  GSub-cong (W₁.CEN∙ m₁ m m₂ {n₁} {n₂} g₁ g₂ (inj₁ c₁) p q p' p'' q') =
    let (g₁' , c₁' , e) = cart-map c₁ in
    W₂.≅-trans (W₂.≅-∷ˡ (W₂.I∙ m₁ (m + suc m₂) refl refl e))
    (W₂.≅-trans (W₂.CEN∙ m₁ m m₂ g₁' (𝒢 g₂) (inj₁ c₁') p q p' p'' q')
                (W₂.≅-∷ (W₂.I∙ m₁ (m + (n₂ + m₂)) q' refl (S₂.≈.sym e))))
  GSub-cong (W₁.CEN∙ m₁ m m₂ {n₁} {n₂} g₁ g₂ (inj₂ c₂) p q p' p'' q') =
    let (g₂' , c₂' , e) = cart-map c₂ in
    W₂.≅-trans (W₂.≅-∷ (W₂.I∙ (m₁ + (n₁ + m)) m₂ q p e))
    (W₂.≅-trans (W₂.CEN∙ m₁ m m₂ (𝒢 g₁) g₂' (inj₂ c₂') p q p' p'' q')
                (W₂.≅-∷ˡ (W₂.I∙ (m₁ + suc m) m₂ (sym p'') p' (S₂.≈.sym e))))
  GSub-cong (W₁.D∙ m₁ m₂ g c) =
    let (g' , c' , e) = cart-map c in
    W₂.≅-trans (W₂.≅-∷ (W₂.I∙ m₁ m₂ refl refl e)) (W₂.D∙ m₁ m₂ g' c')
  GSub-cong (W₁.C∙ m₁ m₂ {n} g c p q) =
    let (g' , c' , e) = cart-map c in
    W₂.≅-trans (W₂.≅-∷ (W₂.I∙ m₁ m₂ refl refl e))
    (W₂.≅-trans (W₂.C∙ m₁ m₂ g' c' p q)
    (W₂.≅-trans (W₂.≅-∷ˡ (W₂.I∙ m₁ (suc m₂) refl refl (S₂.≈.sym e)))
                (W₂.≅-∷ (W₂.≅-∷ˡ (W₂.I∙ (m₁ + n) m₂ q p (S₂.≈.sym e))))))

  ----------------------------------------------------------------------
  -- the induced pre-PROP functor Sub_{ℂ₁} → Sub_{ℂ₂}
  ----------------------------------------------------------------------

  GSubFunctor : PrePROPFunctor (P₁.SubPrePROP Cart₁) (P₂.SubPrePROP Cart₂)
  GSubFunctor = record
    { F      = GSub
    ; F-cong = GSub-cong
    ; F-id   = W₂.≅-refl
    ; F-∘    = λ f g → W₂.≅-≡ (GSub-++ g f)
    ; F-⊣    = λ {m} {n} {k} f → W₂.≅-≡ (GSub-⊣ k f)
    ; F-⊢    = λ {m} {n} {k} f → W₂.≅-≡ (GSub-⊢ k f)
    ; F-σ    = W₂.≅-refl
    }
