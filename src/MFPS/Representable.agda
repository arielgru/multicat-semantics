------------------------------------------------------------------------
-- Corollary 3.17 and Theorem 3.18: the presheaf n ↦ ℂ(n) on Sub_ℂ is
-- representable by 1.
--
-- The unit of the representation sends v ∈ ℂ(n) to the singleton word
-- {0 ⊣ v ⊢ 0} : n → 1; the counit sends Γ : n → 1 to id ⋆ Γ.
--
-- NOTE (paper issue): the proof of Thm. 3.18(i) says "by induction on
-- Γ we get ({0 ⊣ id ⋆ Γ ⊢ 0}) ≅ Γ".  That statement is not provable by
-- a direct induction (the tail of Γ is not a word into 1); the
-- inductive statement is the naturality  {f ⋆ Γ} ≅ {f} ∘ Γ  for all f,
-- proved below as `η-nat`.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.Representable (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊
open import MFPS.Sub 𝕊
open import MFPS.SubSound 𝕊

private
  variable
    k m n : ℕ

------------------------------------------------------------------------
-- Administrative facts about steps
------------------------------------------------------------------------

ins-irr : ∀ n₁ n₂ {m k k'} (p p' : k ≡ n₁ + (m + n₂)) (q q' : k' ≡ n₁ + suc n₂) (g : Op m)
  → ins n₁ n₂ p q g ≡ ins n₁ n₂ p' q' g
ins-irr n₁ n₂ p p' q q' g rewrite ≡-irrelevant p p' | ≡-irrelevant q q' = refl

-- a step is invariant under transporting its operation
ins-subst : ∀ {Cart : ∀ {n} → Op n → Set} n₁ n₂ {m m' k k'} (e : m ≡ m')
  (p : k ≡ n₁ + (m + n₂)) (p' : k ≡ n₁ + (m' + n₂)) (q : k' ≡ n₁ + suc n₂) (g : Op m)
  → Cong Cart ⟦ ins n₁ n₂ p q g ⟧ ⟦ ins n₁ n₂ p' q (subst Op e g) ⟧
ins-subst n₁ n₂ refl p p' q g = ≅-≡ (cong ⟦_⟧ (ins-irr n₁ n₂ p p' q q g))

-- a step is invariant under rewriting its position arities
ins-arity : ∀ {Cart : ∀ {n} → Op n → Set} {n₁ n₁' n₂ n₂' m k k'} (e₁ : n₁ ≡ n₁') (e₂ : n₂ ≡ n₂')
  (p : k ≡ n₁ + (m + n₂)) (p' : k ≡ n₁' + (m + n₂')) (q : k' ≡ n₁ + suc n₂) (q' : k' ≡ n₁' + suc n₂') (g : Op m)
  → Cong Cart ⟦ ins n₁ n₂ p q g ⟧ ⟦ ins n₁' n₂' p' q' g ⟧
ins-arity {n₁ = n₁} {n₂ = n₂} refl refl p p' q q' g = ≅-≡ (cong ⟦_⟧ (ins-irr n₁ n₂ p p' q q' g))

------------------------------------------------------------------------
-- The representation
------------------------------------------------------------------------

-- unit:  v ↦ {0 ⊣ v ⊢ 0}
ηʷ : Op n → Word n 1
ηʷ {n} v = ⟦ ins 0 0 (sym (+-identityʳ n)) refl v ⟧

-- counit:  Γ ↦ id ⋆ Γ
εʷ : Word n 1 → Op n
εʷ Γ = idₒ ⋆ Γ

module _ {Cart : ∀ {n} → Op n → Set} where

  η-cong : {v w : Op n} → v ≈ w → Cong Cart (ηʷ v) (ηʷ w)
  η-cong e = I∙ 0 0 _ _ e

  -- {f[r]} ≅ {f} ∘ [r]
  η-ren : (f : Op n) (r : Ren n m) → Cong Cart (ηʷ (f [ r ])) (ηʷ f ++ ⟦ rn r ⟧)
  η-ren {n} {m} f r =
    ≅-trans (S∙ 0 0 pₘ refl (f [ r ]))                                    -- c₀ ∷ {f[r]} ∷ cₘ
    (≅-trans (≅-∷ (≅-cong {Γ₁ = ε} (≅-sym id-step) ≅-refl))              -- c₀ ∷ [id] ∷ {f[r]} ∷ cₘ
    (≅-trans (≅-∷ (≅-cong (≅-sym (N∙ f (idʳ {0}) r (idʳ {0}))) ≅-refl))  -- c₀ ∷ {f} ∷ [id₀+r+id₀] ∷ cₘ
    (≅-trans (≅-∷ (≅-∷ (R∙ _ _)))                                        -- c₀ ∷ {f} ∷ [cₘ ∘ (id₀+r+id₀)]
    (≅-trans (≅-∷ (≅-∷ (E∙ (+ʳ-zero r (sym pₙ) (sym pₘ)))))              -- c₀ ∷ {f} ∷ [r ∘ cₙ]
    (≅-trans (≅-∷ (≅-∷ (≅-sym (R∙ _ r))))                                -- c₀ ∷ {f} ∷ cₙ ∷ [r]
             (≅-cong (≅-sym (S∙ 0 0 pₙ refl f)) ≅-refl))))))             -- {f} ∷ [r]
    where
      pₙ : n ≡ 0 + (n + 0)
      pₙ = sym (+-identityʳ n)
      pₘ : m ≡ 0 + (m + 0)
      pₘ = sym (+-identityʳ m)
      id-step : Cong Cart ⟦ rn (idʳ {0} +ʳ idʳ {1} +ʳ idʳ {0}) ⟧ ε
      id-step = ≅-trans (E∙ (λ i → trans (+ʳ-cong {r = idʳ {0}} (λ _ → refl) (+ʳ-id 1 0) i) (+ʳ-id 0 1 i))) U₂∙

  -- {f ⋆ s} ≅ {f} ∘ s   for a substitution step
  η-ins : (f : Op n) (s : Step m n) → Cong Cart (ηʷ (f ⋆₁ s)) (ηʷ f ++ ⟦ s ⟧)
  η-ins f (rn r) = η-ren f r
  η-ins {n} {m} f (ins n₁ n₂ {m'} p q g) =
    ≅-trans (≅-sym (ins-subst 0 0 (sym p) P₃ (sym (+-identityʳ m)) refl X))
    (≅-trans (≅-sym (A∙ 0 0 n₁ n₂ (subst Op q f) g p₁ refl p₂ q₂ P₃))
             (≅-cong (≅-sym (ins-subst 0 0 q (sym (+-identityʳ n)) p₁ refl f))
                     (ins-arity refl (+-identityʳ n₂) p₂ p q₂ q g)))
    where
      X : Op (n₁ + (m' + n₂))
      X = (subst Op q f) ⟨ n₁ ⊣ g ⊢ n₂ ⟩
      P₃ : m ≡ 0 + ((n₁ + (m' + n₂)) + 0)
      P₃ = trans p (sym (+-identityʳ _))
      p₁ : n ≡ 0 + ((n₁ + suc n₂) + 0)
      p₁ = trans q (sym (+-identityʳ _))
      q₂ : n ≡ (0 + n₁) + suc (n₂ + 0)
      q₂ = trans q (cong (λ z → n₁ + suc z) (sym (+-identityʳ n₂)))
      p₂ : m ≡ (0 + n₁) + (m' + (n₂ + 0))
      p₂ = trans p (cong (λ z → n₁ + (m' + z)) (sym (+-identityʳ n₂)))

  -- naturality of the unit:  {f ⋆ Γ} ≅ {f} ∘ Γ
  η-nat : (f : Op n) (Γ : Word m n) → Cong Cart (ηʷ (f ⋆ Γ)) (ηʷ f ++ Γ)
  η-nat f ε       = ≅-≡ (sym (++-identityʳ _))
  η-nat f (s ∷ Γ) =
    ≅-trans (η-nat (f ⋆₁ s) Γ)
    (≅-trans (≅-cong (η-ins f s) ≅-refl)
             (≅-≡ (++-assoc (ηʷ f) ⟦ s ⟧ Γ)))

  -- {id} ≅ ε
  η-id : Cong Cart (ηʷ idₒ) ε
  η-id = ≅-trans (≅-≡ (cong ⟦_⟧ (ins-irr 0 0 _ refl refl refl idₒ))) (U₁∙ 0 0 refl)

  -- Theorem 3.18: the two composites
  η∘ε : (Γ : Word n 1) → Cong Cart (ηʷ (εʷ Γ)) Γ
  η∘ε Γ = ≅-trans (η-nat idₒ Γ) (≅-cong η-id ≅-refl)

ε∘η : (v : Op n) → εʷ (ηʷ v) ≈ v
ε∘η {n} v = ≈[]-irr {p = +-identityʳ n} {p' = sym (sym (+-identityʳ n))} {x = idₒ ⟨ 0 ⊣ v ⊢ 0 ⟩} (lunit v (+-identityʳ n))

module _ {Cart : ∀ {n} → Op n → Set} (rules : CartRules Cart) where
  open Soundness rules

  ε-cong : {Γ Δ : Word n 1} → Cong Cart Γ Δ → εʷ Γ ≈ εʷ Δ
  ε-cong e = ⋆-sound e idₒ

  -- Corollary 3.17: ⋆ is a contravariant action (identity and composition)
  ⋆-id : (f : Op n) → f ⋆ ε ≡ f
  ⋆-id f = refl

  ⋆-comp : (f : Op n) (Γ₁ : Word k n) (Γ₂ : Word m k) → f ⋆ (Γ₁ ++ Γ₂) ≡ (f ⋆ Γ₁) ⋆ Γ₂
  ⋆-comp = ⋆-++
