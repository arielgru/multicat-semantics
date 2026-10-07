------------------------------------------------------------------------
-- Word-level cast calculus for the substitution categories.
--
-- Supporting lemmas for Prop. 3.14: how the administrative rules
-- (E), (R), (S), (U₂) of Fig. 3 let cast-like renaming steps be moved,
-- merged and absorbed into substitution steps.  Everything here holds
-- for an arbitrary predicate `Cart` (no cartesian rule is used).
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.SubCast (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊
open import MFPS.Sub 𝕊
import MFPS.PROP
open import MFPS.Representable 𝕊 using (ins-irr; ins-subst; ins-arity) public

private
  variable
    j k m n a b c : ℕ

module _ {Cart : ∀ {n} → Op n → Set} where

  -- a cast-like endo-renaming step is the identity word
  rn-isCast : {r : Ren n n} → IsCast r → Cong Cart ⟦ rn r ⟧ ε
  rn-isCast h = ≅-trans (E∙ (isCast-id h)) U₂∙

  -- two cast-like renaming steps of the same type are equal
  rn-isCast-unique : {r s : Ren n m} → IsCast r → IsCast s → Cong Cart ⟦ rn r ⟧ ⟦ rn s ⟧
  rn-isCast-unique hr hs = E∙ (isCast-unique hr hs)

  -- merging two renaming steps in context
  rn-rn : (r₁ : Ren n k) (r₂ : Ren k m) {Γ : Word j m}
    → Cong Cart (rn r₁ ∷ rn r₂ ∷ Γ) (rn (r₂ ∘ʳ r₁) ∷ Γ)
  rn-rn r₁ r₂ = ≅-cong (R∙ r₁ r₂) ≅-refl

  -- rewriting a renaming step by a pointwise equation, in context
  rn-by : {r r' : Ren n m} → r ≗ r' → {Γ : Word j m} → Cong Cart (rn r ∷ Γ) (rn r' ∷ Γ)
  rn-by e = ≅-∷ˡ (E∙ e)

  -- two cast-like prefixes of the same renaming are interchangeable
  rn-prefix : {Z : Ren n a} (C C' : Ren a m) → IsCast C → IsCast C' → {Γ : Word j m}
    → Cong Cart (rn (C ∘ʳ Z) ∷ Γ) (rn (C' ∘ʳ Z) ∷ Γ)
  rn-prefix {Z = Z} C C' hC hC' = ≅-∷ˡ (E∙ (λ i → isCast-unique hC hC' (Z i)))

  -- a renaming that factors as c₂ ∘ X ∘ c₁, as three steps (c₁ applied first)
  rn-conj : {r : Ren n m} {c₁ : Ren n a} {X : Ren a b} {c₂ : Ren b m}
    → r ≗ (c₂ ∘ʳ X ∘ʳ c₁) → {Γ : Word j m}
    → Cong Cart (rn r ∷ Γ) (rn c₁ ∷ rn X ∷ rn c₂ ∷ Γ)
  rn-conj {c₁ = c₁} {X} {c₂} e = ≅-trans (≅-∷ˡ (E∙ e)) (≅-sym (≅-trans (rn-rn c₁ X) (rn-rn (X ∘ʳ c₁) c₂)))

  -- a substitution step conjugated by cast-like renamings is a substitution step
  ins-conj : ∀ n₁ n₂ {m k k' a b} {c : Ren b k'} {c' : Ren k a}
    (p : k ≡ n₁ + (m + n₂)) (q : k' ≡ n₁ + suc n₂) (p' : a ≡ n₁ + (m + n₂)) (q' : b ≡ n₁ + suc n₂)
    (g : Op m) → IsCast c → IsCast c'
    → Cong Cart (rn c ∷ ins n₁ n₂ p q g ∷ ⟦ rn c' ⟧) ⟦ ins n₁ n₂ p' q' g ⟧
  ins-conj n₁ n₂ {c = c} {c'} p q p' q' g hc hc' =
    ≅-trans (≅-∷ (≅-cong (S∙ n₁ n₂ p q g) ≅-refl))
    (≅-trans (rn-rn _ _)
    (≅-trans (≅-∷ (≅-∷ (R∙ _ _)))
    (≅-trans (≅-∷ˡ (rn-isCast-unique (∘ʳ-isCast (castʳ-isCast q) hc) (castʳ-isCast q')))
    (≅-trans (≅-∷ (≅-∷ (rn-isCast-unique (∘ʳ-isCast hc' (castʳ-isCast (sym p))) (castʳ-isCast (sym p')))))
             (≅-sym (S∙ n₁ n₂ p' q' g))))))

  -- one-sided versions
  ins-conjˡ : ∀ n₁ n₂ {m k k' b} {c : Ren b k'}
    (p : k ≡ n₁ + (m + n₂)) (q : k' ≡ n₁ + suc n₂) (q' : b ≡ n₁ + suc n₂)
    (g : Op m) → IsCast c
    → Cong Cart (rn c ∷ ⟦ ins n₁ n₂ p q g ⟧) ⟦ ins n₁ n₂ p q' g ⟧
  ins-conjˡ n₁ n₂ {k = k} p q q' g hc =
    ≅-trans (≅-∷ (≅-∷ (≅-sym (U₂∙ {n = k}))))
            (ins-conj n₁ n₂ p q p q' g hc idʳ-isCast)

  ins-conjʳ : ∀ n₁ n₂ {m k k' a} {c' : Ren k a}
    (p : k ≡ n₁ + (m + n₂)) (q : k' ≡ n₁ + suc n₂) (p' : a ≡ n₁ + (m + n₂))
    (g : Op m) → IsCast c'
    → Cong Cart (ins n₁ n₂ p q g ∷ ⟦ rn c' ⟧) ⟦ ins n₁ n₂ p' q g ⟧
  ins-conjʳ n₁ n₂ {k' = k'} p q p' g hc' =
    ≅-trans (≅-cong {Γ₁ = ε} (≅-sym (U₂∙ {n = k'})) ≅-refl)
            (ins-conj n₁ n₂ p q p' q g idʳ-isCast hc')

-- transport of a word along arity equations
subst₂W : m ≡ a → n ≡ b → Word m n → Word a b
subst₂W refl refl Γ = Γ

module _ {Cart : ∀ {n} → Op n → Set} where
  -- … is conjugation by casts
  subst₂-Word : (p : m ≡ a) (q : n ≡ b) (Γ : Word m n)
    → Cong Cart (subst₂W p q Γ) (rn (castʳ (sym q)) ∷ (Γ ++ ⟦ rn (castʳ p) ⟧))
  subst₂-Word refl refl Γ =
    ≅-trans (≅-≡ (sym (++-identityʳ Γ)))
    (≅-trans (≅-cong {Γ₁ = Γ} ≅-refl (≅-sym (rn-isCast (castʳ-isCast refl))))
             (≅-cong {Γ₁ = ε} (≅-sym (rn-isCast (castʳ-isCast refl))) ≅-refl))

-- the record PrePROP transports along arity equations with the
-- standard-library `subst₂`; it agrees with `subst₂W` on the nose
subst₂W-≡ : (p : m ≡ a) (q : n ≡ b) (Γ : Word m n) → MFPS.PROP.subst₂ Word p q Γ ≡ subst₂W p q Γ
subst₂W-≡ refl refl Γ = refl
