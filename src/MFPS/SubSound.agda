------------------------------------------------------------------------
-- Theorem 3.16: the congruence of Fig. 3 is sound for pre-substitution
-- application, i.e. Γ ≅ Δ implies f ⋆ Γ ≈ f ⋆ Δ for every f.
--
-- The cartesian rules need, for every operation g satisfying `Cart`,
-- centrality of g and the naturality of discard/copy with respect to
-- g; these are packaged in `CartRules`.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.SubSound (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊
open import MFPS.Sub 𝕊

private
  variable
    j k m n : ℕ

record CartRules (Cart : ∀ {n} → Op n → Set) : Set where
  field
    central : ∀ {n} {g : Op n} → Cart g → Central g
    discard : ∀ {n} {g : Op n} → Cart g → ∀ {m₁ m₂} (f : Op (m₁ + m₂))
      → (f [ idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂} ]) ⟨ m₁ ⊣ g ⊢ m₂ ⟩ ≈ f [ idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂} ]
    copy    : ∀ {n} {g : Op n} → Cart g → ∀ {m₁ m₂} (f : Op (m₁ + suc (suc m₂)))
      (p : m₁ + (n + suc m₂) ≡ (m₁ + n) + suc m₂)
      (q : (m₁ + n) + (n + m₂) ≡ m₁ + ((n + n) + m₂))
      → (f [ idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂} ]) ⟨ m₁ ⊣ g ⊢ m₂ ⟩
        ≈ ((subst Op p (f ⟨ m₁ ⊣ g ⊢ suc m₂ ⟩)) ⟨ m₁ + n ⊣ g ⊢ m₂ ⟩) [ (idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}) ∘ʳ castʳ q ]

-- no operation is cartesian: the purely symmetric congruence
noCart : CartRules (λ _ → ⊥)
noCart = record { central = λ () ; discard = λ () ; copy = λ () }

------------------------------------------------------------------------
-- transport bookkeeping
------------------------------------------------------------------------

private
  subst-cancel : ∀ {m n} (p : m ≡ n) (x : Op m) → subst Op (sym p) (subst Op p x) ≡ x
  subst-cancel refl x = refl

  -- if  subst q x ≈ y  then  subst p x ≈ subst p' y  whenever the arities agree
  move : ∀ {a b c} (p : a ≡ c) (p' : b ≡ c) (q : a ≡ b) {x : Op a} {y : Op b}
    → subst Op q x ≈ y → subst Op p x ≈ subst Op p' y
  move p refl q e rewrite ≡-irrelevant p q = e

  -- subst on the outside of a renaming action
  subst-ren-out : ∀ {a b c} (p : a ≡ b) (x : Op a) (r : Ren b c) → (subst Op p x) [ r ] ≈ x [ r ∘ʳ castʳ p ]
  subst-ren-out p x r = ≈.trans (ren-cong (subst-ren p x) (λ _ → refl)) (≈.sym (ren-∘ x (castʳ p) r))

------------------------------------------------------------------------
-- Theorem 3.16
------------------------------------------------------------------------

module Soundness {Cart : ∀ {n} → Op n → Set} (rules : CartRules Cart) where
  open CartRules rules

  ⋆-sound : {Γ Δ : Word m n} → Cong Cart Γ Δ → (f : Op n) → f ⋆ Γ ≈ f ⋆ Δ
  ⋆-sound ≅-refl f = ≈.refl
  ⋆-sound (≅-sym e) f = ≈.sym (⋆-sound e f)
  ⋆-sound (≅-trans e e') f = ≈.trans (⋆-sound e f) (⋆-sound e' f)
  ⋆-sound (≅-cong {Γ₁ = Γ₁} {Γ₁'} {Γ₂} {Γ₂'} e₁ e₂) f =
    ≈.trans (≈.reflexive (⋆-++ f Γ₁ Γ₂))
    (≈.trans (⋆-cong (⋆-sound e₁ f) Γ₂)
    (≈.trans (⋆-sound e₂ (f ⋆ Γ₁'))
             (≈.reflexive (sym (⋆-++ f Γ₁' Γ₂')))))
  -- administrative
  ⋆-sound (I∙ n₁ n₂ p q e) f = subst-cong (sym p) (sub-cong ≈.refl e)
  ⋆-sound (E∙ e) f = ren-cong ≈.refl e
  ⋆-sound (S∙ n₁ n₂ p q g) f =
    ≈.trans (subst-ren (sym p) _)
            (ren-cong (sub-cong (subst-ren q f) ≈.refl) (λ _ → refl))
  -- symmetric rules
  ⋆-sound (U₁∙ n₁ n₂ p) f =
    ≈.trans (subst-cong (sym p) (runit (subst Op p f))) (≈.reflexive (subst-cancel p f))
  ⋆-sound U₂∙ f = ren-id f
  ⋆-sound (A∙ m₁ m₂ n₁ n₂ {n} g h p₁ q₁ p₂ q₂ p₃) f =
    move (sym p₂) (sym p₃) (trans (sym p₂) p₃)
      (≈.trans (subst-cong (trans (sym p₂) p₃)
                 (sub-cong (≈.reflexive (subst-trans Op (sym p₁) q₂ _)) ≈.refl))
               (assoc (subst Op q₁ f) g h (trans (sym p₁) q₂) (trans (sym p₂) p₃)))
  ⋆-sound (R∙ r₁ r₂) f = ≈.sym (ren-∘ f r₁ r₂)
  ⋆-sound (N∙ v r₁ s r₂) f = ren-sub f v r₁ s r₂
  ⋆-sound (Sℓ∙ m₁ m₂ {n} g p q q') f =
    ≈.trans (σ-natˡ f g q (sym p) q')
    (≈.trans (ren-cong (sub-cong (ren-subst q f) ≈.refl) (λ _ → refl))
             (≈.sym (subst-ren-out (sym p) _ _)))
  ⋆-sound (Sr∙ m₁ m₂ {n} g p q q' q'') f =
    ≈.trans (subst-cong (sym p) (sub-cong (subst-ren q _) ≈.refl))
    (≈.trans (≈.reflexive (subst-irr Op (sym p) _))
             (σ-natʳ f g q q'' q'))
  -- cartesian rules
  ⋆-sound (CEN∙ m₁ m m₂ {n₁} {n₂} g₁ g₂ c p q p' p'' q') f =
    move (sym q) (sym q') (trans (sym q) q')
      (≈.trans (comm m₁ m m₂ f p p' p'' (trans (sym q) q'))
               (sub-cong (≈.reflexive (cong (λ e → subst Op e _) (≡-irrelevant p'' (sym (sym p''))))) ≈.refl))
    where
      comm : Comm g₁ g₂
      comm = [ (λ c₁ → proj₁ (central c₁ g₂)) , (λ c₂ → proj₂ (central c₂ g₁)) ]′ c
  ⋆-sound (D∙ m₁ m₂ g c) f = discard c f
  ⋆-sound (C∙ m₁ m₂ {n} g c p q) f =
    ≈.trans (copy c f p (sym q))
    (≈.trans (ren-∘ _ (castʳ (sym q)) _)
             (ren-cong (ren-subst (sym q) _) (λ _ → refl)))
