------------------------------------------------------------------------
-- Proposition 3.14(i): for a symmetric Ren-cartesian preoperad ℂ, the
-- substitution category Sub_ℂ is a pre-PROP (Def. 2.6).
--
-- This module assembles the record `PrePROP` from the pieces proved in
-- the Sub* modules:
--
--   * category structure: composition is concatenation of words and
--     the identity is the empty word; the laws hold on the nose (here);
--   * whiskering k ⊣ (−), (−) ⊢ k is defined step-wise and is
--     functorial on the nose (here); it respects the congruence of
--     Fig. 3 — "each generating rule is stable under whiskering" —
--     MFPS.SubWhisker (`⊣-stable`, `⊢-stable`);
--   * the strictness laws of the premonoidal structure (0 ⊣ Γ = Γ,
--     Γ ⊢ 0 = Γ, k ⊣ j ⊣ Γ = (k+j) ⊣ Γ, …) — MFPS.SubStrict;
--   * the symmetry σ_{m,n} := [σ_{m,n}] with its involution, unit and
--     hexagon laws, and its naturality against words — MFPS.SubSym;
--   * centrality of the symmetry — MFPS.SubCentral (`central-rn`).
--
-- The instance is parametrised by the predicate `Cart` selecting which
-- substitution steps are subject to the cartesian rules, so it covers
-- Sub_ℂ (Cart = ⊥), Sub×_𝕍 (Cart = ⊤) and the corrected Sub_ℂ of a
-- Freyd operad (Cart = J-image) uniformly.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.SubPROP (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊
open import MFPS.Sub 𝕊
open import MFPS.SubCast 𝕊 using (subst₂W; subst₂W-≡)
open import MFPS.SubWhisker 𝕊 using (⊣-stable; ⊢-stable)
open import MFPS.SubStrict 𝕊 using (⊢-0ʷ; ⊣-⊣ʷ; ⊢-⊢ʷ; ⊣-⊢ʷ)
open import MFPS.SubSym 𝕊 using (σʷ; σʷ-σʷ; σʷ-0ˡ; σʷ-0ʳ; σʷ-hexˡ; σʷ-hexʳ; natL; natR)
open import MFPS.SubCentral 𝕊 using (central-rn)
open import MFPS.PROP using (PrePROP)

private
  variable
    j k m n : ℕ

module _ (Cart : ∀ {n} → Op n → Set) where

  ----------------------------------------------------------------------
  -- category structure: concatenation and the empty word
  ----------------------------------------------------------------------

  ∘-assoc : (Γ₁ : Word k n) (Γ₂ : Word j k) (Γ₃ : Word m j) → Cong Cart ((Γ₁ ++ Γ₂) ++ Γ₃) (Γ₁ ++ (Γ₂ ++ Γ₃))
  ∘-assoc Γ₁ Γ₂ Γ₃ = ≅-≡ (++-assoc Γ₁ Γ₂ Γ₃)

  ∘-idˡ : (Γ : Word m n) → Cong Cart (ε ++ Γ) Γ
  ∘-idˡ Γ = ≅-refl

  ∘-idʳ : (Γ : Word m n) → Cong Cart (Γ ++ ε) Γ
  ∘-idʳ Γ = ≅-≡ (++-identityʳ Γ)

  ----------------------------------------------------------------------
  -- whiskering is functorial on the nose; 0 ⊣ Γ = Γ up to the
  -- administrative rules (arity proofs of steps, (E) for renamings)
  ----------------------------------------------------------------------

  0⊣ʷ : (Γ : Word m n) → Cong Cart (0 ⊣ʷ Γ) Γ
  0⊣ʷ ε = ≅-refl
  0⊣ʷ (ins n₁ n₂ p q g ∷ Γ) = ≅-cong (≅-≡ (cong ⟦_⟧ (ins-irr' p q g))) (0⊣ʷ Γ)
    where
      ins-irr' : ∀ {m k k'} (p : k ≡ n₁ + (m + n₂)) (q : k' ≡ n₁ + suc n₂) (g : Op m)
        → ins (0 + n₁) n₂ (Lp 0 n₁ p) (Lp 0 n₁ q) g ≡ ins n₁ n₂ p q g
      ins-irr' p q g rewrite ≡-irrelevant (Lp 0 n₁ p) p | ≡-irrelevant (Lp 0 n₁ q) q = refl
  0⊣ʷ (rn r ∷ Γ) = ≅-cong (E∙ {r = idʳ {0} +ʳ r} (λ _ → refl)) (0⊣ʷ Γ)

  ----------------------------------------------------------------------
  -- Proposition 3.14(i): the pre-PROP Sub_ℂ
  ----------------------------------------------------------------------

  -- the fields whose statements involve arity casts, with the transport
  -- of the record (`subst₂`) bridged to `subst₂W`
  private
    ⊢-0' : ∀ {m n} (f : Word m n) (p : m + 0 ≡ m) (q : n + 0 ≡ n)
      → Cong Cart (MFPS.PROP.subst₂ Word p q (f ⊢ʷ 0)) f
    ⊢-0' f p q = ≅-trans (≅-≡ (subst₂W-≡ p q _)) (⊢-0ʷ f p q)

    ⊣-⊣' : ∀ {m n k j} (f : Word m n) (p : k + (j + m) ≡ (k + j) + m) (q : k + (j + n) ≡ (k + j) + n)
      → Cong Cart (MFPS.PROP.subst₂ Word p q (k ⊣ʷ (j ⊣ʷ f))) ((k + j) ⊣ʷ f)
    ⊣-⊣' {k = k} {j} f p q = ≅-trans (≅-≡ (subst₂W-≡ p q _)) (⊣-⊣ʷ k j f p q)

    ⊢-⊢' : ∀ {m n j k} (f : Word m n) (p : (m + j) + k ≡ m + (j + k)) (q : (n + j) + k ≡ n + (j + k))
      → Cong Cart (MFPS.PROP.subst₂ Word p q ((f ⊢ʷ j) ⊢ʷ k)) (f ⊢ʷ (j + k))
    ⊢-⊢' {j = j} {k} f p q = ≅-trans (≅-≡ (subst₂W-≡ p q _)) (⊢-⊢ʷ j k f p q)

    ⊣-⊢' : ∀ {m n k j} (f : Word m n) (p : (k + m) + j ≡ k + (m + j)) (q : (k + n) + j ≡ k + (n + j))
      → Cong Cart (MFPS.PROP.subst₂ Word p q ((k ⊣ʷ f) ⊢ʷ j)) (k ⊣ʷ (f ⊢ʷ j))
    ⊣-⊢' {k = k} {j} f p q = ≅-trans (≅-≡ (subst₂W-≡ p q _)) (⊣-⊢ʷ k j f p q)

    σ-0ˡ' : ∀ {m} (p : m + 0 ≡ m) → Cong Cart (MFPS.PROP.subst₂ Word p refl (σʷ m 0)) ε
    σ-0ˡ' {m} p = ≅-trans (≅-≡ (subst₂W-≡ p refl _)) (σʷ-0ˡ m p)

    σ-0ʳ' : ∀ {m} (p : m + 0 ≡ m) → Cong Cart (MFPS.PROP.subst₂ Word refl p (σʷ 0 m)) ε
    σ-0ʳ' {m} p = ≅-trans (≅-≡ (subst₂W-≡ refl p _)) (σʷ-0ʳ m p)

  SubPrePROP : PrePROP
  SubPrePROP = record
    { Hom     = Word
    ; _≈_     = Cong Cart
    ; ≈-equiv = ≅-equiv
    ; idₕ     = ε
    ; _∘_     = _++_
    ; _⊣_     = _⊣ʷ_
    ; _⊢_     = _⊢ʷ_
    ; σ       = σʷ
    ; ∘-cong  = ≅-cong
    ; ∘-assoc = λ f g h → ∘-assoc h g f
    ; ∘-idˡ   = ∘-idˡ
    ; ∘-idʳ   = ∘-idʳ
    ; ⊣-cong  = λ {m} {n} {k} → ⊣-stable k
    ; ⊢-cong  = λ {m} {n} {k} → ⊢-stable k
    ; ⊣-id    = ≅-refl
    ; ⊢-id    = ≅-refl
    ; ⊣-∘     = λ {m} {n} {j} {k} f g → ≅-≡ (⊣ʷ-++ k g f)
    ; ⊢-∘     = λ {m} {n} {j} {k} f g → ≅-≡ (⊢ʷ-++ g f k)
    ; 0-⊣     = 0⊣ʷ
    ; ⊢-0     = ⊢-0'
    ; ⊣-⊣     = ⊣-⊣'
    ; ⊢-⊢     = ⊢-⊢'
    ; ⊣-⊢     = ⊣-⊢'
    ; σ-σ     = λ {n} {m} → σʷ-σʷ m n
    ; σ-nat₁ˡ = natL
    ; σ-nat₁ʳ = natR
    ; σ-central = λ {m} {n} → central-rn (σʳ n m)
    ; σ-0ˡ    = σ-0ˡ'
    ; σ-0ʳ    = σ-0ʳ'
    ; σ-hexˡ  = λ m n k p q q' → ≅-trans (≅-≡ (subst₂W-≡ p refl _)) (σʷ-hexˡ m n k p q q')
    ; σ-hexʳ  = λ m n k p q q' → ≅-trans (≅-≡ (subst₂W-≡ p refl _)) (σʷ-hexʳ m n k p q q')
    }

  ----------------------------------------------------------------------
  -- Remark: the comonoid laws for [Δₙ], [!ₙ] are inherited from Renᵒᵖ
  -- (Prop. 3.14(ii), "the comonoid laws are inherited from Renᵒᵖ");
  -- in the record `CartesianPROP` they are not axioms, since Δ and !
  -- are *defined* as the images of Δʳ, !ʳ under ρ.
  ----------------------------------------------------------------------

  Δʷ : ∀ n → Word n (n + n)
  Δʷ n = ⟦ rn (Δʳ n) ⟧

  !ʷ : ∀ n → Word n 0
  !ʷ n = ⟦ rn (!ʳ n) ⟧

  Δʷ-counitˡ : ∀ n → Cong Cart ((!ʷ n ⊢ʷ n) ++ Δʷ n) ε
  Δʷ-counitˡ n = ≅-trans (R∙ _ _) (≅-trans (E∙ lemma) U₂∙)
    where
      lemma : (Δʳ n ∘ʳ (!ʳ n +ʳ idʳ {n})) ≗ idʳ
      lemma i = trans (cong (Δʳ n) (+ʳ-inj₂ (!ʳ n) idʳ i)) ([,]ʳ-inr idʳ idʳ i)

  Δʷ-cocomm : ∀ n → Cong Cart (σʷ n n ++ Δʷ n) (Δʷ n)
  Δʷ-cocomm n = ≅-trans (R∙ _ _) (E∙ lemma)
    where
      lemma : (Δʳ n ∘ʳ σʳ n n) ≗ Δʳ n
      lemma = Fin+-ext (λ j → trans (cong (Δʳ n) (σʳ-inl n n j)) (trans ([,]ʳ-inr idʳ idʳ j) (sym ([,]ʳ-inl idʳ idʳ j))))
                       (λ j → trans (cong (Δʳ n) (σʳ-inr n n j)) (trans ([,]ʳ-inl idʳ idʳ j) (sym ([,]ʳ-inr idʳ idʳ j))))
