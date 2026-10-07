------------------------------------------------------------------------
-- Definition A.5 (uncurrying) and Lemmas A.6, A.7: interpreting words
-- of Sub_ℂ in a pre-PROP D.
--
-- Given an interpretation of the generators, G : ℂ(n) → D(n ⇒ 1), that
-- preserves identities, substitution and renaming (the data of a
-- preoperad functor ℂ → U(D)), a word is interpreted by
--   ⌊ε⌋ = id,   ⌊{n₁ ⊣ g ⊢ n₂}, Γ⌋ = (n₁ ⊣ (G g ⊢ n₂)) ∘ ⌊Γ⌋,   ⌊[r], Γ⌋ = R r ∘ ⌊Γ⌋
-- (with the arity casts carried by the steps interpreted as cast
-- morphisms).
--
-- Proof in words.
--  * Lemma A.6: ⌊Γ₁ ++ Γ₂⌋ = ⌊Γ₁⌋ ∘ ⌊Γ₂⌋ by induction on Γ₁ (`⌊⌋-++`);
--    ⌊−⌋ commutes with whiskering because whiskering is functorial and
--    strict in D (`⌊⌋-⊣`, `⌊⌋-⊢`).
--  * Lemma A.7: every rule of Fig. 3 (and the administrative rules
--    (I),(E),(S)) is validated by D.  After removing the casts, each
--    rule is exactly one of the identities `core-…` of MFPS.PROPHet
--    ((A) `core-assoc`, (U₁) `core-runit`, (N) `core-N`, (Sℓ)/(Sr)
--    `core-Sℓ`/`core-Sr`, (CEN) `core-CEN`, (D) `core-D`, (C)
--    `core-C`), instantiated at the generators, with G's preservation
--    laws used to rewrite G of a substituted or renamed generator;
--    (U₂),(R) are the functoriality of R and (I),(E),(S) are
--    congruence and the cast lemmas.  The cartesian rules need the
--    interpreted step to be central, discardable and copyable, which
--    is supplied as a hypothesis on `Cart` (`CartInterp`).
--  * Def. A.3 / Lemma A.10 (second item): currying a functor is
--    restriction to the singleton words {0 ⊣ g ⊢ 0}, and currying the
--    uncurried G gives G back (`curry∘uncurry`).
-- Corollary A.9 (the uncurried functor is a Freyd PROP functor) and the
-- first item of Lemma A.10 are in MFPS.FreydAdjunction.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude hiding (_∘_; id)
open import MFPS.Preoperad
open import MFPS.PROP

module MFPS.Uncurry (𝕊 : SymPreoperad) (D : PrePROP) where

open SymPreoperad 𝕊 renaming (_≈_ to _≈ˢ_; Central to Centralˢ; module ≈ to ≈ˢ; setoid to setoidˢ; ≈-equiv to ≈-equivˢ)
open import MFPS.Sub 𝕊
open import MFPS.SubPROP 𝕊 using (SubPrePROP)
open import MFPS.Representable 𝕊 using (ηʷ)
open PrePROP D
open import MFPS.PROPHet D

private
  variable
    j k m n : ℕ

------------------------------------------------------------------------
-- an interpretation of the generators: the data of a functor ℂ → U(D)
------------------------------------------------------------------------

record Interp : Set where
  field
    A      : RenAction
  open RenAction A public
  field
    G      : Op n → Hom n 1
    G-cong : {f g : Op n} → f ≈ˢ g → G f ≈ G g
    G-id   : G idₒ ≈ idₕ
    G-sub  : ∀ {n₁ n₂ m} (f : Op (n₁ + suc n₂)) (g : Op m) → G (f ⟨ n₁ ⊣ g ⊢ n₂ ⟩) ≈ G f ∘ (n₁ ⊣ (G g ⊢ n₂))
    G-ren  : (f : Op m) (r : Ren m n) → G (f [ r ]) ≈ G f ∘ R r

module Uncurry (I : Interp) where
  open Interp I
  open WithR A

  -- Definition A.5
  ⌊_⌋₁ : Step m n → Hom m n
  ⌊ ins n₁ n₂ p q g ⌋₁ = castₕ (sym q) ∘ (n₁ ⊣ (G g ⊢ n₂)) ∘ castₕ p
  ⌊ rn r ⌋₁           = R r

  ⌊_⌋ : Word m n → Hom m n
  ⌊ ε ⌋     = idₕ
  ⌊ s ∷ Γ ⌋ = ⌊ s ⌋₁ ∘ ⌊ Γ ⌋

  -- Lemma A.6
  ⌊⌋-++ : (Γ₁ : Word k n) (Γ₂ : Word m k) → ⌊ Γ₁ ++ Γ₂ ⌋ ≈ ⌊ Γ₁ ⌋ ∘ ⌊ Γ₂ ⌋
  ⌊⌋-++ ε        Γ₂ = ≈.sym (∘-idˡ _)
  ⌊⌋-++ (s ∷ Γ₁) Γ₂ = ≈.trans (∘-cong ≈.refl (⌊⌋-++ Γ₁ Γ₂)) (≈.sym (∘-assoc _ _ _))

  ⌊⟦⟧⌋ : (s : Step m n) → ⌊ ⟦ s ⟧ ⌋ ≈ ⌊ s ⌋₁
  ⌊⟦⟧⌋ s = ∘-idʳ _

  -- a substitution step, up to casts
  ⌊ins⌋≋ : ∀ n₁ n₂ {m k k'} (p : k ≡ n₁ + (m + n₂)) (q : k' ≡ n₁ + suc n₂) (g : Op m)
    → ⌊ ins n₁ n₂ p q g ⌋₁ ≋ (n₁ ⊣ (G g ⊢ n₂))
  ⌊ins⌋≋ n₁ n₂ p q g = ≋-∘ (≋-castₕ (sym q)) (≋-∘ ≋-refl (≋-castₕ' p)) ⟫ ≋-idˡ _ ⟫ ≋-idʳ _

  -- whiskering is preserved
  ⌊⌋₁-⊣ : ∀ k (s : Step m n) → ⌊ k ⊣ₛ s ⌋₁ ≈ k ⊣ ⌊ s ⌋₁
  ⌊⌋₁-⊣ k (rn r) =
    ≈.trans (R-+ idʳ r) (≈.trans (∘-cong (≈.trans (⊢-cong R-id) ⊢-id) ≈.refl) (∘-idˡ _))
  ⌊⌋₁-⊣ k (ins n₁ n₂ p q g) = ≋→≈
    ( ⌊ins⌋≋ (k + n₁) n₂ _ _ g
    ⟫ ≋-sym (≋-⊣⊣ k n₁ _)
    ⟫ ≋-⊣ (≋-sym (⌊ins⌋≋ n₁ n₂ p q g)) )

  ⌊⌋₁-⊢ : ∀ k (s : Step m n) → ⌊ s ⊢ₛ k ⌋₁ ≈ ⌊ s ⌋₁ ⊢ k
  ⌊⌋₁-⊢ k (rn r) =
    ≈.trans (R-+ r idʳ) (≈.trans (∘-cong ≈.refl (≈.trans (⊣-cong R-id) ⊣-id)) (∘-idʳ _))
  ⌊⌋₁-⊢ k (ins n₁ n₂ p q g) = ≋→≈
    ( ⌊ins⌋≋ n₁ (n₂ + k) _ _ g
    ⟫ ≋-⊣ (≋-sym (≋-⊢⊢ n₂ k _))
    ⟫ ≋-sym (≋-⊣⊢ n₁ k _)
    ⟫ ≋-⊢ (≋-sym (⌊ins⌋≋ n₁ n₂ p q g)) )

  ⌊⌋-⊣ : ∀ k (Γ : Word m n) → ⌊ k ⊣ʷ Γ ⌋ ≈ k ⊣ ⌊ Γ ⌋
  ⌊⌋-⊣ k ε       = ≈.sym ⊣-id
  ⌊⌋-⊣ k (s ∷ Γ) = ≈.trans (∘-cong (⌊⌋₁-⊣ k s) (⌊⌋-⊣ k Γ)) (≈.sym (⊣-∘ _ _))

  ⌊⌋-⊢ : ∀ k (Γ : Word m n) → ⌊ Γ ⊢ʷ k ⌋ ≈ ⌊ Γ ⌋ ⊢ k
  ⌊⌋-⊢ k ε       = ≈.sym ⊢-id
  ⌊⌋-⊢ k (s ∷ Γ) = ≈.trans (∘-cong (⌊⌋₁-⊢ k s) (⌊⌋-⊢ k Γ)) (≈.sym (⊢-∘ _ _))

  -- Definition A.3 (currying) and Lemma A.10, second item
  ⌈_⌉ : (∀ {m n} → Word m n → Hom m n) → ∀ {n} → Op n → Hom n 1
  ⌈ F ⌉ g = F (ηʷ g)

  curry∘uncurry : (g : Op n) → ⌈ ⌊_⌋ ⌉ g ≈ G g
  curry∘uncurry {n} g = ≋→≈ (≋-idʳ _ ⟫ ⌊ins⌋≋ 0 0 _ _ g ⟫ ≋-0⊣ _ ⟫ ≋-⊢0 _)

------------------------------------------------------------------------
-- Lemma A.7: the interpretation respects the congruence of Fig. 3
------------------------------------------------------------------------

-- what is needed of the interpreted cartesian steps
record CartInterp (I : Interp) (Cart : ∀ {n} → Op n → Set) : Set where
  open Interp I
  field
    cart-central : {g : Op n} → Cart g → Central (G g)
    cart-!       : {g : Op n} → Cart g → R (!ʳ 1) ∘ G g ≈ R (!ʳ n)
    cart-Δ       : {g : Op n} → Cart g → R (Δʳ 1) ∘ G g ≈ ((G g ⊢ 1) ∘ (n ⊣ G g)) ∘ R (Δʳ n)

module Sound (I : Interp) {Cart : ∀ {n} → Op n → Set} (CI : CartInterp I Cart) where
  open Interp I
  open WithR A
  open Uncurry I public
  open CartInterp CI

  private
    -- the on-the-nose substitution step
    ⌊sub!⌋₁ : ∀ n₁ n₂ {m} (g : Op m) → ⌊ sub! n₁ n₂ g ⌋₁ ≈ n₁ ⊣ (G g ⊢ n₂)
    ⌊sub!⌋₁ n₁ n₂ g = ≈.trans (∘-idˡ _) (∘-idʳ _)

    -- two consecutive substitution steps, up to the outer casts: the
    -- middle casts survive as one cast composition
    ⌊ins∷ins⌋ : ∀ n₁ n₂ {m k k'} (p : k ≡ n₁ + (m + n₂)) (q : k' ≡ n₁ + suc n₂) (g : Op m)
      → ∀ n₁' n₂' {m' k''} (p' : k'' ≡ n₁' + (m' + n₂')) (q' : k ≡ n₁' + suc n₂') (g' : Op m')
      → ⌊ ins n₁ n₂ p q g ∷ ⟦ ins n₁' n₂' p' q' g' ⟧ ⌋
        ≋ ((n₁ ⊣ (G g ⊢ n₂)) ∘[ trans (sym q') p ] (n₁' ⊣ (G g' ⊢ n₂')))
    ⌊ins∷ins⌋ n₁ n₂ p q g n₁' n₂' p' q' g' =
      ≋-∘ (≋-cast-∘ (sym q) _) (≋-idʳ _ ⟫ ≋-∘ ≋-refl (≋-∘-cast p' _))
      ⟫ ≋-assoc _ _ _
      ⟫ ≋-≈ (∘-cong ≈.refl (≈.trans (≈.sym (∘-assoc _ _ _)) (∘-cong (castₕ-castₕ (sym q') p) ≈.refl)))

  ⌊⌋-cong : {Γ Δ : Word m n} → Cong Cart Γ Δ → ⌊ Γ ⌋ ≈ ⌊ Δ ⌋
  ⌊⌋-cong ≅-refl = ≈.refl
  ⌊⌋-cong (≅-sym e) = ≈.sym (⌊⌋-cong e)
  ⌊⌋-cong (≅-trans e e') = ≈.trans (⌊⌋-cong e) (⌊⌋-cong e')
  ⌊⌋-cong (≅-cong {Γ₁ = Γ₁} {Γ₁'} {Γ₂} {Γ₂'} e₁ e₂) =
    ≈.trans (⌊⌋-++ Γ₁ Γ₂) (≈.trans (∘-cong (⌊⌋-cong e₁) (⌊⌋-cong e₂)) (≈.sym (⌊⌋-++ Γ₁' Γ₂')))
  -- administrative rules
  ⌊⌋-cong (I∙ n₁ n₂ p q e) = ∘-cong (∘-cong ≈.refl (∘-cong (⊣-cong (⊢-cong (G-cong e))) ≈.refl)) ≈.refl
  ⌊⌋-cong (E∙ e) = ∘-cong (R-cong e) ≈.refl
  ⌊⌋-cong (S∙ n₁ n₂ p q g) = ≋→≈
    ( ≋-idʳ _ ⟫ ⌊ins⌋≋ n₁ n₂ p q g
    ⟫ ≋-sym ( ≋-∘ (R-cast' q) (≋-∘ (≋-≈ (⌊sub!⌋₁ n₁ n₂ g)) (≋-idʳ _ ⟫ R-cast (sym p)) ⟫ ≋-idʳ _) ⟫ ≋-idˡ _ ) )
  -- symmetric rules
  ⌊⌋-cong (U₁∙ n₁ n₂ p) = ≋→≈
    ( ≋-idʳ _ ⟫ ⌊ins⌋≋ n₁ n₂ {m = 1} p p idₒ ⟫ ≋-⊣ (≋-⊢ (≋-≈ G-id)) ⟫ ≋-≈ (core-runit n₁ n₂) ⟫ ≋-idₕ (sym p) )
  ⌊⌋-cong U₂∙ = ≈.trans (∘-idʳ _) R-id
  ⌊⌋-cong (A∙ m₁ m₂ n₁ n₂ g h p₁ q₁ p₂ q₂ p₃) = ≋→≈
    ( ⌊ins∷ins⌋ m₁ m₂ p₁ q₁ g (m₁ + n₁) (n₂ + m₂) p₂ q₂ h
    ⟫ core-assoc m₁ m₂ n₁ n₂ (G g) (G h) _
    ⟫ ≋-⊣ (≋-⊢ (≋-≈ (≈.sym (G-sub g h))))
    ⟫ ≋-sym (≋-idʳ _ ⟫ ⌊ins⌋≋ m₁ m₂ p₃ q₁ _) )
  ⌊⌋-cong (R∙ r₁ r₂) =
    ≈.trans (∘-cong ≈.refl (∘-idʳ _)) (≈.trans (≈.sym (R-∘ r₁ r₂)) (≈.sym (∘-idʳ _)))
  ⌊⌋-cong (N∙ {n₁} {n₂} {m₁} {m₂} v r₁ s r₂) =
    ≈.trans (∘-cong (⌊sub!⌋₁ n₁ n₂ v) (∘-idʳ _))
    (≈.trans (core-N (G v) r₁ s r₂)
    (∘-cong ≈.refl (≈.sym (≈.trans (∘-idʳ _) (≈.trans (⌊sub!⌋₁ m₁ m₂ (v [ s ])) (⊣-cong (⊢-cong (G-ren v s))))))))
  ⌊⌋-cong (Sℓ∙ m₁ m₂ {n} g p q q') = ≋→≈
    ( ≋-∘ ≋-refl (≋-idʳ _ ⟫ ≋-≈ (⌊sub!⌋₁ m₁ (suc m₂) g))
    ⟫ core-Sℓ m₁ m₂ (G g) p
    ⟫ ≋-sym ( ≋-∘ (≋-cast-∘ (sym q) _) (≋-idʳ _ ⟫ ≋-≈ (R-∘ _ _) ⟫ ≋-∘ ≋-refl (R-cast q') ⟫ ≋-idʳ _)
            ⟫ ≋-assoc _ _ _ ) )
  ⌊⌋-cong (Sr∙ m₁ m₂ {n} g p q q' q'') = ≋→≈
    ( ≋-∘ ≋-refl (≋-idʳ _ ⟫ ≋-∘ ≋-refl (≋-∘-cast p _))
    ⟫ core-Sr m₁ m₂ (G g) (sym q) (sym q'')
    ⟫ ≋-sym ( ≋-∘ (≋-≈ (⌊sub!⌋₁ m₁ (suc m₂) g))
                  (≋-idʳ _ ⟫ ≋-≈ (R-∘ _ _) ⟫ ≋-∘ (≋-≈ (R-∘ _ _)) ≋-refl ⟫ ≋-∘ ≋-refl (R-cast q') ⟫ ≋-idʳ _)
            ⟫ ≋-R-cast q'' _ _ ) )
  -- cartesian rules
  ⌊⌋-cong (CEN∙ m₁ m m₂ {n₁} {n₂} g₁ g₂ c p q p' p'' q') = ≋→≈
    ( ≋-∘ (≋-≈ (⌊sub!⌋₁ m₁ (m + suc m₂) g₁)) (≋-idʳ _ ⟫ ≋-∘ ≋-refl (≋-∘-cast q _))
    ⟫ core-CEN m₁ m m₂ (G g₁) (G g₂) (map⊎ cart-central cart-central c) (sym p) (sym p'')
    ⟫ ≋-sym ( ≋-∘ (≋-cast-∘ (sym p') _) (≋-idʳ _ ⟫ ≋-cast-∘ refl _ ⟫ ≋-∘-cast q' _)
            ⟫ ≋-assoc _ _ _ ) )
  ⌊⌋-cong (D∙ m₁ m₂ {n} g c) =
    ≈.trans (∘-cong ≈.refl (≈.trans (∘-idʳ _) (⌊sub!⌋₁ m₁ m₂ g)))
    (≈.trans (core-D m₁ m₂ (G g) (cart-! c)) (≈.sym (∘-idʳ _)))
  ⌊⌋-cong (C∙ m₁ m₂ {n} g c p q) = ≋→≈
    ( ≋-∘ ≋-refl (≋-idʳ _ ⟫ ≋-≈ (⌊sub!⌋₁ m₁ m₂ g))
    ⟫ core-C m₁ m₂ (G g) (cart-Δ c) (sym p) q
    ⟫ ≋-assoc _ _ _
    ⟫ ≋-∘ ≋-refl (≋-assoc _ _ _)
    ⟫ ≋-sym ( ≋-∘ (≋-≈ (⌊sub!⌋₁ m₁ (suc m₂) g)) (≋-∘ ≋-refl (≋-idʳ _))
            ⟫ ≋-∘ ≋-refl (≋-assoc _ _ _ ⟫ ≋-∘ ≋-refl (≋-assoc _ _ _)) ) )

  ----------------------------------------------------------------------
  -- the uncurried pre-PROP functor Sub_ℂ → D
  ----------------------------------------------------------------------

  ⌊⌋-functor : PrePROPFunctor (SubPrePROP Cart) D
  ⌊⌋-functor = record
    { F      = ⌊_⌋
    ; F-cong = ⌊⌋-cong
    ; F-id   = ≈.refl
    ; F-∘    = λ f g → ⌊⌋-++ g f
    ; F-⊣    = λ {m} {n} {k} f → ⌊⌋-⊣ k f
    ; F-⊢    = λ {m} {n} {k} f → ⌊⌋-⊢ k f
    ; F-σ    = λ {m} {n} → ≈.trans (∘-idʳ _) (R-σ n m)
    }
