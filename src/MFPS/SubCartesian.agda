------------------------------------------------------------------------
-- Proposition 3.14(ii): for a cartesian operad 𝕍, Sub×_𝕍 is a
-- cartesian PROP (Def. 2.9).
--
-- The paper's proof says that "the required naturality [of copy and
-- discard] is enforced by the (D) and (C) rules of Fig. 3".  The rules
-- (D),(C) only speak about discarding/copying the *single* variable
-- that a substitution step fills; naturality of Δₙ, !ₙ for all n and
-- all words has to be derived from them.  This module does that:
--
--   * !-nat: !ₙ ∘ Γ ≈ !ₘ — by induction on Γ; the substitution case
--     splits !_{n₁+1+n₂} through id + !₁ + id and uses (D); every
--     composite with a discard is an equation between maps out of the
--     empty set.
--   * general naturality of the symmetry, σ_{k,n} ∘ (k ⊣ Γ) ≈
--     (Γ ⊢ k) ∘ σ_{k,m} (and its mirror), by induction on k from the
--     generating case k = 1 (MFPS.SubSym) and the hexagon law.
--   * Δ-nat: Δₙ ∘ Γ ≈ ((Γ ⊢ n) ∘ (m ⊣ Γ)) ∘ Δₘ.  Closure of this
--     property under whiskering is proved from the coherence condition
--     Δ_{a+b} = (a ⊣ σ_{a,b} ⊢ b) ∘ (Δ_a + Δ_b) of Def. 2.9 (an
--     equation of renamings), centrality (all steps of Sub× are
--     central, MFPS.SubCentral) and the general naturality of σ; the
--     base case for the step {0 ⊣ g ⊢ 0} is rule (C); renaming steps
--     are an equation of renamings; concatenation uses centrality.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.SubCartesian (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊
open import MFPS.Sub 𝕊
open import MFPS.SubCast 𝕊
open import MFPS.SubStrict 𝕊 using (subst₂W-conj; ⊢-0ʷ; ⊣-⊣ʷ; ⊢-⊢ʷ; ⊣-⊢ʷ)
open import MFPS.SubWhisker 𝕊 using (⊣-stable; ⊢-stable)
open import MFPS.SubSym 𝕊 using (σʷ; σʷ-σʷ; castʷ; castʷ-rn; σʷ-hexʳ; natL; _⟶_; rn-split₅)
open import MFPS.SubCentral 𝕊 using (Eq₁; CentralW; central-rn; central-word; AllCart)
open import MFPS.SubPROP 𝕊 using (0⊣ʷ; SubPrePROP)
open import MFPS.PROP using (CartesianPROP)

private
  variable
    j k m n a b m' n' : ℕ

-- σ_{n,0} is a cast
σʳ-0-isCast : ∀ n → IsCast (σʳ n 0)
σʳ-0-isCast n = Fin+-ext {m = n} {n = 0} (λ j → trans (toℕ-σʳ-inl n 0 j) (sym (toℕ-↑ˡ j 0))) (λ ())

module _ {Cart : ∀ {n} → Op n → Set} where

  ----------------------------------------------------------------------
  -- undoing a conjugation by casts
  ----------------------------------------------------------------------

  insert-ids : (X : Word m n) → Cong Cart X (rn (idʳ {n}) ∷ (X ++ ⟦ rn (idʳ {m}) ⟧))
  insert-ids X =
    ≅-≡ (sym (++-identityʳ X))
    ⟶ ≅-cong {Γ₁ = X} ≅-refl (≅-sym U₂∙)
    ⟶ ≅-cong {Γ₁ = ε} (≅-sym U₂∙) ≅-refl

  unconjW : (p : m ≡ a) (q : n ≡ b) {X : Word m n} {Y : Word a b}
    → Cong Cart (rn (castʳ (sym q)) ∷ (X ++ ⟦ rn (castʳ p) ⟧)) Y
    → Cong Cart X (rn (castʳ q) ∷ (Y ++ ⟦ rn (castʳ (sym p)) ⟧))
  unconjW refl refl {X} {Y} h = insert-ids X ⟶ h ⟶ insert-ids Y

  -- the strictness laws in "conjugated" form
  ⊢-⊢-conj : ∀ j k (Γ : Word m n)
    → Cong Cart ((Γ ⊢ʷ j) ⊢ʷ k)
                (rn (castʳ (+-assoc n j k)) ∷ ((Γ ⊢ʷ (j + k)) ++ ⟦ rn (castʳ (sym (+-assoc m j k))) ⟧))
  ⊢-⊢-conj {m} {n} j k Γ =
    unconjW (+-assoc m j k) (+-assoc n j k)
      (≅-sym (subst₂W-conj (+-assoc m j k) (+-assoc n j k) ((Γ ⊢ʷ j) ⊢ʷ k)) ⟶ ⊢-⊢ʷ j k Γ _ _)

  ⊢-0-conj : (Γ : Word m n)
    → Cong Cart (Γ ⊢ʷ 0) (rn (castʳ (+-identityʳ n)) ∷ (Γ ++ ⟦ rn (castʳ (sym (+-identityʳ m))) ⟧))
  ⊢-0-conj {m} {n} Γ =
    unconjW (+-identityʳ m) (+-identityʳ n)
      (≅-sym (subst₂W-conj (+-identityʳ m) (+-identityʳ n) (Γ ⊢ʷ 0)) ⟶ ⊢-0ʷ Γ _ _)

  ----------------------------------------------------------------------
  -- Naturality of discard: !ₙ ∘ Γ ≈ !ₘ (Def. 2.9), for words all of
  -- whose substitution steps are cartesian.
  ----------------------------------------------------------------------

  -- any renaming after a discard is a discard
  !-absorb : (r : Ren n k) → Cong Cart (rn (!ʳ n) ∷ ⟦ rn r ⟧) ⟦ rn (!ʳ k) ⟧
  !-absorb r = R∙ _ _ ⟶ E∙ (λ ())

  !-nat : (Γ : Word m n) → AllCart {Cart = Cart} Γ → Cong Cart (rn (!ʳ n) ∷ Γ) ⟦ rn (!ʳ m) ⟧
  !-nat ε _ = ≅-refl
  !-nat (rn r ∷ Γ) c = ≅-cong (!-absorb r) ≅-refl ⟶ !-nat Γ c
  !-nat (ins n₁ n₂ {kg} p q g ∷ Γ) (c , a) =
    ≅-∷ (≅-cong (S∙ n₁ n₂ p q g) ≅-refl)
    ⟶ ≅-cong (!-absorb (castʳ q)) ≅-refl
    ⟶ ≅-cong {Γ₁ = ⟦ rn (!ʳ (n₁ + suc n₂)) ⟧} (≅-sym (!-absorb (idʳ {n₁} +ʳ !ʳ 1 +ʳ idʳ {n₂}))) ≅-refl
    ⟶ ≅-∷ (≅-cong (D∙ n₁ n₂ g c) ≅-refl)
    ⟶ ≅-cong (!-absorb (idʳ {n₁} +ʳ !ʳ kg +ʳ idʳ {n₂})) ≅-refl
    ⟶ ≅-cong (!-absorb (castʳ (sym p))) ≅-refl
    ⟶ !-nat Γ a

  ----------------------------------------------------------------------
  -- General naturality of the symmetry:
  --   σ_{k,n} ∘ (k ⊣ Γ) ≈ (Γ ⊢ k) ∘ σ_{k,m}
  -- by induction on k.  k = 0: σ_{0,n} is a cast and 0 ⊣ Γ = Γ,
  -- Γ ⊢ 0 = Γ up to casts.  k = 1 + k': the hexagon law writes
  -- σ_{1+k',n} as (σ_{1,n} ⊢ k') ∘ (1 ⊣ σ_{k',n}) (up to a cast); the
  -- inner symmetry passes k' ⊣ Γ by the induction hypothesis and the
  -- outer one passes 1 ⊣ Γ by the generating case σ-nat₁ˡ.
  ----------------------------------------------------------------------

  natLk : ∀ k (Γ : Word m n)
    → Cong Cart (rn (σʳ n k) ∷ (k ⊣ʷ Γ)) ((Γ ⊢ʷ k) ++ ⟦ rn (σʳ m k) ⟧)
  natLk {m} {n} zero Γ =
    ≅-∷ (0⊣ʷ _ Γ)
    ⟶ ≅-∷ˡ (rn-isCast-unique (σʳ-0-isCast n) (castʳ-isCast (+-identityʳ n)))
    ⟶ ≅-sym
      ( ≅-cong (⊢-0-conj Γ) ≅-refl
      ⟶ ≅-∷ (≅-≡ (++-assoc Γ ⟦ rn (castʳ (sym (+-identityʳ m))) ⟧ ⟦ rn (σʳ m 0) ⟧))
      ⟶ ≅-∷ (≅-cong {Γ₁ = Γ} ≅-refl (rn-rn _ _))
      ⟶ ≅-∷ (≅-cong {Γ₁ = Γ} ≅-refl (rn-isCast (σʳ-0ʳ-isCast m (+-identityʳ m))))
      ⟶ ≅-∷ (≅-≡ (++-identityʳ Γ)) )
  natLk {m} {n} (suc k') Γ =
    -- hexagon for σ_{1+k',n}, and (1+k') ⊣ Γ = 1 ⊣ (k' ⊣ Γ)
    ≅-cong {Γ₁ = σʷ (1 + k') n} (σʷ-hexʳ 1 k' n refl refl (+-assoc n 1 k') ⟶ ≅-cong (castʷ-rn (+-assoc n 1 k')) ≅-refl)
           (≅-sym (⊣-⊣ʷ 1 k' Γ refl refl))
    ⟶ ≅-∷ (≅-≡ (++-assoc (σʷ 1 n ⊢ʷ k') (1 ⊣ʷ σʷ k' n) (1 ⊣ʷ (k' ⊣ʷ Γ))))
    ⟶ ≅-∷ (≅-cong {Γ₁ = σʷ 1 n ⊢ʷ k'} ≅-refl (≅-≡ (sym (⊣ʷ-++ 1 (σʷ k' n) (k' ⊣ʷ Γ)))))
    -- induction hypothesis under 1 ⊣ (−)
    ⟶ ≅-∷ (≅-cong {Γ₁ = σʷ 1 n ⊢ʷ k'} ≅-refl (⊣-stable 1 (natLk k' Γ)))
    ⟶ ≅-∷ (≅-cong {Γ₁ = σʷ 1 n ⊢ʷ k'} ≅-refl (≅-≡ (⊣ʷ-++ 1 (Γ ⊢ʷ k') ⟦ rn (σʳ m k') ⟧)))
    ⟶ ≅-∷ (≅-cong {Γ₁ = σʷ 1 n ⊢ʷ k'} ≅-refl (≅-cong (≅-sym (⊣-⊢ʷ 1 k' Γ refl refl)) ≅-refl))
    ⟶ ≅-∷ (≅-≡ (sym (++-assoc (σʷ 1 n ⊢ʷ k') ((1 ⊣ʷ Γ) ⊢ʷ k') (1 ⊣ʷ σʷ k' m))))
    ⟶ ≅-∷ (≅-cong (≅-≡ (sym (⊢ʷ-++ (σʷ 1 n) (1 ⊣ʷ Γ) k'))) ≅-refl)
    -- the generating case under (−) ⊢ k'
    ⟶ ≅-∷ (≅-cong (⊢-stable k' (natL Γ)) ≅-refl)
    ⟶ ≅-∷ (≅-cong (≅-≡ (⊢ʷ-++ (Γ ⊢ʷ 1) (σʷ 1 m) k')) ≅-refl)
    ⟶ ≅-∷ (≅-≡ (++-assoc ((Γ ⊢ʷ 1) ⊢ʷ k') (σʷ 1 m ⊢ʷ k') (1 ⊣ʷ σʷ k' m)))
    -- (Γ ⊢ 1) ⊢ k' = Γ ⊢ (1 + k') up to casts; the casts cancel
    ⟶ ≅-∷ (≅-cong (⊢-⊢-conj 1 k' Γ) ≅-refl)
    ⟶ rn-rn _ _
    ⟶ ≅-cong {Γ₁ = ⟦ rn (castʳ (+-assoc n 1 k') ∘ʳ castʳ (sym (+-assoc n 1 k'))) ⟧}
             (rn-isCast (∘ʳ-isCast' (castʳ (+-assoc n 1 k')) (castʳ (sym (+-assoc n 1 k')))
                                    (castʳ-isCast (+-assoc n 1 k')) (castʳ-isCast (sym (+-assoc n 1 k'))))) ≅-refl
    ⟶ ≅-≡ (++-assoc (Γ ⊢ʷ (1 + k')) ⟦ rn (castʳ (sym (+-assoc m 1 k'))) ⟧ ((σʷ 1 m ⊢ʷ k') ++ (1 ⊣ʷ σʷ k' m)))
    -- and the hexagon for σ_{1+k',m}, backwards
    ⟶ ≅-cong {Γ₁ = Γ ⊢ʷ (1 + k')} ≅-refl
        (≅-sym (σʷ-hexʳ 1 k' m refl refl (+-assoc m 1 k') ⟶ ≅-cong (castʷ-rn (+-assoc m 1 k')) ≅-refl))

  -- the mirror law σ_{n,k} ∘ (Γ ⊢ k) ≈ (k ⊣ Γ) ∘ σ_{m,k}, by the involution
  natRk : ∀ k (Γ : Word m n)
    → Cong Cart (rn (σʳ k n) ∷ (Γ ⊢ʷ k)) ((k ⊣ʷ Γ) ++ ⟦ rn (σʳ k m) ⟧)
  natRk {m} {n} k Γ =
    ≅-∷ (≅-≡ (sym (++-identityʳ (Γ ⊢ʷ k))))
    ⟶ ≅-∷ (≅-cong {Γ₁ = Γ ⊢ʷ k} ≅-refl (≅-sym (σʷ-σʷ m k)))
    ⟶ ≅-∷ (≅-≡ (sym (++-assoc (Γ ⊢ʷ k) ⟦ rn (σʳ m k) ⟧ ⟦ rn (σʳ k m) ⟧)))
    ⟶ ≅-∷ (≅-cong (≅-sym (natLk k Γ)) ≅-refl)
    ⟶ ≅-cong (σʷ-σʷ k n) ≅-refl

------------------------------------------------------------------------
-- The coherence condition of Def. 2.9 as an equation of renamings:
--   Δ_{a+b} = (a ⊣ σ_{a,b} ⊢ b) ∘ ((a+a) ⊣ Δ_b) ∘ (Δ_a ⊢ b)
-- up to the two arity casts (a+b)+(a+b) = a+((b+a)+b) and
-- a+((a+b)+b) = (a+a)+(b+b).  Proved pointwise on the four blocks
-- [A B A' B'] of the domain.
------------------------------------------------------------------------

Δ-coh : ∀ a b (e₀ : (a + b) + (a + b) ≡ a + ((b + a) + b)) (e₁ : a + ((a + b) + b) ≡ (a + a) + (b + b))
  → Δʳ (a + b) ≗ ((Δʳ a +ʳ idʳ {b}) ∘ʳ (idʳ {a + a} +ʳ Δʳ b) ∘ʳ castʳ e₁ ∘ʳ (idʳ {a} +ʳ (σʳ b a +ʳ idʳ {b})) ∘ʳ castʳ e₀)
Δ-coh a b e₀ e₁ = Fin+-ext {m = a + b} {n = a + b} (Fin+-ext {m = a} {n = b} c₁ c₂) (Fin+-ext {m = a} {n = b} c₃ c₄)
  where
    open ≡-Reasoning
    S = idʳ {a} +ʳ (σʳ b a +ʳ idʳ {b})
    X = idʳ {a + a} +ʳ Δʳ b
    Y = Δʳ a +ʳ idʳ {b}

    c₁ : ∀ j → Δʳ (a + b) ((j ↑ˡ b) ↑ˡ (a + b)) ≡ (Y ∘ʳ X ∘ʳ castʳ e₁ ∘ʳ S ∘ʳ castʳ e₀) ((j ↑ˡ b) ↑ˡ (a + b))
    c₁ j = begin
      Δʳ (a + b) ((j ↑ˡ b) ↑ˡ (a + b))
        ≡⟨ [,]ʳ-inl idʳ idʳ (j ↑ˡ b) ⟩
      j ↑ˡ b
        ≡⟨ sym (cong (_↑ˡ b) ([,]ʳ-inl idʳ idʳ j)) ⟩
      Δʳ a (j ↑ˡ a) ↑ˡ b
        ≡⟨ sym (+ʳ-inj₁ (Δʳ a) idʳ (j ↑ˡ a)) ⟩
      Y ((j ↑ˡ a) ↑ˡ b)
        ≡⟨ cong Y (sym (+ʳ-inj₁ idʳ (Δʳ b) (j ↑ˡ a))) ⟩
      Y (X ((j ↑ˡ a) ↑ˡ (b + b)))
        ≡⟨ cong (Y ∘ʳ X) (sym (castʳ-≡ e₁ _ _ (trans (toℕ-↑ˡ j ((a + b) + b)) (sym (trans (toℕ-↑ˡ (j ↑ˡ a) (b + b)) (toℕ-↑ˡ j a)))))) ⟩
      Y (X (castʳ e₁ (j ↑ˡ ((a + b) + b))))
        ≡⟨ cong (Y ∘ʳ X ∘ʳ castʳ e₁) (sym (+ʳ-inj₁ idʳ (σʳ b a +ʳ idʳ) j)) ⟩
      Y (X (castʳ e₁ (S (j ↑ˡ ((b + a) + b)))))
        ≡⟨ cong (Y ∘ʳ X ∘ʳ castʳ e₁ ∘ʳ S) (sym (castʳ-≡ e₀ _ _ (trans (toℕ-↑ˡ (j ↑ˡ b) (a + b)) (trans (toℕ-↑ˡ j b) (sym (toℕ-↑ˡ j ((b + a) + b))))))) ⟩
      Y (X (castʳ e₁ (S (castʳ e₀ ((j ↑ˡ b) ↑ˡ (a + b)))))) ∎

    c₂ : ∀ j → Δʳ (a + b) ((a ↑ʳ j) ↑ˡ (a + b)) ≡ (Y ∘ʳ X ∘ʳ castʳ e₁ ∘ʳ S ∘ʳ castʳ e₀) ((a ↑ʳ j) ↑ˡ (a + b))
    c₂ j = begin
      Δʳ (a + b) ((a ↑ʳ j) ↑ˡ (a + b))
        ≡⟨ [,]ʳ-inl idʳ idʳ (a ↑ʳ j) ⟩
      a ↑ʳ j
        ≡⟨ sym (+ʳ-inj₂ (Δʳ a) idʳ j) ⟩
      Y ((a + a) ↑ʳ j)
        ≡⟨ cong (λ z → Y ((a + a) ↑ʳ z)) (sym ([,]ʳ-inl idʳ idʳ j)) ⟩
      Y ((a + a) ↑ʳ Δʳ b (j ↑ˡ b))
        ≡⟨ cong Y (sym (+ʳ-inj₂ idʳ (Δʳ b) (j ↑ˡ b))) ⟩
      Y (X ((a + a) ↑ʳ (j ↑ˡ b)))
        ≡⟨ cong (Y ∘ʳ X) (sym (castʳ-≡ e₁ _ _ (trans (toℕ-↑ʳ a ((a ↑ʳ j) ↑ˡ b)) (trans (cong (a +_) (trans (toℕ-↑ˡ (a ↑ʳ j) b) (toℕ-↑ʳ a j))) (trans (sym (+-assoc a a (toℕ j))) (sym (trans (toℕ-↑ʳ (a + a) (j ↑ˡ b)) (cong ((a + a) +_) (toℕ-↑ˡ j b))))))))) ⟩
      Y (X (castʳ e₁ (a ↑ʳ ((a ↑ʳ j) ↑ˡ b))))
        ≡⟨ cong (λ z → Y (X (castʳ e₁ (a ↑ʳ (z ↑ˡ b))))) (sym (σʳ-inl b a j)) ⟩
      Y (X (castʳ e₁ (a ↑ʳ (σʳ b a (j ↑ˡ a) ↑ˡ b))))
        ≡⟨ cong (λ z → Y (X (castʳ e₁ (a ↑ʳ z)))) (sym (+ʳ-inj₁ (σʳ b a) idʳ (j ↑ˡ a))) ⟩
      Y (X (castʳ e₁ (a ↑ʳ (σʳ b a +ʳ idʳ) ((j ↑ˡ a) ↑ˡ b))))
        ≡⟨ cong (Y ∘ʳ X ∘ʳ castʳ e₁) (sym (+ʳ-inj₂ idʳ (σʳ b a +ʳ idʳ) ((j ↑ˡ a) ↑ˡ b))) ⟩
      Y (X (castʳ e₁ (S (a ↑ʳ ((j ↑ˡ a) ↑ˡ b)))))
        ≡⟨ cong (Y ∘ʳ X ∘ʳ castʳ e₁ ∘ʳ S) (sym (castʳ-≡ e₀ _ _ (trans (toℕ-↑ˡ (a ↑ʳ j) (a + b)) (trans (toℕ-↑ʳ a j) (sym (trans (toℕ-↑ʳ a ((j ↑ˡ a) ↑ˡ b)) (cong (a +_) (trans (toℕ-↑ˡ (j ↑ˡ a) b) (toℕ-↑ˡ j a))))))))) ⟩
      Y (X (castʳ e₁ (S (castʳ e₀ ((a ↑ʳ j) ↑ˡ (a + b)))))) ∎

    c₃ : ∀ j → Δʳ (a + b) ((a + b) ↑ʳ (j ↑ˡ b)) ≡ (Y ∘ʳ X ∘ʳ castʳ e₁ ∘ʳ S ∘ʳ castʳ e₀) ((a + b) ↑ʳ (j ↑ˡ b))
    c₃ j = begin
      Δʳ (a + b) ((a + b) ↑ʳ (j ↑ˡ b))
        ≡⟨ [,]ʳ-inr idʳ idʳ (j ↑ˡ b) ⟩
      j ↑ˡ b
        ≡⟨ sym (cong (_↑ˡ b) ([,]ʳ-inr idʳ idʳ j)) ⟩
      Δʳ a (a ↑ʳ j) ↑ˡ b
        ≡⟨ sym (+ʳ-inj₁ (Δʳ a) idʳ (a ↑ʳ j)) ⟩
      Y ((a ↑ʳ j) ↑ˡ b)
        ≡⟨ cong Y (sym (+ʳ-inj₁ idʳ (Δʳ b) (a ↑ʳ j))) ⟩
      Y (X ((a ↑ʳ j) ↑ˡ (b + b)))
        ≡⟨ cong (Y ∘ʳ X) (sym (castʳ-≡ e₁ _ _ (trans (toℕ-↑ʳ a ((j ↑ˡ b) ↑ˡ b)) (trans (cong (a +_) (trans (toℕ-↑ˡ (j ↑ˡ b) b) (toℕ-↑ˡ j b))) (sym (trans (toℕ-↑ˡ (a ↑ʳ j) (b + b)) (toℕ-↑ʳ a j))))))) ⟩
      Y (X (castʳ e₁ (a ↑ʳ ((j ↑ˡ b) ↑ˡ b))))
        ≡⟨ cong (λ z → Y (X (castʳ e₁ (a ↑ʳ (z ↑ˡ b))))) (sym (σʳ-inr b a j)) ⟩
      Y (X (castʳ e₁ (a ↑ʳ (σʳ b a (b ↑ʳ j) ↑ˡ b))))
        ≡⟨ cong (λ z → Y (X (castʳ e₁ (a ↑ʳ z)))) (sym (+ʳ-inj₁ (σʳ b a) idʳ (b ↑ʳ j))) ⟩
      Y (X (castʳ e₁ (a ↑ʳ (σʳ b a +ʳ idʳ) ((b ↑ʳ j) ↑ˡ b))))
        ≡⟨ cong (Y ∘ʳ X ∘ʳ castʳ e₁) (sym (+ʳ-inj₂ idʳ (σʳ b a +ʳ idʳ) ((b ↑ʳ j) ↑ˡ b))) ⟩
      Y (X (castʳ e₁ (S (a ↑ʳ ((b ↑ʳ j) ↑ˡ b)))))
        ≡⟨ cong (Y ∘ʳ X ∘ʳ castʳ e₁ ∘ʳ S) (sym (castʳ-≡ e₀ _ _ (trans (toℕ-↑ʳ (a + b) (j ↑ˡ b)) (trans (cong ((a + b) +_) (toℕ-↑ˡ j b)) (trans (+-assoc a b (toℕ j)) (sym (trans (toℕ-↑ʳ a ((b ↑ʳ j) ↑ˡ b)) (cong (a +_) (trans (toℕ-↑ˡ (b ↑ʳ j) b) (toℕ-↑ʳ b j)))))))))) ⟩
      Y (X (castʳ e₁ (S (castʳ e₀ ((a + b) ↑ʳ (j ↑ˡ b)))))) ∎

    c₄ : ∀ j → Δʳ (a + b) ((a + b) ↑ʳ (a ↑ʳ j)) ≡ (Y ∘ʳ X ∘ʳ castʳ e₁ ∘ʳ S ∘ʳ castʳ e₀) ((a + b) ↑ʳ (a ↑ʳ j))
    c₄ j = begin
      Δʳ (a + b) ((a + b) ↑ʳ (a ↑ʳ j))
        ≡⟨ [,]ʳ-inr idʳ idʳ (a ↑ʳ j) ⟩
      a ↑ʳ j
        ≡⟨ sym (+ʳ-inj₂ (Δʳ a) idʳ j) ⟩
      Y ((a + a) ↑ʳ j)
        ≡⟨ cong (λ z → Y ((a + a) ↑ʳ z)) (sym ([,]ʳ-inr idʳ idʳ j)) ⟩
      Y ((a + a) ↑ʳ Δʳ b (b ↑ʳ j))
        ≡⟨ cong Y (sym (+ʳ-inj₂ idʳ (Δʳ b) (b ↑ʳ j))) ⟩
      Y (X ((a + a) ↑ʳ (b ↑ʳ j)))
        ≡⟨ cong (Y ∘ʳ X) (sym (castʳ-≡ e₁ _ _ (trans (toℕ-↑ʳ a ((a + b) ↑ʳ j)) (trans (cong (a +_) (toℕ-↑ʳ (a + b) j)) (trans (sym (+-assoc a (a + b) (toℕ j))) (trans (cong (_+ toℕ j) (sym (+-assoc a a b))) (trans (+-assoc (a + a) b (toℕ j)) (sym (trans (toℕ-↑ʳ (a + a) (b ↑ʳ j)) (cong ((a + a) +_) (toℕ-↑ʳ b j))))))))))) ⟩
      Y (X (castʳ e₁ (a ↑ʳ ((a + b) ↑ʳ j))))
        ≡⟨ cong (λ z → Y (X (castʳ e₁ (a ↑ʳ z)))) (sym (+ʳ-inj₂ (σʳ b a) idʳ j)) ⟩
      Y (X (castʳ e₁ (a ↑ʳ (σʳ b a +ʳ idʳ) ((b + a) ↑ʳ j))))
        ≡⟨ cong (Y ∘ʳ X ∘ʳ castʳ e₁) (sym (+ʳ-inj₂ idʳ (σʳ b a +ʳ idʳ) ((b + a) ↑ʳ j))) ⟩
      Y (X (castʳ e₁ (S (a ↑ʳ ((b + a) ↑ʳ j)))))
        ≡⟨ cong (Y ∘ʳ X ∘ʳ castʳ e₁ ∘ʳ S) (sym (castʳ-≡ e₀ _ _ (trans (toℕ-↑ʳ (a + b) (a ↑ʳ j)) (trans (cong ((a + b) +_) (toℕ-↑ʳ a j)) (trans (+-assoc a b (a + toℕ j)) (trans (cong (a +_) (sym (+-assoc b a (toℕ j)))) (sym (trans (toℕ-↑ʳ a ((b + a) ↑ʳ j)) (cong (a +_) (toℕ-↑ʳ (b + a) j)))))))))) ⟩
      Y (X (castʳ e₁ (S (castʳ e₀ ((a + b) ↑ʳ (a ↑ʳ j)))))) ∎

------------------------------------------------------------------------
-- Naturality of copy.
------------------------------------------------------------------------

-- the arity casts of the coherence identity
E₀ : ∀ a b → (a + b) + (a + b) ≡ a + ((b + a) + b)
E₀ a b = trans (+-assoc a b (a + b)) (cong (a +_) (sym (+-assoc b a b)))

E₁ : ∀ a b → a + ((a + b) + b) ≡ (a + a) + (b + b)
E₁ a b = trans (cong (a +_) (+-assoc a b b)) (sym (+-assoc a a (b + b)))

-- the block shuffle a ⊣ σ_{a,b} ⊢ b
Sh : ∀ a b → Ren (a + ((b + a) + b)) (a + ((a + b) + b))
Sh a b = idʳ {a} +ʳ (σʳ b a +ʳ idʳ {b})

module _ {Cart : ∀ {n} → Op n → Set} where

  -- Def. 2.9, naturality of Δ, as a property of a word
  ΔNat : Word m n → Set
  ΔNat {m} {n} Γ = Cong Cart (rn (Δʳ n) ∷ Γ) ((Γ ⊢ʷ n) ++ ((m ⊣ʷ Γ) ++ ⟦ rn (Δʳ m) ⟧))

  ΔNat-ε : ΔNat (ε {n})
  ΔNat-ε = ≅-refl

  ΔNat-≅ : {Γ Γ' : Word m n} → Cong Cart Γ Γ' → ΔNat Γ → ΔNat Γ'
  ΔNat-≅ {m} {n} e h = ≅-∷ (≅-sym e) ⟶ h ⟶ ≅-cong (⊢-stable n e) (≅-cong (⊣-stable m e) ≅-refl)

  -- Δ-naturality for a renaming step is an equation of renamings
  ΔNat-rn : (r : Ren n m) → ΔNat ⟦ rn r ⟧
  ΔNat-rn {n} {m} r =
    R∙ _ _ ⟶ E∙ lemma ⟶ ≅-sym (rn-rn _ _ ⟶ rn-rn _ _)
    where
      lemma : (r ∘ʳ Δʳ n) ≗ (Δʳ m ∘ʳ (idʳ {m} +ʳ r) ∘ʳ (r +ʳ idʳ {n}))
      lemma = Fin+-ext
        (λ j → trans (cong r ([,]ʳ-inl idʳ idʳ j))
               (sym (trans (cong (Δʳ m ∘ʳ (idʳ +ʳ r)) (+ʳ-inj₁ r idʳ j))
                    (trans (cong (Δʳ m) (+ʳ-inj₁ idʳ r (r j))) ([,]ʳ-inl idʳ idʳ (r j))))))
        (λ j → trans (cong r ([,]ʳ-inr idʳ idʳ j))
               (sym (trans (cong (Δʳ m ∘ʳ (idʳ +ʳ r)) (+ʳ-inj₂ r idʳ j))
                    (trans (cong (Δʳ m) (+ʳ-inj₂ idʳ r j)) ([,]ʳ-inr idʳ idʳ (r j))))))

  -- Δ-naturality is closed under composition, given centrality of the
  -- second factor (used to interchange (k ⊣ Γ₁) and (Γ₂ ⊢ k))
  ΔNat-++ : {Γ₁ : Word k n} {Γ₂ : Word m k} → ΔNat Γ₁ → ΔNat Γ₂ → CentralW Γ₂ → ΔNat (Γ₁ ++ Γ₂)
  ΔNat-++ {k} {n} {m} {Γ₁} {Γ₂} h₁ h₂ c =
    ≅-cong h₁ ≅-refl
    ⟶ ≅-≡ (++-assoc (Γ₁ ⊢ʷ n) _ Γ₂)
    ⟶ ≅-cong {Γ₁ = Γ₁ ⊢ʷ n} ≅-refl (≅-≡ (++-assoc (k ⊣ʷ Γ₁) ⟦ rn (Δʳ k) ⟧ Γ₂))
    ⟶ ≅-cong {Γ₁ = Γ₁ ⊢ʷ n} ≅-refl (≅-cong {Γ₁ = k ⊣ʷ Γ₁} ≅-refl h₂)
    ⟶ ≅-cong {Γ₁ = Γ₁ ⊢ʷ n} ≅-refl (≅-≡ (sym (++-assoc (k ⊣ʷ Γ₁) (Γ₂ ⊢ʷ k) _)))
    ⟶ ≅-cong {Γ₁ = Γ₁ ⊢ʷ n} ≅-refl (≅-cong (≅-sym (proj₁ (c Γ₁))) ≅-refl)
    ⟶ ≅-cong {Γ₁ = Γ₁ ⊢ʷ n} ≅-refl (≅-≡ (++-assoc (Γ₂ ⊢ʷ n) (m ⊣ʷ Γ₁) _))
    ⟶ ≅-≡ (sym (++-assoc (Γ₁ ⊢ʷ n) (Γ₂ ⊢ʷ n) _))
    ⟶ ≅-cong {Γ₁ = (Γ₁ ⊢ʷ n) ++ (Γ₂ ⊢ʷ n)} ≅-refl (≅-≡ (sym (++-assoc (m ⊣ʷ Γ₁) (m ⊣ʷ Γ₂) _)))
    ⟶ ≅-≡ (cong₂ (λ x y → x ++ (y ++ ⟦ rn (Δʳ m) ⟧)) (sym (⊢ʷ-++ Γ₁ Γ₂ n)) (sym (⊣ʷ-++ m Γ₁ Γ₂)))

  -- the coherence identity as words
  Δ-cohʷ : ∀ a b {Γ : Word j (a + b)}
    → Cong Cart (rn (Δʳ (a + b)) ∷ Γ)
                (rn (castʳ (E₀ a b)) ∷ rn (Sh a b) ∷ rn (castʳ (E₁ a b)) ∷ rn (idʳ {a + a} +ʳ Δʳ b) ∷ rn (Δʳ a +ʳ idʳ {b}) ∷ Γ)
  Δ-cohʷ a b = rn-split₅ (Δ-coh a b (E₀ a b) (E₁ a b))

  ----------------------------------------------------------------------
  -- cast bookkeeping: the strictness laws in "split"/"merge" form
  ----------------------------------------------------------------------

  ⊣-⊣-split : ∀ a b (W : Word m n)
    → Cong Cart ((a + b) ⊣ʷ W)
                (rn (castʳ (+-assoc a b n)) ∷ ((a ⊣ʷ (b ⊣ʷ W)) ++ ⟦ rn (castʳ (sym (+-assoc a b m))) ⟧))
  ⊣-⊣-split {m} {n} a b W =
    ≅-sym (⊣-⊣ʷ a b W (sym (+-assoc a b m)) (sym (+-assoc a b n)))
    ⟶ subst₂W-conj (sym (+-assoc a b m)) (sym (+-assoc a b n)) (a ⊣ʷ (b ⊣ʷ W))
    ⟶ ≅-∷ˡ (rn-isCast-unique (castʳ-isCast _) (castʳ-isCast _))

  ⊣-⊣-merge : ∀ a b (W : Word m n)
    → Cong Cart (a ⊣ʷ (b ⊣ʷ W))
                (rn (castʳ (sym (+-assoc a b n))) ∷ (((a + b) ⊣ʷ W) ++ ⟦ rn (castʳ (+-assoc a b m)) ⟧))
  ⊣-⊣-merge {m} {n} a b W =
    unconjW (sym (+-assoc a b m)) (sym (+-assoc a b n))
      (≅-sym (subst₂W-conj _ _ (a ⊣ʷ (b ⊣ʷ W))) ⟶ ⊣-⊣ʷ a b W _ _)
    ⟶ ≅-∷ (≅-cong {Γ₁ = (a + b) ⊣ʷ W} ≅-refl (rn-isCast-unique (castʳ-isCast _) (castʳ-isCast _)))

  ⊣-⊢-split : ∀ a k (W : Word m n)
    → Cong Cart (a ⊣ʷ (W ⊢ʷ k))
                (rn (castʳ (sym (+-assoc a n k))) ∷ (((a ⊣ʷ W) ⊢ʷ k) ++ ⟦ rn (castʳ (+-assoc a m k)) ⟧))
  ⊣-⊢-split {m} {n} a k W =
    ≅-sym (⊣-⊢ʷ a k W (+-assoc a m k) (+-assoc a n k))
    ⟶ subst₂W-conj (+-assoc a m k) (+-assoc a n k) ((a ⊣ʷ W) ⊢ʷ k)

  ⊣-⊢-merge : ∀ a k (W : Word m n)
    → Cong Cart ((a ⊣ʷ W) ⊢ʷ k)
                (rn (castʳ (+-assoc a n k)) ∷ ((a ⊣ʷ (W ⊢ʷ k)) ++ ⟦ rn (castʳ (sym (+-assoc a m k))) ⟧))
  ⊣-⊢-merge {m} {n} a k W =
    unconjW (+-assoc a m k) (+-assoc a n k)
      (≅-sym (subst₂W-conj _ _ ((a ⊣ʷ W) ⊢ʷ k)) ⟶ ⊣-⊢ʷ a k W _ _)

  ⊢-⊢-split : ∀ j k (W : Word m n)
    → Cong Cart (W ⊢ʷ (j + k))
                (rn (castʳ (sym (+-assoc n j k))) ∷ (((W ⊢ʷ j) ⊢ʷ k) ++ ⟦ rn (castʳ (+-assoc m j k)) ⟧))
  ⊢-⊢-split {m} {n} j k W =
    ≅-sym (⊢-⊢ʷ j k W (+-assoc m j k) (+-assoc n j k))
    ⟶ subst₂W-conj (+-assoc m j k) (+-assoc n j k) ((W ⊢ʷ j) ⊢ʷ k)

  -- re-indexing a whiskering along an equation of the whiskering arity
  ⊣ʷ-idx : {x x' : ℕ} (e : x ≡ x') (W : Word m n)
    → Cong Cart (x ⊣ʷ W) (rn (castʳ (cong (_+ n) e)) ∷ ((x' ⊣ʷ W) ++ ⟦ rn (castʳ (sym (cong (_+ m) e))) ⟧))
  ⊣ʷ-idx refl W = insert-ids _

  ⊢ʷ-idx : {x x' : ℕ} (e : x ≡ x') (W : Word m n)
    → Cong Cart (W ⊢ʷ x) (rn (castʳ (cong (n +_) e)) ∷ ((W ⊢ʷ x') ++ ⟦ rn (castʳ (sym (cong (m +_) e))) ⟧))
  ⊢ʷ-idx refl W = insert-ids _

  -- whiskering a conjugated equation
  ⊣-map : ∀ a {Γ : Word m n} {Γ' : Word m' n'} {c : Ren n n'} {c' : Ren m' m}
    → Cong Cart Γ (rn c ∷ (Γ' ++ ⟦ rn c' ⟧))
    → Cong Cart (a ⊣ʷ Γ) (rn (idʳ {a} +ʳ c) ∷ ((a ⊣ʷ Γ') ++ ⟦ rn (idʳ {a} +ʳ c') ⟧))
  ⊣-map a {Γ' = Γ'} h = ⊣-stable a h ⟶ ≅-∷ (≅-≡ (⊣ʷ-++ a Γ' _))

  ⊢-map : ∀ k {Γ : Word m n} {Γ' : Word m' n'} {c : Ren n n'} {c' : Ren m' m}
    → Cong Cart Γ (rn c ∷ (Γ' ++ ⟦ rn c' ⟧))
    → Cong Cart (Γ ⊢ʷ k) (rn (c +ʳ idʳ {k}) ∷ ((Γ' ⊢ʷ k) ++ ⟦ rn (c' +ʳ idʳ {k}) ⟧))
  ⊢-map k {Γ' = Γ'} h = ⊢-stable k h ⟶ ≅-∷ (≅-≡ (⊢ʷ-++ Γ' _ k))

  -- cancelling runs of cast-like renaming steps
  cancel₂ : {r₁ : Ren n k} {r₂ : Ren k n} → IsCast (r₂ ∘ʳ r₁) → {Γ : Word m n}
    → Cong Cart (rn r₁ ∷ rn r₂ ∷ Γ) Γ
  cancel₂ h = rn-rn _ _ ⟶ ≅-cong {Γ₁ = ⟦ rn _ ⟧} (rn-isCast h) ≅-refl

  cancel₃ : {r₁ : Ren n k} {r₂ : Ren k j} {r₃ : Ren j n} → IsCast (r₃ ∘ʳ r₂ ∘ʳ r₁) → {Γ : Word m n}
    → Cong Cart (rn r₁ ∷ rn r₂ ∷ rn r₃ ∷ Γ) Γ
  cancel₃ h = rn-rn _ _ ⟶ cancel₂ h

  cancel₄ : {r₁ : Ren n k} {r₂ : Ren k j} {r₃ : Ren j a} {r₄ : Ren a n} → IsCast (r₄ ∘ʳ r₃ ∘ʳ r₂ ∘ʳ r₁) → {Γ : Word m n}
    → Cong Cart (rn r₁ ∷ rn r₂ ∷ rn r₃ ∷ rn r₄ ∷ Γ) Γ
  cancel₄ h = rn-rn _ _ ⟶ cancel₃ h

  cancel₅ : {r₁ : Ren n k} {r₂ : Ren k j} {r₃ : Ren j a} {r₄ : Ren a b} {r₅ : Ren b n}
    → IsCast (r₅ ∘ʳ r₄ ∘ʳ r₃ ∘ʳ r₂ ∘ʳ r₁) → {Γ : Word m n}
    → Cong Cart (rn r₁ ∷ rn r₂ ∷ rn r₃ ∷ rn r₄ ∷ rn r₅ ∷ Γ) Γ
  cancel₅ h = rn-rn _ _ ⟶ cancel₄ h

  -- two cast-conjugates of the same renaming are equal
  conj-cast-eq : {C C' : Ren a b} {X : Ren k a} {D D' : Ren n k}
    → IsCast C → IsCast C' → IsCast D → IsCast D' → (C ∘ʳ X ∘ʳ D) ≗ (C' ∘ʳ X ∘ʳ D')
  conj-cast-eq {C = C} {X = X} hC hC' hD hD' i = trans (cong (C ∘ʳ X) (isCast-unique hD hD' i)) (isCast-unique hC hC' _)

  ----------------------------------------------------------------------
  -- Closure of Δ-naturality under left whiskering:
  --   Δ_{a+n} ∘ (a ⊣ Z) ≈ ((a ⊣ Z) ⊢ (a+n)) ∘ ((a+m) ⊣ (a ⊣ Z)) ∘ Δ_{a+m}.
  -- Proof: expand Δ_{a+n} and Δ_{a+m} by the coherence identity; the
  -- factor Δ_a ⊢ n passes a ⊣ Z by centrality of renamings, the factor
  -- (a+a) ⊣ Δ_n passes (a+a) ⊣ Z by the hypothesis, the block shuffle
  -- a ⊣ σ_{a,n} ⊢ n passes the first copy of Z by the general
  -- naturality of σ (natLk) and the second copy by centrality.  All
  -- remaining steps are arity casts, which cancel.
  ----------------------------------------------------------------------

  ΔL : ∀ a {m n} (Z : Word m n) → ΔNat Z → ΔNat (a ⊣ʷ Z)
  ΔL a {m} {n} Z hZ =
    Δ-cohʷ a n
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (proj₁ (central-rn (Δʳ a) Z)))))
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-cong {Γ₁ = (a + a) ⊣ʷ (rn (Δʳ n) ∷ Z)} (⊣-stable (a + a) hZ) ≅-refl)))
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-≡ (cong (_++ ⟦ rn (Δʳ a +ʳ idʳ {m}) ⟧)
         (trans (⊣ʷ-++ (a + a) (Z ⊢ʷ n) _) (cong (X₁ ++_) (⊣ʷ-++ (a + a) (m ⊣ʷ Z) ⟦ rn (Δʳ m) ⟧)))))))
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-≡ (trans (++-assoc X₁ _ _) (trans (cong (X₁ ++_) (++-assoc X₂ _ _)) (sym (++-assoc X₁ X₂ SUF)))))))
    ⟶ ≅-cong {Γ₁ = CORE-L} core ≅-refl
    ⟶ ≅-≡ (trans (++-assoc V _ SUF) (cong (V ++_) (++-assoc V₂ _ SUF)))
    ⟶ ≅-cong {Γ₁ = V} ≅-refl (≅-cong {Γ₁ = V₂} ≅-refl (≅-sym (Δ-cohʷ a m)))
    where
      X₁ = (a + a) ⊣ʷ (Z ⊢ʷ n)
      X₂ = (a + a) ⊣ʷ (m ⊣ʷ Z)
      SUF = rn (idʳ {a + a} +ʳ Δʳ m) ∷ ⟦ rn (Δʳ a +ʳ idʳ {m}) ⟧
      V = (a ⊣ʷ Z) ⊢ʷ (a + n)
      V₂ = (a + m) ⊣ʷ (a ⊣ʷ Z)
      W₁ = a ⊣ʷ ((Z ⊢ʷ a) ⊢ʷ n)
      W₁' = a ⊣ʷ ((a ⊣ʷ Z) ⊢ʷ n)
      W₂ = a ⊣ʷ ((a + m) ⊣ʷ Z)
      W₃ = a ⊣ʷ ((m + a) ⊣ʷ Z)
      e = sym (+-assoc a m a)
      CORE-L = rn (castʳ (E₀ a n)) ∷ rn (Sh a n) ∷ rn (castʳ (E₁ a n)) ∷ (X₁ ++ X₂)
      CORE-R = V ++ (V₂ ++ (rn (castʳ (E₀ a m)) ∷ rn (Sh a m) ∷ ⟦ rn (castʳ (E₁ a m)) ⟧))

      core : Cong Cart CORE-L CORE-R
      core =
        -- (a+a) ⊣ (Z ⊢ n) = casts ∘ a ⊣ ((a ⊣ Z) ⊢ n) ∘ casts
        ≅-∷ (≅-∷ (≅-∷ (≅-cong (⊣-⊣-split a a (Z ⊢ʷ n) ⟶ ≅-∷ (≅-cong (⊣-map a (⊣-⊢-split a n Z)) ≅-refl)) ≅-refl)))
        ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-≡ (trans (++-assoc (W₁' ++ _) _ _) (++-assoc W₁' _ _)))))))
        ⟶ ≅-∷ (≅-∷ (cancel₃ (∘ʳ-isCast' _ _ (id+ʳ-isCast a (sym (+-assoc a n n)) (castʳ-isCast _))
                                          (∘ʳ-isCast' _ _ (castʳ-isCast (+-assoc a a (n + n))) (castʳ-isCast (E₁ a n))))))
        -- the shuffle passes the first copy of Z (general naturality of σ)
        ⟶ ≅-∷ (≅-cong {Γ₁ = a ⊣ʷ ((rn (σʳ n a) ∷ (a ⊣ʷ Z)) ⊢ʷ n)} (⊣-stable a (⊢-stable n (natLk a Z))) ≅-refl)
        ⟶ ≅-∷ (≅-cong (≅-≡ (trans (cong (a ⊣ʷ_) (⊢ʷ-++ (Z ⊢ʷ a) ⟦ rn (σʳ m a) ⟧ n)) (⊣ʷ-++ a ((Z ⊢ʷ a) ⊢ʷ n) _))) ≅-refl)
        ⟶ ≅-∷ (≅-≡ (++-assoc W₁ ⟦ rn (idʳ {a} +ʳ (σʳ m a +ʳ idʳ {n})) ⟧ _))
        -- (a+a) ⊣ (m ⊣ Z) = casts ∘ a ⊣ ((a+m) ⊣ Z) ∘ casts
        ⟶ ≅-∷ (≅-cong {Γ₁ = W₁} ≅-refl (≅-∷ (≅-∷ (≅-∷ (⊣-⊣-split a a (m ⊣ʷ Z) ⟶ ≅-∷ (≅-cong (⊣-map a (⊣-⊣-merge a m Z)) ≅-refl) ⟶ ≅-∷ (≅-∷ (≅-≡ (++-assoc W₂ _ _))))))))
        ⟶ ≅-∷ (≅-cong {Γ₁ = W₁} ≅-refl (≅-∷ (cancel₄ (∘ʳ-isCast' _ _ (id+ʳ-isCast a (sym (+-assoc a m n)) (castʳ-isCast _))
                                              (∘ʳ-isCast' _ _ (castʳ-isCast (+-assoc a a (m + n)))
                                              (∘ʳ-isCast' _ _ (castʳ-isCast (sym (+-assoc a a (m + n)))) (id+ʳ-isCast a (+-assoc a m n) (castʳ-isCast _))))))))
        -- the shuffle passes the second copy of Z (centrality of renamings)
        ⟶ ≅-∷ (≅-cong {Γ₁ = W₁} ≅-refl (≅-cong {Γ₁ = a ⊣ʷ ((σʷ a m ⊢ʷ n) ++ ((a + m) ⊣ʷ Z))} (⊣-stable a (proj₁ (central-rn (σʳ m a) Z))) ≅-refl))
        ⟶ ≅-∷ (≅-cong {Γ₁ = W₁} ≅-refl (≅-cong (≅-≡ (⊣ʷ-++ a ((m + a) ⊣ʷ Z) _)) ≅-refl))
        ⟶ ≅-∷ (≅-cong {Γ₁ = W₁} ≅-refl (≅-≡ (++-assoc W₃ ⟦ rn (Sh a m) ⟧ _)))
        -- a ⊣ ((Z ⊢ a) ⊢ n) = casts ∘ (a ⊣ Z) ⊢ (a+n) ∘ casts
        ⟶ ≅-∷ (≅-cong (⊣-map a (⊢-⊢-conj a n Z) ⟶ ≅-∷ (≅-cong (⊣-⊢-split a (a + n) Z) ≅-refl)) ≅-refl)
        ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-≡ (trans (++-assoc (V ++ _) _ _) (++-assoc V _ _)))))
        ⟶ cancel₃ (∘ʳ-isCast' _ _ (castʳ-isCast (sym (+-assoc a n (a + n))))
                     (∘ʳ-isCast' _ _ (id+ʳ-isCast a (+-assoc n a n) (castʳ-isCast _)) (castʳ-isCast (E₀ a n))))
        -- a ⊣ ((m+a) ⊣ Z) = casts ∘ (a+m) ⊣ (a ⊣ Z) ∘ casts
        ⟶ ≅-cong {Γ₁ = V} ≅-refl (≅-∷ (≅-∷ (≅-cong
             ( ⊣-⊣-merge a (m + a) Z
             ⟶ ≅-∷ (≅-cong (⊣ʷ-idx e Z ⟶ ≅-∷ (≅-cong (⊣-⊣-split (a + m) a Z) ≅-refl) ⟶ ≅-∷ (≅-∷ (≅-≡ (++-assoc V₂ _ _)))) ≅-refl)
             ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-≡ (++-assoc V₂ _ _)))) ) ≅-refl)))
        ⟶ ≅-cong {Γ₁ = V} ≅-refl (≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-≡ (++-assoc V₂ _ _)))))))
        ⟶ ≅-cong {Γ₁ = V} ≅-refl (cancel₅ (∘ʳ-isCast' _ _ (castʳ-isCast (+-assoc (a + m) a n))
                                          (∘ʳ-isCast' _ _ (castʳ-isCast (cong (_+ n) e))
                                          (∘ʳ-isCast' _ _ (castʳ-isCast (sym (+-assoc a (m + a) n)))
                                          (∘ʳ-isCast' _ _ (id+ʳ-isCast a (sym (+-assoc m a n)) (castʳ-isCast (sym (+-assoc m a n)))) (castʳ-isCast (+-assoc a m (a + n))))))))
        -- the residual casts around the shuffle
        ⟶ ≅-cong {Γ₁ = V} ≅-refl (≅-cong {Γ₁ = V₂} ≅-refl
             ( rn-rn _ _ ⟶ rn-rn _ _
             ⟶ ≅-∷ (≅-∷ (rn-rn _ _))
             ⟶ ≅-∷ˡ (rn-isCast-unique (∘ʳ-isCast' _ _ (castʳ-isCast (+-assoc a (m + a) m))
                                          (∘ʳ-isCast' _ _ (castʳ-isCast (sym (cong (_+ m) e))) (castʳ-isCast (sym (+-assoc (a + m) a m)))))
                                       (castʳ-isCast (E₀ a m)))
             ⟶ ≅-∷ (≅-∷ (rn-isCast-unique (∘ʳ-isCast' _ _ (castʳ-isCast (sym (+-assoc a a (m + m)))) (id+ʳ-isCast a (+-assoc a m m) (castʳ-isCast (+-assoc a m m))))
                                          (castʳ-isCast (E₁ a m))))))

  ----------------------------------------------------------------------
  -- Closure of Δ-naturality under right whiskering:
  --   Δ_{n+b} ∘ (Z ⊢ b) ≈ ((Z ⊢ b) ⊢ (n+b)) ∘ ((m+b) ⊣ (Z ⊢ b)) ∘ Δ_{m+b}.
  -- Same pattern as ΔL: Δ_n ⊢ b meets Z ⊢ b directly (hypothesis),
  -- (n+n) ⊣ Δ_b passes both copies of Z by centrality of renamings,
  -- the shuffle n ⊣ σ_{n,b} ⊢ b passes the first copy by centrality and
  -- the second by the mirror naturality of σ (natRk).
  ----------------------------------------------------------------------

  ΔR : ∀ b {m n} (Z : Word m n) → ΔNat Z → ΔNat (Z ⊢ʷ b)
  ΔR b {m} {n} Z hZ =
    Δ-cohʷ n b
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (⊢-stable b hZ))))
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-≡ (trans (⊢ʷ-++ (Z ⊢ʷ n) _ b) (cong (((Z ⊢ʷ n) ⊢ʷ b) ++_) (⊢ʷ-++ (m ⊣ʷ Z) ⟦ rn (Δʳ m) ⟧ b)))))))
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-cong {Γ₁ = ((n + n) ⊣ʷ Δʷ b) ++ ((Z ⊢ʷ n) ⊢ʷ b)} (≅-sym (proj₂ (central-rn (Δʳ b) (Z ⊢ʷ n)))) ≅-refl)))
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-≡ (++-assoc Y₁ _ _))))
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-cong {Γ₁ = Y₁} ≅-refl (≅-cong {Γ₁ = ((m + n) ⊣ʷ Δʷ b) ++ ((m ⊣ʷ Z) ⊢ʷ b)} (≅-sym (proj₂ (central-rn (Δʳ b) (m ⊣ʷ Z)))) ≅-refl))))
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-cong {Γ₁ = Y₁} ≅-refl (≅-≡ (++-assoc Y₂ _ _)))))
    ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-≡ (sym (++-assoc Y₁ Y₂ SUF)))))
    ⟶ ≅-cong {Γ₁ = CORE-L} core ≅-refl
    ⟶ ≅-≡ (trans (++-assoc V _ SUF) (cong (V ++_) (++-assoc V₂ _ SUF)))
    ⟶ ≅-cong {Γ₁ = V} ≅-refl (≅-cong {Γ₁ = V₂} ≅-refl (≅-sym (Δ-cohʷ m b)))
    where
      Δʷ : ∀ x → Word x (x + x)
      Δʷ x = ⟦ rn (Δʳ x) ⟧
      Y₁ = (Z ⊢ʷ n) ⊢ʷ (b + b)
      Y₂ = (m ⊣ʷ Z) ⊢ʷ (b + b)
      SUF = rn (idʳ {m + m} +ʳ Δʳ b) ∷ ⟦ rn (Δʳ m +ʳ idʳ {b}) ⟧
      V = (Z ⊢ʷ b) ⊢ʷ (n + b)
      V₂ = (m + b) ⊣ʷ (Z ⊢ʷ b)
      U = Z ⊢ʷ ((n + b) + b)
      U' = Z ⊢ʷ ((b + n) + b)
      Y₃ = m ⊣ʷ ((Z ⊢ʷ b) ⊢ʷ b)
      Y₄ = m ⊣ʷ ((b ⊣ʷ Z) ⊢ʷ b)
      e₁ : n + (b + b) ≡ (n + b) + b
      e₁ = sym (+-assoc n b b)
      e₂ : (b + n) + b ≡ b + (n + b)
      e₂ = +-assoc b n b
      CORE-L = rn (castʳ (E₀ n b)) ∷ rn (Sh n b) ∷ rn (castʳ (E₁ n b)) ∷ (Y₁ ++ Y₂)
      CORE-R = V ++ (V₂ ++ (rn (castʳ (E₀ m b)) ∷ rn (Sh m b) ∷ ⟦ rn (castʳ (E₁ m b)) ⟧))

      core : Cong Cart CORE-L CORE-R
      core =
        -- (Z ⊢ n) ⊢ (b+b) = casts ∘ Z ⊢ ((n+b)+b) ∘ casts
        ≅-∷ (≅-∷ (≅-∷ (≅-cong (⊢-⊢-conj n (b + b) Z ⟶ ≅-∷ (≅-cong (⊢ʷ-idx e₁ Z) ≅-refl)) ≅-refl)))
        ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-≡ (trans (++-assoc (U ++ _) _ _) (++-assoc U _ _)))))))
        ⟶ ≅-∷ (≅-∷ (cancel₃ (∘ʳ-isCast' _ _ (castʳ-isCast (cong (n +_) e₁))
                                (∘ʳ-isCast' _ _ (castʳ-isCast (+-assoc n n (b + b))) (castʳ-isCast (E₁ n b))))))
        -- the shuffle passes the first copy of Z (centrality of renamings)
        ⟶ ≅-∷ (≅-cong {Γ₁ = (n ⊣ʷ ⟦ rn (σʳ b n +ʳ idʳ {b}) ⟧) ++ U} (≅-sym (proj₂ (central-rn (σʳ b n +ʳ idʳ {b}) Z))) ≅-refl)
        ⟶ ≅-∷ (≅-≡ (++-assoc U' _ _))
        -- (m ⊣ Z) ⊢ (b+b) = casts ∘ m ⊣ ((Z ⊢ b) ⊢ b) ∘ casts
        ⟶ ≅-∷ (≅-cong {Γ₁ = U'} ≅-refl (≅-∷ (≅-∷ (≅-∷ (⊣-⊢-merge m (b + b) Z ⟶ ≅-∷ (≅-cong (⊣-map m (⊢-⊢-split b b Z)) ≅-refl) ⟶ ≅-∷ (≅-∷ (≅-≡ (++-assoc Y₃ _ _))))))))
        ⟶ ≅-∷ (≅-cong {Γ₁ = U'} ≅-refl (≅-∷ (cancel₄ (∘ʳ-isCast' _ _ (id+ʳ-isCast m (sym (+-assoc n b b)) (castʳ-isCast (sym (+-assoc n b b))))
                                             (∘ʳ-isCast' _ _ (castʳ-isCast (+-assoc m n (b + b)))
                                             (∘ʳ-isCast' _ _ (castʳ-isCast (sym (+-assoc m n (b + b)))) (castʳ-isCast (sym (cong (m +_) e₁)))))))))
        -- the shuffle passes the second copy of Z (mirror naturality of σ)
        ⟶ ≅-∷ (≅-cong {Γ₁ = U'} ≅-refl (≅-cong {Γ₁ = m ⊣ʷ ((rn (σʳ b n) ∷ (Z ⊢ʷ b)) ⊢ʷ b)} (⊣-stable m (⊢-stable b (natRk b Z))) ≅-refl))
        ⟶ ≅-∷ (≅-cong {Γ₁ = U'} ≅-refl (≅-cong (≅-≡ (trans (cong (m ⊣ʷ_) (⊢ʷ-++ (b ⊣ʷ Z) ⟦ rn (σʳ b m) ⟧ b)) (⊣ʷ-++ m ((b ⊣ʷ Z) ⊢ʷ b) _))) ≅-refl))
        ⟶ ≅-∷ (≅-cong {Γ₁ = U'} ≅-refl (≅-≡ (++-assoc Y₄ ⟦ rn (Sh m b) ⟧ _)))
        -- Z ⊢ ((b+n)+b) = casts ∘ (Z ⊢ b) ⊢ (n+b) ∘ casts
        ⟶ ≅-∷ (≅-cong (⊢ʷ-idx e₂ Z ⟶ ≅-∷ (≅-cong (⊢-⊢-split b (n + b) Z) ≅-refl)) ≅-refl)
        ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-≡ (trans (++-assoc (V ++ _) _ _) (++-assoc V _ _)))))
        ⟶ cancel₃ (∘ʳ-isCast' _ _ (castʳ-isCast (sym (+-assoc n b (n + b))))
                     (∘ʳ-isCast' _ _ (castʳ-isCast (cong (n +_) e₂)) (castʳ-isCast (E₀ n b))))
        -- m ⊣ ((b ⊣ Z) ⊢ b) = casts ∘ (m+b) ⊣ (Z ⊢ b) ∘ casts
        ⟶ ≅-cong {Γ₁ = V} ≅-refl (≅-∷ (≅-∷ (≅-cong
             ( ⊣-map m (⊣-⊢-merge b b Z)
             ⟶ ≅-∷ (≅-cong (⊣-⊣-merge m b (Z ⊢ʷ b)) ≅-refl)
             ⟶ ≅-∷ (≅-∷ (≅-≡ (++-assoc V₂ _ _))) ) ≅-refl)))
        ⟶ ≅-cong {Γ₁ = V} ≅-refl (≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-≡ (++-assoc V₂ _ _))))))
        ⟶ ≅-cong {Γ₁ = V} ≅-refl (cancel₄ (∘ʳ-isCast' _ _ (castʳ-isCast (sym (+-assoc m b (n + b))))
                                          (∘ʳ-isCast' _ _ (id+ʳ-isCast m (+-assoc b n b) (castʳ-isCast (+-assoc b n b)))
                                          (∘ʳ-isCast' _ _ (castʳ-isCast (sym (cong (m +_) e₂))) (castʳ-isCast (+-assoc m b (n + b)))))))
        -- the residual casts around the shuffle
        ⟶ ≅-cong {Γ₁ = V} ≅-refl (≅-cong {Γ₁ = V₂} ≅-refl
             ( rn-rn _ _
             ⟶ ≅-∷ (≅-∷ (rn-rn _ _))
             ⟶ ≅-∷ˡ (rn-isCast-unique (∘ʳ-isCast' _ _ (id+ʳ-isCast m (sym (+-assoc b m b)) (castʳ-isCast (sym (+-assoc b m b)))) (castʳ-isCast (+-assoc m b (m + b))))
                                       (castʳ-isCast (E₀ m b)))
             ⟶ ≅-∷ (≅-∷ (rn-isCast-unique (∘ʳ-isCast' _ _ (castʳ-isCast (sym (+-assoc m m (b + b)))) (id+ʳ-isCast m (+-assoc m b b) (castʳ-isCast (+-assoc m b b))))
                                          (castʳ-isCast (E₁ m b))))))

  ----------------------------------------------------------------------
  -- The base case: the step {0 ⊣ g ⊢ 0}, by rule (C) of Fig. 3.
  ----------------------------------------------------------------------

  -- {0 ⊣ g ⊢ 0} with source arity kg on the nose
  s₀ : ∀ {kg} (g : Op kg) → Step kg 1
  s₀ {kg} g = ins 0 0 (sym (+-identityʳ kg)) refl g

  ΔNat-s₀ : ∀ {kg} (g : Op kg) → Cart g → ΔNat ⟦ s₀ g ⟧
  ΔNat-s₀ {kg} g c =
    ≅-∷ (S∙ 0 0 p₀ refl g)
    ⟶ ≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)
    ⟶ ≅-∷ˡ (E∙ (λ i → sym (+ʳ-zero (Δʳ 1) refl refl i)))
    ⟶ ≅-cong (C∙ 0 0 g c refl (+-assoc kg kg 0)) ≅-refl
    ⟶ ≅-∷ (≅-∷ (R∙ _ _))
    ⟶ ≅-∷ (≅-∷ (E∙ (+ʳ-zero (Δʳ kg) (+-identityʳ (kg + kg)) (sym p₀))))
    ⟶ ≅-∷ (≅-∷ (≅-sym (R∙ _ _)))
    ⟶ ≅-sym RHS
    where
      p₀ : kg ≡ 0 + (kg + 0)
      p₀ = sym (+-identityʳ kg)
      P' : kg + kg ≡ kg + (kg + 0)
      P' = cong (kg +_) (sym (+-identityʳ kg))
      RHS : Cong Cart ((⟦ s₀ g ⟧ ⊢ʷ 1) ++ ((kg ⊣ʷ ⟦ s₀ g ⟧) ++ ⟦ rn (Δʳ kg) ⟧))
                      (sub! 0 1 g ∷ ins kg 0 (+-assoc kg kg 0) refl g ∷ rn (castʳ (+-identityʳ (kg + kg))) ∷ ⟦ rn (Δʳ kg) ⟧)
      RHS = ≅-cong (S∙ 0 1 (Rp 0 kg 0 1 p₀) (Rq 0 0 1 refl) g) ≅-refl
          ⟶ ≅-cong {Γ₁ = ⟦ rn (castʳ (Rq 0 0 1 refl)) ⟧} (rn-isCast (castʳ-isCast _)) ≅-refl
          ⟶ ≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ (sym (Rp 0 kg 0 1 p₀))) ⟧} (rn-isCast (castʳ-isCast _)) ≅-refl)
          ⟶ ≅-∷ (≅-cong (ins-arity (+-identityʳ kg) refl (Lp kg 0 p₀) P' (Lp kg 0 refl) refl g) ≅-refl)
          ⟶ ≅-∷ (≅-cong (≅-sym (ins-conjʳ kg 0 (+-assoc kg kg 0) refl P' g (castʳ-isCast (+-identityʳ (kg + kg))))) ≅-refl)

  ----------------------------------------------------------------------
  -- Δ-naturality for every substitution step and every word of Sub×
  ----------------------------------------------------------------------

  -- {n₁ ⊣ g ⊢ n₂} = n₁ ⊣ ({0 ⊣ g ⊢ 0} ⊢ n₂)
  ΔNat-sub! : ∀ n₁ n₂ {kg} (g : Op kg) → Cart g → ΔNat ⟦ sub! n₁ n₂ g ⟧
  ΔNat-sub! n₁ n₂ {kg} g c =
    ΔNat-≅ (ins-arity (+-identityʳ n₁) refl _ refl _ refl g)
           (ΔL n₁ (⟦ s₀ g ⟧ ⊢ʷ n₂) (ΔR n₂ ⟦ s₀ g ⟧ (ΔNat-s₀ g c)))

  -- a step with arity proofs is the on-the-nose step conjugated by casts
  ΔNat-ins : ∀ n₁ n₂ {kg k k'} (p : k ≡ n₁ + (kg + n₂)) (q : k' ≡ n₁ + suc n₂) (g : Op kg) → Cart g
    → ΔNat ⟦ ins n₁ n₂ p q g ⟧
  ΔNat-ins n₁ n₂ p q g c =
    ΔNat-≅ (≅-sym (S∙ n₁ n₂ p q g))
      (ΔNat-++ {Γ₁ = ⟦ rn (castʳ q) ⟧} (ΔNat-rn _)
        (ΔNat-++ {Γ₁ = ⟦ sub! n₁ n₂ g ⟧} (ΔNat-sub! n₁ n₂ g c) (ΔNat-rn _) (central-rn _))
        (central-word _ (c , tt)))

  ΔNat-word : (Γ : Word m n) → AllCart {Cart = Cart} Γ → ΔNat Γ
  ΔNat-word ε _ = ΔNat-ε
  ΔNat-word (rn r ∷ Γ) a = ΔNat-++ {Γ₁ = ⟦ rn r ⟧} (ΔNat-rn r) (ΔNat-word Γ a) (central-word Γ a)
  ΔNat-word (ins n₁ n₂ p q g ∷ Γ) (c , a) =
    ΔNat-++ {Γ₁ = ⟦ ins n₁ n₂ p q g ⟧} (ΔNat-ins n₁ n₂ p q g c) (ΔNat-word Γ a) (central-word Γ a)

------------------------------------------------------------------------
-- Proposition 3.14(ii): Sub×_𝕍 is a cartesian PROP.
--
-- The cartesian congruence is `Cong (λ _ → ⊤)`: every substitution
-- step is subject to the cartesian rules.  ρ r := [r]; the functor
-- laws of ρ are the rules (E), (U₂), (R) and the block-sum law of
-- renamings; all morphisms are central (MFPS.SubCentral); Δ and ! are
-- natural by the results above.
------------------------------------------------------------------------

allCart : (Γ : Word m n) → AllCart {Cart = λ _ → ⊤} Γ
allCart ε = tt
allCart (rn r ∷ Γ) = allCart Γ
allCart (ins _ _ _ _ _ ∷ Γ) = tt , allCart Γ

Sub×PROP : CartesianPROP
Sub×PROP = record
  { P      = SubPrePROP (λ _ → ⊤)
  ; prop   = λ Γ → central-word Γ (allCart Γ)
  ; ρ      = λ r → ⟦ rn r ⟧
  ; ρ-cong = E∙
  ; ρ-id   = U₂∙
  ; ρ-∘    = λ r s → ≅-sym (R∙ r s)
  ; ρ-+    = λ r s → ≅-trans (E∙ (+ʳ-∘ idʳ r s idʳ)) (≅-sym (R∙ _ _))
  ; ρ-σ    = ≅-refl
  ; Δ-nat  = λ {m} {n} Γ → ≅-trans (ΔNat-word Γ (allCart Γ)) (≅-≡ (sym (++-assoc (Γ ⊢ʷ n) (m ⊣ʷ Γ) _)))
  ; !-nat  = λ Γ → !-nat Γ (allCart Γ)
  }
