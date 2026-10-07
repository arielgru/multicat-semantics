------------------------------------------------------------------------
-- Tupling in the substitution PROP, and the iterated single
-- substitution `plug` of Def. 4.4 as a word.
--
-- For operations g₁,…,gₖ ∈ ℂ(n) the word
--     ⟨g₁,…,gₖ⟩ := ({g₁} ⊢ k-1) ∘ (n ⊣ ⟨g₂,…,gₖ⟩) ∘ Δₙ  :  n → k
-- (⟨⟩ := !ₙ) is the tuple of the gᵢ in the sense of a cartesian PROP.
-- Its naturality  ⟨g₁ ⋆ Γ, …, gₖ ⋆ Γ⟩ ≅ ⟨g₁,…,gₖ⟩ ∘ Γ  follows from the
-- naturality of the unit {−} (Thm. 3.18), centrality and the
-- naturality of Δ (Prop. 3.14(ii)).  The interpretation of a k-ary
-- term former in Def. 4.4 is `plug 0 f gs [Δᵏ]`; here we show that this
-- is f ⋆ ⟨gs⟩, which is what makes the substitution lemma (Lemma 4.5)
-- a consequence of the PROP-level naturality results.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.SubTuple (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊
open import MFPS.Sub 𝕊
open import MFPS.SubSound 𝕊 using (CartRules; module Soundness)
open import MFPS.SubCast 𝕊
open import MFPS.SubWhisker 𝕊 using (⊣-stable; ⊢-stable; ⊣-assoc)
open import MFPS.SubSym 𝕊 using (_⟶_)
open import MFPS.SubCentral 𝕊 using (AllCart; central-word; Eq₁)
open import MFPS.SubCartesian 𝕊 using (ΔNat-word; !-nat; ⊣-⊣-merge)
open import MFPS.SubPROP 𝕊 using (0⊣ʷ)
open import MFPS.Representable 𝕊 using (ηʷ; η-cong; η-nat; η-ren; η-id)

private
  variable
    j k m n : ℕ

------------------------------------------------------------------------
-- the tuple word
------------------------------------------------------------------------

tupleʷ : (Fin k → Op n) → Word n k
tupleʷ {zero}  {n} gs = ⟦ rn (!ʳ n) ⟧
tupleʷ {suc k} {n} gs = (ηʷ (gs zero) ⊢ʷ k) ++ ((n ⊣ʷ tupleʷ (gs ∘ suc)) ++ ⟦ rn (Δʳ n) ⟧)

-- all steps of a tuple are substitution steps of its components, or renamings
AllCart-++ : ∀ {Cart : ∀ {n} → Op n → Set} (Γ₁ : Word k n) (Γ₂ : Word m k)
  → AllCart {Cart = Cart} Γ₁ → AllCart {Cart = Cart} Γ₂ → AllCart {Cart = Cart} (Γ₁ ++ Γ₂)
AllCart-++ ε Γ₂ _ a₂ = a₂
AllCart-++ (ins _ _ _ _ _ ∷ Γ₁) Γ₂ (c , a₁) a₂ = c , AllCart-++ Γ₁ Γ₂ a₁ a₂
AllCart-++ (rn _ ∷ Γ₁) Γ₂ a₁ a₂ = AllCart-++ Γ₁ Γ₂ a₁ a₂

AllCart-⊣ : ∀ {Cart : ∀ {n} → Op n → Set} k (Γ : Word m n) → AllCart {Cart = Cart} Γ → AllCart {Cart = Cart} (k ⊣ʷ Γ)
AllCart-⊣ k ε a = a
AllCart-⊣ k (ins _ _ _ _ _ ∷ Γ) (c , a) = c , AllCart-⊣ k Γ a
AllCart-⊣ k (rn _ ∷ Γ) a = AllCart-⊣ k Γ a

AllCart-⊢ : ∀ {Cart : ∀ {n} → Op n → Set} k (Γ : Word m n) → AllCart {Cart = Cart} Γ → AllCart {Cart = Cart} (Γ ⊢ʷ k)
AllCart-⊢ k ε a = a
AllCart-⊢ k (ins _ _ _ _ _ ∷ Γ) (c , a) = c , AllCart-⊢ k Γ a
AllCart-⊢ k (rn _ ∷ Γ) a = AllCart-⊢ k Γ a

AllCart-tuple : ∀ {Cart : ∀ {n} → Op n → Set} (gs : Fin k → Op n) → (∀ i → Cart (gs i)) → AllCart {Cart = Cart} (tupleʷ gs)
AllCart-tuple {zero} gs c = tt
AllCart-tuple {suc k} {n} gs c =
  AllCart-++ (ηʷ (gs zero) ⊢ʷ k) ((n ⊣ʷ tupleʷ (gs ∘ suc)) ++ ⟦ rn (Δʳ n) ⟧) (c zero , tt)
    (AllCart-++ (n ⊣ʷ tupleʷ (gs ∘ suc)) ⟦ rn (Δʳ n) ⟧ (AllCart-⊣ n (tupleʷ (gs ∘ suc)) (AllCart-tuple (gs ∘ suc) (c ∘ suc))) tt)

module _ {Cart : ∀ {n} → Op n → Set} where

  tuple-cong : {gs gs' : Fin k → Op n} → (∀ i → gs i ≈ gs' i) → Cong Cart (tupleʷ gs) (tupleʷ gs')
  tuple-cong {zero} h = ≅-refl
  tuple-cong {suc k} {n} h =
    ≅-cong (⊢-stable k (η-cong (h zero))) (≅-cong (⊣-stable n (tuple-cong (h ∘ suc))) ≅-refl)

  ----------------------------------------------------------------------
  -- the tuple of projections ⟨id[pt r 1], …, id[pt r k]⟩ is the renaming
  -- step [r]  (used for the symbol assignments in Thm. 4.9)
  ----------------------------------------------------------------------

  tuple-pt : (r : Ren k n) → Cong Cart (tupleʷ (λ i → idₒ [ ptʳ (r i) ])) ⟦ rn r ⟧
  tuple-pt {zero}  r = E∙ (λ ())
  tuple-pt {suc k} {n} r =
    ≅-cong (⊢-stable k (η-ren idₒ (ptʳ (r zero)) ⟶ ≅-cong η-id ≅-refl))
           (≅-cong (⊣-stable n (tuple-pt (r ∘ suc))) ≅-refl)
    ⟶ rn-rn _ _
    ⟶ rn-rn _ _
    ⟶ ≅-∷ˡ (E∙ total)
    where
      total : (Δʳ n ∘ʳ (idʳ {n} +ʳ (r ∘ suc)) ∘ʳ (ptʳ (r zero) +ʳ idʳ {k})) ≗ r
      total zero = trans (cong (Δʳ n ∘ʳ (idʳ {n} +ʳ (r ∘ suc))) (+ʳ-inj₁ (ptʳ (r zero)) (idʳ {k}) zero))
                   (trans (cong (Δʳ n) (+ʳ-inj₁ (idʳ {n}) (r ∘ suc) (r zero))) ([,]ʳ-inl idʳ idʳ (r zero)))
      total (suc j) = trans (cong (Δʳ n ∘ʳ (idʳ {n} +ʳ (r ∘ suc))) (+ʳ-inj₂ (ptʳ (r zero)) (idʳ {k}) j))
                      (trans (cong (Δʳ n) (+ʳ-inj₂ (idʳ {n}) (r ∘ suc) j)) ([,]ʳ-inr idʳ idʳ (r (suc j))))

  ----------------------------------------------------------------------
  -- naturality:  ⟨gs ⋆ Γ⟩ ≅ ⟨gs⟩ ∘ Γ   for a word Γ all of whose
  -- substitution steps are cartesian (so that Γ is central and Δ,! are
  -- natural against it)
  ----------------------------------------------------------------------

  tuple-nat : (gs : Fin k → Op n) (Γ : Word m n) → AllCart {Cart = Cart} Γ
    → Cong Cart (tupleʷ (λ i → gs i ⋆ Γ)) (tupleʷ gs ++ Γ)
  tuple-nat {zero} gs Γ a = ≅-sym (!-nat Γ a)
  tuple-nat {suc k} {n} {m} gs Γ a =
    ≅-cong (⊢-stable k (η-nat (gs zero) Γ)) (≅-cong (⊣-stable m (tuple-nat (gs ∘ suc) Γ a)) ≅-refl)
    ⟶ ≅-≡ (cong₂ _++_ (⊢ʷ-++ (ηʷ (gs zero)) Γ k) (cong (_++ ⟦ rn (Δʳ m) ⟧) (⊣ʷ-++ m T Γ)))
    ⟶ ≅-≡ (trans (++-assoc H (Γ ⊢ʷ k) _) (cong (H ++_) (trans (sym (++-assoc (Γ ⊢ʷ k) _ _)) (cong (_++ _) (sym (++-assoc (Γ ⊢ʷ k) (m ⊣ʷ T) (m ⊣ʷ Γ)))))))
    ⟶ ≅-cong {Γ₁ = H} ≅-refl (≅-cong (≅-cong (proj₁ (central-word Γ a T)) ≅-refl) ≅-refl)
    ⟶ ≅-cong {Γ₁ = H} ≅-refl (≅-≡ (trans (++-assoc ((n ⊣ʷ T) ++ (Γ ⊢ʷ n)) (m ⊣ʷ Γ) ⟦ rn (Δʳ m) ⟧) (++-assoc (n ⊣ʷ T) (Γ ⊢ʷ n) ((m ⊣ʷ Γ) ++ ⟦ rn (Δʳ m) ⟧))))
    ⟶ ≅-cong {Γ₁ = H} ≅-refl (≅-cong {Γ₁ = n ⊣ʷ T} ≅-refl (≅-sym (ΔNat-word Γ a)))
    ⟶ ≅-≡ (sym (trans (++-assoc H _ Γ) (cong (H ++_) (++-assoc (n ⊣ʷ T) ⟦ rn (Δʳ n) ⟧ Γ))))
    where
      H = ηʷ (gs zero) ⊢ʷ k
      T = tupleʷ (gs ∘ suc)

  ----------------------------------------------------------------------
  -- Def. 4.4's `plug` as a word:  plug off f gs [id_off + Δᵏ] ≈ f ⋆ (off ⊣ ⟨gs⟩)
  ----------------------------------------------------------------------

  -- Δᵏ (1+k) = Δ ∘ (id + Δᵏ k)
  Δᵏ-suc : ∀ k n → Δᵏ (suc k) n ≗ (Δʳ n ∘ʳ (idʳ {n} +ʳ Δᵏ k n))
  Δᵏ-suc k n = Fin+-ext
    (λ j → trans ([,]ʳ-inl idʳ (Δᵏ k n) j) (sym (trans (cong (Δʳ n) (+ʳ-inj₁ idʳ (Δᵏ k n) j)) ([,]ʳ-inl idʳ idʳ j))))
    (λ j → trans ([,]ʳ-inr idʳ (Δᵏ k n) j) (sym (trans (cong (Δʳ n) (+ʳ-inj₂ idʳ (Δᵏ k n) j)) ([,]ʳ-inr idʳ idʳ _))))

  module _ (rules : CartRules Cart) where
    open Soundness rules

    plug-tuple : ∀ off (F : Op (off + k)) (gs : Fin k → Op n)
      → (plug off F gs) [ idʳ {off} +ʳ Δᵏ k n ] ≈ F ⋆ (off ⊣ʷ tupleʷ gs)
    plug-tuple {zero} off F gs = ren-cong ≈.refl (+ʳ-cong {r = idʳ {off}} (λ _ → refl) (λ ()))
    plug-tuple {suc k} {n} off F gs =
      ≈.trans (ren-cong (subst-ren A X) (λ _ → refl))
      (≈.trans (≈.sym (ren-∘ X (castʳ A) (idʳ {off} +ʳ Δᵏ (suc k) n)))
      (≈.trans (ren-cong ≈.refl total)
      (≈.trans (ren-∘ X (idʳ {off + n} +ʳ Δᵏ k n) ((idʳ {off} +ʳ Δʳ n) ∘ʳ castʳ A'))
      (≈.trans (ren-cong (plug-tuple (off + n) F' (gs ∘ suc)) (λ _ → refl))
      (≈.trans (≈.reflexive (sym (⋆-++ F' ((off + n) ⊣ʷ T') ⟦ rn ((idʳ {off} +ʳ Δʳ n) ∘ʳ castʳ A') ⟧)))
      (≈.trans (⋆-cong (subst-ren B (F ⟨ off ⊣ gs zero ⊢ k ⟩)) (((off + n) ⊣ʷ T') ++ ⟦ rn ((idʳ {off} +ʳ Δʳ n) ∘ʳ castʳ A') ⟧))
      (≈.trans (≈.reflexive (sym (⋆-++ F (sub! off k (gs zero) ∷ ⟦ rn (castʳ B) ⟧) (((off + n) ⊣ʷ T') ++ ⟦ rn ((idʳ {off} +ʳ Δʳ n) ∘ʳ castʳ A') ⟧))))
               (⋆-sound word-eq F))))))))
      where
        A = +-assoc off n (k * n)
        B = sym (+-assoc off n k)
        A' = +-assoc off n n
        F' = subst Op B (F ⟨ off ⊣ gs zero ⊢ k ⟩)
        X = plug (off + n) F' (gs ∘ suc)
        T' = tupleʷ (gs ∘ suc)
        -- the contraction splits: id_off + Δᵏ(1+k) after the cast is
        -- (id_off + Δ) ∘ cast ∘ (id_{off+n} + Δᵏ k)
        total : ((idʳ {off} +ʳ Δᵏ (suc k) n) ∘ʳ castʳ A) ≗ (((idʳ {off} +ʳ Δʳ n) ∘ʳ castʳ A') ∘ʳ (idʳ {off + n} +ʳ Δᵏ k n))
        total i = begin
          (idʳ {off} +ʳ Δᵏ (suc k) n) (castʳ A i)
            ≡⟨ +ʳ-cong {r = idʳ {off}} {r' = idʳ {off}} (λ _ → refl) (Δᵏ-suc k n) (castʳ A i) ⟩
          (idʳ {off} +ʳ (Δʳ n ∘ʳ (idʳ {n} +ʳ Δᵏ k n))) (castʳ A i)
            ≡⟨ +ʳ-∘ (idʳ {off}) (idʳ {off}) (Δʳ n) (idʳ {n} +ʳ Δᵏ k n) (castʳ A i) ⟩
          (idʳ {off} +ʳ Δʳ n) ((idʳ {off} +ʳ (idʳ {n} +ʳ Δᵏ k n)) (castʳ A i))
            ≡⟨ cong (idʳ {off} +ʳ Δʳ n) (⊣-assoc off (idʳ {n}) (Δᵏ k n) (castʳ A i)) ⟩
          (idʳ {off} +ʳ Δʳ n) (castʳ A' (((idʳ {off} +ʳ idʳ {n}) +ʳ Δᵏ k n) (castʳ (sym A) (castʳ A i))))
            ≡⟨ cong (λ z → (idʳ {off} +ʳ Δʳ n) (castʳ A' (((idʳ {off} +ʳ idʳ {n}) +ʳ Δᵏ k n) z))) (trans (castʳ-∘ A (sym A) i) (castʳ-refl _ i)) ⟩
          (idʳ {off} +ʳ Δʳ n) (castʳ A' (((idʳ {off} +ʳ idʳ {n}) +ʳ Δᵏ k n) i))
            ≡⟨ cong (λ z → (idʳ {off} +ʳ Δʳ n) (castʳ A' z)) (+ʳ-cong {s = Δᵏ k n} {s' = Δᵏ k n} (+ʳ-id off n) (λ _ → refl) i) ⟩
          (idʳ {off} +ʳ Δʳ n) (castʳ A' ((idʳ {off + n} +ʳ Δᵏ k n) i)) ∎
          where open ≡-Reasoning
        -- the word identity: the substitution of gs zero, whiskered, then
        -- the tuple of the rest, then the contraction
        word-eq : Cong Cart ((sub! off k (gs zero) ∷ ⟦ rn (castʳ B) ⟧) ++ (((off + n) ⊣ʷ T') ++ ⟦ rn ((idʳ {off} +ʳ Δʳ n) ∘ʳ castʳ A') ⟧))
                            (off ⊣ʷ tupleʷ gs)
        word-eq =
          ≅-∷ (≅-∷ (≅-cong {Γ₁ = (off + n) ⊣ʷ T'} ≅-refl (≅-sym (R∙ _ _))))
          ⟶ ≅-∷ (≅-∷ (≅-≡ (sym (++-assoc ((off + n) ⊣ʷ T') ⟦ rn (castʳ A') ⟧ ⟦ rn (idʳ {off} +ʳ Δʳ n) ⟧))))
          ⟶ ≅-∷ (≅-cong {Γ₁ = rn (castʳ B) ∷ (((off + n) ⊣ʷ T') ++ ⟦ rn (castʳ A') ⟧)} (≅-sym (⊣-⊣-merge off n T')) ≅-refl)
          ⟶ ≅-cong {Γ₁ = ⟦ sub! off k (gs zero) ⟧} (≅-sym (ins-arity (+-identityʳ off) refl _ refl _ refl (gs zero))) ≅-refl
          ⟶ ≅-≡ (sym (trans (⊣ʷ-++ off (ηʷ (gs zero) ⊢ʷ k) ((n ⊣ʷ T') ++ ⟦ rn (Δʳ n) ⟧)) (cong ((off ⊣ʷ (ηʷ (gs zero) ⊢ʷ k)) ++_) (⊣ʷ-++ off (n ⊣ʷ T') ⟦ rn (Δʳ n) ⟧))))

    -- the interpretation of a k-ary former:  plug 0 f gs [Δᵏ] ≈ f ⋆ ⟨gs⟩
    plug-tuple₀ : (F : Op k) (gs : Fin k → Op n) → (plug 0 F gs) [ Δᵏ k n ] ≈ F ⋆ tupleʷ gs
    plug-tuple₀ F gs = ≈.trans (plug-tuple 0 F gs) (⋆-sound (0⊣ʷ _ (tupleʷ gs)) F)
