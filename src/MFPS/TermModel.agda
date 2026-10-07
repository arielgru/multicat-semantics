------------------------------------------------------------------------
-- Section 4.3: the term model (Thm. 4.8), in the shared-context
-- de Bruijn presentation.
--
--   VAL(n) = Val n / ≈,   CMP(n) = Cmp n / ≈   (setoids)
--   [V₁]{n₁ ⊣ [V₂] ⊢ n₂} = [V₁{V₂/y}]
--   [M₁]{n₁ ⊣ [M₂] ⊢ n₂} = [let y ⇐ M₂ in M₁]   (y moved to the end)
--   J = return,  ⊛ = x₁ x₂,  ◁ⁿ[M]▷ = [λx.M]
--
-- The laws that are proved here are marked; the remaining ones are
-- collected in the record `Laws` and assumed as a parameter of the
-- construction `termStructure`.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad
open import MFPS.Syntax

module MFPS.TermModel (Σ : Signature) where

open Signature Σ
open Terms Σ
open import MFPS.Theory Σ
open import MFPS.Semantics Σ using (Structure)

private
  variable
    k m n : ℕ
    s : Sort

------------------------------------------------------------------------
-- The three injections of the blocks of  n₁ + (m + n₂)
------------------------------------------------------------------------

ι₁ : ∀ n₁ m n₂ → Ren n₁ (n₁ + (m + n₂))
ι₁ n₁ m n₂ j = j ↑ˡ (m + n₂)

ι₂ : ∀ n₁ m n₂ → Ren m (n₁ + (m + n₂))
ι₂ n₁ m n₂ j = n₁ ↑ʳ (j ↑ˡ n₂)

ι₃ : ∀ n₁ m n₂ → Ren n₂ (n₁ + (m + n₂))
ι₃ n₁ m n₂ j = n₁ ↑ʳ (m ↑ʳ j)

-- the substitution  x_i ↦ x_i (i < n₁),  y ↦ V,  z_j ↦ z_j   used for VAL
σ-ins : ∀ n₁ n₂ {m} → Val m → Subst (n₁ + suc n₂) (n₁ + (m + n₂))
σ-ins n₁ n₂ {m} V = [ ⌜ ι₁ n₁ m n₂ ⌝ , [ (λ _ → ren (ι₂ n₁ m n₂) V) , ⌜ ι₃ n₁ m n₂ ⌝ ]ʳ' ]ʳ'
  where
    -- [_,_] for substitutions
    [_,_]ʳ' : ∀ {a b c} → (Fin a → Val c) → (Fin b → Val c) → Fin (a + b) → Val c
    [_,_]ʳ' {a} f g i = [ f , g ]′ (splitAt a i)

-- the renaming moving the hole variable y (position n₁) to the end, used for CMP
ρ-ins : ∀ n₁ n₂ m → Ren (n₁ + suc n₂) ((n₁ + (m + n₂)) + 1)
ρ-ins n₁ n₂ m = [ (λ j → ι₁ n₁ m n₂ j ↑ˡ 1) , [ (λ _ → last) , (λ j → ι₃ n₁ m n₂ j ↑ˡ 1) ]ʳ ]ʳ

------------------------------------------------------------------------
-- VAL as a preoperad
------------------------------------------------------------------------

subᵛ : ∀ n₁ n₂ {m} → Val (n₁ + suc n₂) → Val m → Val (n₁ + (m + n₂))
subᵛ n₁ n₂ V₁ V₂ = sub (σ-ins n₁ n₂ V₂) V₁

-- computation rules of σ-ins on the three blocks
σ-ins-₁ : ∀ n₁ n₂ {m} (V : Val m) (j : Fin n₁) → σ-ins n₁ n₂ V (j ↑ˡ suc n₂) ≡ var (ι₁ n₁ m n₂ j)
σ-ins-₁ n₁ n₂ {m} V j = cong [ ⌜ ι₁ n₁ m n₂ ⌝ , _ ]′ (splitAt-↑ˡ n₁ j (suc n₂))

σ-ins-₂ : ∀ n₁ n₂ {m} (V : Val m) → σ-ins n₁ n₂ V (n₁ ↑ʳ zero) ≡ ren (ι₂ n₁ m n₂) V
σ-ins-₂ n₁ n₂ {m} V = cong [ ⌜ ι₁ n₁ m n₂ ⌝ , _ ]′ (splitAt-↑ʳ n₁ (suc n₂) zero)

σ-ins-₃ : ∀ n₁ n₂ {m} (V : Val m) (j : Fin n₂) → σ-ins n₁ n₂ V (n₁ ↑ʳ suc j) ≡ var (ι₃ n₁ m n₂ j)
σ-ins-₃ n₁ n₂ {m} V j = cong [ ⌜ ι₁ n₁ m n₂ ⌝ , _ ]′ (splitAt-↑ʳ n₁ (suc n₂) (suc j))

-- pointwise ≈ of two substitutions out of n₁ + suc n₂ is determined blockwise
Fin-ins-ext≈ : ∀ n₁ n₂ {f g : Fin (n₁ + suc n₂) → Val n}
  → (∀ j → f (j ↑ˡ suc n₂) ≈ g (j ↑ˡ suc n₂)) → f (n₁ ↑ʳ zero) ≈ g (n₁ ↑ʳ zero)
  → (∀ j → f (n₁ ↑ʳ suc j) ≈ g (n₁ ↑ʳ suc j)) → ∀ i → f i ≈ g i
Fin-ins-ext≈ n₁ n₂ {f} {g} h₁ h₂ h₃ i with splitAt n₁ i in eq
... | inj₁ j       = subst (λ i → f i ≈ g i) (splitAt⁻¹-↑ˡ eq) (h₁ j)
... | inj₂ zero    = subst (λ i → f i ≈ g i) (splitAt⁻¹-↑ʳ eq) h₂
... | inj₂ (suc j) = subst (λ i → f i ≈ g i) (splitAt⁻¹-↑ʳ eq) (h₃ j)

Fin-ins-ext : ∀ {ℓ} {A : Set ℓ} n₁ n₂ {f g : Fin (n₁ + suc n₂) → A}
  → (∀ j → f (j ↑ˡ suc n₂) ≡ g (j ↑ˡ suc n₂)) → f (n₁ ↑ʳ zero) ≡ g (n₁ ↑ʳ zero)
  → (∀ j → f (n₁ ↑ʳ suc j) ≡ g (n₁ ↑ʳ suc j)) → f ≗ g
Fin-ins-ext n₁ n₂ h₁ h₂ h₃ = Fin+-ext h₁ (λ { zero → h₂ ; (suc j) → h₃ j })

-- (proved) substitution is a congruence in both arguments
subᵛ-cong : ∀ {n₁ n₂ m} {V₁ V₁' : Val (n₁ + suc n₂)} {V₂ V₂' : Val m}
  → V₁ ≈ V₁' → V₂ ≈ V₂' → subᵛ n₁ n₂ V₁ V₂ ≈ subᵛ n₁ n₂ V₁' V₂'
subᵛ-cong {n₁} {n₂} {m} {V₁} {V₁'} {V₂} {V₂'} e₁ e₂ =
  ≈-trans (sub-≈ (σ-ins n₁ n₂ V₂) e₁)
          (sub-cong≈ (Fin-ins-ext≈ n₁ n₂
                        (λ j → ≈-≡ (trans (σ-ins-₁ n₁ n₂ V₂ j) (sym (σ-ins-₁ n₁ n₂ V₂' j))))
                        (≈-trans (≈-≡ (σ-ins-₂ n₁ n₂ V₂)) (≈-trans (ren-≈ _ e₂) (≈-≡ (sym (σ-ins-₂ n₁ n₂ V₂')))))
                        (λ j → ≈-≡ (trans (σ-ins-₃ n₁ n₂ V₂ j) (sym (σ-ins-₃ n₁ n₂ V₂' j)))))
                     V₁')

-- (proved) right unit: V{n₁ ⊣ x ⊢ n₂} ≡ V
σ-ins-id : ∀ n₁ n₂ → σ-ins n₁ n₂ (var zero) ≗ idˢ
σ-ins-id n₁ n₂ = Fin-ins-ext n₁ n₂ (σ-ins-₁ n₁ n₂ (var zero)) (σ-ins-₂ n₁ n₂ (var zero)) (σ-ins-₃ n₁ n₂ (var zero))

runitᵛ : ∀ {n₁ n₂} (V : Val (n₁ + suc n₂)) → subᵛ n₁ n₂ V (var zero) ≈ V
runitᵛ {n₁} {n₂} V = ≈-≡ (trans (sub-cong (σ-ins-id n₁ n₂) V) (sub-id V))

-- (proved) left unit: x{0 ⊣ V ⊢ 0} ≡ V  (up to the arity cast m + 0 = m)
lunitᵛ : ∀ {m} (V : Val m) (p : m + 0 ≡ m) → subst Val p (subᵛ 0 0 (var zero) V) ≈ V
lunitᵛ {m} V p = ≈-≡ (begin
  subst Val p (ren (ι₂ 0 m 0) V)       ≡⟨ subst-ren p _ ⟩
  ren (castʳ p) (ren (ι₂ 0 m 0) V)     ≡⟨ sym (ren-∘ _ _ V) ⟩
  ren (castʳ p ∘ʳ ι₂ 0 m 0) V          ≡⟨ ren-cong (λ i → toℕ-injective (trans (toℕ-castʳ p _) (toℕ-↑ˡ i 0))) V ⟩
  ren idʳ V                            ≡⟨ ren-id V ⟩
  V ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------
-- CMP as a preoperad
------------------------------------------------------------------------

subᶜ : ∀ n₁ n₂ {m} → Cmp (n₁ + suc n₂) → Cmp m → Cmp (n₁ + (m + n₂))
subᶜ n₁ n₂ {m} M₁ M₂ = bnd (ren (ι₂ n₁ m n₂) M₂) (ren (ρ-ins n₁ n₂ m) M₁)

-- (proved) congruence
subᶜ-cong : ∀ {n₁ n₂ m} {M₁ M₁' : Cmp (n₁ + suc n₂)} {M₂ M₂' : Cmp m}
  → M₁ ≈ M₁' → M₂ ≈ M₂' → subᶜ n₁ n₂ M₁ M₂ ≈ subᶜ n₁ n₂ M₁' M₂'
subᶜ-cong e₁ e₂ = bnd-cong (ren-≈ _ e₂) (ren-≈ _ e₁)

-- computation rules of ρ-ins
ρ-ins-₁ : ∀ n₁ n₂ m (j : Fin n₁) → ρ-ins n₁ n₂ m (j ↑ˡ suc n₂) ≡ ι₁ n₁ m n₂ j ↑ˡ 1
ρ-ins-₁ n₁ n₂ m j = [,]ʳ-inl _ _ j

ρ-ins-₂ : ∀ n₁ n₂ m → ρ-ins n₁ n₂ m (n₁ ↑ʳ zero) ≡ last
ρ-ins-₂ n₁ n₂ m = [,]ʳ-inr (λ j → ι₁ n₁ m n₂ j ↑ˡ 1) _ zero

ρ-ins-₃ : ∀ n₁ n₂ m (j : Fin n₂) → ρ-ins n₁ n₂ m (n₁ ↑ʳ suc j) ≡ ι₃ n₁ m n₂ j ↑ˡ 1
ρ-ins-₃ n₁ n₂ m j = [,]ʳ-inr (λ j → ι₁ n₁ m n₂ j ↑ˡ 1) _ (suc j)

-- (proved) left unit for computations:  let y ⇐ M in return y ≡ M
lunitᶜ : ∀ {m} (M : Cmp m) (p : m + 0 ≡ m) → subst Cmp p (subᶜ 0 0 (ret (var zero)) M) ≈ M
lunitᶜ {m} M p =
  ≈-trans (≈-≡ (subst-ren p _))
  (≈-trans (≈-≡ (cong (ren (castʳ p)) (cong (bnd (ren (ι₂ 0 m 0) M)) (cong (ret ∘ var) (ρ-ins-₂ 0 0 m)))))
  (≈-trans (ren-≈ (castʳ p) (runit (ren (ι₂ 0 m 0) M)))
  (≈-≡ (trans (sym (ren-∘ _ _ M))
       (trans (ren-cong (λ i → toℕ-injective (trans (toℕ-castʳ p _) (toℕ-↑ˡ i 0))) M) (ren-id M))))))

-- (proved) right unit for computations:  let y ⇐ return y in M ≡ M
runitᶜ : ∀ {n₁ n₂} (M : Cmp (n₁ + suc n₂)) → subᶜ n₁ n₂ M (ret (var zero)) ≈ M
runitᶜ {n₁} {n₂} M =
  ≈-trans (lunit _ _)
  (≈-≡ (trans (sub-ren (ρ-ins n₁ n₂ 1) (idˢ ∷ˢ var (ι₂ n₁ 1 n₂ zero)) M)
       (trans (sub-cong lemma M) (sub-id M))))
  where
    σ' : Subst ((n₁ + (1 + n₂)) + 1) (n₁ + (1 + n₂))
    σ' = idˢ ∷ˢ var (ι₂ n₁ 1 n₂ zero)
    lemma : (σ' ∘ ρ-ins n₁ n₂ 1) ≗ idˢ
    lemma = Fin-ins-ext n₁ n₂
      (λ j → trans (cong σ' (ρ-ins-₁ n₁ n₂ 1 j)) (∷ˢ-inl idˢ _ (ι₁ n₁ 1 n₂ j)))
      (trans (cong σ' (ρ-ins-₂ n₁ n₂ 1)) (∷ˢ-last idˢ _))
      (λ j → trans (cong σ' (ρ-ins-₃ n₁ n₂ 1 j)) (∷ˢ-inl idˢ _ (ι₃ n₁ 1 n₂ j)))

------------------------------------------------------------------------
-- return is a functor (Def. 3.8): witnessed by (lunit)
------------------------------------------------------------------------

-- (proved) return (V₁{V₂/y}) ≡ let y ⇐ return V₂ in return V₁
ret-sub : ∀ {n₁ n₂ m} (V₁ : Val (n₁ + suc n₂)) (V₂ : Val m)
  → ret (subᵛ n₁ n₂ V₁ V₂) ≈ subᶜ n₁ n₂ (ret V₁) (ret V₂)
ret-sub {n₁} {n₂} {m} V₁ V₂ =
  ≈-sym (≈-trans (lunit _ _)
        (≈-≡ (cong ret (trans (sub-ren (ρ-ins n₁ n₂ m) (idˢ ∷ˢ ren (ι₂ n₁ m n₂) V₂) V₁) (sub-cong lemma V₁)))))
  where
    σ' : Subst ((n₁ + (m + n₂)) + 1) (n₁ + (m + n₂))
    σ' = idˢ ∷ˢ ren (ι₂ n₁ m n₂) V₂
    lemma : (σ' ∘ ρ-ins n₁ n₂ m) ≗ σ-ins n₁ n₂ V₂
    lemma = Fin-ins-ext n₁ n₂
      (λ j → trans (cong σ' (ρ-ins-₁ n₁ n₂ m j)) (trans (∷ˢ-inl idˢ _ _) (sym (σ-ins-₁ n₁ n₂ V₂ j))))
      (trans (cong σ' (ρ-ins-₂ n₁ n₂ m)) (trans (∷ˢ-last idˢ _) (sym (σ-ins-₂ n₁ n₂ V₂))))
      (λ j → trans (cong σ' (ρ-ins-₃ n₁ n₂ m j)) (trans (∷ˢ-inl idˢ _ _) (sym (σ-ins-₃ n₁ n₂ V₂ j))))

------------------------------------------------------------------------
-- The laws not proved here, collected as a record of assumptions.
------------------------------------------------------------------------

-- the underlying preoperads, given associativity
module Pre (assocᵛ : ∀ {m₁ m₂ n₁ n₂ n} (f : Val (m₁ + suc m₂)) (g : Val (n₁ + suc n₂)) (h : Val n)
                       (p : m₁ + ((n₁ + suc n₂) + m₂) ≡ (m₁ + n₁) + suc (n₂ + m₂))
                       (q : (m₁ + n₁) + (n + (n₂ + m₂)) ≡ m₁ + ((n₁ + (n + n₂)) + m₂))
                     → subst Val q (subᵛ (m₁ + n₁) (n₂ + m₂) (subst Val p (subᵛ m₁ m₂ f g)) h)
                       ≈ subᵛ m₁ m₂ f (subᵛ n₁ n₂ g h))
           (assocᶜ : ∀ {m₁ m₂ n₁ n₂ n} (f : Cmp (m₁ + suc m₂)) (g : Cmp (n₁ + suc n₂)) (h : Cmp n)
                       (p : m₁ + ((n₁ + suc n₂) + m₂) ≡ (m₁ + n₁) + suc (n₂ + m₂))
                       (q : (m₁ + n₁) + (n + (n₂ + m₂)) ≡ m₁ + ((n₁ + (n + n₂)) + m₂))
                     → subst Cmp q (subᶜ (m₁ + n₁) (n₂ + m₂) (subst Cmp p (subᶜ m₁ m₂ f g)) h)
                       ≈ subᶜ m₁ m₂ f (subᶜ n₁ n₂ g h)) where

  VAL : Preoperad
  VAL = record
    { Op = Val ; _≈_ = _≈_ ; ≈-equiv = ≈-equiv
    ; idₒ = var zero ; sub = subᵛ
    ; sub-cong = subᵛ-cong ; lunit = lunitᵛ ; runit = runitᵛ ; assoc = assocᵛ }

  CMP : Preoperad
  CMP = record
    { Op = Cmp ; _≈_ = _≈_ ; ≈-equiv = ≈-equiv
    ; idₒ = ret (var zero) ; sub = subᶜ
    ; sub-cong = subᶜ-cong ; lunit = lunitᶜ ; runit = runitᶜ ; assoc = assocᶜ }

  -- (proved) the renaming actions
  renVAL : RenCartesian VAL
  renVAL = record
    { _[_] = λ V r → ren r V
    ; ren-cong = λ e e' → ≈-trans (ren-≈ _ e) (≈-≡ (ren-cong e' _))
    ; ren-id = λ V → ≈-≡ (ren-id V)
    ; ren-∘ = λ V r s → ≈-≡ (ren-∘ r s V)
    ; ren-sub = ren-subᵛ }
    where
      ren-subᵛ : ∀ {n₁ n₂ n m₁ m₂ m} (u : Val (n₁ + suc n₂)) (v : Val n) (r₁ : Ren n₁ m₁) (s : Ren n m) (r₂ : Ren n₂ m₂)
        → ren (r₁ +ʳ s +ʳ r₂) (subᵛ n₁ n₂ u v) ≈ subᵛ m₁ m₂ (ren (r₁ +ʳ idʳ {1} +ʳ r₂) u) (ren s v)
      ren-subᵛ {n₁} {n₂} {n} {m₁} {m₂} {m} u v r₁ s r₂ = ≈-≡ (begin
        ren (r₁ +ʳ s +ʳ r₂) (sub (σ-ins n₁ n₂ v) u)
          ≡⟨ ren-sub _ _ u ⟩
        sub (λ i → ren (r₁ +ʳ s +ʳ r₂) (σ-ins n₁ n₂ v i)) u
          ≡⟨ sub-cong lemma u ⟩
        sub (σ-ins m₁ m₂ (ren s v) ∘ (r₁ +ʳ idʳ {1} +ʳ r₂)) u
          ≡⟨ sym (sub-ren _ _ u) ⟩
        sub (σ-ins m₁ m₂ (ren s v)) (ren (r₁ +ʳ idʳ {1} +ʳ r₂) u) ∎)
        where
          open ≡-Reasoning
          lemma : (λ i → ren (r₁ +ʳ s +ʳ r₂) (σ-ins n₁ n₂ v i)) ≗ (σ-ins m₁ m₂ (ren s v) ∘ (r₁ +ʳ idʳ {1} +ʳ r₂))
          lemma = Fin-ins-ext n₁ n₂
            (λ j → begin
              ren (r₁ +ʳ s +ʳ r₂) (σ-ins n₁ n₂ v (j ↑ˡ suc n₂))     ≡⟨ cong (ren _) (σ-ins-₁ n₁ n₂ v j) ⟩
              var ((r₁ +ʳ s +ʳ r₂) (j ↑ˡ (n + n₂)))                ≡⟨ cong var (+ʳ-inj₁ r₁ (s +ʳ r₂) j) ⟩
              var (r₁ j ↑ˡ (m + m₂))                               ≡⟨ sym (σ-ins-₁ m₁ m₂ (ren s v) (r₁ j)) ⟩
              σ-ins m₁ m₂ (ren s v) (r₁ j ↑ˡ suc m₂)               ≡⟨ cong (σ-ins m₁ m₂ (ren s v)) (sym (+ʳ-inj₁ r₁ (idʳ {1} +ʳ r₂) j)) ⟩
              σ-ins m₁ m₂ (ren s v) ((r₁ +ʳ idʳ {1} +ʳ r₂) (j ↑ˡ suc n₂)) ∎)
            (begin
              ren (r₁ +ʳ s +ʳ r₂) (σ-ins n₁ n₂ v (n₁ ↑ʳ zero))      ≡⟨ cong (ren _) (σ-ins-₂ n₁ n₂ v) ⟩
              ren (r₁ +ʳ s +ʳ r₂) (ren (ι₂ n₁ n n₂) v)              ≡⟨ sym (ren-∘ _ _ v) ⟩
              ren ((r₁ +ʳ s +ʳ r₂) ∘ʳ ι₂ n₁ n n₂) v                 ≡⟨ ren-cong (λ j → trans (+ʳ-inj₂ r₁ (s +ʳ r₂) (j ↑ˡ n₂)) (cong (m₁ ↑ʳ_) (+ʳ-inj₁ s r₂ j))) v ⟩
              ren (ι₂ m₁ m m₂ ∘ʳ s) v                               ≡⟨ ren-∘ _ _ v ⟩
              ren (ι₂ m₁ m m₂) (ren s v)                            ≡⟨ sym (σ-ins-₂ m₁ m₂ (ren s v)) ⟩
              σ-ins m₁ m₂ (ren s v) (m₁ ↑ʳ zero)                    ≡⟨ cong (σ-ins m₁ m₂ (ren s v)) (sym (trans (+ʳ-inj₂ r₁ (idʳ {1} +ʳ r₂) zero) (cong (m₁ ↑ʳ_) (+ʳ-inj₁ (idʳ {1}) r₂ zero)))) ⟩
              σ-ins m₁ m₂ (ren s v) ((r₁ +ʳ idʳ {1} +ʳ r₂) (n₁ ↑ʳ zero)) ∎)
            (λ j → begin
              ren (r₁ +ʳ s +ʳ r₂) (σ-ins n₁ n₂ v (n₁ ↑ʳ suc j))     ≡⟨ cong (ren _) (σ-ins-₃ n₁ n₂ v j) ⟩
              var ((r₁ +ʳ s +ʳ r₂) (n₁ ↑ʳ (n ↑ʳ j)))                ≡⟨ cong var (trans (+ʳ-inj₂ r₁ (s +ʳ r₂) (n ↑ʳ j)) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ s r₂ j))) ⟩
              var (m₁ ↑ʳ (m ↑ʳ r₂ j))                               ≡⟨ sym (σ-ins-₃ m₁ m₂ (ren s v) (r₂ j)) ⟩
              σ-ins m₁ m₂ (ren s v) (m₁ ↑ʳ suc (r₂ j))              ≡⟨ cong (σ-ins m₁ m₂ (ren s v)) (sym (trans (+ʳ-inj₂ r₁ (idʳ {1} +ʳ r₂) (suc j)) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ (idʳ {1}) r₂ j)))) ⟩
              σ-ins m₁ m₂ (ren s v) ((r₁ +ʳ idʳ {1} +ʳ r₂) (n₁ ↑ʳ suc j)) ∎)

  renCMP-cong : {M M' : Cmp m} {r r' : Ren m n} → M ≈ M' → r ≗ r' → ren r M ≈ ren r' M'
  renCMP-cong e e' = ≈-trans (ren-≈ _ e) (≈-≡ (ren-cong e' _))

  -- (proved) renaming/substitution interchange for computations
  ren-subᶜ : ∀ {n₁ n₂ n m₁ m₂ m} (u : Cmp (n₁ + suc n₂)) (v : Cmp n) (r₁ : Ren n₁ m₁) (s : Ren n m) (r₂ : Ren n₂ m₂)
    → ren (r₁ +ʳ s +ʳ r₂) (subᶜ n₁ n₂ u v) ≈ subᶜ m₁ m₂ (ren (r₁ +ʳ idʳ {1} +ʳ r₂) u) (ren s v)
  ren-subᶜ {n₁} {n₂} {n} {m₁} {m₂} {m} u v r₁ s r₂ = ≈-≡ (cong₂ bnd
    (trans (sym (ren-∘ _ _ v))
    (trans (ren-cong (λ j → trans (+ʳ-inj₂ r₁ (s +ʳ r₂) (j ↑ˡ n₂)) (cong (m₁ ↑ʳ_) (+ʳ-inj₁ s r₂ j))) v) (ren-∘ _ _ v)))
    (trans (sym (ren-∘ _ _ u)) (trans (ren-cong lemma u) (ren-∘ _ _ u))))
    where
      R = r₁ +ʳ s +ʳ r₂
      lemma : (liftʳ R ∘ʳ ρ-ins n₁ n₂ n) ≗ (ρ-ins m₁ m₂ m ∘ʳ (r₁ +ʳ idʳ {1} +ʳ r₂))
      lemma = Fin-ins-ext n₁ n₂
        (λ j → begin
          liftʳ R (ρ-ins n₁ n₂ n (j ↑ˡ suc n₂))           ≡⟨ cong (liftʳ R) (ρ-ins-₁ n₁ n₂ n j) ⟩
          liftʳ R (ι₁ n₁ n n₂ j ↑ˡ 1)                      ≡⟨ liftʳ-inl R _ ⟩
          R (j ↑ˡ (n + n₂)) ↑ˡ 1                           ≡⟨ cong (_↑ˡ 1) (+ʳ-inj₁ r₁ (s +ʳ r₂) j) ⟩
          ι₁ m₁ m m₂ (r₁ j) ↑ˡ 1                           ≡⟨ sym (ρ-ins-₁ m₁ m₂ m (r₁ j)) ⟩
          ρ-ins m₁ m₂ m (r₁ j ↑ˡ suc m₂)                   ≡⟨ cong (ρ-ins m₁ m₂ m) (sym (+ʳ-inj₁ r₁ (idʳ {1} +ʳ r₂) j)) ⟩
          ρ-ins m₁ m₂ m ((r₁ +ʳ idʳ {1} +ʳ r₂) (j ↑ˡ suc n₂)) ∎)
        (begin
          liftʳ R (ρ-ins n₁ n₂ n (n₁ ↑ʳ zero))             ≡⟨ cong (liftʳ R) (ρ-ins-₂ n₁ n₂ n) ⟩
          liftʳ R last                                     ≡⟨ liftʳ-last R ⟩
          last                                             ≡⟨ sym (ρ-ins-₂ m₁ m₂ m) ⟩
          ρ-ins m₁ m₂ m (m₁ ↑ʳ zero)                       ≡⟨ cong (ρ-ins m₁ m₂ m) (sym (trans (+ʳ-inj₂ r₁ (idʳ {1} +ʳ r₂) zero) (cong (m₁ ↑ʳ_) (+ʳ-inj₁ (idʳ {1}) r₂ zero)))) ⟩
          ρ-ins m₁ m₂ m ((r₁ +ʳ idʳ {1} +ʳ r₂) (n₁ ↑ʳ zero)) ∎)
        (λ j → begin
          liftʳ R (ρ-ins n₁ n₂ n (n₁ ↑ʳ suc j))           ≡⟨ cong (liftʳ R) (ρ-ins-₃ n₁ n₂ n j) ⟩
          liftʳ R (ι₃ n₁ n n₂ j ↑ˡ 1)                      ≡⟨ liftʳ-inl R _ ⟩
          R (n₁ ↑ʳ (n ↑ʳ j)) ↑ˡ 1                          ≡⟨ cong (_↑ˡ 1) (trans (+ʳ-inj₂ r₁ (s +ʳ r₂) (n ↑ʳ j)) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ s r₂ j))) ⟩
          ι₃ m₁ m m₂ (r₂ j) ↑ˡ 1                           ≡⟨ sym (ρ-ins-₃ m₁ m₂ m (r₂ j)) ⟩
          ρ-ins m₁ m₂ m (m₁ ↑ʳ suc (r₂ j))                 ≡⟨ cong (ρ-ins m₁ m₂ m) (sym (trans (+ʳ-inj₂ r₁ (idʳ {1} +ʳ r₂) (suc j)) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ (idʳ {1}) r₂ j)))) ⟩
          ρ-ins m₁ m₂ m ((r₁ +ʳ idʳ {1} +ʳ r₂) (n₁ ↑ʳ suc j)) ∎)
        where open ≡-Reasoning

  renCMP : RenCartesian CMP
  renCMP = record
    { _[_] = λ M r → ren r M
    ; ren-cong = renCMP-cong
    ; ren-id = λ M → ≈-≡ (ren-id M)
    ; ren-∘ = λ M r s → ≈-≡ (ren-∘ r s M)
    ; ren-sub = ren-subᶜ }

  -- return : VAL → CMP is a cartesian preoperad functor (proved)
  RET : PreoperadFunctor VAL CMP
  RET = record { F = ret ; F-cong = ret-cong ; F-id = ≈-refl ; F-sub = ret-sub }

  RET-ren : CartesianFunctor renVAL renCMP RET
  RET-ren = record { F-ren = λ _ _ → ≈-refl }

  ----------------------------------------------------------------------
  -- The remaining laws of Thm. 4.8, as assumptions.
  ----------------------------------------------------------------------

  record Laws : Set where
    field
      symVAL    : Symmetric VAL renVAL
      symCMP    : Symmetric CMP renCMP
      operadVAL : Centrality.IsOperad VAL
      !-natVAL  : ∀ {m₁ m₂ n} (f : Val (m₁ + m₂)) (g : Val n)
        → subᵛ m₁ m₂ (ren (idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂}) f) g ≈ ren (idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂}) f
      Δ-natVAL  : ∀ {m₁ m₂ n} (f : Val (m₁ + suc (suc m₂))) (g : Val n)
        (p : m₁ + (n + suc m₂) ≡ (m₁ + n) + suc m₂) (q : (m₁ + n) + (n + m₂) ≡ m₁ + ((n + n) + m₂))
        → subᵛ m₁ m₂ (ren (idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂}) f) g
          ≈ ren ((idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}) ∘ʳ castʳ q) (subᵛ (m₁ + n) m₂ (subst Val p (subᵛ m₁ (suc m₂) f g)) g)
      ret-central : ∀ {n} (v : Val n) → Centrality.Central CMP (ret v)
      ret-discard : ∀ {m₁ m₂ n} (f : Cmp (m₁ + m₂)) (v : Val n)
        → subᶜ m₁ m₂ (ren (idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂}) f) (ret v) ≈ ren (idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂}) f
      ret-copy    : ∀ {m₁ m₂ n} (f : Cmp (m₁ + suc (suc m₂))) (v : Val n)
        (p : m₁ + (n + suc m₂) ≡ (m₁ + n) + suc m₂) (q : (m₁ + n) + (n + m₂) ≡ m₁ + ((n + n) + m₂))
        → subᶜ m₁ m₂ (ren (idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂}) f) (ret v)
          ≈ ren ((idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}) ∘ʳ castʳ q) (subᶜ (m₁ + n) m₂ (subst Cmp p (subᶜ m₁ (suc m₂) f (ret v))) (ret v))
      betaᵒ   : ∀ {n} (f : Cmp (n + 1)) → subᶜ 0 1 (app (var zero) (var (suc zero))) (ret (lam f)) ≈ f
      abs-subᵒ : ∀ {m₁ m₂ n} (f : Cmp (m₁ + suc (m₂ + 1))) (v : Val n)
        (p : m₁ + (n + (m₂ + 1)) ≡ (m₁ + (n + m₂)) + 1) (p' : m₁ + suc (m₂ + 1) ≡ (m₁ + suc m₂) + 1)
        → lam (subst Cmp p (subᶜ m₁ (m₂ + 1) f (ret v))) ≈ subᵛ m₁ m₂ (lam (subst Cmp p' f)) v

  module Build (laws : Laws) where
    open Laws laws

    𝕍-term : CartesianOperad
    𝕍-term = record { V = VAL ; ren = renVAL ; symm = symVAL ; operad = operadVAL ; !-nat = !-natVAL ; Δ-nat = Δ-natVAL }

    ℂ-term : SymPreoperad
    ℂ-term = record { C = CMP ; ren = renCMP ; symm = symCMP }

    -- Theorem 4.8 (the Freyd operad part)
    M-term : FreydOperad
    M-term = record
      { 𝕍 = 𝕍-term ; ℂ = ℂ-term ; J = RET ; J-ren = RET-ren
      ; J-central = ret-central ; J-discard = ret-discard ; J-copy = ret-copy }

    -- weak closure: abstraction is λ, application is x₁ x₂
    W-term : WeaklyClosed M-term
    W-term = record
      { abs = lam ; abs-cong = lam-cong
      ; app = app (var zero) (var (suc zero))
      ; beta = betaᵒ
      ; abs-ren = λ f r → ≈-refl            -- λ commutes with renaming on the nose
      ; abs-sub = abs-subᵒ }

    -- the canonical arguments x₁, …, x_k
    vars : ∀ {n} k → (Fin k → Fin n) → Args n k
    vars zero    ι = []
    vars (suc k) ι = var (ι zero) ∷ vars k (ι ∘ suc)

    -- Theorem 4.8: the term λml*-structure
    termStructure : Structure
    termStructure = record
      { M = M-term ; W = W-term
      ; σF = λ {n} f → fun f (vars n idʳ)
      ; σP = λ {n} p → prc p (vars n idʳ) }
