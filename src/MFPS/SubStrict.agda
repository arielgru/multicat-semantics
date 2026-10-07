------------------------------------------------------------------------
-- Proposition 3.14(i), strictness laws of whiskering in Sub.
--
-- The paper identifies the arities k+(j+m) and (k+j)+m on the nose;
-- here the corresponding words are related by transport along the
-- arity equations (`subst₂W`), which is conjugation by cast renaming
-- steps.  All four laws are instances of one induction (`conj-ind`):
-- if two step-transformations agree on every step up to casts, the
-- induced word-transformations agree up to casts.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.SubStrict (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊
open import MFPS.Sub 𝕊
open import MFPS.SubCast 𝕊
open import MFPS.SubWhisker 𝕊 using (⊣-assoc; module ⊢-assoc₂)

private
  variable
    j k m n a b : ℕ

-- word-level map of a step transformation
mapʷ : (φ : ℕ → ℕ) → (∀ {a b} → Step a b → Step (φ a) (φ b)) → Word m n → Word (φ m) (φ n)
mapʷ φ F ε       = ε
mapʷ φ F (s ∷ Γ) = F s ∷ mapʷ φ F Γ

⊣ʷ-map : ∀ k (Γ : Word m n) → k ⊣ʷ Γ ≡ mapʷ (k +_) (k ⊣ₛ_) Γ
⊣ʷ-map k ε       = refl
⊣ʷ-map k (s ∷ Γ) = cong ((k ⊣ₛ s) ∷_) (⊣ʷ-map k Γ)

⊢ʷ-map : ∀ k (Γ : Word m n) → Γ ⊢ʷ k ≡ mapʷ (_+ k) (_⊢ₛ k) Γ
⊢ʷ-map k ε       = refl
⊢ʷ-map k (s ∷ Γ) = cong ((s ⊢ₛ k) ∷_) (⊢ʷ-map k Γ)

mapʷ-∘ : (φ ψ : ℕ → ℕ) (F : ∀ {a b} → Step a b → Step (φ a) (φ b)) (G : ∀ {a b} → Step a b → Step (ψ a) (ψ b))
  (Γ : Word m n) → mapʷ ψ G (mapʷ φ F Γ) ≡ mapʷ (ψ ∘ φ) (G ∘ F) Γ
mapʷ-∘ φ ψ F G ε       = refl
mapʷ-∘ φ ψ F G (s ∷ Γ) = cong (G (F s) ∷_) (mapʷ-∘ φ ψ F G Γ)

mapʷ-id : (Γ : Word m n) → mapʷ (λ x → x) (λ s → s) Γ ≡ Γ
mapʷ-id ε       = refl
mapʷ-id (s ∷ Γ) = cong (s ∷_) (mapʷ-id Γ)

module _ {Cart : ∀ {n} → Op n → Set} where

  -- the generic induction
  conj-ind : (φ ψ : ℕ → ℕ) (e : ∀ x → φ x ≡ ψ x)
    (F : ∀ {a b} → Step a b → Step (φ a) (φ b)) (G : ∀ {a b} → Step a b → Step (ψ a) (ψ b))
    → (∀ {a b} (s : Step a b) → Cong Cart (rn (castʳ (sym (e b))) ∷ F s ∷ ⟦ rn (castʳ (e a)) ⟧) ⟦ G s ⟧)
    → (Γ : Word m n) → Cong Cart (rn (castʳ (sym (e n))) ∷ (mapʷ φ F Γ ++ ⟦ rn (castʳ (e m)) ⟧)) (mapʷ ψ G Γ)
  conj-ind φ ψ e F G h (ε {n}) =
    ≅-trans (rn-rn _ _) (rn-isCast (∘ʳ-isCast' (castʳ (e n)) (castʳ (sym (e n))) (castʳ-isCast (e n)) (castʳ-isCast (sym (e n)))))
  conj-ind φ ψ e F G h (_∷_ {k = k} s Γ) =
    ≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ε} (≅-sym (≅-trans (rn-rn _ _) (rn-isCast (∘ʳ-isCast' (castʳ (sym (e k))) (castʳ (e k)) (castʳ-isCast (sym (e k))) (castʳ-isCast (e k)))))) ≅-refl)))
            (≅-cong (h s) (conj-ind φ ψ e F G h Γ))

  -- transport of a word is conjugation by casts (restated for the shape used here)
  subst₂W-conj : (p : m ≡ a) (q : n ≡ b) (Γ : Word m n)
    → Cong Cart (subst₂W p q Γ) (rn (castʳ (sym q)) ∷ (Γ ++ ⟦ rn (castʳ p) ⟧))
  subst₂W-conj = subst₂-Word

  ----------------------------------------------------------------------
  -- f ⊢ 0 = f
  ----------------------------------------------------------------------
  ⊢0-step : (s : Step a b) → Cong Cart (rn (castʳ (sym (+-identityʳ b))) ∷ (s ⊢ₛ 0) ∷ ⟦ rn (castʳ (+-identityʳ a)) ⟧) ⟦ s ⟧
  ⊢0-step (ins n₁ n₂ {m} p q g) =
    ≅-trans (ins-conj n₁ (n₂ + 0) _ _ p' q' g (castʳ-isCast _) (castʳ-isCast _))
            (ins-arity refl (+-identityʳ n₂) p' p q' q g)
    where
      p' = trans p (cong (λ z → n₁ + (m + z)) (sym (+-identityʳ n₂)))
      q' = trans q (cong (λ z → n₁ + suc z) (sym (+-identityʳ n₂)))
  ⊢0-step (rn r) = ≅-trans (rn-rn _ _) (≅-trans (rn-rn _ _) (E∙ (+ʳ-zeroʳ r _ _)))

  ⊢-0ʷ : (Γ : Word m n) (p : m + 0 ≡ m) (q : n + 0 ≡ n) → Cong Cart (subst₂W p q (Γ ⊢ʷ 0)) Γ
  ⊢-0ʷ {m} {n} Γ p q =
    ≅-trans (subst₂W-conj p q (Γ ⊢ʷ 0))
    (≅-trans (≅-≡ (cong (λ z → rn (castʳ (sym q)) ∷ (z ++ ⟦ rn (castʳ p) ⟧)) (⊢ʷ-map 0 Γ)))
    (≅-trans (≅-≡ (cong₂ (λ c c' → rn (castʳ c) ∷ (mapʷ (_+ 0) (_⊢ₛ 0) Γ ++ ⟦ rn (castʳ c') ⟧)) (≡-irrelevant (sym q) _) (≡-irrelevant p _)))
    (≅-trans (conj-ind (_+ 0) (λ x → x) +-identityʳ (_⊢ₛ 0) (λ s → s) ⊢0-step Γ)
             (≅-≡ (mapʷ-id Γ)))))

  ----------------------------------------------------------------------
  -- k ⊣ (j ⊣ f) = (k + j) ⊣ f
  ----------------------------------------------------------------------
  ⊣⊣-step : ∀ k j {a b} (s : Step a b)
    → Cong Cart (rn (castʳ (sym (sym (+-assoc k j b)))) ∷ (k ⊣ₛ (j ⊣ₛ s)) ∷ ⟦ rn (castʳ (sym (+-assoc k j a))) ⟧) ⟦ (k + j) ⊣ₛ s ⟧
  ⊣⊣-step k j {a} {b} (ins n₁ n₂ {m} p q g) =
    ≅-trans (ins-conj (k + (j + n₁)) n₂ _ _ p' q' g (castʳ-isCast _) (castʳ-isCast _))
            (ins-arity (sym (+-assoc k j n₁)) refl p' (Lp (k + j) n₁ p) q' (Lp (k + j) n₁ q) g)
    where
      p' = trans (+-assoc k j a) (Lp k (j + n₁) (Lp j n₁ p))
      q' = trans (+-assoc k j b) (Lp k (j + n₁) (Lp j n₁ q))
  ⊣⊣-step k j (rn {n} {m} r) =
    ≅-trans (rn-rn _ _) (≅-trans (rn-rn _ _) (E∙ lemma))
    where
      lemma : (castʳ (sym (+-assoc k j m)) ∘ʳ (idʳ {k} +ʳ (idʳ {j} +ʳ r)) ∘ʳ castʳ (sym (sym (+-assoc k j n)))) ≗ (idʳ {k + j} +ʳ r)
      lemma i = begin
        castʳ (sym (+-assoc k j m)) ((idʳ {k} +ʳ (idʳ {j} +ʳ r)) (castʳ (sym (sym (+-assoc k j n))) i))
          ≡⟨ cong (castʳ (sym (+-assoc k j m))) (⊣-assoc k (idʳ {j}) r _) ⟩
        castʳ (sym (+-assoc k j m)) (castʳ (+-assoc k j m) (((idʳ {k} +ʳ idʳ {j}) +ʳ r) (castʳ (sym (+-assoc k j n)) (castʳ (sym (sym (+-assoc k j n))) i))))
          ≡⟨ castʳ-∘ (+-assoc k j m) (sym (+-assoc k j m)) _ ⟩
        castʳ (trans (+-assoc k j m) (sym (+-assoc k j m))) (((idʳ {k} +ʳ idʳ {j}) +ʳ r) (castʳ (sym (+-assoc k j n)) (castʳ (sym (sym (+-assoc k j n))) i)))
          ≡⟨ castʳ-refl _ _ ⟩
        ((idʳ {k} +ʳ idʳ {j}) +ʳ r) (castʳ (sym (+-assoc k j n)) (castʳ (sym (sym (+-assoc k j n))) i))
          ≡⟨ cong ((idʳ {k} +ʳ idʳ {j}) +ʳ r) (trans (castʳ-∘ (sym (sym (+-assoc k j n))) (sym (+-assoc k j n)) i) (castʳ-refl (trans (sym (sym (+-assoc k j n))) (sym (+-assoc k j n))) i)) ⟩
        ((idʳ {k} +ʳ idʳ {j}) +ʳ r) i
          ≡⟨ +ʳ-cong (+ʳ-id k j) (λ _ → refl) i ⟩
        (idʳ {k + j} +ʳ r) i ∎
        where open ≡-Reasoning

  ⊣-⊣ʷ : ∀ k j (Γ : Word m n) (p : k + (j + m) ≡ (k + j) + m) (q : k + (j + n) ≡ (k + j) + n)
    → Cong Cart (subst₂W p q (k ⊣ʷ (j ⊣ʷ Γ))) ((k + j) ⊣ʷ Γ)
  ⊣-⊣ʷ {m} {n} k j Γ p q =
    ≅-trans (subst₂W-conj p q (k ⊣ʷ (j ⊣ʷ Γ)))
    (≅-trans (≅-≡ (cong (λ z → rn (castʳ (sym q)) ∷ (z ++ ⟦ rn (castʳ p) ⟧)) (trans (⊣ʷ-map k (j ⊣ʷ Γ)) (trans (cong (mapʷ (k +_) (k ⊣ₛ_)) (⊣ʷ-map j Γ)) (mapʷ-∘ _ _ _ _ Γ)))))
    (≅-trans (≅-≡ (cong₂ (λ c c' → rn (castʳ c) ∷ (mapʷ _ _ Γ ++ ⟦ rn (castʳ c') ⟧)) (≡-irrelevant (sym q) _) (≡-irrelevant p _)))
    (≅-trans (conj-ind (λ x → k + (j + x)) (λ x → (k + j) + x) (λ x → sym (+-assoc k j x)) (λ s → k ⊣ₛ (j ⊣ₛ s)) ((k + j) ⊣ₛ_) (⊣⊣-step k j) Γ)
             (≅-≡ (sym (⊣ʷ-map (k + j) Γ))))))

  ----------------------------------------------------------------------
  -- (f ⊢ j) ⊢ k = f ⊢ (j + k)
  ----------------------------------------------------------------------
  ⊢⊢-step : ∀ j k {a b} (s : Step a b)
    → Cong Cart (rn (castʳ (sym (+-assoc b j k))) ∷ ((s ⊢ₛ j) ⊢ₛ k) ∷ ⟦ rn (castʳ (+-assoc a j k)) ⟧) ⟦ s ⊢ₛ (j + k) ⟧
  ⊢⊢-step j k {a} {b} (ins n₁ n₂ {m} p q g) =
    ≅-trans (ins-conj n₁ ((n₂ + j) + k) _ _ p' q' g (castʳ-isCast _) (castʳ-isCast _))
            (ins-arity refl (+-assoc n₂ j k) p' (Rp n₁ m n₂ (j + k) p) q' (Rq n₁ n₂ (j + k) q) g)
    where
      p' = trans (sym (+-assoc a j k)) (Rp n₁ m (n₂ + j) k (Rp n₁ m n₂ j p))
      q' = trans (sym (+-assoc b j k)) (Rq n₁ (n₂ + j) k (Rq n₁ n₂ j q))
  ⊢⊢-step j k (rn {n} {m} r) =
    ≅-trans (rn-rn _ _) (≅-trans (rn-rn _ _) (E∙ lemma))
    where
      module M = ⊢-assoc₂ r (idʳ {j}) (idʳ {k}) (idʳ {0})
      lemma : (castʳ (+-assoc m j k) ∘ʳ ((r +ʳ idʳ {j}) +ʳ idʳ {k}) ∘ʳ castʳ (sym (+-assoc n j k))) ≗ (r +ʳ idʳ {j + k})
      lemma i = begin
        castʳ (+-assoc m j k) (((r +ʳ idʳ {j}) +ʳ idʳ {k}) (castʳ (sym (+-assoc n j k)) i))
          ≡⟨ cong (castʳ (+-assoc m j k)) (sym (+ʳ-assoc r (idʳ {j}) (idʳ {k}) (+-assoc n j k) (sym (+-assoc m j k)) _)) ⟩
        castʳ (+-assoc m j k) (castʳ (sym (+-assoc m j k)) ((r +ʳ (idʳ {j} +ʳ idʳ {k})) (castʳ (+-assoc n j k) (castʳ (sym (+-assoc n j k)) i))))
          ≡⟨ trans (castʳ-∘ (sym (+-assoc m j k)) (+-assoc m j k) _) (castʳ-refl _ _) ⟩
        (r +ʳ (idʳ {j} +ʳ idʳ {k})) (castʳ (+-assoc n j k) (castʳ (sym (+-assoc n j k)) i))
          ≡⟨ cong (r +ʳ (idʳ {j} +ʳ idʳ {k})) (trans (castʳ-∘ (sym (+-assoc n j k)) (+-assoc n j k) i) (castʳ-refl _ i)) ⟩
        (r +ʳ (idʳ {j} +ʳ idʳ {k})) i
          ≡⟨ +ʳ-cong {r = r} {r' = r} (λ _ → refl) (+ʳ-id j k) i ⟩
        (r +ʳ idʳ {j + k}) i ∎
        where open ≡-Reasoning

  ⊢-⊢ʷ : ∀ j k (Γ : Word m n) (p : (m + j) + k ≡ m + (j + k)) (q : (n + j) + k ≡ n + (j + k))
    → Cong Cart (subst₂W p q ((Γ ⊢ʷ j) ⊢ʷ k)) (Γ ⊢ʷ (j + k))
  ⊢-⊢ʷ {m} {n} j k Γ p q =
    ≅-trans (subst₂W-conj p q ((Γ ⊢ʷ j) ⊢ʷ k))
    (≅-trans (≅-≡ (cong (λ z → rn (castʳ (sym q)) ∷ (z ++ ⟦ rn (castʳ p) ⟧)) (trans (⊢ʷ-map k (Γ ⊢ʷ j)) (trans (cong (mapʷ (_+ k) (_⊢ₛ k)) (⊢ʷ-map j Γ)) (mapʷ-∘ _ _ _ _ Γ)))))
    (≅-trans (≅-≡ (cong₂ (λ c c' → rn (castʳ c) ∷ (mapʷ _ _ Γ ++ ⟦ rn (castʳ c') ⟧)) (≡-irrelevant (sym q) _) (≡-irrelevant p _)))
    (≅-trans (conj-ind (λ x → (x + j) + k) (λ x → x + (j + k)) (λ x → +-assoc x j k) (λ s → (s ⊢ₛ j) ⊢ₛ k) (_⊢ₛ (j + k)) (⊢⊢-step j k) Γ)
             (≅-≡ (sym (⊢ʷ-map (j + k) Γ))))))

  ----------------------------------------------------------------------
  -- (k ⊣ f) ⊢ j = k ⊣ (f ⊢ j)
  ----------------------------------------------------------------------
  ⊣⊢-step : ∀ k j {a b} (s : Step a b)
    → Cong Cart (rn (castʳ (sym (+-assoc k b j))) ∷ ((k ⊣ₛ s) ⊢ₛ j) ∷ ⟦ rn (castʳ (+-assoc k a j)) ⟧) ⟦ k ⊣ₛ (s ⊢ₛ j) ⟧
  ⊣⊢-step k j {a} {b} (ins n₁ n₂ {m} p q g) =
    ≅-trans (ins-conj (k + n₁) (n₂ + j) _ _ p' q' g (castʳ-isCast _) (castʳ-isCast _))
            (≅-≡ (cong ⟦_⟧ (ins-irr (k + n₁) (n₂ + j) p' (Lp k n₁ (Rp n₁ m n₂ j p)) q' (Lp k n₁ (Rq n₁ n₂ j q)) g)))
    where
      p' = trans (sym (+-assoc k a j)) (Rp (k + n₁) m n₂ j (Lp k n₁ p))
      q' = trans (sym (+-assoc k b j)) (Rq (k + n₁) n₂ j (Lp k n₁ q))
  ⊣⊢-step k j (rn {n} {m} r) =
    ≅-trans (rn-rn _ _) (≅-trans (rn-rn _ _) (E∙ lemma))
    where
      lemma : (castʳ (+-assoc k m j) ∘ʳ ((idʳ {k} +ʳ r) +ʳ idʳ {j}) ∘ʳ castʳ (sym (+-assoc k n j))) ≗ (idʳ {k} +ʳ (r +ʳ idʳ {j}))
      lemma i = begin
        castʳ (+-assoc k m j) (((idʳ {k} +ʳ r) +ʳ idʳ {j}) (castʳ (sym (+-assoc k n j)) i))
          ≡⟨ cong (castʳ (+-assoc k m j)) (sym (+ʳ-assoc (idʳ {k}) r (idʳ {j}) (+-assoc k n j) (sym (+-assoc k m j)) _)) ⟩
        castʳ (+-assoc k m j) (castʳ (sym (+-assoc k m j)) ((idʳ {k} +ʳ (r +ʳ idʳ {j})) (castʳ (+-assoc k n j) (castʳ (sym (+-assoc k n j)) i))))
          ≡⟨ trans (castʳ-∘ (sym (+-assoc k m j)) (+-assoc k m j) _) (castʳ-refl _ _) ⟩
        (idʳ {k} +ʳ (r +ʳ idʳ {j})) (castʳ (+-assoc k n j) (castʳ (sym (+-assoc k n j)) i))
          ≡⟨ cong (idʳ {k} +ʳ (r +ʳ idʳ {j})) (trans (castʳ-∘ (sym (+-assoc k n j)) (+-assoc k n j) i) (castʳ-refl _ i)) ⟩
        (idʳ {k} +ʳ (r +ʳ idʳ {j})) i ∎
        where open ≡-Reasoning

  ⊣-⊢ʷ : ∀ k j (Γ : Word m n) (p : (k + m) + j ≡ k + (m + j)) (q : (k + n) + j ≡ k + (n + j))
    → Cong Cart (subst₂W p q ((k ⊣ʷ Γ) ⊢ʷ j)) (k ⊣ʷ (Γ ⊢ʷ j))
  ⊣-⊢ʷ {m} {n} k j Γ p q =
    ≅-trans (subst₂W-conj p q ((k ⊣ʷ Γ) ⊢ʷ j))
    (≅-trans (≅-≡ (cong (λ z → rn (castʳ (sym q)) ∷ (z ++ ⟦ rn (castʳ p) ⟧)) (trans (⊢ʷ-map j (k ⊣ʷ Γ)) (trans (cong (mapʷ (_+ j) (_⊢ₛ j)) (⊣ʷ-map k Γ)) (mapʷ-∘ _ _ _ _ Γ)))))
    (≅-trans (≅-≡ (cong₂ (λ c c' → rn (castʳ c) ∷ (mapʷ _ _ Γ ++ ⟦ rn (castʳ c') ⟧)) (≡-irrelevant (sym q) _) (≡-irrelevant p _)))
    (≅-trans (conj-ind (λ x → (k + x) + j) (λ x → k + (x + j)) (λ x → +-assoc k x j) (λ s → (k ⊣ₛ s) ⊢ₛ j) (λ s → k ⊣ₛ (s ⊢ₛ j)) (⊣⊢-step k j) Γ)
             (≅-≡ (trans (sym (mapʷ-∘ _ _ _ _ Γ)) (trans (cong (mapʷ (k +_) (k ⊣ₛ_)) (sym (⊢ʷ-map j Γ))) (sym (⊣ʷ-map k (Γ ⊢ʷ j)))))))))
