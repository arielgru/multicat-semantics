------------------------------------------------------------------------
-- Proposition 3.14(i), the key step: the congruence of Fig. 3 is
-- stable under left and right whiskering, so that k ⊣ (−) and (−) ⊢ k
-- descend to the quotients Sub_ℂ and Sub×.
--
-- Proof in words.  Whiskering a substitution step shifts its position
-- (k ⊣ {n₁ ⊣ g ⊢ n₂} = {k+n₁ ⊣ g ⊢ n₂}) and whiskering a renaming step
-- takes a block sum with the identity.  For the rules that only mention
-- substitution steps ((I),(S),(U₁),(A),(CEN)) the whiskered instance is
-- literally another instance of the same rule, up to the arity
-- equations carried by the steps (`ins-irr`, `ins-arity`).  For the
-- rules mentioning renamings, idₖ + (r₁ + s + r₂) differs from
-- (idₖ + r₁) + s + r₂ only by casts (`+ʳ-assoc`); the casts are pushed
-- into the neighbouring substitution steps with `ins-conj` and
-- disappear (`rn-isCast`).
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.SubWhisker (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊
open import MFPS.Sub 𝕊
open import MFPS.SubCast 𝕊

private
  variable
    j k m n : ℕ

------------------------------------------------------------------------
-- The block-sum identities used, in the form  r ≗ c₂ ∘ X ∘ c₁
------------------------------------------------------------------------

-- idₖ + (r₁ + t)  ≗  cast ∘ ((idₖ + r₁) + t) ∘ cast
⊣-assoc : ∀ k {m₁ n₁ m₂ n₂} (r₁ : Ren m₁ n₁) (t : Ren m₂ n₂)
  → (idʳ {k} +ʳ (r₁ +ʳ t)) ≗ (castʳ (+-assoc k n₁ n₂) ∘ʳ ((idʳ {k} +ʳ r₁) +ʳ t) ∘ʳ castʳ (sym (+-assoc k m₁ m₂)))
⊣-assoc k {m₁} {n₁} {m₂} {n₂} r₁ t i = toℕ-injective (begin
  toℕ ((idʳ {k} +ʳ (r₁ +ʳ t)) i)
    ≡⟨ cong toℕ (sym (castʳ-refl' _)) ⟩
  toℕ (castʳ (trans (sym p) p) ((idʳ {k} +ʳ (r₁ +ʳ t)) i))
    ≡⟨ cong toℕ (sym (castʳ-∘ (sym p) p _)) ⟩
  toℕ (castʳ p (castʳ (sym p) ((idʳ {k} +ʳ (r₁ +ʳ t)) i)))
    ≡⟨ toℕ-castʳ p _ ⟩
  toℕ (castʳ (sym p) ((idʳ {k} +ʳ (r₁ +ʳ t)) i))
    ≡⟨ cong toℕ (cong (castʳ (sym p)) (cong (idʳ {k} +ʳ (r₁ +ʳ t)) (sym (castʳ-cancel i)))) ⟩
  toℕ (castʳ (sym p) ((idʳ {k} +ʳ (r₁ +ʳ t)) (castʳ q (castʳ (sym q) i))))
    ≡⟨ cong toℕ (+ʳ-assoc (idʳ {k}) r₁ t q (sym p) (castʳ (sym q) i)) ⟩
  toℕ (((idʳ {k} +ʳ r₁) +ʳ t) (castʳ (sym q) i))
    ≡⟨ sym (toℕ-castʳ (+-assoc k n₁ n₂) _) ⟩
  toℕ (castʳ (+-assoc k n₁ n₂) (((idʳ {k} +ʳ r₁) +ʳ t) (castʳ (sym q) i))) ∎)
  where
    open ≡-Reasoning
    p = +-assoc k n₁ n₂
    q = +-assoc k m₁ m₂
    castʳ-refl' : ∀ {n} (e : n ≡ n) {i : Fin n} → castʳ e i ≡ i
    castʳ-refl' e = castʳ-refl e _
    castʳ-cancel : ∀ (i : Fin (k + (m₁ + m₂))) → castʳ q (castʳ (sym q) i) ≡ i
    castʳ-cancel i = trans (castʳ-∘ (sym q) q i) (castʳ-refl _ i)

-- (r₁ + t) + idₖ  ≗  cast ∘ (r₁ + (t + idₖ)) ∘ cast
⊢-assoc : ∀ k {m₁ n₁ m₂ n₂} (r₁ : Ren m₁ n₁) (t : Ren m₂ n₂)
  → ((r₁ +ʳ t) +ʳ idʳ {k}) ≗ (castʳ (sym (+-assoc n₁ n₂ k)) ∘ʳ (r₁ +ʳ (t +ʳ idʳ {k})) ∘ʳ castʳ (+-assoc m₁ m₂ k))
⊢-assoc k {m₁} {n₁} {m₂} {n₂} r₁ t i =
  sym (+ʳ-assoc r₁ t (idʳ {k}) (+-assoc m₁ m₂ k) (sym (+-assoc n₁ n₂ k)) i)

-- (r₁ + (s + r₂)) + t  ≗  C₂ ∘ (r₁ + (s + (r₂ + t))) ∘ C₁   with cast-like C₁, C₂
module ⊢-assoc₂ {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄} (r₁ : Ren a₁ b₁) (s : Ren a₂ b₂) (r₂ : Ren a₃ b₃) (t : Ren a₄ b₄) where
  C₁ : Ren ((a₁ + (a₂ + a₃)) + a₄) (a₁ + (a₂ + (a₃ + a₄)))
  C₁ = (idʳ {a₁} +ʳ castʳ (+-assoc a₂ a₃ a₄)) ∘ʳ castʳ (+-assoc a₁ (a₂ + a₃) a₄)
  C₂ : Ren (b₁ + (b₂ + (b₃ + b₄))) ((b₁ + (b₂ + b₃)) + b₄)
  C₂ = castʳ (sym (+-assoc b₁ (b₂ + b₃) b₄)) ∘ʳ (idʳ {b₁} +ʳ castʳ (sym (+-assoc b₂ b₃ b₄)))
  C₁-isCast : IsCast C₁
  C₁-isCast = ∘ʳ-isCast' (idʳ {a₁} +ʳ castʳ (+-assoc a₂ a₃ a₄)) (castʳ (+-assoc a₁ (a₂ + a₃) a₄))
                (id+ʳ-isCast a₁ (+-assoc a₂ a₃ a₄) (castʳ-isCast (+-assoc a₂ a₃ a₄))) (castʳ-isCast (+-assoc a₁ (a₂ + a₃) a₄))
  C₂-isCast : IsCast C₂
  C₂-isCast = ∘ʳ-isCast' (castʳ (sym (+-assoc b₁ (b₂ + b₃) b₄))) (idʳ {b₁} +ʳ castʳ (sym (+-assoc b₂ b₃ b₄)))
                (castʳ-isCast (sym (+-assoc b₁ (b₂ + b₃) b₄))) (id+ʳ-isCast b₁ (sym (+-assoc b₂ b₃ b₄)) (castʳ-isCast (sym (+-assoc b₂ b₃ b₄))))
  eq : ((r₁ +ʳ (s +ʳ r₂)) +ʳ t) ≗ (C₂ ∘ʳ (r₁ +ʳ (s +ʳ (r₂ +ʳ t))) ∘ʳ C₁)
  eq i = begin
    ((r₁ +ʳ (s +ʳ r₂)) +ʳ t) i
      ≡⟨ sym (+ʳ-assoc r₁ (s +ʳ r₂) t p q i) ⟩
    castʳ q ((r₁ +ʳ ((s +ʳ r₂) +ʳ t)) (castʳ p i))
      ≡⟨ cong (castʳ q) (+ʳ-cong {r = r₁} {r' = r₁} (λ _ → refl) (λ j → sym (+ʳ-assoc s r₂ t p' q' j)) (castʳ p i)) ⟩
    castʳ q ((r₁ +ʳ (castʳ q' ∘ʳ (s +ʳ (r₂ +ʳ t)) ∘ʳ castʳ p')) (castʳ p i))
      ≡⟨ cong (castʳ q) (+ʳ-∘ (idʳ {b₁}) r₁ (castʳ q') ((s +ʳ (r₂ +ʳ t)) ∘ʳ castʳ p') (castʳ p i)) ⟩
    castʳ q ((idʳ {b₁} +ʳ castʳ q') ((r₁ +ʳ ((s +ʳ (r₂ +ʳ t)) ∘ʳ castʳ p')) (castʳ p i)))
      ≡⟨ cong (castʳ q ∘ʳ (idʳ {b₁} +ʳ castʳ q')) (+ʳ-∘ r₁ (idʳ {a₁}) (s +ʳ (r₂ +ʳ t)) (castʳ p') (castʳ p i)) ⟩
    castʳ q ((idʳ {b₁} +ʳ castʳ q') ((r₁ +ʳ (s +ʳ (r₂ +ʳ t))) ((idʳ {a₁} +ʳ castʳ p') (castʳ p i)))) ∎
    where
      open ≡-Reasoning
      p = +-assoc a₁ (a₂ + a₃) a₄
      q = sym (+-assoc b₁ (b₂ + b₃) b₄)
      p' = +-assoc a₂ a₃ a₄
      q' = sym (+-assoc b₂ b₃ b₄)

------------------------------------------------------------------------
-- Stability under whiskering
------------------------------------------------------------------------

module _ {Cart : ∀ {n} → Op n → Set} where

  -- the two block-sum identities as three-step rewrites of a renaming step
  rn-conj-⊣ : ∀ k {m₁ n₁ m₂ n₂} (r₁ : Ren m₁ n₁) (t : Ren m₂ n₂) {Γ : Word j (k + (n₁ + n₂))}
    → Cong Cart (rn (idʳ {k} +ʳ (r₁ +ʳ t)) ∷ Γ)
                (rn (castʳ (sym (+-assoc k m₁ m₂))) ∷ rn ((idʳ {k} +ʳ r₁) +ʳ t) ∷ rn (castʳ (+-assoc k n₁ n₂)) ∷ Γ)
  rn-conj-⊣ k r₁ t = rn-conj {c₁ = castʳ (sym (+-assoc k _ _))} {X = (idʳ {k} +ʳ r₁) +ʳ t} {c₂ = castʳ (+-assoc k _ _)} (⊣-assoc k r₁ t)

  rn-conj-⊢ : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄} (r₁ : Ren a₁ b₁) (s : Ren a₂ b₂) (r₂ : Ren a₃ b₃) (t : Ren a₄ b₄) {Γ : Word j ((b₁ + (b₂ + b₃)) + b₄)}
    → let module M = ⊢-assoc₂ r₁ s r₂ t in
      Cong Cart (rn ((r₁ +ʳ (s +ʳ r₂)) +ʳ t) ∷ Γ) (rn M.C₁ ∷ rn (r₁ +ʳ (s +ʳ (r₂ +ʳ t))) ∷ rn M.C₂ ∷ Γ)
  rn-conj-⊢ r₁ s r₂ t = rn-conj {c₁ = M.C₁} {X = r₁ +ʳ (s +ʳ (r₂ +ʳ t))} {c₂ = M.C₂} M.eq
    where module M = ⊢-assoc₂ r₁ s r₂ t

  ------------------------------------------------------------------
  -- left whiskering
  ------------------------------------------------------------------

  ⊣-stable : ∀ k {Γ Δ : Word m n} → Cong Cart Γ Δ → Cong Cart (k ⊣ʷ Γ) (k ⊣ʷ Δ)
  ⊣-stable k ≅-refl = ≅-refl
  ⊣-stable k (≅-sym e) = ≅-sym (⊣-stable k e)
  ⊣-stable k (≅-trans e e') = ≅-trans (⊣-stable k e) (⊣-stable k e')
  ⊣-stable k (≅-cong {Γ₁ = Γ₁} {Γ₁'} {Γ₂} {Γ₂'} e₁ e₂) =
    ≅-trans (≅-≡ (⊣ʷ-++ k Γ₁ Γ₂))
    (≅-trans (≅-cong (⊣-stable k e₁) (⊣-stable k e₂)) (≅-≡ (sym (⊣ʷ-++ k Γ₁' Γ₂'))))
  ⊣-stable k (I∙ n₁ n₂ p q e) = I∙ (k + n₁) n₂ _ _ e
  ⊣-stable k (E∙ e) = E∙ (+ʳ-cong (λ _ → refl) e)
  ⊣-stable k (S∙ n₁ n₂ {m} p q g) =
    ≅-sym (ins-conj (k + n₁) n₂ (Lp k n₁ refl) (Lp k n₁ refl) (Lp k n₁ p) (Lp k n₁ q) g
             (id+ʳ-isCast k q (castʳ-isCast q)) (id+ʳ-isCast k (sym p) (castʳ-isCast (sym p))))
  ⊣-stable k (U₁∙ n₁ n₂ p) = U₁∙ (k + n₁) n₂ (Lp k n₁ p)
  ⊣-stable k (U₂∙ {n}) = ≅-trans (E∙ (+ʳ-id k n)) U₂∙
  ⊣-stable k (A∙ m₁ m₂ n₁ n₂ {n} g h p₁ q₁ p₂ q₂ p₃) =
    ≅-trans (≅-∷ (ins-arity (sym (+-assoc k m₁ n₁)) refl (Lp k (m₁ + n₁) p₂) p₂' (Lp k (m₁ + n₁) q₂) q₂' h))
            (A∙ (k + m₁) m₂ n₁ n₂ g h (Lp k m₁ p₁) (Lp k m₁ q₁) p₂' q₂' (Lp k m₁ p₃))
    where
      p₂' = trans (Lp k (m₁ + n₁) p₂) (cong (_+ (n + (n₂ + m₂))) (sym (+-assoc k m₁ n₁)))
      q₂' = trans (Lp k (m₁ + n₁) q₂) (cong (_+ suc (n₂ + m₂)) (sym (+-assoc k m₁ n₁)))
  ⊣-stable k (R∙ r₁ r₂) = ≅-trans (R∙ _ _) (E∙ (λ i → sym (+ʳ-∘ idʳ idʳ r₂ r₁ i)))
  ⊣-stable k (N∙ {n₁} {n₂} {m₁} {m₂} {m'} {m} v r₁ s r₂) = ≅-trans lhs (≅-trans mid (≅-sym rhs))
    where
      -- LHS: {v} shifted, then [idₖ + (r₁ + s + r₂)];  normalise to
      --   [cast] {v}' [(idₖ+r₁) + s + r₂] [cast]
      lhs : Cong Cart (k ⊣ʷ (sub! n₁ n₂ v ∷ ⟦ rn (r₁ +ʳ s +ʳ r₂) ⟧))
                      (rn (castʳ (sym (+-assoc k n₁ (suc n₂)))) ∷ sub! (k + n₁) n₂ v ∷ rn ((idʳ {k} +ʳ r₁) +ʳ s +ʳ r₂) ∷ ⟦ rn (castʳ (+-assoc k m₁ (m' + m₂))) ⟧)
      lhs = ≅-trans (≅-∷ (rn-conj-⊣ k r₁ (s +ʳ r₂)))
            (≅-trans (≅-cong (ins-conjʳ (k + n₁) n₂ (Lp k n₁ refl) (Lp k n₁ refl) refl v (castʳ-isCast (sym (+-assoc k n₁ (m + n₂))))) ≅-refl)
            (≅-trans (≅-cong (S∙ (k + n₁) n₂ refl (Lp k n₁ refl) v) ≅-refl)
                     (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))))
      -- rule (N) in the middle
      mid : Cong Cart (rn (castʳ (sym (+-assoc k n₁ (suc n₂)))) ∷ sub! (k + n₁) n₂ v ∷ rn ((idʳ {k} +ʳ r₁) +ʳ s +ʳ r₂) ∷ ⟦ rn (castʳ (+-assoc k m₁ (m' + m₂))) ⟧)
                      (rn (castʳ (sym (+-assoc k n₁ (suc n₂)))) ∷ rn ((idʳ {k} +ʳ r₁) +ʳ idʳ {1} +ʳ r₂) ∷ sub! (k + m₁) m₂ (v [ s ]) ∷ ⟦ rn (castʳ (+-assoc k m₁ (m' + m₂))) ⟧)
      mid = ≅-∷ (≅-cong (N∙ v (idʳ {k} +ʳ r₁) s r₂) ≅-refl)
      -- RHS: [idₖ + (r₁ + id₁ + r₂)] {v[s]} shifted, normalised the same way
      rhs : Cong Cart (k ⊣ʷ (rn (r₁ +ʳ idʳ {1} +ʳ r₂) ∷ ⟦ sub! m₁ m₂ (v [ s ]) ⟧))
                      (rn (castʳ (sym (+-assoc k n₁ (suc n₂)))) ∷ rn ((idʳ {k} +ʳ r₁) +ʳ idʳ {1} +ʳ r₂) ∷ sub! (k + m₁) m₂ (v [ s ]) ∷ ⟦ rn (castʳ (+-assoc k m₁ (m' + m₂))) ⟧)
      rhs = ≅-trans (rn-conj-⊣ k r₁ (idʳ {1} +ʳ r₂))
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ (k + m₁) m₂ (Lp k m₁ refl) (Lp k m₁ refl) refl (v [ s ]) (castʳ-isCast (+-assoc k m₁ (1 + m₂))))))
            (≅-trans (≅-∷ (≅-∷ (S∙ (k + m₁) m₂ (Lp k m₁ refl) refl (v [ s ]))))
            (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
            (≅-trans (≅-∷ (≅-∷ (≅-∷ (rn-isCast-unique (castʳ-isCast _) (castʳ-isCast _)))))
                     (≅-∷ˡ (rn-isCast-unique (castʳ-isCast _) (castʳ-isCast _)))))))
  ⊣-stable k (Sℓ∙ m₁ m₂ {n} g p q q') = ≅-trans lhs (≅-trans mid (≅-sym rhs))
    where
      Z : Ren ((k + m₁) + ((1 + n) + m₂)) ((k + m₁) + ((n + 1) + m₂))
      Z = idʳ {k + m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂}
      e₁ = +-assoc k m₁ (suc (suc m₂))
      e₂ = +-assoc k m₁ (n + suc m₂)
      e₃ = +-assoc k m₁ ((n + 1) + m₂)
      q₁' : (k + m₁) + ((n + 1) + m₂) ≡ (k + m₁) + (n + suc m₂)
      q₁' = cong ((k + m₁) +_) (+-assoc n 1 m₂)
      P₁ = sym (+-assoc (k + m₁) 1 (n + m₂))
      Q₁ = sym (+-assoc (k + m₁) 1 (suc m₂))
      Q₁' : k + (m₁ + suc (suc m₂)) ≡ ((k + m₁) + 1) + suc m₂
      Q₁' = trans (sym e₁) Q₁
      -- both sides normalise to  [cast] {g}'' [cast ∘ Z] [cast]
      NF : Word (k + (m₁ + (n + suc m₂))) (k + (m₁ + suc (suc m₂)))
      NF = rn (castʳ (sym e₁)) ∷ ins ((k + m₁) + 1) m₂ P₁ Q₁ g ∷ rn (castʳ q₁' ∘ʳ Z) ∷ ⟦ rn (castʳ e₂) ⟧
      lhs : Cong Cart (k ⊣ʷ (rn (idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∷ ⟦ sub! m₁ (suc m₂) g ⟧))
                      (rn (castʳ (sym e₁)) ∷ rn (idʳ {k + m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∷ sub! (k + m₁) (suc m₂) g ∷ ⟦ rn (castʳ e₂) ⟧)
      lhs = ≅-trans (rn-conj-⊣ k (idʳ {m₁}) (σʳ 1 1 +ʳ idʳ {m₂}))
            (≅-trans (≅-∷ (rn-by (+ʳ-cong (+ʳ-id k m₁) (λ _ → refl))))
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ (k + m₁) (suc m₂) _ _ refl g (castʳ-isCast _))))
            (≅-trans (≅-∷ (≅-∷ (S∙ (k + m₁) (suc m₂) _ refl g)))
            (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
                     (≅-∷ (≅-∷ (≅-∷ (rn-isCast-unique (castʳ-isCast _) (castʳ-isCast e₂)))))))))
      mid : Cong Cart (rn (castʳ (sym e₁)) ∷ rn (idʳ {k + m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∷ sub! (k + m₁) (suc m₂) g ∷ ⟦ rn (castʳ e₂) ⟧) NF
      mid = ≅-∷ (≅-cong (Sℓ∙ (k + m₁) m₂ g P₁ Q₁ q₁') ≅-refl)
      rhs : Cong Cart (k ⊣ʷ (ins (m₁ + 1) m₂ p q g ∷ ⟦ rn (castʳ q' ∘ʳ (idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂})) ⟧)) NF
      rhs = ≅-trans (≅-∷ (rn-by (λ i → +ʳ-∘ (idʳ {k}) (idʳ {k}) (castʳ q') (idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂}) i)))
            (≅-trans (≅-∷ (≅-sym (rn-rn (idʳ {k} +ʳ (idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂})) (idʳ {k} +ʳ castʳ q'))))
            (≅-trans (≅-∷ (rn-conj-⊣ k (idʳ {m₁}) (σʳ 1 n +ʳ idʳ {m₂})))
            (≅-trans (≅-∷ (≅-∷ (rn-by (+ʳ-cong (+ʳ-id k m₁) (λ _ → refl)))))
            (≅-trans (≅-cong (ins-conjʳ (k + (m₁ + 1)) m₂ (Lp k (m₁ + 1) p) (Lp k (m₁ + 1) q) (trans (+-assoc k m₁ ((1 + n) + m₂)) (Lp k (m₁ + 1) p)) g (castʳ-isCast (sym (+-assoc k m₁ ((1 + n) + m₂))))) ≅-refl)
            (≅-trans (≅-cong (ins-arity (sym (+-assoc k m₁ 1)) refl (trans (+-assoc k m₁ ((1 + n) + m₂)) (Lp k (m₁ + 1) p)) P₁ (Lp k (m₁ + 1) q) Q₁' g) ≅-refl)
            (≅-trans (≅-∷ (rn-rn _ _))
            (≅-trans (≅-∷ (rn-rn _ _))
            (≅-trans (≅-∷ (rn-prefix ((idʳ {k} +ʳ castʳ q') ∘ʳ castʳ e₃) (castʳ e₂ ∘ʳ castʳ q₁')
                                 (∘ʳ-isCast' (idʳ {k} +ʳ castʳ q') (castʳ e₃) (id+ʳ-isCast k q' (castʳ-isCast q')) (castʳ-isCast e₃))
                                 (∘ʳ-isCast' (castʳ e₂) (castʳ q₁') (castʳ-isCast e₂) (castʳ-isCast q₁'))))
            (≅-trans (≅-∷ (≅-sym (rn-rn (castʳ q₁' ∘ʳ Z) (castʳ e₂))))
                     (≅-cong (≅-sym (ins-conjˡ ((k + m₁) + 1) m₂ P₁ Q₁ Q₁' g (castʳ-isCast (sym e₁)))) ≅-refl))))))))))
  ⊣-stable k (Sr∙ m₁ m₂ {n} g p q q' q'') = ≅-trans lhs (≅-trans mid (≅-sym rhs))
    where
      Z : Ren ((k + m₁) + ((n + 1) + m₂)) ((k + m₁) + ((1 + n) + m₂))
      Z = idʳ {k + m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}
      e₁ = +-assoc k m₁ (suc (suc m₂))
      e₂ = +-assoc k m₁ (n + suc m₂)
      e₃ = +-assoc k m₁ ((1 + n) + m₂)
      e₄ : k + ((m₁ + 1) + (n + m₂)) ≡ ((k + m₁) + 1) + (n + m₂)
      e₄ = trans (sym (+-assoc k (m₁ + 1) (n + m₂))) (cong (_+ (n + m₂)) (sym (+-assoc k m₁ 1)))
      q₁' : (k + m₁) + ((1 + n) + m₂) ≡ ((k + m₁) + 1) + (n + m₂)
      q₁' = sym (+-assoc (k + m₁) 1 (n + m₂))
      q₁'' : (k + m₁) + ((n + 1) + m₂) ≡ (k + m₁) + (n + suc m₂)
      q₁'' = cong ((k + m₁) +_) (+-assoc n 1 m₂)
      Q₁ : (k + m₁) + suc (suc m₂) ≡ ((k + m₁) + 1) + suc m₂
      Q₁ = sym (+-assoc (k + m₁) 1 (suc m₂))
      Q₂ : k + (m₁ + suc (suc m₂)) ≡ (k + m₁) + suc (suc m₂)
      Q₂ = sym e₁
      Q₂' : (k + m₁) + suc (suc m₂) ≡ (k + (m₁ + 1)) + suc m₂
      Q₂' = trans Q₁ (cong (_+ suc m₂) (+-assoc k m₁ 1))
      -- normal form:  [cast] {g}' [Z] [cast]   with {g}' = {k+m₁ ⊣ g ⊢ 1+m₂} re-sourced at Z's target
      NF : Word (k + ((m₁ + 1) + (n + m₂))) (k + (m₁ + suc (suc m₂)))
      NF = ins (k + m₁) (suc m₂) q₁'' Q₂ g ∷ rn Z ∷ ⟦ rn (castʳ (sym e₄) ∘ʳ castʳ q₁') ⟧
      lhs : Cong Cart (k ⊣ʷ (rn (idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∷ ⟦ ins (m₁ + 1) m₂ p q g ⟧))
                      (rn (castʳ (sym e₁)) ∷ rn (idʳ {k + m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∷ ins ((k + m₁) + 1) m₂ refl Q₁ g ∷ ⟦ rn (castʳ (sym e₄)) ⟧)
      lhs = ≅-trans (rn-conj-⊣ k (idʳ {m₁}) (σʳ 1 1 +ʳ idʳ {m₂}))
            (≅-trans (≅-∷ (rn-by (+ʳ-cong (+ʳ-id k m₁) (λ _ → refl))))
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ (k + (m₁ + 1)) m₂ (Lp k (m₁ + 1) p) (Lp k (m₁ + 1) q) Q₂' g (castʳ-isCast (+-assoc k m₁ (suc (suc m₂)))))))
            (≅-trans (≅-∷ (≅-∷ (ins-arity (sym (+-assoc k m₁ 1)) refl (Lp k (m₁ + 1) p) (trans (Lp k (m₁ + 1) p) (cong (_+ (n + m₂)) (sym (+-assoc k m₁ 1)))) Q₂' Q₁ g)))
                     (≅-∷ (≅-∷ (≅-sym (ins-conjʳ ((k + m₁) + 1) m₂ refl Q₁ _ g (castʳ-isCast (sym e₄)))))))))
      mid : Cong Cart (rn (castʳ (sym e₁)) ∷ rn (idʳ {k + m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∷ ins ((k + m₁) + 1) m₂ refl Q₁ g ∷ ⟦ rn (castʳ (sym e₄)) ⟧) NF
      mid = ≅-trans (≅-∷ (≅-cong (Sr∙ (k + m₁) m₂ g refl Q₁ q₁' (sym q₁'')) ≅-refl))
            (≅-trans (≅-∷ (≅-∷ (rn-conj {c₁ = castʳ (sym q₁'')} {X = Z} {c₂ = castʳ q₁'} (λ _ → refl))))
            (≅-trans (≅-∷ (≅-cong (ins-conjʳ (k + m₁) (suc m₂) refl refl q₁'' g (castʳ-isCast (sym q₁''))) ≅-refl))
            (≅-trans (≅-cong (ins-conjˡ (k + m₁) (suc m₂) q₁'' refl Q₂ g (castʳ-isCast (sym e₁))) ≅-refl)
                     (≅-∷ (≅-∷ (rn-rn _ _))))))
      rhs : Cong Cart (k ⊣ʷ (sub! m₁ (suc m₂) g ∷ ⟦ rn (castʳ q' ∘ʳ (idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}) ∘ʳ castʳ q'') ⟧)) NF
      rhs = ≅-trans (≅-∷ (rn-by (λ i → trans (+ʳ-∘ (idʳ {k}) (idʳ {k}) (castʳ q') ((idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}) ∘ʳ castʳ q'') i) (cong (idʳ {k} +ʳ castʳ q') (+ʳ-∘ (idʳ {k}) (idʳ {k}) (idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}) (castʳ q'') i)))))
            (≅-trans (≅-∷ (≅-sym (rn-rn ((idʳ {k} +ʳ (idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂})) ∘ʳ (idʳ {k} +ʳ castʳ q'')) (idʳ {k} +ʳ castʳ q'))))
            (≅-trans (≅-∷ (≅-sym (rn-rn (idʳ {k} +ʳ castʳ q'') (idʳ {k} +ʳ (idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂})))))
            (≅-trans (≅-∷ (≅-∷ (rn-conj-⊣ k (idʳ {m₁}) (σʳ n 1 +ʳ idʳ {m₂}))))
            (≅-trans (≅-∷ (≅-∷ (≅-∷ (rn-by (+ʳ-cong (+ʳ-id k m₁) (λ _ → refl))))))
            (≅-trans (≅-∷ (rn-rn _ _))
            (≅-trans (≅-cong (ins-conjʳ (k + m₁) (suc m₂) (Lp k m₁ refl) (Lp k m₁ refl) q₁'' g (∘ʳ-isCast' (castʳ (sym (+-assoc k m₁ ((n + 1) + m₂)))) (idʳ {k} +ʳ castʳ q'') (castʳ-isCast (sym (+-assoc k m₁ ((n + 1) + m₂)))) (id+ʳ-isCast k q'' (castʳ-isCast q'')))) ≅-refl)
            (≅-trans (≅-∷ (≅-∷ (rn-rn _ _)))
                     (≅-∷ (≅-∷ (rn-prefix ((idʳ {k} +ʳ castʳ q') ∘ʳ castʳ (+-assoc k m₁ ((1 + n) + m₂))) (castʳ (sym e₄) ∘ʳ castʳ q₁')
                                 (∘ʳ-isCast' (idʳ {k} +ʳ castʳ q') (castʳ (+-assoc k m₁ ((1 + n) + m₂))) (id+ʳ-isCast k q' (castʳ-isCast q')) (castʳ-isCast (+-assoc k m₁ ((1 + n) + m₂))))
                                 (∘ʳ-isCast' (castʳ (sym e₄)) (castʳ q₁') (castʳ-isCast (sym e₄)) (castʳ-isCast q₁'))))))))))))
  ⊣-stable k (CEN∙ m₁ m m₂ {n₁} {n₂} {k₃} g₁ g₂ c p q p' p'' q') = ≅-trans lhs (≅-sym rhs)
    where
      e₁ = +-assoc k m₁ (n₁ + (m + suc m₂))
      p₁ : (k + m₁) + (n₁ + (m + suc m₂)) ≡ ((k + m₁) + (n₁ + m)) + suc m₂
      p₁ = trans (cong ((k + m₁) +_) (sym (+-assoc n₁ m (suc m₂)))) (sym (+-assoc (k + m₁) (n₁ + m) (suc m₂)))
      q₁ : k + k₃ ≡ ((k + m₁) + (n₁ + m)) + (n₂ + m₂)
      q₁ = trans (cong (k +_) q) (trans (sym (+-assoc k (m₁ + (n₁ + m)) (n₂ + m₂))) (cong (_+ (n₂ + m₂)) (sym (+-assoc k m₁ (n₁ + m)))))
      p₁' : (k + m₁) + suc (m + suc m₂) ≡ ((k + m₁) + suc m) + suc m₂
      p₁' = sym (+-assoc (k + m₁) (suc m) (suc m₂))
      P'' : ((k + m₁) + suc m) + (n₂ + m₂) ≡ (k + m₁) + suc (m + (n₂ + m₂))
      P'' = +-assoc (k + m₁) (suc m) (n₂ + m₂)
      Q₃ : k + k₃ ≡ (k + m₁) + (n₁ + (m + (n₂ + m₂)))
      Q₃ = trans (cong (k +_) q') (sym (+-assoc k m₁ (n₁ + (m + (n₂ + m₂)))))
      e₅ : k + (m₁ + suc (m + (n₂ + m₂))) ≡ (k + m₁) + suc (m + (n₂ + m₂))
      e₅ = sym (+-assoc k m₁ (suc (m + (n₂ + m₂))))
      P₄ : k + (m₁ + suc (m + (n₂ + m₂))) ≡ ((k + m₁) + suc m) + (n₂ + m₂)
      P₄ = trans e₅ (sym P'')
      Q₄ : k + (m₁ + suc (m + suc m₂)) ≡ ((k + m₁) + suc m) + suc m₂
      Q₄ = trans (sym (+-assoc k m₁ (suc (m + suc m₂)))) p₁'
      NF : Word (k + k₃) (k + (m₁ + suc (m + suc m₂)))
      NF = ins ((k + m₁) + suc m) m₂ P₄ Q₄ g₂ ∷ ⟦ ins (k + m₁) (m + (n₂ + m₂)) Q₃ e₅ g₁ ⟧
      lhs : Cong Cart (k ⊣ʷ (sub! m₁ (m + suc m₂) g₁ ∷ ⟦ ins (m₁ + (n₁ + m)) m₂ q p g₂ ⟧)) NF
      lhs = ≅-trans (≅-∷ (ins-arity (sym (+-assoc k m₁ (n₁ + m))) refl (Lp k (m₁ + (n₁ + m)) q) q₁ (Lp k (m₁ + (n₁ + m)) p) (trans (Lp k (m₁ + (n₁ + m)) p) (cong (_+ suc m₂) (sym (+-assoc k m₁ (n₁ + m))))) g₂))
            (≅-trans (≅-cong (S∙ (k + m₁) (m + suc m₂) _ _ g₁) ≅-refl)
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ ((k + m₁) + (n₁ + m)) m₂ q₁ _ p₁ g₂ (castʳ-isCast _))))
            (≅-trans (≅-∷ (CEN∙ (k + m₁) m m₂ g₁ g₂ c p₁ q₁ p₁' P'' Q₃))
            (≅-trans (≅-cong (ins-conjˡ ((k + m₁) + suc m) m₂ (sym P'') p₁' Q₄ g₂ (castʳ-isCast _)) ≅-refl)
            (≅-trans (≅-cong (≅-sym (ins-conjʳ ((k + m₁) + suc m) m₂ P₄ Q₄ (sym P'') g₂ (castʳ-isCast e₅))) ≅-refl)
                     (≅-∷ (ins-conjˡ (k + m₁) (m + (n₂ + m₂)) Q₃ refl e₅ g₁ (castʳ-isCast e₅))))))))
      rhs : Cong Cart (k ⊣ʷ (ins (m₁ + suc m) m₂ (sym p'') p' g₂ ∷ ⟦ ins m₁ (m + (n₂ + m₂)) q' refl g₁ ⟧)) NF
      rhs = ≅-cong (ins-arity (sym (+-assoc k m₁ (suc m))) refl _ P₄ _ Q₄ g₂) (≅-≡ (cong ⟦_⟧ (ins-irr (k + m₁) (m + (n₂ + m₂)) _ Q₃ _ e₅ g₁)))
  ⊣-stable k (D∙ m₁ m₂ {n} g c) = ≅-trans lhs (≅-sym rhs)
    where
      W : Ren ((k + m₁) + m₂) ((k + m₁) + (n + m₂))
      W = idʳ {k + m₁} +ʳ !ʳ n +ʳ idʳ {m₂}
      e₁ = +-assoc k m₁ m₂
      e₂ = +-assoc k m₁ (n + m₂)
      NF : Word (k + (m₁ + (n + m₂))) (k + (m₁ + m₂))
      NF = ⟦ rn (castʳ e₂ ∘ʳ W ∘ʳ castʳ (sym e₁)) ⟧
      lhs : Cong Cart (k ⊣ʷ (rn (idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂}) ∷ ⟦ sub! m₁ m₂ g ⟧)) NF
      lhs = ≅-trans (rn-conj-⊣ k (idʳ {m₁}) (!ʳ 1 +ʳ idʳ {m₂}))
            (≅-trans (≅-∷ (rn-by (+ʳ-cong (+ʳ-id k m₁) (λ _ → refl))))
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ (k + m₁) m₂ _ _ refl g (castʳ-isCast _))))
            (≅-trans (≅-∷ (≅-∷ (S∙ (k + m₁) m₂ _ refl g)))
            (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
            (≅-trans (≅-∷ (≅-cong (D∙ (k + m₁) m₂ g c) ≅-refl))
            (≅-trans (≅-∷ (R∙ _ _))
            (≅-trans (R∙ _ _)
                     (E∙ (λ i → trans (cong (castʳ (sym (Lp k m₁ refl)) ∘ʳ W) (isCast-unique (castʳ-isCast (sym (+-assoc k m₁ m₂))) (castʳ-isCast (sym e₁)) i))
                                      (isCast-unique (castʳ-isCast (sym (Lp k m₁ refl))) (castʳ-isCast e₂) (W (castʳ (sym e₁) i))))))))))))
      rhs : Cong Cart (k ⊣ʷ ⟦ rn (idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂}) ⟧) NF
      rhs = ≅-trans (rn-conj-⊣ k (idʳ {m₁}) (!ʳ n +ʳ idʳ {m₂}))
            (≅-trans (≅-∷ (rn-by (+ʳ-cong (+ʳ-id k m₁) (λ _ → refl))))
            (≅-trans (rn-rn _ _) (rn-rn _ _)))
  ⊣-stable k (C∙ m₁ m₂ {n} g c p q) = ≅-trans lhs (≅-sym rhs)
    where
      W : Ren ((k + m₁) + ((n + n) + m₂)) ((k + m₁) + (n + m₂))
      W = idʳ {k + m₁} +ʳ Δʳ n +ʳ idʳ {m₂}
      e₁ = +-assoc k m₁ (suc (suc m₂))
      e₂ = +-assoc k m₁ (n + m₂)
      e₃ = +-assoc k m₁ ((n + n) + m₂)
      p₁ : (k + m₁) + (n + suc m₂) ≡ ((k + m₁) + n) + suc m₂
      p₁ = sym (+-assoc (k + m₁) n (suc m₂))
      q₁ : (k + m₁) + ((n + n) + m₂) ≡ ((k + m₁) + n) + (n + m₂)
      q₁ = trans (cong ((k + m₁) +_) (+-assoc n n m₂)) (sym (+-assoc (k + m₁) n (n + m₂)))
      Q₂ : k + (m₁ + suc (suc m₂)) ≡ (k + m₁) + suc (suc m₂)
      Q₂ = sym e₁
      P₂ : k + (m₁ + (n + suc m₂)) ≡ (k + m₁) + (n + suc m₂)
      P₂ = sym (+-assoc k m₁ (n + suc m₂))
      NF : Word (k + (m₁ + (n + m₂))) (k + (m₁ + suc (suc m₂)))
      NF = ins (k + m₁) (suc m₂) P₂ Q₂ g ∷ ins ((k + m₁) + n) m₂ q₁ (trans P₂ p₁) g ∷ ⟦ rn (castʳ e₂ ∘ʳ W) ⟧
      lhs : Cong Cart (k ⊣ʷ (rn (idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂}) ∷ ⟦ sub! m₁ m₂ g ⟧)) NF
      lhs = ≅-trans (rn-conj-⊣ k (idʳ {m₁}) (Δʳ 1 +ʳ idʳ {m₂}))
            (≅-trans (≅-∷ (rn-by (+ʳ-cong (+ʳ-id k m₁) (λ _ → refl))))
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ (k + m₁) m₂ _ _ refl g (castʳ-isCast _))))
            (≅-trans (≅-∷ (≅-∷ (S∙ (k + m₁) m₂ _ refl g)))
            (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
            (≅-trans (≅-∷ (≅-cong (C∙ (k + m₁) m₂ g c p₁ q₁) ≅-refl))
            (≅-trans (≅-cong (ins-conjˡ (k + m₁) (suc m₂) refl refl Q₂ g (castʳ-isCast _)) ≅-refl)
            (≅-trans (≅-cong (≅-sym (ins-conjʳ (k + m₁) (suc m₂) P₂ Q₂ refl g (castʳ-isCast P₂))) ≅-refl)
            (≅-trans (≅-∷ (≅-cong (ins-conjˡ ((k + m₁) + n) m₂ q₁ p₁ (trans P₂ p₁) g (castʳ-isCast P₂)) ≅-refl))
            (≅-trans (≅-∷ (≅-∷ (rn-rn _ _)))
                     (≅-∷ (≅-∷ (rn-prefix (castʳ (sym (Lp k m₁ refl))) (castʳ e₂) (castʳ-isCast (sym (Lp k m₁ refl))) (castʳ-isCast e₂)))))))))))))
      rhs : Cong Cart (k ⊣ʷ (sub! m₁ (suc m₂) g ∷ ins (m₁ + n) m₂ q p g ∷ ⟦ rn (idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}) ⟧)) NF
      rhs = ≅-trans (≅-∷ (≅-∷ (rn-conj-⊣ k (idʳ {m₁}) (Δʳ n +ʳ idʳ {m₂}))))
            (≅-trans (≅-∷ (≅-∷ (≅-∷ (rn-by (+ʳ-cong (+ʳ-id k m₁) (λ _ → refl))))))
            (≅-trans (≅-∷ (≅-cong (ins-conjʳ (k + (m₁ + n)) m₂ (Lp k (m₁ + n) q) (Lp k (m₁ + n) p) (trans (+-assoc k m₁ ((n + n) + m₂)) (Lp k (m₁ + n) q)) g (castʳ-isCast (sym (+-assoc k m₁ ((n + n) + m₂))))) ≅-refl))
            (≅-trans (≅-∷ (≅-cong (ins-arity (sym (+-assoc k m₁ n)) refl _ q₁ _ (trans P₂ p₁) g) ≅-refl))
            (≅-trans (≅-∷ˡ (≅-≡ (cong ⟦_⟧ (ins-irr (k + m₁) (suc m₂) (Lp k m₁ refl) P₂ (Lp k m₁ refl) Q₂ g))))
                     (≅-∷ (≅-∷ (rn-rn _ _)))))))


  ------------------------------------------------------------------
  -- right whiskering
  ------------------------------------------------------------------

  ⊢-stable : ∀ k {Γ Δ : Word m n} → Cong Cart Γ Δ → Cong Cart (Γ ⊢ʷ k) (Δ ⊢ʷ k)
  ⊢-stable k ≅-refl = ≅-refl
  ⊢-stable k (≅-sym e) = ≅-sym (⊢-stable k e)
  ⊢-stable k (≅-trans e e') = ≅-trans (⊢-stable k e) (⊢-stable k e')
  ⊢-stable k (≅-cong {Γ₁ = Γ₁} {Γ₁'} {Γ₂} {Γ₂'} e₁ e₂) =
    ≅-trans (≅-≡ (⊢ʷ-++ Γ₁ Γ₂ k))
    (≅-trans (≅-cong (⊢-stable k e₁) (⊢-stable k e₂)) (≅-≡ (sym (⊢ʷ-++ Γ₁' Γ₂' k))))
  ⊢-stable k (I∙ n₁ n₂ p q e) = I∙ n₁ (n₂ + k) _ _ e
  ⊢-stable k (E∙ e) = E∙ (+ʳ-cong e (λ _ → refl))
  ⊢-stable k (S∙ n₁ n₂ {m} p q g) =
    ≅-sym (ins-conj n₁ (n₂ + k) (Rp n₁ m n₂ k refl) (Rq n₁ n₂ k refl) (Rp n₁ m n₂ k p) (Rq n₁ n₂ k q) g
             (+ʳid-isCast k (castʳ q) q (castʳ-isCast q)) (+ʳid-isCast k (castʳ (sym p)) (sym p) (castʳ-isCast (sym p))))
  ⊢-stable k (U₁∙ n₁ n₂ p) =
    ≅-trans (≅-≡ (cong ⟦_⟧ (ins-irr n₁ (n₂ + k) (Rp n₁ 1 n₂ k p) (Rq n₁ n₂ k p) (Rq n₁ n₂ k p) (Rq n₁ n₂ k p) idₒ))) (U₁∙ n₁ (n₂ + k) (Rq n₁ n₂ k p))
  ⊢-stable k (U₂∙ {n}) = ≅-trans (E∙ (+ʳ-id n k)) U₂∙
  ⊢-stable k (A∙ m₁ m₂ n₁ n₂ {n} g h p₁ q₁ p₂ q₂ p₃) =
    ≅-trans (≅-∷ (ins-arity refl (+-assoc n₂ m₂ k) (Rp (m₁ + n₁) n (n₂ + m₂) k p₂) p₂' (Rq (m₁ + n₁) (n₂ + m₂) k q₂) q₂' h))
    (≅-trans (A∙ m₁ (m₂ + k) n₁ n₂ g h (Rp m₁ (n₁ + suc n₂) m₂ k p₁) (Rq m₁ m₂ k q₁) p₂' q₂' (Rp m₁ (n₁ + (n + n₂)) m₂ k p₃))
             (≅-≡ (cong ⟦_⟧ (ins-irr m₁ (m₂ + k) (Rp m₁ (n₁ + (n + n₂)) m₂ k p₃) (Rp m₁ (n₁ + (n + n₂)) m₂ k p₃) (Rq m₁ m₂ k q₁) (Rq m₁ m₂ k q₁) _))))
    where
      p₂' = trans (Rp (m₁ + n₁) n (n₂ + m₂) k p₂) (cong ((m₁ + n₁) +_) (cong (n +_) (+-assoc n₂ m₂ k)))
      q₂' = trans (Rq (m₁ + n₁) (n₂ + m₂) k q₂) (cong ((m₁ + n₁) +_) (cong suc (+-assoc n₂ m₂ k)))
  ⊢-stable k (R∙ r₁ r₂) = ≅-trans (R∙ _ _) (E∙ (λ i → sym (+ʳ-∘ r₂ r₁ idʳ idʳ i)))
  ⊢-stable k (N∙ {n₁} {n₂} {m₁} {m₂} {m'} {m} v r₁ s r₂) = ≅-trans lhs (≅-trans mid (≅-sym rhs))
    where
      module L = ⊢-assoc₂ r₁ s r₂ (idʳ {k})
      module R = ⊢-assoc₂ r₁ (idʳ {1}) r₂ (idʳ {k})
      Q : (n₁ + suc n₂) + k ≡ n₁ + suc (n₂ + k)
      Q = +-assoc n₁ (suc n₂) k
      NF : Word ((m₁ + (m' + m₂)) + k) ((n₁ + suc n₂) + k)
      NF = rn (castʳ Q) ∷ rn (r₁ +ʳ idʳ {1} +ʳ (r₂ +ʳ idʳ {k})) ∷ sub! m₁ (m₂ + k) (v [ s ]) ∷ ⟦ rn L.C₂ ⟧
      lhs : Cong Cart ((sub! n₁ n₂ v ∷ ⟦ rn (r₁ +ʳ s +ʳ r₂) ⟧) ⊢ʷ k)
                      (rn (castʳ Q) ∷ sub! n₁ (n₂ + k) v ∷ rn (r₁ +ʳ s +ʳ (r₂ +ʳ idʳ {k})) ∷ ⟦ rn L.C₂ ⟧)
      lhs = ≅-trans (≅-∷ (rn-conj-⊢ r₁ s r₂ (idʳ {k})))
            (≅-trans (≅-cong (ins-conjʳ n₁ (n₂ + k) _ _ refl v L.C₁-isCast) ≅-refl)
            (≅-trans (≅-cong (S∙ n₁ (n₂ + k) refl _ v) ≅-refl)
            (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
                     (≅-∷ˡ (rn-isCast-unique (castʳ-isCast _) (castʳ-isCast Q))))))
      mid : Cong Cart (rn (castʳ Q) ∷ sub! n₁ (n₂ + k) v ∷ rn (r₁ +ʳ s +ʳ (r₂ +ʳ idʳ {k})) ∷ ⟦ rn L.C₂ ⟧) NF
      mid = ≅-∷ (≅-cong (N∙ v r₁ s (r₂ +ʳ idʳ {k})) ≅-refl)
      rhs : Cong Cart ((rn (r₁ +ʳ idʳ {1} +ʳ r₂) ∷ ⟦ sub! m₁ m₂ (v [ s ]) ⟧) ⊢ʷ k) NF
      rhs = ≅-trans (rn-conj-⊢ r₁ (idʳ {1}) r₂ (idʳ {k}))
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ m₁ (m₂ + k) _ _ refl (v [ s ]) R.C₂-isCast)))
            (≅-trans (≅-∷ (≅-∷ (S∙ m₁ (m₂ + k) _ refl (v [ s ]))))
            (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
            (≅-trans (≅-∷ (≅-∷ (≅-∷ (rn-isCast-unique (castʳ-isCast _) L.C₂-isCast))))
                     (≅-∷ˡ (rn-isCast-unique R.C₁-isCast (castʳ-isCast Q)))))))
  ⊢-stable k (Sℓ∙ m₁ m₂ {n} g p q q') = ≅-trans lhs (≅-trans mid (≅-sym rhs))
    where
      module L = ⊢-assoc₂ (idʳ {m₁}) (σʳ 1 1) (idʳ {m₂}) (idʳ {k})
      module R = ⊢-assoc₂ (idʳ {m₁}) (σʳ 1 n) (idʳ {m₂}) (idʳ {k})
      Z : Ren (m₁ + ((1 + n) + (m₂ + k))) (m₁ + ((n + 1) + (m₂ + k)))
      Z = idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂ + k}
      e₂ : m₁ + (n + suc (m₂ + k)) ≡ (m₁ + (n + suc m₂)) + k
      e₂ = trans (cong (m₁ +_) (sym (+-assoc n (suc m₂) k))) (sym (+-assoc m₁ (n + suc m₂) k))
      p₁ : m₁ + ((1 + n) + (m₂ + k)) ≡ (m₁ + 1) + (n + (m₂ + k))
      p₁ = sym (+-assoc m₁ 1 (n + (m₂ + k)))
      q₁ : m₁ + suc (suc (m₂ + k)) ≡ (m₁ + 1) + suc (m₂ + k)
      q₁ = sym (+-assoc m₁ 1 (suc (m₂ + k)))
      q₁' : m₁ + ((n + 1) + (m₂ + k)) ≡ m₁ + (n + suc (m₂ + k))
      q₁' = cong (m₁ +_) (+-assoc n 1 (m₂ + k))
      Q₂ : (m₁ + suc (suc m₂)) + k ≡ (m₁ + 1) + suc (m₂ + k)
      Q₂ = trans (+-assoc m₁ (suc (suc m₂)) k) q₁
      NF : Word ((m₁ + (n + suc m₂)) + k) ((m₁ + suc (suc m₂)) + k)
      NF = ins (m₁ + 1) (m₂ + k) p₁ Q₂ g ∷ ⟦ rn (castʳ e₂ ∘ʳ castʳ q₁' ∘ʳ Z) ⟧
      lhs : Cong Cart ((rn (idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∷ ⟦ sub! m₁ (suc m₂) g ⟧) ⊢ʷ k) NF
      lhs = ≅-trans (rn-conj-⊢ (idʳ {m₁}) (σʳ 1 1) (idʳ {m₂}) (idʳ {k}))
            (≅-trans (≅-∷ (rn-by (+ʳ-cong {r = idʳ {m₁}} {r' = idʳ {m₁}} (λ _ → refl) (+ʳ-cong {r = σʳ 1 1} {r' = σʳ 1 1} (λ _ → refl) (+ʳ-id m₂ k)))))
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ m₁ (suc (m₂ + k)) _ _ refl g L.C₂-isCast)))
            (≅-trans (≅-∷ (≅-∷ (S∙ m₁ (suc (m₂ + k)) _ refl g)))
            (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
            (≅-trans (≅-∷ (≅-cong (Sℓ∙ m₁ (m₂ + k) g p₁ q₁ q₁') ≅-refl))
            (≅-trans (≅-cong (ins-conjˡ (m₁ + 1) (m₂ + k) p₁ q₁ Q₂ g L.C₁-isCast) ≅-refl)
            (≅-trans (≅-∷ (rn-rn _ _))
                     (≅-∷ (rn-prefix (castʳ (sym (Rp m₁ n (suc m₂) k refl)) ∘ʳ castʳ q₁') (castʳ e₂ ∘ʳ castʳ q₁')
                             (∘ʳ-isCast' (castʳ (sym (Rp m₁ n (suc m₂) k refl))) (castʳ q₁') (castʳ-isCast (sym (Rp m₁ n (suc m₂) k refl))) (castʳ-isCast q₁'))
                             (∘ʳ-isCast' (castʳ e₂) (castʳ q₁') (castʳ-isCast e₂) (castʳ-isCast q₁')))))))))))
      mid : Cong Cart NF NF
      mid = ≅-refl
      rhs : Cong Cart ((ins (m₁ + 1) m₂ p q g ∷ ⟦ rn (castʳ q' ∘ʳ (idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂})) ⟧) ⊢ʷ k) NF
      rhs = ≅-trans (≅-∷ (rn-by (λ i → +ʳ-∘ (castʳ q') (idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂}) (idʳ {k}) (idʳ {k}) i)))
            (≅-trans (≅-∷ (≅-sym (rn-rn ((idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂}) +ʳ idʳ {k}) (castʳ q' +ʳ idʳ {k}))))
            (≅-trans (≅-∷ (rn-conj-⊢ (idʳ {m₁}) (σʳ 1 n) (idʳ {m₂}) (idʳ {k})))
            (≅-trans (≅-∷ (≅-∷ (rn-by (+ʳ-cong {r = idʳ {m₁}} {r' = idʳ {m₁}} (λ _ → refl) (+ʳ-cong {r = σʳ 1 n} {r' = σʳ 1 n} (λ _ → refl) (+ʳ-id m₂ k))))))
            (≅-trans (≅-cong (ins-conjʳ (m₁ + 1) (m₂ + k) _ _ p₁ g R.C₁-isCast) ≅-refl)
            (≅-trans (≅-∷ˡ (≅-≡ (cong ⟦_⟧ (ins-irr (m₁ + 1) (m₂ + k) p₁ p₁ (Rq (m₁ + 1) m₂ k q) Q₂ g))))
            (≅-trans (≅-∷ (rn-rn _ _))
            (≅-trans (≅-∷ (rn-rn _ _))
                     (≅-∷ (rn-prefix ((castʳ q' +ʳ idʳ {k}) ∘ʳ R.C₂) (castʳ e₂ ∘ʳ castʳ q₁')
                             (∘ʳ-isCast (+ʳid-isCast k (castʳ q') q' (castʳ-isCast q')) R.C₂-isCast)
                             (∘ʳ-isCast (castʳ-isCast e₂) (castʳ-isCast q₁')))))))))))
  ⊢-stable k (Sr∙ m₁ m₂ {n} g p q q' q'') = ≅-trans lhs (≅-trans mid (≅-sym rhs))
    where
      module L = ⊢-assoc₂ (idʳ {m₁}) (σʳ 1 1) (idʳ {m₂}) (idʳ {k})
      module R = ⊢-assoc₂ (idʳ {m₁}) (σʳ n 1) (idʳ {m₂}) (idʳ {k})
      Z : Ren (m₁ + ((n + 1) + (m₂ + k))) (m₁ + ((1 + n) + (m₂ + k)))
      Z = idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂ + k}
      e₄ : ((m₁ + 1) + (n + m₂)) + k ≡ (m₁ + 1) + (n + (m₂ + k))
      e₄ = trans (+-assoc (m₁ + 1) (n + m₂) k) (cong ((m₁ + 1) +_) (+-assoc n m₂ k))
      q₁' : m₁ + ((1 + n) + (m₂ + k)) ≡ (m₁ + 1) + (n + (m₂ + k))
      q₁' = sym (+-assoc m₁ 1 (n + (m₂ + k)))
      q₁'' : m₁ + ((n + 1) + (m₂ + k)) ≡ m₁ + (n + suc (m₂ + k))
      q₁'' = cong (m₁ +_) (+-assoc n 1 (m₂ + k))
      Q₁ : m₁ + suc (suc (m₂ + k)) ≡ (m₁ + 1) + suc (m₂ + k)
      Q₁ = sym (+-assoc m₁ 1 (suc (m₂ + k)))
      Q₂ : (m₁ + suc (suc m₂)) + k ≡ m₁ + suc (suc (m₂ + k))
      Q₂ = +-assoc m₁ (suc (suc m₂)) k
      NF : Word (((m₁ + 1) + (n + m₂)) + k) ((m₁ + suc (suc m₂)) + k)
      NF = ins m₁ (suc (m₂ + k)) q₁'' Q₂ g ∷ rn Z ∷ ⟦ rn (castʳ (sym e₄) ∘ʳ castʳ q₁') ⟧
      lhs : Cong Cart ((rn (idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∷ ⟦ ins (m₁ + 1) m₂ p q g ⟧) ⊢ʷ k)
                      (rn L.C₁ ∷ rn (idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂ + k}) ∷ ins (m₁ + 1) (m₂ + k) refl Q₁ g ∷ ⟦ rn (castʳ (sym e₄)) ⟧)
      lhs = ≅-trans (rn-conj-⊢ (idʳ {m₁}) (σʳ 1 1) (idʳ {m₂}) (idʳ {k}))
            (≅-trans (≅-∷ (rn-by (+ʳ-cong {r = idʳ {m₁}} {r' = idʳ {m₁}} (λ _ → refl) (+ʳ-cong {r = σʳ 1 1} {r' = σʳ 1 1} (λ _ → refl) (+ʳ-id m₂ k)))))
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ (m₁ + 1) (m₂ + k) _ _ Q₁ g L.C₂-isCast)))
                     (≅-∷ (≅-∷ (≅-sym (ins-conjʳ (m₁ + 1) (m₂ + k) refl Q₁ _ g (castʳ-isCast (sym e₄))))))))
      mid : Cong Cart (rn L.C₁ ∷ rn (idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂ + k}) ∷ ins (m₁ + 1) (m₂ + k) refl Q₁ g ∷ ⟦ rn (castʳ (sym e₄)) ⟧) NF
      mid = ≅-trans (≅-∷ (≅-cong (Sr∙ m₁ (m₂ + k) g refl Q₁ q₁' (sym q₁'')) ≅-refl))
            (≅-trans (≅-∷ (≅-∷ (rn-conj {c₁ = castʳ (sym q₁'')} {X = Z} {c₂ = castʳ q₁'} (λ _ → refl))))
            (≅-trans (≅-∷ (≅-cong (ins-conjʳ m₁ (suc (m₂ + k)) refl refl q₁'' g (castʳ-isCast (sym q₁''))) ≅-refl))
            (≅-trans (≅-cong (ins-conjˡ m₁ (suc (m₂ + k)) q₁'' refl Q₂ g L.C₁-isCast) ≅-refl)
                     (≅-∷ (≅-∷ (rn-rn _ _))))))
      rhs : Cong Cart ((sub! m₁ (suc m₂) g ∷ ⟦ rn (castʳ q' ∘ʳ (idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}) ∘ʳ castʳ q'') ⟧) ⊢ʷ k) NF
      rhs = ≅-trans (≅-∷ (rn-by (λ i → trans (+ʳ-∘ (castʳ q') _ (idʳ {k}) (idʳ {k}) i) (cong (castʳ q' +ʳ idʳ {k}) (+ʳ-∘ (idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}) (castʳ q'') (idʳ {k}) (idʳ {k}) i)))))
            (≅-trans (≅-∷ (≅-sym (rn-rn (((idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}) +ʳ idʳ {k}) ∘ʳ (castʳ q'' +ʳ idʳ {k})) (castʳ q' +ʳ idʳ {k}))))
            (≅-trans (≅-∷ (≅-sym (rn-rn (castʳ q'' +ʳ idʳ {k}) ((idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}) +ʳ idʳ {k}))))
            (≅-trans (≅-∷ (≅-∷ (rn-conj-⊢ (idʳ {m₁}) (σʳ n 1) (idʳ {m₂}) (idʳ {k}))))
            (≅-trans (≅-∷ (≅-∷ (≅-∷ (rn-by (+ʳ-cong {r = idʳ {m₁}} {r' = idʳ {m₁}} (λ _ → refl) (+ʳ-cong {r = σʳ n 1} {r' = σʳ n 1} (λ _ → refl) (+ʳ-id m₂ k)))))))
            (≅-trans (≅-∷ (rn-rn _ _))
            (≅-trans (≅-cong (ins-conjʳ m₁ (suc (m₂ + k)) _ _ q₁'' g (∘ʳ-isCast' R.C₁ (castʳ q'' +ʳ idʳ {k}) R.C₁-isCast (+ʳid-isCast k (castʳ q'') q'' (castʳ-isCast q'')))) ≅-refl)
            (≅-trans (≅-∷ˡ (≅-≡ (cong ⟦_⟧ (ins-irr m₁ (suc (m₂ + k)) q₁'' q₁'' (Rq m₁ (suc m₂) k refl) Q₂ g))))
            (≅-trans (≅-∷ (≅-∷ (rn-rn _ _)))
                     (≅-∷ (≅-∷ (rn-prefix ((castʳ q' +ʳ idʳ {k}) ∘ʳ R.C₂) (castʳ (sym e₄) ∘ʳ castʳ q₁')
                                 (∘ʳ-isCast (+ʳid-isCast k (castʳ q') q' (castʳ-isCast q')) R.C₂-isCast)
                                 (∘ʳ-isCast (castʳ-isCast (sym e₄)) (castʳ-isCast q₁')))))))))))))
  ⊢-stable k (CEN∙ m₁ m m₂ {n₁} {n₂} {k₃} g₁ g₂ c p q p' p'' q') = ≅-trans lhs (≅-sym rhs)
    where
      P₀ : (m₁ + (n₁ + (m + suc m₂))) + k ≡ m₁ + (n₁ + (m + suc (m₂ + k)))
      P₀ = trans (+-assoc m₁ (n₁ + (m + suc m₂)) k) (cong (m₁ +_) (trans (+-assoc n₁ (m + suc m₂) k) (cong (n₁ +_) (+-assoc m (suc m₂) k))))
      Q₀ : (m₁ + suc (m + suc m₂)) + k ≡ m₁ + suc (m + suc (m₂ + k))
      Q₀ = trans (+-assoc m₁ (suc (m + suc m₂)) k) (cong (m₁ +_) (cong suc (+-assoc m (suc m₂) k)))
      p₁ : m₁ + (n₁ + (m + suc (m₂ + k))) ≡ (m₁ + (n₁ + m)) + suc (m₂ + k)
      p₁ = trans (cong (m₁ +_) (sym (+-assoc n₁ m (suc (m₂ + k))))) (sym (+-assoc m₁ (n₁ + m) (suc (m₂ + k))))
      q₁ : k₃ + k ≡ (m₁ + (n₁ + m)) + (n₂ + (m₂ + k))
      q₁ = trans (cong (_+ k) q) (trans (+-assoc (m₁ + (n₁ + m)) (n₂ + m₂) k) (cong ((m₁ + (n₁ + m)) +_) (+-assoc n₂ m₂ k)))
      p₁' : m₁ + suc (m + suc (m₂ + k)) ≡ (m₁ + suc m) + suc (m₂ + k)
      p₁' = sym (+-assoc m₁ (suc m) (suc (m₂ + k)))
      P'' : (m₁ + suc m) + (n₂ + (m₂ + k)) ≡ m₁ + suc (m + (n₂ + (m₂ + k)))
      P'' = +-assoc m₁ (suc m) (n₂ + (m₂ + k))
      Q₃ : k₃ + k ≡ m₁ + (n₁ + (m + (n₂ + (m₂ + k))))
      Q₃ = trans (cong (_+ k) q') (trans (+-assoc m₁ (n₁ + (m + (n₂ + m₂))) k) (cong (m₁ +_) (trans (+-assoc n₁ (m + (n₂ + m₂)) k) (cong (n₁ +_) (trans (+-assoc m (n₂ + m₂) k) (cong (m +_) (+-assoc n₂ m₂ k)))))))
      e₅ : (m₁ + suc (m + (n₂ + m₂))) + k ≡ m₁ + suc (m + (n₂ + (m₂ + k)))
      e₅ = trans (+-assoc m₁ (suc (m + (n₂ + m₂))) k) (cong (m₁ +_) (cong suc (trans (+-assoc m (n₂ + m₂) k) (cong (m +_) (+-assoc n₂ m₂ k)))))
      P₄ : (m₁ + suc (m + (n₂ + m₂))) + k ≡ (m₁ + suc m) + (n₂ + (m₂ + k))
      P₄ = trans e₅ (sym P'')
      Q₄ : (m₁ + suc (m + suc m₂)) + k ≡ (m₁ + suc m) + suc (m₂ + k)
      Q₄ = trans Q₀ p₁'
      NF : Word (k₃ + k) ((m₁ + suc (m + suc m₂)) + k)
      NF = ins (m₁ + suc m) (m₂ + k) P₄ Q₄ g₂ ∷ ⟦ ins m₁ (m + (n₂ + (m₂ + k))) Q₃ e₅ g₁ ⟧
      lhs : Cong Cart ((sub! m₁ (m + suc m₂) g₁ ∷ ⟦ ins (m₁ + (n₁ + m)) m₂ q p g₂ ⟧) ⊢ʷ k) NF
      lhs = ≅-trans (≅-cong (ins-arity refl (+-assoc m (suc m₂) k) _ P₀ _ Q₀ g₁) ≅-refl)
            (≅-trans (≅-cong (S∙ m₁ (m + suc (m₂ + k)) P₀ Q₀ g₁) ≅-refl)
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ (m₁ + (n₁ + m)) (m₂ + k) _ _ p₁ g₂ (castʳ-isCast _))))
            (≅-trans (≅-∷ (≅-∷ (≅-≡ (cong ⟦_⟧ (ins-irr (m₁ + (n₁ + m)) (m₂ + k) _ q₁ p₁ p₁ g₂)))))
            (≅-trans (≅-∷ (CEN∙ m₁ m (m₂ + k) g₁ g₂ c p₁ q₁ p₁' P'' Q₃))
            (≅-trans (≅-cong (ins-conjˡ (m₁ + suc m) (m₂ + k) (sym P'') p₁' Q₄ g₂ (castʳ-isCast _)) ≅-refl)
            (≅-trans (≅-cong (≅-sym (ins-conjʳ (m₁ + suc m) (m₂ + k) P₄ Q₄ (sym P'') g₂ (castʳ-isCast e₅))) ≅-refl)
                     (≅-∷ (ins-conjˡ m₁ (m + (n₂ + (m₂ + k))) Q₃ refl e₅ g₁ (castʳ-isCast e₅)))))))))
      rhs : Cong Cart ((ins (m₁ + suc m) m₂ (sym p'') p' g₂ ∷ ⟦ ins m₁ (m + (n₂ + m₂)) q' refl g₁ ⟧) ⊢ʷ k) NF
      rhs = ≅-cong (≅-≡ (cong ⟦_⟧ (ins-irr (m₁ + suc m) (m₂ + k) _ P₄ _ Q₄ g₂)))
                   (ins-arity refl (trans (+-assoc m (n₂ + m₂) k) (cong (m +_) (+-assoc n₂ m₂ k))) _ Q₃ _ e₅ g₁)
  ⊢-stable k (D∙ m₁ m₂ {n} g c) = ≅-trans lhs (≅-sym rhs)
    where
      module L = ⊢-assoc₂ (idʳ {m₁}) (!ʳ 1) (idʳ {m₂}) (idʳ {k})
      module R = ⊢-assoc₂ (idʳ {m₁}) (!ʳ n) (idʳ {m₂}) (idʳ {k})
      W : Ren (m₁ + (m₂ + k)) (m₁ + (n + (m₂ + k)))
      W = idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂ + k}
      P₀ : (m₁ + (n + m₂)) + k ≡ m₁ + (n + (m₂ + k))
      P₀ = trans (+-assoc m₁ (n + m₂) k) (cong (m₁ +_) (+-assoc n m₂ k))
      NF : Word ((m₁ + (n + m₂)) + k) ((m₁ + m₂) + k)
      NF = ⟦ rn (R.C₂ ∘ʳ W ∘ʳ R.C₁) ⟧
      lhs : Cong Cart ((rn (idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂}) ∷ ⟦ sub! m₁ m₂ g ⟧) ⊢ʷ k) NF
      lhs = ≅-trans (rn-conj-⊢ (idʳ {m₁}) (!ʳ 1) (idʳ {m₂}) (idʳ {k}))
            (≅-trans (≅-∷ (rn-by (+ʳ-cong {r = idʳ {m₁}} {r' = idʳ {m₁}} (λ _ → refl) (+ʳ-cong {r = !ʳ 1} {r' = !ʳ 1} (λ _ → refl) (+ʳ-id m₂ k)))))
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ m₁ (m₂ + k) _ _ refl g L.C₂-isCast)))
            (≅-trans (≅-∷ (≅-∷ (S∙ m₁ (m₂ + k) _ refl g)))
            (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
            (≅-trans (≅-∷ (≅-cong (D∙ m₁ (m₂ + k) g c) ≅-refl))
            (≅-trans (≅-∷ (R∙ _ _))
            (≅-trans (R∙ _ _)
                     (E∙ (λ i → trans (cong (castʳ (sym P₀) ∘ʳ W) (isCast-unique L.C₁-isCast R.C₁-isCast i))
                                      (isCast-unique (castʳ-isCast (sym P₀)) R.C₂-isCast (W (R.C₁ i))))))))))))
      rhs : Cong Cart (⟦ rn (idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂}) ⟧ ⊢ʷ k) NF
      rhs = ≅-trans (rn-conj-⊢ (idʳ {m₁}) (!ʳ n) (idʳ {m₂}) (idʳ {k}))
            (≅-trans (≅-∷ (rn-by (+ʳ-cong {r = idʳ {m₁}} {r' = idʳ {m₁}} (λ _ → refl) (+ʳ-cong {r = !ʳ n} {r' = !ʳ n} (λ _ → refl) (+ʳ-id m₂ k)))))
            (≅-trans (rn-rn _ _) (rn-rn _ _)))
  ⊢-stable k (C∙ m₁ m₂ {n} g c p q) = ≅-trans lhs (≅-sym rhs)
    where
      module L = ⊢-assoc₂ (idʳ {m₁}) (Δʳ 1) (idʳ {m₂}) (idʳ {k})
      module R = ⊢-assoc₂ (idʳ {m₁}) (Δʳ n) (idʳ {m₂}) (idʳ {k})
      W : Ren (m₁ + ((n + n) + (m₂ + k))) (m₁ + (n + (m₂ + k)))
      W = idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂ + k}
      e₂ : m₁ + (n + (m₂ + k)) ≡ (m₁ + (n + m₂)) + k
      e₂ = trans (cong (m₁ +_) (sym (+-assoc n m₂ k))) (sym (+-assoc m₁ (n + m₂) k))
      P₀ : (m₁ + (n + m₂)) + k ≡ m₁ + (n + (m₂ + k))
      P₀ = trans (+-assoc m₁ (n + m₂) k) (cong (m₁ +_) (+-assoc n m₂ k))
      e₆ : (m₁ + (n + suc m₂)) + k ≡ m₁ + (n + suc (m₂ + k))
      e₆ = trans (+-assoc m₁ (n + suc m₂) k) (cong (m₁ +_) (+-assoc n (suc m₂) k))
      p₁ : m₁ + (n + suc (m₂ + k)) ≡ (m₁ + n) + suc (m₂ + k)
      p₁ = sym (+-assoc m₁ n (suc (m₂ + k)))
      q₁ : m₁ + ((n + n) + (m₂ + k)) ≡ (m₁ + n) + (n + (m₂ + k))
      q₁ = trans (cong (m₁ +_) (+-assoc n n (m₂ + k))) (sym (+-assoc m₁ n (n + (m₂ + k))))
      Q₂ : (m₁ + suc (suc m₂)) + k ≡ m₁ + suc (suc (m₂ + k))
      Q₂ = +-assoc m₁ (suc (suc m₂)) k
      NF : Word ((m₁ + (n + m₂)) + k) ((m₁ + suc (suc m₂)) + k)
      NF = ins m₁ (suc (m₂ + k)) refl Q₂ g ∷ ins (m₁ + n) (m₂ + k) q₁ p₁ g ∷ ⟦ rn (castʳ e₂ ∘ʳ W) ⟧
      lhs : Cong Cart ((rn (idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂}) ∷ ⟦ sub! m₁ m₂ g ⟧) ⊢ʷ k) NF
      lhs = ≅-trans (rn-conj-⊢ (idʳ {m₁}) (Δʳ 1) (idʳ {m₂}) (idʳ {k}))
            (≅-trans (≅-∷ (rn-by (+ʳ-cong {r = idʳ {m₁}} {r' = idʳ {m₁}} (λ _ → refl) (+ʳ-cong {r = Δʳ 1} {r' = Δʳ 1} (λ _ → refl) (+ʳ-id m₂ k)))))
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ m₁ (m₂ + k) _ _ refl g L.C₂-isCast)))
            (≅-trans (≅-∷ (≅-∷ (S∙ m₁ (m₂ + k) _ refl g)))
            (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
            (≅-trans (≅-∷ (≅-cong (C∙ m₁ (m₂ + k) g c p₁ q₁) ≅-refl))
            (≅-trans (≅-cong (ins-conjˡ m₁ (suc (m₂ + k)) refl refl Q₂ g L.C₁-isCast) ≅-refl)
            (≅-trans (≅-∷ (≅-∷ (rn-rn _ _)))
                     (≅-∷ (≅-∷ (rn-prefix (castʳ (sym P₀)) (castʳ e₂) (castʳ-isCast (sym P₀)) (castʳ-isCast e₂)))))))))))
      rhs : Cong Cart ((sub! m₁ (suc m₂) g ∷ ins (m₁ + n) m₂ q p g ∷ ⟦ rn (idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}) ⟧) ⊢ʷ k) NF
      rhs = ≅-trans (≅-cong (≅-sym (ins-conjʳ m₁ (suc (m₂ + k)) refl _ _ g (castʳ-isCast (sym e₆)))) ≅-refl)
            (≅-trans (≅-∷ (≅-cong (ins-conjˡ (m₁ + n) (m₂ + k) _ _ p₁ g (castʳ-isCast (sym e₆))) ≅-refl))
            (≅-trans (≅-∷ (≅-∷ (rn-conj-⊢ (idʳ {m₁}) (Δʳ n) (idʳ {m₂}) (idʳ {k}))))
            (≅-trans (≅-∷ (≅-∷ (≅-∷ (rn-by (+ʳ-cong {r = idʳ {m₁}} {r' = idʳ {m₁}} (λ _ → refl) (+ʳ-cong {r = Δʳ n} {r' = Δʳ n} (λ _ → refl) (+ʳ-id m₂ k)))))))
            (≅-trans (≅-∷ (≅-cong (ins-conjʳ (m₁ + n) (m₂ + k) _ p₁ q₁ g R.C₁-isCast) ≅-refl))
            (≅-trans (≅-∷ (≅-∷ (rn-rn _ _)))
                     (≅-∷ (≅-∷ (rn-prefix R.C₂ (castʳ e₂) R.C₂-isCast (castʳ-isCast e₂)))))))))
