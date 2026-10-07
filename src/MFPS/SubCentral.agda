------------------------------------------------------------------------
-- Proposition 3.14(i)/(ii): centrality in the substitution categories.
--
-- Proof in words.  Centrality (Def. 2.7) of a word is reduced to the
-- interchange of pairs of *steps* placed on disjoint blocks of
-- variables.  Two renaming steps interchange because block sums are
-- functorial.  A substitution step and a renaming step interchange by
-- rule (N), since a renaming acting on the other block is
-- block-diagonal with respect to the hole.  Two substitution steps
-- interchange by rule (CEN), available when one of them has a `Cart`
-- operation.  Interchange is then closed under concatenation using the
-- functoriality of whiskering, which gives centrality of all words in
-- Sub× and of the J-image words in Sub_ℂ.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.SubCentral (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊
open import MFPS.Sub 𝕊
open import MFPS.SubCast 𝕊
open import MFPS.SubWhisker 𝕊 using (⊣-assoc; module ⊢-assoc₂; rn-conj-⊣; rn-conj-⊢; ⊣-stable; ⊢-stable)

private
  variable
    j k m n m' n' : ℕ

-- inverting a conjugation by casts
conj-inv : ∀ {m n a b} {X : Ren a b} {Y : Ren m n} (e₁ : b ≡ n) (e₂ : m ≡ a)
  → Y ≗ (castʳ e₁ ∘ʳ X ∘ʳ castʳ e₂) → X ≗ (castʳ (sym e₁) ∘ʳ Y ∘ʳ castʳ (sym e₂))
conj-inv {X = X} {Y} e₁ e₂ h i = begin
  X i
    ≡⟨ cong X (sym (trans (castʳ-∘ (sym e₂) e₂ i) (castʳ-refl _ i))) ⟩
  X (castʳ e₂ (castʳ (sym e₂) i))
    ≡⟨ sym (trans (castʳ-∘ e₁ (sym e₁) _) (castʳ-refl _ _)) ⟩
  castʳ (sym e₁) (castʳ e₁ (X (castʳ e₂ (castʳ (sym e₂) i))))
    ≡⟨ cong (castʳ (sym e₁)) (sym (h (castʳ (sym e₂) i))) ⟩
  castʳ (sym e₁) (Y (castʳ (sym e₂) i)) ∎
  where open ≡-Reasoning

-- idₐ + (id_b + t)  ≗  cast ∘ (id_{a+b} + t) ∘ cast
id+ʳ-assoc : ∀ a b {m n} (t : Ren m n)
  → (idʳ {a} +ʳ (idʳ {b} +ʳ t)) ≗ (castʳ (+-assoc a b n) ∘ʳ (idʳ {a + b} +ʳ t) ∘ʳ castʳ (sym (+-assoc a b m)))
id+ʳ-assoc a b t i = trans (⊣-assoc a (idʳ {b}) t i) (cong (castʳ _) (+ʳ-cong (+ʳ-id a b) (λ _ → refl) _))

-- and its inverse form:  id_{a+b} + t  ≗  cast ∘ (idₐ + (id_b + t)) ∘ cast
id+ʳ-assoc⁻¹ : ∀ a b {m n} (t : Ren m n)
  → (idʳ {a + b} +ʳ t) ≗ (castʳ (sym (+-assoc a b n)) ∘ʳ (idʳ {a} +ʳ (idʳ {b} +ʳ t)) ∘ʳ castʳ (sym (sym (+-assoc a b m))))
id+ʳ-assoc⁻¹ a b t = conj-inv (+-assoc a b _) (sym (+-assoc a b _)) (id+ʳ-assoc a b t)

-- a + (c ∘ Z ∘ c')  ≗  (a + c) ∘ (a + Z) ∘ (a + c')
id+ʳ-conj : ∀ a {m n b c} {X : Ren m n} {c₁ : Ren m b} {Z : Ren b c} {c₂ : Ren c n}
  → X ≗ (c₂ ∘ʳ Z ∘ʳ c₁) → (idʳ {a} +ʳ X) ≗ ((idʳ {a} +ʳ c₂) ∘ʳ (idʳ {a} +ʳ Z) ∘ʳ (idʳ {a} +ʳ c₁))
id+ʳ-conj a {X = X} {c₁} {Z} {c₂} h i =
  trans (+ʳ-cong {r = idʳ {a}} {r' = idʳ {a}} (λ _ → refl) h i)
        (trans (+ʳ-∘ (idʳ {a}) (idʳ {a}) c₂ (Z ∘ʳ c₁) i) (cong (idʳ {a} +ʳ c₂) (+ʳ-∘ (idʳ {a}) (idʳ {a}) Z c₁ i)))

module _ {Cart : ∀ {n} → Op n → Set} where

  -- interchange of two steps on disjoint blocks (first equation of Def. 2.7)
  Comm₁ : Step m n → Step m' n' → Set
  Comm₁ {m} {n} {m'} {n'} s t = Cong Cart ((s ⊢ₛ n') ∷ ⟦ m ⊣ₛ t ⟧) ((n ⊣ₛ t) ∷ ⟦ s ⊢ₛ m' ⟧)

  ----------------------------------------------------------------------
  -- renaming / renaming
  ----------------------------------------------------------------------
  comm-rn-rn : (r : Ren n m) (r' : Ren n' m') → Comm₁ (rn r) (rn r')
  comm-rn-rn {n = n} {m = m} {n' = n'} {m' = m'} r r' =
    ≅-trans (R∙ _ _) (≅-trans (E∙ (λ i → trans (sym (+ʳ-∘ (idʳ {m}) r r' (idʳ {n'}) i)) (+ʳ-∘ r (idʳ {n}) (idʳ {m'}) r' i))) (≅-sym (R∙ _ _)))

  ----------------------------------------------------------------------
  -- substitution / renaming, via (N): the renaming id + r' is
  -- block-diagonal with respect to the hole.
  ----------------------------------------------------------------------
  -- the block-diagonal form of  id_{n₁+(h+n₂)} + r'
  split-id : ∀ n₁ h n₂ (r' : Ren n' m') {Γ : Word j (n₁ + (h + n₂) + m')}
    → Cong Cart (rn (idʳ {n₁ + (h + n₂)} +ʳ r') ∷ Γ)
                (rn ((idʳ {n₁} +ʳ castʳ (sym (sym (+-assoc h n₂ n')))) ∘ʳ castʳ (sym (sym (+-assoc n₁ (h + n₂) n'))))
                  ∷ rn (idʳ {n₁} +ʳ idʳ {h} +ʳ (idʳ {n₂} +ʳ r'))
                  ∷ rn (castʳ (sym (+-assoc n₁ (h + n₂) m')) ∘ʳ (idʳ {n₁} +ʳ castʳ (sym (+-assoc h n₂ m')))) ∷ Γ)
  split-id {n' = n'} {m' = m'} n₁ h n₂ r' =
    ≅-trans (rn-conj {c₁ = castʳ (sym (sym (+-assoc n₁ (h + n₂) n')))} {X = idʳ {n₁} +ʳ (idʳ {h + n₂} +ʳ r')} {c₂ = castʳ (sym (+-assoc n₁ (h + n₂) m'))} (id+ʳ-assoc⁻¹ n₁ (h + n₂) r'))
    (≅-trans (≅-∷ (rn-conj {c₁ = idʳ {n₁} +ʳ castʳ (sym (sym (+-assoc h n₂ n')))} {X = idʳ {n₁} +ʳ (idʳ {h} +ʳ (idʳ {n₂} +ʳ r'))} {c₂ = idʳ {n₁} +ʳ castʳ (sym (+-assoc h n₂ m'))}
                      (id+ʳ-conj n₁ (id+ʳ-assoc⁻¹ h n₂ r'))))
    (≅-trans (rn-rn _ _)
             (≅-∷ (≅-∷ (rn-rn _ _)))))

  comm-ins-rn : ∀ n₁ n₂ {k} (g : Op k) (r' : Ren n' m') → Comm₁ (sub! n₁ n₂ g) (rn r')
  comm-ins-rn {n' = n'} {m' = m'} n₁ n₂ {k} g r' =
    ≅-trans (≅-∷ (split-id n₁ k n₂ r'))
    (≅-trans (≅-cong (ins-conjʳ n₁ (n₂ + n') _ _ refl g
                (∘ʳ-isCast' (idʳ {n₁} +ʳ castʳ (sym (sym (+-assoc k n₂ n')))) (castʳ (sym (sym (+-assoc n₁ (k + n₂) n'))))
                            (id+ʳ-isCast n₁ (sym (sym (+-assoc k n₂ n'))) (castʳ-isCast _)) (castʳ-isCast _))) ≅-refl)
    (≅-trans (≅-cong (S∙ n₁ (n₂ + n') refl _ g) ≅-refl)
    (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
    (≅-trans (≅-∷ (≅-cong (N∙ g (idʳ {n₁}) (idʳ {k}) (idʳ {n₂} +ʳ r')) ≅-refl))
    (≅-trans (≅-∷ (≅-∷ (≅-cong (I∙ n₁ (n₂ + m') refl refl (ren-id g)) ≅-refl)))
    (≅-sym
      (≅-trans (split-id n₁ 1 n₂ r')
      (≅-trans (≅-∷ (≅-∷ (ins-conjˡ n₁ (n₂ + m') _ _ refl g
                  (∘ʳ-isCast' (castʳ (sym (+-assoc n₁ (1 + n₂) m'))) (idʳ {n₁} +ʳ castʳ (sym (+-assoc 1 n₂ m')))
                              (castʳ-isCast _) (id+ʳ-isCast n₁ (sym (+-assoc 1 n₂ m')) (castʳ-isCast _))))))
      (≅-trans (≅-∷ (≅-∷ (S∙ n₁ (n₂ + m') _ refl g)))
      (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
      (≅-trans (≅-∷ (≅-∷ (≅-∷ (rn-isCast-unique (castʳ-isCast _)
                        (∘ʳ-isCast' (castʳ (sym (+-assoc n₁ (k + n₂) m'))) (idʳ {n₁} +ʳ castʳ (sym (+-assoc k n₂ m')))
                                    (castʳ-isCast _) (id+ʳ-isCast n₁ (sym (+-assoc k n₂ m')) (castʳ-isCast _)))))))
               (≅-∷ˡ (rn-isCast-unique
                        (∘ʳ-isCast' (idʳ {n₁} +ʳ castʳ (sym (sym (+-assoc 1 n₂ n')))) (castʳ (sym (sym (+-assoc n₁ (1 + n₂) n'))))
                                    (id+ʳ-isCast n₁ (sym (sym (+-assoc 1 n₂ n'))) (castʳ-isCast _)) (castʳ-isCast _))
                        (castʳ-isCast _))))))))))))))

  ----------------------------------------------------------------------
  -- renaming / substitution, via (N)  (mirror image of the previous case)
  ----------------------------------------------------------------------
  -- the block-diagonal form of  r + id_{n₁+(h+n₂)}
  split-idʳ : ∀ {n m} (r : Ren n m) n₁ h n₂ {Γ : Word j (m + (n₁ + (h + n₂)))}
    → Cong Cart (rn (r +ʳ idʳ {n₁ + (h + n₂)}) ∷ Γ)
                (rn (castʳ (sym (+-assoc n n₁ (h + n₂))))
                  ∷ rn ((r +ʳ idʳ {n₁}) +ʳ idʳ {h} +ʳ idʳ {n₂})
                  ∷ rn (castʳ (sym (sym (+-assoc m n₁ (h + n₂))))) ∷ Γ)
  split-idʳ {n = n} {m = m} r n₁ h n₂ =
    ≅-trans (rn-by (+ʳ-cong {r = r} {r' = r} (λ _ → refl) (λ i → sym (trans (+ʳ-cong {r = idʳ {n₁}} {r' = idʳ {n₁}} (λ _ → refl) (+ʳ-id h n₂) i) (+ʳ-id n₁ (h + n₂) i)))))
            (rn-conj {c₁ = castʳ (sym (+-assoc n n₁ (h + n₂)))} {X = (r +ʳ idʳ {n₁}) +ʳ (idʳ {h} +ʳ idʳ {n₂})} {c₂ = castʳ (sym (sym (+-assoc m n₁ (h + n₂))))}
                (conj-inv (sym (+-assoc m n₁ (h + n₂))) (+-assoc n n₁ (h + n₂))
                  (λ i → sym (+ʳ-assoc r (idʳ {n₁}) (idʳ {h} +ʳ idʳ {n₂}) (+-assoc n n₁ (h + n₂)) (sym (+-assoc m n₁ (h + n₂))) i))))

  comm-rn-ins : ∀ {n m} (r : Ren n m) n₁ n₂ {k} (g : Op k) → Comm₁ (rn r) (sub! n₁ n₂ g)
  comm-rn-ins {n = n} {m = m} r n₁ n₂ {k} g =
    ≅-trans (split-idʳ r n₁ 1 n₂)
    (≅-trans (≅-∷ (≅-∷ (ins-conjˡ (m + n₁) n₂ (Lp m n₁ refl) (Lp m n₁ refl) refl g (castʳ-isCast _))))
    (≅-trans (≅-∷ (≅-∷ (S∙ (m + n₁) n₂ (Lp m n₁ refl) refl g)))
    (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
    (≅-trans (≅-∷ (≅-∷ (≅-∷ˡ (I∙ (m + n₁) n₂ refl refl (≈.sym (ren-id g))))))
    (≅-trans (≅-∷ (≅-cong (≅-sym (N∙ g (r +ʳ idʳ {n₁}) (idʳ {k}) (idʳ {n₂}))) ≅-refl))
    (≅-sym
      (≅-trans (≅-∷ (split-idʳ r n₁ k n₂))
      (≅-trans (≅-cong (ins-conjʳ (n + n₁) n₂ (Lp n n₁ refl) (Lp n n₁ refl) refl g (castʳ-isCast _)) ≅-refl)
      (≅-trans (≅-cong (S∙ (n + n₁) n₂ refl (Lp n n₁ refl) g) ≅-refl)
      (≅-trans (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl)))
      (≅-trans (≅-∷ (≅-∷ (≅-∷ (rn-isCast-unique (castʳ-isCast _) (castʳ-isCast (sym (Lp m n₁ refl)))))))
               (≅-∷ˡ (rn-isCast-unique (castʳ-isCast _) (castʳ-isCast _))))))))))))))

  ----------------------------------------------------------------------
  -- substitution / substitution, via (CEN)
  ----------------------------------------------------------------------
  comm-ins-ins : ∀ n₁ n₂ {k₁} (g₁ : Op k₁) n₁' n₂' {k₂} (g₂ : Op k₂) → Cart g₁ ⊎ Cart g₂
    → Comm₁ (sub! n₁ n₂ g₁) (sub! n₁' n₂' g₂)
  comm-ins-ins n₁ n₂ {k₁} g₁ n₁' n₂' {k₂} g₂ c = ≅-trans lhs (≅-sym rhs)
    where
      A = n₁ + (k₁ + n₂)
      B = n₁ + suc n₂
      A' = n₁' + (k₂ + n₂')
      B' = n₁' + suc n₂'
      -- the arity equations of the (CEN) instance at m₁ = n₁, m = n₂ + n₁', m₂ = n₂'
      p : n₁ + (k₁ + ((n₂ + n₁') + suc n₂')) ≡ (n₁ + (k₁ + (n₂ + n₁'))) + suc n₂'
      p = trans (cong (n₁ +_) (sym (+-assoc k₁ (n₂ + n₁') (suc n₂')))) (sym (+-assoc n₁ (k₁ + (n₂ + n₁')) (suc n₂')))
      p' : n₁ + suc ((n₂ + n₁') + suc n₂') ≡ (n₁ + suc (n₂ + n₁')) + suc n₂'
      p' = sym (+-assoc n₁ (suc (n₂ + n₁')) (suc n₂'))
      p'' : (n₁ + suc (n₂ + n₁')) + (k₂ + n₂') ≡ n₁ + suc ((n₂ + n₁') + (k₂ + n₂'))
      p'' = +-assoc n₁ (suc (n₂ + n₁')) (k₂ + n₂')
      q' : A + A' ≡ n₁ + (k₁ + ((n₂ + n₁') + (k₂ + n₂')))
      q' = trans (+-assoc n₁ (k₁ + n₂) A') (cong (n₁ +_) (trans (+-assoc k₁ n₂ A') (cong (k₁ +_) (sym (+-assoc n₂ n₁' (k₂ + n₂'))))))
      q : A + A' ≡ (n₁ + (k₁ + (n₂ + n₁'))) + (k₂ + n₂')
      q = trans q' (trans (cong (n₁ +_) (sym (+-assoc k₁ (n₂ + n₁') (k₂ + n₂')))) (sym (+-assoc n₁ (k₁ + (n₂ + n₁')) (k₂ + n₂'))))
      -- the common normal form
      Q₃ : B + B' ≡ (n₁ + suc (n₂ + n₁')) + suc n₂'
      Q₃ = trans (+-assoc n₁ (suc n₂) B') (trans (cong (n₁ +_) (cong suc (sym (+-assoc n₂ n₁' (suc n₂'))))) p')
      e₅ : B + A' ≡ n₁ + suc ((n₂ + n₁') + (k₂ + n₂'))
      e₅ = trans (+-assoc n₁ (suc n₂) A') (cong (n₁ +_) (cong suc (sym (+-assoc n₂ n₁' (k₂ + n₂')))))
      NF : Word (A + A') (B + B')
      NF = ins (n₁ + suc (n₂ + n₁')) n₂' (trans e₅ (sym p'')) Q₃ g₂ ∷ ⟦ ins n₁ ((n₂ + n₁') + (k₂ + n₂')) q' e₅ g₁ ⟧
      P₂ : A + B' ≡ n₁ + (k₁ + ((n₂ + n₁') + suc n₂'))
      P₂ = trans (Rp n₁ k₁ n₂ B' refl) (cong (λ z → n₁ + (k₁ + z)) (sym (+-assoc n₂ n₁' (suc n₂'))))
      Q₂ : B + B' ≡ n₁ + suc ((n₂ + n₁') + suc n₂')
      Q₂ = trans (Rq n₁ n₂ B' refl) (cong (λ z → n₁ + suc z) (sym (+-assoc n₂ n₁' (suc n₂'))))
      lhs : Cong Cart (ins n₁ (n₂ + B') (Rp n₁ k₁ n₂ B' refl) (Rq n₁ n₂ B' refl) g₁ ∷ ⟦ ins (A + n₁') n₂' (Lp A n₁' refl) (Lp A n₁' refl) g₂ ⟧) NF
      lhs = ≅-trans (≅-cong (ins-arity refl (sym (+-assoc n₂ n₁' (suc n₂'))) _ P₂ _ Q₂ g₁) ≅-refl)
            (≅-trans (≅-cong (S∙ n₁ ((n₂ + n₁') + suc n₂') P₂ Q₂ g₁) ≅-refl)
            (≅-trans (≅-∷ (≅-∷ (ins-conjˡ (A + n₁') n₂' (Lp A n₁' refl) (Lp A n₁' refl) (trans (sym P₂) (Lp A n₁' refl)) g₂ (castʳ-isCast _))))
            (≅-trans (≅-∷ (≅-∷ (ins-arity (trans (+-assoc n₁ (k₁ + n₂) n₁') (cong (n₁ +_) (+-assoc k₁ n₂ n₁'))) refl _ q _ p g₂)))
            (≅-trans (≅-∷ (CEN∙ n₁ (n₂ + n₁') n₂' g₁ g₂ c p q p' p'' q'))
            (≅-trans (≅-cong (ins-conjˡ (n₁ + suc (n₂ + n₁')) n₂' (sym p'') p' Q₃ g₂ (castʳ-isCast _)) ≅-refl)
            (≅-trans (≅-cong (≅-sym (ins-conjʳ (n₁ + suc (n₂ + n₁')) n₂' (trans e₅ (sym p'')) Q₃ (sym p'') g₂ (castʳ-isCast e₅))) ≅-refl)
                     (≅-∷ (ins-conjˡ n₁ ((n₂ + n₁') + (k₂ + n₂')) q' refl e₅ g₁ (castʳ-isCast e₅)))))))))
      rhs : Cong Cart (ins (B + n₁') n₂' (Lp B n₁' refl) (Lp B n₁' refl) g₂ ∷ ⟦ ins n₁ (n₂ + A') (Rp n₁ k₁ n₂ A' refl) (Rq n₁ n₂ A' refl) g₁ ⟧) NF
      rhs = ≅-cong (ins-arity (trans (+-assoc n₁ (suc n₂) n₁') (cong (n₁ +_) refl)) refl _ (trans e₅ (sym p'')) _ Q₃ g₂)
                   (ins-arity refl (sym (+-assoc n₂ n₁' (k₂ + n₂'))) _ q' _ e₅ g₁)

  ----------------------------------------------------------------------
  -- From steps to words
  ----------------------------------------------------------------------

  -- a step commutes with every exact step (renaming step or on-the-nose substitution)
  Comm₁-exact : Step m n → Set
  Comm₁-exact s = (∀ {n' m'} (r : Ren n' m') → Comm₁ s (rn r) × Comm₁ (rn r) s)
                × (∀ n₁ n₂ {k} (g : Op k) → Comm₁ s (sub! n₁ n₂ g) × Comm₁ (sub! n₁ n₂ g) s)

  exact-rn : (r : Ren n m) → Comm₁-exact (rn r)
  exact-rn r = (λ r' → comm-rn-rn r r' , comm-rn-rn r' r) , (λ n₁ n₂ g → comm-rn-ins r n₁ n₂ g , comm-ins-rn n₁ n₂ g r)

  exact-sub! : ∀ n₁ n₂ {k} {g : Op k} → Cart g → Comm₁-exact (sub! n₁ n₂ g)
  exact-sub! n₁ n₂ {g = g} c =
    (λ r' → comm-ins-rn n₁ n₂ g r' , comm-rn-ins r' n₁ n₂ g)
    , (λ n₁' n₂' g' → comm-ins-ins n₁ n₂ g n₁' n₂' g' (inj₁ c) , comm-ins-ins n₁' n₂' g' n₁ n₂ g (inj₂ c))

  -- the two interchange equations of a step against a word
  CommW : Step m n → Word m' n' → Set
  CommW {m} {n} {m'} {n'} s Δ = Cong Cart ((s ⊢ₛ n') ∷ (m ⊣ʷ Δ)) ((n ⊣ʷ Δ) ++ ⟦ s ⊢ₛ m' ⟧)

  CommW' : Word m' n' → Step m n → Set
  CommW' {m'} {n'} {m} {n} Δ s = Cong Cart ((Δ ⊢ʷ n) ++ ⟦ m' ⊣ₛ s ⟧) ((n' ⊣ₛ s) ∷ (Δ ⊢ʷ m))

  commW-ε : (s : Step m n) → CommW s (ε {n'})
  commW-ε s = ≅-refl

  commW-∷ : (s : Step m n) (t : Step k n') {Δ : Word m' k} → Comm₁ s t → CommW s Δ → CommW s (t ∷ Δ)
  commW-∷ s t {Δ} c₁ cΔ = ≅-trans (≅-cong {Γ₁ = (s ⊢ₛ _) ∷ ⟦ _ ⊣ₛ t ⟧} c₁ ≅-refl) (≅-∷ cΔ)

  commW'-ε : (s : Step m n) → CommW' (ε {n'}) s
  commW'-ε s = ≅-refl

  commW'-∷ : (s : Step m n) (t : Step k n') {Δ : Word m' k} → Comm₁ t s → CommW' Δ s → CommW' (t ∷ Δ) s
  commW'-∷ {m = m} s t {Δ} c₁ cΔ = ≅-trans (≅-∷ cΔ) (≅-cong {Γ₁ = (t ⊢ₛ _) ∷ ⟦ _ ⊣ₛ s ⟧} c₁ ≅-refl)

  -- a general substitution step is the conjugate of an on-the-nose one
  ins-norm : ∀ n₁ n₂ {k a b} (p : a ≡ n₁ + (k + n₂)) (q : b ≡ n₁ + suc n₂) (g : Op k) {Δ : Word j a}
    → Cong Cart (ins n₁ n₂ p q g ∷ Δ) (rn (castʳ q) ∷ sub! n₁ n₂ g ∷ rn (castʳ (sym p)) ∷ Δ)
  ins-norm n₁ n₂ p q g = ≅-cong (S∙ n₁ n₂ p q g) ≅-refl

  commW : (s : Step m n) → Comm₁-exact s → (Δ : Word m' n') → CommW s Δ
  commW s e ε = commW-ε s
  commW s e (rn r ∷ Δ) = commW-∷ s (rn r) (proj₁ (proj₁ e r)) (commW s e Δ)
  commW {m} {n} {m'} s e (ins n₁ n₂ p q g ∷ Δ) =
    ≅-trans (≅-∷ (⊣-stable m (ins-norm n₁ n₂ p q g {Δ})))
    (≅-trans (commW-∷ s (rn (castʳ q)) (proj₁ (proj₁ e (castʳ q)))
             (commW-∷ s (sub! n₁ n₂ g) (proj₁ (proj₂ e n₁ n₂ g))
             (commW-∷ s (rn (castʳ (sym p))) (proj₁ (proj₁ e (castʳ (sym p)))) (commW s e Δ))))
             (≅-cong {Γ₁ = n ⊣ʷ (rn (castʳ q) ∷ sub! n₁ n₂ g ∷ rn (castʳ (sym p)) ∷ Δ)} {Γ₂ = ⟦ s ⊢ₛ m' ⟧}
                     (⊣-stable n (≅-sym (ins-norm n₁ n₂ p q g {Δ}))) ≅-refl))

  commW' : (s : Step m n) → Comm₁-exact s → (Δ : Word m' n') → CommW' Δ s
  commW' s e ε = commW'-ε s
  commW' s e (rn r ∷ Δ) = commW'-∷ s (rn r) (proj₂ (proj₁ e r)) (commW' s e Δ)
  commW' {m} {n} {m'} s e (ins n₁ n₂ p q g ∷ Δ) =
    ≅-trans (≅-cong {Γ₁ = (ins n₁ n₂ p q g ∷ Δ) ⊢ʷ n} {Γ₂ = ⟦ m' ⊣ₛ s ⟧} (⊢-stable n (ins-norm n₁ n₂ p q g {Δ})) ≅-refl)
    (≅-trans (commW'-∷ s (rn (castʳ q)) {sub! n₁ n₂ g ∷ rn (castʳ (sym p)) ∷ Δ} (proj₂ (proj₁ e (castʳ q)))
             (commW'-∷ s (sub! n₁ n₂ g) {rn (castʳ (sym p)) ∷ Δ} (proj₂ (proj₂ e n₁ n₂ g))
             (commW'-∷ s (rn (castʳ (sym p))) {Δ} (proj₂ (proj₁ e (castʳ (sym p)))) (commW' s e Δ))))
             (≅-∷ {s = _ ⊣ₛ s} (⊢-stable m (≅-sym (ins-norm n₁ n₂ p q g {Δ})))))

  ----------------------------------------------------------------------
  -- Centrality of words (Def. 2.7 in Sub)
  ----------------------------------------------------------------------

  Eq₁ : Word m n → Word m' n' → Set
  Eq₁ {m} {n} {m'} {n'} Γ Δ = Cong Cart ((Γ ⊢ʷ n') ++ (m ⊣ʷ Δ)) ((n ⊣ʷ Δ) ++ (Γ ⊢ʷ m'))

  CentralW : Word m n → Set
  CentralW Γ = ∀ {m' n'} (Δ : Word m' n') → Eq₁ Γ Δ × Eq₁ Δ Γ

  central-step : (s : Step m n) → Comm₁-exact s → CentralW ⟦ s ⟧
  central-step s e Δ = commW s e Δ , commW' s e Δ

  central-rn : (r : Ren n m) → CentralW ⟦ rn r ⟧
  central-rn r = central-step (rn r) (exact-rn r)

  central-sub! : ∀ n₁ n₂ {k} {g : Op k} → Cart g → CentralW ⟦ sub! n₁ n₂ g ⟧
  central-sub! n₁ n₂ c = central-step (sub! n₁ n₂ _) (exact-sub! n₁ n₂ c)

  central-ε : CentralW (ε {n})
  central-ε Δ = ≅-≡ (sym (++-identityʳ _)) , ≅-≡ (++-identityʳ _)

  central-≅ : {Γ Γ' : Word m n} → Cong Cart Γ Γ' → CentralW Γ → CentralW Γ'
  central-≅ {m} {n} e c Δ =
      ≅-trans (≅-cong (⊢-stable _ (≅-sym e)) ≅-refl) (≅-trans (proj₁ (c Δ)) (≅-cong ≅-refl (⊢-stable _ e)))
    , ≅-trans (≅-cong ≅-refl (⊣-stable _ (≅-sym e))) (≅-trans (proj₂ (c Δ)) (≅-cong (⊣-stable _ e) ≅-refl))

  central-++ : {Γ₁ : Word k n} {Γ₂ : Word m k} → CentralW Γ₁ → CentralW Γ₂ → CentralW (Γ₁ ++ Γ₂)
  central-++ {k} {n} {m} {Γ₁} {Γ₂} c₁ c₂ {m'} {n'} Δ =
      ≅-trans (≅-≡ (cong (_++ (m ⊣ʷ Δ)) (⊢ʷ-++ Γ₁ Γ₂ n')))
      (≅-trans (≅-≡ (++-assoc (Γ₁ ⊢ʷ n') (Γ₂ ⊢ʷ n') (m ⊣ʷ Δ)))
      (≅-trans (≅-cong {Γ₁ = Γ₁ ⊢ʷ n'} ≅-refl (proj₁ (c₂ Δ)))
      (≅-trans (≅-≡ (sym (++-assoc (Γ₁ ⊢ʷ n') (k ⊣ʷ Δ) (Γ₂ ⊢ʷ m'))))
      (≅-trans (≅-cong (proj₁ (c₁ Δ)) ≅-refl)
      (≅-trans (≅-≡ (++-assoc (n ⊣ʷ Δ) (Γ₁ ⊢ʷ m') (Γ₂ ⊢ʷ m')))
               (≅-≡ (cong ((n ⊣ʷ Δ) ++_) (sym (⊢ʷ-++ Γ₁ Γ₂ m')))))))))
    , ≅-trans (≅-≡ (cong ((Δ ⊢ʷ n) ++_) (⊣ʷ-++ m' Γ₁ Γ₂)))
      (≅-trans (≅-≡ (sym (++-assoc (Δ ⊢ʷ n) (m' ⊣ʷ Γ₁) (m' ⊣ʷ Γ₂))))
      (≅-trans (≅-cong (proj₂ (c₁ Δ)) ≅-refl)
      (≅-trans (≅-≡ (++-assoc (n' ⊣ʷ Γ₁) (Δ ⊢ʷ k) (m' ⊣ʷ Γ₂)))
      (≅-trans (≅-cong {Γ₁ = n' ⊣ʷ Γ₁} ≅-refl (proj₂ (c₂ Δ)))
      (≅-trans (≅-≡ (sym (++-assoc (n' ⊣ʷ Γ₁) (n' ⊣ʷ Γ₂) (Δ ⊢ʷ m))))
               (≅-≡ (cong (_++ (Δ ⊢ʷ m)) (sym (⊣ʷ-++ n' Γ₁ Γ₂)))))))))

  central-ins : ∀ n₁ n₂ {k a b} (p : a ≡ n₁ + (k + n₂)) (q : b ≡ n₁ + suc n₂) {g : Op k} → Cart g
    → CentralW ⟦ ins n₁ n₂ p q g ⟧
  central-ins n₁ n₂ p q {g} c =
    central-≅ (≅-sym (S∙ n₁ n₂ p q g))
      (central-++ {Γ₁ = ⟦ rn (castʳ q) ⟧} (central-rn _)
        (central-++ {Γ₁ = ⟦ sub! n₁ n₂ g ⟧} (central-sub! n₁ n₂ c) (central-rn _)))

  -- every word whose substitution steps carry Cart operations is central
  AllCart : Word m n → Set
  AllCart ε = ⊤
  AllCart (ins n₁ n₂ p q g ∷ Γ) = Cart g × AllCart Γ
  AllCart (rn r ∷ Γ) = AllCart Γ

  central-word : (Γ : Word m n) → AllCart Γ → CentralW Γ
  central-word ε _ = central-ε
  central-word (ins n₁ n₂ p q g ∷ Γ) (c , a) = central-++ {Γ₁ = ⟦ ins n₁ n₂ p q g ⟧} (central-ins n₁ n₂ p q c) (central-word Γ a)
  central-word (rn r ∷ Γ) a = central-++ {Γ₁ = ⟦ rn r ⟧} (central-rn r) (central-word Γ a)
