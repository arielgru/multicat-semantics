------------------------------------------------------------------------
-- Proposition 3.14(i): the symmetry of Sub.
--
-- σ_{m,n} is the renaming step [σʳ n m].  Its involutivity, unit and
-- hexagon laws are equations between renamings (Lemma 2.3) and are
-- discharged by (R), (E), (U₂).  Naturality of σ_{1,n} against a word
-- (the paper's "follows from (N) and (Sℓ),(Sr)") is proved by
-- induction on the word: against a renaming step it is a block-sum
-- identity; against a substitution step {n₁ ⊣ g ⊢ n₂} the single
-- variable is moved past n₂ (block-diagonal, rule (N)), past the hole
-- (rule (Sr)), and past n₁ (rule (N)), using the hexagon
-- decomposition of σ_{n₁+1+n₂,1}.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.SubSym (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊
open import MFPS.Sub 𝕊
open import MFPS.SubCast 𝕊
open import MFPS.SubStrict 𝕊 using (subst₂W-conj)
open import MFPS.SubWhisker 𝕊 using (⊣-stable; ⊢-stable)
open import MFPS.SubCentral 𝕊 using (conj-inv; id+ʳ-conj; ins-norm)

private
  variable
    j k m n m' n' : ℕ

-- the symmetry word
σʷ : ∀ m n → Word (m + n) (n + m)
σʷ m n = ⟦ rn (σʳ n m) ⟧

module _ {Cart : ∀ {n} → Op n → Set} where

  -- right-associative chaining of congruence proofs (reads top to bottom)
  infixr 2 _⟶_
  _⟶_ : {Γ Δ Θ : Word m n} → Cong Cart Γ Δ → Cong Cart Δ Θ → Cong Cart Γ Θ
  _⟶_ = ≅-trans

  σʷ-σʷ : ∀ m n → Cong Cart (σʷ n m ++ σʷ m n) ε
  σʷ-σʷ m n = ≅-trans (R∙ _ _) (≅-trans (E∙ (σʳ-σʳ m n)) U₂∙)

  σʷ-0ˡ : ∀ m (p : m + 0 ≡ m) → Cong Cart (subst₂W p refl (σʷ m 0)) ε
  σʷ-0ˡ m p =
    ≅-trans (subst₂W-conj p refl (σʷ m 0))
    (≅-trans (rn-rn _ _) (≅-trans (rn-rn _ _)
      (rn-isCast (∘ʳ-isCast' (castʳ p) (σʳ 0 m ∘ʳ castʳ (sym refl)) (castʳ-isCast p)
                              (∘ʳ-isCast' (σʳ 0 m) (castʳ (sym refl)) (σʳ-0ˡ-isCast m) (castʳ-isCast _))))))

  σʷ-0ʳ : ∀ m (p : m + 0 ≡ m) → Cong Cart (subst₂W refl p (σʷ 0 m)) ε
  σʷ-0ʳ m p =
    ≅-trans (subst₂W-conj refl p (σʷ 0 m))
    (≅-trans (rn-rn _ _) (≅-trans (rn-rn _ _)
      (rn-isCast (∘ʳ-isCast' (castʳ refl) (σʳ m 0 ∘ʳ castʳ (sym p)) (castʳ-isCast refl) (σʳ-0ʳ-isCast m p)))))

  -- transported identities are cast renaming steps
  castʷ : (q : m ≡ n) → Word m n
  castʷ {m} q = subst (Word m) q ε

  castʷ-rn : (q : m ≡ n) → Cong Cart (castʷ q) ⟦ rn (castʳ (sym q)) ⟧
  castʷ-rn refl = ≅-sym U₂∙

  -- hexagon laws
  σʷ-hexˡ : ∀ m n k (p : m + (n + k) ≡ (m + n) + k) (q : (n + m) + k ≡ n + (m + k)) (q' : n + (k + m) ≡ (n + k) + m)
    → Cong Cart (subst₂W p refl (σʷ m (n + k)))
                (castʷ q' ++ (n ⊣ʷ σʷ m k) ++ castʷ q ++ (σʷ m n ⊢ʷ k))
  σʷ-hexˡ m n k p q q' =
    ≅-trans (subst₂W-conj p refl (σʷ m (n + k)))
    (≅-trans (rn-rn _ _) (≅-trans (rn-rn _ _)
    (≅-trans (E∙ lemma)
    (≅-sym (≅-trans (≅-cong (castʷ-rn q') (≅-cong {Γ₁ = n ⊣ʷ σʷ m k} ≅-refl (≅-cong (castʷ-rn q) ≅-refl)))
           (≅-trans (rn-rn _ _) (≅-trans (rn-rn _ _) (rn-rn _ _))))))))
    where
      lemma : (castʳ p ∘ʳ σʳ (n + k) m ∘ʳ castʳ (sym refl))
            ≗ ((σʳ n m +ʳ idʳ {k}) ∘ʳ castʳ (sym q) ∘ʳ (idʳ {n} +ʳ σʳ k m) ∘ʳ castʳ (sym q'))
      lemma i = begin
        castʳ p (σʳ (n + k) m (castʳ (sym refl) i))
          ≡⟨ cong (castʳ p ∘ʳ σʳ (n + k) m) (castʳ-refl (sym refl) i) ⟩
        castʳ p (σʳ (n + k) m i)
          ≡⟨ cong (castʳ p) (σʳ-hexʳ n k m (sym q') (sym q) (sym p) i) ⟩
        castʳ p (castʳ (sym p) ((σʳ n m +ʳ idʳ {k}) (castʳ (sym q) ((idʳ {n} +ʳ σʳ k m) (castʳ (sym q') i)))))
          ≡⟨ trans (castʳ-∘ (sym p) p _) (castʳ-refl _ _) ⟩
        (σʳ n m +ʳ idʳ {k}) (castʳ (sym q) ((idʳ {n} +ʳ σʳ k m) (castʳ (sym q') i))) ∎
        where open ≡-Reasoning

  σʷ-hexʳ : ∀ m n k (p : (m + n) + k ≡ m + (n + k)) (q : m + (k + n) ≡ (m + k) + n) (q' : (k + m) + n ≡ k + (m + n))
    → Cong Cart (subst₂W p refl (σʷ (m + n) k))
                (castʷ q' ++ (σʷ m k ⊢ʷ n) ++ castʷ q ++ (m ⊣ʷ σʷ n k))
  σʷ-hexʳ m n k p q q' =
    ≅-trans (subst₂W-conj p refl (σʷ (m + n) k))
    (≅-trans (rn-rn _ _) (≅-trans (rn-rn _ _)
    (≅-trans (E∙ lemma)
    (≅-sym (≅-trans (≅-cong (castʷ-rn q') (≅-cong {Γ₁ = σʷ m k ⊢ʷ n} ≅-refl (≅-cong (castʷ-rn q) ≅-refl)))
           (≅-trans (rn-rn _ _) (≅-trans (rn-rn _ _) (rn-rn _ _))))))))
    where
      lemma : (castʳ p ∘ʳ σʳ k (m + n) ∘ʳ castʳ (sym refl))
            ≗ ((idʳ {m} +ʳ σʳ k n) ∘ʳ castʳ (sym q) ∘ʳ (σʳ k m +ʳ idʳ {n}) ∘ʳ castʳ (sym q'))
      lemma i = begin
        castʳ p (σʳ k (m + n) (castʳ (sym refl) i))
          ≡⟨ cong (castʳ p ∘ʳ σʳ k (m + n)) (castʳ-refl (sym refl) i) ⟩
        castʳ p (σʳ k (m + n) i)
          ≡⟨ cong (castʳ p) (σʳ-hexˡ k m n (sym q') (sym q) (sym p) i) ⟩
        castʳ p (castʳ (sym p) ((idʳ {m} +ʳ σʳ k n) (castʳ (sym q) ((σʳ k m +ʳ idʳ {n}) (castʳ (sym q') i)))))
          ≡⟨ trans (castʳ-∘ (sym p) p _) (castʳ-refl _ _) ⟩
        (idʳ {m} +ʳ σʳ k n) (castʳ (sym q) ((σʳ k m +ʳ idʳ {n}) (castʳ (sym q') i))) ∎
        where open ≡-Reasoning

  -- splitting a five-fold factorisation  c₂ ∘ A ∘ c ∘ B ∘ c₁  into steps (c₁ applied first)
  rn-split₅ : {r : Ren n m} {a b c d : ℕ} {c₁ : Ren n a} {B : Ren a b} {cc : Ren b c} {A : Ren c d} {c₂ : Ren d m}
    → r ≗ (c₂ ∘ʳ A ∘ʳ cc ∘ʳ B ∘ʳ c₁) → {Γ : Word j m}
    → Cong Cart (rn r ∷ Γ) (rn c₁ ∷ rn B ∷ rn cc ∷ rn A ∷ rn c₂ ∷ Γ)
  rn-split₅ {c₁ = c₁} {B} {cc} {A} {c₂} e =
    ≅-trans (rn-by e)
    (≅-trans (≅-sym (rn-rn (A ∘ʳ cc ∘ʳ B ∘ʳ c₁) c₂))
    (≅-trans (≅-sym (rn-rn (cc ∘ʳ B ∘ʳ c₁) A))
    (≅-trans (≅-sym (rn-rn (B ∘ʳ c₁) cc))
             (≅-sym (rn-rn c₁ B)))))

  -- whiskering a five-fold factorisation by an identity block
  id+ʳ-conj₅ : ∀ a {m n b c d e} {X : Ren m n} {c₁ : Ren m b} {B : Ren b c} {cc : Ren c d} {A : Ren d e} {c₂ : Ren e n}
    → X ≗ (c₂ ∘ʳ A ∘ʳ cc ∘ʳ B ∘ʳ c₁)
    → (idʳ {a} +ʳ X) ≗ ((idʳ {a} +ʳ c₂) ∘ʳ (idʳ {a} +ʳ A) ∘ʳ (idʳ {a} +ʳ cc) ∘ʳ (idʳ {a} +ʳ B) ∘ʳ (idʳ {a} +ʳ c₁))
  id+ʳ-conj₅ a {X = X} {c₁} {B} {cc} {A} {c₂} h i =
    trans (+ʳ-cong {r = idʳ {a}} {r' = idʳ {a}} (λ _ → refl) h i)
    (trans (+ʳ-∘ (idʳ {a}) (idʳ {a}) c₂ (A ∘ʳ cc ∘ʳ B ∘ʳ c₁) i)
    (cong (idʳ {a} +ʳ c₂)
      (trans (+ʳ-∘ (idʳ {a}) (idʳ {a}) A (cc ∘ʳ B ∘ʳ c₁) i)
      (cong (idʳ {a} +ʳ A)
        (trans (+ʳ-∘ (idʳ {a}) (idʳ {a}) cc (B ∘ʳ c₁) i)
        (cong (idʳ {a} +ʳ cc) (+ʳ-∘ (idʳ {a}) (idʳ {a}) B c₁ i)))))))

  -- the residual renamings after moving the hole: comparing two
  -- factorisations that differ only in their cast-like factors
  casts-eq : {a b c d e f : ℕ} {A₁ : Ren a b} {A₂ : Ren c d} {A₃ : Ren e f}
    {C₁ D₁ : Ren n a} {C₂ D₂ : Ren b c} {C₃ D₃ : Ren d e} {C₄ D₄ : Ren f m}
    → IsCast C₁ → IsCast D₁ → IsCast C₂ → IsCast D₂ → IsCast C₃ → IsCast D₃ → IsCast C₄ → IsCast D₄
    → (C₄ ∘ʳ A₃ ∘ʳ C₃ ∘ʳ A₂ ∘ʳ C₂ ∘ʳ A₁ ∘ʳ C₁) ≗ (D₄ ∘ʳ A₃ ∘ʳ D₃ ∘ʳ A₂ ∘ʳ D₂ ∘ʳ A₁ ∘ʳ D₁)
  casts-eq {A₁ = A₁} {A₂} {A₃} {C₁} {D₁} {C₂} {D₂} {C₃} {D₃} {C₄} {D₄} h₁ h₁' h₂ h₂' h₃ h₃' h₄ h₄' i =
    trans (cong (C₄ ∘ʳ A₃ ∘ʳ C₃ ∘ʳ A₂ ∘ʳ C₂ ∘ʳ A₁) (isCast-unique h₁ h₁' i))
    (trans (cong (C₄ ∘ʳ A₃ ∘ʳ C₃ ∘ʳ A₂) (isCast-unique h₂ h₂' _))
    (trans (cong (C₄ ∘ʳ A₃) (isCast-unique h₃ h₃' _)) (isCast-unique h₄ h₄' _)))

  ----------------------------------------------------------------------
  -- naturality of σ_{1,n} against a substitution step
  ----------------------------------------------------------------------
  natL-sub! : ∀ n₁ n₂ {kg} (g : Op kg)
    → Cong Cart (rn (σʳ (n₁ + (1 + n₂)) 1) ∷ ⟦ 1 ⊣ₛ sub! n₁ n₂ g ⟧)
                ((sub! n₁ n₂ g ⊢ₛ 1) ∷ ⟦ rn (σʳ (n₁ + (kg + n₂)) 1) ⟧)
  natL-sub! n₁ n₂ {kg} g = ≅-trans lhs (≅-sym rhs)
    where
      H = n₁ + (1 + n₂)
      K = n₁ + (kg + n₂)
      -- outer hexagon for σ_{H,1}
      p₀ : (n₁ + (1 + n₂)) + 1 ≡ n₁ + ((1 + n₂) + 1)
      p₀ = +-assoc n₁ (1 + n₂) 1
      q₀ : n₁ + (1 + (1 + n₂)) ≡ (n₁ + 1) + (1 + n₂)
      q₀ = sym (+-assoc n₁ 1 (1 + n₂))
      q₀' : (1 + n₁) + (1 + n₂) ≡ 1 + (n₁ + (1 + n₂))
      q₀' = +-assoc 1 n₁ (1 + n₂)
      -- inner hexagon for σ_{1+n₂,1}
      p₁ : (1 + n₂) + 1 ≡ 1 + (n₂ + 1)
      p₁ = +-assoc 1 n₂ 1
      q₁ : 1 + (1 + n₂) ≡ (1 + 1) + n₂
      q₁ = sym (+-assoc 1 1 n₂)
      q₁' : (1 + 1) + n₂ ≡ 1 + (1 + n₂)
      q₁' = +-assoc 1 1 n₂
      -- the same for the substituted arity K
      P₀ : (n₁ + (kg + n₂)) + 1 ≡ n₁ + ((kg + n₂) + 1)
      P₀ = +-assoc n₁ (kg + n₂) 1
      Q₀ : n₁ + (1 + (kg + n₂)) ≡ (n₁ + 1) + (kg + n₂)
      Q₀ = sym (+-assoc n₁ 1 (kg + n₂))
      Q₀' : (1 + n₁) + (kg + n₂) ≡ 1 + (n₁ + (kg + n₂))
      Q₀' = +-assoc 1 n₁ (kg + n₂)
      P₁ : (kg + n₂) + 1 ≡ kg + (n₂ + 1)
      P₁ = +-assoc kg n₂ 1
      Q₁ : kg + (1 + n₂) ≡ (kg + 1) + n₂
      Q₁ = sym (+-assoc kg 1 n₂)
      Q₁' : (1 + kg) + n₂ ≡ 1 + (kg + n₂)
      Q₁' = +-assoc 1 kg n₂
      -- pieces
      A₁ : Ren (n₁ + (kg + (n₂ + 1))) (n₁ + (kg + (1 + n₂)))
      A₁ = idʳ {n₁} +ʳ (idʳ {kg} +ʳ σʳ n₂ 1)
      A₂ : Ren (n₁ + ((kg + 1) + n₂)) (n₁ + ((1 + kg) + n₂))
      A₂ = idʳ {n₁} +ʳ (σʳ kg 1 +ʳ idʳ {n₂})
      A₃ : Ren ((n₁ + 1) + (kg + n₂)) ((1 + n₁) + (kg + n₂))
      A₃ = σʳ n₁ 1 +ʳ idʳ {kg + n₂}
      NF : Word (1 + K) (H + 1)
      NF = ins n₁ (n₂ + 1) (Rp n₁ kg n₂ 1 refl) (Rq n₁ n₂ 1 refl) g
           ∷ ⟦ rn (castʳ Q₀' ∘ʳ A₃ ∘ʳ castʳ Q₀ ∘ʳ (idʳ {n₁} +ʳ castʳ Q₁') ∘ʳ A₂ ∘ʳ (idʳ {n₁} +ʳ castʳ Q₁) ∘ʳ A₁ ∘ʳ (idʳ {n₁} +ʳ castʳ P₁) ∘ʳ castʳ P₀) ⟧
      rhs : Cong Cart ((sub! n₁ n₂ g ⊢ₛ 1) ∷ ⟦ rn (σʳ K 1) ⟧) NF
      rhs = ≅-∷ (rn-by (λ i → trans (σʳ-hexʳ n₁ (kg + n₂) 1 P₀ Q₀ Q₀' i)
                                  (cong (castʳ Q₀' ∘ʳ A₃ ∘ʳ castʳ Q₀)
                                        (id+ʳ-conj₅ n₁ {X = σʳ (kg + n₂) 1} {c₁ = castʳ P₁} {B = idʳ {kg} +ʳ σʳ n₂ 1} {cc = castʳ Q₁} {A = σʳ kg 1 +ʳ idʳ {n₂}} {c₂ = castʳ Q₁'}
                                           (σʳ-hexʳ kg n₂ 1 P₁ Q₁ Q₁') _))))
      L : 1 + K ≡ (1 + n₁) + (kg + n₂)
      L = Lp 1 n₁ refl
      q' : n₁ + ((1 + kg) + n₂) ≡ (n₁ + 1) + (kg + n₂)
      q' = sym (+-assoc n₁ 1 (kg + n₂))
      q'' : n₁ + (kg + suc n₂) ≡ n₁ + ((kg + 1) + n₂)
      q'' = cong (n₁ +_) (sym (+-assoc kg 1 n₂))
      Q₃ : n₁ + ((1 + 1) + n₂) ≡ (n₁ + 1) + suc n₂
      Q₃ = trans (cong (n₁ +_) q₁') q₀
      Q₅ : H + 1 ≡ n₁ + suc (n₂ + 1)
      Q₅ = Rq n₁ n₂ 1 refl
      -- the word after moving the hole, before re-assembling the residual renamings
      MID : Word (1 + K) (H + 1)
      MID = ins n₁ (n₂ + 1) refl Q₅ g
            ∷ rn (idʳ {n₁} +ʳ idʳ {kg} +ʳ σʳ n₂ 1)
            ∷ rn (castʳ q' ∘ʳ (idʳ {n₁} +ʳ σʳ kg 1 +ʳ idʳ {n₂}) ∘ʳ castʳ q'')
            ∷ rn (σʳ n₁ 1 +ʳ idʳ {kg} +ʳ idʳ {n₂})
            ∷ ⟦ rn (castʳ (sym L)) ⟧
      lhs : Cong Cart (rn (σʳ H 1) ∷ ⟦ 1 ⊣ₛ sub! n₁ n₂ g ⟧) NF
      lhs = to-mid ⟶ from-mid
        where
        to-mid : Cong Cart (rn (σʳ H 1) ∷ ⟦ 1 ⊣ₛ sub! n₁ n₂ g ⟧) MID
        to-mid =
          -- outer hexagon: σ_{H,1} = c₂ ∘ (σ_{n₁,1} + id) ∘ cc ∘ (id + σ_{1+n₂,1}) ∘ c₁
          rn-split₅ {c₁ = castʳ p₀} {B = idʳ {n₁} +ʳ σʳ (1 + n₂) 1} {cc = castʳ q₀}
                    {A = σʳ n₁ 1 +ʳ idʳ {1 + n₂}} {c₂ = castʳ q₀'} (σʳ-hexʳ n₁ (1 + n₂) 1 p₀ q₀ q₀')
          -- depth 4: absorb the cast c₂ into the substitution step
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (ins-conjˡ (1 + n₁) n₂ L (Lp 1 n₁ refl) refl g (castʳ-isCast q₀')))))
          -- depth 3: (S), (I), (N)⁻¹ move the hole past the block n₁
          ⟶ ≅-∷ (≅-∷ (≅-∷ (rn-by (+ʳ-cong {r = σʳ n₁ 1} {r' = σʳ n₁ 1} (λ _ → refl) (λ i → sym (+ʳ-id 1 n₂ i))))))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (S∙ (1 + n₁) n₂ L refl g))))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ refl) ⟧} (rn-isCast (castʳ-isCast refl)) ≅-refl))))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-∷ˡ (I∙ (1 + n₁) n₂ refl refl (≈.sym (ren-id g)))))))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-cong (≅-sym (N∙ g (σʳ n₁ 1) (idʳ {kg}) (idʳ {n₂}))) ≅-refl)))
          -- depth 2: absorb the cast cc
          ⟶ ≅-∷ (≅-∷ (≅-cong (ins-conjˡ (n₁ + 1) n₂ refl refl q₀ g (castʳ-isCast q₀)) ≅-refl))
          -- depth 1: inner hexagon for σ_{1+n₂,1}, whiskered by n₁
          ⟶ ≅-∷ (rn-split₅ {c₁ = idʳ {n₁} +ʳ castʳ p₁} {B = idʳ {n₁} +ʳ (idʳ {1} +ʳ σʳ n₂ 1)} {cc = idʳ {n₁} +ʳ castʳ q₁}
                            {A = idʳ {n₁} +ʳ (σʳ 1 1 +ʳ idʳ {n₂})} {c₂ = idʳ {n₁} +ʳ castʳ q₁'}
                   (id+ʳ-conj₅ n₁ {X = σʳ (1 + n₂) 1} {c₁ = castʳ p₁} {B = idʳ {1} +ʳ σʳ n₂ 1} {cc = castʳ q₁}
                               {A = σʳ 1 1 +ʳ idʳ {n₂}} {c₂ = castʳ q₁'} (σʳ-hexʳ 1 n₂ 1 p₁ q₁ q₁')))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-cong (ins-conjˡ (n₁ + 1) n₂ refl q₀ Q₃ g (id+ʳ-isCast n₁ q₁' (castʳ-isCast q₁'))) ≅-refl)))))
          -- (Sr): the hole moves past the single variable
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-cong (Sr∙ n₁ n₂ g refl Q₃ q' q'') ≅-refl))))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-cong (ins-conjˡ n₁ (suc n₂) refl refl (cong (n₁ +_) q₁) g (id+ʳ-isCast n₁ q₁ (castʳ-isCast q₁))) ≅-refl)))
          -- (S), (I), (N)⁻¹ move the hole past the block n₂
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-cong (S∙ n₁ (suc n₂) refl (cong (n₁ +_) q₁) g) ≅-refl)))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ (cong (n₁ +_) q₁)) ⟧} (rn-isCast (castʳ-isCast _)) ≅-refl)))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (≅-cong {Γ₁ = ⟦ rn (castʳ (sym refl)) ⟧} (rn-isCast (castʳ-isCast _)) ≅-refl))))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ˡ (I∙ n₁ (suc n₂) refl refl (≈.sym (ren-id g))))))
          ⟶ ≅-∷ (≅-∷ (≅-cong (≅-sym (N∙ g (idʳ {n₁}) (idʳ {kg}) (σʳ n₂ 1))) ≅-refl))
          -- absorb the two leading casts
          ⟶ rn-rn _ _
          ⟶ ≅-cong (ins-conjˡ n₁ (n₂ + 1) refl refl Q₅ g
                      (∘ʳ-isCast' (idʳ {n₁} +ʳ castʳ p₁) (castʳ p₀) (id+ʳ-isCast n₁ p₁ (castʳ-isCast p₁)) (castʳ-isCast p₀))) ≅-refl
        from-mid : Cong Cart MID NF
        from-mid =
          ≅-cong (≅-sym (ins-conjʳ n₁ (n₂ + 1) (Rp n₁ kg n₂ 1 refl) Q₅ refl g (castʳ-isCast (Rp n₁ kg n₂ 1 refl)))) ≅-refl
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (rn-by (+ʳ-cong {r = σʳ n₁ 1} {r' = σʳ n₁ 1} (λ _ → refl) (+ʳ-id kg n₂))))))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (≅-∷ (rn-rn _ _))))
          ⟶ ≅-∷ (≅-∷ (≅-∷ (rn-rn _ _)))
          ⟶ ≅-∷ (≅-∷ (rn-rn _ _))
          ⟶ ≅-∷ (rn-rn _ _)
          ⟶ ≅-∷ (E∙ (λ i → casts-eq {A₁ = A₁} {A₂} {A₃}
                            (castʳ-isCast (Rp n₁ kg n₂ 1 refl)) (∘ʳ-isCast' (idʳ {n₁} +ʳ castʳ P₁) (castʳ P₀) (id+ʳ-isCast n₁ P₁ (castʳ-isCast P₁)) (castʳ-isCast P₀))
                            (castʳ-isCast q'') (id+ʳ-isCast n₁ Q₁ (castʳ-isCast Q₁))
                            (castʳ-isCast q') (∘ʳ-isCast' (castʳ Q₀) (idʳ {n₁} +ʳ castʳ Q₁') (castʳ-isCast Q₀) (id+ʳ-isCast n₁ Q₁' (castʳ-isCast Q₁')))
                            (castʳ-isCast (sym L)) (castʳ-isCast Q₀') i))

  ----------------------------------------------------------------------
  -- naturality of σ_{1,n} against a renaming step: an identity of
  -- renamings, (id₁ + r) ∘ σ_{n,1} = σ_{m,1} ∘ (r + id₁), discharged by
  -- (R) and (E).  (Recall that [r] : Word m n for r : Ren n m.)
  ----------------------------------------------------------------------

  natL-rn : (r : Ren n m)
    → Cong Cart (rn (σʳ n 1) ∷ ⟦ rn (idʳ {1} +ʳ r) ⟧) (rn (r +ʳ idʳ {1}) ∷ ⟦ rn (σʳ m 1) ⟧)
  natL-rn {n} {m} r = R∙ _ _ ⟶ E∙ lemma ⟶ ≅-sym (R∙ _ _)
    where
      lemma : ((idʳ {1} +ʳ r) ∘ʳ σʳ n 1) ≗ (σʳ m 1 ∘ʳ (r +ʳ idʳ {1}))
      lemma = Fin+1-ext
        (λ j → trans (cong (idʳ {1} +ʳ r) (σʳ-inl n 1 j))
               (trans (+ʳ-inj₂ (idʳ {1}) r j)
                      (sym (trans (cong (σʳ m 1) (+ʳ-inj₁ r (idʳ {1}) j)) (σʳ-inl m 1 (r j))))))
        (trans (cong (idʳ {1} +ʳ r) (σʳ-inr n 1 zero))
               (trans (+ʳ-inj₁ (idʳ {1}) r zero)
                      (sym (trans (cong (σʳ m 1) (+ʳ-inj₂ r (idʳ {1}) zero)) (σʳ-inr m 1 zero)))))

  ----------------------------------------------------------------------
  -- naturality of σ_{1,n} against an arbitrary step: a substitution
  -- step with arity proofs p, q is, by (S), the on-the-nose step
  -- conjugated by cast renamings; whiskering is compatible with this
  -- (Prop. 3.14(i), `⊣-stable`/`⊢-stable`), and the casts move past σ
  -- by the renaming case.
  ----------------------------------------------------------------------

  natL-step : (s : Step m n)
    → Cong Cart (rn (σʳ n 1) ∷ ⟦ 1 ⊣ₛ s ⟧) ((s ⊢ₛ 1) ∷ ⟦ rn (σʳ m 1) ⟧)
  natL-step (rn r) = natL-rn r
  natL-step (ins n₁ n₂ p q g) =
    ≅-∷ (⊣-stable 1 (S∙ n₁ n₂ p q g))
    ⟶ ≅-cong (natL-rn (castʳ q)) ≅-refl
    ⟶ ≅-∷ (≅-cong (natL-sub! n₁ n₂ g) ≅-refl)
    ⟶ ≅-∷ (≅-∷ (natL-rn (castʳ (sym p))))
    ⟶ ≅-cong (≅-sym (⊢-stable 1 (S∙ n₁ n₂ p q g))) ≅-refl

  ----------------------------------------------------------------------
  -- Proposition 3.14(i), the axiom σ-nat₁ˡ of Def. 2.6:
  --   σ_{1,n} ∘ (1 ⊣ Γ) ≈ (Γ ⊢ 1) ∘ σ_{1,m}      for Γ : Word m n,
  -- by induction on the word, one step at a time.
  ----------------------------------------------------------------------

  natL : (Γ : Word m n)
    → Cong Cart (rn (σʳ n 1) ∷ (1 ⊣ʷ Γ)) ((Γ ⊢ʷ 1) ++ ⟦ rn (σʳ m 1) ⟧)
  natL ε       = ≅-refl
  natL (s ∷ Γ) = ≅-cong (natL-step s) ≅-refl ⟶ ≅-∷ (natL Γ)

  ----------------------------------------------------------------------
  -- The axiom σ-nat₁ʳ,  σ_{n,1} ∘ (Γ ⊢ 1) ≈ (1 ⊣ Γ) ∘ σ_{m,1},
  -- follows from σ-nat₁ˡ and the involution law: insert
  -- σ_{m,1} ∘ σ_{1,m} = id on the right, apply σ-nat₁ˡ backwards, and
  -- cancel σ_{n,1} ∘ σ_{1,n} on the left.
  ----------------------------------------------------------------------

  natR : (Γ : Word m n)
    → Cong Cart (rn (σʳ 1 n) ∷ (Γ ⊢ʷ 1)) ((1 ⊣ʷ Γ) ++ ⟦ rn (σʳ 1 m) ⟧)
  natR {m} {n} Γ =
    ≅-∷ (≅-≡ (sym (++-identityʳ (Γ ⊢ʷ 1))))
    ⟶ ≅-∷ (≅-cong {Γ₁ = Γ ⊢ʷ 1} ≅-refl (≅-sym (σʷ-σʷ m 1)))
    ⟶ ≅-∷ (≅-≡ (sym (++-assoc (Γ ⊢ʷ 1) ⟦ rn (σʳ m 1) ⟧ ⟦ rn (σʳ 1 m) ⟧)))
    ⟶ ≅-∷ (≅-cong (≅-sym (natL Γ)) ≅-refl)
    ⟶ ≅-cong (σʷ-σʷ 1 n) ≅-refl
