------------------------------------------------------------------------
-- Section 3.3–3.4: the free substitution construction.
--
-- Words of single substitutions and renamings over a symmetric
-- Ren-cartesian preoperad ℂ, the congruence of Fig. 3, pre-substitution
-- application ⋆ (Def. 3.15), soundness of the congruence (Thm. 3.16),
-- the presheaf structure (Cor. 3.17) and representability (Thm. 3.18).
--
-- Orientation.  A word Γ : Word m n is a morphism m → n of Sub_ℂ.  It
-- acts on f ∈ ℂ(n) and returns f ⋆ Γ ∈ ℂ(m).  The head of the list is
-- the step applied first, i.e. the step adjacent to the *target* n:
--
--     f ⋆ (s ∷ Γ) = (f ⋆₁ s) ⋆ Γ .
--
-- NOTE (paper issue).  Def. 3.11(ii) equips a word (Γ₁,…,Γ_k) : m → n
-- with arities m = m₀, m₁, …, m_k = n, i.e. the head is adjacent to
-- the *source*; but Def. 3.15 and Def. A.5 consume the list head-first
-- starting from an n-ary operation, which forces the head to be
-- adjacent to the *target*.  We follow Def. 3.15 / A.5 / Ex. 3.10.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad

module MFPS.Sub (𝕊 : SymPreoperad) where

open SymPreoperad 𝕊

private
  variable
    j k m n : ℕ

------------------------------------------------------------------------
-- Definition 3.11: single substitutions, renamings, pre-substitutions
--
-- A substitution step {n₁ ⊣ g ⊢ n₂} (g ∈ ℂ(m)) is a morphism
-- n₁ + m + n₂ → n₁ + 1 + n₂.  We let the step carry proofs that its
-- source/target are *equal* to those arities, so that whiskering and
-- the rule (A) can be stated without inserting explicit casts.
-- A renaming step [r] : m → n is given by r ∈ Ren (n ⇒ m) (Renᵒᵖ).
------------------------------------------------------------------------

data Step : ℕ → ℕ → Set where
  ins : ∀ n₁ n₂ {m k k'} → k ≡ n₁ + (m + n₂) → k' ≡ n₁ + suc n₂ → Op m → Step k k'
  rn  : Ren n m → Step m n

infixr 5 _∷_
data Word : ℕ → ℕ → Set where
  ε   : Word n n
  _∷_ : Step k n → Word m k → Word m n

infixr 5 _++_
_++_ : Word k n → Word m k → Word m n
ε       ++ Δ = Δ
(s ∷ Γ) ++ Δ = s ∷ (Γ ++ Δ)

++-identityʳ : (Γ : Word m n) → Γ ++ ε ≡ Γ
++-identityʳ ε       = refl
++-identityʳ (s ∷ Γ) = cong (s ∷_) (++-identityʳ Γ)

++-assoc : (Γ₁ : Word k n) (Γ₂ : Word j k) (Γ₃ : Word m j)
  → (Γ₁ ++ Γ₂) ++ Γ₃ ≡ Γ₁ ++ (Γ₂ ++ Γ₃)
++-assoc ε        Γ₂ Γ₃ = refl
++-assoc (s ∷ Γ₁) Γ₂ Γ₃ = cong (s ∷_) (++-assoc Γ₁ Γ₂ Γ₃)

-- singleton words
⟦_⟧ : Step m n → Word m n
⟦ s ⟧ = s ∷ ε

-- the paper's {n₁ ⊣ g ⊢ n₂} with arities on the nose
sub! : ∀ n₁ n₂ {m} → Op m → Step (n₁ + (m + n₂)) (n₁ + suc n₂)
sub! n₁ n₂ g = ins n₁ n₂ refl refl g

------------------------------------------------------------------------
-- Definition 3.15: pre-substitution application
------------------------------------------------------------------------

infixl 7 _⋆₁_ _⋆_
_⋆₁_ : Op n → Step m n → Op m
f ⋆₁ ins n₁ n₂ p q g = subst Op (sym p) ((subst Op q f) ⟨ n₁ ⊣ g ⊢ n₂ ⟩)
f ⋆₁ rn r           = f [ r ]

_⋆_ : Op n → Word m n → Op m
f ⋆ ε       = f
f ⋆ (s ∷ Γ) = (f ⋆₁ s) ⋆ Γ

⋆-++ : (f : Op n) (Γ₁ : Word k n) (Γ₂ : Word m k) → f ⋆ (Γ₁ ++ Γ₂) ≡ (f ⋆ Γ₁) ⋆ Γ₂
⋆-++ f ε        Γ₂ = refl
⋆-++ f (s ∷ Γ₁) Γ₂ = ⋆-++ (f ⋆₁ s) Γ₁ Γ₂

⋆₁-cong : {f g : Op n} → f ≈ g → (s : Step m n) → f ⋆₁ s ≈ g ⋆₁ s
⋆₁-cong e (ins n₁ n₂ p q g) = subst-cong (sym p) (sub-cong (subst-cong q e) ≈.refl)
⋆₁-cong e (rn r)           = ren-cong e (λ _ → refl)

⋆-cong : {f g : Op n} → f ≈ g → (Γ : Word m n) → f ⋆ Γ ≈ g ⋆ Γ
⋆-cong e ε       = e
⋆-cong e (s ∷ Γ) = ⋆-cong (⋆₁-cong e s) Γ

------------------------------------------------------------------------
-- Whiskering of steps and words (used in Prop. 3.14)
------------------------------------------------------------------------

infixr 6 _⊣ₛ_ _⊣ʷ_
infixl 6 _⊢ₛ_ _⊢ʷ_

-- the arity equations of a shifted step
Lp : ∀ k n₁ {x y} → x ≡ n₁ + y → k + x ≡ (k + n₁) + y
Lp k n₁ {y = y} p = trans (cong (k +_) p) (sym (+-assoc k n₁ y))

Rp : ∀ n₁ m n₂ k {x} → x ≡ n₁ + (m + n₂) → x + k ≡ n₁ + (m + (n₂ + k))
Rp n₁ m n₂ k p = trans (cong (_+ k) p) (trans (+-assoc n₁ (m + n₂) k) (cong (n₁ +_) (+-assoc m n₂ k)))

Rq : ∀ n₁ n₂ k {x} → x ≡ n₁ + suc n₂ → x + k ≡ n₁ + suc (n₂ + k)
Rq n₁ n₂ k q = trans (cong (_+ k) q) (+-assoc n₁ (suc n₂) k)

_⊣ₛ_ : ∀ k → Step m n → Step (k + m) (k + n)
k ⊣ₛ ins n₁ n₂ {m} p q g = ins (k + n₁) n₂ (Lp k n₁ p) (Lp k n₁ q) g
k ⊣ₛ rn r = rn (idʳ {k} +ʳ r)

_⊢ₛ_ : Step m n → ∀ k → Step (m + k) (n + k)
ins n₁ n₂ {m} p q g ⊢ₛ k = ins n₁ (n₂ + k) (Rp n₁ m n₂ k p) (Rq n₁ n₂ k q) g
rn r ⊢ₛ k = rn (r +ʳ idʳ {k})

_⊣ʷ_ : ∀ k → Word m n → Word (k + m) (k + n)
k ⊣ʷ ε       = ε
k ⊣ʷ (s ∷ Γ) = (k ⊣ₛ s) ∷ (k ⊣ʷ Γ)

_⊢ʷ_ : Word m n → ∀ k → Word (m + k) (n + k)
ε       ⊢ʷ k = ε
(s ∷ Γ) ⊢ʷ k = (s ⊢ₛ k) ∷ (Γ ⊢ʷ k)

⊣ʷ-++ : ∀ k (Γ₁ : Word j n) (Γ₂ : Word m j) → k ⊣ʷ (Γ₁ ++ Γ₂) ≡ (k ⊣ʷ Γ₁) ++ (k ⊣ʷ Γ₂)
⊣ʷ-++ k ε        Γ₂ = refl
⊣ʷ-++ k (s ∷ Γ₁) Γ₂ = cong ((k ⊣ₛ s) ∷_) (⊣ʷ-++ k Γ₁ Γ₂)

⊢ʷ-++ : (Γ₁ : Word j n) (Γ₂ : Word m j) (l : ℕ) → (Γ₁ ++ Γ₂) ⊢ʷ l ≡ (Γ₁ ⊢ʷ l) ++ (Γ₂ ⊢ʷ l)
⊢ʷ-++ ε        Γ₂ l = refl
⊢ʷ-++ (s ∷ Γ₁) Γ₂ l = cong ((s ⊢ₛ l) ∷_) (⊢ʷ-++ Γ₁ Γ₂ l)

------------------------------------------------------------------------
-- Figure 3: the congruence on pre-substitutions.
--
-- `Cart` is a predicate on operations: the "additional cartesian rules"
-- (CEN), (D), (C) apply to substitution steps whose operation satisfies
-- it ((CEN) when either of the two operations does, which covers the
-- paper's (CEN₁) and (CEN₂)).  Instantiating Cart := const ⊤ gives the cartesian congruence
-- Sub×_𝕍; Cart := const ⊥ the purely symmetric one; and for a Freyd
-- operad, Cart g := "g is a J-image" gives the congruence for Sub_ℂ.
--
-- NOTE (paper issue): with Sub_ℂ defined by the symmetric rules only
-- (Def. 3.12), J^Sub of Def. 3.13 does *not* respect the congruence:
-- e.g. (CEN) in Sub×_𝕍 would have to map to a commutation of two
-- substitution steps {Jv₁},{Jv₂} in Sub_ℂ, which no symmetric rule
-- provides.  Sub_ℂ must be quotiented by the cartesian rules for
-- J-image steps as well; this is the Cart := J-image instance.
--
-- Three administrative generators are added to the paper's list:
--   (I) a substitution step is extensional in its operation (modulo ≈);
--   (E) a renaming step is extensional in the renaming;
--   (S) a step with arity proofs is the same as the on-the-nose step
--       conjugated by the corresponding cast renamings.
-- All are sound for ⋆ (Thm. 3.16) and are validated by any model.
--
-- NOTE (paper issue): the side conditions of Fig. 3 write Ren(a,b) for
-- what must be Renᵒᵖ(a ⇒ b) = Ren(b ⇒ a) (Def. 2.1 only defines
-- Ren(m ⇒ n)).  The orientations below are the ones for which the
-- rules type-check.
------------------------------------------------------------------------

data Cong (Cart : ∀ {n} → Op n → Set) : Word m n → Word m n → Set where
  ≅-refl  : {Γ : Word m n} → Cong Cart Γ Γ
  ≅-sym   : {Γ Δ : Word m n} → Cong Cart Γ Δ → Cong Cart Δ Γ
  ≅-trans : {Γ Δ Θ : Word m n} → Cong Cart Γ Δ → Cong Cart Δ Θ → Cong Cart Γ Θ
  ≅-cong  : {Γ₁ Γ₁' : Word k n} {Γ₂ Γ₂' : Word m k}
          → Cong Cart Γ₁ Γ₁' → Cong Cart Γ₂ Γ₂' → Cong Cart (Γ₁ ++ Γ₂) (Γ₁' ++ Γ₂')
  -- administrative
  I∙ : ∀ n₁ n₂ {m k k'} (p : k ≡ n₁ + (m + n₂)) (q : k' ≡ n₁ + suc n₂) {g g' : Op m}
     → g ≈ g' → Cong Cart ⟦ ins n₁ n₂ p q g ⟧ ⟦ ins n₁ n₂ p q g' ⟧
  E∙ : {r s : Ren n m} → r ≗ s → Cong Cart ⟦ rn r ⟧ ⟦ rn s ⟧
  S∙ : ∀ n₁ n₂ {m k k'} (p : k ≡ n₁ + (m + n₂)) (q : k' ≡ n₁ + suc n₂) (g : Op m)
     → Cong Cart ⟦ ins n₁ n₂ p q g ⟧ (rn (castʳ q) ∷ sub! n₁ n₂ g ∷ ⟦ rn (castʳ (sym p)) ⟧)
  -- symmetric rules
  U₁∙ : ∀ n₁ n₂ {k} (p : k ≡ n₁ + suc n₂) → Cong Cart ⟦ ins n₁ n₂ p p idₒ ⟧ ε
  U₂∙ : Cong Cart ⟦ rn (idʳ {n}) ⟧ ε
  A∙ : ∀ m₁ m₂ n₁ n₂ {n k k₁ k'} (g : Op (n₁ + suc n₂)) (h : Op n)
       (p₁ : k₁ ≡ m₁ + ((n₁ + suc n₂) + m₂)) (q₁ : k' ≡ m₁ + suc m₂)
       (p₂ : k ≡ (m₁ + n₁) + (n + (n₂ + m₂))) (q₂ : k₁ ≡ (m₁ + n₁) + suc (n₂ + m₂))
       (p₃ : k ≡ m₁ + ((n₁ + (n + n₂)) + m₂))
     → Cong Cart (ins m₁ m₂ p₁ q₁ g ∷ ⟦ ins (m₁ + n₁) (n₂ + m₂) p₂ q₂ h ⟧)
                 ⟦ ins m₁ m₂ p₃ q₁ (g ⟨ n₁ ⊣ h ⊢ n₂ ⟩) ⟧
  R∙ : (r₁ : Ren n k) (r₂ : Ren k m) → Cong Cart (rn r₁ ∷ ⟦ rn r₂ ⟧) ⟦ rn (r₂ ∘ʳ r₁) ⟧
  N∙ : ∀ {n₁ n₂ m₁ m₂ m'} {m} (v : Op m) (r₁ : Ren n₁ m₁) (s : Ren m m') (r₂ : Ren n₂ m₂)
     → Cong Cart (sub! n₁ n₂ v ∷ ⟦ rn (r₁ +ʳ s +ʳ r₂) ⟧)
                 (rn (r₁ +ʳ idʳ {1} +ʳ r₂) ∷ ⟦ sub! m₁ m₂ (v [ s ]) ⟧)
  Sℓ∙ : ∀ m₁ m₂ {n} (g : Op n)
       (p : m₁ + ((1 + n) + m₂) ≡ (m₁ + 1) + (n + m₂)) (q : m₁ + suc (suc m₂) ≡ (m₁ + 1) + suc m₂)
       (q' : m₁ + ((n + 1) + m₂) ≡ m₁ + (n + suc m₂))
     → Cong Cart (rn (idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∷ ⟦ sub! m₁ (suc m₂) g ⟧)
                 (ins (m₁ + 1) m₂ p q g ∷ ⟦ rn (castʳ q' ∘ʳ (idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂})) ⟧)
  Sr∙ : ∀ m₁ m₂ {n} (g : Op n)
       (p : (m₁ + 1) + (n + m₂) ≡ (m₁ + 1) + (n + m₂)) (q : m₁ + suc (suc m₂) ≡ (m₁ + 1) + suc m₂)
       (q' : m₁ + ((1 + n) + m₂) ≡ (m₁ + 1) + (n + m₂)) (q'' : m₁ + (n + suc m₂) ≡ m₁ + ((n + 1) + m₂))
     → Cong Cart (rn (idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∷ ⟦ ins (m₁ + 1) m₂ p q g ⟧)
                 (sub! m₁ (suc m₂) g ∷ ⟦ rn (castʳ q' ∘ʳ (idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}) ∘ʳ castʳ q'') ⟧)
  -- additional cartesian rules
  CEN∙ : ∀ m₁ m m₂ {n₁ n₂ k} (g₁ : Op n₁) (g₂ : Op n₂) → Cart g₁ ⊎ Cart g₂ →
       (p   : m₁ + (n₁ + (m + suc m₂)) ≡ (m₁ + (n₁ + m)) + suc m₂)
       (q   : k ≡ (m₁ + (n₁ + m)) + (n₂ + m₂))
       (p'  : m₁ + suc (m + suc m₂) ≡ (m₁ + suc m) + suc m₂)
       (p'' : (m₁ + suc m) + (n₂ + m₂) ≡ m₁ + suc (m + (n₂ + m₂)))
       (q'  : k ≡ m₁ + (n₁ + (m + (n₂ + m₂))))
     → Cong Cart (sub! m₁ (m + suc m₂) g₁ ∷ ⟦ ins (m₁ + (n₁ + m)) m₂ q p g₂ ⟧)
                 (ins (m₁ + suc m) m₂ (sym p'') p' g₂ ∷ ⟦ ins m₁ (m + (n₂ + m₂)) q' refl g₁ ⟧)
  D∙ : ∀ m₁ m₂ {n} (g : Op n) → Cart g
     → Cong Cart (rn (idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂}) ∷ ⟦ sub! m₁ m₂ g ⟧) ⟦ rn (idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂}) ⟧
  C∙ : ∀ m₁ m₂ {n} (g : Op n) → Cart g →
       (p : m₁ + (n + suc m₂) ≡ (m₁ + n) + suc m₂) (q : m₁ + ((n + n) + m₂) ≡ (m₁ + n) + (n + m₂))
     → Cong Cart (rn (idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂}) ∷ ⟦ sub! m₁ m₂ g ⟧)
                 (sub! m₁ (suc m₂) g ∷ ins (m₁ + n) m₂ q p g ∷ ⟦ rn (idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}) ⟧)

-- the purely symmetric congruence and the cartesian one (Sub×, Def. 3.12)
infix 4 _≅ˢ_ _≅ˣ_
_≅ˢ_ : Word m n → Word m n → Set
_≅ˢ_ = Cong (λ _ → ⊥)

_≅ˣ_ : Word m n → Word m n → Set
_≅ˣ_ = Cong (λ _ → ⊤)

module _ {Cart : ∀ {n} → Op n → Set} where
  ≅-equiv : IsEquivalence (Cong Cart {m} {n})
  ≅-equiv = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }

  ≅-∷ : {s : Step k n} {Γ Δ : Word m k} → Cong Cart Γ Δ → Cong Cart (s ∷ Γ) (s ∷ Δ)
  ≅-∷ {s = s} e = ≅-cong {Γ₁ = ⟦ s ⟧} ≅-refl e

  ≅-∷ˡ : {s t : Step k n} {Γ : Word m k} → Cong Cart ⟦ s ⟧ ⟦ t ⟧ → Cong Cart (s ∷ Γ) (t ∷ Γ)
  ≅-∷ˡ e = ≅-cong e ≅-refl

  ≅-≡ : {Γ Δ : Word m n} → Γ ≡ Δ → Cong Cart Γ Δ
  ≅-≡ refl = ≅-refl
