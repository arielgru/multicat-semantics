------------------------------------------------------------------------
-- MFPS 2026, "Multicategorical Semantics for Untyped Effects"
-- (Cohen, Grunfeld).  Agda formalisation.
--
-- Prelude: re-exports, arity arithmetic, casts along arity equations,
-- and the category Ren of renamings (Section 2.1).
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
module MFPS.Prelude where

open import Level using (Level; 0ℓ) public
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_) public
open import Data.Nat.Properties
  using (+-assoc; +-identityʳ; +-suc; +-comm; ≡-irrelevant) public
open import Data.Fin.Base
  using (Fin; zero; suc; splitAt; join; _↑ˡ_; _↑ʳ_; toℕ) public
open import Data.Fin.Properties
  using (splitAt-join; join-splitAt; splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ;
         toℕ-injective; toℕ-↑ˡ; toℕ-↑ʳ) public
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′; swap) renaming (map to map⊎) public
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax) public
open import Data.Unit.Base using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Function.Base using (id; _∘_; _∘′_; const; flip; _$_) public
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; _≗_; module ≡-Reasoning) public
open import Relation.Binary using (Rel; IsEquivalence; Setoid) public
open import Relation.Binary.Structures using () public

private
  variable
    k m n : ℕ
    ℓ : Level

------------------------------------------------------------------------
-- Casts along arity equations.
--
-- All structures in the paper are "strict" and ℕ-indexed, so laws such
-- as associativity of substitution relate operations whose arities are
-- only *propositionally* equal (e.g. (m₁+n₁)+(n+(n₂+m₂)) versus
-- m₁+((n₁+(n+n₂))+m₂)).  We transport along such equations with
-- `subst`; since ℕ has decidable equality these transports are
-- coherent (`≡-irrelevant`), which is what `subst-irr` records.
------------------------------------------------------------------------

subst-irr : (P : ℕ → Set ℓ) (p : n ≡ n) (x : P n) → subst P p x ≡ x
subst-irr P p x rewrite ≡-irrelevant p refl = refl

subst-trans : (P : ℕ → Set ℓ) (p : k ≡ m) (q : m ≡ n) (x : P k)
  → subst P q (subst P p x) ≡ subst P (trans p q) x
subst-trans P refl refl x = refl

subst-sym-cancel : (P : ℕ → Set ℓ) (p : m ≡ n) (x : P n)
  → subst P p (subst P (sym p) x) ≡ x
subst-sym-cancel P refl x = refl

subst-cancel-sym : (P : ℕ → Set ℓ) (p : m ≡ n) (x : P m)
  → subst P (sym p) (subst P p x) ≡ x
subst-cancel-sym P refl x = refl

------------------------------------------------------------------------
-- Section 2.1: renamings.
--
-- A renaming r : m → n is a function [m] → [n]; we take [n] := Fin n.
-- Ren (m ⇒ n) of the paper is `Ren m n`.  The tensor is the block sum,
-- σ is swap, ! is discard and Δ is copy, exactly as in Def. 2.1.
------------------------------------------------------------------------

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

idʳ : Ren n n
idʳ = id

infixr 9 _∘ʳ_
_∘ʳ_ : Ren n k → Ren m n → Ren m k
s ∘ʳ r = s ∘ r

infixr 6 _+ʳ_
-- block sum  r + r' : Ren (m₁ + m₂) (n₁ + n₂)
_+ʳ_ : ∀ {m₁ n₁ m₂ n₂} → Ren m₁ n₁ → Ren m₂ n₂ → Ren (m₁ + m₂) (n₁ + n₂)
_+ʳ_ {m₁} {n₁} {m₂} {n₂} r s i = join n₁ n₂ (map⊎ r s (splitAt m₁ i))

-- concatenation [r , r'] : Ren (m + k) n
[_,_]ʳ : Ren m n → Ren k n → Ren (m + k) n
[_,_]ʳ {m} r s i = [ r , s ]′ (splitAt m i)

-- swap σ_{m,n} : Ren (m + n) (n + m)
σʳ : ∀ m n → Ren (m + n) (n + m)
σʳ m n i = join n m (swap (splitAt m i))

-- discard !_n : Ren 0 n
!ʳ : ∀ n → Ren 0 n
!ʳ n ()

-- copy Δ_n : Ren (n + n) n
Δʳ : ∀ n → Ren (n + n) n
Δʳ n = [ idʳ , idʳ ]ʳ

-- k-fold contraction Δᵏ : Ren (k·n) n (used to interpret k-ary term formers)
Δᵏ : ∀ k n → Ren (k * n) n
Δᵏ zero    n ()
Δᵏ (suc k) n = [ idʳ , Δᵏ k n ]ʳ

-- casts along arity equations are themselves renamings.  (Defined by
-- matching on the equation, so that the equation is a *relevant*
-- argument and can be inferred by unification; Data.Fin.cast takes it
-- irrelevantly.)
castʳ : m ≡ n → Ren m n
castʳ refl i = i

-- the point i : Ren 1 n
ptʳ : Fin n → Ren 1 n
ptʳ i _ = i

------------------------------------------------------------------------
-- Basic facts about renamings (Lemma 2.3 in unbundled form).
------------------------------------------------------------------------

private
  map⊎-id : ∀ {A B : Set} (x : A ⊎ B) → map⊎ id id x ≡ x
  map⊎-id (inj₁ _) = refl
  map⊎-id (inj₂ _) = refl

+ʳ-id : ∀ m n → (idʳ {m} +ʳ idʳ {n}) ≗ idʳ
+ʳ-id m n i rewrite map⊎-id (splitAt m i) = join-splitAt m n i

+ʳ-∘ : ∀ {m₁ n₁ k₁ m₂ n₂ k₂}
  (s₁ : Ren n₁ k₁) (r₁ : Ren m₁ n₁) (s₂ : Ren n₂ k₂) (r₂ : Ren m₂ n₂)
  → ((s₁ ∘ʳ r₁) +ʳ (s₂ ∘ʳ r₂)) ≗ ((s₁ +ʳ s₂) ∘ʳ (r₁ +ʳ r₂))
+ʳ-∘ {m₁} {n₁} {k₁} {m₂} {n₂} {k₂} s₁ r₁ s₂ r₂ i with splitAt m₁ i
... | inj₁ j rewrite splitAt-↑ˡ n₁ (r₁ j) n₂ = refl
... | inj₂ j rewrite splitAt-↑ʳ n₁ n₂ (r₂ j) = refl

+ʳ-cong : ∀ {m₁ n₁ m₂ n₂} {r r' : Ren m₁ n₁} {s s' : Ren m₂ n₂}
  → r ≗ r' → s ≗ s' → (r +ʳ s) ≗ (r' +ʳ s')
+ʳ-cong {m₁} p q i with splitAt m₁ i
... | inj₁ j = cong (join _ _) (cong inj₁ (p j))
... | inj₂ j = cong (join _ _) (cong inj₂ (q j))

+ʳ-inj₁ : ∀ {m₁ n₁ m₂ n₂} (r : Ren m₁ n₁) (s : Ren m₂ n₂) (i : Fin m₁)
  → (r +ʳ s) (i ↑ˡ m₂) ≡ r i ↑ˡ n₂
+ʳ-inj₁ {m₁} {n₁} {m₂} r s i rewrite splitAt-↑ˡ m₁ i m₂ = refl

+ʳ-inj₂ : ∀ {m₁ n₁ m₂ n₂} (r : Ren m₁ n₁) (s : Ren m₂ n₂) (i : Fin m₂)
  → (r +ʳ s) (m₁ ↑ʳ i) ≡ n₁ ↑ʳ s i
+ʳ-inj₂ {m₁} {n₁} {m₂} r s i rewrite splitAt-↑ʳ m₁ m₂ i = refl

σʳ-σʳ : ∀ m n → (σʳ n m ∘ʳ σʳ m n) ≗ idʳ
σʳ-σʳ m n i with splitAt m i in eq
... | inj₁ j rewrite splitAt-↑ʳ n m j = trans (cong (join m n) (sym eq)) (join-splitAt m n i)
... | inj₂ j rewrite splitAt-↑ˡ n j m = trans (cong (join m n) (sym eq)) (join-splitAt m n i)

castʳ-refl : (p : n ≡ n) → castʳ p ≗ idʳ
castʳ-refl p i rewrite ≡-irrelevant p refl = refl

castʳ-∘ : (p : k ≡ m) (q : m ≡ n) → (castʳ q ∘ʳ castʳ p) ≗ castʳ (trans p q)
castʳ-∘ refl refl i = refl

toℕ-castʳ : (p : m ≡ n) (i : Fin m) → toℕ (castʳ p i) ≡ toℕ i
toℕ-castʳ refl i = refl

-- A `subst` along an arity equation on Fin is a cast.
subst-Fin : (p : m ≡ n) (i : Fin m) → subst Fin p i ≡ castʳ p i
subst-Fin refl i = refl

-- Block sums with empty outer blocks are casts:  id₀ + r + id₀ = r up to cast.
+ʳ-zero : ∀ {n m} (r : Ren n m) (p : n + 0 ≡ n) (q : m + 0 ≡ m)
  → (castʳ q ∘ʳ (idʳ {0} +ʳ r +ʳ idʳ {0})) ≗ (r ∘ʳ castʳ p)
+ʳ-zero {n} {m} r p q i with splitAt n i in eq
... | inj₁ j = toℕ-injective (begin
      toℕ (castʳ q (r j ↑ˡ 0))  ≡⟨ toℕ-castʳ q (r j ↑ˡ 0) ⟩
      toℕ (r j ↑ˡ 0)           ≡⟨ toℕ-↑ˡ (r j) 0 ⟩
      toℕ (r j)                ≡⟨ cong (toℕ ∘ r) (toℕ-injective (begin
                                    toℕ j            ≡⟨ sym (toℕ-↑ˡ j 0) ⟩
                                    toℕ (j ↑ˡ 0)     ≡⟨ cong toℕ (splitAt⁻¹-↑ˡ eq) ⟩
                                    toℕ i            ≡⟨ sym (toℕ-castʳ p i) ⟩
                                    toℕ (castʳ p i)   ∎)) ⟩
      toℕ (r (castʳ p i))       ∎)
  where open ≡-Reasoning

-- Functions out of Fin (m + n) are determined by their values on the two blocks.
Fin+-ext : ∀ {ℓ} {A : Set ℓ} {m n} {f g : Fin (m + n) → A}
  → (∀ j → f (j ↑ˡ n) ≡ g (j ↑ˡ n)) → (∀ j → f (m ↑ʳ j) ≡ g (m ↑ʳ j)) → f ≗ g
Fin+-ext {m = m} {n} {f} {g} h₁ h₂ i with splitAt m i in eq
... | inj₁ j = subst (λ i → f i ≡ g i) (splitAt⁻¹-↑ˡ eq) (h₁ j)
... | inj₂ j = subst (λ i → f i ≡ g i) (splitAt⁻¹-↑ʳ eq) (h₂ j)

Fin+1-ext : ∀ {ℓ} {A : Set ℓ} {m} {f g : Fin (m + 1) → A}
  → (∀ j → f (j ↑ˡ 1) ≡ g (j ↑ˡ 1)) → f (m ↑ʳ zero) ≡ g (m ↑ʳ zero) → f ≗ g
Fin+1-ext h₁ h₂ = Fin+-ext h₁ (λ { zero → h₂ })

-- computation rules for [_,_]ʳ
[,]ʳ-inl : ∀ {m n k} (r : Ren m n) (s : Ren k n) (j : Fin m) → [ r , s ]ʳ (j ↑ˡ k) ≡ r j
[,]ʳ-inl {m} {n} {k} r s j = cong [ r , s ]′ (splitAt-↑ˡ m j k)

[,]ʳ-inr : ∀ {m n k} (r : Ren m n) (s : Ren k n) (j : Fin k) → [ r , s ]ʳ (m ↑ʳ j) ≡ s j
[,]ʳ-inr {m} {n} {k} r s j = cong [ r , s ]′ (splitAt-↑ʳ m k j)

-- computation rules for σʳ
σʳ-inl : ∀ m n (j : Fin m) → σʳ m n (j ↑ˡ n) ≡ n ↑ʳ j
σʳ-inl m n j = cong (join n m ∘ swap) (splitAt-↑ˡ m j n)

σʳ-inr : ∀ m n (j : Fin n) → σʳ m n (m ↑ʳ j) ≡ j ↑ˡ m
σʳ-inr m n j = cong (join n m ∘ swap) (splitAt-↑ʳ m n j)

------------------------------------------------------------------------
-- Cast-like renamings.
--
-- Whiskering and the strict identifications of arities produce
-- renamings such as  idₖ + cast p  or  cast q ∘ (id + (r + s)) ∘ cast p.
-- All the bookkeeping is handled uniformly by observing that such
-- renamings preserve the numeric value of positions, and that any two
-- value-preserving renamings between the same arities are equal.
------------------------------------------------------------------------

IsCast : Ren m n → Set
IsCast r = ∀ i → toℕ (r i) ≡ toℕ i

castʳ-isCast : (p : m ≡ n) → IsCast (castʳ p)
castʳ-isCast p i = toℕ-castʳ p i

idʳ-isCast : IsCast (idʳ {n})
idʳ-isCast i = refl

∘ʳ-isCast : {r : Ren m n} {s : Ren n k} → IsCast s → IsCast r → IsCast (s ∘ʳ r)
∘ʳ-isCast hs hr i = trans (hs _) (hr i)

-- explicit-argument variants (for use where the composite cannot be inferred)
∘ʳ-isCast' : (s : Ren n k) (r : Ren m n) → IsCast s → IsCast r → IsCast (s ∘ʳ r)
∘ʳ-isCast' s r hs hr = ∘ʳ-isCast {r = r} {s = s} hs hr

-- two cast-like renamings between the same arities coincide
isCast-unique : {r s : Ren m n} → IsCast r → IsCast s → r ≗ s
isCast-unique hr hs i = toℕ-injective (trans (hr i) (sym (hs i)))

-- a cast-like endo-renaming is the identity
isCast-id : {r : Ren n n} → IsCast r → r ≗ idʳ
isCast-id hr = isCast-unique hr idʳ-isCast

-- numeric value of a block sum
toℕ-+ʳ-inl : ∀ {m₁ n₁ m₂ n₂} (r : Ren m₁ n₁) (s : Ren m₂ n₂) (j : Fin m₁)
  → toℕ ((r +ʳ s) (j ↑ˡ m₂)) ≡ toℕ (r j)
toℕ-+ʳ-inl {n₂ = n₂} r s j = trans (cong toℕ (+ʳ-inj₁ r s j)) (toℕ-↑ˡ (r j) n₂)

toℕ-+ʳ-inr : ∀ {m₁ n₁ m₂ n₂} (r : Ren m₁ n₁) (s : Ren m₂ n₂) (j : Fin m₂)
  → toℕ ((r +ʳ s) (m₁ ↑ʳ j)) ≡ n₁ + toℕ (s j)
toℕ-+ʳ-inr {n₁ = n₁} r s j = trans (cong toℕ (+ʳ-inj₂ r s j)) (toℕ-↑ʳ n₁ (s j))

-- block sums of cast-like renamings are cast-like (when the left arities agree)
+ʳ-isCast : ∀ {m₁ n₁ m₂ n₂} {r : Ren m₁ n₁} {s : Ren m₂ n₂}
  → m₁ ≡ n₁ → IsCast r → IsCast s → IsCast (r +ʳ s)
+ʳ-isCast {m₁} {n₁} {m₂} {n₂} {r} {s} e hr hs = Fin+-ext
  (λ j → trans (toℕ-+ʳ-inl r s j) (trans (hr j) (sym (toℕ-↑ˡ j m₂))))
  (λ j → trans (toℕ-+ʳ-inr r s j) (trans (cong₂ _+_ (sym e) (hs j)) (sym (toℕ-↑ʳ m₁ j))))

-- block sums with an identity on one side (explicit arity, for inference)
id+ʳ-isCast : ∀ k {m n} {s : Ren m n} → m ≡ n → IsCast s → IsCast (idʳ {k} +ʳ s)
id+ʳ-isCast k {s = s} e hs = +ʳ-isCast {r = idʳ {k}} {s = s} refl idʳ-isCast hs

+ʳid-isCast : ∀ k {m n} (r : Ren m n) → m ≡ n → IsCast r → IsCast (r +ʳ idʳ {k})
+ʳid-isCast k r e hr = +ʳ-isCast {r = r} {s = idʳ {k}} e hr idʳ-isCast

-- block sum is associative up to casts
+ʳ-assoc : ∀ {m₁ n₁ m₂ n₂ m₃ n₃} (r : Ren m₁ n₁) (s : Ren m₂ n₂) (t : Ren m₃ n₃)
  (p : (m₁ + m₂) + m₃ ≡ m₁ + (m₂ + m₃)) (q : n₁ + (n₂ + n₃) ≡ (n₁ + n₂) + n₃)
  → (castʳ q ∘ʳ (r +ʳ (s +ʳ t)) ∘ʳ castʳ p) ≗ ((r +ʳ s) +ʳ t)
+ʳ-assoc {m₁} {n₁} {m₂} {n₂} {m₃} {n₃} r s t p q = Fin+-ext
  (Fin+-ext
    (λ j → toℕ-injective (begin
      toℕ (castʳ q ((r +ʳ (s +ʳ t)) (castʳ p ((j ↑ˡ m₂) ↑ˡ m₃))))
        ≡⟨ toℕ-castʳ q _ ⟩
      toℕ ((r +ʳ (s +ʳ t)) (castʳ p ((j ↑ˡ m₂) ↑ˡ m₃)))
        ≡⟨ cong (toℕ ∘ (r +ʳ (s +ʳ t))) (toℕ-injective (trans (toℕ-castʳ p _) (trans (toℕ-↑ˡ (j ↑ˡ m₂) m₃) (trans (toℕ-↑ˡ j m₂) (sym (toℕ-↑ˡ j (m₂ + m₃))))))) ⟩
      toℕ ((r +ʳ (s +ʳ t)) (j ↑ˡ (m₂ + m₃)))
        ≡⟨ toℕ-+ʳ-inl r (s +ʳ t) j ⟩
      toℕ (r j)
        ≡⟨ sym (toℕ-+ʳ-inl r s j) ⟩
      toℕ ((r +ʳ s) (j ↑ˡ m₂))
        ≡⟨ sym (toℕ-+ʳ-inl (r +ʳ s) t (j ↑ˡ m₂)) ⟩
      toℕ (((r +ʳ s) +ʳ t) ((j ↑ˡ m₂) ↑ˡ m₃)) ∎))
    (λ j → toℕ-injective (begin
      toℕ (castʳ q ((r +ʳ (s +ʳ t)) (castʳ p ((m₁ ↑ʳ j) ↑ˡ m₃))))
        ≡⟨ toℕ-castʳ q _ ⟩
      toℕ ((r +ʳ (s +ʳ t)) (castʳ p ((m₁ ↑ʳ j) ↑ˡ m₃)))
        ≡⟨ cong (toℕ ∘ (r +ʳ (s +ʳ t))) (toℕ-injective (trans (toℕ-castʳ p _) (trans (toℕ-↑ˡ (m₁ ↑ʳ j) m₃) (trans (toℕ-↑ʳ m₁ j) (trans (cong (m₁ +_) (sym (toℕ-↑ˡ j m₃))) (sym (toℕ-↑ʳ m₁ (j ↑ˡ m₃)))))))) ⟩
      toℕ ((r +ʳ (s +ʳ t)) (m₁ ↑ʳ (j ↑ˡ m₃)))
        ≡⟨ toℕ-+ʳ-inr r (s +ʳ t) (j ↑ˡ m₃) ⟩
      n₁ + toℕ ((s +ʳ t) (j ↑ˡ m₃))
        ≡⟨ cong (n₁ +_) (toℕ-+ʳ-inl s t j) ⟩
      n₁ + toℕ (s j)
        ≡⟨ sym (toℕ-+ʳ-inr r s j) ⟩
      toℕ ((r +ʳ s) (m₁ ↑ʳ j))
        ≡⟨ sym (toℕ-+ʳ-inl (r +ʳ s) t (m₁ ↑ʳ j)) ⟩
      toℕ (((r +ʳ s) +ʳ t) ((m₁ ↑ʳ j) ↑ˡ m₃)) ∎)))
  (λ j → toℕ-injective (begin
      toℕ (castʳ q ((r +ʳ (s +ʳ t)) (castʳ p ((m₁ + m₂) ↑ʳ j))))
        ≡⟨ toℕ-castʳ q _ ⟩
      toℕ ((r +ʳ (s +ʳ t)) (castʳ p ((m₁ + m₂) ↑ʳ j)))
        ≡⟨ cong (toℕ ∘ (r +ʳ (s +ʳ t))) (toℕ-injective (trans (toℕ-castʳ p _) (trans (toℕ-↑ʳ (m₁ + m₂) j) (trans (+-assoc m₁ m₂ (toℕ j)) (trans (cong (m₁ +_) (sym (toℕ-↑ʳ m₂ j))) (sym (toℕ-↑ʳ m₁ (m₂ ↑ʳ j)))))))) ⟩
      toℕ ((r +ʳ (s +ʳ t)) (m₁ ↑ʳ (m₂ ↑ʳ j)))
        ≡⟨ toℕ-+ʳ-inr r (s +ʳ t) (m₂ ↑ʳ j) ⟩
      n₁ + toℕ ((s +ʳ t) (m₂ ↑ʳ j))
        ≡⟨ cong (n₁ +_) (toℕ-+ʳ-inr s t j) ⟩
      n₁ + (n₂ + toℕ (t j))
        ≡⟨ sym (+-assoc n₁ n₂ (toℕ (t j))) ⟩
      (n₁ + n₂) + toℕ (t j)
        ≡⟨ sym (toℕ-+ʳ-inr (r +ʳ s) t j) ⟩
      toℕ (((r +ʳ s) +ʳ t) ((m₁ + m₂) ↑ʳ j)) ∎))
  where open ≡-Reasoning

-- value of the identity-with-empty-block renamings
!ʳ+ʳ-inr : ∀ {m n} (r : Ren m n) (j : Fin m) → (!ʳ k +ʳ r) j ≡ k ↑ʳ r j
!ʳ+ʳ-inr {k} r j = refl

------------------------------------------------------------------------
-- Further renaming identities (values under toℕ)
------------------------------------------------------------------------

toℕ-σʳ-inl : ∀ m n (j : Fin m) → toℕ (σʳ m n (j ↑ˡ n)) ≡ n + toℕ j
toℕ-σʳ-inl m n j = trans (cong toℕ (σʳ-inl m n j)) (toℕ-↑ʳ n j)

toℕ-σʳ-inr : ∀ m n (j : Fin n) → toℕ (σʳ m n (m ↑ʳ j)) ≡ toℕ j
toℕ-σʳ-inr m n j = trans (cong toℕ (σʳ-inr m n j)) (toℕ-↑ˡ j m)

-- a block sum with an empty right block is a cast
+ʳ-zeroʳ : ∀ {n m} (r : Ren n m) (p : n + 0 ≡ n) (q : m + 0 ≡ m)
  → (castʳ q ∘ʳ (r +ʳ idʳ {0}) ∘ʳ castʳ (sym p)) ≗ r
+ʳ-zeroʳ {n} {m} r p q i = toℕ-injective (begin
  toℕ (castʳ q ((r +ʳ idʳ {0}) (castʳ (sym p) i)))
    ≡⟨ toℕ-castʳ q _ ⟩
  toℕ ((r +ʳ idʳ {0}) (castʳ (sym p) i))
    ≡⟨ cong (toℕ ∘ (r +ʳ idʳ {0})) (toℕ-injective (trans (toℕ-castʳ (sym p) i) (sym (toℕ-↑ˡ i 0)))) ⟩
  toℕ ((r +ʳ idʳ {0}) (i ↑ˡ 0))
    ≡⟨ toℕ-+ʳ-inl r idʳ i ⟩
  toℕ (r i) ∎)
  where open ≡-Reasoning

-- symmetries with an empty block are casts
σʳ-0ˡ-isCast : ∀ m → IsCast (σʳ 0 m)
σʳ-0ˡ-isCast m i = trans (toℕ-σʳ-inr 0 m i) refl

σʳ-0ʳ-isCast : ∀ m (p : m + 0 ≡ m) → IsCast (σʳ m 0 ∘ʳ castʳ (sym p))
σʳ-0ʳ-isCast m p i = begin
  toℕ (σʳ m 0 (castʳ (sym p) i))
    ≡⟨ cong (toℕ ∘ σʳ m 0) (toℕ-injective (trans (toℕ-castʳ (sym p) i) (sym (toℕ-↑ˡ i 0)))) ⟩
  toℕ (σʳ m 0 (i ↑ˡ 0))
    ≡⟨ toℕ-σʳ-inl m 0 i ⟩
  toℕ i ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The hexagon identities for σ, as renamings (up to casts)
------------------------------------------------------------------------

castʳ-≡ : (e : m ≡ n) (i : Fin m) (j : Fin n) → toℕ i ≡ toℕ j → castʳ e i ≡ j
castʳ-≡ e i j h = toℕ-injective (trans (toℕ-castʳ e i) h)

-- σ_{m,n+k}  =  (n + σ_{m,k}) ∘ (σ_{m,n} + k)
σʳ-hexˡ : ∀ m n k (p : m + (n + k) ≡ (m + n) + k) (q : (n + m) + k ≡ n + (m + k)) (q' : n + (k + m) ≡ (n + k) + m)
  → σʳ m (n + k) ≗ (castʳ q' ∘ʳ (idʳ {n} +ʳ σʳ m k) ∘ʳ castʳ q ∘ʳ (σʳ m n +ʳ idʳ {k}) ∘ʳ castʳ p)
σʳ-hexˡ m n k p q q' = Fin+-ext
  (λ j → toℕ-injective (begin
    toℕ (σʳ m (n + k) (j ↑ˡ (n + k)))
      ≡⟨ toℕ-σʳ-inl m (n + k) j ⟩
    (n + k) + toℕ j
      ≡⟨ +-assoc n k (toℕ j) ⟩
    n + (k + toℕ j)
      ≡⟨ sym (trans (toℕ-+ʳ-inr (idʳ {n}) (σʳ m k) (j ↑ˡ k)) (cong (n +_) (toℕ-σʳ-inl m k j))) ⟩
    toℕ ((idʳ {n} +ʳ σʳ m k) (n ↑ʳ (j ↑ˡ k)))
      ≡⟨ cong (toℕ ∘ (idʳ {n} +ʳ σʳ m k)) (sym (castʳ-≡ q ((n ↑ʳ j) ↑ˡ k) (n ↑ʳ (j ↑ˡ k)) (trans (toℕ-↑ˡ (n ↑ʳ j) k) (trans (toℕ-↑ʳ n j) (sym (trans (toℕ-↑ʳ n (j ↑ˡ k)) (cong (n +_) (toℕ-↑ˡ j k)))))))) ⟩
    toℕ ((idʳ {n} +ʳ σʳ m k) (castʳ q ((n ↑ʳ j) ↑ˡ k)))
      ≡⟨ cong (toℕ ∘ (idʳ {n} +ʳ σʳ m k) ∘ castʳ q) (sym (trans (+ʳ-inj₁ (σʳ m n) (idʳ {k}) (j ↑ˡ n)) (cong (_↑ˡ k) (σʳ-inl m n j)))) ⟩
    toℕ ((idʳ {n} +ʳ σʳ m k) (castʳ q ((σʳ m n +ʳ idʳ {k}) ((j ↑ˡ n) ↑ˡ k))))
      ≡⟨ cong (toℕ ∘ (idʳ {n} +ʳ σʳ m k) ∘ castʳ q ∘ (σʳ m n +ʳ idʳ {k})) (sym (castʳ-≡ p (j ↑ˡ (n + k)) ((j ↑ˡ n) ↑ˡ k) (trans (toℕ-↑ˡ j (n + k)) (sym (trans (toℕ-↑ˡ (j ↑ˡ n) k) (toℕ-↑ˡ j n)))))) ⟩
    toℕ ((idʳ {n} +ʳ σʳ m k) (castʳ q ((σʳ m n +ʳ idʳ {k}) (castʳ p (j ↑ˡ (n + k))))))
      ≡⟨ sym (toℕ-castʳ q' _) ⟩
    toℕ (castʳ q' ((idʳ {n} +ʳ σʳ m k) (castʳ q ((σʳ m n +ʳ idʳ {k}) (castʳ p (j ↑ˡ (n + k))))))) ∎))
  (Fin+-ext
    (λ j → toℕ-injective (begin
      toℕ (σʳ m (n + k) (m ↑ʳ (j ↑ˡ k)))
        ≡⟨ toℕ-σʳ-inr m (n + k) (j ↑ˡ k) ⟩
      toℕ (j ↑ˡ k)
        ≡⟨ toℕ-↑ˡ j k ⟩
      toℕ j
        ≡⟨ sym (trans (toℕ-+ʳ-inl (idʳ {n}) (σʳ m k) j) refl) ⟩
      toℕ ((idʳ {n} +ʳ σʳ m k) (j ↑ˡ (m + k)))
        ≡⟨ cong (toℕ ∘ (idʳ {n} +ʳ σʳ m k)) (sym (castʳ-≡ q ((j ↑ˡ m) ↑ˡ k) (j ↑ˡ (m + k)) (trans (toℕ-↑ˡ (j ↑ˡ m) k) (trans (toℕ-↑ˡ j m) (sym (toℕ-↑ˡ j (m + k))))))) ⟩
      toℕ ((idʳ {n} +ʳ σʳ m k) (castʳ q ((j ↑ˡ m) ↑ˡ k)))
        ≡⟨ cong (toℕ ∘ (idʳ {n} +ʳ σʳ m k) ∘ castʳ q) (sym (trans (+ʳ-inj₁ (σʳ m n) (idʳ {k}) (m ↑ʳ j)) (cong (_↑ˡ k) (σʳ-inr m n j)))) ⟩
      toℕ ((idʳ {n} +ʳ σʳ m k) (castʳ q ((σʳ m n +ʳ idʳ {k}) ((m ↑ʳ j) ↑ˡ k))))
        ≡⟨ cong (toℕ ∘ (idʳ {n} +ʳ σʳ m k) ∘ castʳ q ∘ (σʳ m n +ʳ idʳ {k})) (sym (castʳ-≡ p (m ↑ʳ (j ↑ˡ k)) ((m ↑ʳ j) ↑ˡ k) (trans (toℕ-↑ʳ m (j ↑ˡ k)) (trans (cong (m +_) (toℕ-↑ˡ j k)) (sym (trans (toℕ-↑ˡ (m ↑ʳ j) k) (toℕ-↑ʳ m j))))))) ⟩
      toℕ ((idʳ {n} +ʳ σʳ m k) (castʳ q ((σʳ m n +ʳ idʳ {k}) (castʳ p (m ↑ʳ (j ↑ˡ k))))))
        ≡⟨ sym (toℕ-castʳ q' _) ⟩
      toℕ (castʳ q' ((idʳ {n} +ʳ σʳ m k) (castʳ q ((σʳ m n +ʳ idʳ {k}) (castʳ p (m ↑ʳ (j ↑ˡ k))))))) ∎))
    (λ j → toℕ-injective (begin
      toℕ (σʳ m (n + k) (m ↑ʳ (n ↑ʳ j)))
        ≡⟨ toℕ-σʳ-inr m (n + k) (n ↑ʳ j) ⟩
      toℕ (n ↑ʳ j)
        ≡⟨ toℕ-↑ʳ n j ⟩
      n + toℕ j
        ≡⟨ sym (trans (toℕ-+ʳ-inr (idʳ {n}) (σʳ m k) (m ↑ʳ j)) (cong (n +_) (toℕ-σʳ-inr m k j))) ⟩
      toℕ ((idʳ {n} +ʳ σʳ m k) (n ↑ʳ (m ↑ʳ j)))
        ≡⟨ cong (toℕ ∘ (idʳ {n} +ʳ σʳ m k)) (sym (castʳ-≡ q ((n + m) ↑ʳ j) (n ↑ʳ (m ↑ʳ j)) (trans (toℕ-↑ʳ (n + m) j) (trans (+-assoc n m (toℕ j)) (sym (trans (toℕ-↑ʳ n (m ↑ʳ j)) (cong (n +_) (toℕ-↑ʳ m j)))))))) ⟩
      toℕ ((idʳ {n} +ʳ σʳ m k) (castʳ q ((n + m) ↑ʳ j)))
        ≡⟨ cong (toℕ ∘ (idʳ {n} +ʳ σʳ m k) ∘ castʳ q) (sym (+ʳ-inj₂ (σʳ m n) (idʳ {k}) j)) ⟩
      toℕ ((idʳ {n} +ʳ σʳ m k) (castʳ q ((σʳ m n +ʳ idʳ {k}) ((m + n) ↑ʳ j))))
        ≡⟨ cong (toℕ ∘ (idʳ {n} +ʳ σʳ m k) ∘ castʳ q ∘ (σʳ m n +ʳ idʳ {k})) (sym (castʳ-≡ p (m ↑ʳ (n ↑ʳ j)) ((m + n) ↑ʳ j) (trans (toℕ-↑ʳ m (n ↑ʳ j)) (trans (cong (m +_) (toℕ-↑ʳ n j)) (trans (sym (+-assoc m n (toℕ j))) (sym (toℕ-↑ʳ (m + n) j))))))) ⟩
      toℕ ((idʳ {n} +ʳ σʳ m k) (castʳ q ((σʳ m n +ʳ idʳ {k}) (castʳ p (m ↑ʳ (n ↑ʳ j))))))
        ≡⟨ sym (toℕ-castʳ q' _) ⟩
      toℕ (castʳ q' ((idʳ {n} +ʳ σʳ m k) (castʳ q ((σʳ m n +ʳ idʳ {k}) (castʳ p (m ↑ʳ (n ↑ʳ j))))))) ∎)))
  where open ≡-Reasoning

-- σ_{m+n,k}  =  (σ_{m,k} + n) ∘ (m + σ_{n,k})
σʳ-hexʳ : ∀ m n k (p : (m + n) + k ≡ m + (n + k)) (q : m + (k + n) ≡ (m + k) + n) (q' : (k + m) + n ≡ k + (m + n))
  → σʳ (m + n) k ≗ (castʳ q' ∘ʳ (σʳ m k +ʳ idʳ {n}) ∘ʳ castʳ q ∘ʳ (idʳ {m} +ʳ σʳ n k) ∘ʳ castʳ p)
σʳ-hexʳ m n k p q q' = Fin+-ext
  (Fin+-ext
    (λ j → toℕ-injective (begin
      toℕ (σʳ (m + n) k ((j ↑ˡ n) ↑ˡ k))
        ≡⟨ toℕ-σʳ-inl (m + n) k (j ↑ˡ n) ⟩
      k + toℕ (j ↑ˡ n)
        ≡⟨ cong (k +_) (toℕ-↑ˡ j n) ⟩
      k + toℕ j
        ≡⟨ sym (trans (toℕ-+ʳ-inl (σʳ m k) (idʳ {n}) (j ↑ˡ k)) (toℕ-σʳ-inl m k j)) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) ((j ↑ˡ k) ↑ˡ n))
        ≡⟨ cong (toℕ ∘ (σʳ m k +ʳ idʳ {n})) (sym (castʳ-≡ q (j ↑ˡ (k + n)) ((j ↑ˡ k) ↑ˡ n) (trans (toℕ-↑ˡ j (k + n)) (sym (trans (toℕ-↑ˡ (j ↑ˡ k) n) (toℕ-↑ˡ j k)))))) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) (castʳ q (j ↑ˡ (k + n))))
        ≡⟨ cong (toℕ ∘ (σʳ m k +ʳ idʳ {n}) ∘ castʳ q) (sym (+ʳ-inj₁ (idʳ {m}) (σʳ n k) j)) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) (castʳ q ((idʳ {m} +ʳ σʳ n k) (j ↑ˡ (n + k)))))
        ≡⟨ cong (toℕ ∘ (σʳ m k +ʳ idʳ {n}) ∘ castʳ q ∘ (idʳ {m} +ʳ σʳ n k)) (sym (castʳ-≡ p ((j ↑ˡ n) ↑ˡ k) (j ↑ˡ (n + k)) (trans (toℕ-↑ˡ (j ↑ˡ n) k) (trans (toℕ-↑ˡ j n) (sym (toℕ-↑ˡ j (n + k))))))) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) (castʳ q ((idʳ {m} +ʳ σʳ n k) (castʳ p ((j ↑ˡ n) ↑ˡ k)))))
        ≡⟨ sym (toℕ-castʳ q' _) ⟩
      toℕ (castʳ q' ((σʳ m k +ʳ idʳ {n}) (castʳ q ((idʳ {m} +ʳ σʳ n k) (castʳ p ((j ↑ˡ n) ↑ˡ k)))))) ∎))
    (λ j → toℕ-injective (begin
      toℕ (σʳ (m + n) k ((m ↑ʳ j) ↑ˡ k))
        ≡⟨ toℕ-σʳ-inl (m + n) k (m ↑ʳ j) ⟩
      k + toℕ (m ↑ʳ j)
        ≡⟨ cong (k +_) (toℕ-↑ʳ m j) ⟩
      k + (m + toℕ j)
        ≡⟨ sym (+-assoc k m (toℕ j)) ⟩
      (k + m) + toℕ j
        ≡⟨ sym (toℕ-+ʳ-inr (σʳ m k) (idʳ {n}) j) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) ((m + k) ↑ʳ j))
        ≡⟨ cong (toℕ ∘ (σʳ m k +ʳ idʳ {n})) (sym (castʳ-≡ q (m ↑ʳ (k ↑ʳ j)) ((m + k) ↑ʳ j) (trans (toℕ-↑ʳ m (k ↑ʳ j)) (trans (cong (m +_) (toℕ-↑ʳ k j)) (trans (sym (+-assoc m k (toℕ j))) (sym (toℕ-↑ʳ (m + k) j))))))) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) (castʳ q (m ↑ʳ (k ↑ʳ j))))
        ≡⟨ cong (toℕ ∘ (σʳ m k +ʳ idʳ {n}) ∘ castʳ q) (sym (trans (+ʳ-inj₂ (idʳ {m}) (σʳ n k) (j ↑ˡ k)) (cong (m ↑ʳ_) (σʳ-inl n k j)))) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) (castʳ q ((idʳ {m} +ʳ σʳ n k) (m ↑ʳ (j ↑ˡ k)))))
        ≡⟨ cong (toℕ ∘ (σʳ m k +ʳ idʳ {n}) ∘ castʳ q ∘ (idʳ {m} +ʳ σʳ n k)) (sym (castʳ-≡ p ((m ↑ʳ j) ↑ˡ k) (m ↑ʳ (j ↑ˡ k)) (trans (toℕ-↑ˡ (m ↑ʳ j) k) (trans (toℕ-↑ʳ m j) (sym (trans (toℕ-↑ʳ m (j ↑ˡ k)) (cong (m +_) (toℕ-↑ˡ j k)))))))) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) (castʳ q ((idʳ {m} +ʳ σʳ n k) (castʳ p ((m ↑ʳ j) ↑ˡ k)))))
        ≡⟨ sym (toℕ-castʳ q' _) ⟩
      toℕ (castʳ q' ((σʳ m k +ʳ idʳ {n}) (castʳ q ((idʳ {m} +ʳ σʳ n k) (castʳ p ((m ↑ʳ j) ↑ˡ k)))))) ∎)))
  (λ j → toℕ-injective (begin
      toℕ (σʳ (m + n) k ((m + n) ↑ʳ j))
        ≡⟨ toℕ-σʳ-inr (m + n) k j ⟩
      toℕ j
        ≡⟨ sym (trans (toℕ-+ʳ-inl (σʳ m k) (idʳ {n}) (m ↑ʳ j)) (toℕ-σʳ-inr m k j)) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) ((m ↑ʳ j) ↑ˡ n))
        ≡⟨ cong (toℕ ∘ (σʳ m k +ʳ idʳ {n})) (sym (castʳ-≡ q (m ↑ʳ (j ↑ˡ n)) ((m ↑ʳ j) ↑ˡ n) (trans (toℕ-↑ʳ m (j ↑ˡ n)) (trans (cong (m +_) (toℕ-↑ˡ j n)) (sym (trans (toℕ-↑ˡ (m ↑ʳ j) n) (toℕ-↑ʳ m j))))))) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) (castʳ q (m ↑ʳ (j ↑ˡ n))))
        ≡⟨ cong (toℕ ∘ (σʳ m k +ʳ idʳ {n}) ∘ castʳ q) (sym (trans (+ʳ-inj₂ (idʳ {m}) (σʳ n k) (n ↑ʳ j)) (cong (m ↑ʳ_) (σʳ-inr n k j)))) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) (castʳ q ((idʳ {m} +ʳ σʳ n k) (m ↑ʳ (n ↑ʳ j)))))
        ≡⟨ cong (toℕ ∘ (σʳ m k +ʳ idʳ {n}) ∘ castʳ q ∘ (idʳ {m} +ʳ σʳ n k)) (sym (castʳ-≡ p ((m + n) ↑ʳ j) (m ↑ʳ (n ↑ʳ j)) (trans (toℕ-↑ʳ (m + n) j) (trans (+-assoc m n (toℕ j)) (sym (trans (toℕ-↑ʳ m (n ↑ʳ j)) (cong (m +_) (toℕ-↑ʳ n j)))))))) ⟩
      toℕ ((σʳ m k +ʳ idʳ {n}) (castʳ q ((idʳ {m} +ʳ σʳ n k) (castʳ p ((m + n) ↑ʳ j)))))
        ≡⟨ sym (toℕ-castʳ q' _) ⟩
      toℕ (castʳ q' ((σʳ m k +ʳ idʳ {n}) (castʳ q ((idʳ {m} +ʳ σʳ n k) (castʳ p ((m + n) ↑ʳ j)))))) ∎))
  where open ≡-Reasoning

-- case analysis on the three blocks of Fin (n₁ + suc n₂)
Fin-ins-cases : ∀ {ℓ} n₁ n₂ (P : Fin (n₁ + suc n₂) → Set ℓ)
  → (∀ j → P (j ↑ˡ suc n₂)) → P (n₁ ↑ʳ zero) → (∀ j → P (n₁ ↑ʳ suc j)) → ∀ i → P i
Fin-ins-cases n₁ n₂ P h₁ h₂ h₃ i with splitAt n₁ i in eq
... | inj₁ j       = subst P (splitAt⁻¹-↑ˡ eq) (h₁ j)
... | inj₂ zero    = subst P (splitAt⁻¹-↑ʳ eq) h₂
... | inj₂ (suc j) = subst P (splitAt⁻¹-↑ʳ eq) (h₃ j)
