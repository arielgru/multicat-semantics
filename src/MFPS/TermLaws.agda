------------------------------------------------------------------------
-- Section 4.3, Theorem 4.8: the laws of the term model.
--
-- Every law is an equation between terms built from the same
-- constituents by renamings, substitutions and the term formers
-- `bnd`/`ret`/`lam`.  The proofs follow a uniform pattern:
--   * fuse all renamings, substitutions and arity transports into a
--     single simultaneous substitution `sub σ` (the σ-calculus of
--     MFPS.Syntax: ren-sub, sub-ren, sub-sub, subst-ren);
--   * compare the two resulting substitutions pointwise, block by block
--     on the context  n₁ | hole | n₂  (`Fin-ins-ext`), where the
--     values are variables (compared through toℕ, with the arithmetic
--     discharged by the ring solver) or renamed copies of the
--     substituted term (compared with `ren-cong`);
--   * for computations, first use (lunit) to turn `let y ⇐ return V`
--     into a substitution, and (assoc) to reassociate nested lets.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad
open import MFPS.Syntax

module MFPS.TermLaws (Σ : Signature) where

open Signature Σ
open Terms Σ
open import MFPS.Theory Σ
open import MFPS.TermModel Σ
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_; con)

private
  variable
    k m n : ℕ
    s : Sort

------------------------------------------------------------------------
-- toℕ-characterisations of the block injections and hole-moving renaming
------------------------------------------------------------------------

toℕ-ι₁ : ∀ n₁ m n₂ (j : Fin n₁) → toℕ (ι₁ n₁ m n₂ j) ≡ toℕ j
toℕ-ι₁ n₁ m n₂ j = toℕ-↑ˡ j (m + n₂)

toℕ-ι₂ : ∀ n₁ m n₂ (j : Fin m) → toℕ (ι₂ n₁ m n₂ j) ≡ n₁ + toℕ j
toℕ-ι₂ n₁ m n₂ j = trans (toℕ-↑ʳ n₁ (j ↑ˡ n₂)) (cong (n₁ +_) (toℕ-↑ˡ j n₂))

toℕ-ι₃ : ∀ n₁ m n₂ (j : Fin n₂) → toℕ (ι₃ n₁ m n₂ j) ≡ n₁ + (m + toℕ j)
toℕ-ι₃ n₁ m n₂ j = trans (toℕ-↑ʳ n₁ (m ↑ʳ j)) (cong (n₁ +_) (toℕ-↑ʳ m j))

toℕ-hole : ∀ n₁ n₂ → toℕ (n₁ ↑ʳ zero {n₂}) ≡ n₁ + 0
toℕ-hole n₁ n₂ = toℕ-↑ʳ n₁ zero

toℕ-blk₃ : ∀ n₁ n₂ (j : Fin n₂) → toℕ (n₁ ↑ʳ suc j) ≡ n₁ + suc (toℕ j)
toℕ-blk₃ n₁ n₂ j = toℕ-↑ʳ n₁ (suc j)

toℕ-ρ-ins-₁ : ∀ n₁ n₂ m (j : Fin n₁) → toℕ (ρ-ins n₁ n₂ m (j ↑ˡ suc n₂)) ≡ toℕ j
toℕ-ρ-ins-₁ n₁ n₂ m j = trans (cong toℕ (ρ-ins-₁ n₁ n₂ m j)) (trans (toℕ-↑ˡ _ 1) (toℕ-ι₁ n₁ m n₂ j))

toℕ-ρ-ins-₂ : ∀ n₁ n₂ m → toℕ (ρ-ins n₁ n₂ m (n₁ ↑ʳ zero)) ≡ (n₁ + (m + n₂)) + 0
toℕ-ρ-ins-₂ n₁ n₂ m = trans (cong toℕ (ρ-ins-₂ n₁ n₂ m)) (toℕ-↑ʳ _ zero)

toℕ-ρ-ins-₃ : ∀ n₁ n₂ m (j : Fin n₂) → toℕ (ρ-ins n₁ n₂ m (n₁ ↑ʳ suc j)) ≡ n₁ + (m + toℕ j)
toℕ-ρ-ins-₃ n₁ n₂ m j = trans (cong toℕ (ρ-ins-₃ n₁ n₂ m j)) (trans (toℕ-↑ˡ _ 1) (toℕ-ι₃ n₁ m n₂ j))

toℕ-last : ∀ n → toℕ (last {n}) ≡ n + 0
toℕ-last n = toℕ-↑ʳ n zero

-- comparing variables and renamed terms through toℕ
var-≡ : {x y : Fin n} → toℕ x ≡ toℕ y → var {n} x ≡ var y
var-≡ e = cong var (toℕ-injective e)

ren-≡ : {r r' : Ren m n} → (∀ i → toℕ (r i) ≡ toℕ (r' i)) → (E : Trm m s) → ren r E ≡ ren r' E
ren-≡ h E = ren-cong (λ i → toℕ-injective (h i)) E

-- transport along an arity equation, fused into a substitution
subst-sub : (p : m ≡ n) (σ : Subst k m) (E : Trm k s)
  → subst (λ n → Trm n s) p (sub σ E) ≡ sub (λ i → ren (castʳ p) (σ i)) E
subst-sub p σ E = trans (subst-ren p _) (ren-sub σ (castʳ p) E)

-- arithmetic side conditions (discharged by the ring solver)
arith₁ : ∀ a b c → a + (b + suc c) ≡ (a + b) + suc c
arith₁ = solve 3 (λ a b c → a :+ (b :+ (con 1 :+ c)) := (a :+ b) :+ (con 1 :+ c)) refl
arith₂ : ∀ a b c d → (a + b) + (c + d) ≡ a + (b + (c + d))
arith₂ = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := a :+ (b :+ (c :+ d))) refl
arith₃ : ∀ a b c d → a + ((b + suc c) + d) ≡ (a + b) + suc (c + d)
arith₃ = solve 4 (λ a b c d → a :+ ((b :+ (con 1 :+ c)) :+ d) := (a :+ b) :+ (con 1 :+ (c :+ d))) refl
arith₄ : ∀ a b c d e → (a + b) + (c + (d + e)) ≡ a + ((b + (c + d)) + e)
arith₄ = solve 5 (λ a b c d e → (a :+ b) :+ (c :+ (d :+ e)) := a :+ ((b :+ (c :+ d)) :+ e)) refl
arith₅ : ∀ a b c → a + (b + (c + 0)) ≡ (a + (b + c)) + 0
arith₅ = solve 3 (λ a b c → a :+ (b :+ (c :+ con 0)) := (a :+ (b :+ c)) :+ con 0) refl
arith₆ : ∀ a b c d → (a + (b + c)) + d ≡ a + (b + (c + d))
arith₆ = solve 4 (λ a b c d → (a :+ (b :+ c)) :+ d := a :+ (b :+ (c :+ d))) refl
arith₇ : ∀ a b c → (a + suc b) + c ≡ a + suc (b + c)
arith₇ = solve 3 (λ a b c → (a :+ (con 1 :+ b)) :+ c := a :+ (con 1 :+ (b :+ c))) refl
arith₈ : ∀ a b → a + suc (b + 0) ≡ (a + suc b) + 0
arith₈ = solve 2 (λ a b → a :+ (con 1 :+ (b :+ con 0)) := (a :+ (con 1 :+ b)) :+ con 0) refl
arith₉ : ∀ a b c d → a + (b + (c + suc d)) ≡ (a + (b + c)) + suc d
arith₉ = solve 4 (λ a b c d → a :+ (b :+ (c :+ (con 1 :+ d))) := (a :+ (b :+ c)) :+ (con 1 :+ d)) refl
arith₁₀ : ∀ a b c d e → (a + (b + c)) + (d + e) ≡ a + (b + (c + (d + e)))
arith₁₀ = solve 5 (λ a b c d e → (a :+ (b :+ c)) :+ (d :+ e) := a :+ (b :+ (c :+ (d :+ e)))) refl
arith₁₁ : ∀ a b c d → (a + suc b) + (c + d) ≡ a + suc (b + (c + d))
arith₁₁ = solve 4 (λ a b c d → (a :+ (con 1 :+ b)) :+ (c :+ d) := a :+ (con 1 :+ (b :+ (c :+ d)))) refl
arith₁₂ : ∀ a b c → a + suc (b + suc c) ≡ (a + suc b) + suc c
arith₁₂ = solve 3 (λ a b c → a :+ (con 1 :+ (b :+ (con 1 :+ c))) := (a :+ (con 1 :+ b)) :+ (con 1 :+ c)) refl
arith₁₃ : ∀ a b c → a + ((b + 1) + c) ≡ a + (b + suc c)
arith₁₃ = solve 3 (λ a b c → a :+ ((b :+ con 1) :+ c) := a :+ (b :+ (con 1 :+ c))) refl
arith₁₄ : ∀ a b c → a + (b + suc c) ≡ a + ((b + 1) + c)
arith₁₄ = solve 3 (λ a b c → a :+ (b :+ (con 1 :+ c)) := a :+ ((b :+ con 1) :+ c)) refl
arith₁₅ : ∀ a b c → a + (b + (c + 0)) ≡ (a + (b + c)) + 0
arith₁₅ = solve 3 (λ a b c → a :+ (b :+ (c :+ con 0)) := (a :+ (b :+ c)) :+ con 0) refl
arith₁₆ : ∀ a b → a + suc (b + 0) ≡ (a + suc b) + 0
arith₁₆ = solve 2 (λ a b → a :+ (con 1 :+ (b :+ con 0)) := (a :+ (con 1 :+ b)) :+ con 0) refl

------------------------------------------------------------------------
-- (iii) associativity for values
------------------------------------------------------------------------

assocᵛ : ∀ {m₁ m₂ n₁ n₂ n} (f : Val (m₁ + suc m₂)) (g : Val (n₁ + suc n₂)) (h : Val n)
  (p : m₁ + ((n₁ + suc n₂) + m₂) ≡ (m₁ + n₁) + suc (n₂ + m₂))
  (q : (m₁ + n₁) + (n + (n₂ + m₂)) ≡ m₁ + ((n₁ + (n + n₂)) + m₂))
  → subst Val q (subᵛ (m₁ + n₁) (n₂ + m₂) (subst Val p (subᵛ m₁ m₂ f g)) h)
    ≈ subᵛ m₁ m₂ f (subᵛ n₁ n₂ g h)
assocᵛ {m₁} {m₂} {n₁} {n₂} {n} f g h p q = ≈-≡ (begin
  subst Val q (sub S₂ (subst Val p (sub S₁ f)))
    ≡⟨ subst-sub q S₂ (subst Val p (sub S₁ f)) ⟩
  sub (λ i → ren (castʳ q) (S₂ i)) (subst Val p (sub S₁ f))
    ≡⟨ cong (sub _) (subst-sub p S₁ f) ⟩
  sub (λ i → ren (castʳ q) (S₂ i)) (sub (λ i → ren (castʳ p) (S₁ i)) f)
    ≡⟨ sub-sub _ _ f ⟩
  sub Σ₀ f
    ≡⟨ sub-cong pointwise f ⟩
  sub (σ-ins m₁ m₂ (subᵛ n₁ n₂ g h)) f ∎)
  where
    open ≡-Reasoning
    S₁ = σ-ins m₁ m₂ g
    S₂ = σ-ins (m₁ + n₁) (n₂ + m₂) h
    Σ₀ : Subst (m₁ + suc m₂) (m₁ + ((n₁ + (n + n₂)) + m₂))
    Σ₀ i = sub (λ i → ren (castʳ q) (S₂ i)) (ren (castʳ p) (S₁ i))
    -- the middle block of the middle block: the argument h
    hole-hole : Σ₀ (m₁ ↑ʳ zero) ≡ σ-ins m₁ m₂ (subᵛ n₁ n₂ g h) (m₁ ↑ʳ zero)
    hole-hole = begin
      sub (λ i → ren (castʳ q) (S₂ i)) (ren (castʳ p) (S₁ (m₁ ↑ʳ zero)))
        ≡⟨ cong (λ z → sub _ (ren (castʳ p) z)) (σ-ins-₂ m₁ m₂ g) ⟩
      sub (λ i → ren (castʳ q) (S₂ i)) (ren (castʳ p) (ren (ι₂ m₁ (n₁ + suc n₂) m₂) g))
        ≡⟨ cong (sub _) (sym (ren-∘ _ _ g)) ⟩
      sub (λ i → ren (castʳ q) (S₂ i)) (ren (castʳ p ∘ʳ ι₂ m₁ (n₁ + suc n₂) m₂) g)
        ≡⟨ sub-ren _ _ g ⟩
      sub ((λ i → ren (castʳ q) (S₂ i)) ∘ (castʳ p ∘ʳ ι₂ m₁ (n₁ + suc n₂) m₂)) g
        ≡⟨ sub-cong inner g ⟩
      sub (λ i → ren (ι₂ m₁ (n₁ + (n + n₂)) m₂) (σ-ins n₁ n₂ h i)) g
        ≡⟨ sym (ren-sub _ _ g) ⟩
      ren (ι₂ m₁ (n₁ + (n + n₂)) m₂) (sub (σ-ins n₁ n₂ h) g)
        ≡⟨ sym (σ-ins-₂ m₁ m₂ _) ⟩
      σ-ins m₁ m₂ (subᵛ n₁ n₂ g h) (m₁ ↑ʳ zero) ∎
      where
        inner : ((λ i → ren (castʳ q) (S₂ i)) ∘ (castʳ p ∘ʳ ι₂ m₁ (n₁ + suc n₂) m₂))
              ≗ (λ i → ren (ι₂ m₁ (n₁ + (n + n₂)) m₂) (σ-ins n₁ n₂ h i))
        inner = Fin-ins-ext n₁ n₂
          (λ j → begin
            ren (castʳ q) (S₂ (castʳ p (ι₂ m₁ (n₁ + suc n₂) m₂ (j ↑ˡ suc n₂))))
              ≡⟨ cong (λ z → ren (castʳ q) (S₂ z)) (castʳ-≡ p _ ((m₁ ↑ʳ j) ↑ˡ suc (n₂ + m₂))
                   (trans (toℕ-ι₂ m₁ (n₁ + suc n₂) m₂ (j ↑ˡ suc n₂)) (trans (cong (m₁ +_) (toℕ-↑ˡ j (suc n₂))) (sym (trans (toℕ-↑ˡ (m₁ ↑ʳ j) (suc (n₂ + m₂))) (toℕ-↑ʳ m₁ j)))))) ⟩
            ren (castʳ q) (S₂ ((m₁ ↑ʳ j) ↑ˡ suc (n₂ + m₂)))
              ≡⟨ cong (ren (castʳ q)) (σ-ins-₁ (m₁ + n₁) (n₂ + m₂) h (m₁ ↑ʳ j)) ⟩
            var (castʳ q (ι₁ (m₁ + n₁) n (n₂ + m₂) (m₁ ↑ʳ j)))
              ≡⟨ var-≡ (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + n₁) n (n₂ + m₂) (m₁ ↑ʳ j)) (trans (toℕ-↑ʳ m₁ j) (sym (trans (toℕ-ι₂ m₁ (n₁ + (n + n₂)) m₂ (ι₁ n₁ n n₂ j)) (cong (m₁ +_) (toℕ-ι₁ n₁ n n₂ j))))))) ⟩
            var (ι₂ m₁ (n₁ + (n + n₂)) m₂ (ι₁ n₁ n n₂ j))
              ≡⟨ cong (ren _) (sym (σ-ins-₁ n₁ n₂ h j)) ⟩
            ren (ι₂ m₁ (n₁ + (n + n₂)) m₂) (σ-ins n₁ n₂ h (j ↑ˡ suc n₂)) ∎)
          (begin
            ren (castʳ q) (S₂ (castʳ p (ι₂ m₁ (n₁ + suc n₂) m₂ (n₁ ↑ʳ zero))))
              ≡⟨ cong (λ z → ren (castʳ q) (S₂ z)) (castʳ-≡ p _ ((m₁ + n₁) ↑ʳ zero)
                   (trans (toℕ-ι₂ m₁ (n₁ + suc n₂) m₂ (n₁ ↑ʳ zero)) (trans (cong (m₁ +_) (toℕ-hole n₁ n₂)) (trans (sym (+-assoc m₁ n₁ 0)) (sym (toℕ-hole (m₁ + n₁) _)))))) ⟩
            ren (castʳ q) (S₂ ((m₁ + n₁) ↑ʳ zero))
              ≡⟨ cong (ren (castʳ q)) (σ-ins-₂ (m₁ + n₁) (n₂ + m₂) h) ⟩
            ren (castʳ q) (ren (ι₂ (m₁ + n₁) n (n₂ + m₂)) h)
              ≡⟨ sym (ren-∘ _ _ h) ⟩
            ren (castʳ q ∘ʳ ι₂ (m₁ + n₁) n (n₂ + m₂)) h
              ≡⟨ ren-≡ (λ x → trans (toℕ-castʳ q _) (trans (toℕ-ι₂ (m₁ + n₁) n (n₂ + m₂) x) (trans (+-assoc m₁ n₁ (toℕ x)) (sym (trans (toℕ-ι₂ m₁ (n₁ + (n + n₂)) m₂ (ι₂ n₁ n n₂ x)) (cong (m₁ +_) (toℕ-ι₂ n₁ n n₂ x))))))) h ⟩
            ren (ι₂ m₁ (n₁ + (n + n₂)) m₂ ∘ʳ ι₂ n₁ n n₂) h
              ≡⟨ ren-∘ _ _ h ⟩
            ren (ι₂ m₁ (n₁ + (n + n₂)) m₂) (ren (ι₂ n₁ n n₂) h)
              ≡⟨ cong (ren _) (sym (σ-ins-₂ n₁ n₂ h)) ⟩
            ren (ι₂ m₁ (n₁ + (n + n₂)) m₂) (σ-ins n₁ n₂ h (n₁ ↑ʳ zero)) ∎)
          (λ j → begin
            ren (castʳ q) (S₂ (castʳ p (ι₂ m₁ (n₁ + suc n₂) m₂ (n₁ ↑ʳ suc j))))
              ≡⟨ cong (λ z → ren (castʳ q) (S₂ z)) (castʳ-≡ p _ ((m₁ + n₁) ↑ʳ suc (j ↑ˡ m₂))
                   (trans (toℕ-ι₂ m₁ (n₁ + suc n₂) m₂ (n₁ ↑ʳ suc j)) (trans (cong (m₁ +_) (toℕ-blk₃ n₁ n₂ j)) (trans (arith₁ m₁ n₁ (toℕ j)) (sym (trans (toℕ-blk₃ (m₁ + n₁) _ _) (cong (λ z → (m₁ + n₁) + suc z) (toℕ-↑ˡ j m₂)))))))) ⟩
            ren (castʳ q) (S₂ ((m₁ + n₁) ↑ʳ suc (j ↑ˡ m₂)))
              ≡⟨ cong (ren (castʳ q)) (σ-ins-₃ (m₁ + n₁) (n₂ + m₂) h (j ↑ˡ m₂)) ⟩
            var (castʳ q (ι₃ (m₁ + n₁) n (n₂ + m₂) (j ↑ˡ m₂)))
              ≡⟨ var-≡ (trans (toℕ-castʳ q _) (trans (toℕ-ι₃ (m₁ + n₁) n (n₂ + m₂) (j ↑ˡ m₂)) (trans (cong (λ z → (m₁ + n₁) + (n + z)) (toℕ-↑ˡ j m₂)) (trans (arith₂ m₁ n₁ n (toℕ j)) (sym (trans (toℕ-ι₂ m₁ (n₁ + (n + n₂)) m₂ (ι₃ n₁ n n₂ j)) (cong (m₁ +_) (toℕ-ι₃ n₁ n n₂ j)))))))) ⟩
            var (ι₂ m₁ (n₁ + (n + n₂)) m₂ (ι₃ n₁ n n₂ j))
              ≡⟨ cong (ren _) (sym (σ-ins-₃ n₁ n₂ h j)) ⟩
            ren (ι₂ m₁ (n₁ + (n + n₂)) m₂) (σ-ins n₁ n₂ h (n₁ ↑ʳ suc j)) ∎)
    pointwise : Σ₀ ≗ σ-ins m₁ m₂ (subᵛ n₁ n₂ g h)
    pointwise = Fin-ins-ext m₁ m₂
      (λ j → begin
        sub (λ i → ren (castʳ q) (S₂ i)) (ren (castʳ p) (S₁ (j ↑ˡ suc m₂)))
          ≡⟨ cong (λ z → sub _ (ren (castʳ p) z)) (σ-ins-₁ m₁ m₂ g j) ⟩
        ren (castʳ q) (S₂ (castʳ p (ι₁ m₁ (n₁ + suc n₂) m₂ j)))
          ≡⟨ cong (λ z → ren (castʳ q) (S₂ z)) (castʳ-≡ p _ ((j ↑ˡ n₁) ↑ˡ suc (n₂ + m₂)) (trans (toℕ-ι₁ m₁ (n₁ + suc n₂) m₂ j) (sym (trans (toℕ-↑ˡ (j ↑ˡ n₁) (suc (n₂ + m₂))) (toℕ-↑ˡ j n₁))))) ⟩
        ren (castʳ q) (S₂ ((j ↑ˡ n₁) ↑ˡ suc (n₂ + m₂)))
          ≡⟨ cong (ren (castʳ q)) (σ-ins-₁ (m₁ + n₁) (n₂ + m₂) h (j ↑ˡ n₁)) ⟩
        var (castʳ q (ι₁ (m₁ + n₁) n (n₂ + m₂) (j ↑ˡ n₁)))
          ≡⟨ var-≡ (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + n₁) n (n₂ + m₂) (j ↑ˡ n₁)) (trans (toℕ-↑ˡ j n₁) (sym (toℕ-ι₁ m₁ (n₁ + (n + n₂)) m₂ j))))) ⟩
        var (ι₁ m₁ (n₁ + (n + n₂)) m₂ j)
          ≡⟨ sym (σ-ins-₁ m₁ m₂ _ j) ⟩
        σ-ins m₁ m₂ (subᵛ n₁ n₂ g h) (j ↑ˡ suc m₂) ∎)
      hole-hole
      (λ j → begin
        sub (λ i → ren (castʳ q) (S₂ i)) (ren (castʳ p) (S₁ (m₁ ↑ʳ suc j)))
          ≡⟨ cong (λ z → sub _ (ren (castʳ p) z)) (σ-ins-₃ m₁ m₂ g j) ⟩
        ren (castʳ q) (S₂ (castʳ p (ι₃ m₁ (n₁ + suc n₂) m₂ j)))
          ≡⟨ cong (λ z → ren (castʳ q) (S₂ z)) (castʳ-≡ p _ ((m₁ + n₁) ↑ʳ suc (n₂ ↑ʳ j))
               (trans (toℕ-ι₃ m₁ (n₁ + suc n₂) m₂ j) (trans (arith₃ m₁ n₁ n₂ (toℕ j)) (sym (trans (toℕ-blk₃ (m₁ + n₁) _ _) (cong (λ z → (m₁ + n₁) + suc z) (toℕ-↑ʳ n₂ j))))))) ⟩
        ren (castʳ q) (S₂ ((m₁ + n₁) ↑ʳ suc (n₂ ↑ʳ j)))
          ≡⟨ cong (ren (castʳ q)) (σ-ins-₃ (m₁ + n₁) (n₂ + m₂) h (n₂ ↑ʳ j)) ⟩
        var (castʳ q (ι₃ (m₁ + n₁) n (n₂ + m₂) (n₂ ↑ʳ j)))
          ≡⟨ var-≡ (trans (toℕ-castʳ q _) (trans (toℕ-ι₃ (m₁ + n₁) n (n₂ + m₂) (n₂ ↑ʳ j)) (trans (cong (λ z → (m₁ + n₁) + (n + z)) (toℕ-↑ʳ n₂ j)) (trans (arith₄ m₁ n₁ n n₂ (toℕ j)) (sym (toℕ-ι₃ m₁ (n₁ + (n + n₂)) m₂ j)))))) ⟩
        var (ι₃ m₁ (n₁ + (n + n₂)) m₂ j)
          ≡⟨ sym (σ-ins-₃ m₁ m₂ _ j) ⟩
        σ-ins m₁ m₂ (subᵛ n₁ n₂ g h) (m₁ ↑ʳ suc j) ∎)

------------------------------------------------------------------------
-- Def. 3.6: any two values commute (VAL is an operad).
-- Both orders of substituting g₁ (at position m₁) and g₂ (at position
-- m₁ + 1 + m) into f fuse to the same simultaneous substitution.
------------------------------------------------------------------------

-- substituting into a renamed term
sub-ren-var : (R : Ren k m) (τ : Subst m n) (R' : Ren k n) → (∀ x → τ (R x) ≡ var (R' x)) → (E : Trm k s)
  → sub τ (ren R E) ≡ ren R' E
sub-ren-var R τ R' h E = trans (sub-ren R τ E) (trans (sub-cong h E) (sub-⌜⌝ R' E))

-- the statement of Def. 3.6 (Centrality.Comm) for VAL, unfolded
commᵛ : ∀ {n₁ n₂} (g₁ : Val n₁) (g₂ : Val n₂) m₁ m m₂ (f : Val (m₁ + suc (m + suc m₂)))
  (p   : m₁ + (n₁ + (m + suc m₂)) ≡ (m₁ + (n₁ + m)) + suc m₂)
  (p'  : m₁ + suc (m + suc m₂) ≡ (m₁ + suc m) + suc m₂)
  (p'' : (m₁ + suc m) + (n₂ + m₂) ≡ m₁ + suc (m + (n₂ + m₂)))
  (q   : (m₁ + (n₁ + m)) + (n₂ + m₂) ≡ m₁ + (n₁ + (m + (n₂ + m₂))))
  → subst Val q (subᵛ (m₁ + (n₁ + m)) m₂ (subst Val p (subᵛ m₁ (m + suc m₂) f g₁)) g₂)
    ≈ subᵛ m₁ (m + (n₂ + m₂)) (subst Val p'' (subᵛ (m₁ + suc m) m₂ (subst Val p' f) g₂)) g₁
commᵛ {n₁} {n₂} g₁ g₂ m₁ m m₂ f p p' p'' q = ≈-≡ (begin
  subst Val q (sub S₂ (subst Val p (sub S₁ f)))
    ≡⟨ subst-sub q S₂ (subst Val p (sub S₁ f)) ⟩
  sub (λ i → ren (castʳ q) (S₂ i)) (subst Val p (sub S₁ f))
    ≡⟨ cong (sub _) (subst-sub p S₁ f) ⟩
  sub (λ i → ren (castʳ q) (S₂ i)) (sub (λ i → ren (castʳ p) (S₁ i)) f)
    ≡⟨ sub-sub _ _ f ⟩
  sub ΣL f
    ≡⟨ sub-cong pointwise f ⟩
  sub ΣR f
    ≡⟨ sym (sub-sub _ _ f) ⟩
  sub T₁ (sub (λ i → ren (castʳ p'') (T₂ (castʳ p' i))) f)
    ≡⟨ cong (sub T₁) (sym (subst-sub p'' _ f)) ⟩
  sub T₁ (subst Val p'' (sub (T₂ ∘ castʳ p') f))
    ≡⟨ cong (λ z → sub T₁ (subst Val p'' z)) (sym (sub-ren _ _ f)) ⟩
  sub T₁ (subst Val p'' (sub T₂ (ren (castʳ p') f)))
    ≡⟨ cong (λ z → sub T₁ (subst Val p'' (sub T₂ z))) (sym (subst-ren p' f)) ⟩
  sub T₁ (subst Val p'' (sub T₂ (subst Val p' f))) ∎)
  where
    open ≡-Reasoning
    S₁ = σ-ins m₁ (m + suc m₂) g₁
    S₂ = σ-ins (m₁ + (n₁ + m)) m₂ g₂
    T₂ = σ-ins (m₁ + suc m) m₂ g₂
    T₁ = σ-ins m₁ (m + (n₂ + m₂)) g₁
    ΣL ΣR : Subst (m₁ + suc (m + suc m₂)) (m₁ + (n₁ + (m + (n₂ + m₂))))
    ΣL i = sub (λ i → ren (castʳ q) (S₂ i)) (ren (castʳ p) (S₁ i))
    ΣR i = sub T₁ (ren (castʳ p'') (T₂ (castʳ p' i)))
    -- the value of ΣL, ΣR at a variable is determined by its position
    ΣL-var : (x : Fin (m₁ + suc (m + suc m₂))) {y : Fin (m₁ + (n₁ + (m + suc m₂)))} → S₁ x ≡ var y
      → ΣL x ≡ ren (castʳ q) (S₂ (castʳ p y))
    ΣL-var x e = cong (λ z → sub _ (ren (castʳ p) z)) e
    ΣR-var : (x : Fin (m₁ + suc (m + suc m₂))) {y : Fin ((m₁ + suc m) + (n₂ + m₂))} → T₂ (castʳ p' x) ≡ var y
      → ΣR x ≡ T₁ (castʳ p'' y)
    ΣR-var x e = cong (λ z → sub T₁ (ren (castʳ p'') z)) e

    pointwise : ΣL ≗ ΣR
    pointwise = Fin-ins-ext m₁ (m + suc m₂) blockA hole₁ (Fin-ins-ext m m₂ blockB hole₂ blockC)
      where
      blockA : ∀ j → ΣL (j ↑ˡ suc (m + suc m₂)) ≡ ΣR (j ↑ˡ suc (m + suc m₂))
      blockA j = begin
        ΣL (j ↑ˡ _)
          ≡⟨ ΣL-var _ (σ-ins-₁ m₁ (m + suc m₂) g₁ j) ⟩
        ren (castʳ q) (S₂ (castʳ p (ι₁ m₁ n₁ (m + suc m₂) j)))
          ≡⟨ cong (λ z → ren (castʳ q) (S₂ z)) (castʳ-≡ p _ ((j ↑ˡ (n₁ + m)) ↑ˡ suc m₂) (trans (toℕ-ι₁ m₁ n₁ _ j) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j _))))) ⟩
        ren (castʳ q) (S₂ ((j ↑ˡ (n₁ + m)) ↑ˡ suc m₂))
          ≡⟨ cong (ren (castʳ q)) (σ-ins-₁ (m₁ + (n₁ + m)) m₂ g₂ (j ↑ˡ (n₁ + m))) ⟩
        var (castʳ q (ι₁ (m₁ + (n₁ + m)) n₂ m₂ (j ↑ˡ (n₁ + m))))
          ≡⟨ var-≡ (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + (n₁ + m)) n₂ m₂ _) (trans (toℕ-↑ˡ j _) (sym (toℕ-ι₁ m₁ n₁ _ j))))) ⟩
        var (ι₁ m₁ n₁ (m + (n₂ + m₂)) j)
          ≡⟨ sym (σ-ins-₁ m₁ (m + (n₂ + m₂)) g₁ j) ⟩
        T₁ (j ↑ˡ suc (m + (n₂ + m₂)))
          ≡⟨ cong T₁ (sym (castʳ-≡ p'' _ _ (trans (toℕ-ι₁ (m₁ + suc m) n₂ m₂ _) (trans (toℕ-↑ˡ j _) (sym (toℕ-↑ˡ j _)))))) ⟩
        T₁ (castʳ p'' (ι₁ (m₁ + suc m) n₂ m₂ (j ↑ˡ suc m)))
          ≡⟨ sym (ΣR-var _ (trans (cong T₂ (castʳ-≡ p' _ ((j ↑ˡ suc m) ↑ˡ suc m₂) (trans (toℕ-↑ˡ j _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j _)))))) (σ-ins-₁ (m₁ + suc m) m₂ g₂ (j ↑ˡ suc m)))) ⟩
        ΣR (j ↑ˡ _) ∎
      hole₁ : ΣL (m₁ ↑ʳ zero) ≡ ΣR (m₁ ↑ʳ zero)
      hole₁ = begin
        ΣL (m₁ ↑ʳ zero)
          ≡⟨ cong (λ z → sub _ (ren (castʳ p) z)) (σ-ins-₂ m₁ (m + suc m₂) g₁) ⟩
        sub (λ i → ren (castʳ q) (S₂ i)) (ren (castʳ p) (ren (ι₂ m₁ n₁ (m + suc m₂)) g₁))
          ≡⟨ cong (sub _) (sym (ren-∘ _ _ g₁)) ⟩
        sub (λ i → ren (castʳ q) (S₂ i)) (ren (castʳ p ∘ʳ ι₂ m₁ n₁ (m + suc m₂)) g₁)
          ≡⟨ sub-ren-var _ _ (ι₂ m₁ n₁ (m + (n₂ + m₂)))
               (λ x → trans (cong (λ z → ren (castʳ q) (S₂ z)) (castʳ-≡ p _ ((m₁ ↑ʳ (x ↑ˡ m)) ↑ˡ suc m₂)
                               (trans (toℕ-ι₂ m₁ n₁ _ x) (sym (trans (toℕ-↑ˡ _ _) (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ˡ x m))))))))
                     (trans (cong (ren (castʳ q)) (σ-ins-₁ (m₁ + (n₁ + m)) m₂ g₂ (m₁ ↑ʳ (x ↑ˡ m))))
                            (var-≡ (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + (n₁ + m)) n₂ m₂ _) (trans (toℕ-↑ʳ m₁ _) (trans (cong (m₁ +_) (toℕ-↑ˡ x m)) (sym (toℕ-ι₂ m₁ n₁ _ x)))))))))
               g₁ ⟩
        ren (ι₂ m₁ n₁ (m + (n₂ + m₂))) g₁
          ≡⟨ sym (σ-ins-₂ m₁ (m + (n₂ + m₂)) g₁) ⟩
        T₁ (m₁ ↑ʳ zero)
          ≡⟨ cong T₁ (sym (castʳ-≡ p'' _ _ (trans (toℕ-ι₁ (m₁ + suc m) n₂ m₂ _) (trans (toℕ-hole m₁ m) (sym (toℕ-hole m₁ _)))))) ⟩
        T₁ (castʳ p'' (ι₁ (m₁ + suc m) n₂ m₂ (m₁ ↑ʳ zero)))
          ≡⟨ sym (ΣR-var _ (trans (cong T₂ (castʳ-≡ p' _ ((m₁ ↑ʳ zero) ↑ˡ suc m₂) (trans (toℕ-hole m₁ _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-hole m₁ m))))))
                            (σ-ins-₁ (m₁ + suc m) m₂ g₂ (m₁ ↑ʳ zero)))) ⟩
        ΣR (m₁ ↑ʳ zero) ∎
      blockB : ∀ j → ΣL (m₁ ↑ʳ suc (j ↑ˡ suc m₂)) ≡ ΣR (m₁ ↑ʳ suc (j ↑ˡ suc m₂))
      blockB j = begin
        ΣL (m₁ ↑ʳ suc (j ↑ˡ suc m₂))
          ≡⟨ ΣL-var _ (σ-ins-₃ m₁ (m + suc m₂) g₁ (j ↑ˡ suc m₂)) ⟩
        ren (castʳ q) (S₂ (castʳ p (ι₃ m₁ n₁ (m + suc m₂) (j ↑ˡ suc m₂))))
          ≡⟨ cong (λ z → ren (castʳ q) (S₂ z)) (castʳ-≡ p _ ((m₁ ↑ʳ (n₁ ↑ʳ j)) ↑ˡ suc m₂)
               (trans (toℕ-ι₃ m₁ n₁ _ _) (trans (cong (λ z → m₁ + (n₁ + z)) (toℕ-↑ˡ j _)) (sym (trans (toℕ-↑ˡ _ _) (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ n₁ j)))))))) ⟩
        ren (castʳ q) (S₂ ((m₁ ↑ʳ (n₁ ↑ʳ j)) ↑ˡ suc m₂))
          ≡⟨ cong (ren (castʳ q)) (σ-ins-₁ (m₁ + (n₁ + m)) m₂ g₂ (m₁ ↑ʳ (n₁ ↑ʳ j))) ⟩
        var (castʳ q (ι₁ (m₁ + (n₁ + m)) n₂ m₂ (m₁ ↑ʳ (n₁ ↑ʳ j))))
          ≡⟨ var-≡ (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + (n₁ + m)) n₂ m₂ _) (trans (toℕ-↑ʳ m₁ _) (trans (cong (m₁ +_) (toℕ-↑ʳ n₁ j)) (sym (trans (toℕ-ι₃ m₁ n₁ _ _) (cong (λ z → m₁ + (n₁ + z)) (toℕ-↑ˡ j _)))))))) ⟩
        var (ι₃ m₁ n₁ (m + (n₂ + m₂)) (j ↑ˡ (n₂ + m₂)))
          ≡⟨ sym (σ-ins-₃ m₁ (m + (n₂ + m₂)) g₁ (j ↑ˡ (n₂ + m₂))) ⟩
        T₁ (m₁ ↑ʳ suc (j ↑ˡ (n₂ + m₂)))
          ≡⟨ cong T₁ (sym (castʳ-≡ p'' _ _ (trans (toℕ-ι₁ (m₁ + suc m) n₂ m₂ _) (trans (toℕ-blk₃ m₁ m j) (sym (trans (toℕ-blk₃ m₁ _ _) (cong (λ z → m₁ + suc z) (toℕ-↑ˡ j _)))))))) ⟩
        T₁ (castʳ p'' (ι₁ (m₁ + suc m) n₂ m₂ (m₁ ↑ʳ suc j)))
          ≡⟨ sym (ΣR-var _ (trans (cong T₂ (castʳ-≡ p' _ ((m₁ ↑ʳ suc j) ↑ˡ suc m₂) (trans (toℕ-blk₃ m₁ _ _) (trans (cong (λ z → m₁ + suc z) (toℕ-↑ˡ j _)) (sym (trans (toℕ-↑ˡ _ _) (toℕ-blk₃ m₁ m j)))))))
                            (σ-ins-₁ (m₁ + suc m) m₂ g₂ (m₁ ↑ʳ suc j)))) ⟩
        ΣR (m₁ ↑ʳ suc (j ↑ˡ suc m₂)) ∎
      hole₂ : ΣL (m₁ ↑ʳ suc (m ↑ʳ zero)) ≡ ΣR (m₁ ↑ʳ suc (m ↑ʳ zero))
      hole₂ = begin
        ΣL (m₁ ↑ʳ suc (m ↑ʳ zero))
          ≡⟨ ΣL-var _ (σ-ins-₃ m₁ (m + suc m₂) g₁ (m ↑ʳ zero)) ⟩
        ren (castʳ q) (S₂ (castʳ p (ι₃ m₁ n₁ (m + suc m₂) (m ↑ʳ zero))))
          ≡⟨ cong (λ z → ren (castʳ q) (S₂ z)) (castʳ-≡ p _ ((m₁ + (n₁ + m)) ↑ʳ zero)
               (trans (toℕ-ι₃ m₁ n₁ _ _) (trans (cong (λ z → m₁ + (n₁ + z)) (toℕ-hole m _)) (trans (arith₅ m₁ n₁ m) (sym (toℕ-hole _ _)))))) ⟩
        ren (castʳ q) (S₂ ((m₁ + (n₁ + m)) ↑ʳ zero))
          ≡⟨ cong (ren (castʳ q)) (σ-ins-₂ (m₁ + (n₁ + m)) m₂ g₂) ⟩
        ren (castʳ q) (ren (ι₂ (m₁ + (n₁ + m)) n₂ m₂) g₂)
          ≡⟨ sym (ren-∘ _ _ g₂) ⟩
        ren (castʳ q ∘ʳ ι₂ (m₁ + (n₁ + m)) n₂ m₂) g₂
          ≡⟨ ren-≡ (λ x → trans (toℕ-castʳ q _) (trans (toℕ-ι₂ (m₁ + (n₁ + m)) n₂ m₂ x) (trans (arith₆ m₁ n₁ m (toℕ x)) (sym (trans (toℕ-ι₃ m₁ n₁ _ _) (cong (λ z → m₁ + (n₁ + z)) (trans (toℕ-↑ʳ m (x ↑ˡ m₂)) (cong (m +_) (toℕ-↑ˡ x m₂))))))))) g₂ ⟩
        ren (λ x → ι₃ m₁ n₁ (m + (n₂ + m₂)) (m ↑ʳ (x ↑ˡ m₂))) g₂
          ≡⟨ sym (sub-ren-var _ T₁ _ (λ x → trans (cong T₁ (castʳ-≡ p'' _ (m₁ ↑ʳ suc (m ↑ʳ (x ↑ˡ m₂))) (trans (toℕ-ι₂ (m₁ + suc m) n₂ m₂ x) (trans (arith₇ m₁ m (toℕ x)) (sym (trans (toℕ-blk₃ m₁ _ _) (cong (λ z → m₁ + suc z) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ˡ x m₂))))))))))
                                              (σ-ins-₃ m₁ (m + (n₂ + m₂)) g₁ (m ↑ʳ (x ↑ˡ m₂)))) g₂) ⟩
        sub T₁ (ren (castʳ p'' ∘ʳ ι₂ (m₁ + suc m) n₂ m₂) g₂)
          ≡⟨ cong (sub T₁) (ren-∘ _ _ g₂) ⟩
        sub T₁ (ren (castʳ p'') (ren (ι₂ (m₁ + suc m) n₂ m₂) g₂))
          ≡⟨ cong (λ z → sub T₁ (ren (castʳ p'') z)) (sym (σ-ins-₂ (m₁ + suc m) m₂ g₂)) ⟩
        sub T₁ (ren (castʳ p'') (T₂ ((m₁ + suc m) ↑ʳ zero)))
          ≡⟨ cong (λ z → sub T₁ (ren (castʳ p'') (T₂ z))) (sym (castʳ-≡ p' _ _ (trans (toℕ-blk₃ m₁ _ _) (trans (cong (λ z → m₁ + suc z) (toℕ-hole m m₂)) (trans (arith₈ m₁ m) (sym (toℕ-hole _ _))))))) ⟩
        ΣR (m₁ ↑ʳ suc (m ↑ʳ zero)) ∎
      blockC : ∀ j → ΣL (m₁ ↑ʳ suc (m ↑ʳ suc j)) ≡ ΣR (m₁ ↑ʳ suc (m ↑ʳ suc j))
      blockC j = begin
        ΣL (m₁ ↑ʳ suc (m ↑ʳ suc j))
          ≡⟨ ΣL-var _ (σ-ins-₃ m₁ (m + suc m₂) g₁ (m ↑ʳ suc j)) ⟩
        ren (castʳ q) (S₂ (castʳ p (ι₃ m₁ n₁ (m + suc m₂) (m ↑ʳ suc j))))
          ≡⟨ cong (λ z → ren (castʳ q) (S₂ z)) (castʳ-≡ p _ ((m₁ + (n₁ + m)) ↑ʳ suc j)
               (trans (toℕ-ι₃ m₁ n₁ _ _) (trans (cong (λ z → m₁ + (n₁ + z)) (toℕ-blk₃ m m₂ j)) (trans (arith₉ m₁ n₁ m (toℕ j)) (sym (toℕ-blk₃ _ m₂ j)))))) ⟩
        ren (castʳ q) (S₂ ((m₁ + (n₁ + m)) ↑ʳ suc j))
          ≡⟨ cong (ren (castʳ q)) (σ-ins-₃ (m₁ + (n₁ + m)) m₂ g₂ j) ⟩
        var (castʳ q (ι₃ (m₁ + (n₁ + m)) n₂ m₂ j))
          ≡⟨ var-≡ (trans (toℕ-castʳ q _) (trans (toℕ-ι₃ (m₁ + (n₁ + m)) n₂ m₂ j) (trans (arith₁₀ m₁ n₁ m n₂ (toℕ j)) (sym (trans (toℕ-ι₃ m₁ n₁ _ _) (cong (λ z → m₁ + (n₁ + z)) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ʳ n₂ j))))))))) ⟩
        var (ι₃ m₁ n₁ (m + (n₂ + m₂)) (m ↑ʳ (n₂ ↑ʳ j)))
          ≡⟨ sym (σ-ins-₃ m₁ (m + (n₂ + m₂)) g₁ (m ↑ʳ (n₂ ↑ʳ j))) ⟩
        T₁ (m₁ ↑ʳ suc (m ↑ʳ (n₂ ↑ʳ j)))
          ≡⟨ cong T₁ (sym (castʳ-≡ p'' _ _ (trans (toℕ-ι₃ (m₁ + suc m) n₂ m₂ j) (trans (arith₁₁ m₁ m n₂ (toℕ j)) (sym (trans (toℕ-blk₃ m₁ _ _) (cong (λ z → m₁ + suc z) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ʳ n₂ j)))))))))) ⟩
        T₁ (castʳ p'' (ι₃ (m₁ + suc m) n₂ m₂ j))
          ≡⟨ sym (ΣR-var _ (trans (cong T₂ (castʳ-≡ p' _ ((m₁ + suc m) ↑ʳ suc j) (trans (toℕ-blk₃ m₁ _ _) (trans (cong (λ z → m₁ + suc z) (toℕ-blk₃ m m₂ j)) (trans (arith₁₂ m₁ m (toℕ j)) (sym (toℕ-blk₃ _ m₂ j)))))))
                            (σ-ins-₃ (m₁ + suc m) m₂ g₂ j))) ⟩
        ΣR (m₁ ↑ʳ suc (m ↑ʳ suc j)) ∎

------------------------------------------------------------------------
-- Def. 3.3: the symmetry laws for values.  Both sides fuse to a single
-- substitution of f; the swap σ₁,₁ exchanges the hole with the
-- following variable, and on the other side σ₁,ₙ / σₙ,₁ moves the
-- n-block of g past that variable.
------------------------------------------------------------------------

-- the three block sums used in the symmetry laws, on block elements
W₁₁ : ∀ m₁ m₂ → Ren (m₁ + suc (suc m₂)) (m₁ + suc (suc m₂))
W₁₁ m₁ m₂ = idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}

W₁₁-A : ∀ m₁ m₂ (j : Fin m₁) → toℕ (W₁₁ m₁ m₂ (j ↑ˡ suc (suc m₂))) ≡ toℕ j
W₁₁-A m₁ m₂ j = trans (cong toℕ (+ʳ-inj₁ idʳ (σʳ 1 1 +ʳ idʳ) j)) (toℕ-↑ˡ j _)

W₁₁-h₁ : ∀ m₁ m₂ → toℕ (W₁₁ m₁ m₂ (m₁ ↑ʳ zero)) ≡ m₁ + 1
W₁₁-h₁ m₁ m₂ = trans (cong toℕ (+ʳ-inj₂ idʳ (σʳ 1 1 +ʳ idʳ) zero))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (cong toℕ (+ʳ-inj₁ (σʳ 1 1) (idʳ {m₂}) zero)) (trans (toℕ-↑ˡ (σʳ 1 1 zero) m₂) (cong toℕ (σʳ-inl 1 1 zero))))))

W₁₁-h₂ : ∀ m₁ m₂ → toℕ (W₁₁ m₁ m₂ (m₁ ↑ʳ suc zero)) ≡ m₁ + 0
W₁₁-h₂ m₁ m₂ = trans (cong toℕ (+ʳ-inj₂ idʳ (σʳ 1 1 +ʳ idʳ) (suc zero)))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (cong toℕ (+ʳ-inj₁ (σʳ 1 1) (idʳ {m₂}) (suc zero))) (trans (toℕ-↑ˡ (σʳ 1 1 (suc zero)) m₂) (cong toℕ (σʳ-inr 1 1 zero))))))

W₁₁-C : ∀ m₁ m₂ (j : Fin m₂) → toℕ (W₁₁ m₁ m₂ (m₁ ↑ʳ suc (suc j))) ≡ m₁ + suc (suc (toℕ j))
W₁₁-C m₁ m₂ j = trans (cong toℕ (+ʳ-inj₂ idʳ (σʳ 1 1 +ʳ idʳ) (suc (suc j))))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (cong toℕ (+ʳ-inj₂ (σʳ 1 1) idʳ j)) (toℕ-↑ʳ 2 j))))

-- (id + σ₁,ₙ + id) on the four kinds of positions of m₁ + ((1 + n) + m₂)
S₁ₙ : ∀ m₁ n m₂ → Ren (m₁ + ((1 + n) + m₂)) (m₁ + ((n + 1) + m₂))
S₁ₙ m₁ n m₂ = idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂}

S₁ₙ-A : ∀ m₁ n m₂ (j : Fin m₁) → toℕ (S₁ₙ m₁ n m₂ (j ↑ˡ _)) ≡ toℕ j
S₁ₙ-A m₁ n m₂ j = trans (cong toℕ (+ʳ-inj₁ idʳ (σʳ 1 n +ʳ idʳ) j)) (toℕ-↑ˡ j _)

S₁ₙ-h : ∀ m₁ n m₂ → toℕ (S₁ₙ m₁ n m₂ (m₁ ↑ʳ (zero ↑ˡ m₂))) ≡ m₁ + (n + 0)
S₁ₙ-h m₁ n m₂ = trans (cong toℕ (+ʳ-inj₂ idʳ (σʳ 1 n +ʳ idʳ) (zero ↑ˡ m₂)))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (cong toℕ (+ʳ-inj₁ (σʳ 1 n) (idʳ {m₂}) zero)) (trans (toℕ-↑ˡ _ m₂) (trans (cong toℕ (σʳ-inl 1 n zero)) (toℕ-↑ʳ n zero))))))

S₁ₙ-B : ∀ m₁ n m₂ (x : Fin n) → toℕ (S₁ₙ m₁ n m₂ (m₁ ↑ʳ ((1 ↑ʳ x) ↑ˡ m₂))) ≡ m₁ + toℕ x
S₁ₙ-B m₁ n m₂ x = trans (cong toℕ (+ʳ-inj₂ idʳ (σʳ 1 n +ʳ idʳ) ((1 ↑ʳ x) ↑ˡ m₂)))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (cong toℕ (+ʳ-inj₁ (σʳ 1 n) (idʳ {m₂}) (1 ↑ʳ x))) (trans (toℕ-↑ˡ _ m₂) (trans (cong toℕ (σʳ-inr 1 n x)) (toℕ-↑ˡ x 1))))))

S₁ₙ-C : ∀ m₁ n m₂ (j : Fin m₂) → toℕ (S₁ₙ m₁ n m₂ (m₁ ↑ʳ ((1 + n) ↑ʳ j))) ≡ m₁ + ((n + 1) + toℕ j)
S₁ₙ-C m₁ n m₂ j = trans (cong toℕ (+ʳ-inj₂ idʳ (σʳ 1 n +ʳ idʳ) ((1 + n) ↑ʳ j)))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (cong toℕ (+ʳ-inj₂ (σʳ 1 n) idʳ j)) (toℕ-↑ʳ (n + 1) j))))

-- (id + σₙ,₁ + id) on the positions of m₁ + ((n + 1) + m₂)
Sₙ₁ : ∀ m₁ n m₂ → Ren (m₁ + ((n + 1) + m₂)) (m₁ + ((1 + n) + m₂))
Sₙ₁ m₁ n m₂ = idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}

Sₙ₁-A : ∀ m₁ n m₂ (j : Fin m₁) → toℕ (Sₙ₁ m₁ n m₂ (j ↑ˡ _)) ≡ toℕ j
Sₙ₁-A m₁ n m₂ j = trans (cong toℕ (+ʳ-inj₁ idʳ (σʳ n 1 +ʳ idʳ) j)) (toℕ-↑ˡ j _)

Sₙ₁-B : ∀ m₁ n m₂ (x : Fin n) → toℕ (Sₙ₁ m₁ n m₂ (m₁ ↑ʳ ((x ↑ˡ 1) ↑ˡ m₂))) ≡ m₁ + (1 + toℕ x)
Sₙ₁-B m₁ n m₂ x = trans (cong toℕ (+ʳ-inj₂ idʳ (σʳ n 1 +ʳ idʳ) ((x ↑ˡ 1) ↑ˡ m₂)))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (cong toℕ (+ʳ-inj₁ (σʳ n 1) (idʳ {m₂}) (x ↑ˡ 1))) (trans (toℕ-↑ˡ _ m₂) (trans (cong toℕ (σʳ-inl n 1 x)) (toℕ-↑ʳ 1 x))))))

Sₙ₁-h : ∀ m₁ n m₂ → toℕ (Sₙ₁ m₁ n m₂ (m₁ ↑ʳ ((n ↑ʳ zero) ↑ˡ m₂))) ≡ m₁ + 0
Sₙ₁-h m₁ n m₂ = trans (cong toℕ (+ʳ-inj₂ idʳ (σʳ n 1 +ʳ idʳ) ((n ↑ʳ zero) ↑ˡ m₂)))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (cong toℕ (+ʳ-inj₁ (σʳ n 1) (idʳ {m₂}) (n ↑ʳ zero))) (trans (toℕ-↑ˡ _ m₂) (trans (cong toℕ (σʳ-inr n 1 zero)) (toℕ-↑ˡ (zero {n}) n))))))

Sₙ₁-C : ∀ m₁ n m₂ (j : Fin m₂) → toℕ (Sₙ₁ m₁ n m₂ (m₁ ↑ʳ ((n + 1) ↑ʳ j))) ≡ m₁ + ((1 + n) + toℕ j)
Sₙ₁-C m₁ n m₂ j = trans (cong toℕ (+ʳ-inj₂ idʳ (σʳ n 1 +ʳ idʳ) ((n + 1) ↑ʳ j)))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (cong toℕ (+ʳ-inj₂ (σʳ n 1) idʳ j)) (toℕ-↑ʳ (1 + n) j))))

-- the value of a conjugated renaming cast ∘ S ∘ cast at a position,
-- through toℕ: pick the block form of the inner cast's value
conj-toℕ : ∀ {a b c d} (q : a ≡ b) (S : Ren b c) (q' : c ≡ d) (x : Fin a) (y : Fin b)
  → toℕ x ≡ toℕ y → toℕ ((castʳ q' ∘ʳ S ∘ʳ castʳ q) x) ≡ toℕ (S y)
conj-toℕ q S q' x y e = trans (toℕ-castʳ q' _) (cong (toℕ ∘ S) (castʳ-≡ q x y e))

σ-natˡᵛ : ∀ {m₁ m₂ n} (f : Val (m₁ + suc (suc m₂))) (g : Val n)
  (p  : m₁ + suc (suc m₂) ≡ (m₁ + 1) + suc m₂)
  (q  : (m₁ + 1) + (n + m₂) ≡ m₁ + ((1 + n) + m₂))
  (q' : m₁ + ((n + 1) + m₂) ≡ m₁ + (n + suc m₂))
  → subᵛ m₁ (suc m₂) (ren (W₁₁ m₁ m₂) f) g
    ≈ ren (castʳ q' ∘ʳ S₁ₙ m₁ n m₂ ∘ʳ castʳ q) (subᵛ (m₁ + 1) m₂ (ren (castʳ p) f) g)
σ-natˡᵛ {m₁} {m₂} {n} f g p q q' = ≈-≡ (begin
  sub S (ren W f)
    ≡⟨ sub-ren W S f ⟩
  sub (S ∘ W) f
    ≡⟨ sub-cong pointwise f ⟩
  sub (λ i → ren R (T (castʳ p i))) f
    ≡⟨ sym (ren-sub _ R f) ⟩
  ren R (sub (T ∘ castʳ p) f)
    ≡⟨ cong (ren R) (sym (sub-ren (castʳ p) T f)) ⟩
  ren R (sub T (ren (castʳ p) f)) ∎)
  where
    open ≡-Reasoning
    W = W₁₁ m₁ m₂
    S = σ-ins m₁ (suc m₂) g
    T = σ-ins (m₁ + 1) m₂ g
    R = castʳ q' ∘ʳ S₁ₙ m₁ n m₂ ∘ʳ castʳ q
    -- a variable of the left side, given the block of W i
    var-case : ∀ i {y z} → W i ≡ y → S y ≡ var z → (S ∘ W) i ≡ var z
    var-case i e₁ e₂ = trans (cong S e₁) e₂
    pointwise : (S ∘ W) ≗ (λ i → ren R (T (castʳ p i)))
    pointwise = Fin-ins-ext m₁ (suc m₂) blockA hole₁ (λ { zero → hole₂ ; (suc j) → blockC j })
      where
      blockA : ∀ j → (S ∘ W) (j ↑ˡ _) ≡ ren R (T (castʳ p (j ↑ˡ _)))
      blockA j = begin
        S (W (j ↑ˡ _))
          ≡⟨ cong S (toℕ-injective (trans (W₁₁-A m₁ m₂ j) (sym (toℕ-↑ˡ j _)))) ⟩
        S (j ↑ˡ _)
          ≡⟨ σ-ins-₁ m₁ (suc m₂) g j ⟩
        var (ι₁ m₁ n (suc m₂) j)
          ≡⟨ var-≡ (trans (toℕ-ι₁ m₁ n _ j) (sym (trans (conj-toℕ q (S₁ₙ m₁ n m₂) q' _ (j ↑ˡ ((1 + n) + m₂)) (trans (toℕ-ι₁ (m₁ + 1) n m₂ _) (trans (toℕ-↑ˡ j 1) (sym (toℕ-↑ˡ j _))))) (S₁ₙ-A m₁ n m₂ j)))) ⟩
        var (R (ι₁ (m₁ + 1) n m₂ (j ↑ˡ 1)))
          ≡⟨ cong (ren R) (sym (σ-ins-₁ (m₁ + 1) m₂ g (j ↑ˡ 1))) ⟩
        ren R (T ((j ↑ˡ 1) ↑ˡ suc m₂))
          ≡⟨ cong (ren R ∘ T) (sym (castʳ-≡ p _ _ (trans (toℕ-↑ˡ j _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j 1)))))) ⟩
        ren R (T (castʳ p (j ↑ˡ _))) ∎
      hole₁ : (S ∘ W) (m₁ ↑ʳ zero) ≡ ren R (T (castʳ p (m₁ ↑ʳ zero)))
      hole₁ = begin
        S (W (m₁ ↑ʳ zero))
          ≡⟨ cong S (toℕ-injective (trans (W₁₁-h₁ m₁ m₂) (sym (toℕ-blk₃ m₁ _ zero)))) ⟩
        S (m₁ ↑ʳ suc zero)
          ≡⟨ σ-ins-₃ m₁ (suc m₂) g zero ⟩
        var (ι₃ m₁ n (suc m₂) zero)
          ≡⟨ var-≡ (trans (toℕ-ι₃ m₁ n _ zero) (sym (trans (conj-toℕ q (S₁ₙ m₁ n m₂) q' _ (m₁ ↑ʳ (zero ↑ˡ m₂)) (trans (toℕ-ι₁ (m₁ + 1) n m₂ _) (trans (toℕ-hole m₁ 0) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ˡ (zero {n}) m₂))))))) (S₁ₙ-h m₁ n m₂)))) ⟩
        var (R (ι₁ (m₁ + 1) n m₂ (m₁ ↑ʳ zero)))
          ≡⟨ cong (ren R) (sym (σ-ins-₁ (m₁ + 1) m₂ g (m₁ ↑ʳ zero))) ⟩
        ren R (T ((m₁ ↑ʳ zero) ↑ˡ suc m₂))
          ≡⟨ cong (ren R ∘ T) (sym (castʳ-≡ p _ _ (trans (toℕ-hole m₁ _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-hole m₁ 0)))))) ⟩
        ren R (T (castʳ p (m₁ ↑ʳ zero))) ∎
      hole₂ : (S ∘ W) (m₁ ↑ʳ suc zero) ≡ ren R (T (castʳ p (m₁ ↑ʳ suc zero)))
      hole₂ = begin
        S (W (m₁ ↑ʳ suc zero))
          ≡⟨ cong S (toℕ-injective (trans (W₁₁-h₂ m₁ m₂) (sym (toℕ-hole m₁ _)))) ⟩
        S (m₁ ↑ʳ zero)
          ≡⟨ σ-ins-₂ m₁ (suc m₂) g ⟩
        ren (ι₂ m₁ n (suc m₂)) g
          ≡⟨ ren-≡ (λ x → trans (toℕ-ι₂ m₁ n _ x) (sym (trans (conj-toℕ q (S₁ₙ m₁ n m₂) q' _ (m₁ ↑ʳ ((1 ↑ʳ x) ↑ˡ m₂)) (trans (toℕ-ι₂ (m₁ + 1) n m₂ x) (trans (+-assoc m₁ 1 (toℕ x)) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (toℕ-↑ˡ _ m₂) (toℕ-↑ʳ 1 x)))))))) (S₁ₙ-B m₁ n m₂ x)))) g ⟩
        ren (R ∘ʳ ι₂ (m₁ + 1) n m₂) g
          ≡⟨ ren-∘ _ _ g ⟩
        ren R (ren (ι₂ (m₁ + 1) n m₂) g)
          ≡⟨ cong (ren R) (sym (σ-ins-₂ (m₁ + 1) m₂ g)) ⟩
        ren R (T ((m₁ + 1) ↑ʳ zero))
          ≡⟨ cong (ren R ∘ T) (sym (castʳ-≡ p _ _ (trans (toℕ-blk₃ m₁ _ zero) (trans (sym (+-identityʳ (m₁ + 1))) (sym (toℕ-hole (m₁ + 1) m₂)))))) ⟩
        ren R (T (castʳ p (m₁ ↑ʳ suc zero))) ∎
      blockC : ∀ j → (S ∘ W) (m₁ ↑ʳ suc (suc j)) ≡ ren R (T (castʳ p (m₁ ↑ʳ suc (suc j))))
      blockC j = begin
        S (W (m₁ ↑ʳ suc (suc j)))
          ≡⟨ cong S (toℕ-injective (trans (W₁₁-C m₁ m₂ j) (sym (toℕ-blk₃ m₁ _ (suc j))))) ⟩
        S (m₁ ↑ʳ suc (suc j))
          ≡⟨ σ-ins-₃ m₁ (suc m₂) g (suc j) ⟩
        var (ι₃ m₁ n (suc m₂) (suc j))
          ≡⟨ var-≡ (trans (toℕ-ι₃ m₁ n _ (suc j)) (sym (trans (conj-toℕ q (S₁ₙ m₁ n m₂) q' _ (m₁ ↑ʳ ((1 + n) ↑ʳ j)) (trans (toℕ-ι₃ (m₁ + 1) n m₂ j) (trans (+-assoc m₁ 1 _) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ (1 + n) j))))))) (trans (S₁ₙ-C m₁ n m₂ j) (arith₁₃ m₁ n (toℕ j)))))) ⟩
        var (R (ι₃ (m₁ + 1) n m₂ j))
          ≡⟨ cong (ren R) (sym (σ-ins-₃ (m₁ + 1) m₂ g j)) ⟩
        ren R (T ((m₁ + 1) ↑ʳ suc j))
          ≡⟨ cong (ren R ∘ T) (sym (castʳ-≡ p _ _ (trans (toℕ-blk₃ m₁ _ (suc j)) (sym (trans (toℕ-blk₃ (m₁ + 1) m₂ j) (+-assoc m₁ 1 (suc (toℕ j)))))))) ⟩
        ren R (T (castʳ p (m₁ ↑ʳ suc (suc j)))) ∎

σ-natʳᵛ : ∀ {m₁ m₂ n} (f : Val (m₁ + suc (suc m₂))) (g : Val n)
  (p  : m₁ + suc (suc m₂) ≡ (m₁ + 1) + suc m₂)
  (q  : m₁ + (n + suc m₂) ≡ m₁ + ((n + 1) + m₂))
  (q' : m₁ + ((1 + n) + m₂) ≡ (m₁ + 1) + (n + m₂))
  → subᵛ (m₁ + 1) m₂ (ren (castʳ p) (ren (W₁₁ m₁ m₂) f)) g
    ≈ ren (castʳ q' ∘ʳ Sₙ₁ m₁ n m₂ ∘ʳ castʳ q) (subᵛ m₁ (suc m₂) f g)
σ-natʳᵛ {m₁} {m₂} {n} f g p q q' = ≈-≡ (begin
  sub T (ren (castʳ p) (ren W f))
    ≡⟨ cong (sub T) (sym (ren-∘ _ _ f)) ⟩
  sub T (ren (castʳ p ∘ʳ W) f)
    ≡⟨ sub-ren _ T f ⟩
  sub (T ∘ (castʳ p ∘ʳ W)) f
    ≡⟨ sub-cong pointwise f ⟩
  sub (λ i → ren R (S i)) f
    ≡⟨ sym (ren-sub S R f) ⟩
  ren R (sub S f) ∎)
  where
    open ≡-Reasoning
    W = W₁₁ m₁ m₂
    S = σ-ins m₁ (suc m₂) g
    T = σ-ins (m₁ + 1) m₂ g
    R = castʳ q' ∘ʳ Sₙ₁ m₁ n m₂ ∘ʳ castʳ q
    pointwise : (T ∘ (castʳ p ∘ʳ W)) ≗ (λ i → ren R (S i))
    pointwise = Fin-ins-ext m₁ (suc m₂) blockA hole₁ (λ { zero → hole₂ ; (suc j) → blockC j })
      where
      blockA : ∀ j → T (castʳ p (W (j ↑ˡ _))) ≡ ren R (S (j ↑ˡ _))
      blockA j = begin
        T (castʳ p (W (j ↑ˡ _)))
          ≡⟨ cong T (castʳ-≡ p _ ((j ↑ˡ 1) ↑ˡ suc m₂) (trans (W₁₁-A m₁ m₂ j) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j 1))))) ⟩
        T ((j ↑ˡ 1) ↑ˡ suc m₂)
          ≡⟨ σ-ins-₁ (m₁ + 1) m₂ g (j ↑ˡ 1) ⟩
        var (ι₁ (m₁ + 1) n m₂ (j ↑ˡ 1))
          ≡⟨ var-≡ (trans (toℕ-ι₁ (m₁ + 1) n m₂ _) (trans (toℕ-↑ˡ j 1) (sym (trans (conj-toℕ q (Sₙ₁ m₁ n m₂) q' _ (j ↑ˡ ((n + 1) + m₂)) (trans (toℕ-ι₁ m₁ n _ j) (sym (toℕ-↑ˡ j _)))) (Sₙ₁-A m₁ n m₂ j))))) ⟩
        var (R (ι₁ m₁ n (suc m₂) j))
          ≡⟨ cong (ren R) (sym (σ-ins-₁ m₁ (suc m₂) g j)) ⟩
        ren R (S (j ↑ˡ _)) ∎
      hole₁ : T (castʳ p (W (m₁ ↑ʳ zero))) ≡ ren R (S (m₁ ↑ʳ zero))
      hole₁ = begin
        T (castʳ p (W (m₁ ↑ʳ zero)))
          ≡⟨ cong T (castʳ-≡ p _ ((m₁ + 1) ↑ʳ zero) (trans (W₁₁-h₁ m₁ m₂) (sym (trans (toℕ-hole (m₁ + 1) m₂) (+-identityʳ (m₁ + 1)))))) ⟩
        T ((m₁ + 1) ↑ʳ zero)
          ≡⟨ σ-ins-₂ (m₁ + 1) m₂ g ⟩
        ren (ι₂ (m₁ + 1) n m₂) g
          ≡⟨ ren-≡ (λ x → trans (toℕ-ι₂ (m₁ + 1) n m₂ x) (trans (+-assoc m₁ 1 (toℕ x)) (sym (trans (conj-toℕ q (Sₙ₁ m₁ n m₂) q' _ (m₁ ↑ʳ ((x ↑ˡ 1) ↑ˡ m₂)) (trans (toℕ-ι₂ m₁ n _ x) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (toℕ-↑ˡ _ m₂) (toℕ-↑ˡ x 1))))))) (Sₙ₁-B m₁ n m₂ x))))) g ⟩
        ren (R ∘ʳ ι₂ m₁ n (suc m₂)) g
          ≡⟨ ren-∘ _ _ g ⟩
        ren R (ren (ι₂ m₁ n (suc m₂)) g)
          ≡⟨ cong (ren R) (sym (σ-ins-₂ m₁ (suc m₂) g)) ⟩
        ren R (S (m₁ ↑ʳ zero)) ∎
      hole₂ : T (castʳ p (W (m₁ ↑ʳ suc zero))) ≡ ren R (S (m₁ ↑ʳ suc zero))
      hole₂ = begin
        T (castʳ p (W (m₁ ↑ʳ suc zero)))
          ≡⟨ cong T (castʳ-≡ p _ ((m₁ ↑ʳ zero) ↑ˡ suc m₂) (trans (W₁₁-h₂ m₁ m₂) (sym (trans (toℕ-↑ˡ _ _) (toℕ-hole m₁ 0))))) ⟩
        T ((m₁ ↑ʳ zero) ↑ˡ suc m₂)
          ≡⟨ σ-ins-₁ (m₁ + 1) m₂ g (m₁ ↑ʳ zero) ⟩
        var (ι₁ (m₁ + 1) n m₂ (m₁ ↑ʳ zero))
          ≡⟨ var-≡ (trans (toℕ-ι₁ (m₁ + 1) n m₂ _) (trans (toℕ-hole m₁ 0) (sym (trans (conj-toℕ q (Sₙ₁ m₁ n m₂) q' _ (m₁ ↑ʳ ((n ↑ʳ zero) ↑ˡ m₂)) (trans (toℕ-ι₃ m₁ n _ zero) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (toℕ-↑ˡ _ m₂) (toℕ-hole n 0))))))) (Sₙ₁-h m₁ n m₂))))) ⟩
        var (R (ι₃ m₁ n (suc m₂) zero))
          ≡⟨ cong (ren R) (sym (σ-ins-₃ m₁ (suc m₂) g zero)) ⟩
        ren R (S (m₁ ↑ʳ suc zero)) ∎
      blockC : ∀ j → T (castʳ p (W (m₁ ↑ʳ suc (suc j)))) ≡ ren R (S (m₁ ↑ʳ suc (suc j)))
      blockC j = begin
        T (castʳ p (W (m₁ ↑ʳ suc (suc j))))
          ≡⟨ cong T (castʳ-≡ p _ ((m₁ + 1) ↑ʳ suc j) (trans (W₁₁-C m₁ m₂ j) (sym (trans (toℕ-blk₃ (m₁ + 1) m₂ j) (+-assoc m₁ 1 _))))) ⟩
        T ((m₁ + 1) ↑ʳ suc j)
          ≡⟨ σ-ins-₃ (m₁ + 1) m₂ g j ⟩
        var (ι₃ (m₁ + 1) n m₂ j)
          ≡⟨ var-≡ (trans (toℕ-ι₃ (m₁ + 1) n m₂ j) (trans (+-assoc m₁ 1 _) (sym (trans (conj-toℕ q (Sₙ₁ m₁ n m₂) q' _ (m₁ ↑ʳ ((n + 1) ↑ʳ j)) (trans (toℕ-ι₃ m₁ n _ (suc j)) (trans (arith₁₄ m₁ n (toℕ j)) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ (n + 1) j))))))) (Sₙ₁-C m₁ n m₂ j))))) ⟩
        var (R (ι₃ m₁ n (suc m₂) (suc j)))
          ≡⟨ cong (ren R) (sym (σ-ins-₃ m₁ (suc m₂) g (suc j))) ⟩
        ren R (S (m₁ ↑ʳ suc (suc j))) ∎

------------------------------------------------------------------------
-- Def. 3.7 (i),(ii): discarding and copying are natural in VAL.
------------------------------------------------------------------------

!-natᵛ : ∀ {m₁ m₂ n} (f : Val (m₁ + m₂)) (g : Val n)
  → subᵛ m₁ m₂ (ren (idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂}) f) g ≈ ren (idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂}) f
!-natᵛ {m₁} {m₂} {n} f g = ≈-≡ (begin
  sub S (ren D₁ f)
    ≡⟨ sub-ren D₁ S f ⟩
  sub (S ∘ D₁) f
    ≡⟨ sub-cong pointwise f ⟩
  sub ⌜ Dₙ ⌝ f
    ≡⟨ sub-⌜⌝ Dₙ f ⟩
  ren Dₙ f ∎)
  where
    open ≡-Reasoning
    S = σ-ins m₁ m₂ g
    D₁ = idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂}
    Dₙ = idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂}
    pointwise : (S ∘ D₁) ≗ ⌜ Dₙ ⌝
    pointwise = Fin+-ext
      (λ j → begin
        S (D₁ (j ↑ˡ m₂))
          ≡⟨ cong S (+ʳ-inj₁ idʳ (!ʳ 1 +ʳ idʳ) j) ⟩
        S (j ↑ˡ suc m₂)
          ≡⟨ σ-ins-₁ m₁ m₂ g j ⟩
        var (ι₁ m₁ n m₂ j)
          ≡⟨ var-≡ (trans (toℕ-ι₁ m₁ n m₂ j) (sym (trans (cong toℕ (+ʳ-inj₁ idʳ (!ʳ n +ʳ idʳ) j)) (toℕ-↑ˡ j _)))) ⟩
        var (Dₙ (j ↑ˡ m₂)) ∎)
      (λ j → begin
        S (D₁ (m₁ ↑ʳ j))
          ≡⟨ cong S (trans (+ʳ-inj₂ (idʳ {m₁}) (!ʳ 1 +ʳ idʳ) j) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ (!ʳ 1) (idʳ {m₂}) j))) ⟩
        S (m₁ ↑ʳ suc j)
          ≡⟨ σ-ins-₃ m₁ m₂ g j ⟩
        var (ι₃ m₁ n m₂ j)
          ≡⟨ var-≡ (trans (toℕ-ι₃ m₁ n m₂ j) (sym (trans (cong toℕ (trans (+ʳ-inj₂ (idʳ {m₁}) (!ʳ n +ʳ idʳ) j) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ (!ʳ n) (idʳ {m₂}) j)))) (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ n j)))))) ⟩
        var (Dₙ (m₁ ↑ʳ j)) ∎)

-- the contraction id + Δₙ + id on block elements
Cₙ : ∀ m₁ n m₂ → Ren (m₁ + ((n + n) + m₂)) (m₁ + (n + m₂))
Cₙ m₁ n m₂ = idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}

Cₙ-A : ∀ m₁ n m₂ (j : Fin m₁) → toℕ (Cₙ m₁ n m₂ (j ↑ˡ _)) ≡ toℕ j
Cₙ-A m₁ n m₂ j = trans (cong toℕ (+ʳ-inj₁ idʳ (Δʳ n +ʳ idʳ) j)) (toℕ-↑ˡ j _)

Cₙ-B₁ : ∀ m₁ n m₂ (x : Fin n) → toℕ (Cₙ m₁ n m₂ (m₁ ↑ʳ ((x ↑ˡ n) ↑ˡ m₂))) ≡ m₁ + toℕ x
Cₙ-B₁ m₁ n m₂ x = trans (cong toℕ (trans (+ʳ-inj₂ idʳ (Δʳ n +ʳ idʳ) _) (cong (m₁ ↑ʳ_) (trans (+ʳ-inj₁ (Δʳ n) (idʳ {m₂}) (x ↑ˡ n)) (cong (_↑ˡ m₂) ([,]ʳ-inl idʳ idʳ x))))))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ˡ x m₂)))

Cₙ-B₂ : ∀ m₁ n m₂ (x : Fin n) → toℕ (Cₙ m₁ n m₂ (m₁ ↑ʳ ((n ↑ʳ x) ↑ˡ m₂))) ≡ m₁ + toℕ x
Cₙ-B₂ m₁ n m₂ x = trans (cong toℕ (trans (+ʳ-inj₂ idʳ (Δʳ n +ʳ idʳ) _) (cong (m₁ ↑ʳ_) (trans (+ʳ-inj₁ (Δʳ n) (idʳ {m₂}) (n ↑ʳ x)) (cong (_↑ˡ m₂) ([,]ʳ-inr idʳ idʳ x))))))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ˡ x m₂)))

Cₙ-C : ∀ m₁ n m₂ (j : Fin m₂) → toℕ (Cₙ m₁ n m₂ (m₁ ↑ʳ ((n + n) ↑ʳ j))) ≡ m₁ + (n + toℕ j)
Cₙ-C m₁ n m₂ j = trans (cong toℕ (trans (+ʳ-inj₂ idʳ (Δʳ n +ʳ idʳ) _) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ (Δʳ n) (idʳ {m₂}) j))))
  (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ n j)))

Δ-natᵛ : ∀ {m₁ m₂ n} (f : Val (m₁ + suc (suc m₂))) (g : Val n)
  (p : m₁ + (n + suc m₂) ≡ (m₁ + n) + suc m₂) (q : (m₁ + n) + (n + m₂) ≡ m₁ + ((n + n) + m₂))
  → subᵛ m₁ m₂ (ren (idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂}) f) g
    ≈ ren (Cₙ m₁ n m₂ ∘ʳ castʳ q) (subᵛ (m₁ + n) m₂ (subst Val p (subᵛ m₁ (suc m₂) f g)) g)
Δ-natᵛ {m₁} {m₂} {n} f g p q = ≈-≡ (begin
  sub S₀ (ren D f)
    ≡⟨ sub-ren D S₀ f ⟩
  sub (S₀ ∘ D) f
    ≡⟨ sub-cong pointwise f ⟩
  sub ΣR f
    ≡⟨ sym (sub-sub _ _ f) ⟩
  sub (λ i → ren R (S₂ i)) (sub (λ i → ren (castʳ p) (S₁ i)) f)
    ≡⟨ cong (sub _) (sym (subst-sub p S₁ f)) ⟩
  sub (λ i → ren R (S₂ i)) (subst Val p (sub S₁ f))
    ≡⟨ sym (ren-sub S₂ R (subst Val p (sub S₁ f))) ⟩
  ren R (sub S₂ (subst Val p (sub S₁ f))) ∎)
  where
    open ≡-Reasoning
    D = idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂}
    S₀ = σ-ins m₁ m₂ g
    S₁ = σ-ins m₁ (suc m₂) g
    S₂ = σ-ins (m₁ + n) m₂ g
    R = Cₙ m₁ n m₂ ∘ʳ castʳ q
    ΣR : Subst (m₁ + suc (suc m₂)) (m₁ + (n + m₂))
    ΣR i = sub (λ i → ren R (S₂ i)) (ren (castʳ p) (S₁ i))
    -- toℕ of R at a variable of S₂'s target, given the block form of the cast's value
    R-toℕ : (x : Fin ((m₁ + n) + (n + m₂))) (y : Fin (m₁ + ((n + n) + m₂))) → toℕ x ≡ toℕ y → toℕ (R x) ≡ toℕ (Cₙ m₁ n m₂ y)
    R-toℕ x y e = cong (toℕ ∘ Cₙ m₁ n m₂) (castʳ-≡ q x y e)
    -- the two holes are both filled by g renamed into the middle block
    hole-val : ∀ {y : Fin (m₁ + (n + suc m₂))} → toℕ y ≡ m₁ + n → ren (ι₂ m₁ n m₂) g ≡ sub (λ i → ren R (S₂ i)) (ren (castʳ p) (var y))
    hole-val {y} e = begin
      ren (ι₂ m₁ n m₂) g
        ≡⟨ ren-≡ (λ x → trans (toℕ-ι₂ m₁ n m₂ x) (sym (trans (R-toℕ _ (m₁ ↑ʳ ((n ↑ʳ x) ↑ˡ m₂)) (trans (toℕ-ι₂ (m₁ + n) n m₂ x) (trans (+-assoc m₁ n (toℕ x)) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (toℕ-↑ˡ _ m₂) (toℕ-↑ʳ n x)))))))) (Cₙ-B₂ m₁ n m₂ x)))) g ⟩
      ren (R ∘ʳ ι₂ (m₁ + n) n m₂) g
        ≡⟨ ren-∘ _ _ g ⟩
      ren R (ren (ι₂ (m₁ + n) n m₂) g)
        ≡⟨ cong (ren R) (sym (σ-ins-₂ (m₁ + n) m₂ g)) ⟩
      ren R (S₂ ((m₁ + n) ↑ʳ zero))
        ≡⟨ cong (ren R ∘ S₂) (sym (castʳ-≡ p y _ (trans e (trans (sym (+-identityʳ (m₁ + n))) (sym (toℕ-hole (m₁ + n) m₂)))))) ⟩
      ren R (S₂ (castʳ p y)) ∎
    pointwise : (S₀ ∘ D) ≗ ΣR
    pointwise = Fin-ins-ext m₁ (suc m₂) blockA hole₁ (λ { zero → hole₂ ; (suc j) → blockC j })
      where
      blockA : ∀ j → S₀ (D (j ↑ˡ _)) ≡ ΣR (j ↑ˡ _)
      blockA j = begin
        S₀ (D (j ↑ˡ _))
          ≡⟨ cong S₀ (+ʳ-inj₁ idʳ (Δʳ 1 +ʳ idʳ) j) ⟩
        S₀ (j ↑ˡ suc m₂)
          ≡⟨ σ-ins-₁ m₁ m₂ g j ⟩
        var (ι₁ m₁ n m₂ j)
          ≡⟨ var-≡ (trans (toℕ-ι₁ m₁ n m₂ j) (sym (trans (R-toℕ _ (j ↑ˡ ((n + n) + m₂)) (trans (toℕ-ι₁ (m₁ + n) n m₂ _) (trans (toℕ-↑ˡ j n) (sym (toℕ-↑ˡ j _))))) (Cₙ-A m₁ n m₂ j)))) ⟩
        var (R (ι₁ (m₁ + n) n m₂ (j ↑ˡ n)))
          ≡⟨ cong (ren R) (sym (σ-ins-₁ (m₁ + n) m₂ g (j ↑ˡ n))) ⟩
        ren R (S₂ ((j ↑ˡ n) ↑ˡ suc m₂))
          ≡⟨ cong (ren R ∘ S₂) (sym (castʳ-≡ p _ _ (trans (toℕ-ι₁ m₁ n _ j) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j n)))))) ⟩
        ren R (S₂ (castʳ p (ι₁ m₁ n (suc m₂) j)))
          ≡⟨ cong (λ z → sub (λ i → ren R (S₂ i)) (ren (castʳ p) z)) (sym (σ-ins-₁ m₁ (suc m₂) g j)) ⟩
        ΣR (j ↑ˡ _) ∎
      hole₁ : S₀ (D (m₁ ↑ʳ zero)) ≡ ΣR (m₁ ↑ʳ zero)
      hole₁ = begin
        S₀ (D (m₁ ↑ʳ zero))
          ≡⟨ cong S₀ (trans (+ʳ-inj₂ idʳ (Δʳ 1 +ʳ idʳ) zero) (cong (m₁ ↑ʳ_) (trans (+ʳ-inj₁ (Δʳ 1) (idʳ {m₂}) zero) (cong (_↑ˡ m₂) ([,]ʳ-inl idʳ idʳ zero))))) ⟩
        S₀ (m₁ ↑ʳ zero)
          ≡⟨ σ-ins-₂ m₁ m₂ g ⟩
        ren (ι₂ m₁ n m₂) g
          ≡⟨ sub-ren-var' ⟩
        sub (λ i → ren R (S₂ i)) (ren (castʳ p) (ren (ι₂ m₁ n (suc m₂)) g))
          ≡⟨ cong (λ z → sub (λ i → ren R (S₂ i)) (ren (castʳ p) z)) (sym (σ-ins-₂ m₁ (suc m₂) g)) ⟩
        ΣR (m₁ ↑ʳ zero) ∎
        where
          sub-ren-var' : ren (ι₂ m₁ n m₂) g ≡ sub (λ i → ren R (S₂ i)) (ren (castʳ p) (ren (ι₂ m₁ n (suc m₂)) g))
          sub-ren-var' = begin
            ren (ι₂ m₁ n m₂) g
              ≡⟨ sym (sub-ren-var _ _ (ι₂ m₁ n m₂)
                   (λ x → trans (cong (λ z → ren R (S₂ z)) (castʳ-≡ p _ ((m₁ ↑ʳ x) ↑ˡ suc m₂) (trans (toℕ-ι₂ m₁ n _ x) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ʳ m₁ x))))))
                          (trans (cong (ren R) (σ-ins-₁ (m₁ + n) m₂ g (m₁ ↑ʳ x)))
                                 (var-≡ (trans (R-toℕ _ (m₁ ↑ʳ ((x ↑ˡ n) ↑ˡ m₂)) (trans (toℕ-ι₁ (m₁ + n) n m₂ _) (trans (toℕ-↑ʳ m₁ x) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (toℕ-↑ˡ _ m₂) (toℕ-↑ˡ x n)))))))) (trans (Cₙ-B₁ m₁ n m₂ x) (sym (toℕ-ι₂ m₁ n m₂ x)))))))
                   g) ⟩
            sub (λ i → ren R (S₂ i)) (ren (castʳ p ∘ʳ ι₂ m₁ n (suc m₂)) g)
              ≡⟨ cong (sub (λ i → ren R (S₂ i))) (ren-∘ _ _ g) ⟩
            sub (λ i → ren R (S₂ i)) (ren (castʳ p) (ren (ι₂ m₁ n (suc m₂)) g)) ∎
      hole₂ : S₀ (D (m₁ ↑ʳ suc zero)) ≡ ΣR (m₁ ↑ʳ suc zero)
      hole₂ = begin
        S₀ (D (m₁ ↑ʳ suc zero))
          ≡⟨ cong S₀ (trans (+ʳ-inj₂ idʳ (Δʳ 1 +ʳ idʳ) (suc zero)) (cong (m₁ ↑ʳ_) (trans (+ʳ-inj₁ (Δʳ 1) (idʳ {m₂}) (suc zero)) (cong (_↑ˡ m₂) ([,]ʳ-inr idʳ idʳ zero))))) ⟩
        S₀ (m₁ ↑ʳ zero)
          ≡⟨ σ-ins-₂ m₁ m₂ g ⟩
        ren (ι₂ m₁ n m₂) g
          ≡⟨ hole-val (trans (toℕ-ι₃ m₁ n _ zero) (cong (m₁ +_) (+-identityʳ n))) ⟩
        sub (λ i → ren R (S₂ i)) (ren (castʳ p) (var (ι₃ m₁ n (suc m₂) zero)))
          ≡⟨ cong (λ z → sub (λ i → ren R (S₂ i)) (ren (castʳ p) z)) (sym (σ-ins-₃ m₁ (suc m₂) g zero)) ⟩
        ΣR (m₁ ↑ʳ suc zero) ∎
      blockC : ∀ j → S₀ (D (m₁ ↑ʳ suc (suc j))) ≡ ΣR (m₁ ↑ʳ suc (suc j))
      blockC j = begin
        S₀ (D (m₁ ↑ʳ suc (suc j)))
          ≡⟨ cong S₀ (trans (+ʳ-inj₂ idʳ (Δʳ 1 +ʳ idʳ) (suc (suc j))) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ (Δʳ 1) (idʳ {m₂}) j))) ⟩
        S₀ (m₁ ↑ʳ suc j)
          ≡⟨ σ-ins-₃ m₁ m₂ g j ⟩
        var (ι₃ m₁ n m₂ j)
          ≡⟨ var-≡ (trans (toℕ-ι₃ m₁ n m₂ j) (sym (trans (R-toℕ _ (m₁ ↑ʳ ((n + n) ↑ʳ j)) (trans (toℕ-ι₃ (m₁ + n) n m₂ j) (trans (arith₂ m₁ n n (toℕ j)) (trans (cong (m₁ +_) (sym (+-assoc n n (toℕ j)))) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ (n + n) j)))))))) (Cₙ-C m₁ n m₂ j)))) ⟩
        var (R (ι₃ (m₁ + n) n m₂ j))
          ≡⟨ cong (ren R) (sym (σ-ins-₃ (m₁ + n) m₂ g j)) ⟩
        ren R (S₂ ((m₁ + n) ↑ʳ suc j))
          ≡⟨ cong (ren R ∘ S₂) (sym (castʳ-≡ p _ _ (trans (toℕ-ι₃ m₁ n _ (suc j)) (trans (arith₁ m₁ n (toℕ j)) (sym (toℕ-blk₃ (m₁ + n) m₂ j)))))) ⟩
        ren R (S₂ (castʳ p (ι₃ m₁ n (suc m₂) (suc j))))
          ≡⟨ cong (λ z → sub (λ i → ren R (S₂ i)) (ren (castʳ p) z)) (sym (σ-ins-₃ m₁ (suc m₂) g (suc j))) ⟩
        ΣR (m₁ ↑ʳ suc (suc j)) ∎

------------------------------------------------------------------------
-- The computation side.  subᶜ n₁ n₂ M₁ M₂ = let y ⇐ M₂[ι₂] in M₁[ρ],
-- where ρ moves the hole of M₁ to the last position.  The laws are
-- equations between nested lets; (assoc) and (lunit) do the
-- reassociation, everything else is a comparison of renamings.
------------------------------------------------------------------------

toℕ-liftʳ-inl : (r : Ren m n) (j : Fin m) → toℕ (liftʳ r (j ↑ˡ 1)) ≡ toℕ (r j)
toℕ-liftʳ-inl r j = trans (cong toℕ (liftʳ-inl r j)) (toℕ-↑ˡ (r j) 1)

toℕ-liftʳ-last : (r : Ren m n) → toℕ (liftʳ r (last {m})) ≡ n + 0
toℕ-liftʳ-last {n = n} r = trans (cong toℕ (liftʳ-last r)) (toℕ-last n)

-- pointwise ≡ of two renamings out of  n₁ + suc n₂ , through toℕ
Fin-ins-toℕ : ∀ n₁ n₂ {r r' : Ren (n₁ + suc n₂) m}
  → (∀ j → toℕ (r (j ↑ˡ suc n₂)) ≡ toℕ (r' (j ↑ˡ suc n₂))) → toℕ (r (n₁ ↑ʳ zero)) ≡ toℕ (r' (n₁ ↑ʳ zero))
  → (∀ j → toℕ (r (n₁ ↑ʳ suc j)) ≡ toℕ (r' (n₁ ↑ʳ suc j))) → ∀ i → toℕ (r i) ≡ toℕ (r' i)
Fin-ins-toℕ n₁ n₂ h₁ h₂ h₃ = Fin-ins-ext n₁ n₂ h₁ h₂ h₃

-- renaming a let
ren-bnd : (r : Ren m n) (M₂ : Cmp m) (M₁ : Cmp (m + 1)) → ren r (bnd M₂ M₁) ≡ bnd (ren r M₂) (ren (liftʳ r) M₁)
ren-bnd r M₂ M₁ = refl

assocᶜ : ∀ {m₁ m₂ n₁ n₂ n} (f : Cmp (m₁ + suc m₂)) (g : Cmp (n₁ + suc n₂)) (h : Cmp n)
  (p : m₁ + ((n₁ + suc n₂) + m₂) ≡ (m₁ + n₁) + suc (n₂ + m₂))
  (q : (m₁ + n₁) + (n + (n₂ + m₂)) ≡ m₁ + ((n₁ + (n + n₂)) + m₂))
  → subst Cmp q (subᶜ (m₁ + n₁) (n₂ + m₂) (subst Cmp p (subᶜ m₁ m₂ f g)) h)
    ≈ subᶜ m₁ m₂ f (subᶜ n₁ n₂ g h)
assocᶜ {m₁} {m₂} {n₁} {n₂} {n} f g h p q =
  ≈-trans (≈-≡ LHS-form)
  (≈-trans (bnd-cong (≈-≡ (trans (ren-≡ h-eq h) (ren-∘ _ _ h))) (bnd-cong (≈-≡ (trans (ren-≡ g-eq g) (ren-∘ _ _ g))) (≈-≡ (trans (ren-≡ f-eq f) (ren-∘ _ _ f)))))
           (≈-sym (assoc _ _ _)))
  where
    open ≡-Reasoning
    kg = n₁ + suc n₂
    N = m₁ + ((n₁ + (n + n₂)) + m₂)
    ρf = ρ-ins m₁ m₂ kg
    ρg = ρ-ins n₁ n₂ n
    ρ₁ = ρ-ins (m₁ + n₁) (n₂ + m₂) n
    ρ₂ = ρ-ins m₁ m₂ (n₁ + (n + n₂))
    ιg = ι₂ m₁ kg m₂
    ιh = ι₂ (m₁ + n₁) n (n₂ + m₂)
    ιg' = ι₂ m₁ (n₁ + (n + n₂)) m₂
    ιh' = ι₂ n₁ n n₂
    X = liftʳ (castʳ q) ∘ʳ ρ₁ ∘ʳ castʳ p
    -- the left side, with all renamings pushed to the leaves
    LHS-form : subst Cmp q (subᶜ (m₁ + n₁) (n₂ + m₂) (subst Cmp p (subᶜ m₁ m₂ f g)) h)
             ≡ bnd (ren (castʳ q ∘ʳ ιh) h) (bnd (ren (X ∘ʳ ιg) g) (ren (liftʳ X ∘ʳ ρf) f))
    LHS-form = begin
      subst Cmp q (bnd (ren ιh h) (ren ρ₁ (subst Cmp p (bnd (ren ιg g) (ren ρf f)))))
        ≡⟨ subst-ren q _ ⟩
      ren (castʳ q) (bnd (ren ιh h) (ren ρ₁ (subst Cmp p (bnd (ren ιg g) (ren ρf f)))))
        ≡⟨ cong (λ z → ren (castʳ q) (bnd (ren ιh h) (ren ρ₁ z))) (subst-ren p _) ⟩
      bnd (ren (castʳ q) (ren ιh h)) (ren (liftʳ (castʳ q)) (ren ρ₁ (ren (castʳ p) (bnd (ren ιg g) (ren ρf f)))))
        ≡⟨ cong₂ bnd (sym (ren-∘ _ _ h)) (trans (cong (ren (liftʳ (castʳ q))) (sym (ren-∘ _ _ _))) (sym (ren-∘ _ _ _))) ⟩
      bnd (ren (castʳ q ∘ʳ ιh) h) (ren X (bnd (ren ιg g) (ren ρf f)))
        ≡⟨ cong (bnd _) (cong₂ bnd (sym (ren-∘ _ _ g)) (sym (ren-∘ _ _ f))) ⟩
      bnd (ren (castʳ q ∘ʳ ιh) h) (bnd (ren (X ∘ʳ ιg) g) (ren (liftʳ X ∘ʳ ρf) f)) ∎
    h-eq : ∀ x → toℕ ((castʳ q ∘ʳ ιh) x) ≡ toℕ ((ιg' ∘ʳ ιh') x)
    h-eq x = trans (toℕ-castʳ q _) (trans (toℕ-ι₂ (m₁ + n₁) n _ x) (trans (+-assoc m₁ n₁ _) (sym (trans (toℕ-ι₂ m₁ _ m₂ _) (cong (m₁ +_) (toℕ-ι₂ n₁ n n₂ x))))))
    -- X at a position of (m₁ + n₁) + suc (n₂ + m₂), given as the block form of the cast
    X-toℕ : (x : Fin (m₁ + (kg + m₂))) (y : Fin ((m₁ + n₁) + suc (n₂ + m₂))) → toℕ x ≡ toℕ y → toℕ (X x) ≡ toℕ (liftʳ (castʳ q) (ρ₁ y))
    X-toℕ x y e = cong (toℕ ∘ liftʳ (castʳ q) ∘ ρ₁) (castʳ-≡ p x y e)
    g-eq : ∀ x → toℕ ((X ∘ʳ ιg) x) ≡ toℕ ((liftʳ ιg' ∘ʳ ρg) x)
    g-eq = Fin-ins-toℕ n₁ n₂
      (λ j → trans (X-toℕ _ ((m₁ ↑ʳ j) ↑ˡ suc (n₂ + m₂)) (trans (toℕ-ι₂ m₁ kg m₂ _) (trans (cong (m₁ +_) (toℕ-↑ˡ j _)) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ʳ m₁ j))))))
             (trans (cong (toℕ ∘ liftʳ (castʳ q)) (ρ-ins-₁ (m₁ + n₁) (n₂ + m₂) n (m₁ ↑ʳ j)))
             (trans (toℕ-liftʳ-inl (castʳ q) _) (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + n₁) n _ _) (trans (toℕ-↑ʳ m₁ j)
               (sym (trans (cong (toℕ ∘ liftʳ ιg') (ρ-ins-₁ n₁ n₂ n j)) (trans (toℕ-liftʳ-inl ιg' _) (trans (toℕ-ι₂ m₁ _ m₂ _) (cong (m₁ +_) (toℕ-ι₁ n₁ n n₂ j))))))))))))
      (trans (X-toℕ _ ((m₁ + n₁) ↑ʳ zero) (trans (toℕ-ι₂ m₁ kg m₂ _) (trans (cong (m₁ +_) (toℕ-hole n₁ n₂)) (trans (sym (+-assoc m₁ n₁ 0)) (sym (toℕ-hole (m₁ + n₁) _))))))
             (trans (cong (toℕ ∘ liftʳ (castʳ q)) (ρ-ins-₂ (m₁ + n₁) (n₂ + m₂) n))
             (trans (toℕ-liftʳ-last (castʳ q))
               (sym (trans (cong (toℕ ∘ liftʳ ιg') (ρ-ins-₂ n₁ n₂ n)) (toℕ-liftʳ-last ιg'))))))
      (λ j → trans (X-toℕ _ ((m₁ + n₁) ↑ʳ suc (j ↑ˡ m₂)) (trans (toℕ-ι₂ m₁ kg m₂ _) (trans (cong (m₁ +_) (toℕ-blk₃ n₁ n₂ j)) (trans (arith₁ m₁ n₁ (toℕ j)) (sym (trans (toℕ-blk₃ (m₁ + n₁) _ _) (cong (λ z → (m₁ + n₁) + suc z) (toℕ-↑ˡ j m₂))))))))
             (trans (cong (toℕ ∘ liftʳ (castʳ q)) (ρ-ins-₃ (m₁ + n₁) (n₂ + m₂) n (j ↑ˡ m₂)))
             (trans (toℕ-liftʳ-inl (castʳ q) _) (trans (toℕ-castʳ q _) (trans (toℕ-ι₃ (m₁ + n₁) n _ _) (trans (cong (λ z → (m₁ + n₁) + (n + z)) (toℕ-↑ˡ j m₂)) (trans (arith₂ m₁ n₁ n (toℕ j))
               (sym (trans (cong (toℕ ∘ liftʳ ιg') (ρ-ins-₃ n₁ n₂ n j)) (trans (toℕ-liftʳ-inl ιg' _) (trans (toℕ-ι₂ m₁ _ m₂ _) (cong (m₁ +_) (toℕ-ι₃ n₁ n n₂ j)))))))))))))
    f-eq : ∀ x → toℕ ((liftʳ X ∘ʳ ρf) x) ≡ toℕ ((wk₁ ∘ʳ ρ₂) x)
    f-eq = Fin-ins-toℕ m₁ m₂
      (λ j → trans (cong (toℕ ∘ liftʳ X) (ρ-ins-₁ m₁ m₂ kg j))
             (trans (toℕ-liftʳ-inl X _)
             (trans (X-toℕ _ ((j ↑ˡ n₁) ↑ˡ suc (n₂ + m₂)) (trans (toℕ-ι₁ m₁ kg m₂ j) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j n₁)))))
             (trans (cong (toℕ ∘ liftʳ (castʳ q)) (ρ-ins-₁ (m₁ + n₁) (n₂ + m₂) n (j ↑ˡ n₁)))
             (trans (toℕ-liftʳ-inl (castʳ q) _) (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + n₁) n _ _) (trans (toℕ-↑ˡ j n₁)
               (sym (trans (cong (toℕ ∘ wk₁) (ρ-ins-₁ m₁ m₂ _ j)) (trans (toℕ-liftʳ-inl (_↑ˡ 1) _) (trans (toℕ-↑ˡ _ 1) (toℕ-ι₁ m₁ _ m₂ j)))))))))))))
      (trans (cong (toℕ ∘ liftʳ X) (ρ-ins-₂ m₁ m₂ kg))
             (trans (toℕ-liftʳ-last X)
               (sym (trans (cong (toℕ ∘ wk₁) (ρ-ins-₂ m₁ m₂ _)) (toℕ-liftʳ-last (_↑ˡ 1))))))
      (λ j → trans (cong (toℕ ∘ liftʳ X) (ρ-ins-₃ m₁ m₂ kg j))
             (trans (toℕ-liftʳ-inl X _)
             (trans (X-toℕ _ ((m₁ + n₁) ↑ʳ suc (n₂ ↑ʳ j)) (trans (toℕ-ι₃ m₁ kg m₂ j) (trans (arith₃ m₁ n₁ n₂ (toℕ j)) (sym (trans (toℕ-blk₃ (m₁ + n₁) _ _) (cong (λ z → (m₁ + n₁) + suc z) (toℕ-↑ʳ n₂ j)))))))
             (trans (cong (toℕ ∘ liftʳ (castʳ q)) (ρ-ins-₃ (m₁ + n₁) (n₂ + m₂) n (n₂ ↑ʳ j)))
             (trans (toℕ-liftʳ-inl (castʳ q) _) (trans (toℕ-castʳ q _) (trans (toℕ-ι₃ (m₁ + n₁) n _ _) (trans (cong (λ z → (m₁ + n₁) + (n + z)) (toℕ-↑ʳ n₂ j)) (trans (arith₄ m₁ n₁ n n₂ (toℕ j))
               (sym (trans (cong (toℕ ∘ wk₁) (ρ-ins-₃ m₁ m₂ _ j)) (trans (toℕ-liftʳ-inl (_↑ˡ 1) _) (trans (toℕ-↑ˡ _ 1) (toℕ-ι₃ m₁ _ m₂ j))))))))))))))

------------------------------------------------------------------------
-- Def. 3.3: the symmetry laws for computations (comparisons of renamings)
------------------------------------------------------------------------

σ-natˡᶜ : ∀ {m₁ m₂ n} (f : Cmp (m₁ + suc (suc m₂))) (g : Cmp n)
  (p  : m₁ + suc (suc m₂) ≡ (m₁ + 1) + suc m₂)
  (q  : (m₁ + 1) + (n + m₂) ≡ m₁ + ((1 + n) + m₂))
  (q' : m₁ + ((n + 1) + m₂) ≡ m₁ + (n + suc m₂))
  → subᶜ m₁ (suc m₂) (ren (W₁₁ m₁ m₂) f) g
    ≈ ren (castʳ q' ∘ʳ S₁ₙ m₁ n m₂ ∘ʳ castʳ q) (subᶜ (m₁ + 1) m₂ (ren (castʳ p) f) g)
σ-natˡᶜ {m₁} {m₂} {n} f g p q q' = ≈-≡ (cong₂ bnd
  (trans (ren-≡ g-eq g) (ren-∘ _ _ g))
  (trans (sym (ren-∘ _ _ f)) (trans (ren-≡ f-eq f) (trans (ren-∘ _ _ f) (cong (ren (liftʳ R)) (ren-∘ _ _ f))))))
  where
    W = W₁₁ m₁ m₂
    R = castʳ q' ∘ʳ S₁ₙ m₁ n m₂ ∘ʳ castʳ q
    ρL = ρ-ins m₁ (suc m₂) n
    ρR = ρ-ins (m₁ + 1) m₂ n
    g-eq : ∀ x → toℕ (ι₂ m₁ n (suc m₂) x) ≡ toℕ ((R ∘ʳ ι₂ (m₁ + 1) n m₂) x)
    g-eq x = trans (toℕ-ι₂ m₁ n _ x) (sym (trans (conj-toℕ q (S₁ₙ m₁ n m₂) q' _ (m₁ ↑ʳ ((1 ↑ʳ x) ↑ˡ m₂)) (trans (toℕ-ι₂ (m₁ + 1) n m₂ x) (trans (+-assoc m₁ 1 (toℕ x)) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (toℕ-↑ˡ _ m₂) (toℕ-↑ʳ 1 x)))))))) (S₁ₙ-B m₁ n m₂ x)))
    -- liftʳ R after ρR after the cast, at a position given by the block form of the cast
    RR : (x : Fin (m₁ + suc (suc m₂))) (y : Fin ((m₁ + 1) + suc m₂)) → toℕ x ≡ toℕ y → toℕ ((liftʳ R ∘ʳ ρR ∘ʳ castʳ p) x) ≡ toℕ (liftʳ R (ρR y))
    RR x y e = cong (toℕ ∘ liftʳ R ∘ ρR) (castʳ-≡ p x y e)
    f-eq : ∀ x → toℕ ((ρL ∘ʳ W) x) ≡ toℕ ((liftʳ R ∘ʳ ρR ∘ʳ castʳ p) x)
    f-eq = Fin-ins-ext m₁ (suc m₂)
      (λ j → trans (cong (toℕ ∘ ρL) (toℕ-injective (trans (W₁₁-A m₁ m₂ j) (sym (toℕ-↑ˡ j _)))))
             (trans (toℕ-ρ-ins-₁ m₁ (suc m₂) n j)
             (sym (trans (RR _ ((j ↑ˡ 1) ↑ˡ suc m₂) (trans (toℕ-↑ˡ j _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j 1)))))
                  (trans (cong (toℕ ∘ liftʳ R) (ρ-ins-₁ (m₁ + 1) m₂ n (j ↑ˡ 1)))
                  (trans (toℕ-liftʳ-inl R _) (trans (conj-toℕ q (S₁ₙ m₁ n m₂) q' _ (j ↑ˡ ((1 + n) + m₂)) (trans (toℕ-ι₁ (m₁ + 1) n m₂ _) (trans (toℕ-↑ˡ j 1) (sym (toℕ-↑ˡ j _))))) (S₁ₙ-A m₁ n m₂ j))))))))
      (trans (cong (toℕ ∘ ρL) (toℕ-injective (trans (W₁₁-h₁ m₁ m₂) (sym (toℕ-blk₃ m₁ _ zero)))))
             (trans (toℕ-ρ-ins-₃ m₁ (suc m₂) n zero)
             (sym (trans (RR _ ((m₁ ↑ʳ zero) ↑ˡ suc m₂) (trans (toℕ-hole m₁ _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-hole m₁ 0)))))
                  (trans (cong (toℕ ∘ liftʳ R) (ρ-ins-₁ (m₁ + 1) m₂ n (m₁ ↑ʳ zero)))
                  (trans (toℕ-liftʳ-inl R _) (trans (conj-toℕ q (S₁ₙ m₁ n m₂) q' _ (m₁ ↑ʳ (zero ↑ˡ m₂)) (trans (toℕ-ι₁ (m₁ + 1) n m₂ _) (trans (toℕ-hole m₁ 0) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ˡ (zero {n}) m₂))))))) (S₁ₙ-h m₁ n m₂))))))))
      (λ { zero →
             trans (cong (toℕ ∘ ρL) (toℕ-injective (trans (W₁₁-h₂ m₁ m₂) (sym (toℕ-hole m₁ _)))))
             (trans (toℕ-ρ-ins-₂ m₁ (suc m₂) n)
             (sym (trans (RR _ ((m₁ + 1) ↑ʳ zero) (trans (toℕ-blk₃ m₁ _ zero) (trans (sym (+-identityʳ (m₁ + 1))) (sym (toℕ-hole (m₁ + 1) m₂)))))
                  (trans (cong (toℕ ∘ liftʳ R) (ρ-ins-₂ (m₁ + 1) m₂ n)) (toℕ-liftʳ-last R)))))
         ; (suc j) →
             trans (cong (toℕ ∘ ρL) (toℕ-injective (trans (W₁₁-C m₁ m₂ j) (sym (toℕ-blk₃ m₁ _ (suc j))))))
             (trans (toℕ-ρ-ins-₃ m₁ (suc m₂) n (suc j))
             (sym (trans (RR _ ((m₁ + 1) ↑ʳ suc j) (trans (toℕ-blk₃ m₁ _ (suc j)) (sym (trans (toℕ-blk₃ (m₁ + 1) m₂ j) (+-assoc m₁ 1 (suc (toℕ j)))))))
                  (trans (cong (toℕ ∘ liftʳ R) (ρ-ins-₃ (m₁ + 1) m₂ n j))
                  (trans (toℕ-liftʳ-inl R _) (trans (conj-toℕ q (S₁ₙ m₁ n m₂) q' _ (m₁ ↑ʳ ((1 + n) ↑ʳ j)) (trans (toℕ-ι₃ (m₁ + 1) n m₂ j) (trans (+-assoc m₁ 1 _) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ (1 + n) j))))))) (trans (S₁ₙ-C m₁ n m₂ j) (arith₁₃ m₁ n (toℕ j)))))))))
         })

σ-natʳᶜ : ∀ {m₁ m₂ n} (f : Cmp (m₁ + suc (suc m₂))) (g : Cmp n)
  (p  : m₁ + suc (suc m₂) ≡ (m₁ + 1) + suc m₂)
  (q  : m₁ + (n + suc m₂) ≡ m₁ + ((n + 1) + m₂))
  (q' : m₁ + ((1 + n) + m₂) ≡ (m₁ + 1) + (n + m₂))
  → subᶜ (m₁ + 1) m₂ (ren (castʳ p) (ren (W₁₁ m₁ m₂) f)) g
    ≈ ren (castʳ q' ∘ʳ Sₙ₁ m₁ n m₂ ∘ʳ castʳ q) (subᶜ m₁ (suc m₂) f g)
σ-natʳᶜ {m₁} {m₂} {n} f g p q q' = ≈-≡ (cong₂ bnd
  (trans (ren-≡ g-eq g) (ren-∘ _ _ g))
  (trans (cong (ren ρR) (sym (ren-∘ _ _ f))) (trans (sym (ren-∘ _ _ f)) (trans (ren-≡ f-eq f) (ren-∘ _ _ f)))))
  where
    W = W₁₁ m₁ m₂
    R = castʳ q' ∘ʳ Sₙ₁ m₁ n m₂ ∘ʳ castʳ q
    ρL = ρ-ins m₁ (suc m₂) n
    ρR = ρ-ins (m₁ + 1) m₂ n
    g-eq : ∀ x → toℕ (ι₂ (m₁ + 1) n m₂ x) ≡ toℕ ((R ∘ʳ ι₂ m₁ n (suc m₂)) x)
    g-eq x = trans (toℕ-ι₂ (m₁ + 1) n m₂ x) (trans (+-assoc m₁ 1 (toℕ x)) (sym (trans (conj-toℕ q (Sₙ₁ m₁ n m₂) q' _ (m₁ ↑ʳ ((x ↑ˡ 1) ↑ˡ m₂)) (trans (toℕ-ι₂ m₁ n _ x) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (toℕ-↑ˡ _ m₂) (toℕ-↑ˡ x 1))))))) (Sₙ₁-B m₁ n m₂ x))))
    LL : (x : Fin (m₁ + suc (suc m₂))) (y : Fin ((m₁ + 1) + suc m₂)) → toℕ (W x) ≡ toℕ y → toℕ ((ρR ∘ʳ castʳ p ∘ʳ W) x) ≡ toℕ (ρR y)
    LL x y e = cong (toℕ ∘ ρR) (castʳ-≡ p (W x) y e)
    f-eq : ∀ x → toℕ ((ρR ∘ʳ castʳ p ∘ʳ W) x) ≡ toℕ ((liftʳ R ∘ʳ ρL) x)
    f-eq = Fin-ins-ext m₁ (suc m₂)
      (λ j → trans (LL _ ((j ↑ˡ 1) ↑ˡ suc m₂) (trans (W₁₁-A m₁ m₂ j) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j 1)))))
             (trans (toℕ-ρ-ins-₁ (m₁ + 1) m₂ n (j ↑ˡ 1))
             (trans (toℕ-↑ˡ j 1)
             (sym (trans (cong (toℕ ∘ liftʳ R) (ρ-ins-₁ m₁ (suc m₂) n j))
                  (trans (toℕ-liftʳ-inl R _) (trans (conj-toℕ q (Sₙ₁ m₁ n m₂) q' _ (j ↑ˡ ((n + 1) + m₂)) (trans (toℕ-ι₁ m₁ n _ j) (sym (toℕ-↑ˡ j _)))) (Sₙ₁-A m₁ n m₂ j))))))))
      (trans (LL _ ((m₁ + 1) ↑ʳ zero) (trans (W₁₁-h₁ m₁ m₂) (sym (trans (toℕ-hole (m₁ + 1) m₂) (+-identityʳ (m₁ + 1))))))
             (trans (toℕ-ρ-ins-₂ (m₁ + 1) m₂ n)
             (sym (trans (cong (toℕ ∘ liftʳ R) (ρ-ins-₂ m₁ (suc m₂) n)) (toℕ-liftʳ-last R)))))
      (λ { zero →
             trans (LL _ ((m₁ ↑ʳ zero) ↑ˡ suc m₂) (trans (W₁₁-h₂ m₁ m₂) (sym (trans (toℕ-↑ˡ _ _) (toℕ-hole m₁ 0)))))
             (trans (toℕ-ρ-ins-₁ (m₁ + 1) m₂ n (m₁ ↑ʳ zero))
             (trans (toℕ-hole m₁ 0)
             (sym (trans (cong (toℕ ∘ liftʳ R) (ρ-ins-₃ m₁ (suc m₂) n zero))
                  (trans (toℕ-liftʳ-inl R _) (trans (conj-toℕ q (Sₙ₁ m₁ n m₂) q' _ (m₁ ↑ʳ ((n ↑ʳ zero) ↑ˡ m₂)) (trans (toℕ-ι₃ m₁ n _ zero) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (toℕ-↑ˡ _ m₂) (toℕ-hole n 0))))))) (Sₙ₁-h m₁ n m₂)))))))
         ; (suc j) →
             trans (LL _ ((m₁ + 1) ↑ʳ suc j) (trans (W₁₁-C m₁ m₂ j) (sym (trans (toℕ-blk₃ (m₁ + 1) m₂ j) (+-assoc m₁ 1 _)))))
             (trans (toℕ-ρ-ins-₃ (m₁ + 1) m₂ n j)
             (trans (+-assoc m₁ 1 _)
             (sym (trans (cong (toℕ ∘ liftʳ R) (ρ-ins-₃ m₁ (suc m₂) n (suc j)))
                  (trans (toℕ-liftʳ-inl R _) (trans (conj-toℕ q (Sₙ₁ m₁ n m₂) q' _ (m₁ ↑ʳ ((n + 1) ↑ʳ j)) (trans (toℕ-ι₃ m₁ n _ (suc j)) (trans (arith₁₄ m₁ n (toℕ j)) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ (n + 1) j))))))) (Sₙ₁-C m₁ n m₂ j)))))))
         })

------------------------------------------------------------------------
-- Def. 3.8: return is discardable (Def. 3.8 (i) for J-images), the β
-- law of Def. 4.1 and the compatibility of λ with substitution.
------------------------------------------------------------------------

ret-discardᵒ : ∀ {m₁ m₂ n} (f : Cmp (m₁ + m₂)) (v : Val n)
  → subᶜ m₁ m₂ (ren (idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂}) f) (ret v) ≈ ren (idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂}) f
ret-discardᵒ {m₁} {m₂} {n} f v =
  ≈-trans (lunit _ _)
  (≈-≡ (trans (cong (sub _) (sym (ren-∘ _ _ f)))
       (sub-ren-var _ _ Dₙ pointwise f)))
  where
    D₁ = idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂}
    Dₙ = idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂}
    ρ = ρ-ins m₁ m₂ n
    V = ren (ι₂ m₁ n m₂) v
    pointwise : ∀ x → (idˢ ∷ˢ V) ((ρ ∘ʳ D₁) x) ≡ var (Dₙ x)
    pointwise = Fin+-ext
      (λ j → trans (cong (idˢ ∷ˢ V) (trans (cong ρ (+ʳ-inj₁ (idʳ {m₁}) (!ʳ 1 +ʳ idʳ) j)) (ρ-ins-₁ m₁ m₂ n j)))
             (trans (∷ˢ-inl idˢ V _) (var-≡ (trans (toℕ-ι₁ m₁ n m₂ j) (sym (trans (cong toℕ (+ʳ-inj₁ (idʳ {m₁}) (!ʳ n +ʳ idʳ) j)) (toℕ-↑ˡ j _)))))))
      (λ j → trans (cong (idˢ ∷ˢ V) (trans (cong ρ (trans (+ʳ-inj₂ (idʳ {m₁}) (!ʳ 1 +ʳ idʳ) j) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ (!ʳ 1) (idʳ {m₂}) j)))) (ρ-ins-₃ m₁ m₂ n j)))
             (trans (∷ˢ-inl idˢ V _) (var-≡ (trans (toℕ-ι₃ m₁ n m₂ j) (sym (trans (cong toℕ (trans (+ʳ-inj₂ (idʳ {m₁}) (!ʳ n +ʳ idʳ) j) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ (!ʳ n) (idʳ {m₂}) j)))) (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ n j)))))))))

betaᵒ : ∀ {n} (f : Cmp (n + 1)) → subᶜ 0 1 (app (var zero) (var (suc zero))) (ret (lam f)) ≈ f
betaᵒ {n} f =
  ≈-trans (lunit _ _)
  (≈-trans (≈-≡ (cong₂ app (trans (cong (idˢ ∷ˢ L) (ρ-ins-₂ 0 1 n)) (∷ˢ-last idˢ L))
                            (trans (cong (idˢ ∷ˢ L) (ρ-ins-₃ 0 1 n zero)) (∷ˢ-inl idˢ L _))))
  (≈-trans (beta _ _)
           (≈-≡ (trans (sub-ren-var _ _ idʳ pointwise f) (ren-id f)))))
  where
    L = lam (ren (liftʳ (ι₂ 0 n 1)) f)
    pointwise : ∀ x → (idˢ ∷ˢ var last) (liftʳ (ι₂ 0 n 1) x) ≡ var (idʳ x)
    pointwise = Fin+1-ext
      (λ j → trans (cong (idˢ ∷ˢ var last) (liftʳ-inl (ι₂ 0 n 1) j)) (∷ˢ-inl idˢ _ _))
      (trans (cong (idˢ ∷ˢ var last) (liftʳ-last (ι₂ 0 n 1))) (∷ˢ-last idˢ _))

abs-subᵒ : ∀ {m₁ m₂ n} (f : Cmp (m₁ + suc (m₂ + 1))) (v : Val n)
  (p  : m₁ + (n + (m₂ + 1)) ≡ (m₁ + (n + m₂)) + 1) (p' : m₁ + suc (m₂ + 1) ≡ (m₁ + suc m₂) + 1)
  → lam (subst Cmp p (subᶜ m₁ (m₂ + 1) f (ret v))) ≈ subᵛ m₁ m₂ (lam (subst Cmp p' f)) v
abs-subᵒ {m₁} {m₂} {n} f v p p' =
  ≈-trans (≈-≡ (cong lam (subst-ren p _)))
  (≈-trans (lam-cong (lunit _ _))
  (≈-≡ (cong lam (begin
    sub (idˢ ∷ˢ V) (ren (liftʳ (castʳ p)) (ren ρ f))
      ≡⟨ cong (sub _) (sym (ren-∘ _ _ f)) ⟩
    sub (idˢ ∷ˢ V) (ren (liftʳ (castʳ p) ∘ʳ ρ) f)
      ≡⟨ sub-ren _ _ f ⟩
    sub ((idˢ ∷ˢ V) ∘ (liftʳ (castʳ p) ∘ʳ ρ)) f
      ≡⟨ sub-cong pointwise f ⟩
    sub (liftˢ S ∘ castʳ p') f
      ≡⟨ sym (sub-ren _ _ f) ⟩
    sub (liftˢ S) (ren (castʳ p') f)
      ≡⟨ cong (sub (liftˢ S)) (sym (subst-ren p' f)) ⟩
    sub (liftˢ S) (subst Cmp p' f) ∎))))
  where
    open ≡-Reasoning
    ρ = ρ-ins m₁ (m₂ + 1) n
    V = ren (castʳ p) (ren (ι₂ m₁ n (m₂ + 1)) v)
    S = σ-ins m₁ m₂ v
    pointwise : ((idˢ ∷ˢ V) ∘ (liftʳ (castʳ p) ∘ʳ ρ)) ≗ (liftˢ S ∘ castʳ p')
    pointwise = Fin-ins-ext m₁ (m₂ + 1)
      (λ j → begin
        (idˢ ∷ˢ V) (liftʳ (castʳ p) (ρ (j ↑ˡ _)))
          ≡⟨ cong (λ z → (idˢ ∷ˢ V) (liftʳ (castʳ p) z)) (ρ-ins-₁ m₁ (m₂ + 1) n j) ⟩
        (idˢ ∷ˢ V) (liftʳ (castʳ p) (ι₁ m₁ n (m₂ + 1) j ↑ˡ 1))
          ≡⟨ cong (idˢ ∷ˢ V) (liftʳ-inl (castʳ p) _) ⟩
        (idˢ ∷ˢ V) (castʳ p (ι₁ m₁ n (m₂ + 1) j) ↑ˡ 1)
          ≡⟨ ∷ˢ-inl idˢ V _ ⟩
        var (castʳ p (ι₁ m₁ n (m₂ + 1) j))
          ≡⟨ var-≡ (trans (toℕ-castʳ p _) (trans (toℕ-ι₁ m₁ n _ j) (sym (trans (toℕ-↑ˡ _ 1) (toℕ-ι₁ m₁ n m₂ j))))) ⟩
        var (ι₁ m₁ n m₂ j ↑ˡ 1)
          ≡⟨ cong wk (sym (σ-ins-₁ m₁ m₂ v j)) ⟩
        wk (S (j ↑ˡ suc m₂))
          ≡⟨ sym (liftˢ-inl S (j ↑ˡ suc m₂)) ⟩
        liftˢ S ((j ↑ˡ suc m₂) ↑ˡ 1)
          ≡⟨ cong (liftˢ S) (sym (castʳ-≡ p' _ _ (trans (toℕ-↑ˡ j _) (sym (trans (toℕ-↑ˡ _ 1) (toℕ-↑ˡ j _)))))) ⟩
        liftˢ S (castʳ p' (j ↑ˡ _)) ∎)
      (begin
        (idˢ ∷ˢ V) (liftʳ (castʳ p) (ρ (m₁ ↑ʳ zero)))
          ≡⟨ cong (λ z → (idˢ ∷ˢ V) (liftʳ (castʳ p) z)) (ρ-ins-₂ m₁ (m₂ + 1) n) ⟩
        (idˢ ∷ˢ V) (liftʳ (castʳ p) last)
          ≡⟨ cong (idˢ ∷ˢ V) (liftʳ-last (castʳ p)) ⟩
        (idˢ ∷ˢ V) last
          ≡⟨ ∷ˢ-last idˢ V ⟩
        ren (castʳ p) (ren (ι₂ m₁ n (m₂ + 1)) v)
          ≡⟨ sym (ren-∘ _ _ v) ⟩
        ren (castʳ p ∘ʳ ι₂ m₁ n (m₂ + 1)) v
          ≡⟨ ren-≡ (λ x → trans (toℕ-castʳ p _) (trans (toℕ-ι₂ m₁ n _ x) (sym (trans (toℕ-↑ˡ _ 1) (toℕ-ι₂ m₁ n m₂ x))))) v ⟩
        ren ((_↑ˡ 1) ∘ʳ ι₂ m₁ n m₂) v
          ≡⟨ ren-∘ _ _ v ⟩
        wk (ren (ι₂ m₁ n m₂) v)
          ≡⟨ cong wk (sym (σ-ins-₂ m₁ m₂ v)) ⟩
        wk (S (m₁ ↑ʳ zero))
          ≡⟨ sym (liftˢ-inl S (m₁ ↑ʳ zero)) ⟩
        liftˢ S ((m₁ ↑ʳ zero) ↑ˡ 1)
          ≡⟨ cong (liftˢ S) (sym (castʳ-≡ p' _ _ (trans (toℕ-hole m₁ _) (sym (trans (toℕ-↑ˡ _ 1) (toℕ-hole m₁ m₂)))))) ⟩
        liftˢ S (castʳ p' (m₁ ↑ʳ zero)) ∎)
      (Fin+1-ext
        (λ j → begin
          (idˢ ∷ˢ V) (liftʳ (castʳ p) (ρ (m₁ ↑ʳ suc (j ↑ˡ 1))))
            ≡⟨ cong (λ z → (idˢ ∷ˢ V) (liftʳ (castʳ p) z)) (ρ-ins-₃ m₁ (m₂ + 1) n (j ↑ˡ 1)) ⟩
          (idˢ ∷ˢ V) (liftʳ (castʳ p) (ι₃ m₁ n (m₂ + 1) (j ↑ˡ 1) ↑ˡ 1))
            ≡⟨ cong (idˢ ∷ˢ V) (liftʳ-inl (castʳ p) _) ⟩
          (idˢ ∷ˢ V) (castʳ p (ι₃ m₁ n (m₂ + 1) (j ↑ˡ 1)) ↑ˡ 1)
            ≡⟨ ∷ˢ-inl idˢ V _ ⟩
          var (castʳ p (ι₃ m₁ n (m₂ + 1) (j ↑ˡ 1)))
            ≡⟨ var-≡ (trans (toℕ-castʳ p _) (trans (toℕ-ι₃ m₁ n _ _) (trans (cong (λ z → m₁ + (n + z)) (toℕ-↑ˡ j 1)) (sym (trans (toℕ-↑ˡ _ 1) (toℕ-ι₃ m₁ n m₂ j)))))) ⟩
          var (ι₃ m₁ n m₂ j ↑ˡ 1)
            ≡⟨ cong wk (sym (σ-ins-₃ m₁ m₂ v j)) ⟩
          wk (S (m₁ ↑ʳ suc j))
            ≡⟨ sym (liftˢ-inl S (m₁ ↑ʳ suc j)) ⟩
          liftˢ S ((m₁ ↑ʳ suc j) ↑ˡ 1)
            ≡⟨ cong (liftˢ S) (sym (castʳ-≡ p' _ _ (trans (toℕ-blk₃ m₁ _ _) (trans (cong (λ z → m₁ + suc z) (toℕ-↑ˡ j 1)) (sym (trans (toℕ-↑ˡ _ 1) (toℕ-blk₃ m₁ m₂ j))))))) ⟩
          liftˢ S (castʳ p' (m₁ ↑ʳ suc (j ↑ˡ 1))) ∎)
        (begin
          (idˢ ∷ˢ V) (liftʳ (castʳ p) (ρ (m₁ ↑ʳ suc last)))
            ≡⟨ cong (λ z → (idˢ ∷ˢ V) (liftʳ (castʳ p) z)) (ρ-ins-₃ m₁ (m₂ + 1) n last) ⟩
          (idˢ ∷ˢ V) (liftʳ (castʳ p) (ι₃ m₁ n (m₂ + 1) last ↑ˡ 1))
            ≡⟨ cong (idˢ ∷ˢ V) (liftʳ-inl (castʳ p) _) ⟩
          (idˢ ∷ˢ V) (castʳ p (ι₃ m₁ n (m₂ + 1) last) ↑ˡ 1)
            ≡⟨ ∷ˢ-inl idˢ V _ ⟩
          var (castʳ p (ι₃ m₁ n (m₂ + 1) last))
            ≡⟨ var-≡ (trans (toℕ-castʳ p _) (trans (toℕ-ι₃ m₁ n _ last) (trans (cong (λ z → m₁ + (n + z)) (toℕ-last m₂)) (trans (arith₁₅ m₁ n m₂) (sym (toℕ-last (m₁ + (n + m₂)))))))) ⟩
          var last
            ≡⟨ sym (liftˢ-last S) ⟩
          liftˢ S last
            ≡⟨ cong (liftˢ S) (sym (castʳ-≡ p' _ _ (trans (toℕ-blk₃ m₁ _ last) (trans (cong (λ z → m₁ + suc z) (toℕ-last m₂)) (trans (arith₁₆ m₁ m₂) (sym (toℕ-last (m₁ + suc m₂)))))))) ⟩
          liftˢ S (castʳ p' (m₁ ↑ʳ suc last)) ∎))

------------------------------------------------------------------------
-- Def. 3.8 (ii) for J-images: return is copyable.
------------------------------------------------------------------------

ret-copyᵒ : ∀ {m₁ m₂ n} (f : Cmp (m₁ + suc (suc m₂))) (v : Val n)
  (p : m₁ + (n + suc m₂) ≡ (m₁ + n) + suc m₂) (q : (m₁ + n) + (n + m₂) ≡ m₁ + ((n + n) + m₂))
  → subᶜ m₁ m₂ (ren (idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂}) f) (ret v)
    ≈ ren (Cₙ m₁ n m₂ ∘ʳ castʳ q) (subᶜ (m₁ + n) m₂ (subst Cmp p (subᶜ m₁ (suc m₂) f (ret v))) (ret v))
ret-copyᵒ {m₁} {m₂} {n} f v p q =
  ≈-trans (lunit _ _)
  (≈-trans (≈-≡ (trans (cong (sub _) (sym (ren-∘ _ _ f))) (trans (sub-ren _ _ f) (sub-cong pointwise f))))
  (≈-sym (≈-trans (≈-≡ RHS-form)
         (≈-trans (bnd-cong ≈-refl (lunit _ _))
         (≈-trans (lunit _ _)
                  (≈-≡ (trans (cong (sub _) (sub-ren _ _ f)) (sub-sub _ _ f))))))))
  where
    open ≡-Reasoning
    D = idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂}
    ρ₀ = ρ-ins m₁ m₂ n
    ρ₁ = ρ-ins m₁ (suc m₂) n
    ρ₂ = ρ-ins (m₁ + n) m₂ n
    ι₀ = ι₂ m₁ n m₂
    ι₁' = ι₂ m₁ n (suc m₂)
    ι₂' = ι₂ (m₁ + n) n m₂
    R = Cₙ m₁ n m₂ ∘ʳ castʳ q
    Y = liftʳ R ∘ʳ ρ₂ ∘ʳ castʳ p
    V₀ = ren ι₀ v
    V₁ = ren (Y ∘ʳ ι₁') v
    V₂ = ren (R ∘ʳ ι₂') v
    RHS-form : ren R (subᶜ (m₁ + n) m₂ (subst Cmp p (subᶜ m₁ (suc m₂) f (ret v))) (ret v))
             ≡ bnd (ret V₂) (bnd (ret V₁) (ren (liftʳ Y ∘ʳ ρ₁) f))
    RHS-form = begin
      ren R (bnd (ren ι₂' (ret v)) (ren ρ₂ (subst Cmp p (bnd (ren ι₁' (ret v)) (ren ρ₁ f)))))
        ≡⟨ cong (λ z → ren R (bnd (ren ι₂' (ret v)) (ren ρ₂ z))) (subst-ren p _) ⟩
      bnd (ret (ren R (ren ι₂' v))) (ren (liftʳ R) (ren ρ₂ (ren (castʳ p) (bnd (ren ι₁' (ret v)) (ren ρ₁ f)))))
        ≡⟨ cong₂ (λ a b → bnd (ret a) b) (sym (ren-∘ _ _ v)) (trans (cong (ren (liftʳ R)) (sym (ren-∘ _ _ _))) (sym (ren-∘ _ _ _))) ⟩
      bnd (ret V₂) (ren Y (bnd (ren ι₁' (ret v)) (ren ρ₁ f)))
        ≡⟨ cong (bnd (ret V₂)) (cong₂ (λ a b → bnd (ret a) b) (sym (ren-∘ _ _ v)) (sym (ren-∘ _ _ f))) ⟩
      bnd (ret V₂) (bnd (ret V₁) (ren (liftʳ Y ∘ʳ ρ₁) f)) ∎
    R-toℕ : (x : Fin ((m₁ + n) + (n + m₂))) (y : Fin (m₁ + ((n + n) + m₂))) → toℕ x ≡ toℕ y → toℕ (R x) ≡ toℕ (Cₙ m₁ n m₂ y)
    R-toℕ x y e = cong (toℕ ∘ Cₙ m₁ n m₂) (castʳ-≡ q x y e)
    -- Y at a position, given the block form of the cast
    Y-at : (x : Fin (m₁ + (n + suc m₂))) (y : Fin ((m₁ + n) + suc m₂)) → toℕ x ≡ toℕ y → Y x ≡ liftʳ R (ρ₂ y)
    Y-at x y e = cong (liftʳ R ∘ ρ₂) (castʳ-≡ p x y e)
    ΣR : Subst (m₁ + suc (suc m₂)) (m₁ + (n + m₂))
    ΣR i = sub (idˢ ∷ˢ V₂) ((idˢ ∷ˢ V₁) (liftʳ Y (ρ₁ i)))
    -- both holes are filled with v renamed into the middle block
    hole-L : ∀ {x} → D x ≡ m₁ ↑ʳ zero → (idˢ ∷ˢ V₀) (ρ₀ (D x)) ≡ V₀
    hole-L e = trans (cong (idˢ ∷ˢ V₀) (trans (cong ρ₀ e) (ρ-ins-₂ m₁ m₂ n))) (∷ˢ-last idˢ V₀)
    pointwise : ((idˢ ∷ˢ V₀) ∘ (ρ₀ ∘ʳ D)) ≗ ΣR
    pointwise = Fin-ins-ext m₁ (suc m₂) blockA hole₁ (λ { zero → hole₂ ; (suc j) → blockC j })
      where
      blockA : ∀ j → (idˢ ∷ˢ V₀) (ρ₀ (D (j ↑ˡ _))) ≡ ΣR (j ↑ˡ _)
      blockA j = begin
        (idˢ ∷ˢ V₀) (ρ₀ (D (j ↑ˡ _)))
          ≡⟨ cong (idˢ ∷ˢ V₀) (trans (cong ρ₀ (+ʳ-inj₁ (idʳ {m₁}) (Δʳ 1 +ʳ idʳ) j)) (ρ-ins-₁ m₁ m₂ n j)) ⟩
        (idˢ ∷ˢ V₀) (ι₁ m₁ n m₂ j ↑ˡ 1)
          ≡⟨ ∷ˢ-inl idˢ V₀ _ ⟩
        var (ι₁ m₁ n m₂ j)
          ≡⟨ var-≡ (trans (toℕ-ι₁ m₁ n m₂ j) (sym (trans (R-toℕ _ (j ↑ˡ ((n + n) + m₂)) (trans (toℕ-ι₁ (m₁ + n) n m₂ _) (trans (toℕ-↑ˡ j n) (sym (toℕ-↑ˡ j _))))) (Cₙ-A m₁ n m₂ j)))) ⟩
        var (R (ι₁ (m₁ + n) n m₂ (j ↑ˡ n)))
          ≡⟨ sym (∷ˢ-inl idˢ V₂ _) ⟩
        (idˢ ∷ˢ V₂) (R (ι₁ (m₁ + n) n m₂ (j ↑ˡ n)) ↑ˡ 1)
          ≡⟨ cong (idˢ ∷ˢ V₂) (sym (trans (Y-at _ ((j ↑ˡ n) ↑ˡ suc m₂) (trans (toℕ-ι₁ m₁ n _ j) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j n))))) (trans (cong (liftʳ R) (ρ-ins-₁ (m₁ + n) m₂ n (j ↑ˡ n))) (liftʳ-inl R _)))) ⟩
        (idˢ ∷ˢ V₂) (Y (ι₁ m₁ n (suc m₂) j))
          ≡⟨ cong (sub (idˢ ∷ˢ V₂)) (sym (∷ˢ-inl idˢ V₁ _)) ⟩
        sub (idˢ ∷ˢ V₂) ((idˢ ∷ˢ V₁) (Y (ι₁ m₁ n (suc m₂) j) ↑ˡ 1))
          ≡⟨ cong (λ z → sub (idˢ ∷ˢ V₂) ((idˢ ∷ˢ V₁) z)) (sym (trans (cong (liftʳ Y) (ρ-ins-₁ m₁ (suc m₂) n j)) (liftʳ-inl Y _))) ⟩
        ΣR (j ↑ˡ _) ∎
      hole₁ : (idˢ ∷ˢ V₀) (ρ₀ (D (m₁ ↑ʳ zero))) ≡ ΣR (m₁ ↑ʳ zero)
      hole₁ = begin
        (idˢ ∷ˢ V₀) (ρ₀ (D (m₁ ↑ʳ zero)))
          ≡⟨ hole-L (trans (+ʳ-inj₂ (idʳ {m₁}) (Δʳ 1 +ʳ idʳ) zero) (cong (m₁ ↑ʳ_) (trans (+ʳ-inj₁ (Δʳ 1) (idʳ {m₂}) zero) (cong (_↑ˡ m₂) ([,]ʳ-inl idʳ idʳ zero))))) ⟩
        ren ι₀ v
          ≡⟨ sym (sub-ren-var _ _ ι₀ (λ x → trans (cong (idˢ ∷ˢ V₂) (trans (Y-at _ ((m₁ ↑ʳ x) ↑ˡ suc m₂) (trans (toℕ-ι₂ m₁ n _ x) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ʳ m₁ x)))))
                                                                    (trans (cong (liftʳ R) (ρ-ins-₁ (m₁ + n) m₂ n (m₁ ↑ʳ x))) (liftʳ-inl R _))))
                                                  (trans (∷ˢ-inl idˢ V₂ _) (var-≡ (trans (R-toℕ _ (m₁ ↑ʳ ((x ↑ˡ n) ↑ˡ m₂)) (trans (toℕ-ι₁ (m₁ + n) n m₂ _) (trans (toℕ-↑ʳ m₁ x) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (toℕ-↑ˡ _ m₂) (toℕ-↑ˡ x n)))))))) (trans (Cₙ-B₁ m₁ n m₂ x) (sym (toℕ-ι₂ m₁ n m₂ x)))))))
                              v) ⟩
        sub (idˢ ∷ˢ V₂) V₁
          ≡⟨ cong (sub (idˢ ∷ˢ V₂)) (sym (∷ˢ-last idˢ V₁)) ⟩
        sub (idˢ ∷ˢ V₂) ((idˢ ∷ˢ V₁) last)
          ≡⟨ cong (λ z → sub (idˢ ∷ˢ V₂) ((idˢ ∷ˢ V₁) z)) (sym (trans (cong (liftʳ Y) (ρ-ins-₂ m₁ (suc m₂) n)) (liftʳ-last Y))) ⟩
        ΣR (m₁ ↑ʳ zero) ∎
      hole₂ : (idˢ ∷ˢ V₀) (ρ₀ (D (m₁ ↑ʳ suc zero))) ≡ ΣR (m₁ ↑ʳ suc zero)
      hole₂ = begin
        (idˢ ∷ˢ V₀) (ρ₀ (D (m₁ ↑ʳ suc zero)))
          ≡⟨ hole-L (trans (+ʳ-inj₂ (idʳ {m₁}) (Δʳ 1 +ʳ idʳ) (suc zero)) (cong (m₁ ↑ʳ_) (trans (+ʳ-inj₁ (Δʳ 1) (idʳ {m₂}) (suc zero)) (cong (_↑ˡ m₂) ([,]ʳ-inr idʳ idʳ zero))))) ⟩
        ren ι₀ v
          ≡⟨ ren-≡ (λ x → trans (toℕ-ι₂ m₁ n m₂ x) (sym (trans (R-toℕ _ (m₁ ↑ʳ ((n ↑ʳ x) ↑ˡ m₂)) (trans (toℕ-ι₂ (m₁ + n) n m₂ x) (trans (+-assoc m₁ n (toℕ x)) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (trans (toℕ-↑ˡ _ m₂) (toℕ-↑ʳ n x)))))))) (Cₙ-B₂ m₁ n m₂ x)))) v ⟩
        ren (R ∘ʳ ι₂') v
          ≡⟨ sym (∷ˢ-last idˢ V₂) ⟩
        (idˢ ∷ˢ V₂) last
          ≡⟨ cong (idˢ ∷ˢ V₂) (sym (trans (Y-at _ ((m₁ + n) ↑ʳ zero) (trans (toℕ-ι₃ m₁ n _ zero) (trans (cong (m₁ +_) (+-identityʳ n)) (trans (sym (+-identityʳ (m₁ + n))) (sym (toℕ-hole (m₁ + n) m₂)))))) (trans (cong (liftʳ R) (ρ-ins-₂ (m₁ + n) m₂ n)) (liftʳ-last R)))) ⟩
        (idˢ ∷ˢ V₂) (Y (ι₃ m₁ n (suc m₂) zero))
          ≡⟨ cong (sub (idˢ ∷ˢ V₂)) (sym (∷ˢ-inl idˢ V₁ _)) ⟩
        sub (idˢ ∷ˢ V₂) ((idˢ ∷ˢ V₁) (Y (ι₃ m₁ n (suc m₂) zero) ↑ˡ 1))
          ≡⟨ cong (λ z → sub (idˢ ∷ˢ V₂) ((idˢ ∷ˢ V₁) z)) (sym (trans (cong (liftʳ Y) (ρ-ins-₃ m₁ (suc m₂) n zero)) (liftʳ-inl Y _))) ⟩
        ΣR (m₁ ↑ʳ suc zero) ∎
      blockC : ∀ j → (idˢ ∷ˢ V₀) (ρ₀ (D (m₁ ↑ʳ suc (suc j)))) ≡ ΣR (m₁ ↑ʳ suc (suc j))
      blockC j = begin
        (idˢ ∷ˢ V₀) (ρ₀ (D (m₁ ↑ʳ suc (suc j))))
          ≡⟨ cong (idˢ ∷ˢ V₀) (trans (cong ρ₀ (trans (+ʳ-inj₂ (idʳ {m₁}) (Δʳ 1 +ʳ idʳ) (suc (suc j))) (cong (m₁ ↑ʳ_) (+ʳ-inj₂ (Δʳ 1) (idʳ {m₂}) j)))) (ρ-ins-₃ m₁ m₂ n j)) ⟩
        (idˢ ∷ˢ V₀) (ι₃ m₁ n m₂ j ↑ˡ 1)
          ≡⟨ ∷ˢ-inl idˢ V₀ _ ⟩
        var (ι₃ m₁ n m₂ j)
          ≡⟨ var-≡ (trans (toℕ-ι₃ m₁ n m₂ j) (sym (trans (R-toℕ _ (m₁ ↑ʳ ((n + n) ↑ʳ j)) (trans (toℕ-ι₃ (m₁ + n) n m₂ j) (trans (arith₂ m₁ n n (toℕ j)) (trans (cong (m₁ +_) (sym (+-assoc n n (toℕ j)))) (sym (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ (n + n) j)))))))) (Cₙ-C m₁ n m₂ j)))) ⟩
        var (R (ι₃ (m₁ + n) n m₂ j))
          ≡⟨ sym (∷ˢ-inl idˢ V₂ _) ⟩
        (idˢ ∷ˢ V₂) (R (ι₃ (m₁ + n) n m₂ j) ↑ˡ 1)
          ≡⟨ cong (idˢ ∷ˢ V₂) (sym (trans (Y-at _ ((m₁ + n) ↑ʳ suc j) (trans (toℕ-ι₃ m₁ n _ (suc j)) (trans (arith₁ m₁ n (toℕ j)) (sym (toℕ-blk₃ (m₁ + n) m₂ j))))) (trans (cong (liftʳ R) (ρ-ins-₃ (m₁ + n) m₂ n j)) (liftʳ-inl R _)))) ⟩
        (idˢ ∷ˢ V₂) (Y (ι₃ m₁ n (suc m₂) (suc j)))
          ≡⟨ cong (sub (idˢ ∷ˢ V₂)) (sym (∷ˢ-inl idˢ V₁ _)) ⟩
        sub (idˢ ∷ˢ V₂) ((idˢ ∷ˢ V₁) (Y (ι₃ m₁ n (suc m₂) (suc j)) ↑ˡ 1))
          ≡⟨ cong (λ z → sub (idˢ ∷ˢ V₂) ((idˢ ∷ˢ V₁) z)) (sym (trans (cong (liftʳ Y) (ρ-ins-₃ m₁ (suc m₂) n (suc j))) (liftʳ-inl Y _))) ⟩
        ΣR (m₁ ↑ʳ suc (suc j)) ∎

------------------------------------------------------------------------
-- Def. 3.8: return v is central in CMP (Def. 3.6, both orders).
-- The let binding the value is eliminated by (lunit) on both sides,
-- after which the sides are the same let over g with a substitution
-- of f, compared blockwise.
------------------------------------------------------------------------

-- Comm (ret v) g
ret-commˡ : ∀ {n₁ n₂} (v : Val n₁) (g : Cmp n₂) m₁ m m₂ (f : Cmp (m₁ + suc (m + suc m₂)))
  (p   : m₁ + (n₁ + (m + suc m₂)) ≡ (m₁ + (n₁ + m)) + suc m₂)
  (p'  : m₁ + suc (m + suc m₂) ≡ (m₁ + suc m) + suc m₂)
  (p'' : (m₁ + suc m) + (n₂ + m₂) ≡ m₁ + suc (m + (n₂ + m₂)))
  (q   : (m₁ + (n₁ + m)) + (n₂ + m₂) ≡ m₁ + (n₁ + (m + (n₂ + m₂))))
  → subst Cmp q (subᶜ (m₁ + (n₁ + m)) m₂ (subst Cmp p (subᶜ m₁ (m + suc m₂) f (ret v))) g)
    ≈ subᶜ m₁ (m + (n₂ + m₂)) (subst Cmp p'' (subᶜ (m₁ + suc m) m₂ (subst Cmp p' f) g)) (ret v)
ret-commˡ {n₁} {n₂} v g m₁ m m₂ f p p' p'' q =
  ≈-trans (≈-≡ LHS-form)
  (≈-trans (bnd-cong ≈-refl (lunit _ _))
  (≈-trans (≈-≡ (cong₂ bnd (trans (ren-≡ g-eq g) (sub-ren-var' g)) (trans (sub-ren _ _ f) (trans (sub-cong pointwise f) (sym (sub-ren _ _ f))))))
  (≈-sym (≈-trans (≈-≡ RHS-form) (lunit _ _)))))
  where
    open ≡-Reasoning
    ιv = ι₂ m₁ n₁ (m + suc m₂)
    ρ₁ = ρ-ins m₁ (m + suc m₂) n₁
    ιg = ι₂ (m₁ + (n₁ + m)) n₂ m₂
    ρ₂ = ρ-ins (m₁ + (n₁ + m)) m₂ n₂
    ι₁' = ι₂ m₁ n₁ (m + (n₂ + m₂))
    ρ₁' = ρ-ins m₁ (m + (n₂ + m₂)) n₁
    ιg' = ι₂ (m₁ + suc m) n₂ m₂
    ρ₂' = ρ-ins (m₁ + suc m) m₂ n₂
    X = liftʳ (castʳ q) ∘ʳ ρ₂ ∘ʳ castʳ p
    Y = ρ₁' ∘ʳ castʳ p''
    VL = ren (X ∘ʳ ιv) v
    VR = ren ι₁' v
    LHS-form : subst Cmp q (subᶜ (m₁ + (n₁ + m)) m₂ (subst Cmp p (subᶜ m₁ (m + suc m₂) f (ret v))) g)
             ≡ bnd (ren (castʳ q ∘ʳ ιg) g) (bnd (ret VL) (ren (liftʳ X ∘ʳ ρ₁) f))
    LHS-form = begin
      subst Cmp q (bnd (ren ιg g) (ren ρ₂ (subst Cmp p (bnd (ren ιv (ret v)) (ren ρ₁ f)))))
        ≡⟨ subst-ren q _ ⟩
      ren (castʳ q) (bnd (ren ιg g) (ren ρ₂ (subst Cmp p (bnd (ren ιv (ret v)) (ren ρ₁ f)))))
        ≡⟨ cong (λ z → ren (castʳ q) (bnd (ren ιg g) (ren ρ₂ z))) (subst-ren p _) ⟩
      bnd (ren (castʳ q) (ren ιg g)) (ren (liftʳ (castʳ q)) (ren ρ₂ (ren (castʳ p) (bnd (ren ιv (ret v)) (ren ρ₁ f)))))
        ≡⟨ cong₂ bnd (sym (ren-∘ _ _ g)) (trans (cong (ren (liftʳ (castʳ q))) (sym (ren-∘ _ _ _))) (sym (ren-∘ _ _ _))) ⟩
      bnd (ren (castʳ q ∘ʳ ιg) g) (ren X (bnd (ren ιv (ret v)) (ren ρ₁ f)))
        ≡⟨ cong (bnd _) (cong₂ (λ a b → bnd (ret a) b) (sym (ren-∘ _ _ v)) (sym (ren-∘ _ _ f))) ⟩
      bnd (ren (castʳ q ∘ʳ ιg) g) (bnd (ret VL) (ren (liftʳ X ∘ʳ ρ₁) f)) ∎
    RHS-form : subᶜ m₁ (m + (n₂ + m₂)) (subst Cmp p'' (subᶜ (m₁ + suc m) m₂ (subst Cmp p' f) g)) (ret v)
             ≡ bnd (ret VR) (bnd (ren (Y ∘ʳ ιg') g) (ren (liftʳ Y ∘ʳ ρ₂' ∘ʳ castʳ p') f))
    RHS-form = begin
      bnd (ren ι₁' (ret v)) (ren ρ₁' (subst Cmp p'' (bnd (ren ιg' g) (ren ρ₂' (subst Cmp p' f)))))
        ≡⟨ cong (λ z → bnd (ren ι₁' (ret v)) (ren ρ₁' z)) (trans (subst-ren p'' _) (cong (λ z → ren (castʳ p'') (bnd (ren ιg' g) (ren ρ₂' z))) (subst-ren p' f))) ⟩
      bnd (ret VR) (ren ρ₁' (bnd (ren (castʳ p'') (ren ιg' g)) (ren (liftʳ (castʳ p'')) (ren ρ₂' (ren (castʳ p') f)))))
        ≡⟨ cong (bnd (ret VR)) (cong₂ bnd (trans (cong (ren ρ₁') (sym (ren-∘ _ _ g))) (sym (ren-∘ _ _ g)))
                                          (trans (cong (ren (liftʳ ρ₁')) (trans (cong (ren (liftʳ (castʳ p''))) (sym (ren-∘ _ _ f))) (sym (ren-∘ _ _ f)))) (sym (ren-∘ _ _ f)))) ⟩
      bnd (ret VR) (bnd (ren (Y ∘ʳ ιg') g) (ren (liftʳ ρ₁' ∘ʳ liftʳ (castʳ p'') ∘ʳ ρ₂' ∘ʳ castʳ p') f))
        ≡⟨ cong (λ z → bnd (ret VR) (bnd (ren (Y ∘ʳ ιg') g) z)) (ren-≡ (λ x → cong toℕ (sym (liftʳ-∘ (castʳ p'') ρ₁' _))) f) ⟩
      bnd (ret VR) (bnd (ren (Y ∘ʳ ιg') g) (ren (liftʳ Y ∘ʳ ρ₂' ∘ʳ castʳ p') f)) ∎
    -- the two casts and hole-moving renamings at a position, by block form
    X-at : (x : Fin (m₁ + (n₁ + (m + suc m₂)))) (y : Fin ((m₁ + (n₁ + m)) + suc m₂)) → toℕ x ≡ toℕ y → X x ≡ liftʳ (castʳ q) (ρ₂ y)
    X-at x y e = cong (liftʳ (castʳ q) ∘ ρ₂) (castʳ-≡ p x y e)
    Y-at : (x : Fin ((m₁ + suc m) + (n₂ + m₂))) (y : Fin (m₁ + suc (m + (n₂ + m₂)))) → toℕ x ≡ toℕ y → Y x ≡ ρ₁' y
    Y-at x y e = cong ρ₁' (castʳ-≡ p'' x y e)
    -- the renaming of g on the right, after (lunit)
    rR : Ren n₂ (m₁ + (n₁ + (m + (n₂ + m₂))))
    rR x = ι₃ m₁ n₁ (m + (n₂ + m₂)) (m ↑ʳ (x ↑ˡ m₂))
    sub-ren-var' : (g : Cmp n₂) → ren rR g ≡ sub (idˢ ∷ˢ VR) (ren (Y ∘ʳ ιg') g)
    sub-ren-var' g = sym (sub-ren-var _ _ _ (λ x → trans (cong (idˢ ∷ˢ VR) (trans (Y-at _ (m₁ ↑ʳ suc (m ↑ʳ (x ↑ˡ m₂))) (trans (toℕ-ι₂ (m₁ + suc m) n₂ m₂ x) (trans (arith₇ m₁ m (toℕ x)) (sym (trans (toℕ-blk₃ m₁ _ _) (cong (λ z → m₁ + suc z) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ˡ x m₂)))))))))
                                                                                   (ρ-ins-₃ m₁ (m + (n₂ + m₂)) n₁ _)))
                                                          (∷ˢ-inl idˢ VR _)) g)
    g-eq : ∀ x → toℕ ((castʳ q ∘ʳ ιg) x) ≡ toℕ (rR x)
    g-eq x = trans (toℕ-castʳ q _) (trans (toℕ-ι₂ (m₁ + (n₁ + m)) n₂ m₂ x) (trans (arith₆ m₁ n₁ m (toℕ x)) (sym (trans (toℕ-ι₃ m₁ n₁ _ _) (cong (λ z → m₁ + (n₁ + z)) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ˡ x m₂))))))))
    ΣL ΣR : Subst (m₁ + suc (m + suc m₂)) ((m₁ + (n₁ + (m + (n₂ + m₂)))) + 1)
    ΣL i = (idˢ ∷ˢ VL) ((liftʳ X ∘ʳ ρ₁) i)
    ΣR i = liftˢ (idˢ ∷ˢ VR) ((liftʳ Y ∘ʳ ρ₂' ∘ʳ castʳ p') i)
    -- a variable of ΣL: block form of the cast p, then ρ₂, then the cast q
    ΣL-var : (i : Fin (m₁ + suc (m + suc m₂))) {x : Fin (m₁ + (n₁ + (m + suc m₂)))} (y : Fin ((m₁ + (n₁ + m)) + suc m₂)) {z : Fin ((m₁ + (n₁ + m)) + (n₂ + m₂))}
      → ρ₁ i ≡ x ↑ˡ 1 → toℕ x ≡ toℕ y → ρ₂ y ≡ z ↑ˡ 1 → ΣL i ≡ var (castʳ q z ↑ˡ 1)
    ΣL-var i {x} y {z} e₁ e₂ e₃ = trans (cong (idˢ ∷ˢ VL) (trans (cong (liftʳ X) e₁) (trans (liftʳ-inl X x) (cong (_↑ˡ 1) (trans (X-at x y e₂) (trans (cong (liftʳ (castʳ q)) e₃) (liftʳ-inl (castʳ q) z))))))) (∷ˢ-inl idˢ VL _)
    -- a variable of ΣR: block form of the cast p', then ρ₂', the cast p'', then ρ₁'
    ΣR-var : (i : Fin (m₁ + suc (m + suc m₂))) (y : Fin ((m₁ + suc m) + suc m₂)) {x : Fin ((m₁ + suc m) + (n₂ + m₂))} (y' : Fin (m₁ + suc (m + (n₂ + m₂)))) {z : Fin (m₁ + (n₁ + (m + (n₂ + m₂))))}
      → toℕ i ≡ toℕ y → ρ₂' y ≡ x ↑ˡ 1 → toℕ x ≡ toℕ y' → ρ₁' y' ≡ z ↑ˡ 1 → ΣR i ≡ var (z ↑ˡ 1)
    ΣR-var i y {x} y' {z} e₀ e₁ e₂ e₃ =
      trans (cong (liftˢ (idˢ ∷ˢ VR)) (trans (cong (liftʳ Y ∘ ρ₂') (castʳ-≡ p' i y e₀)) (trans (cong (liftʳ Y) e₁) (trans (liftʳ-inl Y x) (cong (_↑ˡ 1) (trans (Y-at x y' e₂) e₃))))))
      (trans (liftˢ-inl (idˢ ∷ˢ VR) _) (cong wk (∷ˢ-inl idˢ VR z)))
    pointwise : ΣL ≗ ΣR
    pointwise = Fin-ins-ext m₁ (m + suc m₂) blockA hole₁ (Fin-ins-ext m m₂ blockB hole₂ blockC)
      where
      blockA : ∀ j → ΣL (j ↑ˡ _) ≡ ΣR (j ↑ˡ _)
      blockA j = trans (ΣL-var _ ((j ↑ˡ (n₁ + m)) ↑ˡ suc m₂) (ρ-ins-₁ m₁ (m + suc m₂) n₁ j) (trans (toℕ-ι₁ m₁ n₁ _ j) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j _)))) (ρ-ins-₁ (m₁ + (n₁ + m)) m₂ n₂ _))
                 (trans (var-≡ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + (n₁ + m)) n₂ m₂ _) (trans (toℕ-↑ˡ j _) (sym (trans (toℕ-↑ˡ _ 1) (toℕ-ι₁ m₁ n₁ _ j))))))))
                 (sym (ΣR-var _ ((j ↑ˡ suc m) ↑ˡ suc m₂) (j ↑ˡ suc (m + (n₂ + m₂))) (trans (toℕ-↑ˡ j _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j _)))) (ρ-ins-₁ (m₁ + suc m) m₂ n₂ _) (trans (toℕ-ι₁ (m₁ + suc m) n₂ m₂ _) (trans (toℕ-↑ˡ j _) (sym (toℕ-↑ˡ j _)))) (ρ-ins-₁ m₁ (m + (n₂ + m₂)) n₁ j))))
      hole₁ : ΣL (m₁ ↑ʳ zero) ≡ ΣR (m₁ ↑ʳ zero)
      hole₁ = begin
        ΣL (m₁ ↑ʳ zero)
          ≡⟨ cong (idˢ ∷ˢ VL) (trans (cong (liftʳ X) (ρ-ins-₂ m₁ (m + suc m₂) n₁)) (liftʳ-last X)) ⟩
        (idˢ ∷ˢ VL) last
          ≡⟨ ∷ˢ-last idˢ VL ⟩
        ren (X ∘ʳ ιv) v
          ≡⟨ ren-≡ (λ x → trans (cong toℕ (trans (X-at _ ((m₁ ↑ʳ (x ↑ˡ m)) ↑ˡ suc m₂) (trans (toℕ-ι₂ m₁ n₁ _ x) (sym (trans (toℕ-↑ˡ _ _) (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ˡ x m)))))))
                                             (trans (cong (liftʳ (castʳ q)) (ρ-ins-₁ (m₁ + (n₁ + m)) m₂ n₂ _)) (liftʳ-inl (castʳ q) _))))
                          (trans (toℕ-↑ˡ _ 1) (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + (n₁ + m)) n₂ m₂ _) (trans (toℕ-↑ʳ m₁ _) (trans (cong (m₁ +_) (toℕ-↑ˡ x m)) (sym (trans (toℕ-↑ˡ _ 1) (toℕ-ι₂ m₁ n₁ _ x))))))))) v ⟩
        ren ((_↑ˡ 1) ∘ʳ ι₁') v
          ≡⟨ ren-∘ _ _ v ⟩
        wk VR
          ≡⟨ cong wk (sym (∷ˢ-last idˢ VR)) ⟩
        wk ((idˢ ∷ˢ VR) last)
          ≡⟨ sym (liftˢ-inl (idˢ ∷ˢ VR) last) ⟩
        liftˢ (idˢ ∷ˢ VR) (last ↑ˡ 1)
          ≡⟨ cong (liftˢ (idˢ ∷ˢ VR)) (sym (trans (cong (liftʳ Y ∘ ρ₂') (castʳ-≡ p' _ ((m₁ ↑ʳ zero) ↑ˡ suc m₂) (trans (toℕ-hole m₁ _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-hole m₁ m))))))
                                                  (trans (cong (liftʳ Y) (ρ-ins-₁ (m₁ + suc m) m₂ n₂ _)) (trans (liftʳ-inl Y _) (cong (_↑ˡ 1) (trans (Y-at _ (m₁ ↑ʳ zero) (trans (toℕ-ι₁ (m₁ + suc m) n₂ m₂ _) (trans (toℕ-hole m₁ m) (sym (toℕ-hole m₁ _))))) (ρ-ins-₂ m₁ (m + (n₂ + m₂)) n₁))))))) ⟩
        ΣR (m₁ ↑ʳ zero) ∎
      blockB : ∀ j → ΣL (m₁ ↑ʳ suc (j ↑ˡ suc m₂)) ≡ ΣR (m₁ ↑ʳ suc (j ↑ˡ suc m₂))
      blockB j = trans (ΣL-var _ ((m₁ ↑ʳ (n₁ ↑ʳ j)) ↑ˡ suc m₂) (ρ-ins-₃ m₁ (m + suc m₂) n₁ _) (trans (toℕ-ι₃ m₁ n₁ _ _) (trans (cong (λ z → m₁ + (n₁ + z)) (toℕ-↑ˡ j _)) (sym (trans (toℕ-↑ˡ _ _) (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ n₁ j))))))) (ρ-ins-₁ (m₁ + (n₁ + m)) m₂ n₂ _))
                 (trans (var-≡ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + (n₁ + m)) n₂ m₂ _) (trans (toℕ-↑ʳ m₁ _) (trans (cong (m₁ +_) (toℕ-↑ʳ n₁ j)) (sym (trans (toℕ-↑ˡ _ 1) (trans (toℕ-ι₃ m₁ n₁ _ _) (cong (λ z → m₁ + (n₁ + z)) (toℕ-↑ˡ j _)))))))))))
                 (sym (ΣR-var _ ((m₁ ↑ʳ suc j) ↑ˡ suc m₂) (m₁ ↑ʳ suc (j ↑ˡ (n₂ + m₂))) (trans (toℕ-blk₃ m₁ _ _) (trans (cong (λ z → m₁ + suc z) (toℕ-↑ˡ j _)) (sym (trans (toℕ-↑ˡ _ _) (toℕ-blk₃ m₁ m j))))) (ρ-ins-₁ (m₁ + suc m) m₂ n₂ _) (trans (toℕ-ι₁ (m₁ + suc m) n₂ m₂ _) (trans (toℕ-blk₃ m₁ m j) (sym (trans (toℕ-blk₃ m₁ _ _) (cong (λ z → m₁ + suc z) (toℕ-↑ˡ j _)))))) (ρ-ins-₃ m₁ (m + (n₂ + m₂)) n₁ _))))
      hole₂ : ΣL (m₁ ↑ʳ suc (m ↑ʳ zero)) ≡ ΣR (m₁ ↑ʳ suc (m ↑ʳ zero))
      hole₂ = begin
        ΣL (m₁ ↑ʳ suc (m ↑ʳ zero))
          ≡⟨ cong (idˢ ∷ˢ VL) (trans (cong (liftʳ X) (ρ-ins-₃ m₁ (m + suc m₂) n₁ _)) (trans (liftʳ-inl X _) (cong (_↑ˡ 1) (trans (X-at _ ((m₁ + (n₁ + m)) ↑ʳ zero) (trans (toℕ-ι₃ m₁ n₁ _ _) (trans (cong (λ z → m₁ + (n₁ + z)) (toℕ-hole m _)) (trans (arith₅ m₁ n₁ m) (sym (toℕ-hole _ _)))))) (trans (cong (liftʳ (castʳ q)) (ρ-ins-₂ (m₁ + (n₁ + m)) m₂ n₂)) (liftʳ-last (castʳ q))))))) ⟩
        (idˢ ∷ˢ VL) (last ↑ˡ 1)
          ≡⟨ ∷ˢ-inl idˢ VL last ⟩
        var last
          ≡⟨ sym (liftˢ-last (idˢ ∷ˢ VR)) ⟩
        liftˢ (idˢ ∷ˢ VR) last
          ≡⟨ cong (liftˢ (idˢ ∷ˢ VR)) (sym (trans (cong (liftʳ Y ∘ ρ₂') (castʳ-≡ p' _ ((m₁ + suc m) ↑ʳ zero) (trans (toℕ-blk₃ m₁ _ _) (trans (cong (λ z → m₁ + suc z) (toℕ-hole m m₂)) (trans (arith₈ m₁ m) (sym (toℕ-hole _ _)))))))
                                                  (trans (cong (liftʳ Y) (ρ-ins-₂ (m₁ + suc m) m₂ n₂)) (liftʳ-last Y)))) ⟩
        ΣR (m₁ ↑ʳ suc (m ↑ʳ zero)) ∎
      blockC : ∀ j → ΣL (m₁ ↑ʳ suc (m ↑ʳ suc j)) ≡ ΣR (m₁ ↑ʳ suc (m ↑ʳ suc j))
      blockC j = trans (ΣL-var _ ((m₁ + (n₁ + m)) ↑ʳ suc j) (ρ-ins-₃ m₁ (m + suc m₂) n₁ _) (trans (toℕ-ι₃ m₁ n₁ _ _) (trans (cong (λ z → m₁ + (n₁ + z)) (toℕ-blk₃ m m₂ j)) (trans (arith₉ m₁ n₁ m (toℕ j)) (sym (toℕ-blk₃ _ m₂ j))))) (ρ-ins-₃ (m₁ + (n₁ + m)) m₂ n₂ j))
                 (trans (var-≡ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-castʳ q _) (trans (toℕ-ι₃ (m₁ + (n₁ + m)) n₂ m₂ j) (trans (arith₁₀ m₁ n₁ m n₂ (toℕ j)) (sym (trans (toℕ-↑ˡ _ 1) (trans (toℕ-ι₃ m₁ n₁ _ _) (cong (λ z → m₁ + (n₁ + z)) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ʳ n₂ j))))))))))))
                 (sym (ΣR-var _ ((m₁ + suc m) ↑ʳ suc j) (m₁ ↑ʳ suc (m ↑ʳ (n₂ ↑ʳ j))) (trans (toℕ-blk₃ m₁ _ _) (trans (cong (λ z → m₁ + suc z) (toℕ-blk₃ m m₂ j)) (trans (arith₁₂ m₁ m (toℕ j)) (sym (toℕ-blk₃ _ m₂ j))))) (ρ-ins-₃ (m₁ + suc m) m₂ n₂ j) (trans (toℕ-ι₃ (m₁ + suc m) n₂ m₂ j) (trans (arith₁₁ m₁ m n₂ (toℕ j)) (sym (trans (toℕ-blk₃ m₁ _ _) (cong (λ z → m₁ + suc z) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ʳ n₂ j)))))))) (ρ-ins-₃ m₁ (m + (n₂ + m₂)) n₁ _))))

-- Comm g (ret v)
ret-commʳ : ∀ {n₁ n₂} (g : Cmp n₁) (v : Val n₂) m₁ m m₂ (f : Cmp (m₁ + suc (m + suc m₂)))
  (p   : m₁ + (n₁ + (m + suc m₂)) ≡ (m₁ + (n₁ + m)) + suc m₂)
  (p'  : m₁ + suc (m + suc m₂) ≡ (m₁ + suc m) + suc m₂)
  (p'' : (m₁ + suc m) + (n₂ + m₂) ≡ m₁ + suc (m + (n₂ + m₂)))
  (q   : (m₁ + (n₁ + m)) + (n₂ + m₂) ≡ m₁ + (n₁ + (m + (n₂ + m₂))))
  → subst Cmp q (subᶜ (m₁ + (n₁ + m)) m₂ (subst Cmp p (subᶜ m₁ (m + suc m₂) f g)) (ret v))
    ≈ subᶜ m₁ (m + (n₂ + m₂)) (subst Cmp p'' (subᶜ (m₁ + suc m) m₂ (subst Cmp p' f) (ret v))) g
ret-commʳ {n₁} {n₂} g v m₁ m m₂ f p p' p'' q =
  ≈-trans (≈-≡ LHS-form)
  (≈-trans (lunit _ _)
  (≈-trans (≈-≡ (cong₂ bnd (sub-ren-var _ _ ιg' g-eq g) (trans (sub-ren _ _ f) (trans (sub-cong pointwise f) (sym (sub-ren _ _ f))))))
  (≈-sym (≈-trans (≈-≡ RHS-form) (bnd-cong ≈-refl (lunit _ _))))))
  where
    open ≡-Reasoning
    ιg = ι₂ m₁ n₁ (m + suc m₂)
    ρ₁ = ρ-ins m₁ (m + suc m₂) n₁
    ιv = ι₂ (m₁ + (n₁ + m)) n₂ m₂
    ρ₂ = ρ-ins (m₁ + (n₁ + m)) m₂ n₂
    ιg' = ι₂ m₁ n₁ (m + (n₂ + m₂))
    ρ₁' = ρ-ins m₁ (m + (n₂ + m₂)) n₁
    ιv' = ι₂ (m₁ + suc m) n₂ m₂
    ρ₂' = ρ-ins (m₁ + suc m) m₂ n₂
    X = liftʳ (castʳ q) ∘ʳ ρ₂ ∘ʳ castʳ p
    Y = ρ₁' ∘ʳ castʳ p''
    VL = ren (castʳ q ∘ʳ ιv) v
    VR = ren (Y ∘ʳ ιv') v
    LHS-form : subst Cmp q (subᶜ (m₁ + (n₁ + m)) m₂ (subst Cmp p (subᶜ m₁ (m + suc m₂) f g)) (ret v))
             ≡ bnd (ret VL) (bnd (ren (X ∘ʳ ιg) g) (ren (liftʳ X ∘ʳ ρ₁) f))
    LHS-form = begin
      subst Cmp q (bnd (ren ιv (ret v)) (ren ρ₂ (subst Cmp p (bnd (ren ιg g) (ren ρ₁ f)))))
        ≡⟨ subst-ren q _ ⟩
      ren (castʳ q) (bnd (ren ιv (ret v)) (ren ρ₂ (subst Cmp p (bnd (ren ιg g) (ren ρ₁ f)))))
        ≡⟨ cong (λ z → ren (castʳ q) (bnd (ren ιv (ret v)) (ren ρ₂ z))) (subst-ren p _) ⟩
      bnd (ret (ren (castʳ q) (ren ιv v))) (ren (liftʳ (castʳ q)) (ren ρ₂ (ren (castʳ p) (bnd (ren ιg g) (ren ρ₁ f)))))
        ≡⟨ cong₂ (λ a b → bnd (ret a) b) (sym (ren-∘ _ _ v)) (trans (cong (ren (liftʳ (castʳ q))) (sym (ren-∘ _ _ _))) (sym (ren-∘ _ _ _))) ⟩
      bnd (ret VL) (ren X (bnd (ren ιg g) (ren ρ₁ f)))
        ≡⟨ cong (bnd (ret VL)) (cong₂ bnd (sym (ren-∘ _ _ g)) (sym (ren-∘ _ _ f))) ⟩
      bnd (ret VL) (bnd (ren (X ∘ʳ ιg) g) (ren (liftʳ X ∘ʳ ρ₁) f)) ∎
    RHS-form : subᶜ m₁ (m + (n₂ + m₂)) (subst Cmp p'' (subᶜ (m₁ + suc m) m₂ (subst Cmp p' f) (ret v))) g
             ≡ bnd (ren ιg' g) (bnd (ret VR) (ren (liftʳ Y ∘ʳ ρ₂' ∘ʳ castʳ p') f))
    RHS-form = begin
      bnd (ren ιg' g) (ren ρ₁' (subst Cmp p'' (bnd (ren ιv' (ret v)) (ren ρ₂' (subst Cmp p' f)))))
        ≡⟨ cong (λ z → bnd (ren ιg' g) (ren ρ₁' z)) (trans (subst-ren p'' _) (cong (λ z → ren (castʳ p'') (bnd (ren ιv' (ret v)) (ren ρ₂' z))) (subst-ren p' f))) ⟩
      bnd (ren ιg' g) (bnd (ret (ren ρ₁' (ren (castʳ p'') (ren ιv' v)))) (ren (liftʳ ρ₁') (ren (liftʳ (castʳ p'')) (ren ρ₂' (ren (castʳ p') f)))))
        ≡⟨ cong (bnd (ren ιg' g)) (cong₂ (λ a b → bnd (ret a) b) (trans (cong (ren ρ₁') (sym (ren-∘ _ _ v))) (sym (ren-∘ _ _ v)))
                                          (trans (cong (ren (liftʳ ρ₁')) (trans (cong (ren (liftʳ (castʳ p''))) (sym (ren-∘ _ _ f))) (sym (ren-∘ _ _ f)))) (sym (ren-∘ _ _ f)))) ⟩
      bnd (ren ιg' g) (bnd (ret VR) (ren (liftʳ ρ₁' ∘ʳ liftʳ (castʳ p'') ∘ʳ ρ₂' ∘ʳ castʳ p') f))
        ≡⟨ cong (λ z → bnd (ren ιg' g) (bnd (ret VR) z)) (ren-≡ (λ x → cong toℕ (sym (liftʳ-∘ (castʳ p'') ρ₁' _))) f) ⟩
      bnd (ren ιg' g) (bnd (ret VR) (ren (liftʳ Y ∘ʳ ρ₂' ∘ʳ castʳ p') f)) ∎
    X-at : (x : Fin (m₁ + (n₁ + (m + suc m₂)))) (y : Fin ((m₁ + (n₁ + m)) + suc m₂)) → toℕ x ≡ toℕ y → X x ≡ liftʳ (castʳ q) (ρ₂ y)
    X-at x y e = cong (liftʳ (castʳ q) ∘ ρ₂) (castʳ-≡ p x y e)
    Y-at : (x : Fin ((m₁ + suc m) + (n₂ + m₂))) (y : Fin (m₁ + suc (m + (n₂ + m₂)))) → toℕ x ≡ toℕ y → Y x ≡ ρ₁' y
    Y-at x y e = cong ρ₁' (castʳ-≡ p'' x y e)
    -- the renaming of g on the left, after (lunit)
    g-eq : ∀ x → (idˢ ∷ˢ VL) ((X ∘ʳ ιg) x) ≡ var (ιg' x)
    g-eq x = trans (cong (idˢ ∷ˢ VL) (trans (X-at _ ((m₁ ↑ʳ (x ↑ˡ m)) ↑ˡ suc m₂) (trans (toℕ-ι₂ m₁ n₁ _ x) (sym (trans (toℕ-↑ˡ _ _) (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ˡ x m)))))))
                                             (trans (cong (liftʳ (castʳ q)) (ρ-ins-₁ (m₁ + (n₁ + m)) m₂ n₂ _)) (liftʳ-inl (castʳ q) _))))
             (trans (∷ˢ-inl idˢ VL _) (var-≡ (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + (n₁ + m)) n₂ m₂ _) (trans (toℕ-↑ʳ m₁ _) (trans (cong (m₁ +_) (toℕ-↑ˡ x m)) (sym (toℕ-ι₂ m₁ n₁ _ x))))))))
    ΣL ΣR : Subst (m₁ + suc (m + suc m₂)) ((m₁ + (n₁ + (m + (n₂ + m₂)))) + 1)
    ΣL i = liftˢ (idˢ ∷ˢ VL) ((liftʳ X ∘ʳ ρ₁) i)
    ΣR i = (idˢ ∷ˢ VR) ((liftʳ Y ∘ʳ ρ₂' ∘ʳ castʳ p') i)
    ΣL-var : (i : Fin (m₁ + suc (m + suc m₂))) {x : Fin (m₁ + (n₁ + (m + suc m₂)))} (y : Fin ((m₁ + (n₁ + m)) + suc m₂)) {z : Fin ((m₁ + (n₁ + m)) + (n₂ + m₂))}
      → ρ₁ i ≡ x ↑ˡ 1 → toℕ x ≡ toℕ y → ρ₂ y ≡ z ↑ˡ 1 → ΣL i ≡ var (castʳ q z ↑ˡ 1)
    ΣL-var i {x} y {z} e₁ e₂ e₃ =
      trans (cong (liftˢ (idˢ ∷ˢ VL)) (trans (cong (liftʳ X) e₁) (trans (liftʳ-inl X x) (cong (_↑ˡ 1) (trans (X-at x y e₂) (trans (cong (liftʳ (castʳ q)) e₃) (liftʳ-inl (castʳ q) z)))))))
      (trans (liftˢ-inl (idˢ ∷ˢ VL) _) (cong wk (∷ˢ-inl idˢ VL _)))
    ΣR-var : (i : Fin (m₁ + suc (m + suc m₂))) (y : Fin ((m₁ + suc m) + suc m₂)) {x : Fin ((m₁ + suc m) + (n₂ + m₂))} (y' : Fin (m₁ + suc (m + (n₂ + m₂)))) {z : Fin (m₁ + (n₁ + (m + (n₂ + m₂))))}
      → toℕ i ≡ toℕ y → ρ₂' y ≡ x ↑ˡ 1 → toℕ x ≡ toℕ y' → ρ₁' y' ≡ z ↑ˡ 1 → ΣR i ≡ var (z ↑ˡ 1)
    ΣR-var i y {x} y' {z} e₀ e₁ e₂ e₃ =
      trans (cong (idˢ ∷ˢ VR) (trans (cong (liftʳ Y ∘ ρ₂') (castʳ-≡ p' i y e₀)) (trans (cong (liftʳ Y) e₁) (trans (liftʳ-inl Y x) (cong (_↑ˡ 1) (trans (Y-at x y' e₂) e₃))))))
      (∷ˢ-inl idˢ VR _)
    pointwise : ΣL ≗ ΣR
    pointwise = Fin-ins-ext m₁ (m + suc m₂) blockA hole₁ (Fin-ins-ext m m₂ blockB hole₂ blockC)
      where
      blockA : ∀ j → ΣL (j ↑ˡ _) ≡ ΣR (j ↑ˡ _)
      blockA j = trans (ΣL-var _ ((j ↑ˡ (n₁ + m)) ↑ˡ suc m₂) (ρ-ins-₁ m₁ (m + suc m₂) n₁ j) (trans (toℕ-ι₁ m₁ n₁ _ j) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j _)))) (ρ-ins-₁ (m₁ + (n₁ + m)) m₂ n₂ _))
                 (trans (var-≡ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + (n₁ + m)) n₂ m₂ _) (trans (toℕ-↑ˡ j _) (sym (trans (toℕ-↑ˡ _ 1) (toℕ-ι₁ m₁ n₁ _ j))))))))
                 (sym (ΣR-var _ ((j ↑ˡ suc m) ↑ˡ suc m₂) (j ↑ˡ suc (m + (n₂ + m₂))) (trans (toℕ-↑ˡ j _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j _)))) (ρ-ins-₁ (m₁ + suc m) m₂ n₂ _) (trans (toℕ-ι₁ (m₁ + suc m) n₂ m₂ _) (trans (toℕ-↑ˡ j _) (sym (toℕ-↑ˡ j _)))) (ρ-ins-₁ m₁ (m + (n₂ + m₂)) n₁ j))))
      hole₁ : ΣL (m₁ ↑ʳ zero) ≡ ΣR (m₁ ↑ʳ zero)
      hole₁ = begin
        ΣL (m₁ ↑ʳ zero)
          ≡⟨ cong (liftˢ (idˢ ∷ˢ VL)) (trans (cong (liftʳ X) (ρ-ins-₂ m₁ (m + suc m₂) n₁)) (liftʳ-last X)) ⟩
        liftˢ (idˢ ∷ˢ VL) last
          ≡⟨ liftˢ-last (idˢ ∷ˢ VL) ⟩
        var last
          ≡⟨ sym (∷ˢ-inl idˢ VR last) ⟩
        (idˢ ∷ˢ VR) (last ↑ˡ 1)
          ≡⟨ cong (idˢ ∷ˢ VR) (sym (trans (cong (liftʳ Y ∘ ρ₂') (castʳ-≡ p' _ ((m₁ ↑ʳ zero) ↑ˡ suc m₂) (trans (toℕ-hole m₁ _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-hole m₁ m))))))
                                        (trans (cong (liftʳ Y) (ρ-ins-₁ (m₁ + suc m) m₂ n₂ _)) (trans (liftʳ-inl Y _) (cong (_↑ˡ 1) (trans (Y-at _ (m₁ ↑ʳ zero) (trans (toℕ-ι₁ (m₁ + suc m) n₂ m₂ _) (trans (toℕ-hole m₁ m) (sym (toℕ-hole m₁ _))))) (ρ-ins-₂ m₁ (m + (n₂ + m₂)) n₁))))))) ⟩
        ΣR (m₁ ↑ʳ zero) ∎
      blockB : ∀ j → ΣL (m₁ ↑ʳ suc (j ↑ˡ suc m₂)) ≡ ΣR (m₁ ↑ʳ suc (j ↑ˡ suc m₂))
      blockB j = trans (ΣL-var _ ((m₁ ↑ʳ (n₁ ↑ʳ j)) ↑ˡ suc m₂) (ρ-ins-₃ m₁ (m + suc m₂) n₁ _) (trans (toℕ-ι₃ m₁ n₁ _ _) (trans (cong (λ z → m₁ + (n₁ + z)) (toℕ-↑ˡ j _)) (sym (trans (toℕ-↑ˡ _ _) (trans (toℕ-↑ʳ m₁ _) (cong (m₁ +_) (toℕ-↑ʳ n₁ j))))))) (ρ-ins-₁ (m₁ + (n₁ + m)) m₂ n₂ _))
                 (trans (var-≡ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-castʳ q _) (trans (toℕ-ι₁ (m₁ + (n₁ + m)) n₂ m₂ _) (trans (toℕ-↑ʳ m₁ _) (trans (cong (m₁ +_) (toℕ-↑ʳ n₁ j)) (sym (trans (toℕ-↑ˡ _ 1) (trans (toℕ-ι₃ m₁ n₁ _ _) (cong (λ z → m₁ + (n₁ + z)) (toℕ-↑ˡ j _)))))))))))
                 (sym (ΣR-var _ ((m₁ ↑ʳ suc j) ↑ˡ suc m₂) (m₁ ↑ʳ suc (j ↑ˡ (n₂ + m₂))) (trans (toℕ-blk₃ m₁ _ _) (trans (cong (λ z → m₁ + suc z) (toℕ-↑ˡ j _)) (sym (trans (toℕ-↑ˡ _ _) (toℕ-blk₃ m₁ m j))))) (ρ-ins-₁ (m₁ + suc m) m₂ n₂ _) (trans (toℕ-ι₁ (m₁ + suc m) n₂ m₂ _) (trans (toℕ-blk₃ m₁ m j) (sym (trans (toℕ-blk₃ m₁ _ _) (cong (λ z → m₁ + suc z) (toℕ-↑ˡ j _)))))) (ρ-ins-₃ m₁ (m + (n₂ + m₂)) n₁ _))))
      hole₂ : ΣL (m₁ ↑ʳ suc (m ↑ʳ zero)) ≡ ΣR (m₁ ↑ʳ suc (m ↑ʳ zero))
      hole₂ = begin
        ΣL (m₁ ↑ʳ suc (m ↑ʳ zero))
          ≡⟨ cong (liftˢ (idˢ ∷ˢ VL)) (trans (cong (liftʳ X) (ρ-ins-₃ m₁ (m + suc m₂) n₁ _)) (trans (liftʳ-inl X _) (cong (_↑ˡ 1) (trans (X-at _ ((m₁ + (n₁ + m)) ↑ʳ zero) (trans (toℕ-ι₃ m₁ n₁ _ _) (trans (cong (λ z → m₁ + (n₁ + z)) (toℕ-hole m _)) (trans (arith₅ m₁ n₁ m) (sym (toℕ-hole _ _)))))) (trans (cong (liftʳ (castʳ q)) (ρ-ins-₂ (m₁ + (n₁ + m)) m₂ n₂)) (liftʳ-last (castʳ q))))))) ⟩
        liftˢ (idˢ ∷ˢ VL) (last ↑ˡ 1)
          ≡⟨ liftˢ-inl (idˢ ∷ˢ VL) last ⟩
        wk ((idˢ ∷ˢ VL) last)
          ≡⟨ cong wk (∷ˢ-last idˢ VL) ⟩
        wk (ren (castʳ q ∘ʳ ιv) v)
          ≡⟨ sym (ren-∘ _ _ v) ⟩
        ren ((_↑ˡ 1) ∘ʳ castʳ q ∘ʳ ιv) v
          ≡⟨ ren-≡ (λ x → trans (toℕ-↑ˡ _ 1) (trans (toℕ-castʳ q _) (trans (toℕ-ι₂ (m₁ + (n₁ + m)) n₂ m₂ x) (trans (arith₆ m₁ n₁ m (toℕ x))
                          (sym (trans (cong toℕ (trans (Y-at _ (m₁ ↑ʳ suc (m ↑ʳ (x ↑ˡ m₂))) (trans (toℕ-ι₂ (m₁ + suc m) n₂ m₂ x) (trans (arith₇ m₁ m (toℕ x)) (sym (trans (toℕ-blk₃ m₁ _ _) (cong (λ z → m₁ + suc z) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ˡ x m₂)))))))))
                                                          (ρ-ins-₃ m₁ (m + (n₂ + m₂)) n₁ _)))
                                      (trans (toℕ-↑ˡ _ 1) (trans (toℕ-ι₃ m₁ n₁ _ _) (cong (λ z → m₁ + (n₁ + z)) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ˡ x m₂)))))))))))) v ⟩
        ren (Y ∘ʳ ιv') v
          ≡⟨ sym (∷ˢ-last idˢ VR) ⟩
        (idˢ ∷ˢ VR) last
          ≡⟨ cong (idˢ ∷ˢ VR) (sym (trans (cong (liftʳ Y ∘ ρ₂') (castʳ-≡ p' _ ((m₁ + suc m) ↑ʳ zero) (trans (toℕ-blk₃ m₁ _ _) (trans (cong (λ z → m₁ + suc z) (toℕ-hole m m₂)) (trans (arith₈ m₁ m) (sym (toℕ-hole _ _)))))))
                                        (trans (cong (liftʳ Y) (ρ-ins-₂ (m₁ + suc m) m₂ n₂)) (liftʳ-last Y)))) ⟩
        ΣR (m₁ ↑ʳ suc (m ↑ʳ zero)) ∎
      blockC : ∀ j → ΣL (m₁ ↑ʳ suc (m ↑ʳ suc j)) ≡ ΣR (m₁ ↑ʳ suc (m ↑ʳ suc j))
      blockC j = trans (ΣL-var _ ((m₁ + (n₁ + m)) ↑ʳ suc j) (ρ-ins-₃ m₁ (m + suc m₂) n₁ _) (trans (toℕ-ι₃ m₁ n₁ _ _) (trans (cong (λ z → m₁ + (n₁ + z)) (toℕ-blk₃ m m₂ j)) (trans (arith₉ m₁ n₁ m (toℕ j)) (sym (toℕ-blk₃ _ m₂ j))))) (ρ-ins-₃ (m₁ + (n₁ + m)) m₂ n₂ j))
                 (trans (var-≡ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-castʳ q _) (trans (toℕ-ι₃ (m₁ + (n₁ + m)) n₂ m₂ j) (trans (arith₁₀ m₁ n₁ m n₂ (toℕ j)) (sym (trans (toℕ-↑ˡ _ 1) (trans (toℕ-ι₃ m₁ n₁ _ _) (cong (λ z → m₁ + (n₁ + z)) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ʳ n₂ j))))))))))))
                 (sym (ΣR-var _ ((m₁ + suc m) ↑ʳ suc j) (m₁ ↑ʳ suc (m ↑ʳ (n₂ ↑ʳ j))) (trans (toℕ-blk₃ m₁ _ _) (trans (cong (λ z → m₁ + suc z) (toℕ-blk₃ m m₂ j)) (trans (arith₁₂ m₁ m (toℕ j)) (sym (toℕ-blk₃ _ m₂ j))))) (ρ-ins-₃ (m₁ + suc m) m₂ n₂ j) (trans (toℕ-ι₃ (m₁ + suc m) n₂ m₂ j) (trans (arith₁₁ m₁ m n₂ (toℕ j)) (sym (trans (toℕ-blk₃ m₁ _ _) (cong (λ z → m₁ + suc z) (trans (toℕ-↑ʳ m _) (cong (m +_) (toℕ-↑ʳ n₂ j)))))))) (ρ-ins-₃ m₁ (m + (n₂ + m₂)) n₁ _))))

------------------------------------------------------------------------
-- Theorem 4.8: the term λml*-structure.  All laws of the record
-- `Laws` of MFPS.TermModel are now proved.
------------------------------------------------------------------------

open Pre assocᵛ assocᶜ public

termLaws : Laws
termLaws = record
  { symVAL      = record { σ-natˡ = σ-natˡᵛ ; σ-natʳ = σ-natʳᵛ }
  ; symCMP      = record { σ-natˡ = σ-natˡᶜ ; σ-natʳ = σ-natʳᶜ }
  ; operadVAL   = λ g g' → commᵛ g g' , commᵛ g' g
  ; !-natVAL    = !-natᵛ
  ; Δ-natVAL    = Δ-natᵛ
  ; ret-central = λ v g → ret-commˡ v g , ret-commʳ g v
  ; ret-discard = ret-discardᵒ
  ; ret-copy    = ret-copyᵒ
  ; betaᵒ       = betaᵒ
  ; abs-subᵒ    = abs-subᵒ
  }

open Build termLaws public
-- `termStructure : Structure` is Theorem 4.8
