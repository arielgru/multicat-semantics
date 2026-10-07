------------------------------------------------------------------------
-- Section 4.3: interpretation in the term model, and completeness
-- (Corollary 4.10).
--
-- The interpretation ⟦E⟧ of a term in the term λml*-structure of
-- Thm. 4.8 is provably equal to E itself.  (This is the existence half
-- of Thm. 4.9 specialised to the identity: the interpretation is the
-- unique structure morphism out of the term model, and the identity is
-- one.)  Completeness follows: if E₁ ≡ E₂ holds in every structure it
-- holds in the term model, i.e. ⟦E₁⟧ ≈ ⟦E₂⟧, i.e. E₁ ≈ E₂.
--
-- The only non-trivial cases are the k-ary term formers f(V₁,…,Vₖ)
-- and p(V₁,…,Vₖ), interpreted by the iterated single substitution
-- `plug` followed by the k-fold contraction Δᵏ.  In the term model an
-- iterated single substitution is a single simultaneous substitution
-- (`plug-sub`), and the contraction undoes the block injections.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad
open import MFPS.Syntax

module MFPS.Completeness (Σ : Signature) where

open Signature Σ
open Terms Σ
open import MFPS.Theory Σ
open import MFPS.Semantics Σ
open import MFPS.TermModel Σ
open import MFPS.TermLaws Σ using (termStructure; vars; toℕ-ι₁; toℕ-ι₂; toℕ-ι₃; var-≡; ren-≡; subst-sub; toℕ-hole; toℕ-blk₃; toℕ-ρ-ins-₁; toℕ-ρ-ins-₂; toℕ-ρ-ins-₃; sub-ren-var)
open Interp termStructure
open Structure termStructure using (module 𝕍; module ℂ)

private
  variable
    k m n : ℕ
    s : Sort

------------------------------------------------------------------------
-- block injections into k·n and the k-fold contraction
------------------------------------------------------------------------

blk : ∀ k n → Fin k → Ren n (k * n)
blk (suc k) n zero    j = j ↑ˡ (k * n)
blk (suc k) n (suc i) j = n ↑ʳ blk k n i j

Δᵏ-blk : ∀ k n (i : Fin k) (j : Fin n) → Δᵏ k n (blk k n i j) ≡ j
Δᵏ-blk (suc k) n zero    j = [,]ʳ-inl idʳ (Δᵏ k n) j
Δᵏ-blk (suc k) n (suc i) j = trans ([,]ʳ-inr idʳ (Δᵏ k n) _) (Δᵏ-blk k n i j)

-- the simultaneous substitution computed by `plug off F gs`
σplug : ∀ off k {n} (gs : Fin k → Val n) → Subst (off + k) (off + k * n)
σplug off k {n} gs x = [ (λ j → var (j ↑ˡ (k * n))) , (λ i → ren (λ j → off ↑ʳ blk k n i j) (gs i)) ]′ (splitAt off x)

σplug-inl : ∀ off k {n} (gs : Fin k → Val n) (j : Fin off) → σplug off k gs (j ↑ˡ k) ≡ var (j ↑ˡ (k * n))
σplug-inl off k gs j = cong [ _ , _ ]′ (splitAt-↑ˡ off j k)

σplug-inr : ∀ off k {n} (gs : Fin k → Val n) (i : Fin k) → σplug off k gs (off ↑ʳ i) ≡ ren (λ j → off ↑ʳ blk k n i j) (gs i)
σplug-inr off k gs i = cong [ _ , _ ]′ (splitAt-↑ʳ off k i)

------------------------------------------------------------------------
-- one step of `plug`, as substitutions (independent of the sort)
------------------------------------------------------------------------

plug-step : ∀ off k {n} (gs : Fin (suc k) → Val n) (F : Trm (off + suc k) s)
  → ren (castʳ (+-assoc off n (k * n)))
        (sub (σplug (off + n) k (gs ∘ suc)) (ren (castʳ (sym (+-assoc off n k))) (sub (σ-ins off k (gs zero)) F)))
    ≡ sub (σplug off (suc k) gs) F
plug-step off k {n} gs F = begin
  ren (castʳ A) (sub σ' (ren (castʳ B) (sub S F)))
    ≡⟨ cong (ren (castʳ A)) (sub-ren (castʳ B) σ' (sub S F)) ⟩
  ren (castʳ A) (sub (σ' ∘ castʳ B) (sub S F))
    ≡⟨ cong (ren (castʳ A)) (sub-sub _ _ F) ⟩
  ren (castʳ A) (sub ((σ' ∘ castʳ B) ∘ˢ S) F)
    ≡⟨ ren-sub _ _ F ⟩
  sub (λ i → ren (castʳ A) (sub (σ' ∘ castʳ B) (S i))) F
    ≡⟨ sub-cong pointwise F ⟩
  sub (σplug off (suc k) gs) F ∎
  where
    open ≡-Reasoning
    A = +-assoc off n (k * n)
    B = sym (+-assoc off n k)
    S = σ-ins off k (gs zero)
    σ' = σplug (off + n) k (gs ∘ suc)
    pointwise : (λ i → ren (castʳ A) (sub (σ' ∘ castʳ B) (S i))) ≗ σplug off (suc k) gs
    pointwise = Fin-ins-ext off k
      (λ j → begin
        ren (castʳ A) (sub (σ' ∘ castʳ B) (S (j ↑ˡ suc k)))
          ≡⟨ cong (λ z → ren (castʳ A) (sub (σ' ∘ castʳ B) z)) (σ-ins-₁ off k (gs zero) j) ⟩
        ren (castʳ A) (σ' (castʳ B (ι₁ off n k j)))
          ≡⟨ cong (λ z → ren (castʳ A) (σ' z)) (castʳ-≡ B _ ((j ↑ˡ n) ↑ˡ k) (trans (toℕ-ι₁ off n k j) (sym (trans (toℕ-↑ˡ _ k) (toℕ-↑ˡ j n))))) ⟩
        ren (castʳ A) (σ' ((j ↑ˡ n) ↑ˡ k))
          ≡⟨ cong (ren (castʳ A)) (σplug-inl (off + n) k (gs ∘ suc) (j ↑ˡ n)) ⟩
        var (castʳ A ((j ↑ˡ n) ↑ˡ (k * n)))
          ≡⟨ var-≡ (trans (toℕ-castʳ A _) (trans (toℕ-↑ˡ _ _) (trans (toℕ-↑ˡ j n) (sym (toℕ-↑ˡ j _))))) ⟩
        var (j ↑ˡ (suc k * n))
          ≡⟨ sym (σplug-inl off (suc k) gs j) ⟩
        σplug off (suc k) gs (j ↑ˡ suc k) ∎)
      (begin
        ren (castʳ A) (sub (σ' ∘ castʳ B) (S (off ↑ʳ zero)))
          ≡⟨ cong (λ z → ren (castʳ A) (sub (σ' ∘ castʳ B) z)) (σ-ins-₂ off k (gs zero)) ⟩
        ren (castʳ A) (sub (σ' ∘ castʳ B) (ren (ι₂ off n k) (gs zero)))
          ≡⟨ cong (ren (castʳ A)) (sub-ren-var _ _ (λ x → (off ↑ʳ x) ↑ˡ (k * n))
               (λ x → trans (cong σ' (castʳ-≡ B _ ((off ↑ʳ x) ↑ˡ k) (trans (toℕ-ι₂ off n k x) (sym (trans (toℕ-↑ˡ _ k) (toℕ-↑ʳ off x))))))
                            (σplug-inl (off + n) k (gs ∘ suc) (off ↑ʳ x)))
               (gs zero)) ⟩
        ren (castʳ A) (ren (λ x → (off ↑ʳ x) ↑ˡ (k * n)) (gs zero))
          ≡⟨ sym (ren-∘ _ _ (gs zero)) ⟩
        ren (castʳ A ∘ʳ (λ x → (off ↑ʳ x) ↑ˡ (k * n))) (gs zero)
          ≡⟨ ren-≡ (λ x → trans (toℕ-castʳ A _) (trans (toℕ-↑ˡ _ _) (trans (toℕ-↑ʳ off x) (sym (trans (toℕ-↑ʳ off _) (cong (off +_) (toℕ-↑ˡ x _))))))) (gs zero) ⟩
        ren (λ j → off ↑ʳ blk (suc k) n zero j) (gs zero)
          ≡⟨ sym (σplug-inr off (suc k) gs zero) ⟩
        σplug off (suc k) gs (off ↑ʳ zero) ∎)
      (λ i → begin
        ren (castʳ A) (sub (σ' ∘ castʳ B) (S (off ↑ʳ suc i)))
          ≡⟨ cong (λ z → ren (castʳ A) (sub (σ' ∘ castʳ B) z)) (σ-ins-₃ off k (gs zero) i) ⟩
        ren (castʳ A) (σ' (castʳ B (ι₃ off n k i)))
          ≡⟨ cong (λ z → ren (castʳ A) (σ' z)) (castʳ-≡ B _ ((off + n) ↑ʳ i) (trans (toℕ-ι₃ off n k i) (trans (sym (+-assoc off n (toℕ i))) (sym (toℕ-↑ʳ (off + n) i))))) ⟩
        ren (castʳ A) (σ' ((off + n) ↑ʳ i))
          ≡⟨ cong (ren (castʳ A)) (σplug-inr (off + n) k (gs ∘ suc) i) ⟩
        ren (castʳ A) (ren (λ j → (off + n) ↑ʳ blk k n i j) (gs (suc i)))
          ≡⟨ sym (ren-∘ _ _ (gs (suc i))) ⟩
        ren (castʳ A ∘ʳ (λ j → (off + n) ↑ʳ blk k n i j)) (gs (suc i))
          ≡⟨ ren-≡ (λ j → trans (toℕ-castʳ A _) (trans (toℕ-↑ʳ (off + n) _) (trans (+-assoc off n _) (sym (trans (toℕ-↑ʳ off _) (cong (off +_) (toℕ-↑ʳ n _))))))) (gs (suc i)) ⟩
        ren (λ j → off ↑ʳ blk (suc k) n (suc i) j) (gs (suc i))
          ≡⟨ sym (σplug-inr off (suc k) gs (suc i)) ⟩
        σplug off (suc k) gs (off ↑ʳ suc i) ∎)

------------------------------------------------------------------------
-- iterated single substitution in the term model is a simultaneous
-- substitution: for values on the nose, for computations up to (lunit)
------------------------------------------------------------------------

plug-subᵛ : ∀ off k {n} (gs : Fin k → Val n) (F : Val (off + k)) → 𝕍.plug off F gs ≡ sub (σplug off k gs) F
plug-subᵛ off zero    gs F = sym (trans (sub-cong (Fin+-ext (λ j → σplug-inl off 0 gs j) (λ ())) F) (sub-id F))
plug-subᵛ off (suc k) {n} gs F =
  trans (subst-ren (+-assoc off n (k * n)) _)
  (trans (cong (ren (castʳ (+-assoc off n (k * n)))) (plug-subᵛ (off + n) k (gs ∘ suc) _))
  (trans (cong (λ z → ren (castʳ (+-assoc off n (k * n))) (sub (σplug (off + n) k (gs ∘ suc)) z)) (subst-ren (sym (+-assoc off n k)) (subᵛ off k F (gs zero))))
         (plug-step off k gs F)))

-- let y ⇐ return v in M[ρ] is the substitution of v for the hole
subᶜ-ret : ∀ n₁ n₂ {m} (M : Cmp (n₁ + suc n₂)) (v : Val m) → subᶜ n₁ n₂ M (ret v) ≈ sub (σ-ins n₁ n₂ v) M
subᶜ-ret n₁ n₂ {m} M v =
  ≈-trans (lunit _ _) (≈-≡ (trans (sub-ren _ _ M) (sub-cong lemma M)))
  where
    σ' : Subst ((n₁ + (m + n₂)) + 1) (n₁ + (m + n₂))
    σ' = idˢ ∷ˢ ren (ι₂ n₁ m n₂) v
    lemma : (σ' ∘ ρ-ins n₁ n₂ m) ≗ σ-ins n₁ n₂ v
    lemma = Fin-ins-ext n₁ n₂
      (λ j → trans (cong σ' (ρ-ins-₁ n₁ n₂ m j)) (trans (∷ˢ-inl idˢ _ _) (sym (σ-ins-₁ n₁ n₂ v j))))
      (trans (cong σ' (ρ-ins-₂ n₁ n₂ m)) (trans (∷ˢ-last idˢ _) (sym (σ-ins-₂ n₁ n₂ v))))
      (λ j → trans (cong σ' (ρ-ins-₃ n₁ n₂ m j)) (trans (∷ˢ-inl idˢ _ _) (sym (σ-ins-₃ n₁ n₂ v j))))

subst-≈ : (p : m ≡ n) {E E' : Trm m s} → E ≈ E' → subst (λ n → Trm n s) p E ≈ subst (λ n → Trm n s) p E'
subst-≈ refl e = e

plug-subᶜ : ∀ off k {n} (gs : Fin k → Val n) (F : Cmp (off + k)) → ℂ.plug off F (ret ∘ gs) ≈ sub (σplug off k gs) F
plug-subᶜ off zero    gs F = ≈-≡ (sym (trans (sub-cong (Fin+-ext (λ j → σplug-inl off 0 gs j) (λ ())) F) (sub-id F)))
plug-subᶜ off (suc k) {n} gs F =
  ≈-trans (subst-≈ (+-assoc off n (k * n)) (plug-subᶜ (off + n) k (gs ∘ suc) _))
  (≈-trans (subst-≈ (+-assoc off n (k * n)) (sub-≈ (σplug (off + n) k (gs ∘ suc)) (subst-≈ (sym (+-assoc off n k)) (subᶜ-ret off k F (gs zero)))))
  (≈-≡ (trans (subst-ren (+-assoc off n (k * n)) _)
       (trans (cong (λ z → ren (castʳ (+-assoc off n (k * n))) (sub (σplug (off + n) k (gs ∘ suc)) z)) (subst-ren (sym (+-assoc off n k)) (sub (σ-ins off k (gs zero)) F)))
              (plug-step off k gs F)))))

------------------------------------------------------------------------
-- the canonical arguments and tabulation
------------------------------------------------------------------------

tabulate : (Fin k → Val n) → Args n k
tabulate {zero}  f = []
tabulate {suc k} f = f zero ∷ tabulate (f ∘ suc)

subA-vars : (σ : Subst m n) (k : ℕ) (ι : Fin k → Fin m) → subA σ (vars k ι) ≡ tabulate (σ ∘ ι)
subA-vars σ zero    ι = refl
subA-vars σ (suc k) ι = cong (σ (ι zero) ∷_) (subA-vars σ k (ι ∘ suc))

renA-tabulate : (r : Ren m n) (f : Fin k → Val m) → renA r (tabulate f) ≡ tabulate (ren r ∘ f)
renA-tabulate {k = zero}  r f = refl
renA-tabulate {k = suc k} r f = cong (ren r (f zero) ∷_) (renA-tabulate r (f ∘ suc))

tabulate-≈ᵃ : {f : Fin k → Val n} (Vs : Args n k) → (∀ i → f i ≈ lookup Vs i) → tabulate f ≈ᵃ Vs
tabulate-≈ᵃ []       h = []
tabulate-≈ᵃ (V ∷ Vs) h = h zero ∷ tabulate-≈ᵃ Vs (h ∘ suc)

-- the interpretation of a k-ary former applied to the canonical arguments
former-sub : ∀ {n} (k : ℕ) (gs : Fin k → Val n) (ι : Fin k → Fin k)
  → renA (Δᵏ k n) (subA (σplug 0 k gs) (vars k ι)) ≡ tabulate (gs ∘ ι)
former-sub {n} k gs ι =
  trans (cong (renA (Δᵏ k n)) (subA-vars (σplug 0 k gs) k ι))
  (trans (renA-tabulate (Δᵏ k n) _)
         (tabulate-cong (λ i → trans (cong (ren (Δᵏ k n)) (σplug-inr 0 k gs (ι i)))
                                     (trans (sym (ren-∘ _ _ (gs (ι i)))) (trans (ren-cong (λ j → Δᵏ-blk k n (ι i) j) (gs (ι i))) (ren-id (gs (ι i))))))))
  where
    tabulate-cong : ∀ {k} {f g : Fin k → Val n} → (∀ i → f i ≡ g i) → tabulate f ≡ tabulate g
    tabulate-cong {zero}  h = refl
    tabulate-cong {suc k} h = cong₂ _∷_ (h zero) (tabulate-cong (h ∘ suc))

------------------------------------------------------------------------
-- the interpretation in the term model is the identity
------------------------------------------------------------------------

-- the contraction used by `let` and application undoes the block injections
contr-ι₂ : ∀ n (x : Fin n) → contr n (ι₂ n n 0 x) ≡ x
contr-ι₂ n x = trans ([,]ʳ-inr idʳ (castʳ (+-identityʳ n)) (x ↑ˡ 0)) (castʳ-≡ _ _ _ (toℕ-↑ˡ x 0))

contr-ι₁ : ∀ n (x : Fin n) → contr n (ι₁ n n 0 x) ≡ x
contr-ι₁ n x = [,]ʳ-inl idʳ (castʳ (+-identityʳ n)) x

term-interpᵛ : (V : Val n) → ⟦ V ⟧ᵛ ≈ V
term-interpᶜ : (M : Cmp n) → ⟦ M ⟧ᶜ ≈ M
term-interpᵃ : (Vs : Args n k) (i : Fin k) → ⟦ Vs ⟧ᵃ i ≈ lookup Vs i

term-interpᵛ (var i) = ≈-refl
term-interpᵛ {n} (fun {k} f Vs) =
  ≈-trans (≈-≡ (trans (cong (ren (Δᵏ k n)) (plug-subᵛ 0 k ⟦ Vs ⟧ᵃ (fun f (vars k idʳ)))) (cong (fun f) (former-sub k ⟦ Vs ⟧ᵃ idʳ))))
          (fun-cong (tabulate-≈ᵃ Vs (term-interpᵃ Vs)))
term-interpᵛ (lam M) = lam-cong (term-interpᶜ M)

term-interpᶜ (ret V) = ret-cong (term-interpᵛ V)
term-interpᶜ {n} (bnd M₂ M₁) =
  ≈-trans (≈-≡ (cong₂ bnd (trans (sym (ren-∘ _ _ ⟦ M₂ ⟧ᶜ)) (trans (ren-cong (contr-ι₂ n) ⟦ M₂ ⟧ᶜ) (ren-id ⟦ M₂ ⟧ᶜ)))
                          (trans (sym (ren-∘ _ _ ⟦ M₁ ⟧ᶜ)) (trans (ren-cong lemma ⟦ M₁ ⟧ᶜ) (ren-id ⟦ M₁ ⟧ᶜ)))))
          (bnd-cong (term-interpᶜ M₂) (term-interpᶜ M₁))
  where
    lemma : (liftʳ (contr n) ∘ʳ ρ-ins n 0 n) ≗ idʳ
    lemma = Fin+1-ext
      (λ j → trans (cong (liftʳ (contr n)) (ρ-ins-₁ n 0 n j)) (trans (liftʳ-inl (contr n) _) (cong (_↑ˡ 1) (contr-ι₁ n j))))
      (trans (cong (liftʳ (contr n)) (ρ-ins-₂ n 0 n)) (liftʳ-last (contr n)))
term-interpᶜ {n} (prc {k} p Vs) =
  ≈-trans (ren-≈ (Δᵏ k n) (plug-subᶜ 0 k ⟦ Vs ⟧ᵃ (prc p (vars k idʳ))))
  (≈-trans (≈-≡ (cong (prc p) (former-sub k ⟦ Vs ⟧ᵃ idʳ)))
           (prc-cong (tabulate-≈ᵃ Vs (term-interpᵃ Vs))))
term-interpᶜ {n} (app V₁ V₂) =
  ≈-trans (ren-≈ (contr n) (≈-trans (subᶜ-cong (subᶜ-ret 0 1 ⊛ V₁') ≈-refl) (subᶜ-ret n 0 (sub (σ-ins 0 1 V₁') ⊛) V₂')))
  (≈-trans (≈-≡ (cong₂ app
     (trans (cong (ren (contr n)) (trans (cong (sub S₂) (σ-ins-₂ 0 1 V₁'))
                                        (sub-ren-var (ι₂ 0 n 1) S₂ (ι₁ n n 0) (λ x → σ-ins-₁ n 0 V₂' x) V₁')))
            (trans (sym (ren-∘ _ _ V₁')) (trans (ren-cong (contr-ι₁ n) V₁') (ren-id V₁'))))
     (trans (cong (ren (contr n)) (trans (cong (sub S₂) (σ-ins-₃ 0 1 V₁' zero)) (σ-ins-₂ n 0 V₂')))
            (trans (sym (ren-∘ _ _ V₂')) (trans (ren-cong (contr-ι₂ n) V₂') (ren-id V₂'))))))
           (app-cong (term-interpᵛ V₁) (term-interpᵛ V₂)))
  where
    V₁' = ⟦ V₁ ⟧ᵛ
    V₂' = ⟦ V₂ ⟧ᵛ
    ⊛ : Cmp 2
    ⊛ = app (var zero) (var (suc zero))
    S₂ = σ-ins n 0 V₂'

term-interpᵃ (V ∷ Vs) zero    = term-interpᵛ V
term-interpᵃ (V ∷ Vs) (suc i) = term-interpᵃ Vs i

------------------------------------------------------------------------
-- Definition 4.6: validity, and Corollary 4.10 (completeness)
------------------------------------------------------------------------

-- ⊩ E₁ ≡_Γ E₂ : the equation holds in every λml*-structure
Valid : Trm n s → Trm n s → Set₁
Valid {n} E₁ E₂ = (S : Structure) → Interp._⊨_≡_ S n E₁ E₂

complete : {E₁ E₂ : Trm n s} → Valid E₁ E₂ → E₁ ≈ E₂
complete {s = val} {E₁} {E₂} h = ≈-trans (≈-sym (term-interpᵛ E₁)) (≈-trans (h termStructure) (term-interpᵛ E₂))
complete {s = cmp} {E₁} {E₂} h = ≈-trans (≈-sym (term-interpᶜ E₁)) (≈-trans (h termStructure) (term-interpᶜ E₂))
