------------------------------------------------------------------------
-- Lemma 4.5 (the interpretation commutes with renaming and with
-- substitution), for an arbitrary λml*-structure S.
--
-- Method.  Every case of the induction is an equation between two
-- ways of applying words of Sub×_𝕍 / Sub_ℂ to the interpretation of
-- the immediate subterms; the equation between the words holds in the
-- substitution PROP (naturality of tupling, of Δ, centrality, …) and
-- is transferred to S by soundness (Thm. 3.16).  The k-ary formers are
-- handled by `plug-tuple` (MFPS.SubTuple), which identifies Def. 4.4's
-- `plug` with the tuple word.
--
-- Part (a): renaming.  Part (b) is proved for the "disjoint-context"
-- substitution σ-ins n₁ n₂ W (which the term model uses as its
-- operadic substitution) — this is exactly the paper's
--   ⟦E{W/y}⟧ ≡ ⟦E⟧{n₁ ⊣ ⟦W⟧ ⊢ n₂}
-- — and the shared-context single substitution E[W] of Fig. 2 is
-- obtained from it by contraction.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad
open import MFPS.Syntax

module MFPS.SubstLemma (Σ : Signature) where

open Signature Σ
open Terms Σ
open import MFPS.Semantics Σ
open import MFPS.Theory Σ using (wk₁; _≈_)
open import MFPS.TermModel Σ using (σ-ins; σ-ins-₁; σ-ins-₂; σ-ins-₃; ι₁; ι₂; ι₃; Fin-ins-ext)
open import MFPS.TermLaws Σ using (toℕ-ι₁; toℕ-ι₂; toℕ-ι₃; toℕ-hole; toℕ-blk₃; toℕ-last)

private
  variable
    k m n : ℕ
    s : Sort

------------------------------------------------------------------------
-- lifting the disjoint-context substitution under a binder: it is the
-- same substitution with the last variable added to the right block,
-- up to the arity casts (n₁+1+n₂)+1 = n₁+1+(n₂+1) and
-- n₁+(m+(n₂+1)) = (n₁+(m+n₂))+1
------------------------------------------------------------------------

open import MFPS.TermLaws Σ using (var-≡; ren-≡)

P₁ : ∀ n₁ m n₂ → n₁ + (m + (n₂ + 1)) ≡ (n₁ + (m + n₂)) + 1
P₁ n₁ m n₂ = trans (cong (n₁ +_) (sym (+-assoc m n₂ 1))) (sym (+-assoc n₁ (m + n₂) 1))

E₁ : ∀ n₁ n₂ → (n₁ + suc n₂) + 1 ≡ n₁ + suc (n₂ + 1)
E₁ n₁ n₂ = +-assoc n₁ (suc n₂) 1

liftˢ-σ-ins : ∀ n₁ n₂ {m} (W : Val m) (E : Trm ((n₁ + suc n₂) + 1) s)
  → sub (liftˢ (σ-ins n₁ n₂ W)) E ≡ ren (castʳ (P₁ n₁ m n₂)) (sub (σ-ins n₁ (n₂ + 1) W) (ren (castʳ (E₁ n₁ n₂)) E))
liftˢ-σ-ins n₁ n₂ {m} W E =
  trans (sub-cong pointwise E) (trans (sym (ren-sub (S₁ ∘ castʳ E') (castʳ P) E)) (cong (ren (castʳ P)) (sym (sub-ren (castʳ E') S₁ E))))
  where
    open ≡-Reasoning
    S₀ = σ-ins n₁ n₂ W
    S₁ = σ-ins n₁ (n₂ + 1) W
    P = P₁ n₁ m n₂
    E' = E₁ n₁ n₂
    pointwise : liftˢ S₀ ≗ (λ i → ren (castʳ P) (S₁ (castʳ E' i)))
    pointwise = Fin+1-ext
      (Fin-ins-ext n₁ n₂
        (λ j → begin
          liftˢ S₀ ((j ↑ˡ suc n₂) ↑ˡ 1)
            ≡⟨ trans (liftˢ-inl S₀ _) (cong wk (σ-ins-₁ n₁ n₂ W j)) ⟩
          var (ι₁ n₁ m n₂ j ↑ˡ 1)
            ≡⟨ var-≡ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-ι₁ n₁ m n₂ j) (sym (trans (toℕ-castʳ P _) (toℕ-ι₁ n₁ m (n₂ + 1) j))))) ⟩
          var (castʳ P (ι₁ n₁ m (n₂ + 1) j))
            ≡⟨ cong (ren (castʳ P)) (sym (σ-ins-₁ n₁ (n₂ + 1) W j)) ⟩
          ren (castʳ P) (S₁ (j ↑ˡ suc (n₂ + 1)))
            ≡⟨ cong (ren (castʳ P) ∘ S₁) (sym (castʳ-≡ E' _ _ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-↑ˡ j _) (sym (toℕ-↑ˡ j _)))))) ⟩
          ren (castʳ P) (S₁ (castʳ E' ((j ↑ˡ suc n₂) ↑ˡ 1))) ∎)
        (begin
          liftˢ S₀ ((n₁ ↑ʳ zero) ↑ˡ 1)
            ≡⟨ trans (liftˢ-inl S₀ _) (cong wk (σ-ins-₂ n₁ n₂ W)) ⟩
          wk (ren (ι₂ n₁ m n₂) W)
            ≡⟨ sym (ren-∘ _ _ W) ⟩
          ren ((_↑ˡ 1) ∘ʳ ι₂ n₁ m n₂) W
            ≡⟨ ren-≡ (λ x → trans (toℕ-↑ˡ _ 1) (trans (toℕ-ι₂ n₁ m n₂ x) (sym (trans (toℕ-castʳ P _) (toℕ-ι₂ n₁ m (n₂ + 1) x))))) W ⟩
          ren (castʳ P ∘ʳ ι₂ n₁ m (n₂ + 1)) W
            ≡⟨ ren-∘ _ _ W ⟩
          ren (castʳ P) (ren (ι₂ n₁ m (n₂ + 1)) W)
            ≡⟨ cong (ren (castʳ P)) (sym (σ-ins-₂ n₁ (n₂ + 1) W)) ⟩
          ren (castʳ P) (S₁ (n₁ ↑ʳ zero))
            ≡⟨ cong (ren (castʳ P) ∘ S₁) (sym (castʳ-≡ E' _ _ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-hole n₁ n₂) (sym (toℕ-hole n₁ _)))))) ⟩
          ren (castʳ P) (S₁ (castʳ E' ((n₁ ↑ʳ zero) ↑ˡ 1))) ∎)
        (λ j → begin
          liftˢ S₀ ((n₁ ↑ʳ suc j) ↑ˡ 1)
            ≡⟨ trans (liftˢ-inl S₀ _) (cong wk (σ-ins-₃ n₁ n₂ W j)) ⟩
          var (ι₃ n₁ m n₂ j ↑ˡ 1)
            ≡⟨ var-≡ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-ι₃ n₁ m n₂ j) (sym (trans (toℕ-castʳ P _) (trans (toℕ-ι₃ n₁ m (n₂ + 1) _) (cong (λ z → n₁ + (m + z)) (toℕ-↑ˡ j 1))))))) ⟩
          var (castʳ P (ι₃ n₁ m (n₂ + 1) (j ↑ˡ 1)))
            ≡⟨ cong (ren (castʳ P)) (sym (σ-ins-₃ n₁ (n₂ + 1) W (j ↑ˡ 1))) ⟩
          ren (castʳ P) (S₁ (n₁ ↑ʳ suc (j ↑ˡ 1)))
            ≡⟨ cong (ren (castʳ P) ∘ S₁) (sym (castʳ-≡ E' _ _ (trans (toℕ-↑ˡ _ 1) (trans (toℕ-blk₃ n₁ n₂ j) (sym (trans (toℕ-blk₃ n₁ _ _) (cong (λ z → n₁ + suc z) (toℕ-↑ˡ j 1)))))))) ⟩
          ren (castʳ P) (S₁ (castʳ E' ((n₁ ↑ʳ suc j) ↑ˡ 1))) ∎))
      (begin
        liftˢ S₀ last
          ≡⟨ liftˢ-last S₀ ⟩
        var last
          ≡⟨ var-≡ (trans (toℕ-last (n₁ + (m + n₂))) (trans (trans (+-identityʳ _) (cong (λ z → n₁ + (m + z)) (sym (+-identityʳ n₂)))) (sym (trans (toℕ-castʳ P _) (trans (toℕ-ι₃ n₁ m (n₂ + 1) last) (cong (λ z → n₁ + (m + z)) (toℕ-last n₂))))))) ⟩
        var (castʳ P (ι₃ n₁ m (n₂ + 1) last))
          ≡⟨ cong (ren (castʳ P)) (sym (σ-ins-₃ n₁ (n₂ + 1) W last)) ⟩
        ren (castʳ P) (S₁ (n₁ ↑ʳ suc last))
          ≡⟨ cong (ren (castʳ P) ∘ S₁) (sym (castʳ-≡ E' _ _ (trans (toℕ-last (n₁ + suc n₂)) (trans (arithL n₁ n₂) (sym (trans (toℕ-blk₃ n₁ _ last) (cong (λ z → n₁ + suc z) (toℕ-last n₂)))))))) ⟩
        ren (castʳ P) (S₁ (castʳ E' last)) ∎)
      where
        arithL : ∀ a b → (a + suc b) + 0 ≡ a + suc (b + 0)
        arithL a b = trans (+-identityʳ (a + suc b)) (cong (λ z → a + suc z) (sym (+-identityʳ b)))

module Lemma45 (S : Structure) where
  open Structure S
  open Interp S
  open import MFPS.FreydSub M
  import MFPS.Sub 𝕊ᵥ as V
  import MFPS.Sub ℂ as C
  import MFPS.SubTuple 𝕊ᵥ as VT
  import MFPS.SubTuple ℂ as CT
  import MFPS.Representable 𝕊ᵥ as VR
  import MFPS.Representable ℂ as CR

  -- the k-fold contraction Δᵏ is natural in the renaming
  contr-nat : (r : Ren m n) → (contr n ∘ʳ (r +ʳ r +ʳ idʳ {0})) ≗ (r ∘ʳ contr m)
  contr-nat {m} {n} r = Fin+-ext
    (λ j → trans (cong (contr n) (+ʳ-inj₁ r (r +ʳ idʳ) j)) (trans ([,]ʳ-inl idʳ (castʳ (+-identityʳ n)) (r j)) (cong r (sym ([,]ʳ-inl idʳ (castʳ (+-identityʳ m)) j)))))
    (Fin+-ext {m = m} {n = 0}
      (λ j → toℕ-injective (begin
        toℕ (contr n ((r +ʳ r +ʳ idʳ) (m ↑ʳ (j ↑ˡ 0))))
          ≡⟨ cong (toℕ ∘ contr n) (trans (+ʳ-inj₂ r (r +ʳ idʳ) (j ↑ˡ 0)) (cong (n ↑ʳ_) (+ʳ-inj₁ r (idʳ {0}) j))) ⟩
        toℕ (contr n (n ↑ʳ (r j ↑ˡ 0)))
          ≡⟨ cong toℕ ([,]ʳ-inr idʳ (castʳ (+-identityʳ n)) (r j ↑ˡ 0)) ⟩
        toℕ (castʳ (+-identityʳ n) (r j ↑ˡ 0))
          ≡⟨ trans (toℕ-castʳ _ _) (toℕ-↑ˡ (r j) 0) ⟩
        toℕ (r j)
          ≡⟨ cong (toℕ ∘ r) (sym (toℕ-injective (trans (cong toℕ ([,]ʳ-inr idʳ (castʳ (+-identityʳ m)) (j ↑ˡ 0))) (trans (toℕ-castʳ _ _) (toℕ-↑ˡ j 0))))) ⟩
        toℕ (r (contr m (m ↑ʳ (j ↑ˡ 0)))) ∎))
      (λ ()))
    where open ≡-Reasoning

  ----------------------------------------------------------------------
  -- Lemma 4.5 (a): ⟦E[r]⟧ ≈ ⟦E⟧[r]
  ----------------------------------------------------------------------

  ren-lemmaᵛ : (r : Ren m n) (V : Val m) → ⟦ ren r V ⟧ᵛ 𝕍.≈ ⟦ V ⟧ᵛ 𝕍.[ r ]
  ren-lemmaᶜ : (r : Ren m n) (M : Cmp m) → ⟦ ren r M ⟧ᶜ ℂ.≈ ⟦ M ⟧ᶜ ℂ.[ r ]
  ren-lemmaᵃ : (r : Ren m n) (Vs : Args m k) (i : Fin k) → ⟦ renA r Vs ⟧ᵃ i 𝕍.≈ ⟦ Vs ⟧ᵃ i 𝕍.[ r ]

  ren-lemmaᵛ r (var i) = 𝕍.≈.sym (𝕍.≈.trans (𝕍.≈.sym (𝕍.ren-∘ 𝕍.idₒ (ptʳ i) r)) (𝕍.ren-cong 𝕍.≈.refl (λ _ → refl)))
  ren-lemmaᵛ {m} {n} r (fun {k} f Vs) =
    𝕍.≈.trans (VT.plug-tuple₀ cartRulesᵥ (σF f) ⟦ renA r Vs ⟧ᵃ)
    (𝕍.≈.trans (⋆-soundᵛ (VT.tuple-cong (ren-lemmaᵃ r Vs)) (σF f))
    (𝕍.≈.trans (⋆-soundᵛ (VT.tuple-nat ⟦ Vs ⟧ᵃ V.⟦ V.rn r ⟧ tt) (σF f))
    (𝕍.≈.trans (𝕍.≈.reflexive (V.⋆-++ (σF f) (VT.tupleʷ ⟦ Vs ⟧ᵃ) V.⟦ V.rn r ⟧))
               (𝕍.ren-cong (𝕍.≈.sym (VT.plug-tuple₀ cartRulesᵥ (σF f) ⟦ Vs ⟧ᵃ)) (λ _ → refl)))))
  ren-lemmaᵛ r (lam M) = 𝕍.≈.trans (abs-cong (ren-lemmaᶜ (liftʳ r) M)) (abs-ren ⟦ M ⟧ᶜ r)

  ren-lemmaᶜ r (ret V) = ℂ.≈.trans (𝒥-cong (ren-lemmaᵛ r V)) (𝒥-ren ⟦ V ⟧ᵛ r)
  ren-lemmaᶜ {m} {n} r (bnd M₂ M₁) =
    ℂ.≈.trans (ℂ.ren-cong (ℂ.sub-cong (ℂ.≈.trans (ren-lemmaᶜ (liftʳ r) M₁) (ℂ.ren-cong ℂ.≈.refl (+ʳ-cong {r = r} {r' = r} (λ _ → refl) (λ i → sym (+ʳ-id 1 0 i))))) (ren-lemmaᶜ r M₂)) (λ _ → refl))
    (ℂ.≈.trans (ℂ.ren-cong (ℂ.≈.sym (ℂ.ren-sub ⟦ M₁ ⟧ᶜ ⟦ M₂ ⟧ᶜ r r idʳ)) (λ _ → refl))
    (ℂ.≈.trans (ℂ.≈.sym (ℂ.ren-∘ _ _ _))
    (ℂ.≈.trans (ℂ.ren-cong ℂ.≈.refl (contr-nat r))
               (ℂ.ren-∘ _ _ _))))
  ren-lemmaᶜ {m} {n} r (prc {k} p Vs) =
    ℂ.≈.trans (CT.plug-tuple₀ cartRulesᶜ (σP p) (𝒥 ∘ ⟦ renA r Vs ⟧ᵃ))
    (ℂ.≈.trans (⋆-soundᶜ (CT.tuple-cong (λ i → ℂ.≈.trans (𝒥-cong (ren-lemmaᵃ r Vs i)) (𝒥-ren (⟦ Vs ⟧ᵃ i) r))) (σP p))
    (ℂ.≈.trans (⋆-soundᶜ (CT.tuple-nat (𝒥 ∘ ⟦ Vs ⟧ᵃ) C.⟦ C.rn r ⟧ tt) (σP p))
    (ℂ.≈.trans (ℂ.≈.reflexive (C.⋆-++ (σP p) (CT.tupleʷ (𝒥 ∘ ⟦ Vs ⟧ᵃ)) C.⟦ C.rn r ⟧))
               (ℂ.ren-cong (ℂ.≈.sym (CT.plug-tuple₀ cartRulesᶜ (σP p) (𝒥 ∘ ⟦ Vs ⟧ᵃ))) (λ _ → refl)))))
  ren-lemmaᶜ {m} {n} r (app V₁ V₂) =
    ℂ.≈.trans (ℂ.ren-cong (ℂ.sub-cong (ℂ.sub-cong ℂ.≈.refl (ℂ.≈.trans (𝒥-cong (ren-lemmaᵛ r V₁)) (𝒥-ren ⟦ V₁ ⟧ᵛ r)))
                                       (ℂ.≈.trans (𝒥-cong (ren-lemmaᵛ r V₂)) (𝒥-ren ⟦ V₂ ⟧ᵛ r))) (λ _ → refl))
    (ℂ.≈.trans (ℂ.ren-cong (ℂ.sub-cong inner ℂ.≈.refl) (λ _ → refl))
    (ℂ.≈.trans (ℂ.ren-cong (ℂ.≈.sym (ℂ.ren-sub _ _ r r idʳ)) (λ _ → refl))
    (ℂ.≈.trans (ℂ.≈.sym (ℂ.ren-∘ _ _ _))
    (ℂ.≈.trans (ℂ.ren-cong ℂ.≈.refl (contr-nat r))
               (ℂ.ren-∘ _ _ _)))))
    where
      a = 𝒥 ⟦ V₁ ⟧ᵛ
      -- ⊛{0 ⊣ a[r] ⊢ 1} ≈ (⊛{0 ⊣ a ⊢ 1})[r + id₁ + id₀]
      inner : ⊛ ℂ.⟨ 0 ⊣ a ℂ.[ r ] ⊢ 1 ⟩ ℂ.≈ (⊛ ℂ.⟨ 0 ⊣ a ⊢ 1 ⟩) ℂ.[ r +ʳ idʳ {1} +ʳ idʳ {0} ]
      inner = ℂ.≈.trans (ℂ.sub-cong (ℂ.≈.sym (ℂ.≈.trans (ℂ.ren-cong ℂ.≈.refl (λ i → trans (+ʳ-cong {r = idʳ {0}} {r' = idʳ {0}} (λ _ → refl) (+ʳ-id 1 1) i) (+ʳ-id 0 2 i))) (ℂ.ren-id ⊛))) ℂ.≈.refl)
              (ℂ.≈.trans (ℂ.≈.sym (ℂ.ren-sub ⊛ a (idʳ {0}) r (idʳ {1})))
                         (ℂ.ren-cong ℂ.≈.refl (λ i → trans (+ʳ-inj₂ (idʳ {0}) (r +ʳ idʳ {1}) i) (+ʳ-cong {r = r} {r' = r} (λ _ → refl) (λ x → sym (+ʳ-id 1 0 x)) i))))

  ren-lemmaᵃ r (V ∷ Vs) zero    = ren-lemmaᵛ r V
  ren-lemmaᵃ r (V ∷ Vs) (suc i) = ren-lemmaᵃ r Vs i

  ----------------------------------------------------------------------
  -- Lemma 4.5 (b): ⟦E{W/y}⟧ ≈ ⟦E⟧{n₁ ⊣ ⟦W⟧ ⊢ n₂}, for the
  -- disjoint-context substitution σ-ins n₁ n₂ W of the variable y at
  -- position n₁.
  ----------------------------------------------------------------------

  open import MFPS.SubCartesian ℂ using (ΔNat-word; ⊢-0-conj; cancel₂)
  open import MFPS.SubCentral ℂ using (central-word)
  open import MFPS.SubCast ℂ using (ins-arity; ins-irr; ins-conj; rn-isCast; rn-rn)
  open import MFPS.SubSym ℂ using (_⟶_)

  -- the contraction is the copy up to the arity cast
  contr-Δ : ∀ N → contr N ≗ (Δʳ N ∘ʳ (idʳ {N} +ʳ castʳ (+-identityʳ N)))
  contr-Δ N = Fin+-ext
    (λ j → trans ([,]ʳ-inl idʳ _ j) (sym (trans (cong (Δʳ N) (+ʳ-inj₁ idʳ (castʳ (+-identityʳ N)) j)) ([,]ʳ-inl idʳ idʳ j))))
    (λ j → trans ([,]ʳ-inr idʳ _ j) (sym (trans (cong (Δʳ N) (+ʳ-inj₂ idʳ (castʳ (+-identityʳ N)) j)) ([,]ʳ-inr idʳ idʳ _))))

  -- {N ⊣ h ⊢ 0} ∘ [contr N]  ≅  (N ⊣ {h}) ∘ [Δ_N]   (substitution for the last variable)
  sub!-last : ∀ N (h : ℂ.Op N)
    → C.Cong JImg (C.sub! N 0 h C.∷ C.⟦ C.rn (contr N) ⟧) ((N C.⊣ʷ CR.ηʷ h) C.++ C.⟦ C.rn (Δʳ N) ⟧)
  sub!-last N h =
    C.≅-cong {Γ₁ = C.⟦ C.sub! N 0 h ⟧} (C.≅-sym (ins-arity (+-identityʳ N) refl _ refl _ refl h)) (C.E∙ (contr-Δ N))
    ⟶ C.≅-cong {Γ₁ = X} C.≅-refl (C.≅-sym (C.R∙ _ _))
    ⟶ C.≅-≡ (sym (C.++-assoc X Y Z))
    ⟶ C.≅-≡ (cong (C._++ Z) (sym (C.⊣ʷ-++ N (CR.ηʷ h C.⊢ʷ 0) C.⟦ C.rn (castʳ (+-identityʳ N)) ⟧)))
    ⟶ C.≅-cong (⊣-stableᶜ N inner) C.≅-refl
    where
      open import MFPS.SubWhisker ℂ using () renaming (⊣-stable to ⊣-stableᶜ)
      X = N C.⊣ʷ (CR.ηʷ h C.⊢ʷ 0)
      Y = N C.⊣ʷ C.⟦ C.rn (castʳ (+-identityʳ N)) ⟧
      Z = C.⟦ C.rn (Δʳ N) ⟧
      c₂ = castʳ (sym (+-identityʳ N))
      c₃ = castʳ (+-identityʳ N)
      -- ({h} ⊢ 0) ∘ [cast] ≅ {h}
      inner : C.Cong JImg ((CR.ηʷ h C.⊢ʷ 0) C.++ C.⟦ C.rn c₃ ⟧) (CR.ηʷ h)
      inner =
        C.≅-cong (⊢-0-conj (CR.ηʷ h)) C.≅-refl
        ⟶ C.≅-∷ (C.≅-≡ (C.++-assoc (CR.ηʷ h) C.⟦ C.rn c₂ ⟧ C.⟦ C.rn c₃ ⟧))
        ⟶ C.≅-∷ (C.≅-cong {Γ₁ = CR.ηʷ h} C.≅-refl (cancel₂ {r₁ = c₂} {r₂ = c₃} (∘ʳ-isCast' c₃ c₂ (castʳ-isCast _) (castʳ-isCast _)) {C.ε}))
        ⟶ C.≅-∷ (C.≅-≡ (C.++-identityʳ (CR.ηʷ h)))
        ⟶ C.≅-cong {Γ₁ = C.⟦ C.rn (castʳ (+-identityʳ 1)) ⟧} (rn-isCast (castʳ-isCast _)) C.≅-refl

  -- the word equation behind the `let` case
  bnd-nat : ∀ n₁ n₂ {m} (jw : ℂ.Op m) (jc : JImg jw) (g₂ : ℂ.Op (n₁ + suc n₂))
    → C.Cong JImg
        (C.rn (castʳ (E₁ n₁ n₂)) C.∷ C.sub! n₁ (n₂ + 1) jw C.∷ C.rn (castʳ (P₁ n₁ m n₂)) C.∷ C.sub! (n₁ + (m + n₂)) 0 (g₂ C.⋆ C.⟦ C.sub! n₁ n₂ jw ⟧) C.∷ C.⟦ C.rn (contr (n₁ + (m + n₂))) ⟧)
        (C.sub! (n₁ + suc n₂) 0 g₂ C.∷ C.rn (contr (n₁ + suc n₂)) C.∷ C.⟦ C.sub! n₁ n₂ jw ⟧)
  bnd-nat n₁ n₂ {m} jw jc g₂ = C.≅-sym
    ( C.≅-cong {Γ₁ = C.sub! N 0 g₂ C.∷ C.⟦ C.rn (contr N) ⟧} (sub!-last N g₂) C.≅-refl
    ⟶ C.≅-≡ (C.++-assoc (N C.⊣ʷ CR.ηʷ g₂) C.⟦ C.rn (Δʳ N) ⟧ JT)
    ⟶ C.≅-cong {Γ₁ = N C.⊣ʷ CR.ηʷ g₂} C.≅-refl (ΔNat-word JT (jc , tt))
    ⟶ C.≅-≡ (sym (C.++-assoc (N C.⊣ʷ CR.ηʷ g₂) (JT C.⊢ʷ N) ((N' C.⊣ʷ JT) C.++ C.⟦ C.rn (Δʳ N') ⟧)))
    ⟶ C.≅-cong (C.≅-sym (proj₁ (central-word JT (jc , tt) (CR.ηʷ g₂)))) C.≅-refl
    ⟶ C.≅-≡ (trans (C.++-assoc (JT C.⊢ʷ 1) (N' C.⊣ʷ CR.ηʷ g₂) ((N' C.⊣ʷ JT) C.++ C.⟦ C.rn (Δʳ N') ⟧)) (cong ((JT C.⊢ʷ 1) C.++_) (sym (C.++-assoc (N' C.⊣ʷ CR.ηʷ g₂) (N' C.⊣ʷ JT) C.⟦ C.rn (Δʳ N') ⟧))))
    ⟶ C.≅-cong {Γ₁ = JT C.⊢ʷ 1} C.≅-refl (C.≅-cong (C.≅-≡ (sym (C.⊣ʷ-++ N' (CR.ηʷ g₂) JT))) C.≅-refl)
    ⟶ C.≅-cong {Γ₁ = JT C.⊢ʷ 1} C.≅-refl (C.≅-cong (⊣-stableᶜ N' (C.≅-sym (CR.η-nat g₂ JT))) C.≅-refl)
    ⟶ C.≅-cong {Γ₁ = JT C.⊢ʷ 1} C.≅-refl (C.≅-sym (sub!-last N' (g₂ C.⋆ JT)))
    ⟶ C.≅-cong {Γ₁ = JT C.⊢ʷ 1} (C.≅-≡ (cong C.⟦_⟧ (ins-irr n₁ (n₂ + 1) (C.Rp n₁ m n₂ 1 refl) (sym (P₁ n₁ m n₂)) (C.Rq n₁ n₂ 1 refl) (E₁ n₁ n₂) jw))
                                   ⟶ C.≅-sym (ins-conj n₁ (n₂ + 1) refl refl (sym (P₁ n₁ m n₂)) (E₁ n₁ n₂) jw (castʳ-isCast (E₁ n₁ n₂)) (castʳ-isCast (P₁ n₁ m n₂)))) C.≅-refl )
    where
      open import MFPS.SubWhisker ℂ using () renaming (⊣-stable to ⊣-stableᶜ)
      N = n₁ + suc n₂
      N' = n₁ + (m + n₂)
      JT = C.⟦ C.sub! n₁ n₂ jw ⟧

  -- the word equation behind the application case
  app-nat : ∀ n₁ n₂ {m} (jw : ℂ.Op m) (jc : JImg jw) (a b : ℂ.Op (n₁ + suc n₂))
    → C.Cong JImg
        (C.sub! 0 1 (a C.⋆ C.⟦ C.sub! n₁ n₂ jw ⟧) C.∷ C.sub! (n₁ + (m + n₂)) 0 (b C.⋆ C.⟦ C.sub! n₁ n₂ jw ⟧) C.∷ C.⟦ C.rn (contr (n₁ + (m + n₂))) ⟧)
        (C.sub! 0 1 a C.∷ C.sub! (n₁ + suc n₂) 0 b C.∷ C.rn (contr (n₁ + suc n₂)) C.∷ C.⟦ C.sub! n₁ n₂ jw ⟧)
  app-nat n₁ n₂ {m} jw jc a b = C.≅-sym
    ( C.≅-∷ (C.≅-cong {Γ₁ = C.sub! N 0 b C.∷ C.⟦ C.rn (contr N) ⟧} (sub!-last N b) C.≅-refl)
    ⟶ C.≅-∷ (C.≅-≡ (C.++-assoc (N C.⊣ʷ CR.ηʷ b) C.⟦ C.rn (Δʳ N) ⟧ JT))
    ⟶ C.≅-∷ (C.≅-cong {Γ₁ = N C.⊣ʷ CR.ηʷ b} C.≅-refl (ΔNat-word JT (jc , tt)))
    ⟶ C.≅-∷ (C.≅-≡ (sym (C.++-assoc (N C.⊣ʷ CR.ηʷ b) (JT C.⊢ʷ N) ((N' C.⊣ʷ JT) C.++ C.⟦ C.rn (Δʳ N') ⟧))))
    ⟶ C.≅-∷ (C.≅-cong (C.≅-sym (proj₁ (central-word JT (jc , tt) (CR.ηʷ b)))) C.≅-refl)
    ⟶ C.≅-∷ (C.≅-≡ (trans (C.++-assoc (JT C.⊢ʷ 1) (N' C.⊣ʷ CR.ηʷ b) ((N' C.⊣ʷ JT) C.++ C.⟦ C.rn (Δʳ N') ⟧)) (cong ((JT C.⊢ʷ 1) C.++_) (sym (C.++-assoc (N' C.⊣ʷ CR.ηʷ b) (N' C.⊣ʷ JT) C.⟦ C.rn (Δʳ N') ⟧)))))
    ⟶ C.≅-∷ (C.≅-cong {Γ₁ = JT C.⊢ʷ 1} C.≅-refl (C.≅-cong (C.≅-≡ (sym (C.⊣ʷ-++ N' (CR.ηʷ b) JT))) C.≅-refl))
    ⟶ C.≅-∷ (C.≅-cong {Γ₁ = JT C.⊢ʷ 1} C.≅-refl (C.≅-cong (⊣-stableᶜ N' (C.≅-sym (CR.η-nat b JT))) C.≅-refl))
    ⟶ C.≅-∷ (C.≅-cong {Γ₁ = JT C.⊢ʷ 1} C.≅-refl (C.≅-sym (sub!-last N' (b C.⋆ JT))))
    ⟶ C.≅-cong {Γ₁ = C.sub! 0 1 a C.∷ (JT C.⊢ʷ 1)}
        ( C.≅-cong {Γ₁ = C.⟦ C.sub! 0 1 a ⟧} (C.≅-≡ (cong C.⟦_⟧ (ins-irr 0 1 refl (C.Rp 0 N 0 1 (sym (+-identityʳ N))) refl (C.Rq 0 0 1 refl) a))) C.≅-refl
        ⟶ C.≅-≡ (sym (C.⊢ʷ-++ (CR.ηʷ a) JT 1))
        ⟶ ⊢-stableᶜ 1 (C.≅-sym (CR.η-nat a JT))
        ⟶ C.≅-≡ (cong C.⟦_⟧ (ins-irr 0 1 (C.Rp 0 N' 0 1 (sym (+-identityʳ N'))) refl (C.Rq 0 0 1 refl) refl (a C.⋆ JT))) ) C.≅-refl )
    where
      open import MFPS.SubWhisker ℂ using () renaming (⊣-stable to ⊣-stableᶜ; ⊢-stable to ⊢-stableᶜ)
      N = n₁ + suc n₂
      N' = n₁ + (m + n₂)
      JT = C.⟦ C.sub! n₁ n₂ jw ⟧

  -- the word equations with an extra renaming r : k → n₁+1+n₂ of the
  -- context (needed to make the induction structural)
  bnd-natʳ : ∀ n₁ n₂ {m k} (jw : ℂ.Op m) (jc : JImg jw) (r : Ren k (n₁ + suc n₂)) (g₂ : ℂ.Op k)
    → C.Cong JImg
        (C.rn (castʳ (E₁ n₁ n₂) ∘ʳ liftʳ r) C.∷ C.sub! n₁ (n₂ + 1) jw C.∷ C.rn (castʳ (P₁ n₁ m n₂)) C.∷ C.sub! (n₁ + (m + n₂)) 0 ((g₂ ℂ.[ r ]) C.⋆ C.⟦ C.sub! n₁ n₂ jw ⟧) C.∷ C.⟦ C.rn (contr (n₁ + (m + n₂))) ⟧)
        (C.sub! k 0 g₂ C.∷ C.rn (contr k) C.∷ C.rn r C.∷ C.⟦ C.sub! n₁ n₂ jw ⟧)
  bnd-natʳ n₁ n₂ {m} {k} jw jc r g₂ = C.≅-sym
    ( C.≅-∷ (C.≅-cong {Γ₁ = C.rn (contr k) C.∷ C.⟦ C.rn r ⟧} (C.R∙ _ _ ⟶ C.E∙ (λ i → sym (contr-nat r i)) ⟶ C.≅-sym (C.R∙ (r +ʳ r +ʳ idʳ) (contr _))) C.≅-refl)
    ⟶ C.≅-cong {Γ₁ = C.sub! k 0 g₂ C.∷ C.⟦ C.rn (r +ʳ r +ʳ idʳ) ⟧} (C.N∙ g₂ r r idʳ) C.≅-refl
    ⟶ C.≅-∷ (C.≅-sym (bnd-nat n₁ n₂ jw jc (g₂ ℂ.[ r ])))
    ⟶ rn-rn _ _
    ⟶ C.≅-∷ˡ (C.E∙ (λ i → cong (castʳ (E₁ n₁ n₂)) (+ʳ-cong {r = r} {r' = r} (λ _ → refl) (+ʳ-id 1 0) i))) )

  app-natʳ : ∀ n₁ n₂ {m k} (jw : ℂ.Op m) (jc : JImg jw) (r : Ren k (n₁ + suc n₂)) (a b : ℂ.Op k)
    → C.Cong JImg
        (C.sub! 0 1 ((a ℂ.[ r ]) C.⋆ C.⟦ C.sub! n₁ n₂ jw ⟧) C.∷ C.sub! (n₁ + (m + n₂)) 0 ((b ℂ.[ r ]) C.⋆ C.⟦ C.sub! n₁ n₂ jw ⟧) C.∷ C.⟦ C.rn (contr (n₁ + (m + n₂))) ⟧)
        (C.sub! 0 1 a C.∷ C.sub! k 0 b C.∷ C.rn (contr k) C.∷ C.rn r C.∷ C.⟦ C.sub! n₁ n₂ jw ⟧)
  app-natʳ n₁ n₂ {m} {k} jw jc r a b = C.≅-sym
    ( C.≅-∷ (C.≅-∷ (C.≅-cong {Γ₁ = C.rn (contr k) C.∷ C.⟦ C.rn r ⟧} (C.R∙ _ _ ⟶ C.E∙ (λ i → sym (contr-nat r i)) ⟶ C.≅-sym (C.R∙ (r +ʳ r +ʳ idʳ) (contr _))) C.≅-refl))
    ⟶ C.≅-∷ (C.≅-cong {Γ₁ = C.sub! k 0 b C.∷ C.⟦ C.rn (r +ʳ r +ʳ idʳ) ⟧} (C.N∙ b r r idʳ) C.≅-refl)
    ⟶ C.≅-∷ (C.≅-∷ˡ (C.E∙ (λ i → trans (+ʳ-cong {r = r} {r' = r} (λ _ → refl) (+ʳ-id 1 0) i) (sym (+ʳ-inj₂ (idʳ {0}) (r +ʳ idʳ {1}) i)))))
    ⟶ C.≅-cong {Γ₁ = C.sub! 0 1 a C.∷ C.⟦ C.rn (idʳ {0} +ʳ r +ʳ idʳ {1}) ⟧} (C.N∙ a (idʳ {0}) r (idʳ {1})) C.≅-refl
    ⟶ C.≅-cong {Γ₁ = C.⟦ C.rn (idʳ {0} +ʳ idʳ {1} +ʳ idʳ {1}) ⟧} (C.E∙ (λ i → trans (+ʳ-cong {r = idʳ {0}} {r' = idʳ {0}} (λ _ → refl) (+ʳ-id 1 1) i) (+ʳ-id 0 2 i)) ⟶ C.U₂∙) C.≅-refl
    ⟶ C.≅-sym (app-nat n₁ n₂ jw jc (a ℂ.[ r ]) (b ℂ.[ r ])) )

  -- id{0 ⊣ w ⊢ 0} ≈ w[cast]  (the left unit law, unbundled)
  lunit-ren : (w : 𝕍.Op m) → 𝕍.idₒ 𝕍.⟨ 0 ⊣ w ⊢ 0 ⟩ 𝕍.≈ w 𝕍.[ castʳ (sym (+-identityʳ m)) ]
  lunit-ren {m} w =
    𝕍.≈.trans (𝕍.≈.reflexive (sym (subst-cancel-sym 𝕍.Op (+-identityʳ m) _)))
    (𝕍.≈.trans (𝕍.subst-cong (sym (+-identityʳ m)) (𝕍.lunit w (+-identityʳ m))) (𝕍.subst-ren (sym (+-identityʳ m)) w))

  -- the variable case: substituting for a variable of the context
  var-sub : ∀ n₁ n₂ (W : Val m) (i : Fin (n₁ + suc n₂)) → ⟦ σ-ins n₁ n₂ W i ⟧ᵛ 𝕍.≈ (𝕍.idₒ 𝕍.[ ptʳ i ]) 𝕍.⟨ n₁ ⊣ ⟦ W ⟧ᵛ ⊢ n₂ ⟩
  var-sub {m} n₁ n₂ W = Fin-ins-cases n₁ n₂ (λ i → ⟦ σ-ins n₁ n₂ W i ⟧ᵛ 𝕍.≈ (𝕍.idₒ 𝕍.[ ptʳ i ]) 𝕍.⟨ n₁ ⊣ w ⊢ n₂ ⟩) c₁ c₂ c₃
    where
      w = ⟦ W ⟧ᵛ
      D₁ = idʳ {n₁} +ʳ !ʳ 1 +ʳ idʳ {n₂}
      Dₘ = idʳ {n₁} +ʳ !ʳ m +ʳ idʳ {n₂}
      -- a variable outside the hole: discard the hole (Def. 3.7 (i))
      discard : (x : Fin (n₁ + n₂)) (y : Fin (n₁ + suc n₂)) (z : Fin (n₁ + (m + n₂))) → D₁ x ≡ y → Dₘ x ≡ z
        → 𝕍.idₒ 𝕍.[ ptʳ z ] 𝕍.≈ (𝕍.idₒ 𝕍.[ ptʳ y ]) 𝕍.⟨ n₁ ⊣ w ⊢ n₂ ⟩
      discard x y z e₁ e₂ =
        𝕍.≈.trans (𝕍.ren-cong 𝕍.≈.refl (λ _ → sym e₂))
        (𝕍.≈.trans (𝕍.ren-∘ 𝕍.idₒ (ptʳ x) Dₘ)
        (𝕍.≈.trans (𝕍.≈.sym (𝕍.!-nat (𝕍.idₒ 𝕍.[ ptʳ x ]) w))
                   (𝕍.sub-cong (𝕍.≈.trans (𝕍.≈.sym (𝕍.ren-∘ 𝕍.idₒ (ptʳ x) D₁)) (𝕍.ren-cong 𝕍.≈.refl (λ _ → e₁))) 𝕍.≈.refl)))
      c₁ : ∀ j → ⟦ σ-ins n₁ n₂ W (j ↑ˡ suc n₂) ⟧ᵛ 𝕍.≈ (𝕍.idₒ 𝕍.[ ptʳ (j ↑ˡ suc n₂) ]) 𝕍.⟨ n₁ ⊣ w ⊢ n₂ ⟩
      c₁ j = 𝕍.≈.trans (𝕍.≈.reflexive (cong ⟦_⟧ᵛ (σ-ins-₁ n₁ n₂ W j)))
               (discard (j ↑ˡ n₂) _ _ (+ʳ-inj₁ (idʳ {n₁}) (!ʳ 1 +ʳ idʳ) j) (+ʳ-inj₁ (idʳ {n₁}) (!ʳ m +ʳ idʳ) j))
      c₃ : ∀ j → ⟦ σ-ins n₁ n₂ W (n₁ ↑ʳ suc j) ⟧ᵛ 𝕍.≈ (𝕍.idₒ 𝕍.[ ptʳ (n₁ ↑ʳ suc j) ]) 𝕍.⟨ n₁ ⊣ w ⊢ n₂ ⟩
      c₃ j = 𝕍.≈.trans (𝕍.≈.reflexive (cong ⟦_⟧ᵛ (σ-ins-₃ n₁ n₂ W j)))
               (discard (n₁ ↑ʳ j) _ _ (trans (+ʳ-inj₂ (idʳ {n₁}) (!ʳ 1 +ʳ idʳ) j) (cong (n₁ ↑ʳ_) (+ʳ-inj₂ (!ʳ 1) (idʳ {n₂}) j)))
                                        (trans (+ʳ-inj₂ (idʳ {n₁}) (!ʳ m +ʳ idʳ) j) (cong (n₁ ↑ʳ_) (+ʳ-inj₂ (!ʳ m) (idʳ {n₂}) j))))
      -- the hole itself: the left unit law and the renaming/substitution interchange
      c₂ : ⟦ σ-ins n₁ n₂ W (n₁ ↑ʳ zero) ⟧ᵛ 𝕍.≈ (𝕍.idₒ 𝕍.[ ptʳ (n₁ ↑ʳ zero) ]) 𝕍.⟨ n₁ ⊣ w ⊢ n₂ ⟩
      c₂ = 𝕍.≈.trans (𝕍.≈.reflexive (cong ⟦_⟧ᵛ (σ-ins-₂ n₁ n₂ W)))
           (𝕍.≈.trans (ren-lemmaᵛ _ W)
           (𝕍.≈.trans (𝕍.ren-cong 𝕍.≈.refl (λ x → toℕ-injective (trans (toℕ-ι₂ n₁ m n₂ x)
               (sym (trans (cong (toℕ ∘ (!ʳ n₁ +ʳ idʳ {m} +ʳ !ʳ n₂)) (castʳ-≡ (sym (+-identityʳ m)) x (x ↑ˡ 0) (sym (toℕ-↑ˡ x 0))))
                    (trans (cong toℕ (+ʳ-inj₂ (!ʳ n₁) (idʳ {m} +ʳ !ʳ n₂) (x ↑ˡ 0)))
                    (trans (toℕ-↑ʳ n₁ _) (cong (n₁ +_) (trans (cong toℕ (+ʳ-inj₁ (idʳ {m}) (!ʳ n₂) x)) (toℕ-↑ˡ x n₂))))))))))
           (𝕍.≈.trans (𝕍.ren-∘ w _ _)
           (𝕍.≈.trans (𝕍.ren-cong (𝕍.≈.sym (lunit-ren w)) (λ _ → refl))
           (𝕍.≈.trans (𝕍.ren-sub 𝕍.idₒ w (!ʳ n₁) idʳ (!ʳ n₂))
                      (𝕍.sub-cong (𝕍.ren-cong 𝕍.≈.refl (λ { zero → trans (+ʳ-inj₂ (!ʳ n₁) (idʳ {1} +ʳ !ʳ n₂) zero) (cong (n₁ ↑ʳ_) (+ʳ-inj₁ (idʳ {1}) (!ʳ n₂) zero)) })) (𝕍.ren-id w)))))))

  -- Lemma 4.5 (b), generalised by a renaming r of the context so that
  -- the induction is structural under binders
  sub-lemmaᵛ : ∀ n₁ n₂ (W : Val m) (r : Ren k (n₁ + suc n₂)) (V : Val k)
    → ⟦ sub (σ-ins n₁ n₂ W ∘ r) V ⟧ᵛ 𝕍.≈ (⟦ V ⟧ᵛ 𝕍.[ r ]) 𝕍.⟨ n₁ ⊣ ⟦ W ⟧ᵛ ⊢ n₂ ⟩
  sub-lemmaᶜ : ∀ n₁ n₂ (W : Val m) (r : Ren k (n₁ + suc n₂)) (M : Cmp k)
    → ⟦ sub (σ-ins n₁ n₂ W ∘ r) M ⟧ᶜ ℂ.≈ (⟦ M ⟧ᶜ ℂ.[ r ]) ℂ.⟨ n₁ ⊣ 𝒥 ⟦ W ⟧ᵛ ⊢ n₂ ⟩
  sub-lemmaᵃ : ∀ n₁ n₂ (W : Val m) (r : Ren k (n₁ + suc n₂)) {j} (Vs : Args k j) (i : Fin j)
    → ⟦ subA (σ-ins n₁ n₂ W ∘ r) Vs ⟧ᵃ i 𝕍.≈ (⟦ Vs ⟧ᵃ i 𝕍.[ r ]) 𝕍.⟨ n₁ ⊣ ⟦ W ⟧ᵛ ⊢ n₂ ⟩

  -- the substituted computation, lifted under a binder
  sub-lift : ∀ n₁ n₂ (W : Val m) (r : Ren k (n₁ + suc n₂)) (M : Cmp (k + 1))
    → ⟦ sub (liftˢ (σ-ins n₁ n₂ W ∘ r)) M ⟧ᶜ ℂ.≈ ((⟦ M ⟧ᶜ ℂ.[ castʳ (E₁ n₁ n₂) ∘ʳ liftʳ r ]) ℂ.⟨ n₁ ⊣ 𝒥 ⟦ W ⟧ᵛ ⊢ n₂ + 1 ⟩) ℂ.[ castʳ (P₁ n₁ m n₂) ]
  sub-lift {m} n₁ n₂ W r M =
    ℂ.≈.trans (ℂ.≈.reflexive (cong ⟦_⟧ᶜ (trans (sub-cong (liftˢ-∘ʳ r (σ-ins n₁ n₂ W)) M) (trans (sym (sub-ren (liftʳ r) (liftˢ (σ-ins n₁ n₂ W)) M)) (trans (liftˢ-σ-ins n₁ n₂ W (ren (liftʳ r) M)) (cong (ren (castʳ (P₁ n₁ m n₂))) (trans (cong (sub (σ-ins n₁ (n₂ + 1) W)) (sym (ren-∘ (liftʳ r) (castʳ (E₁ n₁ n₂)) M))) (sub-ren (castʳ (E₁ n₁ n₂) ∘ʳ liftʳ r) (σ-ins n₁ (n₂ + 1) W) M))))))))
    (ℂ.≈.trans (ren-lemmaᶜ (castʳ (P₁ n₁ m n₂)) (sub (σ-ins n₁ (n₂ + 1) W ∘ (castʳ (E₁ n₁ n₂) ∘ʳ liftʳ r)) M))
               (ℂ.ren-cong (sub-lemmaᶜ n₁ (n₂ + 1) W (castʳ (E₁ n₁ n₂) ∘ʳ liftʳ r) M) (λ _ → refl)))

  sub-lemmaᵛ n₁ n₂ W r (var i) =
    𝕍.≈.trans (var-sub n₁ n₂ W (r i)) (𝕍.sub-cong (𝕍.≈.trans (𝕍.ren-cong 𝕍.≈.refl (λ _ → refl)) (𝕍.ren-∘ 𝕍.idₒ (ptʳ i) r)) 𝕍.≈.refl)
  sub-lemmaᵛ {m} n₁ n₂ W r (fun {k} f Vs) =
    𝕍.≈.trans (VT.plug-tuple₀ cartRulesᵥ (σF f) ⟦ subA (σ-ins n₁ n₂ W ∘ r) Vs ⟧ᵃ)
    (𝕍.≈.trans (⋆-soundᵛ (VT.tuple-cong (sub-lemmaᵃ n₁ n₂ W r Vs)) (σF f))
    (𝕍.≈.trans (⋆-soundᵛ (VT.tuple-nat ⟦ Vs ⟧ᵃ (V.rn r V.∷ V.⟦ V.sub! n₁ n₂ ⟦ W ⟧ᵛ ⟧) (tt , tt)) (σF f))
    (𝕍.≈.trans (𝕍.≈.reflexive (V.⋆-++ (σF f) (VT.tupleʷ ⟦ Vs ⟧ᵃ) (V.rn r V.∷ V.⟦ V.sub! n₁ n₂ ⟦ W ⟧ᵛ ⟧)))
               (𝕍.sub-cong (𝕍.ren-cong (𝕍.≈.sym (VT.plug-tuple₀ cartRulesᵥ (σF f) ⟦ Vs ⟧ᵃ)) (λ _ → refl)) 𝕍.≈.refl))))
  sub-lemmaᵛ {m} n₁ n₂ W r (lam M) =
    𝕍.≈.trans (abs-cong (ℂ.≈.trans (sub-lift n₁ n₂ W r M) (ℂ.ren-subst (P₁ n₁ m n₂) _)))
    (𝕍.≈.trans (abs-sub (⟦ M ⟧ᶜ ℂ.[ castʳ (E₁ n₁ n₂) ∘ʳ liftʳ r ]) ⟦ W ⟧ᵛ (P₁ n₁ m n₂) (sym (E₁ n₁ n₂)))
    (𝕍.sub-cong (𝕍.≈.trans (abs-cong (ℂ.≈.trans (ℂ.subst-ren _ _) (ℂ.≈.trans (ℂ.≈.sym (ℂ.ren-∘ _ _ _)) (ℂ.ren-cong ℂ.≈.refl (λ i → trans (castʳ-∘ (E₁ n₁ n₂) (sym (E₁ n₁ n₂)) _) (castʳ-refl (trans (E₁ n₁ n₂) (sym (E₁ n₁ n₂))) _))))))
                            (abs-ren ⟦ M ⟧ᶜ r)) 𝕍.≈.refl))

  sub-lemmaᶜ n₁ n₂ W r (ret V) =
    ℂ.≈.trans (𝒥-cong (sub-lemmaᵛ n₁ n₂ W r V)) (ℂ.≈.trans (𝒥-sub _ ⟦ W ⟧ᵛ) (ℂ.sub-cong (𝒥-ren ⟦ V ⟧ᵛ r) ℂ.≈.refl))
  sub-lemmaᶜ {m} n₁ n₂ W r (bnd M₂ M₁) =
    ℂ.≈.trans (ℂ.ren-cong (ℂ.sub-cong (sub-lift n₁ n₂ W r M₁) (sub-lemmaᶜ n₁ n₂ W r M₂)) (λ _ → refl))
              (⋆-soundᶜ (bnd-natʳ n₁ n₂ (𝒥 ⟦ W ⟧ᵛ) (⟦ W ⟧ᵛ , refl) r ⟦ M₂ ⟧ᶜ) ⟦ M₁ ⟧ᶜ)
  sub-lemmaᶜ {m} n₁ n₂ W r (prc {k} p Vs) =
    ℂ.≈.trans (CT.plug-tuple₀ cartRulesᶜ (σP p) (𝒥 ∘ ⟦ subA (σ-ins n₁ n₂ W ∘ r) Vs ⟧ᵃ))
    (ℂ.≈.trans (⋆-soundᶜ (CT.tuple-cong (λ i → ℂ.≈.trans (𝒥-cong (sub-lemmaᵃ n₁ n₂ W r Vs i)) (ℂ.≈.trans (𝒥-sub _ ⟦ W ⟧ᵛ) (ℂ.sub-cong (𝒥-ren (⟦ Vs ⟧ᵃ i) r) ℂ.≈.refl)))) (σP p))
    (ℂ.≈.trans (⋆-soundᶜ (CT.tuple-nat (𝒥 ∘ ⟦ Vs ⟧ᵃ) (C.rn r C.∷ C.⟦ C.sub! n₁ n₂ (𝒥 ⟦ W ⟧ᵛ) ⟧) ((⟦ W ⟧ᵛ , refl) , tt)) (σP p))
    (ℂ.≈.trans (ℂ.≈.reflexive (C.⋆-++ (σP p) (CT.tupleʷ (𝒥 ∘ ⟦ Vs ⟧ᵃ)) (C.rn r C.∷ C.⟦ C.sub! n₁ n₂ (𝒥 ⟦ W ⟧ᵛ) ⟧)))
               (ℂ.sub-cong (ℂ.ren-cong (ℂ.≈.sym (CT.plug-tuple₀ cartRulesᶜ (σP p) (𝒥 ∘ ⟦ Vs ⟧ᵃ))) (λ _ → refl)) ℂ.≈.refl))))
  sub-lemmaᶜ {m} n₁ n₂ W r (app V₁ V₂) =
    ℂ.≈.trans (ℂ.ren-cong (ℂ.sub-cong (ℂ.sub-cong ℂ.≈.refl (ℂ.≈.trans (𝒥-cong (sub-lemmaᵛ n₁ n₂ W r V₁)) (ℂ.≈.trans (𝒥-sub _ ⟦ W ⟧ᵛ) (ℂ.sub-cong (𝒥-ren ⟦ V₁ ⟧ᵛ r) ℂ.≈.refl))))
                                       (ℂ.≈.trans (𝒥-cong (sub-lemmaᵛ n₁ n₂ W r V₂)) (ℂ.≈.trans (𝒥-sub _ ⟦ W ⟧ᵛ) (ℂ.sub-cong (𝒥-ren ⟦ V₂ ⟧ᵛ r) ℂ.≈.refl)))) (λ _ → refl))
              (⋆-soundᶜ (app-natʳ n₁ n₂ (𝒥 ⟦ W ⟧ᵛ) (⟦ W ⟧ᵛ , refl) r (𝒥 ⟦ V₁ ⟧ᵛ) (𝒥 ⟦ V₂ ⟧ᵛ)) ⊛)

  sub-lemmaᵃ n₁ n₂ W r (V ∷ Vs) zero    = sub-lemmaᵛ n₁ n₂ W r V
  sub-lemmaᵃ n₁ n₂ W r (V ∷ Vs) (suc i) = sub-lemmaᵃ n₁ n₂ W r Vs i

  -- Lemma 4.5 (b) as stated in the paper: r = id
  sub-lemmaᵛ₀ : ∀ n₁ n₂ (W : Val m) (V : Val (n₁ + suc n₂)) → ⟦ sub (σ-ins n₁ n₂ W) V ⟧ᵛ 𝕍.≈ ⟦ V ⟧ᵛ 𝕍.⟨ n₁ ⊣ ⟦ W ⟧ᵛ ⊢ n₂ ⟩
  sub-lemmaᵛ₀ n₁ n₂ W V = 𝕍.≈.trans (sub-lemmaᵛ n₁ n₂ W idʳ V) (𝕍.sub-cong (𝕍.ren-id ⟦ V ⟧ᵛ) 𝕍.≈.refl)

  sub-lemmaᶜ₀ : ∀ n₁ n₂ (W : Val m) (M : Cmp (n₁ + suc n₂)) → ⟦ sub (σ-ins n₁ n₂ W) M ⟧ᶜ ℂ.≈ ⟦ M ⟧ᶜ ℂ.⟨ n₁ ⊣ 𝒥 ⟦ W ⟧ᵛ ⊢ n₂ ⟩
  sub-lemmaᶜ₀ n₁ n₂ W M = ℂ.≈.trans (sub-lemmaᶜ n₁ n₂ W idʳ M) (ℂ.sub-cong (ℂ.ren-id ⟦ M ⟧ᶜ) ℂ.≈.refl)

  ----------------------------------------------------------------------
  -- Lemma 4.5 (b) in the shared-context form of MFPS.Semantics:
  --   ⟦E[W]⟧ ≈ (⟦E⟧{n ⊣ ⟦W⟧ ⊢ 0})[contr n]
  -- since E[W] is the disjoint-context substitution followed by the
  -- contraction of the two copies of the context.
  ----------------------------------------------------------------------

  -- (idˢ ∷ˢ W) = [contr n] ∘ σ-ins n 0 W, pointwise
  ∷ˢ-σ-ins : ∀ n (W : Val n) (E : Trm (n + 1) s) → E [ W ] ≡ ren (contr n) (sub (σ-ins n 0 W) E)
  ∷ˢ-σ-ins n W E = trans (sub-cong pointwise E) (sym (ren-sub _ _ E))
    where
      pointwise : (idˢ ∷ˢ W) ≗ (λ i → ren (contr n) (σ-ins n 0 W i))
      pointwise = Fin-ins-ext n 0
        (λ j → trans (∷ˢ-inl idˢ W j) (trans (cong var (sym ([,]ʳ-inl idʳ _ j))) (cong (ren (contr n)) (sym (σ-ins-₁ n 0 W j)))))
        (trans (∷ˢ-last idˢ W)
          (trans (sym (ren-id W))
          (trans (ren-cong (λ x → sym (trans ([,]ʳ-inr idʳ (castʳ (+-identityʳ n)) (x ↑ˡ 0)) (castʳ-≡ _ _ _ (toℕ-↑ˡ x 0)))) W)
          (trans (ren-∘ _ _ W) (cong (ren (contr n)) (sym (σ-ins-₂ n 0 W)))))))
        (λ ())

  subLemma : SubLemma
  subLemma =
    (λ {n} V W → 𝕍.≈.trans (𝕍.≈.reflexive (cong ⟦_⟧ᵛ (∷ˢ-σ-ins n W V)))
                 (𝕍.≈.trans (ren-lemmaᵛ (contr n) (sub (σ-ins n 0 W) V)) (𝕍.ren-cong (sub-lemmaᵛ₀ n 0 W V) (λ _ → refl)))) ,
    (λ {n} M W → ℂ.≈.trans (ℂ.≈.reflexive (cong ⟦_⟧ᶜ (∷ˢ-σ-ins n W M)))
                 (ℂ.≈.trans (ren-lemmaᶜ (contr n) (sub (σ-ins n 0 W) M)) (ℂ.ren-cong (sub-lemmaᶜ₀ n 0 W M) (λ _ → refl))))

  ----------------------------------------------------------------------
  -- The (assoc) case of Theorem 4.7.  In the shared-context
  -- presentation it is the following identity of words of Sub_ℂ
  -- (rules (A) is not even needed: the nested lets are moved past each
  -- other by (N) and the naturality of the unit {−}; the contractions
  -- are then an equation between renamings).
  ----------------------------------------------------------------------

  assoc-word : ∀ n (g₁ : ℂ.Op n) (g₂ : ℂ.Op (n + 1))
    → C.Cong JImg
        (C.sub! n 0 (g₂ C.⋆ (C.sub! n 0 g₁ C.∷ C.⟦ C.rn (contr n) ⟧)) C.∷ C.⟦ C.rn (contr n) ⟧)
        (C.rn wk₁ C.∷ C.sub! (n + 1) 0 g₂ C.∷ C.rn (contr (n + 1)) C.∷ C.sub! n 0 g₁ C.∷ C.⟦ C.rn (contr n) ⟧)
  assoc-word n g₁ g₂ =
    sub!-last n (g₂ C.⋆ W₁)
    ⟶ C.≅-cong (⊣-stableᶜ n (CR.η-nat g₂ W₁)) C.≅-refl
    ⟶ C.≅-≡ (cong (C._++ C.⟦ C.rn (Δʳ n) ⟧) (C.⊣ʷ-++ n (CR.ηʷ g₂) W₁))
    ⟶ C.≅-≡ (C.++-assoc (n C.⊣ʷ CR.ηʷ g₂) (n C.⊣ʷ W₁) _)
    ⟶ C.≅-cong (ins-arity (+-identityʳ n) refl _ P' _ refl g₂ ⟶ C.≅-sym (ins-conjʳ n 0 refl refl P' g₂ (castʳ-isCast (sym P')))) C.≅-refl
    ⟶ C.≅-∷ (C.≅-∷ (C.≅-cong (C.S∙ (n + n) 0 P₂ Q₂ g₁) C.≅-refl))
    ⟶ C.≅-∷ (rn-rn _ _)
    ⟶ C.≅-∷ (C.≅-∷ˡ (rn-isCast-unique (∘ʳ-isCast' (castʳ Q₂) (castʳ (sym P')) (castʳ-isCast _) (castʳ-isCast _)) (castʳ-isCast c)))
    ⟶ C.≅-∷ (C.≅-∷ (C.≅-∷ (rn-rn _ _ ⟶ rn-rn _ _ ⟶ C.E∙ tail-eq ⟶ C.≅-sym (rn-rn _ _))))
    ⟶ C.≅-∷ (C.≅-∷ (C.≅-cong {Γ₁ = C.sub! (n + n) 0 g₁ C.∷ C.⟦ C.rn (Δʳ n +ʳ idʳ {n} +ʳ idʳ {0}) ⟧} (C.N∙ g₁ (Δʳ n) (idʳ {n}) (idʳ {0})) C.≅-refl))
    ⟶ C.≅-∷ (C.≅-∷ (C.≅-∷ (C.≅-∷ˡ (C.I∙ n 0 refl refl (ℂ.ren-id g₁)))))
    ⟶ C.≅-∷ (rn-rn _ _)
    ⟶ C.≅-∷ (C.≅-∷ˡ (C.E∙ (λ i → sym (R₁-eq i))))
    ⟶ C.≅-∷ (C.≅-sym (rn-rn (wkʳ +ʳ idʳ {n + 1} +ʳ idʳ {0}) (contr (n + 1))))
    ⟶ C.≅-cong {Γ₁ = C.sub! n 0 g₂ C.∷ C.⟦ C.rn (wkʳ +ʳ idʳ {n + 1} +ʳ idʳ {0}) ⟧} (C.N∙ g₂ wkʳ (idʳ {n + 1}) (idʳ {0})) C.≅-refl
    ⟶ C.≅-∷ (C.≅-∷ˡ (C.I∙ (n + 1) 0 refl refl (ℂ.ren-id g₂)))
    ⟶ C.≅-∷ˡ (C.E∙ (λ i → +ʳ-cong {r = _↑ˡ 1} {r' = _↑ˡ 1} (λ _ → refl) (+ʳ-id 1 0) i))
    where
      open import MFPS.SubWhisker ℂ using () renaming (⊣-stable to ⊣-stableᶜ)
      open import MFPS.SubCast ℂ using (ins-conjʳ; rn-isCast-unique)
      W₁ = C.sub! n 0 g₁ C.∷ C.⟦ C.rn (contr n) ⟧
      -- the weakening renaming n → n + 1 (source arity made explicit)
      wkʳ : Ren n (n + 1)
      wkʳ = _↑ˡ 1
      P' : n + (n + 1) ≡ n + ((n + 1) + 0)
      P' = cong (n +_) (sym (+-identityʳ (n + 1)))
      P₂ : n + (n + (n + 0)) ≡ (n + n) + (n + 0)
      P₂ = C.Lp n n {n + (n + 0)} {n + 0} refl
      Q₂ : n + (n + 1) ≡ (n + n) + suc 0
      Q₂ = C.Lp n n {n + 1} {1} refl
      c : n + ((n + 1) + 0) ≡ (n + n) + (1 + 0)
      c = trans (cong (n +_) (+-identityʳ (n + 1))) (trans (sym (+-assoc n n 1)) (cong ((n + n) +_) (sym (+-identityʳ 1))))
      -- the two contractions agree
      tail-eq : (Δʳ n ∘ʳ (idʳ {n} +ʳ contr n) ∘ʳ castʳ (sym P₂)) ≗ (contr n ∘ʳ (Δʳ n +ʳ idʳ {n} +ʳ idʳ {0}))
      tail-eq = Fin+-ext
        (Fin+-ext
          (λ j → toℕ-injective (begin
            toℕ (Δʳ n ((idʳ +ʳ contr n) (castʳ (sym P₂) ((j ↑ˡ n) ↑ˡ (n + 0)))))
              ≡⟨ cong (toℕ ∘ Δʳ n ∘ (idʳ +ʳ contr n)) (castʳ-≡ _ _ (j ↑ˡ (n + (n + 0))) (trans (toℕ-↑ˡ _ _) (trans (toℕ-↑ˡ j n) (sym (toℕ-↑ˡ j _))))) ⟩
            toℕ (Δʳ n ((idʳ +ʳ contr n) (j ↑ˡ (n + (n + 0)))))
              ≡⟨ cong toℕ (trans (cong (Δʳ n) (+ʳ-inj₁ idʳ (contr n) j)) ([,]ʳ-inl idʳ idʳ j)) ⟩
            toℕ j
              ≡⟨ cong toℕ (sym (trans (cong (contr n) (trans (+ʳ-inj₁ (Δʳ n) (idʳ {n} +ʳ idʳ {0}) (j ↑ˡ n)) (cong (_↑ˡ (n + 0)) ([,]ʳ-inl idʳ idʳ j)))) ([,]ʳ-inl idʳ (castʳ (+-identityʳ n)) j))) ⟩
            toℕ (contr n ((Δʳ n +ʳ idʳ {n} +ʳ idʳ {0}) ((j ↑ˡ n) ↑ˡ (n + 0)))) ∎))
          (λ j → toℕ-injective (begin
            toℕ (Δʳ n ((idʳ +ʳ contr n) (castʳ (sym P₂) ((n ↑ʳ j) ↑ˡ (n + 0)))))
              ≡⟨ cong (toℕ ∘ Δʳ n ∘ (idʳ +ʳ contr n)) (castʳ-≡ _ _ (n ↑ʳ (j ↑ˡ (n + 0))) (trans (toℕ-↑ˡ _ _) (trans (toℕ-↑ʳ n j) (sym (trans (toℕ-↑ʳ n _) (cong (n +_) (toℕ-↑ˡ j _))))))) ⟩
            toℕ (Δʳ n ((idʳ +ʳ contr n) (n ↑ʳ (j ↑ˡ (n + 0)))))
              ≡⟨ cong toℕ (trans (cong (Δʳ n) (+ʳ-inj₂ idʳ (contr n) _)) (trans ([,]ʳ-inr idʳ idʳ _) ([,]ʳ-inl idʳ _ j))) ⟩
            toℕ j
              ≡⟨ cong toℕ (sym (trans (cong (contr n) (trans (+ʳ-inj₁ (Δʳ n) (idʳ {n} +ʳ idʳ {0}) (n ↑ʳ j)) (cong (_↑ˡ (n + 0)) ([,]ʳ-inr idʳ idʳ j)))) ([,]ʳ-inl idʳ (castʳ (+-identityʳ n)) j))) ⟩
            toℕ (contr n ((Δʳ n +ʳ idʳ {n} +ʳ idʳ {0}) ((n ↑ʳ j) ↑ˡ (n + 0)))) ∎)))
        (λ y → toℕ-injective (begin
          toℕ (Δʳ n ((idʳ +ʳ contr n) (castʳ (sym P₂) ((n + n) ↑ʳ y))))
            ≡⟨ cong (toℕ ∘ Δʳ n ∘ (idʳ +ʳ contr n)) (castʳ-≡ _ _ (n ↑ʳ (n ↑ʳ y)) (trans (toℕ-↑ʳ (n + n) y) (trans (+-assoc n n (toℕ y)) (sym (trans (toℕ-↑ʳ n _) (cong (n +_) (toℕ-↑ʳ n y))))))) ⟩
          toℕ (Δʳ n ((idʳ +ʳ contr n) (n ↑ʳ (n ↑ʳ y))))
            ≡⟨ cong toℕ (trans (cong (Δʳ n) (+ʳ-inj₂ idʳ (contr n) _)) (trans ([,]ʳ-inr idʳ idʳ _) ([,]ʳ-inr idʳ _ y))) ⟩
          toℕ (castʳ (+-identityʳ n) y)
            ≡⟨ cong toℕ (sym (trans (cong (contr n) (+ʳ-inj₂ (Δʳ n) (idʳ {n} +ʳ idʳ {0}) y)) (trans ([,]ʳ-inr idʳ (castʳ (+-identityʳ n)) ((idʳ {n} +ʳ idʳ {0}) y)) (cong (castʳ (+-identityʳ n)) (+ʳ-id n 0 y))))) ⟩
          toℕ (contr n ((Δʳ n +ʳ idʳ {n} +ʳ idʳ {0}) ((n + n) ↑ʳ y))) ∎))
        where open ≡-Reasoning
      -- the renaming after the first substitution, block-diagonal for the hole
      R₁-eq : (contr (n + 1) ∘ʳ (wkʳ +ʳ idʳ {n + 1} +ʳ idʳ {0})) ≗ ((Δʳ n +ʳ idʳ {1} +ʳ idʳ {0}) ∘ʳ castʳ c)
      R₁-eq = Fin+-ext
        (λ j → toℕ-injective (begin
          toℕ (contr (n + 1) ((wkʳ +ʳ idʳ {n + 1} +ʳ idʳ {0}) (j ↑ˡ ((n + 1) + 0))))
            ≡⟨ cong toℕ (trans (cong (contr (n + 1)) (+ʳ-inj₁ wkʳ (idʳ {n + 1} +ʳ idʳ {0}) j)) ([,]ʳ-inl idʳ _ (j ↑ˡ 1))) ⟩
          toℕ (j ↑ˡ 1)
            ≡⟨ trans (toℕ-↑ˡ j 1) (sym (trans (cong toℕ (trans (cong (Δʳ n +ʳ idʳ {1} +ʳ idʳ {0}) (castʳ-≡ c _ ((j ↑ˡ n) ↑ˡ (1 + 0)) (trans (toℕ-↑ˡ j _) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ˡ j n)))))) (+ʳ-inj₁ (Δʳ n) (idʳ {1} +ʳ idʳ {0}) (j ↑ˡ n)))) (trans (toℕ-↑ˡ _ _) (cong toℕ ([,]ʳ-inl idʳ idʳ j))))) ⟩
          toℕ ((Δʳ n +ʳ idʳ {1} +ʳ idʳ {0}) (castʳ c (j ↑ˡ ((n + 1) + 0)))) ∎))
        (Fin+-ext
          (Fin+1-ext
            (λ j → toℕ-injective (begin
              toℕ (contr (n + 1) ((wkʳ +ʳ idʳ {n + 1} +ʳ idʳ {0}) (n ↑ʳ ((j ↑ˡ 1) ↑ˡ 0))))
                ≡⟨ cong toℕ (trans (cong (contr (n + 1)) (trans (+ʳ-inj₂ wkʳ (idʳ {n + 1} +ʳ idʳ {0}) _) (cong ((n + 1) ↑ʳ_) (+ʳ-inj₁ (idʳ {n + 1}) (idʳ {0}) (j ↑ˡ 1))))) (trans ([,]ʳ-inr idʳ _ _) (castʳ-≡ _ _ (j ↑ˡ 1) (toℕ-↑ˡ _ 0)))) ⟩
              toℕ (j ↑ˡ 1)
                ≡⟨ trans (toℕ-↑ˡ j 1) (sym (trans (cong toℕ (trans (cong (Δʳ n +ʳ idʳ {1} +ʳ idʳ {0}) (castʳ-≡ c _ ((n ↑ʳ j) ↑ˡ (1 + 0)) (trans (toℕ-↑ʳ n _) (trans (cong (n +_) (trans (toℕ-↑ˡ _ 0) (toℕ-↑ˡ j 1))) (sym (trans (toℕ-↑ˡ _ _) (toℕ-↑ʳ n j))))))) (+ʳ-inj₁ (Δʳ n) (idʳ {1} +ʳ idʳ {0}) (n ↑ʳ j)))) (trans (toℕ-↑ˡ _ _) (cong toℕ ([,]ʳ-inr idʳ idʳ j))))) ⟩
              toℕ ((Δʳ n +ʳ idʳ {1} +ʳ idʳ {0}) (castʳ c (n ↑ʳ ((j ↑ˡ 1) ↑ˡ 0)))) ∎))
            (toℕ-injective (begin
              toℕ (contr (n + 1) ((wkʳ +ʳ idʳ {n + 1} +ʳ idʳ {0}) (n ↑ʳ (last ↑ˡ 0))))
                ≡⟨ cong toℕ (trans (cong (contr (n + 1)) (trans (+ʳ-inj₂ wkʳ (idʳ {n + 1} +ʳ idʳ {0}) _) (cong ((n + 1) ↑ʳ_) (+ʳ-inj₁ (idʳ {n + 1}) (idʳ {0}) last)))) (trans ([,]ʳ-inr idʳ _ _) (castʳ-≡ _ _ last (toℕ-↑ˡ _ 0)))) ⟩
              toℕ (last {n})
                ≡⟨ trans (toℕ-last n) (sym (trans (cong toℕ (trans (cong (Δʳ n +ʳ idʳ {1} +ʳ idʳ {0}) (castʳ-≡ c _ ((n + n) ↑ʳ zero) (trans (toℕ-↑ʳ n _) (trans (cong (n +_) (trans (toℕ-↑ˡ _ 0) (toℕ-last n))) (trans (arithA n) (sym (toℕ-↑ʳ (n + n) zero))))))) (+ʳ-inj₂ (Δʳ n) (idʳ {1} +ʳ idʳ {0}) zero))) (trans (toℕ-↑ʳ n ((idʳ {1} +ʳ idʳ {0}) zero)) (cong (n +_) (trans (cong toℕ (+ʳ-inj₁ (idʳ {1}) (idʳ {0}) zero)) (toℕ-↑ˡ (zero {0}) 0)))))) ⟩
              toℕ ((Δʳ n +ʳ idʳ {1} +ʳ idʳ {0}) (castʳ c (n ↑ʳ (last ↑ˡ 0)))) ∎)))
          (λ ()))
        where
          open ≡-Reasoning
          arithA : ∀ n → n + (n + 0) ≡ (n + n) + 0
          arithA n = trans (cong (n +_) (+-identityʳ n)) (sym (+-identityʳ (n + n)))

  assocSound : AssocSound
  assocSound {n} M₁ M₂ M =
    ℂ.≈.trans (⋆-soundᶜ (assoc-word n ⟦ M₁ ⟧ᶜ ⟦ M₂ ⟧ᶜ) ⟦ M ⟧ᶜ)
              (ℂ.ren-cong (ℂ.sub-cong (ℂ.ren-cong (ℂ.sub-cong (ℂ.≈.sym (ren-lemmaᶜ wk₁ M)) ℂ.≈.refl) (λ _ → refl)) ℂ.≈.refl) (λ _ → refl))

  ----------------------------------------------------------------------
  -- Theorem 4.7 (Soundness), with no remaining assumptions
  ----------------------------------------------------------------------

  open Soundness subLemma assocSound public

------------------------------------------------------------------------
-- Theorem 4.7:  Γ ⊢ E₁ ≡ E₂  ⟹  ⊩ E₁ ≡ E₂
------------------------------------------------------------------------

open import MFPS.Completeness Σ using (Valid)

soundness : {E₁ E₂ : Trm n s} → E₁ ≈ E₂ → Valid E₁ E₂
soundness e S = Lemma45.sound S e
