------------------------------------------------------------------------
-- Section 4.3, Theorem 4.9 (Initiality): the term model is the initial
-- λml*-structure.
--
-- For every λml*-structure S:
--
--   * existence (`interp`): the interpretation ⟦−⟧ of Def. 4.4 is a
--     morphism of structures termStructure → S, i.e. a Freyd operad
--     functor (Def. 3.9) that is closed (Def. 4.2) and preserves the
--     symbol assignments;
--   * uniqueness (`unique`): any morphism G : termStructure → S agrees
--     with ⟦−⟧ on every term.
--
-- Proof in words.
--
-- Existence.  The functor laws are the substitution lemmas of
-- Lemma 4.5 (MFPS.SubstLemma): renaming (`ren-lemma`) and value
-- substitution (`sub-lemma₀`) are preserved.  Composition of
-- computations, [M₁]{n₁ ⊣ [M₂] ⊢ n₂} = [let y ⇐ M₂[ι₂] in M₁[ρ]], is
-- the one case that the paper attributes to "the interaction of the
-- let case with the exchange rule": after the renaming lemma the
-- interpretation is ⟦M₁⟧ ⋆ ([ρ] ; {N ⊣ ⟦M₂⟧[ι₂] ⊢ 0} ; [contr N]) in
-- Sub_ℂ, and the word equation `hole-move` rewrites this word to the
-- single step {n₁ ⊣ ⟦M₂⟧ ⊢ n₂}: the renamings are pushed through the
-- substitution step by (N), which leaves a pure exchange — moving the
-- hole to the end and the substituted block back to the middle — that
-- is the general naturality of the symmetry (`natLk`, Prop. 3.14).
-- The identities are preserved because ⟦x⟧ = id[pt x] = id and
-- ⟦return x⟧ = J id = id; J is preserved on the nose; abstraction is
-- preserved on the nose; application is preserved because
-- ⟦x₁ x₂⟧ = ((⊛{J id[pt 1] ⊢ 1}){2 ⊣ J id[pt 2] ⊢ 0})[contr 2] and the
-- two unit substitutions cancel by (U₁) and (N) (`app-word`).  The
-- symbols are preserved because ⟦f(x₁,…,xₙ)⟧ = plug σF(f) ⟨id[pt i]⟩[Δⁿ]
-- and the tuple of projections is the identity word (`tuple-pt`).
--
-- Uniqueness.  By induction on the term, using that a morphism G
-- preserves every operation out of which the term model is built:
-- a term E is provably equal to its own interpretation in the term
-- model (`term-interp`, MFPS.Completeness), which is a composite of
-- symbol assignments, plug, substitution, renaming, J, abs, app; G
-- preserves each of these (`F-plug` for plug), so G E is the same
-- composite in S, which is ⟦E⟧.
--
-- Paper ↔ code:
--   Thm. 4.9 (existence)   `interp   : StructureMorphism termStructure S`
--   Thm. 4.9 (uniqueness)  `unique   : (G : StructureMorphism termStructure S) → …`
--   category FreydOp_S     `StructureMorphism` (MFPS.Semantics)
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad
open import MFPS.Syntax

module MFPS.Initiality (Σ : Signature) where

open Signature Σ
open Terms Σ
open import MFPS.Theory Σ using (_≈_; ≈-sym; ≈-trans)
open import MFPS.Semantics Σ
open import MFPS.TermModel Σ using (ι₁; ι₂; ι₃; ρ-ins; subᵛ; subᶜ; Fin-ins-ext)
open import MFPS.TermLaws Σ using (termStructure; vars; toℕ-ι₁; toℕ-ι₂; toℕ-ι₃; toℕ-ρ-ins-₁; toℕ-ρ-ins-₂; toℕ-ρ-ins-₃)
open import MFPS.Completeness Σ using (term-interpᵛ; term-interpᶜ)
open import MFPS.SubstLemma Σ using (module Lemma45)

private
  variable
    k m n : ℕ
    s : Sort

------------------------------------------------------------------------
-- A preoperad functor preserves the iterated substitution `plug`
------------------------------------------------------------------------

module _ {C₁ C₂ : Preoperad} (G : PreoperadFunctor C₁ C₂) where
  private
    module C₁ = Preoperad C₁
    module C₂ = Preoperad C₂
  open PreoperadFunctor G

  F-plug : ∀ {k n} off (f : C₁.Op (off + k)) (gs : Fin k → C₁.Op n)
    → F (C₁.plug off f gs) C₂.≈ C₂.plug off (F f) (F ∘ gs)
  F-plug {zero}  off f gs = C₂.≈.refl
  F-plug {suc k} {n} off f gs =
    C₂.≈.trans (C₂.≈.reflexive (F-subst (+-assoc off n (k * n)) _))
    (C₂.subst-cong (+-assoc off n (k * n))
      (C₂.≈.trans (F-plug (off + n) _ (gs ∘ suc))
        (C₂.plug-cong (off + n)
          (C₂.≈.trans (C₂.≈.reflexive (F-subst (sym (+-assoc off n k)) _))
                      (C₂.subst-cong (sym (+-assoc off n k)) (F-sub f (gs zero))))
          (λ _ → C₂.≈.refl))))

------------------------------------------------------------------------
-- Theorem 4.9, for a fixed structure S
------------------------------------------------------------------------

module Initial (S : Structure) where
  open Structure S
  open Interp S
  open Lemma45 S using (ren-lemmaᵛ; ren-lemmaᶜ; sub-lemmaᵛ₀; sub-lemmaᶜ₀; sound)
  open import MFPS.FreydSub M
  import MFPS.Sub ℂ as C
  import MFPS.SubTuple 𝕊ᵥ as VT
  import MFPS.SubTuple ℂ as CT
  import MFPS.Representable ℂ as CR
  open import MFPS.SubCast ℂ using (ins-arity; ins-irr; rn-rn)
  open import MFPS.SubSym ℂ using (_⟶_; σʷ-σʷ)
  open import MFPS.SubCartesian ℂ using (natLk)
  open import MFPS.SubWhisker ℂ using () renaming (⊣-stable to ⊣-stableᶜ)

  -- the term model, and its interpretation of its own terms
  private
    module T = Interp termStructure
    module TS = Structure termStructure

  ----------------------------------------------------------------------
  -- small facts about the interpretation of variables
  ----------------------------------------------------------------------

  -- ⟦x⟧ = id[pt x], and J id[pt x] = id[pt x]
  J-pt : (i : Fin n) → 𝒥 (𝕍.idₒ 𝕍.[ ptʳ i ]) ℂ.≈ ℂ.idₒ ℂ.[ ptʳ i ]
  J-pt i = ℂ.≈.trans (𝒥-ren 𝕍.idₒ (ptʳ i)) (ℂ.ren-cong 𝒥-id (λ _ → refl))

  -- the canonical arguments x₁,…,xₖ are interpreted by the projections
  vars-interp : ∀ k (ι : Fin k → Fin n) (i : Fin k) → ⟦ vars k ι ⟧ᵃ i ≡ 𝕍.idₒ 𝕍.[ ptʳ (ι i) ]
  vars-interp (suc k) ι zero    = refl
  vars-interp (suc k) ι (suc i) = vars-interp k (ι ∘ suc) i

  -- id[pt 0] = id in arity 1
  pt-zero : 𝕍.idₒ 𝕍.[ ptʳ zero ] 𝕍.≈ 𝕍.idₒ
  pt-zero = 𝕍.≈.trans (𝕍.ren-cong 𝕍.≈.refl (λ { zero → refl })) (𝕍.ren-id 𝕍.idₒ)

  ----------------------------------------------------------------------
  -- The word equation behind the preservation of computation
  -- composition ("the let case with the exchange rule").
  --
  --   [ρ-ins] ; {N ⊣ g[ι₂] ⊢ 0} ; [contr N]  ≅  {n₁ ⊣ g ⊢ n₂}
  --
  -- Read from left to right (steps are applied in order):
  --   (N)   pull the renaming ι₂ out of the substituted operation;
  --   (E)   factor ρ-ins as an exchange π (hole to the end) followed
  --         by a block renaming ρ₂;
  --   (N)   push ρ₂ through the substitution step, which becomes
  --         {n₁+n₂ ⊣ g ⊢ 0}; all remaining renamings compose to an
  --         exchange τ' moving the block of g back to the middle;
  --   the result is n₁ ⊣ ([σ₁,ₙ₂] ; {n₂ ⊣ g ⊢ 0} ; [σₙ₂,ₘ]) up to casts,
  --   and the inner word is {0 ⊣ g ⊢ n₂} by the naturality of the
  --   symmetry (`natLk`).
  ----------------------------------------------------------------------

  hole-move : ∀ n₁ n₂ {m} (g : ℂ.Op m)
    → C.Cong JImg
        (C.rn (ρ-ins n₁ n₂ m) C.∷ C.sub! (n₁ + (m + n₂)) 0 (g ℂ.[ ι₂ n₁ m n₂ ]) C.∷ C.rn (contr (n₁ + (m + n₂))) C.∷ C.ε)
        C.⟦ C.sub! n₁ n₂ g ⟧
  hole-move n₁ n₂ {m} g =
    C.≅-∷ (C.≅-cong {Γ₁ = C.ε} (C.≅-sym idN₁) C.≅-refl)
    ⟶ C.≅-∷ (C.≅-cong {Γ₁ = C.rn (idʳ {N} +ʳ idʳ {1} +ʳ idʳ {0}) C.∷ C.⟦ C.sub! N 0 (g ℂ.[ ι₂ n₁ m n₂ ]) ⟧}
                       (C.≅-sym (C.N∙ g (idʳ {N}) (ι₂ n₁ m n₂) (idʳ {0}))) C.≅-refl)
    ⟶ C.≅-∷ (C.≅-∷ (rn-rn _ _))
    ⟶ C.≅-∷ˡ (C.E∙ E1)
    ⟶ C.≅-sym (rn-rn π ρ₂)
    ⟶ C.≅-∷ (C.≅-∷ (C.≅-∷ˡ (C.≅-sym (C.I∙ N 0 refl refl (ℂ.ren-id g)))))
    ⟶ C.≅-∷ (C.≅-cong {Γ₁ = C.rn ρ₂ C.∷ C.⟦ C.sub! N 0 (g ℂ.[ idʳ ]) ⟧}
                       (C.≅-sym (C.N∙ g ι₁₃ (idʳ {m}) (idʳ {0}))) C.≅-refl)
    ⟶ C.≅-∷ (C.≅-∷ (rn-rn _ _))
    ⟶ C.≅-∷ (C.≅-∷ (C.≅-∷ˡ (C.E∙ E2)))
    ⟶ C.≅-sym (rn-rn (idʳ {n₁} +ʳ π₀) (castʳ Q))
    ⟶ C.≅-∷ (C.≅-∷ (C.≅-∷ (C.≅-sym (rn-rn (castʳ (sym P)) (idʳ {n₁} +ʳ τ₀)))))
    ⟶ C.≅-∷ (C.≅-cong (C.≅-sym (C.S∙ (n₁ + n₂) 0 P Q g)) C.≅-refl)
    ⟶ ⊣-stableᶜ n₁ core
    ⟶ ins-arity (+-identityʳ n₁) refl (C.Lp n₁ 0 refl) refl (C.Lp n₁ 0 refl) refl g
    where
      N = n₁ + (m + n₂)
      -- the renamings involved
      ι₁₃ : Ren (n₁ + n₂) N
      ι₁₃ = [ ι₁ n₁ m n₂ , ι₃ n₁ m n₂ ]ʳ
      P₁' : n₂ + m ≡ n₂ + (m + 0)
      P₁' = cong (n₂ +_) (sym (+-identityʳ m))
      π₀ : Ren (suc n₂) (n₂ + 1)
      π₀ = σʳ 1 n₂
      τ₀ : Ren (n₂ + (m + 0)) (m + n₂)
      τ₀ = σʳ n₂ m ∘ʳ castʳ (sym P₁')
      P : n₁ + (n₂ + (m + 0)) ≡ (n₁ + n₂) + (m + 0)
      P = C.Lp n₁ n₂ refl
      Q : n₁ + (n₂ + 1) ≡ (n₁ + n₂) + 1
      Q = C.Lp n₁ n₂ refl
      π : Ren (n₁ + suc n₂) ((n₁ + n₂) + 1)
      π = castʳ Q ∘ʳ (idʳ {n₁} +ʳ π₀)
      τ' : Ren ((n₁ + n₂) + (m + 0)) N
      τ' = (idʳ {n₁} +ʳ τ₀) ∘ʳ castʳ (sym P)
      ρ₂ : Ren ((n₁ + n₂) + 1) (N + 1)
      ρ₂ = ι₁₃ +ʳ idʳ {1} +ʳ idʳ {0}
      S₀ : Ren (N + (m + 0)) (N + (N + 0))
      S₀ = idʳ {N} +ʳ ι₂ n₁ m n₂ +ʳ idʳ {0}
      R₀ : Ren ((n₁ + n₂) + (m + 0)) (N + (m + 0))
      R₀ = ι₁₃ +ʳ idʳ {m} +ʳ idʳ {0}

      idN₁ : C.Cong JImg C.⟦ C.rn (idʳ {N} +ʳ idʳ {1} +ʳ idʳ {0}) ⟧ C.ε
      idN₁ = C.E∙ (λ i → trans (+ʳ-cong {r = idʳ {N}} {r' = idʳ {N}} (λ _ → refl) (+ʳ-id 1 0) i) (+ʳ-id N 1 i)) ⟶ C.U₂∙

      -- ρ-ins = ρ₂ ∘ π
      E1 : ρ-ins n₁ n₂ m ≗ (ρ₂ ∘ʳ π)
      E1 = Fin-ins-ext n₁ n₂
        (λ j → toℕ-injective (begin
          toℕ (ρ-ins n₁ n₂ m (j ↑ˡ suc n₂))
            ≡⟨ toℕ-ρ-ins-₁ n₁ n₂ m j ⟩
          toℕ j
            ≡⟨ sym (toℕ-ι₁ n₁ m n₂ j) ⟩
          toℕ (ι₁ n₁ m n₂ j)
            ≡⟨ cong toℕ (sym ([,]ʳ-inl (ι₁ n₁ m n₂) (ι₃ n₁ m n₂) j)) ⟩
          toℕ (ι₁₃ (j ↑ˡ n₂))
            ≡⟨ sym (toℕ-↑ˡ _ 1) ⟩
          toℕ (ι₁₃ (j ↑ˡ n₂) ↑ˡ 1)
            ≡⟨ cong toℕ (sym (+ʳ-inj₁ ι₁₃ (idʳ {1} +ʳ idʳ {0}) (j ↑ˡ n₂))) ⟩
          toℕ (ρ₂ ((j ↑ˡ n₂) ↑ˡ 1))
            ≡⟨ cong (toℕ ∘ ρ₂) (sym (castʳ-≡ Q _ ((j ↑ˡ n₂) ↑ˡ 1) (trans (toℕ-↑ˡ j (n₂ + 1)) (sym (trans (toℕ-↑ˡ (j ↑ˡ n₂) 1) (toℕ-↑ˡ j n₂)))))) ⟩
          toℕ (ρ₂ (castʳ Q (j ↑ˡ (n₂ + 1))))
            ≡⟨ cong (toℕ ∘ ρ₂ ∘ castʳ Q) (sym (+ʳ-inj₁ (idʳ {n₁}) π₀ j)) ⟩
          toℕ (ρ₂ (castʳ Q ((idʳ {n₁} +ʳ π₀) (j ↑ˡ suc n₂)))) ∎))
        (toℕ-injective (begin
          toℕ (ρ-ins n₁ n₂ m (n₁ ↑ʳ zero))
            ≡⟨ toℕ-ρ-ins-₂ n₁ n₂ m ⟩
          N + 0
            ≡⟨ cong (N +_) (sym (trans (cong toℕ (+ʳ-inj₁ (idʳ {1}) (idʳ {0}) zero)) (toℕ-↑ˡ (zero {0}) 0))) ⟩
          N + toℕ ((idʳ {1} +ʳ idʳ {0}) zero)
            ≡⟨ sym (toℕ-↑ʳ N _) ⟩
          toℕ (N ↑ʳ (idʳ {1} +ʳ idʳ {0}) zero)
            ≡⟨ cong toℕ (sym (+ʳ-inj₂ ι₁₃ (idʳ {1} +ʳ idʳ {0}) zero)) ⟩
          toℕ (ρ₂ ((n₁ + n₂) ↑ʳ zero))
            ≡⟨ cong (toℕ ∘ ρ₂) (sym (castʳ-≡ Q _ ((n₁ + n₂) ↑ʳ zero)
                 (trans (toℕ-↑ʳ n₁ _) (trans (cong (n₁ +_) (toℕ-σʳ-inl 1 n₂ zero)) (trans (sym (+-assoc n₁ n₂ 0)) (sym (toℕ-↑ʳ (n₁ + n₂) zero))))))) ⟩
          toℕ (ρ₂ (castʳ Q (n₁ ↑ʳ π₀ zero)))
            ≡⟨ cong (toℕ ∘ ρ₂ ∘ castʳ Q) (sym (+ʳ-inj₂ (idʳ {n₁}) π₀ zero)) ⟩
          toℕ (ρ₂ (castʳ Q ((idʳ {n₁} +ʳ π₀) (n₁ ↑ʳ zero)))) ∎))
        (λ j → toℕ-injective (begin
          toℕ (ρ-ins n₁ n₂ m (n₁ ↑ʳ suc j))
            ≡⟨ toℕ-ρ-ins-₃ n₁ n₂ m j ⟩
          n₁ + (m + toℕ j)
            ≡⟨ sym (toℕ-ι₃ n₁ m n₂ j) ⟩
          toℕ (ι₃ n₁ m n₂ j)
            ≡⟨ cong toℕ (sym ([,]ʳ-inr (ι₁ n₁ m n₂) (ι₃ n₁ m n₂) j)) ⟩
          toℕ (ι₁₃ (n₁ ↑ʳ j))
            ≡⟨ sym (toℕ-↑ˡ _ 1) ⟩
          toℕ (ι₁₃ (n₁ ↑ʳ j) ↑ˡ 1)
            ≡⟨ cong toℕ (sym (+ʳ-inj₁ ι₁₃ (idʳ {1} +ʳ idʳ {0}) (n₁ ↑ʳ j))) ⟩
          toℕ (ρ₂ ((n₁ ↑ʳ j) ↑ˡ 1))
            ≡⟨ cong (toℕ ∘ ρ₂) (sym (castʳ-≡ Q _ ((n₁ ↑ʳ j) ↑ˡ 1)
                 (trans (toℕ-↑ʳ n₁ _) (trans (cong (n₁ +_) (toℕ-σʳ-inr 1 n₂ j)) (sym (trans (toℕ-↑ˡ _ 1) (toℕ-↑ʳ n₁ j))))))) ⟩
          toℕ (ρ₂ (castʳ Q (n₁ ↑ʳ π₀ (suc j))))
            ≡⟨ cong (toℕ ∘ ρ₂ ∘ castʳ Q) (sym (+ʳ-inj₂ (idʳ {n₁}) π₀ (suc j))) ⟩
          toℕ (ρ₂ (castʳ Q ((idʳ {n₁} +ʳ π₀) (n₁ ↑ʳ suc j)))) ∎))
        where open ≡-Reasoning

      -- (contr N ∘ S₀) ∘ R₀ = τ'
      E2 : ((contr N ∘ʳ S₀) ∘ʳ R₀) ≗ τ'
      E2 = Fin+-ext
        (Fin+-ext
          (λ j₁ → toℕ-injective (begin
            toℕ (contr N (S₀ (R₀ ((j₁ ↑ˡ n₂) ↑ˡ (m + 0)))))
              ≡⟨ cong (toℕ ∘ contr N ∘ S₀) (+ʳ-inj₁ ι₁₃ (idʳ {m} +ʳ idʳ {0}) (j₁ ↑ˡ n₂)) ⟩
            toℕ (contr N (S₀ (ι₁₃ (j₁ ↑ˡ n₂) ↑ˡ (m + 0))))
              ≡⟨ cong (toℕ ∘ contr N) (+ʳ-inj₁ (idʳ {N}) (ι₂ n₁ m n₂ +ʳ idʳ {0}) (ι₁₃ (j₁ ↑ˡ n₂))) ⟩
            toℕ (contr N (ι₁₃ (j₁ ↑ˡ n₂) ↑ˡ (N + 0)))
              ≡⟨ cong toℕ ([,]ʳ-inl idʳ (castʳ (+-identityʳ N)) (ι₁₃ (j₁ ↑ˡ n₂))) ⟩
            toℕ (ι₁₃ (j₁ ↑ˡ n₂))
              ≡⟨ cong toℕ ([,]ʳ-inl (ι₁ n₁ m n₂) (ι₃ n₁ m n₂) j₁) ⟩
            toℕ (ι₁ n₁ m n₂ j₁)
              ≡⟨ toℕ-ι₁ n₁ m n₂ j₁ ⟩
            toℕ j₁
              ≡⟨ sym (toℕ-↑ˡ j₁ (m + n₂)) ⟩
            toℕ (j₁ ↑ˡ (m + n₂))
              ≡⟨ cong toℕ (sym (+ʳ-inj₁ (idʳ {n₁}) τ₀ j₁)) ⟩
            toℕ ((idʳ {n₁} +ʳ τ₀) (j₁ ↑ˡ (n₂ + (m + 0))))
              ≡⟨ cong (toℕ ∘ (idʳ {n₁} +ʳ τ₀)) (sym (castʳ-≡ (sym P) _ (j₁ ↑ˡ (n₂ + (m + 0)))
                   (trans (toℕ-↑ˡ _ (m + 0)) (trans (toℕ-↑ˡ j₁ n₂) (sym (toℕ-↑ˡ j₁ _)))))) ⟩
            toℕ ((idʳ {n₁} +ʳ τ₀) (castʳ (sym P) ((j₁ ↑ˡ n₂) ↑ˡ (m + 0)))) ∎))
          (λ j₂ → toℕ-injective (begin
            toℕ (contr N (S₀ (R₀ ((n₁ ↑ʳ j₂) ↑ˡ (m + 0)))))
              ≡⟨ cong (toℕ ∘ contr N ∘ S₀) (+ʳ-inj₁ ι₁₃ (idʳ {m} +ʳ idʳ {0}) (n₁ ↑ʳ j₂)) ⟩
            toℕ (contr N (S₀ (ι₁₃ (n₁ ↑ʳ j₂) ↑ˡ (m + 0))))
              ≡⟨ cong (toℕ ∘ contr N) (+ʳ-inj₁ (idʳ {N}) (ι₂ n₁ m n₂ +ʳ idʳ {0}) (ι₁₃ (n₁ ↑ʳ j₂))) ⟩
            toℕ (contr N (ι₁₃ (n₁ ↑ʳ j₂) ↑ˡ (N + 0)))
              ≡⟨ cong toℕ ([,]ʳ-inl idʳ (castʳ (+-identityʳ N)) (ι₁₃ (n₁ ↑ʳ j₂))) ⟩
            toℕ (ι₁₃ (n₁ ↑ʳ j₂))
              ≡⟨ cong toℕ ([,]ʳ-inr (ι₁ n₁ m n₂) (ι₃ n₁ m n₂) j₂) ⟩
            toℕ (ι₃ n₁ m n₂ j₂)
              ≡⟨ toℕ-ι₃ n₁ m n₂ j₂ ⟩
            n₁ + (m + toℕ j₂)
              ≡⟨ cong (n₁ +_) (sym (toℕ-σʳ-inl n₂ m j₂)) ⟩
            n₁ + toℕ (σʳ n₂ m (j₂ ↑ˡ m))
              ≡⟨ cong (λ z → n₁ + toℕ (σʳ n₂ m z)) (sym (castʳ-≡ (sym P₁') _ (j₂ ↑ˡ m) (trans (toℕ-↑ˡ j₂ _) (sym (toℕ-↑ˡ j₂ m))))) ⟩
            n₁ + toℕ (τ₀ (j₂ ↑ˡ (m + 0)))
              ≡⟨ sym (toℕ-↑ʳ n₁ _) ⟩
            toℕ (n₁ ↑ʳ τ₀ (j₂ ↑ˡ (m + 0)))
              ≡⟨ cong toℕ (sym (+ʳ-inj₂ (idʳ {n₁}) τ₀ _)) ⟩
            toℕ ((idʳ {n₁} +ʳ τ₀) (n₁ ↑ʳ (j₂ ↑ˡ (m + 0))))
              ≡⟨ cong (toℕ ∘ (idʳ {n₁} +ʳ τ₀)) (sym (castʳ-≡ (sym P) _ (n₁ ↑ʳ (j₂ ↑ˡ (m + 0)))
                   (trans (toℕ-↑ˡ _ (m + 0)) (trans (toℕ-↑ʳ n₁ j₂) (sym (trans (toℕ-↑ʳ n₁ _) (cong (n₁ +_) (toℕ-↑ˡ j₂ _)))))))) ⟩
            toℕ ((idʳ {n₁} +ʳ τ₀) (castʳ (sym P) ((n₁ ↑ʳ j₂) ↑ˡ (m + 0)))) ∎)))
        (Fin+-ext
          (λ y₁ → toℕ-injective (begin
            toℕ (contr N (S₀ (R₀ ((n₁ + n₂) ↑ʳ (y₁ ↑ˡ 0)))))
              ≡⟨ cong (toℕ ∘ contr N ∘ S₀) (+ʳ-inj₂ ι₁₃ (idʳ {m} +ʳ idʳ {0}) (y₁ ↑ˡ 0)) ⟩
            toℕ (contr N (S₀ (N ↑ʳ (idʳ {m} +ʳ idʳ {0}) (y₁ ↑ˡ 0))))
              ≡⟨ cong (λ z → toℕ (contr N (S₀ (N ↑ʳ z)))) (+ʳ-inj₁ (idʳ {m}) (idʳ {0}) y₁) ⟩
            toℕ (contr N (S₀ (N ↑ʳ (y₁ ↑ˡ 0))))
              ≡⟨ cong (toℕ ∘ contr N) (+ʳ-inj₂ (idʳ {N}) (ι₂ n₁ m n₂ +ʳ idʳ {0}) (y₁ ↑ˡ 0)) ⟩
            toℕ (contr N (N ↑ʳ (ι₂ n₁ m n₂ +ʳ idʳ {0}) (y₁ ↑ˡ 0)))
              ≡⟨ cong toℕ ([,]ʳ-inr idʳ (castʳ (+-identityʳ N)) _) ⟩
            toℕ (castʳ (+-identityʳ N) ((ι₂ n₁ m n₂ +ʳ idʳ {0}) (y₁ ↑ˡ 0)))
              ≡⟨ toℕ-castʳ _ _ ⟩
            toℕ ((ι₂ n₁ m n₂ +ʳ idʳ {0}) (y₁ ↑ˡ 0))
              ≡⟨ cong toℕ (+ʳ-inj₁ (ι₂ n₁ m n₂) (idʳ {0}) y₁) ⟩
            toℕ (ι₂ n₁ m n₂ y₁ ↑ˡ 0)
              ≡⟨ trans (toℕ-↑ˡ _ 0) (toℕ-ι₂ n₁ m n₂ y₁) ⟩
            n₁ + toℕ y₁
              ≡⟨ cong (n₁ +_) (sym (toℕ-σʳ-inr n₂ m y₁)) ⟩
            n₁ + toℕ (σʳ n₂ m (n₂ ↑ʳ y₁))
              ≡⟨ cong (λ z → n₁ + toℕ (σʳ n₂ m z)) (sym (castʳ-≡ (sym P₁') _ (n₂ ↑ʳ y₁)
                   (trans (toℕ-↑ʳ n₂ _) (trans (cong (n₂ +_) (toℕ-↑ˡ y₁ 0)) (sym (toℕ-↑ʳ n₂ y₁)))))) ⟩
            n₁ + toℕ (τ₀ (n₂ ↑ʳ (y₁ ↑ˡ 0)))
              ≡⟨ sym (toℕ-↑ʳ n₁ _) ⟩
            toℕ (n₁ ↑ʳ τ₀ (n₂ ↑ʳ (y₁ ↑ˡ 0)))
              ≡⟨ cong toℕ (sym (+ʳ-inj₂ (idʳ {n₁}) τ₀ _)) ⟩
            toℕ ((idʳ {n₁} +ʳ τ₀) (n₁ ↑ʳ (n₂ ↑ʳ (y₁ ↑ˡ 0))))
              ≡⟨ cong (toℕ ∘ (idʳ {n₁} +ʳ τ₀)) (sym (castʳ-≡ (sym P) _ (n₁ ↑ʳ (n₂ ↑ʳ (y₁ ↑ˡ 0)))
                   (trans (toℕ-↑ʳ (n₁ + n₂) _) (trans (+-assoc n₁ n₂ _) (sym (trans (toℕ-↑ʳ n₁ _) (cong (n₁ +_) (toℕ-↑ʳ n₂ _)))))))) ⟩
            toℕ ((idʳ {n₁} +ʳ τ₀) (castʳ (sym P) ((n₁ + n₂) ↑ʳ (y₁ ↑ˡ 0)))) ∎))
          (λ ()))
        where open ≡-Reasoning

      -- the exchange:  [σ₁,ₙ₂] ; {n₂ ⊣ g ⊢ 0} ; [σₙ₂,ₘ ∘ cast]  ≅  {0 ⊣ g ⊢ n₂}
      P₀ : m + n₂ ≡ 0 + (m + (0 + n₂))
      P₀ = C.Rp 0 m 0 n₂ (sym (+-identityʳ m))
      Q₀ : 1 + n₂ ≡ 0 + suc (0 + n₂)
      Q₀ = C.Rq 0 0 n₂ refl
      P₁ : n₂ + m ≡ (n₂ + 0) + (m + 0)
      P₁ = C.Lp n₂ 0 (sym (+-identityʳ m))
      Q₁ : n₂ + 1 ≡ (n₂ + 0) + 1
      Q₁ = C.Lp n₂ 0 refl

      core : C.Cong JImg (C.rn π₀ C.∷ C.sub! n₂ 0 g C.∷ C.rn τ₀ C.∷ C.ε) C.⟦ C.sub! 0 n₂ g ⟧
      core = C.≅-sym
        ( C.≅-≡ (cong C.⟦_⟧ (ins-irr 0 n₂ refl P₀ refl Q₀ g))
        ⟶ C.≅-≡ (sym (C.++-identityʳ (CR.ηʷ g C.⊢ʷ n₂)))
        ⟶ C.≅-cong {Γ₁ = CR.ηʷ g C.⊢ʷ n₂} C.≅-refl (C.≅-sym (σʷ-σʷ m n₂))
        ⟶ C.≅-≡ (sym (C.++-assoc (CR.ηʷ g C.⊢ʷ n₂) C.⟦ C.rn (σʳ m n₂) ⟧ C.⟦ C.rn (σʳ n₂ m) ⟧))
        ⟶ C.≅-cong (C.≅-sym (natLk n₂ (CR.ηʷ g))) C.≅-refl
        ⟶ C.≅-∷ (C.≅-∷ˡ (ins-arity (+-identityʳ n₂) refl P₁ P₁' Q₁ refl g))
        ⟶ C.≅-∷ (C.≅-cong (C.S∙ n₂ 0 P₁' refl g) C.≅-refl)
        ⟶ rn-rn _ _
        ⟶ C.≅-∷ (C.≅-∷ (rn-rn _ _)) )

  ----------------------------------------------------------------------
  -- Preservation of application:  ⟦x₁ x₂⟧ = ⊛
  ----------------------------------------------------------------------

  private
    id₃ : C.Cong JImg C.⟦ C.rn (idʳ {0} +ʳ idʳ {1} +ʳ idʳ {1}) ⟧ C.ε
    id₃ = C.E∙ (λ i → trans (+ʳ-cong {r = idʳ {0}} {r' = idʳ {0}} (λ _ → refl) (+ʳ-id 1 1) i) (+ʳ-id 0 2 i)) ⟶ C.U₂∙

    id₃' : C.Cong JImg C.⟦ C.rn (idʳ {2} +ʳ idʳ {1} +ʳ idʳ {0}) ⟧ C.ε
    id₃' = C.E∙ (λ i → trans (+ʳ-cong {r = idʳ {2}} {r' = idʳ {2}} (λ _ → refl) (+ʳ-id 1 0) i) (+ʳ-id 2 1 i)) ⟶ C.U₂∙

  app-word : C.Cong JImg
    (C.sub! 0 1 (ℂ.idₒ ℂ.[ ptʳ (zero {1}) ]) C.∷ C.sub! 2 0 (ℂ.idₒ ℂ.[ ptʳ (suc {1} zero) ]) C.∷ C.rn (contr 2) C.∷ C.ε)
    C.ε
  app-word =
    C.≅-cong {Γ₁ = C.ε} (C.≅-sym id₃) C.≅-refl
    ⟶ C.≅-cong {Γ₁ = C.rn (idʳ {0} +ʳ idʳ {1} +ʳ idʳ {1}) C.∷ C.⟦ C.sub! 0 1 (ℂ.idₒ ℂ.[ ptʳ (zero {1}) ]) ⟧}
               (C.≅-sym (C.N∙ ℂ.idₒ (idʳ {0}) (ptʳ (zero {1})) (idʳ {1}))) C.≅-refl
    ⟶ C.≅-cong (C.U₁∙ 0 1 refl) C.≅-refl
    ⟶ C.≅-∷ (C.≅-cong {Γ₁ = C.ε} (C.≅-sym id₃') C.≅-refl)
    ⟶ C.≅-∷ (C.≅-cong {Γ₁ = C.rn (idʳ {2} +ʳ idʳ {1} +ʳ idʳ {0}) C.∷ C.⟦ C.sub! 2 0 (ℂ.idₒ ℂ.[ ptʳ (suc {1} zero) ]) ⟧}
                       (C.≅-sym (C.N∙ ℂ.idₒ (idʳ {2}) (ptʳ (suc {1} zero)) (idʳ {0}))) C.≅-refl)
    ⟶ C.≅-∷ (C.≅-cong (C.U₁∙ 2 0 refl) C.≅-refl)
    ⟶ rn-rn _ _
    ⟶ rn-rn _ _
    ⟶ C.E∙ (λ { zero → refl ; (suc zero) → refl })
    ⟶ C.U₂∙

  ----------------------------------------------------------------------
  -- Theorem 4.9, existence: ⟦−⟧ is a morphism of structures
  ----------------------------------------------------------------------

  Gᵛ-interp : PreoperadFunctor TS.𝕍.V 𝕍.V
  Gᵛ-interp = record
    { F      = ⟦_⟧ᵛ
    ; F-cong = sound
    ; F-id   = pt-zero
    ; F-sub  = λ {n₁} {n₂} V W → sub-lemmaᵛ₀ n₁ n₂ W V }

  Gᶜ-interp : PreoperadFunctor TS.ℂ.C ℂ.C
  Gᶜ-interp = record
    { F      = ⟦_⟧ᶜ
    ; F-cong = sound
    ; F-id   = ℂ.≈.trans (𝒥-cong pt-zero) 𝒥-id
    ; F-sub  = λ {n₁} {n₂} {m} M₁ M₂ →
        ℂ.≈.trans (ℂ.ren-cong (ℂ.sub-cong (ren-lemmaᶜ (ρ-ins n₁ n₂ m) M₁) (ren-lemmaᶜ (ι₂ n₁ m n₂) M₂)) (λ _ → refl))
                  (⋆-soundᶜ (hole-move n₁ n₂ ⟦ M₂ ⟧ᶜ) ⟦ M₁ ⟧ᶜ) }

  G-interp : FreydOperadFunctor TS.M M
  G-interp = record
    { Gᵛ     = Gᵛ-interp
    ; Gᵛ-ren = record { F-ren = λ V r → ren-lemmaᵛ r V }
    ; Gᶜ     = Gᶜ-interp
    ; Gᶜ-ren = record { F-ren = λ M r → ren-lemmaᶜ r M }
    ; G-J    = λ V → ℂ.≈.refl }

  closed-interp : ClosedFunctor TS.W W G-interp
  closed-interp = record
    { G-app = ℂ.≈.trans (ℂ.ren-cong (ℂ.sub-cong (ℂ.sub-cong ℂ.≈.refl (J-pt (zero {1}))) (J-pt (suc {1} zero))) (λ _ → refl))
                        (⋆-soundᶜ app-word ⊛)
    ; G-abs = λ M → 𝕍.≈.refl }

  interp : StructureMorphism termStructure S
  interp = record
    { G      = G-interp
    ; closed = closed-interp
    ; G-σF   = λ {n} f →
        𝕍.≈.trans (𝕍.ren-cong (𝕍.plug-cong 0 𝕍.≈.refl (λ i → 𝕍.≈.reflexive (vars-interp n idʳ i))) (λ _ → refl))
        (𝕍.≈.trans (VT.plug-tuple₀ cartRulesᵥ (σF f) _)
                   (⋆-soundᵛ (VT.tuple-pt idʳ ⟶ᵛ V.U₂∙) (σF f)))
    ; G-σP   = λ {n} p →
        ℂ.≈.trans (ℂ.ren-cong (ℂ.plug-cong 0 ℂ.≈.refl (λ i → ℂ.≈.trans (𝒥-cong (𝕍.≈.reflexive (vars-interp n idʳ i))) (J-pt i))) (λ _ → refl))
        (ℂ.≈.trans (CT.plug-tuple₀ cartRulesᶜ (σP p) _)
                   (⋆-soundᶜ (CT.tuple-pt idʳ ⟶ C.U₂∙) (σP p))) }
    where
      import MFPS.Sub 𝕊ᵥ as V
      open import MFPS.SubSym 𝕊ᵥ using () renaming (_⟶_ to _⟶ᵛ_)

  ----------------------------------------------------------------------
  -- Theorem 4.9, uniqueness: every morphism out of the term model is
  -- the interpretation
  ----------------------------------------------------------------------

  module Unique (G : StructureMorphism termStructure S) where
    open StructureMorphism G

    uniqᵛ : (V : Val n) → 𝒢ᵛ V 𝕍.≈ ⟦ V ⟧ᵛ
    uniqᶜ : (M : Cmp n) → 𝒢ᶜ M ℂ.≈ ⟦ M ⟧ᶜ
    -- for the arguments of a term former, through the term model's own
    -- interpretation of them
    uniqᵃ : (Vs : Args n k) (i : Fin k) → 𝒢ᵛ (T.⟦ Vs ⟧ᵃ i) 𝕍.≈ ⟦ Vs ⟧ᵃ i

    -- G agrees with ⟦−⟧ on the term model's interpretation of a term
    uniqᵛ' : (V : Val n) → 𝒢ᵛ T.⟦ V ⟧ᵛ 𝕍.≈ ⟦ V ⟧ᵛ
    uniqᵛ' V = 𝕍.≈.trans (𝒢ᵛ-cong (term-interpᵛ V)) (uniqᵛ V)

    uniqᶜ' : (M : Cmp n) → 𝒢ᶜ T.⟦ M ⟧ᶜ ℂ.≈ ⟦ M ⟧ᶜ
    uniqᶜ' M = ℂ.≈.trans (𝒢ᶜ-cong (term-interpᶜ M)) (uniqᶜ M)

    uniqᵛ (var i) =
      𝕍.≈.trans (𝒢ᵛ-ren (var zero) (ptʳ i)) (𝕍.ren-cong 𝒢ᵛ-id (λ _ → refl))
    uniqᵛ {n} (fun {k} f Vs) =
      𝕍.≈.trans (𝒢ᵛ-cong (≈-sym (term-interpᵛ (fun f Vs))))
      (𝕍.≈.trans (𝒢ᵛ-ren _ (Δᵏ k n))
      (𝕍.ren-cong (𝕍.≈.trans (F-plug Gᵛ {k} {n} 0 (TS.σF f) T.⟦ Vs ⟧ᵃ) (𝕍.plug-cong 0 (G-σF f) (uniqᵃ Vs))) (λ _ → refl)))
    uniqᵛ (lam M) = 𝕍.≈.trans (G-abs M) (abs-cong (uniqᶜ M))

    uniqᶜ (ret V) = ℂ.≈.trans (G-J V) (𝒥-cong (uniqᵛ V))
    uniqᶜ {n} (bnd M₂ M₁) =
      ℂ.≈.trans (𝒢ᶜ-cong (≈-sym (term-interpᶜ (bnd M₂ M₁))))
      (ℂ.≈.trans (𝒢ᶜ-ren _ (contr n))
      (ℂ.ren-cong (ℂ.≈.trans (𝒢ᶜ-sub _ _) (ℂ.sub-cong (uniqᶜ' M₁) (uniqᶜ' M₂))) (λ _ → refl)))
    uniqᶜ {n} (prc {k} p Vs) =
      ℂ.≈.trans (𝒢ᶜ-cong (≈-sym (term-interpᶜ (prc p Vs))))
      (ℂ.≈.trans (𝒢ᶜ-ren _ (Δᵏ k n))
      (ℂ.ren-cong (ℂ.≈.trans (F-plug Gᶜ {k} {n} 0 (TS.σP p) (TS.𝒥 ∘ T.⟦ Vs ⟧ᵃ))
                             (ℂ.plug-cong 0 (G-σP p) (λ i → ℂ.≈.trans (G-J _) (𝒥-cong (uniqᵃ Vs i)))))
                  (λ _ → refl)))
    uniqᶜ {n} (app V₁ V₂) =
      ℂ.≈.trans (𝒢ᶜ-cong (≈-sym (term-interpᶜ (app V₁ V₂))))
      (ℂ.≈.trans (𝒢ᶜ-ren _ (contr n))
      (ℂ.ren-cong
        (ℂ.≈.trans (𝒢ᶜ-sub _ _)
          (ℂ.sub-cong (ℂ.≈.trans (𝒢ᶜ-sub _ _) (ℂ.sub-cong G-app (ℂ.≈.trans (G-J _) (𝒥-cong (uniqᵛ' V₁)))))
                      (ℂ.≈.trans (G-J _) (𝒥-cong (uniqᵛ' V₂)))))
        (λ _ → refl)))

    uniqᵃ (V ∷ Vs) zero    = uniqᵛ' V
    uniqᵃ (V ∷ Vs) (suc i) = uniqᵃ Vs i

  -- Theorem 4.9: the term model is initial
  unique : (G : StructureMorphism termStructure S)
    → (∀ {n} (V : Val n) → StructureMorphism.𝒢ᵛ G V 𝕍.≈ ⟦ V ⟧ᵛ)
    × (∀ {n} (M : Cmp n) → StructureMorphism.𝒢ᶜ G M ℂ.≈ ⟦ M ⟧ᶜ)
  unique G = Unique.uniqᵛ G , Unique.uniqᶜ G
