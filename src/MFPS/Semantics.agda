------------------------------------------------------------------------
-- Section 4.1–4.2: λml*-structures (Def. 4.3), the interpretation
-- (Def. 4.4), satisfiability (Def. 4.6) and soundness (Thm. 4.7).
--
-- Shared contexts.  The paper interprets a term formed from subterms in
-- disjoint contexts Γ₁,…,Γ_k by the parallel composite of the
-- interpretations.  In the shared-context presentation every subterm
-- lives in the same context of length n, so a k-ary former is
-- interpreted by the parallel composite (arity k·n) followed by the
-- contraction renaming Δᵏ : Ren (k·n) n; similarly `let` uses the
-- single substitution of the paper followed by a contraction.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Preoperad
open import MFPS.Syntax

module MFPS.Semantics (Σ : Signature) where

open Signature Σ
open Terms Σ
open import MFPS.Theory Σ

private
  variable
    k m n : ℕ
    s : Sort

------------------------------------------------------------------------
-- Definition 4.3
------------------------------------------------------------------------

record Structure : Set₁ where
  field
    M  : FreydOperad
    W  : WeaklyClosed M
    σF : ∀ {n} → Func n → FreydOperad.𝕍.Op M n
    σP : ∀ {n} → Proc n → FreydOperad.ℂ.Op M n
  open FreydOperad M public
  open WeaklyClosed W public renaming (app to ⊛; beta to β-law)

record StructureMorphism (S₁ S₂ : Structure) : Set where
  private
    module S₁ = Structure S₁
    module S₂ = Structure S₂
  field
    G      : FreydOperadFunctor S₁.M S₂.M
    closed : ClosedFunctor S₁.W S₂.W G
  open FreydOperadFunctor G public
  open ClosedFunctor closed public
  field
    G-σF : ∀ {n} (f : Func n) → 𝒢ᵛ (S₁.σF f) S₂.𝕍.≈ S₂.σF f
    G-σP : ∀ {n} (p : Proc n) → 𝒢ᶜ (S₁.σP p) S₂.ℂ.≈ S₂.σP p

------------------------------------------------------------------------
-- k-fold contraction Δᵏ : Ren (k·n) n and the contraction used by let
------------------------------------------------------------------------

contr : ∀ n → Ren (n + (n + 0)) n
contr n = [ idʳ , castʳ (+-identityʳ n) ]ʳ

------------------------------------------------------------------------
-- Definition 4.4: the interpretation
------------------------------------------------------------------------

module Interp (S : Structure) where
  open Structure S

  ⟦_⟧ᵛ : Val n → 𝕍.Op n
  ⟦_⟧ᶜ : Cmp n → ℂ.Op n
  ⟦_⟧ᵃ : Args n k → Fin k → 𝕍.Op n

  ⟦ var i ⟧ᵛ    = 𝕍.idₒ 𝕍.[ ptʳ i ]
  ⟦_⟧ᵛ {n} (fun {k} f Vs) = (𝕍.plug 0 (σF f) ⟦ Vs ⟧ᵃ) 𝕍.[ Δᵏ k n ]
  ⟦ lam M ⟧ᵛ    = abs ⟦ M ⟧ᶜ

  ⟦ ret V ⟧ᶜ           = 𝒥 ⟦ V ⟧ᵛ
  ⟦_⟧ᶜ {n} (bnd M₂ M₁) = (⟦ M₁ ⟧ᶜ ℂ.⟨ n ⊣ ⟦ M₂ ⟧ᶜ ⊢ 0 ⟩) ℂ.[ contr n ]
  ⟦_⟧ᶜ {n} (prc {k} p Vs) = (ℂ.plug 0 (σP p) (𝒥 ∘ ⟦ Vs ⟧ᵃ)) ℂ.[ Δᵏ k n ]
  ⟦_⟧ᶜ {n} (app V₁ V₂) = ((⊛ ℂ.⟨ 0 ⊣ 𝒥 ⟦ V₁ ⟧ᵛ ⊢ 1 ⟩) ℂ.⟨ n ⊣ 𝒥 ⟦ V₂ ⟧ᵛ ⊢ 0 ⟩) ℂ.[ contr n ]

  ⟦ V ∷ Vs ⟧ᵃ zero    = ⟦ V ⟧ᵛ
  ⟦ V ∷ Vs ⟧ᵃ (suc i) = ⟦ Vs ⟧ᵃ i

  -- the interpretation of either sort
  ⟦_⟧ : Trm n s → Set
  ⟦_⟧ {n} {val} _ = 𝕍.Op n
  ⟦_⟧ {n} {cmp} _ = ℂ.Op n

  -- Definition 4.6: satisfaction
  infix 4 _⊨_≡_
  _⊨_≡_ : ∀ n → Trm n s → Trm n s → Set
  _⊨_≡_ {s = val} n V V' = ⟦ V ⟧ᵛ 𝕍.≈ ⟦ V' ⟧ᵛ
  _⊨_≡_ {s = cmp} n M M' = ⟦ M ⟧ᶜ ℂ.≈ ⟦ M' ⟧ᶜ

  ----------------------------------------------------------------------
  -- Lemma 4.5 (the two semantic substitution lemmas), stated.
  --
  -- (a) interpretation commutes with renaming;
  -- (b) interpretation commutes with single substitution:
  --       ⟦M{V/x}⟧ = ⟦M⟧{n ⊣ J⟦V⟧ ⊢ 0}[contr]      (and likewise for values).
  ----------------------------------------------------------------------

  RenLemma : Set
  RenLemma = (∀ {m n} (r : Ren m n) (V : Val m) → ⟦ ren r V ⟧ᵛ 𝕍.≈ ⟦ V ⟧ᵛ 𝕍.[ r ])
           × (∀ {m n} (r : Ren m n) (M : Cmp m) → ⟦ ren r M ⟧ᶜ ℂ.≈ ⟦ M ⟧ᶜ ℂ.[ r ])

  SubLemma : Set
  SubLemma = (∀ {n} (V : Val (n + 1)) (W : Val n) → ⟦ V [ W ] ⟧ᵛ 𝕍.≈ (⟦ V ⟧ᵛ 𝕍.⟨ n ⊣ ⟦ W ⟧ᵛ ⊢ 0 ⟩) 𝕍.[ contr n ])
           × (∀ {n} (M : Cmp (n + 1)) (W : Val n) → ⟦ M [ W ] ⟧ᶜ ℂ.≈ (⟦ M ⟧ᶜ ℂ.⟨ n ⊣ 𝒥 ⟦ W ⟧ᵛ ⊢ 0 ⟩) ℂ.[ contr n ])

  ----------------------------------------------------------------------
  -- Theorem 4.7 (Soundness), relative to Lemma 4.5(b) and, for (assoc),
  -- to Lemma 4.5(a).
  ----------------------------------------------------------------------

  -- the (runit) case: needs the *left* unit law id{f} ≡ f (not the
  -- right unit law as stated in the paper's proof), plus the
  -- renaming/substitution interchange.
  runit-sound : (M : Cmp n) → ⟦ bnd M (ret (var last)) ⟧ᶜ ℂ.≈ ⟦ M ⟧ᶜ
  runit-sound {n} M =
    ℂ.≈.trans (ℂ.ren-cong (ℂ.sub-cong step₁ (ℂ.≈.sym (ℂ.ren-id ⟦ M ⟧ᶜ))) (λ _ → refl))
    (ℂ.≈.trans (ℂ.ren-cong (ℂ.≈.sym (ℂ.ren-sub ℂ.idₒ ⟦ M ⟧ᶜ (!ʳ n) idʳ idʳ)) (λ _ → refl))
    (ℂ.≈.trans (ℂ.ren-cong (ℂ.ren-cong step₂ (λ _ → refl)) (λ _ → refl))
    (ℂ.≈.trans (ℂ.≈.sym (ℂ.ren-∘ _ _ _))
    (ℂ.≈.trans (ℂ.≈.sym (ℂ.ren-∘ _ _ _))
    (ℂ.≈.trans (ℂ.ren-cong ℂ.≈.refl step₃) (ℂ.ren-id ⟦ M ⟧ᶜ))))))
    where
      -- J(id[pt last]) ≈ id[!ₙ + id₁ + id₀]
      step₁ : 𝒥 (𝕍.idₒ 𝕍.[ ptʳ last ]) ℂ.≈ ℂ.idₒ ℂ.[ !ʳ n +ʳ idʳ {1} +ʳ idʳ {0} ]
      step₁ = ℂ.≈.trans (𝒥-ren 𝕍.idₒ (ptʳ last)) (ℂ.ren-cong 𝒥-id (λ { zero → refl }))
      -- id{0 ⊣ f ⊢ 0} ≈ f[cast]
      step₂ : ℂ.idₒ ℂ.⟨ 0 ⊣ ⟦ M ⟧ᶜ ⊢ 0 ⟩ ℂ.≈ ⟦ M ⟧ᶜ ℂ.[ castʳ (sym (+-identityʳ n)) ]
      step₂ = ℂ.≈.trans (ℂ.≈.reflexive (sym (subst-cancel-sym ℂ.Op (+-identityʳ n) (ℂ.idₒ ℂ.⟨ 0 ⊣ ⟦ M ⟧ᶜ ⊢ 0 ⟩))))
              (ℂ.≈.trans (ℂ.subst-cong (sym (+-identityʳ n)) (ℂ.lunit ⟦ M ⟧ᶜ (+-identityʳ n)))
                         (ℂ.subst-ren (sym (+-identityʳ n)) ⟦ M ⟧ᶜ))
      -- the total renaming is the identity
      step₃ : (contr n ∘ʳ (!ʳ n +ʳ idʳ {n} +ʳ idʳ {0}) ∘ʳ castʳ (sym (+-identityʳ n))) ≗ idʳ
      step₃ i = begin
        contr n ((!ʳ n +ʳ idʳ {n} +ʳ idʳ {0}) (castʳ (sym (+-identityʳ n)) i))
          ≡⟨ cong (contr n) (+ʳ-inj₂ (!ʳ n) (idʳ {n} +ʳ idʳ {0}) _) ⟩
        contr n (n ↑ʳ ((idʳ {n} +ʳ idʳ {0}) (castʳ (sym (+-identityʳ n)) i)))
          ≡⟨ [,]ʳ-inr idʳ (castʳ (+-identityʳ n)) _ ⟩
        castʳ (+-identityʳ n) ((idʳ {n} +ʳ idʳ {0}) (castʳ (sym (+-identityʳ n)) i))
          ≡⟨ cong (castʳ (+-identityʳ n)) (+ʳ-id n 0 _) ⟩
        castʳ (+-identityʳ n) (castʳ (sym (+-identityʳ n)) i)
          ≡⟨ castʳ-∘ (sym (+-identityʳ n)) (+-identityʳ n) i ⟩
        castʳ (trans (sym (+-identityʳ n)) (+-identityʳ n)) i
          ≡⟨ castʳ-refl (trans (sym (+-identityʳ n)) (+-identityʳ n)) i ⟩
        i ∎
        where open ≡-Reasoning

  -- the (assoc) case, stated (proved in MFPS.SoundAssoc from RenLemma)
  AssocSound : Set
  AssocSound = ∀ {n} (M₁ : Cmp n) (M₂ : Cmp (n + 1)) (M : Cmp (n + 1))
    → ⟦ bnd (bnd M₁ M₂) M ⟧ᶜ ℂ.≈ ⟦ bnd M₁ (bnd M₂ (ren wk₁ M)) ⟧ᶜ

  module Soundness (subLemma : SubLemma) (assocSound : AssocSound) where

    sound  : {E E' : Trm n s} → E ≈ E' → n ⊨ E ≡ E'
    soundᵃ : {Vs Vs' : Args n k} → Vs ≈ᵃ Vs' → ∀ i → ⟦ Vs ⟧ᵃ i 𝕍.≈ ⟦ Vs' ⟧ᵃ i

    sound {s = val} ≈-refl = 𝕍.≈.refl
    sound {s = cmp} ≈-refl = ℂ.≈.refl
    sound {s = val} (≈-sym e) = 𝕍.≈.sym (sound e)
    sound {s = cmp} (≈-sym e) = ℂ.≈.sym (sound e)
    sound {s = val} (≈-trans e e') = 𝕍.≈.trans (sound e) (sound e')
    sound {s = cmp} (≈-trans e e') = ℂ.≈.trans (sound e) (sound e')
    sound (ret-cong e) = 𝒥-cong (sound e)
    sound {n} (fun-cong {k = k} e) = 𝕍.ren-cong (𝕍.plug-cong {k} {n} 0 𝕍.≈.refl (soundᵃ e)) (λ _ → refl)
    sound (bnd-cong e e') = ℂ.ren-cong (ℂ.sub-cong (sound e') (sound e)) (λ _ → refl)
    sound {n} (prc-cong {k = k} e) = ℂ.ren-cong (ℂ.plug-cong {k} {n} 0 ℂ.≈.refl (λ i → 𝒥-cong (soundᵃ e i))) (λ _ → refl)
    sound (lam-cong e) = abs-cong (sound e)
    sound (app-cong e e') = ℂ.ren-cong (ℂ.sub-cong (ℂ.sub-cong ℂ.≈.refl (𝒥-cong (sound e))) (𝒥-cong (sound e'))) (λ _ → refl)
    sound (lunit V M) = ℂ.≈.sym (proj₂ subLemma M V)
    sound (runit M) = runit-sound M
    sound (beta M V) =
      ℂ.≈.trans (ℂ.ren-cong (ℂ.sub-cong (β-law ⟦ M ⟧ᶜ) ℂ.≈.refl) (λ _ → refl)) (ℂ.≈.sym (proj₂ subLemma M V))
    sound (assoc M₁ M₂ M) = assocSound M₁ M₂ M
    soundᵃ [] ()
    soundᵃ (e ∷ es) zero    = sound e
    soundᵃ (e ∷ es) (suc i) = soundᵃ es i
