------------------------------------------------------------------------
-- Appendix A.4: interpretation in Freyd PROPs.
--
--   Def. A.12  `CatStructure`: a categorical λml*-structure is a Freyd
--              PROP D with symbol interpretations and a weak closure on
--              its morphisms into 1 (i.e. on U(D), Def. 3.19) — so the
--              axioms are the paper's ⊛ ∘ (J◁ⁿf▷ ⊢ 1) = f, plus the
--              naturality of ◁ⁿ−▷ in n and its compatibility with
--              substitution (REPORT §5, §13);
--   Lemma A.15 `UStr`, `UMor`: U of a categorical structure/morphism is a
--              λml*-structure/morphism (on the nose);
--   Def. A.14  `CatMorphism`;
--   soundness/completeness in categorical structures: `catSound`,
--              `catComplete`;
--   Cor. A.13 = Cor. A.16  `FreeTerm.FTerm` (the free Freyd PROP on the
--              term model is a categorical structure), `CatInitial.initial`
--              (the unique morphism to any categorical structure),
--              `CatInitial.unique`.
--
-- Proof in words.  The weak closure of F(T) = (Sub×_VAL, Sub_CMP, J^Sub)
-- is transported from the term model through the representation of
-- Thm. 3.18: ◁ⁿΓ▷ := {λx. id ⋆ Γ} and ⊛ := {x₁ x₂}; β and the two
-- naturality laws follow from those of T by the naturality of the unit
-- {−} and the fact that whiskered units are substitution steps.
-- Initiality combines Thm. 3.21 with Thm. 4.9: a morphism F(T) → S
-- curries to a morphism of structures T → U(S), which is the
-- interpretation by Thm. 4.9, so the morphism is the uncurried
-- interpretation.  Completeness for categorical structures follows
-- since F(T) is one, and the interpretation in U(F(T)) is the unit
-- {−} of the adjunction (again by Thm. 4.9).
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude hiding (_∘_; id)
open import MFPS.Preoperad
open import MFPS.PROP
open import MFPS.Syntax
open import MFPS.FunctorOps
import MFPS.PROPOperad as PO
import MFPS.FreydSub
import MFPS.Sub
import MFPS.SubCast
import MFPS.SubWhisker
import MFPS.SubPROP
import MFPS.Representable
import MFPS.FreydAdjunction as FA

module MFPS.CatSemantics (Σ : Signature) where

open Signature Σ
open Terms Σ
open import MFPS.Theory Σ using (_≈_; ≈-sym; ≈-trans)
open import MFPS.Semantics Σ
open import MFPS.TermLaws Σ using (termStructure)
open import MFPS.SubstLemma Σ using (soundness)
open import MFPS.Initiality Σ using (module Initial)

private
  variable
    k m n : ℕ
    s : Sort

------------------------------------------------------------------------
-- Definition A.12, Lemma A.15 (objects)
------------------------------------------------------------------------

record CatStructure : Set₁ where
  field
    D  : FreydPROP
    W  : WeaklyClosed (PO.U.UD D)
    σF : ∀ {n} → Func n → FreydPROP.𝕍.Hom D n 1
    σP : ∀ {n} → Proc n → FreydPROP.ℂ.Hom D n 1
  open FreydPROP D public
  open WeaklyClosed W public renaming (app to ⊛; beta to β-law)

UStr : CatStructure → Structure
UStr S = record { M = PO.U.UD S.D ; W = S.W ; σF = S.σF ; σP = S.σP }
  where module S = CatStructure S

-- interpretation, soundness and completeness in categorical structures
module CatInterp (S : CatStructure) = Interp (UStr S)

catSound : (S : CatStructure) {E₁ E₂ : Trm n s} → E₁ ≈ E₂ → CatInterp._⊨_≡_ S n E₁ E₂
catSound S e = soundness e (UStr S)

------------------------------------------------------------------------
-- Definition A.14, Lemma A.15 (morphisms)
------------------------------------------------------------------------

record CatMorphism (S₁ S₂ : CatStructure) : Set where
  private
    module S₁ = CatStructure S₁
    module S₂ = CatStructure S₂
  field
    ℱ : FreydPROPFunctor S₁.D S₂.D
  open FreydPROPFunctor ℱ public
  field
    F-app : ℱᶜ S₁.⊛ S₂.ℂ.≈ S₂.⊛
    F-abs : ∀ {n} (f : S₁.ℂ.Hom (n + 1) 1) → ℱᵛ (S₁.abs f) S₂.𝕍.≈ S₂.abs (ℱᶜ f)
    F-σF  : ∀ {n} (f : Func n) → ℱᵛ (S₁.σF f) S₂.𝕍.≈ S₂.σF f
    F-σP  : ∀ {n} (p : Proc n) → ℱᶜ (S₁.σP p) S₂.ℂ.≈ S₂.σP p

UMor : {S₁ S₂ : CatStructure} → CatMorphism S₁ S₂ → StructureMorphism (UStr S₁) (UStr S₂)
UMor K = record
  { G = PO.UFunctor.UG K.ℱ
  ; closed = record { G-app = K.F-app ; G-abs = K.F-abs }
  ; G-σF = K.F-σF ; G-σP = K.F-σP }
  where module K = CatMorphism K

------------------------------------------------------------------------
-- The free Freyd PROP on the term model is a categorical structure
------------------------------------------------------------------------

module FreeTerm where
  private
    module T = Structure termStructure
  open MFPS.FreydSub T.M
  private
    module V = MFPS.Sub 𝕊ᵥ
    module C = MFPS.Sub T.ℂ
    module VR = MFPS.Representable 𝕊ᵥ
    module CR = MFPS.Representable T.ℂ
    module VCast = MFPS.SubCast 𝕊ᵥ
    module CCast = MFPS.SubCast T.ℂ
    module CW = MFPS.SubWhisker T.ℂ
    module VW = MFPS.SubWhisker 𝕊ᵥ
    module CP = MFPS.SubPROP T.ℂ
    module UT = PO.U FreydSubPROP
  open import MFPS.SubSym T.ℂ using () renaming (_⟶_ to _⟶ᶜ_)
  open import MFPS.SubSym 𝕊ᵥ using () renaming (_⟶_ to _⟶ᵛ_)

  -- abstraction and application on words (Def. A.12 for F(T))
  absʷ : C.Word (n + 1) 1 → V.Word n 1
  absʷ Γ = VR.ηʷ (T.abs (CR.εʷ Γ))

  appʷ : C.Word 2 1
  appʷ = CR.ηʷ T.⊛

  private
    -- the counit commutes with transports
    εʷ-subst : (p : m ≡ n) (Γ : C.Word m 1) → CR.εʷ (subst (λ n → C.Word n 1) p Γ) ≡ subst T.ℂ.Op p (CR.εʷ Γ)
    εʷ-subst refl Γ = refl

    -- whiskered units are substitution steps
    unit-step : ∀ n₁ n₂ {m} (g : T.ℂ.Op m) → C.Cong JImg (n₁ C.⊣ʷ (CR.ηʷ g C.⊢ʷ n₂)) C.⟦ C.sub! n₁ n₂ g ⟧
    unit-step n₁ n₂ g = CCast.ins-arity (+-identityʳ n₁) refl _ refl _ refl g

    unit-stepᵛ : ∀ n₁ n₂ {m} (g : T.𝕍.Op m) → V.Cong (λ _ → ⊤) (n₁ V.⊣ʷ (VR.ηʷ g V.⊢ʷ n₂)) V.⟦ V.sub! n₁ n₂ g ⟧
    unit-stepᵛ n₁ n₂ g = VCast.ins-arity (+-identityʳ n₁) refl _ refl _ refl g

  W-free : WeaklyClosed UT.UD
  W-free = record
    { abs      = absʷ
    ; abs-cong = λ e → VR.η-cong (T.abs-cong (CR.ε-cong cartRulesᶜ e))
    ; app      = appʷ
    ; beta     = λ {n} Γ →
        C.≅-cong {Γ₁ = appʷ} C.≅-refl (CP.0⊣ʷ JImg _)
        ⟶ᶜ C.≅-cong {Γ₁ = appʷ} C.≅-refl (C.≅-≡ (cong C.⟦_⟧ (CCast.ins-irr 0 1 _ refl _ refl _)))
        ⟶ᶜ C.≅-sym (CR.η-nat T.⊛ C.⟦ C.sub! 0 1 (T.𝒥 (T.abs (CR.εʷ Γ))) ⟧)
        ⟶ᶜ CR.η-cong (T.β-law (CR.εʷ Γ))
        ⟶ᶜ CR.η∘ε Γ
    ; abs-ren  = λ {m} {n} Γ r →
        V.≅-≡ (cong (λ z → VR.ηʷ (T.abs z)) (C.⋆-++ T.ℂ.idₒ Γ C.⟦ C.rn (r +ʳ idʳ {1}) ⟧))
        ⟶ᵛ VR.η-cong (T.abs-ren (CR.εʷ Γ) r)
        ⟶ᵛ VR.η-ren (T.abs (CR.εʷ Γ)) r
    ; abs-sub  = λ {m₁} {m₂} {n} Γ Δ p p' →
        VR.η-cong (T.abs-cong (T.ℂ.≈.trans (T.ℂ.≈.reflexive (εʷ-subst p _))
          (T.ℂ.subst-cong p (T.ℂ.≈.trans (T.ℂ.≈.reflexive (C.⋆-++ T.ℂ.idₒ Γ _))
            (⋆-soundᶜ (CW.⊣-stable m₁ (CW.⊢-stable (m₂ + 1) (JSub-cong (V.≅-sym (VR.η∘ε Δ)))) ⟶ᶜ unit-step m₁ (m₂ + 1) (T.𝒥 (VR.εʷ Δ))) (CR.εʷ Γ))))))
        ⟶ᵛ VR.η-cong (T.abs-sub (CR.εʷ Γ) (VR.εʷ Δ) p p')
        ⟶ᵛ VR.η-cong (T.𝕍.sub-cong (T.abs-cong (T.ℂ.≈.reflexive (sym (εʷ-subst p' Γ)))) T.𝕍.≈.refl)
        ⟶ᵛ VR.η-nat _ V.⟦ V.sub! m₁ m₂ (VR.εʷ Δ) ⟧
        ⟶ᵛ V.≅-cong {Γ₁ = VR.ηʷ _} V.≅-refl (V.≅-sym (unit-stepᵛ m₁ m₂ (VR.εʷ Δ)))
        ⟶ᵛ V.≅-cong {Γ₁ = VR.ηʷ _} V.≅-refl (VW.⊣-stable m₁ (VW.⊢-stable m₂ (VR.η∘ε Δ)))
    }

  -- Corollary A.13 / A.16, the object
  FTerm : CatStructure
  FTerm = record { D = FreydSubPROP ; W = W-free ; σF = λ f → VR.ηʷ (T.σF f) ; σP = λ p → CR.ηʷ (T.σP p) }

------------------------------------------------------------------------
-- Corollary A.13 / A.16: F(T) is initial among categorical structures
------------------------------------------------------------------------

module CatInitial (S : CatStructure) where
  private
    module T = Structure termStructure
    module S = CatStructure S
    module FT = FreeTerm
    US = UStr S
    module I = StructureMorphism (Initial.interp US)
    module Unc = FA.Uncurry T.M S.D I.G
    module Adj = FA.Adjunction T.M S.D
    open MFPS.FreydSub T.M using (𝕊ᵥ; FreydSubPROP)
    module VR = MFPS.Representable 𝕊ᵥ
    module CR = MFPS.Representable T.ℂ

  -- existence: the uncurried interpretation
  initial : CatMorphism FT.FTerm S
  initial = record
    { ℱ     = Unc.uncurry
    ; F-app = S.ℂ.≈.trans (Unc.Sᶜ.curry∘uncurry T.⊛) I.G-app
    ; F-abs = λ Γ →
        S.𝕍.≈.trans (Unc.Sᵛ.curry∘uncurry (T.abs (CR.εʷ Γ)))
        (S.𝕍.≈.trans (I.G-abs (CR.εʷ Γ))
                     (S.abs-cong (S.ℂ.≈.trans (S.ℂ.≈.sym (Unc.Sᶜ.curry∘uncurry (CR.εʷ Γ))) (Unc.Sᶜ.⌊⌋-cong (CR.η∘ε Γ)))))
    ; F-σF  = λ f → S.𝕍.≈.trans (Unc.Sᵛ.curry∘uncurry (T.σF f)) (I.G-σF f)
    ; F-σP  = λ p → S.ℂ.≈.trans (Unc.Sᶜ.curry∘uncurry (T.σP p)) (I.G-σP p) }

  -- a categorical morphism out of F(T) curries to a morphism of
  -- structures out of T (the closure and the symbols are preserved
  -- because {−} is a bijection, Thm. 3.18)
  curryMor : CatMorphism FT.FTerm S → StructureMorphism termStructure US
  curryMor K = record
    { G = FA.Curry.curry T.M S.D K.ℱ
    ; closed = record
        { G-app = K.F-app
        ; G-abs = λ f → S.𝕍.≈.trans (K.ℱᵛ-cong (VR.η-cong (T.abs-cong (T.ℂ.≈.sym (CR.ε∘η f))))) (K.F-abs (CR.ηʷ f)) }
    ; G-σF = K.F-σF
    ; G-σP = K.F-σP }
    where module K = CatMorphism K

  -- uniqueness: by Thm. 4.9 the curried morphism is the interpretation,
  -- and by Thm. 3.21 the morphism is the uncurried curried morphism
  unique : (K : CatMorphism FT.FTerm S) → CatMorphism.ℱ K ≈ᶠ Unc.uncurry
  unique K =
    ≈ᶠ-trans {D₁ = FreydSubPROP} {D₂ = S.D} {F = CatMorphism.ℱ K} {F' = FA.Uncurry.uncurry T.M S.D (FA.Curry.curry T.M S.D (CatMorphism.ℱ K))} {F'' = Unc.uncurry}
      (≈ᶠ-sym {D₁ = FreydSubPROP} {D₂ = S.D} {F = FA.Uncurry.uncurry T.M S.D (FA.Curry.curry T.M S.D (CatMorphism.ℱ K))} {F' = CatMorphism.ℱ K} (Adj.uncurry∘curry (CatMorphism.ℱ K)))
      (Adj.uncurry-cong {G = FA.Curry.curry T.M S.D (CatMorphism.ℱ K)} {G' = I.G} (Initial.unique US (curryMor K)))


------------------------------------------------------------------------
-- Completeness for categorical structures: an equation valid in every
-- categorical structure is provable (F(T) is a categorical structure,
-- and the interpretation in U(F(T)) is the unit {−} of the adjunction)
------------------------------------------------------------------------

module CatCompleteness where
  private
    module T = Structure termStructure
    module FT = FreeTerm
    open MFPS.FreydSub T.M using (𝕊ᵥ; cartRulesᵥ; cartRulesᶜ)
    module VR = MFPS.Representable 𝕊ᵥ
    module CR = MFPS.Representable T.ℂ
    module V = MFPS.Sub 𝕊ᵥ
    module C = MFPS.Sub T.ℂ

    -- U(F(T)), kept opaque
    UFT : Structure
    UFT = UStr FT.FTerm

  idCat : CatMorphism FT.FTerm FT.FTerm
  idCat = record { ℱ = idᶠ ; F-app = C.≅-refl ; F-abs = λ _ → V.≅-refl ; F-σF = λ _ → V.≅-refl ; F-σP = λ _ → C.≅-refl }

  -- the unit T → U(F(T)) of the adjunction, as a morphism of structures
  unitMor : StructureMorphism termStructure UFT
  unitMor = CatInitial.curryMor FT.FTerm idCat

  private
    -- the interpretation in U(F(T)) is {−}  (Thm. 4.9)
    uᵛ : (V : Val n) → VR.ηʷ V V.≅ˣ Interp.⟦_⟧ᵛ UFT V
    uᵛ = proj₁ (Initial.unique UFT unitMor)

    uᶜ : (M : Cmp n) → C.Cong (MFPS.FreydSub.JImg T.M) (CR.ηʷ M) (Interp.⟦_⟧ᶜ UFT M)
    uᶜ = proj₂ (Initial.unique UFT unitMor)

  catComplete : {E₁ E₂ : Trm n s} → ((S : CatStructure) → CatInterp._⊨_≡_ S n E₁ E₂) → E₁ ≈ E₂
  catComplete {s = val} {E₁} {E₂} h =
    ≈-trans (≈-sym (VR.ε∘η E₁))
    (≈-trans (VR.ε-cong cartRulesᵥ (V.≅-trans (uᵛ E₁) (V.≅-trans (h FT.FTerm) (V.≅-sym (uᵛ E₂)))))
             (VR.ε∘η E₂))
  catComplete {s = cmp} {E₁} {E₂} h =
    ≈-trans (≈-sym (CR.ε∘η E₁))
    (≈-trans (CR.ε-cong cartRulesᶜ (C.≅-trans (uᶜ E₁) (C.≅-trans (h FT.FTerm) (C.≅-sym (uᶜ E₂)))))
             (CR.ε∘η E₂))
