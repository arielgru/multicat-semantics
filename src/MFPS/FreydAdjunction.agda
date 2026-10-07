------------------------------------------------------------------------
-- Section 3.5 / Appendix A.2: the Freyd adjunction F ⊣ U (Theorem 3.21).
--
--   F : FreydOp → FreydPROP,  F(M) = (Sub×_𝕍, Sub_ℂ, J^Sub)   (Def. 3.20, MFPS.FreydSub)
--   U : FreydPROP → FreydOp,  U(D) = morphisms into 1           (Def. 3.19, MFPS.PROPOperad)
--
-- Contents (paper ↔ code):
--   Lemma A.2   `FreeFunctorial`: F preserves identities and composition
--   Def. A.3, Lemma A.4   `Curry.curry`: a Freyd PROP functor F(M) → D
--               restricts, along {0 ⊣ − ⊢ 0}, to a Freyd operad functor M → U(D)
--   Def. A.5, Lemmas A.6–A.8, Cor. A.9   `Uncurry.uncurry`: a Freyd operad
--               functor M → U(D) extends to a Freyd PROP functor F(M) → D
--   Lemma A.10  `Adjunction.uncurry∘curry`, `Adjunction.curry∘uncurry`
--   Thm. 3.21 / Cor. A.11   `Adjunction` together with `Naturality`
--
-- Proof in words.  Uncurrying interprets a word step by step in D
-- (MFPS.Uncurry), which respects the congruence because D validates
-- every rule of Fig. 3 (Lemma A.7); it commutes with J^Sub because J
-- is a functor and the cast morphisms are J-images (Lemma A.8).
-- Currying restricts to the singleton words {0 ⊣ g ⊢ 0}; it is a
-- Freyd operad functor because {−} is natural (Thm. 3.18: {f ⋆ Γ} ≅
-- {f} ∘ Γ) and a singleton step {n₁ ⊣ g ⊢ n₂} is n₁ ⊣ ({g} ⊢ n₂) up to
-- casts.  The two operations are inverse: uncurrying the restriction
-- of ℱ gives back ℱ by induction on words (each step is ℱ of the
-- corresponding singleton word, by (S) and the strictness of ℱ), and
-- restricting the uncurried G gives back G since ⌊{0 ⊣ g ⊢ 0}⌋ = G g.
-- Naturality in both variables holds on the nose.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude hiding (_∘_; id)
open import MFPS.Preoperad
open import MFPS.PROP
open import MFPS.FunctorOps
import MFPS.PROPOperad as PO
import MFPS.FreydSub
import MFPS.FreydSubFunctor
import MFPS.Sub
import MFPS.SubCast
import MFPS.Representable
import MFPS.PROPHet
import MFPS.Uncurry

module MFPS.FreydAdjunction where

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Lemma A.2: F is a functor
------------------------------------------------------------------------

module FreeFunctorial where

  module _ (M : FreydOperad) where
    private
      module FS = MFPS.FreydSub M
      module FI = FreydPROPFunctor (MFPS.FreydSubFunctor.FSub {M} {M} idᴼ)
      module V = MFPS.Sub FS.𝕊ᵥ
      module C = MFPS.Sub (FreydOperad.ℂ M)

    FSub-idᵛ : (Γ : V.Word m n) → FI.ℱᵛ Γ ≡ Γ
    FSub-idᵛ V.ε = refl
    FSub-idᵛ (V.ins _ _ _ _ _ V.∷ Γ) = cong (_ V.∷_) (FSub-idᵛ Γ)
    FSub-idᵛ (V.rn _ V.∷ Γ) = cong (_ V.∷_) (FSub-idᵛ Γ)

    FSub-idᶜ : (Γ : C.Word m n) → FI.ℱᶜ Γ ≡ Γ
    FSub-idᶜ C.ε = refl
    FSub-idᶜ (C.ins _ _ _ _ _ C.∷ Γ) = cong (_ C.∷_) (FSub-idᶜ Γ)
    FSub-idᶜ (C.rn _ C.∷ Γ) = cong (_ C.∷_) (FSub-idᶜ Γ)

    FSub-id : MFPS.FreydSubFunctor.FSub {M} {M} idᴼ ≈ᶠ idᶠ
    FSub-id = (λ Γ → V.≅-≡ (FSub-idᵛ Γ)) , (λ Γ → C.≅-≡ (FSub-idᶜ Γ))

  module _ {M₁ M₂ M₃ : FreydOperad} (G₂ : FreydOperadFunctor M₂ M₃) (G₁ : FreydOperadFunctor M₁ M₂) where
    private
      module F₁ = FreydPROPFunctor (MFPS.FreydSubFunctor.FSub G₁)
      module F₂ = FreydPROPFunctor (MFPS.FreydSubFunctor.FSub G₂)
      module F₂₁ = FreydPROPFunctor (MFPS.FreydSubFunctor.FSub (G₂ ∘ᴼ G₁))
      module FS₁ = MFPS.FreydSub M₁
      module V₁ = MFPS.Sub FS₁.𝕊ᵥ
      module C₁ = MFPS.Sub (FreydOperad.ℂ M₁)
      module FS₃ = MFPS.FreydSub M₃
      module V₃ = MFPS.Sub FS₃.𝕊ᵥ
      module C₃ = MFPS.Sub (FreydOperad.ℂ M₃)

    FSub-∘ᵛ : (Γ : V₁.Word m n) → F₂₁.ℱᵛ Γ ≡ F₂.ℱᵛ (F₁.ℱᵛ Γ)
    FSub-∘ᵛ V₁.ε = refl
    FSub-∘ᵛ (V₁.ins _ _ _ _ _ V₁.∷ Γ) = cong (_ V₃.∷_) (FSub-∘ᵛ Γ)
    FSub-∘ᵛ (V₁.rn _ V₁.∷ Γ) = cong (_ V₃.∷_) (FSub-∘ᵛ Γ)

    FSub-∘ᶜ : (Γ : C₁.Word m n) → F₂₁.ℱᶜ Γ ≡ F₂.ℱᶜ (F₁.ℱᶜ Γ)
    FSub-∘ᶜ C₁.ε = refl
    FSub-∘ᶜ (C₁.ins _ _ _ _ _ C₁.∷ Γ) = cong (_ C₃.∷_) (FSub-∘ᶜ Γ)
    FSub-∘ᶜ (C₁.rn _ C₁.∷ Γ) = cong (_ C₃.∷_) (FSub-∘ᶜ Γ)

    FSub-∘ : MFPS.FreydSubFunctor.FSub (G₂ ∘ᴼ G₁) ≈ᶠ (MFPS.FreydSubFunctor.FSub G₂ ∘ᶠ MFPS.FreydSubFunctor.FSub G₁)
    FSub-∘ = (λ Γ → V₃.≅-≡ (FSub-∘ᵛ Γ)) , (λ Γ → C₃.≅-≡ (FSub-∘ᶜ Γ))

------------------------------------------------------------------------
-- Uncurrying: FreydOp(M, U D) → FreydPROP(F M, D)
------------------------------------------------------------------------

module Uncurry (M : FreydOperad) (D : FreydPROP) (G : FreydOperadFunctor M (PO.U.UD D)) where
  private
    module M = FreydOperad M
    module D = FreydPROP D
    module UD = PO.U D
    module FS = MFPS.FreydSub M
    module V = MFPS.Sub FS.𝕊ᵥ
    module C = MFPS.Sub M.ℂ
    module UV = MFPS.Uncurry FS.𝕊ᵥ D.𝕍.P
    module UC = MFPS.Uncurry M.ℂ D.ℂ
    module HC = MFPS.PROPHet D.ℂ
  open FreydOperadFunctor G

  -- the interpretations of the generators
  Iᵛ : UV.Interp
  Iᵛ = record { A = UD.ρ-action ; G = 𝒢ᵛ ; G-cong = 𝒢ᵛ-cong ; G-id = 𝒢ᵛ-id ; G-sub = 𝒢ᵛ-sub ; G-ren = 𝒢ᵛ-ren }

  Iᶜ : UC.Interp
  Iᶜ = record { A = UD.Jρ-action ; G = 𝒢ᶜ ; G-cong = 𝒢ᶜ-cong ; G-id = 𝒢ᶜ-id ; G-sub = 𝒢ᶜ-sub ; G-ren = 𝒢ᶜ-ren }

  -- every value is central, discardable and copyable in the cartesian
  -- PROP 𝕍; the J-images are so in ℂ by functoriality of J
  CIᵛ : UV.CartInterp Iᵛ (λ _ → ⊤)
  CIᵛ = record
    { cart-central = λ {_} {g} _ → D.𝕍.prop (𝒢ᵛ g)
    ; cart-!       = λ {_} {g} _ → D.𝕍.!-nat (𝒢ᵛ g)
    ; cart-Δ       = λ {_} {g} _ → D.𝕍.Δ-nat (𝒢ᵛ g) }

  CIᶜ : UC.CartInterp Iᶜ FS.JImg
  CIᶜ = record
    { cart-central = λ { (v , refl) → HC.central-≈ (G-J v) (D.J-central (𝒢ᵛ v)) }
    ; cart-!       = λ { (v , refl) → D.ℂ.≈.trans (D.ℂ.∘-cong D.ℂ.≈.refl (G-J v)) (UD.J-discardable (𝒢ᵛ v)) }
    ; cart-Δ       = λ { (v , refl) →
        D.ℂ.≈.trans (D.ℂ.∘-cong D.ℂ.≈.refl (G-J v))
        (D.ℂ.≈.trans (UD.J-copyable (𝒢ᵛ v))
                     (D.ℂ.∘-cong (D.ℂ.∘-cong (D.ℂ.⊢-cong (D.ℂ.≈.sym (G-J v))) (D.ℂ.⊣-cong (D.ℂ.≈.sym (G-J v)))) D.ℂ.≈.refl)) } }

  module Sᵛ = UV.Sound Iᵛ CIᵛ
  module Sᶜ = UC.Sound Iᶜ CIᶜ

  -- J sends cast morphisms to cast morphisms
  private
    𝒥-cast : (p : m ≡ n) → D.𝒥 (D.𝕍.castₕ p) D.ℂ.≈ D.ℂ.castₕ p
    𝒥-cast refl = D.𝒥-id

  -- Lemma A.8: ⌊J^Sub Γ⌋ = J ⌊Γ⌋
  uncurry-J : (Γ : V.Word m n) → Sᶜ.⌊ FS.JSub Γ ⌋ D.ℂ.≈ D.𝒥 (Sᵛ.⌊ Γ ⌋)
  uncurry-J V.ε = D.ℂ.≈.sym D.𝒥-id
  uncurry-J (V.rn r V.∷ Γ) =
    D.ℂ.≈.trans (D.ℂ.∘-cong D.ℂ.≈.refl (uncurry-J Γ)) (D.ℂ.≈.sym (D.𝒥-∘ _ _))
  uncurry-J (V.ins n₁ n₂ p q v V.∷ Γ) =
    D.ℂ.≈.trans (D.ℂ.∘-cong step (uncurry-J Γ)) (D.ℂ.≈.sym (D.𝒥-∘ _ _))
    where
      step : D.ℂ.castₕ (sym q) D.ℂ.∘ ((n₁ D.ℂ.⊣ (𝒢ᶜ (M.𝒥 v) D.ℂ.⊢ n₂)) D.ℂ.∘ D.ℂ.castₕ p)
             D.ℂ.≈ D.𝒥 (D.𝕍.castₕ (sym q) D.𝕍.∘ ((n₁ D.𝕍.⊣ (𝒢ᵛ v D.𝕍.⊢ n₂)) D.𝕍.∘ D.𝕍.castₕ p))
      step =
        D.ℂ.≈.trans (D.ℂ.∘-cong (D.ℂ.≈.sym (𝒥-cast (sym q)))
                                (D.ℂ.∘-cong (D.ℂ.⊣-cong (D.ℂ.⊢-cong (G-J v))) (D.ℂ.≈.sym (𝒥-cast p))))
        (D.ℂ.≈.sym (D.ℂ.≈.trans (D.𝒥-∘ _ _)
                   (D.ℂ.∘-cong D.ℂ.≈.refl (D.ℂ.≈.trans (D.𝒥-∘ _ _)
                                          (D.ℂ.∘-cong (D.ℂ.≈.trans (D.𝒥-⊣ _) (D.ℂ.⊣-cong (D.𝒥-⊢ _))) D.ℂ.≈.refl)))))

  -- Corollary A.9
  uncurry : FreydPROPFunctor FS.FreydSubPROP D
  uncurry = record
    { Fᵛ  = record { functor = Sᵛ.⌊⌋-functor ; F-ρ = λ r → D.𝕍.∘-idʳ _ }
    ; Fᶜ  = Sᶜ.⌊⌋-functor
    ; F-J = uncurry-J }

------------------------------------------------------------------------
-- Currying: FreydPROP(F M, D) → FreydOp(M, U D)
------------------------------------------------------------------------

module Curry (M : FreydOperad) (D : FreydPROP) (ℱ : FreydPROPFunctor (MFPS.FreydSub.FreydSubPROP M) D) where
  private
    module M = FreydOperad M
    module D = FreydPROP D
    module UD = PO.U D
    module FS = MFPS.FreydSub M
    module V = MFPS.Sub FS.𝕊ᵥ
    module C = MFPS.Sub M.ℂ
    module VR = MFPS.Representable FS.𝕊ᵥ
    module CR = MFPS.Representable M.ℂ
    module VCast = MFPS.SubCast FS.𝕊ᵥ
    module CCast = MFPS.SubCast M.ℂ
  open FreydPROPFunctor ℱ

  -- a singleton substitution step is a whiskered unit, up to casts
  ℱᵛ-sub! : ∀ n₁ n₂ {m} (g : M.𝕍.Op m) → ℱᵛ V.⟦ V.sub! n₁ n₂ g ⟧ D.𝕍.≈ n₁ D.𝕍.⊣ (ℱᵛ (VR.ηʷ g) D.𝕍.⊢ n₂)
  ℱᵛ-sub! n₁ n₂ g =
    D.𝕍.≈.trans (ℱᵛ-cong (V.≅-sym (VCast.ins-arity (+-identityʳ n₁) refl _ refl _ refl g)))
    (D.𝕍.≈.trans (ℱᵛ-⊣ _) (D.𝕍.⊣-cong (ℱᵛ-⊢ _)))

  ℱᶜ-sub! : ∀ n₁ n₂ {m} (g : M.ℂ.Op m) → ℱᶜ C.⟦ C.sub! n₁ n₂ g ⟧ D.ℂ.≈ n₁ D.ℂ.⊣ (ℱᶜ (CR.ηʷ g) D.ℂ.⊢ n₂)
  ℱᶜ-sub! n₁ n₂ g =
    D.ℂ.≈.trans (ℱᶜ-cong (C.≅-sym (CCast.ins-arity (+-identityʳ n₁) refl _ refl _ refl g)))
    (D.ℂ.≈.trans (ℱᶜ-⊣ _) (D.ℂ.⊣-cong (ℱᶜ-⊢ _)))

  -- renaming steps of Sub_ℂ are J-images
  ℱᶜ-rn : (r : Ren n m) → ℱᶜ C.⟦ C.rn r ⟧ D.ℂ.≈ D.𝒥 (D.𝕍.ρ r)
  ℱᶜ-rn r = D.ℂ.≈.trans (F-J V.⟦ V.rn r ⟧) (D.𝒥-cong (ℱᵛ-ρ r))

  -- Definition A.3 / Lemma A.4
  curry : FreydOperadFunctor M UD.UD
  curry = record
    { Gᵛ = record
        { F      = λ v → ℱᵛ (VR.ηʷ v)
        ; F-cong = λ e → ℱᵛ-cong (VR.η-cong e)
        ; F-id   = D.𝕍.≈.trans (ℱᵛ-cong VR.η-id) ℱᵛ-id
        ; F-sub  = λ {n₁} {n₂} f g →
            D.𝕍.≈.trans (ℱᵛ-cong (VR.η-nat f V.⟦ V.sub! n₁ n₂ g ⟧))
            (D.𝕍.≈.trans (ℱᵛ-∘ _ _) (D.𝕍.∘-cong D.𝕍.≈.refl (ℱᵛ-sub! n₁ n₂ g))) }
    ; Gᵛ-ren = record { F-ren = λ v r →
        D.𝕍.≈.trans (ℱᵛ-cong (VR.η-ren v r)) (D.𝕍.≈.trans (ℱᵛ-∘ _ _) (D.𝕍.∘-cong D.𝕍.≈.refl (ℱᵛ-ρ r))) }
    ; Gᶜ = record
        { F      = λ f → ℱᶜ (CR.ηʷ f)
        ; F-cong = λ e → ℱᶜ-cong (CR.η-cong e)
        ; F-id   = D.ℂ.≈.trans (ℱᶜ-cong CR.η-id) ℱᶜ-id
        ; F-sub  = λ {n₁} {n₂} f g →
            D.ℂ.≈.trans (ℱᶜ-cong (CR.η-nat f C.⟦ C.sub! n₁ n₂ g ⟧))
            (D.ℂ.≈.trans (ℱᶜ-∘ _ _) (D.ℂ.∘-cong D.ℂ.≈.refl (ℱᶜ-sub! n₁ n₂ g))) }
    ; Gᶜ-ren = record { F-ren = λ f r →
        D.ℂ.≈.trans (ℱᶜ-cong (CR.η-ren f r)) (D.ℂ.≈.trans (ℱᶜ-∘ _ _) (D.ℂ.∘-cong D.ℂ.≈.refl (ℱᶜ-rn r))) }
    ; G-J = λ v → F-J (VR.ηʷ v) }

------------------------------------------------------------------------
-- Theorem 3.21: the two operations are mutually inverse
------------------------------------------------------------------------

module Adjunction (M : FreydOperad) (D : FreydPROP) where
  private
    module M = FreydOperad M
    module D = FreydPROP D
    module UD = PO.U D
    module FS = MFPS.FreydSub M
    module V = MFPS.Sub FS.𝕊ᵥ
    module C = MFPS.Sub M.ℂ
    module VR = MFPS.Representable FS.𝕊ᵥ
    module CR = MFPS.Representable M.ℂ

  open Uncurry M D using (uncurry)
  open Curry M D using (curry)

  -- Lemma A.10, second item
  curry∘uncurry : (G : FreydOperadFunctor M UD.UD) → curry (uncurry G) ≈ᴼ G
  curry∘uncurry G = Sᵛ.curry∘uncurry , Sᶜ.curry∘uncurry
    where
      module Sᵛ = Uncurry.Sᵛ M D G
      module Sᶜ = Uncurry.Sᶜ M D G

  -- Lemma A.10, first item
  private
    ρ-cast : (p : m ≡ n) → D.𝕍.ρ (castʳ p) D.𝕍.≈ D.𝕍.castₕ (sym p)
    ρ-cast refl = D.𝕍.ρ-id

    ρ-cast' : (p : m ≡ n) → D.𝕍.ρ (castʳ (sym p)) D.𝕍.≈ D.𝕍.castₕ p
    ρ-cast' refl = D.𝕍.ρ-id

  module _ (ℱ : FreydPROPFunctor FS.FreydSubPROP D) where
    open FreydPROPFunctor ℱ
    open Curry M D ℱ using (ℱᵛ-sub!; ℱᶜ-sub!; ℱᶜ-rn)
    private
      module Sᵛ = Uncurry.Sᵛ M D (curry ℱ)
      module Sᶜ = Uncurry.Sᶜ M D (curry ℱ)

    uncurry∘curryᵛ : (Γ : V.Word m n) → Sᵛ.⌊ Γ ⌋ D.𝕍.≈ ℱᵛ Γ
    uncurry∘curryᵛ V.ε = D.𝕍.≈.sym ℱᵛ-id
    uncurry∘curryᵛ (V.rn r V.∷ Γ) =
      D.𝕍.≈.trans (D.𝕍.∘-cong (D.𝕍.≈.sym (ℱᵛ-ρ r)) (uncurry∘curryᵛ Γ)) (D.𝕍.≈.sym (ℱᵛ-∘ Γ _))
    uncurry∘curryᵛ (V.ins n₁ n₂ p q g V.∷ Γ) =
      D.𝕍.≈.trans (D.𝕍.∘-cong (D.𝕍.≈.sym step) (uncurry∘curryᵛ Γ)) (D.𝕍.≈.sym (ℱᵛ-∘ Γ _))
      where
        step : ℱᵛ V.⟦ V.ins n₁ n₂ p q g ⟧ D.𝕍.≈ D.𝕍.castₕ (sym q) D.𝕍.∘ ((n₁ D.𝕍.⊣ (ℱᵛ (VR.ηʷ g) D.𝕍.⊢ n₂)) D.𝕍.∘ D.𝕍.castₕ p)
        step =
          D.𝕍.≈.trans (ℱᵛ-cong (V.S∙ n₁ n₂ p q g))
          (D.𝕍.≈.trans (ℱᵛ-∘ _ _)
          (D.𝕍.∘-cong (D.𝕍.≈.trans (ℱᵛ-ρ (castʳ q)) (ρ-cast q))
                      (D.𝕍.≈.trans (ℱᵛ-∘ _ _) (D.𝕍.∘-cong (ℱᵛ-sub! n₁ n₂ g) (D.𝕍.≈.trans (ℱᵛ-ρ (castʳ (sym p))) (ρ-cast' p))))))

    uncurry∘curryᶜ : (Γ : C.Word m n) → Sᶜ.⌊ Γ ⌋ D.ℂ.≈ ℱᶜ Γ
    uncurry∘curryᶜ C.ε = D.ℂ.≈.sym ℱᶜ-id
    uncurry∘curryᶜ (C.rn r C.∷ Γ) =
      D.ℂ.≈.trans (D.ℂ.∘-cong (D.ℂ.≈.sym (ℱᶜ-rn r)) (uncurry∘curryᶜ Γ)) (D.ℂ.≈.sym (ℱᶜ-∘ Γ _))
    uncurry∘curryᶜ (C.ins n₁ n₂ p q g C.∷ Γ) =
      D.ℂ.≈.trans (D.ℂ.∘-cong (D.ℂ.≈.sym step) (uncurry∘curryᶜ Γ)) (D.ℂ.≈.sym (ℱᶜ-∘ Γ _))
      where
        step : ℱᶜ C.⟦ C.ins n₁ n₂ p q g ⟧ D.ℂ.≈ D.ℂ.castₕ (sym q) D.ℂ.∘ ((n₁ D.ℂ.⊣ (ℱᶜ (CR.ηʷ g) D.ℂ.⊢ n₂)) D.ℂ.∘ D.ℂ.castₕ p)
        step =
          D.ℂ.≈.trans (ℱᶜ-cong (C.S∙ n₁ n₂ p q g))
          (D.ℂ.≈.trans (ℱᶜ-∘ _ _)
          (D.ℂ.∘-cong (D.ℂ.≈.trans (ℱᶜ-rn (castʳ q)) (D.ℂ.≈.trans (D.𝒥-cong (ρ-cast q)) (𝒥-cast (sym q))))
                      (D.ℂ.≈.trans (ℱᶜ-∘ _ _) (D.ℂ.∘-cong (ℱᶜ-sub! n₁ n₂ g)
                         (D.ℂ.≈.trans (ℱᶜ-rn (castʳ (sym p))) (D.ℂ.≈.trans (D.𝒥-cong (ρ-cast' p)) (𝒥-cast p)))))))
          where
            𝒥-cast : (e : m ≡ n) → D.𝒥 (D.𝕍.castₕ e) D.ℂ.≈ D.ℂ.castₕ e
            𝒥-cast refl = D.𝒥-id

    uncurry∘curry : uncurry (curry ℱ) ≈ᶠ ℱ
    uncurry∘curry = uncurry∘curryᵛ , uncurry∘curryᶜ

  -- uncurrying respects pointwise equality of functors
  module _ {G G' : FreydOperadFunctor M UD.UD} (e : G ≈ᴼ G') where
    private
      module S = Uncurry M D G
      module S' = Uncurry M D G'

    uncurry-congᵛ : (Γ : V.Word m n) → S.Sᵛ.⌊ Γ ⌋ D.𝕍.≈ S'.Sᵛ.⌊ Γ ⌋
    uncurry-congᵛ V.ε = D.𝕍.≈.refl
    uncurry-congᵛ (V.rn r V.∷ Γ) = D.𝕍.∘-cong D.𝕍.≈.refl (uncurry-congᵛ Γ)
    uncurry-congᵛ (V.ins n₁ n₂ p q g V.∷ Γ) =
      D.𝕍.∘-cong (D.𝕍.∘-cong D.𝕍.≈.refl (D.𝕍.∘-cong (D.𝕍.⊣-cong (D.𝕍.⊢-cong (proj₁ e g))) D.𝕍.≈.refl)) (uncurry-congᵛ Γ)

    uncurry-congᶜ : (Γ : C.Word m n) → S.Sᶜ.⌊ Γ ⌋ D.ℂ.≈ S'.Sᶜ.⌊ Γ ⌋
    uncurry-congᶜ C.ε = D.ℂ.≈.refl
    uncurry-congᶜ (C.rn r C.∷ Γ) = D.ℂ.∘-cong D.ℂ.≈.refl (uncurry-congᶜ Γ)
    uncurry-congᶜ (C.ins n₁ n₂ p q g C.∷ Γ) =
      D.ℂ.∘-cong (D.ℂ.∘-cong D.ℂ.≈.refl (D.ℂ.∘-cong (D.ℂ.⊣-cong (D.ℂ.⊢-cong (proj₂ e g))) D.ℂ.≈.refl)) (uncurry-congᶜ Γ)

    uncurry-cong : uncurry G ≈ᶠ uncurry G'
    uncurry-cong = uncurry-congᵛ , uncurry-congᶜ

------------------------------------------------------------------------
-- Naturality of the bijection, on the nose
------------------------------------------------------------------------

module Naturality where

  -- in the Freyd PROP: curry (K ∘ ℱ) = U(K) ∘ curry ℱ
  natD : (M : FreydOperad) {D D' : FreydPROP} (K : FreydPROPFunctor D D')
    (ℱ : FreydPROPFunctor (MFPS.FreydSub.FreydSubPROP M) D)
    → Curry.curry M D' (K ∘ᶠ ℱ) ≈ᴼ (PO.UFunctor.UG K ∘ᴼ Curry.curry M D ℱ)
  natD M {D} {D'} K ℱ = (λ _ → D'.𝕍.≈.refl) , (λ _ → D'.ℂ.≈.refl)
    where module D' = FreydPROP D'

  -- in the Freyd operad: curry (ℱ ∘ F(H)) = curry ℱ ∘ H
  natM : {M M' : FreydOperad} (D : FreydPROP) (H : FreydOperadFunctor M' M)
    (ℱ : FreydPROPFunctor (MFPS.FreydSub.FreydSubPROP M) D)
    → Curry.curry M' D (ℱ ∘ᶠ MFPS.FreydSubFunctor.FSub H) ≈ᴼ (Curry.curry M D ℱ ∘ᴼ H)
  natM D H ℱ = (λ _ → D.𝕍.≈.refl) , (λ _ → D.ℂ.≈.refl)
    where module D = FreydPROP D
