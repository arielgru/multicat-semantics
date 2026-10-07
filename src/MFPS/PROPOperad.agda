------------------------------------------------------------------------
-- Definition 3.19 / Lemma A.1: the forgetful functor U : FreydPROP → FreydOp.
--
-- On objects, U(𝕍, ℂ, J) has V^U(n) = 𝕍(n ⇒ 1), C^U(n) = ℂ(n ⇒ 1), with
--   id := id₁,   f{n₁ ⊣ g ⊢ n₂} := f ∘ (n₁ ⊣ (g ⊢ n₂)),
--   v[r] := v ∘ ρ r  in V^U,   f[r] := f ∘ J(ρ r)  in C^U,
-- and J^U the restriction of J.
--
-- Proof in words (Lemma A.1).  Every law of a Freyd operad is one of
-- the identities of MFPS.PROPHet precomposed with the operation f:
-- unit laws (`core-lunit`, `core-runit`), associativity (`core-assoc`),
-- the renaming/substitution interchange (`core-N`), the symmetry laws
-- (`core-Sℓ`, `core-Sr`), commutation (`core-CEN`, from centrality in
-- the PROP), and the naturality of discard/copy (`core-D`, `core-C`,
-- from the naturality of !, Δ in the cartesian PROP, transported to ℂ
-- along J by functoriality — this is where the discardability and
-- copyability of J-images in ℂ (REPORT §1(b)) come from).
--
-- The construction is done once for a pre-PROP with an action of the
-- renamings (`Restrict`) and instantiated twice: for 𝕍 with ρ and for ℂ
-- with J ∘ ρ (`U`).  `UFunctor` is U on morphisms: restriction to
-- codomain 1.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude hiding (_∘_; id)
open import MFPS.PROP
open import MFPS.Preoperad
import MFPS.PROPHet

module MFPS.PROPOperad where

private
  variable
    k m n : ℕ

------------------------------------------------------------------------
-- The morphisms into 1 of a pre-PROP with an action of renamings form
-- a symmetric Ren-cartesian preoperad
------------------------------------------------------------------------

module Restrict (D : PrePROP) (A : MFPS.PROPHet.RenAction D) where
  open PrePROP D
  open MFPS.PROPHet D
  open RenAction A
  open WithR A

  U-pre : Preoperad
  U-pre = record
    { Op = λ n → Hom n 1
    ; _≈_ = _≈_
    ; ≈-equiv = ≈-equiv
    ; idₒ = idₕ
    ; sub = λ n₁ n₂ f g → f ∘ (n₁ ⊣ (g ⊢ n₂))
    ; sub-cong = λ e e' → ∘-cong e (⊣-cong (⊢-cong e'))
    ; lunit = λ f p → ≋→≈ (≋-subst₁ p _ ⟫ core-lunit f)
    ; runit = λ f → ≈.trans (∘-cong ≈.refl (core-runit _ _)) (∘-idʳ f)
    ; assoc = λ {m₁} {m₂} {n₁} {n₂} f g h p q → ≋→≈
        ( ≋-subst₁ q _
        ⟫ ≋-subst₁-∘ p _ _
        ⟫ ≋-assoc _ _ _
        ⟫ ≋-∘ ≋-refl (core-assoc m₁ m₂ n₁ n₂ g h (sym p)) )
    }

  U-ren : RenCartesian U-pre
  U-ren = record
    { _[_] = λ f r → f ∘ R r
    ; ren-cong = λ e e' → ∘-cong e (R-cong e')
    ; ren-id = λ f → ≈.trans (∘-cong ≈.refl R-id) (∘-idʳ f)
    ; ren-∘ = λ f r s → R-∘' r s f
    ; ren-sub = λ u v r₁ s r₂ → ≈.trans (∘-assoc _ _ _) (≈.trans (∘-cong ≈.refl (core-N v r₁ s r₂)) (≈.sym (∘-assoc _ _ _)))
    }

  U-symm : Symmetric U-pre U-ren
  U-symm = record
    { σ-natˡ = λ {m₁} {m₂} {n} f g p q q' → ≋→≈
        ( ≋-assoc _ _ _
        ⟫ ≋-sym (≋-∘[] (sym p) ≋-refl (≋-sym (core-Sℓ m₁ m₂ g (sym q))))
        ⟫ ≋-sym ( ≋-∘ ≋-refl (≋-≈ (R-∘ _ _) ⟫ ≋-∘ (≋-≈ (R-∘ _ _)) ≋-refl)
                ⟫ ≋-∘ ≋-refl (≋-∘ ≋-refl (R-cast q') ⟫ ≋-idʳ _)
                ⟫ ≋-∘ (≋-assoc _ _ _ ⟫ ≋-R-cast p f _) ≋-refl
                ⟫ ≋-R-cast q _ _
                ⟫ ≋-assoc _ _ _
                ⟫ ≋-∘ ≋-refl (≋-assoc _ _ _) ) )
    ; σ-natʳ = λ {m₁} {m₂} {n} f g p q q' → ≋→≈
        ( ≋-assoc _ _ _
        ⟫ ≋-assoc _ _ _
        ⟫ ≋-∘ ≋-refl (≋-R-cast p _ _)
        ⟫ ≋-∘ ≋-refl (core-Sr m₁ m₂ g (sym p) (sym q))
        ⟫ ≋-sym ( ≋-∘ ≋-refl (≋-≈ (R-∘ _ _) ⟫ ≋-∘ (≋-≈ (R-∘ _ _)) ≋-refl)
                ⟫ ≋-∘ ≋-refl (≋-∘ ≋-refl (R-cast q') ⟫ ≋-idʳ _)
                ⟫ ≋-R-cast q _ _
                ⟫ ≋-assoc _ _ _ ) )
    }

  U-sym : SymPreoperad
  U-sym = record { C = U-pre ; ren = U-ren ; symm = U-symm }

  open Centrality U-pre using () renaming (Central to Centralᵘ; Comm to Commᵘ)

  -- centrality in D gives centrality in U(D)
  U-central : (a : Hom n 1) → Central a → Centralᵘ a
  U-central a ca g' = comm (inj₁ ca) , comm (inj₂ ca)
    where
      comm : ∀ {n₁ n₂} {a : Hom n₁ 1} {b : Hom n₂ 1} → Central a ⊎ Central b → Commᵘ a b
      comm {a = a} {b} c m₁ m m₂ f p p' p'' q = ≋→≈
        ( ≋-subst₁ q _
        ⟫ ≋-subst₁-∘ p _ _
        ⟫ ≋-assoc _ _ _
        ⟫ ≋-sym (≋-∘[] (sym p') ≋-refl (≋-sym (core-CEN m₁ m m₂ a b c (sym p) (sym p''))))
        ⟫ ≋-sym ( ≋-subst₁-∘ p'' _ _
                ⟫ ≋-∘[]₂ (sym p'') (sym p'') (≋-subst₁-∘ p' f _) ≋-refl
                ⟫ ≋-assoc _ _ _
                ⟫ ≋-∘ ≋-refl (≋-assoc _ _ _) ) )

  -- discardable and copyable operations
  U-discard : ∀ {m₁ m₂} (a : Hom n 1) → R (!ʳ 1) ∘ a ≈ R (!ʳ n) → (f : Hom (m₁ + m₂) 1)
    → (f ∘ R (idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂})) ∘ (m₁ ⊣ (a ⊢ m₂)) ≈ f ∘ R (idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂})
  U-discard {m₁ = m₁} {m₂} a d f = ≈.trans (∘-assoc _ _ _) (∘-cong ≈.refl (core-D m₁ m₂ a d))

  U-copy : ∀ {m₁ m₂} (a : Hom n 1) → R (Δʳ 1) ∘ a ≈ ((a ⊢ 1) ∘ (n ⊣ a)) ∘ R (Δʳ n)
    → (f : Hom (m₁ + suc (suc m₂)) 1)
      (p : m₁ + (n + suc m₂) ≡ (m₁ + n) + suc m₂) (q : (m₁ + n) + (n + m₂) ≡ m₁ + ((n + n) + m₂))
    → (f ∘ R (idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂})) ∘ (m₁ ⊣ (a ⊢ m₂))
      ≈ ((subst (λ n → Hom n 1) p (f ∘ (m₁ ⊣ (a ⊢ suc m₂)))) ∘ ((m₁ + n) ⊣ (a ⊢ m₂))) ∘ R ((idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}) ∘ʳ castʳ q)
  U-copy {m₁ = m₁} {m₂} a cp f p q = ≋→≈
    ( ≋-assoc _ _ _
    ⟫ ≋-∘ ≋-refl (core-C m₁ m₂ a cp (sym p) (sym q))
    ⟫ ≋-sym ( ≋-∘ (≋-subst₁-∘ p _ _) (≋-≈ (R-∘ _ _))
            ⟫ ≋-R-cast q _ _
            ⟫ ≋-∘[]₂ (sym q) (sym q) (≋-assoc _ _ _) ≋-refl
            ⟫ ≋-assoc _ _ _ ) )

------------------------------------------------------------------------
-- U on objects: a Freyd PROP gives a Freyd operad
------------------------------------------------------------------------

module U (D : FreydPROP) where
  open FreydPROP D

  -- the action of renamings on 𝕍 and on ℂ
  ρ-action : MFPS.PROPHet.RenAction 𝕍.P
  ρ-action = record
    { R = 𝕍.ρ ; R-cong = 𝕍.ρ-cong ; R-id = 𝕍.ρ-id ; R-∘ = 𝕍.ρ-∘ ; R-+ = 𝕍.ρ-+ ; R-σ = λ m n → 𝕍.ρ-σ
    ; R-central = λ r → 𝕍.prop (𝕍.ρ r) }

  Jρ-action : MFPS.PROPHet.RenAction ℂ
  Jρ-action = record
    { R = λ r → 𝒥 (𝕍.ρ r)
    ; R-cong = λ e → 𝒥-cong (𝕍.ρ-cong e)
    ; R-id = ℂ.≈.trans (𝒥-cong 𝕍.ρ-id) 𝒥-id
    ; R-∘ = λ r s → ℂ.≈.trans (𝒥-cong (𝕍.ρ-∘ r s)) (𝒥-∘ _ _)
    ; R-+ = λ r s → ℂ.≈.trans (𝒥-cong (𝕍.ρ-+ r s)) (ℂ.≈.trans (𝒥-∘ _ _) (ℂ.∘-cong (𝒥-⊢ _) (𝒥-⊣ _)))
    ; R-σ = λ m n → ℂ.≈.trans (𝒥-cong 𝕍.ρ-σ) 𝒥-σ
    ; R-central = λ r → J-central (𝕍.ρ r) }

  module UV = Restrict 𝕍.P ρ-action
  module UC = Restrict ℂ Jρ-action

  -- Lemma A.1, the value side: a cartesian operad
  𝕍ᵁ : CartesianOperad
  𝕍ᵁ = record
    { V = UV.U-pre ; ren = UV.U-ren ; symm = UV.U-symm
    ; operad = λ g → UV.U-central g (𝕍.prop g)
    ; !-nat = λ f g → UV.U-discard g (𝕍.!-nat g) f
    ; Δ-nat = λ f g p q → UV.U-copy g (𝕍.Δ-nat g) f p q }

  -- the computation side
  ℂᵁ : SymPreoperad
  ℂᵁ = UC.U-sym

  -- J restricted to codomain 1
  Jᵁ : PreoperadFunctor UV.U-pre UC.U-pre
  Jᵁ = record
    { F = 𝒥 ; F-cong = 𝒥-cong ; F-id = 𝒥-id
    ; F-sub = λ f g → ℂ.≈.trans (𝒥-∘ _ _) (ℂ.∘-cong ℂ.≈.refl (ℂ.≈.trans (𝒥-⊣ _) (ℂ.⊣-cong (𝒥-⊢ _)))) }

  Jᵁ-ren : CartesianFunctor UV.U-ren UC.U-ren Jᵁ
  Jᵁ-ren = record { F-ren = λ x r → 𝒥-∘ _ _ }

  -- discardability and copyability of J-images, from the naturality
  -- of ! and Δ in 𝕍 and functoriality of J
  J-discardable : (v : 𝕍.Hom n 1) → 𝒥 (𝕍.ρ (!ʳ 1)) ℂ.∘ 𝒥 v ℂ.≈ 𝒥 (𝕍.ρ (!ʳ n))
  J-discardable v = ℂ.≈.trans (ℂ.≈.sym (𝒥-∘ _ _)) (𝒥-cong (𝕍.!-nat v))

  J-copyable : (v : 𝕍.Hom n 1)
    → 𝒥 (𝕍.ρ (Δʳ 1)) ℂ.∘ 𝒥 v ℂ.≈ ((𝒥 v ℂ.⊢ 1) ℂ.∘ (n ℂ.⊣ 𝒥 v)) ℂ.∘ 𝒥 (𝕍.ρ (Δʳ n))
  J-copyable v =
    ℂ.≈.trans (ℂ.≈.sym (𝒥-∘ _ _))
    (ℂ.≈.trans (𝒥-cong (𝕍.Δ-nat v))
    (ℂ.≈.trans (𝒥-∘ _ _) (ℂ.∘-cong (ℂ.≈.trans (𝒥-∘ _ _) (ℂ.∘-cong (𝒥-⊢ _) (𝒥-⊣ _))) ℂ.≈.refl)))

  -- Lemma A.1: U(D) is a Freyd operad
  UD : FreydOperad
  UD = record
    { 𝕍 = 𝕍ᵁ ; ℂ = ℂᵁ ; J = Jᵁ ; J-ren = Jᵁ-ren
    ; J-central = λ v → UC.U-central (𝒥 v) (J-central v)
    ; J-discard = λ f v → UC.U-discard (𝒥 v) (J-discardable v) f
    ; J-copy = λ f v p q → UC.U-copy (𝒥 v) (J-copyable v) f p q }

------------------------------------------------------------------------
-- U on morphisms: restriction of a Freyd PROP functor to codomain 1
------------------------------------------------------------------------

module UFunctor {D₁ D₂ : FreydPROP} (G : FreydPROPFunctor D₁ D₂) where
  open FreydPROPFunctor G
  private
    module D₁ = FreydPROP D₁
    module D₂ = FreydPROP D₂
    module U₁ = U D₁
    module U₂ = U D₂

  Gᵛᵁ : PreoperadFunctor U₁.UV.U-pre U₂.UV.U-pre
  Gᵛᵁ = record
    { F = ℱᵛ ; F-cong = ℱᵛ-cong ; F-id = ℱᵛ-id
    ; F-sub = λ f g → D₂.𝕍.≈.trans (ℱᵛ-∘ _ _) (D₂.𝕍.∘-cong D₂.𝕍.≈.refl (D₂.𝕍.≈.trans (ℱᵛ-⊣ _) (D₂.𝕍.⊣-cong (ℱᵛ-⊢ _)))) }

  Gᶜᵁ : PreoperadFunctor U₁.UC.U-pre U₂.UC.U-pre
  Gᶜᵁ = record
    { F = ℱᶜ ; F-cong = ℱᶜ-cong ; F-id = ℱᶜ-id
    ; F-sub = λ f g → D₂.ℂ.≈.trans (ℱᶜ-∘ _ _) (D₂.ℂ.∘-cong D₂.ℂ.≈.refl (D₂.ℂ.≈.trans (ℱᶜ-⊣ _) (D₂.ℂ.⊣-cong (ℱᶜ-⊢ _)))) }

  UG : FreydOperadFunctor U₁.UD U₂.UD
  UG = record
    { Gᵛ = Gᵛᵁ
    ; Gᵛ-ren = record { F-ren = λ x r → D₂.𝕍.≈.trans (ℱᵛ-∘ _ _) (D₂.𝕍.∘-cong D₂.𝕍.≈.refl (ℱᵛ-ρ r)) }
    ; Gᶜ = Gᶜᵁ
    ; Gᶜ-ren = record { F-ren = λ x r → D₂.ℂ.≈.trans (ℱᶜ-∘ _ _) (D₂.ℂ.∘-cong D₂.ℂ.≈.refl (D₂.ℂ.≈.trans (F-J _) (D₂.𝒥-cong (ℱᵛ-ρ r)))) }
    ; G-J = F-J }
