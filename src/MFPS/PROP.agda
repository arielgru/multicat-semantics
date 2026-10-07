------------------------------------------------------------------------
-- Section 2.3: pre-PROPs, centrality, PROPs, cartesian PROPs, Freyd
-- PROPs and their structure-preserving functors (Defs. 2.6–2.11).
--
-- A pre-PROP is a strict symmetric premonoidal category with objects ℕ
-- and tensor +.  Only whiskering (k ⊣ f, f ⊢ k) is functorial.  The
-- paper does not list the axioms of "strict symmetric premonoidal";
-- we state the standard ones (Power–Robinson), with `subst` transports
-- where strictness identifies arities such as (k+j)+m and k+(j+m).
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
module MFPS.PROP where

open import MFPS.Prelude hiding (_∘_; id)

private
  variable
    j k m n m' n' : ℕ

subst₂ : ∀ {ℓ} (P : ℕ → ℕ → Set ℓ) {m m' n n'} → m ≡ m' → n ≡ n' → P m n → P m' n'
subst₂ P refl refl x = x

record PrePROP : Set₁ where
  infix  4 _≈_
  infixr 9 _∘_
  infixr 6 _⊣_
  infixl 6 _⊢_
  field
    Hom     : ℕ → ℕ → Set
    _≈_     : Rel (Hom m n) 0ℓ
    ≈-equiv : IsEquivalence (_≈_ {m} {n})
    idₕ     : Hom n n
    _∘_     : Hom n k → Hom m n → Hom m k
    _⊣_     : ∀ k → Hom m n → Hom (k + m) (k + n)
    _⊢_     : Hom m n → ∀ k → Hom (m + k) (n + k)
    σ       : ∀ m n → Hom (m + n) (n + m)

  module ≈ {m n} = IsEquivalence (≈-equiv {m} {n})

  setoid : ℕ → ℕ → Setoid 0ℓ 0ℓ
  setoid m n = record { Carrier = Hom m n ; _≈_ = _≈_ ; isEquivalence = ≈-equiv }

  -- equality across arity equations
  infix 4 _≈[_,_]_
  _≈[_,_]_ : Hom m n → m ≡ m' → n ≡ n' → Hom m' n' → Set
  x ≈[ p , q ] y = subst₂ Hom p q x ≈ y

  -- the identity, transported along an arity equation
  castₕ : m ≡ n → Hom m n
  castₕ {m} p = subst (Hom m) p idₕ

  -- Definition 2.7 (centrality)
  Central : Hom m n → Set
  Central {m} {n} f = ∀ {m' n'} (g : Hom m' n')
    → ((f ⊢ n') ∘ (m ⊣ g) ≈ (n ⊣ g) ∘ (f ⊢ m'))
    × ((g ⊢ n) ∘ (m' ⊣ f) ≈ (n' ⊣ f) ∘ (g ⊢ m))

  -- Axioms of a strict symmetric premonoidal category (Power–Robinson),
  -- ℕ-indexed.  The symmetry is given by its naturality against σ_{1,n}
  -- and σ_{n,1} (the paper's generating symmetries, cf. Def. 3.3 and
  -- Lemma 2.2) together with the coherence equations that determine
  -- σ_{m,n} from these; general naturality follows.
  field
    ∘-cong  : {f f' : Hom m n} {g g' : Hom n k} → g ≈ g' → f ≈ f' → g ∘ f ≈ g' ∘ f'
    ∘-assoc : (f : Hom m n) (g : Hom n k) (h : Hom k j) → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    ∘-idˡ   : (f : Hom m n) → idₕ ∘ f ≈ f
    ∘-idʳ   : (f : Hom m n) → f ∘ idₕ ≈ f
    ⊣-cong  : {f f' : Hom m n} → f ≈ f' → k ⊣ f ≈ k ⊣ f'
    ⊢-cong  : {f f' : Hom m n} → f ≈ f' → f ⊢ k ≈ f' ⊢ k
    ⊣-id    : k ⊣ idₕ {n} ≈ idₕ
    ⊢-id    : idₕ {n} ⊢ k ≈ idₕ
    ⊣-∘     : (f : Hom m n) (g : Hom n j) → k ⊣ (g ∘ f) ≈ (k ⊣ g) ∘ (k ⊣ f)
    ⊢-∘     : (f : Hom m n) (g : Hom n j) → (g ∘ f) ⊢ k ≈ (g ⊢ k) ∘ (f ⊢ k)
    0-⊣     : (f : Hom m n) → 0 ⊣ f ≈ f
    ⊢-0     : (f : Hom m n) (p : m + 0 ≡ m) (q : n + 0 ≡ n) → f ⊢ 0 ≈[ p , q ] f
    ⊣-⊣     : (f : Hom m n) (p : k + (j + m) ≡ (k + j) + m) (q : k + (j + n) ≡ (k + j) + n)
              → k ⊣ (j ⊣ f) ≈[ p , q ] (k + j) ⊣ f
    ⊢-⊢     : (f : Hom m n) (p : (m + j) + k ≡ m + (j + k)) (q : (n + j) + k ≡ n + (j + k))
              → (f ⊢ j) ⊢ k ≈[ p , q ] f ⊢ (j + k)
    ⊣-⊢     : (f : Hom m n) (p : (k + m) + j ≡ k + (m + j)) (q : (k + n) + j ≡ k + (n + j))
              → (k ⊣ f) ⊢ j ≈[ p , q ] k ⊣ (f ⊢ j)
    σ-σ     : σ n m ∘ σ m n ≈ idₕ
    σ-nat₁ˡ : (g : Hom m' n') → σ 1 n' ∘ (1 ⊣ g) ≈ (g ⊢ 1) ∘ σ 1 m'
    σ-nat₁ʳ : (g : Hom m' n') → σ n' 1 ∘ (g ⊢ 1) ≈ (1 ⊣ g) ∘ σ m' 1
    σ-central : Central (σ m n)
    σ-0ˡ    : (p : m + 0 ≡ m) → σ m 0 ≈[ p , refl ] idₕ
    σ-0ʳ    : (p : m + 0 ≡ m) → σ 0 m ≈[ refl , p ] idₕ
    σ-hexˡ  : ∀ m n k (p : m + (n + k) ≡ (m + n) + k) (q : (n + m) + k ≡ n + (m + k)) (q' : n + (k + m) ≡ (n + k) + m)
              → σ m (n + k) ≈[ p , refl ] castₕ q' ∘ (n ⊣ σ m k) ∘ castₕ q ∘ (σ m n ⊢ k)
    σ-hexʳ  : ∀ m n k (p : (m + n) + k ≡ m + (n + k)) (q : m + (k + n) ≡ (m + k) + n) (q' : (k + m) + n ≡ k + (m + n))
              → σ (m + n) k ≈[ p , refl ] castₕ q' ∘ (σ m k ⊢ n) ∘ castₕ q ∘ (m ⊣ σ n k)

  -- Definition 2.8
  IsPROP : Set
  IsPROP = ∀ {m n} (f : Hom m n) → Central f

------------------------------------------------------------------------
-- Definition 2.9 (Cartesian PROP)
--
-- Representation.  The paper equips a PROP with natural commutative
-- comonoids (Δ, !) satisfying coherence with +.  By Lemma 2.2 (and
-- Fox's theorem) this is the same as an identity-on-objects strict
-- symmetric monoidal functor ρ : Renᵒᵖ → V whose values on Δₙ, !ₙ are
-- natural.  We take ρ as the primitive datum: Δₙ := ρ Δₙ, !ₙ := ρ !ₙ,
-- and the comonoid and coherence equations of Def. 2.9 are then
-- inherited from Ren (they are equations between renamings).  The
-- substitution PROP Sub× has ρ r = [r] on the nose, and for a Freyd
-- PROP D the operad U(D) uses ρ to reindex.
------------------------------------------------------------------------

record CartesianPROP : Set₁ where
  field
    P : PrePROP
  open PrePROP P public
  field
    prop   : IsPROP
    -- the action of renamings:  r : Ren m n (a map [m] → [n]) gives an
    -- m-tuple of the n variables, i.e. a morphism n → m
    ρ      : Ren m n → Hom n m
    ρ-cong : {r s : Ren m n} → r ≗ s → ρ r ≈ ρ s
    ρ-id   : ρ (idʳ {n}) ≈ idₕ
    ρ-∘    : (r : Ren m n) (s : Ren n k) → ρ (s ∘ʳ r) ≈ ρ r ∘ ρ s
    ρ-+    : ∀ {m₁ n₁ m₂ n₂} (r : Ren m₁ n₁) (s : Ren m₂ n₂) → ρ (r +ʳ s) ≈ (ρ r ⊢ m₂) ∘ (n₁ ⊣ ρ s)
    ρ-σ    : ρ (σʳ m n) ≈ σ n m

  Δ : ∀ n → Hom n (n + n)
  Δ n = ρ (Δʳ n)

  ! : ∀ n → Hom n 0
  ! n = ρ (!ʳ n)

  field
    -- naturality of copy and discard
    Δ-nat : (f : Hom m n) → Δ n ∘ f ≈ ((f ⊢ n) ∘ (m ⊣ f)) ∘ Δ m
    !-nat : (f : Hom m n) → ! n ∘ f ≈ ! m

------------------------------------------------------------------------
-- Definition 2.11: structure preserving functors
------------------------------------------------------------------------

record PrePROPFunctor (D₁ D₂ : PrePROP) : Set where
  private
    module D₁ = PrePROP D₁
    module D₂ = PrePROP D₂
  field
    F      : D₁.Hom m n → D₂.Hom m n
    F-cong : {f g : D₁.Hom m n} → f D₁.≈ g → F f D₂.≈ F g
    F-id   : F (D₁.idₕ {n}) D₂.≈ D₂.idₕ
    F-∘    : (f : D₁.Hom m n) (g : D₁.Hom n k) → F (g D₁.∘ f) D₂.≈ F g D₂.∘ F f
    F-⊣    : (f : D₁.Hom m n) → F (k D₁.⊣ f) D₂.≈ k D₂.⊣ F f
    F-⊢    : (f : D₁.Hom m n) → F (f D₁.⊢ k) D₂.≈ F f D₂.⊢ k
    F-σ    : F (D₁.σ m n) D₂.≈ D₂.σ m n

record CartesianPROPFunctor (V₁ V₂ : CartesianPROP) : Set where
  private
    module V₁ = CartesianPROP V₁
    module V₂ = CartesianPROP V₂
  field
    functor : PrePROPFunctor V₁.P V₂.P
  open PrePROPFunctor functor public
  field
    F-ρ : (r : Ren m n) → F (V₁.ρ r) V₂.≈ V₂.ρ r

  -- hence copy and discard are preserved
  F-Δ : F (V₁.Δ n) V₂.≈ V₂.Δ n
  F-Δ = F-ρ _
  F-! : F (V₁.! n) V₂.≈ V₂.! n
  F-! = F-ρ _

------------------------------------------------------------------------
-- Definition 2.10 (Freyd PROP)
------------------------------------------------------------------------

record FreydPROP : Set₁ where
  field
    𝕍 : CartesianPROP
    ℂ : PrePROP
  module 𝕍 = CartesianPROP 𝕍
  module ℂ = PrePROP ℂ
  field
    J : PrePROPFunctor 𝕍.P ℂ
  open PrePROPFunctor J public renaming (F to 𝒥; F-cong to 𝒥-cong; F-id to 𝒥-id; F-∘ to 𝒥-∘; F-⊣ to 𝒥-⊣; F-⊢ to 𝒥-⊢; F-σ to 𝒥-σ)
  field
    J-central : (v : 𝕍.Hom m n) → ℂ.Central (𝒥 v)

record FreydPROPFunctor (D₁ D₂ : FreydPROP) : Set where
  private
    module D₁ = FreydPROP D₁
    module D₂ = FreydPROP D₂
  field
    Fᵛ : CartesianPROPFunctor D₁.𝕍 D₂.𝕍
    Fᶜ : PrePROPFunctor D₁.ℂ D₂.ℂ
  open CartesianPROPFunctor Fᵛ public renaming (F to ℱᵛ; F-cong to ℱᵛ-cong; F-id to ℱᵛ-id; F-∘ to ℱᵛ-∘; F-⊣ to ℱᵛ-⊣; F-⊢ to ℱᵛ-⊢; F-σ to ℱᵛ-σ; F-ρ to ℱᵛ-ρ; F-Δ to ℱᵛ-Δ; F-! to ℱᵛ-!; functor to Fᵛ-functor)
  open PrePROPFunctor Fᶜ public renaming (F to ℱᶜ; F-cong to ℱᶜ-cong; F-id to ℱᶜ-id; F-∘ to ℱᶜ-∘; F-⊣ to ℱᶜ-⊣; F-⊢ to ℱᶜ-⊢; F-σ to ℱᶜ-σ)
  field
    F-J : (v : D₁.𝕍.Hom m n) → ℱᶜ (D₁.𝒥 v) D₂.ℂ.≈ D₂.𝒥 (ℱᵛ v)
