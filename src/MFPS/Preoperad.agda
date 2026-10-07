------------------------------------------------------------------------
-- Section 3.1–3.2: preoperads, reindexing, symmetry, centrality,
-- (cartesian) operads, Freyd operads; Section 4.1: weak closure.
--
-- Conventions.  A preoperad is an ℕ-indexed family of setoids
-- (morphisms of arity n, up to the paper's ≡, written _≈_ here).
-- The paper's f{n₁ ⊣ g ⊢ n₂} is written  f ⟨ n₁ ⊣ g ⊢ n₂ ⟩.
-- Arities are kept in the canonical right-associated shape
-- n₁ + (m + n₂); where the paper silently identifies e.g.
-- (m₁+n₁)+(n+(n₂+m₂)) with m₁+((n₁+(n+n₂))+m₂) we transport with
-- `subst Op p` for an *arbitrary* proof p (all such proofs are equal,
-- `≡-irrelevant`).
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
module MFPS.Preoperad where

open import MFPS.Prelude

------------------------------------------------------------------------
-- Definition 3.1 (Preoperad)
------------------------------------------------------------------------

record Preoperad : Set₁ where
  infix 4 _≈_
  field
    Op      : ℕ → Set
    _≈_     : ∀ {n} → Rel (Op n) 0ℓ
    ≈-equiv : ∀ {n} → IsEquivalence (_≈_ {n})
    idₒ     : Op 1
    sub     : ∀ n₁ n₂ {m} → Op (n₁ + suc n₂) → Op m → Op (n₁ + (m + n₂))

  syntax sub n₁ n₂ f g = f ⟨ n₁ ⊣ g ⊢ n₂ ⟩

  module ≈ {n} = IsEquivalence (≈-equiv {n})

  setoid : ℕ → Setoid 0ℓ 0ℓ
  setoid n = record { Carrier = Op n ; _≈_ = _≈_ ; isEquivalence = ≈-equiv }

  -- equality across an arity equation
  infix 4 _≈[_]_
  _≈[_]_ : ∀ {m n} → Op m → m ≡ n → Op n → Set
  x ≈[ p ] y = subst Op p x ≈ y

  field
    sub-cong : ∀ {n₁ n₂ m} {f f' : Op (n₁ + suc n₂)} {g g' : Op m}
      → f ≈ f' → g ≈ g' → f ⟨ n₁ ⊣ g ⊢ n₂ ⟩ ≈ f' ⟨ n₁ ⊣ g' ⊢ n₂ ⟩
    -- (i) left unit:  id{f} ≡ f          (arity 0 + (m + 0) = m + 0)
    lunit : ∀ {m} (f : Op m) (p : m + 0 ≡ m) → idₒ ⟨ 0 ⊣ f ⊢ 0 ⟩ ≈[ p ] f
    -- (ii) right unit: f{n₁ ⊣ id ⊢ n₂} ≡ f
    runit : ∀ {n₁ n₂} (f : Op (n₁ + suc n₂)) → f ⟨ n₁ ⊣ idₒ ⊢ n₂ ⟩ ≈ f
    -- (iii) associativity
    assoc : ∀ {m₁ m₂ n₁ n₂ n} (f : Op (m₁ + suc m₂)) (g : Op (n₁ + suc n₂)) (h : Op n)
      (p : m₁ + ((n₁ + suc n₂) + m₂) ≡ (m₁ + n₁) + suc (n₂ + m₂))
      (q : (m₁ + n₁) + (n + (n₂ + m₂)) ≡ m₁ + ((n₁ + (n + n₂)) + m₂))
      → (subst Op p (f ⟨ m₁ ⊣ g ⊢ m₂ ⟩)) ⟨ m₁ + n₁ ⊣ h ⊢ n₂ + m₂ ⟩
          ≈[ q ] f ⟨ m₁ ⊣ g ⟨ n₁ ⊣ h ⊢ n₂ ⟩ ⊢ m₂ ⟩

  -- transports respect ≈
  subst-cong : ∀ {m n} (p : m ≡ n) {x y : Op m} → x ≈ y → subst Op p x ≈ subst Op p y
  subst-cong refl e = e

  ≈[]-irr : ∀ {m n} {p p' : m ≡ n} {x : Op m} {y : Op n} → x ≈[ p ] y → x ≈[ p' ] y
  ≈[]-irr {p = p} {p'} e rewrite ≡-irrelevant p p' = e

  ≈[refl] : ∀ {n} {p : n ≡ n} {x y : Op n} → x ≈[ p ] y → x ≈ y
  ≈[refl] {p = p} {x} e = ≈.trans (≈.reflexive (sym (subst-irr Op p x))) e

  ≈⇒≈[] : ∀ {n} {p : n ≡ n} {x y : Op n} → x ≈ y → x ≈[ p ] y
  ≈⇒≈[] {p = p} {x} e = ≈.trans (≈.reflexive (subst-irr Op p x)) e

  -- Iterated single substitution of k operations of arity n into the
  -- inputs off, …, off + k - 1 of f (the paper's f{g₁ + ⋯ + g_k} when
  -- the gᵢ are central; in general the left-to-right order is fixed).
  plug : ∀ {k n} (off : ℕ) → Op (off + k) → (Fin k → Op n) → Op (off + k * n)
  plug {zero}  off f gs = f
  plug {suc k} {n} off f gs =
    subst Op (+-assoc off n (k * n))
      (plug (off + n) (subst Op (sym (+-assoc off n k)) (f ⟨ off ⊣ gs zero ⊢ k ⟩)) (gs ∘ suc))

  plug-cong : ∀ {k n} (off : ℕ) {f f' : Op (off + k)} {gs gs' : Fin k → Op n}
    → f ≈ f' → (∀ i → gs i ≈ gs' i) → plug off f gs ≈ plug off f' gs'
  plug-cong {zero}  off e es = e
  plug-cong {suc k} {n} off e es =
    subst-cong (+-assoc off n (k * n))
      (plug-cong (off + n) (subst-cong (sym (+-assoc off n k)) (sub-cong e (es zero))) (es ∘ suc))

------------------------------------------------------------------------
-- Definition 3.2 (S-cartesian preoperad), for S = Ren.
--
-- NOTE (paper issue): in Def. 3.2(iii) the paper writes rᵢ ∈ S(mᵢ ⇒ nᵢ)
-- and s ∈ S(m ⇒ n); with v[r] : V(m) → V(n) for r ∈ S(m ⇒ n) this does
-- not type-check.  The directions used below (rᵢ : nᵢ → mᵢ, s : n → m)
-- are the ones that make both sides land in V(m₁ + m + m₂).
------------------------------------------------------------------------

record RenCartesian (C : Preoperad) : Set where
  open Preoperad C
  infixl 8 _[_]
  field
    _[_]     : ∀ {m n} → Op m → Ren m n → Op n
    ren-cong : ∀ {m n} {x y : Op m} {r s : Ren m n} → x ≈ y → r ≗ s → x [ r ] ≈ y [ s ]
    ren-id   : ∀ {n} (x : Op n) → x [ idʳ ] ≈ x
    ren-∘    : ∀ {m n k} (x : Op m) (r : Ren m n) (s : Ren n k) → x [ s ∘ʳ r ] ≈ x [ r ] [ s ]
    ren-sub  : ∀ {n₁ n₂ n m₁ m₂ m} (u : Op (n₁ + suc n₂)) (v : Op n)
      (r₁ : Ren n₁ m₁) (s : Ren n m) (r₂ : Ren n₂ m₂)
      → (u ⟨ n₁ ⊣ v ⊢ n₂ ⟩) [ r₁ +ʳ s +ʳ r₂ ] ≈ (u [ r₁ +ʳ idʳ {1} +ʳ r₂ ]) ⟨ m₁ ⊣ v [ s ] ⊢ m₂ ⟩

  -- A transport along an arity equation is the action of a cast renaming.
  subst-ren : ∀ {m n} (p : m ≡ n) (x : Op m) → subst Op p x ≈ x [ castʳ p ]
  subst-ren refl x = ≈.trans (≈.sym (ren-id x)) (ren-cong ≈.refl (λ _ → refl))

  ren-subst : ∀ {m n} (p : m ≡ n) (x : Op m) → x [ castʳ p ] ≈ subst Op p x
  ren-subst p x = ≈.sym (subst-ren p x)

------------------------------------------------------------------------
-- Definition 3.3 (Symmetric preoperad).
--
-- We assume a full Ren-action (the paper only asks for a Perm-action;
-- every preoperad of the paper is Ren-cartesian anyway).  The two
-- naturality laws for σ_{1,n} and σ_{n,1} are stated with explicit
-- cast renamings where the paper identifies arities on the nose.
------------------------------------------------------------------------

record Symmetric (C : Preoperad) (R : RenCartesian C) : Set where
  open Preoperad C
  open RenCartesian R
  field
    σ-natˡ : ∀ {m₁ m₂ n} (f : Op (m₁ + suc (suc m₂))) (g : Op n)
      (p  : m₁ + suc (suc m₂) ≡ (m₁ + 1) + suc m₂)
      (q  : (m₁ + 1) + (n + m₂) ≡ m₁ + ((1 + n) + m₂))
      (q' : m₁ + ((n + 1) + m₂) ≡ m₁ + (n + suc m₂))
      → (f [ idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂} ]) ⟨ m₁ ⊣ g ⊢ suc m₂ ⟩
        ≈ ((f [ castʳ p ]) ⟨ m₁ + 1 ⊣ g ⊢ m₂ ⟩) [ castʳ q' ∘ʳ (idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂}) ∘ʳ castʳ q ]
    σ-natʳ : ∀ {m₁ m₂ n} (f : Op (m₁ + suc (suc m₂))) (g : Op n)
      (p  : m₁ + suc (suc m₂) ≡ (m₁ + 1) + suc m₂)
      (q  : m₁ + (n + suc m₂) ≡ m₁ + ((n + 1) + m₂))
      (q' : m₁ + ((1 + n) + m₂) ≡ (m₁ + 1) + (n + m₂))
      → ((f [ idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂} ]) [ castʳ p ]) ⟨ m₁ + 1 ⊣ g ⊢ m₂ ⟩
        ≈ (f ⟨ m₁ ⊣ g ⊢ suc m₂ ⟩) [ castʳ q' ∘ʳ (idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}) ∘ʳ castʳ q ]

------------------------------------------------------------------------
-- Definitions 3.4, 3.5 (preoperad functors, cartesian ones).
------------------------------------------------------------------------

record PreoperadFunctor (C₁ C₂ : Preoperad) : Set where
  private
    module C₁ = Preoperad C₁
    module C₂ = Preoperad C₂
  field
    F      : ∀ {n} → C₁.Op n → C₂.Op n
    F-cong : ∀ {n} {x y : C₁.Op n} → x C₁.≈ y → F x C₂.≈ F y
    F-id   : F C₁.idₒ C₂.≈ C₂.idₒ
    F-sub  : ∀ {n₁ n₂ m} (f : C₁.Op (n₁ + suc n₂)) (g : C₁.Op m)
      → F (f C₁.⟨ n₁ ⊣ g ⊢ n₂ ⟩) C₂.≈ (F f) C₂.⟨ n₁ ⊣ F g ⊢ n₂ ⟩

  F-subst : ∀ {m n} (p : m ≡ n) (x : C₁.Op m) → F (subst C₁.Op p x) ≡ subst C₂.Op p (F x)
  F-subst refl x = refl

record CartesianFunctor {C₁ C₂ : Preoperad} (R₁ : RenCartesian C₁) (R₂ : RenCartesian C₂)
                        (G : PreoperadFunctor C₁ C₂) : Set where
  open PreoperadFunctor G
  private
    module C₁ = Preoperad C₁
    module C₂ = Preoperad C₂
    module R₁ = RenCartesian R₁
    module R₂ = RenCartesian R₂
  field
    F-ren : ∀ {m n} (x : C₁.Op m) (r : Ren m n) → F (x R₁.[ r ]) C₂.≈ (F x) R₂.[ r ]

------------------------------------------------------------------------
-- Definition 3.6 (commutation, centrality, operads).
--
-- `Comm g₁ g₂` is the first displayed equation of Def. 3.6; the second
-- one is literally `Comm g₂ g₁`, so "g₁ commutes with g₂" is the pair.
------------------------------------------------------------------------

module Centrality (C : Preoperad) where
  open Preoperad C

  Comm : ∀ {n₁ n₂} → Op n₁ → Op n₂ → Set
  Comm {n₁} {n₂} g₁ g₂ = ∀ m₁ m m₂ (f : Op (m₁ + suc (m + suc m₂)))
    (p   : m₁ + (n₁ + (m + suc m₂)) ≡ (m₁ + (n₁ + m)) + suc m₂)
    (p'  : m₁ + suc (m + suc m₂) ≡ (m₁ + suc m) + suc m₂)
    (p'' : (m₁ + suc m) + (n₂ + m₂) ≡ m₁ + suc (m + (n₂ + m₂)))
    (q   : (m₁ + (n₁ + m)) + (n₂ + m₂) ≡ m₁ + (n₁ + (m + (n₂ + m₂))))
    → (subst Op p (f ⟨ m₁ ⊣ g₁ ⊢ m + suc m₂ ⟩)) ⟨ m₁ + (n₁ + m) ⊣ g₂ ⊢ m₂ ⟩
      ≈[ q ] (subst Op p'' ((subst Op p' f) ⟨ m₁ + suc m ⊣ g₂ ⊢ m₂ ⟩)) ⟨ m₁ ⊣ g₁ ⊢ m + (n₂ + m₂) ⟩

  Commutes : ∀ {n₁ n₂} → Op n₁ → Op n₂ → Set
  Commutes g₁ g₂ = Comm g₁ g₂ × Comm g₂ g₁

  Central : ∀ {n} → Op n → Set
  Central g = ∀ {n'} (g' : Op n') → Commutes g g'

  IsOperad : Set
  IsOperad = ∀ {n} (g : Op n) → Central g

------------------------------------------------------------------------
-- Definition 3.7 (Cartesian operad).
------------------------------------------------------------------------

record CartesianOperad : Set₁ where
  field
    V     : Preoperad
    ren   : RenCartesian V
    symm  : Symmetric V ren
  open Preoperad V public
  open RenCartesian ren public
  open Symmetric symm public
  open Centrality V public
  field
    operad  : IsOperad
    -- (i) discarding is natural
    !-nat : ∀ {m₁ m₂ n} (f : Op (m₁ + m₂)) (g : Op n)
      → (f [ idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂} ]) ⟨ m₁ ⊣ g ⊢ m₂ ⟩ ≈ f [ idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂} ]
    -- (ii) copying is natural   (g + g is the iterated single substitution)
    Δ-nat : ∀ {m₁ m₂ n} (f : Op (m₁ + suc (suc m₂))) (g : Op n)
      (p : m₁ + (n + suc m₂) ≡ (m₁ + n) + suc m₂)
      (q : (m₁ + n) + (n + m₂) ≡ m₁ + ((n + n) + m₂))
      → (f [ idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂} ]) ⟨ m₁ ⊣ g ⊢ m₂ ⟩
        ≈ ((subst Op p (f ⟨ m₁ ⊣ g ⊢ suc m₂ ⟩)) ⟨ m₁ + n ⊣ g ⊢ m₂ ⟩) [ (idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}) ∘ʳ castʳ q ]

------------------------------------------------------------------------
-- The computation side: a symmetric Ren-cartesian preoperad, bundled.
------------------------------------------------------------------------

record SymPreoperad : Set₁ where
  field
    C    : Preoperad
    ren  : RenCartesian C
    symm : Symmetric C ren
  open Preoperad C public
  open RenCartesian ren public
  open Symmetric symm public
  open Centrality C public

------------------------------------------------------------------------
-- Definition 3.8 (Freyd operad).
--
-- NOTE (paper issue): Def. 3.8 asks that "the image of J is a cartesian
-- operad".  Being an operad is a property *internal* to the image
-- (image morphisms commute with each other), whereas the proofs of
-- Prop. 3.14(iii) and the analogy with Def. 2.10 need every J v to be
-- central *in C*.  Moreover, for J^Sub (Def. 3.13) to respect the
-- cartesian rules (D),(C) of Fig. 3, for C to be representable over
-- Sub_ℂ (Thm. 3.18(ii)), and for the (lunit) case of soundness
-- (Thm. 4.7) when the bound variable is weakened or contracted, the
-- discard/copy naturality of V must also hold *in C* for J-images:
--
--   (f[id + !₁ + id]){m₁ ⊣ Jv ⊢ m₂} ≡ f[id + !ₙ + id]
--   (f[id + Δ₁ + id]){m₁ ⊣ Jv ⊢ m₂} ≡ f{m₁ ⊣ Jv + Jv ⊢ m₂}[id + Δₙ + id]
--
-- for every f ∈ C.  These are the Führmann "discardable/copyable"
-- conditions; they hold in every Freyd PROP (by functoriality of J) and
-- in the term model (by (lunit)), but do not follow from the axioms as
-- stated.  We add them as `J-discard`, `J-copy`.
------------------------------------------------------------------------

record FreydOperad : Set₁ where
  field
    𝕍 : CartesianOperad
    ℂ : SymPreoperad
  module 𝕍 = CartesianOperad 𝕍
  module ℂ = SymPreoperad ℂ
  field
    J     : PreoperadFunctor 𝕍.V ℂ.C
    J-ren : CartesianFunctor 𝕍.ren ℂ.ren J
  open PreoperadFunctor J public renaming (F to 𝒥; F-cong to 𝒥-cong; F-id to 𝒥-id; F-sub to 𝒥-sub; F-subst to 𝒥-subst)
  open CartesianFunctor J-ren public renaming (F-ren to 𝒥-ren)
  field
    J-central : ∀ {n} (v : 𝕍.Op n) → ℂ.Central (𝒥 v)
    J-discard : ∀ {m₁ m₂ n} (f : ℂ.Op (m₁ + m₂)) (v : 𝕍.Op n)
      → (f ℂ.[ idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂} ]) ℂ.⟨ m₁ ⊣ 𝒥 v ⊢ m₂ ⟩ ℂ.≈ f ℂ.[ idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂} ]
    J-copy    : ∀ {m₁ m₂ n} (f : ℂ.Op (m₁ + suc (suc m₂))) (v : 𝕍.Op n)
      (p : m₁ + (n + suc m₂) ≡ (m₁ + n) + suc m₂)
      (q : (m₁ + n) + (n + m₂) ≡ m₁ + ((n + n) + m₂))
      → (f ℂ.[ idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂} ]) ℂ.⟨ m₁ ⊣ 𝒥 v ⊢ m₂ ⟩
        ℂ.≈ ((subst ℂ.Op p (f ℂ.⟨ m₁ ⊣ 𝒥 v ⊢ suc m₂ ⟩)) ℂ.⟨ m₁ + n ⊣ 𝒥 v ⊢ m₂ ⟩) ℂ.[ (idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}) ∘ʳ castʳ q ]

------------------------------------------------------------------------
-- Definition 3.9 (Freyd operad functor).
------------------------------------------------------------------------

record FreydOperadFunctor (M₁ M₂ : FreydOperad) : Set where
  private
    module M₁ = FreydOperad M₁
    module M₂ = FreydOperad M₂
  field
    Gᵛ     : PreoperadFunctor M₁.𝕍.V M₂.𝕍.V
    Gᵛ-ren : CartesianFunctor M₁.𝕍.ren M₂.𝕍.ren Gᵛ
    Gᶜ     : PreoperadFunctor M₁.ℂ.C M₂.ℂ.C
    Gᶜ-ren : CartesianFunctor M₁.ℂ.ren M₂.ℂ.ren Gᶜ
  open PreoperadFunctor Gᵛ public renaming (F to 𝒢ᵛ; F-cong to 𝒢ᵛ-cong; F-id to 𝒢ᵛ-id; F-sub to 𝒢ᵛ-sub; F-subst to 𝒢ᵛ-subst)
  open PreoperadFunctor Gᶜ public renaming (F to 𝒢ᶜ; F-cong to 𝒢ᶜ-cong; F-id to 𝒢ᶜ-id; F-sub to 𝒢ᶜ-sub; F-subst to 𝒢ᶜ-subst)
  open CartesianFunctor Gᵛ-ren public renaming (F-ren to 𝒢ᵛ-ren)
  open CartesianFunctor Gᶜ-ren public renaming (F-ren to 𝒢ᶜ-ren)
  field
    G-J : ∀ {n} (v : M₁.𝕍.Op n) → 𝒢ᶜ (M₁.𝒥 v) M₂.ℂ.≈ M₂.𝒥 (𝒢ᵛ v)

------------------------------------------------------------------------
-- Definition 4.1 (Weakly closed Freyd operad) and 4.2 (closed functor).
--
-- ◁ⁿ f ▷ abstracts the *last* input of f ∈ C(n + 1).
--
-- NOTE (paper issue): Def. 4.1 calls ◁ⁿ−▷ a "transformation" without
-- any naturality in n.  The interpretation of λx.M under a renaming
-- (exchange/weakening/contraction of Γ) is ◁⟦M⟧[r + id₁]▷ if the
-- structural rule is applied to M and ◁⟦M⟧▷[r] if it is applied to
-- λx.M; for ⟦−⟧ to be well defined on terms (and for the "renamings
-- are preserved" step of Thm. 4.9) these must agree.  This does not
-- follow from the two displayed axioms, so we add it as `abs-ren`.
------------------------------------------------------------------------

record WeaklyClosed (M : FreydOperad) : Set where
  open FreydOperad M
  field
    abs      : ∀ {n} → ℂ.Op (n + 1) → 𝕍.Op n
    abs-cong : ∀ {n} {f g : ℂ.Op (n + 1)} → f ℂ.≈ g → abs f 𝕍.≈ abs g
    app      : ℂ.Op 2
    -- β:  ⊛{J◁ⁿf▷ ⊢ 1} = f
    beta     : ∀ {n} (f : ℂ.Op (n + 1)) → app ℂ.⟨ 0 ⊣ 𝒥 (abs f) ⊢ 1 ⟩ ℂ.≈ f
    -- abstraction is natural in the context (see the note above)
    abs-ren  : ∀ {m n} (f : ℂ.Op (m + 1)) (r : Ren m n) → abs (f ℂ.[ r +ʳ idʳ {1} ]) 𝕍.≈ (abs f) 𝕍.[ r ]
    -- abstraction commutes with value substitution
    abs-sub  : ∀ {m₁ m₂ n} (f : ℂ.Op (m₁ + suc (m₂ + 1))) (v : 𝕍.Op n)
      (p  : m₁ + (n + (m₂ + 1)) ≡ (m₁ + (n + m₂)) + 1)
      (p' : m₁ + suc (m₂ + 1) ≡ (m₁ + suc m₂) + 1)
      → abs (subst ℂ.Op p (f ℂ.⟨ m₁ ⊣ 𝒥 v ⊢ m₂ + 1 ⟩)) 𝕍.≈ (abs (subst ℂ.Op p' f)) 𝕍.⟨ m₁ ⊣ v ⊢ m₂ ⟩

  -- the η law of Section 4 (not assumed): ◁ⁿ ⊛{Jv ⊢ 1} ▷ = v
  Eta : Set
  Eta = ∀ {n} (v : 𝕍.Op n) → abs (app ℂ.⟨ 0 ⊣ 𝒥 v ⊢ 1 ⟩) 𝕍.≈ v

record ClosedFunctor {M₁ M₂ : FreydOperad} (W₁ : WeaklyClosed M₁) (W₂ : WeaklyClosed M₂)
                     (G : FreydOperadFunctor M₁ M₂) : Set where
  open FreydOperadFunctor G
  private
    module W₁ = WeaklyClosed W₁
    module W₂ = WeaklyClosed W₂
    module M₂ = FreydOperad M₂
  field
    G-app : 𝒢ᶜ W₁.app M₂.ℂ.≈ W₂.app
    G-abs : ∀ {n} (f : FreydOperad.ℂ.Op M₁ (n + 1)) → 𝒢ᵛ (W₁.abs f) M₂.𝕍.≈ W₂.abs (𝒢ᶜ f)
