------------------------------------------------------------------------
-- Computations in a pre-PROP up to arity casts.
--
-- The paper identifies arities such as k+(j+m) and (k+j)+m on the nose.
-- Here a morphism f : m → n and a morphism g : m' → n' are "equal up to
-- casts", f ≋ g, when m ≡ m', n ≡ n' and the transport of f along these
-- equations is ≈ g.  Since equations between natural numbers are
-- unique, ≋ is an equivalence relation, congruent for ∘, ⊣, ⊢, and it
-- restricts to ≈ on morphisms of the same type; the strictness axioms
-- of a pre-PROP (Def. 2.6) become cast-free equations
--   k ⊣ (j ⊣ f) ≋ (k+j) ⊣ f,   (f ⊢ j) ⊢ k ≋ f ⊢ (j+k),   …
-- and the cast morphisms castₕ p are ≋ identities.
--
-- On top of this the module proves, for a pre-PROP D, the identities
-- between whiskered composites that underlie
--   * the preoperad laws of U(D) (Def. 3.19, Lemma A.1) — the operations
--     of U(D) are the morphisms into 1 and f{n₁ ⊣ g ⊢ n₂} = f ∘ (n₁ ⊣ (g ⊢ n₂));
--   * the soundness of the rules of Fig. 3 in D (Lemma A.7).
-- Each rule of Fig. 3 corresponds to one identity `core-…` below:
--   (A) `core-assoc`, (U₁) `core-runit`, lunit `core-lunit`,
--   (CEN) `core-CEN`; and, given an action R of renamings
--   (module `WithR`): (N) `core-N`, (Sℓ) `core-Sℓ`, (Sr) `core-Sr`,
--   (D) `core-D`, (C) `core-C`.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude hiding (_∘_; id)
open import MFPS.PROP
open import Function.Base using (case_of_)

module MFPS.PROPHet (D : PrePROP) where

open PrePROP D

private
  variable
    j k m n m' n' k' a b c : ℕ

------------------------------------------------------------------------
-- transports
------------------------------------------------------------------------

subst₂-irr : (p : m ≡ m) (q : n ≡ n) (f : Hom m n) → subst₂ Hom p q f ≡ f
subst₂-irr p q f rewrite ≡-irrelevant p refl | ≡-irrelevant q refl = refl

subst₂-trans : (p : m ≡ m') (p' : m' ≡ k) (q : n ≡ n') (q' : n' ≡ k') (f : Hom m n)
  → subst₂ Hom p' q' (subst₂ Hom p q f) ≡ subst₂ Hom (trans p p') (trans q q') f
subst₂-trans refl refl refl refl f = refl

-- a transport of the first index only, as used by U(D)
subst₁-subst₂ : (P : ℕ → ℕ) (p : m ≡ n) (f : Hom m 1) → subst (λ n → Hom n 1) p f ≡ subst₂ Hom p refl f
subst₁-subst₂ P refl f = refl

castₕ-subst₂ : (p : m ≡ n) → castₕ p ≡ subst₂ Hom refl p idₕ
castₕ-subst₂ refl = refl

------------------------------------------------------------------------
-- equality up to arity casts
------------------------------------------------------------------------

infix 4 _≋_
record _≋_ (f : Hom m n) (g : Hom m' n') : Set where
  constructor ≋[_,_,_]
  field
    src : m ≡ m'
    tgt : n ≡ n'
    eq  : subst₂ Hom src tgt f ≈ g

open _≋_ public

≋-refl : {f : Hom m n} → f ≋ f
≋-refl = ≋[ refl , refl , ≈.refl ]

≋-≈ : {f g : Hom m n} → f ≈ g → f ≋ g
≋-≈ e = ≋[ refl , refl , e ]

≋-≡ : {f g : Hom m n} → f ≡ g → f ≋ g
≋-≡ refl = ≋-refl

≋→≈ : {f g : Hom m n} → f ≋ g → f ≈ g
≋→≈ ≋[ p , q , e ] = ≈.trans (≈.reflexive (sym (subst₂-irr p q _))) e

≋-sym : {f : Hom m n} {g : Hom m' n'} → f ≋ g → g ≋ f
≋-sym ≋[ refl , refl , e ] = ≋[ refl , refl , ≈.sym e ]

≋-trans : {f : Hom m n} {g : Hom m' n'} {h : Hom k k'} → f ≋ g → g ≋ h → f ≋ h
≋-trans ≋[ refl , refl , e ] ≋[ p , q , e' ] = ≋[ p , q , ≈.trans (subst₂-cong p q e) e' ]
  where
    subst₂-cong : ∀ {m m' n n'} (p : m ≡ m') (q : n ≡ n') {f g : Hom m n} → f ≈ g → subst₂ Hom p q f ≈ subst₂ Hom p q g
    subst₂-cong refl refl e = e

infixr 2 _⟫_
_⟫_ : {f : Hom m n} {g : Hom m' n'} {h : Hom k k'} → f ≋ g → g ≋ h → f ≋ h
_⟫_ = ≋-trans

≋-∘ : {g : Hom n k} {g' : Hom n' k'} {f : Hom m n} {f' : Hom m' n'}
  → g ≋ g' → f ≋ f' → (g ∘ f) ≋ (g' ∘ f')
≋-∘ ≋[ refl , refl , e ] ≋[ refl , q , e' ] =
  ≋[ refl , refl , ∘-cong e (≈.trans (≈.reflexive (sym (subst₂-irr refl q _))) e') ]

≋-⊣ : {f : Hom m n} {f' : Hom m' n'} → f ≋ f' → (k ⊣ f) ≋ (k ⊣ f')
≋-⊣ ≋[ refl , refl , e ] = ≋[ refl , refl , ⊣-cong e ]

≋-⊢ : {f : Hom m n} {f' : Hom m' n'} → f ≋ f' → (f ⊢ k) ≋ (f' ⊢ k)
≋-⊢ ≋[ refl , refl , e ] = ≋[ refl , refl , ⊢-cong e ]

-- transports and casts disappear
≋-subst₂ : (p : m ≡ m') (q : n ≡ n') (f : Hom m n) → subst₂ Hom p q f ≋ f
≋-subst₂ refl refl f = ≋-refl

≋-subst₁ : (p : m ≡ m') (f : Hom m 1) → subst (λ n → Hom n 1) p f ≋ f
≋-subst₁ refl f = ≋-refl

≋-castₕ : (p : m ≡ n) → castₕ p ≋ idₕ {m}
≋-castₕ refl = ≋-refl

≋-castₕ' : (p : m ≡ n) → castₕ p ≋ idₕ {n}
≋-castₕ' refl = ≋-refl

≋-idₕ : (p : m ≡ n) → idₕ {m} ≋ idₕ {n}
≋-idₕ refl = ≋-refl

-- the strictness axioms, cast-free
≋-0⊣ : (f : Hom m n) → (0 ⊣ f) ≋ f
≋-0⊣ f = ≋-≈ (0-⊣ f)

≋-⊢0 : (f : Hom m n) → (f ⊢ 0) ≋ f
≋-⊢0 {m} {n} f = ≋[ +-identityʳ m , +-identityʳ n , ⊢-0 f _ _ ]

≋-⊣⊣ : ∀ k j (f : Hom m n) → (k ⊣ (j ⊣ f)) ≋ ((k + j) ⊣ f)
≋-⊣⊣ {m} {n} k j f = ≋[ sym (+-assoc k j m) , sym (+-assoc k j n) , ⊣-⊣ f _ _ ]

≋-⊢⊢ : ∀ j k (f : Hom m n) → ((f ⊢ j) ⊢ k) ≋ (f ⊢ (j + k))
≋-⊢⊢ {m} {n} j k f = ≋[ +-assoc m j k , +-assoc n j k , ⊢-⊢ f _ _ ]

≋-⊣⊢ : ∀ k j (f : Hom m n) → ((k ⊣ f) ⊢ j) ≋ (k ⊣ (f ⊢ j))
≋-⊣⊢ {m} {n} k j f = ≋[ +-assoc k m j , +-assoc k n j , ⊣-⊢ f _ _ ]

-- unit and associativity, for chaining
≋-idˡ : (f : Hom m n) → (idₕ ∘ f) ≋ f
≋-idˡ f = ≋-≈ (∘-idˡ f)

≋-idʳ : (f : Hom m n) → (f ∘ idₕ) ≋ f
≋-idʳ f = ≋-≈ (∘-idʳ f)

≋-assoc : (f : Hom m n) (g : Hom n k) (h : Hom k j) → ((h ∘ g) ∘ f) ≋ (h ∘ (g ∘ f))
≋-assoc f g h = ≋-≈ (∘-assoc f g h)

-- a morphism conjugated by casts
≋-conj : (p : m ≡ m') (q : n ≡ n') (f : Hom m n) → (castₕ q ∘ f ∘ castₕ (sym p)) ≋ f
≋-conj p q f = ≋-∘ (≋-castₕ q) (≋-∘ ≋-refl (≋-castₕ' (sym p))) ⟫ ≋-idˡ _ ⟫ ≋-idʳ f

castₕ-refl : (p : m ≡ m) → castₕ p ≈ idₕ
castₕ-refl p rewrite ≡-irrelevant p refl = ≈.refl

castₕ-castₕ : (p : a ≡ b) (q : b ≡ c) → castₕ q ∘ castₕ p ≈ castₕ (trans p q)
castₕ-castₕ refl refl = ∘-idˡ _

-- composition across an arity equation (the paper's on-the-nose
-- composite g ∘ f where cod f and dom g are only provably equal)
infixr 9 _∘[_]_
_∘[_]_ : Hom n k → m' ≡ n → Hom m m' → Hom m k
g ∘[ p ] f = g ∘ (castₕ p ∘ f)

≋-∘[] : {g : Hom n k} {g' : Hom n' k'} {f : Hom m m'} {f' : Hom a n'} (p : m' ≡ n)
  → g ≋ g' → f ≋ f' → (g ∘[ p ] f) ≋ (g' ∘ f')
≋-∘[] p ≋[ refl , refl , eg ] ≋[ refl , refl , ef ] =
  ≋-≈ (∘-cong eg (≈.trans (∘-cong (castₕ-refl p) ≈.refl) (≈.trans (∘-idˡ _) ef)))

≋-∘[]₂ : {g : Hom n k} {g' : Hom n' k'} {f : Hom m m'} {f' : Hom a b} (p : m' ≡ n) (p' : b ≡ n')
  → g ≋ g' → f ≋ f' → (g ∘[ p ] f) ≋ (g' ∘[ p' ] f')
≋-∘[]₂ refl p' ≋[ refl , refl , eg ] ≋[ refl , refl , ef ] =
  ≋-≈ (∘-cong eg (∘-cong (≈.sym (castₕ-refl p')) ef))

≋-cast-∘ : (p : m' ≡ n) (f : Hom m m') → (castₕ p ∘ f) ≋ f
≋-cast-∘ refl f = ≋-idˡ f

≋-∘-cast : (p : m ≡ n) (f : Hom n k) → (f ∘ castₕ p) ≋ f
≋-∘-cast refl f = ≋-idʳ f

-- a transported morphism composed on either side
≋-subst₁-∘ : (p : m' ≡ n) (g : Hom m' 1) (f : Hom m n) → (subst (λ n → Hom n 1) p g ∘ f) ≋ (g ∘[ sym p ] f)
≋-subst₁-∘ refl g f = ≋-≈ (∘-cong ≈.refl (≈.sym (∘-idˡ f)))

≋-subst₂-∘ : (p : m' ≡ n) (g : Hom m' k) (f : Hom m n) → (subst₂ Hom p refl g ∘ f) ≋ (g ∘[ sym p ] f)
≋-subst₂-∘ refl g f = ≋-≈ (∘-cong ≈.refl (≈.sym (∘-idˡ f)))

------------------------------------------------------------------------
-- centrality is stable under ≈ and under whiskering
------------------------------------------------------------------------

central-≈ : {f g : Hom m n} → f ≈ g → Central g → Central f
central-≈ e c h =
  ≈.trans (∘-cong (⊢-cong e) ≈.refl) (≈.trans (proj₁ (c h)) (∘-cong ≈.refl (⊢-cong (≈.sym e)))) ,
  ≈.trans (∘-cong ≈.refl (⊣-cong e)) (≈.trans (proj₂ (c h)) (∘-cong (⊣-cong (≈.sym e)) ≈.refl))

central-⊢ : {f : Hom m n} → Central f → ∀ k → Central (f ⊢ k)
central-⊢ {m} {n} {f} c k {m'} {n'} g =
  ( ≋→≈ ( ≋-∘ (≋-⊢⊢ k n' f) (≋-sym (≋-⊣⊣ m k g))
        ⟫ ≋-≈ (proj₁ (c (k ⊣ g)))
        ⟫ ≋-∘ (≋-⊣⊣ n k g) (≋-sym (≋-⊢⊢ k m' f)) )
  , ≋→≈ ( ≋-∘ (≋-sym (≋-⊢⊢ n k g)) (≋-sym (≋-⊣⊢ m' k f))
        ⟫ ≋-≈ (≈.sym (⊢-∘ _ _))
        ⟫ ≋-⊢ (≋-≈ (proj₂ (c g)))
        ⟫ ≋-≈ (⊢-∘ _ _)
        ⟫ ≋-∘ (≋-⊣⊢ n' k f) (≋-⊢⊢ m k g) ) )

central-⊣ : {f : Hom m n} → Central f → ∀ k → Central (k ⊣ f)
central-⊣ {m} {n} {f} c k {m'} {n'} g =
  ( ≋→≈ ( ≋-∘ (≋-⊣⊢ k n' f) (≋-sym (≋-⊣⊣ k m g))
        ⟫ ≋-≈ (≈.sym (⊣-∘ _ _))
        ⟫ ≋-⊣ (≋-≈ (proj₁ (c g)))
        ⟫ ≋-≈ (⊣-∘ _ _)
        ⟫ ≋-∘ (≋-⊣⊣ k n g) (≋-sym (≋-⊣⊢ k m' f)) )
  , ≋→≈ ( ≋-∘ (≋-sym (≋-⊢⊢ k n g)) (≋-⊣⊣ m' k f)
        ⟫ ≋-≈ (proj₂ (c (g ⊢ k)))
        ⟫ ≋-∘ (≋-sym (≋-⊣⊣ n' k f)) (≋-⊢⊢ k m g) ) )

------------------------------------------------------------------------
-- The core identities (operations = morphisms into 1)
------------------------------------------------------------------------

-- (A) / associativity of U(D)
core-assoc : ∀ m₁ m₂ n₁ n₂ {n} (a : Hom (n₁ + suc n₂) 1) (b : Hom n 1)
  (p : (m₁ + n₁) + suc (n₂ + m₂) ≡ m₁ + ((n₁ + suc n₂) + m₂))
  → ((m₁ ⊣ (a ⊢ m₂)) ∘[ p ] ((m₁ + n₁) ⊣ (b ⊢ (n₂ + m₂))))
    ≋ (m₁ ⊣ ((a ∘ (n₁ ⊣ (b ⊢ n₂))) ⊢ m₂))
core-assoc m₁ m₂ n₁ n₂ a b p =
  ≋-∘[] p ≋-refl (≋-sym (≋-⊣⊣ m₁ n₁ _) ⟫ ≋-⊣ (≋-⊣ (≋-sym (≋-⊢⊢ n₂ m₂ b)) ⟫ ≋-sym (≋-⊣⊢ n₁ m₂ _)))
  ⟫ ≋-≈ (≈.sym (⊣-∘ _ _))
  ⟫ ≋-⊣ (≋-≈ (≈.sym (⊢-∘ _ _)))

-- left unit of U(D)
core-lunit : (a : Hom m 1) → (idₕ ∘ (0 ⊣ (a ⊢ 0))) ≋ a
core-lunit a = ≋-idˡ _ ⟫ ≋-0⊣ _ ⟫ ≋-⊢0 a

-- (U₁) / right unit of U(D)
core-runit : ∀ n₁ n₂ → (n₁ ⊣ (idₕ {1} ⊢ n₂)) ≈ idₕ
core-runit n₁ n₂ = ≈.trans (⊣-cong ⊢-id) ⊣-id

-- (CEN) / commutation in U(D): two substitutions in disjoint positions
-- commute when either operation is central
core-CEN : ∀ m₁ m m₂ {n₁ n₂} (a : Hom n₁ 1) (b : Hom n₂ 1) → Central a ⊎ Central b
  → (p  : (m₁ + (n₁ + m)) + suc m₂ ≡ m₁ + (n₁ + (m + suc m₂)))
    (p' : m₁ + suc (m + (n₂ + m₂)) ≡ (m₁ + suc m) + (n₂ + m₂))
  → ((m₁ ⊣ (a ⊢ (m + suc m₂))) ∘[ p ] ((m₁ + (n₁ + m)) ⊣ (b ⊢ m₂)))
    ≋ (((m₁ + suc m) ⊣ (b ⊢ m₂)) ∘[ p' ] (m₁ ⊣ (a ⊢ (m + (n₂ + m₂)))))
core-CEN m₁ m m₂ {n₁} {n₂} a b c p p' =
  ≋-∘[] p (≋-⊣ (≋-sym (≋-⊢⊢ m (suc m₂) a) ⟫ ≋-sym (≋-⊢⊢ 1 m₂ (a ⊢ m))))
          (≋-sym (≋-⊣⊣ m₁ (n₁ + m) _) ⟫ ≋-⊣ (≋-sym (≋-⊣⊢ (n₁ + m) m₂ b)))
  ⟫ ≋-≈ (≈.sym (⊣-∘ _ _))
  ⟫ ≋-⊣ (≋-≈ (≈.sym (⊢-∘ _ _)))
  ⟫ ≋-⊣ (≋-⊢ (≋-≈ inner))
  ⟫ ≋-⊣ (≋-≈ (⊢-∘ _ _))
  ⟫ ≋-≈ (⊣-∘ _ _)
  ⟫ ≋-sym (≋-∘[] p' (≋-sym (≋-⊣ (≋-⊣⊢ (suc m) m₂ b) ⟫ ≋-⊣⊣ m₁ (suc m) _))
                    (≋-sym (≋-⊣ (≋-⊢⊢ n₂ m₂ (a ⊢ m) ⟫ ≋-⊢⊢ m (n₂ + m₂) a))))
  where
    inner : (((a ⊢ m) ⊢ 1) ∘ ((n₁ + m) ⊣ b)) ≈ (((1 + m) ⊣ b) ∘ ((a ⊢ m) ⊢ n₂))
    inner = case c of λ where
      (inj₁ ca) → proj₁ (central-⊢ ca m b)
      (inj₂ cb) → proj₂ (cb (a ⊢ m))

------------------------------------------------------------------------
-- With an action of renamings R r : m → n for r ∈ Ren(n ⇒ m)
-- (contravariant, cf. Def. 3.19 "v[r] := v ∘ r")
------------------------------------------------------------------------

record RenAction : Set where
  field
    R         : Ren n m → Hom m n
    R-cong    : {r s : Ren n m} → r ≗ s → R r ≈ R s
    R-id      : R (idʳ {n}) ≈ idₕ
    R-∘       : (r : Ren m n) (s : Ren n k) → R (s ∘ʳ r) ≈ R r ∘ R s
    R-+       : ∀ {m₁ n₁ m₂ n₂} (r : Ren n₁ m₁) (s : Ren n₂ m₂) → R (r +ʳ s) ≈ (R r ⊢ n₂) ∘ (m₁ ⊣ R s)
    R-σ       : ∀ m n → R (σʳ m n) ≈ σ n m
    R-central : (r : Ren n m) → Central (R r)

module WithR (A : RenAction) where
  open RenAction A

  -- a cast renaming acts as a cast (R (castʳ p) : n → m for p : m ≡ n)
  R-cast : (p : m ≡ n) → R (castʳ p) ≋ idₕ {m}
  R-cast refl = ≋-≈ R-id

  R-cast' : (p : m ≡ n) → R (castʳ p) ≋ idₕ {n}
  R-cast' refl = ≋-≈ R-id

  -- absorbing the action of a cast renaming into a cast composition
  ≋-R-cast : (p : a ≡ b) (g : Hom a k) (f : Hom m b) → (g ∘ (R (castʳ p) ∘ f)) ≋ (g ∘[ sym p ] f)
  ≋-R-cast refl g f = ≋-≈ (∘-cong ≈.refl (∘-cong R-id ≈.refl))

  -- f[r] for f into 1, and f[r][s] = f[s ∘ r]
  R-∘' : (r : Ren m n) (s : Ren n k) (f : Hom m 1) → f ∘ R (s ∘ʳ r) ≈ (f ∘ R r) ∘ R s
  R-∘' r s f = ≈.trans (∘-cong ≈.refl (R-∘ r s)) (≈.sym (∘-assoc _ _ _))

  -- R (r₁ + s + r₂) as a composite of three whiskered pieces
  R-+₃ : ∀ {m₁ n₁ m n m₂ n₂} (r₁ : Ren n₁ m₁) (s : Ren n m) (r₂ : Ren n₂ m₂)
    → R (r₁ +ʳ s +ʳ r₂) ≈ (R r₁ ⊢ (n + n₂)) ∘ (m₁ ⊣ (R s ⊢ n₂)) ∘ (m₁ ⊣ (m ⊣ R r₂))
  R-+₃ {m₁} r₁ s r₂ =
    ≈.trans (R-+ r₁ (s +ʳ r₂))
    (≈.trans (∘-cong ≈.refl (⊣-cong (R-+ s r₂)))
             (∘-cong ≈.refl (⊣-∘ _ _)))

  -- id + s + id
  R-mid : ∀ {m₁ m n m₂} (s : Ren n m) → R (idʳ {m₁} +ʳ s +ʳ idʳ {m₂}) ≈ m₁ ⊣ (R s ⊢ m₂)
  R-mid {m₁} {m} {n} {m₂} s =
    ≈.trans (R-+₃ idʳ s idʳ)
    (≈.trans (∘-cong (⊢-cong R-id) (∘-cong ≈.refl (⊣-cong (⊣-cong R-id))))
    (≈.trans (∘-cong ⊢-id (∘-cong ≈.refl (⊣-cong ⊣-id)))
    (≈.trans (∘-idˡ _) (≈.trans (∘-cong ≈.refl ⊣-id) (∘-idʳ _)))))

  -- (N) / the renaming–substitution interchange of U(D)
  core-N : ∀ {n₁ m₁ n m n₂ m₂} (a : Hom n 1) (r₁ : Ren n₁ m₁) (s : Ren n m) (r₂ : Ren n₂ m₂)
    → ((n₁ ⊣ (a ⊢ n₂)) ∘ R (r₁ +ʳ s +ʳ r₂))
      ≈ (R (r₁ +ʳ idʳ {1} +ʳ r₂) ∘ (m₁ ⊣ ((a ∘ R s) ⊢ m₂)))
  core-N {n₁} {m₁} {n} {m} {n₂} {m₂} a r₁ s r₂ = ≋→≈
    ( ≋-∘ ≋-refl (≋-≈ (R-+₃ r₁ s r₂))
    ⟫ ≋-≈ (≈.sym (∘-assoc _ _ _))
    ⟫ ≋-∘ (≋-≈ (≈.sym (proj₁ (R-central r₁ (a ⊢ n₂))))) ≋-refl
    ⟫ ≋-≈ (∘-assoc _ _ _)
    ⟫ ≋-∘ ≋-refl (≋-≈ (≈.sym (∘-assoc _ _ _)) ⟫ ≋-∘ (≋-≈ (≈.sym (⊣-∘ _ _))) ≋-refl ⟫ ≋-≈ (≈.sym (⊣-∘ _ _)))
    ⟫ ≋-∘ ≋-refl (≋-⊣ (≋-∘ (≋-≈ (≈.sym (⊢-∘ _ _))) ≋-refl ⟫ ≋-≈ (proj₂ (R-central r₂ (a ∘ R s)))))
    ⟫ ≋-∘ ≋-refl (≋-≈ (⊣-∘ _ _))
    ⟫ ≋-≈ (≈.sym (∘-assoc _ _ _))
    ⟫ ≋-∘ (≋-≈ (≈.sym idmid)) ≋-refl )
    where
      idmid : R (r₁ +ʳ idʳ {1} +ʳ r₂) ≈ (R r₁ ⊢ (1 + n₂)) ∘ (m₁ ⊣ (1 ⊣ R r₂))
      idmid = ≈.trans (R-+₃ r₁ idʳ r₂)
              (∘-cong ≈.refl (≈.trans (∘-cong (⊣-cong (⊢-cong R-id)) ≈.refl)
                             (≈.trans (∘-cong (⊣-cong ⊢-id) ≈.refl) (≈.trans (∘-cong ⊣-id ≈.refl) (∘-idˡ _)))))

  -- (Sℓ) / σ-natˡ of U(D):  moving the hole one step to the right
  core-Sℓ : ∀ m₁ m₂ {n} (a : Hom n 1) (p : m₁ + ((1 + n) + m₂) ≡ (m₁ + 1) + (n + m₂))
    → (R (idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∘ (m₁ ⊣ (a ⊢ suc m₂)))
      ≋ (((m₁ + 1) ⊣ (a ⊢ m₂)) ∘[ p ] R (idʳ {m₁} +ʳ σʳ 1 n +ʳ idʳ {m₂}))
  core-Sℓ m₁ m₂ {n} a p =
    ≋-∘ (≋-≈ (R-mid (σʳ 1 1)) ⟫ ≋-⊣ (≋-⊢ (≋-≈ (R-σ 1 1)))) (≋-⊣ (≋-sym (≋-⊢⊢ 1 m₂ a)))
    ⟫ ≋-≈ (≈.sym (⊣-∘ _ _))
    ⟫ ≋-⊣ (≋-≈ (≈.sym (⊢-∘ _ _)))
    ⟫ ≋-⊣ (≋-⊢ (≋-≈ (σ-nat₁ʳ a)))
    ⟫ ≋-⊣ (≋-≈ (⊢-∘ _ _))
    ⟫ ≋-≈ (⊣-∘ _ _)
    ⟫ ≋-sym (≋-∘[] p (≋-sym (≋-⊣ (≋-⊣⊢ 1 m₂ a) ⟫ ≋-⊣⊣ m₁ 1 _))
                     (≋-sym (≋-⊣ (≋-⊢ (≋-≈ (≈.sym (R-σ 1 n)))) ⟫ ≋-≈ (≈.sym (R-mid (σʳ 1 n))))))

  -- (Sr) / σ-natʳ of U(D):  moving the hole one step to the left
  core-Sr : ∀ m₁ m₂ {n} (a : Hom n 1)
    (p : (m₁ + 1) + suc m₂ ≡ m₁ + suc (suc m₂)) (q : m₁ + ((n + 1) + m₂) ≡ m₁ + (n + suc m₂))
    → (R (idʳ {m₁} +ʳ σʳ 1 1 +ʳ idʳ {m₂}) ∘[ p ] ((m₁ + 1) ⊣ (a ⊢ m₂)))
      ≋ ((m₁ ⊣ (a ⊢ suc m₂)) ∘[ q ] R (idʳ {m₁} +ʳ σʳ n 1 +ʳ idʳ {m₂}))
  core-Sr m₁ m₂ {n} a p q =
    ≋-∘[] p (≋-≈ (R-mid (σʳ 1 1)) ⟫ ≋-⊣ (≋-⊢ (≋-≈ (R-σ 1 1))))
            (≋-sym (≋-⊣⊣ m₁ 1 _) ⟫ ≋-⊣ (≋-sym (≋-⊣⊢ 1 m₂ a)))
    ⟫ ≋-≈ (≈.sym (⊣-∘ _ _))
    ⟫ ≋-⊣ (≋-≈ (≈.sym (⊢-∘ _ _)))
    ⟫ ≋-⊣ (≋-⊢ (≋-≈ (σ-nat₁ˡ a)))
    ⟫ ≋-⊣ (≋-≈ (⊢-∘ _ _))
    ⟫ ≋-≈ (⊣-∘ _ _)
    ⟫ ≋-sym (≋-∘[] q (≋-sym (≋-⊣ (≋-⊢⊢ 1 m₂ a)))
                     (≋-sym (≋-⊣ (≋-⊢ (≋-≈ (≈.sym (R-σ n 1)))) ⟫ ≋-≈ (≈.sym (R-mid (σʳ n 1))))))

  -- (D) / discarding: given that a is discardable
  core-D : ∀ m₁ m₂ {n} (a : Hom n 1) → R (!ʳ 1) ∘ a ≈ R (!ʳ n)
    → (R (idʳ {m₁} +ʳ !ʳ 1 +ʳ idʳ {m₂}) ∘ (m₁ ⊣ (a ⊢ m₂))) ≈ R (idʳ {m₁} +ʳ !ʳ n +ʳ idʳ {m₂})
  core-D m₁ m₂ {n} a d = ≋→≈
    ( ≋-∘ (≋-≈ (R-mid (!ʳ 1))) ≋-refl
    ⟫ ≋-≈ (≈.sym (⊣-∘ _ _))
    ⟫ ≋-⊣ (≋-≈ (≈.sym (⊢-∘ _ _)) ⟫ ≋-⊢ (≋-≈ d))
    ⟫ ≋-≈ (≈.sym (R-mid (!ʳ n))) )

  -- (C) / copying: given that a is copyable
  core-C : ∀ m₁ m₂ {n} (a : Hom n 1) → R (Δʳ 1) ∘ a ≈ ((a ⊢ 1) ∘ (n ⊣ a)) ∘ R (Δʳ n)
    → (p : (m₁ + n) + suc m₂ ≡ m₁ + (n + suc m₂)) (q : m₁ + ((n + n) + m₂) ≡ (m₁ + n) + (n + m₂))
    → (R (idʳ {m₁} +ʳ Δʳ 1 +ʳ idʳ {m₂}) ∘ (m₁ ⊣ (a ⊢ m₂)))
      ≋ (((m₁ ⊣ (a ⊢ suc m₂)) ∘[ p ] ((m₁ + n) ⊣ (a ⊢ m₂))) ∘[ q ] R (idʳ {m₁} +ʳ Δʳ n +ʳ idʳ {m₂}))
  core-C m₁ m₂ {n} a cp p q =
    ≋-∘ (≋-≈ (R-mid (Δʳ 1))) ≋-refl
    ⟫ ≋-≈ (≈.sym (⊣-∘ _ _))
    ⟫ ≋-⊣ (≋-≈ (≈.sym (⊢-∘ _ _)) ⟫ ≋-⊢ (≋-≈ cp) ⟫ ≋-≈ (⊢-∘ _ _) ⟫ ≋-∘ (≋-≈ (⊢-∘ _ _)) ≋-refl)
    ⟫ ≋-≈ (⊣-∘ _ _)
    ⟫ ≋-sym (≋-∘[] q (≋-∘[] p (≋-⊣ (≋-sym (≋-⊢⊢ 1 m₂ a))) (≋-sym (≋-⊣⊣ m₁ n _) ⟫ ≋-⊣ (≋-sym (≋-⊣⊢ n m₂ a)))
                      ⟫ ≋-≈ (≈.sym (⊣-∘ _ _)))
                     (≋-≈ (R-mid (Δʳ n))))
