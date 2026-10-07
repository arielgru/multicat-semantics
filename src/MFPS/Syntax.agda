------------------------------------------------------------------------
-- Section 2.2: the syntax of λml* (Fig. 1), renaming and substitution
-- (Def. 2.4, Lemma 2.5).
--
-- Representation.  Terms are intrinsically scoped by the length n of
-- their context: `Trm n s` is the set of well-formed terms Γ ⊢ E with
-- |Γ| = n and sort s.  Variables are de Bruijn *positions* (Fin n,
-- position 0 = leftmost variable of Γ), and binders bind the *last*
-- position, so the paper's  Γ, x ⊢ M  is  `Trm (n + 1) cmp`.
--
-- The paper's well-formedness rules (Fig. 1) form terms from subterms
-- in *disjoint* contexts and add weakening, exchange and contraction
-- as separate structural rules.  We use the equivalent shared-context
-- presentation in which every constructor takes its subterms in the
-- same context and the structural rules are admissible (they are the
-- renamings `ren`).  The disjoint-context rules are derivable, e.g.
--   Γ₁, x ⊢ M₁  and  Γ₂ ⊢ M₂  give  bnd (ren inr M₂) (ren (inl + id) M₁)
-- in context Γ₁, Γ₂.  Lemma 2.5 (substitution preserves
-- well-formedness) is the well-typedness of `sub`.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude

module MFPS.Syntax where

private
  variable
    k m n : ℕ

record Signature : Set₁ where
  field
    Func : ℕ → Set
    Proc : ℕ → Set

data Sort : Set where
  val cmp : Sort

module Terms (Σ : Signature) where
  open Signature Σ

  data Trm (n : ℕ) : Sort → Set
  data Args (n : ℕ) : ℕ → Set

  data Trm n where
    var : Fin n → Trm n val
    fun : Func k → Args n k → Trm n val
    lam : Trm (n + 1) cmp → Trm n val
    ret : Trm n val → Trm n cmp
    bnd : Trm n cmp → Trm (n + 1) cmp → Trm n cmp        -- let x ⇐ M₂ in M₁  is  bnd M₂ M₁
    prc : Proc k → Args n k → Trm n cmp
    app : Trm n val → Trm n val → Trm n cmp

  data Args n where
    []  : Args n 0
    _∷_ : Trm n val → Args n k → Args n (suc k)

  Val Cmp : ℕ → Set
  Val n = Trm n val
  Cmp n = Trm n cmp

  private
    variable
      s : Sort
      j : ℕ

  -- the last variable of a context of length n + 1
  last : Fin (n + 1)
  last {n} = n ↑ʳ zero

  lookup : Args n k → Fin k → Val n
  lookup (V ∷ _)  zero    = V
  lookup (_ ∷ Vs) (suc i) = lookup Vs i

  ----------------------------------------------------------------------
  -- Renaming (the structural rules of Fig. 1, all at once)
  ----------------------------------------------------------------------

  liftʳ : Ren m n → Ren (m + 1) (n + 1)
  liftʳ r = r +ʳ idʳ {1}

  ren  : Ren m n → Trm m s → Trm n s
  renA : Ren m n → Args m k → Args n k
  ren r (var i)      = var (r i)
  ren r (fun f Vs)   = fun f (renA r Vs)
  ren r (lam M)      = lam (ren (liftʳ r) M)
  ren r (ret V)      = ret (ren r V)
  ren r (bnd M₂ M₁)  = bnd (ren r M₂) (ren (liftʳ r) M₁)
  ren r (prc p Vs)   = prc p (renA r Vs)
  ren r (app V₁ V₂)  = app (ren r V₁) (ren r V₂)
  renA r []       = []
  renA r (V ∷ Vs) = ren r V ∷ renA r Vs

  wk : Trm n s → Trm (n + 1) s
  wk = ren (_↑ˡ 1)

  ----------------------------------------------------------------------
  -- Simultaneous substitution of values for variables (Def. 2.4)
  ----------------------------------------------------------------------

  Subst : ℕ → ℕ → Set
  Subst m n = Fin m → Val n

  idˢ : Subst n n
  idˢ = var

  -- the substitution induced by a renaming
  ⌜_⌝ : Ren m n → Subst m n
  ⌜ r ⌝ i = var (r i)

  liftˢ : Subst m n → Subst (m + 1) (n + 1)
  liftˢ {m} {n} σ i = [ (λ j → wk (σ j)) , (λ _ → var last) ]′ (splitAt m i)

  sub  : Subst m n → Trm m s → Trm n s
  subA : Subst m n → Args m k → Args n k
  sub σ (var i)      = σ i
  sub σ (fun f Vs)   = fun f (subA σ Vs)
  sub σ (lam M)      = lam (sub (liftˢ σ) M)
  sub σ (ret V)      = ret (sub σ V)
  sub σ (bnd M₂ M₁)  = bnd (sub σ M₂) (sub (liftˢ σ) M₁)
  sub σ (prc p Vs)   = prc p (subA σ Vs)
  sub σ (app V₁ V₂)  = app (sub σ V₁) (sub σ V₂)
  subA σ []       = []
  subA σ (V ∷ Vs) = sub σ V ∷ subA σ Vs

  -- extending a substitution by a value for the last variable
  _∷ˢ_ : Subst m n → Val n → Subst (m + 1) n
  _∷ˢ_ {m} σ V i = [ σ , (λ _ → V) ]′ (splitAt m i)

  -- single substitution for the last variable:  E {V/x}
  infix 9 _[_]
  _[_] : Trm (n + 1) s → Val n → Trm n s
  E [ V ] = sub (idˢ ∷ˢ V) E

  -- composition of substitutions
  infixr 9 _∘ˢ_
  _∘ˢ_ : Subst n k → Subst m n → Subst m k
  (τ ∘ˢ σ) i = sub τ (σ i)

  ----------------------------------------------------------------------
  -- Computation rules for lifting and extension
  ----------------------------------------------------------------------

  liftʳ-inl : (r : Ren m n) (j : Fin m) → liftʳ r (j ↑ˡ 1) ≡ r j ↑ˡ 1
  liftʳ-inl r j = +ʳ-inj₁ r (idʳ {1}) j

  liftʳ-last : (r : Ren m n) → liftʳ r (last {m}) ≡ last {n}
  liftʳ-last r = +ʳ-inj₂ r (idʳ {1}) zero

  liftˢ-inl : (σ : Subst m n) (j : Fin m) → liftˢ σ (j ↑ˡ 1) ≡ wk (σ j)
  liftˢ-inl {m} {n} σ j = cong [ (λ j → wk (σ j)) , (λ _ → var last) ]′ (splitAt-↑ˡ m j 1)

  liftˢ-last : (σ : Subst m n) → liftˢ σ (last {m}) ≡ var (last {n})
  liftˢ-last {m} {n} σ = cong [ (λ j → wk (σ j)) , (λ _ → var last) ]′ (splitAt-↑ʳ m 1 zero)

  ∷ˢ-inl : (σ : Subst m n) (V : Val n) (j : Fin m) → (σ ∷ˢ V) (j ↑ˡ 1) ≡ σ j
  ∷ˢ-inl {m} σ V j = cong [ σ , (λ _ → V) ]′ (splitAt-↑ˡ m j 1)

  ∷ˢ-last : (σ : Subst m n) (V : Val n) → (σ ∷ˢ V) (last {m}) ≡ V
  ∷ˢ-last {m} σ V = cong [ σ , (λ _ → V) ]′ (splitAt-↑ʳ m 1 zero)

  ----------------------------------------------------------------------
  -- The σ-calculus: congruence, identity and fusion laws
  ----------------------------------------------------------------------

  liftʳ-cong : {r r' : Ren m n} → r ≗ r' → liftʳ r ≗ liftʳ r'
  liftʳ-cong e = +ʳ-cong e (λ _ → refl)

  liftʳ-id : liftʳ (idʳ {n}) ≗ idʳ
  liftʳ-id {n} = +ʳ-id n 1

  liftʳ-∘ : (r : Ren m n) (r' : Ren n k) → liftʳ (r' ∘ʳ r) ≗ liftʳ r' ∘ʳ liftʳ r
  liftʳ-∘ r r' = +ʳ-∘ r' r idʳ idʳ

  ren-cong  : {r r' : Ren m n} → r ≗ r' → (E : Trm m s) → ren r E ≡ ren r' E
  renA-cong : {r r' : Ren m n} → r ≗ r' → (Vs : Args m k) → renA r Vs ≡ renA r' Vs
  ren-cong e (var i)      = cong var (e i)
  ren-cong e (fun f Vs)   = cong (fun f) (renA-cong e Vs)
  ren-cong e (lam M)      = cong lam (ren-cong (liftʳ-cong e) M)
  ren-cong e (ret V)      = cong ret (ren-cong e V)
  ren-cong e (bnd M₂ M₁)  = cong₂ bnd (ren-cong e M₂) (ren-cong (liftʳ-cong e) M₁)
  ren-cong e (prc p Vs)   = cong (prc p) (renA-cong e Vs)
  ren-cong e (app V₁ V₂)  = cong₂ app (ren-cong e V₁) (ren-cong e V₂)
  renA-cong e []       = refl
  renA-cong e (V ∷ Vs) = cong₂ _∷_ (ren-cong e V) (renA-cong e Vs)

  ren-id  : (E : Trm n s) → ren idʳ E ≡ E
  renA-id : (Vs : Args n k) → renA idʳ Vs ≡ Vs
  ren-id (var i)      = refl
  ren-id (fun f Vs)   = cong (fun f) (renA-id Vs)
  ren-id (lam M)      = cong lam (trans (ren-cong liftʳ-id M) (ren-id M))
  ren-id (ret V)      = cong ret (ren-id V)
  ren-id (bnd M₂ M₁)  = cong₂ bnd (ren-id M₂) (trans (ren-cong liftʳ-id M₁) (ren-id M₁))
  ren-id (prc p Vs)   = cong (prc p) (renA-id Vs)
  ren-id (app V₁ V₂)  = cong₂ app (ren-id V₁) (ren-id V₂)
  renA-id []       = refl
  renA-id (V ∷ Vs) = cong₂ _∷_ (ren-id V) (renA-id Vs)

  ren-∘  : (r : Ren m n) (r' : Ren n k) (E : Trm m s) → ren (r' ∘ʳ r) E ≡ ren r' (ren r E)
  renA-∘ : (r : Ren m n) (r' : Ren n k) (Vs : Args m j) → renA (r' ∘ʳ r) Vs ≡ renA r' (renA r Vs)
  ren-∘ r r' (var i)      = refl
  ren-∘ r r' (fun f Vs)   = cong (fun f) (renA-∘ r r' Vs)
  ren-∘ r r' (lam M)      = cong lam (trans (ren-cong (liftʳ-∘ r r') M) (ren-∘ (liftʳ r) (liftʳ r') M))
  ren-∘ r r' (ret V)      = cong ret (ren-∘ r r' V)
  ren-∘ r r' (bnd M₂ M₁)  = cong₂ bnd (ren-∘ r r' M₂) (trans (ren-cong (liftʳ-∘ r r') M₁) (ren-∘ (liftʳ r) (liftʳ r') M₁))
  ren-∘ r r' (prc p Vs)   = cong (prc p) (renA-∘ r r' Vs)
  ren-∘ r r' (app V₁ V₂)  = cong₂ app (ren-∘ r r' V₁) (ren-∘ r r' V₂)
  renA-∘ r r' []       = refl
  renA-∘ r r' (V ∷ Vs) = cong₂ _∷_ (ren-∘ r r' V) (renA-∘ r r' Vs)

  liftˢ-cong : {σ σ' : Subst m n} → σ ≗ σ' → liftˢ σ ≗ liftˢ σ'
  liftˢ-cong {σ = σ} {σ'} e =
    Fin+1-ext (λ j → trans (liftˢ-inl σ j) (trans (cong wk (e j)) (sym (liftˢ-inl σ' j))))
              (trans (liftˢ-last σ) (sym (liftˢ-last σ')))

  sub-cong  : {σ σ' : Subst m n} → σ ≗ σ' → (E : Trm m s) → sub σ E ≡ sub σ' E
  subA-cong : {σ σ' : Subst m n} → σ ≗ σ' → (Vs : Args m k) → subA σ Vs ≡ subA σ' Vs
  sub-cong e (var i)      = e i
  sub-cong e (fun f Vs)   = cong (fun f) (subA-cong e Vs)
  sub-cong e (lam M)      = cong lam (sub-cong (liftˢ-cong e) M)
  sub-cong e (ret V)      = cong ret (sub-cong e V)
  sub-cong e (bnd M₂ M₁)  = cong₂ bnd (sub-cong e M₂) (sub-cong (liftˢ-cong e) M₁)
  sub-cong e (prc p Vs)   = cong (prc p) (subA-cong e Vs)
  sub-cong e (app V₁ V₂)  = cong₂ app (sub-cong e V₁) (sub-cong e V₂)
  subA-cong e []       = refl
  subA-cong e (V ∷ Vs) = cong₂ _∷_ (sub-cong e V) (subA-cong e Vs)

  -- lifting a renaming-substitution
  liftˢ-⌜⌝ : (r : Ren m n) → liftˢ ⌜ r ⌝ ≗ ⌜ liftʳ r ⌝
  liftˢ-⌜⌝ r = Fin+1-ext (λ j → trans (liftˢ-inl ⌜ r ⌝ j) (cong var (sym (liftʳ-inl r j))))
                         (trans (liftˢ-last ⌜ r ⌝) (cong var (sym (liftʳ-last r))))

  liftˢ-id : liftˢ (idˢ {n}) ≗ idˢ
  liftˢ-id {n} i = trans (liftˢ-⌜⌝ idʳ i) (cong var (liftʳ-id i))

  -- substitution by a renaming is renaming
  sub-⌜⌝  : (r : Ren m n) (E : Trm m s) → sub ⌜ r ⌝ E ≡ ren r E
  subA-⌜⌝ : (r : Ren m n) (Vs : Args m k) → subA ⌜ r ⌝ Vs ≡ renA r Vs
  sub-⌜⌝ r (var i)      = refl
  sub-⌜⌝ r (fun f Vs)   = cong (fun f) (subA-⌜⌝ r Vs)
  sub-⌜⌝ r (lam M)      = cong lam (trans (sub-cong (liftˢ-⌜⌝ r) M) (sub-⌜⌝ (liftʳ r) M))
  sub-⌜⌝ r (ret V)      = cong ret (sub-⌜⌝ r V)
  sub-⌜⌝ r (bnd M₂ M₁)  = cong₂ bnd (sub-⌜⌝ r M₂) (trans (sub-cong (liftˢ-⌜⌝ r) M₁) (sub-⌜⌝ (liftʳ r) M₁))
  sub-⌜⌝ r (prc p Vs)   = cong (prc p) (subA-⌜⌝ r Vs)
  sub-⌜⌝ r (app V₁ V₂)  = cong₂ app (sub-⌜⌝ r V₁) (sub-⌜⌝ r V₂)
  subA-⌜⌝ r []       = refl
  subA-⌜⌝ r (V ∷ Vs) = cong₂ _∷_ (sub-⌜⌝ r V) (subA-⌜⌝ r Vs)

  sub-id : (E : Trm n s) → sub idˢ E ≡ E
  sub-id E = trans (sub-⌜⌝ idʳ E) (ren-id E)

  -- fusion: renaming after substitution
  liftˢ-ren : (σ : Subst m n) (r : Ren n k) → liftˢ (λ i → ren r (σ i)) ≗ (λ i → ren (liftʳ r) (liftˢ σ i))
  liftˢ-ren σ r = Fin+1-ext
    (λ j → trans (liftˢ-inl (λ i → ren r (σ i)) j)
           (trans (sym (ren-∘ r (_↑ˡ 1) (σ j)))
           (trans (ren-cong (λ x → sym (liftʳ-inl r x)) (σ j))
           (trans (ren-∘ (_↑ˡ 1) (liftʳ r) (σ j)) (cong (ren (liftʳ r)) (sym (liftˢ-inl σ j)))))))
    (trans (liftˢ-last (λ i → ren r (σ i))) (trans (cong var (sym (liftʳ-last r))) (cong (ren (liftʳ r)) (sym (liftˢ-last σ)))))

  ren-sub  : (σ : Subst m n) (r : Ren n k) (E : Trm m s) → ren r (sub σ E) ≡ sub (λ i → ren r (σ i)) E
  renA-sub : (σ : Subst m n) (r : Ren n k) (Vs : Args m j) → renA r (subA σ Vs) ≡ subA (λ i → ren r (σ i)) Vs
  ren-sub σ r (var i)      = refl
  ren-sub σ r (fun f Vs)   = cong (fun f) (renA-sub σ r Vs)
  ren-sub σ r (lam M)      = cong lam (trans (ren-sub (liftˢ σ) (liftʳ r) M) (sub-cong (λ i → sym (liftˢ-ren σ r i)) M))
  ren-sub σ r (ret V)      = cong ret (ren-sub σ r V)
  ren-sub σ r (bnd M₂ M₁)  = cong₂ bnd (ren-sub σ r M₂) (trans (ren-sub (liftˢ σ) (liftʳ r) M₁) (sub-cong (λ i → sym (liftˢ-ren σ r i)) M₁))
  ren-sub σ r (prc p Vs)   = cong (prc p) (renA-sub σ r Vs)
  ren-sub σ r (app V₁ V₂)  = cong₂ app (ren-sub σ r V₁) (ren-sub σ r V₂)
  renA-sub σ r []       = refl
  renA-sub σ r (V ∷ Vs) = cong₂ _∷_ (ren-sub σ r V) (renA-sub σ r Vs)

  -- fusion: substitution after renaming
  liftˢ-∘ʳ : (r : Ren m n) (σ : Subst n k) → liftˢ (σ ∘ r) ≗ (liftˢ σ ∘ liftʳ r)
  liftˢ-∘ʳ r σ = Fin+1-ext
    (λ j → trans (liftˢ-inl (σ ∘ r) j) (trans (sym (liftˢ-inl σ (r j))) (cong (liftˢ σ) (sym (liftʳ-inl r j)))))
    (trans (liftˢ-last (σ ∘ r)) (trans (sym (liftˢ-last σ)) (cong (liftˢ σ) (sym (liftʳ-last r)))))

  sub-ren  : (r : Ren m n) (σ : Subst n k) (E : Trm m s) → sub σ (ren r E) ≡ sub (σ ∘ r) E
  subA-ren : (r : Ren m n) (σ : Subst n k) (Vs : Args m j) → subA σ (renA r Vs) ≡ subA (σ ∘ r) Vs
  sub-ren r σ (var i)      = refl
  sub-ren r σ (fun f Vs)   = cong (fun f) (subA-ren r σ Vs)
  sub-ren r σ (lam M)      = cong lam (trans (sub-ren (liftʳ r) (liftˢ σ) M) (sub-cong (λ i → sym (liftˢ-∘ʳ r σ i)) M))
  sub-ren r σ (ret V)      = cong ret (sub-ren r σ V)
  sub-ren r σ (bnd M₂ M₁)  = cong₂ bnd (sub-ren r σ M₂) (trans (sub-ren (liftʳ r) (liftˢ σ) M₁) (sub-cong (λ i → sym (liftˢ-∘ʳ r σ i)) M₁))
  sub-ren r σ (prc p Vs)   = cong (prc p) (subA-ren r σ Vs)
  sub-ren r σ (app V₁ V₂)  = cong₂ app (sub-ren r σ V₁) (sub-ren r σ V₂)
  subA-ren r σ []       = refl
  subA-ren r σ (V ∷ Vs) = cong₂ _∷_ (sub-ren r σ V) (subA-ren r σ Vs)

  -- fusion: substitution after substitution
  liftˢ-∘ˢ : (σ : Subst m n) (τ : Subst n k) → liftˢ (τ ∘ˢ σ) ≗ (liftˢ τ ∘ˢ liftˢ σ)
  liftˢ-∘ˢ σ τ = Fin+1-ext
    (λ j → trans (liftˢ-inl (τ ∘ˢ σ) j)
           (trans (ren-sub τ (_↑ˡ 1) (σ j))
           (trans (sub-cong (λ x → sym (liftˢ-inl τ x)) (σ j))
           (trans (sym (sub-ren (_↑ˡ 1) (liftˢ τ) (σ j))) (cong (sub (liftˢ τ)) (sym (liftˢ-inl σ j)))))))
    (trans (liftˢ-last (τ ∘ˢ σ)) (trans (sym (liftˢ-last τ)) (cong (sub (liftˢ τ)) (sym (liftˢ-last σ)))))

  sub-sub  : (σ : Subst m n) (τ : Subst n k) (E : Trm m s) → sub τ (sub σ E) ≡ sub (τ ∘ˢ σ) E
  subA-sub : (σ : Subst m n) (τ : Subst n k) (Vs : Args m j) → subA τ (subA σ Vs) ≡ subA (τ ∘ˢ σ) Vs
  sub-sub σ τ (var i)      = refl
  sub-sub σ τ (fun f Vs)   = cong (fun f) (subA-sub σ τ Vs)
  sub-sub σ τ (lam M)      = cong lam (trans (sub-sub (liftˢ σ) (liftˢ τ) M) (sub-cong (λ i → sym (liftˢ-∘ˢ σ τ i)) M))
  sub-sub σ τ (ret V)      = cong ret (sub-sub σ τ V)
  sub-sub σ τ (bnd M₂ M₁)  = cong₂ bnd (sub-sub σ τ M₂) (trans (sub-sub (liftˢ σ) (liftˢ τ) M₁) (sub-cong (λ i → sym (liftˢ-∘ˢ σ τ i)) M₁))
  sub-sub σ τ (prc p Vs)   = cong (prc p) (subA-sub σ τ Vs)
  sub-sub σ τ (app V₁ V₂)  = cong₂ app (sub-sub σ τ V₁) (sub-sub σ τ V₂)
  subA-sub σ τ []       = refl
  subA-sub σ τ (V ∷ Vs) = cong₂ _∷_ (sub-sub σ τ V) (subA-sub σ τ Vs)

  -- transport along an arity equation is a cast renaming
  subst-ren : (p : m ≡ n) (E : Trm m s) → subst (λ n → Trm n s) p E ≡ ren (castʳ p) E
  subst-ren refl E = trans (sym (ren-id E)) (ren-cong (λ _ → refl) E)
