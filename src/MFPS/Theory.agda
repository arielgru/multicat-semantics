------------------------------------------------------------------------
-- Section 2.2, Fig. 2: the equational theory of λml*.
--
-- In the shared-context presentation the rules read:
--   (lunit)  let x ⇐ return V in M  ≡  M{V/x}
--   (runit)  let x ⇐ M in return x  ≡  M
--   (assoc)  let x₂ ⇐ (let x₁ ⇐ M₁ in M₂) in M
--              ≡ let x₁ ⇐ M₁ in let x₂ ⇐ M₂ in M      (M weakened by x₁)
--   (beta)   (λx.M) V ≡ M{V/x}
-- plus reflexivity, symmetry, transitivity and one congruence rule per
-- term former.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
open import MFPS.Prelude
open import MFPS.Syntax

module MFPS.Theory (Σ : Signature) where

open Terms Σ

private
  variable
    k m n : ℕ
    s : Sort

infix 4 _≈_ _≈ᵃ_

data _≈_  : Trm n s → Trm n s → Set
data _≈ᵃ_ : Args n k → Args n k → Set

data _≈_ where
  ≈-refl  : {E : Trm n s} → E ≈ E
  ≈-sym   : {E E' : Trm n s} → E ≈ E' → E' ≈ E
  ≈-trans : {E E' E'' : Trm n s} → E ≈ E' → E' ≈ E'' → E ≈ E''
  -- congruence
  ret-cong : {V V' : Val n} → V ≈ V' → ret V ≈ ret V'
  fun-cong : ∀ {f : Signature.Func Σ k} {Vs Vs' : Args n k} → Vs ≈ᵃ Vs' → fun f Vs ≈ fun f Vs'
  bnd-cong : {M₂ M₂' : Cmp n} {M₁ M₁' : Cmp (n + 1)} → M₂ ≈ M₂' → M₁ ≈ M₁' → bnd M₂ M₁ ≈ bnd M₂' M₁'
  prc-cong : ∀ {p : Signature.Proc Σ k} {Vs Vs' : Args n k} → Vs ≈ᵃ Vs' → prc p Vs ≈ prc p Vs'
  lam-cong : {M M' : Cmp (n + 1)} → M ≈ M' → lam M ≈ lam M'
  app-cong : {V₁ V₁' V₂ V₂' : Val n} → V₁ ≈ V₁' → V₂ ≈ V₂' → app V₁ V₂ ≈ app V₁' V₂'
  -- the monad laws
  lunit : (V : Val n) (M : Cmp (n + 1)) → bnd (ret V) M ≈ M [ V ]
  runit : (M : Cmp n) → bnd M (ret (var last)) ≈ M
  assoc : (M₁ : Cmp n) (M₂ : Cmp (n + 1)) (M : Cmp (n + 1))
        → bnd (bnd M₁ M₂) M ≈ bnd M₁ (bnd M₂ (ren (liftʳ (_↑ˡ 1)) M))   -- see wk₁ below
  -- β
  beta  : (M : Cmp (n + 1)) (V : Val n) → app (lam M) V ≈ M [ V ]

data _≈ᵃ_ where
  []  : _≈ᵃ_ {n} [] []
  _∷_ : {V V' : Val n} {Vs Vs' : Args n k} → V ≈ V' → Vs ≈ᵃ Vs' → (V ∷ Vs) ≈ᵃ (V' ∷ Vs')

≈-equiv : IsEquivalence (_≈_ {n} {s})
≈-equiv = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

≈-≡ : {E E' : Trm n s} → E ≡ E' → E ≈ E'
≈-≡ refl = ≈-refl

≈ᵃ-refl : {Vs : Args n k} → Vs ≈ᵃ Vs
≈ᵃ-refl {Vs = []}     = []
≈ᵃ-refl {Vs = V ∷ Vs} = ≈-refl ∷ ≈ᵃ-refl

------------------------------------------------------------------------
-- The theory is closed under renaming and substitution.
------------------------------------------------------------------------

-- renaming commutes with single substitution
ren-[] : (r : Ren m n) (E : Trm (m + 1) s) (V : Val m)
  → ren r (E [ V ]) ≡ (ren (liftʳ r) E) [ ren r V ]
ren-[] {m} {n} r E V =
  trans (ren-sub (idˢ ∷ˢ V) r E)
  (trans (sub-cong lemma E) (sym (sub-ren (liftʳ r) (idˢ ∷ˢ ren r V) E)))
  where
    lemma : (i : Fin (m + 1)) → ren r ((idˢ ∷ˢ V) i) ≡ (idˢ ∷ˢ ren r V) (liftʳ r i)
    lemma = Fin+1-ext
      (λ j → trans (cong (ren r) (∷ˢ-inl idˢ V j))
             (trans (sym (∷ˢ-inl idˢ (ren r V) (r j))) (cong (idˢ ∷ˢ ren r V) (sym (liftʳ-inl r j)))))
      (trans (cong (ren r) (∷ˢ-last idˢ V))
             (trans (sym (∷ˢ-last idˢ (ren r V))) (cong (idˢ ∷ˢ ren r V) (sym (liftʳ-last r)))))

-- the middle weakening used in (assoc)
wk₁ : Ren (n + 1) ((n + 1) + 1)
wk₁ = liftʳ (_↑ˡ 1)

-- renaming commutes with the middle weakening
ren-assoc-wk : (r : Ren m n) (M : Cmp (m + 1))
  → ren (liftʳ (liftʳ r)) (ren wk₁ M) ≡ ren wk₁ (ren (liftʳ r) M)
ren-assoc-wk {m} {n} r M =
  trans (sym (ren-∘ _ _ M)) (trans (ren-cong lemma M) (ren-∘ _ _ M))
  where
    lemma : (i : Fin (m + 1)) → liftʳ (liftʳ r) (wk₁ i) ≡ wk₁ (liftʳ r i)
    lemma = Fin+1-ext
      (λ j → trans (cong (liftʳ (liftʳ r)) (liftʳ-inl (_↑ˡ 1) j))
             (trans (liftʳ-inl (liftʳ r) (j ↑ˡ 1))
             (trans (cong (_↑ˡ 1) (liftʳ-inl r j))
             (trans (sym (liftʳ-inl (_↑ˡ 1) (r j))) (cong wk₁ (sym (liftʳ-inl r j)))))))
      (trans (cong (liftʳ (liftʳ r)) (liftʳ-last (_↑ˡ 1)))
             (trans (liftʳ-last (liftʳ r)) (trans (sym (liftʳ-last (_↑ˡ 1))) (cong wk₁ (sym (liftʳ-last r))))))

ren-last : (r : Ren m n) → liftʳ r (last {m}) ≡ last {n}
ren-last = liftʳ-last

ren-≈  : (r : Ren m n) {E E' : Trm m s} → E ≈ E' → ren r E ≈ ren r E'
renA-≈ : (r : Ren m n) {Vs Vs' : Args m k} → Vs ≈ᵃ Vs' → renA r Vs ≈ᵃ renA r Vs'
ren-≈ r ≈-refl = ≈-refl
ren-≈ r (≈-sym e) = ≈-sym (ren-≈ r e)
ren-≈ r (≈-trans e e') = ≈-trans (ren-≈ r e) (ren-≈ r e')
ren-≈ r (ret-cong e) = ret-cong (ren-≈ r e)
ren-≈ r (fun-cong e) = fun-cong (renA-≈ r e)
ren-≈ r (bnd-cong e e') = bnd-cong (ren-≈ r e) (ren-≈ (liftʳ r) e')
ren-≈ r (prc-cong e) = prc-cong (renA-≈ r e)
ren-≈ r (lam-cong e) = lam-cong (ren-≈ (liftʳ r) e)
ren-≈ r (app-cong e e') = app-cong (ren-≈ r e) (ren-≈ r e')
ren-≈ r (lunit V M) = ≈-trans (lunit (ren r V) (ren (liftʳ r) M)) (≈-≡ (sym (ren-[] r M V)))
ren-≈ r (runit M) = ≈-trans (≈-≡ (cong (bnd (ren r M)) (cong (ret ∘ var) (ren-last r)))) (runit (ren r M))
ren-≈ r (assoc M₁ M₂ M) = ≈-trans (assoc _ _ _) (≈-≡ (cong (bnd (ren r M₁) ∘ bnd (ren (liftʳ r) M₂)) (sym (ren-assoc-wk r M))))
ren-≈ r (beta M V) = ≈-trans (beta (ren (liftʳ r) M) (ren r V)) (≈-≡ (sym (ren-[] r M V)))
renA-≈ r [] = []
renA-≈ r (e ∷ es) = ren-≈ r e ∷ renA-≈ r es

-- substitution commutes with single substitution
sub-[] : (σ : Subst m n) (E : Trm (m + 1) s) (V : Val m)
  → sub σ (E [ V ]) ≡ (sub (liftˢ σ) E) [ sub σ V ]
sub-[] {m} {n} σ E V =
  trans (sub-sub (idˢ ∷ˢ V) σ E) (trans (sub-cong lemma E) (sym (sub-sub (liftˢ σ) (idˢ ∷ˢ sub σ V) E)))
  where
    lemma : (i : Fin (m + 1)) → sub σ ((idˢ ∷ˢ V) i) ≡ sub (idˢ ∷ˢ sub σ V) (liftˢ σ i)
    lemma = Fin+1-ext
      (λ j → trans (cong (sub σ) (∷ˢ-inl idˢ V j))
             (trans (sym (sub-id (σ j)))
             (trans (sub-cong (λ x → sym (∷ˢ-inl idˢ (sub σ V) x)) (σ j))
             (trans (sym (sub-ren (_↑ˡ 1) (idˢ ∷ˢ sub σ V) (σ j))) (cong (sub (idˢ ∷ˢ sub σ V)) (sym (liftˢ-inl σ j)))))))
      (trans (cong (sub σ) (∷ˢ-last idˢ V))
             (trans (sym (∷ˢ-last idˢ (sub σ V))) (cong (sub (idˢ ∷ˢ sub σ V)) (sym (liftˢ-last σ)))))

sub-assoc-wk : (σ : Subst m n) (M : Cmp (m + 1))
  → sub (liftˢ (liftˢ σ)) (ren wk₁ M) ≡ ren wk₁ (sub (liftˢ σ) M)
sub-assoc-wk {m} {n} σ M =
  trans (sub-ren _ _ M) (trans (sub-cong lemma M) (sym (ren-sub _ _ M)))
  where
    lemma : (i : Fin (m + 1)) → liftˢ (liftˢ σ) (wk₁ i) ≡ ren wk₁ (liftˢ σ i)
    lemma = Fin+1-ext
      (λ j → trans (cong (liftˢ (liftˢ σ)) (liftʳ-inl (_↑ˡ 1) j))
             (trans (liftˢ-inl (liftˢ σ) (j ↑ˡ 1))
             (trans (cong wk (liftˢ-inl σ j))
             (trans (sym (ren-∘ _ _ (σ j)))
             (trans (ren-cong (λ x → sym (liftʳ-inl (_↑ˡ 1) x)) (σ j))
             (trans (ren-∘ _ _ (σ j)) (cong (ren wk₁) (sym (liftˢ-inl σ j)))))))))
      (trans (cong (liftˢ (liftˢ σ)) (liftʳ-last (_↑ˡ 1)))
             (trans (liftˢ-last (liftˢ σ))
             (trans (cong var (sym (liftʳ-last (_↑ˡ 1)))) (cong (ren wk₁) (sym (liftˢ-last σ))))))

sub-last : (σ : Subst m n) → liftˢ σ (last {m}) ≡ var last
sub-last = liftˢ-last

sub-≈  : (σ : Subst m n) {E E' : Trm m s} → E ≈ E' → sub σ E ≈ sub σ E'
subA-≈ : (σ : Subst m n) {Vs Vs' : Args m k} → Vs ≈ᵃ Vs' → subA σ Vs ≈ᵃ subA σ Vs'
sub-≈ σ ≈-refl = ≈-refl
sub-≈ σ (≈-sym e) = ≈-sym (sub-≈ σ e)
sub-≈ σ (≈-trans e e') = ≈-trans (sub-≈ σ e) (sub-≈ σ e')
sub-≈ σ (ret-cong e) = ret-cong (sub-≈ σ e)
sub-≈ σ (fun-cong e) = fun-cong (subA-≈ σ e)
sub-≈ σ (bnd-cong e e') = bnd-cong (sub-≈ σ e) (sub-≈ (liftˢ σ) e')
sub-≈ σ (prc-cong e) = prc-cong (subA-≈ σ e)
sub-≈ σ (lam-cong e) = lam-cong (sub-≈ (liftˢ σ) e)
sub-≈ σ (app-cong e e') = app-cong (sub-≈ σ e) (sub-≈ σ e')
sub-≈ σ (lunit V M) = ≈-trans (lunit (sub σ V) (sub (liftˢ σ) M)) (≈-≡ (sym (sub-[] σ M V)))
sub-≈ σ (runit M) = ≈-trans (≈-≡ (cong (bnd (sub σ M) ∘ ret) (sub-last σ))) (runit (sub σ M))
sub-≈ σ (assoc M₁ M₂ M) = ≈-trans (assoc _ _ _) (≈-≡ (cong (bnd (sub σ M₁) ∘ bnd (sub (liftˢ σ) M₂)) (sym (sub-assoc-wk σ M))))
sub-≈ σ (beta M V) = ≈-trans (beta (sub (liftˢ σ) M) (sub σ V)) (≈-≡ (sym (sub-[] σ M V)))
subA-≈ σ [] = []
subA-≈ σ (e ∷ es) = sub-≈ σ e ∷ subA-≈ σ es

-- pointwise ≈ of substitutions is determined on the two blocks of Fin (m + 1)
Fin+1-ext≈ : {f g : Fin (m + 1) → Val n} → (∀ j → f (j ↑ˡ 1) ≈ g (j ↑ˡ 1)) → f last ≈ g last → ∀ i → f i ≈ g i
Fin+1-ext≈ {m} {f = f} {g} h₁ h₂ i with splitAt m i in eq
... | inj₁ j    = subst (λ i → f i ≈ g i) (splitAt⁻¹-↑ˡ eq) (h₁ j)
... | inj₂ zero = subst (λ i → f i ≈ g i) (splitAt⁻¹-↑ʳ eq) h₂

-- substitution is a congruence in the substitution as well
sub-cong≈  : {σ σ' : Subst m n} → (∀ i → σ i ≈ σ' i) → (E : Trm m s) → sub σ E ≈ sub σ' E
subA-cong≈ : {σ σ' : Subst m n} → (∀ i → σ i ≈ σ' i) → (Vs : Args m k) → subA σ Vs ≈ᵃ subA σ' Vs
liftˢ-cong≈ : {σ σ' : Subst m n} → (∀ i → σ i ≈ σ' i) → ∀ i → liftˢ σ i ≈ liftˢ σ' i
liftˢ-cong≈ {σ = σ} {σ'} e = Fin+1-ext≈ (λ j → ≈-trans (≈-≡ (liftˢ-inl σ j)) (≈-trans (ren-≈ (_↑ˡ 1) (e j)) (≈-≡ (sym (liftˢ-inl σ' j)))))
                                       (≈-trans (≈-≡ (liftˢ-last σ)) (≈-≡ (sym (liftˢ-last σ'))))
sub-cong≈ e (var i)      = e i
sub-cong≈ e (fun f Vs)   = fun-cong (subA-cong≈ e Vs)
sub-cong≈ e (lam M)      = lam-cong (sub-cong≈ (liftˢ-cong≈ e) M)
sub-cong≈ e (ret V)      = ret-cong (sub-cong≈ e V)
sub-cong≈ e (bnd M₂ M₁)  = bnd-cong (sub-cong≈ e M₂) (sub-cong≈ (liftˢ-cong≈ e) M₁)
sub-cong≈ e (prc p Vs)   = prc-cong (subA-cong≈ e Vs)
sub-cong≈ e (app V₁ V₂)  = app-cong (sub-cong≈ e V₁) (sub-cong≈ e V₂)
subA-cong≈ e []       = []
subA-cong≈ e (V ∷ Vs) = sub-cong≈ e V ∷ subA-cong≈ e Vs
