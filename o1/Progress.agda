open import Prelude
open import Term
open import Context Type
open import Value 
open import Typecheck

-- exts
--   : ∀ {n} {Γ Δ : Context n}
--   → (∀ {τ} → (t : Term n) → Δ ⊢ t ⦂ τ)
--   → (∀ {τ σ} → (t : Term (suc n)) → (Δ , σ) ⊢ t ⦂ τ)
-- exts ψ ty = {!   !}

-- subst
--   : ∀ {n} {Γ Δ : Context n}
--   → (∀ {τ} → (t : Term n) → Δ ⊢ t ⦂ τ)
--   → (∀ {τ t} → Γ ⊢ t ⦂ τ → Δ ⊢ t ⦂ τ)
-- subst ψ (⊢↑⦂ (⊢var x)) = ψ (↑⁺ var x)
-- subst ψ (⊢↑⦂ (f ⊢· x)) with subst ψ (⊢↑⦂ f) | subst ψ (⊢↓⦂ x)
-- ... | ⊢↑⦂ f' | ⊢↓⦂ x' = ⊢↑⦂ (f' ⊢· x')
-- subst ψ (⊢↑⦂ (⊢↓ x)) with subst ψ (⊢↓⦂ x) 
-- ... | ⊢↓⦂ x' = ⊢↑⦂ (⊢↓ x')
-- subst {n} {Γ} ψ (⊢↓⦂ (⊢ƛ f)) with subst (exts {n} {Γ} ψ) (⊢↓⦂ f)
-- ... | ⊢↓⦂ f' = ⊢↓⦂ (⊢ƛ f')
-- subst ψ (⊢↓⦂ (⊢↑ x σ≡τ)) with subst ψ (⊢↑⦂ x)
-- ... | ⊢↑⦂ x' = ⊢↓⦂ (⊢↑ x' σ≡τ)

exts
  : ∀ {n} {Γ Δ : Context n}
  → (∀ {τ t i} → lookup i Γ ∈ Γ → Δ ⊢ t ⦂ τ)
  → (∀ {τ σ t i} → lookup i (Γ , σ) ∈ Γ → (Δ , σ) ⊢ t ⦂ τ)
exts ψ {t = t} ty = {!   !}

subst
  : ∀ {n} {Γ Δ : Context n}
  → (∀ {τ t i} → lookup i Γ ∈ Γ → Δ ⊢ t ⦂ τ)
  → (∀ {τ t} → Γ ⊢ t ⦂ τ → Δ ⊢ t ⦂ τ)
subst {Γ = Γ} ψ (⊢↑⦂ (⊢var x)) = ψ {i = x} (index Γ x)
subst ψ (⊢↑⦂ (⊢↓ x)) with subst ψ (⊢↓⦂ x) 
... | ⊢↓⦂ x' = ⊢↑⦂ (⊢↓ x')
subst ψ (⊢↑⦂ (f ⊢· x)) with subst ψ (⊢↑⦂ f) | subst ψ (⊢↓⦂ x)
... | ⊢↑⦂ f' | ⊢↓⦂ x' = ⊢↑⦂ (f' ⊢· x')
-- subst {n} {Γ} ψ (⊢↓⦂ (⊢ƛ f)) with subst (exts {n} {Γ} ψ) (⊢↓⦂ f)
-- ... | ⊢↓⦂ f' = ⊢↓⦂ (⊢ƛ f')
-- subst {n} {Γ} ψ (⊢↓⦂ (⊢ƛ f)) with subst (exts {n} {Γ} ψ) (⊢↓⦂ f)
-- ... | ⊢↓⦂ f' = ⊢↓⦂ (⊢ƛ f')
-- subst {n} {Γ} ψ {τ} (⊢↓⦂ (⊢ƛ {t = t} f)) = {!   !}
subst {n} {Γ} {Δ} ψ (⊢↓⦂ (⊢ƛ {t = t} f)) with subst (exts {n} {Γ} {Δ} ψ {t = ↓⁻ t}) (⊢↓⦂ f)
... | ⊢↓⦂ f' = ⊢↓⦂ (⊢ƛ f')
subst ψ (⊢↓⦂ (⊢↑ x σ≡τ)) with subst ψ (⊢↑⦂ x)
... | ⊢↑⦂ x' = ⊢↓⦂ (⊢↑ x' σ≡τ)
-- subst ψ (⊢↑⦂ (x ⊢· x₁)) = {!   !}

infixl 4 _—→_

data _—→_ 
  : ∀ {n σ} {Γ : Context n} {t t'} 
  → Γ ⊢ t  ⦂ σ 
  → Γ ⊢ t' ⦂ σ 
  → Set 
  where 
  -- ξ-·₁ 
  --   : ∀ {n} {a a' : Term⁺ n} {b : Term⁻ n} 
  --   → ↑⁺ a —→ ↑⁺ a' 
  --   → ↑⁺ (a · b) —→ ↑⁺ (a' · b)

  -- ξ-·₂
  --   : ∀ {n} {a : Term⁺ n} {b b' : Term⁻ n} 
  --   → Value (↑⁺ a)
  --   → ↓⁻ b —→ ↓⁻ b' 
  --   → ↑⁺ (a · b) —→ ↑⁺ (a · b')

  -- β-ƛ : ∀ {x N V}
  --     → Value V
  --     → (ƛ x ⇒ N) $ V —→ N [ x := V ]

-- β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
--     → Value V
--       --------------------
--     → (ƛ N) · V —→ N [ V ]

  -- β-ƛ 
  --   : ∀ {n} {Γ : Context n} {σ τ} {t t'} {f : Γ , σ ⊢ t ↓ τ} {x : Γ ⊢ t' ↓ σ}
  --   -- → Value (↓⁻ x)
  --   → ↑⁺ ((ƛ f ↓ σ ⇒ τ) · x) —→ f [ x ]⁻ 
  --   → (↑⁺ ?) —→ ?


-- infix  2 _—↠_
-- infix  1 begin_
-- infixr 2 _—→⟨_⟩_
-- infix  3 _∎

-- data _—↠_ : ∀ {n} → Term n → Term n → Set where
--   _—→⟨_⟩_ 
--     : ∀ {n} (a : Term n) {b c : Term n}
--     → a —→ b
--     → b —↠ c
--     → a —↠ c

--   _∎ 
--     : ∀ {n} {a : Term n}
--     → a —↠ a

-- begin_ 
--   : ∀ {n} {a b : Term n}
--   → a —↠ b
--   → a —↠ b
-- begin_ = id

-- postulate
--   confluence 
--     : ∀ {n} {a b c : Term n}
--     → (a —↠ b) × (a —↠ c)
--     → ∃ λ d → (b —↠ d) × (c —↠ d)

--   diamond 
--     : ∀ {n} {a b c : Term n}
--     → (a —→ b) × (a —→ c)
--     → ∃ λ d → (b —↠ d) × (c —↠ d)

--   deterministic 
--     : ∀ {n} {a b c : Term n}
--     → a —→ b
--     → a —→ c
--     → b ≡ c
  