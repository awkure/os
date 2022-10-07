open import Prelude

module Context A where 
  infixl 5 _,_

  data Context : ℕ → Set where
    ∅   : Context 0
    _,_ : ∀ {n} → Context n → A → Context (suc n)

  data _∈_ : ∀ {n} → A → Context n → Set where 
    Z : ∀ {n} {Γ : Context n} {σ} → σ ∈ (Γ , σ)
    S : ∀ {n} {Γ : Context n} {σ τ} → σ ∈ Γ → σ ∈ (Γ , τ)

  lookup : ∀ {n} → Fin n → Context n → A
  lookup fzero (_ , v) = v
  lookup (fsuc i) (Γ , _) = lookup i Γ

  index 
    : ∀ {n} 
    → (Γ : Context n)
    → (i : Fin n) 
    → lookup i Γ ∈ Γ
  index (_ , σ) fzero = Z
  index (Γ , _) (fsuc i) = S (index Γ i)
