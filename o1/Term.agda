module Term where 

open import Prelude 

infix 8 ƛ_
infix 7 _↑
infix 7 _↓_
infix 6 ↑⁺_
infix 6 ↓⁻_

data Type : Set where
  ι   : Type
  _⇒_ : Type → Type → Type

open import Context Type

mutual 
  data Term⁺ n : Set where
    var  : Fin   n        → Term⁺ n
    _·_  : Term⁺ n        → Term⁻ n → Term⁺ n
    _↓_  : Term⁻ n → Type → Term⁺ n

  data Term⁻ n : Set where 
    ƛ_ : Term⁻ (suc n) → Term⁻ n
    μ_ : Term⁻ (suc n) → Term⁻ n
    _↑ : Term⁺ n → Term⁻ n

  data Term n : Set where 
    ↑⁺_ : Term⁺ n → Term n
    ↓⁻_ : Term⁻ n → Term n

#_ : (n : ℕ) → Term⁺ (suc n)
#_ = var ∘ fromℕ

module Properties where 
  ≡⇒dom : ∀ {σ σ' τ τ'} → (τ ⇒ σ) ≡ (τ' ⇒ σ') → τ ≡ τ'
  ≡⇒dom refl = refl

  ≡⇒cod : ∀ {σ σ' τ τ'} → (τ ⇒ σ) ≡ (τ' ⇒ σ') → σ ≡ σ'
  ≡⇒cod refl = refl

  _≟_ : (σ τ : Type) → Dec (σ ≡ τ)
  ι ≟ ι = yes refl
  ι ≟ (_ ⇒ _) = no (λ ())
  (_ ⇒ _) ≟ ι = no (λ ())
  (τ ⇒ σ) ≟ (τ' ⇒ σ') with τ ≟ τ' | σ ≟ σ'
  ... | yes refl | yes refl = yes refl
  ... | no τ≠τ'  | _        = no (τ≠τ' ∘ ≡⇒dom)
  ... | _        | no σ≠σ'  = no (σ≠σ' ∘ ≡⇒cod)  
