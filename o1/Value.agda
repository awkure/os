open import Prelude 
open import Term

data Value : ∀ {n} → Term n → Set where 
  varᵛ 
    : ∀ {n} {v : Fin n} 
    → Value (↑⁺ var v) 

  ƛᵛ 
    : ∀ {n} {t : Term⁻ (suc n)} 
    → Value (↓⁻ ƛ t)

