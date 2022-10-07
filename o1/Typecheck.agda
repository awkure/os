module Typecheck where 

open import Prelude 
open import Term hiding (module Properties)
open import Context Type

infix 4 _⊢_↑_
infix 4 _⊢_↓_

mutual 
  data _⊢_↑_ {n} : Context n → Term⁺ n → Type → Set where 
    ⊢var 
      : ∀ {Γ} 
      → (x : Fin n) 
      → Γ ⊢ var x ↑ lookup x Γ

    _⊢·_  
      : ∀ {Γ σ τ f x}
      → Γ ⊢ f ↑ σ ⇒ τ 
      → Γ ⊢ x ↓ σ 
      → Γ ⊢ f · x ↑ τ

    ⊢↓
      : ∀ {Γ σ t}
      → Γ ⊢ t ↓ σ
      → Γ ⊢ (t ↓ σ) ↑ σ

  data _⊢_↓_ {n} : Context n → Term⁻ n → Type → Set where 
    ⊢ƛ 
      : ∀ {Γ σ τ t}
      → Γ , σ ⊢ t ↓ τ
      → Γ ⊢ ƛ t ↓ σ ⇒ τ 

    ⊢μ 
      : ∀ {Γ τ t}
      → Γ , τ ⊢ t ↓ τ
      → Γ ⊢ μ t ↓ τ

    ⊢↑
      : ∀ {Γ σ τ t}
      → Γ ⊢ t ↑ σ
      → σ ≡ τ
      → Γ ⊢ (t ↑) ↓ τ

  data _⊢_⦂_ : ∀ {n} → Context n → Term n → Type → Set where 
    ⊢↑⦂ 
      : ∀ {n} {Γ : Context n} {σ t}
      → Γ ⊢ t ↑ σ
      → Γ ⊢ ↑⁺ t ⦂ σ

    ⊢↓⦂
      : ∀ {n} {Γ : Context n} {σ t}
      → Γ ⊢ t ↓ σ
      → Γ ⊢ ↓⁻ t ⦂ σ

module Properties where
  ι≠⇒ : ∀ {σ τ} → ι ≢ σ ⇒ τ
  ι≠⇒ ()

  ↑-uniq 
    : ∀ {n} {Γ : Context n} {t σ τ} 
    → Γ ⊢ t ↑ σ 
    → Γ ⊢ t ↑ τ
    → σ ≡ τ
  ↑-uniq (⊢var  _) (⊢var   _) = refl
  ↑-uniq (⊢f ⊢· _) (⊢f' ⊢· _) = ≡⇒cod (↑-uniq ⊢f ⊢f') where open Term.Properties
  ↑-uniq (⊢↓    _) (⊢↓     _) = refl

  ¬≢↑↓
    : ∀ {n} {Γ : Context n} {t σ τ}
    → Γ ⊢ t ↑ σ 
    → σ ≢ τ
    → ¬ Γ ⊢ (t ↑) ↓ τ
  ¬≢↑↓ ⊢t σ≢τ (⊢↑ ⊢t' σ'≡τ) rewrite ↑-uniq ⊢t ⊢t' = σ≢τ σ'≡τ


mutual 
  open Properties 
  open Term.Properties 
  
  infer 
    : ∀ {n} {Γ : Context n} 
    → (t : Term⁺ n)
    → Dec (∃ λ σ → (Γ ⊢ t ↑ σ))
  infer {Γ = Γ} (var x) = yes ⟨ lookup x Γ , ⊢var x ⟩

  infer (f · x) with infer f 
  ... | no ¬∃ = no λ{ ⟨ _ , ⊢f ⊢· _ ⟩ → ¬∃ ⟨ _ , ⊢f ⟩ }
  ... | yes ⟨ ι , ⊢f ⟩ = no λ{ ⟨ _ , ⊢f' ⊢· _ ⟩ → ι≠⇒ (↑-uniq ⊢f ⊢f') }
  ... | yes ⟨ σ ⇒ τ , f ⟩ with check x σ
  ...   | yes x = yes ⟨ τ , f ⊢· x ⟩
  ...   | no ¬∃ = no (¬arg f ¬∃)
    where 
      ¬arg 
        : ∀ {n} {Γ : Context n} {f x σ τ}
        →   Γ ⊢ f ↑ σ ⇒ τ
        → ¬ Γ ⊢ x ↓ σ
        → ¬ (∃ λ τ' → Γ ⊢ f · x ↑ τ')
      ¬arg ⊢f ¬⊢x ⟨ τ' , ⊢f' ⊢· ⊢x' ⟩ rewrite ≡⇒dom (↑-uniq ⊢f ⊢f') = ¬⊢x ⊢x'

  infer (x ↓ σ) with check x σ
  ... | no ¬t = no λ{ ⟨ _ , ⊢↓ ⊢t ⟩ → ¬t ⊢t }
  ... | yes x = yes ⟨ σ , ⊢↓ x ⟩

  check 
    : ∀ {n} {Γ : Context n} 
    → (t : Term⁻ n)
    → (σ : Type)
    → Dec (Γ ⊢ t ↓ σ)
  check (ƛ t) ι = no (λ ())
  check {Γ = Γ} (ƛ t) (σ ⇒ τ) with check {_} {Γ , σ} t τ
  ... | no ¬⊢t = no λ{ (⊢ƛ ⊢t) → ¬⊢t ⊢t } 
  ... | yes ⊢t = yes (⊢ƛ ⊢t)
  check {Γ = Γ} (μ t) σ with check {_} {Γ , σ} t σ
  ... | no ¬⊢t = no λ{ (⊢μ ⊢t) → ¬⊢t ⊢t }
  ... | yes ⊢t = yes (⊢μ ⊢t)
  check (x ↑) τ with infer x 
  ... | no ¬∃ = no λ{ (⊢↑ ⊢x _) → ¬∃ ⟨ _ , ⊢x ⟩ }
  ... | yes ⟨ σ , ⊢t ⟩ with σ ≟ τ
  ...   | no ¬σ≡τ = no (¬≢↑↓ ⊢t ¬σ≡τ)
  ...   | yes σ≡τ = yes (⊢↑ ⊢t σ≡τ)

  