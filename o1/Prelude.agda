open import Function                   using (_$_; _∘_; flip; id) public
open import Data.Empty                 using (⊥; ⊥-elim) public
open import Data.Unit.Base             using (⊤; tt) public
open import Data.Fin                   using (Fin; toℕ; fromℕ) renaming (zero to fzero; suc to fsuc) public
open import Data.Nat                   using (ℕ; zero; suc; _+_) public
open import Data.Product               using (Σ; ∃; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; _≢_; sym) public
open import Relation.Nullary           using (¬_; Dec; yes; no) public 
open import Relation.Nullary.Decidable using (False; toWitnessFalse) public
