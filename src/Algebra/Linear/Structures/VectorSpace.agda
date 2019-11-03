open import Relation.Binary using (Rel; IsEquivalence)
open import Algebra.Linear.Structures.Field

open import Algebra.FunctionProperties

module Algebra.Linear.Structures.VectorSpace
  {k ℓᵏ} {K : Set k}
  {_≈ᵏ_ : Rel K ℓᵏ} {≈ᵏ-isEquiv : IsEquivalence _≈ᵏ_}
  {_+ᵏ_ _*ᵏ_ : Op₂ K} {0ᵏ 1ᵏ : K} { -ᵏ_ : Op₁ K } {_⁻¹ : MultiplicativeInverse ≈ᵏ-isEquiv 0ᵏ}
  (isField : IsField ≈ᵏ-isEquiv _+ᵏ_ _*ᵏ_ 0ᵏ 1ᵏ -ᵏ_ _⁻¹)
  {v ℓ} {V : Set v}
  {_≈_ : Rel V ℓ}
  (isEquiv : IsEquivalence _≈_)
  where

open import Algebra.Structures _≈_
open import Level using (_⊔_)
open import Data.Nat using (ℕ)

record IsVectorSpace (_+_ : Op₂ V) (_∙_ : K → V → V) (-_ : Op₁ V) (0# : V) : Set (v ⊔ k ⊔ ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup _+_ 0# -_
    *ᵏ-∙-compat      : ∀ (a b : K) (u : V) -> ((a *ᵏ b) ∙ u) ≈ (a ∙ (b ∙ u))
    ∙-+-distrib      : ∀ (a : K) (u v : V) -> (a ∙ (u + v)) ≈ ((a ∙ u) + (a ∙ v))
    ∙-+ᵏ-distrib     : ∀ (a b : K) (u : V) -> ((a +ᵏ b) ∙ u) ≈ ((a ∙ u) + (b ∙ u))
    ∙-cong           : ∀ (a : K) (u v : V) -> u ≈ v -> (a ∙ u) ≈ (a ∙ v)
    ∙-identity       : ∀ (x : V) → (1ᵏ ∙ x) ≈ x
    ∙-absorb         : ∀ (x : V) → (0ᵏ ∙ x) ≈ 0#

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc     to +-assoc
    ; ∙-cong    to +-cong
    ; identity  to +-identity
    ; identityˡ  to +-identityˡ
    ; identityʳ  to +-identityʳ
    ; comm      to +-comm
    ; inverse   to -‿inverse
    ; inverseˡ   to -‿inverseˡ
    ; inverseʳ   to -‿inverseʳ
    ; ⁻¹-cong    to -‿cong
    )
