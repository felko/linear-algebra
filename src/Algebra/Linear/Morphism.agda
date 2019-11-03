open import Relation.Binary using (Rel; IsEquivalence)
open import Algebra.Linear.Structures.Field

open import Algebra.FunctionProperties as FP

open import Level

module Algebra.Linear.Morphism
  {k ℓᵏ : Level} {K : Set k}
  {_≈ᵏ_ : Rel K ℓᵏ} {≈ᵏ-isEquiv : IsEquivalence _≈ᵏ_}
  {_+ᵏ_ _*ᵏ_ : Op₂ K} {0ᵏ 1ᵏ : K} { -ᵏ_ : Op₁ K } {_⁻¹ : MultiplicativeInverse ≈ᵏ-isEquiv 0ᵏ}
  (isField : IsField ≈ᵏ-isEquiv _+ᵏ_ _*ᵏ_ 0ᵏ 1ᵏ -ᵏ_ _⁻¹)
  where

open import Algebra.Linear.Morphism.VectorSpace isField public
