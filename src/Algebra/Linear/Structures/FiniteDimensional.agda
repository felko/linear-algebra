open import Relation.Binary using (Rel; IsEquivalence)
open import Algebra.Linear.Structures.Field

open import Algebra.FunctionProperties

module Algebra.Linear.Structures.FiniteDimensional
  {k ℓᵏ} {K : Set k}
  {_≈ᵏ_ : Rel K ℓᵏ} {≈ᵏ-isEquiv : IsEquivalence _≈ᵏ_}
  {_+ᵏ_ _*ᵏ_ : Op₂ K} {0ᵏ 1ᵏ : K} { -ᵏ_ : Op₁ K } {_⁻¹ : MultiplicativeInverse ≈ᵏ-isEquiv 0ᵏ}
  (isField : IsField ≈ᵏ-isEquiv _+ᵏ_ _*ᵏ_ 0ᵏ 1ᵏ -ᵏ_ _⁻¹)
  where

open import Algebra.Linear.Morphism.VectorSpace isField
open import Algebra.Linear.Structures.VectorSpace isField

open import Level using (_⊔_)
open import Data.Nat hiding (_⊔_)
import Algebra.Linear.Construct.Vector ≈ᵏ-isEquiv isField as Vec

record IsFiniteDimensional
       {v ℓ} {V : Set v}
       {_≈_ : Rel V ℓ} (isEquiv : IsEquivalence _≈_)
       (_+_ : Op₂ V) (_∙_ : K → V → V) (-_ : Op₁ V) (0# : V)
       (n : ℕ) : Set (v ⊔ k ⊔ ℓ ⊔ ℓᵏ)
       where
  field
    isVectorSpace       : IsVectorSpace isEquiv _+_ _∙_ -_ 0#
    to                  : V -> Vec.Vector n
    from                : Vec.Vector n -> V
    embed-isIsomorphism : IsLinearIsomorphism isVectorSpace (Vec.isVectorSpace {n}) to from

  open IsVectorSpace isEquiv isVectorSpace public

module Vector {n} where
  open Vec public

  isFiniteDimensional : IsFiniteDimensional Vec.≈-isEquiv Vec._+_ Vec._∙_ Vec.-_ 0# n
  isFiniteDimensional = record
    { isVectorSpace       = isVectorSpace
    ; to                  = embed
    ; from                = embed
    ; embed-isIsomorphism = embed-isIsomorphism
    }
