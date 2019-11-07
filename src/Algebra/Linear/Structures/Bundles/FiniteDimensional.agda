open import Relation.Binary using (Rel; IsEquivalence)
open import Algebra.Linear.Structures.Field

open import Algebra.FunctionProperties

module Algebra.Linear.Structures.Bundles.FiniteDimensional where

open import Algebra
open import Level using (Level; suc; _⊔_)

open import Algebra.Linear.Structures.Bundles.Field
open import Algebra.Linear.Structures.Bundles

open import Algebra.Linear.Structures.VectorSpace
open import Algebra.Linear.Structures.FiniteDimensional

open import Data.Nat using (ℕ)

record FiniteDimensional {k ℓᵏ} (K : Field k ℓᵏ) (c ℓ : Level) (n : ℕ) : Set (suc (c ⊔ k ⊔ ℓ ⊔ ℓᵏ)) where
  field
    Carrier             : Set c
    _≈_                 : Rel Carrier ℓ
    _+_                 : Carrier -> Carrier -> Carrier
    _∙_                 : Field.Carrier K -> Carrier -> Carrier
    -_                  : Carrier -> Carrier
    0#                  : Carrier
    isFiniteDimensional : IsFiniteDimensional K _≈_ _+_ _∙_ -_ 0# n

  open IsFiniteDimensional isFiniteDimensional public

  vectorSpace : VectorSpace K c ℓ
  vectorSpace = record { isVectorSpace = isVectorSpace }
