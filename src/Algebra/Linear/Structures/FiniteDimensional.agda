{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Structures.FiniteDimensional
  {k ℓᵏ} (K : Field k ℓᵏ)
  where

open import Algebra.Linear.Core
open import Algebra.FunctionProperties
open import Relation.Binary using (Rel)

open import Algebra.Linear.Morphism.Bundles K

open import Algebra.Linear.Structures.VectorSpace K

open import Function.Equality

open import Level using (_⊔_; suc)
open import Data.Nat using (ℕ)
import Algebra.Linear.Construct.Vector K as Vec

private
  K' : Set k
  K' = Field.Carrier K

record IsFiniteDimensional
       {v ℓ} {V : Set v}
       (_≈_ : Rel V ℓ)
       (_+_ : Op₂ V) (_∙_ : K' → V → V) (-_ : Op₁ V) (0# : V)
       (n : ℕ) : Set (suc (v ⊔ k ⊔ ℓ ⊔ ℓᵏ))
    where
  field
    isVectorSpace : IsVectorSpace _≈_ _+_ _∙_ -_ 0#
    embed         : LinearIsomorphism (record { isVectorSpace = isVectorSpace })
                                      (record { isVectorSpace = Vec.isVectorSpace {n} })

  open IsVectorSpace isVectorSpace public

module Vector {n} where
  open Vec

  isFiniteDimensional : IsFiniteDimensional (Vec._≈_) (Vec._+_) (Vec._∙_) (Vec.-_) (Vec.0#) n
  isFiniteDimensional = record
    { isVectorSpace = Vec.isVectorSpace
    ; embed         = Vec.embed
    }
