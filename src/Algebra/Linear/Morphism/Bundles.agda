{-# OPTIONS --without-K --safe #-}

open import Algebra.Linear.Structures.Bundles.Field

module Algebra.Linear.Morphism.Bundles
  {k ℓᵏ} (K : Field k ℓᵏ)
  where

open import Algebra.FunctionProperties as FP
open import Relation.Binary using (Rel; IsEquivalence)
open import Level

import Algebra.Linear.Structures.Bundles as VS

open import Algebra.Linear.Morphism.VectorSpace K

module VectorSpace
  {a₁ ℓ₁} (From : VS.VectorSpace K a₁ ℓ₁)
  {a₂ ℓ₂} (To   : VS.VectorSpace K a₂ ℓ₂)
  where

  private
    module F = VS.VectorSpace From
    module T = VS.VectorSpace To

    K' : Set k
    K' = Field.Carrier K

    open F using () renaming (Carrier to A; _+_ to +₁; _∙_ to ∙₁)
    open T using () renaming (Carrier to B; _≈_ to ≈₂; _+_ to +₂; _∙_ to ∙₂)

  open LinearDefinitions (VS.VectorSpace.Carrier From) (VS.VectorSpace.Carrier To) ≈₂

  record LinearMap : Set (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      ⟦_⟧         : Morphism
      isLinearMap : IsLinearMap From To ⟦_⟧

    open IsLinearMap isLinearMap public

  record LinearIsomorphism : Set (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      ⟦_⟧                 : Morphism
      isLinearIsomorphism : IsLinearIsomorphism From To ⟦_⟧

    open IsLinearIsomorphism isLinearIsomorphism public

open VectorSpace
