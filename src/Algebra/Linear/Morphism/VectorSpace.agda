{-# OPTIONS --without-K --safe #-}

open import Algebra.Linear.Structures.Bundles.Field

module Algebra.Linear.Morphism.VectorSpace
  {k ℓᵏ} (K : Field k ℓᵏ)
  where

open import Level
open import Algebra.FunctionProperties as FP
import Algebra.Linear.Morphism.Definitions as LinearMorphismDefinitions
import Algebra.Morphism as Morphism
open import Relation.Binary using (Rel)
open import Relation.Binary.Morphism.Structures
open import Algebra.Morphism

open import Algebra.Linear.Core
open import Algebra.Linear.Structures.VectorSpace K
open import Algebra.Linear.Structures.Bundles

module LinearDefinitions {a b ℓ₂} (A : Set a) (B : Set b) (_≈_ : Rel B ℓ₂) where
  open Morphism.Definitions A B _≈_ public
  open LinearMorphismDefinitions K A B _≈_ public

module _
  {a ℓ₁} (From : VectorSpace K a ℓ₁)
  {b ℓ₂} (To   : VectorSpace K b ℓ₂)
  where

  private
    module F = VectorSpace From
    module T = VectorSpace To

    K' : Set k
    K' = Field.Carrier K

  open F using () renaming (Carrier to A; _≈_ to ≈₁; _+_ to +₁; _∙_ to ∙₁)
  open T using () renaming (Carrier to B; _≈_ to ≈₂; _+_ to +₂; _∙_ to ∙₂)
  open import Function ≈₁ ≈₂

  open LinearDefinitions (VectorSpace.Carrier From) (VectorSpace.Carrier To) ≈₂

  record IsLinearMap (⟦_⟧ : Morphism) : Set (k ⊔ a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isAbelianGroupMorphism : IsAbelianGroupMorphism F.abelianGroup T.abelianGroup ⟦_⟧
      ∙-homo : ScalarHomomorphism ⟦_⟧ ∙₁ ∙₂

    open IsAbelianGroupMorphism isAbelianGroupMorphism public
      renaming (∙-homo to +-homo; ε-homo to 0#-homo)

  record IsLinearMonomorphism (⟦_⟧ : Morphism) : Set (k ⊔ a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLinearMap : IsLinearMap ⟦_⟧
      injective   : Injective ⟦_⟧

    open IsLinearMap isLinearMap public

  record IsLinearIsomorphism (⟦_⟧ : Morphism) : Set (k ⊔ a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLinearMonomorphism : IsLinearMonomorphism ⟦_⟧
      surjective           : Surjective ⟦_⟧

    open IsLinearMonomorphism isLinearMonomorphism public

module _
  {a ℓ} (V : VectorSpace K a ℓ)
  where

  open VectorSpace V

  open LinearDefinitions Carrier Carrier _≈_

  IsLinearEndomorphism : Morphism -> Set (k ⊔ a ⊔ ℓ)
  IsLinearEndomorphism ⟦_⟧ = IsLinearMap V V ⟦_⟧

  IsLinearAutomorphism : Morphism -> Set (k ⊔ a ⊔ ℓ)
  IsLinearAutomorphism ⟦_⟧ = IsLinearIsomorphism V V ⟦_⟧
