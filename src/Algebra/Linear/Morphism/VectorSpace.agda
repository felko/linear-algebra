{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Morphism.VectorSpace
  {k ℓᵏ} (K : Field k ℓᵏ)
  where

open import Level
open import Algebra.FunctionProperties as FP
import Algebra.Linear.Morphism.Definitions as LinearMorphismDefinitions
import Algebra.Morphism as Morphism
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.Morphism.Structures
open import Algebra.Morphism

open import Algebra.Linear.Core
open import Algebra.Linear.Structures.VectorSpace K
open import Algebra.Linear.Structures.Bundles

module LinearDefinitions {a₁ a₂ ℓ₂} (A : Set a₁) (B : Set a₂) (_≈_ : Rel B ℓ₂) where
  open Morphism.Definitions A B _≈_ public
  open LinearMorphismDefinitions K A B _≈_ public

module _
  {a₁ ℓ₁} (From : VectorSpace K a₁ ℓ₁)
  {a₂ ℓ₂} (To   : VectorSpace K a₂ ℓ₂)
  where

  private
    module F = VectorSpace From
    module T = VectorSpace To

    K' : Set k
    K' = Field.Carrier K

  open F using () renaming (Carrier to A; _≈_ to _≈₁_; _+_ to _+₁_; _∙_ to _∙₁_)
  open T using () renaming (Carrier to B; _≈_ to _≈₂_; _+_ to _+₂_; _∙_ to _∙₂_)

  open import Function

  open LinearDefinitions (VectorSpace.Carrier From) (VectorSpace.Carrier To) _≈₂_

  record IsLinearMap (⟦_⟧ : Morphism) : Set (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isAbelianGroupMorphism : IsAbelianGroupMorphism F.abelianGroup T.abelianGroup ⟦_⟧
      ∙-homo : ScalarHomomorphism ⟦_⟧ _∙₁_ _∙₂_

    open IsAbelianGroupMorphism isAbelianGroupMorphism public
      renaming (∙-homo to +-homo; ε-homo to 0#-homo)

    distrib-linear : ∀ (a b : K') (u v : A) -> ⟦ a ∙₁ u +₁ b ∙₁ v ⟧ ≈₂ a ∙₂ ⟦ u ⟧ +₂ b ∙₂ ⟦ v ⟧
    distrib-linear a b u v = T.trans (+-homo (a ∙₁ u) (b ∙₁ v)) (T.+-cong (∙-homo a u) (∙-homo b v))

  record IsLinearMonomorphism (⟦_⟧ : Morphism) : Set (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLinearMap : IsLinearMap ⟦_⟧
      injective   : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsLinearMap isLinearMap public

  record IsLinearIsomorphism (⟦_⟧ : Morphism) : Set (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLinearMonomorphism : IsLinearMonomorphism ⟦_⟧
      surjective           : Surjective _≈₁_ _≈₂_ ⟦_⟧

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
