{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Morphism.Definitions
  {k ℓᵏ} (K : Field k ℓᵏ)
  {a} (A : Set a)
  {b} (B : Set b)
  {ℓ} (_≈_ : Rel B ℓ)
  where

open import Algebra.Linear.Core
open import Function

import Algebra.Morphism as Morphism
open Morphism.Definitions A B _≈_

private
  K' : Set k
  K' = Field.Carrier K

Linear : Morphism
       -> VectorAddition A -> ScalarMultiplication K' A
       -> VectorAddition B -> ScalarMultiplication K' B
       -> Set _
Linear ⟦_⟧ _+₁_ _∙₁_ _+₂_ _∙₂_ =
  ∀ (a b : K') (u v : A) ->
    ⟦ (a ∙₁ u) +₁ (b ∙₁ v) ⟧ ≈ ((a ∙₂ ⟦ u ⟧) +₂ (b ∙₂ ⟦ v ⟧))

ScalarHomomorphism : Morphism
                   -> ScalarMultiplication K' A
                   -> ScalarMultiplication K' B
                   -> Set _
ScalarHomomorphism ⟦_⟧ _∙_ _∘_ = ∀ (c : K') (u : A) -> ⟦ c ∙ u ⟧ ≈ (c ∘ ⟦ u ⟧)
