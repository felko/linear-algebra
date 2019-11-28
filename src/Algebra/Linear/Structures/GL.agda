{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Structures.GL
  {k ℓᵏ} (K : Field k ℓᵏ)
  {a ℓ}
  where

open import Relation.Binary using (Setoid)
open import Algebra.Linear.Structures.Bundles
open import Algebra.Linear.Morphism.Bundles K
open import Categories.Category

open LinearMap
