{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Morphism
  {k ℓᵏ} (K : Field k ℓᵏ)
  where

open import Algebra.Linear.Morphism.Definitions K public
open import Algebra.Linear.Morphism.Structures  K public
open import Algebra.Linear.Morphism.Bundles     K public
open import Algebra.Linear.Morphism.VectorSpace K public
