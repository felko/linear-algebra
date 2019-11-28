{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Construct.Matrix.Square
  {k ℓ} (K : Field k ℓ)
  where

open import Level using (_⊔_)
open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Product

open import Algebra.Structures.Field.Utils K
open import Algebra.Linear.Construct.Matrix K public

module F = Field K

private
  M : ℕ -> Set k
  M n = Matrix n n

  K' : Set k
  K' = F.Carrier

UpperTriangular : ℕ -> Set (k ⊔ ℓ)
UpperTriangular n = ∃ λ (A : M n) -> ∀ {i j} -> j ≤ i -> (A ⟪ i , j ⟫) F.≈ F.0#

LowerTriangular : ℕ -> Set (k ⊔ ℓ)
LowerTriangular n = ∃ λ (A : M n) -> ∀ {i j} -> i ≤ j -> (A ⟪ i , j ⟫) F.≈ F.0#

Invertible : ℕ -> Set (k ⊔ ℓ)
Invertible n = ∃₂ λ (A B : M n) -> (A * B) ≈ I n ×  (B * A) ≈ I n

trace : ∀ {n} -> M n n -> K'
trace A = vsum (V.tabulate λ i → A ⟪ i , i ⟫)

det : ∀ {n} -> M n -> K'
det A = {!!}
