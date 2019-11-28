{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Structures.Field.Utils
  {k ℓ} (K : Field k ℓ)
  where

open Field K hiding (zero)

open import Data.Fin
import Data.Nat as Nat

private
  K' : Set k
  K' = Carrier

δ : ∀ {n p} -> Fin n -> Fin p -> K'
δ zero zero = 1#
δ (suc i) zero = 0#
δ zero (suc j) = 0#
δ (suc i) (suc j) = δ i j

δ-comm : ∀ {n p} (i : Fin n) (j : Fin p) -> δ i j ≈ δ j i
δ-comm zero zero = refl
δ-comm (suc i) zero = refl
δ-comm zero (suc j) = refl
δ-comm (suc i) (suc j) = δ-comm i j

δ-cancelˡ : ∀ {n p} (j : Fin p) -> δ {Nat.suc n} zero (suc j) ≈ 0#
δ-cancelˡ zero = refl
δ-cancelˡ (suc j) = refl

δ-cancelʳ : ∀ {n p} (i : Fin n) -> δ {p = Nat.suc p} (suc i) zero ≈ 0#
δ-cancelʳ {n} {p} i = trans (δ-comm (suc i) (zero {Nat.suc p})) (δ-cancelˡ {p} {n} i)
