{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Structures.Field.Utils
  {k ℓ} (K : Field k ℓ)
  where

open import Data.Fin

private
  module F = Field K

  K' : Set k
  K' = F.Carrier

δ : ∀ {n p} -> Fin n -> Fin p -> K'
δ zero zero = F.1#
δ (suc n) zero = F.0#
δ zero (suc p) = F.0#
δ (suc n) (suc p) = δ n p
