{-# OPTIONS --without-K --safe #-}

module Algebra.Structures.Bundles.Field where

open import Algebra
open import Level using (suc; _⊔_)
open import Relation.Binary using (Rel)

open import Algebra.Structures.Field

record Field c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _+_     : Carrier -> Carrier -> Carrier
    _*_     : Carrier -> Carrier -> Carrier
    0#      : Carrier
    1#      : Carrier
    -_      : Carrier -> Carrier
    _⁻¹      : MultiplicativeInverse _≈_ 0#
    isField : IsField _≈_ _+_ _*_ 0# 1# -_ _⁻¹

  open IsField isField public
