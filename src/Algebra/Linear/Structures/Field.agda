{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

module Algebra.Linear.Structures.Field
  {a ℓ} {A : Set a}
  (_≈_ : Rel A ℓ)
  where

open import Algebra.Linear.Core

open import Relation.Nullary using (¬_)

open import Algebra.Structures _≈_
open import Algebra.FunctionProperties _≈_

open import Level using (_⊔_)

record IsField (_+_ _*_ : Op₂ A) (0# 1# : A) (-_ : Op₁ A) (_⁻¹ : MultiplicativeInverse _≈_ 0#) : Set (a ⊔ ℓ) where
  field
    isRing     : IsRing _+_ _*_ -_ 0# 1#
    _⁻¹-involutive : ∀ (x : NonZero _≈_ 0#) → NonZero.value ((x ⁻¹) ⁻¹) ≈ NonZero.value x
    _⁻¹-inverse  : ∀ (x : NonZero _≈_ 0#) → ((NonZero.value x) * (NonZero.value (x ⁻¹))) ≈ 1#
    0#-not-1#    : ¬ (0# ≈ 1#)

  open IsRing isRing public
