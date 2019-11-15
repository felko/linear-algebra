{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

module Algebra.Structures.Field
  {a ℓ} {A : Set a}
  (_≈_ : Rel A ℓ)
  where

open import Algebra.Linear.Core

open import Relation.Nullary using (¬_)

open import Algebra.Structures _≈_
open import Algebra.FunctionProperties _≈_

open import Level using (_⊔_)

record NonZero (0# : A) : Set (a ⊔ ℓ) where
  field
    value    : A
    non-zero : ¬ (value ≈ 0#)

MultiplicativeInverse : ∀ (0# : A) -> Set (a ⊔ ℓ)
MultiplicativeInverse 0# = NonZero 0# → NonZero 0#

record IsField (_+_ _*_ : Op₂ A) (0# 1# : A) (-_ : Op₁ A) (_⁻¹ : MultiplicativeInverse 0#) : Set (a ⊔ ℓ) where
  field
    isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0# 1#
    _⁻¹-involutive : ∀ (x : NonZero 0#) → NonZero.value ((x ⁻¹) ⁻¹) ≈ NonZero.value x
    _⁻¹-inverse  : ∀ (x : NonZero 0#) → ((NonZero.value x) * (NonZero.value (x ⁻¹))) ≈ 1#
    0#-not-1#    : ¬ (0# ≈ 1#)

  open IsCommutativeRing isCommutativeRing public

  open import Algebra.Properties.Ring (record { isRing = isRing }) public
