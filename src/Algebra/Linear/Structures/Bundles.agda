{-# OPTIONS --without-K --safe #-}

module Algebra.Linear.Structures.Bundles where

open import Algebra
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Rel; IsEquivalence)

open import Algebra.FunctionProperties
open import Algebra.Linear.Structures.Field
open import Algebra.Linear.Structures.Bundles.Field
open import Algebra.Linear.Structures.VectorSpace

record RawVectorSpace {k ℓᵏ} (K : Field k ℓᵏ) (c ℓ : Level) : Set (suc (c ⊔ k ⊔ ℓ)) where
  infix  20 _≈_
  infixl 25 _+_
  infixr 30 _∙_

  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _+_           : Carrier -> Carrier -> Carrier
    _∙_           : Field.Carrier K -> Carrier -> Carrier
    -_            : Carrier -> Carrier
    0#            : Carrier

  rawGroup : RawGroup c ℓ
  rawGroup = record { _≈_ = _≈_; _∙_ = _+_; ε = 0#; _⁻¹ = -_ }

  open RawGroup rawGroup public
    using (rawMagma; rawMonoid)

record VectorSpace {k ℓᵏ} (K : Field k ℓᵏ) (c ℓ : Level) : Set (suc (c ⊔ k ⊔ ℓ)) where
  infix  20 _≈_
  infixl 25 _+_
  infixr 30 _∙_

  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _+_           : Carrier -> Carrier -> Carrier
    _∙_           : Field.Carrier K -> Carrier -> Carrier
    -_            : Carrier -> Carrier
    0#            : Carrier
    isVectorSpace : IsVectorSpace K _≈_ _+_ _∙_ -_ 0#

  open IsVectorSpace isVectorSpace public

  rawVectorSpace : RawVectorSpace K c ℓ
  rawVectorSpace = record
    { _≈_ = _≈_; _+_ = _+_; _∙_ = _∙_; -_ = -_; 0# = 0# }

  abelianGroup : AbelianGroup c ℓ
  abelianGroup = record { isAbelianGroup = isAbelianGroup }

  open AbelianGroup abelianGroup public
    using (rawMagma; magma; rawMonoid; monoid; rawGroup; group)
