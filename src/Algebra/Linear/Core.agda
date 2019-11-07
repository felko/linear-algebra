module Algebra.Linear.Core where

open import Relation.Binary
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)

VectorAddition : ∀ {c} -> Set c -> Set c
VectorAddition V = V -> V -> V

ScalarMultiplication : ∀ {c k} -> Set k -> Set c -> Set (k ⊔ c)
ScalarMultiplication K V = K -> V -> V

record NonZero {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (0# : A) : Set (a ⊔ ℓ) where
  field
    value    : A
    non-zero : ¬ (value ≈ 0#)

MultiplicativeInverse : ∀ {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (0# : A) -> Set (a ⊔ ℓ)
MultiplicativeInverse ≈ 0# = NonZero ≈ 0# → NonZero ≈ 0#
