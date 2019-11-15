{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Morphism.Bundles
  {k ℓᵏ} (K : Field k ℓᵏ)
  where

open import Algebra.FunctionProperties as FP
open import Relation.Binary using (Rel; Setoid)
open import Level

import Algebra.Linear.Structures.Bundles as VS

open import Algebra.Linear.Morphism.VectorSpace K

open import Function.Equality as FunEq using (_⟶_; _⟨$⟩_; setoid)

module _
  {a₁ ℓ₁} (From : VS.VectorSpace K a₁ ℓ₁)
  {a₂ ℓ₂} (To   : VS.VectorSpace K a₂ ℓ₂)
  where

  private
    module F = VS.VectorSpace From
    module T = VS.VectorSpace To

    K' : Set k
    K' = Field.Carrier K

    open F using ()
      renaming
        ( Carrier to A
        ; _≈_     to _≈₁_
        ; refl    to ≈₁-refl
        ; sym     to ≈₁-sym
        ; setoid  to A-setoid
        ; _+_     to +₁
        ; _∙_     to ∙₁
        )

    open T using ()
      renaming
        ( Carrier to B
        ; _≈_     to _≈₂_
        ; refl    to ≈₂-refl
        ; sym     to ≈₂-sym
        ; trans   to ≈₂-trans
        ; setoid  to B-setoid
        ; _+_     to +₂
        ; _∙_     to ∙₂
        )

    hom-setoid : ∀ {Carrier} -> (Carrier -> (A-setoid ⟶ B-setoid))
                     -> Setoid (suc (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂)) (a₁ ⊔ ℓ₁ ⊔ ℓ₂)
    hom-setoid {Carrier} app = record
      { Carrier       = Carrier
      ; _≈_           = λ f g → ∀ {x y} (r : x ≈₁ y) -> (app f ⟨$⟩ x) ≈₂ (app g ⟨$⟩ y)
      ; isEquivalence = record
        { refl  = λ {f} -> FunEq.cong (app f)
        ; sym   = λ r rₓ → ≈₂-sym (r (≈₁-sym rₓ))
        ; trans = λ r₁ r₂ rₓ → ≈₂-trans (r₁ ≈₁-refl) (r₂ rₓ)
        }
      }

  open LinearDefinitions A B _≈₂_

  record LinearMap : Set (suc (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      ⟦_⟧         : Morphism
      isLinearMap : IsLinearMap From To ⟦_⟧

    infixl 25 _⟪$⟫_
    _⟪$⟫_ : A -> B
    _⟪$⟫_ = ⟦_⟧

    open IsLinearMap isLinearMap public

  linearMap-setoid : Setoid (suc (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂)) (a₁ ⊔ ℓ₁ ⊔ ℓ₂)
  linearMap-setoid = hom-setoid {LinearMap} λ f → record
    { _⟨$⟩_ = λ x → f LinearMap.⟪$⟫ x
    ; cong = LinearMap.⟦⟧-cong f
    }

  record LinearIsomorphism : Set (suc (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      ⟦_⟧                 : Morphism
      isLinearIsomorphism : IsLinearIsomorphism From To ⟦_⟧

    open IsLinearIsomorphism isLinearIsomorphism public

    linearMap : LinearMap
    linearMap = record { ⟦_⟧ = ⟦_⟧ ; isLinearMap = isLinearMap }

    open LinearMap linearMap public
      using (_⟪$⟫_)

  linearIsomorphism-setoid : Setoid (suc (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂)) (a₁ ⊔ ℓ₁ ⊔ ℓ₂)
  linearIsomorphism-setoid = hom-setoid {LinearIsomorphism} λ f → record
    { _⟨$⟩_ = λ x -> f LinearIsomorphism.⟪$⟫ x
    ; cong = LinearIsomorphism.⟦⟧-cong f
    }

module _ {a ℓ} (V : VS.VectorSpace K a ℓ) where
  LinearEndomorphism : Set (suc (k ⊔ a ⊔ ℓ))
  LinearEndomorphism = LinearMap V V

  LinearAutomorphism : Set (suc (k ⊔ a ⊔ ℓ))
  LinearAutomorphism = LinearIsomorphism V V
