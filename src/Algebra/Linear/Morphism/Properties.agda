{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Morphism.Properties
  {k ℓᵏ} (K : Field k ℓᵏ)
  where

open import Level
open import Algebra.FunctionProperties as FP
import Algebra.Linear.Morphism.Definitions as LinearMorphismDefinitions
import Algebra.Morphism as Morphism
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.Morphism.Structures
open import Algebra.Morphism
open import Algebra.Linear.Structures.VectorSpace K
open import Algebra.Linear.Structures.Bundles

module _
  {a₁ ℓ₁} (From : VectorSpace K a₁ ℓ₁)
  {a₂ ℓ₂} (To   : VectorSpace K a₂ ℓ₂)
  where

  open import Algebra.Linear.Morphism.VectorSpace K

  private
    module F = VectorSpace From
    module T = VectorSpace To

    open VectorSpaceField

  open F
    using ()
    renaming
      ( Carrier     to A
      ; _≈_         to _≈₁_
      ; refl        to ≈₁-refl
      ; sym         to ≈₁-sym
      ; trans       to ≈₁-trans
      ; setoid      to setoid₁
      ; _+_         to _+₁_
      ; +-cong      to +₁-cong
      ; +-identityˡ  to +₁-identityˡ
      ; _∙_         to _∙₁_
      ; ∙-identity  to ∙₁-identity
      ; ∙-absorbˡ    to ∙₁-absorbˡ
      ; ∙-absorbʳ    to ∙₁-absorbʳ
      ; 0#          to 0₁
      )

  open T
    using ()
    renaming
      ( Carrier    to B
      ; _≈_        to _≈₂_
      ; refl       to ≈₂-refl
      ; sym        to ≈₂-sym
      ; trans      to ≈₂-trans
      ; setoid     to setoid₂
      ; _+_        to _+₂_
      ; +-cong     to +₂-cong
      ; +-identityˡ to +₂-identityˡ
      ; _∙_        to _∙₂_
      ; ∙-identity to ∙₂-identity
      ; ∙-absorbˡ   to ∙₂-absorbˡ
      ; ∙-absorbʳ   to ∙₂-absorbʳ
      ; 0#         to 0₂
      )

  open import Function _≈₁_ _≈₂_
  open import Function.Equality

  open LinearDefinitions (VectorSpace.Carrier From) (VectorSpace.Carrier To) _≈₂_

  linear : ∀ (f : setoid₁ ⟶ setoid₂)
         -> (∀ (a b : K') (u v : A) -> (f ⟨$⟩ (a ∙₁ u +₁ b ∙₁ v)) ≈₂ a ∙₂ (f ⟨$⟩ u) +₂ b ∙₂ (f ⟨$⟩ v))
         -> IsLinearMap From To (f ⟨$⟩_)
  linear f lin = record
    { isAbelianGroupMorphism = record
      { gp-homo = record
        { mn-homo = record
          { sm-homo = record
            { ⟦⟧-cong = cong f
            ; ∙-homo = λ x y →
              begin
                f ⟨$⟩ x +₁ y
              ≈⟨ cong f (+₁-cong (≈₁-sym (∙₁-identity x)) (≈₁-sym (∙₁-identity y))) ⟩
                f ⟨$⟩ (1ᵏ ∙₁ x +₁ 1ᵏ ∙₁ y)
              ≈⟨ lin 1ᵏ 1ᵏ x y ⟩
                1ᵏ ∙₂ (f ⟨$⟩ x) +₂ 1ᵏ ∙₂ (f ⟨$⟩ y)
              ≈⟨ +₂-cong (∙₂-identity (f ⟨$⟩ x)) (∙₂-identity (f ⟨$⟩ y)) ⟩
                (f ⟨$⟩ x) +₂ (f ⟨$⟩ y)
              ∎
            }
          ; ε-homo =
            begin
              f ⟨$⟩ 0₁
            ≈⟨ cong f (≈₁-trans (≈₁-sym (+₁-identityˡ 0₁)) (+₁-cong (≈₁-sym (∙₁-absorbˡ 0₁)) (≈₁-sym (∙₁-absorbˡ 0₁)))) ⟩
              f ⟨$⟩ 0ᵏ ∙₁ 0₁ +₁ 0ᵏ ∙₁ 0₁
            ≈⟨ lin 0ᵏ 0ᵏ 0₁ 0₁ ⟩
              0ᵏ ∙₂ (f ⟨$⟩ 0₁) +₂ 0ᵏ ∙₂ (f ⟨$⟩ 0₁)
            ≈⟨ ≈₂-trans (+₂-cong (∙₂-absorbˡ (f ⟨$⟩ 0₁)) (∙₂-absorbˡ (f ⟨$⟩ 0₁))) (+₂-identityˡ 0₂) ⟩
              0₂
            ∎
          }
        }
      }
    ; ∙-homo = λ c u →
      begin
        f ⟨$⟩ c ∙₁ u
      ≈⟨ cong f (≈₁-trans (≈₁-sym (+₁-identityˡ (c ∙₁ u))) (+₁-cong (≈₁-sym (∙₁-absorbˡ 0₁)) ≈₁-refl)) ⟩
        f ⟨$⟩ 0ᵏ ∙₁ 0₁ +₁ c ∙₁ u
      ≈⟨ lin 0ᵏ c 0₁ u ⟩
        0ᵏ ∙₂ (f ⟨$⟩ 0₁) +₂ c ∙₂ (f ⟨$⟩ u)
      ≈⟨ ≈₂-trans (+₂-cong (∙₂-absorbˡ (f ⟨$⟩ 0₁)) ≈₂-refl) (+₂-identityˡ (c ∙₂ (f ⟨$⟩ u))) ⟩
        c ∙₂ (f ⟨$⟩ u)
      ∎
    }
    where open import Relation.Binary.EqReasoning setoid₂
