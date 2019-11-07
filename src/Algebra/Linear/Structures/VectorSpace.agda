open import Relation.Binary using (Rel; IsEquivalence)
open import Algebra.Linear.Structures.Bundles.Field

open import Algebra.FunctionProperties

module Algebra.Linear.Structures.VectorSpace
  {k ℓᵏ} (K : Field k ℓᵏ)
  where

open import Level using (_⊔_)
open import Data.Nat using (ℕ)

module VectorSpaceField where
    open Field K public
      using ()
      renaming
      ( Carrier       to K'
      ; _≈_           to _≈ᵏ_
      ; refl          to ≈ᵏ-refl
      ; sym           to ≈ᵏ-sym
      ; trans         to ≈ᵏ-trans
      ; reflexive     to ≈ᵏ-reflexive
      ; setoid        to K-setoid
      ; _+_           to _+ᵏ_
      ; _*_           to _*ᵏ_
      ; _-_           to _-ᵏ_
      ; 0#            to 0ᵏ
      ; 1#            to 1ᵏ
      ; -_            to -ᵏ_
      ; _⁻¹            to _⁻¹ᵏ
      ; +-cong        to +ᵏ-cong
      ; *-cong        to *ᵏ-cong
      ; +-identity    to +ᵏ-identity
      ; +-identityˡ    to +ᵏ-identityˡ
      ; +-identityʳ    to +ᵏ-identityʳ
      ; *-identity    to *ᵏ-identity
      ; *-identityˡ    to *ᵏ-identityˡ
      ; *-identityʳ    to *ᵏ-identityʳ
      ; zero          to *ᵏ-zero
      ; zeroˡ          to *ᵏ-zeroˡ
      ; zeroʳ          to *ᵏ-zeroʳ
      ; +-comm        to +ᵏ-comm
      ; +-assoc       to +ᵏ-assoc
      ; *-assoc       to *ᵏ-assoc
      ; distrib       to *ᵏ-+ᵏ-distrib
      ; distribˡ      to *ᵏ-+ᵏ-distribˡ
      ; distribʳ      to *ᵏ-+ᵏ-distribʳ
      ; -‿cong       to -ᵏ‿cong
      ; -‿inverse    to -ᵏ‿inverse
      ; -‿inverseˡ    to -ᵏ‿inverseˡ
      ; -‿inverseʳ    to -ᵏ‿inverseʳ
      ; uniqueˡ-⁻¹     to uniqueˡ-⁻¹ᵏ
      ; uniqueʳ-⁻¹     to uniqueʳ-⁻¹ᵏ
      ; _⁻¹-inverse    to _⁻¹ᵏ-inverse
      ; _⁻¹-involutive to _⁻¹ᵏ-involutive
      ; 0#-not-1#     to 0ᵏ-not-1ᵏ
      )

module _
  {v ℓ} {V : Set v}
  (_≈_ : Rel V ℓ)
  where

  open VectorSpaceField

  open import Algebra.Structures _≈_

  record IsVectorSpace (_+_ : Op₂ V) (_∙_ : K' → V → V) (-_ : Op₁ V) (0# : V) : Set (v ⊔ k ⊔ ℓ) where
    field
      isAbelianGroup : IsAbelianGroup _+_ 0# -_
      *ᵏ-∙-compat    : ∀ (a b : K') (u : V) -> ((a *ᵏ b) ∙ u) ≈ (a ∙ (b ∙ u))
      ∙-+-distrib    : ∀ (a : K') (u v : V) -> (a ∙ (u + v)) ≈ ((a ∙ u) + (a ∙ v))
      ∙-+ᵏ-distrib   : ∀ (a b : K') (u : V) -> ((a +ᵏ b) ∙ u) ≈ ((a ∙ u) + (b ∙ u))
      ∙-cong         : ∀ (a : K') (u v : V) -> u ≈ v -> (a ∙ u) ≈ (a ∙ v)
      ∙-identity     : ∀ (x : V) → (1ᵏ ∙ x) ≈ x
      ∙-absorb       : ∀ (x : V) → (0ᵏ ∙ x) ≈ 0#

    open IsAbelianGroup isAbelianGroup public
      renaming
      ( assoc     to +-assoc
      ; ∙-cong    to +-cong
      ; identity  to +-identity
      ; identityˡ  to +-identityˡ
      ; identityʳ  to +-identityʳ
      ; comm      to +-comm
      ; inverse   to -‿inverse
      ; inverseˡ   to -‿inverseˡ
      ; inverseʳ   to -‿inverseʳ
      ; ⁻¹-cong    to -‿cong
      )
