open import Relation.Binary
open import Algebra.Linear.Structures.Field
open import Algebra.Linear.Structures.VectorSpace

import Algebra.FunctionProperties as FP

open import Data.Product
open import Data.Nat using (ℕ; zero; suc)

module Algebra.Linear.Construct.ProductSpace
  {a₁ a₂ k ℓ₁ ℓ₂ ℓᵏ} {K : Set k}
  {_≈ᵏ_ : Rel K ℓᵏ}
  (≈ᵏ-isEquiv : IsEquivalence _≈ᵏ_)
  {_+ᵏ_ _*ᵏ_ : FP.Op₂ K} {0ᵏ 1ᵏ : K} { -ᵏ_ : FP.Op₁ K } {_⁻¹ᵏ : MultiplicativeInverse ≈ᵏ-isEquiv 0ᵏ}
  (isField : IsField ≈ᵏ-isEquiv _+ᵏ_ _*ᵏ_ 0ᵏ 1ᵏ -ᵏ_ _⁻¹ᵏ)
  {V₁ : Set a₁} {_≈₁_ : Rel V₁ ℓ₁} {≈₁-isEquiv : IsEquivalence _≈₁_}
  {_+₁_ : FP.Op₂ V₁} {_∙₁_ : K → V₁ -> V₁} { -₁_ : FP.Op₁ V₁ } {0₁ : V₁}
  (isVectorSpace₁ : IsVectorSpace isField ≈₁-isEquiv _+₁_ _∙₁_ -₁_ 0₁)
  {V₂ : Set a₂}  {_≈₂_ : Rel V₂ ℓ₂} {≈₂-isEquiv : IsEquivalence _≈₂_}
  {_+₂_ : FP.Op₂ V₂} {_∙₂_ : K → V₂ -> V₂} { -₂_ : FP.Op₁ V₂ } {0₂ : V₂}
  (isVectorSpace₂ : IsVectorSpace isField ≈₂-isEquiv _+₂_ _∙₂_ -₂_ 0₂)
  where

open IsEquivalence ≈ᵏ-isEquiv renaming
  ( refl  to ≈ᵏ-refl
  ; sym   to ≈ᵏ-sym
  ; trans to ≈ᵏ-trans
  )

open IsEquivalence ≈₁-isEquiv renaming
  ( refl  to ≈₁-refl
  ; sym   to ≈₁-sym
  ; trans to ≈₁-trans
  )

open IsEquivalence ≈₂-isEquiv renaming
  ( refl  to ≈₂-refl
  ; sym   to ≈₂-sym
  ; trans to ≈₂-trans
  )

open IsField isField
  hiding (+-isMagma; +-isSemigroup; +-isMonoid; +-isGroup; +-isAbelianGroup)
  renaming
  ( +-cong        to +ᵏ-cong
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
  ; _-_           to _-ᵏ_
  ; _⁻¹-inverse    to _⁻¹ᵏ-inverse
  ; _⁻¹-involutive to _⁻¹ᵏ-involutive
  ; 0#-not-1#     to 0ᵏ-not-1ᵏ
  )

open import Level using (_⊔_)

open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent

private
  V : Set (a₁ ⊔ a₂)
  V = V₁ × V₂

_≈_ : Rel V (ℓ₁ ⊔ ℓ₂)
_≈_ = Pointwise _≈₁_ _≈₂_

≈-isEquiv : IsEquivalence _≈_
≈-isEquiv = ×-isEquivalence ≈₁-isEquiv ≈₂-isEquiv

open IsEquivalence ≈-isEquiv renaming
  ( refl  to ≈-refl
  ; sym   to ≈-sym
  ; trans to ≈-trans
  )

open import Algebra.FunctionProperties _≈_
open import Algebra.Structures _≈_

0# : V
0# = (0₁ , 0₂)

-_ : Op₁ V
- (x₁ , x₂) = (-₁ x₁ , -₂ x₂)

_+_ : Op₂ V
(x₁ , x₂) + (y₁ , y₂) = (x₁ +₁ y₁ , x₂ +₂ y₂)

_∙_ : K -> V -> V
k ∙ (x₁ , x₂) = (k ∙₁ x₁ , k ∙₂ x₂)

+-cong : Congruent₂ _+_
+-cong r₁ r₂ = ( IsVectorSpace.+-cong isVectorSpace₁ (proj₁ r₁) (proj₁ r₂)
              , IsVectorSpace.+-cong isVectorSpace₂ (proj₂ r₁) (proj₂ r₂))

+-assoc : Associative _+_
+-assoc (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) = ( IsVectorSpace.+-assoc isVectorSpace₁ x₁ y₁ z₁
                                       , IsVectorSpace.+-assoc isVectorSpace₂ x₂ y₂ z₂ )

+-identityˡ : LeftIdentity 0# _+_
+-identityˡ (x₁ , x₂) = ( IsVectorSpace.+-identityˡ isVectorSpace₁ x₁
                       , IsVectorSpace.+-identityˡ isVectorSpace₂ x₂ )

+-identityʳ : RightIdentity 0# _+_
+-identityʳ (x₁ , x₂) = ( IsVectorSpace.+-identityʳ isVectorSpace₁ x₁
                       , IsVectorSpace.+-identityʳ isVectorSpace₂ x₂ )

+-identity : Identity 0# _+_
+-identity = +-identityˡ , +-identityʳ

+-comm : Commutative _+_
+-comm (x₁ , x₂) (y₁ , y₂) = ( IsVectorSpace.+-comm isVectorSpace₁ x₁ y₁
                            , IsVectorSpace.+-comm isVectorSpace₂ x₂ y₂ )

*ᵏ-∙-compat : ∀ (a b : K) (u : V) -> ((a *ᵏ b) ∙ u) ≈ (a ∙ (b ∙ u))
*ᵏ-∙-compat a b (x₁ , x₂) = ( IsVectorSpace.*ᵏ-∙-compat isVectorSpace₁ a b x₁
                           , IsVectorSpace.*ᵏ-∙-compat isVectorSpace₂ a b x₂ )

∙-+-distrib : ∀ (a : K) (u v : V) -> (a ∙ (u + v)) ≈ ((a ∙ u) + (a ∙ v))
∙-+-distrib a (x₁ , x₂) (y₁ , y₂) = ( IsVectorSpace.∙-+-distrib isVectorSpace₁ a x₁ y₁
                                   , IsVectorSpace.∙-+-distrib isVectorSpace₂ a x₂ y₂ )

∙-+ᵏ-distrib : ∀ (a b : K) (u : V) -> ((a +ᵏ b) ∙ u) ≈ ((a ∙ u) + (b ∙ u))
∙-+ᵏ-distrib a b  (x₁ , x₂) = ( IsVectorSpace.∙-+ᵏ-distrib isVectorSpace₁ a b x₁
                             , IsVectorSpace.∙-+ᵏ-distrib isVectorSpace₂ a b x₂ )

∙-cong : ∀ (a : K) (u v : V) -> u ≈ v -> (a ∙ u) ≈ (a ∙ v)
∙-cong a (x₁ , x₂) (y₁ , y₂) (r₁ , r₂) = ( IsVectorSpace.∙-cong isVectorSpace₁ a x₁ y₁ r₁
                                        , IsVectorSpace.∙-cong isVectorSpace₂ a x₂ y₂ r₂ )

∙-identity : ∀ (x : V) → (1ᵏ ∙ x) ≈ x
∙-identity (x₁ , x₂) = ( IsVectorSpace.∙-identity isVectorSpace₁ x₁
                       , IsVectorSpace.∙-identity isVectorSpace₂ x₂ )

∙-absorb : ∀ (x : V) → (0ᵏ ∙ x) ≈ 0#
∙-absorb (x₁ , x₂) = ( IsVectorSpace.∙-absorb isVectorSpace₁ x₁
                     , IsVectorSpace.∙-absorb isVectorSpace₂ x₂ )

-‿inverseˡ : LeftInverse 0# -_ _+_
-‿inverseˡ (x₁ , x₂) =  ( IsVectorSpace.-‿inverseˡ isVectorSpace₁ x₁
                        , IsVectorSpace.-‿inverseˡ isVectorSpace₂ x₂ )

-‿inverseʳ : RightInverse 0# -_ _+_
-‿inverseʳ (x₁ , x₂) = ( IsVectorSpace.-‿inverseʳ isVectorSpace₁ x₁
                       , IsVectorSpace.-‿inverseʳ isVectorSpace₂ x₂ )

-‿inverse : Inverse 0# -_ _+_
-‿inverse = -‿inverseˡ , -‿inverseʳ

-‿cong : Congruent₁ -_
-‿cong  (x₁ , x₂) = ( IsVectorSpace.-‿cong isVectorSpace₁ x₁
                     , IsVectorSpace.-‿cong isVectorSpace₂ x₂ )

+-isMagma : IsMagma _+_
+-isMagma = record
  { isEquivalence = ≈-isEquiv
  ; ∙-cong        = +-cong
  }

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-isMonoid : IsMonoid _+_ 0#
+-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-isGroup : IsGroup _+_ 0# -_
+-isGroup = record
  { isMonoid = +-isMonoid
  ; inverse  = -‿inverse
  ; ⁻¹-cong   = -‿cong
  }

+-isAbelianGroup : IsAbelianGroup _+_ 0# -_
+-isAbelianGroup = record
  { isGroup = +-isGroup
  ; comm    = +-comm
  }

import Algebra.Linear.Structures.VectorSpace {k} {ℓᵏ} {K = K} isField as VS

+-∙-isVectorSpace : VS.IsVectorSpace ≈-isEquiv _+_ _∙_ -_ 0#
+-∙-isVectorSpace = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *ᵏ-∙-compat      = *ᵏ-∙-compat
  ; ∙-+-distrib      = ∙-+-distrib
  ; ∙-+ᵏ-distrib     = ∙-+ᵏ-distrib
  ; ∙-cong           = ∙-cong
  ; ∙-identity       = ∙-identity
  ; ∙-absorb         = ∙-absorb
  }
{-
+-∙-isFiniteDimensional : ∀ {n} -> IsFiniteDimensional (≈-isEquiv {n}) _+_ _∙_ -_ 0#
+-∙-isFiniteDimensional {n} = record
  { isVectorSpace = +-∙-isVectorSpace
  ; dim           = n
  }
-}
