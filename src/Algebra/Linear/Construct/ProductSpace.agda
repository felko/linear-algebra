open import Relation.Binary
open import Algebra.Linear.Structures.VectorSpace
open import Algebra.Linear.Structures.Bundles.Field
open import Algebra.Linear.Structures.Bundles

import Algebra.FunctionProperties as FP

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)

module Algebra.Linear.Construct.ProductSpace
  {k ℓ} (K : Field k ℓ)
  {a₁ ℓ₁} (V₁-space : VectorSpace K a₁ ℓ₁)
  {a₂ ℓ₂} (V₂-space : VectorSpace K a₂ ℓ₂)
  where

open VectorSpaceField K

open VectorSpace V₁-space
  using ()
  renaming
  ( Carrier       to V₁
  ; _≈_           to _≈₁_
  ; isEquivalence to ≈₁-isEquiv
  ; refl          to ≈₁-refl
  ; sym           to ≈₁-sym
  ; trans         to ≈₁-trans
  ; _+_           to _+₁_
  ; _∙_           to _∙₁_
  ; -_            to -₁_
  ; 0#            to 0₁
  ; +-identityˡ    to +₁-identityˡ
  ; +-identityʳ    to +₁-identityʳ
  ; +-identity    to +₁-identity
  ; +-cong        to +₁-cong
  ; +-assoc       to +₁-assoc
  ; +-comm        to +₁-comm
  ; *ᵏ-∙-compat   to *ᵏ-∙₁-compat
  ; ∙-+-distrib   to ∙₁-+₁-distrib
  ; ∙-+ᵏ-distrib  to ∙₁-+ᵏ-distrib
  ; ∙-cong        to ∙₁-cong
  ; ∙-identity    to ∙₁-identity
  ; ∙-absorb      to ∙₁-absorb
  ; -‿cong        to -₁‿cong
  ; -‿inverseˡ    to -₁‿inverseˡ
  ; -‿inverseʳ    to -₁‿inverseʳ
  )

open VectorSpace V₂-space
  using ()
  renaming
  ( Carrier       to V₂
  ; _≈_           to _≈₂_
  ; isEquivalence to ≈₂-isEquiv
  ; refl          to ≈₂-refl
  ; sym           to ≈₂-sym
  ; trans         to ≈₂-trans
  ; _+_           to _+₂_
  ; _∙_           to _∙₂_
  ; -_            to -₂_
  ; 0#            to 0₂
  ; +-identityˡ    to +₂-identityˡ
  ; +-identityʳ    to +₂-identityʳ
  ; +-identity    to +₂-identity
  ; +-cong        to +₂-cong
  ; +-assoc       to +₂-assoc
  ; +-comm        to +₂-comm
  ; *ᵏ-∙-compat   to *ᵏ-∙₂-compat
  ; ∙-+-distrib   to ∙₂-+₂-distrib
  ; ∙-+ᵏ-distrib  to ∙₂-+ᵏ-distrib
  ; ∙-cong        to ∙₂-cong
  ; ∙-identity    to ∙₂-identity
  ; ∙-absorb      to ∙₂-absorb
  ; -‿cong        to -₂‿cong
  ; -‿inverseˡ    to -₂‿inverseˡ
  ; -‿inverseʳ    to -₂‿inverseʳ
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

prod-setoid : Setoid (a₁ ⊔ a₂) (ℓ₁ ⊔ ℓ₂)
prod-setoid = record
  { Carrier       = V
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquiv
  }

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

infixr 25 _+_
_+_ : Op₂ V
(x₁ , x₂) + (y₁ , y₂) = (x₁ +₁ y₁ , x₂ +₂ y₂)

infixr 30 _∙_
_∙_ : K' -> V -> V
k ∙ (x₁ , x₂) = (k ∙₁ x₁ , k ∙₂ x₂)

+-cong : Congruent₂ _+_
+-cong (r₁ , r₂) (s₁ , s₂) = ( +₁-cong r₁ s₁ , +₂-cong r₂ s₂ )

+-assoc : Associative _+_
+-assoc (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) = ( +₁-assoc x₁ y₁ z₁ , +₂-assoc x₂ y₂ z₂ )

+-identityˡ : LeftIdentity 0# _+_
+-identityˡ (x₁ , x₂) = ( +₁-identityˡ x₁ , +₂-identityˡ x₂ )

+-identityʳ : RightIdentity 0# _+_
+-identityʳ (x₁ , x₂) = ( +₁-identityʳ x₁ , +₂-identityʳ x₂ )

+-identity : Identity 0# _+_
+-identity = +-identityˡ , +-identityʳ

+-comm : Commutative _+_
+-comm (x₁ , x₂) (y₁ , y₂) = ( +₁-comm x₁ y₁ , +₂-comm x₂ y₂ )

*ᵏ-∙-compat : ∀ (a b : K') (u : V) -> ((a *ᵏ b) ∙ u) ≈ (a ∙ (b ∙ u))
*ᵏ-∙-compat a b (x₁ , x₂) = ( *ᵏ-∙₁-compat a b x₁ , *ᵏ-∙₂-compat a b x₂ )

∙-+-distrib : ∀ (a : K') (u v : V) -> (a ∙ (u + v)) ≈ ((a ∙ u) + (a ∙ v))
∙-+-distrib a (x₁ , x₂) (y₁ , y₂) = ( ∙₁-+₁-distrib a x₁ y₁ , ∙₂-+₂-distrib a x₂ y₂ )

∙-+ᵏ-distrib : ∀ (a b : K') (u : V) -> ((a +ᵏ b) ∙ u) ≈ ((a ∙ u) + (b ∙ u))
∙-+ᵏ-distrib a b  (x₁ , x₂) = ( ∙₁-+ᵏ-distrib a b x₁ , ∙₂-+ᵏ-distrib a b x₂ )

∙-cong : ∀ (a : K') (u v : V) -> u ≈ v -> (a ∙ u) ≈ (a ∙ v)
∙-cong a (x₁ , x₂) (y₁ , y₂) (r₁ , r₂) = ( ∙₁-cong a x₁ y₁ r₁ , ∙₂-cong a x₂ y₂ r₂ )

∙-identity : ∀ (x : V) → (1ᵏ ∙ x) ≈ x
∙-identity (x₁ , x₂) = ( ∙₁-identity x₁ , ∙₂-identity x₂ )

∙-absorb : ∀ (x : V) → (0ᵏ ∙ x) ≈ 0#
∙-absorb (x₁ , x₂) = ( ∙₁-absorb x₁ , ∙₂-absorb x₂ )

-‿inverseˡ : LeftInverse 0# -_ _+_
-‿inverseˡ (x₁ , x₂) = ( -₁‿inverseˡ x₁ , -₂‿inverseˡ x₂ )

-‿inverseʳ : RightInverse 0# -_ _+_
-‿inverseʳ (x₁ , x₂) = ( -₁‿inverseʳ x₁ , -₂‿inverseʳ x₂ )

-‿inverse : Inverse 0# -_ _+_
-‿inverse = -‿inverseˡ , -‿inverseʳ

-‿cong : Congruent₁ -_
-‿cong  (x₁ , x₂) = ( -₁‿cong x₁ , -₂‿cong x₂ )

isMagma : IsMagma _+_
isMagma = record
  { isEquivalence = ≈-isEquiv
  ; ∙-cong        = +-cong
  }

isSemigroup : IsSemigroup _+_
isSemigroup = record
  { isMagma = isMagma
  ; assoc   = +-assoc
  }

isMonoid : IsMonoid _+_ 0#
isMonoid = record
  { isSemigroup = isSemigroup
  ; identity    = +-identity
  }

isGroup : IsGroup _+_ 0# -_
isGroup = record
  { isMonoid = isMonoid
  ; inverse  = -‿inverse
  ; ⁻¹-cong   = -‿cong
  }

isAbelianGroup : IsAbelianGroup _+_ 0# -_
isAbelianGroup = record
  { isGroup = isGroup
  ; comm    = +-comm
  }

isVectorSpace : IsVectorSpace K _≈_ _+_ _∙_ -_ 0#
isVectorSpace = record
  { isAbelianGroup = isAbelianGroup
  ; *ᵏ-∙-compat      = *ᵏ-∙-compat
  ; ∙-+-distrib      = ∙-+-distrib
  ; ∙-+ᵏ-distrib     = ∙-+ᵏ-distrib
  ; ∙-cong           = ∙-cong
  ; ∙-identity       = ∙-identity
  ; ∙-absorb         = ∙-absorb
  }

vectorSpace : VectorSpace K (a₁ ⊔ a₂)  (ℓ₁ ⊔ ℓ₂)
vectorSpace = record { isVectorSpace = isVectorSpace }
