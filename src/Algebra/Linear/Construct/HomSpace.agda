{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field
open import Algebra.Linear.Structures.Bundles

module Algebra.Linear.Construct.HomSpace
  {k ℓ} (K : Field k ℓ)
  {a₁ ℓ₁} (V₁-space : VectorSpace K a₁ ℓ₁)
  {a₂ ℓ₂} (V₂-space : VectorSpace K a₂ ℓ₂)
  where

open import Relation.Binary
open import Level using (_⊔_; suc)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Algebra.Linear.Morphism.Bundles K
open import Algebra.Linear.Morphism.Properties K
open import Algebra.Linear.Structures.VectorSpace

open import Data.Product

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
  ; setoid        to setoid₁
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
  ; ∙-absorbˡ      to ∙₁-absorbˡ
  ; ∙-absorbʳ      to ∙₁-absorbʳ
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
  ; setoid        to setoid₂
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
  ; ∙-absorbˡ      to ∙₂-absorbˡ
  ; ∙-absorbʳ      to ∙₂-absorbʳ
  ; ∙-∙-comm      to ∙₂-∙₂-comm
  ; -‿cong        to -₂‿cong
  ; -‿inverseˡ    to -₂‿inverseˡ
  ; -‿inverseʳ    to -₂‿inverseʳ
  ; -‿+-comm     to -₂‿+₂-comm
  ; -1∙u≈-u       to -1∙u≈₂-u
  )

import Function

private
  V : Set (suc (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂))
  V = LinearMap V₁-space V₂-space

open LinearMap using (_⟪$⟫_; ⟦⟧-cong; distrib-linear)

setoid : Setoid (suc (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂)) _
setoid = linearMap-setoid V₁-space V₂-space

open Setoid setoid public
  renaming (isEquivalence to ≈-isEquiv)

open import Algebra.FunctionProperties _≈_
open import Algebra.Structures _≈_
open import Function.Equality hiding (setoid; _∘_)

open import Relation.Binary.EqReasoning setoid₂

0# : V
0# = record
  { ⟦_⟧ = λ x → 0₂
  ; isLinearMap = linear V₁-space V₂-space π
    λ a b u v →
      begin
        0₂
      ≈⟨ ≈₂-trans (≈₂-sym (∙₂-absorbʳ b)) (≈₂-sym (+₂-identityˡ (b ∙₂ 0₂))) ⟩
        0₂ +₂ b ∙₂ 0₂
      ≈⟨ +₂-cong (≈₂-sym (∙₂-absorbʳ a)) ≈₂-refl ⟩
        a ∙₂ 0₂ +₂ b ∙₂ 0₂
      ∎
  }
  where π : setoid₁ ⟶ setoid₂
        π = record
          { _⟨$⟩_ = λ x → 0₂
          ; cong  = λ r → ≈₂-refl }

-_ : Op₁ V
- f = record
  { ⟦_⟧ = λ x → -₂ f ⟪$⟫ x
  ; isLinearMap = linear V₁-space V₂-space π
    let -[a∙u]≈₂a∙[-u] : ∀ (a : K') (u : V₂) -> (-₂ (a ∙₂ u)) ≈₂ a ∙₂ (-₂ u)
        -[a∙u]≈₂a∙[-u] a u =
          begin
            (-₂ (a ∙₂ u))
          ≈⟨ ≈₂-sym (-1∙u≈₂-u (a ∙₂ u)) ⟩
            (-ᵏ 1ᵏ) ∙₂ (a ∙₂ u)
          ≈⟨ ≈₂-sym (*ᵏ-∙₂-compat (-ᵏ 1ᵏ) a u) ⟩
            ((-ᵏ 1ᵏ) *ᵏ a) ∙₂ u
          ≈⟨ ∙₂-cong (≈ᵏ-trans (≈ᵏ-sym (-ᵏ‿distribˡ-*ᵏ 1ᵏ a)) (-ᵏ‿cong (*ᵏ-identityˡ a))) ≈₂-refl ⟩
            (-ᵏ a) ∙₂ u
          ≈⟨ ∙₂-cong (≈ᵏ-trans (-ᵏ‿cong (≈ᵏ-sym (*ᵏ-identityʳ a))) (-ᵏ‿distribʳ-*ᵏ a 1ᵏ)) ≈₂-refl ⟩
            (a *ᵏ (-ᵏ 1ᵏ)) ∙₂ u
          ≈⟨ ≈₂-trans (*ᵏ-∙₂-compat a (-ᵏ 1ᵏ) u) (∙₂-cong ≈ᵏ-refl (-1∙u≈₂-u u)) ⟩
             a ∙₂ (-₂ u)
          ∎
    in λ a b u v →
      begin
        π ⟨$⟩ a ∙₁ u +₁ b ∙₁ v
      ≈⟨ -₂‿cong (distrib-linear f a b u v) ⟩
        -₂ (a ∙₂ (f ⟪$⟫ u) +₂ b ∙₂ (f ⟪$⟫ v))
      ≈⟨ ≈₂-sym (-₂‿+₂-comm (a ∙₂ (f ⟪$⟫ u)) ( b ∙₂ (f ⟪$⟫ v))) ⟩
        ((-₂ (a ∙₂ (f ⟪$⟫ u))) +₂ (-₂ (b ∙₂ (f ⟪$⟫ v))))
      ≈⟨ +₂-cong (-[a∙u]≈₂a∙[-u] a (f ⟪$⟫ u)) (-[a∙u]≈₂a∙[-u] b (f ⟪$⟫ v)) ⟩
        a ∙₂ (π ⟨$⟩ u) +₂ b ∙₂ (π ⟨$⟩ v)
      ∎
  } where π : setoid₁ ⟶ setoid₂
          π = record
            { _⟨$⟩_ = λ x → -₂ f ⟪$⟫ x
            ; cong  = λ r → -₂‿cong (⟦⟧-cong f r)
            }

infixr 25 _+_
_+_ : Op₂ V
f + g = record
  { ⟦_⟧ = λ x -> (f ⟪$⟫ x) +₂ (g ⟪$⟫ x)
  ; isLinearMap = linear V₁-space V₂-space π
    let reassoc : ∀ (u v u' v' : V₂) -> (u +₂ v) +₂ (u' +₂ v') ≈₂ (u +₂ u') +₂ (v +₂ v')
        reassoc u v u' v' =
          begin
            (u +₂ v) +₂ (u' +₂ v')
          ≈⟨ +₂-assoc u v (u' +₂ v') ⟩
            u +₂ (v +₂ (u' +₂ v'))
          ≈⟨ +₂-cong ≈₂-refl (≈₂-trans (≈₂-sym (+₂-assoc v u' v')) (+₂-cong (+₂-comm v u') ≈₂-refl)) ⟩
            u +₂ ((u' +₂ v) +₂ v')
          ≈⟨ ≈₂-trans (+₂-cong ≈₂-refl (+₂-assoc u' v v')) (≈₂-sym (+₂-assoc u u' (v +₂ v'))) ⟩
            (u +₂ u') +₂ (v +₂ v')
          ∎
        distrib-f-g k w = ≈₂-sym (∙₂-+₂-distrib k (f ⟪$⟫ w) (g ⟪$⟫ w))
    in λ a b u v →
      begin
        π ⟨$⟩ a ∙₁ u +₁ b ∙₁ v
      ≡⟨⟩
        (f ⟪$⟫ (a ∙₁ u +₁ b ∙₁ v)) +₂ (g ⟪$⟫ (a ∙₁ u +₁ b ∙₁ v))
      ≈⟨ +₂-cong (distrib-linear f a b u v) (distrib-linear g a b u v) ⟩
        (a ∙₂ (f ⟪$⟫ u) +₂ b ∙₂ (f ⟪$⟫ v)) +₂ ((a ∙₂ (g ⟪$⟫ u) +₂ b ∙₂ (g ⟪$⟫ v)))
      ≈⟨ reassoc (a ∙₂ (f ⟪$⟫ u)) (b ∙₂ (f ⟪$⟫ v)) (a ∙₂ (g ⟪$⟫ u)) (b ∙₂ (g ⟪$⟫ v)) ⟩
        (a ∙₂ (f ⟪$⟫ u) +₂ a ∙₂ (g ⟪$⟫ u)) +₂ ((b ∙₂ (f ⟪$⟫ v)) +₂ b ∙₂ (g ⟪$⟫ v))
      ≈⟨ +₂-cong (distrib-f-g a u) (distrib-f-g b v) ⟩
        a ∙₂ (π ⟨$⟩ u) +₂ b ∙₂ (π ⟨$⟩ v)
      ∎
  } where π : setoid₁ ⟶ setoid₂
          π = record
            { _⟨$⟩_ = λ x → (f ⟪$⟫ x) +₂ (g ⟪$⟫ x)
            ; cong  = λ r → +₂-cong (⟦⟧-cong f r) (⟦⟧-cong g r)
            }

infixr 30 _∙_
_∙_ : K' -> V -> V
c ∙ f = record
  { ⟦_⟧ = λ x → c ∙₂ (f ⟪$⟫ x)
  ; isLinearMap = linear V₁-space V₂-space π
    λ a b u v →
      begin
        π ⟨$⟩ a ∙₁ u +₁ b ∙₁ v
      ≈⟨ ∙₂-cong ≈ᵏ-refl (distrib-linear f a b u v) ⟩
        c ∙₂ (a ∙₂ (f ⟪$⟫ u) +₂ b ∙₂ (f ⟪$⟫ v))
      ≈⟨ ∙₂-+₂-distrib c (a ∙₂ (f ⟪$⟫ u)) ( b ∙₂ (f ⟪$⟫ v)) ⟩
        (c ∙₂ (a ∙₂ (f ⟪$⟫ u))) +₂ (c ∙₂ (b ∙₂ (f ⟪$⟫ v)))
      ≈⟨ +₂-cong (∙₂-∙₂-comm c a (f ⟪$⟫ u)) (∙₂-∙₂-comm c b (f ⟪$⟫ v)) ⟩
        a ∙₂ (π ⟨$⟩ u) +₂ b ∙₂ (π ⟨$⟩ v)
      ∎
  } where π : setoid₁ ⟶ setoid₂
          π = record
            { _⟨$⟩_ = λ x → c ∙₂ (f ⟪$⟫ x)
            ; cong  = λ r → ∙₂-cong ≈ᵏ-refl (⟦⟧-cong f r)
            }

+-cong : Congruent₂ _+_
+-cong r₁ r₂ = λ rₓ -> +₂-cong (r₁ rₓ) (r₂ rₓ)

+-assoc : Associative _+_
+-assoc f g h {y = y} rₓ = ≈₂-trans
  (+₂-cong (+₂-cong (⟦⟧-cong f rₓ) (⟦⟧-cong g rₓ)) (⟦⟧-cong h rₓ))
  (+₂-assoc (f ⟪$⟫ y) (g ⟪$⟫ y) (h ⟪$⟫ y))

+-identityˡ : LeftIdentity 0# _+_
+-identityˡ  f {x} rₓ = ≈₂-trans
  (+₂-identityˡ (f ⟪$⟫ x))
  (⟦⟧-cong f rₓ)

+-identityʳ : RightIdentity 0# _+_
+-identityʳ f {x} rₓ = ≈₂-trans
  (+₂-identityʳ (f ⟪$⟫ x))
  (⟦⟧-cong f rₓ)

+-identity : Identity 0# _+_
+-identity = +-identityˡ , +-identityʳ

+-comm : Commutative _+_
+-comm f g {x} rₓ = ≈₂-trans
  (+₂-comm (f ⟪$⟫ x) (g ⟪$⟫ x))
  (+₂-cong (⟦⟧-cong g rₓ) (⟦⟧-cong f rₓ))

*ᵏ-∙-compat : ∀ (a b : K') (f : V) -> ((a *ᵏ b) ∙ f) ≈ (a ∙ (b ∙ f))
*ᵏ-∙-compat a b f {x} rₓ = ≈₂-trans
  (*ᵏ-∙₂-compat a b (f ⟪$⟫ x))
  (∙₂-cong ≈ᵏ-refl (∙₂-cong ≈ᵏ-refl (⟦⟧-cong f rₓ)))

∙-+-distrib : ∀ (a : K') (f g : V) -> (a ∙ (f + g)) ≈ ((a ∙ f) + (a ∙ g))
∙-+-distrib a f g {x} rₓ = ≈₂-trans
  (∙₂-+₂-distrib a (f ⟪$⟫ x) (g ⟪$⟫ x))
  (+₂-cong (∙₂-cong ≈ᵏ-refl (⟦⟧-cong f rₓ)) (∙₂-cong ≈ᵏ-refl (⟦⟧-cong g rₓ)))

∙-+ᵏ-distrib : ∀ (a b : K') (f : V) -> ((a +ᵏ b) ∙ f) ≈ ((a ∙ f) + (b ∙ f))
∙-+ᵏ-distrib a b f {x} rₓ = ≈₂-trans
  (∙₂-+ᵏ-distrib a b (f ⟪$⟫ x))
  (+₂-cong cf cf)
  where cf : ∀ {c : K'} -> _
        cf {c} = ∙₂-cong (≈ᵏ-refl {c}) (⟦⟧-cong f rₓ)

∙-cong : ∀ {a b : K'} {f g : V} -> a ≈ᵏ b -> f ≈ g -> (a ∙ f) ≈ (b ∙ g)
∙-cong {f = f} {g = g} rk rf rₓ = ≈₂-trans
  (∙₂-cong rk (rf rₓ))
  (∙₂-cong ≈ᵏ-refl (⟦⟧-cong g ≈₁-refl))

∙-identity : ∀ (f : V) → (1ᵏ ∙ f) ≈ f
∙-identity f {x} rₓ = ≈₂-trans (∙₂-identity (f ⟪$⟫ x)) (⟦⟧-cong f rₓ)

∙-absorbˡ : ∀ (x : V) → (0ᵏ ∙ x) ≈ 0#
∙-absorbˡ f {x} _ = ≈₂-trans (∙₂-absorbˡ (f ⟪$⟫ x)) ≈₂-refl

-‿inverseˡ : LeftInverse 0# -_ _+_
-‿inverseˡ f {x} _ = ≈₂-trans (-₂‿inverseˡ (f ⟪$⟫ x)) ≈₂-refl

-‿inverseʳ : RightInverse 0# -_ _+_
-‿inverseʳ f {x} _ = -₂‿inverseʳ (f ⟪$⟫ x)

-‿inverse : Inverse 0# -_ _+_
-‿inverse = -‿inverseˡ , -‿inverseʳ

-‿cong : Congruent₁ -_
-‿cong r rₓ = -₂‿cong (r rₓ)

isMagma : IsMagma _+_
isMagma = record
  { isEquivalence = ≈-isEquiv
  -- I don't know how to solve this: I'd like to write simply ∙-cong = +-cong
  ; ∙-cong        = λ {f} {g} {u} {v} -> +-cong {f} {g} {u} {v}
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
  ; ⁻¹-cong   = λ {f} {g} -> -‿cong {f} {g}
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
  ; ∙-cong           = λ {a} {b} {f} {g} -> ∙-cong {a} {b} {f} {g}
  ; ∙-identity       = ∙-identity
  ; ∙-absorbˡ         = ∙-absorbˡ
  }

vectorSpace : VectorSpace K (suc (k ⊔ a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂)) (a₁ ⊔ ℓ₁ ⊔ ℓ₂)
vectorSpace = record { isVectorSpace = isVectorSpace }
