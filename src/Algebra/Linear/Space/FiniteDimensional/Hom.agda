{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field
import Algebra.Linear.Structures.Bundles.FiniteDimensional as FDB

module Algebra.Linear.Space.FiniteDimensional.Hom
       {k ℓᵏ} (K : Field k ℓᵏ)
       {p a₁ ℓ₁} (V₁-space : FDB.FiniteDimensional K a₁ ℓ₁ p)
       {n a₂ ℓ₂} (V₂-space : FDB.FiniteDimensional K a₂ ℓ₂ n)
       where

open import Algebra.Linear.Structures.VectorSpace K
open import Algebra.Linear.Structures.Bundles as VS
open import Algebra.Linear.Structures.FiniteDimensional K

open import Algebra.Linear.Morphism.Bundles K

open VectorSpaceField

open FDB.FiniteDimensional V₁-space
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
  ; ∙-absorbˡ      to ∙₁-absorbˡ
  ; ∙-absorbʳ      to ∙₁-absorbʳ
  ; -‿cong        to -₁‿cong
  ; -‿inverseˡ    to -₁‿inverseˡ
  ; -‿inverseʳ    to -₁‿inverseʳ
  ; vectorSpace   to vectorSpace₁
  ; embed         to embed₁
  )

open FDB.FiniteDimensional V₂-space
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
  ; ∙-absorbˡ      to ∙₂-absorbˡ
  ; ∙-absorbʳ      to ∙₂-absorbʳ
  ; -‿cong        to -₂‿cong
  ; -‿inverseˡ    to -₂‿inverseˡ
  ; -‿inverseʳ    to -₂‿inverseʳ
  ; vectorSpace   to vectorSpace₂
  ; embed         to embed₂
  )

open LinearIsomorphism embed₁
  using ()
  renaming
  ( ⟦_⟧        to ⟦_⟧₁
  ; ⟦⟧-cong    to ⟦⟧₁-cong
  ; injective  to ⟦⟧₁-injective
  ; surjective to ⟦⟧₁-surjective
  ; +-homo     to +₁-homo
  ; ∙-homo     to ∙₁-homo
  ; 0#-homo    to 0₁-homo
  )

open LinearIsomorphism embed₂
  using ()
  renaming
  ( ⟦_⟧        to ⟦_⟧₂
  ; ⟦⟧-cong    to ⟦⟧₂-cong
  ; injective  to ⟦⟧₂-injective
  ; surjective to ⟦⟧₂-surjective
  ; +-homo     to +₂-homo
  ; ∙-homo     to ∙₂-homo
  ; 0#-homo    to 0₂-homo
  )

import Algebra.Linear.Construct.HomSpace K vectorSpace₁ vectorSpace₂ as PS

open VS.VectorSpace PS.vectorSpace
  renaming
    ( refl  to ≈-refl
    ; sym   to ≈-sym
    ; trans to ≈-trans
    )

import Algebra.Linear.Construct.Vector as Vec
open Vec K
  using
    ( ++-cong
    ; ++-identityˡ
    ; +-distrib-++
    ; ∙-distrib-++
    ; 0++0≈0
    )
  renaming
    ( _≈_         to _≈v_
    ; ≈-refl      to ≈v-refl
    ; ≈-sym       to ≈v-sym
    ; ≈-trans     to ≈v-trans
    ; _+_         to _+v_
    ; _∙_         to _∙v_
    ; 0#          to 0v
    ; +-cong      to +v-cong
    ; setoid      to vec-setoid
    ; vectorSpace to vector-vectorSpace
    )

import Algebra.Linear.Construct.Matrix K as M

open import Data.Nat hiding (_+_) renaming (_*_ to _*ℕ_)

open import Relation.Binary.PropositionalEquality as P
  using (_≡_; subst; subst-subst-sym)
  renaming
  ( refl  to ≡-refl
  ; sym   to ≡-sym
  ; trans to ≡-trans
  )

open import Data.Vec
open import Data.Product
open import Data.Fin
open import Function

δ : ∀ {n p} -> Fin n -> Fin p -> K'
δ zero zero = 1ᵏ
δ (suc n) zero = 0ᵏ
δ zero (suc p) = 0ᵏ
δ (suc n) (suc p) = δ n p

canonicalBasis : M.Matrix n p
canonicalBasis = M.tabulate δ

module _ where
  open import Algebra.Morphism.Definitions (LinearMap vectorSpace₁ vectorSpace₂) (M.Matrix n p) M._≈_
  open import Algebra.Linear.Morphism.Definitions K (LinearMap vectorSpace₁ vectorSpace₂) (M.Matrix n p) M._≈_
  import Relation.Binary.Morphism.Definitions (LinearMap vectorSpace₁ vectorSpace₂) (M.Matrix n p) as R
  open import Relation.Binary.EqReasoning (M.setoid {n} {p})

  Mat : LinearMap vectorSpace₁ vectorSpace₂ -> M.Matrix n p
  Mat f = M.mapCols (λ u -> embed₂ LinearIsomorphism.⟪$⟫ (f LinearMap.⟪$⟫ {! embed₁ ⁻¹ ⟪$⟫ u!}))
                    canonicalBasis

-- (λ u → embed₂ LinearIsomorphism.⟪$⟫ (proj₁ (⟦⟧₂-surjective u))) canonicalBasis

  Mat-cong : R.Homomorphic₂ _≈_ M._≈_ Mat
  Mat-cong {A} {B} f =
    begin
      Mat A
    ≈⟨ M.≈-reflexive (M.mapCols-cong (λ u → {!!}) canonicalBasis) ⟩
      {!!}
    ≈⟨ {!!} ⟩
      Mat B
    ∎

{-

Mat-cong : R.Homomorphic₂ PS._≈_ _≈v_ Mat
⟦⟧-cong (r₁ , r₂) = ++-cong (⟦⟧₁-cong r₁) (⟦⟧₂-cong r₂)

+-homo : Homomorphic₂ ⟦_⟧ _+_ _+v_
+-homo (x₁ , x₂) (y₁ , y₂) =
    begin
      ⟦ (x₁ , x₂) + (y₁ , y₂) ⟧
    ≡⟨⟩
      ⟦ x₁ +₁ y₁ ⟧₁ ++ ⟦ x₂ +₂ y₂ ⟧₂
    ≈⟨ ++-cong (+₁-homo x₁ y₁) (+₂-homo x₂ y₂) ⟩
      (⟦ x₁ ⟧₁ +v ⟦ y₁ ⟧₁) ++ (⟦ x₂ ⟧₂ +v ⟦ y₂ ⟧₂)
    ≈⟨ ≈v-sym (+-distrib-++ ⟦ x₁ ⟧₁ ⟦ x₂ ⟧₂ ⟦ y₁ ⟧₁ ⟦ y₂ ⟧₂) ⟩
      (⟦ x₁ ⟧₁ ++ ⟦ x₂ ⟧₂) +v (⟦ y₁ ⟧₁ ++ ⟦ y₂ ⟧₂)
    ≈⟨ +v-cong ≈v-refl ≈v-refl ⟩
       ⟦ x₁ , x₂ ⟧ +v ⟦ y₁ , y₂ ⟧
    ∎

0#-homo : Homomorphic₀ ⟦_⟧ 0# 0v
0#-homo =
  begin
    ⟦ 0# ⟧
  ≡⟨⟩
    ⟦ 0₁ ⟧₁ ++ ⟦ 0₂ ⟧₂
  ≈⟨ ++-cong 0₁-homo 0₂-homo ⟩
    (0v {n}) ++ (0v {p})
  ≈⟨ 0++0≈0 {n} {p} ⟩
    0v {n +ℕ p}
  ∎

∙-homo : ScalarHomomorphism ⟦_⟧ _∙_ _∙v_
∙-homo c (x₁ , x₂) =
  begin
    ⟦ c ∙ (x₁ , x₂) ⟧
  ≈⟨ ++-cong (∙₁-homo c x₁) (∙₂-homo c x₂) ⟩
    (c ∙v ⟦ x₁ ⟧₁) ++ (c ∙v ⟦ x₂ ⟧₂)
  ≈⟨ ≈v-sym (∙-distrib-++ c ⟦ x₁ ⟧₁ ⟦ x₂ ⟧₂) ⟩
    c ∙v ⟦ x₁ , x₂ ⟧
  ∎

⟦⟧-injective : Injective ⟦_⟧
⟦⟧-injective {x₁ , x₂} {y₁ , y₂} r =
  let (r₁ , r₂) = ++-split r
  in ⟦⟧₁-injective r₁ , ⟦⟧₂-injective r₂

⟦⟧-surjective : Surjective ⟦_⟧
⟦⟧-surjective y =
  let (x₁ , x₂) = splitAt' n p ≡-refl y
      (u , r₁) = ⟦⟧₁-surjective x₁
      (v , r₂) = ⟦⟧₂-surjective x₂
  in  (u , v) , ≈v-trans (++-cong r₁ r₂) (++-splitAt' {n} {p} y)

embed : LinearIsomorphism PS.vectorSpace (vector-vectorSpace {n +ℕ p})
embed = record
  { ⟦_⟧ = ⟦_⟧
  ; isLinearIsomorphism = record
    { isLinearMonomorphism = record
      { isLinearMap = record
        { isAbelianGroupMorphism = record
          { gp-homo = record
            { mn-homo = record
              { sm-homo = record
                { ⟦⟧-cong = ⟦⟧-cong
                ; ∙-homo = +-homo
                }
              ; ε-homo = 0#-homo
              }
            }
          }
        ; ∙-homo = ∙-homo
        }
      ; injective = ⟦⟧-injective
      }
    ; surjective = ⟦⟧-surjective
    }
  }

isFiniteDimensional : IsFiniteDimensional _≈_ _+_ _∙_ -_ 0# (n +ℕ p)
isFiniteDimensional = record
  { isVectorSpace = isVectorSpace
  ; embed         = embed
  }
-}
