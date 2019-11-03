open import Relation.Binary using (Rel; IsEquivalence)
open import Algebra.Linear.Structures.Field

open import Algebra.FunctionProperties as FP
open import Algebra.Linear.Structures.VectorSpace

open import Level

module Algebra.Linear.Morphism.VectorSpace
  {k ℓᵏ : Level} {K : Set k}
  {_≈ᵏ_ : Rel K ℓᵏ} {≈ᵏ-isEquiv : IsEquivalence _≈ᵏ_}
  {_+ᵏ_ _*ᵏ_ : Op₂ K} {0ᵏ 1ᵏ : K} { -ᵏ_ : Op₁ K } {_⁻¹ : MultiplicativeInverse ≈ᵏ-isEquiv 0ᵏ}
  (isField : IsField ≈ᵏ-isEquiv _+ᵏ_ _*ᵏ_ 0ᵏ 1ᵏ -ᵏ_ _⁻¹)
  where

open import Algebra.Morphism public
open Definitions public

record IsLinearMap
       {a₁ ℓ₁} {V₁ : Set a₁} {_≈₁_ : Rel V₁ ℓ₁} {≈₁-isEquiv : IsEquivalence _≈₁_}
       {_+₁_ : FP.Op₂ V₁} {_∙₁_ : K → V₁ -> V₁} { -₁_ : FP.Op₁ V₁ } {0₁ : V₁}
       (isVectorSpace₁ : IsVectorSpace isField ≈₁-isEquiv _+₁_ _∙₁_ -₁_ 0₁)
       {a₂ ℓ₂} {V₂ : Set a₂}  {_≈₂_ : Rel V₂ ℓ₂} {≈₂-isEquiv : IsEquivalence _≈₂_}
       {_+₂_ : FP.Op₂ V₂} {_∙₂_ : K → V₂ -> V₂} { -₂_ : FP.Op₁ V₂ } {0₂ : V₂}
       (isVectorSpace₂ : IsVectorSpace isField ≈₂-isEquiv _+₂_ _∙₂_ -₂_ 0₂)
       (μ : Morphism V₁ V₂ _≈₂_)
       : Set (a₁ ⊔ a₂ ⊔ ℓ₂ ⊔ k)
    where
  field
    linear : ∀ (x y : K) (u v : V₁) -> μ ((x ∙₁ u) +₁ (y ∙₁ v)) ≈₂ ((x ∙₂ (μ u)) +₂ (y ∙₂ (μ v)))

record IsLinearIsomorphism
       {a₁ ℓ₁} {V₁ : Set a₁} {_≈₁_ : Rel V₁ ℓ₁} {≈₁-isEquiv : IsEquivalence _≈₁_}
       {_+₁_ : FP.Op₂ V₁} {_∙₁_ : K → V₁ -> V₁} { -₁_ : FP.Op₁ V₁ } {0₁ : V₁}
       (isVectorSpace₁ : IsVectorSpace isField ≈₁-isEquiv _+₁_ _∙₁_ -₁_ 0₁)
       {a₂ ℓ₂} {V₂ : Set a₂}  {_≈₂_ : Rel V₂ ℓ₂} {≈₂-isEquiv : IsEquivalence _≈₂_}
       {_+₂_ : FP.Op₂ V₂} {_∙₂_ : K → V₂ -> V₂} { -₂_ : FP.Op₁ V₂ } {0₂ : V₂}
       (isVectorSpace₂ : IsVectorSpace isField ≈₂-isEquiv _+₂_ _∙₂_ -₂_ 0₂)
       (μ : Morphism V₁ V₂ _≈₂_) (μ⁻¹ : Morphism V₂ V₁ _≈₁_)
       : Set (a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ k)
    where
  field
    μ-isLinear  : IsLinearMap isVectorSpace₁ isVectorSpace₂ μ
    μ⁻¹-isLinear : IsLinearMap isVectorSpace₂ isVectorSpace₁ μ⁻¹
    μ∘μ⁻¹≈₂id     : ∀ (u : V₂) -> μ (μ⁻¹ u) ≈₂ u
    μ⁻¹∘μ≈₁id     : ∀ (u : V₁) → μ⁻¹ (μ u) ≈₁ u

IsLinearEndomorphism :
  ∀ {a ℓ} {V : Set a} {_≈_ : Rel V ℓ} {≈-isEquiv : IsEquivalence _≈_}
    {_+_ : FP.Op₂ V} {_∙_ : K → V -> V} { -_ : FP.Op₁ V } {0# : V}
    (isVectorSpace : IsVectorSpace isField ≈-isEquiv _+_ _∙_ -_ 0#)
    (μ : Morphism V V _≈_)
  -> Set (a ⊔ ℓ ⊔ k)
IsLinearEndomorphism space μ = IsLinearMap space space μ

IsLinearAutomorphism :
  ∀ {a ℓ} {V : Set a} {_≈_ : Rel V ℓ} {≈-isEquiv : IsEquivalence _≈_}
    {_+_ : FP.Op₂ V} {_∙_ : K → V -> V} { -_ : FP.Op₁ V } {0# : V}
    (isVectorSpace : IsVectorSpace isField ≈-isEquiv _+_ _∙_ -_ 0#)
    (μ : Morphism V V _≈_) (μ⁻¹ : Morphism V V _≈_)
  -> Set (a ⊔ ℓ ⊔ k)
IsLinearAutomorphism space μ μ⁻¹ = IsLinearIsomorphism space space μ μ⁻¹
