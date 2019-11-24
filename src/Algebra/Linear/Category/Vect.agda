{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Category.Vect
  {k ℓᵏ} (K : Field k ℓᵏ)
  {a ℓ}
  where

open import Relation.Binary using (Setoid)
open import Algebra.Linear.Structures.Bundles
open import Algebra.Linear.Morphism.Bundles K
open import Categories.Category

open LinearMap

id : ∀ {V : VectorSpace K a ℓ} -> LinearMap V V
id {V = V} = record
  { ⟦_⟧ = λ u -> u
  ; isLinearMap = record
   { isAbelianGroupMorphism = record
     { gp-homo = record
       { mn-homo = record
         { sm-homo = record
           { ⟦⟧-cong = λ r -> r
           ; ∙-homo = λ x y → VectorSpace.refl V }
         ; ε-homo = VectorSpace.refl V } } }
   ; ∙-homo = λ c u → VectorSpace.refl V } }

_∘_ : ∀ {U V W : VectorSpace K a ℓ} -> LinearMap V W -> LinearMap U V -> LinearMap U W
_∘_ {U = U} {V} {W} f g = record
  { ⟦_⟧ = λ u → f ⟪$⟫ g ⟪$⟫ u
  ; isLinearMap = record
    { isAbelianGroupMorphism = record
      { gp-homo = record
        { mn-homo = record
          { sm-homo = record
            { ⟦⟧-cong = λ r → ⟦⟧-cong f (⟦⟧-cong g r)
            ; ∙-homo = λ u v → VectorSpace.trans W (⟦⟧-cong f (+-homo g u v)) (+-homo f (g ⟪$⟫ u) (g ⟪$⟫ v))
            }
          ; ε-homo = VectorSpace.trans W (⟦⟧-cong f (0#-homo g)) (0#-homo f)
          }
        }
      }
    ; ∙-homo = λ c u → VectorSpace.trans W (⟦⟧-cong f (∙-homo g c u)) (∙-homo f c (g ⟪$⟫ u))
    }
  }

private
  module Assoc
    {U V W X : VectorSpace K a ℓ}
    {f : LinearMap U V} {g : LinearMap V W} {h : LinearMap W X}
    where

    open Setoid (linearMap-setoid U X)
    open import Relation.Binary.EqReasoning (linearMap-setoid U X)

    right : ((h ∘ g) ∘ f) ≈ (h ∘ (g ∘ f))
    right r = ⟦⟧-cong h (⟦⟧-cong g (⟦⟧-cong f r))

    left : (h ∘ (g ∘ f)) ≈ ((h ∘ g) ∘ f)
    left r = ⟦⟧-cong h (⟦⟧-cong g (⟦⟧-cong f r))

Vect : Category _ _ _
Vect = record
  { Obj = VectorSpace K a ℓ
  ; _⇒_ = λ V W → LinearMap V W
  ; _≈_ = λ {V} {W} -> Setoid._≈_ (linearMap-setoid V W)
  ; id = id
  ; _∘_ = _∘_
  ; assoc =  λ {U} {V} {W} {X} {f} {g} {h} -> Assoc.right {U} {V} {W} {X} {f} {g} {h}
  ; sym-assoc = λ {U} {V} {W} {X} {f} {g} {h} -> Assoc.left {U} {V} {W} {X} {f} {g} {h}
  ; identityˡ = λ {U} {V} {f} -> ⟦⟧-cong f
  ; identityʳ = λ {U} {V} {f} → ⟦⟧-cong f
  ; equiv = λ {V} {W} -> Setoid.isEquivalence (linearMap-setoid V W)
  ; ∘-resp-≈ = λ {U} {V} {W} {f} {h} {g} {i} rf rg rx →
    VectorSpace.trans W (rf (⟦⟧-cong g rx)) (⟦⟧-cong h (rg (VectorSpace.refl U)))
  }
