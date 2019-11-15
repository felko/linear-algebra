{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Structures.VectorSpace
  {k ℓᵏ} (K : Field k ℓᵏ)
  where

open import Algebra.FunctionProperties
open import Relation.Binary using (Rel)
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
      ; +-identity    to +ᵏ-identity
      ; +-identityˡ    to +ᵏ-identityˡ
      ; +-identityʳ    to +ᵏ-identityʳ
      ; +-assoc       to +ᵏ-assoc
      ; +-comm        to +ᵏ-comm
      ; *-cong        to *ᵏ-cong
      ; *-identity    to *ᵏ-identity
      ; *-identityˡ    to *ᵏ-identityˡ
      ; *-identityʳ    to *ᵏ-identityʳ
      ; *-assoc       to *ᵏ-assoc
      ; *-comm        to *ᵏ-comm
      ; zero          to *ᵏ-zero
      ; zeroˡ          to *ᵏ-zeroˡ
      ; zeroʳ          to *ᵏ-zeroʳ
      ; distrib       to *ᵏ-+ᵏ-distrib
      ; distribˡ      to *ᵏ-+ᵏ-distribˡ
      ; distribʳ      to *ᵏ-+ᵏ-distribʳ
      ; -‿distribˡ-*  to -ᵏ‿distribˡ-*ᵏ
      ; -‿distribʳ-*  to -ᵏ‿distribʳ-*ᵏ
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

  record IsVectorSpace (_+_ : Op₂ V) (_∙_ : K' → V → V) (-_ : Op₁ V) (0# : V) : Set (v ⊔ k ⊔ ℓ ⊔ ℓᵏ) where
    field
      isAbelianGroup : IsAbelianGroup _+_ 0# -_
      *ᵏ-∙-compat    : ∀ (a b : K') (u : V) -> ((a *ᵏ b) ∙ u) ≈ (a ∙ (b ∙ u))
      ∙-+-distrib    : ∀ (a : K') (u v : V) -> (a ∙ (u + v)) ≈ ((a ∙ u) + (a ∙ v))
      ∙-+ᵏ-distrib   : ∀ (a b : K') (u : V) -> ((a +ᵏ b) ∙ u) ≈ ((a ∙ u) + (b ∙ u))
      ∙-cong         : ∀ {a b : K'} {u v : V} -> a ≈ᵏ b -> u ≈ v -> (a ∙ u) ≈ (b ∙ v)
      ∙-identity     : ∀ (x : V) → (1ᵏ ∙ x) ≈ x
      ∙-absorbˡ       : ∀ (x : V) → (0ᵏ ∙ x) ≈ 0#

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

    open import Algebra.Properties.AbelianGroup (record { isAbelianGroup = isAbelianGroup }) public
      renaming
      ( ε⁻¹≈ε            to -0≈0
      ; ∙-cancelˡ        to +-cancelˡ
      ; ∙-cancelʳ        to +-cancelʳ
      ; ∙-cancel        to +-cancel
      ; identityˡ-unique to +-identityˡ-unique
      ; identityʳ-unique to +-identityʳ-unique
      ; identity-unique to +-identity-unique
      ; inverseˡ-unique  to +-inverseˡ-unique
      ; inverseʳ-unique  to +-inverseʳ-unique
      ; xyx⁻¹≈y          to x+y-x≈y
      ; ⁻¹-∙-comm        to -‿+-comm
      )

    open import Relation.Binary.EqReasoning setoid

    ∙-absorbʳ : ∀ (a : K') -> (a ∙ 0#) ≈ 0#
    ∙-absorbʳ a =
      begin
        a ∙ 0#
      ≈⟨ trans (∙-cong ≈ᵏ-refl (sym (∙-absorbˡ 0#))) (sym (*ᵏ-∙-compat a 0ᵏ 0#))  ⟩
        (a *ᵏ 0ᵏ) ∙ 0#
      ≈⟨ ∙-cong (*ᵏ-zeroʳ a) refl ⟩
        0ᵏ ∙ 0#
      ≈⟨ ∙-absorbˡ 0# ⟩
        0#
      ∎

    ∙-∙-comm : ∀ (a b : K') (u : V) -> (a ∙ (b ∙ u)) ≈ (b ∙ (a ∙ u))
    ∙-∙-comm a b u =
      begin
        a ∙ (b ∙ u)
      ≈⟨ sym (*ᵏ-∙-compat a b u) ⟩
        (a *ᵏ b) ∙ u
      ≈⟨ ∙-cong (*ᵏ-comm a b) refl ⟩
        (b *ᵏ a) ∙ u
      ≈⟨ *ᵏ-∙-compat b a u ⟩
        b ∙ (a ∙ u)
      ∎

    private
      lemma-inverseʳ : ∀ (u : V) -> (u + ((-ᵏ 1ᵏ) ∙ u)) ≈ 0#
      lemma-inverseʳ u =
        begin
          u + ((-ᵏ 1ᵏ) ∙ u)
        ≈⟨ +-cong (sym (∙-identity u)) refl ⟩
          (1ᵏ ∙ u) + ((-ᵏ 1ᵏ) ∙ u)
        ≈⟨ sym (∙-+ᵏ-distrib 1ᵏ (-ᵏ 1ᵏ) u) ⟩
          (1ᵏ +ᵏ (-ᵏ 1ᵏ)) ∙ u
        ≈⟨ ∙-cong (-ᵏ‿inverseʳ 1ᵏ) refl ⟩
          0ᵏ ∙ u
        ≈⟨ ∙-absorbˡ u ⟩
          0#
        ∎

    -1∙u≈-u : ∀ (u : V) -> ((-ᵏ 1ᵏ) ∙ u) ≈ (- u)
    -1∙u≈-u u =
      begin
        ((-ᵏ 1ᵏ) ∙ u)
      ≈⟨ +-inverseʳ-unique u ((-ᵏ 1ᵏ) ∙ u) (lemma-inverseʳ u) ⟩
        - u
      ∎
