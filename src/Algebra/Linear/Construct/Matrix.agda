{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Construct.Matrix
  {k ℓ} (K : Field k ℓ)
  where

open import Level using (_⊔_)
open import Data.Product hiding (map)
open import Data.Fin using (Fin; toℕ; fromℕ)
open import Data.Nat hiding (_⊔_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (1+n≢0)

open import Relation.Binary
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
open import Algebra.Linear.Core

import Data.Vec.Properties as VP

import Algebra.Linear.Construct.Vector K as V
open V
  using (Vec; zipWith; replicate)
  renaming
    ( _+_ to _+v_
    ; _∙_ to _∙v_
    ; -_  to -v_
    )

open import Relation.Binary.PropositionalEquality as P
  using (_≡_; subst; subst-subst-sym; _≗_)
  renaming
  ( refl  to ≡-refl
  ; sym   to ≡-sym
  ; trans to ≡-trans
  )

import Algebra.Linear.Structures.VectorSpace as VS

open VS.VectorSpaceField K

open import Data.Nat.Properties
  using
    ( ≤-refl
    ; ≤-reflexive
    ; ≤-antisym
    ; n∸n≡0
    ; m+[n∸m]≡n
    ; m≤m+n
    ; suc-injective
    )
  renaming
    ( +-identityˡ to +ℕ-identityˡ
    ; +-identityʳ to +ℕ-identityʳ 
    )

Matrix : ℕ -> ℕ -> Set k
Matrix n p = Vec (Vec K' p) n

private
  M : ℕ -> ℕ -> Set k
  M = Matrix

_≈ʰ_ : ∀ {n p n' p'} (A : M n p) (B : M n' p') → Set (k ⊔ ℓ)
_≈ʰ_ = PW.Pointwise V._≈ʰ_

module _ {n p} where
  setoid : Setoid k (k ⊔ ℓ)
  setoid = record
    { Carrier       = M n p
    ; _≈_           = _≈ʰ_ {n} {p}
    ; isEquivalence = PW.isEquivalence (V.≈-isEquiv {p}) n
    }

  open Setoid setoid public
    renaming
      ( refl  to ≈-refl
      ; sym   to ≈-sym
      ; trans to ≈-trans
      ; reflexive to ≈-reflexive
      ; isEquivalence to ≈-isEquiv
      )

import Algebra.FunctionProperties as FP

tabulate : ∀ {n p} -> (Fin n -> Fin p -> K') -> M n p
tabulate f = V.tabulate λ i -> V.tabulate λ j -> f i j

tabulate⁺ : ∀ {n p} {f g : Fin n -> Fin p -> K'}
         -> (∀ i j -> f i j ≈ᵏ g i j)
         -> tabulate f ≈ tabulate g
tabulate⁺ {0} r = PW.[]
tabulate⁺ {suc n} {p} {f} {g} r =
  (PW.tabulate⁺ (r Fin.zero)) PW.∷ tabulate⁺ {n} {p} λ i j → r (Fin.suc i) j

fromVec : ∀ {n p} -> V.Vec K' (n *ℕ p) -> M n p
fromVec {0} V.[] = V.[]
fromVec {suc n} {p} xs =
  let (vp , vnp , _) = V.splitAt p xs
  in vp V.∷ fromVec {n} vnp

toVec : ∀ {n p} -> M n p -> V.Vec K' (n *ℕ p)
toVec {n} {p} = V.concat {m = p} {n = n}

concat∘fromVec : ∀ {n p} (v : V.Vec K' (n *ℕ p)) -> toVec {n} {p} (fromVec v) V.≈ v
concat∘fromVec {0} V.[] = PW.[]
concat∘fromVec {suc n} {p} v =
  let (vn , vnp , r) = V.splitAt p v
  in begin
    toVec {suc n} {p} (fromVec v)
  ≡⟨⟩
    vn V.++ toVec {n} {p} (fromVec vnp)
  ≈⟨ V.++-cong {p} {n *ℕ p} V.≈-refl (concat∘fromVec {n} {p} vnp) ⟩
    vn V.++ vnp
  ≈⟨ V.≈-sym (V.≈-reflexive r) ⟩
    v
  ∎
  where open import Relation.Binary.EqReasoning (V.setoid (suc n *ℕ p))

_++_ : ∀ {n p q} -> M n p -> M n q -> M n (p +ℕ q)
_++_ = zipWith V._++_

_‡_ : ∀ {n m p} -> M n p -> M m p -> M (n +ℕ m) p
_‡_ = V._++_

lookup : ∀ {n p} -> M n p -> Fin n -> Fin p -> K'
lookup A i j = V.lookup (V.lookup A i) j

_⟪_,_⟫ : ∀ {n p} -> M n p -> Fin n -> Fin p -> K'
_⟪_,_⟫ = lookup

tabulate∘lookup : ∀ {n p} (A : M n p) → tabulate (lookup A) ≡ A
tabulate∘lookup A =
  begin
    tabulate (lookup A)
  ≡⟨⟩
    V.tabulate (λ i -> V.tabulate λ j -> V.lookup (V.lookup A i) j)
  ≡⟨ VP.tabulate-cong (λ i → VP.tabulate∘lookup (V.lookup A i)) ⟩
    V.tabulate (λ i -> V.lookup A i)
  ≡⟨ VP.tabulate∘lookup A ⟩
    A
  ∎
  where open import Relation.Binary.PropositionalEquality as Eq
        open Eq.≡-Reasoning

lookup∘tabulate : ∀ {n p} (f : Fin n -> Fin p -> K') (i : Fin n) (j : Fin p)
                -> lookup (tabulate f) i j ≡ f i j
lookup∘tabulate {suc n} f i j =
  begin
    lookup (tabulate f) i j
  ≡⟨⟩
    V.lookup (V.lookup (V.tabulate λ i′ -> V.tabulate λ j′ -> f i′ j′) i) j
  ≡⟨ cong (λ u → V.lookup u j) (VP.lookup∘tabulate (λ i′ -> V.tabulate λ j′ -> f i′ j′) i) ⟩
    V.lookup (V.tabulate λ j′ -> f i j′) j
  ≡⟨ VP.lookup∘tabulate (λ j′ -> f i j′) j ⟩
    f i j
  ∎
  where open import Relation.Binary.PropositionalEquality as Eq
        open Eq.≡-Reasoning

tabulate-cong : ∀ {n p} {f g : Fin n -> Fin p -> K'} -> (∀ i j -> f i j ≡ g i j) -> tabulate f ≡ tabulate g
tabulate-cong {f = f} {g = g} r =
  begin
    tabulate f
  ≡⟨⟩
    V.tabulate (λ i -> V.tabulate λ j -> f i j)
  ≡⟨ VP.tabulate-cong (λ i → VP.tabulate-cong (λ j → r i j)) ⟩
    tabulate g
  ∎
  where open import Relation.Binary.PropositionalEquality as Eq
        open Eq.≡-Reasoning

transpose : ∀ {n p} -> M n p -> M p n
transpose A = tabulate λ i j -> A ⟪ j , i ⟫

_ᵀ : ∀ {n p} -> M n p -> M p n
_ᵀ = transpose

transpose-involutive : ∀ {n p} (A : M n p) -> ((A ᵀ) ᵀ) ≡ A
transpose-involutive A =
  begin
    ((A ᵀ)ᵀ)
  ≡⟨⟩
    (tabulate λ i j -> (tabulate λ i′ j′ -> A ⟪ j′ , i′ ⟫) ⟪ j , i ⟫)
  ≡⟨ tabulate-cong (λ i j → lookup∘tabulate (λ i′ j′ -> A ⟪ j′ , i′ ⟫) j i) ⟩
    (tabulate λ i j -> A ⟪ i , j ⟫)
  ≡⟨ tabulate∘lookup A ⟩
    A
  ∎
  where open import Relation.Binary.PropositionalEquality as Eq
        open Eq.≡-Reasoning

map : ∀ {n p} -> (K' -> K') -> M n p -> M n p
map f = V.map (V.map f)

mapRows : ∀ {n p q} -> (V.Vec K' p -> V.Vec K' q) -> M n p -> M n q
mapRows = V.map

mapCols : ∀ {n m p} -> (V.Vec K' n -> V.Vec K' m) -> M n p -> M m p
mapCols f A = (V.map f (A ᵀ)) ᵀ

map-cong : ∀ {n p} {f g : K' -> K'} -> f ≗ g -> map {n} {p} f ≗ map g
map-cong r = VP.map-cong (VP.map-cong r)

mapRows-cong : ∀ {n p q} {f g : V.Vec K' p -> V.Vec K' q}
             -> f ≗ g -> mapRows {n} f ≗ mapRows g
mapRows-cong = VP.map-cong

mapCols-cong : ∀ {n m p} {f g : V.Vec K' n -> V.Vec K' m}
             -> f ≗ g -> mapCols {n} {m} {p} f ≗ mapCols g
mapCols-cong r A = P.cong transpose (VP.map-cong r (transpose A))

open import Data.Nat.DivMod

_+_ : ∀ {n p} -> FP.Op₂ (M n p)
_+_ = zipWith V._+_

_∙_ : ∀ {n p} -> ScalarMultiplication K' (M n p)
_∙_ k = V.map (k V.∙_)

-_ : ∀ {n p} -> FP.Op₁ (M n p)
-_ = V.map V.-_

0# : ∀ {n p} -> M n p
0# = replicate V.0#

+-cong : ∀ {n p} {A B C D : M n p} -> A ≈ B -> C ≈ D -> (A + C) ≈ (B + D)
+-cong PW.[] PW.[] = PW.[]
+-cong (r₁ PW.∷ rs₁) (r₂ PW.∷ rs₂) = V.+-cong r₁ r₂ PW.∷ +-cong rs₁ rs₂

+-assoc : ∀ {n p} (A B C : M n p) -> ((A + B) + C) ≈ (A + (B + C))
+-assoc V.[] V.[] V.[] = PW.[]
+-assoc (u V.∷ us) (v V.∷ vs) (w V.∷ ws) =
  V.+-assoc u v w PW.∷ +-assoc us vs ws

+-identityˡ : ∀ {n p} (A : M n p) -> (0# + A) ≈ A
+-identityˡ V.[] = PW.[]
+-identityˡ (u V.∷ us) = V.+-identityˡ u PW.∷ +-identityˡ us

+-identityʳ : ∀ {n p} (A : M n p) -> (A + 0#) ≈ A
+-identityʳ V.[] = PW.[]
+-identityʳ (u V.∷ us) = V.+-identityʳ u PW.∷ +-identityʳ us

+-identity : ∀ {n p} -> ((∀ (A : M n p) -> ((0# + A) ≈ A)) × (∀ (A : M n p) -> ((A + 0#) ≈ A)))
+-identity = +-identityˡ , +-identityʳ

+-comm : ∀ {n p} (A B : M n p) -> (A + B) ≈ (B + A)
+-comm V.[] V.[] = PW.[]
+-comm (u V.∷ us) (v V.∷ vs) = (V.+-comm u v) PW.∷ (+-comm us vs)

*ᵏ-∙-compat : ∀ {n p} (a b : K') (A : M n p) -> ((a *ᵏ b) ∙ A) ≈ (a ∙ (b ∙ A))
*ᵏ-∙-compat a b V.[] = PW.[]
*ᵏ-∙-compat a b (u V.∷ us) = (V.*ᵏ-∙-compat a b u) PW.∷ (*ᵏ-∙-compat a b us)

∙-+-distrib : ∀ {n p} (a : K') (A B : M n p) -> (a ∙ (A + B)) ≈ ((a ∙ A) + (a ∙ B))
∙-+-distrib a V.[] V.[] = PW.[]
∙-+-distrib a (u V.∷ us) (v V.∷ vs) = (V.∙-+-distrib a u v) PW.∷ (∙-+-distrib a us vs)

∙-+ᵏ-distrib : ∀ {n p} (a b : K') (A : M n p) -> ((a +ᵏ b) ∙ A) ≈ ((a ∙ A) + (b ∙ A))
∙-+ᵏ-distrib a b V.[] = PW.[]
∙-+ᵏ-distrib a b (u V.∷ us) = (V.∙-+ᵏ-distrib a b u) PW.∷ (∙-+ᵏ-distrib a b us)

∙-cong : ∀ {n p} {a b : K'} {A B : M n p} → a ≈ᵏ b -> A ≈ B -> (a ∙ A) ≈ (b ∙ B)
∙-cong rᵏ PW.[] = PW.[]
∙-cong rᵏ (r PW.∷ rs) = (V.∙-cong rᵏ r) PW.∷ (∙-cong rᵏ rs)

∙-identity : ∀ {n p} (A : M n p) → (1ᵏ ∙ A) ≈ A
∙-identity V.[] = PW.[]
∙-identity (u V.∷ us) = (V.∙-identity u) PW.∷ (∙-identity us)

∙-absorbˡ : ∀ {n p} (A : M n p) → (0ᵏ ∙ A) ≈ 0#
∙-absorbˡ V.[] = PW.[]
∙-absorbˡ (u V.∷ us) = (V.∙-absorbˡ u) PW.∷ (∙-absorbˡ us)

-‿inverseˡ : ∀ {n p} (A : M n p) -> ((- A) + A) ≈ 0#
-‿inverseˡ V.[] = PW.[]
-‿inverseˡ (u V.∷ us) = (V.-‿inverseˡ u) PW.∷ (-‿inverseˡ us)

-‿inverseʳ : ∀ {n p} (A : M n p) -> (A + (- A)) ≈ 0#
-‿inverseʳ V.[] = PW.[]
-‿inverseʳ (u V.∷ us) = (V.-‿inverseʳ u) PW.∷ (-‿inverseʳ us)

-‿inverse : ∀ {n p} → (∀ (A : M n p) -> ((- A) + A) ≈ 0#) × (∀ (A : M n p) -> (A + (- A)) ≈ 0#)
-‿inverse = -‿inverseˡ , -‿inverseʳ

-‿cong : ∀ {n p} {A B : M n p} -> A ≈ B -> (- A) ≈ (- B)
-‿cong PW.[] = PW.[]
-‿cong (r PW.∷ rs) = (V.-‿cong r) PW.∷ (-‿cong rs)

concat-+ : ∀ {n p} (A B : M n p) -> V.concat (V.zipWith V._+_ A B) V.≈ (V.concat A) +v (V.concat B)
concat-+ {0} {p} V.[] V.[] =
  V.≈-trans (PW.concat⁺ {m = p} {p = 0} PW.[]) (V.≈-sym (V.+-identityˡ V.[]))
concat-+ {suc n} {p} (u V.∷ us) (v V.∷ vs) =
  begin
    V.concat (V.zipWith V._+_ (u V.∷ us) (v V.∷ vs))
  ≡⟨⟩
    (u V.+ v) V.++ V.concat (V.zipWith V._+_ us vs)
  ≈⟨ V.++-cong V.≈-refl (concat-+ {n} {p} us vs) ⟩
    (u V.+ v) V.++ (V.concat us V.+ V.concat vs)
  ≈⟨ V.≈-sym (V.+-distrib-++ u (V.concat us) v (V.concat vs)) ⟩
    (V.concat (u V.∷ us)) V.+ (V.concat (v V.∷ vs))
  ∎
  where open import Relation.Binary.EqReasoning (V.setoid (p +ℕ n *ℕ p))

concat-0# : ∀ {n p} -> V.concat (0# {n} {p}) V.≈ (V.0# {n *ℕ p})
concat-0# {0} = PW.[]
concat-0# {suc n} {p} =
  begin
    V.concat (0# {suc n} {p})
  ≡⟨⟩
    V.0# {p} V.++ V.concat (0# {n} {p})
  ≈⟨ PW.++⁺ V.≈-refl (concat-0# {n} {p}) ⟩
    V.0# {p} V.++ V.0# {n *ℕ p}
  ≈⟨ V.0++0≈0 {p} {n *ℕ p} ⟩
    V.0# {p +ℕ n *ℕ p}
  ∎
  where open import Relation.Binary.EqReasoning (V.setoid (p +ℕ n *ℕ p))

concat-∙ : ∀ {n p} (c : K') (A : M n p) -> V.concat (c ∙ A) V.≈ (c V.∙ V.concat A)
concat-∙ {0} c V.[] = PW.[]
concat-∙ {suc n} {p} c (u V.∷ us) =
  begin
    V.concat ((c V.∙ u) V.∷ (c ∙ us))
  ≡⟨⟩
    (c V.∙ u) V.++ (V.concat (c ∙ us))
  ≈⟨ V.++-cong V.≈-refl (concat-∙ {n} {p} c us) ⟩
    (c V.∙ u) V.++ (c V.∙ V.concat us)
  ≈⟨ V.≈-sym (V.∙-distrib-++ c u (V.concat us)) ⟩
    c V.∙ V.concat (u V.∷ us)
  ∎
  where open import Relation.Binary.EqReasoning (V.setoid (p +ℕ n *ℕ p))

module _ {n p} where
  open IsEquivalence (≈-isEquiv {n} {p}) public
    using ()
    renaming
      ( refl  to ≈-refl
      ; sym   to ≈-sym
      ; trans to ≈-trans
      )

  open FP (_≈_ {n} {p})

  open import Algebra.Structures (_≈_ {n} {p})
  open import Algebra.Linear.Structures.Bundles

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

  open VS K

  isVectorSpace : VS.IsVectorSpace K (_≈_ {n}) _+_ _∙_ -_ 0#
  isVectorSpace = record
    { isAbelianGroup  = isAbelianGroup
    ; *ᵏ-∙-compat     = *ᵏ-∙-compat
    ; ∙-+-distrib     = ∙-+-distrib
    ; ∙-+ᵏ-distrib    = ∙-+ᵏ-distrib
    ; ∙-cong          = ∙-cong
    ; ∙-identity      = ∙-identity
    ; ∙-absorbˡ        = ∙-absorbˡ
    }

  vectorSpace : VectorSpace K k (k ⊔ ℓ)
  vectorSpace = record { isVectorSpace = isVectorSpace }

  open import Algebra.Linear.Structures.FiniteDimensional K
  open import Algebra.Linear.Morphism.VectorSpace K
  open import Algebra.Linear.Morphism.Bundles K

  open import Algebra.Morphism.Definitions (M n p) (Vec K' (n *ℕ p)) V._≈_
  open import Algebra.Linear.Morphism.Definitions K (M n p) (Vec K' (n *ℕ p)) V._≈_
  import Relation.Binary.Morphism.Definitions (M n p) (Vec K' (n *ℕ p)) as R
  open import Function
  open import Relation.Binary.EqReasoning (V.setoid (n *ℕ p))

  ⟦_⟧ : M n p -> Vec K' (n *ℕ p)
  ⟦_⟧ = V.concat

  ⟦⟧-cong : R.Homomorphic₂ _≈_ (V._≈_ {n *ℕ p}) ⟦_⟧
  ⟦⟧-cong = PW.concat⁺

  +-homo : Homomorphic₂ ⟦_⟧ _+_ _+v_
  +-homo = concat-+

  0#-homo : Homomorphic₀ ⟦_⟧ 0# V.0#
  0#-homo = concat-0# {n} {p}

  ∙-homo : ScalarHomomorphism ⟦_⟧ _∙_ _∙v_
  ∙-homo = concat-∙

  ⟦⟧-injective : Injective (_≈_ {n} {p}) (V._≈_ {n *ℕ p}) ⟦_⟧
  ⟦⟧-injective {A} {B} r = PW.concat⁻ A B r

  ⟦⟧-surjective : Surjective (_≈_ {n} {p}) (V._≈_ {n *ℕ p}) ⟦_⟧
  ⟦⟧-surjective v = fromVec {n} {p} v , concat∘fromVec {n} {p} v

  embed : LinearIsomorphism vectorSpace (V.vectorSpace {n *ℕ p})
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

  isFiniteDimensional : IsFiniteDimensional _≈_ _+_ _∙_ -_ 0# (n *ℕ p)
  isFiniteDimensional = record
    { isVectorSpace = isVectorSpace
    ; embed         = embed
    }
