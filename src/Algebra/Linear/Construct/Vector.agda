{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Construct.Vector
  {k ℓ} (K : Field k ℓ)
  where

open import Level using (_⊔_)
open import Data.Product
open import Data.Nat hiding (_⊔_) renaming (_+_ to _+ℕ_)

open import Relation.Binary
open import Algebra.Linear.Core
open import Algebra.FunctionProperties


open import Relation.Binary.PropositionalEquality as P
  using (_≡_; subst; subst-subst-sym)
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

data Vector : ℕ → Set k where
  []  : Vector 0
  _∷_ : ∀ {n} → K' → Vector n → Vector (suc n)

infixr 40 _∷_

infixl 30 _++_
_++_ : ∀ {n p} -> Vector n -> Vector p -> Vector (n +ℕ p)
[] ++ v = v
(x ∷ xs) ++ v = x ∷ (xs ++ v)

splitAt : ∀ {n} (k : ℕ) -> k ≤ n -> Vector n → Vector k × Vector (n ∸ k)
splitAt {0} 0 _ [] =  ([] , [])
splitAt {suc n} 0 _ u = ([] , u)
splitAt {suc n} (suc k) sk≤sn (x ∷ xs) =
  let (xs₁ , xs₂) = splitAt {n} k (≤-pred sk≤sn) xs
  in (x ∷ xs₁ , xs₂)

splitAt' : ∀ {n} (i : ℕ) (j : ℕ) -> i +ℕ j ≡ n -> Vector n → Vector i × Vector j
splitAt' {0} 0 0 r [] = ([] , [])
splitAt' {suc n} 0 (suc j) r u = ([] , subst Vector (≡-sym r) u)
splitAt' {suc n} (suc i) j r (x ∷ xs) =
  let (xs₁ , xs₂) = splitAt' {n} i j (suc-injective r) xs
  in (x ∷ xs₁ , xs₂)

data _≈_ : ∀ {n} -> Rel (Vector n) (k ⊔ ℓ) where
  ≈-null : [] ≈ []
  ≈-cons : ∀ {n} {x y : K'} {xs ys : Vector n} → x ≈ᵏ y → xs ≈ ys → x ∷ xs ≈ y ∷ ys

≈-refl : ∀ {n} {u : Vector n} -> u ≈ u
≈-refl {u = []} = ≈-null
≈-refl {u = x ∷ xs} = ≈-cons ≈ᵏ-refl ≈-refl

≈-sym : ∀ {n} {u v : Vector n} -> u ≈ v -> v ≈ u
≈-sym ≈-null        = ≈-null
≈-sym (≈-cons r rs) = ≈-cons (≈ᵏ-sym r) (≈-sym rs)

≈-trans : ∀ {n} {u v w : Vector n} → u ≈ v → v ≈ w → u ≈ w
≈-trans ≈-null ≈-null = ≈-null
≈-trans (≈-cons r₁ rs₁) (≈-cons r₂ rs₂) = ≈-cons (≈ᵏ-trans r₁ r₂) (≈-trans rs₁ rs₂)

≈-isEquiv : ∀ {n} -> IsEquivalence (_≈_ {n})
≈-isEquiv = record
  { refl  =  ≈-refl
  ; sym   =  ≈-sym
  ; trans =  ≈-trans
  }

0# : ∀ {n} → Vector n
0# {0}     = []
0# {suc n} = 0ᵏ ∷ 0# {n}

-_ : ∀ {n} → Vector n → Vector n
-_ [] = []
-_ (x ∷ xs) = (-ᵏ x) ∷ (- xs)


infixr 25 _+_
_+_ : ∀ {n} → Op₂ (Vector n)
[] + [] = []
(x ∷ xs) + (y ∷ ys) = (x +ᵏ y) ∷ (xs + ys)

infixr 35 _∙_
_∙_ : ∀ {n} → K' → Vector n → Vector n
k ∙ [] = []
k ∙ (x ∷ xs) = (k *ᵏ x) ∷ (k ∙ xs)


module HeterogeneousEquivalence where
  import Relation.Binary.Indexed.Heterogeneous as IH

  data _≈ʰ_ : IH.IRel Vector (k ⊔ ℓ) where
    ≈ʰ-null : ∀ {n p} {u : Vector n} {v : Vector p} -> n ≡ 0 -> p ≡ 0 -> u ≈ʰ v
    ≈ʰ-cons : ∀ {n p} {x y : K'} {u : Vector n} {v : Vector p} -> n ≡ p -> x ≈ᵏ y -> u ≈ʰ v -> x ∷ u ≈ʰ y ∷ v

  pattern ≈ʰ-zero = ≈ʰ-null ≡-refl ≡-refl

  ≈ʰ-refl : IH.Reflexive Vector _≈ʰ_
  ≈ʰ-refl {0} {[]} = ≈ʰ-zero
  ≈ʰ-refl {suc n} {x ∷ xs} = ≈ʰ-cons (≡-refl) ≈ᵏ-refl (≈ʰ-refl {n} {xs})

  ≈ʰ-sym : IH.Symmetric Vector _≈ʰ_
  ≈ʰ-sym {0} ≈ʰ-zero = ≈ʰ-zero
  ≈ʰ-sym {suc n} (≈ʰ-cons rn r rs) = ≈ʰ-cons (≡-sym rn) (≈ᵏ-sym r) (≈ʰ-sym rs)

  ≈ʰ-trans : IH.Transitive Vector _≈ʰ_
  ≈ʰ-trans (≈ʰ-null rn rp) (≈ʰ-null rn' rp') = ≈ʰ-null rn rp'
  ≈ʰ-trans (≈ʰ-cons rn r rs) (≈ʰ-cons rn' r' rs') = ≈ʰ-cons (≡-trans rn rn') (≈ᵏ-trans r r') (≈ʰ-trans rs rs')

  ≈ʰ-isEquiv : IH.IsIndexedEquivalence Vector _≈ʰ_
  ≈ʰ-isEquiv = record
    { refl  = ≈ʰ-refl
    ; sym   = ≈ʰ-sym
    ; trans = ≈ʰ-trans
    }

  ≈-to-≈ʰ : ∀ {n} {u v : Vector n} -> u ≈ v -> u ≈ʰ v
  ≈-to-≈ʰ {0} ≈-null = ≈ʰ-zero
  ≈-to-≈ʰ {suc n} (≈-cons r rs) = ≈ʰ-cons ≡-refl r (≈-to-≈ʰ rs)

  ≈ʰ-to-≈ : ∀ {n} {u v : Vector n} -> u ≈ʰ v -> u ≈ v
  ≈ʰ-to-≈ {0} {[]} {[]} ≈ʰ-zero = ≈-null
  ≈ʰ-to-≈ {suc n} (≈ʰ-cons _ r rs) = ≈-cons r (≈ʰ-to-≈ rs)

  ≈ʰ-tail : ∀ {n p} {x y : K'} {u : Vector n} {v : Vector p} -> x ∷ u ≈ʰ x ∷ v -> u ≈ʰ v
  ≈ʰ-tail (≈ʰ-cons _ _ r) = r

  indexedSetoid : IH.IndexedSetoid ℕ k (ℓ ⊔ k)
  indexedSetoid = record
    { Carrier       = Vector
    ; _≈_           = _≈ʰ_
    ; isEquivalence = ≈ʰ-isEquiv
    }

setoid : ℕ -> Setoid k (k ⊔ ℓ)
setoid n = record
  { Carrier       = Vector n
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquiv
  }

++-identityˡ : ∀ {n} (u : Vector n) -> [] ++ u ≈ u
++-identityˡ _ = ≈-refl

open HeterogeneousEquivalence

++-identityʳ-≈ʰ : ∀ {n} (u : Vector n) -> u ++ [] ≈ʰ u
++-identityʳ-≈ʰ [] = ≈ʰ-refl
++-identityʳ-≈ʰ {suc n} (x ∷ xs) = ≈ʰ-cons (+ℕ-identityʳ n) ≈ᵏ-refl (++-identityʳ-≈ʰ {n} xs)

++-cong : ∀ {n p} {u₁ v₁ : Vector n} {u₂ v₂ : Vector p}
        -> u₁ ≈ v₁ -> u₂ ≈ v₂ -> u₁ ++ u₂ ≈ v₁ ++ v₂
++-cong  ≈-null        r₂ = r₂
++-cong (≈-cons r₁ rs₁) r₂ = ≈-cons r₁ (++-cong rs₁ r₂)

++-split : ∀ {n p} {u₁ v₁ : Vector n} {u₂ v₂ : Vector p}
        ->  u₁ ++ u₂ ≈ v₁ ++ v₂ -> (u₁ ≈ v₁ × u₂ ≈ v₂)
++-split {0} {p} {[]} {[]} r = ≈-null , r
++-split {suc n} {p} {x ∷ xs} {y ∷ ys} (≈-cons r rs) =
  let (r₁ , r₂) = ++-split {n} {p} rs
  in (≈-cons r r₁) , r₂

++-cong-≈ʰ : ∀ {n p} {u₁ v₁ : Vector n} {u₂ v₂ : Vector p}
           -> u₁ ≈ʰ v₁ -> u₂ ≈ʰ v₂ -> u₁ ++ u₂ ≈ʰ v₁ ++ v₂
++-cong-≈ʰ r₁ r₂ = ≈-to-≈ʰ (++-cong (≈ʰ-to-≈ r₁) (≈ʰ-to-≈ r₂))

0++0≈0 : ∀ {n p} -> 0# {n} ++ 0# {p} ≈ 0# {n +ℕ p}
0++0≈0 {zero} = ++-identityˡ 0#
0++0≈0 {suc n} = ≈-cons ≈ᵏ-refl (0++0≈0 {n})

splitAt-identityˡ : ∀ {n} (u : Vector n) -> let (x₁ , x₂) = splitAt 0 z≤n u in (x₁ ≈ʰ []) × (x₂ ≈ʰ u)
splitAt-identityˡ {0}_ = ≈ʰ-zero , ≈ʰ-zero
splitAt-identityˡ {suc n} _ = ≈ʰ-zero , ≈ʰ-refl

splitAt-identityʳ : ∀ {n} (u : Vector n) -> let (x₁ , x₂) = splitAt n ≤-refl u in (x₁ ≈ʰ u) × (x₂ ≈ʰ [])
splitAt-identityʳ {0} [] = ≈ʰ-refl , ≈ʰ-refl
splitAt-identityʳ {suc n} (x ∷ xs) = ≈ʰ-cons ≡-refl ≈ᵏ-refl (proj₁ (splitAt-identityʳ xs))
                                   , ≈ʰ-null (n∸n≡0 (suc n)) ≡-refl

++-splitAt : ∀ {n} (k : ℕ) (r : k ≤ n) (u : Vector n) -> let (x₁ , x₂) = splitAt k r u in x₁ ++ x₂ ≈ʰ u
++-splitAt {0} 0 r u = ≈ʰ-null (m+[n∸m]≡n r) ≡-refl
++-splitAt {suc n} 0 r (x ∷ xs) = ≈ʰ-refl
++-splitAt {suc n} (suc k) sk≤sn (x ∷ xs) =
  let k≤n = ≤-pred sk≤sn
  in ≈ʰ-cons (m+[n∸m]≡n k≤n) ≈ᵏ-refl (++-splitAt k k≤n xs)

splitAt-++ : ∀ {n p} (u : Vector n) (v : Vector p) ->
  let (u' , v') = splitAt n (m≤m+n n p) (u ++ v) in (u ≈ʰ u') × (v ≈ʰ v')
splitAt-++ {0} {0} [] [] =  ≈ʰ-zero , ≈ʰ-zero
splitAt-++ {0} {suc p} [] (y ∷ ys) = ≈ʰ-zero , ≈ʰ-refl
splitAt-++ {suc n} {0} (x ∷ xs) [] =
  let (rxs , rv) = splitAt-++ xs []
  in ≈ʰ-cons ≡-refl ≈ᵏ-refl rxs , rv
splitAt-++ {suc n} {suc p} (x ∷ xs) (y ∷ ys) =
  let (u' , v') = splitAt (suc n) (m≤m+n (suc n) (suc p)) (x ∷ xs ++ y ∷ ys)
      (ru , rys) = splitAt-++ {suc n} {p} (x ∷ xs) ys
      (rxs , rv) = splitAt-++ {n} {suc p} xs (y ∷ ys)
  in ≈ʰ-cons ≡-refl ≈ᵏ-refl rxs , rv

++-splitAt' : ∀ {n p} (u : Vector (n +ℕ p)) -> let (x₁ , x₂) = splitAt' n p ≡-refl u in x₁ ++ x₂ ≈ u
++-splitAt' {0} [] = ≈-null
++-splitAt' {0} (x ∷ xs) = ≈-refl
++-splitAt' {suc n} (x ∷ xs) = ≈-cons ≈ᵏ-refl (++-splitAt' {n} xs)

splitAt'-++ : ∀ {n p} (u : Vector n) (v : Vector p) ->
  let (u' , v') = splitAt' n p ≡-refl (u ++ v) in (u ≈ u') × (v ≈ v')
splitAt'-++ {0} {0} [] [] =  ≈-null , ≈-null
splitAt'-++ {0} {suc p} [] (y ∷ ys) = ≈-null , ≈-refl
splitAt'-++ {suc n} {0} (x ∷ xs) [] =
  let (rxs , rv) = splitAt'-++ xs []
  in ≈-cons ≈ᵏ-refl rxs , rv
splitAt'-++ {suc n} {suc p} (x ∷ xs) (y ∷ ys) =
  let (u' , v') = splitAt' (suc n) (suc p) ≡-refl (x ∷ xs ++ y ∷ ys)
      (ru , rys) = splitAt'-++ {suc n} {p} (x ∷ xs) ys
      (rxs , rv) = splitAt'-++ {n} {suc p} xs (y ∷ ys)
  in ≈-cons ≈ᵏ-refl rxs , rv

+-cong : ∀ {n} → Congruent₂ (_≈_ {n}) _+_
+-cong ≈-null ≈-null = ≈-null
+-cong (≈-cons r₁ rs₁) (≈-cons r₂ rs₂) = ≈-cons (+ᵏ-cong r₁ r₂) (+-cong rs₁ rs₂)

+-assoc : ∀ {n} → Associative (_≈_ {n}) _+_
+-assoc [] [] [] = ≈-null
+-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = ≈-cons (+ᵏ-assoc x y z) (+-assoc xs ys zs)

+-identityˡ : ∀ {n} → LeftIdentity (_≈_ {n}) 0# _+_
+-identityˡ [] = ≈-null
+-identityˡ (x ∷ xs) = ≈-cons (+ᵏ-identityˡ x) (+-identityˡ xs)

+-identityʳ : ∀ {n} → RightIdentity (_≈_ {n}) 0# _+_
+-identityʳ [] = ≈-null
+-identityʳ (x ∷ xs) = ≈-cons (+ᵏ-identityʳ x) (+-identityʳ xs)

+-identity : ∀ {n} → Identity (_≈_ {n}) 0# _+_
+-identity = +-identityˡ , +-identityʳ

+-comm : ∀ {n} -> Commutative (_≈_ {n}) _+_
+-comm [] [] = ≈-null
+-comm (x ∷ xs) (y ∷ ys) = ≈-cons (+ᵏ-comm x y) (+-comm xs ys)

*ᵏ-∙-compat : ∀ {n} (a b : K') (u : Vector n) -> ((a *ᵏ b) ∙ u) ≈ (a ∙ (b ∙ u))
*ᵏ-∙-compat a b [] = ≈-null
*ᵏ-∙-compat a b (x ∷ xs) = ≈-cons (*ᵏ-assoc a b x) (*ᵏ-∙-compat a b xs)

∙-+-distrib : ∀ {n} (a : K') (u v : Vector n) -> (a ∙ (u + v)) ≈ ((a ∙ u) + (a ∙ v))
∙-+-distrib a [] [] = ≈-null
∙-+-distrib a (x ∷ xs) (y ∷ ys) = ≈-cons (*ᵏ-+ᵏ-distribˡ a x y) (∙-+-distrib a xs ys)

∙-+ᵏ-distrib : ∀ {n} (a b : K') (u : Vector n) -> ((a +ᵏ b) ∙ u) ≈ ((a ∙ u) + (b ∙ u))
∙-+ᵏ-distrib a b [] = ≈-null
∙-+ᵏ-distrib a b (x ∷ u) = ≈-cons (*ᵏ-+ᵏ-distribʳ x a b) (∙-+ᵏ-distrib a b u)

∙-cong : ∀ {n} {a b : K'} {u v : Vector n} → a ≈ᵏ b -> u ≈ v -> (a ∙ u) ≈ (b ∙ v)
∙-cong rᵏ ≈-null = ≈-null
∙-cong rᵏ (≈-cons r rs) = ≈-cons (*ᵏ-cong rᵏ r) (∙-cong rᵏ rs)

∙-identity : ∀ {n} (x : Vector n) → (1ᵏ ∙ x) ≈ x
∙-identity [] = ≈-null
∙-identity (x ∷ xs) = ≈-cons (*ᵏ-identityˡ x) (∙-identity xs)

∙-absorbˡ : ∀ {n} (x : Vector n) → (0ᵏ ∙ x) ≈ 0#
∙-absorbˡ [] = ≈-null
∙-absorbˡ (x ∷ xs) = ≈-cons (*ᵏ-zeroˡ x) (∙-absorbˡ xs)

-‿inverseˡ : ∀ {n} → LeftInverse  (_≈_ {n}) 0# -_ _+_
-‿inverseˡ [] = ≈-null
-‿inverseˡ (x ∷ xs) = ≈-cons (-ᵏ‿inverseˡ x) (-‿inverseˡ xs)

-‿inverseʳ : ∀ {n} → RightInverse (_≈_ {n}) 0# -_ _+_
-‿inverseʳ [] = ≈-null
-‿inverseʳ (x ∷ xs) = ≈-cons (-ᵏ‿inverseʳ x) (-‿inverseʳ xs)

-‿inverse : ∀ {n} → Inverse (_≈_ {n}) 0# -_ _+_
-‿inverse = -‿inverseˡ , -‿inverseʳ

-‿cong : ∀ {n} -> Congruent₁ (_≈_ {n}) -_
-‿cong ≈-null = ≈-null
-‿cong (≈-cons r rs) = ≈-cons (-ᵏ‿cong r) (-‿cong rs)

+-distrib-++ : ∀ {n p}
                 (u₁ : Vector n) (u₂ : Vector p)
                 (v₁ : Vector n) (v₂ : Vector p)
             -> (u₁ ++ u₂) + (v₁ ++ v₂) ≈ (u₁ + v₁) ++ (u₂ + v₂)
+-distrib-++ [] [] [] [] = ≈-null
+-distrib-++ (x₁ ∷ xs₁) [] (y₁ ∷ ys₁) [] = ++-cong ≈-refl (+-distrib-++ xs₁ [] ys₁ [])
+-distrib-++ {0} {suc p} [] (x₂ ∷ xs₂) [] (y₂ ∷ ys₂) = ++-identityˡ ((x₂ +ᵏ y₂) ∷ (xs₂ + ys₂))
+-distrib-++ (x₁ ∷ xs₁) u₂ (y₁ ∷ ys₁) v₂ =
  ≈-cons ≈ᵏ-refl (++-cong ≈-refl (+-distrib-++ xs₁ u₂ ys₁ v₂))

∙-distrib-++ : ∀ {n p} (a : K') (u : Vector n) (v : Vector p) -> a ∙ (u ++ v) ≈ a ∙ u ++ a ∙ v
∙-distrib-++ a [] v = ≈-refl
∙-distrib-++ a (x ∷ xs) v = ≈-cons ≈ᵏ-refl (∙-distrib-++ a xs v)

module _ {n} where
  open import Algebra.Structures (_≈_ {n})
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

  open import Algebra.Linear.Morphism.VectorSpace K

  open import Algebra.Linear.Morphism.Bundles K

  open import Function

  embed : LinearIsomorphism vectorSpace vectorSpace
  embed = record
    { ⟦_⟧ = id
    ; isLinearIsomorphism = record
        { isLinearMonomorphism = record
            { isLinearMap = record
                { isAbelianGroupMorphism = record
                    { gp-homo = record
                        { mn-homo = record
                          { sm-homo = record
                              { ⟦⟧-cong = id
                              ; ∙-homo = λ x y → ≈-refl
                              }
                          ; ε-homo = ≈-refl
                          }
                        }
                    }
                ; ∙-homo = λ c u → ≈-refl
                }
            ; injective = id
            }
        ; surjective = λ y → y , ≈-refl
        }
    }
