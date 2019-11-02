open import Relation.Binary
open import Algebra.Linear.Structures.Field

open import Algebra.FunctionProperties

open import Data.Product
open import Data.Nat using (ℕ; zero; suc)

module Data.Linear.Vector
  {a k ℓ ℓᵏ} {K : Set k}
  {_≈ᵏ_ : Rel K ℓᵏ}
  (isEquivᵏ : IsEquivalence _≈ᵏ_)
  {_+ᵏ_ _*ᵏ_ : Op₂ K} {0ᵏ 1ᵏ : K} { -ᵏ_ : Op₁ K } {_⁻¹ᵏ : MultiplicativeInverse isEquivᵏ 0ᵏ}
  (isField : IsField isEquivᵏ _+ᵏ_ _*ᵏ_ 0ᵏ 1ᵏ -ᵏ_ _⁻¹ᵏ)
  where

open IsEquivalence isEquivᵏ renaming
  ( refl  to ≈ᵏ-refl
  ; sym   to ≈ᵏ-sym
  ; trans to ≈ᵏ-trans
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
  ; -‿cong       to -ᵏ‿cong
  ; -‿inverse    to -ᵏ‿inverse
  ; -‿inverseˡ    to -ᵏ‿inverseˡ
  ; -‿inverseʳ    to -ᵏ‿inverseʳ
  ; _-_           to _-ᵏ_
  ; _⁻¹-inverse    to _⁻¹ᵏ-inverse
  ; _⁻¹-involutive to _⁻¹ᵏ-involutive
  ; 0#-not-1#     to 0ᵏ-not-1ᵏ
  )

open import Level    using (_⊔_)

data Vector : ℕ → Set (k ⊔ a) where
  []  : Vector 0
  _∷_ : ∀ {n} → K → Vector n → Vector (suc n)

data _≈_ : ∀ {n} → Rel (Vector n) (ℓ ⊔ ℓᵏ) where
  ≈-null : [] ≈ []
  ≈-cons : ∀ {n} {x y : K} {xs ys : Vector n} → x ≈ᵏ y → xs ≈ ys → (x ∷ xs) ≈ (y ∷ ys)

≈-refl : ∀ {n} {u : Vector n} -> u ≈ u
≈-refl {u = []} = ≈-null
≈-refl {u = x ∷ xs} = ≈-cons ≈ᵏ-refl ≈-refl

≈-sym : ∀ {n} {u v : Vector n} -> u ≈ v -> v ≈ u
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

open import Algebra.Structures

infixr 25 _+_
infixr 30 _∷_

0# : ∀ {n} → Vector n
0# {0}     = []
0# {suc n} = 0ᵏ ∷ 0# {n}

-_ : ∀ {n} → Vector n → Vector n
-_ [] = []
-_ (x ∷ xs) = (-ᵏ x) ∷ (- xs)

_+_ : ∀ {n} → Op₂ (Vector n)
[] + [] = []
(x ∷ xs) + (y ∷ ys) = (x +ᵏ y) ∷ (xs + ys)

_•_ : ∀ {n} → K → Vector n → Vector n
k • [] = []
k • (x ∷ xs) = (k *ᵏ x) ∷ (k • xs)

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

•-absorb : ∀ {n} (x : Vector n) → (0ᵏ • x) ≈ 0#
•-absorb [] = ≈-null
•-absorb (x ∷ xs) = ≈-cons (*ᵏ-zeroˡ x) (•-absorb xs)

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

+-isMagma : ∀ {n} -> IsMagma (_≈_ {n}) _+_
+-isMagma = record
  { isEquivalence = ≈-isEquiv
  ; ∙-cong        = +-cong
  }

+-isSemigroup : ∀ {n} -> IsSemigroup (_≈_ {n}) _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-isMonoid : ∀ {n} -> IsMonoid (_≈_ {n}) _+_ 0#
+-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-isGroup : ∀ {n} -> IsGroup (_≈_ {n}) _+_ 0# -_
+-isGroup = record
  { isMonoid = +-isMonoid
  ; inverse  = -‿inverse
  ; ⁻¹-cong   = -‿cong
  }

+-isAbelianGroup : ∀ {n} -> IsAbelianGroup (_≈_ {n}) _+_ 0# -_
+-isAbelianGroup = record
  { isGroup = +-isGroup
  ; comm    = +-comm
  }

open import Algebra.Linear.Structures.VectorSpace  {a ⊔ k} {k} {ℓ ⊔ ℓᵏ} {ℓᵏ} {K = K} isField

+-•-isVectorSpace : ∀ {n} -> IsVectorSpace (≈-isEquiv {n}) _+_ _•_ -_ 0#
+-•-isVectorSpace = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; •-absorb         = •-absorb
  }
