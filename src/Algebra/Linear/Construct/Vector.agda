{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures.Bundles.Field

module Algebra.Linear.Construct.Vector
  {k ℓ} (K : Field k ℓ)
  where

open import Level using (_⊔_)
open import Data.Product using (_×_; _,_)
open import Data.Vec public hiding (sum)
import Data.Vec.Properties as VP
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
open import Data.Nat hiding (_⊔_) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin)

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

open import Algebra.Structures.Field.Utils K
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

private
  V : ℕ -> Set k
  V = Vec K'

splitAt' : ∀ {n} (i : ℕ) (j : ℕ) -> i +ℕ j ≡ n -> V n → V i × V j
splitAt' {0} 0 0 r [] = ([] , [])
splitAt' {suc n} 0 (suc j) r u = ([] , subst V (≡-sym r) u)
splitAt' {suc n} (suc i) j r (x ∷ xs) =
  let (xs₁ , xs₂) = splitAt' {n} i j (suc-injective r) xs
  in (x ∷ xs₁ , xs₂)

open PW public
  using ()
  renaming
    ( _∷_    to ≈-cons
    ; []     to ≈-null
    ; head   to ≈-head
    ; tail   to ≈-tail
    ; uncons to ≈-uncons
    ; lookup to ≈-lookup
    ; map      to ≈-map
    )

_≈ʰ_ : ∀ {m n} (xs : Vec K' m) (ys : Vec K' n) → Set (k ⊔ ℓ)
_≈ʰ_ = PW.Pointwise _≈ᵏ_

_≈_ : ∀ {n} (xs : Vec K' n) (ys : Vec K' n) → Set (k ⊔ ℓ)
_≈_ = _≈ʰ_

≈-isEquiv : ∀ {n} -> IsEquivalence (_≈_ {n})
≈-isEquiv {n} = PW.isEquivalence ≈ᵏ-isEquiv n

setoid : ℕ -> Setoid k (k ⊔ ℓ)
setoid n = record { isEquivalence = ≈-isEquiv {n} }

module _ {n} where
  open IsEquivalence (≈-isEquiv {n}) public
    using ()
    renaming
      ( refl  to ≈-refl
      ; sym   to ≈-sym
      ; trans to ≈-trans
      ; reflexive to ≈-reflexive
      )

0# : ∀ {n} → V n
0# {0}     = []
0# {suc n} = 0ᵏ ∷ 0# {n}

-_ : ∀ {n} → V n → V n
-_ = map (-ᵏ_)

infixr 25 _+_
_+_ : ∀ {n} → Op₂ (V n)
_+_ = zipWith _+ᵏ_

infixr 35 _∙_
_∙_ : ∀ {n} → K' → V n → V n
_∙_ k = map (k *ᵏ_)

{-
module HeterogeneousEquivalence where
  import Relation.Binary.Indexed.Heterogeneous as IH

  data _≈ʰ_ : IH.IRel V (k ⊔ ℓ) where
    ≈ʰ-null : ∀ {n p} {u : V n} {v : V p} -> n ≡ 0 -> p ≡ 0 -> u ≈ʰ v
    ≈ʰ-cons : ∀ {n p} {x y : K'} {u : V n} {v : V p} -> n ≡ p -> x ≈ᵏ y -> u ≈ʰ v -> (x ∷ u) ≈ʰ (y ∷ v)

  pattern ≈ʰ-zero = ≈ʰ-null ≡-refl ≡-refl

  ≈ʰ-refl : IH.Reflexive V _≈ʰ_
  ≈ʰ-refl {0} {[]} = ≈ʰ-zero
  ≈ʰ-refl {suc n} {x ∷ xs} = ≈ʰ-cons (≡-refl) ≈ᵏ-refl (≈ʰ-refl {n} {xs})

  ≈ʰ-sym : IH.Symmetric V _≈ʰ_
  ≈ʰ-sym {0} ≈ʰ-zero = ≈ʰ-zero
  ≈ʰ-sym {suc n} (≈ʰ-cons rn r rs) = ≈ʰ-cons (≡-sym rn) (≈ᵏ-sym r) (≈ʰ-sym rs)

  ≈ʰ-trans : IH.Transitive V _≈ʰ_
  ≈ʰ-trans (≈ʰ-null rn rp) (≈ʰ-null rn' rp') = ≈ʰ-null rn rp'
  ≈ʰ-trans (≈ʰ-cons rn r rs) (≈ʰ-cons rn' r' rs') = ≈ʰ-cons (≡-trans rn rn') (≈ᵏ-trans r r') (≈ʰ-trans rs rs')

  ≈ʰ-isEquiv : IH.IsIndexedEquivalence V _≈ʰ_
  ≈ʰ-isEquiv = record
    { refl  = ≈ʰ-refl
    ; sym   = ≈ʰ-sym
    ; trans = ≈ʰ-trans
    }

  ≈-to-≈ʰ : ∀ {n} {u v : V n} -> u ≈ v -> u ≈ʰ v
  ≈-to-≈ʰ {0} ≈-null = ≈ʰ-zero
  ≈-to-≈ʰ {suc n} (≈-cons r rs) = ≈ʰ-cons ≡-refl r (≈-to-≈ʰ rs)

  ≈ʰ-to-≈ : ∀ {n} {u v : V n} -> u ≈ʰ v -> u ≈ v
  ≈ʰ-to-≈ {0} {[]} {[]} ≈ʰ-zero = ≈-null
  ≈ʰ-to-≈ {suc n} (≈ʰ-cons _ r rs) = ≈-cons r (≈ʰ-to-≈ rs)

  ≈ʰ-tail : ∀ {n p} {x y : K'} {u : V n} {v : V p} -> (x ∷ u) ≈ʰ (x ∷ v) -> u ≈ʰ v
  ≈ʰ-tail (≈ʰ-cons _ _ r) = r

  indexedSetoid : IH.IndexedSetoid ℕ k (ℓ ⊔ k)
  indexedSetoid = record
    { Carrier       = V
    ; _≈_           = _≈ʰ_
    ; isEquivalence = ≈ʰ-isEquiv
    }
setoid : ℕ -> Setoid k (k ⊔ ℓ)
setoid n = record
  { Carrier       = V n
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquiv
  }
-}

++-identityˡ : ∀ {n} (u : V n) -> ([] ++ u) ≈ u
++-identityˡ _ = ≈-refl

++-cong : ∀ {n p} {u₁ v₁ : V n} {u₂ v₂ : V p}
        -> u₁ ≈ v₁ -> u₂ ≈ v₂ -> (u₁ ++ u₂) ≈ (v₁ ++ v₂)
++-cong  ≈-null        r₂ = r₂
++-cong (≈-cons r₁ rs₁) r₂ = ≈-cons r₁ (++-cong rs₁ r₂)

++-split : ∀ {n p} {u₁ v₁ : V n} {u₂ v₂ : V p}
        ->  (u₁ ++ u₂) ≈ (v₁ ++ v₂) -> (u₁ ≈ v₁ × u₂ ≈ v₂)
++-split {0} {p} {[]} {[]} r = ≈-null , r
++-split {suc n} {p} {x ∷ xs} {y ∷ ys} (≈-cons r rs) =
  let (r₁ , r₂) = ++-split {n} {p} rs
  in (≈-cons r r₁) , r₂

0++0≈0 : ∀ {n p} -> (0# {n} ++ 0# {p}) ≈ 0# {n +ℕ p}
0++0≈0 {zero} = ++-identityˡ 0#
0++0≈0 {suc n} = ≈-cons ≈ᵏ-refl (0++0≈0 {n})

{-
open HeterogeneousEquivalence

++-identityʳ-≈ʰ : ∀ {n} (u : V n) -> (u ++ []) ≈ʰ u
++-identityʳ-≈ʰ [] = ≈ʰ-refl
++-identityʳ-≈ʰ {suc n} (x ∷ xs) = ≈ʰ-cons (+ℕ-identityʳ n) ≈ᵏ-refl (++-identityʳ-≈ʰ {n} xs)

++-cong-≈ʰ : ∀ {n p} {u₁ v₁ : V n} {u₂ v₂ : V p}
           -> u₁ ≈ʰ v₁ -> u₂ ≈ʰ v₂ -> (u₁ ++ u₂) ≈ʰ (v₁ ++ v₂)
++-cong-≈ʰ r₁ r₂ = ≈-to-≈ʰ (++-cong (≈ʰ-to-≈ r₁) (≈ʰ-to-≈ r₂))

splitAt-identityˡ : ∀ {n} (u : V n) -> let (x₁ , x₂) = splitAt 0 z≤n u in (x₁ ≈ʰ []) × (x₂ ≈ʰ u)
splitAt-identityˡ {0}_ = ≈ʰ-zero , ≈ʰ-zero
splitAt-identityˡ {suc n} _ = ≈ʰ-zero , ≈ʰ-refl

splitAt-identityʳ : ∀ {n} (u : V n) -> let (x₁ , x₂) = splitAt n ≤-refl u in (x₁ ≈ʰ u) × (x₂ ≈ʰ [])
splitAt-identityʳ {0} [] = ≈ʰ-refl , ≈ʰ-refl
splitAt-identityʳ {suc n} (x ∷ xs) = ≈ʰ-cons ≡-refl ≈ᵏ-refl (proj₁ (splitAt-identityʳ xs))
                                   , ≈ʰ-null (n∸n≡0 (suc n)) ≡-refl

++-splitAt : ∀ {n} (k : ℕ) (r : k ≤ n) (u : V n) -> let (x₁ , x₂, _) = splitAt n u in (x₁ ++ x₂) ≡ u
++-splitAt {0} 0 r u = ≈ʰ-null (m+[n∸m]≡n r) ≡-refl
++-splitAt {suc n} 0 r (x ∷ xs) = ≈ʰ-refl
++-splitAt {suc n} (suc k) sk≤sn (x ∷ xs) =
  let k≤n = ≤-pred sk≤sn
  in ≈ʰ-cons (m+[n∸m]≡n k≤n) ≈ᵏ-refl (++-splitAt k k≤n xs)

splitAt-++ : ∀ {n p} (u : Vec n) (v : Vec p) ->
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

++-splitAt' : ∀ {n p} (u : Vec (n +ℕ p)) -> let (x₁ , x₂) = splitAt' n p ≡-refl u in x₁ ++ x₂ ≈ u
++-splitAt' {0} [] = ≈-null
++-splitAt' {0} (x ∷ xs) = ≈-refl
++-splitAt' {suc n} (x ∷ xs) = ≈-cons ≈ᵏ-refl (++-splitAt' {n} xs)

splitAt'-++ : ∀ {n p} (u : Vec n) (v : Vec p) ->
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
-}

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

*ᵏ-∙-compat : ∀ {n} (a b : K') (u : V n) -> ((a *ᵏ b) ∙ u) ≈ (a ∙ (b ∙ u))
*ᵏ-∙-compat a b [] = ≈-null
*ᵏ-∙-compat a b (x ∷ xs) = ≈-cons (*ᵏ-assoc a b x) (*ᵏ-∙-compat a b xs)

∙-+-distrib : ∀ {n} (a : K') (u v : V n) -> (a ∙ (u + v)) ≈ ((a ∙ u) + (a ∙ v))
∙-+-distrib a [] [] = ≈-null
∙-+-distrib a (x ∷ xs) (y ∷ ys) = ≈-cons (*ᵏ-+ᵏ-distribˡ a x y) (∙-+-distrib a xs ys)

∙-+ᵏ-distrib : ∀ {n} (a b : K') (u : V n) -> ((a +ᵏ b) ∙ u) ≈ ((a ∙ u) + (b ∙ u))
∙-+ᵏ-distrib a b [] = ≈-null
∙-+ᵏ-distrib a b (x ∷ u) = ≈-cons (*ᵏ-+ᵏ-distribʳ x a b) (∙-+ᵏ-distrib a b u)

∙-cong : ∀ {n} {a b : K'} {u v : V n} → a ≈ᵏ b -> u ≈ v -> (a ∙ u) ≈ (b ∙ v)
∙-cong rᵏ ≈-null = ≈-null
∙-cong rᵏ (≈-cons r rs) = ≈-cons (*ᵏ-cong rᵏ r) (∙-cong rᵏ rs)

∙-identity : ∀ {n} (x : V n) → (1ᵏ ∙ x) ≈ x
∙-identity [] = ≈-null
∙-identity (x ∷ xs) = ≈-cons (*ᵏ-identityˡ x) (∙-identity xs)

∙-absorbˡ : ∀ {n} (x : V n) → (0ᵏ ∙ x) ≈ 0#
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

+-++-distrib : ∀ {n p}
                 (u₁ : V n) (u₂ : V p)
                 (v₁ : V n) (v₂ : V p)
             -> ((u₁ ++ u₂) + (v₁ ++ v₂)) ≈ ((u₁ + v₁) ++ (u₂ + v₂))
+-++-distrib [] [] [] [] = ≈-null
+-++-distrib (x₁ ∷ xs₁) [] (y₁ ∷ ys₁) [] = ++-cong ≈-refl (+-++-distrib xs₁ [] ys₁ [])
+-++-distrib {0} {suc p} [] (x₂ ∷ xs₂) [] (y₂ ∷ ys₂) = ++-identityˡ ((x₂ +ᵏ y₂) ∷ (xs₂ + ys₂))
+-++-distrib (x₁ ∷ xs₁) u₂ (y₁ ∷ ys₁) v₂ =
  ≈-cons ≈ᵏ-refl (++-cong ≈-refl (+-++-distrib xs₁ u₂ ys₁ v₂))

∙-++-distrib : ∀ {n p} (a : K') (u : V n) (v : V p) -> (a ∙ (u ++ v)) ≈ ((a ∙ u) ++ (a ∙ v))
∙-++-distrib a [] v = ≈-refl
∙-++-distrib a (x ∷ xs) v = ≈-cons ≈ᵏ-refl (∙-++-distrib a xs v)

sum : ∀ {n} -> V n -> K'
sum = foldr _ _+ᵏ_ 0ᵏ

sum-tab : ∀ {n} -> (Fin n -> K') -> K'
sum-tab f = sum (tabulate f)

sum-cong : ∀ {n} {u v : V n} -> u ≈ v -> sum u ≈ᵏ sum v
sum-cong {0} PW.[] = ≈ᵏ-refl
sum-cong {suc n} (r PW.∷ rs) = +ᵏ-cong r (sum-cong {n} rs)

tabulate-cong-≡ : ∀ {n} {f g : Fin n -> K'} -> (∀ i -> f i ≡ g i) -> tabulate f ≡ tabulate g
tabulate-cong-≡ = VP.tabulate-cong

tabulate-cong : ∀ {n} {f g : Fin n -> K'} -> (∀ i -> f i ≈ᵏ g i) -> tabulate f ≈ tabulate g
tabulate-cong {0} r = PW.[]
tabulate-cong {suc n} r = r Fin.zero PW.∷ tabulate-cong (λ i → r (Fin.suc i))

sum-tab-cong : ∀ {n} {f g : Fin n -> K'} -> (∀ i -> f i ≈ᵏ g i) -> sum-tab f ≈ᵏ sum-tab g
sum-tab-cong r = sum-cong (tabulate-cong r)

*ᵏ-sum-tab-distribʳ : ∀ {n} (a : K') (f : Fin n -> K')
                    → (sum-tab f *ᵏ a) ≈ᵏ sum-tab (λ k -> f k *ᵏ a)
*ᵏ-sum-tab-distribʳ {0} a f = *ᵏ-zeroˡ a
*ᵏ-sum-tab-distribʳ {suc n} a f =
  begin
    sum-tab f *ᵏ a
  ≈⟨ *ᵏ-+ᵏ-distribʳ a (f Fin.zero) (sum-tab (λ k -> f (Fin.suc k))) ⟩
     (f Fin.zero *ᵏ a) +ᵏ (sum-tab (λ k -> f (Fin.suc k)) *ᵏ a)
  ≈⟨ +ᵏ-cong ≈ᵏ-refl  (*ᵏ-sum-tab-distribʳ a (λ k -> f (Fin.suc k))) ⟩
     sum-tab (λ k -> f k *ᵏ a)
  ∎
  where open import Relation.Binary.EqReasoning (Field.setoid K)

sum-assoc : ∀ {n} (f g : Fin n -> K')
          -> (sum-tab f +ᵏ sum-tab g) ≈ᵏ sum-tab (λ k -> f k +ᵏ g k)
sum-assoc {0} f g = +ᵏ-identityˡ 0ᵏ
sum-assoc {suc n} f g =
  begin
    sum-tab f +ᵏ sum-tab g
  ≡⟨⟩
    (f Fin.zero +ᵏ sum-tab {n} (λ k -> f (Fin.suc k))) +ᵏ (g Fin.zero +ᵏ sum-tab {n} (λ k -> g (Fin.suc k)))
  ≈⟨ +ᵏ-assoc (f Fin.zero) (sum-tab {n} (λ k -> f (Fin.suc k))) (g Fin.zero +ᵏ sum-tab {n} (λ k -> g (Fin.suc k))) ⟩
     f Fin.zero +ᵏ (sum-tab (λ k → f (Fin.suc k)) +ᵏ (g Fin.zero +ᵏ sum-tab (λ k → g (Fin.suc k))))
  ≈⟨ +ᵏ-cong ≈ᵏ-refl (+ᵏ-comm (sum-tab (λ k -> f (Fin.suc k))) ((g Fin.zero +ᵏ sum-tab (λ k → g (Fin.suc k))))) ⟩
     f Fin.zero +ᵏ ((g Fin.zero +ᵏ sum-tab (λ k → g (Fin.suc k))) +ᵏ sum-tab (λ k → f (Fin.suc k)))
  ≈⟨ +ᵏ-cong ≈ᵏ-refl (+ᵏ-assoc (g Fin.zero) (sum-tab (λ k -> g (Fin.suc k))) (sum-tab (λ k -> f (Fin.suc k)))) ⟩
     f Fin.zero +ᵏ (g Fin.zero +ᵏ (sum-tab (λ k → g (Fin.suc k)) +ᵏ sum-tab (λ k → f (Fin.suc k))))
  ≈⟨ ≈ᵏ-sym (+ᵏ-assoc (f Fin.zero) (g Fin.zero) (sum-tab (λ k → g (Fin.suc k)) +ᵏ sum-tab (λ k → f (Fin.suc k)))) ⟩
     (f Fin.zero +ᵏ g Fin.zero) +ᵏ (sum-tab (λ k → g (Fin.suc k)) +ᵏ sum-tab (λ k → f (Fin.suc k)))
  ≈⟨ +ᵏ-cong ≈ᵏ-refl (+ᵏ-comm (sum-tab λ k -> g (Fin.suc k)) (sum-tab λ k -> f (Fin.suc k))) ⟩
     (f Fin.zero +ᵏ g Fin.zero) +ᵏ (sum-tab (λ k → f (Fin.suc k)) +ᵏ sum-tab (λ k → g (Fin.suc k)))
  ≈⟨ +ᵏ-cong ≈ᵏ-refl (sum-assoc {n} (λ k -> f (Fin.suc k)) (λ k -> g (Fin.suc k))) ⟩
     sum-tab (λ k -> f k +ᵏ g k)
  ∎
  where open import Relation.Binary.EqReasoning (Field.setoid K)

sum-tab-0ᵏ : ∀ {n} -> sum-tab {n} (λ k -> 0ᵏ) ≈ᵏ 0ᵏ
sum-tab-0ᵏ {0} = ≈ᵏ-refl
sum-tab-0ᵏ {suc n} = ≈ᵏ-trans (+ᵏ-identityˡ (sum-tab {n} λ k -> 0ᵏ)) (sum-tab-0ᵏ {n})

sum-tab-swap : ∀ {n p} (f : Fin n -> Fin p -> K') (g : Fin n -> K')
             -> sum-tab (λ k′ -> sum-tab λ k -> f k k′ *ᵏ g k)
             ≈ᵏ sum-tab (λ k -> sum-tab λ k′ -> f k k′ *ᵏ g k)
sum-tab-swap {n} {0} f g = ≈ᵏ-sym (sum-tab-0ᵏ {n})
sum-tab-swap {n} {suc p} f g =
  begin
    sum-tab (λ k′ -> sum-tab λ k -> f k k′ *ᵏ g k)
  ≡⟨⟩
    (sum-tab λ k -> f k Fin.zero *ᵏ g k) +ᵏ (sum-tab λ k′ -> sum-tab λ k -> f k (Fin.suc k′) *ᵏ g k)
  ≈⟨ +ᵏ-cong ≈ᵏ-refl (sum-tab-swap {n} {p} (λ k k′ -> f k (Fin.suc k′)) g) ⟩
     sum-tab (λ k → f k Fin.zero *ᵏ g k) +ᵏ sum-tab (λ k → sum-tab (λ k′ → f k (Fin.suc k′) *ᵏ g k))
  ≈⟨ +ᵏ-cong ≈ᵏ-refl (sum-tab-cong λ k -> ≈ᵏ-sym (*ᵏ-sum-tab-distribʳ {p} (g k) λ k′ -> f k (Fin.suc k′))) ⟩
     sum-tab (λ k → f k Fin.zero *ᵏ g k) +ᵏ sum-tab (λ k → sum-tab (λ k′ → f k (Fin.suc k′)) *ᵏ g k)
  ≈⟨ sum-assoc (λ k -> f k Fin.zero *ᵏ g k) (λ k -> sum-tab (λ k′ -> f k (Fin.suc k′)) *ᵏ g k) ⟩
     sum-tab (λ k -> (f k Fin.zero *ᵏ g k) +ᵏ (sum-tab (λ k′ -> f k (Fin.suc k′)) *ᵏ g k))
  ≈⟨ sum-tab-cong (λ k -> ≈ᵏ-sym (*ᵏ-+ᵏ-distribʳ (g k) (f k Fin.zero) (sum-tab λ k′ -> f k (Fin.suc k′)))) ⟩
     sum-tab (λ k -> sum-tab (λ k′ -> f k k′) *ᵏ g k)
  ≈⟨ sum-tab-cong (λ k -> *ᵏ-sum-tab-distribʳ {suc p} (g k) (λ k′ -> f k k′)) ⟩
     sum-tab (λ k -> sum-tab λ k′ -> f k k′ *ᵏ g k)
  ∎
  where open import Relation.Binary.EqReasoning (Field.setoid K)

sum-tab-δ : ∀ {n} (f : Fin n -> K') (i : Fin n) -> sum-tab (λ k -> δ i k *ᵏ f k) ≈ᵏ f i
sum-tab-δ {suc n} f i@Fin.zero =
  begin
    sum-tab (λ k -> δ i k *ᵏ f k)
  ≡⟨⟩
    (δ i i *ᵏ f i) +ᵏ sum-tab (λ k -> δ i (Fin.suc k) *ᵏ f (Fin.suc k))
  ≈⟨ +ᵏ-cong (*ᵏ-identityˡ (f i))
     (sum-tab-cong (λ k -> ≈ᵏ-trans (*ᵏ-cong (δ-cancelˡ {n} k) ≈ᵏ-refl) (*ᵏ-zeroˡ (f (Fin.suc k))))) ⟩
    f i +ᵏ sum-tab {n} (λ k -> 0ᵏ)
  ≈⟨ ≈ᵏ-trans (+ᵏ-cong ≈ᵏ-refl (sum-tab-0ᵏ {n})) (+ᵏ-identityʳ (f i)) ⟩
    f i
  ∎
  where open import Relation.Binary.EqReasoning (Field.setoid K)
sum-tab-δ {suc n} f (Fin.suc i) =
  begin
    sum-tab (λ k -> δ (Fin.suc i) k *ᵏ f k)
  ≡⟨⟩
    (δ (Fin.suc i) (Fin.zero {suc n}) *ᵏ f Fin.zero) +ᵏ sum-tab (λ k -> δ (Fin.suc i) (Fin.suc k) *ᵏ f (Fin.suc k))
  ≈⟨ +ᵏ-cong (≈ᵏ-trans (*ᵏ-cong (δ-cancelʳ {p = suc n} (Fin.suc i)) ≈ᵏ-refl) (*ᵏ-zeroˡ (f Fin.zero))) ≈ᵏ-refl ⟩
    0ᵏ +ᵏ sum-tab (λ k → δ (Fin.suc i) (Fin.suc k) *ᵏ f (Fin.suc k))
  ≈⟨ +ᵏ-identityˡ (sum-tab λ k -> δ (Fin.suc i) (Fin.suc k) *ᵏ f (Fin.suc k)) ⟩
    sum-tab (λ k → δ (Fin.suc i) (Fin.suc k) *ᵏ f (Fin.suc k))
  ≈⟨ sum-tab-δ (λ k -> f (Fin.suc k)) i ⟩
    f (Fin.suc i)
  ∎
  where open import Relation.Binary.EqReasoning (Field.setoid K)

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
