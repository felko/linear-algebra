{-# OPTIONS --without-K --safe #-}

module Algebra.Linear.Core where

open import Relation.Binary
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)
open import Data.Fin using (Fin; suc; zero)

VectorAddition : ∀ {c} -> Set c -> Set c
VectorAddition V = V -> V -> V

ScalarMultiplication : ∀ {c k} -> Set k -> Set c -> Set (k ⊔ c)
ScalarMultiplication K V = K -> V -> V
