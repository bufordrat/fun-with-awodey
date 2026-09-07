module FreeMonoid where

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

record Monoid (A : Set) : Set where
  field
    _·_ : A → A → A
    𝟙 : A
    ·-assoc : ∀ { a b c } → ((a · b) · c) ≡ (a · (b · c))
    left-id : ∀ { a } → 𝟙 · a ≡ a
    right-id : ∀ { a } → a · 𝟙 ≡ a

