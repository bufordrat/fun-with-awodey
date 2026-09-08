module FreeMonoid where

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning
open import Agda.Builtin.Sigma

record Monoid (A : Set) : Set where
  field
    _·_ : A → A → A
    𝟙 : A
    ·-assoc : ∀ { a b c : A } → ((a · b) · c) ≡ (a · (b · c))
    left-id : ∀ { a : A } → 𝟙 · a ≡ a
    right-id : ∀ { a : A } → a · 𝟙 ≡ a

record MonoidHomomorphism (A : Set) (B : Set) : Set where
  field
    h : A -> B
    source : Monoid A
    target : Monoid B
  open Monoid source renaming (_·_ to _·ₛ_; 𝟙 to 𝟙ₛ)
  open Monoid target renaming (_·_ to _·ₜ_; 𝟙 to 𝟙ₜ)
  field
    homo : ∀ { a b : A } → h (a ·ₛ b) ≡ h a ·ₜ h b

data List (A : Set) : Set where
  — : List A
  _::_ : A -> List A -> List A

_*_ : { A : Set } → List A -> List A -> List A
— * second = second
first * — = first
(x :: xs) * second = x :: (xs * second)

mkFreeMonoid : { A : Set } → Monoid (List A)
mkFreeMonoid a = {!!}
