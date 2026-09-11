module FreeMonoid where

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

record Monoid (A : Set) : Set where
  field
    _·_ : A → A → A
    𝟙 : A
    ·-assoc : ∀ { a b c : A } → (a · b) · c ≡ a · (b · c)
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
(x :: xs) * second = x :: (xs * second)

generate : { A : Set } → Monoid (List A)
generate { A } =
  record { _·_ = _*_ ;
           𝟙 = — ;
           ·-assoc = {!!} ;
           left-id = refl ;
           right-id = *-satisfies-right-id 
         }
  where
    *-satisfies-right-id : { a : List A } → (a * —) ≡ a
    *-satisfies-right-id { — } = {!!}
    *-satisfies-right-id { x :: xs } =
      begin
        (x :: xs) * —
      ≡⟨ refl ⟩
        x :: (xs * —)
      ≡⟨ {!!} ⟩
        x :: xs
      ∎

-- this doesn't build

-- *-is-assoc : { A : Set } →
--              { a b c : List A } →
--              (a * b) * c ≡ a * (b * c)
-- *-is-assoc { a } { b } { c } =
--   begin_
--     (a * b) * c
--   ≡⟨ ? ⟩
--      a * (b * c)
--   ∎


-- use second branch of _*_ definition to do this equational reasoning:

-- ((h :: t) * y) * z
-- (h :: (t * y)) * z
-- h :: ((t * y) * z)

-- ...?...

-- h :: (t * (y * z))
-- (h :: t) * (y * z)
