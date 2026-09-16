module FreeMonoid where

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

-- there's a thing where you can make all those implicit foralls for
-- one using "private" syntax; figure out how to do that

-- you might need to do in within the definition of the record type

-- private

record Monoid (A : Set) : Set where
  field
    _·_ : A → A → A
    𝟙 : A
    ·-assoc : ∀ (a b c : A) → (a · b) · c ≡ a · (b · c)
    left-id : ∀ (a : A) → 𝟙 · a ≡ a
    right-id : ∀ (a : A) → a · 𝟙 ≡ a

record MonoidHomomorphism (A : Set) (B : Set) : Set where
  field
    h : A -> B
    source : Monoid A
    target : Monoid B
  open Monoid source renaming (_·_ to _·ₛ_; 𝟙 to 𝟙ₛ)
  open Monoid target renaming (_·_ to _·ₜ_; 𝟙 to 𝟙ₜ)
  field
    homo : ∀ (a b : A) → h (a ·ₛ b) ≡ h a ·ₜ h b

data List (A : Set) : Set where
  — : List A
  _::_ : A -> List A -> List A

_*_ : { A : Set } → List A -> List A -> List A
— * second = second
(x :: xs) * second = x :: (xs * second)

generate : (A : Set) → Monoid (List A)
generate A =
  record { _·_ = _*_ ;
           𝟙 = — ;
           ·-assoc = *-is-assoc ;
           left-id = λ _ → refl ;
           right-id = *-satisfies-right-id 
         }
  where
    *-is-assoc : (a b c : List A) → (a * b) * c ≡ a * (b * c)
    *-is-assoc — b c = refl
    *-is-assoc (x :: xs) b c =
      begin
        ((x :: xs) * b) * c
      ≡⟨ {!!} ⟩
        (x :: xs) * (b * c)
      ∎

    *-satisfies-right-id : (a : List A) → (a * —) ≡ a
    *-satisfies-right-id — = refl
    *-satisfies-right-id (x :: xs) =
      begin
        (x :: xs) * —
      ≡⟨ refl ⟩
        x :: (xs * —)
      ≡⟨ cong (x ::_) (*-satisfies-right-id xs) ⟩
        x :: xs
      ∎
