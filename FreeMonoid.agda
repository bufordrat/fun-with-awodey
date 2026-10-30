module FreeMonoid where

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning
open import Function

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
    h-is-homo : ∀ (a b : A) → h (a ·ₛ b) ≡ h a ·ₜ h b

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
      ≡⟨ cong (x ::_) (*-is-assoc xs b c) ⟩
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

forget-set : (A : Set) → (M : Monoid A) → Set
forget-set A _ = A

forget-func : (A : Set) → (B : Set) → (f : MonoidHomomorphism A B) → A → B
forget-func A B f = MonoidHomomorphism.h f

identityMH : (A : Set) → Monoid A → MonoidHomomorphism A A
identityMH A Mon =
  record { h = h ;
           source = Mon ;
           target = Mon ;
           h-is-homo = λ _ _ → refl
         }
  where
    h = λ x → x
    _·_ = Monoid._·_ Mon

composeMH : (A : Set) →
            (B : Set) →
            (C : Set) →
            (g : MonoidHomomorphism B C) →
            (f : MonoidHomomorphism A B) →
            let monB₁ = MonoidHomomorphism.target f
                monB₂ = MonoidHomomorphism.source g
            in
            monB₁ ≡ monB₂ →
            MonoidHomomorphism A C
composeMH A B C g f prf =
  record { h = h ;
           source = monA ;
           target = monC ;
           h-is-homo = h-is-homo
         }
  where
    fh = MonoidHomomorphism.h f
    gh = MonoidHomomorphism.h g
    fh-is-homo = MonoidHomomorphism.h-is-homo f
    gh-is-homo = MonoidHomomorphism.h-is-homo g
    h = gh ∘ fh
    monA = MonoidHomomorphism.source f
    monB₁ = MonoidHomomorphism.target f
    monB₂ = MonoidHomomorphism.source g
    monC = MonoidHomomorphism.target g
    _·₁_ = Monoid._·_ monA
    _·₂_ = Monoid._·_ monB₁
    _·₃_ = Monoid._·_ monB₂
    _·₄_ = Monoid._·_ monC
    h-is-homo : ∀ (a b : A) → h (a ·₁ b) ≡ h a ·₄ h b
    h-is-homo a b =
      begin
        h (a ·₁ b)
      ≡⟨ refl ⟩
        gh (fh (a ·₁ b))
      ≡⟨ cong (λ x → gh x) (fh-is-homo a b) ⟩
        gh (fh a ·₂ fh b)
      ≡⟨ cong (λ op → gh ((Monoid._·_ op) (fh a) (fh b))) prf ⟩
        gh (fh a ·₃ fh b)
      ≡⟨ gh-is-homo (fh a) (fh b) ⟩
         gh (fh a) ·₄ gh (fh b)
      ≡⟨ refl ⟩
        h a ·₄ h b
      ∎

forget-satisfies-id : (A : Set) →
                      (M : Monoid A) →
                      let id_forget = λ (x : forget-set A M) -> x in
                      forget-func A A (identityMH A M) ≡ id_forget
forget-satisfies-id A M = refl

forget-satisfies-comp : (A : Set) →
                        (B : Set) →
                        (C : Set) →
                        (g : MonoidHomomorphism B C) →
                        (f : MonoidHomomorphism A B) →
                        let monB₁ = MonoidHomomorphism.target f
                            monB₂ = MonoidHomomorphism.source g
                        in
                        (prf : monB₁ ≡ monB₂) →
                        let g∘f = composeMH A B C g f prf in
                        forget-func A C (g∘f) ≡ forget-func B C g ∘ forget-func A B f
forget-satisfies-comp A B C g f prf = refl

