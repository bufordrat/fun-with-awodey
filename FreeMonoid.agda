module FreeMonoid where

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning
open import Function
open import Data.Product

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

record MonoidHomomorphism
       {A : Set} {B : Set} (M : Monoid A) (N : Monoid B)
       : Set where
  field
    h : A -> B
  open Monoid M renaming (_·_ to _·ₘ_; 𝟙 to 𝟙ₛ)
  open Monoid N renaming (_·_ to _·ₙ_; 𝟙 to 𝟙ₜ)
  field
    h-is-homo : ∀ (a b : A) → h (a ·ₘ b) ≡ h a ·ₙ h b

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

forget-set : Σ Set Monoid → Set
forget-set (A , _) = A

forget-func : {A : Set} →
              {B : Set} →
              (M : Monoid A) →
              (N : Monoid B) →
              (f : MonoidHomomorphism {A} {B} M N) →
              A → B
forget-func {A} {B} M N f = MonoidHomomorphism.h f

identityMH : {A : Set} → (M : Monoid A) → MonoidHomomorphism {A} {A} M M
identityMH {A} Mon =
  let identity = λ x → x in
  record { h = identity ;
           h-is-homo = λ _ _ → refl
         }

composeMH : {A : Set} →
            {B : Set} →
            {C : Set} →
            (MA : Monoid A) →
            (MB : Monoid B) →
            (MC : Monoid C) →
            (g : MonoidHomomorphism {B} {C} MB MC) →
            (f : MonoidHomomorphism {A} {B} MA MB) →
            MonoidHomomorphism {A} {C} MA MC
composeMH {A} {B} {C} MA MB MC g f =
  record { h = h ;
           h-is-homo = h-is-homo
         }
  where
    fh = MonoidHomomorphism.h f
    gh = MonoidHomomorphism.h g
    fh-is-homo = MonoidHomomorphism.h-is-homo f
    gh-is-homo = MonoidHomomorphism.h-is-homo g
    h = gh ∘ fh
    _·₁_ = Monoid._·_ MA
    _·₂_ = Monoid._·_ MB
    _·₃_ = Monoid._·_ MC
    h-is-homo : ∀ (a b : A) → h (a ·₁ b) ≡ h a ·₃ h b
    h-is-homo a b =
      begin
        h (a ·₁ b)
      ≡⟨ refl ⟩
        gh (fh (a ·₁ b))
      ≡⟨ cong (λ x → gh x) (fh-is-homo a b) ⟩
        gh (fh a ·₂ fh b)
      ≡⟨ gh-is-homo (fh a) (fh b) ⟩
         gh (fh a) ·₃ gh (fh b)
      ≡⟨ refl ⟩
        h a ·₃ h b
      ∎

forget-satisfies-id : {A : Set} →
                      (M : Monoid A) →
                      let id_forget = λ (x : forget-set (A , M)) -> x in
                      forget-func {A} {A} M M (identityMH {A} M) ≡ id_forget
forget-satisfies-id {A} M = refl

forget-satisfies-comp : {A : Set} →
                        {B : Set} →
                        {C : Set} →
                        (MA : Monoid A) →
                        (MB : Monoid B) →
                        (MC : Monoid C) →
                        (g : MonoidHomomorphism {B} {C} MB MC) →
                        (f : MonoidHomomorphism {A} {B} MA MB) →
                        let g∘f = composeMH {A} {B} {C} MA MB MC g f
                            F₁ = forget-func {A} {C} MA MC
                            F₂ = forget-func {B} {C} MB MC
                            F₃ = forget-func {A} {B} MA MB
                        in
                        F₁ (g∘f) ≡ F₂ g ∘ F₃ f
forget-satisfies-comp {A} {B} {C} MA MB MC g f = refl

record Category (Obj : Set₁) (Arrow : Obj → Obj → Set₀) : Set₁ where 
  field
    idₘ : (A : Obj) → Arrow A A
    _∘ₘ_ : (A B C : Obj) → Arrow B C → Arrow A B → Arrow A C
    left-id : (A B : Obj) →
              (f : Arrow A B) →
              let idₗ = idₘ B
                  _∘ₗ_ = _∘ₘ_ A B B
              in
              idₗ ∘ₗ f ≡ f
    right-id : (A B : Obj) →
               (f : Arrow A B) →
               let idᵣ = idₘ A
                   _∘ᵣ_ = _∘ₘ_ A A B
               in
               f ∘ᵣ idᵣ ≡ f
    comp : (A B C D : Obj) →
           (f : Arrow C D) →
           (g : Arrow B C) →
           (h : Arrow A B) →
           let _∘₁_ = _∘ₘ_ B C D
               _∘₂_ = _∘ₘ_ A B D
               _∘₃_ = _∘ₘ_ A C D
               _∘₄_ = _∘ₘ_ A B C
           in 
           (f ∘₁ g) ∘₂ h ≡ f ∘₃ (g ∘₄ h)
