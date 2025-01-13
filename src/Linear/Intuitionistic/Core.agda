module Linear.Intuitionistic.Core where

open import Cubical.Foundations.Prelude

import Cubical.Data.Empty as E
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Prod

open import Util

--------------
-- Language --
--------------

infixr 7 _⊸_
infixl 8 _⊕_
infixl 9 _⊗_ _&_
infix 10 !_
data ILL : Type where
  var : ℕ → ILL

  _⊸_ : ILL → ILL → ILL

  _⊗_ : ILL → ILL → ILL
  one : ILL

  _&_ : ILL → ILL → ILL
  ⊤ : ILL

  _⊕_ : ILL → ILL → ILL
  zer : ILL

  !_ : ILL → ILL

---------------------------
-- Multiset of resources --
---------------------------

-- The 'Resources' datatype represents a *list* of formulas/resources. Every resource matters.

infixl 5 _⟪_

data Resources : Type where
  • : Resources
  _⟪_ : Resources → ILL → Resources

infixl 5 _++_
_++_ : Resources → Resources → Resources
r ++ • = r
r ++ (s ⟪ x) = r ++ s ⟪ x

infix 6 [_]
[_] : ILL → Resources
[ formula ] = • ⟪ formula

infix 6 [_⟨_]
[_⟨_] : ILL → ILL → Resources
[ formula₁ ⟨ formula₂ ] = • ⟪ formula₁ ⟪ formula₂

length : Resources → ℕ
length • = zero
length (r ⟪ _) = suc (length r)

within_at_ : (r : Resources) → Fin (length r) → ILL
within • at (n , h) = E.rec h
within (r ⟪ x) at (zero , h) = x
within (r ⟪ x) at (suc i , h) = within r at (i , h)

within_at_setTo_ : (r : Resources) → Fin (length r) → ILL → Resources
within • at (n , h) setTo y = E.rec h
within (r ⟪ x) at (zero , h) setTo y = r ⟪ y
within (r ⟪ x) at (suc i , h) setTo y = within r at (i , h) setTo y ⟪ x

setTo-lengths-= : (r : Resources) → (i : Fin (length r)) → (x : ILL) → length r ≡ length (within r at i setTo x)
setTo-lengths-= • (i , h) x = E.rec h
setTo-lengths-= (r ⟪ x₁) (zero , h) x = refl
setTo-lengths-= (r ⟪ x₁) (suc i , h) x = cong suc (setTo-lengths-= r (i , h) x)

-- Setting up the exchange rule with the swapping mechanism
within_swap_and_ : (r : Resources) → Fin (length r) → Fin (length r) → Resources
within r swap i and j = let x = within r at i
                            y = within r at j
                        in within (within r at i setTo y) at (subst Fin (setTo-lengths-= r i y) j) setTo x

------------------------
-- Persistent context --
------------------------

data Per : Resources → Type where
  Per1 : {A : ILL} → Per ([ ! A ])
  PerS : {Δ : Resources} {A : ILL} → Per Δ → Per (Δ ⟪ ! A)

-------------
-- Sequent --
-------------

infix 4 _⊢_
data _⊢_ : Resources → ILL → Type where
  -- Exchange rule, the only substructural rule allowed in Linear Logic
  Exchange : {Δ : Resources} {A : ILL} (i j : ℕ) {ih : True (suc i ≤? length Δ)} {jh : True (suc j ≤? length Δ)} →
             Δ ⊢ A →
             -----------------------------------------------------------
             within Δ swap (i , toWitness ih) and (j , toWitness jh) ⊢ A

  Idₙ : ∀ {n : ℕ} →
        -----------------
        [ var n ] ⊢ var n

  Cut : ∀ (Δ₁ Δ₂ : Resources) {B : ILL} (A : ILL) →
        Δ₁ ⊢ A →
        Δ₂ ⟪ A ⊢ B →
        ------------
        Δ₁ ++ Δ₂ ⊢ B

  ⊸L : (Δ₁ Δ₂ : Resources) {A B C : ILL} →
       Δ₁ ⊢ A →
       Δ₂ ⟪ B ⊢ C →
       --------------------
       Δ₁ ++ Δ₂ ⟪ A ⊸ B ⊢ C

  ⊸R : ∀ {Δ : Resources} {A B : ILL} →
       Δ ⟪ A ⊢ B →
       ---------
       Δ ⊢ A ⊸ B

  ⊗L : ∀ {Δ : Resources} {A B C : ILL} →
       Δ ⟪ A ⟪ B ⊢ C →
       -------------
       Δ ⟪ A ⊗ B ⊢ C

  ⊗R : ∀ (Δ₁ Δ₂ : Resources) {A B : ILL} →
       Δ₁ ⊢ A →
       Δ₂ ⊢ B →
       ----------------
       Δ₁ ++ Δ₂ ⊢ A ⊗ B

  1R : -------
       • ⊢ one

  1L : ∀ {Δ : Resources} {A : ILL} →
       Δ ⊢ A →
       -----------
       Δ ⟪ one ⊢ A

  &L₁ : ∀ {Δ : Resources} {A B C : ILL} →
        Δ ⟪ A ⊢ C →
        -------------
        Δ ⟪ A & B ⊢ C

  &L₂ : ∀ {Δ : Resources} {A B C : ILL} →
        Δ ⟪ B ⊢ C →
        -------------
        Δ ⟪ A & B ⊢ C

  &R : ∀ {Δ : Resources} {A B : ILL} →
       Δ ⊢ A →
       Δ ⊢ B →
       ---------
       Δ ⊢ A & B

  ⊤R : ∀ {Δ : Resources} →
       -----
       Δ ⊢ ⊤

  ⊕L : ∀ {Δ : Resources} {A B C : ILL} →
       Δ ⟪ A ⊢ C →
       Δ ⟪ B ⊢ C →
       -------------
       Δ ⟪ A ⊕ B ⊢ C

  ⊕R₁ : ∀ {Δ : Resources} {A B : ILL} →
        Δ ⊢ A →
        ---------
        Δ ⊢ A ⊕ B

  ⊕R₂ : ∀ {Δ : Resources} {A B : ILL} →
        Δ ⊢ B →
        ---------
        Δ ⊢ A ⊕ B

  0L : ∀ {Δ : Resources} {A : ILL} →
       -----------
       Δ ⟪ zer ⊢ A

  !W : ∀ {Δ : Resources} {A B : ILL} →
       Δ ⊢ B →
       -----------
       Δ ⟪ ! A ⊢ B

  !C : ∀ {Δ : Resources} {A B : ILL} →
       Δ ⟪ ! A ⟪ ! A ⊢ B →
       -----------
       Δ ⟪ ! A ⊢ B

  !D : ∀ {Δ : Resources} {A B : ILL} →
       Δ ⟪ A ⊢ B →
       -----------
       Δ ⟪ ! A ⊢ B

  !R : ∀ {Δ : Resources} {A : ILL} →
       Δ ⊢ A →
       Per Δ →
       -------
       Δ ⊢ ! A

ExchangeTopTwo : ∀ {Δ : Resources} {A B C : ILL} →
                 Δ ⟪ A ⟪ B ⊢ C →
                 -------------
                 Δ ⟪ B ⟪ A ⊢ C
ExchangeTopTwo = Exchange 0 1

Exchange12 : ∀ {Δ : Resources} {A B C D : ILL} →
             Δ ⟪ A ⟪ B ⟪ C ⊢ D →
             -------------
             Δ ⟪ B ⟪ A ⟪ C ⊢ D
Exchange12 = Exchange 1 2

----------------------------
-- Lindenbaum equivalence --
----------------------------

infix 4 _⊣⊢_
_⊣⊢_ : ILL → ILL → Type _
x ⊣⊢ y = ([ x ] ⊢ y) × ([ y ] ⊢ x)
