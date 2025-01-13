module Linear.Intuitionistic.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod

open import Linear.Intuitionistic.Core

-----------------
-- Composition --
-----------------

Comp : ∀ {A C : ILL} (B : ILL) →
       [ A ] ⊢ B →
       [ B ] ⊢ C →
       -----
       [ A ] ⊢ C
Comp {A} {C} B A⊢B B⊢C = Cut [ A ] • B A⊢B B⊢C

-----------------------
-- Higher Identities --
-----------------------

Id⊸ : ∀ {A B : ILL} → [ A ] ⊢ A → [ B ] ⊢ B → [ A ⊸ B ] ⊢ A ⊸ B
Id⊸ {A} {B} IdA IdB = ⊸R (ExchangeTopTwo (⊸L [ A ] • IdA IdB))

Id⊗ : ∀ {A B : ILL} → [ A ] ⊢ A → [ B ] ⊢ B → [ A ⊗ B ] ⊢ A ⊗ B
Id⊗ {A} {B} IdA IdB = ⊗L (⊗R [ A ] [ B ] IdA IdB)

Id1 : [ one ] ⊢ one
Id1 = 1L 1R

Id& : ∀ {A B : ILL} → [ A ] ⊢ A → [ B ] ⊢ B → [ A & B ] ⊢ A & B
Id& {A} {B} IdA IdB = &R (&L₁ IdA) (&L₂ IdB)

Id⊤ : [ ⊤ ] ⊢ ⊤
Id⊤ = ⊤R

Id⊕ : ∀ {A B : ILL} → [ A ] ⊢ A → [ B ] ⊢ B → [ A ⊕ B ] ⊢ A ⊕ B
Id⊕ {A} {B} IdA IdB = ⊕L (⊕R₁ IdA) (⊕R₂ IdB)

Id0 : [ zer ] ⊢ zer
Id0 = 0L

Id! : ∀ {A : ILL} → [ A ] ⊢ A → [ ! A ] ⊢ ! A
Id! {A} IdA = !R (!D IdA) Per1

-- THE Identity rule
Id : ∀ {A : ILL} → [ A ] ⊢ A
Id {var n} = Idₙ
Id {A ⊸ B} = Id⊸ Id Id
Id {A ⊗ B} = Id⊗ Id Id
Id {one} = Id1
Id {A & B} = Id& Id Id
Id {⊤} = Id⊤
Id {A ⊕ B} = Id⊕ Id Id
Id {zer} = Id0
Id { ! A } = Id! Id

-----------------------------------
-- Properties of ILL conncetives --
-----------------------------------

MP : ∀ {A B : ILL} →
     -----------------
     [ A ⟨ A ⊸ B ] ⊢ B
MP {A} {B} = ⊸L [ A ] • Id Id

&π₁ : ∀ {A B : ILL} →
      -------------
      [ A & B ] ⊢ A
&π₁ = &L₁ Id

&π₂ : ∀ {A B : ILL} →
      -------------
      [ A & B ] ⊢ B
&π₂ = &L₂ Id

⊗Intro : ∀ {A B : ILL} →
         -----------------
         [ A ⟨ B ] ⊢ A ⊗ B
⊗Intro {A} {B} = ⊗R [ A ] [ B ] Id Id

⊕Inl : ∀ {A B : ILL} →
       -------------
       [ A ] ⊢ A ⊕ B
⊕Inl = ⊕R₁ Id

⊕Inr : ∀ {A B : ILL} →
       -------------
       [ B ] ⊢ A ⊕ B
⊕Inr = ⊕R₂ Id

-----------------------
-- Inverse rules (R) --
-----------------------

-- Linear implication is a negative connective (R-invertible)

⊸R⁻¹ : ∀ {Δ : Resources} {A B : ILL} →
       Δ ⊢ A ⊸ B →
       ---------
       Δ ⟪ A ⊢ B
⊸R⁻¹ {Δ} {A} {B} ⊢A⊸B = Cut Δ [ A ] (A ⊸ B) ⊢A⊸B MP

-- Alternative conjunction is a negative connective (R-invertible)

&R⁻¹₁ : ∀ {Δ : Resources} {A : ILL} (B : ILL) →
        Δ ⊢ A & B →
        ---------
        Δ ⊢ A
&R⁻¹₁ {Δ} {A} B ⊢A&B = Cut Δ • (A & B) ⊢A&B &π₁

&R⁻¹₂ : ∀ {Δ : Resources} {A : ILL} (B : ILL) →
        Δ ⊢ A & B →
        ---------
        Δ ⊢ B
&R⁻¹₂ {Δ} {A} B ⊢A&B = Cut Δ • (A & B) ⊢A&B &π₂

-- Top is a negative connective (R-invertible)
-- ... but its rule has no premises, so this is a trivial fact

-----------------------------
-- Lindenbaum equivalences --
-----------------------------

-- '⊗' is commutative

⊢⊗Comm : ∀ {A B : ILL} → [ A ⊗ B ] ⊢ B ⊗ A
⊢⊗Comm {A} {B} = ⊗L (ExchangeTopTwo (⊗R [ B ] [ A ] Id Id))

⊗Comm : ∀ {A B : ILL} → A ⊗ B ⊣⊢ B ⊗ A
⊗Comm = ⊢⊗Comm , ⊢⊗Comm

-- '&' is commutative

⊢&Comm : ∀ {A B : ILL} → [ A & B ] ⊢ B & A
⊢&Comm {A} {B} = &R (&L₂ Id) (&L₁ Id)

&Comm : ∀ {A B : ILL} → A & B ⊣⊢ B & A
&Comm = ⊢&Comm , ⊢&Comm

-- 'one' is the identity of '⊗'

⊢⊗1 : ∀ {A : ILL} → [ A ⊗ one ] ⊢ A
⊢⊗1 = ⊗L (1L Id)

⊗1⊢ : ∀ {A : ILL} → [ A ] ⊢ A ⊗ one
⊗1⊢ {A} = ⊗R [ A ] • Id 1R

⊗1 : ∀ {A : ILL} → A ⊗ one ⊣⊢ A
⊗1 = ⊢⊗1 , ⊗1⊢

-- '⊤' is the identity of '&'

⊢&⊤ : ∀ {A : ILL} → [ A & ⊤ ] ⊢ A
⊢&⊤ = &L₁ Id

&⊤⊢ : ∀ {A : ILL} → [ A ] ⊢ A & ⊤
&⊤⊢ = &R Id ⊤R

&⊤ : ∀ {A : ILL} → A & ⊤ ⊣⊢ A
&⊤ = ⊢&⊤ , &⊤⊢

-- Flip

⊢Flip : ∀ {A B C : ILL} → [ A ⊸ B ⊸ C ] ⊢ B ⊸ A ⊸ C
⊢Flip = ⊸R (⊸R (ExchangeTopTwo (⊸R⁻¹ (⊸R⁻¹ Id))))

Flip : ∀ {A B C : ILL} → A ⊸ B ⊸ C ⊣⊢ B ⊸ A ⊸ C
Flip = ⊢Flip , ⊢Flip

---------------------
-- Exchange++ rule --
---------------------

Exchange++ : ∀ (Δ₁ Δ₂ : Resources) {A : ILL} →
             Δ₁ ++ Δ₂ ⊢ A →
             -------------
             Δ₂ ++ Δ₁ ⊢ A
Exchange++ • • h = h
Exchange++ • (Δ₂ ⟪ x) h = ⊸R⁻¹ (Exchange++ • Δ₂ (⊸R h))
Exchange++ (Δ₁ ⟪ x) • h = ⊸R⁻¹ (Exchange++ Δ₁ • (⊸R h))
Exchange++ (Δ₁ ⟪ x) (Δ₂ ⟪ y) {A} h =
  ⊸R⁻¹ (Exchange++ Δ₁ (Δ₂ ⟪ y) (⊸R⁻¹ (Exchange++ Δ₂ Δ₁ (Cut (Δ₂ ++ Δ₁) • (x ⊸ y ⊸ A) (⊸R (Exchange++ (Δ₁ ⟪ x) Δ₂ (⊸R h))) ⊢Flip))))

-----------------------
-- Inverse rules (L) --
-----------------------

-- Simultaneous conjunction is a positive connective (L-invertible)

⊗L⁻¹ : ∀ {Δ : Resources} {A B C : ILL} →
       Δ ⟪ A ⊗ B ⊢ C →
       -------------
       Δ ⟪ A ⟪ B ⊢ C
⊗L⁻¹ {Δ} {A} {B} {C} h = Exchange++ [ A ⟨ B ] Δ (Cut [ A ⟨ B ] Δ (A ⊗ B) ⊗Intro h)

-- Alternative disjunction is a positive connective (L-invertible)

⊕L⁻¹₁ : ∀ {Δ : Resources} {A B C : ILL} →
        Δ ⟪ A ⊕ B ⊢ C →
        -------------
        Δ ⟪ A ⊢ C
⊕L⁻¹₁ {Δ} {A} {B} {C} h = Exchange++ [ A ] Δ (Cut [ A ] Δ (A ⊕ B) ⊕Inl h)

⊕L⁻¹₂ : ∀ {Δ : Resources} {A B C : ILL} →
        Δ ⟪ A ⊕ B ⊢ C →
        -------------
        Δ ⟪ B ⊢ C
⊕L⁻¹₂ {Δ} {A} {B} {C} h = Exchange++ [ B ] Δ (Cut [ B ] Δ (A ⊕ B) ⊕Inr h)

-----------------------
-- Elimination rules --
-----------------------

⊸E : ∀ {Δ₁ Δ₂ : Resources} {B : ILL} (A : ILL) →
     Δ₁ ⊢ A →
     Δ₂ ⊢ A ⊸ B →
     ------------
     Δ₁ ++ Δ₂ ⊢ B
⊸E {Δ₁} {Δ₂} {B} A ⊢A ⊢A⊸B = Cut Δ₁ Δ₂ A ⊢A (⊸R⁻¹ ⊢A⊸B)
