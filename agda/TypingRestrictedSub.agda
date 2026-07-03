module TypingRestrictedSub where

open import lib hiding ( _⟨_⟩_ )
open import Tp
open import Tm
open import TmC
open import Decproc
open import Coe

infix 7 ⊢r_!_

data ⊢r_!_ : Tm → Tp → Set where
  S : ∀{A B C : Tp} →
      ⊢r S ! (C ⟶ B ⟶ A) ⟶ (C ⟶ B) ⟶ C ⟶ A

  K : ∀{A B : Tp} →
      ⊢r K ! A ⟶ B ⟶ A

  -- this still allows flexibility for coercing f a b: coerce f or coerce f a.
  --
  -- Another point: maybe can prove terms have unique minimal types, and then the
  -- application case where we have
  --
  --   f : X    a : A    X <: A -> B
  --
  -- and
  --
  --   f : X'    a : A'    X' <: A' -> B
  --
  -- could get simpler, because there would be minimal X'' for f and A'' for a.

  App : ∀{X A B : Tp}{t1 t2 : Tm} →
         ⊢r t1 ! X →
         ⊢r t2 ! A →
         X <:: A ⟶ B → 
         ⊢r t1 · t2 ! B

  Suc : ∀{A : Tp} → 
         ⊢r Suc ! (A ⟶ D A)

  Zero : ∀{A : Tp} → 
         ⊢r Zero ! D A

  Case : ∀{X A B1 B2 B : Tp}{n cz cs : Tm} →
         ⊢r n ! X →
         ⊢r cz ! B1 →
         ⊢r cs ! B2 →
         X <:: D A →
         B1 <:: B →
         B2 <:: A ⟶ B → 
         ⊢r (Case n cz cs) ! B

  Alg : ∀{X : Tp}{Y : Tp → Tp}{b : Tm} →
        (∀{R : Tp} → ⊢r b ! Y R) →
        (∀{R : Tp} → Y R <:: (R ⟶ X) ⟶ D R ⟶ X) → 
        ⊢r (Alg b) ! D⇒ X

infix 8 ⟨_⟩

⟨_⟩ : ∀{t : Tm}{X : Tp} →
       ⊢r t ! X →
       TmC
⟨ S ⟩ = S
⟨ K ⟩ = K
⟨ App d d₁ x ⟩ = App ⟨ d ⟩ ⟨ d₁ ⟩ ⟪ x ⟫ 
⟨ Suc ⟩ = Suc
⟨ Zero ⟩ = Zero
⟨ Case d d₁ d₂ x x₁ x₂ ⟩ = Case ⟨ d ⟩ ⟨ d₁ ⟩ ⟨ d₂ ⟩ ⟪ x ⟫ ⟪ x₁ ⟫ ⟪ x₂ ⟫ 
⟨ Alg d x ⟩ = Alg ⟨ d{μD} ⟩ ⟪ x{μD} ⟫