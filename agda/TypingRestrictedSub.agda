module TypingRestrictedSub where

open import lib
open import Tp
open import Tm
open import Declarative

infix 7 ⊢r_!_

data ⊢r_!_ : Tm → Tp → Set where
  S : ∀{A B C : Tp} →
      ⊢r S ! (C ⟶ B ⟶ A) ⟶ (C ⟶ B) ⟶ C ⟶ A

  K : ∀{A B : Tp} →
      ⊢r K ! A ⟶ B ⟶ A

  App : ∀{X A B : Tp}{t1 t2 : Tm} →
         ⊢r t1 ! X →
         ⊢r t2 ! A →
         X <: A ⟶ B → 
         ⊢r t1 · t2 ! B

  Suc : ∀{A : Tp} → 
         ⊢r Suc ! (A ⟶ D A)

  Zero : ∀{A : Tp} → 
         ⊢r Zero ! D A

  Case : ∀{X A B1 B2 B : Tp}{n cz cs : Tm} →
         ⊢r n ! X →
         ⊢r cz ! B1 →
         ⊢r cs ! B2 →
         X <: D A →
         B1 <: B →
         B2 <: A ⟶ B → 
         ⊢r (Case n cz cs) ! B

  Alg : ∀{X : Tp}{Y : Tp → Tp}{b : Tm} →
        (∀{R : Tp} → ⊢r b ! Y R) →
        (∀{R : Tp} → Y R <: (R ⟶ X) ⟶ D R ⟶ X) → 
        ⊢r (Alg b) ! D⇒ X

