-- typing for Tms (which do not have coercions)

module Typing where

open import lib
open import Tp
open import Tm
open import Declarative

infix 7 ⊢_!_

data ⊢_!_ : Tm → Tp → Set where
  S : ∀{A B C : Tp} →
      ⊢ S ! (C ⟶ B ⟶ A) ⟶ (C ⟶ B) ⟶ C ⟶ A

  K : ∀{A B : Tp} →
      ⊢ K ! A ⟶ B ⟶ A

  App : ∀{A B : Tp}{t1 t2 : Tm} →
         ⊢ t1 ! A ⟶ B →
         ⊢ t2 ! A →
         ⊢ t1 · t2 ! B

  Suc : ∀{A : Tp} → 
         ⊢ Suc ! (A ⟶ D A)

  Zero : ∀{A : Tp} → 
         ⊢ Zero ! D A

  Case : ∀{A B : Tp}{n cz cs : Tm} →
         ⊢ n ! D A →
         ⊢ cz ! B →
         ⊢ cs ! A ⟶ B →
         ⊢ (Case n cz cs) ! B

  Alg : ∀{X : Tp}{b : Tm} →
        (∀{R : Tp} → ⊢ b ! (R ⟶ X) ⟶ D R ⟶ X) →
        ⊢ (Alg b) ! D⇒ X

  Sub : ∀{A B : Tp}{t : Tm} →
        A <: B →
        ⊢ t ! A →
        ⊢ t ! B


  
