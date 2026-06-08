-- intrinsically typed terms, with coercions 
module Ctm where

open import lib
open import Tp
open import Decproc

data Ctm : Tp → Set where
  S : ∀{A B C : Tp} → Ctm ((C ⟶ B ⟶ A) ⟶ (C ⟶ B) ⟶ C ⟶ A)
  K : ∀{A B : Tp} → Ctm (A ⟶ B ⟶ A)
  _·_ : ∀{A B : Tp} → Ctm (A ⟶ B) → Ctm A → Ctm B
  Suc : ∀{R : Tp} → Ctm (R ⟶ D R)
  Zero : ∀{R : Tp} → Ctm (D R)
  Case : ∀{R C : Tp} → Ctm (D R) → Ctm C → Ctm (R ⟶ C) → Ctm C
  Alg : ∀{X : Tp} → (∀{R : Tp} → Ctm ((R ⟶ X) ⟶ D R ⟶ X)) → Ctm (D⇒ X)
  Coerce : ∀{A B : Tp} → A <:: B → Ctm A → Ctm B

