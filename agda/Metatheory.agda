module Metatheory where

open import lib hiding (_⟨_⟩_)

open import Tp
open import Typing
open import Decproc
open import Tm
open import Ctm
open import Declarative
open import Soundness

infix 4 _▹_

{- this relation represents the erasure of the Ctm to just a Tm.

   It turned out to be necessary to represent erasure relationally,
   because of the quantification over R in the type of the argument
   to Alg.  If we try to define erasure as a function, we are forced
   to instantiate that R with some particular type, and this led
   to problems in the soundness proof.  The relational approach
   does not have this issue. -}
data _▹_ : ∀{A : Tp} → Ctm A → Tm → Set where
  S : ∀{A B C : Tp} → S{A}{B}{C} ▹ S
  K : ∀{A B : Tp} → K{A}{B} ▹ K  
  _·_ : ∀{A B : Tp}{c : Ctm (A ⟶ B)}{c' : Ctm A}{t t'} →
         c ▹ t →
         c' ▹ t' →
         (c · c') ▹ (t · t')
  Suc : ∀{R : Tp} → Suc{R} ▹ Suc
  Zero : ∀{R : Tp} → Zero{R} ▹ Zero
  Case : ∀{R C : Tp}{c : Ctm (D R)}{c' : Ctm C}{c'' : Ctm (R ⟶ C)}{t t' t''} →
         c ▹ t →
         c' ▹ t' →
         c'' ▹ t'' →
         (Case c c' c'') ▹ (Case t t' t'')
  Alg : ∀{X : Tp}{c : ∀{R : Tp} → Ctm ((R ⟶ X) ⟶ D R ⟶ X)}{t} →
         (∀{R : Tp} → c{R} ▹ t) →
         Alg c ▹ Alg t
  Coerce : ∀{A B : Tp}(d : A <:: B){c : Ctm A}{t} →
           c ▹ t →
           (Coerce d c) ▹ t

Soundness : ∀{A : Tp}{c : Ctm A}{t : Tm} →
            c ▹ t → 
            ⊢ t ! A
Soundness S = S
Soundness K = K
Soundness (u · u₁) = App (Soundness u) (Soundness u₁)
Soundness Suc = Suc
Soundness Zero = Zero
Soundness (Case u u₁ u₂) = Case (Soundness u) (Soundness u₁) (Soundness u₂) 
Soundness (Alg x) = Alg λ{R} → Soundness (x{R})
Soundness (Coerce d u) = Sub (soundness d) (Soundness u)
