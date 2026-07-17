{- prove that if a term can be assigned a type with the declarative rules
   in Typing.agda, which include the Sub rule; then it can be assigned one
   where subtyping is used only in certain places (TypingRestrictedSub).

   This corresponds to Theorem 16.2.5, "Completeness/Minimal Typing" in
   Pierce's "Types and Programming Languages."

   The proof below relies on (derivable) reflexivity, transitivity,
   and the arrow subtyping rule.
-}
module Metatheory.RestrictedSub where

open import lib
open import Tp
open import Tm
open import TmC
open import Coe
open import Decproc
open import Typing
open import TypingRestrictedSub
import Metatheory.Completeness
import Metatheory.Uniqueness

strengthen⟶ : ∀{T A A' B : Tp} →
               T <:: A ⟶ B →
               A' <:: A →
               T <:: A' ⟶ B
strengthen⟶ d d' = trans<:: d (Arr d' refl<::)

completeness : ∀{t : Tm}{T : Tp} →
      ⊢ t ! T →
      ∃ Tp (λ T' → ⊢r t ! T' ∧ T' <:: T)
completeness S = _ , (S , refl<::)
completeness K = _ , (K , refl<::)
completeness (App d d1) with completeness d | completeness d1
completeness (App{B = B} d d1) | T , d' , s | T' , d1' , s1 = B , ((App d' d1' (strengthen⟶ s s1)) , refl<::)
completeness Suc = _ , (Suc , refl<::)
completeness Zero = _ , (Zero , refl<::)
completeness (Case d d1 d2) with completeness d | completeness d1 | completeness d2
completeness (Case{B = B} d d1 d2) | T , d' , s | T' , d1' , s1 | T'' , d2' , s2 = B , ((Case d' d1' d2' s s1 s2) , refl<::)
completeness (Alg x) = _ , ((Alg (λ{R} → fst (snd' (completeness (x{R})))) λ{R} → snd (snd' (completeness (x{R})))) , refl<::)
completeness (Sub x d) with completeness d
completeness (Sub x d) | T , d' , s = _ , (d' , (trans<:: s (Metatheory.Completeness.completeness x)))

{-

K : A → B1 → A
a : A
b : B1'
with B1' <: B1

Then K a b will have different typing derivation from

K : A → B2 → A
a : A
b : B2'
with B2' <: B2



uniqueness : ∀{t : Tm}{T T' : Tp} →
             (d : ⊢r t ! T) →
             (d' : ⊢r t ! T') →
             ⟨ d ⟩ ≡ ⟨ d' ⟩ 
uniqueness S S = refl
uniqueness K K = refl
uniqueness (App d d₁ x) (App d' d'' x₁) = {!!}
uniqueness Suc Suc = refl
uniqueness Zero Zero = refl
uniqueness (Case d d₁ d₂ x x₁ x₂) (Case d' d'' d''' x₃ x₄ x₅) = {!!}
uniqueness (Alg x x₁) (Alg x₂ x₃) = {!!}
-}