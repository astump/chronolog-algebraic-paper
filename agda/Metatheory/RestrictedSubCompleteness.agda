{- prove that if a term can be assigned a type with the declarative rules
   in Typing.agda, which include the Sub rule; then it can be assigned one
   where subtyping is used only in certain places (TypingRestrictedSub).

   This corresponds to Theorem 16.2.5, "Completeness/Minimal Typing" in
   Pierce's "Types and Programming Languages."

   The proof below relies on (derivable) reflexivity, transitivity,
   and the arrow subtyping rule.
-}
module Metatheory.RestrictedSubCompleteness where

open import lib
open import Tp
open import Tm
open import Declarative
open import Typing
open import TypingRestrictedSub

strengthen⟶ : ∀{T A A' B : Tp} →
               T <: A ⟶ B →
               A' <: A →
               T <: A' ⟶ B
strengthen⟶ d d' = Trans d (Arr d' refl<:)

thm : ∀{t : Tm}{T : Tp} →
      ⊢ t ! T →
      ∃ Tp (λ T' → ⊢r t ! T' ∧ T' <: T)
thm S = _ , (S , refl<:)
thm K = _ , (K , refl<:)
thm (App d d1) with thm d | thm d1
thm (App{B = B} d d1) | T , d' , s | T' , d1' , s1 = B , ((App d' d1' (strengthen⟶ s s1)) , refl<:)
thm Suc = _ , (Suc , refl<:)
thm Zero = _ , (Zero , refl<:)
thm (Case d d1 d2) with thm d | thm d1 | thm d2
thm (Case{B = B} d d1 d2) | T , d' , s | T' , d1' , s1 | T'' , d2' , s2 = B , ((Case d' d1' d2' s s1 s2) , refl<:)
thm (Alg x) = _ , ((Alg (λ{R} → fst (snd' (thm (x{R})))) λ{R} → snd (snd' (thm (x{R})))) , refl<:)
thm (Sub x d) with thm d
thm (Sub x d) | T , d' , s = _ , (d' , (Trans s x))