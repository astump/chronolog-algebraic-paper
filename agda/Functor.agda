module Functor where

open import lib

record Functor(F : Set → Set) : Set₁ where
  field
    fmap : ∀{A B : Set} → (A → B) → F A → F B
