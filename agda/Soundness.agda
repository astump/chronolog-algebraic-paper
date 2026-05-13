open import lib
open import Tp
open import Declarative
open import Decproc

module Soundness where

soundness : ∀{T T' : Tp} →
            T <:: T' →
            T <: T'
soundness Refl = Refl
soundness (Fun d d₁) = Fun (soundness d) (soundness d₁)
soundness (Roll1 d) = roll1 (soundness d)
soundness (Roll2 d) = roll2 (soundness d)
soundness (Cov d) = Cov (soundness d)