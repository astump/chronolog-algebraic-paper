open import lib
open import Tp
open import Declarative
open import Decproc

module Soundness where

soundness : ∀{T T' : Tp} →
            T <:: T' →
            T <: T'
soundness Refl = Refl
soundness (Arr d d₁) = Arr (soundness d) (soundness d₁)
soundness (Roll d) = roll1 (soundness d)
soundness (Unroll d) = roll2 (soundness d)
soundness (Cov d) = Cov (soundness d)
soundness (Alg d) = Alg (soundness d)
soundness (Cata d d₁) = Trans Cata (Arr (soundness d) (soundness d₁))