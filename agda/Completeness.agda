open import lib
open import Tp
open import Declarative
open import Decproc

module Completeness where

completeness : ∀{T T' : Tp} →
               T <: T' →
               T <:: T'
completeness Refl = Refl
completeness (Fun d d₁) = Fun (completeness d) (completeness d₁)
completeness Roll = roll
completeness Unroll = unroll
completeness (Cov d) = Cov (completeness d)
completeness (Trans d d₁) = trans<:: (completeness d) (completeness d₁)