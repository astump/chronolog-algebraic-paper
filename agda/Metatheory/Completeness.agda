open import lib
open import Tp
open import Declarative
open import Decproc

module Metatheory.Completeness where

completeness : ∀{T T' : Tp} →
               T <: T' →
               T <:: T'
completeness Refl = Refl
completeness (Arr d d₁) = Arr (completeness d) (completeness d₁)
completeness Roll = roll
completeness Unroll = unroll
completeness (Cov d) = Cov (completeness d)
completeness (Trans d d₁) = trans<:: (completeness d) (completeness d₁)
completeness Cata = Cata refl<:: refl<::
completeness (Alg d) = Alg (completeness d)
completeness ReflV = ReflV
completeness ReflR = ReflR