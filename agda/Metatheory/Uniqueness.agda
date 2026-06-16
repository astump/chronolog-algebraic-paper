module Metatheory.Uniqueness where

open import lib
open import Tp
open import Decproc

uniqueness : ∀{T1 T2 : Tp} →
              (d1 : T1 <:: T2) →
              (d2 : T1 <:: T2) →
              d1 ≡ d2
uniqueness {T1} {T2} Refl Refl = refl
uniqueness {T1} {T2} ReflV ReflV = refl
uniqueness {T1} {T2} ReflR ReflR = refl
uniqueness {T1} {T2} (Arr d1 d2) (Arr d3 d4) with uniqueness d1 d3 | uniqueness d2 d4
uniqueness {T1} {T2} (Arr d1 d2) (Arr d3 d4) | refl | refl = refl
uniqueness {T1} {T2} (Roll d1) (Roll d2) with uniqueness d1 d2
uniqueness {T1} {T2} (Roll d1) (Roll d2) | refl = refl
uniqueness {T1} {T2} (Unroll d1) (Unroll d2) with uniqueness d1 d2
uniqueness {T1} {T2} (Unroll d1) (Unroll d2) | refl = refl
uniqueness {T1} {T2} (Cov d1) (Cov d2) with uniqueness d1 d2
uniqueness {T1} {T2} (Cov d1) (Cov d2) | refl = refl
uniqueness {T1} {T2} (Alg d1) (Alg d2) with uniqueness d1 d2
uniqueness {T1} {T2} (Alg d1) (Alg d2) | refl = refl
uniqueness {T1} {T2} (Cata d1 d2) (Cata d3 d4) with uniqueness d1 d3 | uniqueness d2 d4
uniqueness {T1} {T2} (Cata d1 d2) (Cata d3 d4) | refl | refl = refl 