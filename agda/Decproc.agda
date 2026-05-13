open import lib
open import Tp

module Decproc where

infix 5 _<::_ 

data _<::_ : Tp → Tp → Set where
  Refl : D <:: D
  Fun : ∀{T1 T2 T1' T2' : Tp} → 
         T1' <:: T1 →
         T2 <:: T2' →
         T1 ⇒ T2 <:: T1' ⇒ T2'
  Roll1 : ∀ {T : Tp} → T <:: D → F T <:: D
  Roll2 : ∀ {T : Tp} → D <:: T → D <:: F T
  Cov : ∀{T1 T2 : Tp} → T1 <:: T2 → F T1 <:: F T2

refl<:: : ∀{T} → T <:: T
refl<:: {D} = Refl
refl<:: {F T} = Cov (refl<::{T})
refl<:: {T ⇒ T'} = Fun (refl<::{T}) (refl<::{T'})

trans<:: : ∀{T1 T2 T3 : Tp} →
          (d1 : T1 <:: T2) →
          (d2 : T2 <:: T3) →
          T1 <:: T3
trans<:: d Refl = d
trans<:: Refl d = d
trans<::(Fun d1 d2) (Fun d3 d4) =
  Fun (trans<:: d3 d1) (trans<:: d2 d4)
trans<:: (Roll1 d1) (Roll2 d2) = Cov (trans<:: d1 d2)
trans<:: (Roll2 d1) (Roll1 d2) = Refl
trans<:: (Roll2 d1) (Cov d2) = Roll2 (trans<:: d1 d2)
trans<:: (Cov d1) (Roll1 d2) = Roll1 (trans<:: d1 d2)
trans<:: (Cov d1) (Cov d2) = Cov (trans<:: d1 d2)

roll : F D <:: D
roll = Roll1 Refl

unroll : D <:: F D
unroll = Roll2 Refl