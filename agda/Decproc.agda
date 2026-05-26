open import lib
open import Tp

module Decproc where

infix 5 _<::_ 

data _<::_ : Tp → Tp → Set where
  Refl : μD <:: μD
  ReflV : ∀{n : ℕ} → V n <:: V n
  Arr : ∀{T1 T2 T1' T2' : Tp} → 
         T1' <:: T1 →
         T2 <:: T2' →
         T1 ⟶ T2 <:: T1' ⟶ T2'
  Roll : ∀ {T : Tp} → T <:: μD → D T <:: μD
  Unroll : ∀ {T : Tp} → μD <:: T → μD <:: D T
  Cov : ∀{T1 T2 : Tp} → T1 <:: T2 → D T1 <:: D T2
  Alg : ∀{T1 T2 : Tp} → T1 <:: T2 → D⇒ T1 <:: D⇒ T2
  Cata : ∀{T T1 T2 : Tp} →
        T1 <:: μD →
        T <:: T2 →
        D⇒ T <:: T1 ⟶ T2  

refl<:: : ∀{T} → T <:: T
refl<:: {μD} = Refl
refl<:: {D T} = Cov (refl<::{T})
refl<:: {T ⟶ T'} = Arr (refl<::{T}) (refl<::{T'})
refl<:: {D⇒ T} = Alg (refl<::{T})
refl<:: {V n} = ReflV

trans<:: : ∀{T1 T2 T3 : Tp} →
          (d1 : T1 <:: T2) →
          (d2 : T2 <:: T3) →
          T1 <:: T3
trans<:: d Refl = d
trans<:: Refl d = d
trans<::(Arr d1 d2) (Arr d3 d4) = Arr (trans<:: d3 d1) (trans<:: d2 d4)
trans<:: (Roll d1) (Unroll d2) = Cov (trans<:: d1 d2)
trans<:: (Unroll d1) (Roll d2) = Refl
trans<:: (Unroll d1) (Cov d2) = Unroll (trans<:: d1 d2)
trans<:: (Cov d1) (Roll d2) = Roll (trans<:: d1 d2)
trans<:: (Cov d1) (Cov d2) = Cov (trans<:: d1 d2)
trans<:: (Alg d1) (Alg d2) = Alg (trans<:: d1 d2)
trans<:: (Alg d1) (Cata d2 d3) = Cata d2 (trans<:: d1 d3)
trans<:: (Cata d1 d2) (Arr d3 d4) = Cata (trans<:: d3 d1) (trans<:: d2 d4)
trans<:: ReflV ReflV = ReflV

roll : D μD <:: μD
roll = Roll Refl

unroll : μD <:: D μD
unroll = Unroll Refl