open import lib
open import Tp

module Declarative where

infix 5 _<:_ 

data _<:_ : Tp → Tp → Set where
  Refl : μD <: μD
  Arr : ∀{T1 T2 T1' T2' : Tp} → 
         T1' <: T1 →
         T2 <: T2' →
         T1 ⟶ T2 <: T1' ⟶ T2'
  Roll : D μD <: μD  
  Unroll : μD <: D μD
  Cov : ∀{T1 T2 : Tp} → T1 <: T2 → D T1 <: D T2
  Trans : ∀{T1 T2 T3 : Tp} → T1 <: T2 → T2 <: T3 → T1 <: T3
  Cata : ∀{X : Tp} → D⇒ X <: μD ⟶ X
  Alg : ∀{T1 T2 : Tp} → T1 <: T2 → D⇒ T1 <: D⇒ T2

-- not actually needed for soundness or completeness
refl<: : ∀{T} → T <: T
refl<: {μD} = Refl
refl<: {D T} = Cov (refl<:{T})
refl<: {T ⟶ T'} = Arr (refl<:{T}) (refl<:{T'})
refl<: {D⇒ X} = Alg (refl<:{X})

roll1 : ∀{T : Tp} →
        T <: μD → 
        D T <: μD
roll1 Refl = Roll
roll1 Roll = Trans (Cov Roll) Roll
roll1 (Trans d d₁) = Trans (Cov d) (roll1 d₁)

roll2 : ∀{T : Tp} →
        μD <: T → 
        μD <: D T 
roll2 Refl = Unroll
roll2 Unroll = Trans Unroll (Cov Unroll)
roll2 (Trans d d₁) = Trans (roll2 d) (Cov d₁)