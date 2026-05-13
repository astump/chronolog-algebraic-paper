open import lib
open import Tp

module Declarative where

infix 5 _<:_ 

data _<:_ : Tp → Tp → Set where
  Refl : D <: D
  Fun : ∀{T1 T2 T1' T2' : Tp} → 
         T1' <: T1 →
         T2 <: T2' →
         T1 ⇒ T2 <: T1' ⇒ T2'
  Roll : F D <: D  
  Unroll : D <: F D
  Cov : ∀{T1 T2 : Tp} → T1 <: T2 → F T1 <: F T2
  Trans : ∀{T1 T2 T3 : Tp} → T1 <: T2 → T2 <: T3 → T1 <: T3

refl<: : ∀{T} → T <: T
refl<: {D} = Refl
refl<: {F T} = Cov (refl<:{T})
refl<: {T ⇒ T'} = Fun (refl<:{T}) (refl<:{T'})

roll1 : ∀{T : Tp} →
        T <: D → 
        F T <: D
roll1 Refl = Roll
roll1 Roll = Trans (Cov Roll) Roll
roll1 (Trans d d₁) = Trans (Cov d) (roll1 d₁)

roll2 : ∀{T : Tp} →
        D <: T → 
        D <: F T 
roll2 Refl = Unroll
roll2 Unroll = Trans Unroll (Cov Unroll)
roll2 (Trans d d₁) = Trans (roll2 d) (Cov d₁)