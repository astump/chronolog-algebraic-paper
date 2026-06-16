module Constraint where

open import lib
open import Tp

infix 7 _◃_

data Constraint : Set where
  _◃_ : Tp → Tp → Constraint

Constraints : Set
Constraints = 𝕃 Constraint
infix 7 _↦_ 

data Binding : Set where
  _↦_ : ℕ → Tp → Binding

Bindings : Set
Bindings = 𝕃 Binding

lookup : Bindings → ℕ → Tp
lookup [] y = V y
lookup (x ↦ T :: bs) y =
 if x =ℕ y then
   T
 else
   lookup bs y    

subst : Bindings → Tp → Tp
subst bs (D T) = D (subst bs T)
subst bs (T ⟶ T') = subst bs T ⟶ subst bs T'
subst bs (D⇒ T) = D⇒ (subst bs T)
subst bs (V x) = lookup bs x
subst _ μD = μD
subst _ (R x) = R x

substC : Bindings → Constraint → Constraint
substC bs (T ◃ T') = subst bs T ◃ subst bs T'

substCs : Bindings → Constraints → Constraints
substCs bs = map (substC bs)