module Interp where

open import lib hiding (_>>=_ ; return ; _∘_ ; ↓ )
open import Monad
open import Tm

data Val : Set where
  S : Val
  K : Val
  K1 : Val → Val
  S1 : Val → Val
  S2 : Val → Val → Val
  Cons : Val
  Cons1 : Val → Val
  Cons2 : Val → Val → Val  
  Nil : Val
  In : Val → Val
  Alg : Val

infixl 8 _∘_

infixl 9 ↓_

↓_ : Val → Tm
↓ S = S
↓ K = S
↓ K1 v = K · ↓ v
↓ S1 v = S · ↓ v
↓ S2 v v₁ = S · ↓ v · ↓ v₁
↓ Cons = Cons
↓ Cons1 v = Cons · ↓ v
↓ Cons2 v v₁ = Cons · ↓ v · ↓ v₁
↓ Nil = Nil
↓ In v = In (↓ v)

_∘_ : Val → Val → Tm
v ∘ v' = ↓ v · ↓ v'

data Result (A : Set) : Set where
  Answer : A → Result A
  Fail : Result A
  Unfinished : Result A

infixr 8 _>>=r_

_>>=r_ : ∀{A B : Set} → Result A → (A → Result B) → Result B
Answer x >>=r r = r x 
Fail >>=r r = Fail
Unfinished >>=r r' = Unfinished

returnr : ∀{A : Set} → A → Result A
returnr = Answer

instance
  RMonad : Monad Result 
  RMonad = record { return = returnr ; _>>=_ = _>>=r_ }

mutual
 interp : ℕ → Tm → Result Val
 interp 0 _ = Unfinished
 interp (suc n) S = return S
 interp (suc n) K = return K
 interp (suc n) (t · t₁) =
  do
    r ← interp n t
    r₁ ← interp n t₁
    app n r r₁
 interp (suc n) Cons = return Cons
 interp (suc n) Nil = return Nil
 interp (suc n) (In t) =
  do
    r ← interp n t
    return (In r)
 interp (suc n) (Case t t₁ t₂) =
  do
    r ← interp n t
    r₁ ← interp n t₁
    r₂ ← interp n t₂
    case n r r₁ r₂

 app : ℕ → Val → Val → Result Val
 app n S v' = return (S1 v')
 app n K v' = return (K1 v')
 app n (K1 v) v' = return v
 app n (S1 v) v' = return (S2 v v')
 app n (S2 v v₁) v' = interp n (v ∘ v' · (v₁ ∘ v'))
 app n Cons v' = return (Cons1 v')
 app n (Cons1 v) v' = return (Cons2 v v')
 app n (Cons2 v v₁) v' = Fail
 app n Nil v' = Fail
 app n (In v) v' = Fail

 case : ℕ → Val → Val → Val → Result Val
 case n S cn cc = Fail
 case n K cn cc = Fail
 case n (K1 scrut) cn cc = Fail
 case n (S1 scrut) cn cc = Fail
 case n (S2 scrut scrut₁) cn cc = Fail
 case n Cons cn cc = Fail
 case n (Cons1 scrut) cn cc = Fail
 case n (Cons2 scrut scrut₁) cn cc = interp n (cc ∘ scrut · ↓ scrut₁)
 case n Nil cn cc = return cn
 case n (In scrut) cn cc = case n scrut cn cc