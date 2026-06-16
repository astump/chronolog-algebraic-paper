-- constraint-generating type inference for Tms

module ConstraintGenerating where

open import lib hiding (_>>=_ ; return )
open import Tp
open import Tm
open import Monad
open import Constraint

data ≫Mdata (A : Set) : Set where
  ≫mdata : (v : A) → (n : ℕ) → (cs : Constraints) → ≫Mdata A

data ≫M (A : Set) : Set where
  ≫m : (s : (n : ℕ) {- next var num -} → ≫Mdata A) → ≫M A

infixr 7 _>>=M_ 

_>>=M_ : ∀{A B : Set} → ≫M A → (A → ≫M B) → ≫M B
_>>=M_{A}{B} (≫m s) f = ≫m λ n → connect (s n) 
  where connect : ≫Mdata A →  ≫Mdata B
        connect (≫mdata v n' cs) with f v
        connect (≫mdata v n' cs) | ≫m f1 with f1 n'
        connect (≫mdata v n' cs) | ≫m f1 | ≫mdata v' n'' cs' = ≫mdata v' n'' (cs ++ cs')

returnM : ∀{A : Set} → A → ≫M A
returnM v = ≫m (λ n → ≫mdata v n [])

freshvar : ≫M ℕ
freshvar = ≫m (λ n → ≫mdata n (suc n) [])

addConstraint : Tp → Tp → ≫M ⊤
addConstraint T1 T2 = ≫m (λ n → ≫mdata triv n [ Constr T1 T2 ])

instance
  ≫Monad : Monad ≫M
  ≫Monad = record { return = returnM ; _>>=_ = _>>=M_ }

gen : Tm → ≫M Tp 
gen S =
  do
    a ← freshvar
    b ← freshvar    
    c ← freshvar
    return ((V c ⟶ V b ⟶ V a) ⟶ (V c ⟶ V b) ⟶ V c ⟶ V a)

gen K = 
  do
    a ← freshvar
    b ← freshvar    
    return (V a ⟶ V b ⟶ V a)

gen (t1 · t2) = 
  do
    a ← freshvar
    T1 ← gen t1 
    T2 ← gen t2
    _ ← addConstraint T1 (T2 ⟶ V a)
    return (V a)

gen Suc =
  do
    a ← freshvar
    return (V a ⟶ D (V a))

gen Zero = 
  do
    a ← freshvar
    return (D (V a))

gen (Case t1 t2 t3) =
  do
    T1 ← gen t1
    T2 ← gen t2
    T3 ← gen t3
    a ← freshvar
    x ← freshvar    
    _ ← addConstraint T1 (D (V a))
    _ ← addConstraint T2 (V x)
    _ ← addConstraint T2 (V a ⟶ V x)
    return (V x)

gen (Alg t) =
  do
    T ← gen t
    x ← freshvar
    r ← freshvar
    _ ← addConstraint T ((R r ⟶ V x) ⟶ D (V r) ⟶ V x)
    return (V x)
