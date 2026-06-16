module Solving where

open import lib
open import Constraint
open import Tp
open import Decproc

infix 5 _!_↝_!_-_ 

{- A relation

   nv ! c ↝ nv' ! cs - bs

   for one step of nondeterministically breaking down a constraint c into constraints cs.
   The parameters are

   nv  the next number to use for a fresh variable (introduced when breaking down some constraints)
   c   the constraint to break down
   nv' the new number to use for other fresh variables (it will be greater than or equal to nv)
   cs  the constraints resulting from breaking down c
   bs  instantiations of variables X, introduced where we refine X (for example, refine X to a function type)

   Note that constraints which are not in the domain of this relation
   may be unsolvable or may correspond to ones which we suspend during solving.
   We will treat the latter separately.
-}
data _!_↝_!_-_ : ℕ → Constraint → ℕ → Constraints → Bindings → Set where

  -- rules that are abstractions of the arrow subtyping rule
  Arr : ∀{nv : ℕ}{T1 T2 T1' T2' : Tp} →
        nv ! T1 ⟶ T2 ◃ T1' ⟶ T2'  ↝  nv ! (T1' ◃ T1) :: [ T2 ◃ T2' ] - []
  ArrV1 : ∀{nv n : ℕ}{T1 T2 : Tp} →
          nv ! V n ◃ T1 ⟶ T2  ↝  2 + nv ! (T1 ◃ V nv) :: [  V (suc nv) ◃ T2 ] - [ n ↦ V nv ⟶ V (suc nv) ]
  ArrV2 : ∀{nv n : ℕ}{T1 T2 : Tp} →
          nv ! T1 ⟶ T2 ◃ V n  ↝  2 + nv ! (V nv ◃ T1) :: [ T2 ◃ V (suc nv) ] - [ n ↦ V nv ⟶ V (suc nv) ]
  
  -- rules that are abstractions of the Cata subtyping rule
  Cata : ∀{nv : ℕ}{T T1 T2 : Tp} →
          nv ! D⇒ T ◃ T1 ⟶ T2  ↝  nv ! (T1 ◃ μD) :: [ T ◃ T2 ] - []
  CataV1 : ∀{nv n : ℕ}{T1 T2 : Tp} →
           nv ! V n ◃ T1 ⟶ T2  ↝  suc nv ! (T1 ◃ μD) :: [  V nv ◃ T2 ] - [ n ↦ D⇒ (V nv) ]
  CataV2 : ∀{nv n : ℕ}{T T1 T2 : Tp} →
           nv ! D⇒ T ◃ V n  ↝  2 + nv ! (V nv ◃ μD) :: [ T ◃ V (suc nv) ] - [ n ↦ V nv ⟶ V (suc nv)]
     
  -- similar for Roll.  When either side is a variable, we would suspend, so those cases do not appear
  Roll : ∀{nv : ℕ}{T : Tp} →
          nv ! D T ◃ μD  ↝  nv ! [ T ◃ μD ] - []

  -- for Unroll, again suspending when either side is a variable
  Unroll : ∀{nv : ℕ}{T : Tp} →
           nv ! μD ◃ D T  ↝  nv ! [ μD ◃ T ] - []

  -- for Cov.  We suspend when either side is a variable
  Cov : ∀{nv : ℕ}{T T' : Tp} →
        nv ! D T ◃ D T'  ↝  nv ! [ T ◃ T' ] - []

  -- for Alg.
  Alg : ∀{nv : ℕ}{T T' : Tp} →
        nv ! D⇒ T ◃ D⇒ T'  ↝  nv ! [ T ◃ T' ] - []
  AlgV1 : ∀{n nv : ℕ}{T T' : Tp} →
          nv ! V n ◃ D⇒ T'  ↝  suc nv ! [ V nv ◃ T' ] - [ n ↦ D⇒ (V nv) ]
  AlgV2 : ∀{n nv : ℕ}{T T' : Tp} →
          nv ! D⇒ T' ◃ V n  ↝  suc nv ! [ T' ◃ V nv ] - [ n ↦ D⇒ (V nv) ]

{- non-deterministically reducing a set of constraints -}
data _!_-_↝⋆_!_-_ : ℕ → Constraints → Bindings → ℕ → Constraints → Bindings → Set where
  Refl : ∀{nv : ℕ}{cs : Constraints}{bs : Bindings} →
         nv ! cs - bs ↝⋆ nv ! cs - bs
  Trans : ∀{nv nv' nv'' : ℕ}{c : Constraint}{cs1 cs2 cs cs' : Constraints}{bs bs' bs'' : Bindings} →
          nv' ! cs1 ++ cs ++ cs2 - bs ++ bs'  ↝⋆  nv'' ! cs' - bs'' →
          nv  ! substC bs c                   ↝   nv'  ! cs - bs' →
          nv  ! cs1 ++ c  :: cs2 - bs         ↝⋆  nv'' ! cs' - bs''

{-
step : ∀{nv nv' : ℕ}{c : Constraint}{cs cs' : Constraints}{bs : Bindings} →
       nv ! c ↝ nv'  ! cs - bs →
       nv ! c :: cs' ↝⋆ nv'  ! cs ++ cs' - bs 
step{nv}{nv'}{c}{cs}{cs'}{bs} d = q
  where p : nv ! c :: cs' ↝⋆ nv' ! cs ++ cs' - (bs ++ [])
        p = Trans{nv}{nv'}{nv'}{c}{[]}{cs'}{cs}{cs ++ cs'}{bs}{[]} d Refl
        q : nv ! c :: cs' ↝⋆ nv' ! cs ++ cs' - bs
        q rewrite sym (++[] bs) = p
-}

infix 5 _⊣

{- constraints in ↝-normal form -}
_⊣ : Constraints → Set
cs ⊣ = ∀ {nv nv' : ℕ}{cs' : Constraints}{bs bs' : Bindings} →
          nv ! cs - bs ↝⋆ nv' ! cs' - bs'   →   cs ≡ cs'

infix 5 _!_-_↝ⁿ_!_-_

{- reduction to normal form -}
_!_-_↝ⁿ_!_-_ : ℕ → Constraints → Bindings → ℕ → Constraints → Bindings → Set
nv ! cs - bs ↝ⁿ nv' ! cs' - bs' = nv ! cs - bs ↝⋆ nv' ! cs' - bs'   ∧   cs' ⊣

{- weights of types and constraints -}
wt : Tp → ℕ
wt (D T) = suc (wt T)
wt (T ⟶ T₁) = suc (wt T + wt T₁)
wt (D⇒ T) = suc (wt T)
wt μD = 0
wt (V x) = 0
wt (R x) = 0

wtC : Constraint → ℕ
wtC (x ◃ x₁) = wt x + wt x₁

wtCs : Constraints → ℕ
wtCs = foldr (λ c w → wtC c + w) 0

{- the ↝ relation decreases the measure -}
decreaseLem : ∀{nv nv' : ℕ}{c : Constraint}{cs' : Constraints}{bs' : Bindings} →
              nv ! c ↝ nv' ! cs' - bs' →
              wtC c > wtCs cs' ≡ tt
decreaseLem (Arr{T1 = T1}{T2}{T1'}{T2'}) rewrite +0 (wt T2') | +0 (wt T2 + wt T2') | +comm (wt T1') (wt T1)
  | sym (+assoc (wt T1) (wt T1') (wt T2 + wt T2')) | +perm (wt T1') (wt T2) (wt T2')
  | +assoc (wt T1) (wt T2) (wt T1' + wt T2') | +suc (wt T1 + wt T2) (wt T1' + wt T2')
  = let q = wt T1 + wt T2 + (wt T1' + wt T2') in
      <-trans{q} (<-suc q) (<-suc (suc q))
decreaseLem (ArrV1{T1 = T1}{T2}) rewrite +0 (wt T2) | +0 (wt T1) = <-suc (wt T1 + wt T2)
decreaseLem (ArrV2{T1 = T1}{T2}) rewrite +0 (wt T2) | +0 (wt T2) | +0 (wt T1 + wt T2) =
 <-suc (wt T1 + wt T2)
decreaseLem (Cata{T = T}{T1}{T2}) rewrite +0 (wt T2) | +0 (wt T1) | +0 (wt T + wt T2) |
  +suc (wt T) (wt T1 + wt T2) | +perm (wt T1) (wt T) (wt T2) = 
  let q = wt T + (wt T1 + wt T2) in
   <-trans{q} (<-suc q) (<-suc (suc q))
decreaseLem (CataV1{T1 = T1}{T2}) rewrite +0 (wt T2) | +0 (wt T1) = <-suc (wt T1 + wt T2)
decreaseLem (CataV2{T = T}) rewrite +0 (wt T) | +0 (wt T) = <-suc (wt T)
decreaseLem (Roll{T = T}) rewrite +0 (wt T) | +0 (wt T) = <-suc (wt T)
decreaseLem (Unroll{T = T}) rewrite +0 (wt T) | +0 (wt T) = <-suc (wt T)
decreaseLem (Cov{T = T}{T'}) rewrite +0 (wt T) | +0 (wt T + wt T') | +suc (wt T) (wt T') =
  let q = wt T + wt T' in
   <-trans{q} (<-suc q) (<-suc (suc q))
decreaseLem (Alg{T = T}{T'}) rewrite +0 (wt T) | +0 (wt T + wt T') | +suc (wt T) (wt T') =
  let q = wt T + wt T' in
   <-trans{q} (<-suc q) (<-suc (suc q))
decreaseLem (AlgV1{T' = T'}) rewrite +0 (wt T') = <-suc (wt T')
decreaseLem (AlgV2{T' = T'}) rewrite +0 (wt T') | +0 (wt T') = <-suc (wt T')

infix 5 _↝s_

data _↝s_ : Constraint → Bindings → Set where
  Var-μD     : ∀{x : ℕ}   →           V x ◃ μD   ↝s  [ x ↦ μD ]
  μD-Var     : ∀{x : ℕ}   →           μD  ◃ V x  ↝s  [ x ↦ μD ]
  Var-R      : ∀{x r : ℕ} →           V x ◃ R r  ↝s  [ x ↦ R r ]
  R-Var      : ∀{x r : ℕ} →           R r ◃ V x  ↝s  [ x ↦ R r ]
  Var-Var    : ∀{x y : ℕ} →  x ≢ y →  V x ◃ V y  ↝s  [ x ↦ V y ]
  Var-D-Var1 : ∀{x y k : ℕ} →         V x ◃ iter k D_ (V y) ↝s x ↦ μD :: [ y ↦ μD ]
  Var-D-Var2 : ∀{x y k : ℕ} →         iter k D_ (V x) ◃ V y ↝s x ↦ μD :: [ y ↦ μD ]
  Var-D-μ1   : ∀{x y k : ℕ} →         V x ◃ iter k D_ μD    ↝s [ x ↦ μD ]
  Var-D-μ2   : ∀{x y k : ℕ} →         iter k D_ μD ◃ V x    ↝s [ x ↦ μD ]  
  Refl       :                        μD ◃ μD    ↝s  []
  ReflV      : ∀{x : ℕ} →             V x ◃ V x  ↝s  []
  ReflR      : ∀{r : ℕ} →             R r ◃ R r  ↝s  []    

infix 5 _↝s⋆_

data _↝s⋆_ : Constraints → Bindings → Set where
  Refl : [] ↝s⋆ []
  Trans : ∀{c : Constraint}{cs : Constraints}
           {bs bs' : Bindings} →
           c ↝s bs →
           substCs bs cs ↝s⋆ bs' → 
           c :: cs ↝s⋆ bs ++ bs'

infix 5 _⊨_

_⊨_ : Bindings → Constraint → Set
bs ⊨ T ◃ T' = subst bs T <:: subst bs T'

_⊨⋆_ : Bindings → Constraints → Set
bs ⊨⋆ [] = ⊤
bs ⊨⋆ (c :: cs) = bs ⊨ c ∧ bs ⊨⋆ cs


↝s⊨ : ∀{cs : Constraints}{bs bs' : Bindings} →
       substCs bs cs ↝s⋆ bs' →
       (bs ++ bs') ⊨⋆ cs
↝s⊨ {[]} d = triv
↝s⊨ {D T ◃ V x :: cs} (Trans d d') = {!!}
↝s⊨ {T ⟶ T₁ ◃ V x :: cs} (Trans d d') = {!!}
↝s⊨ {D⇒ T ◃ V x :: cs} (Trans d d') = {!!}
↝s⊨ {μD ◃ V x :: cs} (Trans d d') = {!!}
↝s⊨ {V x ◃ D T' :: cs} (Trans d d') = {!!}
↝s⊨ {V x ◃ T' ⟶ T'' :: cs} (Trans d d') = {!!}
↝s⊨ {V x ◃ D⇒ T' :: cs} (Trans d d') = {!!}
↝s⊨ {V x ◃ μD :: cs} (Trans d d') = {!!}
↝s⊨ {V x ◃ V x₁ :: cs} (Trans d d') = {!!}
↝s⊨ {V x ◃ R x₁ :: cs} (Trans d d') = {!!}
↝s⊨ {R x ◃ V x₁ :: cs} (Trans d d') = {!!}