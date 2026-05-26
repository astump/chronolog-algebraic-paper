-- trying to analyze the situation where there are multiple solutions to a constraint with variables

module Solutions where

open import lib
open import Tp
open import Decproc

{- these are the forms of goals suspended when we call Chronolog -}
suspended : Tp → Tp → 𝔹
suspended (V _) (V _) = tt
suspended (V _) μD = tt
suspended μD (V _) = tt
suspended (D A) (V _) = tt
suspended (V _) (D A) = tt
suspended _ _ = ff

-- a solution is an association list from variable numbers to types.
solution : Set
solution = 𝕃 (ℕ × Tp)

Equiv : Tp → Tp → Set
Equiv T1 T2 = (T1 <:: T2) × (T2 <:: T1)

lookup : solution → ℕ → Tp
lookup [] x = V x
lookup ((n , T) :: s) x = if n =ℕ x then T else lookup s x

subst : solution → Tp → Tp
subst s (D T) = D (subst s T)
subst s (T1 ⟶ T2) = (subst s T1) ⟶ (subst s T2)
subst s (D⇒ T) = D⇒ (subst s T)
subst s μD = μD
subst s (V x) = lookup s x

UniqueSolutions : ∀{T1 T2 : Tp}{s s' : solution} →
                  (suspended T1 T2 ≡ tt → subst s T1 ≡ subst s' T1 ∧ subst s T2 ≡ subst s' T2) → 
                  subst s T1 <:: subst s T2 →
                  subst s' T1 <:: subst s' T2 →
                  Equiv (subst s T1) (subst s' T1) ∧ Equiv (subst s T2) (subst s' T2)
UniqueSolutions {D T1} {D T2} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {D T1} {μD} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {D T1} {V x} {s} {s'} u d1 d2 with u refl
UniqueSolutions {D T1} {V x} {s} {s'} u d1 d2 | r1 , r2 rewrite r1 | r2 = (refl<:: , refl<::) , (refl<:: , refl<::)
UniqueSolutions {T1 ⟶ T2} {T3 ⟶ T4} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {T1 ⟶ T2} {V x} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {D⇒ T1} {T2 ⟶ T3} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {D⇒ T1} {D⇒ T2} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {D⇒ T1} {V x} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {μD} {D T2} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {μD} {μD} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {μD} {V x} {s} {s'} u d1 d2 with u refl
UniqueSolutions {μD} {V x} {s} {s'} u d1 d2 | r1 , r2 rewrite r1 | r2 = (refl<:: , refl<::) , (refl<:: , refl<::)
UniqueSolutions {V x} {D T2} {s} {s'} u d1 d2 with u refl
UniqueSolutions {V x} {D T2} {s} {s'} u d1 d2 | r1 , r2 rewrite r1 | r2 = (refl<:: , refl<::) , (refl<:: , refl<::)
UniqueSolutions {V x} {T2 ⟶ T3} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {V x} {D⇒ T2} {s} {s'} u d1 d2 = {!!}
UniqueSolutions {V x} {μD} {s} {s'} u d1 d2 with u refl
UniqueSolutions {V x} {μD} {s} {s'} u d1 d2 | r1 , r2 rewrite r1 | r2 = (refl<:: , refl<::) , (refl<:: , refl<::)
UniqueSolutions {V x} {V x₁} {s} {s'} u d1 d2 with u refl
UniqueSolutions {V x} {V x₁} {s} {s'} u d1 d2 | r1 , r2 rewrite r1 | r2 = (refl<:: , refl<::) , (refl<:: , refl<::)