module ChronologV1 (Name : Set) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Maybe using (Maybe; nothing; just; map; ap; _>>=_; maybe; fromMaybe)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Axiom.Extensionality.Propositional using (Extensionality)

--------------------------------------------------------------------------------

data Justly {A} : Maybe A → Set where
    justly : ∀ {a} → Justly (just a)

--------------------------------------------------------------------------------

infixr 9 _⇒_
infix 5 _<:_ _<:+_
infix 4 _⊏<:+_⟨_⟩ _⊏State_

--------------------------------------------------------------------------------
-- types
--------------------------------------------------------------------------------

data Ty : Set where
    C : Ty
    D : Ty
    F : Ty → Ty 
    A : Ty → Ty
    _⇒_ : Ty → Ty → Ty

--------------------------------------------------------------------------------
-- subtyping
--------------------------------------------------------------------------------

data _<:_ : Ty → Ty → Set where
    ReflD : D <: D
    ReflC : C <: C
    Arrow : ∀ {X X′ Y Y′} → X′ <: X → Y <: Y′ → X ⇒ Y <: X′ ⇒ Y′
    Roll : ∀ {X} → X <: D → F X <: D
    Unroll : ∀ {X} → D <: X → D <: F X
    Cov : ∀ {X Y} → X <: Y → F X <: F Y
    Cata : ∀ {X} → A X <: D ⇒ X
    Alg : ∀ {X Y} → X <: Y → A X <: A Y

refl<: : ∀ {X} → X <: X
refl<: {C} = ReflC
refl<: {D} = ReflD
refl<: {F X} = Cov refl<:
refl<: {A X} = Alg refl<:
refl<: {X ⇒ Y} = Arrow refl<: refl<:

roll : F D <: D
roll = Roll ReflD

unroll : D <: F D
unroll = Unroll ReflD

--------------------------------------------------------------------------------
-- types with metavariables
--------------------------------------------------------------------------------

data Ty+ : Set where
    C+ : Ty+
    D+ : Ty+
    F+ : Ty+ → Ty+ 
    A+ : Ty+ → Ty+
    _⇒+_ : Ty+ → Ty+ → Ty+
    M : Name → Ty+

fromTy+ : Ty+ → Maybe Ty
fromTy+ C+ = just C
fromTy+ D+ = just D
fromTy+ (F+ x) = map F (fromTy+ x)
fromTy+ (A+ x) = map A (fromTy+ x)
fromTy+ (x ⇒+ y) = ap (map _⇒_ (fromTy+ x)) (fromTy+ y)
fromTy+ (M x) = nothing

--------------------------------------------------------------------------------
-- subtyping with holes
--------------------------------------------------------------------------------

data _<:+_ : Ty+ → Ty+ → Set where
    ReflD+ : D+ <:+ D+
    ReflC+ : C+ <:+ C+
    Arrow+ : ∀ {X₁ X₂ Y₁ Y₂} → X₂ <:+ X₁ → Y₁ <:+ Y₂ → X₁ ⇒+ Y₁ <:+ X₂ ⇒+ Y₂
    Roll+ : ∀ {X} → X <:+ D+ → F+ X <:+ D+
    Unroll+ : ∀ {X} → D+ <:+ X → D+ <:+ F+ X
    Cov+ : ∀ {X Y} → X <:+ Y → F+ X <:+ F+ Y
    Cata+ : ∀ {X} → A+ X <:+ D+ ⇒+ X
    Alg+ : ∀ {X Y} → X <:+ Y → A+ X <:+ A+ Y
    Hole : ∀ {X Y} → X <:+ Y

--------------------------------------------------------------------------------

State : Set
State = Σ Ty+ λ X → Σ Ty+ λ Y → X <:+ Y

Sub : Set
Sub = Name → Maybe Ty+

subTy+ : Sub → Ty+ → Ty+
subTy+ s C+ = C+
subTy+ s D+ = D+
subTy+ s (F+ x) = F+ (subTy+ s x)
subTy+ s (A+ x) = A+ (subTy+ s x)
subTy+ s (x ⇒+ y) = subTy+ s x ⇒+ subTy+ s y
subTy+ s (M x) = maybe (λ y → y) (M x) (s x)

postulate -- TODO
    sub<:+ : ∀ {X Y} (s : Sub) → X <:+ Y → subTy+ s X <:+ subTy+ s Y

subState : Sub → State → State
subState s (X , Y , drv) = subTy+ s X , subTy+ s Y , sub<:+ s drv

data IsHole : ∀ {X Y} → X <:+ Y → Set where
    is-Hole : ∀ {X Y} → IsHole {X} {Y} Hole

-- The Bool reflects whether or not this is a strict refinement (non-equivalence). The only way for this to be a strict refinement is to use the `⊏Fill` construct at least once, which fills a derivation hole with a non-hole derivation.
data _⊏<:+_⟨_⟩ : ∀ {X Y} → X <:+ Y → X <:+ Y → Bool → Set where
    -- These are just injections of the constructors from `_<:+_`.
    ⊏ReflD+ : ReflD+ ⊏<:+ ReflD+ ⟨ false ⟩
    ⊏ReflC+ : ReflC+ ⊏<:+ ReflC+ ⟨ false ⟩
    ⊏Arrow+ : ∀ {X₁ X₂ Y₁ Y₂} {drv₁ drv₁′ : X₁ <:+ Y₁} {drv₂ drv₂′ : X₂ <:+ Y₂} {b₁ b₂} → 
        drv₁ ⊏<:+ drv₁′ ⟨ b₁ ⟩ →
        drv₂ ⊏<:+ drv₂′ ⟨ b₂ ⟩ →
        Arrow+ drv₁ drv₂ ⊏<:+ Arrow+ drv₁′ drv₂′ ⟨ b₁ ∨ b₂ ⟩
    ⊏Roll+ : ∀ {X} {drv drv′ : X <:+ D+} {b} →
        drv ⊏<:+ drv′ ⟨ b ⟩ →
        Roll+ drv ⊏<:+ Roll+ drv′ ⟨ b ⟩
    ⊏Unroll+ : ∀ {X} {drv drv′ : D+ <:+ X} {b} →
        drv ⊏<:+ drv′ ⟨ b ⟩ →
        Unroll+ drv ⊏<:+ Unroll+ drv′ ⟨ b ⟩
    ⊏Cov+ : ∀ {X Y} {drv drv′ : X <:+ Y} {b} →
        drv ⊏<:+ drv′ ⟨ b ⟩ →
        Cov+ drv ⊏<:+ Cov+ drv′ ⟨ b ⟩
    ⊏Cata+ : ∀ {X} → Cata+ {X} ⊏<:+ Cata+ ⟨ false ⟩
    ⊏Alg+ : ∀ {X Y} {drv drv′ : X <:+ A+ Y} {b} →
        drv ⊏<:+ drv′ ⟨ b ⟩ →
        Alg+ drv ⊏<:+ Alg+ drv′ ⟨ b ⟩
    ⊏Hole : ∀ {X Y} → Hole {X} {Y} ⊏<:+ Hole ⟨ false ⟩

    -- Any concrete derivation is more specific than Hole.
    ⊏Fill : ∀ {X Y} (drv : X <:+ Y) → ¬ (IsHole drv) → Hole ⊏<:+ drv ⟨ true ⟩

-- A state `st1` is refined by another state `st2` if `st2` is the same as `st1` with a metavariable substitution applied to it and any holes filled.
data _⊏State_ : State → State → Set where
    -- Substitute metavariables and fill holes at the same time.
    mk⊏State : ∀ {X Y} {drv₁ : X <:+ Y} (s : Sub) {drv₂ : subTy+ s X <:+ subTy+ s Y} {b} →
        sub<:+ s drv₁ ⊏<:+ drv₂ ⟨ b ⟩ →
        (X , Y , drv₁) ⊏State (subTy+ s X , subTy+ s Y , drv₂)

postulate -- TODO
    -- Whether or not a subtyping constraint between these types should be suspended.
    suspended : Ty+ → Ty+ → Bool

data Stagnant<:+ : ∀ {X Y} → X <:+ Y → Set where
    StagnantReflD+ : Stagnant<:+ ReflD+
    StagnantReflC+ : Stagnant<:+ ReflC+
    StagnantArrow+ : ∀ {X₁ X₂ Y₁ Y₂} {drv₁ : X₁ <:+ Y₁} {drv₂ : X₂ <:+ Y₂} → Stagnant<:+ (Arrow+ drv₁ drv₂)
    StagnantRoll+ : ∀ {X} {drv : X <:+ D+} → Stagnant<:+ (Roll+ drv)
    StagnantUnroll+ : ∀ {X} {drv : D+ <:+ X} → Stagnant<:+ (Unroll+ drv)
    StagnantCov+ : ∀ {X Y} {drv : X <:+ Y} → Stagnant<:+ (Cov+ drv)
    StagnantCata+ : ∀ {X} → Stagnant<:+ (Cata+ {X})
    StagnantAlg+ : ∀ {X Y} {drv : X <:+ Y} → Stagnant<:+ (Alg+ drv)
    -- A derivation hole must have a suspended goal in order for the derivation to be stagnant. If the goal isn't suspended, then actually the result should have been failure rather than stagnation.
    StagnantHole : ∀ {X Y} → 
        suspended X Y ≡ true →
        Stagnant<:+ (Hole {X} {Y})

data StagnantState : State → Set where
    mkStagnantState : ∀ {X Y} {drv : X <:+ Y} →
        Stagnant<:+ drv →
        StagnantState (X , Y , drv)

data SolveStepResult : Set where
    progress : State → SolveStepResult
    stagnation : SolveStepResult
    failure : SolveStepResult

data SolveBlockResult : Set where
    success : State → SolveBlockResult
    failure : SolveBlockResult

-- Attempts to fill an active hole with a subtyping rule.
postulate
    solve-inner-step : State → SolveStepResult

    solve-inner-step-progress-refinement : ∀ {st₁ st₂} → 
        solve-inner-step st₁ ≡ progress st₂ →
        st₁ ⊏State st₂

    solver-inner-step-stagnation : ∀ {st} →
        solve-inner-step st ≡ stagnation →
        StagnantState st

-- Repeatedly `solve-inner-step` until stagnation or failure.
-- TODO: how to formally address termination argument here? We know that we have to make progress each time when filling holes via `solve-inner-step`, so there's definitely a way of expressing that as refinements of the derivations.
{-# TERMINATING #-}
solve-inner-block : State → SolveBlockResult
solve-inner-block st with solve-inner-step st 
solve-inner-block st | progress st′ = solve-inner-block st′
solve-inner-block st | stagnation = success st
solve-inner-block st | failure = failure

postulate -- TODO
    -- Refines the state by applying a metavariable substitution.
    solve-outer : State → SolveBlockResult

postulate
    solve : ∀ X Y → Maybe (X <: Y)

postulate
    completeness : ∀ {X Y} → X <: Y → Justly (solve X Y)
