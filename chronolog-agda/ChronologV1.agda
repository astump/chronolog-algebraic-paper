module ChronologV1 where

--------------------------------------------------------------------------------

infixr 9 _`→_
infix 5 _<:_

--------------------------------------------------------------------------------

data Ty : Set where
    `C : Ty
    `D : Ty
    `F : Ty → Ty 
    `A : Ty → Ty
    _`→_ : Ty → Ty → Ty

--------------------------------------------------------------------------------

data _<:_ : Ty → Ty → Set where
    ReflD : `D <: `D
    ReflC : `C <: `C
    Arrow : ∀ {X X′ Y Y′} → X′ <: X → Y <: Y′ → X `→ Y <: X′ `→ Y′
    Roll : ∀ {X} → X <: `D → `F X <: `D
    Unroll : ∀ {X} → `D <: X → `D <: `F X
    Cov : ∀ {X Y} → X <: Y → `F X <: `F Y
    Cata : ∀ {X} → `A X <: `D `→ X
    Alg : ∀ {X Y} → X <: Y → `A X <: `A Y

refl<: : ∀ {X} → X <: X
refl<: {`C} = ReflC
refl<: {`D} = ReflD
refl<: {`F X} = Cov refl<:
refl<: {`A X} = Alg refl<:
refl<: {X `→ Y} = Arrow refl<: refl<:

roll : `F `D <: `D
roll = Roll ReflD

unroll : `D <: `F `D
unroll = Unroll ReflD
