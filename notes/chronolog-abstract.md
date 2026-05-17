# Abstract Typechecking with Chronolog

In the new type system, the use of Chronolog slightly changes.

## Definitions

- `D` is the datatype
- `F` is the signature functor of `D`
- `C` is the type constant
- `Alg` is the algebra type family

## Suspension Predicate

A goal should be suspended if it has any of these forms:

- `?x <: R`
- `?x <: D` or `D <: ?x` where `?x` is a metavariable
- `?x <: F y` or `F y <: ?x` where `?x` is a metavariable
- `?x <: y`
- `?x <: C` or `C <: ?x`

## Subtype Checking

A suspended goal is processed by the outer loop of the subtype checker in these cases:

- `a <: a` => trivial
- `?x <: C` or `C <: ?x` => `?x := C`
- `?x <: R` => `?x := R`
- `D <: ?x` => `?x := D`
- `F ?x <: ?y` => `?y := F ?z`
- `R <: ?x` => `?x := R`
- `?x <: F ?y` => `?x := F ?z`
- `?x <: D` => `?x := D`
- `?x <: ?y` => `?x := ?y`
