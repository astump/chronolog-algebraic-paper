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

A suspended goal is processed by the outer loop of the subtype checker in these
cases:

- `a <: a` => trivial
- `?x <: C` or `C <: ?x` => `?x := C`
- `?x <: R` => `?x := R`
- `D <: ?x` => `?x := D`
- `F ?x <: ?y` => `?y := F ?z`
- `R <: ?x` => `?x := R`
- `?x <: F ?y` => `?x := F ?z`
- `?x <: D` => `?x := D`
- `?x <: ?y` => `?x := ?y`

## Outline of Completeness Argument

_Abstracted away from implementation, this is how solving works._

The proof state is an forest of possibly incomplete derivations of propositions
of the form `a <: b`. Each node of a derivation tree is one of these forms:

- a typing rule, which child derivations
- a derivation hole, indicating that this derivation is incomplete

The sub-propositions that each node is a derivation of can contain (globally
scoped) metavariables.

The solver inner loop (Chronolog) makes progress on the proof state _only_ by
filling in derivation holes. The solver outer loop makes progress on the proof
state _only_ by substituting metavariables.

**Inner loop.** If any derivation hole should _not_ be suspended, and there is a
derivation rule with a conclusion that unifies with the hole's proposition, then
the rule is used and the corresponding global substitution applied. Then invoke
inner loop.

**Outer loop.** If any derivation holes have propositions that match the
expected patterns, then the appropriate global substitution is applied. Then
invoke inner loop.

Completeness boils down to this statement:

> Assume that a set of constraints has a solution. Then the typechecking
> algorithm will find it (up to some equivalences).

The solution is a "filling out" of the derivation forest for the original
constraints. So we have to show that at each step of the typechecking algorithm,
it can always find the next part of the full solution, one piece at a time, and
not get stuck.

Let's ignore the question of finding the exact unique solution for now. Let's
just try to prove it can find _some_ solution if we assume that a solution
exists.

The problem case to avoid is where neither the inner loop nor the outer loop can
make progress from a certain state, even though there is a solution that is
reachable from that state.

I'm not sure what to do from here because it kind of feels like you have to
quantify over all possible sets of constraints, which is infeasible. I know that
the proof should have some sort of inductive form where I am showing that if you
start from a good set of incomplete derivations, then you can always find the
next thing to do that makes sense, which will, of course, only refine the
original constraints.

Since the set of constraints can have any number of constraints in it, how
should I approach the order of solving these constraints? In a typical proof of
completeness for a type-checking algorithm, there is exactly one constraint that
you are solving, rather than a set.

Actually, it's not a big deal to prove a set of constraints because we can just
consider the case when we're only solving one constraint, right? Does that
naturally extend to completeness of solving a set of constraints? Well, let's
just try proving completeness of solving a single constraint and see how far
that gets.

**Outline of algorithm:**

- Inner loop:
  - The inner loop step function tries to make progress on the state by filling
    in a derivation hole.
  - The inner loop step function will continue to make progress by filling in
    holes until it either fails or becomes stagnant.
  - The inner loop step function fails when a derivation hole's constraint is
    not refinable by any subtyping rule and the constraint is not suspended.
  - The inner loop step function stagnates when all derivation holes constraints
    are suspended.
- Outer loop:
  - The outer loop runs the inner loop and then tries to apply metavariable
    substitutions to refine the derivation.

**Outline of proof:** One iteration of the outer loop will always make progress
on an incomplete derivation if we assume that there exists a solution
derivation. Essentially, the outer loop will refine a partial derivation that is
a prefix of the solution derivation.

- The inner loop will continue to make progress until there are only suspended
  goals left.
- The outer loop can refine all cases of suspended goals to be more specific so
  that the inner loop can continue making progress.
- This process will terminate because the only way it could possibly be infinite
  is if it was rolling and unrolling over and over, but the inner loop will
  never take a step that completes a roll and unroll, and the outer loop cannot
  introduce a roll or unroll.
