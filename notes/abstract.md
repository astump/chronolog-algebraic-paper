# Abstract

This paper presents a system for more convenient algebraic programming. This
system uses coercive subtyping to infer as coercions the operations for working
with algebras --- such as `cata`, `roll`, and `unroll` --- that the user is
usually burdened with in algebraic programming. The language supports
Mendler-style recursion for least fixpoints of covariant signature functors.
Type checking for this system is implemented via constraint solving with
Chronolog, a logic programming engine that can suspend and resume goals of
specified forms, in order to avoid infinite regressions when proof searching in
the context of the subtyping rules for `roll` and `unroll` which can be applied
ad infinitum. We prove soundness and completeness for the type system used by
type checking algorithm with respect to the declarative typing system, and we
argue {{TODO: is this the right phrasing for it?}} for soundness and
completeness of the type checking algorithm itself. We present numerous examples
of algebraic programs written in our system in comparison to Haskell (general
recursion allowing) and Rocq (structural termination checking), such as:
{{TODO: names some interesting examples}}
