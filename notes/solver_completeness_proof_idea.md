# Solver Completeness Proof Idea

A constraint solution is a set of derivations, composed of uses of the subtyping
rules, for each of the original constraints. Extend the notion of derivations to
partial derivations, which are derivations that allow for metavariables
(annotated with the constraint they are standing in place fo a derivation for)
in place of a sub-derivation.

**Algorithm**. Constraint solving.

- While there exists some derivation metavariables left in proof state:
  - Invoke Chronolog, which refines the proof state with rule applications until
    the only derivation metavariables left are those with suspended constraints.
  - If there are no derivation metavariables left, we have a complete derivation
    and are done.
  - Otherwise, each derivation metavariable in the proof state corresponds to a
    suspended constraint (as guaranteed by Chronolog). We choose one of these
    constraints and refine it via substitution so it is no longer suspended (as
    guaranteed by suspended goal refinement strategy).

**Theorem**. Completeness of constraint solving algorithm.

**Proof**. Idea of proof:

- **Definition**. A proof state P is a prefix of another proof state P' if there
  exists a logic variable substitution and derivation metavariable substitution
  such that transforms P into P'.
- The initial proof state is a set of derivation metavariables (one derivation
  metavariable for each of the original required constraints).
- Assume there is a solution (since we are proving completeness).
- The solver maintains the invariant that the current proof state is a prefix of
  the solution proof state.
- Proof of invariant:
  - Induction:
    - Base case: The initial proof state is a prefix of the solution proof state
      (obviously true).
    - Inductive step:
      - Chronolog maintains the prefix invariant since it is only able to
        validly apply rules, and branches that don't reach a solution are found
        to be unsolvable in finite time and are pruned. So, there always exists
        a branch that has as it's proof state a prefix of the solution proof
        state.
      - The suspended constraint refinement strategy maintains the prefix
        invariant. (TODO: proof)
  - Termination:
    - Chronolog terminates since infinite regresses are prevented by the
      suspension predicate (TODO: proof).
    - The suspended constraint refinement strategy cannot enter a loop with
      Chronolog that results in an infinite regress i.e. this can't happen:
      Chronolog suspends a constraint C, ..., suspended constraint refinement
      strategy resumes a constraint C. (TODO: proof)
