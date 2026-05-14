# Ideation

- Github: https://github.com/astump/chronolog-algebraic-paper
- Target: https://icfp26.sigplan.org/home/lopstr-ppdp-2026
- Abstract deadline: May 20
- Paper deadline: May 27

## Aaron's Proposal

> This is colocated with ICFP. Could we bang together a paper talking about
> Chronolog in the context of a simplified version of DCS, featuring just
> Mendler algebras, with rolling and unrolling signature functors, plus maybe
> some example subtyping like Bool <: Nat?
>
> My rationale is that it would be nice to publish something on Chronolog, and
> this venue might be receptive. We would not have too much work to do: we could
> give an overview of the algebraic approach to programming, and give basically
> the same syntax as DCS but with different (much simpler!) static typing of
> algebras. The focus would be on how great it is to use logic programming to
> solve our subtyping constraints.
>
> The abstract deadline is one week from today, with papers due two weeks from
> today.
>
> It is a little zany, but maybe worth a try? What do you guys think?
>
> Maybe don't even need any primitive coercion, since we can just focus on
> coercing from algebra types to function types. Basically, all the
> implementation is just there already, and we would just write it up and
> present it differently (no divide-and-conquer recursion, just the algebraic
> approach to FP). We could say that the algebraic approach is very appealing
> for total functional programming, but it is annoying to call cata everywhere,
> and also annoying to fold and unfold signature functors explicitly. Subtyping
> can elide this, but then we need bespoke logic programming to control folidng
> and unfolding.

## Meta Notes

- The project is a narrower, more digestible spin-off of the original ICFP
  submission.
  - Focus on algebraic programming, coercive subtyping, and Chronolog
  - Omit divide-and-conquer recursion, restrict to Mendler algebras (which are
    already well-understood)

## Core Ideas

- Solve the verbosity of (Mendler) algebraic programming by using subtyping to
  infer necessary coercions, specifically cata, roll, and unroll.
- Use a simple subtyping system that just has covariant functors and fixpoints
  of covariant functors. These functors are used as the signature functors of
  Mendler algebras for the sake of expressing recursion schemes.
- Admissibility of transitivity of subtyping for inference-friendly subtyping
  system.
  - The proof is mechanized in Agda (see
    [Completeness.agda](../agda/Completeness.agda)).
- Logic programming engine for solving subtyping constraints by inferring
  coercions.
  - The traditional difficulties with inference in the context of rolling and
    unrolling are solved by the goal suspension/resumption system.
- Examples
  - Since we have Haskell and Rocq compilers, we can show what examples look
    like in several languages.
  - Need to pick new examples that only require Mendler algebras.

## Main Responsibilities

**Shared**.

- [ ] Decide on target paper size: 8 pages vs 15 pages (not including
      bibliography)
  - We will probably go with the longer format, but no pressure.

**Aaron**.

- [x] Setup Github repository for project.
  - https://github.com/astump/chronolog-algebraic-paper
- [x] Admissibility of transitivity for subtyping system, mechanized in Agda.
  - [Completeness.agda](../agda/Completeness.agda)
- [ ] Work on draft abstract.
- [ ] Introduction section.

**Henry**

- [ ] Work on draft abstract.
- [ ] Chronolog section, reworked from previous version to present a
      higher-level description that focuses on the suspension/resumption system
      and how that helps constraint solving in the context of rolling and
      unrolling.
- [ ] Demonstrate or at least argue for completeness of inference. Would be nice
      to prove this, but probably not feasible in the given time frame.
- [ ] Specify more precisely what kinds of solutions can be expected from the
      Chronolog subtyping inference implementation. Unique solutions up to
      rolling/unrolling? A minimal solution among a class of equivalent
      solutions up to rolling/unrolling?
