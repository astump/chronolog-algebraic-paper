# Abstract

This paper presents a system for more convenient algebraic
programming, a form of total functional programming where datatypes
are defined as least fixed points of covariant signature functors, and
recursive functions are defined as algebras.  This approach requires
the use of certain combinators to roll and unroll fixed points, and to
convert algebras to functions which can be applied to recurse over
data.  These combinators are a burden for programming in this style.
To alleviate that burden, in this paper we propose to insert them
automatically, using coercive subtyping.  The type checker generates
subtyping constraints, which are then solved with the help of a custom
logic programming engined called Chronolog.  The subtyping axioms are
given to Chronolog as rules, which uses them to solve the subtyping
constraints.  To avoid infinite applications of rules for unrolling
signature functors, Chronolog provides a mechanism for suspending and
resuming certain forms of goals.  The subtyping axioms presented to
Chronolog are an algorithmic version of the usual declarative rules
for algebraic programming.  We prove equivalence of the declarative
and algorithmic rules, in Agda. We present numerous examples of
algebraic programs written in our system. 
