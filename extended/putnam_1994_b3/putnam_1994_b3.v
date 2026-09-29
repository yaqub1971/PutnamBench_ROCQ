(* ============================================================================
   PutnamBench 1994 B3 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1994_b3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines; see below).
   Problem: find the set of all real numbers k such that for every positive
   differentiable f : R -> R with f'(x) > f(x) for all x there is N with f(x) > e^(kx)
   for all x > N. (Answer: k < 1.)
   Defects (naming and compile; the mathematics is faithful):
   (1) naming: the file is putnam_1994_b3.v but defines "putnam_1993_b3_solution" and
       "Theorem putnam_1993_b3" (the year is wrong; 1993 B3 is a different problem).
   (2) compile: in "[set k | forall f (hf : ...), ...]" the type of f is left to
       inference, which fails at "0 < f x": f is first typed as a map into a normed
       module (from "differentiable f x") and then required to land in an ordered
       domain, and unification cannot bridge the two structures:
         In environment k : ?T  f : ?t1 -> ?W  x : ?t1
         The term "f x" has type "NormedModule.sort ?W"
         while it is expected to have type "Order.POrder.sort (...)".
       Annotating "f : R -> R" (the intended type) fixes it.
   Proposed fix: putnam_1994_b3_corrected.v (both names changed to putnam_1994_b3,
   f annotated). There is no statement_is_false / statement_is_vacuous file: once it
   compiles, the statement is faithful and true.
   Compat lines: none. The repository's marked "(* compat: ... *)" lines would not make
   this file compile (with all of them added, Rocq 9.1 stops at the same "f x" error),
   so the upstream text is kept strictly verbatim; putnam_1994_b3_corrected.v carries
   the compat lines.
   Does not compile on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (Nix): the
   first error is at the upstream "Variable R : realType." ("Use of Variable or
   Hypothesis outside sections", declaration-outside-section, an error since Rocq 9.0),
   and with that line silenced the "f x" error quoted above follows (upstream line 16,
   characters 66-69).
   Does not compile on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu
   24.04): the "f x" error quoted above, at upstream line 16, characters 66-69. (The
   upstream Variable outside a Section also draws Coq 8.18's local-declaration warning.)
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1; the import lines below trigger warnings emitted by MathComp itself
   (all_ssreflect deprecated since MathComp 2.5, ambiguous coercion paths, overridden
   notations), which are library warnings, not warnings about this file. The import
   lines are kept exactly as upstream wrote them so that the statement stays identical to
   the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import reals normedtype derive topology sequences.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Definition putnam_1993_b3_solution : set R := [set k | k < 1].
Theorem putnam_1993_b3
    : [set k | forall f (hf : forall x, differentiable f x /\ 0 < f x < f^`() x),
        exists N : R, forall x, N < x -> expR (k * x) < f x] = putnam_1993_b3_solution.
Proof. Admitted.