(* ============================================================================
   PutnamBench 1967 A4 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: show that if lambda > 1/2 there is no real-valued function u such that
   u(x) = 1 + lambda * int_x^1 u(y) u(y - x) dy for all x in the closed interval [0, 1].
   Source: coq/src/putnam_1967_a4.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement (audit verdict: unfaithful): the integral is taken
   over [0, 1] instead of [x, 1], so the encoded equation also evaluates u at the
   negative arguments y - x in [-x, 0), which the problem never does, and is a
   different, much weaker constraint. It has solutions (for lambda = 1 a bounded
   piecewise exponential u, written out in putnam_1967_a4.v and NOTES.md and checked
   numerically), so the upstream theorem is in fact false. Second defect, found on
   re-reading: "\int[mu]_(y in D) g y" in ring_scope is MathComp-Analysis' real-valued
   integral (Rintegral), the finite part of the Lebesgue integral, which is 0 whenever
   the integrand is not integrable over D. Upstream puts no integrability condition on
   u, so it also ranges over functions for which the problem's integral does not exist
   and reads the equation for them as u x = 1 + lambda * 0; the problem presupposes
   that its integrals exist.
   Fix: exactly one line of the statement differs from putnam_1967_a4.v (the upstream
   statement), in two places, both following PutnamBench's Lean statement of the same
   problem ("IntegrableOn u (Set.Icc 0 1) /\ forall x in Set.Icc 0 1,
   u x = 1 + lambda * (integral over Set.Ioo x 1 of u y * u (y - x))"):
     1. the integration domain "[set y | 0 <= y <= 1]" -> "[set y | x <= y <= 1]", i.e.
        int_x^1 as in the problem (the endpoints are Lebesgue-null, so this closed
        interval and Lean's open one give the same integral);
     2. "~exists u : R -> R, forall x : R, ..." ->
        "~exists u : R -> R, mu.-integrable [set y | 0 <= y <= 1] (constructive_ereal.EFin \o u) /\ forall x : R, ...":
        u is Lebesgue integrable on [0, 1] (Lean's IntegrableOn u (Set.Icc 0 1)). EFin is
        the embedding of R into the extended reals that MathComp-Analysis' integrable
        expects; it is written with its module name because the upstream imports do not
        bring it into scope, so no import line has to be added. The conjunct only records
        what the problem presupposes: at x = 0 its integral is int_0^1 u(y)^2 dy, which
        exists (as a real number) for a measurable u only if u is square-integrable,
        hence integrable, on [0, 1]; so no function the problem speaks about is
        excluded. Under it, Rocq's integral is the genuine one for almost every x in
        [0, 1] (Tonelli), which is what the classical proof uses (integrate the equation
        over [0, 1]: I = 1 + lambda I^2 / 2 has no real root when lambda > 1/2). Without
        it the Rocq statement would also be a claim about junk values on non-integrable
        functions.
   Everything else -- "lambda > 1 / 2" in R, the closed interval for x, the factors
   u y * u (y - x), the negated existential -- is upstream's text.
   Compat line: the line marked "(* compat: ... *)" was added because the upstream file
   does not compile at all on Rocq 9.1: a Variable outside a Section is an error since
   Rocq 9.0 (Coq 8.x only warns), and the upstream statement declares R this way. It
   does not change the meaning of the statement. (No ssralg re-import is needed: this
   file imports all_ssreflect before all_algebra; see putnam_1967_a4.v.)
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. On both toolchains the first import line below triggers warnings
   emitted by MathComp itself (under Rocq 9.1 / MathComp 2.5 about thirty: all_ssreflect
   is deprecated since 2.5, ambiguous coercion paths, overridden notations). They are
   library warnings, not warnings about this file: none of this file's own lines
   produce any. The import lines are kept exactly as upstream wrote them so that the
   statement stays identical to the benchmark's.
   ============================================================================ *)


From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals normedtype topology measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Definition mu := [the measure _ _ of @lebesgue_measure R].
Theorem putnam_1967_a4
    (lambda : R)
    (hlambda : lambda > 1 / 2)
    : ~exists u : R -> R, mu.-integrable [set y | 0 <= y <= 1] (constructive_ereal.EFin \o u) /\ forall x : R, 0 <= x <= 1 -> u x = 1 + lambda * \int[mu]_(y in [set y | x <= y <= 1]) (u y * u (y - x)).
Proof. Admitted.