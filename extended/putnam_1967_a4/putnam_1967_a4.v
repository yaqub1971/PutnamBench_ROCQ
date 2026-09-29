(* ============================================================================
   PutnamBench 1967 A4 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1967_a4.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim, except for the one line
   marked "(* compat: ... *)".
   Problem: show that if lambda > 1/2 there is no real-valued function u such that
   u(x) = 1 + lambda * int_x^1 u(y) u(y - x) dy for all x in the closed interval [0, 1].
   Defect (audit verdict: unfaithful): the integral is taken over [0, 1] --
   "\int[mu]_(y in [set y | 0 <= y <= 1])" -- instead of over [x, 1], so the encoded
   equation also evaluates u at the negative arguments y - x in [-x, 0), which the
   problem never does. The values of u on [-1, 0) become free parameters and the
   theorem is in fact FALSE as written, not only unfaithful. A bounded counterexample:
   for lambda = 1 and k = -4 put c = (1 - e^(2k))/(-2k) = (1 - e^-8)/8, let
   A = 1.17149... be the smaller root of c A^2 - A + 1 = 0, and put u(y) = A e^(k y)
   for y >= 0, u(z) = k/A + A e^(2k) e^(k z) for z < 0. Then for every x in [0, 1]
   int_0^1 u(y) u(y - x) dy = (e^(kx) - 1) + c A^2 e^(kx) = A e^(kx) - 1 = u(x) - 1
   (derivation in NOTES.md, which also gives the version for every lambda > 1/2;
   checked numerically to 5e-15). On [-1, 1], the only arguments the equation uses,
   u is bounded and piecewise continuous, so the Lebesgue integral of the statement is
   the ordinary one. No _statement_is_false.v file: deriving False in Rocq would need
   these integrals of exponentials in closed form (or, for the simpler unbounded
   counterexample described in NOTES.md, the divergence of int_0^x 1/t dt), which is
   more than modest work.
   Proposed fix: putnam_1967_a4_corrected.v.
   Reading the statement: "\int[mu]_(y in D) g y" in ring_scope is MathComp-Analysis'
   real-valued integral (Rintegral), the finite part of the Lebesgue integral, which
   is 0 when the integral is infinite or undefined; mu is Lebesgue measure. The
   statement puts no integrability condition on u, so it also ranges over functions
   for which the problem's integral does not exist and the equation is read with that
   junk value 0 (second defect; the corrected file adds the integrability condition of
   PutnamBench's Lean statement of the problem).
   Compat line: the line marked "(* compat: ... *)" was added because the upstream file
   does not compile at all on Rocq 9.1: a Variable outside a Section is an error since
   Rocq 9.0 (Coq 8.x only warns), and the upstream statement declares R this way. It
   does not change the meaning of the statement. The ssralg re-import that other files
   of this repository carry is not needed here: this file imports all_ssreflect BEFORE
   all_algebra, so the ring notations 1 and %:R keep their ssralg meaning (checked under
   Rocq 9.1.1 / MathComp 2.5.0 with Set Printing All: the numerals of the statement
   elaborate to GRing.one of R).
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
    : ~exists u : R -> R, forall x : R, 0 <= x <= 1 -> u x = 1 + lambda * \int[mu]_(y in [set y | 0 <= y <= 1]) (u y * u (y - x)).
Proof. Admitted.