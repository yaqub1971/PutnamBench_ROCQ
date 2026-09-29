(* ============================================================================
   PutnamBench 1964 A2 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: let alpha be a real number; find all continuous f : [0, 1] -> (0, +oo) with
   int_0^1 f(x) dx = 1, int_0^1 x f(x) dx = alpha and int_0^1 x^2 f(x) dx = alpha^2.
   Answer: there is no such f.
   Source: coq/src/putnam_1964_a2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: the first condition of the problem,
   int_0^1 f(x) dx = 1, is missing from the set on the right-hand side. Without it the
   set is not empty -- the constant f = 4/3 is positive and continuous on [0, 1] and,
   for alpha = 2/3, has int_0^1 x f = 2/3 = alpha and int_0^1 x^2 f = 4/9 = alpha^2 --
   while the answer key putnam_1964_a2_solution alpha is set0, so the upstream theorem
   is FALSE (derivation of False: putnam_1964_a2_statement_is_false.v).
   Fix: apart from this header comment and the marked compat lines, this file differs
   from putnam_1964_a2.v (the upstream statement) in exactly one added line, the
   missing condition, inserted where the problem and PutnamBench's Lean statement have
   it (after the positivity/continuity conjunct, before the two moment conditions):
     +        /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (f x) = 1
   It is the same real-valued integral over the same set as the two moment conditions
   (Set Printing All: Rintegral mu [set x | 0 <= x <= 1] (fun x => f x) = GRing.one R).
   Everything else is upstream's and faithful: f > 0 on [0, 1]; continuity of f within
   [0, 1] (the counterpart of Lean's ContinuousOn f (Icc 0 1)); the moment conditions
   with x ^+ 2 and alpha ^+ 2 (nat exponent 2); alpha universally quantified; the answer
   set0 (Lean: fun _ => emptyset). With the condition restored the statement is true:
   for such an f, int_0^1 (x - alpha)^2 f(x) dx = alpha^2 - 2 alpha^2 + alpha^2 = 0,
   while the integrand is continuous, nonnegative and positive except at x = alpha, so
   that integral is positive.
   Reading the statement: "\int[mu]_(x in D) g x" in ring_scope is MathComp-Analysis'
   real-valued integral (Rintegral), i.e. the finite part of the Lebesgue integral,
   which is 0 when the integral is infinite; mu is Lebesgue measure. For the functions
   the problem is about (continuous, hence bounded, on [0, 1]) it is the ordinary
   integral. The continuity conjunct sits inside "forall x, 0 <= x <= 1 -> ..."; as
   [0, 1] is not empty this is the same as stating it once.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect
   after all_algebra (upstream's order) overrides the ring notations 1 and %:R, so
   ssralg is re-imported. Neither changes the meaning of the statement.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. The first import line below triggers library warnings emitted by
   MathComp itself (30 under Rocq 9.1.1 / MathComp 2.5.0: all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations; 23 under Coq 8.18.0 /
   MathComp 2.1.0: ambiguous coercion paths, overridden notations). None of this file's
   own lines produce any warning (on Coq 8.18.0 the upstream Variable line alone emits
   "local-declaration"; the compat line before it silences that). The import lines are
   kept exactly as upstream wrote them so that the statement stays identical to the
   benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals topology normedtype measure lebesgue_measure lebesgue_integral.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
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
Definition putnam_1964_a2_solution := fun a : R => (set0 : set (R -> R)).
Theorem putnam_1964_a2
    (alpha : R)
    : putnam_1964_a2_solution alpha = [set f : R -> R | 
        (forall x : R, 0 <= x <= 1 -> (f x > 0)
        /\ {within [set x | 0 <= x <= 1], continuous f}) 
        /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (f x) = 1
        /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (x * f x) = alpha
        /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (x ^+ 2 * f x) = alpha ^+ 2].
Proof. Admitted.