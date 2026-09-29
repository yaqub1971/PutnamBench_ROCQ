(* ============================================================================
   PutnamBench 1964 A2 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1964_a2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim, except for the lines
   marked "(* compat: ... *)".
   Problem: let alpha be a real number; find all continuous f : [0, 1] -> (0, +oo) with
   int_0^1 f(x) dx = 1, int_0^1 x f(x) dx = alpha and int_0^1 x^2 f(x) dx = alpha^2.
   Answer: there is no such f.
   Defect: the first of the three conditions, int_0^1 f(x) dx = 1, is missing from the
   set on the right-hand side (the informal statement and PutnamBench's Lean statement
   both have it). Without it the set is not empty: the constant function f = 4/3 is
   positive and continuous on [0, 1], and for alpha = 2/3 it has
   int_0^1 x f(x) dx = 2/3 = alpha and int_0^1 x^2 f(x) dx = 4/9 = alpha^2; but the
   answer key putnam_1964_a2_solution alpha is set0. So the theorem is FALSE as written:
   proof in putnam_1964_a2_statement_is_false.v (its witness is the constant
   c = i2 / i1^2 with alpha = c * i1, where i1 and i2 are the integrals of x and x^2
   over [0, 1]; that is the pair above, but the proof never evaluates an integral in
   closed form). Proposed fix: putnam_1964_a2_corrected.v (the missing condition is
   added as one line; nothing else changes).
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
        /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (x * f x) = alpha
        /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (x ^+ 2 * f x) = alpha ^+ 2].
Proof. Admitted.