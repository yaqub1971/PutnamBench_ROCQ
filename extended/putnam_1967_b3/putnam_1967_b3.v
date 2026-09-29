(* ============================================================================
   PutnamBench 1967 B3 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1967_b3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines; see below).
   Problem: if f and g are continuous and periodic with period 1 on the real line, then
   lim_{n -> oo} int_0^1 f(x) g(n x) dx = (int_0^1 f(x) dx) (int_0^1 g(x) dx).
   Defect (a compile defect; the mathematics is faithful): the file does not compile.
   In the conclusion
     : (fun n : nat => \int[mu]_(x in [set y | 0 < y < 1]) (f x * g (n%:~R * x))) --> ...
   "-->" is applied directly to the sequence, a function nat -> R. "F --> l" expects F to
   be a filter (or a point of a filtered type) and a bare function is neither, so
   elaboration fails with
     The term
      "fun n : nat => \int[mu]_(x in [set y | 0 < y < 1]) (f x * g (n%:~R * x))"
     has type "nat -> R" while it is expected to have type "Filtered.sort ?s".
   The missing "@ \oo" (the image of the filter \oo = eventually on nat under the
   sequence, i.e. the limit as n -> oo) fixes it without changing the intended meaning;
   the rest of the statement is faithful to the problem.
   Proposed fix: putnam_1967_b3_corrected.v.
   Compat lines: none. The repository's marked "(* compat: ... *)" lines would not make
   this file compile (the error above is independent of them: with the Variable compat
   line added, Rocq 9.1 stops at the same "-->" error), so the upstream text is kept
   strictly verbatim; putnam_1967_b3_corrected.v carries the compat lines.
   Does not compile on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (Nix): the
   first error is at the upstream "Variable R : realType." ("Use of Variable or
   Hypothesis outside sections", declaration-outside-section, an error since Rocq 9.0),
   and with that line silenced the error quoted above follows.
   Does not compile on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu
   24.04): the error quoted above, at the conclusion (upstream line 19, characters
   7-79). (The upstream Variable outside a Section also draws Coq 8.18's
   local-declaration warning.)
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1; the import lines below trigger warnings emitted by MathComp itself
   (all_ssreflect deprecated since MathComp 2.5, ambiguous coercion paths, overridden
   notations), which are library warnings, not warnings about this file. The import
   lines are kept exactly as upstream wrote them so that the statement stays identical to
   the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals normedtype trigo measure lebesgue_measure lebesgue_integral topology.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Definition mu := [the measure _ _ of @lebesgue_measure R].
Theorem putnam_1967_b3
    (f g : R -> R)
    (fgcont : continuous f /\ continuous g)
    (fgperiod : periodic f 1 /\ periodic g 1)
    : (fun n : nat => \int[mu]_(x in [set y | 0 < y < 1]) (f x * g (n%:~R * x))) --> 
        (\int[mu]_(x in [set y | 0 < y < 1]) f x) * (\int[mu]_(x in [set y | 0 < y < 1]) g x).
Proof. Admitted.