(* ============================================================================
   PutnamBench 1978 B2 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1978_b2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines; see below).
   Problem: find sum_{i=1}^oo sum_{j=1}^oo 1 / (i^2 j + 2 i j + i j^2) (answer: 7/4).
   Defect (a compile defect; the mathematics is faithful): the file does not compile.
   The target of "-->" in the conclusion
     : (f @ \oo --> ratr putnam_1978_b2_solution).
   is "ratr putnam_1978_b2_solution" with no type. "-->" expects a point of a filtered
   (topological) type, but "ratr q" is only known to live in some unit ring, so
   elaboration fails with
     The term "ratr putnam_1978_b2_solution" has type "GRing.UnitRing.sort ?R"
     while it is expected to have type "Filtered.sort ?s".
   The one-token ascription "--> (ratr putnam_1978_b2_solution : R)" fixes it without
   changing the meaning; the rest of the statement is faithful to the problem.
   Proposed fix: putnam_1978_b2_corrected.v.
   Compat lines: none. The repository's marked "(* compat: ... *)" lines would not make
   this file compile (the error above is independent of them), so the upstream text is
   kept strictly verbatim; putnam_1978_b2_corrected.v carries the compat lines it needs
   on Rocq 9.1 / MathComp 2.5.
   Does not compile on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu 24.04):
   error at the "--> ratr ..." of the conclusion, quoted above. (The upstream "Variable R :
   realType." outside a Section also draws Coq 8.18's local-declaration warning there.)
   Does not compile on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (Nix) either:
   there the first error is at the top-level "Variable R : realType." line,
     Error: Use of "Variable" or "Hypothesis" outside sections behaves as
     "#[local] Parameter" or "#[local] Axiom". [declaration-outside-section,vernacular,default]
   (Rocq >= 9.0 rejects a Variable declared outside a Section), before the "-->" is reached.
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1; the import lines below trigger warnings emitted by MathComp itself
   (ambiguous coercion paths, overridden notations), which are library warnings, not
   warnings about this file. The import lines are kept exactly as upstream wrote them so
   that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals topology sequences normedtype.
From mathcomp Require Import classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Definition putnam_1978_b2_solution : rat := 7/4.
Theorem putnam_1978_b2
    (f : nat -> R := fun n => \sum_(1 <= i < n.+1) (\sum_(1 <= j < n.+1) (1%R)/(i%:R ^+ 2 * j%:R + 2 * i%:R * j%:R + i%:R * j%:R ^+ 2)))
    : (f @ \oo --> ratr putnam_1978_b2_solution).
Proof. Admitted.