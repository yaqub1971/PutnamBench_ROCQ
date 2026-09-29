(* ============================================================================
   PutnamBench 1966 A3 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1966_a3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines; see below).
   Problem: if 0 < x_1 < 1 and x_{n+1} = x_n (1 - x_n) for all n >= 1, prove that
   lim_{n -> oo} n x_n = 1.
   Defect (a compile defect; the mathematics is faithful): the file does not compile.
   The target of "-->" in the conclusion
     : (fun n : nat => n%:R * x n) @ \oo --> 1.
   is the bare numeral "1". "-->" expects a point of a filtered (topological) type, but a
   bare "1" is only known to be the unit of some semiring, so elaboration fails with
     The term "1" has type "GRing.SemiRing.sort ?s0"
     while it is expected to have type "Filtered.sort ?s".
   The one-token ascription "--> (1 : R)" fixes it without changing the meaning; the rest
   of the statement is faithful to the problem (1-indexed x, hypothesis on x 1, recurrence
   for every n >= 1, limit of n%:R * x n along \oo).
   Proposed fix: putnam_1966_a3_corrected.v.
   Compat lines: none. The repository's marked "(* compat: ... *)" lines would not make
   this file compile (the error above is independent of them), so the upstream text is
   kept strictly verbatim; putnam_1966_a3_corrected.v carries the compat lines it needs
   on Rocq 9.1 / MathComp 2.5.
   Does not compile on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu 24.04):
   error at the "--> 1" of the conclusion, quoted above. (The upstream "Variable R :
   realType." outside a Section also draws Coq 8.18's local-declaration warning there.)
   Does not compile on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (Nix) either:
   there the first error is at the top-level "Variable R : realType." line,
     Error: Use of "Variable" or "Hypothesis" outside sections behaves as
     "#[local] Parameter" or "#[local] Axiom". [declaration-outside-section,vernacular,default]
   (Rocq >= 9.0 rejects a Variable declared outside a Section), before the "--> 1" is reached.
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1; the import lines below trigger warnings emitted by MathComp itself
   (ambiguous coercion paths, overridden notations), which are library warnings, not
   warnings about this file. The import lines are kept exactly as upstream wrote them so
   that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals topology normedtype.
From mathcomp Require Import classical_sets.
Import numFieldTopology.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Theorem putnam_1966_a3
    (x : nat -> R)
    (hx1 : 0 < x 1%nat /\ x 1%nat < 1)
    (hxi : forall n : nat, ge n 1 -> x (n.+1) = x n * (1 - x n))
    : (fun n : nat => n%:R * x n) @ \oo --> 1.
Proof. Admitted.