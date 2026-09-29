(* ============================================================================
   PutnamBench 1978 B2 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: find sum_{i=1}^oo sum_{j=1}^oo 1 / (i^2 j + 2 i j + i j^2); the answer is 7/4.
   Source: coq/src/putnam_1978_b2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: it does not compile (see putnam_1978_b2.v). The target
   of "-->" in the conclusion is "ratr putnam_1978_b2_solution" with no type; "-->"
   expects a point of a filtered (topological) type and "ratr q" is only known to live in
   some unit ring, so elaboration fails with
     The term "ratr putnam_1978_b2_solution" has type "GRing.UnitRing.sort ?R"
     while it is expected to have type "Filtered.sort ?s".
   The mathematics of the upstream statement is faithful; nothing else needed a change.
   Fix: exactly one type ascription is added, in the conclusion:
     : (f @ \oo --> ratr putnam_1978_b2_solution).
   becomes
     : (f @ \oo --> (ratr putnam_1978_b2_solution : R)).
   The ascription only names the type of the limit: the conclusion is "the partial sums
   f n converge to the real number 7/4 as n -> oo" (checked: ratr (7/4 : rat) = 7/4 in R).
   Everything else is upstream's text and matches the problem: f n is the square partial
   sum sum_{i=1}^{n} sum_{j=1}^{n} 1 / (i^2 j + 2 i j + i j^2) (the \sum_(1 <= i < n.+1)
   bounds are i = 1..n; the denominators are real, positive, and the numerals and powers
   are ring operations in R); the answer 7/4 is taken in rat, so there is no nat/int
   division. Because every term is positive, the square partial sums converge to the
   same value as the problem's iterated sum (Tonelli), so the limit of f is exactly the
   problem's double sum; PutnamBench's Lean statement writes it as an iterated tsum over
   positive naturals with the same answer 7/4.
   Compat lines: the lines marked "(* compat: ... *)" were added because, independently of
   the defect above, the upstream text has the two constructs that the repository README
   documents as fatal on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a Section is an
   error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect after all_algebra
   (upstream's order) overrides the ring notations 1 and %:R, so ssralg is re-imported.
   Neither changes the meaning of the statement; both are no-ops on Coq 8.18 / MathComp 2.1.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1; the import lines below trigger warnings emitted by MathComp itself
   (ambiguous coercion paths, overridden notations). They are library warnings, not
   warnings about this file: none of this file's own lines produce any. The import lines
   are kept exactly as upstream wrote them so that the statement stays identical to the
   benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals topology sequences normedtype.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
From mathcomp Require Import classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Definition putnam_1978_b2_solution : rat := 7/4.
Theorem putnam_1978_b2
    (f : nat -> R := fun n => \sum_(1 <= i < n.+1) (\sum_(1 <= j < n.+1) (1%R)/(i%:R ^+ 2 * j%:R + 2 * i%:R * j%:R + i%:R * j%:R ^+ 2)))
    : (f @ \oo --> (ratr putnam_1978_b2_solution : R)).
Proof. Admitted.