(* ============================================================================
   PutnamBench 1962 B5 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Apart from this header comment, differs from putnam_1962_b5.v (the upstream
   statement) in exactly one line: the
   lower bound "(3 * (n%:R + 1) + 1) / (2 * n%:R + 2)" -- i.e. (3n+4)/(2n+2), false at
   n = 2 -- becomes "(3 * n%:R + 1) / (2 * n%:R + 2)", the bound of the problem and of
   the Lean and Isabelle versions. This corrected statement is provable:
   see putnam_1962_b5_corrected_proof.v.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect
   after all_algebra (upstream's order) overrides the ring notations 1 and %:R, so
   ssralg is re-imported. Neither changes the meaning of the statement.
   Verified: compiles on Rocq 9.1.0 / MathComp 2.5 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import line
   below triggers ~30 warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import line is kept exactly as upstream wrote it so that the statement stays
   identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1962_b5
    (n : nat)
    (ng1 : gt n 1)
    (sumf : nat -> R := fun N => \sum_(1 <= i < N.+1) ((i%:R / N%:R) ^+ N))
    : (3 * n%:R + 1) / (2 * n%:R + 2) < sumf n < 2.
Proof. Admitted.