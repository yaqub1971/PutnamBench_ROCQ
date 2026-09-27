(* ============================================================================
   PutnamBench 1962 B5 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1962_b5.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim, except for the two lines
   marked "(* compat: ... *)".
   Defects found in this statement (reported to the maintainers, see
   ISSUE_REPORT_rocq.md):
     1. The lower bound is encoded as (3n+4)/(2n+2) instead of (3n+1)/(2n+2), which
        makes the statement FALSE at n = 2 (5/3 < 5/4). Proof: putnam_1962_b5_statement_is_false.v.
        Proposed fix: putnam_1962_b5_corrected.v (one line of the statement differs).
     2. "Variable R : realType." outside a Section is an error since Rocq 9.0.
     3. Importing all_ssreflect after all_algebra breaks the ring notations 1 and %:R
        on MathComp 2.5, so "i%:R / N%:R" in the statement no longer typechecks.
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
    : (3 * (n%:R + 1) + 1) / (2 * n%:R + 2) < sumf n < 2.
Proof. Admitted.