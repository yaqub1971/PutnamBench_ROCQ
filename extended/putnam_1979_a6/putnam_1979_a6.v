(* ============================================================================
   PutnamBench 1979 A6 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1979_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim, except for the four lines
   marked "(* compat: ... *)".
   Problem: given p_0, ..., p_(n-1) in [0, 1], show that some x in [0, 1] satisfies
   sum_(i = 0)^(n-1) 1/|x - p_i| <= 8n * sum_(i = 0)^(n-1) 1/(2i + 1).
   Defects (audit verdict "naming"; reported in putnam_1979_a6_corrected.v and NOTES.md):
     1. The theorem is named putnam_1979_b6, the name of a different PutnamBench
        problem (1979 B6, on real parts of square roots of sums of complex squares),
        instead of putnam_1979_a6.
     2. The inner sum of the bound runs over "0 <= i < (size p).+1", i.e. i = 0, ..., n
        (n + 1 terms, n = size p), instead of i = 0, ..., n - 1 (n terms). The extra
        term 1/(2n + 1) makes the right-hand side larger by 8n/(2n + 1) whenever n >= 1
        (for n = 1: 8 * (1 + 1/3) = 32/3 instead of 8), so the statement is WEAKER than
        the problem. It is still true (it follows from the problem's statement), so it
        is not false; its only hypothesis hp is satisfiable (e.g. p = [:: 0]), so it is
        not vacuous: there is no _statement_is_false / _statement_is_vacuous file.
     Proposed fix: putnam_1979_a6_corrected.v (theorem renamed, "(size p).+1" -> "(size p)").
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect
   after all_algebra (upstream's order) overrides the ring notations 1 and %:R, so
   ssralg is re-imported. Neither changes the meaning of the statement.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1.1 / MathComp 2.5.0 the first import line below triggers
   30 warnings emitted by MathComp itself (all_ssreflect is deprecated since 2.5,
   ambiguous coercion paths, overridden notations); under Coq 8.18.0 / MathComp 2.1.0 it
   triggers 23. They are library warnings, not warnings about this file: none of this
   file's own lines produce any. The import lines are kept exactly as upstream wrote them
   so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect fintype.
From mathcomp Require Import reals.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1979_b6
    (p : seq R)
    (hp : all (fun x => 0 <= x <= 1) p)
    : exists x : R, 0 <= x <= 1 /\ (all (fun i => x != i) p) /\ (\sum_(i <- p) 1/`|x - i|) <= 8*(size p)%:R*(\sum_(0 <= i < (size p).+1) (1%R)/(2*(i%:R) + 1)).
Proof. Admitted.