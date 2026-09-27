(* ============================================================================
   PutnamBench 1962 B5 -- proof that the UPSTREAM statement is false.
   Loads putnam_1962_b5.vo (the upstream statement compiled as published, apart from
   its marked compat lines; it ends in Admitted) and derives False from it: at n = 2 the
   statement asserts (3*(2+1)+1)/(2*2+2) = 5/3 < (1/2)^2 + (2/2)^2 = 5/4.
   Compile with:  rocq compile -R . "" putnam_1962_b5_statement_is_false.v
   (after compiling putnam_1962_b5.v).
   Print Assumptions at the end shows the derivation depends only on the admitted
   theorem putnam_1962_b5 itself, the Variable R declared by the statement, and the
   three classical axioms that mathcomp.reals is built on.
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 (Ubuntu 24.04):
   compiles and prints the assumption list described above.
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import line
   below triggers ~30 warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import line is kept exactly as upstream wrote it so that the statement stays
   identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals lra.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
(* The benchmark statement putnam_1962_b5.v, compiled as published apart from its two marked
   compat lines (it ends in Admitted). *)
Require putnam_1962_b5.
Import putnam_1962_b5.
Local Notation R := putnam_1962_b5.R.

Import GRing.Theory Num.Theory.
Open Scope ring_scope.

(* Assuming the benchmark's Rocq statement of 1962 B5, False follows:
   at n = 2 it asserts (3*(2+1)+1)/(2*2+2) = 5/3 < (1/2)^2 + (2/2)^2 = 5/4.
   Lean and Isabelle state the correct bound (3n+1)/(2n+2). *)
Lemma putnam_1962_b5_rocq_statement_is_false : False.
Proof.
have := putnam_1962_b5 (le_n 2); cbv zeta => /andP[h _].
move: h; rewrite big_ltn // big_ltn // big_geq // addr0 !expr2 ltr_pdivrMr; last by lra.
move=> h; lra.
Qed.

Print Assumptions putnam_1962_b5_rocq_statement_is_false.
