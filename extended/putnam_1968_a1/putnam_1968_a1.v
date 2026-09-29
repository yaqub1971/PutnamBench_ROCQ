(* ============================================================================
   PutnamBench 1968 A1 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1968_a1.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim, except for the lines
   marked "(* compat: ... *)".
   Problem: prove that 22/7 - pi = int_0^1 x^4 (1 - x)^4 / (1 + x^2) dx.
   Defect (naming; the mathematics is faithful): the theorem is declared as
     Theorem putnam_1968_b1
   although the file is coq/src/putnam_1968_a1.v and the problem is Putnam 1968 A1
   (PutnamBench's informal and Lean statements are both named putnam_1968_a1; 1968 B1
   is a different problem). A harness or a proof file that looks for the theorem
   putnam_1968_a1 does not find it. The statement is neither false nor vacuous, so
   there is no _statement_is_false / _statement_is_vacuous file.
   Proposed fix: putnam_1968_a1_corrected.v (the theorem is renamed putnam_1968_a1;
   no other token changes).
   Reading the statement: the left-hand side is the real number 22%:R / 7%:R - pi of R
   (pi is MathComp-Analysis' pi from trigo); "\int[mu]_(x in D) g x" in ring_scope is
   MathComp-Analysis' real-valued integral Rintegral mu D g = fine (\int[mu]_(x in D)
   (g x)%:E), the finite part of the Lebesgue integral (0 when that integral is
   infinite), with mu = Lebesgue measure and D = [0, 1]; "x ^ 4" is exprz x 4 with an
   int exponent, convertible to x ^+ 4. The integrand is continuous on R (1 + x^2 > 0)
   and nonnegative on [0, 1], so its integral over [0, 1] is finite and equals the
   Riemann integral of the problem.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0 (Coq 8.x only warns); (2) with MathComp 2.5,
   importing all_ssreflect after all_algebra (upstream's order) overrides the ring
   notations 1 and %:R, so ssralg is re-imported (without it the "1" of "0 <= x <= 1"
   fails to elaborate). Neither changes the meaning of the statement; on Coq 8.18 /
   MathComp 2.1 both are no-ops apart from silencing the local-declaration warning of
   the Variable line.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. The first import line below triggers warnings emitted by MathComp
   itself (30 under Rocq 9.1 / MathComp 2.5, among them the deprecation of
   all_ssreflect; 23 under Coq 8.18 / MathComp 2.1: ambiguous coercion paths,
   overridden notations). They are library warnings, not warnings about this file: none
   of this file's own lines produce any. The import lines are kept exactly as upstream
   wrote them so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals sequences trigo measure lebesgue_measure lebesgue_integral normedtype topology.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
From mathcomp Require Import classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Definition mu := [the measure _ _ of @lebesgue_measure R].
Theorem putnam_1968_b1
    : 22/7 - pi = \int[mu]_(x in [set x : R | 0 <= x <= 1]) (x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2)).
Proof. Admitted.
