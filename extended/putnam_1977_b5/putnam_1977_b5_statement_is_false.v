(* ============================================================================
   PutnamBench 1977 B5 -- proof that the UPSTREAM statement is false.
   Loads putnam_1977_b5.vo (the upstream statement compiled as published, apart from
   its marked compat lines; it ends in Admitted) and derives False from it. The
   upstream hypothesis hA is non-strict: for n = 2, a = (1, 1), A = 2 it holds with
   equality, 2 + (1^2 + 1^2) = 4 = 1/(2 - 1) * (1 + 1)^2, and the conclusion then
   asserts 2 < 2 * 1 * 1, i.e. 2 < 2.
   Compile with:  rocq compile -R . "" putnam_1977_b5_statement_is_false.v
   (Coq 8.18: coqc -R . "" ...; after compiling putnam_1977_b5.v).
   Print Assumptions at the end shows the derivation depends only on the admitted
   theorem putnam_1977_b5 itself, the Variable R declared by the statement, and the
   three classical axioms of mathcomp.classical (boolp) that mathcomp.reals is built on.
   Compat lines: the three lines marked "(* compat: ... *)" re-import ssralg after the
   upstream imports, as in putnam_1977_b5.v (with MathComp 2.5, importing all_ssreflect
   after all_algebra overrides the ring notations 1 and %:R). This file's own proof
   writes 1 and %:R on R. They change nothing mathematically.
   Verified on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04):
   compiles and prints the assumption list described above.
   About the warnings: on both toolchains the first import line emits library warnings
   (ambiguous coercion paths, overridden notations; on MathComp 2.5 also the
   deprecation of all_ssreflect) that come from MathComp itself; none of this file's
   own lines produce any. The import lines are kept exactly as upstream wrote them.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals lra.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
(* The benchmark statement putnam_1977_b5.v, compiled as published apart from its marked
   compat lines (it ends in Admitted). *)
Require putnam_1977_b5.
Import putnam_1977_b5.
Local Notation R := putnam_1977_b5.R.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* Assuming the benchmark's Rocq statement of 1977 B5, False follows: for n = 2,
   a = (1, 1), A = 2 its non-strict hypothesis holds with equality,
   2 + (1 + 1) = 4 = 1 / (2 - 1) * (1 + 1) ^ 2, and its conclusion asserts 2 < 2 * 1 * 1.
   The problem (and the Lean statement) has a strict hypothesis. *)
Lemma putnam_1977_b5_rocq_statement_is_false : False.
Proof.
have hA : 2 + \sum_(i <- [:: 1; 1]) (i ^+ 2)
          <= 1 / ((size [:: 1; 1 : R])%:R - 1) * (\sum_(i <- [:: 1; 1]) i) ^+ 2 :> R.
  rewrite !big_cons !big_nil ?big_nil /= !expr2 (_ : 2%:R - 1 = 1 :> R) ?divr1; lra.
have := @putnam_1977_b5 [:: 1; 1] 2 (le_n 2) hA.
by rewrite /= !mulr1 Order.POrderTheory.ltxx.
Qed.

Print Assumptions putnam_1977_b5_rocq_statement_is_false.
