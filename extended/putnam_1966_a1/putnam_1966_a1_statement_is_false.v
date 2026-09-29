(* ============================================================================
   PutnamBench 1966 A1 -- proof that the UPSTREAM statement is false.
   Loads putnam_1966_a1.vo (the upstream statement compiled as published; it ends in
   Admitted) and derives False from it. At x = 2, y = 1 the statement asserts
   (2 * 1)%:Z = f 3 - f 1, where f n is upstream's sum over 0 <= m <= n of the terms
   "(m%:Z)/2" (m even) and "(m%:Z-1)/2" (m odd). In MathComp's int the inverse is the
   identity ("Definition invz n : int := n." in ssrint.v), so these terms are m * 2 and
   (m - 1) * 2: the sequence is 0, 0, 4, 4, 8, 8, ..., f 3 = 0 + 0 + 4 + 4 = 8, f 1 = 0, and
   the statement asserts 2 = 8.
   The proof instantiates the theorem at x = 2, y = 1 (the three hypotheses 2 > 0, 1 > 0,
   2 > 1 are Peano's le_S/le_n), exposes the body of MathComp's locked big operator with
   "rewrite unlock", evaluates both sides with vm_compute to Posz 2 = Posz 8, and concludes
   with discriminate.
   Compile with:  coqc -R . "" putnam_1966_a1_statement_is_false.v
   (after compiling putnam_1966_a1.v).
   Print Assumptions at the end shows the derivation depends only on the admitted theorem
   putnam_1966_a1 itself (no other axiom).
   Verified on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04):
   compiles and prints "Axioms: putnam_1966_a1 : ..." and nothing else.
   About the warnings: the import line below triggers library warnings emitted by MathComp
   itself (overridden notations, ambiguous coercion paths). They are library warnings, not
   warnings about this file: none of this file's own lines produce any.
   ============================================================================ *)

From mathcomp Require Import all_ssreflect ssrnum ssralg ssrint.
(* The benchmark statement putnam_1966_a1.v, compiled as published (it ends in Admitted). *)
Require putnam_1966_a1.
Import putnam_1966_a1.

(* Assuming the benchmark's Rocq statement of 1966 A1, False follows: at x = 2, y = 1 it
   asserts 2 = 8, because "/ 2" on MathComp's int is multiplication by 2. *)
Lemma putnam_1966_a1_rocq_statement_is_false : False.
Proof.
have h := @putnam_1966_a1 2 1 (@le_S 1 1 (le_n 1)) (le_n 1) (le_n 2).
rewrite unlock in h; vm_compute in h.
discriminate.
Qed.

Print Assumptions putnam_1966_a1_rocq_statement_is_false.
