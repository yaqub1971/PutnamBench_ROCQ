(* ============================================================================
   PutnamBench 1965 B4 -- proof that the UPSTREAM statement is false.
   Loads putnam_1965_b4.vo (the upstream statement compiled as published, apart from
   its marked compat lines; it ends in Admitted) and derives False from it.
   Counterexample: instantiate u, v, f with the sums the hypotheses hu, hv, hf prescribe
   (so hu, hv, hf hold by reflexivity) and take n = 5, x = 1. Because the upstream bounds
   "n%/2 .+1" and "(n.-1)%/2 .+1" parse as n %/ 3 and (n.-1) %/ 3, and the denominator
   uses 'C(n, 2 * (i.+1)), the encoded values are u 5 1 = C(5,0) = 1, v 5 1 = C(5,2) = 10,
   u 6 1 = C(6,0) + C(6,2) = 16 and v 6 1 = C(6,2) = 15; the recurrence conjunct of the
   statement (its three guards 10 <> 0, 15 <> 0, 1/10 + 1 <> 0 hold) then asserts
   16/15 = f 6 1 = (f 5 1 + 1) / (f 5 1 + 1) = 1, i.e. 16 = 15.
   Compile with:  rocq compile -R . "" putnam_1965_b4_statement_is_false.v
   (coqc -R . "" ... on Coq 8.18; after compiling putnam_1965_b4.v in the same folder).
   Print Assumptions at the end shows the derivation depends only on the admitted
   theorem putnam_1965_b4 itself, the Variable R declared by the statement, and the
   three classical axioms of mathcomp.classical (boolp.propositional_extensionality,
   boolp.functional_extensionality_dep, boolp.constructive_indefinite_description) that
   mathcomp.reals is built on.
   Compat lines: the lines marked "(* compat: ... *)" repeat the ones of putnam_1965_b4.v
   (see there); they change nothing mathematically.
   Verified on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04):
   compiles and prints the assumption list described above.
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. The first "From mathcomp Require Import" line below triggers warnings
   emitted by MathComp itself (30 on Rocq 9.1.1 / MathComp 2.5.0: all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations;
   23 on Coq 8.18.0 / MathComp 2.1.0). They are library warnings, not warnings about this
   file: none of this file's own lines produce any. The import lines are kept exactly as
   upstream wrote them so that the statement's notations are read exactly as in the benchmark.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals normedtype sequences topology.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.
Import Order.TTheory GRing.Theory Num.Theory.
(* The benchmark statement putnam_1965_b4.v, compiled as published apart from its marked
   compat lines (it ends in Admitted). *)
Require putnam_1965_b4.
Import putnam_1965_b4.
Local Notation R := putnam_1965_b4.R.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* Assuming the benchmark's Rocq statement of 1965 B4, False follows: with u, v, f the sums
   that hu, hv, hf prescribe, at n = 5 and x = 1 the recurrence conjunct asserts
   16/15 = f 6 1 = (f 5 1 + 1) / (f 5 1 + 1) = 1. *)
Lemma putnam_1965_b4_rocq_statement_is_false : False.
Proof.
pose u : nat -> R -> R := fun n x => \sum_(0 <= i < n%/2 .+1) ('C(n, 2 * i)%:R * x^i).
pose v : nat -> R -> R := fun n x => \sum_(0 <= i < (n.-1)%/2 .+1) ('C(n, 2 * (i.+1))%:R * x^i).
pose f : nat -> R -> R := fun n x => u n x / v n x.
have hu : forall n : nat, gt n 0 -> forall x : R, u n x = \sum_(0 <= i < n%/2 .+1) ('C(n, 2 * i)%:R * x^i) by [].
have hv : forall n : nat, gt n 0 -> forall x : R, v n x = \sum_(0 <= i < (n.-1)%/2 .+1) ('C(n, 2 * (i.+1))%:R * x^i) by [].
have hf : forall n : nat, gt n 0 -> forall x : R, f n x = u n x / v n x by [].
have hn5 : gt 5 0 := le_n_S 0 4 (le_0_n 4).
(* the encoded values at n = 5, 6 and x = 1: the sums have 5 %/ 3 = 1, 4 %/ 3 = 1, 6 %/ 3 = 2
   and 5 %/ 3 = 1 terms respectively *)
have u5 : u 5 1 = 1%:R by rewrite /u big_ltn // big_geq // addr0 exp1rz mulr1.
have v5 : v 5 1 = 10%:R by rewrite /v big_ltn // big_geq // addr0 exp1rz mulr1.
have u6 : u 6 1 = 16%:R by rewrite /u big_ltn // big_ltn // big_geq // addr0 !exp1rz !mulr1 -natrD.
have v6 : v 6 1 = 15%:R by rewrite /v big_ltn // big_geq // addr0 exp1rz mulr1.
have ne10 : 10%:R <> 0 :> R by apply/eqP; rewrite pnatr_eq0.
have ne15 : 15%:R <> 0 :> R by apply/eqP; rewrite pnatr_eq0.
have ne11 : 1%:R / 10%:R + 1 != 0 :> R by rewrite gt_eqF // addr_gt0 // divr_gt0 // ltr0n.
have := @putnam_1965_b4 f u v hu hv hf 5 hn5.
case=> h _.
have {h} := h 1.
rewrite /f u5 v5 u6 v6 => /(_ ne10) /(_ ne15) /(_ (elimN eqP ne11)).
rewrite (divff ne11) => /(congr1 (fun z => z * 15%:R)).
rewrite mulfVK ?pnatr_eq0 // mul1r => /eqP.
by rewrite eqr_nat.
Qed.

Print Assumptions putnam_1965_b4_rocq_statement_is_false.
