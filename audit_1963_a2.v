(* ============================================================================
   Sanity check ("audit") for putnam_1963_a2.v. Not part of the proof.
   Needs putnam_1963_a2.vo; compile with:  rocq compile -R . "" audit_1963_a2.v
   Purpose: make sure the benchmark statement is a genuine theorem and not an
   accident of its encoding (the kind of defect found in putnam_1962_a6.v).
     hyps_satisfiable        : some f satisfies all four hypotheses (the identity),
                               so the theorem is not vacuously true.
     without_H2_false        : drop f 2 = 2 and the conclusion fails.
     without_Hmul_false      : drop multiplicativity and the conclusion fails.
     without_Hinc_false      : drop strict monotonicity and the conclusion fails.
                               (so every hypothesis is doing work)
     audit_matches_benchmark : the audited statement is derived from the compiled
                               benchmark theorem, so it is the benchmark's hypotheses
                               that were audited, not a paraphrase.
   Each Print Assumptions prints "Closed under the global context".
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 (Ubuntu 24.04): compiles.
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import line
   below triggers ~30 warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import line is kept exactly as upstream wrote it so that the statement stays
   identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import zify.
Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(* The hypotheses of the benchmark statement, bundled *)
Definition Hpos (f : nat -> nat) := forall n : nat, 0 < f n.
Definition Hinc (f : nat -> nat) := forall i j : nat, 0 < i -> i < j -> f i < f j.
Definition H2   (f : nat -> nat) := f 2 = 2.
Definition Hmul (f : nat -> nat) := forall m n : nat, 0 < m -> 0 < n -> coprime m n -> f (m * n) = f m * f n.
Definition Concl (f : nat -> nat) := forall n : nat, 0 < n -> f n = n.

(* TEST 1 - not vacuous: some f satisfies ALL hypotheses (contrast: 1962 A6 fails this) *)
Lemma hyps_satisfiable : exists f, Hpos f /\ Hinc f /\ H2 f /\ Hmul f.
Proof.
exists (fun n => if n == 0 then 1 else n); split; [|split; [|split]].
- by move=> n; case: n.
- by move=> i j; case: i => // i _; case: j => // j.
- by [].
- by move=> m n; case: m => // m _; case: n => // n _ _.
Qed.

(* TEST 2 - f(2)=2 is load-bearing: drop it and n^2 is a counterexample *)
Lemma without_H2_false : ~ (forall f, Hpos f -> Hinc f -> Hmul f -> Concl f).
Proof.
move=> H; have := H (fun n => if n == 0 then 1 else n ^ 2).
have h1 : Hpos (fun n => if n == 0 then 1 else n ^ 2) by move=> n; case: n => // n; rewrite /= expn_gt0.
have h2 : Hinc (fun n => if n == 0 then 1 else n ^ 2).
  by move=> i j; case: i => // i _; case: j => // j; rewrite /= ltn_sqr.
have h3 : Hmul (fun n => if n == 0 then 1 else n ^ 2).
  move=> m n; case: m => // m _; case: n => // n _ _.
  have -> : (m.+1 * n.+1 == 0) = false by rewrite muln_eq0.
  by rewrite /= expnMn.
by move=> /(_ h1 h2 h3 2 isT).
Qed.

(* TEST 3 - multiplicativity is load-bearing: drop it and a shifted identity is a counterexample *)
Lemma without_Hmul_false : ~ (forall f, Hpos f -> Hinc f -> H2 f -> Concl f).
Proof.
move=> H; have := H (fun n => if n <= 2 then n.-1.+1 else n.+1).
have h1 : Hpos (fun n => if n <= 2 then n.-1.+1 else n.+1) by move=> n; case: ifP.
have h2 : Hinc (fun n => if n <= 2 then n.-1.+1 else n.+1).
  by move=> i j hi hij; case: ifP; case: ifP; lia.
by move=> /(_ h1 h2 erefl 3 isT).
Qed.

(* TEST 4 - monotonicity is load-bearing: drop it and "2-part of n" is a counterexample *)
Lemma without_Hinc_false : ~ (forall f, Hpos f -> H2 f -> Hmul f -> Concl f).
Proof.
move=> H; have := H (fun n => n`_2).
have h1 : Hpos (fun n => n`_2) by move=> n; exact: part_gt0.
have h2 : H2 (fun n => n`_2) by rewrite /H2 part_pnat_id // pnat_id.
have h3 : Hmul (fun n => n`_2) by move=> m n hm hn _; exact: partnM.
move=> /(_ h1 h2 h3 3 isT); rewrite (@part_p'nat 2 3) //.
Qed.

Print Assumptions hyps_satisfiable.
Print Assumptions without_H2_false.
Print Assumptions without_Hmul_false.
Print Assumptions without_Hinc_false.

(* TIE-BACK: the bundled definitions above are exactly the benchmark theorem's hypotheses and conclusion *)
Require putnam_1963_a2.
Lemma audit_matches_benchmark : forall f, Hpos f -> Hinc f -> H2 f -> Hmul f -> Concl f.
Proof. exact: putnam_1963_a2.putnam_1963_a2. Qed.
