(* ============================================================================
   PutnamBench 1962 B5 -- Rocq/MathComp proof of the CORRECTED statement.
   Problem: for n > 1,  (3n+1)/(2n+2)  <  sum_(i = 1..n) (i/n)^n  <  2.
   Statement: coq/src/putnam_1962_b5.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20), with ONE change:
   upstream writes the lower bound as "(3 * (n%:R + 1) + 1) / (2 * n%:R + 2)", i.e.
   (3n+4)/(2n+2), which is false (at n = 2 it asserts 5/3 < 5/4; proved in
   putnam_1962_b5_statement_is_false.v). This file uses "(3 * n%:R + 1) / (2 * n%:R + 2)",
   the bound of the problem and of the Lean and Isabelle versions. Everything else in
   the statement is upstream's text (see putnam_1962_b5_corrected.v, the statement alone).
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect
   after all_algebra (upstream's order) overrides the ring notations 1 and %:R, so
   ssralg is re-imported. Neither changes the meaning of the statement.
   The proof follows the structure of a Lean proof of the same problem.
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 (Ubuntu 24.04):
   compiles; Print Assumptions putnam_1962_b5 lists only R (the Variable declared by
   the statement itself) and the three classical axioms that mathcomp.reals is built on
   (propositional_extensionality, functional_extensionality_dep,
   constructive_indefinite_description) -- nothing from the proof;
   rocqchk / coqchk: "Modules were successfully checked".
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import line
   below triggers ~30 warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import line is kept exactly as upstream wrote it so that the statement stays
   identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals zify lra ring.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(* Natural-number lemmas. Following the Lean proof: one-step bounds on
   (k+1)^(p+1) - k^(p+1), summed into bounds on sum_{k<m} k^p.          *)
(* ------------------------------------------------------------------ *)
Section NatLemmas.
Local Open Scope nat_scope.

(* (p+1) k^p + k^(p+1) <= (k+1)^(p+1) *)
Lemma step (p k : nat) : (p.+1 * k ^ p + k ^ p.+1 <= k.+1 ^ p.+1)%N.
Proof.
elim: p => [|p ih]; first by rewrite expn0 !expn1; lia.
move: ih; rewrite !expnS.
set a := k ^ p; set b := k.+1 ^ p; move=> ih.
nia.
Qed.

(* 2 (k+1)^(p+1) <= (p+1)((k+1)^p + k^p) + 2 k^(p+1)   (trapezoid bound) *)
Lemma trap (p k : nat) : (2 * k.+1 ^ p.+1 <= p.+1 * (k.+1 ^ p + k ^ p) + 2 * k ^ p.+1)%N.
Proof.
elim: p => [|p ih]; first by rewrite !expn1 !expn0; lia.
have := step p k.
move: ih; rewrite !expnS.
set a := k ^ p; set b := k.+1 ^ p; move=> ih st.
nia.
Qed.

(* (p+1) sum_{k<m} k^p <= m^(p+1) *)
Lemma sum_upper (p m : nat) : (p.+1 * (\sum_(0 <= k < m) k ^ p) <= m ^ p.+1)%N.
Proof.
elim: m => [|m ih]; first by rewrite big_geq // muln0 leq0n.
rewrite big_nat_recr //= mulnDr.
have := step p m.
set S := \sum_(0 <= k < m) k ^ p; set a := m ^ p; set b := m ^ p.+1; set c := m.+1 ^ p.+1.
lia.
Qed.

(* 2 (m+1)^(p+1) + (p+1)(m+1)^p < 2 (p+1) sum_{k<m+2} k^p,  for p >= 2 (strict) *)
Lemma sum_lower (p m : nat) : (2 <= p)%N ->
  (2 * m.+1 ^ p.+1 + p.+1 * m.+1 ^ p < 2 * p.+1 * (\sum_(0 <= k < m.+2) k ^ p))%N.
Proof.
move=> hp; elim: m => [|m ih].
  rewrite big_nat_recr //= big_nat_recr //= big_geq //= exp0n ?exp1n; last lia.
  lia.
have := trap p m.+1.
rewrite big_nat_recr //=.
move: ih; set S := \sum_(0 <= k < m.+2) k ^ p.
set a := m.+1 ^ p; set b := m.+1 ^ p.+1; set c := m.+2 ^ p; set d := m.+2 ^ p.+1.
lia.
Qed.

End NatLemmas.

(* ------------------------------------------------------------------ *)
(* The corrected statement (only change from the benchmark file:
   3 * n%:R + 1 instead of 3 * (n%:R + 1) + 1).                        *)
(* ------------------------------------------------------------------ *)
Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1962_b5
    (n : nat)
    (ng1 : gt n 1)
    (sumf : nat -> R := fun N => \sum_(1 <= i < N.+1) ((i%:R / N%:R) ^+ N))
    : (3 * n%:R + 1) / (2 * n%:R + 2) < sumf n < 2.
Proof.
have n1 : (1 < n)%N by apply/ltP.
have n0 : (0 < n)%N by lia.
have h1n : (1 <= n)%N by lia.
have nn0 : (0 < n ^ n)%N by rewrite expn_gt0 n0.
have nnR : 0 < (n ^ n)%:R :> R by rewrite ltr0n.
have hnR : 0 < n%:R :> R by rewrite ltr0n.
(* the sum over a common denominator *)
have -> : sumf n = (\sum_(1 <= i < n.+1) i ^ n)%:R / (n ^ n)%:R.
  rewrite /sumf natr_sum mulr_suml; apply: eq_bigr => i _.
  by rewrite expr_div_n !natrX.
have -> : (\sum_(1 <= i < n.+1) i ^ n)%N = (\sum_(0 <= i < n) i ^ n + n ^ n)%N.
  by rewrite big_nat_recr // [in RHS]big_ltn // exp0n // add0n.
set T := (\sum_(0 <= i < n) i ^ n)%N.
(* the two inequalities, in nat *)
have hup : (T + n ^ n < 2 * n ^ n)%N.
  have := sum_upper n n; have := nn0; rewrite -/T expnS.
  set P := (n ^ n)%N => P0 h; nia.
have hlo : ((3 * n + 1) * n ^ n < (T + n ^ n) * (2 * n + 2))%N.
  have := @sum_lower n n.-1 n1.
  rewrite prednK // big_nat_recr //= -/T expnS.
  set P := (n ^ n)%N => h; nia.
(* transfer to R *)
apply/andP; split.
- rewrite ltr_pdivrMr; last by lra.
  rewrite mulrAC ltr_pdivlMr //.
  rewrite (_ : (3 * n%:R + 1) * (n ^ n)%:R = ((3 * n + 1) * n ^ n)%:R); last by ring.
  rewrite (_ : (T + n ^ n)%:R * (2 * n%:R + 2) = ((T + n ^ n) * (2 * n + 2))%:R); last by ring.
  by rewrite ltr_nat.
- rewrite ltr_pdivrMr //.
  rewrite (_ : 2 * (n ^ n)%:R = (2 * n ^ n)%:R); last by ring.
  by rewrite ltr_nat.
Qed.

Print Assumptions putnam_1962_b5.
