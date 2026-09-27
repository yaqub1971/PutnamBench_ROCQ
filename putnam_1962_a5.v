(* ============================================================================
   PutnamBench 1962 A5 -- Rocq/MathComp proof.
   Problem: for n >= 2,  sum_(k = 1..n) C(n,k) * k^2  =  n (n+1) 2^(n-2).
   Statement: coq/src/putnam_1962_a5.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   The Definition and the Theorem below are byte-identical to upstream; only the
   helper lemmas and the proof script were added.
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 (Ubuntu 24.04):
   compiles; Print Assumptions putnam_1962_a5 = "Closed under the global context"
   (no axioms); rocqchk / coqchk: "Modules were successfully checked".
   Companion sanity check: audit_1962_a5.v.
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import line
   below triggers ~30 warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import line is kept exactly as upstream wrote it so that the statement stays
   identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope nat_scope.

Definition putnam_1962_a5_solution : nat -> nat := fun n : nat => n * (n + 1) * 2 ^ (n - 2).

(* Row sum of Pascal's triangle. Mathlib has this as Nat.sum_range_choose;
   MathComp only ships the general binomial theorem, so we specialise it. *)
Lemma sum_bin n : \sum_(0 <= k < n.+1) 'C(n, k) = 2 ^ n.
Proof.
rewrite -[2]/(1 + 1) expnDn big_mkord.
by apply: eq_bigr => i _; rewrite !exp1n !muln1.
Qed.

(* First moment: sum of k * C(m+1, k), via the absorption identity mul_bin_diag *)
Lemma sum_bin_k m : \sum_(1 <= k < m.+2) 'C(m.+1, k) * k = m.+1 * 2 ^ m.
Proof.
rewrite big_add1 /= -sum_bin big_distrr /=.
by apply: eq_bigr => k _; rewrite mulnC -mul_bin_diag.
Qed.

(* Second moment, for n = r + 2 *)
Lemma sum_bin_k2 r : \sum_(1 <= k < r.+3) 'C(r.+2, k) * k ^ 2 = r.+2 * r.+3 * 2 ^ r.
Proof.
rewrite big_add1 /=.
have -> : \sum_(0 <= j < r.+2) 'C(r.+2, j.+1) * j.+1 ^ 2
        = r.+2 * (\sum_(0 <= j < r.+2) 'C(r.+1, j) * j + \sum_(0 <= j < r.+2) 'C(r.+1, j)).
  rewrite -big_split /= big_distrr /=; apply: eq_bigr => j _.
  by rewrite addnC -mulnS mulnA mul_bin_diag -mulnn mulnA [j.+1 * _]mulnC.
rewrite big_ltn // muln0 add0n sum_bin_k sum_bin.
by rewrite expnS -mulnDl addn2 mulnA.
Qed.

Theorem putnam_1962_a5
    : forall n : nat, n >= 2 ->
        putnam_1962_a5_solution n = \sum_(1 <= k < n.+1) (binomial n k * k ^ 2).
Proof.
case=> [|[|r]] // _.
by rewrite /putnam_1962_a5_solution addn1 !subSS subn0 sum_bin_k2.
Qed.
