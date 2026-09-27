(* ============================================================================
   Sanity check ("audit") for putnam_1962_a5.v. Not part of the proof.
   Needs putnam_1962_a5.vo; compile with:  rocq compile -R . "" audit_1962_a5.v
   Purpose: make sure the benchmark statement means what the Putnam problem says,
   independently of the proof.
     spot_checks  : evaluates both sides of the identity at n = 2..7 by computation
                    (6, 24, 80, 240, 672, 1792), so the formal sum has the intended
                    bounds and meaning.
     n_ge2_needed : the two sides differ at n = 1 (2 vs 1), so the hypothesis n >= 2
                    is necessary; the theorem is neither vacuous nor over-general.
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 (Ubuntu 24.04): compiles (both lemmas are closed by computation).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import line
   below triggers ~30 warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import line is kept exactly as upstream wrote it so that the statement stays
   identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
Require putnam_1962_a5.
Open Scope nat_scope.
Notation sol := putnam_1962_a5.putnam_1962_a5_solution.
Definition rhs n := \sum_(1 <= k < n.+1) (binomial n k * k ^ 2).

(* The formal sum really is  sum_{k=1..n} C(n,k) k^2 : evaluate both sides concretely *)
Lemma spot_checks : [seq (sol n, rhs n) | n <- [:: 2; 3; 4; 5; 6; 7]]
                  = [:: (6,6); (24,24); (80,80); (240,240); (672,672); (1792,1792)].
Proof. by rewrite /rhs /sol /= !unlock /=. Qed.

(* The side condition n >= 2 is load-bearing: at n = 1 the two sides differ (2 vs 1),
   because 2^(n-2) uses truncated subtraction *)
Lemma n_ge2_needed : sol 1 <> rhs 1.
Proof. by rewrite /rhs /sol /= unlock. Qed.
