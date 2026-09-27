(* ============================================================================
   PutnamBench 1962 A6 -- proof that the UPSTREAM statement is vacuous.
   The Theorem below is upstream's statement verbatim (coq/src/putnam_1962_a6.v from
   PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20)), closed by a one-line proof
   that only exploits the contradiction in hSScond (no mathematics involved): the
   second conjunct denies both A r and A (-r), so the first conjunct forces 1 = 0.
   Print Assumptions at the end prints "Closed under the global context".
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 and on Coq 8.18.0.
   About the warnings: the file is written for Coq 8.x. Rocq 9.1 warns "Loading Stdlib
   without prefix is deprecated" on the Require line and would prefer
   "From Stdlib Require Import Ensembles QArith"; the line is kept as upstream wrote it.
   ============================================================================ *)

(* The benchmark statement putnam_1962_a6.v, verbatim, closed by a one-line proof that only
   exploits the contradiction in hSScond (no mathematics involved): *)
Require Import Ensembles QArith.
Theorem putnam_1962_a6
    (A : Ensemble Q)
    (hSSadd : forall a b : Q, (A a /\ A b) -> A (a + b))
    (hSSprod : forall a b : Q, (A a /\ A b) -> A (a * b))
    (hSScond : forall r : Q, (A r \/ A (-r) \/ r = 0) /\ ~(A r \/ A (-r)) /\ ~(A r /\ r = 0) /\ ~(A (-r) /\ r = 0))
    : A = (fun r : Q => r > 0).
Proof.
  (* the 2nd conjunct says neither A r nor A (-r) ever holds, so the 1st forces 1 = 0 *)
  destruct (hSScond 1) as [[h|[h|h]] [hn _]]; try (exfalso; apply hn; tauto); discriminate h.
Qed.
Print Assumptions putnam_1962_a6.
