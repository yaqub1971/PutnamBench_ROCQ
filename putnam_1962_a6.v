(* ============================================================================
   PutnamBench 1962 A6 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1962_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim.
   Defects found in this statement (reported to the maintainers, see
   ISSUE_REPORT_rocq.md):
     1. In hSScond the second conjunct is "~(A r \/ A (-r))"; it should be
        "~(A r /\ A (-r))". As written it says neither A r nor A (-r) ever holds, which
        with the first conjunct forces r = 0 for every r. The hypotheses are therefore
        contradictory and the theorem is VACUOUSLY provable with no mathematics:
        see putnam_1962_a6_statement_is_vacuous.v.
     2. "r = 0" is Leibniz equality on Q, whose fractions are not canonical
        (0#2 <> 0 although 0#2 == 0); it should be "r == 0".
   Proposed fix: putnam_1962_a6_corrected.v.
   Verified: compiles on Rocq 9.1.0 and on Coq 8.18.0.
   About the warnings: the file is written for Coq 8.x. Rocq 9.1 warns "Loading Stdlib
   without prefix is deprecated" on the Require line and would prefer
   "From Stdlib Require Import Ensembles QArith"; the line is kept as upstream wrote it.
   ============================================================================ *)

Require Import Ensembles QArith.
Theorem putnam_1962_a6
    (A : Ensemble Q)
    (hSSadd : forall a b : Q, (A a /\ A b) -> A (a + b))
    (hSSprod : forall a b : Q, (A a /\ A b) -> A (a * b))
    (hSScond : forall r : Q, (A r \/ A (-r) \/ r = 0) /\ ~(A r \/ A (-r)) /\ ~(A r /\ r = 0) /\ ~(A (-r) /\ r = 0))
    : A = (fun r : Q => r > 0).
Proof. Admitted.