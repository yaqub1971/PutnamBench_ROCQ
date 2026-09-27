(* ============================================================================
   PutnamBench 1962 A6 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Differs from putnam_1962_a6.v (the upstream statement) in two ways, both inside
   hSScond: "~(A r \/ A (-r))" becomes "~(A r /\ A (-r))", and every "r = 0" (Leibniz
   equality on non-canonical Q fractions) becomes "r == 0" (Qeq). With these changes
   the hypotheses are satisfied by the positive rationals, so the theorem is no longer
   vacuous, and no further hypothesis is needed for the conclusion.
   Proved in putnam_1962_a6_corrected_proof.v.
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
    (hSScond : forall r : Q, (A r \/ A (-r) \/ r == 0) /\ ~(A r /\ A (-r)) /\ ~(A r /\ r == 0) /\ ~(A (-r) /\ r == 0))
    : A = (fun r : Q => r > 0).
Proof. Admitted.