(* ============================================================================
   PutnamBench 1966 A6 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1966_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines were added:
   they could not make the file compile, see below).
   Problem: prove that sqrt(1 + 2 sqrt(1 + 3 sqrt(1 + 4 sqrt(1 + 5 sqrt(...))))) = 3, encoded
   as: the truncations a n 1 = sqrt(1 + 2 sqrt(1 + 3 sqrt(1 + ... + (n-1) sqrt(1 + n)))),
   defined by a n n = n and a n m = m * sqrt(1 + a n (m+1)) for 1 <= m < n, tend to 3.
   Defect (audit verdict: compile): the file does not compile. The target of "-->" on the
   last line of the statement is the bare numeral 3, which elaborates to 3%:R in an unknown
   additive monoid and cannot be unified with the filter structure the notation expects:
     File "./putnam_1966_a6.v", line 18, characters 37-38:
     Error: The term "3" has type "GRing.Nmodule.sort ?t"
     while it is expected to have type "Filtered.sort ?s".
   Mathematically the statement is faithful to the problem (it is the Lean statement of the
   same problem, transcribed). Proposed fix, one token, "--> 3" -> "--> (3 : R)":
   putnam_1966_a6_corrected.v. No evidence file: the statement is neither false nor vacuous.
   On Rocq 9.1 the file would in addition be rejected for declaring "Variable R : realType."
   outside a Section (an error since Rocq 9.0; Coq 8.x only warns), which the marked compat
   line of putnam_1966_a6_corrected.v addresses there.
   Does not compile on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04):
   the error quoted above (checked by running coqc on this file; the build log of the
   upstream file shows the same error at the same position).
   About the warnings: the import line below triggers library warnings emitted by MathComp
   itself (overridden notations, ambiguous coercion paths); they are not about this file.
   The import lines are kept exactly as upstream wrote them so that the statement stays
   identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals normedtype topology sequences.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Theorem putnam_1966_a6
    (a : nat -> (nat -> R))
    (ha : forall n : nat, ge n 1 ->
        a n n = n%:R /\ (forall m : nat, ge m 1 -> lt m n -> a n m = m%:R * (@Num.sqrt R (1 + a n (S m)))))
    : (fun n => a n 1%nat) @ \oo --> 3.
Proof. Admitted.