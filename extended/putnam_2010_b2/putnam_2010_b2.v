(* ============================================================================
   PutnamBench 2010 B2 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_2010_b2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines were needed:
   the file uses only the standard library).
   Problem: A, B, C are noncollinear points in the plane with integer coordinates such that
   the distances AB, AC, BC are integers; what is the smallest possible value of AB?
   (Answer: 3.)
   Defect (audit verdict: vacuous, machine-checked): the local definition
   "noncollinear A B C := ~exists (s t : R), (s * (c - a) + t * (e - a), s * (d - b) + t * (f - b)) = (0, 0)"
   is ALWAYS false, because s = t = 0 is such a pair for every A, B, C (it should exclude
   only NONTRIVIAL linear relations between B - A and C - A). So p A B C is never
   satisfied, hypothesis hm is unsatisfiable, and the theorem is provable for any value of
   putnam_2010_b2_solution with no mathematics: see putnam_2010_b2_statement_is_vacuous.v.
   Proposed fix (one line, in the definition of noncollinear): putnam_2010_b2_corrected.v.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the file is written for Coq 8.x. Rocq 9.1 warns "Loading Stdlib
   without prefix is deprecated" on the Require line and would prefer
   "From Stdlib Require Import Reals Rgeom ZArith"; the line is kept as upstream wrote it.
   ============================================================================ *)

Require Import Reals Rgeom ZArith.
Open Scope R.
Definition putnam_2010_b2_solution := 3.
Theorem putnam_2010_b2
    (dist : (R * R) -> (R * R) -> R := fun A B => let (a, b) := A in let (c, d) := B in dist_euc a b c d)
    (int_val : (R * R) -> Prop := fun P => exists (x y : Z), P = (IZR x, IZR y))
    (noncollinear: (R * R) -> (R * R) -> (R * R) -> Prop := fun A B C => let (a, b) := A in let (c, d) := B in let (e, f) := C in
        ~exists (s t : R), (s * (c - a) + t * (e - a), s * (d - b) + t * (f - b)) = (0, 0))
    (p : (R * R) -> (R * R) -> (R * R) -> Prop :=
        fun A B C => noncollinear A B C /\ int_val A /\ int_val B /\ int_val C /\
        (exists (x : Z), dist A B = IZR x) /\ (exists (y : Z), dist A C = IZR y) /\ (exists (z : Z), dist B C = IZR z))
    (m : R)
    (hm : exists (A B C: R * R), p A B C /\ dist A B = m)
    (hmlb : forall (A B C: R * R), p A B C -> dist A B >= m)
    : m = putnam_2010_b2_solution.
Proof. Admitted.
