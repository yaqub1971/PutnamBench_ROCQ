(* ============================================================================
   PutnamBench 2010 B2 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: A, B, C are noncollinear points in the plane with integer coordinates such that
   the distances AB, AC, BC are integers; what is the smallest possible value of AB?
   (Answer: 3.)
   Source: coq/src/putnam_2010_b2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: the local definition
   "noncollinear A B C := ~exists (s t : R), (s * (c - a) + t * (e - a), s * (d - b) + t * (f - b)) = (0, 0)"
   is always false (s = t = 0 is such a pair for every A, B, C), so p A B C never holds,
   hypothesis hm is unsatisfiable and the theorem is VACUOUS
   (putnam_2010_b2_statement_is_vacuous.v proves it with no mathematics).
   Fix: apart from this header comment, this file differs from putnam_2010_b2.v (the upstream
   statement) in one line, the body of noncollinear:
     "~exists (s t : R), (s * (c - a) + t * (e - a), ...) = (0, 0))"
       -> "~exists (s t : R), (s <> 0 \/ t <> 0) /\ (s * (c - a) + t * (e - a), ...) = (0, 0))"
   With A = (a, b), B = (c, d), C = (e, f) the pair is s (B - A) + t (C - A); noncollinear
   now says that no NONTRIVIAL combination of B - A and C - A vanishes, i.e. that B - A and
   C - A are linearly independent, which is exactly "A, B, C are not collinear" (it also
   excludes A = B, A = C and B = C). This is the meaning of the Lean statement's
   "not Collinear R {A, B, C}". Everything else is upstream's and faithful: integer
   coordinates (int_val), integer distances AB, AC, BC (dist is the Euclidean distance
   dist_euc of Rgeom), and "m is the smallest possible AB" encoded as hm (m is attained)
   plus hmlb (m is a lower bound), with conclusion m = 3 (the set of attainable AB is a
   nonempty set of positive integers, so its least element exists and this is equivalent
   to the Lean statement's IsLeast {AB} 3).
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
        ~exists (s t : R), (s <> 0 \/ t <> 0) /\ (s * (c - a) + t * (e - a), s * (d - b) + t * (f - b)) = (0, 0))
    (p : (R * R) -> (R * R) -> (R * R) -> Prop :=
        fun A B C => noncollinear A B C /\ int_val A /\ int_val B /\ int_val C /\
        (exists (x : Z), dist A B = IZR x) /\ (exists (y : Z), dist A C = IZR y) /\ (exists (z : Z), dist B C = IZR z))
    (m : R)
    (hm : exists (A B C: R * R), p A B C /\ dist A B = m)
    (hmlb : forall (A B C: R * R), p A B C -> dist A B >= m)
    : m = putnam_2010_b2_solution.
Proof. Admitted.
