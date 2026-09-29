(* ============================================================================
   PutnamBench 2022 A6 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: for a positive integer n, determine the largest integer m such that there
   are reals -1 < x_1 < ... < x_{2n} < 1 for which the total length of the n intervals
   [x_1^(2k-1), x_2^(2k-1)], ..., [x_{2n-1}^(2k-1), x_{2n}^(2k-1)] equals 1 for every
   k = 1, ..., m. Answer: m = n.
   Source: coq/src/putnam_2022_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Notation: the statement's N is the problem's n (the number of intervals), its
   n := N * 2 is the number of points, and s : 'I_n -> R lists x_1, ..., x_{2N} as
   s 0, ..., s (2N-1) (0-indexed). N >= 1 is implied by the inhabitant i0 : 'I_n.
   Defect of the upstream statement: VACUOUS -- hvalid m was
   "exists s, (ordering conditions) -> valid m s", true for every m via any s that
   violates the ordering (e.g. a constant s), so hMub at M+1 gives M+1 <= M (see
   putnam_2022_a6_statement_is_vacuous.v). Moreover (a) the ordering used the cyclic
   successor ordS, which can never be strictly increasing all the way round, (b) the
   interval sum added all 2N consecutive differences, reading index 2N out of range,
   and (c) the conclusion stated the answer 2N (solution applied to n = 2N) instead of N.
   Fix (three lines of the statement; everything else is upstream's text):
     sumIntervals: sum_n (fun i => s(nth (i+1))^(2k-1) - s(nth i)^(2k-1)) (n-1)
                -> sum_n (fun i => s(nth (2*i+1))^(2k-1) - s(nth (2*i))^(2k-1)) (N-1),
        i.e. sum over i = 0..N-1 (sum_n is inclusive) of x_{2i+2}^(2k-1) - x_{2i+1}^(2k-1)
        in the problem's 1-indexing: the lengths of the N intervals.
     hvalid: "(s i < s (ordS i)) /\ ... ) -> valid m s"
          -> "(forall (j : 'I_n), lt i j -> s i < s j) /\ ... ) /\ valid m s":
        s strictly increasing, -1 < x_1, x_{2N} < 1, AND the interval condition.
     conclusion: "M = putnam_2022_a6_solution n" -> "M = putnam_2022_a6_solution N".
   The shape (hM : M has the property, hMub : every m with the property is <= M,
   conclude M = answer) is upstream's and is kept; the set of such m is {0, ..., N},
   so it pins down the answer. The Lean statement (IsGreatest of the same set, with
   x : nat -> R strictly monotone, -1 < x 1, x (2n) < 1 and the sum over i in [1, n]
   of x(2i)^(2k-1) - x(2i-1)^(2k-1)) encodes the same set.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the import line below triggers warnings emitted by the libraries
   themselves (Rocq 9.1: "Loading Stdlib without prefix is deprecated"; MathComp:
   ambiguous coercion paths, overridden notations, hidden scope keys). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import line is kept exactly as upstream wrote it.
   ============================================================================ *)

Require Import Nat Reals Coquelicot.Hierarchy. From mathcomp Require Import div fintype seq ssralg ssrbool ssrnat ssrnum .
Definition putnam_2022_a6_solution := fun n : nat => n.
Theorem putnam_2022_a6
    (N : nat)
    (M : nat)
    (n := mul N 2)
    (i0 : 'I_n)
    (sumIntervals : ('I_n -> R) -> nat -> R := fun s k => sum_n (fun i => (((s (nth i0 (enum 'I_n) (2*i+1))))^(2*k-1) - ((s (nth i0 (enum 'I_n) (2*i))))^(2*k-1))) (N-1))
    (valid : nat -> ('I_n -> R) -> Prop := fun m s => forall (k: nat), and (le 1 k) (le k m) -> sumIntervals s k = 1)
    (hvalid : nat -> Prop := fun m => exists (s : 'I_n -> R), (forall (i : 'I_n),  (forall (j : 'I_n), lt i j -> s i < s j) /\ s (nth i0 (enum 'I_n) 0) > -1 /\ s (nth i0 (enum 'I_n) (n-1)) < 1) /\ valid m s)
    (hM : hvalid M)
    (hMub : forall m : nat, hvalid m -> le m M)
    : M = putnam_2022_a6_solution N.
Proof. Admitted. 
