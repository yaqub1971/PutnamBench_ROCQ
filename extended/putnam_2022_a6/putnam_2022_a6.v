(* ============================================================================
   PutnamBench 2022 A6 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_2022_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines needed).
   Problem: for a positive integer n, determine the largest integer m such that there
   are reals -1 < x_1 < ... < x_{2n} < 1 for which the total length of the n intervals
   [x_1^(2k-1), x_2^(2k-1)], ..., [x_{2n-1}^(2k-1), x_{2n}^(2k-1)] equals 1 for every
   k = 1, ..., m. Answer: m = n.
   Defects (here N is the problem's n and the statement's n is 2N):
     1. VACUOUS: hvalid m is "exists s, (ordering conditions) -> valid m s". Any s
        violating the ordering (e.g. a constant one) makes the implication true, so
        hvalid m holds for every m, and hMub at M+1 gives M+1 <= M. Proof (the upstream
        Theorem closed using only this contradiction): putnam_2022_a6_statement_is_vacuous.v.
     2. The ordering "forall i, s i < s (ordS i)" uses the cyclic successor ordS
        (ordS of the last index is 0), so it can never hold: even with "/\" in place of
        "->" the set of valid m would be empty.
     3. sumIntervals sums ALL 2N consecutive differences s(x_{i+1})^(2k-1) - s(x_i)^(2k-1)
        for i = 0..2N-1 (sum_n is inclusive), which telescopes, and index 2N is out of
        range (nth returns the default i0); the problem sums only the N differences
        x_{2i}^(2k-1) - x_{2i-1}^(2k-1).
     4. The conclusion "M = putnam_2022_a6_solution n" states the answer 2N (n = 2N);
        the answer is N.
     Proposed fix: putnam_2022_a6_corrected.v.
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
    (sumIntervals : ('I_n -> R) -> nat -> R := fun s k => sum_n (fun i => (((s (nth i0 (enum 'I_n) (i+1))))^(2*k-1) - ((s (nth i0 (enum 'I_n) i)))^(2*k-1))) (n-1))
    (valid : nat -> ('I_n -> R) -> Prop := fun m s => forall (k: nat), and (le 1 k) (le k m) -> sumIntervals s k = 1)
    (hvalid : nat -> Prop := fun m => exists (s : 'I_n -> R), (forall (i : 'I_n),  (s i < s (ordS i)) /\ s (nth i0 (enum 'I_n) 0) > -1 /\ s (nth i0 (enum 'I_n) (n-1)) < 1) -> valid m s)
    (hM : hvalid M)
    (hMub : forall m : nat, hvalid m -> le m M)
    : M = putnam_2022_a6_solution n.
Proof. Admitted. 
