(* ============================================================================
   PutnamBench 2015 B4 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: let T be the set of all triples (a,b,c) of positive integers that are the
   side lengths of a triangle; express sum_{(a,b,c) in T} 2^a / (3^b 5^c) as a rational
   number in lowest terms (answer: 17/21).
   Source: coq/src/putnam_2015_b4.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: it does not compile (see putnam_2015_b4.v). The target
   of "-->" in hypothesis hf is "ratr C", whose type is only known to be some unit ring;
   "-->" expects a point of a filtered (topological) type, so elaboration fails with
     The term "ratr C" has type "GRing.UnitRing.sort ?R"
     while it is expected to have type "Filtered.sort ?s".
   The mathematics of the upstream statement is faithful; nothing else needed a change.
   Fix: exactly one type ascription is added, in hypothesis hf:
     (hf : (fun n : nat => f n) @ \oo --> ratr C)
   becomes
     (hf : (fun n : nat => f n) @ \oo --> (ratr C : R))
   The ascription only names the type of the limit: hf says "the partial sums f n converge
   to the real number C" (it unfolds to cvg_to (fmap f \oo) (nbhs (ratr C : R))). Everything
   else is upstream's text and matches the problem: tri_fun i j k is 2^i / (3^j 5^k) when
   i, j, k satisfy the three STRICT triangle inequalities (a non-degenerate triangle) and 0
   otherwise; f n sums it over 1 <= i, j, k < n (positive integers only), and as the terms
   are nonnegative the limit of these cube partial sums is the sum over T; the conclusion
   (numq C, denq C) = (17, 21) says that C is 17/21 written in lowest terms (numq/denq are
   the reduced numerator and positive denominator). PutnamBench's Lean statement has the
   same answer (17, 21) read off with q.num, q.den.
   Compat lines: the lines marked "(* compat: ... *)" were added because, independently of
   the defect above, the upstream text has the two constructs that the repository README
   documents as fatal on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a Section is an
   error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect after all_algebra
   (upstream's order) overrides the ring notations 1 and %:R, so ssralg is re-imported.
   Neither changes the meaning of the statement; both are no-ops on Coq 8.18 / MathComp 2.1.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1; the import lines below trigger warnings emitted by MathComp itself
   (ambiguous coercion paths, overridden notations). They are library warnings, not
   warnings about this file: none of this file's own lines produce any. The import lines
   are kept exactly as upstream wrote them so that the statement stays identical to the
   benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals normedtype sequences topology.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Definition putnam_2015_b4_solution : int * int := (17%Z, 21%Z).
Theorem putnam_2015_b4
    (tri_fun : nat -> nat -> nat -> R := fun i j k : nat => 
        if (ltn i (Nat.add j k)) && (ltn j (Nat.add i k)) && (ltn k (Nat.add i j)) then (2 ^+ i) / ((3 ^+ j * 5 ^+ k)) else 0)
    (f : nat -> R := fun n : nat => 
        \sum_(1 <= i < n)
        (\sum_(1 <= j < n) 
        (\sum_(1 <= k < n) 
        (tri_fun i j k))))
    (C : rat)
    (hf : (fun n : nat => f n) @ \oo --> (ratr C : R))
    : (numq C, denq C) = putnam_2015_b4_solution.
Proof. Admitted.