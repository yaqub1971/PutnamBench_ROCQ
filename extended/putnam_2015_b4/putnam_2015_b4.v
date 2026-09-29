(* ============================================================================
   PutnamBench 2015 B4 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_2015_b4.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines; see below).
   Problem: let T be the set of all triples (a,b,c) of positive integers that are the
   side lengths of a triangle; express sum_{(a,b,c) in T} 2^a / (3^b 5^c) as a rational
   number in lowest terms (answer: 17/21).
   Defect (a compile defect; the mathematics is faithful): the file does not compile.
   The target of "-->" in the hypothesis
     (hf : (fun n : nat => f n) @ \oo --> ratr C)
   is "ratr C", whose type is only known to be some unit ring; "-->" expects a point of
   a filtered (topological) type, so elaboration fails with
     The term "ratr C" has type "GRing.UnitRing.sort ?R"
     while it is expected to have type "Filtered.sort ?s".
   The one-token ascription "--> (ratr C : R)" fixes it without changing the meaning; the
   rest of the statement is faithful to the problem (strict triangle inequalities, all
   three indices ranging over the positive integers, limit of the cube partial sums, and
   the answer 17/21 read off as (numq C, denq C) = (17, 21), i.e. in lowest terms).
   Proposed fix: putnam_2015_b4_corrected.v.
   Compat lines: none. The repository's marked "(* compat: ... *)" lines would not make
   this file compile (the error above is independent of them), so the upstream text is
   kept strictly verbatim; putnam_2015_b4_corrected.v carries the compat lines it needs
   on Rocq 9.1 / MathComp 2.5.
   Does not compile on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu 24.04):
   error at the "--> ratr C" of hypothesis hf (upstream line 25, characters 41-47), quoted
   above. (The upstream "Variable R : realType." outside a Section also draws Coq 8.18's
   local-declaration warning there.)
   Does not compile on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (Nix) either:
   there the first error is at the top-level "Variable R : realType." line,
     Error: Use of "Variable" or "Hypothesis" outside sections behaves as
     "#[local] Parameter" or "#[local] Axiom". [declaration-outside-section,vernacular,default]
   (Rocq >= 9.0 rejects a Variable declared outside a Section), before "--> ratr C" is reached.
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1; the import lines below trigger warnings emitted by MathComp itself
   (ambiguous coercion paths, overridden notations), which are library warnings, not
   warnings about this file. The import lines are kept exactly as upstream wrote them so
   that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals normedtype sequences topology.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

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
    (hf : (fun n : nat => f n) @ \oo --> ratr C)
    : (numq C, denq C) = putnam_2015_b4_solution.
Proof. Admitted.