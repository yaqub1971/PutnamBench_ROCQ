(* ============================================================================
   PutnamBench 1966 A6 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: prove that sqrt(1 + 2 sqrt(1 + 3 sqrt(1 + 4 sqrt(1 + 5 sqrt(...))))) = 3, i.e.
   that the truncations a n 1 = sqrt(1 + 2 sqrt(1 + 3 sqrt(1 + ... + (n-1) sqrt(1 + n)))),
   defined by a n n = n and a n m = m * sqrt(1 + a n (m+1)) for 1 <= m < n, tend to 3
   as n -> oo.
   Source: coq/src/putnam_1966_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement (audit verdict: compile): the file does not compile.
   The target of "-->" is the bare numeral 3, which elaborates to 3%:R in an unknown
   additive monoid ("GRing.Nmodule.sort ?t") and cannot be unified with the filter
   structure the notation expects ("Filtered.sort ?s"); Coq 8.18.0 / MathComp 2.1.0 /
   MathComp-Analysis 1.0.0 reject the upstream file at that token. Mathematically the
   statement is faithful to the problem: it is PutnamBench's Lean statement of 1966 A6
   (Tendsto (fun n => a n 1) atTop (nhds 3), same recursion for a) transcribed to Rocq.
   Fix: exactly one line of the statement differs from putnam_1966_a6.v (the upstream
   statement), by one token:
     "    : (fun n => a n 1%nat) @ \oo --> 3."
     -> "    : (fun n => a n 1%nat) @ \oo --> (3 : R)."
   The ascription only names the type in which the numeral lives (R, the realType the
   statement is about), which is what the upstream author necessarily meant and what the
   Lean statement has (3 : Real). Hypotheses, recursion, indexing (1-based, a n n = n) and
   the limit are unchanged; the corrected statement is neither weakened nor strengthened.
   Compat lines: the lines marked "(* compat: ... *)" are the repository's marked
   compatibility lines for its CI toolchain (Rocq 9.1 / MathComp 2.5 / MathComp-Analysis
   1.16, not run here): (1) a Variable outside a Section is an error since Rocq 9.0, and
   the upstream statement declares R this way; (2) MathComp 2.5's all_ssreflect
   re-declares the ring notations 1 and %:R, which the statement uses (n%:R, 1 + ..., 3),
   so ssralg is re-imported after the upstream imports as in the repository's other
   MathComp files (this file's upstream import order is all_ssreflect then all_algebra,
   so the re-import is expected to be redundant here; it is kept for uniformity). On
   Coq 8.18 / MathComp 2.1 both are no-ops. Neither changes the meaning of the statement.
   Verified: compiles on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: on that toolchain the import lines below trigger library warnings
   emitted by MathComp itself (overridden notations, ambiguous coercion paths); they are
   not about this file, and none of this file's own lines produces any. The import lines
   are kept exactly as upstream wrote them so that the statement stays identical to the
   benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals normedtype topology sequences.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1966_a6
    (a : nat -> (nat -> R))
    (ha : forall n : nat, ge n 1 ->
        a n n = n%:R /\ (forall m : nat, ge m 1 -> lt m n -> a n m = m%:R * (@Num.sqrt R (1 + a n (S m)))))
    : (fun n => a n 1%nat) @ \oo --> (3 : R).
Proof. Admitted.