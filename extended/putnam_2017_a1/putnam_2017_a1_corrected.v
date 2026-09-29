(* ============================================================================
   PutnamBench 2017 A1 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: let S be the smallest set of positive integers such that (a) 2 is in S,
   (b) n is in S whenever n^2 is in S, and (c) (n+5)^2 is in S whenever n is in S; which
   positive integers are not in S? (Answer: 1 and the positive multiples of 5.)
   Source: coq/src/putnam_2017_a1.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: the minimality of S is written
   "forall T : set int, T `<=` S -> ~ IsQualifying T", which quantifies over all subsets
   T of S including T = S; with the first conjunct "IsQualifying S" the hypothesis hS is
   contradictory, so the theorem is vacuously true for any solution set
   (putnam_2017_a1_statement_is_vacuous.v closes it in two lines).
   Fix: apart from this header comment, differs from putnam_2017_a1.v (the upstream
   statement) in exactly one line:
     before: (hS : IsQualifying S /\ forall T : set int, T `<=` S -> ~ IsQualifying T)
     after:  (hS : IsQualifying S /\ forall T : set int, IsQualifying T -> S `<=` T)
   i.e. S is the LEAST qualifying set: it qualifies and is contained in every qualifying
   set. This is "the smallest set" of the problem and exactly the Lean statement's
   "IsLeast IsQualifying S" (IsQualifying S /\ S is a lower bound of the qualifying sets
   for inclusion). Such an S exists (the intersection of all qualifying sets qualifies,
   and the positive integers form a qualifying set), so the hypotheses are satisfiable.
   Everything else (imports, IsQualifying_def, the solution set {x > 0 | x = 1 or 5 | x},
   the conclusion "complement of S within the positive integers = solution") is
   upstream's text unchanged.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile on Rocq 9.1 / MathComp 2.5: importing all_ssreflect after
   all_algebra (upstream's order) overrides the ring notation 1, so "x = 1" on int in
   the solution set no longer typechecks; ssralg is re-imported. They change nothing in
   the meaning of the statement and are no-ops on Coq 8.18 / MathComp 2.1.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the first import line below triggers library warnings emitted by
   MathComp itself (all_ssreflect is deprecated since 2.5, ambiguous coercion paths,
   overridden notations). They are library warnings, not warnings about this file: none
   of this file's own lines produce any. The import lines are kept exactly as upstream
   wrote them so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import classical_sets.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition putnam_2017_a1_solution : set int := [set x : int | x > 0 /\ (x = 1 \/ (5 %| x)%Z)].
Theorem putnam_2017_a1
    (IsQualifying : (set int) -> Prop)
    (IsQualifying_def : forall S, IsQualifying S <-> 
        (forall n : int, n \in S -> n > 0) /\
        2 \in S /\
        (forall n : int, n > 0 /\ (n ^ 2) \in S -> n \in S) /\
        (forall n : int, n \in S -> (n + 5) ^ 2 \in S))
    (S : set int)
    (hS : IsQualifying S /\ forall T : set int, IsQualifying T -> S `<=` T)
    : ~` S `&` [set n : int | n > 0] = putnam_2017_a1_solution.
Proof. Admitted.