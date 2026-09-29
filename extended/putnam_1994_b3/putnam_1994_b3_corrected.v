(* ============================================================================
   PutnamBench 1994 B3 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: find the set of all real numbers k such that for every positive
   differentiable f : R -> R with f'(x) > f(x) for all x there is N with f(x) > e^(kx)
   for all x > N. (Answer: the interval (-oo, 1).)
   Source: coq/src/putnam_1994_b3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement (see putnam_1994_b3.v): (1) naming: it defines
   putnam_1993_b3_solution and Theorem putnam_1993_b3 instead of the 1994 names;
   (2) compile: the type of f in the set-builder is left to inference, which fails at
   "0 < f x" ("The term f x has type NormedModule.sort ?W while it is expected to have
   type Order.POrder.sort (...)"). The mathematics is otherwise faithful.
   Fix: four changed lines (upstream lines 14-17), nothing else:
     Definition putnam_1993_b3_solution ...   ->  Definition putnam_1994_b3_solution ...
     Theorem putnam_1993_b3                   ->  Theorem putnam_1994_b3
     : [set k | forall f (hf : ...            ->  : [set k | forall (f : R -> R) (hf : ...
     ... expR (k * x) < f x] = putnam_1993_b3_solution.
                                              ->  ... = putnam_1994_b3_solution.
   The annotation only states the type the problem intends
   (f : R -> R); it matches PutnamBench's Lean statement (f : R -> R there by
   inference from Real.exp and deriv). The rest is upstream's text and matches the
   problem: "differentiable f x" at every x; "0 < f x < f^`() x" is 0 < f(x) and
   f(x) < f'(x) (f^`() is derive1, the ordinary derivative); "expR (k * x)" is e^(kx)
   (expR is the exponential series); "exists N : R, forall x, N < x -> ..." is "for all
   x > N"; the answer set [set k | k < 1] is (-oo, 1), the official answer and the
   Lean statement's Set.Iio 1; the equality of sets is the "find all k" of the problem.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   text has constructs that the repository README documents as fatal or risky on
   Rocq 9.1 / MathComp 2.5: (1) a Variable outside a Section is an error since Rocq 9.0;
   (2) the ssralg re-import that protects the ring notations 1 and %:R. This file already
   imports ssralg after all_ssreflect and never imports all_algebra, so here the
   re-import is a no-op on MathComp 2.5 as well (checked: the theorem's type and the
   solution set print identically under Set Printing All with and without it); it is
   kept for uniformity with the repository. Neither line changes the meaning of the
   statement. The file already opens classical_set_scope, where MathComp-Analysis
   >= 1.9 puts the notation f^`(), so compat line (3) is not needed.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1; the first import line below triggers warnings emitted by MathComp
   itself (all_ssreflect deprecated since MathComp 2.5, ambiguous coercion paths,
   overridden notations). They are library warnings, not warnings about this file: none
   of this file's own lines produce any. The import lines are kept exactly as upstream
   wrote them so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import reals normedtype derive topology sequences.
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
Definition putnam_1994_b3_solution : set R := [set k | k < 1].
Theorem putnam_1994_b3
    : [set k | forall (f : R -> R) (hf : forall x, differentiable f x /\ 0 < f x < f^`() x),
        exists N : R, forall x, N < x -> expR (k * x) < f x] = putnam_1994_b3_solution.
Proof. Admitted.