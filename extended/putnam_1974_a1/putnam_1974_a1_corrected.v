(* ============================================================================
   PutnamBench 1974 A1 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: call a set of positive integers conspiratorial if no three of them are
   pairwise relatively prime; what is the largest number of elements of a conspiratorial
   subset of the integers 1 through 16? (Answer: 11.)
   Source: coq/src/putnam_1974_a1.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: it is incomplete. Its conclusion only says that
   every conspiratorial A included in [1, 16] has at most putnam_1974_a1_solution = 11
   elements (A #<= [set : 'I_11]); it never says that 11 elements are attained. That
   upper bound implies the same bound with 12, 13, ... in place of 11, so the theorem
   does not determine the answer: it would be just as provable with the wrong answer
   putnam_1974_a1_solution := 12. The problem asks for the LARGEST size, i.e. both halves.
   Fix: apart from this header comment and the marked compat lines, the file differs
   from putnam_1974_a1.v (the upstream statement) only in the conclusion. The line
     : forall A : set int, A `<=` [set x : int | 1 <= x <= 16] -> conspiratorial A -> A #<= [set : 'I_(putnam_1974_a1_solution)].
   becomes the two lines
     : (exists A : set int, A `<=` [set x : int | 1 <= x <= 16] /\ conspiratorial A /\ A #= [set : 'I_(putnam_1974_a1_solution)]) /\
       forall A : set int, A `<=` [set x : int | 1 <= x <= 16] -> conspiratorial A -> A #<= [set : 'I_(putnam_1974_a1_solution)].
   The first conjunct is new: some conspiratorial subset of [1, 16] has exactly
   putnam_1974_a1_solution elements ("#=" is MathComp-Analysis' equality of cardinals,
   the notation PutnamBench's own 2015 B5 statement uses). The second conjunct is the
   upstream conclusion, verbatim. Together they say that putnam_1974_a1_solution is the
   maximum size, which is what the problem asks and what the Lean statement says
   (IsGreatest {k | exists S, S subset of Icc 1 16, conspiratorial S, S.encard = k}
   putnam_1974_a1_solution: membership = the new conjunct, upper bound = the old one).
   The answer 11, the definition of conspiratorial (pairwise distinct positive a, b, c
   of A are never pairwise coprime), the range 1 <= x <= 16 and the names are upstream's
   and were re-checked against the problem; nothing is weakened and no hypothesis added.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: with MathComp 2.5, importing
   all_ssreflect after all_algebra (upstream's order) overrides the ring notations 1 and
   %:R, so ssralg is re-imported. This does not change the meaning of the statement and
   is a no-op on Coq 8.18 / MathComp 2.1.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1.1 / MathComp 2.5.0 the first import line below triggers
   30 warnings emitted by MathComp itself (all_ssreflect is deprecated since 2.5,
   ambiguous coercion paths, overridden notations); under Coq 8.18.0 / MathComp 2.1.0 it
   triggers 23. They are library warnings, not warnings about this file: none of this
   file's own lines produce any. The import lines are kept exactly as upstream wrote them
   so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import classical_sets cardinality.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

Definition putnam_1974_a1_solution : nat := 11%nat.
Theorem putnam_1974_a1
    (conspiratorial : set int -> Prop := fun A => forall a b c : int, (a \in A) -> (b \in A) -> (c \in A) -> (a > 0) -> (b > 0) -> (c > 0) -> (a <> b) -> (b <> c) -> (c <> a) -> (~ coprimez a b \/ ~ coprimez b c \/ ~ coprimez c a))
    : (exists A : set int, A `<=` [set x : int | 1 <= x <= 16] /\ conspiratorial A /\ A #= [set : 'I_(putnam_1974_a1_solution)]) /\
      forall A : set int, A `<=` [set x : int | 1 <= x <= 16] -> conspiratorial A -> A #<= [set : 'I_(putnam_1974_a1_solution)].
Proof. Admitted.
