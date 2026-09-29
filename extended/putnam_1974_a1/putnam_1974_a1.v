(* ============================================================================
   PutnamBench 1974 A1 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1974_a1.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim, except for the three lines
   marked "(* compat: ... *)".
   Problem: call a set of positive integers conspiratorial if no three of them are
   pairwise relatively prime; what is the largest number of elements of a conspiratorial
   subset of the integers 1 through 16? (Answer: 11.)
   Defect: the statement is INCOMPLETE (audit verdict "unfaithful (incomplete)"). Its
     conclusion only says that every conspiratorial A included in [1, 16] has at most
     putnam_1974_a1_solution = 11 elements (A #<= [set : 'I_11]). It never says that 11
     elements are attained, so it does not determine the answer: the same conclusion
     with 12 (or any larger number) in place of 11 follows from it, and the theorem
     would be just as provable with the wrong answer putnam_1974_a1_solution := 12.
     The statement is not false (the upper bound is the true half of the problem) and
     not vacuous, so there is no _statement_is_false / _statement_is_vacuous file.
     Proposed fix: putnam_1974_a1_corrected.v (adds the missing existence half).
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: with MathComp 2.5, importing
   all_ssreflect after all_algebra (upstream's order) overrides the ring notations 1 and
   %:R, so the numeral 1 in "1 <= x <= 16" no longer typechecks (error: The term "1" has
   type "BaseUMagma.sort ?s0" while it is expected to have type "Order.Preorder.sort ?s");
   ssralg is therefore re-imported. This does not change the meaning of the statement and
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
    : forall A : set int, A `<=` [set x : int | 1 <= x <= 16] -> conspiratorial A -> A #<= [set : 'I_(putnam_1974_a1_solution)].
Proof. Admitted.
