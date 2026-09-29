(* ============================================================================
   PutnamBench 1974 A3 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: given that a prime p > 2 is a sum of two squares iff p = 1 (mod 4), find the
   primes p > 2 of the form (a) x^2 + 16 y^2 and (b) 4 x^2 + 4 x y + 5 y^2, with x, y
   integers. (Answer: (a) the primes p = 1 (mod 8); (b) the primes p = 5 (mod 8).)
   Source: coq/src/putnam_1974_a3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: the hypothesis that encodes the "well-known theorem"
   has misplaced parentheses. Upstream reads it as
     forall p : nat, ((prime p /\ gt p 2) -> (exists m n : int, ...)) <-> p = 1 %[mod 4],
   a biconditional for EVERY natural number p whose left side is an implication. At
   p = 4 the left side holds vacuously (4 is not prime) and the right side says
   4 = 1 (mod 4), i.e. 0 = 1: the hypothesis is contradictory, so the upstream theorem
   is vacuous (proof in putnam_1974_a3_statement_is_vacuous.v).
   Fix: apart from this header comment and the marked compat lines, the file differs
   from putnam_1974_a3.v (the upstream statement) only in the hypothesis line
     (assmption : forall p : nat, ((prime p /\ gt p 2) -> ((exists m n : int, p%:Z = m ^+ 2 + n ^+ 2))) <-> p = 1 %[mod 4])
   which becomes
     (assmption : forall p : nat, (prime p /\ gt p 2) -> ((exists m n : int, p%:Z = m ^+ 2 + n ^+ 2) <-> p = 1 %[mod 4]))
   i.e. "for every prime p > 2: p is a sum of two integer squares iff p = 1 (mod 4)",
   which is the theorem the problem quotes (Fermat's two-squares theorem, a true
   statement, so the hypothesis is now satisfiable) and exactly the hypothesis of
   PutnamBench's Lean statement of the problem. Only parentheses moved; the tokens are
   upstream's. The conclusion (both biconditionals, with prime p /\ p > 2 on the left)
   and the answer sets {p prime | p = 1 (mod 8)}, {p prime | p = 5 (mod 8)} are
   upstream's, were re-checked against the problem and agree with the Lean statement.
   Compat lines: the lines marked "(* compat: ... *)" are the repository's marked
   compatibility lines for its CI toolchain (Rocq 9.1 / MathComp 2.5): MathComp 2.5's
   all_ssreflect, imported after all_algebra (the upstream order), re-declares the ring
   notations 1 and %:R, which the statement's int arithmetic (16 * y ^+ 2, ...) relies
   on, so ssralg is re-imported. For this file they are a no-op: the upstream statement
   compiles on Rocq 9.1 without them, and the theorem and its Definition print
   identically under Set Printing All with and without them. They do not change the
   meaning of the statement and are a no-op on Coq 8.18 / MathComp 2.1.
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
From mathcomp Require Import classical_sets.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition putnam_1974_a3_solution : (set nat) * (set nat) := ([set p : nat | prime p /\ p = 1 %[mod 8]], [set p : nat | prime p /\ p = 5 %[mod 8]]).
Theorem putnam_1974_a3
    (assmption : forall p : nat, (prime p /\ gt p 2) -> ((exists m n : int, p%:Z = m ^+ 2 + n ^+ 2) <-> p = 1 %[mod 4]))
    : forall p : nat, 
        ((prime p /\ gt p 2 /\ (exists x y : int, p%:Z = x ^+ 2 + 16 * y ^+ 2)) <-> p \in fst putnam_1974_a3_solution) /\
        ((prime p /\ gt p 2 /\ (exists x y : int, p%:Z = 4 * x ^+ 2 + 4 * x * y + 5 * y ^+ 2)) <-> p \in snd putnam_1974_a3_solution).
Proof. Admitted.