(* ============================================================================
   PutnamBench 1974 A3 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1974_a3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines were needed:
   it compiles unchanged on both toolchains listed below).
   Problem: given that a prime p > 2 is a sum of two squares iff p = 1 (mod 4), find the
   primes p > 2 of the form (a) x^2 + 16 y^2 and (b) 4 x^2 + 4 x y + 5 y^2, with x, y
   integers. (Answer: (a) the primes p = 1 (mod 8); (b) the primes p = 5 (mod 8).)
   Defect: the statement is VACUOUS (audit verdict "vacuous (machine-checked)"). The
     "well-known theorem" is encoded with misplaced parentheses as
       forall p : nat, ((prime p /\ gt p 2) -> (exists m n : int, p%:Z = m ^+ 2 + n ^+ 2)) <-> p = 1 %[mod 4]
     i.e. as a biconditional for EVERY natural number p, whose left side is an
     implication. At p = 4 the left side holds vacuously (4 is not prime) while the
     right side says 4 = 1 (mod 4), i.e. 0 = 1; so the hypothesis is contradictory and
     the theorem holds for any solution sets whatsoever. Machine-checked proof that only
     uses this contradiction: putnam_1974_a3_statement_is_vacuous.v.
     The answer sets and the two conclusions are correct; the intended hypothesis (as in
     the Lean statement) is forall p, prime p /\ p > 2 -> (sum of two squares <-> p = 1 mod 4).
     Proposed fix: putnam_1974_a3_corrected.v.
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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition putnam_1974_a3_solution : (set nat) * (set nat) := ([set p : nat | prime p /\ p = 1 %[mod 8]], [set p : nat | prime p /\ p = 5 %[mod 8]]).
Theorem putnam_1974_a3
    (assmption : forall p : nat, ((prime p /\ gt p 2) -> ((exists m n : int, p%:Z = m ^+ 2 + n ^+ 2))) <-> p = 1 %[mod 4])
    : forall p : nat, 
        ((prime p /\ gt p 2 /\ (exists x y : int, p%:Z = x ^+ 2 + 16 * y ^+ 2)) <-> p \in fst putnam_1974_a3_solution) /\
        ((prime p /\ gt p 2 /\ (exists x y : int, p%:Z = 4 * x ^+ 2 + 4 * x * y + 5 * y ^+ 2)) <-> p \in snd putnam_1974_a3_solution).
Proof. Admitted.