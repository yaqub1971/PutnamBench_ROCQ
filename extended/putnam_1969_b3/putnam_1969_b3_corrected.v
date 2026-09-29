(* ============================================================================
   PutnamBench 1969 B3 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: if a real sequence T satisfies T_n T_(n+1) = n for every n >= 1 and
   T_n / T_(n+1) -> 1 as n -> oo, then pi T_1^2 = 2.
   Source: coq/src/putnam_1969_b3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement (audit verdict: compile): the file does not compile.
   The target of "-->" in hypothesis hT2 is the bare numeral 1, which elaborates to 1 in
   an unknown semiring ("GRing.SemiRing.sort ?s0") and cannot be unified with the filter
   structure the notation expects ("Filtered.sort ?s"); Coq 8.18.0 / MathComp 2.1.0 /
   MathComp-Analysis 1.0.0 reject the upstream file at that token, and so does Rocq 9.1.1 /
   MathComp 2.5.0 / MathComp-Analysis 1.16.0 once the compat lines below are added.
   Mathematically the statement is faithful to the problem: it is PutnamBench's Lean
   statement of 1969 B3 (T n * T (n + 1) = n for n >= 1,
   Tendsto (fun n => T n / T (n + 1)) atTop (nhds 1), conclusion pi * (T 1)^2 = 2)
   transcribed to Rocq.
   Fix: exactly one line of the statement differs from putnam_1969_b3.v (the upstream
   statement), by one token:
     "    (hT2 : (fun n => (T n)/(T n.+1)) @ \oo --> 1)"
     -> "    (hT2 : (fun n => (T n)/(T n.+1)) @ \oo --> (1 : R))"
   The ascription only names the type in which the numeral lives (R, the realType the
   statement is about), which is what the upstream author necessarily meant and what the
   Lean statement has (1 : Real). The hypothesis hT1, the 1-based indexing (n >= 1), the
   ratio T n / T n.+1 and the conclusion pi * T 1 ^+ 2 = 2 (pi is MathComp-Analysis'
   trigo.pi) are unchanged; the corrected statement is neither weakened nor strengthened.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect
   after all_algebra (upstream's order) overrides the ring notations 1 and %:R, so
   ssralg is re-imported (without it, n%:R in hT1 fails to typecheck on MathComp 2.5).
   Neither changes the meaning of the statement; on Coq 8.18 / MathComp 2.1 both are
   no-ops.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: on both toolchains the first import line below triggers library
   warnings emitted by MathComp itself (overridden notations, ambiguous coercion paths,
   and on MathComp 2.5 the deprecation of all_ssreflect); they are not about this file,
   and none of this file's own lines produces any. The import lines are kept exactly as
   upstream wrote them so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals exp sequences topology normedtype trigo.
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
Theorem putnam_1969_b3
    (T : nat -> R)
    (hT1 : forall n : nat, ge n 1 -> (T n) * (T (n.+1)) = n%:R)
    (hT2 : (fun n => (T n)/(T n.+1)) @ \oo --> (1 : R))
    : pi * (T 1%nat) ^+ 2 = 2.
Proof. Admitted.