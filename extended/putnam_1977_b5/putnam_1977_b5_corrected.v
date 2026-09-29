(* ============================================================================
   PutnamBench 1977 B5 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: if a_1, ..., a_n are real numbers, n > 1, and
   A + sum a_i^2 < (1/(n-1)) (sum a_i)^2, then A < 2 a_i a_j for all 1 <= i < j <= n.
   Source: coq/src/putnam_1977_b5.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: the hypothesis hA is non-strict ("<=") while the
   problem's is strict ("<"). That makes the statement FALSE: for n = 2, a = (1, 1),
   A = 2 the hypothesis holds with equality (2 + 2 = 4 = 1/(2-1) * 2^2) and the
   conclusion claims 2 < 2 * 1 * 1 (see putnam_1977_b5_statement_is_false.v).
   Fix: apart from this header comment, this file differs from putnam_1977_b5.v (the
   upstream copy, with the same compat lines) in exactly one line:
     (hA : A + \sum_(i <- a) (i ^+ 2) <= 1/((size a)%:R - 1) * (\sum_(i <- a) i) ^+ 2)
   ->(hA : A + \sum_(i <- a) (i ^+ 2) < 1/((size a)%:R - 1) * (\sum_(i <- a) i) ^+ 2)
   which is the strict inequality of the problem and of the Lean statement
   (hA : A + sum (a i)^2 < (1/((n : R) - 1)) * (sum a i)^2). Everything else was
   checked faithful: the sequence a : seq R of length n = size a > 1 (a nat
   comparison), the sums over all entries, the real division 1/(n - 1) with n - 1 > 0,
   and "pairwise (fun x y => A < 2 * x * y) a", which states A < 2 a_i a_j for every
   pair of positions i < j of a, i.e. the conclusion for all 1 <= i < j <= n.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0 (the Set Warnings line before "Variable R");
   (2) with MathComp 2.5, importing all_ssreflect after all_algebra (upstream's order)
   overrides the ring notations 1 and %:R, so ssralg is re-imported (the three lines
   after the imports); without (2) the statement fails on Rocq 9.1 at the "1" of
   "1/((size a)%:R - 1)" (checked). Neither changes the meaning of the statement. On
   Coq 8.18.0 they are no-ops, except that (1) also silences the "local-declaration"
   warning that the upstream Variable line emits there.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: on both toolchains the first import line emits library warnings
   (ambiguous coercion paths, overridden notations; on MathComp 2.5 also the
   deprecation of all_ssreflect) that come from MathComp itself; none of this file's
   own lines produce any. The import lines are kept exactly as upstream wrote them so
   that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1977_b5
    (a : seq R)
    (A : R)
    (ha : gt (size a) 1)
    (hA : A + \sum_(i <- a) (i ^+ 2) < 1/((size a)%:R - 1) * (\sum_(i <- a) i) ^+ 2)
    : pairwise (fun x y => A < 2 * x * y) a.
Proof. Admitted.