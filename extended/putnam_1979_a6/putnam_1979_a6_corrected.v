(* ============================================================================
   PutnamBench 1979 A6 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: given p_0, ..., p_(n-1) in [0, 1], show that some x in [0, 1] satisfies
   sum_(i = 0)^(n-1) 1/|x - p_i| <= 8n * sum_(i = 0)^(n-1) 1/(2i + 1).
   Source: coq/src/putnam_1979_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement (audit verdict "naming"): (1) the theorem is named
   putnam_1979_b6, the name of a different PutnamBench problem (1979 B6), instead of
   putnam_1979_a6; (2) the inner sum of the bound, "\sum_(0 <= i < (size p).+1)", runs
   over i = 0, ..., n (n = size p, the number of points) instead of i = 0, ..., n - 1.
   The extra term 1/(2n + 1) enlarges the bound by 8n/(2n + 1) whenever n >= 1 (n = 1:
   32/3 instead of 8), so the upstream theorem is strictly weaker than the problem
   (true, but not the problem's claim).
   Fix: apart from this header comment and the marked compat lines, the file differs
   from putnam_1979_a6.v (the upstream statement) in two places:
     Theorem putnam_1979_b6              ->  Theorem putnam_1979_a6
     \sum_(0 <= i < (size p).+1) ...     ->  \sum_(0 <= i < (size p)) ...
   (the second in the conclusion line; nothing else on that line changes). The bound
   is now 8n * sum_(i = 0)^(n-1) 1/(2i + 1), exactly the problem's and the Lean
   statement's (Finset.range n). The rest was re-checked against the problem and kept:
   the points are the entries of the list p (repetitions allowed, n = size p), hp says
   each lies in [0, 1], x lies in [0, 1], and the left-hand side sums 1/|x - p_i| over
   the entries of p. The conjunct "all (fun i => x != i) p" (x differs from every p_i)
   is also in the Lean statement; it makes every 1/|x - p_i| a genuine real number
   (MathComp's 1/0 = 0 would otherwise let x = p_i drop a term), so it only
   strengthens the claim, as the problem intends. All numerals, %:R casts and the
   division are in ring_scope on R; no nat arithmetic is involved. The corrected theorem
   implies the upstream one (machine-checked in a scratch file, see NOTES.md), so the fix
   only strengthens the statement, back to the problem's bound.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect
   after all_algebra (upstream's order) overrides the ring notations 1 and %:R, so
   ssralg is re-imported. Neither changes the meaning of the statement.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1.1 / MathComp 2.5.0 the first import line below triggers
   30 warnings emitted by MathComp itself (all_ssreflect is deprecated since 2.5,
   ambiguous coercion paths, overridden notations); under Coq 8.18.0 / MathComp 2.1.0 it
   triggers 23. They are library warnings, not warnings about this file: none of this
   file's own lines produce any. The import lines are kept exactly as upstream wrote them
   so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect fintype.
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
Theorem putnam_1979_a6
    (p : seq R)
    (hp : all (fun x => 0 <= x <= 1) p)
    : exists x : R, 0 <= x <= 1 /\ (all (fun i => x != i) p) /\ (\sum_(i <- p) 1/`|x - i|) <= 8*(size p)%:R*(\sum_(0 <= i < (size p)) (1%R)/(2*(i%:R) + 1)).
Proof. Admitted.