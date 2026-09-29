(* ============================================================================
   PutnamBench 1966 A5 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: C is the set of continuous functions R -> R and T : C -> C is linear
   (T (a f + b g) = a T f + b T g) and local (if f and g agree on an interval I, then
   T f and T g agree on I); prove that there is an h in C with T g = h * g for all g in C.
   Source: coq/src/putnam_1966_a5.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: the locality hypothesis localT ranges over all
   closed intervals [r, s] with "r <= s", i.e. also over the degenerate intervals
   [x, x]. With r = s = x it says that T f x depends only on the value f x, and with
   linearT the conclusion follows immediately (T g x = g x * T 1 x for the constant
   function 1): the upstream theorem is provable in a few lines with no analysis, so
   the statement is UNFAITHFUL (trivialized). The problem's "interval" is a
   nondegenerate interval; that is the whole content of the problem.
   Fix: apart from this header comment and the marked compat lines, differs from
   putnam_1966_a5.v (the upstream statement) in exactly one token, in localT:
       "forall r s : R, r <= s -> ..."   ->   "forall r s : R, r < s -> ..."
   Locality is now assumed only for nondegenerate closed intervals [r, s], r < s.
   This is the problem's hypothesis: agreement on any nondegenerate interval (open,
   half-open, closed, bounded or not) implies agreement on the nondegenerate closed
   sub-intervals it contains and conversely, so quantifying over closed [r, s] with
   r < s is equivalent to quantifying over all nondegenerate intervals, while the
   degenerate case [x, x] that trivialized the upstream statement is excluded. The
   hypotheses remain satisfiable (e.g. T f x = x * f x, checked in NOTES.md) and the
   conclusion is unchanged. PutnamBench's Lean statement has the same "r <= s" as the
   upstream Rocq statement and was therefore not followed on this point.
   Compat lines: the lines marked "(* compat: ... *)" were added for Rocq 9.1 /
   MathComp 2.5, on which the upstream file does not compile as written: (1) a
   Variable outside a Section is an error since Rocq 9.0 (Coq 8.x only warns);
   (2) with MathComp 2.5, importing all_ssreflect after all_algebra (upstream's
   order) overrides ring_scope notations of ssralg, so ssralg is re-imported as a
   precaution for the statement's ring_scope arithmetic on R (a no-op on MathComp
   <= 2.4). Neither changes the meaning of the statement.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. On that toolchain the first import line below triggers 23 warnings
   emitted by MathComp itself (ambiguous coercion paths, overridden notations); the
   repository's README describes the further ones under Rocq 9.1 / MathComp 2.5.
   They are library warnings, not warnings about this file: none of this file's own
   lines produce any. The import lines are kept exactly as upstream wrote them so
   that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals topology normedtype.
From mathcomp Require Import classical_sets.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
Import numFieldTopology.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1966_a5
    (C := [set f : R -> R | continuous f])
    (T : (R -> R) -> (R -> R))
    (imageTC : forall f : R -> R, f \in C -> T f \in C)
    (linearT : forall a b : R, forall f g : R -> R, f \in C -> g \in C -> T (fun x : R => a * f x + b * g x) = (fun x => a * T f x + b * T g x))
    (localT : forall r s : R, r < s -> forall f g : R -> R, f \in C -> g \in C -> (forall x : R, r <= x <= s -> f x = g x) -> (forall x : R, r <= x <= s -> T f x = T g x))
    : exists f : R -> R, f \in C /\ (forall g : R -> R, g \in C -> T g = fun x => f x * g x).
Proof. Admitted.
