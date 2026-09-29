(* ============================================================================
   PutnamBench 1966 A5 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1966_a5.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim, except for the lines
   marked "(* compat: ... *)".
   Problem: C is the set of continuous functions R -> R and T : C -> C is linear
   (T (a f + b g) = a T f + b T g) and local (if f and g agree on an interval I, then
   T f and T g agree on I); prove that there is an h in C with T g = h * g for all g in C.
   Defect (UNFAITHFUL: the statement is trivialized; see NOTES.md):
     the locality hypothesis localT is quantified over all closed intervals [r, s]
     with "r <= s", which includes the degenerate intervals [x, x]. Taken with
     r = s = x it says that T f x depends only on the single value f x, and with
     linearT this gives the conclusion at once: for every x, g agrees at x with the
     constant function g x * 1 + 0 * 1, so T g x = g x * T 1 x, where 1 is the
     constant function 1 and T 1 is in C by imageTC. The upstream theorem is thus
     provable in a few lines with no analysis at all (the script is in NOTES.md);
     the problem's "interval" is a nondegenerate interval, and the actual content of
     the problem (a pasting argument using continuity) is gone. PutnamBench's Lean
     statement has the same "r <= s" and hence the same defect.
     Proposed fix: putnam_1966_a5_corrected.v ("r <= s" becomes "r < s" in localT;
     nothing else changes).
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
    (localT : forall r s : R, r <= s -> forall f g : R -> R, f \in C -> g \in C -> (forall x : R, r <= x <= s -> f x = g x) -> (forall x : R, r <= x <= s -> T f x = T g x))
    : exists f : R -> R, f \in C /\ (forall g : R -> R, g \in C -> T g = fun x => f x * g x).
Proof. Admitted.