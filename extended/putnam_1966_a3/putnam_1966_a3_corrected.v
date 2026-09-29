(* ============================================================================
   PutnamBench 1966 A3 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: if 0 < x_1 < 1 and x_{n+1} = x_n (1 - x_n) for all n >= 1, prove that
   lim_{n -> oo} n x_n = 1.
   Source: coq/src/putnam_1966_a3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: it does not compile (see putnam_1966_a3.v). The target
   of "-->" in the conclusion is the bare numeral "1"; "-->" expects a point of a filtered
   (topological) type and a bare "1" is only known to be the unit of some semiring, so
   elaboration fails with
     The term "1" has type "GRing.SemiRing.sort ?s0"
     while it is expected to have type "Filtered.sort ?s".
   The mathematics of the upstream statement is faithful; nothing else needed a change.
   Fix: exactly one token is added, in the conclusion:
     : (fun n : nat => n%:R * x n) @ \oo --> 1.
   becomes
     : (fun n : nat => n%:R * x n) @ \oo --> (1 : R).
   The ascription only names the type of the limit: the conclusion is "n%:R * x n converges
   to the real number 1 as n -> oo" (it unfolds to cvg_to (fmap (fun n => n%:R * x n) \oo)
   (nbhs (1 : R))), which is what the problem asks and what PutnamBench's Lean statement
   says (Tendsto (fun n => n * x n) atTop (nhds 1)). Everything else is upstream's text and
   matches the problem: x : nat -> R is 1-indexed like the problem's x_1, x_2, ... (x 0 is
   unconstrained and irrelevant: the limit does not depend on it); hx1 is 0 < x_1 < 1; hxi
   is the recurrence for every n >= 1 (ge n 1 is Peano's n >= 1); "@ \oo" is the limit
   along n -> oo.
   Compat lines: the lines marked "(* compat: ... *)" were added because, independently of
   the defect above, the upstream text has the two constructs that the repository README
   documents as fatal on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a Section is an
   error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect after all_algebra
   (upstream's order) overrides the ring notations 1 and %:R, so ssralg is re-imported.
   Neither changes the meaning of the statement; both are no-ops on Coq 8.18 / MathComp 2.1.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1; the import lines below trigger warnings emitted by MathComp itself
   (ambiguous coercion paths, overridden notations). They are library warnings, not
   warnings about this file: none of this file's own lines produce any. The import lines
   are kept exactly as upstream wrote them so that the statement stays identical to the
   benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals topology normedtype.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
From mathcomp Require Import classical_sets.
Import numFieldTopology.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1966_a3
    (x : nat -> R)
    (hx1 : 0 < x 1%nat /\ x 1%nat < 1)
    (hxi : forall n : nat, ge n 1 -> x (n.+1) = x n * (1 - x n))
    : (fun n : nat => n%:R * x n) @ \oo --> (1 : R).
Proof. Admitted.