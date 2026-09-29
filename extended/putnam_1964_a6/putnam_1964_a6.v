(* ============================================================================
   PutnamBench 1964 A6 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1964_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim, except for the lines
   marked "(* compat: ... *)".
   Problem: S is a finite set of collinear points; k is the largest distance between two
   of its points; whenever two points of S are a distance d < k apart, some other pair
   of points of S is also a distance d apart. Show that the ratio of the distances of
   any two pairs of points of S is rational.
   Defect: the finiteness of the point set is not assumed. The problem says "a finite
   set of collinear points" and the Lean statement of PutnamBench has S : Finset R, but
   here T is an arbitrary set R. With T = [set: R] (the whole line) every hypothesis
   holds: for any pair p the translate (p.1 + 1, p.2 + 1) is a second pair at the same
   distance, so hrepdist is satisfied. The conclusion applied to the pairs
   (0, sqrt 2) and (0, 1) then says that sqrt 2 = n / d for some integers n, d with
   d <> 0, which is false. So the theorem is FALSE as written: derivation of False in
   putnam_1964_a6_statement_is_false.v. Proposed fix: putnam_1964_a6_corrected.v (the
   hypothesis (hT : finite_set T) added, and cardinality -- the module defining
   finite_set -- added to the classical_sets import line).
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0 (the Set Warnings line before "Variable R");
   (2) with MathComp 2.5, importing all_ssreflect after all_algebra (upstream's order)
   overrides the ring notations 1 and %:R, so ssralg is re-imported (the three lines
   after the imports). This statement itself writes neither 1 nor %:R: on Rocq 9.1 it
   also compiles without (2), and its type printed with Set Printing All is the same
   with and without (2); the re-import is kept, as in the repository's other MathComp
   files over a ring, so that the ring notations mean the same on every MathComp
   version. Neither changes the meaning of the statement. On Coq 8.18.0 they are
   no-ops, except that (1) also silences the "local-declaration" warning that the
   upstream Variable line emits there.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: on both toolchains the first import line emits library warnings
   (ambiguous coercion paths, overridden notations; on MathComp 2.5 also the
   deprecation of all_ssreflect) that come from MathComp itself; none of this file's
   own lines produce any. The import lines are kept exactly as upstream wrote them so
   that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals topology normedtype.
From mathcomp Require Import classical_sets.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1964_a6 
    (T : set R)
    (pairs : set (R * R) := [set p : R * R | p.1 \in T /\ p.2 \in T /\ p.1 < p.2])
    (distance : (R * R) -> R := fun p => p.2 - p.1)
    (hrepdist : forall p : R * R, p \in pairs ->
        (exists m : R * R, m \in pairs /\ distance m > distance p) ->
        (exists q : R * R, q \in pairs /\ q <> p /\ distance p = distance q))
    : forall p q : R * R, (p \in pairs /\ q \in pairs /\ q <> p) ->
        exists n d : int, d <> 0 /\ distance p / distance q = (n%:~R)/(d%:~R).
Proof. Admitted.